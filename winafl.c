/*
   WinAFL - DynamoRIO client (instrumentation) code
   ------------------------------------------------

   Written and maintained by Ivan Fratric <ifratric@google.com>

   Copyright 2016 Google Inc. All Rights Reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

*/

#define _CRT_SECURE_NO_WARNINGS

#define MAP_SIZE 65536

#include "dr_api.h"
#include "drmgr.h"
#include "drx.h"
#include "drreg.h"
#include "drwrap.h"
#include "modules.h"
#include "utils.h"
#include "hashtable.h"
#include "drtable.h"
#include "limits.h"
#include <string.h>
#include <stdlib.h>

#define UNKNOWN_MODULE_ID USHRT_MAX

static uint verbose;

#define NOTIFY(level, fmt, ...) do {          \
    if (verbose >= (level))                   \
        dr_fprintf(STDERR, fmt, __VA_ARGS__); \
} while (0)

void dbgprint(char *fmt, ...)
{
	do {
		va_list arg;
		char buffer[4096] = { 0 };

		va_start(arg, fmt);
		dr_vsnprintf(buffer, 4096, fmt, arg);
		va_end(arg);

		OutputDebugStringA(buffer);
	} while (0);
}

void __forceinline dbgbreak(void)
{
	__debugbreak();
}

#ifdef _DEBUG
#define DEBUG_PRINT dbgprint        
#define DEBUG_BREAK dbgbreak
#else 
#define DEBUG_PRINT
#define DEBUG_BREAK __nop
#endif

// Make it optional for GUI-based software (eg: Microsoft Office or Windows Media Player)
#ifdef _WMP
#define MAXIMUM_MESSAGE_IDS 256
BOOL	g_BoolFirstRun = true;
/*	Maximum wait time (ms) for the next input iteration.
*	Must be smaller than client time-out value specified
*	in afl-fuzz CreateNamePipe function and also exec_tmout
*	(using -t option)
*/
UINT	g_WaitTimeMs = 20000;
// This is a maximum count of continuous message id hit by GetMessage API
int		g_MaxCountMessageIdOccurred = 1000;
#endif

#define OPTION_MAX_LENGTH MAXIMUM_PATH

#define COVERAGE_BB 0
#define COVERAGE_EDGE 1

typedef struct _target_module_t {
    char module_name[MAXIMUM_PATH];
    struct _target_module_t *next;
} target_module_t;

typedef struct _winafl_option_t {
    /* Use nudge to notify the process for termination so that
     * event_exit will be called.
     */
    bool nudge_kills;
    bool debug_mode;
    int coverage_kind;
    char logdir[MAXIMUM_PATH];
    target_module_t *target_modules;
    //char instrument_module[MAXIMUM_PATH];
    char fuzz_module[MAXIMUM_PATH];
    char fuzz_method[MAXIMUM_PATH];
    char pipe_name[MAXIMUM_PATH];
    char shm_name[MAXIMUM_PATH];
    unsigned long fuzz_offset;
    int fuzz_iterations;
    void **func_args;
    int num_fuz_args;
    drwrap_callconv_t callconv;
#ifdef _WMP
	unsigned long timeout;
	int messageid[MAXIMUM_MESSAGE_IDS];
#endif
} winafl_option_t;
static winafl_option_t options;

#define NUM_THREAD_MODULE_CACHE 4

typedef struct _winafl_data_t {
    module_entry_t *cache[NUM_THREAD_MODULE_CACHE];
    file_t  log;
    //unsigned char afl_area[MAP_SIZE];
    unsigned char *afl_area;
#ifdef _WIN64
    uint64 previous_offset;
#else
    unsigned int previous_offset;
#endif
} winafl_data_t;
static winafl_data_t winafl_data;

typedef struct _fuzz_target_t {
    reg_t xsp;            /* stack level at entry to the fuzz target */
	reg_t xcx;
    app_pc func_pc;
	char *cur_input;
    int iteration;
} fuzz_target_t;
static fuzz_target_t fuzz_target;

typedef struct _debug_data_t {
    int pre_hanlder_called;
    int post_handler_called;
} debug_data_t;
static debug_data_t debug_data;

static module_table_t *module_table;
static client_id_t client_id;

static volatile bool go_native;

static void
event_exit(void);

static void
event_thread_exit(void *drcontext);

static HANDLE pipe;

/****************************************************************************
* Helper functions
*/
/* Get current time in milliseconds */
static uint64 get_cur_time(void) {

	uint64 ret;
	FILETIME filetime;
	GetSystemTimeAsFileTime(&filetime);

	ret = (((uint64)filetime.dwHighDateTime) << 32) + (uint64)filetime.dwLowDateTime;

	return ret / 10000;

}

/****************************************************************************
 * Nudges
 */

enum {
    NUDGE_TERMINATE_PROCESS = 1,
};

static void
event_nudge(void *drcontext, uint64 argument)
{
    int nudge_arg = (int)argument;
    int exit_arg  = (int)(argument >> 32);
    if (nudge_arg == NUDGE_TERMINATE_PROCESS) {
        static int nudge_term_count;
        /* handle multiple from both NtTerminateProcess and NtTerminateJobObject */
        uint count = dr_atomic_add32_return_sum(&nudge_term_count, 1);
        if (count == 1) {
            dr_exit_process(exit_arg);
        }
    }
    ASSERT(nudge_arg == NUDGE_TERMINATE_PROCESS, "unsupported nudge");
    ASSERT(false, "should not reach"); /* should not reach */
}

static bool
event_soft_kill(process_id_t pid, int exit_code)
{
    /* we pass [exit_code, NUDGE_TERMINATE_PROCESS] to target process */
    dr_config_status_t res;
    res = dr_nudge_client_ex(pid, client_id,
                             NUDGE_TERMINATE_PROCESS | (uint64)exit_code << 32,
                             0);
    if (res == DR_SUCCESS) {
        /* skip syscall since target will terminate itself */
        return true;
    }
    /* else failed b/c target not under DR control or maybe some other
     * error: let syscall go through
     */
    return false;
}

/****************************************************************************
 * Event Callbacks
 */

static void
dump_winafl_data()
{
    dr_write_file(winafl_data.log, winafl_data.afl_area, MAP_SIZE);
}

static bool
onexception(void *drcontext, dr_exception_t *excpt) {
    DWORD num_written;
    DWORD exception_code = excpt->record->ExceptionCode;

    if(options.debug_mode)
        dr_fprintf(winafl_data.log, "Exception caught: %x\n", exception_code);

    if((exception_code == EXCEPTION_ACCESS_VIOLATION) ||
       (exception_code == EXCEPTION_ILLEGAL_INSTRUCTION) ||
       (exception_code == EXCEPTION_PRIV_INSTRUCTION) ||
       (exception_code == EXCEPTION_STACK_OVERFLOW)) {
		DEBUG_BREAK();
		dr_fprintf(winafl_data.log, "crashed at %08x\n", excpt->mcontext->pc);
          if(!options.debug_mode)
            WriteFile(pipe, "C", 1, &num_written, NULL);
          dr_exit_process(1);
    }
    return true;
}

static dr_emit_flags_t
analysis_bb_coverage(void *drcontext, void *tag, instrlist_t *bb,
					 bool for_trace, bool translating, OUT void **user_data)
{
	instr_t *instr;
	app_pc start_pc;
	int cur_size = 0;

	if (translating)
		return DR_EMIT_DEFAULT;

	start_pc = dr_fragment_app_pc(tag);

	for (instr = instrlist_first_app(bb);
		instr != NULL;
		instr = instr_get_next_app(instr))
		cur_size++;


	return DR_EMIT_DEFAULT;
}

#ifdef _WMP
uint64 start_instru_ms = 0; /* A time to indicate when the last instrumentation was started (ms) */
#endif
static dr_emit_flags_t
instrument_bb_coverage(void *drcontext, void *tag, instrlist_t *bb, instr_t *inst,
                      bool for_trace, bool translating, void *user_data)
{
    static bool debug_information_output = false;
    app_pc start_pc;
    module_entry_t **mod_entry_cache;
    module_entry_t *mod_entry;
    const char *module_name;
    uint offset;
    target_module_t *target_modules;
    bool should_instrument;

    if (!drmgr_is_first_instr(drcontext, inst))
        return DR_EMIT_DEFAULT;

    start_pc = dr_fragment_app_pc(tag);

    mod_entry_cache = winafl_data.cache;
    mod_entry = module_table_lookup(mod_entry_cache,
                                                NUM_THREAD_MODULE_CACHE,
                                                module_table, start_pc);

    if (mod_entry == NULL || mod_entry->data == NULL) return DR_EMIT_DEFAULT;

    module_name = dr_module_preferred_name(mod_entry->data);

    should_instrument = false;
    target_modules = options.target_modules;
    while(target_modules) {
        if(_stricmp(module_name, target_modules->module_name) == 0) {
            should_instrument = true;
            if(options.debug_mode && debug_information_output == false) {
                dr_fprintf(winafl_data.log, "Instrumenting %s with the 'bb' mode\n", module_name);
                debug_information_output = true;
            }
            break;
        }
        target_modules = target_modules->next;
    }
    if(!should_instrument) return DR_EMIT_DEFAULT;

#ifdef _WMP
	/*
	*  Get the start time of the instrumentation
	*  that can be used to determine if we should start
	*  next input
	*/
	//start_instru_ms = get_cur_time();
#endif

    offset = (uint)(start_pc - mod_entry->data->start);
    offset &= MAP_SIZE - 1;

    drreg_reserve_aflags(drcontext, bb, inst);

    instrlist_meta_preinsert(bb, inst,
        INSTR_CREATE_inc(drcontext, OPND_CREATE_ABSMEM
        (&(winafl_data.afl_area[offset]), OPSZ_1)));

    drreg_unreserve_aflags(drcontext, bb, inst);

	//DEBUG_PRINT("%s:%d Post BB hit at block %08x\n", __FUNCTION__, __LINE__, start_pc);
    return DR_EMIT_DEFAULT;
}

static dr_emit_flags_t
instrument_edge_coverage(void *drcontext, void *tag, instrlist_t *bb, instr_t *inst,
                      bool for_trace, bool translating, void *user_data)
{
    static bool debug_information_output = false;
    app_pc start_pc;
    module_entry_t **mod_entry_cache;
    module_entry_t *mod_entry;
    reg_id_t reg;
#ifdef _WIN64
    reg_id_t reg2;
#endif
    opnd_t opnd1, opnd2;
    instr_t *new_instr;
    const char *module_name;
    uint offset;
    target_module_t *target_modules;
    bool should_instrument;

    if (!drmgr_is_first_instr(drcontext, inst))
        return DR_EMIT_DEFAULT;

    start_pc = dr_fragment_app_pc(tag);

    mod_entry_cache = winafl_data.cache;
    mod_entry = module_table_lookup(mod_entry_cache,
                                                NUM_THREAD_MODULE_CACHE,
                                                module_table, start_pc);

     if (mod_entry == NULL || mod_entry->data == NULL) return DR_EMIT_DEFAULT;

    module_name = dr_module_preferred_name(mod_entry->data);

    should_instrument = false;
    target_modules = options.target_modules;
    while(target_modules) {
        if(_stricmp(module_name, target_modules->module_name) == 0) {
            should_instrument = true;
            if(options.debug_mode && debug_information_output == false) {
                dr_fprintf(winafl_data.log, "Instrumenting %s with the 'edge' mode\n", module_name);
                debug_information_output = true;
            }
            break;
        }
        target_modules = target_modules->next;
    }
    if(!should_instrument) return DR_EMIT_DEFAULT;

#ifdef _WMP
	/*
	*  Get the start time of the instrumentation
	*  that can be used to determine if we should start
	*  next input
	*/
	//start_instru_ms = get_cur_time();
#endif

    offset = (uint)(start_pc - mod_entry->data->start);
    offset &= MAP_SIZE - 1;

    drreg_reserve_aflags(drcontext, bb, inst);
    drreg_reserve_register(drcontext, bb, inst, NULL, &reg);

#ifdef _WIN64

    drreg_reserve_register(drcontext, bb, inst, NULL, &reg2);

    //load previous offset into register
    opnd1 = opnd_create_reg(reg);
    opnd2 = OPND_CREATE_ABSMEM(&(winafl_data.previous_offset), OPSZ_8);
    new_instr = INSTR_CREATE_mov_ld(drcontext, opnd1, opnd2);
    instrlist_meta_preinsert(bb, inst, new_instr);

    //xor register with the new offset
    opnd1 = opnd_create_reg(reg);
    opnd2 = OPND_CREATE_INT32(offset);
    new_instr = INSTR_CREATE_xor(drcontext, opnd1, opnd2);
    instrlist_meta_preinsert(bb, inst, new_instr);

    //load address of shm into the second register
    opnd1 = opnd_create_reg(reg2);
    opnd2 = OPND_CREATE_INT64((uint64)winafl_data.afl_area);
    new_instr = INSTR_CREATE_mov_imm(drcontext, opnd1, opnd2);
    instrlist_meta_preinsert(bb, inst, new_instr);

    //increase the counter at reg + reg2
    opnd1 = opnd_create_base_disp(reg2, reg, 1, 0, OPSZ_1);
    new_instr = INSTR_CREATE_inc(drcontext, opnd1);
    instrlist_meta_preinsert(bb, inst, new_instr);

    //store the new value
    offset = (offset >> 1)&(MAP_SIZE - 1);
    opnd1 = OPND_CREATE_ABSMEM(&(winafl_data.previous_offset), OPSZ_8);
    opnd2 = OPND_CREATE_INT32(offset);
    new_instr = INSTR_CREATE_mov_st(drcontext, opnd1, opnd2);
    instrlist_meta_preinsert(bb, inst, new_instr);

    drreg_unreserve_register(drcontext, bb, inst, reg2);

#else

    //load previous offset into register
    opnd1 = opnd_create_reg(reg);
    opnd2 = OPND_CREATE_ABSMEM(&(winafl_data.previous_offset), OPSZ_4);
    new_instr = INSTR_CREATE_mov_ld(drcontext, opnd1, opnd2);
    instrlist_meta_preinsert(bb, inst, new_instr);

    //xor register with the new offset
    opnd1 = opnd_create_reg(reg);
    opnd2 = OPND_CREATE_INT32(offset);
    new_instr = INSTR_CREATE_xor(drcontext, opnd1, opnd2);
    instrlist_meta_preinsert(bb, inst, new_instr);

    //increase the counter at afl_area+reg
    opnd1 = OPND_CREATE_MEM8(reg, (int)winafl_data.afl_area);
    new_instr = INSTR_CREATE_inc(drcontext, opnd1);
    instrlist_meta_preinsert(bb, inst, new_instr);

    //store the new value
    offset = (offset >> 1)&(MAP_SIZE - 1);
    opnd1 = OPND_CREATE_ABSMEM(&(winafl_data.previous_offset), OPSZ_4);
    opnd2 = OPND_CREATE_INT32(offset);
    new_instr = INSTR_CREATE_mov_st(drcontext, opnd1, opnd2);
    instrlist_meta_preinsert(bb, inst, new_instr);

#endif

    drreg_unreserve_register(drcontext, bb, inst, reg);
    drreg_unreserve_aflags(drcontext, bb, inst);

    return DR_EMIT_DEFAULT;
}

static void
pre_fuzz_handler(void *wrapcxt, INOUT void **user_data)
{
    char command = 0;
    int i;
    DWORD num_read;
	
    app_pc target_to_fuzz = drwrap_get_func(wrapcxt);
    dr_mcontext_t *mc = drwrap_get_mcontext_ex(wrapcxt, DR_MC_ALL);

    fuzz_target.xsp = mc->xsp;
	fuzz_target.xcx = mc->xcx;
    fuzz_target.func_pc = target_to_fuzz;

    if(!options.debug_mode) {
        ReadFile(pipe, &command, 1, &num_read, NULL);

        if(command != 'F') {
            if(command == 'Q') {
                dr_exit_process(0);
            } else {
                DR_ASSERT_MSG(false, "unrecognized command received over pipe");
            }
        }
    } else {
        debug_data.pre_hanlder_called++;
		if (options.debug_mode)
			dr_fprintf(winafl_data.log, "In pre_fuzz_handler: 0x%08x\n", target_to_fuzz);
    }

    //save or restore arguments
    if(fuzz_target.iteration == 0) {
        for(i = 0; i < options.num_fuz_args; i++) {
            options.func_args[i] = drwrap_get_arg(wrapcxt, i);
			if (options.debug_mode)
				dr_fprintf(winafl_data.log, "get arg(%d): 0x%x\n", i, options.func_args[i]);
        }
    } else {
        for(i = 0; i < options.num_fuz_args; i++) {
			if (options.debug_mode)
				dr_fprintf(winafl_data.log, "set arg(%d): 0x%x\n", i, options.func_args[i]);
            drwrap_set_arg(wrapcxt, i, options.func_args[i]);
        }
    }

    memset(winafl_data.afl_area, 0, MAP_SIZE);
    winafl_data.previous_offset = 0;
}

static void
post_fuzz_handler(void *wrapcxt, void *user_data)
{
    DWORD num_written;
    dr_mcontext_t *mc = drwrap_get_mcontext(wrapcxt);
	app_pc addr = drwrap_get_func(wrapcxt);
	
    if(!options.debug_mode) {
		DEBUG_PRINT("%s:%d: Sending OK command to afl-fuzz\n", __FUNCTION__, __LINE__);
        WriteFile(pipe, "K", 1, &num_written, NULL);
    } else {
        debug_data.post_handler_called++;
        dr_fprintf(winafl_data.log, "In post_fuzz_handler: 0x%08x\n", addr);
    }

    fuzz_target.iteration++;
    if(fuzz_target.iteration == options.fuzz_iterations) {
        dr_exit_process(0);
    }

    mc->xsp = fuzz_target.xsp;
	mc->xcx = fuzz_target.xcx;
    mc->pc = fuzz_target.func_pc;
    drwrap_redirect_execution(wrapcxt);
}

static void
createfilew_interceptor(void *wrapcxt, INOUT void **user_data)
{
    wchar_t *filenamew = (wchar_t *)drwrap_get_arg(wrapcxt, 0);

    if(options.debug_mode)
        dr_fprintf(winafl_data.log, "In OpenFileW, reading %ls\n", filenamew);
}

static void
createfilea_interceptor(void *wrapcxt, INOUT void **user_data)
{
    char *filename = (char *)drwrap_get_arg(wrapcxt, 0);

    if(options.debug_mode)
        dr_fprintf(winafl_data.log, "In OpenFileA, reading %s\n", filename);
}

static void
messagebox_interceptor(void *wrapcxt, INOUT void **user_data)
{
	/* Always return IDOK */
	bool res = drwrap_skip_call(wrapcxt, (int *)IDOK, sizeof(void*) * 5);
	if (options.debug_mode)
		dr_fprintf(winafl_data.log, "Skipped MessageBoxExAorW\n");
	DEBUG_PRINT("%s:%d: drwrap_skip_call: %d\n", __FUNCTION__, __LINE__, res);

}

static void
dialogboxidnirectparam_interceptor(void *wrapcxt, INOUT void **user_data)
{
	bool res = drwrap_skip_call(wrapcxt, (int *)-1, sizeof(void*) * 6);
	if (options.debug_mode)
		dr_fprintf(winafl_data.log, "Skipped DialogBoxIndirectParamAorW\n");
	DEBUG_PRINT("%s:%d: drwrap_skip_call: %d\n", __FUNCTION__, __LINE__, res);

}

#ifdef _WMP

static void
helper_start_wmp()
{
	/*char szWMPlayerPath[MAX_PATH] = { 0 };
	char szWMPlayer[MAX_PATH] = { 0 };
	char szParameter[MAX_PARAMETER] = { 0 };
	char *command = NULL;

	STARTUPINFOA si;
	PROCESS_INFORMATION pi;
	memset(&si, 0, sizeof(STARTUPINFOA));
	memset(&pi, 0, sizeof(PROCESS_INFORMATION));
	si.cb = sizeof(STARTUPINFOA);*/

	//ExpandEnvironmentStringsA("%PROGRAMFILES%\\Windows Media Player", szWMPlayerPath, MAX_PATH);
	//dr_snprintf(szWMPlayer, MAX_PATH, "%s\\wmplayer.exe", szWMPlayerPath);
	//ExpandEnvironmentStringsA("%PROGRAMFILES%\\Windows Media Player\\wmplayer.exe", szWMPlayer, MAX_PATH);
	//dr_snprintf(szParameter, BUFFER_SIZE_ELEMENTS(szParameter), "\"%s\" %s", szWMPlayer, fuzz_target.cur_input);
	//CreateProcessA(szWMPlayer, szParameter, NULL, NULL, FALSE, 0, NULL, NULL, &si, &pi);
	//ShellExecuteA(NULL, "open", szWMPlayer, szParameter, szWMPlayerPath, SW_SHOW);
	HANDLE hWMPPipe = NULL;

	while (1)
	{
		hWMPPipe = CreateFile(
			"\\\\.\\pipe\\pipecreatewmp",   // WMP pipe name 
			GENERIC_READ |                  // read and write access 
			GENERIC_WRITE,
			0,                              // no sharing 
			NULL,                           // default security attributes
			OPEN_EXISTING,                  // opens existing pipe 
			0,                              // default attributes 
			NULL);                          // no template file 

		if (GetLastError() == ERROR_PIPE_BUSY)
		{
			DEBUG_PRINT("%s:%d: All pipe instances are busy, wait for 1 second\n", __FUNCTION__, __LINE__);
			if (!WaitNamedPipeA("\\\\.\\pipe\\pipecreatewmp", 1000))
				DR_ASSERT_MSG(false, "helper_start_wmp: could not open pipe after waiting for 1 second\n");

		}
		else
			break;
	}

	if (hWMPPipe == INVALID_HANDLE_VALUE)
		DR_ASSERT_MSG(false, "helper_start_wmp failed\n");

	WriteFile(hWMPPipe, fuzz_target.cur_input, strlen(fuzz_target.cur_input), NULL, NULL);
	CloseHandle(hWMPPipe);
}

static void start_dummy_wmp()
{
	HANDLE hWMPPipe = NULL;

	hWMPPipe = CreateFile(
		"\\\\.\\pipe\\pipecreatewmp",   // WMP pipe name 
		GENERIC_READ |                  // read and write access 
		GENERIC_WRITE,
		0,                              // no sharing 
		NULL,                           // default security attributes
		OPEN_EXISTING,                  // opens existing pipe 
		0,                              // default attributes 
		NULL);                          // no template file 

	if (hWMPPipe == INVALID_HANDLE_VALUE)
		DR_ASSERT_MSG(false, "start_dummy_wmp failed\n");

	WriteFile(hWMPPipe, "c:\\dummy.wmv", strlen("c:\\dummy.wmv"), NULL, NULL);
	CloseHandle(hWMPPipe);
}

static void
getmessage_interceptor_pre(void *wrapcxt, INOUT void **user_data)
{
	MSG* msg = (MSG*)drwrap_get_arg(wrapcxt, 0);
	*user_data = (MSG*)msg;
}

bool g_DummyWMPCalled = false;
static void
getmessage_interceptor_post(void *wrapcxt, void *user_data)
{
	MSG* msg = (MSG*)user_data;
	
	/*if (getenv("AFL_WRITE_LOCK") && atoi(getenv("AFL_WRITE_LOCK")))
		return;*/

	// Proceed only when GetMessage call is successful
	if ((unsigned int)drwrap_get_retval(wrapcxt) != -1)
	{
		// Message we want to intercept so that we will proceed to the next input
		DR_ASSERT_MSG(options.messageid[0] != -1, "Options message_id is empty");
		if (msg != NULL)
		{
			if (fuzz_target.iteration == options.fuzz_iterations)
			{
				DEBUG_PRINT("%s:%d: Finished %d iteration\n", __FUNCTION__, __LINE__, options.fuzz_iterations);
				dr_exit_process(0);
			}

			DEBUG_PRINT("%s:%d: Message: 0x%x\n", __FUNCTION__, __LINE__, msg->message);
			for (int i = 0; i < MAXIMUM_MESSAGE_IDS; i++)
			{
				//if (msg->message == 0x8001)
				//{
				//	//
				//	// 3. Now we proceed to next input test case
				//	//
				//	if (g_DummyWMPCalled)
				//	{
				//		g_DummyWMPCalled = false;
				//		helper_start_wmp();
				//		DEBUG_PRINT("%s:%d: afl.wmv called\n", __FUNCTION__, __LINE__);
				//		return;
				//	}
				//}

				if (msg->message == options.messageid[i])
				{
					if (!options.debug_mode)
					{
						char command = 0;
						DWORD num_read;
						DEBUG_PRINT("%s:%d: Reading command...\n", __FUNCTION__, __LINE__);
						ReadFile(pipe, &command, 1, &num_read, NULL);
						DEBUG_PRINT("%s:%d: Read command: %c\n", __FUNCTION__, __LINE__, command);

						if (command != 'F')
						{
							if (command == 'Q')
							{
								dr_exit_process(0);
							}
							else
							{
								DEBUG_PRINT("%s:%d: Command: %c\n", __FUNCTION__, __LINE__, command);
								DR_ASSERT_MSG(false, "unrecognized command received over pipe");
							}
						}
					}
					
					start_instru_ms = get_cur_time();
					memset(winafl_data.afl_area, 0, MAP_SIZE);
					winafl_data.previous_offset = 0;
				}
			}

			if (start_instru_ms > 0 && get_cur_time() > start_instru_ms + options.timeout)
			{
				DEBUG_PRINT("%s:%d: Threshold met\n", __FUNCTION__, __LINE__);
				if (!options.debug_mode)
				{
					//
					// 1. Before proceed, we need to close the file handle
					// of the current input test case by starting WMP with
					// dummy file
					//
					/*g_DummyWMPCalled = true;
					start_dummy_wmp();
					DEBUG_PRINT("%s:%d: Dummy WMP called\n", __FUNCTION__, __LINE__);*/

					//
					// 2. Tell afl-fuzz fuzzing is OK
					//
					DWORD num_written;
					WriteFile(pipe, "K", 1, &num_written, NULL);
					start_instru_ms = 0;

					/*if (getenv("AFL_DRYRUN_COMPLETE") && atoi(getenv("AFL_DRYRUN_COMPLETE")))
					{
						helper_start_wmp();
					}*/

					//
					// Now we proceed to next input test case
					//
					/*char command;
					ReadFile(pipe, &command, 1, NULL, NULL);
					if (command == 'S')
					{
					helper_start_wmp();
					}*/
				}
				else
				{
					DEBUG_BREAK();
					start_instru_ms = 0;
					helper_start_wmp();
				}
				
				fuzz_target.iteration++;
			}

		}
	}
}
#endif // End _WMP

static void
event_module_unload(void *drcontext, const module_data_t *info)
{
    module_table_unload(module_table, info);
}

int mod_index = 0;
static void
event_module_load(void *drcontext, const module_data_t *info, bool loaded)
{
    const char *module_name = info->names.exe_name;
    app_pc to_wrap;

    if (module_name == NULL) {
        // In case exe_name is not defined, we will fall back on the preferred name.
        module_name = dr_module_preferred_name(info);
    }

	if (options.debug_mode)
		dr_fprintf(winafl_data.log, "#%d Module loaded, %s, Loaded address: 0x%x, End address: 0x%x\n", mod_index++, module_name, info->start, info->end);

    if(options.fuzz_module[0]) {
		if (_stricmp(module_name, options.fuzz_module) == 0) {
            if(options.fuzz_offset) {
                to_wrap = info->start + options.fuzz_offset;
            } else {
                to_wrap = (app_pc)dr_get_proc_address(info->handle, options.fuzz_method);
                DR_ASSERT_MSG(to_wrap, "Can't find specified method in fuzz_module");
            }
            drwrap_wrap_ex(to_wrap, pre_fuzz_handler, post_fuzz_handler, NULL, options.callconv);
        }

		if (options.debug_mode && (_stricmp(module_name, "KERNEL32.dll") == 0)) {
            to_wrap = (app_pc)dr_get_proc_address(info->handle, "CreateFileW");
            drwrap_wrap(to_wrap, createfilew_interceptor, NULL);
            to_wrap = (app_pc)dr_get_proc_address(info->handle, "CreateFileA");
            drwrap_wrap(to_wrap, createfilea_interceptor, NULL);
        }

		if (_stricmp(module_name, "USER32.dll") == 0) {
			// TODO: Experimenting if the following are the caused of unknown random WMP crash
			to_wrap = (app_pc)dr_get_proc_address(info->handle, "MessageBoxExW");
			drwrap_wrap(to_wrap, messagebox_interceptor, NULL);
			to_wrap = (app_pc)dr_get_proc_address(info->handle, "MessageBoxExA");
			drwrap_wrap(to_wrap, messagebox_interceptor, NULL);
			to_wrap = (app_pc)dr_get_proc_address(info->handle, "DialogBoxIndirectParamAorW");
			drwrap_wrap(to_wrap, dialogboxidnirectparam_interceptor, NULL);
#ifdef _WMP
			to_wrap = (app_pc)dr_get_proc_address(info->handle, "GetMessageW");
			drwrap_wrap(to_wrap, getmessage_interceptor_pre, getmessage_interceptor_post);
			to_wrap = (app_pc)dr_get_proc_address(info->handle, "GetMessageA");
			drwrap_wrap(to_wrap, getmessage_interceptor_pre, getmessage_interceptor_post);
#endif
		}
    }

    module_table_load(module_table, info);
}

static void
event_exit(void)
{
    if(options.debug_mode) {
        if(debug_data.pre_hanlder_called == 0) {
            dr_fprintf(winafl_data.log, "WARNING: Target function was never called. Incorrect target_offset?\n");
        } else if(debug_data.post_handler_called == 0) {
            dr_fprintf(winafl_data.log, "WARNING: Post-fuzz handler was never reached. Did the target function return normally?\n");
        } else {
            dr_fprintf(winafl_data.log, "Everything appears to be running normally.\n");
        }

        dr_fprintf(winafl_data.log, "Coverage map follows:\n");
        dump_winafl_data();
        dr_close_file(winafl_data.log);
    }

    /* destroy module table */
    module_table_destroy(module_table);

//#ifdef _WMP
//	_putenv_s("AFL_DRYRUN_COMPLETE", "0");
//#endif
    drx_exit();
    drmgr_exit();
}

static void
event_init(void)
{
    char buf[MAXIMUM_PATH];

    module_table = module_table_create();

    memset(winafl_data.cache, 0, sizeof(winafl_data.cache));
    memset(winafl_data.afl_area, 0, MAP_SIZE);

    winafl_data.previous_offset = 0;

    if(options.debug_mode) {
        debug_data.pre_hanlder_called = 0;
        debug_data.post_handler_called = 0;

        winafl_data.log =
            drx_open_unique_appid_file(options.logdir, dr_get_process_id(),
                                   "afl_debug", "proc.log",
                                   DR_FILE_ALLOW_LARGE,
                                   buf, BUFFER_SIZE_ELEMENTS(buf));
        if (winafl_data.log != INVALID_FILE) {
            dr_log(NULL, LOG_ALL, 1, "winafl: log file is %s\n", buf);
            NOTIFY(1, "<created log file %s>\n", buf);
        }
    }


	else
	{
		winafl_data.log =
			drx_open_unique_appid_file(options.logdir, dr_get_process_id(),
			"afl_release", "proc.log",
			DR_FILE_ALLOW_LARGE,
			buf, BUFFER_SIZE_ELEMENTS(buf));
		if (winafl_data.log != INVALID_FILE) {
			dr_log(NULL, LOG_ALL, 1, "winafl: log file is %s\n", buf);
			NOTIFY(1, "<created log file %s>\n", buf);
		}
	}

    fuzz_target.iteration = 0;
}


static void
setup_pipe() {
    pipe = CreateFile(
         options.pipe_name,   // pipe name
         GENERIC_READ |  // read and write access
         GENERIC_WRITE,
         0,              // no sharing
         NULL,           // default security attributes
         OPEN_EXISTING,  // opens existing pipe
         0,              // default attributes
         NULL);          // no template file

    if (pipe == INVALID_HANDLE_VALUE) DR_ASSERT_MSG(false, "error connecting to pipe");
}

static void
setup_shmem() {
   HANDLE map_file;

   map_file = OpenFileMapping(
                   FILE_MAP_ALL_ACCESS,   // read/write access
                   FALSE,                 // do not inherit the name
                   options.shm_name);            // name of mapping object

   if (map_file == NULL) DR_ASSERT_MSG(false, "error accesing shared memory");

   winafl_data.afl_area = (unsigned char *) MapViewOfFile(map_file, // handle to map object
               FILE_MAP_ALL_ACCESS,  // read/write permission
               0,
               0,
               MAP_SIZE);

   if (winafl_data.afl_area == NULL) DR_ASSERT_MSG(false, "error accesing shared memory");
}

static void
options_init(client_id_t id, int argc, const char *argv[])
{
    int i;
    const char *token;
    target_module_t *target_modules;
    /* default values */
    options.nudge_kills = true;
    options.debug_mode = false;
    options.coverage_kind = COVERAGE_BB;
    options.target_modules = NULL;
    options.fuzz_module[0] = 0;
    options.fuzz_method[0] = 0;
    options.fuzz_offset = 0;
    options.fuzz_iterations = 1000;
    options.func_args = NULL;
    options.num_fuz_args = 0;
    options.callconv = DRWRAP_CALLCONV_DEFAULT;
#ifdef _WMP
	options.messageid[0] = -1;
	options.timeout = g_WaitTimeMs; // Default timeout 
#endif
    dr_snprintf(options.logdir, BUFFER_SIZE_ELEMENTS(options.logdir), ".");

    strcpy(options.pipe_name, "\\\\.\\pipe\\afl_pipe_default");
    strcpy(options.shm_name, "afl_shm_default");

    for (i = 1/*skip client*/; i < argc; i++) {
        token = argv[i];
        if (strcmp(token, "-no_nudge_kills") == 0)
            options.nudge_kills = false;
        else if (strcmp(token, "-nudge_kills") == 0)
            options.nudge_kills = true;
        else if (strcmp(token, "-debug") == 0)
            options.debug_mode = true;
        else if (strcmp(token, "-logdir") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing logdir path");
            strncpy(options.logdir, argv[++i], BUFFER_SIZE_ELEMENTS(options.logdir));
        }
        else if (strcmp(token, "-fuzzer_id") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing fuzzer id");
            strcpy(options.pipe_name, "\\\\.\\pipe\\afl_pipe_");
            strcpy(options.shm_name, "afl_shm_");
            strcat(options.pipe_name, argv[i+1]);
            strcat(options.shm_name, argv[i+1]);
            i++;
        }
        else if (strcmp(token, "-covtype") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing coverage type");
            token = argv[++i];
            if(strcmp(token, "bb")==0) options.coverage_kind = COVERAGE_BB;
            else if (strcmp(token, "edge")==0) options.coverage_kind = COVERAGE_EDGE;
            else USAGE_CHECK(false, "invalid coverage type");
        }
        else if (strcmp(token, "-coverage_module") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing module");
            target_modules = options.target_modules;
            options.target_modules = (target_module_t *)dr_global_alloc(sizeof(target_module_t));
            options.target_modules->next = target_modules;
            strncpy(options.target_modules->module_name, argv[++i], BUFFER_SIZE_ELEMENTS(options.target_modules->module_name));
        }
        else if (strcmp(token, "-target_module") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing module");
            strncpy(options.fuzz_module, argv[++i], BUFFER_SIZE_ELEMENTS(options.fuzz_module));
        }
        else if (strcmp(token, "-target_method") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing method");
            strncpy(options.fuzz_method, argv[++i], BUFFER_SIZE_ELEMENTS(options.fuzz_method));
        }
        else if (strcmp(token, "-fuzz_iterations") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing number of iterations");
            options.fuzz_iterations = atoi(argv[++i]);
        }
        else if (strcmp(token, "-nargs") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing number of arguments");
            options.num_fuz_args = atoi(argv[++i]);
        }
        else if (strcmp(token, "-target_offset") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing offset");
            options.fuzz_offset = strtoul(argv[++i], NULL, 0);
        }
        else if (strcmp(token, "-verbose") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing -verbose number");
            token = argv[++i];
            if (dr_sscanf(token, "%u", &verbose) != 1) {
                USAGE_CHECK(false, "invalid -verbose number");
            }
        }
        else if (strcmp(token, "-call_convention") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing calling convention");
            ++i;
            if (strcmp(argv[i], "stdcall") == 0)
                options.callconv = DRWRAP_CALLCONV_CDECL;
            else if (strcmp(argv[i], "fastcall") == 0)
                options.callconv = DRWRAP_CALLCONV_FASTCALL;
            else if (strcmp(argv[i], "thiscall") == 0)
                options.callconv = DRWRAP_CALLCONV_THISCALL;
            else if (strcmp(argv[i], "ms64") == 0)
                options.callconv = DRWRAP_CALLCONV_MICROSOFT_X64;
            else
                NOTIFY(0, "Unknown calling convention, using default value instead.\n");
        }
#ifdef _WMP
		else if (strcmp(token, "-message_id") == 0) {
			USAGE_CHECK((i + 1) < argc, "missing -message_id");
			/*
			*	A message id is typically used by event-based GUI software
			*	You can select a message id that will trigger the file to be parsed
			*   You can specify more than one message id using comma (",") as separator
			*	(For example: On Windows Media Player, WMI_TIMER (0x8000) is triggered
			*                 continuously)
			*/
			int size = strlen(argv[i+1]);
			char *msg_ids = (char*)dr_global_alloc(size+1);
			memset(msg_ids, 0, size+1);
			strncpy(msg_ids, argv[i+1], size);
			char *p = msg_ids, *start_s = msg_ids;
			int id = 0;

			if (strrchr(msg_ids, ',') != NULL)
			{
				while (1)
				{
					if (*p == ',' || *p == '\0')
					{
						*p = '\0';
						options.messageid[id++] = atoi(start_s);
						// Set the start string to next p
						start_s = p + 1;
						//id++;
					}

					if (p++ >= (msg_ids + size + 1))
						break;
				}
			}
			else
			{
				options.messageid[id] = atoi(start_s);
			}
			dr_global_free(msg_ids, size+1);
			i++;
		}
		else if (strcmp(token, "-input_filename") == 0) {
			USAGE_CHECK((i + 1) < argc, "missing -input_filename file path");
			/*
			*  *MUST* be the same as -t option in afl-fuzz
			*/
			fuzz_target.cur_input = (char *)dr_global_alloc(MAXIMUM_PATH);
			memset(fuzz_target.cur_input, 0, MAXIMUM_PATH);
			strncpy(fuzz_target.cur_input, argv[++i], MAXIMUM_PATH);
		}
		else if (strcmp(token, "-timeout") == 0) {
			/*
			*	Equivalent to '-t' option under afl-fuzz
			*/
			USAGE_CHECK((i + 1) < argc, "missing timetout");
			options.timeout = strtoul(argv[++i], NULL, 0);
		}
#endif
        else {
            NOTIFY(0, "UNRECOGNIZED OPTION: \"%s\"\n", token);
            USAGE_CHECK(false, "invalid option");
        }
    }

    if(options.fuzz_module[0] && (options.fuzz_offset == 0) && (options.fuzz_method[0] == 0)) {
       USAGE_CHECK(false, "If fuzz_module is specified, then either fuzz_method or fuzz_offset must be as well");
    }

    if(options.num_fuz_args) {
        options.func_args = (void **)dr_global_alloc(options.num_fuz_args * sizeof(void *));
    }
}

DR_EXPORT void
dr_client_main(client_id_t id, int argc, const char *argv[])
{
    drreg_options_t ops = {sizeof(ops), 3 /*max slots needed: aflags*/, false};

    dr_set_client_name("WinAFL", "");

	if (!drmgr_init() || !drx_init() || !drwrap_init() || drreg_init(&ops) != DRREG_SUCCESS)
		DR_ASSERT(false);

    options_init(id, argc, argv);

    dr_register_exit_event(event_exit);

    drmgr_register_exception_event(onexception);

	if (options.coverage_kind == COVERAGE_BB) {
		drmgr_register_bb_instrumentation_event(NULL, instrument_bb_coverage, NULL);
	}
	else if (options.coverage_kind == COVERAGE_EDGE) {
		drmgr_register_bb_instrumentation_event(NULL, instrument_edge_coverage, NULL);
	}

	drmgr_register_module_load_event(event_module_load);
	drmgr_register_module_unload_event(event_module_unload);
	dr_register_nudge_event(event_nudge, id);

    client_id = id;

    if (options.nudge_kills)
        drx_register_soft_kills(event_soft_kill);

    if(!options.debug_mode) {
        setup_pipe();
        setup_shmem();
    }
    else {
        winafl_data.afl_area = (unsigned char *)dr_global_alloc(MAP_SIZE);
    }

    event_init();
}
