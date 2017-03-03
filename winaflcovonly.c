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
#include <windows.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>
#include <tlhelp32.h>

time_t start_time, end_time;

#define UNKNOWN_MODULE_ID USHRT_MAX
#define FILE_REP_PATTERN_A "@@"
#define FILE_REP_PATTERN_W L"@@"

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

#ifdef _DEBUG
#define DEBUG_PRINT dbgprint        
#else 
#define DEBUG_PRINT
#endif

// Make it optional for GUI-based software (eg: Microsoft Office or Windows Media Player)
#ifdef _WMP
#define MAXIMUM_MESSAGE_IDS 256
BOOL	g_BoolShouldProceed = false;
/*	Maximum wait time (ms) for the next input iteration.
*	Must be smaller than client time-out value specified
*	in afl-fuzz CreateNamePipe function and also exec_tmout
*	(using -t option)
*/
UINT64	g_WaitTimeMs = 10000; 
// This is a maximum count of continuous message id hit by GetMessage API
int		g_MaxCountMessageIdOccurred = 1000;
#endif

#define OPTION_MAX_LENGTH MAXIMUM_PATH
#define UNICODE_MAX_PATH sizeof(wchar_t)*MAXIMUM_PATH
#define COVERAGE_BB 0
#define COVERAGE_EDGE 1

typedef struct _target_module_t {
    char module_name[MAXIMUM_PATH];
    int mod_id;
#ifdef _WIN64
    uint64_t base;
#else
    uint base;
#endif
    bool marked_to_log;
    struct _target_module_t *next;
} target_module_t;

typedef struct _input_corpus_t {
    char dir_name[MAXIMUM_PATH];
    bool processed_dir;
    struct _input_corpus_t *next;
} input_corpus_t;

typedef struct _file_list_t {
    char file_name[MAXIMUM_PATH];
    struct _file_list_t *next;
} file_list_t;

file_list_t *g_filelist = NULL;

/* Data structure for BB info per-thread */
typedef struct _per_thread_t {
    void *bb_table;
    file_t  log;
    char logname[MAXIMUM_PATH];
} per_thread_t;

static per_thread_t *global_data;
static int tls_idx = -1;

/* Data structure for the coverage info itself */
typedef struct _bb_entry_t {
    uint   start;      /* offset of bb start from the image base */
    ushort size;
    ushort mod_id;
} bb_entry_t;

typedef struct _winafl_option_t {
    /* Use nudge to notify the process for termination so that
     * event_exit will be called.
     */
    bool nudge_kills;
    bool debug_mode;
	bool single_test_case;
    int coverage_kind;
    char logdir[MAXIMUM_PATH];
    char covlogdir[MAXIMUM_PATH];
    target_module_t *target_modules;
    input_corpus_t *corpus_list;
    //char instrument_module[MAXIMUM_PATH];
    char fuzz_module[MAXIMUM_PATH];
    char fuzz_method[MAXIMUM_PATH];
    char pipe_name[MAXIMUM_PATH];
    char shm_name[MAXIMUM_PATH];
    unsigned long fuzz_offset;
    int cov_iterations;
    void **func_args;
    int num_fuz_args;
    int file_arg_index;
#ifdef _WMP
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

typedef struct _cov_target_t {
    reg_t xsp;            /* stack level at entry to the fuzz target */
	reg_t xcx;            /* stack level at entry to the fuzz target */
    app_pc func_pc;
    char *cur_input;      /* Current test case file name obtained from g_filelist */
    char *cur_covlog;
    file_t  log;
    int bcrashed;
    int iteration;
} cov_target_t;
static cov_target_t cov_target;

typedef struct _resume_cov_t {
    dr_mcontext_t *mc;
}resume_cov_t;
static resume_cov_t redirect_cov;

typedef struct _debug_data_t {
    int pre_handler_called;
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
int get_parent_pid()
{
    HANDLE hSnapshot;
    PROCESSENTRY32 pe32;
    DWORD ppid = 0, pid = dr_get_process_id();

    hSnapshot = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0);
    __try{
        if (hSnapshot == INVALID_HANDLE_VALUE) __leave;

        ZeroMemory(&pe32, sizeof(pe32));
        pe32.dwSize = sizeof(pe32);
        if (!Process32First(hSnapshot, &pe32)) __leave;

        do{
            if (pe32.th32ProcessID == pid){
                ppid = pe32.th32ParentProcessID;
                break;
            }
        } while (Process32Next(hSnapshot, &pe32));

    }
    __finally{
        if (hSnapshot != INVALID_HANDLE_VALUE) CloseHandle(hSnapshot);
    }
    return ppid;
}

/* Get current time in milliseconds */
static uint64 get_cur_time(void) {

	uint64 ret;
	FILETIME filetime;
	GetSystemTimeAsFileTime(&filetime);

	ret = (((uint64)filetime.dwHighDateTime) << 32) + (uint64)filetime.dwLowDateTime;

	return ret / 10000;

}

static char *
get_cov_result_filenameA(IN char *testcase_name)
{
    char *filename = NULL;
    
    if (filename = strrchr(testcase_name, '\\'))
    {
        return filename+1;
    }

    return testcase_name;
}

static wchar_t *
get_cov_result_filenameW(IN wchar_t *testcase_name)
{
    char test_case[MAXIMUM_PATH] = { 0 };
    wchar_t *filename = NULL;

    wcstombs(test_case, (const wchar_t*)testcase_name, MAXIMUM_PATH);
    if (filename = wcsrchr(testcase_name, L'\\'))
    {
        return filename+1;
    }

    return testcase_name;
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
static bool
onexception(void *drcontext, dr_exception_t *excpt) {
    DWORD num_written;
    DWORD exception_code = excpt->record->ExceptionCode;

	if (options.debug_mode)
		dr_fprintf(winafl_data.log, "Exception caught: %x\n", exception_code);

    if((exception_code == EXCEPTION_ACCESS_VIOLATION) || (exception_code == EXCEPTION_ILLEGAL_INSTRUCTION) ||
       (exception_code == EXCEPTION_PRIV_INSTRUCTION) || (exception_code == EXCEPTION_STACK_OVERFLOW)) 
    {
        //__debugbreak();
        // Redirect execution to our specified start function
		if (options.debug_mode)
			dr_fprintf(winafl_data.log, "crashed at %08x\n", excpt->mcontext->pc);
        dr_fprintf(cov_target.log, "crashed at %08x\n", excpt->mcontext->pc);
        if (options.corpus_list)
        {
            excpt->mcontext->xsp = cov_target.xsp;
            excpt->mcontext->pc = cov_target.func_pc;
            cov_target.bcrashed = (bool)true;
            dr_redirect_execution(excpt->mcontext);
            DR_ASSERT_MSG(false, "should not reach here");
        }
        else
            dr_exit_process(1);
    }
    return true;
}

uint64 start_instru_ms = 0; /* A time to indicate when the last instrumentation was started (ms) */
static dr_emit_flags_t
event_basic_block_analysis(void *drcontext, void *tag, instrlist_t *bb,
bool for_trace, bool translating, OUT void **user_data)
{
    per_thread_t *data;
    instr_t *instr;
    app_pc start_pc, end_pc;
    module_entry_t **mod_entry_cache;
    module_entry_t *mod_entry;
    const char *module_name;
    uint offset;
    target_module_t *target_modules;
    bool should_instrument;
    int mod_index = 0;
    start_pc = dr_fragment_app_pc(tag);

    //DEBUG_PRINT("%s:%d:%s: Pre BB hit at block %08x (translating:%d)\n", __FUNCTION__, __LINE__, cov_target.cur_covlog, start_pc, translating);

    /* do nothing for translation */
    if (translating)
        return DR_EMIT_DEFAULT;

    //start_pc = dr_fragment_app_pc(tag);
    mod_entry_cache = winafl_data.cache;
    mod_entry = module_table_lookup(mod_entry_cache, NUM_THREAD_MODULE_CACHE, module_table, start_pc);

    if (mod_entry == NULL || mod_entry->data == NULL) return DR_EMIT_DEFAULT;

    module_name = dr_module_preferred_name(mod_entry->data);
    should_instrument = false;
    target_modules = options.target_modules;

    while (target_modules) {
        if (_stricmp(module_name, target_modules->module_name) == 0) {
            should_instrument = true;
            break;
        }
        target_modules = target_modules->next;
    }

    /* Skip instrument as well if coverage log is not ready
    *  and coverage log is ready when our instrumented function
    *  is started. In other words, we have more optimized coverage
    *  as those the program stub code (eg: MSVCR code) will be skipped
    *  gracefully
    */
    if (cov_target.log == NULL) should_instrument = false;

    if (!should_instrument) return DR_EMIT_DEFAULT;

	/*
	*  Get the start time of the instrumentation
	*  that can be used to determine if we should start
	*  next input
	*/
	start_instru_ms = get_cur_time();

    /* Collect the number of instructions and the basic block size,
    * assuming the basic block does not have any elision on control
    * transfer instructions, which is true for default options passed
    * to DR but not for -opt_speed.
    */
    end_pc = start_pc; /* for finding the size */
    offset = (uint)(start_pc - mod_entry->data->start);
    for (instr = instrlist_first_app(bb);
        instr != NULL;
        instr = instr_get_next_app(instr)) {
        app_pc pc = instr_get_app_pc(instr);
        int len = instr_length(drcontext, instr);
        /* -opt_speed (elision) is not supported */
        ASSERT(pc != NULL && pc >= start_pc, "-opt_speed is not supported");
        if (pc + len > end_pc)
            end_pc = pc + len;
    }
  
    /*
    *  Analyzer required the module information for post processing later
    */
    if (!target_modules->marked_to_log)
    {
        char buff_modentry[4096] = { 0 };
        dr_snprintf(buff_modentry, BUFFER_SIZE_ELEMENTS(buff_modentry), "%s|%02d\n", module_name, mod_entry->id);
        dr_write_file(cov_target.log, buff_modentry, strlen(buff_modentry));
        target_modules->marked_to_log = true;
    }

    char bb_entry[4096] = { 0 };
#ifdef _WIN64
    dr_snprintf(bb_entry, BUFFER_SIZE_ELEMENTS(bb_entry), "%d|%I64x\n", mod_entry->id, offset);
#else
    dr_snprintf(bb_entry, BUFFER_SIZE_ELEMENTS(bb_entry), "%d|%08x\n", mod_entry->id, offset);
#endif
    //DEBUG_PRINT("%s:%d:%s: Post BB hit at block %08x\n", __FUNCTION__, __LINE__, cov_target.cur_covlog, offset);
    dr_write_file(cov_target.log, bb_entry, strlen(bb_entry));



    return DR_EMIT_DEFAULT;
}

static void
helper_prepare_cov_log()
{
	char cur_cov_log[MAXIMUM_PATH] = { 0 };
	cov_target.log = NULL;

	if (cov_target.cur_covlog == NULL)
	{
		cov_target.cur_covlog = (char*)dr_global_alloc(MAXIMUM_PATH);
	}

	if (options.corpus_list || g_filelist)
		cov_target.cur_input = g_filelist->file_name;

	// Some safety check
	DR_ASSERT_MSG(cov_target.cur_covlog != NULL, "Something wrong with coverage log dir");
	DR_ASSERT_MSG(cov_target.cur_input != NULL, "Current input is empty");

	// Setup current input filename and the associated coverage log filename
	memset(cov_target.cur_covlog, 0, MAXIMUM_PATH);

	// Get the coverage log filename ready and open it for witting
	strncpy(cur_cov_log, get_cov_result_filenameA(cov_target.cur_input), MAXIMUM_PATH);
	cov_target.log = drx_open_unique_file(options.covlogdir, cur_cov_log, "cov.result", DR_FILE_ALLOW_LARGE, cov_target.cur_covlog, MAXIMUM_PATH);

	// Some safety check
	DR_ASSERT_MSG(cov_target.log != INVALID_FILE, "Unable to create coverage log file");

	DEBUG_PRINT("%s:%d: Initialized covlog: %s\n", __FUNCTION__, __LINE__, cov_target.cur_covlog);
}

static void
helper_next_cov_log()
{
	if (!options.single_test_case)
	{
		DEBUG_PRINT("%s:%d: Closed cur_input: %s (iter:%d, cov_iter: %d)\n", __FUNCTION__, __LINE__, cov_target.cur_covlog, cov_target.iteration, options.cov_iterations);
		
		if (cov_target.cur_input != NULL)
			dr_global_free(cov_target.cur_input, MAXIMUM_PATH);

		cov_target.cur_input = NULL;

		// Next input corpus
		if (options.corpus_list)
			g_filelist = g_filelist->next;
	}
	else
	{
		cov_target.cur_input = g_filelist->file_name;
	}
}

static void
pre_fuzz_handler(void *wrapcxt, INOUT void **user_data)
{
    int i;
    DWORD num_read;
	
    app_pc target_to_cov = drwrap_get_func(wrapcxt);
    dr_mcontext_t *mc = drwrap_get_mcontext_ex(wrapcxt, DR_MC_ALL);

    /* Initialize coverage information */
    cov_target.xsp = mc->xsp;
	cov_target.xcx = mc->xcx;
    cov_target.func_pc = target_to_cov;

    debug_data.pre_handler_called++;
    if (options.debug_mode)
        dr_fprintf(winafl_data.log, "In pre_fuzz_handler: 0x%08x\n", target_to_cov);

    //save or restore arguments
    if (cov_target.iteration == 0) {
        for(i = 0; i < options.num_fuz_args; i++) {
            options.func_args[i] = drwrap_get_arg(wrapcxt, i);
            if (options.debug_mode)
			    dr_fprintf(winafl_data.log, "get arg(%d): 0x%x\n", i, options.func_args[i]);
        }
    } else {
        for(i = 0; i < options.num_fuz_args; i++) {
            if(options.file_arg_index && options.corpus_list)
                options.func_args[options.file_arg_index - 1] = g_filelist->file_name;
            if (options.debug_mode)
			    dr_fprintf(winafl_data.log, "set arg(%d): 0x%x\n", i, options.func_args[i]);
            drwrap_set_arg(wrapcxt, i, options.func_args[i]);
        }
    }

	/*
	* As soon as the target function is started, we should get the coverage log ready,
	* otherwise, we might miss some BB
	* g_filelist pointer will be adjusted in post-callback function
	*/
	helper_prepare_cov_log();
    winafl_data.previous_offset = 0;
}

static void
post_fuzz_handler(void *wrapcxt, void *user_data)
{
    DWORD num_written;
    dr_mcontext_t *mc = drwrap_get_mcontext(wrapcxt);
	app_pc addr = drwrap_get_func(wrapcxt);

    debug_data.post_handler_called++;
    if (options.debug_mode)
        dr_fprintf(winafl_data.log, "In post_fuzz_handler: 0x%08x\n", addr);

    cov_target.iteration++;
    if (cov_target.iteration == options.cov_iterations) {
        DEBUG_PRINT("%s:%d: Exit Winaflcov\n", __FUNCTION__, __LINE__);
        dr_exit_process(0);
    }

	helper_next_cov_log();

	mc->xsp = cov_target.xsp;
	mc->xcx = cov_target.xcx;
	mc->pc = cov_target.func_pc;
	drwrap_redirect_execution(wrapcxt);

}

static void
createfilew_interceptor(void *wrapcxt, INOUT void **user_data)
{
    wchar_t *filenamew = (wchar_t *)drwrap_get_arg(wrapcxt, 0);
    
    /* Replace "@@" with our corpus file */
    if (filenamew && get_cov_result_filenameW(filenamew)[0] == L'@' && get_cov_result_filenameW(filenamew)[1] == L'@' && g_filelist)
    {
        *user_data = (wchar_t *)dr_global_alloc(UNICODE_MAX_PATH);
        mbstowcs(*user_data, g_filelist->file_name, UNICODE_MAX_PATH);
        drwrap_set_arg(wrapcxt, 0, *user_data);
        
        if (options.debug_mode)
            dr_fprintf(winafl_data.log, "In OpenFileW, reading %ls (replaced)\n", *user_data);
    }
    else if(options.debug_mode)
        dr_fprintf(winafl_data.log, "In OpenFileW, reading %ls\n", filenamew);
}

static void
createfilew_interceptor_post(void *wrapcxt, void *user_data)
{
    // Free the allocated buffer
    if (user_data)
        dr_global_free(user_data, UNICODE_MAX_PATH);

    user_data = NULL;
}

static void
createfilea_interceptor(void *wrapcxt, INOUT void **user_data)
{
    char *filename = (char *)drwrap_get_arg(wrapcxt, 0);

    /* Replace "@@" with our corpus file */
    if (filename && get_cov_result_filenameA(filename)[0] == '@' && get_cov_result_filenameA(filename)[1] == '@' && g_filelist)
    {
        drwrap_set_arg(wrapcxt, 0, g_filelist->file_name);
        
        if (options.debug_mode)
            dr_fprintf(winafl_data.log, "In OpenFileA, reading %s (replaced)\n", g_filelist->file_name);

    }
    else if(options.debug_mode)
        dr_fprintf(winafl_data.log, "In OpenFileA, reading %s\n", filename);
}

static void
messagebox_interceptor(void *wrapcxt, INOUT void **user_data)
{
    /* Always return IDOK */
    //__debugbreak();
    bool res = drwrap_skip_call(wrapcxt, (int *)IDOK, sizeof(void*) * 5);
    if (options.debug_mode)
        dr_fprintf(winafl_data.log, "Skipped MessageBoxExAorW\n");
    DEBUG_PRINT("%s:%d: drwrap_skip_call: %d\n", __FUNCTION__, __LINE__, res);
    
}

static void
dialogboxidnirectparam_interceptor(void *wrapcxt, INOUT void **user_data)
{
    //__debugbreak();
    bool res = drwrap_skip_call(wrapcxt, (int *)-1, sizeof(void*) * 6);
    if (options.debug_mode)
        dr_fprintf(winafl_data.log, "Skipped DialogBoxIndirectParamAorW\n");
    DEBUG_PRINT("%s:%d: drwrap_skip_call: %d\n", __FUNCTION__, __LINE__, res);

}

static void
getmessage_interceptor_pre(void *wrapcxt, INOUT void **user_data)
{
	MSG* msg = (MSG*)drwrap_get_arg(wrapcxt, 0);
	*user_data = (MSG*)msg;
}


#ifdef _WMP
#define MAX_PARAMETER 32768
static void
helper_start_wmp()
{

		char szWMPlayer[MAX_PATH] = { 0 };
		char szParameter[MAX_PARAMETER] = { 0 };
		STARTUPINFOA si;
		PROCESS_INFORMATION pi;
		memset(&si, 0, sizeof(STARTUPINFOA));
		memset(&pi, 0, sizeof(PROCESS_INFORMATION));
		si.cb = sizeof(STARTUPINFOA);

		ExpandEnvironmentStringsA("%PROGRAMFILES%\\Windows Media Player\\wmplayer.exe", szWMPlayer, MAX_PATH);
		dr_snprintf(szParameter, BUFFER_SIZE_ELEMENTS(szParameter), "\"%s\" %s", szWMPlayer, cov_target.cur_input);
		CreateProcessA(szWMPlayer, szParameter, NULL, NULL, FALSE, CREATE_NEW_CONSOLE, NULL, NULL, &si, &pi);
}

static void
getmessage_interceptor_post(void *wrapcxt, void *user_data)
{
	MSG* msg = (MSG*)user_data;

	// Proceed only when GetMessage call is successful
	if ((unsigned int)drwrap_get_retval(wrapcxt) != -1)
	{
		// Message we want to intercept so that we will proceed to the next input
		DR_ASSERT_MSG(options.messageid[0] != -1, "Options message_id is empty");
		if (msg != NULL)
		{
			if (cov_target.iteration == options.cov_iterations) {
				DEBUG_PRINT("%s:%d: Finished %d iteration\n", __FUNCTION__, __LINE__, options.cov_iterations);
				dr_exit_process(0);
			}

			DEBUG_PRINT("%s:%d: Message: 0x%x\n", __FUNCTION__, __LINE__, msg->message);

			for (int i = 0; i < MAXIMUM_MESSAGE_IDS; i++)
			{
				if (msg->message == options.messageid[i])
				{
					helper_prepare_cov_log();
				}
			}

			if (start_instru_ms > 0 && get_cur_time() > start_instru_ms + g_WaitTimeMs)
			{
				DEBUG_PRINT("%s:%d: Threshold met\n", __FUNCTION__, __LINE__);
				start_instru_ms = 0;
				helper_start_wmp();
				helper_next_cov_log();
				cov_target.iteration++;
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
    const char *module_name = dr_module_preferred_name(info);
    app_pc to_wrap;

	if (options.debug_mode)
		dr_fprintf(winafl_data.log, "#%d Module loaded, %s, Loaded address: 0x%x\n", mod_index, module_name, info->start);

    if(options.fuzz_module[0]) {
        if(_stricmp(module_name, options.fuzz_module) == 0) {
            if(options.fuzz_offset) {
                to_wrap = info->start + options.fuzz_offset;
            } else {
				to_wrap = (app_pc)dr_get_proc_address(info->handle, options.fuzz_method);
                DR_ASSERT_MSG(to_wrap, "Can't find specified method in fuzz_module");
            }
            drwrap_wrap(to_wrap, pre_fuzz_handler, post_fuzz_handler);
        }
    
        if(_stricmp(module_name, "KERNEL32.dll") == 0) {
            to_wrap = (app_pc)dr_get_proc_address(info->handle, "CreateFileW");
            drwrap_wrap(to_wrap, createfilew_interceptor, createfilew_interceptor_post);
            to_wrap = (app_pc)dr_get_proc_address(info->handle, "CreateFileA");
            drwrap_wrap(to_wrap, createfilea_interceptor, NULL);
        }

        if (_stricmp(module_name, "USER32.dll") == 0) {
            to_wrap = (app_pc)dr_get_proc_address(info->handle, "MessageBoxExW");
            drwrap_wrap(to_wrap, messagebox_interceptor, NULL);
            to_wrap = (app_pc)dr_get_proc_address(info->handle, "MessageBoxExA");
            drwrap_wrap(to_wrap, messagebox_interceptor, NULL);
            to_wrap = (app_pc)dr_get_proc_address(info->handle, "DialogBoxIndirectParamAorW");
            drwrap_wrap(to_wrap, dialogboxidnirectparam_interceptor, NULL);
        }

    }

    if (options.target_modules)
    {
        target_module_t *target_module = options.target_modules;
        while (target_module)
        {   
            if (_stricmp(module_name, target_module->module_name))
            {
                target_module->mod_id = mod_index;
#ifdef _WIN64
                target_module->base = (uint64_t)info->start;
#else
                target_module->base = (uint)info->start;
#endif
                break;
            }
            target_module = target_module->next;
        }

    }

    /* We keep track of the module ID our own */
    mod_index++;
    module_table_load(module_table, info);
}

static void
event_exit(void)
{
    if (options.debug_mode && debug_data.pre_handler_called == 0) {
        dr_fprintf(winafl_data.log, "WARNING: Target function was never called. Incorrect target_offset?\n");
    }
	else if (options.debug_mode && debug_data.post_handler_called == 0) {
        dr_fprintf(winafl_data.log, "WARNING: Post-fuzz handler was never reached. Did the target function return normally?\n");
    }
	else if (options.debug_mode){
        dr_fprintf(winafl_data.log, "Everything appears to be running normally.\n");
    }

    /* destroy module table */
    module_table_destroy(module_table);

    /* Show elapsed time */
    double elapsed;
    end_time = time(NULL);
    elapsed = difftime(end_time, start_time);
	if (options.debug_mode)
	{
		if (elapsed < 60)
			dr_fprintf(winafl_data.log, "Elapsed time: %.2f seconds\n", elapsed);
		else if (elapsed > 60 && elapsed < 60 * 60)
			dr_fprintf(winafl_data.log, "Elapsed time: %.2f minutes\n", (elapsed / 60));
		else if (elapsed > 60 * 60 && elapsed < 60 * 60 * 24)
			dr_fprintf(winafl_data.log, "Elapsed time: %.2f hours\n", (elapsed / 60 / 60));
		else
			dr_fprintf(winafl_data.log, "Elapsed time: ~%d days\n", ceil(elapsed / 60 / 60 / 24));
		dr_close_file(winafl_data.log);
	}
    drx_exit();
    drmgr_exit();
}

static void
event_init(void)
{
    char buf[MAXIMUM_PATH];

    module_table = module_table_create();

	memset(winafl_data.cache, 0, sizeof(winafl_data.cache));

    winafl_data.previous_offset = 0;

    if(options.debug_mode) {
        debug_data.pre_handler_called = 0;
        debug_data.post_handler_called = 0;

        winafl_data.log =
            drx_open_unique_appid_file(options.logdir, get_parent_pid(),
                                   "winaflcov", "proc.log",
                                   DR_FILE_ALLOW_LARGE,
                                   buf, BUFFER_SIZE_ELEMENTS(buf));
        if (winafl_data.log != INVALID_FILE) {
            dr_log(NULL, LOG_ALL, 1, "winaflcov: log file is %s\n", buf);
            NOTIFY(1, "<created log file %s>\n", buf);
        }
    }

    /* Coverage target initialization */
    cov_target.iteration = 0;
    cov_target.cur_covlog = NULL;    
    cov_target.log = NULL;
}

// -----------------------------------------------------------------------
/*
	thread_close_nuidialog
	Watchdog thread to monitor and close NUIDialog
	Refer Cuckoo's auxiliary human.py
*/
// -----------------------------------------------------------------------
static void WINAPIV
thread_close_nuidialog(void *context)
{
	HWND hWnd = NULL;
	char *lpszClassName = "NUIDialog";
	DEBUG_PRINT("%s:%d: Watchdog thread entry point\n", __FUNCTION__, __LINE__);
	while (1)
	{
		hWnd = FindWindowA(lpszClassName, NULL);
		DEBUG_PRINT("%s:%d: FindWindowA: 0x%x\n", __FUNCTION__, __LINE__, hWnd);
		if (hWnd != NULL)
		{
			char *lpszWindowText = (char*)dr_global_alloc(256);

			if (GetWindowTextA(hWnd, (char*)lpszWindowText, 256))
			{
				if (lpszWindowText[0] == 'M' && lpszWindowText[1] == 'i' &&
					lpszWindowText[2] == 'c' && lpszWindowText[3] == 'r' &&
					lpszWindowText[4] == 'o' && lpszWindowText[5] == 's' &&
					lpszWindowText[6] == 'o' && lpszWindowText[7] == 'f' &&
					lpszWindowText[8] == 't')
				{
					// Set focus to NUIDialog Window
					SetForegroundWindow(hWnd);
					// Animate keyboard to click
					keybd_event(VK_RETURN, 0x1C /*ENTER*/, 0, 0);
					keybd_event(VK_RETURN, 0x1C /*ENTER*/, KEYEVENTF_KEYUP, 0);
				}
			}
			else
			{
				DR_ASSERT_MSG(false, "Failed GetWindowText");
			}

			dr_global_free(lpszWindowText, 256);
			hWnd = NULL;
			lpszWindowText = NULL;
		}
		dr_sleep(1000);
	}

	return;
}

static void
options_init(client_id_t id, int argc, const char *argv[])
{
    int i;
    const char *token;
    bool set_index_arg = false;
    target_module_t *target_modules;
    input_corpus_t *corpus_dirs;
    /* default values */
    options.nudge_kills = true;
    options.debug_mode = false;
    options.coverage_kind = COVERAGE_BB;
    options.target_modules = NULL;
    options.corpus_list = NULL;
    options.fuzz_module[0] = 0;
    options.fuzz_method[0] = 0;
    options.fuzz_offset = 0;
#ifdef _WMP
	options.messageid[0] = -1;
#endif
    options.cov_iterations = 1;
    options.func_args = NULL;
    options.file_arg_index = 0;
    options.num_fuz_args = 0;
	options.single_test_case = false;
    dr_snprintf(options.logdir, BUFFER_SIZE_ELEMENTS(options.logdir), ".");
    dr_snprintf(options.covlogdir, BUFFER_SIZE_ELEMENTS(options.covlogdir), ".");

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
        else if (strcmp(token, "-covlogdir") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing covlogdir path");
            strncpy(options.covlogdir, argv[++i], BUFFER_SIZE_ELEMENTS(options.covlogdir));
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
            options.target_modules->marked_to_log = false;
        }
        else if (strcmp(token, "-target_module") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing module");
            strncpy(options.fuzz_module, argv[++i], BUFFER_SIZE_ELEMENTS(options.fuzz_module));
        }
        else if (strcmp(token, "-target_method") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing method");
            strncpy(options.fuzz_method, argv[++i], BUFFER_SIZE_ELEMENTS(options.fuzz_method));
        }
        else if (strcmp(token, "-nargs") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing number of arguments");
            options.num_fuz_args = atoi(argv[++i]);
        }
        else if (strcmp(token, "-target_offset") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing offset");
            options.fuzz_offset = strtoul(argv[++i], NULL, 0);
        }
        else if (strcmp(token, "-cov_iterations") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing number of iterations");
            options.cov_iterations = atoi(argv[++i]);
        }
        else if (strcmp(token, "-verbose") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing -verbose number");
            token = argv[++i];
            if (dr_sscanf(token, "%u", &verbose) != 1) {
                USAGE_CHECK(false, "invalid -verbose number");
            }
        }
        else if (strcmp(token, "-file_arg_index") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing -file_arg_index number");
            options.file_arg_index = atoi(argv[++i]);
        }
        else if (strcmp(token, "-single_test_case") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing -single_test_case file path");
            /*
            *  A single test case should be used to perform code coverage
            */
            g_filelist = (file_list_t *)dr_global_alloc(sizeof(file_list_t));
            strncpy(g_filelist->file_name, argv[++i], BUFFER_SIZE_ELEMENTS(g_filelist->file_name));
            g_filelist->next = NULL;
			options.single_test_case = true;
        }
        else if (strcmp(token, "-list_input") == 0) {
            USAGE_CHECK((i + 1) < argc, "missing input corpus");
            int size = strlen(argv[++i]);
            char *list_input = (char*)dr_global_alloc(size);
            strncpy(list_input, argv[i], size);
            char *plist = list_input;
            char *tmpplist = plist;
            while ((plist = strchr(plist, ',')) || strlen(tmpplist) > 0)
            {
                if (plist)
                    *plist = '\0';
                corpus_dirs = options.corpus_list;
                options.corpus_list = (input_corpus_t *)dr_global_alloc(sizeof(input_corpus_t));
                options.corpus_list->next = corpus_dirs;
                options.corpus_list->processed_dir = false;
                strncpy(options.corpus_list->dir_name, tmpplist, BUFFER_SIZE_ELEMENTS(options.corpus_list->dir_name));
                if (!plist)
                    break;
                tmpplist = plist = plist + 1;
            }
			options.single_test_case = false;
            dr_global_free(list_input, size);

            // The number of coverage depends on the number of input corpus
            options.cov_iterations = 0;
        }
		else if (strcmp(token, "-human") == 0){
			/* Start watchdog thread */
			// FIXME: CreateThread call is successful, however the client thread is not started properly?
			// FIXED: Used dr_create_client_thread instead (ref: http://dynamorio.org/docs/dr__tools_8h.html#ac6b80b83502ff13d4674b13e7b30b555)
			dr_create_client_thread(thread_close_nuidialog, NULL);
			DEBUG_PRINT("%s:%d Started watchdog thread\n", __FUNCTION__, __LINE__);
		}
        else {
            NOTIFY(0, "UNRECOGNIZED OPTION: \"%s\"\n", token);
            USAGE_CHECK(false, "invalid option");
        }
    }

    if(options.fuzz_module[0] && (options.fuzz_offset == 0) && (options.fuzz_method[0] == 0)) {
       USAGE_CHECK(false, "If fuzz_module is specified, then either fuzz_method or fuzz_offset must be as well");
    }

	if ((options.single_test_case && options.corpus_list != NULL))
		USAGE_CHECK(false, "-single_test_case and -list_input should be mutual exclusive");

    if(options.num_fuz_args) {
        options.func_args = (void **)dr_global_alloc(options.num_fuz_args * sizeof(void *));
    }
}

// --------------------------------------------------------------------
/*
    filelist_init
    Get the list of test cases from initial corpus directory
    FIXME: If the number of test cases is big enough (eg: >15000),
           does it cause performance overhead?
*/
// --------------------------------------------------------------------
static void filelist_init()
{
    input_corpus_t *input_corpus = options.corpus_list;
    input_corpus_t *temp = NULL;
    file_list_t *test_case = NULL;

    while (input_corpus)
    {
        // Simple sanity check to make sure we are enumerating folder
        if (!dr_directory_exists(input_corpus->dir_name))
        {
            DEBUG_PRINT("%s:%d: It's not directory: %s\n", __FUNCTION__, __LINE__, input_corpus->dir_name);
            dr_exit_process(0);
        }

        // Make sure the input corpus is unique
        temp = input_corpus->next;
        while (temp)
        {
            if (strcmp(temp->dir_name, input_corpus->dir_name) == 0)
            {
                if (temp->next != NULL)
                {
                    dr_global_free(temp->dir_name, BUFFER_SIZE_ELEMENTS(options.corpus_list->dir_name));
                    input_corpus->next = temp->next;
                }
                else
                {
                    dr_global_free(temp->dir_name, BUFFER_SIZE_ELEMENTS(options.corpus_list->dir_name));
                    input_corpus->next = NULL;
                }
            }
            temp = temp->next;
        }

        // Init list of test cases that will be processed later
        {
            WIN32_FIND_DATA ffd;
            HANDLE hFind = INVALID_HANDLE_VALUE;
            hFind = FindFirstFile(input_corpus->dir_name, &ffd);

            if (hFind == INVALID_HANDLE_VALUE)
            {
                DEBUG_PRINT("%s:%d: Failed to open directory: %s (0x%d)\n", __FUNCTION__, __LINE__, input_corpus->dir_name, GetLastError());
                dr_exit_process(0);
            }

            do 
            {
                // Ignore the directory within the folder
                if (!(ffd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY))
                {
                    g_filelist = test_case;
                    test_case = (file_list_t*)dr_global_alloc(sizeof(file_list_t));
                    test_case->next = g_filelist;
                    strncpy(test_case->file_name, input_corpus->dir_name, MAXIMUM_PATH);
                    strcat(test_case->file_name, "\\");
                    strcat(test_case->file_name, ffd.cFileName);
                    DEBUG_PRINT("%s:%d: Filename: %s\n", __FUNCTION__, __LINE__, test_case->file_name);
                    // Number of coverage to be run depends on the number of input corpus
                    options.cov_iterations++;
                }
            } while (FindNextFile(hFind, &ffd) != 0);
            
            CloseHandle(hFind);
            // Don't miss the last file!
            g_filelist = test_case;
        }
        input_corpus->processed_dir = true;
        input_corpus = input_corpus->next;
    }
    DEBUG_PRINT("%s:%d: g_fiellist: 0x%x\n", __FUNCTION__, __LINE__, g_filelist);
    //options.cov_iterations--;
}

DR_EXPORT void
dr_client_main(client_id_t id, int argc, const char *argv[])
{
    drreg_options_t ops = {sizeof(ops), 2 /*max slots needed: aflags*/, false};

    start_time = time(NULL);

    dr_set_client_name("WinAFL", "");

    drmgr_init();
    drx_init();
    drreg_init(&ops);
    drwrap_init();

    options_init(id, argc, argv);

    if (options.corpus_list != NULL)
        filelist_init();
    dr_register_exit_event(event_exit);

    drmgr_register_exception_event(onexception);

	if (options.coverage_kind == COVERAGE_BB) {
		drmgr_register_bb_instrumentation_event(event_basic_block_analysis, NULL, NULL);
    }

    drmgr_register_module_load_event(event_module_load);
    drmgr_register_module_unload_event(event_module_unload);
    dr_register_nudge_event(event_nudge, id);

    client_id = id;

    if (options.nudge_kills)
        drx_register_soft_kills(event_soft_kill);


    tls_idx = drmgr_register_tls_field();
    if (tls_idx == -1)
    {
		if (options.debug_mode)
			dr_fprintf(winafl_data.log, "Failed to allocate TLS");
        return;
    }

    event_init();
    return;
}
