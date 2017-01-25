/* **********************************************************
* Copyright (c) 2014 Google, Inc.  All rights reserved.
* Copyright (c) 2003-2008 VMware, Inc.  All rights reserved.
* **********************************************************/

/*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*
* * Redistributions of source code must retain the above copyright notice,
*   this list of conditions and the following disclaimer.
*
* * Redistributions in binary form must reproduce the above copyright notice,
*   this list of conditions and the following disclaimer in the documentation
*   and/or other materials provided with the distribution.
*
* * Neither the name of VMware, Inc. nor the names of its contributors may be
*   used to endorse or promote products derived from this software without
*   specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
* AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
* IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
* ARE DISCLAIMED. IN NO EVENT SHALL VMWARE, INC. OR CONTRIBUTORS BE LIABLE
* FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
* DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
* SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
* CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
* LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
* OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
* DAMAGE.
*/

/* Code Manipulation API Sample:
* drexception.c
*
* Demonstrate exception interception using DBI
*/

#define _CRT_SECURE_NO_WARNINGS

#include "dr_api.h"
#include "drmgr.h"
#include "drx.h"
#include "drreg.h"
#include "drwrap.h"
#include "dr_events.h"
#include <windows.h>
#include <stdlib.h>

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

static void
event_exit(void);

static void
event_thread_exit(void *drcontext);

static bool
onexception(void *drcontext, dr_exception_t *excpt) 
{
	DWORD exception_code = excpt->record->ExceptionCode;
	DEBUG_PRINT("Exception caught: %x\n", exception_code);
	if ((exception_code == EXCEPTION_ACCESS_VIOLATION) ||
		(exception_code == EXCEPTION_ILLEGAL_INSTRUCTION) ||
		(exception_code == EXCEPTION_PRIV_INSTRUCTION) ||
		(exception_code == EXCEPTION_STACK_OVERFLOW)) {
		DEBUG_BREAK();
		DEBUG_PRINT("Crashed at %08x: %x\n", excpt->mcontext->pc);
		dr_exit_process(1);
	}
	return true;
}


static void
event_exit(void)
{
	drx_exit();
	drmgr_exit();
}

DR_EXPORT void
dr_client_main(client_id_t id, int argc, const char *argv[])
{
	drreg_options_t ops = { sizeof(ops), 2 /*max slots needed: aflags*/, false };

	dr_set_client_name("DRException", "");

	drmgr_init();
	drx_init();
	drreg_init(&ops);
	drwrap_init();

	dr_register_exit_event(event_exit);
	drmgr_register_exception_event(onexception);
}
