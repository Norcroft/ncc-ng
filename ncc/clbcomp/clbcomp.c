/*
 * ccomp/ccomp.c: callable compiler
 * Copyright (C) Advanced RISC Machines Limited, 1996.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

#include <signal.h>
#include "globals.h"    /* for errstate_init() */
#include "aetree.h"     /* aetree_init() */
#include "store.h"      /* alloc_initialise(); store for AEtree */
#include "bind.h"       /* bind_init(); namelookup */
#include "lex.h"        /* lex_init() */
#include "syn.h"        /* syn_init() */
#include "sem.h"        /* sem_init() */
#include "builtin.h"    /* built_init */
#include "compiler.h"   /* compiler_exit() */
#include "backchat.h"   /* BC_DIAGMSG, */
#include "simplify.h"
#include "aeops.h"
#include "defs.h"
#include "dump.h"
#include "clbcomp.h"

BackChatHandler backchat;

/* defined in arm/mcdep.c etc but really should be guarded by NO_CONFIG
   in the rest of the compiler */
int32 config;

/* Dummy definitions */
unsigned dump_state;
char *expr_string;
char *phasename;
struct CurrentFnDetails currentfunction;

Dump_LoadState dump_loadstate;

/* Hacked until the debug toolbox decided what to do with err msgs. */

static void clb_ErrorMessage(backchat_Diagnostic *diag) {
  char const *msg = diag->msgtext;
  unsigned line = diag->lineno;
  char b[256];
  cc_announce_error(b, diag->severity, diag->filename, line);
  fputs(b, stderr);
  fputs(msg, stderr);
}

static int clb_BC(unsigned code, const void *msg, void *handle)
{   IGNORE(handle);
    switch (code) {
    case BC_DIAGMSG: clb_ErrorMessage((backchat_Diagnostic *)msg); return 0;
    }
    return 0;
}

void clb_init(void)
{
    int i = 0;

#ifndef COMPILING_ON_MSDOS
    /* The signal ignore state can be inherited from the parent... */
    if (signal(SIGINT, SIG_IGN) != SIG_IGN)
      (void) signal(SIGINT, compile_abort);
#ifdef SIGHUP
    if (signal(SIGHUP, SIG_IGN) != SIG_IGN)
      (void) signal(SIGINT, compile_abort);
#endif
    if (signal(SIGTERM, SIG_IGN) != SIG_IGN)
      (void) signal(SIGINT, compile_abort);
#endif
    SetFeatures2(Feature_CPP, Feature_CFront);
    expr_string = NULL;
    errstate_initialise();
    errstate_perfileinit();
    aetree_init();
#ifndef USE_PP
    for (; i <= 'z'-'a'; i++)
        pp_pragmavec[i] = -1;
#else
    IGNORE(i);
    pp_init(&curlex.fl);
    var_cc_private_flags = 0;
#endif
    bind_init();
    lex_init();
    builtin_init();
    sem_init();
    syn_init();
    backchat.send = clb_BC;
    backchat.handle = NULL;
}

Expr *clb_parse_expr(char *s)
{   Expr *e, *edtor;
    SynBindList *bl;
    lex_reinit();
    expr_string = s;
    push_saved_temps(0);
    push_exprtemp_scope();
    nextsym();
    e = rd_expr(10/*PASTCOMMA*/);
    bl = pop_saved_temps(NULL);
    if ((edtor = killexprtemp()) != NULL)
    {   TypeExpr *t = typeofexpr(e);
        Binder *b = gentempbinder(t);
        e = mkbinary(s_init, (Expr *)b, e);
        e = mkbinary(s_comma, e, edtor);
        e = mkbinary(s_comma, e, (Expr *)b);
        e = mk_exprlet(s_let, t,
                       reverse_SynBindList(mkSynBindList(bl, b)),
                       e);
    }
    else if (bl != NULL)
        e = mk_exprlet(s_let, typeofexpr(e), reverse_SynBindList(bl), e);
    return optimise0(e);
}

void compiler_exit(int status)
{   IGNORE(status);
}
