/*
 * mip/cg.h
 * Copyright (C) Acorn Computers Ltd., 1988-1990.
 * Copyright (C) Codemist Ltd., 1987-1992.
 * Copyright (C) Advanced RISC Machines Limited, 1991-1992.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

#ifndef _cg_h
#define _cg_h 1

#ifndef _defs_LOADED
#  include "defs.h"
#endif
#ifndef _cgdefs_LOADED
#  include "cgdefs.h"
#endif
#ifndef _jopcode_LOADED
#include "jopcode.h"
#endif

extern bool has_main;
extern const FileLine *current_fl;

extern J_OPCODE Q_swap(J_OPCODE);
/* alter a condition mask as required after interchanging the two operands
   of a comparison
 */

extern Binder *gentempvarofsort(RegSort sort);

extern Binder *gentempvarofsortwithname(RegSort sort, char *name);

#if defined(CALLABLE_COMPILER)
#define cg_topdecl(x, fl)               ((void)0)
#define cg_reinit()                     ((void)0)
#define cg_tidy()                       ((void)0)
#define cg_topdecl2(locals,regs)        ((void)0)
#define cg_init()                       ((void)0)
#define cg_sub_reinit()                 ((void)0)
#else
extern void cg_topdecl(TopDecl *x, FileLine fl);
extern void cg_reinit(void);
extern void cg_tidy(void);
extern void cg_topdecl2(BindList *local_binders, BindList *regvar_binders);
extern void cg_init(void);
extern void cg_sub_reinit(void);
#endif

extern VRegnum cg_exprvoid(Expr *x);
extern VRegnum cg_expr(Expr *x);

extern void bfreeregister(VRegnum r);
extern VRegnum fgetregister(RegSort rsort);
extern VRegnum cg_storein(VRegnum r,Expr *val,Expr *e,AEop flag);

#endif

/* end of mip/cg.h */
