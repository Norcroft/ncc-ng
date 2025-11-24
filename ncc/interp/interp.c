/*
 * interp/interp.c: main C interpreter routines
 * Copyright (C) Codemist Ltd., 1988-1993
 * Copyright (C) Acorn Computers Ltd., 1988-1990.
 * Copyright (C) Advanced RISC Machines Limited, 1992.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$ Codemist 188
 * Checkin $Date$
 * Revising $Author$
 */

#include <setjmp.h>

#include "globals.h"
#include "lex.h"
#include "syn.h"
#include "sem.h"
#include "bind.h"
#include "builtin.h"
#include "aetree.h"
#include "codebuf.h"
#include "aeops.h"
#include "pp.h"
#include "store.h"
#include "simplify.h"
#include "util.h"
#ifdef USE_PP
#include "pp.h"
#endif

#include "asdfmt.h"
#include "dbg_hdr.h"
#include "dbg_tbl.h"

#ifndef USE_PP
/* Dummy definitions for stuff in cfe/pp.c */
int32 pp_pragmavec['z'-'a'+1];
bool list_this_file;
int pp_inhashif;
#else
FILE *asmstream, *objstream;
#endif
bool target_lsbitfirst;
int32 config;
char *expr_string;

extern int curchar;
extern Expr *rd_expr();

static Dbg_MCState *cc_dbg_state;
static Dbg_Environment *cc_dbg_env;

#define b_dbgaddr 0x80000000

#define STACKSIZE 1024
typedef char *SP;
SP sp;
char stack[STACKSIZE];          /* /* a tiny stack for the moment */
static int32 max_spoffset;

static void inst_decls(Cmd *x, int32 spoffset);
static void inst_exprdecls(Expr *e, int32 spoffset);
static Expr *do_cmd(Cmd *x);
static void eval_error(char *s, ...);

static SP adjust_sp(int32 n)
{
    return sp -= n;
}

static Dbg_Error readword(Dbg_MCState *state, ARMword *word, ARMaddress addr)
{
    if (addr & b_dbgaddr) {
        *word = *(ARMword *)(addr & ~b_dbgaddr);
        return 0;
    } else {
        return dbg_ReadWord(state, word, addr);
    }
}

static Dbg_Error writeword(Dbg_MCState *state, ARMaddress addr, ARMword word)
{
    if (addr & b_dbgaddr) {
        *(ARMword *)(addr & ~b_dbgaddr) = word;
        return 0;
    } else {
        return dbg_WriteWord(state, addr, word);
    }
}

static Dbg_Error readhalf(Dbg_MCState *state, ARMhword *hword, ARMaddress addr)
{
    if (addr & b_dbgaddr) {
        *hword = *(ARMhword *)(addr & ~b_dbgaddr);
        return 0;
    } else {
        return Dbg_ReadHalf(state, hword, addr);
    }
}

static Dbg_Error writehalf(Dbg_MCState *state, ARMaddress addr, ARMhword hword)
{
    if (addr & b_dbgaddr) {
        *(ARMhword *)(addr & ~b_dbgaddr) = hword;
        return 0;
    } else {
        return Dbg_WriteHalf(state, addr, hword);
    }
}

static Dbg_Error readbyte(Dbg_MCState *state, Dbg_Byte *byte, ARMaddress addr)
{
    if (addr & b_dbgaddr) {
        *byte = *(Dbg_Byte *)(addr & ~b_dbgaddr);
        return 0;
    } else {
        return dbg_ReadByte(state, byte, addr);
    }
}

static Dbg_Error writebyte(Dbg_MCState *state, ARMaddress addr, Dbg_Byte byte)
{
    if (addr & b_dbgaddr) {
        *(Dbg_Byte *)(addr & ~b_dbgaddr) = byte;
        return 0;
    } else {
        return dbg_WriteByte(state, addr, byte);
    }
}

static void define(Binder *b)
{
    Dbg_LLSymType junk;
    unsigned32 val;
    void *llsym;

    llsym = dbg_LLSymVal(cc_dbg_state, cc_dbg_env->st, symname_(bindsym_(b)), &junk, &val);
    if (llsym)
        bindaddr_(b) = val;
    else
        eval_error("$b not defined\n", b);
}

static int32 mk_string(String *str)
{
    char *s, *t;
    int len;
    StringSegList *strseg;

    /* /* At the moment this just reallocates the string every time it is used ! */
    len = 0;
    for (strseg = str->strseg; strseg; strseg = strseg->strsegcdr)
        len += strseg->strseglen;
    s = t = SynAlloc(len + 1);
    for (strseg = str->strseg; strseg; strseg = strseg->strsegcdr) {
        memcpy(t, strseg->strsegbase, strseg->strseglen);
        t += strseg->strseglen;
    }
    s[len] = 0;
    return (int32)s + b_dbgaddr;
}

static jmp_buf eval_recover;

static void eval_error(char *s, ...)
{
    va_list a;
    va_start(a, s);
    sstart_string_char(s); ssuperrprintf(a);
    va_end(a);
    cc_msg("\n");
    longjmp(eval_recover, 0);
}

extern Expr *eval_expr(Expr *e);

static int32 read_with_mcrep(ARMaddress a, int32 m)
{
    ARMword w;
    ARMhword h;
    Dbg_Byte b;
    int32 i;

    switch (m & MCR_SIZE_MASK) {
        case sizeof(ARMword):
            readword(cc_dbg_state, &w, a);
            i = w;
            break;
        case sizeof(ARMhword):
            readhalf(cc_dbg_state, &h, a);
            i = (int32)(unsigned32)h;
            if ((m & MCR_SORT_MASK) == MCR_SORT_SIGNED)
                i = (int32)(h << 16) / (1 << 16);
            break;
        case sizeof(Dbg_Byte):
            readbyte(cc_dbg_state, &b, a);
            i = (int32)(unsigned32)b;
            if ((m & MCR_SORT_MASK) == MCR_SORT_SIGNED)
                i = (int32)(h << 24) / (1 << 24);
            break;
        default:
            eval_error("read_with_mcrep 0x%8x", m);
    }
    return i;
}

static void write_with_mcrep(ARMaddress addr, int32 m, int32 i)
{
    switch (m & MCR_SIZE_MASK) {
        case sizeof(ARMword):
            writeword(cc_dbg_state, addr, i);
            break;
        case sizeof(ARMhword):
            writehalf(cc_dbg_state, addr, i);
            break;
        case sizeof(Dbg_Byte):
            writebyte(cc_dbg_state, addr, i);
            break;
        default:
            eval_error("write_with_mcrep 0x%8x", m);
    }
}

static void assign_expr(int32 addr, Expr *e, TypeExpr *container)
{
    int32 size;
    ARMaddress source;
    int32 i;
    Dbg_Error err;
    ARMword w;
    Expr *x;
    int32 mc, me;

    mc = mcrepoftype(container);
    me = mcrepofexpr(e);
    if ((me & MCR_SORT_MASK) == MCR_SORT_UNSIGNED || (me & MCR_SORT_MASK) == MCR_SORT_SIGNED) {
        if (h0_(e) != s_integer)
            eval_error("Cannot evaluate $e", e);
        i = intval_(e);
        write_with_mcrep(addr, mc, i);
    } else {
        switch (h0_(e)) {
            case s_binder:
                source = bindaddr_((Binder *)e);
                if (bindstg_((Binder *)e) & bitofstg_(s_auto)) {
                    if (source & b_dbgaddr)
                        source += (int32)sp;
                }
                break;
            case s_content:
                x = eval_expr(arg1_(e));
                if (h0_(x) != s_integer)
                    eval_error("Cannot evaluate $e", e);
                source = intval_(x);
                break;
            default:
                eval_error("Cannot evaluate $e", e);
        }
        size = me & MCR_SIZE_MASK;
        for (i = 0; i < size/4; i++) {
            err = readword(cc_dbg_state, &w, source);
            if (err) eval_error("Error reading 0x%08x", source);
            err = writeword(cc_dbg_state, addr, w);
            if (err) eval_error("Error writing 0x%08x", addr);
            addr += 4;
            source += 4;
        }
    }
}

Expr *eval_expr(Expr *e)
{
    AEop op;
    Expr *e1;
    Expr *e2;
    Expr *x;
    int32 i1, i2;
    Binder *b;
    Dbg_Error err;
    ARMword w;
    int32 m;
    TypeExpr *t;

    if (!e) return 0;
    op = h0_(e);
    e1 = arg1_(e);
    e2 = arg2_(e);
    switch (op) {
        case s_let:
        case s_invisible:
            return eval_expr(e2);
        case s_comma:
            return eval_expr(e1), eval_expr(e2);
        case s_fnap: {
            ARMaddress addr;
            int argw;
            ExprList *el;
            static ARMword args[32];
            int i = 0;
            char *structresult = 0;

            el = exprfnargs_(e);
            t = typeofexpr(e);
            m = mcrepoftype(t);
            x = eval_expr(e1);
            if (h0_(x) != s_integer)
                eval_error("Attempt to call non function $e", e1);
            addr = intval_(x);
            if (!(addr & b_dbgaddr)) {
                if ((m & MCR_SORT_MASK) == MCR_SORT_STRUCT) {
                    structresult = SynAlloc(m & MCR_SIZE_MASK);
                    args[i++] = (ARMword)structresult | b_dbgaddr;
                }
            }
            while (el) {
                x = eval_expr(exprcar_(el));
                assign_expr((int32)&args[i] | b_dbgaddr, x, te_int);
                i += pad_to_word(sizeoftype(typeofexpr(x)))/4;
                el = cdr_(el);
            }
            argw = i;
            if (!(addr & b_dbgaddr)) {
                if (Dbg_CallNaturalSize(cc_dbg_state, addr, argw, args) != ps_callreturned)
                    eval_error("Call to function $e did not return normally", e1);
                if (structresult) {
                    b = mk_binder(gensymval(0), bitofstg_(s_static), t);
                    bindaddr_(b) = (IPtr)structresult;
                    return (Expr *)b;
                } else
                    return mkintconst(t, cc_dbg_state->call.res.intres, 0);
            } else {
                TopDecl *t;
                int32 spoffset;
                SynBindList *bl;

                t = (TopDecl *)(addr & ~b_dbgaddr);
                max_spoffset = 0;
                inst_decls(t->v_f.fn.body, 0);
                spoffset = max_spoffset;
                i = 0;
                bl = t->v_f.fn.formals;
                while (bl) {
                    bindaddr_(bl->bindlistcar) = spoffset + i * sizeof(ARMword) | b_dbgaddr;
                    i += pad_to_word(sizeoftype(bindtype_(bl->bindlistcar)))/4;
                    bl = bl->bindlistcdr;
                }
                sp = adjust_sp(spoffset + i * sizeof(ARMword));
                memcpy(sp+spoffset, args, argw * sizeof(ARMword));
                x = do_cmd(t->v_f.fn.body);
                adjust_sp(-(spoffset + i * sizeof(ARMword)));
                return x;
            }
        }
        case s_plusplus:
        case s_minusminus:
            x = eval_expr(e1);
            if (h0_(x) != s_integer)
                eval_error("Cannot evaluate $e", e1);
            i2 = intval_(x);
            e2 = mkintconst(typeofexpr(e1), s_plusplus ? i2++ : i2--, 0);
        case s_displace:
        case s_init:
        case s_assign:
            t = typeofexpr(e1);
            x = mk_expr1(s_addrof, ptrtotype_(t), e1);
            x = eval_expr(x);
            if (h0_(x) != s_integer)
                eval_error("Unable to take address of $e", e1);
            i1 = intval_(x);
            x = eval_expr(e2);
            assign_expr(i1, x, t);
            return x;
        case s_cond:
            x = eval_expr(e1);
            if (h0_(x) != s_integer)
                eval_error("Cannot evaluate $e", e1);
            return eval_expr(intval_(x) ? arg2_(e):arg3_(e));
        case s_addrof: {
            switch (h0_(e1)) {
                case s_binder:
                    b = (Binder *)e1;
                    if (bindstg_(b) & b_undef) define(b);
                    i1 = bindaddr_(b);
                    if (bindstg_(b) & bitofstg_(s_auto)) {
                        if (i1 & b_dbgaddr)
                            i1 += (int32)sp;
                    }
                    return mkintconst(ptrtotype_(bindtype_(b)), i1, 0);
                case s_content:
                    return eval_expr(arg1_(e1));
                case s_dot:
                    x = mk_expr1(s_addrof, ptrtotype_(typeofexpr(arg1_(e1))), arg1_(e1));
                    x = eval_expr(x);
                    if (h0_(x) != s_integer)
                        eval_error("Cannot evaluate $e", e1);
                    return mkintconst(typeofexpr(e), intval_(x)+exprdotoff_(e1), 0);
                case s_string:
                    return mkintconst(te_charptr, mk_string((String *)e1), 0);
                default:
                    cc_msg("Unknown op(%d) in $e (s_addrof)\n", h0_(e1), e1);
                    return 0;
            }
            break;
        }
        case s_content:
            m = mcrepofexpr(e);
            if ((m & MCR_SORT_MASK) == MCR_SORT_SIGNED || (m & MCR_SORT_MASK) == MCR_SORT_UNSIGNED) {
                x = eval_expr(e1);
                w = read_with_mcrep(intval_(x), m);
                return mkintconst(typeofexpr(e), w, 0);
            }
            return e;
        case s_dot:
            e1 = mk_expr1(s_addrof, te_int, e1);
            x = eval_expr(e1);
            if (h0_(x) != s_integer)
                eval_error("Cannot evaluate $e", e1);
            i1 = intval_(x);
            w = read_with_mcrep(i1+exprdotoff_(e), mcrepofexpr(e));
            return mkintconst(typeofexpr(e), w, 0);
        case s_binder:
            b = (Binder *)e;
            if (bindstg_(b) & b_undef) define(b);
            m = mcrepofexpr((Expr *)b);
            if ((m & MCR_SORT_MASK) == MCR_SORT_SIGNED || (m & MCR_SORT_MASK) == MCR_SORT_UNSIGNED) {
                i1 = bindaddr_(b);
                if (bindstg_(b) & bitofstg_(s_auto)) {
                    if (i1 & b_dbgaddr)
                        i1 += (int32)sp;
                }
                w = read_with_mcrep(i1, mcrepoftype(bindtype_(b)));
                return mkintconst(bindtype_(b), w, 0);
            }
            return (Expr *)b;
        case s_cast:
            return eval_expr(e1);
        case s_string:
            return mkintconst(te_charptr, mk_string((String *)e), 0);
        case s_integer:
        case s_boolean:
            return e;
        case s_plus:
        case s_minus:
        case s_times:
        case s_div:
        case s_rem:
        case s_and:
        case s_or:
        case s_xor:
        case s_andand:
        case s_oror:
        case s_leftshift:
        case s_rightshift:
        case s_equalequal:
        case s_notequal:
        case s_less:
        case s_lessequal:
        case s_greater:
        case s_greaterequal:
                x = eval_expr(e2);
                if (h0_(x) != s_integer)
                    eval_error("Cannot evaluate $e", e2);
                i2 = intval_(x);
        case s_monplus:
        case s_neg:
        case s_bitnot:
        case s_boolnot:
                x = eval_expr(e1);
                if (h0_(x) != s_integer)
                    eval_error("Cannot evaluate $e", e1);
                i1 = intval_(x);
                switch (op) {
                    case s_plus:
                        i1 = i1+i2; break;
                    case s_minus:
                        i1 = i1-i2; break;
                    case s_times:
                        i1 = i1*i2; break;
                    case s_div:
                        i1 = i1/i2; break;
                    case s_rem:
                        i1 = i1%i2; break;
                    case s_and:
                        i1 = i1&i2; break;
                    case s_or:
                        i1 = i1|i2; break;
                    case s_xor:
                        i1 = i1^i2; break;
                    case s_andand:
                        i1 = i1&&i2; break;
                    case s_oror:
                        i1 = i1||i2; break;
                    case s_leftshift:
                        i1 = i1<<i2; break;
                    case s_rightshift:
                        i1 = i1>>i2; break;
                    case s_equalequal:
                        i1 = i1==i2; break;
                    case s_notequal:
                        i1 = i1!=i2; break;
                    case s_less:
                        i1 = i1<i2; break;
                    case s_lessequal:
                        i1 = i1<=i2; break;
                    case s_greater:
                        i1 = i1>i2; break;
                    case s_greaterequal:
                        i1 = i1>=i2; break;
                    case s_monplus:
                        i1 = i1; break;
                    case s_neg:
                        i1 = -i1; break;
                    case s_bitnot:
                        i1 = ~i1; break;
                    case s_boolnot:
                        i1 = !i1; break;
                }
                return mkintconst(typeofexpr(e), i1, 0);
        default:
            cc_msg("Unknown op(%d) in $e\n", op, e);
    }
}

static void spaces(int i)
{
    while (i--) cc_msg(" ");
}

static void display_expr_i(int32 i, TypeExpr *t, char *format, int indent)
{
    switch (h0_(t)) {
        case s_typespec:
            cc_msg("%d", i);
            break;
        case t_content:
            cc_msg("%p", i);
            break;
        default:
            eval_error("Cannot handle h0_(t) = %d in display_expr_i", h0_(t));
    }
}

static void display_expr_a(int32 a, TypeExpr *t, char *format, int indent)
{
    SET_BITMAP m;
    TagBinder *tb;
    ClassMember *members;
    StructPos sp;
    SET_BITMAP sort;
    int32 i, n;
    int32 size;
    ARMword w;

    switch (h0_(t)) {
        case t_content:
            readword(cc_dbg_state, &w, a);
            display_expr_i(w, t, format, indent);
            break;
        case s_typespec:
            m = typespecmap_(t);
            switch (sort = (m & -m)) {
                case bitoftype_(s_class):
                case bitoftype_(s_struct):
                case bitoftype_(s_union):
                    tb = typespectagbind_(t);
                    indent += 4;
                    cc_msg("{");
                    for (members = tagbindmems_(tb); members; members = memcdr_(members)) {
                        if (!structfield(members, sort, &sp)) continue;
                        if (!memsv_(members)) continue;
                        cc_msg("\n");
                        spaces(indent);
                        cc_msg("%s = ", symname_(memsv_(members)));
                        display_expr_a(a+sp.boffset, memtype_(members), format, indent);
                    }
                    cc_msg("\n");
                    indent -= 4;
                    spaces(indent);
                    cc_msg("}");
                    break;
                case bitoftype_(s_char):
                case bitoftype_(s_int):
                case bitoftype_(s_enum):
                    i = read_with_mcrep(a, mcrepoftype(t));
                    display_expr_i(i, t, format, indent);
                    break;
            }
            break;
        case t_subscript:
            n = intval_(typesubsize_(t));
            indent += 4;
            t = typearg_(t);
            size = sizeoftype(t);
            cc_msg("{");
            structpos_init(&sp, tb);
            for (i = 0; i < n; i++) {
                cc_msg("\n");
                spaces(indent);
                display_expr_a(a, t, format, indent);
                a += size;
            }
            cc_msg("\n");
            indent -= 4;
            spaces(indent);
            cc_msg("}");
            break;
        default:
            eval_error("Cannot handle h0_(t) = %d in display_expr_a", h0_(t));
    }
}

static void display_expr(Expr *e, TypeExpr *t, char *format, int indent)
{
    Expr *x;

    if (h0_(e) == s_integer) {
        display_expr_i(intval_(e), t, format, indent);
        return;
    }
    x = mk_expr1(s_addrof, ptrtotype_(t), e);  /* Side effect free ? */
    x = eval_expr(x);
    if (h0_(x) != s_integer)
        eval_error("Cannot take address of $e", e);
    display_expr_a(intval_(x), t, format, indent);
}

void cc_rd_expr(Dbg_MCState *state, Dbg_Environment *env, char *s, char *format)
{
    Expr *e, *x;
    int32 i;
    TypeExpr *t;
    int32 spoffset;
    Expr *edtor;

    cc_dbg_state = state;
    cc_dbg_env = env;
    expr_string = s;
    curchar = 0;
#ifdef USE_PP
    pp_notesource("<expr>", 0);
#endif
    nextsym();
    if (setjmp(eval_recover) == 0) {
        push_exprtemp_scope();
        e = rd_expr(10/*PASTCOMMA*/);
        if (e && h0_(e) != s_error) {
            e = optimise0(e);
            sp = stack + STACKSIZE;
            max_spoffset = 0;
            inst_exprdecls(e, 0);
            spoffset = max_spoffset;
            sp = adjust_sp(spoffset);
            x = eval_expr(e);
            pr_expr(e);
            if (x) {
                t = typeofexpr(x);
                cc_msg(" = [");
                pr_typeexpr(t, 0);
                cc_msg("] ");
                display_expr(x, t, format, 0);
            } else
                cc_msg("void");
            sp = adjust_sp(-spoffset);
            cc_msg("\n");
        }
    }
    return;
}

static void inst_exprdecls(Expr *e, int32 spoffset)
{
    Expr *e1, *e2;
    SynBindList *bl;
    ExprList *el;

    if (!e) return;
    e1 = arg1_(e);
    e2 = arg2_(e);
    switch (h0_(e)) {
        case s_let:
            bl = (SynBindList *)e1;
            while (bl) {
                bindaddr_(bl->bindlistcar) = spoffset | b_dbgaddr;
                spoffset += pad_to_word(sizeoftype(bindtype_(bl->bindlistcar)));
                bl = bl->bindlistcdr;
            }
            if (spoffset > max_spoffset) max_spoffset = spoffset;
            inst_exprdecls(e2, spoffset);
            break;
        case s_fnapstructvoid:
        case s_fnapstruct:
        case s_fnap:
            inst_exprdecls(e1, spoffset);
            el = exprfnargs_(e);
            while (el) {
                inst_exprdecls(exprcar_(el), spoffset);
                el = cdr_(el);
            }
            break;
        case s_dot:
            inst_exprdecls(e1, spoffset);
            if (h0_(typeofexpr(e)) == t_ovld || h0_(typeofexpr(e)) == t_fnap)
                inst_exprdecls(e2, spoffset);
            break;
        case s_invisible:
            inst_exprdecls(e2, spoffset);
            break;
        case s_cond:
            inst_exprdecls(arg3_(e), spoffset);
            inst_exprdecls(e2, spoffset);
        case s_cast:
            inst_exprdecls(e1, spoffset);
        case s_floatcon:
        case s_string:
        case s_integer:
        case s_boolean:
        case s_binder:
        case s_member:
        case s_identifier:
        case s_error:
            break;
        default:
            if (ismonad_(h0_(e)) || h0_(e) == s_return || h0_(e) == s_throw)
                inst_exprdecls(e1, spoffset);
            else if (isdiad_(h0_(e)))
                inst_exprdecls(e1, spoffset), inst_exprdecls(e2, spoffset);
            else
                eval_error("Unhandled op in inst_exprdecls %d", h0_(e));
            break;
    }
}

static void inst_decls(Cmd *x, int32 spoffset)
{
    SynBindList *bl;
    CmdList *cl;

    if (!x) return;
    switch (h0_(x)) {
        case s_return:
        case s_semicolon:
            inst_exprdecls(cmd1e_(x), spoffset);
            return;
        case s_block:
            bl = cmdblk_bl_(x);
            while (bl) {
                bindaddr_(bl->bindlistcar) = spoffset | b_dbgaddr;
                spoffset += pad_to_word(sizeoftype(bindtype_(bl->bindlistcar)));
                bl = bl->bindlistcdr;
            }
            if (spoffset > max_spoffset) max_spoffset = spoffset;
            cl = cmdblk_cl_(x);
            while (cl) {
                inst_decls(cmdcar_(cl), spoffset);
                cl = (CmdList *)cdr_((List *)cl);
            }
            return;
        case s_do:
            inst_decls(cmd1c_(x), spoffset);
            inst_exprdecls(cmd2e_(x), spoffset);
            return;
        case s_for:
            inst_exprdecls(cmd1e_(x), spoffset);
            inst_exprdecls(cmd2e_(x), spoffset);
            inst_exprdecls(cmd3e_(x), spoffset);
            inst_decls(cmd4c_(x), spoffset);
            return;
        case s_if:
            inst_exprdecls(cmd1e_(x), spoffset);
            inst_decls(cmd2c_(x), spoffset);
            inst_decls(cmd3c_(x), spoffset);
            return;
    }
}

#define DO_EXEC         0
#define DO_GOTO         1
#define DO_SWITCH       2
#define DO_DEFAULT      3

static int do_flags;
static LabBind *goto_dest;
static int32 switch_dest;
static Expr *fn_res;

static AEop do_cmd_1(Cmd *x)
{
    Expr *e;
    CmdList *cl;
    AEop op;

    if (!x) return 0;
    switch (h0_(x)) {
        case s_semicolon:
            if (do_flags != DO_EXEC) return 0;
            eval_expr(cmd1e_(x));
            return 0;
        case s_block:
            cl = cmdblk_cl_(x);
            while (cl) {
                op = do_cmd_1(cmdcar_(cl));
                if (op) return op;
                cl = (CmdList *)cdr_((List *)cl);
            }
            return 0;
        case s_colon:
            if (do_flags == DO_GOTO && goto_dest == cmd1lab_(x))
                do_flags = DO_EXEC;
            return do_cmd_1(cmd2c_(x));
        case s_case:
            if (do_flags == DO_SWITCH && switch_dest == intval_(cmd1e_(x)))
                do_flags = DO_EXEC;
            return do_cmd_1(cmd2c_(x));
        case s_default:
            if (do_flags == DO_DEFAULT) do_flags = DO_EXEC;
            return do_cmd_1(cmd1c_(x));
        case s_switch:
            if (do_flags == DO_GOTO) return do_cmd_1(cmd2c_(x));
            if (do_flags != DO_EXEC) return 0;
            do_flags = DO_SWITCH;
            switch_dest = intval_(eval_expr(cmd1e_(x)));
            op = do_cmd_1(cmd2c_(x));
            if (do_flags == DO_SWITCH) {
                do_flags = DO_DEFAULT;
                op = do_cmd_1(cmd2c_(x));
                do_flags = 0;
            }
            if (op == s_break) op = 0;
            return op;
        case s_goto:
            if (do_flags != DO_EXEC) return 0;
            do_flags = DO_GOTO;
            goto_dest = cmd1lab_(x);
            return s_goto;
        case s_return: {
            int32 m;
            TypeExpr *t;
            Binder *b;
            char *structresult;

            if (do_flags != DO_EXEC) return 0;
            e = eval_expr(cmd1e_(x));
            if (e) {
                t = typeofexpr(e);
                m = mcrepoftype(t);
                if ((m & MCR_SORT_MASK) == MCR_SORT_STRUCT) {
                    structresult = SynAlloc(m & MCR_SIZE_MASK);
                    b = mk_binder(gensymval(0), bitofstg_(s_static), t);
                    bindaddr_(b) = (IPtr)structresult | b_dbgaddr;
                    assign_expr(bindaddr_(b), e, t);
                    e = (Expr *)b;
                }
            }
            fn_res = e;
            return s_return;
        }
        case s_break:
            if (do_flags != DO_EXEC) return 0;
            return s_break;
        case s_continue:
            if (do_flags != DO_EXEC) return 0;
            return s_continue;
        case s_do:
            do {
                op = do_cmd_1(cmd1c_(x));
                if (op == s_continue) continue;
                if (op == s_break) break;
                if (op) return op;
                if (do_flags != DO_EXEC) return 0;
            } while (intval_(eval_expr(cmd2e_(x))));
            return 0;
        case s_for:
            if (do_flags != DO_EXEC) goto go_into;
            for (eval_expr(cmd1e_(x)); intval_(eval_expr(cmd2e_(x))); eval_expr(cmd3e_(x))) {
        go_into:
                op = do_cmd_1(cmd4c_(x));
                if (op == s_continue) continue;
                if (op == s_break) break;
                if (op) return op;
                if (do_flags != DO_EXEC) return 0;
            }
            return 0;
        case s_if:
            if (do_flags != DO_EXEC) {
                op = do_cmd_1(cmd2c_(x));
                if (do_flags != DO_EXEC) op = do_cmd_1(cmd3c_(x));
                return op;
            } else {
                if (intval_(eval_expr(cmd1e_(x))))
                    return do_cmd_1(cmd2c_(x));
                else
                    return do_cmd_1(cmd3c_(x));
            }
    }
}

static Expr *do_cmd(Cmd *x)
{
    int32 res;
    AEop op;

    goto_dest = 0;
    fn_res = 0;
    do {
        op = do_cmd_1(x);
    } while (op == s_goto);
    return fn_res;
}

Expr *genstaticparts(DeclRhsList *const d, bool topflag, bool dummy_call,
        Expr *dyninit)
{
    char *p;
    const SET_BITMAP stg = d->declstg;

    if ((stg & bitofstg_(s_typedef)) || (stg & b_fnconst)) return 0;
#if 0
    if (!(stg & bitofstg_(s_static)) && !(stg & bitofstg_(s_extern))) return 0;
#endif
    if (stg & b_undef) return 0;
    if (topflag) {
        p = (char *)SynAlloc(sizeoftype(d->decltype));
        bindaddr_(d->declbind) = (int32)p | b_dbgaddr;
    }
    if (!dummy_call) {
        /* This putrid code comes from vargen */
        if (dyninit == 0 && syn_canrdinit()) {
            dyninit = syn_rdinit(d->decltype, 0, 0);
            if (dyninit && h0_(dyninit) != s_error)
                dyninit = mkbinary(s_assign, d->declbind, dyninit);
        }
    }
    if (topflag) {
        if (dyninit && h0_(dyninit) != s_error)
            eval_expr(dyninit);
        else
            memset(p, 0, sizeoftype(d->decltype));
    }
    return dyninit;
}

Dbg_Error cc_rd_topdecl(Dbg_MCState *state, Dbg_Environment *env, char *s)
{
    TopDecl *t;
    FILE *f;

    cc_dbg_state = state;
    cc_dbg_env = env;
    expr_string = 0;
    curchar = 0;
#ifdef USE_PP
    while (isspace(*s)) s++;
    if (*s) {
        f = fopen(s, "r");
        if (!f) {
            cc_msg("Error opening '%s'\n", s);
            return 0;
        }
    } else {
        f = stdin;
        s = "<stdin>";
    }
    pp_notesource(s, f);
#endif
    nextsym();
    while (1) {
        t = rd_topdecl();
        pr_topdecl(t);
        sp = stack + STACKSIZE;
        if (h0_(t) == s_eof)
            break;
        else if (h0_(t) == s_fndef) {
            cc_msg("Defined function $b\n", t->v_f.fn.name);
            bindaddr_(t->v_f.fn.name) = (IPtr)t | b_dbgaddr;
            t->v_f.fn.structresult = currentfunction.structresult;
        }
    }
#ifdef USE_PP
    if (f != stdin) fclose(f);
#endif
    return 0;
}

static int gensymno;

typedef struct Faked_TypeExpr {
    struct Faked_TypeExpr *next;
    ItemSection *section;
    asd_Type type;
    TypeExpr *t;
} Faked_TypeExpr;

Faked_TypeExpr *faked_typeexprs;

static TypeExpr *fake_typeexpr_1(ItemSection *section, asd_Type type);

static void add_faked_typeexpr(ItemSection *section, asd_Type type, TypeExpr *t)
{
    Faked_TypeExpr *ft;

    ft = SynAlloc(sizeof(Faked_TypeExpr));
    ft->section = section;
    ft->type = type;
    ft->t = t;
    ft->next = faked_typeexprs;
    faked_typeexprs = ft;
}

TypeExpr *fake_typeexpr(ItemSection *section, asd_Type type)
{
    Faked_TypeExpr *ft;
    TypeExpr *t;

    for (ft = faked_typeexprs; ft; ft=ft->next) {
        if (ft->section == section && ft->type == type)
            return ft->t;
    }
    t = fake_typeexpr_1(section, type);
    add_faked_typeexpr(section, type, t);
    return t;
}

static TypeExpr *fake_typeexpr_1(ItemSection *section, asd_Type type)
{
    TypeExpr *t;
    int32 tcode;
    Item *item;

    tcode = TYPE_TYPECODE(type);
    if (TYPE_PTRCOUNT(type)) {
        type = TYPE_TYPEWORD(tcode, TYPE_PTRCOUNT(type)-1);
        return ptrtotype_(fake_typeexpr(section, type));
    }
    if (tcode >= 0) {
        switch (tcode) {
            case TYPEVOID: return te_void;

            case TYPESBYTE: return mk_typeexpr1(s_typespec, (TypeExpr *)(bitoftype_(s_char)|bitoftype_(s_signed)), 0);
            case TYPESHALF: return mk_typeexpr1(s_typespec, (TypeExpr *)(bitoftype_(s_int)|bitoftype_(s_short)), 0);
            case TYPESWORD: return te_int;

            case TYPEUBYTE: return mk_typeexpr1(s_typespec, (TypeExpr *)(bitoftype_(s_char)|bitoftype_(s_unsigned)), 0);
            case TYPEUHALF: return mk_typeexpr1(s_typespec, (TypeExpr *)(bitoftype_(s_int)|bitoftype_(s_short)|bitoftype_(s_unsigned)), 0);
            case TYPEUWORD: return te_uint;

            case TYPEFLOAT: return te_float;
            case TYPEDOUBLE: return te_double;

            case TYPESTRING: return ptrtotype_(te_char);

            case TYPEFUNCTION: {
                TypeExprFnAux s;
                return mkTypeExprfn(t_fnap, te_int, 0, 0,
                    packTypeExprFnAux(s, 0, 1999, 0, 0, 0));
            }
            default:
                cc_msg("Unrecognised type code %d\n", tcode);
                return te_int;
        }
    } else {
        item = (Item *)((char *)section - tcode);
        switch (asd_code_(item->c)) {
            case ITEMARRAY: {
                ItemArray *item_a = &item->a;
                return mk_typeexpr1(t_subscript,
                                    fake_typeexpr(section, item_a->basetype),
                                    mkintconst(te_int, item_a->upperbound.i+1, 0));
            }
            case ITEMTYPE:
                return fake_typeexpr(section, item->t.type);
            case ITEMSTRUCT:
            case ITEMUNION:
            case ITEMCLASS: {
                TagBinder *tb;
                char name[12];
                Symstr *s;
                ClassMember **pm, *m;
                SUC *item_s = &item->s;
                unsigned32 i;
                StructField *sf;
                TypeExpr *t;
                Binder *b;

                tb = (TagBinder *)SynAlloc(sizeof(TagBinder));
                t = mk_typeexpr1(s_typespec,
                    (TypeExpr *)(asd_code_(item->c) == ITEMSTRUCT ? bitoftype_(s_struct) :
                        (asd_code_(item->c) == ITEMUNION ? bitoftype_(s_union) : bitoftype_(s_class))),
                    (Expr *)tb);
                add_faked_typeexpr(section, type, t);
                memset(tb, 0, sizeof(TagBinder));
                h0_(tb) = s_tagbind;
                gensymno++;
                sprintf(name, "<Anon%d>", gensymno);
                tagbindsym_(tb) = s = (sym_lookup)(name, 0);
                tagbindbits_(tb) = TB_DEFD;
                pm = &tagbindmems_(tb);
                for (i = 0; i < item_s->fields; i++) {
                    /* /* Note!! We assume the offsets are in ascending order here */
                    sf = &item_s->fieldtable[i];
                    m = (ClassMember *)SynAlloc(sizeof(ClassMember));
                    memset(m, 0, sizeof(ClassMember));
                    h0_(m) = s_member;
                    memsv_(m) = (sym_lookup)(sf->n.namep, 0);
                    memtype_(m) = fake_typeexpr(section, sf->type);
                    attributes_(m) = A_INTERN;
                    *pm = m;
                    pm = &memcdr_(m);
                }
                tagbindtype_(tb) = t;
                return t;

            }
            default:
                cc_msg("Unhandled item code %d\n", asd_code_(item->c));
                return te_int;
        }
        return te_int;
    }
}

Symstr *int_sym_lookup(char const *name, int glo)
{
    char *varname;
    VarDef *var;
    Dbg_Environment env;
    Dbg_Error err;
    Symstr *sym;
    Binder *b;
    TypeExpr *t;
    ItemSection *section;
    ItemVar *item;
    StgClass stgclass;

    sym = (sym_lookup)(name, glo);
    if (symtype_(sym) != s_identifier) return sym;
    if (bind_global_(sym)) return sym;

    err = dbg_StringToVarDef(cc_dbg_state, name, cc_dbg_env, &varname, &var, &env);

    /* fake a Symstr */
    symchain_(sym) = 0;
    bind_global_(sym) = 0;    /* Return 0 for binder if err occurs */
    symext_(sym) = 0;

    if (err) {
        ItemProc *p;
        Item *ip;
        TypeExpr *fntype;
        FormTypeList *ftlist;
        int i;
        TypeExprFnAux aux;
        Symstr *s;
        size_t size;

        err = dbg_StringToPath(cc_dbg_state, name, name+strlen(name),
                               &env, 0, cc_dbg_env->st, cc_dbg_env->proc);
        if (err) return sym;
        b = SynAlloc(sizeof(Binder));
        memset(b, 0, sizeof(Binder));
        h0_(b) = s_binder;
        bindsym_(b) = sym;
        p = env.proc->item;
        section = env.proc->n.section;
        fntype = fake_typeexpr(section, p->type);
        ftlist = 0;
        ip = (Item *)p;
        for (i = 0; i < p->args; i++) {
            ip = (Item *)(&ip->b + asd_len_(ip->c));
            if (asd_code_(ip->v.id) != ITEMVAR) {
                cc_msg("Missing arguments in debug table\n");
                break;
            }
            item = (ItemVar *)ip;
            if (strcmp(item->n.namep, "__struct_result") != 0) {
                size = offsetof(Symstr, symname) + strlen(item->n.namep) + 1;
                s = (Symstr *)SynAlloc(size);
                memclr(s, size);
                symtype_(s) = s_identifier;
                strcpy(symname_(s), item->n.namep);
                ftlist = mkFormTypeList(ftlist, s, fake_typeexpr(section, item->type), 0);
                i++;
            }
        }
        ftlist = (FormTypeList *)dreverse((List *)ftlist);
        t = mkTypeExprfn(t_fnap, fntype, 0, ftlist,
                         packTypeExprFnAux(aux, p->args, p->args, 0, 0, 0));
        bindtype_(b) = t;
        bindstg_(b) = bitofstg_(s_extern);
        bind_global_(sym) = b;
        bindaddr_(b) = p->startaddr;
        return sym;
    }
    section = var->n.section;
    item = &var->item->v;

    if (asd_code_(item->id) != ITEMVAR && asd_code_(item->id) != ITEMTYPE)
        return sym;

    stgclass = (StgClass)item->storageclass;

    /* Fake a binder */
    b = SynAlloc(sizeof(Binder));
    memset(b, 0, sizeof(Binder));
    h0_(b) = s_binder;
    bindsym_(b) = sym;
    bindtype_(b) = fake_typeexpr(section, item->type);
    if (asd_code_(item->id) == ITEMTYPE)
        bindstg_(b) = bitofstg_(s_typedef);
    else switch (stgclass) {
        case C_EXTERN:
            bindstg_(b) = bitofstg_(s_extern);
            bindaddr_(b) = (IPtr)item->location.address;
            break;
        case C_STATIC:
            bindstg_(b) = bitofstg_(s_static);
            bindaddr_(b) = (IPtr)item->location.address;
            break;
        case C_AUTO:
        case C_VAR:
            bindstg_(b) = bitofstg_(s_auto);
            if (dbg_FindActivation(cc_dbg_state, cc_dbg_env) != Error_OK)
                return sym;
            bindaddr_(b) = FPOffset(item->location.offset, cc_dbg_env);
            break;
        case C_REG:
            bindstg_(b) = bitofstg_(s_register);
            bindaddr_(b) = (IPtr)0;
            bindxx_(b) = (VRegnum)item->location.offset;
            bindxxp_(b) = (void *)cc_dbg_env->frame.fp;
            break;
        default:
            return sym;
    }
    bind_global_(sym) = b;

    return sym;
}

/* Dummy definitions for stuff in cfe/vargen.c */
void initstaticvar(Binder *b, bool topflag)
{
}

void compile_abort(int sig_no)
{
    /* May be a bit unfriendly for an interactive program */
    exit(1);
}

#ifndef USE_PP
int pp_nextchar(void)
{
    if (!expr_string) {
        int c = getchar();
        if (c == EOF) c = PP_EOF;
        return c;
    }
    if (!*expr_string) return PP_EOF;
    return *expr_string++;
}
#endif

extern void cc_init(void)
{
    int i;

#if 0
    SetFeature(Feature_CPP);
#else
    SetFeature(Feature_ANSI);
    ClearFeatires3(Feature_PCC, Feature_CPP, Feature_CFront);
#endif
    expr_string = "";
    errstate_init();
    aetree_init();
    alloc_init();
#ifndef USE_PP
    for (i = 0; i <= 'z'-'a'; i++)
        pp_pragmavec[i] = -1;
#else
    compiler_init();
    pp_init(&curlex.fl);
#endif
    var_cc_private_flags = 0;
    bind_init();
    lex_init();
    builtin_init();
    sem_init();
    syn_init();
}
