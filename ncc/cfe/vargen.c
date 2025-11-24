/*
 * vargen.c: static initialised variable generator for C compiler
 * Copyright (C) Codemist Ltd, 1988-1992.
 * Copyright (C) Acorn Computers Ltd., 1988-1990.
 * Copyright (C) Advanced RISC Machines Limited, 1991-1992.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$  Codemist 46
 * Checkin $Date$
 * Revising $Author$
 */

/* AM memo: for C++ soon suppress static const's until first &taken.        */
/* AM memo: I do not see how genpointer gets called with a string arg       */
/*   for WR_STR_LITS since it s_string is filtered off by initsubstatic().  */
/*   Bug in WR_STR_LITS in ANSI mode?                                       */
/*   I think the two calls to genpointer need merging -- read ANSI carefully.*/
/* AM memo: see obj_symref @@@ below for more general use?                  */
/* Warning: the vg_copyobj/zeroobj probably depend on structs/arrays being  */
/*   aligned as the compiler currently does to 4 word boundaries.           */
/* AM memo: void values/vars need faulting earlier -- see initsubstatic()   */
/* WGD 28-9-87 ACW support added, 27-3-88 updated                           */
/* 30-Nov-86: vargen now assembles bytes/halfword data initialisations      */
/* into bytes and adds LIT_XXX flags for xxxasm.c, xxxobj.c                 */

/* Discussion:  Observe that generating code in full generality for
   arbitrary open arrays requires two passes - consider (e.g.)
   "char [][] = { "a", "bc",... }".  Moreover ANSI forbid such
   possibly useful initialisations.  So do we, but for reasons of
   producing (type and size) error messages as soon as possible rather
   than after a reading phase.  Accordingly we adopt a coroutine-like
   linkage to syn.c.
*/

#ifndef _VARGEN_H
#include "globals.h"
#include "vargen.h"
#include "lex.h"               /* for curlex */
#include "syn.h"
#include "sem.h"
#include "simplify.h"
#include "bind.h"
#include "builtin.h"
#include "aetree.h"
#include "codebuf.h"
#ifndef NON_CODEMIST_MIDDLE_END
#include "regalloc.h"  /* to handle global register variables */
#endif
#include "mcdep.h"     /* for dbg_xxx */
#include "store.h"
#include "aeops.h"
#include "util.h"      /* for padsize */
#include "xrefs.h"
#include "inline.h"
#include "errors.h"

#include "dump.h"

/* and for C-only compiler... */
#define vg_note_topdtor(b, topflag) (void)0
#define vg_get_dyninit(topflag) 0
#define dynamic_init(init, fl) (void)0
#define Vargen_cpp_LoadState(f) (void)0
#define Vargen_cpp_DumpState(f) (void)0

#endif /*_VARGEN_H */

static FileLine init_fl;        /* @@@ not always set just before use! */

static TypeExpr *inittype;
static bool complain_non_aggregate;
static int32 initbsize, initboffset, initwoffset;
static Binder *cur_initlhs;

#define orig_(p)  arg1_(p)
#define compl_(p) arg2_(p)

/* It is now clear that vg_acton_globreg() should be part of syn.c      */
/* and/or bind.c (see bind_err_conflicting_globalreg below).            */
static void vg_acton_globreg(DeclRhsList *d, Binder *b)
{   VRegnum reg = GAP;
    TypeExpr *t = princtype(bindtype_(b));
    int32 rno = declstgval_(d) >> 1;
#ifndef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
    if (declstgval_(d) & 1)
    {
        if (rno <= 0 || rno > MAXGLOBFLTREG)
            cc_err(vargen_err_overlarge_reg);
        else {
            if ( h0_(t) == s_typespec &&
                 ( typespecmap_(t) & bitoftype_(s_double) ) )
                reg = R_FV1+rno-1;
            else
                cc_err(vargen_err_not_float);
        }
    }
    else
#endif
    {
        {
            if (0 < rno && rno <= MAXGLOBINTREG)
                reg = R_V1+rno-1;
#ifdef TARGET_IS_AIH324
/* Prefered form, also prepares for use of a0...d31 etc.                */
            else if (160 <= rno && rno < 160+32)
                reg = R_V1 + rno - 160;
#endif
            else
                cc_err(vargen_err_overlarge_reg);
            if (reg != GAP) switch (h0_(t)) {
            case t_content:
                break;
            case s_typespec:
#ifdef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
                if (typespecmap_(t) & bitoftype_(s_double))
                    break;
#endif
                if (typespecmap_(t) & ( bitoftype_(s_char) |
                                        bitoftype_(s_int) |
                                        bitoftype_(s_enum) ))
                    break;
                /* no one_word structs, unions - cg isn't up to the
                   notion that they might be in registers (?) */
                /* @@@AM: it ought to be! */
            default:
                cc_err(vargen_err_not_int);
                reg = GAP;
            }
        }
    }
    if (reg != GAP) {
    /* We have arranged that this binder has room to record a
     * register (though normally only auto binders have).
     */
        if (bindxx_(b) != GAP && bindxx_(b) != reg)
            cc_rerr(bind_err_conflicting_globalreg, b);
        bindxx_(b) = reg;
        globalregistervariable(reg);
        asm_setregname(reg, symname_(bindsym_(b)));
    }
}

static Expr *reduce(Expr *e, Binder *whole)
{
    /* a reduced optimise0: expose s_floatcon/s_integer             */
    if (whole &&
        (h0_(e) == s_assign || h0_(e) == s_init) &&
         arg1_(e) == (Expr *)whole)
        e = arg2_(e);
    if (h0_(e) == s_invisible && h0_(compl_(e)) == s_floatcon)
        return compl_(e);
    return e;
}

static Expr *rdinit(TypeExpr *t, Binder *whole, int32 flag)
{
    Expr *e;
    if (LanguageIsCPlusPlus)
    {
/* We can't do optimise0() since it removes the cast to break toplevel  */
/*   int x = (int)"abc";  Make C code share this soon.                  */
/* Maybe the right thing to do is optimise0(x = e) for some var 'x'.    */
      e = syn_rdinit(t, whole, flag);
      if (e) e = reduce(e, whole);
    }
    else
    {
/* The code for C and C++ has diverged -- share the above code soon.    */
      e = syn_rdinit(t, whole, flag|8);
      if (e) e = optimise0(e);
    }
    if (e && h0_(e) == s_error) e = 0;
    return e;
}

/* @@@ check this routine takes care with padding for wide strings.    */
static int32 genstring(String *s, int32 size)
{   /* the efficiency of this is abysmal. */
    StringSegList *p = s->strseg;
    AEop sort = h0_(s);
    int32 length = stringlength(p)/(sort == s_wstring ? 4 : 1);
    if (size == 0xffffff)
        size = length + 1;
    else if (length > size)
        cc_rerr(vargen_err_long_string, sort==s_wstring ? "wchar_t":"char",
                (long)size);
    else if (length == size)
        cc_warn(vargen_warn_nonull, sort==s_wstring ? "wchar_t":"char",
                (long)size);
    vg_genstring(p, size*(sort == s_wstring ? 4:1), 0);
    return size;
}

static int32 int_of_init0(Expr *init, bool *ok)
{   int32 ival = 0;
    if (init != 0 && *ok)
    {   int32 op = h0_(init);
        if (op == s_integer)
            ival = intval_(init);
        else
        {
#ifndef PROPER_CODE_TO_SUPPORT_OFFSETOF_IN_STATIC_INITIALISERS
/* AM: It isn't just a case of being sensibly centralised, an attempt    */
/* was made to encourage sem.c only to reduce 'honest' constant exprs,   */
/* like 3.4*2, but not to do algebraic re-arrangement (which simplify.c  */
/* or cg.c are responsible for).  This is partly to enable that correct  */
/* diagnostics are produced (e.g. we do not want (x+0)=3 to become x=3). */
/* The offsetof rules changed and so I believe that sem.c should NOW     */
/* do a little more about these things.  Note the requirement to         */
/* diagnose "static int x = 1 || f();" comes in here!                    */
            /* @@@ LDS 27-Mar-90. The following makes offsetof() work in */
            /* static initializer contexts. Oh woe, expression reduction */
            /* isn't sensibly centralised. This must be regarded as an   */
            /* interim bodge of the worst sort, but I don't have time to */
            /* rstructure the tree-reduction part of the compiler.       */
            if (op == s_cast || op == s_plus || op == s_minus)
            {   Expr *a1, *a2;
                if (op == s_cast)
                    a1 = init, a2 = arg1_(init);
                else
                    a1 = arg1_(init), a2 = arg2_(init);
                if ((mcrepofexpr(a1) & ~0x01000000) == sizeof_int &&
                    (mcrepofexpr(a2) & ~0x01000000) == sizeof_int)
                {   ival = int_of_init0(a2, ok);
                    if (op == s_plus)
                        ival = int_of_init0(a1, ok) + ival;
                    if (op == s_minus)
                        ival = int_of_init0(a1, ok) - ival;
                    return ival;
                }
            }
#endif
            *ok = 0;
        }
    }
    return ival;
}

static int32 int_of_init(Expr *init)
{   bool ok = YES;
    int32 ival = int_of_init0(init, &ok);
    if (!ok)
    {   if (LanguageIsCPlusPlus)
            dynamic_init(init, 0);
        else
            moan_nonconst(init, moan_static_int_type_nonconst,
                          moan_static_int_type_nonconst1,
                          moan_static_int_type_nonconst2);
    }
    return ival;
}

static Int64Con *int64_of_init(Expr *init)
{   static Int64Con zero = {
      s_int64con,
      bitoftype_(s_short)|bitoftype_(s_long)|bitoftype_(s_int),
      { 0, 0}
    };
    Int64Con *fval = &zero;
    if (init != 0)
    {   if (h0_(init) == s_int64con)
            fval = (Int64Con *)init;
        else if (LanguageIsCPlusPlus)
            dynamic_init(init, 0);
        else
            moan_nonconst(init, moan_static_int_type_nonconst,
                          moan_static_int_type_nonconst1,
                          moan_static_int_type_nonconst2);
    }
    return fval;
}

static FloatCon *float_of_init(Expr *init)
{   FloatCon *fval = fc_zero.d;
    if (init != 0)
    {   if (h0_(init) == s_floatcon) fval = (FloatCon *)init;
        else
        if (LanguageIsCPlusPlus)
            dynamic_init(init, 0);
        else
            moan_nonconst(init, moan_floating_type_nonconst,
                          moan_floating_type_nonconst1,
                          moan_floating_type_nonconst2);
    }
    return fval;
}

static String *string_of_init(Expr *init, bool wide)
{   if (init != 0 && h0_(init) == s_invisible)
        init = orig_(init);     /* can only happen in CPLUSPLUS         */
    if (init != 0 && isstring_(h0_(init)))
    {   if (wide == (h0_(init) == s_wstring)) return (String *)init;
    }
    return 0;
}

static int32 rd_bitinit(TypeExpr *t, int32 size)
{   t = unbitfield_type(t);
/* Apr 92: for type-safe enums, now use 't' instead of prev. te_int     */
/* The current version of unbitbields returns te_int/enum type.         */
    {   int32 i = int_of_init(rdinit(t, 0, 0));
        if (size < 32) i &= ((unsigned32)1 << size)-1;
        return i;
    }
/* One day it might be nice to compare the value read with size...      */
}

/**************************************************************************
      oo          oo     Problem: This code is tailored to putting string
      o\\  ____  //o     literals in the read only code area, thus it handles
        \\/    \//       initialised char *s without additional buffering and
         | O  O |        can generate the address constants on the fly. In
          : oo :         order to put the literals in the data area, we have
           \__/          to postpone generating them until after we've made
           //\\          the adcons pointing to them. Clever use of existing
         o//  \\o        data structures makes this almost painless... but
         oo    oo        BEWARE if you aspire to grok the code...
**************************************************************************/

    struct StrLit {
        struct StrLit *next;
        DataInit *d;
        String *s;
    };
    static struct StrLit *str_lits;

static void genpointer(Expr *einit)
{   int32 offset = 0;
    AEop op;
    Expr *x;
    if (LanguageIsCPlusPlus)
    {   x = optimise0(einit); /* @@@ dubious -- see rdinit().         */
        if (x == 0 || h0_(x) == s_integer) syserr("genpointer new code");
    } else
        x = einit;

    for (;;) switch (op = h0_(x))
    {   case s_addrof:
        {   Expr *y = arg1_(x); Binder *b;
            if (h0_(y) != s_binder)
                syserr(syserr_genpointer, (long)h0_(y));
            b = (Binder *)y;
            if (bindstg_(b) & b_fnconst)
                Inline_RealUse(b);
            if ((bindstg_(b) & (bitofstg_(s_static) | u_loctype))
                 == bitofstg_(s_static))
            {   /* now statics may be local (and hence use datasegment
                 * offsets -- see initstaticvar()) or functions (possibly
                 * not yet defined -- "static f(), (*g)() = f;".
                 */
                if (bindstg_(b) & b_fnconst) gendcF(bindsym_(b), offset, 0);
                else {
                    gendcA(bindsym_(datasegment), bindaddr_(b)+offset, 0);
                }
            }
#ifdef TARGET_HAS_BSS
            else if ((bindstg_(b) & bitofstg_(s_static)) &&
                     bindaddr_(b) != BINDADDR_UNSET)
#ifdef CONST_DATA_IN_CODE
                gendcA(
                    (bindstg_(b) & u_constdata) ? bindsym_(constdatasegment) :
                                                  bindsym_(bsssegment),
                            bindaddr_(b)+offset, 0);
#else
                gendcA(bindsym_(bsssegment), bindaddr_(b)+offset, 0);
#endif
#endif
            else if (bindstg_(b) & (bitofstg_(s_extern) | u_loctype))
            {   int xr = (bindstg_(b) & bitofstg_(s_weak)) ? xr_weak : 0;
                if (bindstg_(b) & b_fnconst)
                    gendcF(bindsym_(b), offset, xr);
                else
                    gendcA(bindsym_(b), offset, xr);
            }
            else
            {   cc_err(vargen_err_nonstatic_addr, b);
                if (sizeof_ptr == 8 && target_lsbytefirst)
                    gendcI(sizeof_ptr-4, TARGET_NULL_BITPATTERN);
                else gendcI(sizeof_ptr, TARGET_NULL_BITPATTERN);
            }
/*
 * The next line is because (at present?) gendcA does not put out the
 * high-order part of an 8-byte address... to allow me to fudge string
 * addresses....
 */
            if (sizeof_ptr == 8 && target_lsbytefirst) gendcI(4, 0); /* ! */
            return;
        }
        case_s_any_string
            if (HasFeature(Feature_WRStrLits) ||
                (config & CONFIG_REENTRANT_CODE)) {
              /*
               * Standard pcc mode: first dump a reference to the
               * literal then record that the literal must be generated
               * and the reference updated when the recursion terminates.
               * I.e. the offset value stashed away in the next value
               *  will be sought out again and updated.
               */
              gendcA(bindsym_(datasegment), offset, 0);  /* dataseg relative */
              str_lits = (struct StrLit *) syn_list3(str_lits, get_datadesc_ht(NO), x);
/*
 * Here is the reason that (as a temporary hack?) I make gendcA only generate
 * 4 bytes if sizeof_ptr == 8 and target_lsbytefirst.  It is because the fudge
 * here needs to have a handle on the LOW word of the address to relocate it
 * to talk about the offset of the string being mentioned.
 */
              if (sizeof_ptr == 8 && target_lsbytefirst) gendcI(4, 0);
            } else {
              /*
               * Standard ANSI mode: put the strings in code space,
               * nonmodifiable. Rely on the fact that CG thinks it is
               * between routines (even for local static inits).
               * codeloc() is a routine temporarily for forward ref
               */
              gendcF(bindsym_(codesegment),codeloc()+offset, 0);
              if (sizeof_ptr == 8 && target_lsbytefirst) gendcI(4, 0);
              codeseg_stringsegs(((String *)x)->strseg, NO);
            }
            return;
        case s_integer:
            /*
             * A New case to deal with things like '(&(struct tag*)0)->field'
             * Such expressions turn into '(int) + (int)' in the AE tree.
             * So here I calculate the value and assign it to the pointer.
             */
            /* @@@AM: new pointer reduction code in sem.c (for offsetof)   */
            /* *probably* means can never happen.  Review.                 */
            gendcI(sizeof_ptr, evaluate(x) + offset);
            return;
        case s_monplus:
        case s_cast:
            x = arg1_(x); break;
        case s_plus:
            if (h0_(arg1_(x)) == s_integer)
              { offset += evaluate(arg1_(x)); x = arg2_(x); break; }
            /* drop through */
        case s_minus:
            if (h0_(arg2_(x)) == s_integer)
              { offset += (op == s_plus ? evaluate(arg2_(x)) :
                                          -evaluate(arg2_(x)));
                x = arg1_(x); break; }
            /* drop through */
        default:
            /* I wonder if the type system allows the next error to occur! */
            /* ',' operator probably does */
            if (LanguageIsCPlusPlus)
                /* we must use 'einit': (1) to avoid optimise0()        */
                /*                  and (2) to keep 'offset'.           */
                dynamic_init(einit, 0);
            else
                cc_err(vargen_err_bad_ptr, op);
            gendcI(sizeof_ptr, TARGET_NULL_BITPATTERN);
            return;
    }
}

static void initbitfield(unsigned32 bfval, int32 bfsize, bool pad_to_int)
{
    int32 j;
    /* Bitfield initialisers may start on any container boundary, so    */
    /* (except in strict ANSI mode) they aren't necessarily int-aligned */
    /* nor int-sized                                                    */
    bfsize = (bfsize + 7) & ~7;
    if (debugging(DEBUG_DATA))
        cc_msg("initbitfield(%.8lx, %lu, %i)\n", bfval, bfsize, pad_to_int);
    for (j = 0;  j < bfsize;  j += 8)
        if (target_lsbytefirst)
            gendcI(1, bfval & 255), bfval >>= 8;
        else
            gendcI(1, bfval >> 24), bfval <<= 8;
    if (pad_to_int) padstatic(alignof_int);
}

/* NB. this MUST be kept in step with sizeoftype and findfield (q.v.) */
static void initsubstatic(TypeExpr *t, Binder *whole, bool aligned, Expr *einit)
{   SET_BITMAP m;
    inittype = t;    /* for possible dynamic initialization */
    switch (h0_(t))
    {
case s_typespec:
            m = typespecmap_(t);
            switch (m & -m)    /* LSB - unsigned/long etc. are higher */
            {   case bitoftype_(s_void):
                    /*
                     * This Guy is trying to initalise a 'void' !!!
                     * @@@ Can this happen any more?
                     */
                    cc_err(vargen_err_init_void);
                    (void)int_of_init(rdinit(te_int,whole,0));
                    break;
                case bitoftype_(s_char):
                case bitoftype_(s_enum):    /* maybe do something more later */
                case bitoftype_(s_bool):
                case bitoftype_(s_int):
                    if (m & BITFIELD) syserr(syserr_initsubstatic);
                        /* these are all supposedly done as part of the
                         * enclosing struct or union.
                         */
                    if (int_islonglong_(m)) {

                        if (einit == 0 && syn_canrdinit())
                            einit = rdinit(t,whole,0);
                        {   Int64Con *ic = int64_of_init(einit);
                            gendcI_a(sizeof_long, ((int32 *)&ic->bin.i)[0], aligned);
                            gendcI_a(sizeof_long, ((int32 *)&ic->bin.i)[1], aligned);
                        }
                        break;
                    }
#ifndef REVIEW_AND_REMOVE     /* in by default */
/*    This code to be reviewed now that the front end reduces some
      such expressions to integers.  AM and ??? to discuss.
      Do we need support for:   int x = (int)"abc";?
      Check the exact wording of last ANSI draft.
      If nothing else review the cc_err() message in genpointer.
*/
                    /*
                     * Okay, I confess, I have used the pointer initialisation
                     * code here to initialise 'int' values in PCC mode,
                     * But I can explain !!!.  Well, it goes like this, some
                     * PCC code contains expressions like :
                     *   'int x = (int) (&(struct tag*)0)->field;'
                     * Well, this is really a pointer initialisation so why
                     * not use the code.  (See simple, isn't it).
                     **** AM cringes at this.  Tidy soon.
                     *@@@ LDS too - BUT DON'T BREAK IT;
                     *              Unix won't compile if you do.
                     * AM dec90: this code probably is redundant since
                     *  changes elsewhere means it works in ansi mode.
                     *  but it does allow:  int x = (int)"abc";
                     */
                    if (HasFeature(Feature_PCC) && (sizeoftype(t) == 4))
                    {   Expr *init = rdinit(t,whole,0);
                        if (init == 0) gendcI_a(4, 0, aligned);
                        else if (h0_(init) == s_integer)
                            gendcI_a(4, intval_(init), aligned);
                        else
                            genpointer(init);
                    }
                    else
#endif /* REVIEW_AND_REMOVE */
                    {   if (einit == 0 && syn_canrdinit())
                            einit = rdinit(t,whole,0);
                        gendcI_a(sizeoftype(t), int_of_init(einit), aligned);
                    }
                    break;
                case bitoftype_(s_double):
                    if (einit == 0 && syn_canrdinit())
                        einit = rdinit(t,whole,0);
                    gendcE(sizeoftype(t), float_of_init(einit));
                    break;
                case bitoftype_(s_struct):
                case bitoftype_(s_class):
                case bitoftype_(s_union):
/* ANSI 3rd public review draft says that                            */
/*   union { int a[2][2] a, ... } x = {{1,2}} initialises like       */
/*   int a[2][2] = {1,2}   ( = {{1,0},{2,0}}).                       */
                {   int32 note = syn_begin_agg();  /* skips and notes if '{' */
                    TagBinder *b = typespectagbind_(t);
                    ClassMember *l;
                    int32 bfsize, bfval, k, woffset;
                    bool is_union = ((m & -m) == bitoftype_(s_union));
                    (void)sizeofclass(b, NULL);
                    if (!(tagbindbits_(b) & TB_DEFD))
                        cc_err(vargen_err_undefined_struct, b);
                    bfsize = bfval = woffset = 0;
                    for (l = tagbindmems_(b); l != 0; l = memcdr_(l))
                      if (is_datamember_(l))
                      {
                        inittype = memtype_(l);
                        initbsize = membits_(l);
                        initboffset = memboff_(l);
                        initwoffset = memwoff_(l);
                        if (isbitfield_type(memtype_(l)))
                        {   if (is_union && memsv_(l) == NULL) continue;
                            k = membits_(l);
                            if (bfsize == 0)
                            {   while (woffset < memwoff_(l))
                                {   gendcI(1, 0);
                                    ++woffset;
                                }
                            }
                            if (woffset < memwoff_(l))
                            {   initbitfield(bfval, bfsize, 0);
                                bfsize = bfval = 0;
                                woffset = memwoff_(l);
                            }
                            /* accumulate bitfield in bfval */
                            {   int32 leftshift = memboff_(l);
                                if (woffset != memwoff_(l))
                                    leftshift -= (woffset-memwoff_(l))*8;
                                if ((leftshift + k) > bfsize)
                                    bfsize = leftshift + k;
                                if (!target_lsbitfirst)
                                    leftshift = MAXBITSIZE - k - leftshift;
                                /* ANSI 3rd draft says unnamed bitfields */
                                /* never consume initialisers.           */
                                /* (even for unions)                     */
                                if (memsv_(l) != NULL)
                                    bfval |= rd_bitinit(memtype_(l), k)
                                                << leftshift;
                            }
                        }
                        else
                        {   if (bfsize != 0)
                            {   int32 align = memwoff_(l) & -memwoff_(l);
                                initbitfield(bfval, bfsize, 0);
                                padstatic(align > alignof_int ? alignof_int : align);
                                bfsize = bfval = 0;
                            }
                            if (!(tagbindbits_(b) & TB_UNALIGNED))
                            {   padstatic(alignof_member);
                                padstatic(alignoftype(memtype_(l)));
                            }
                            if (attributes_(l) & CB_MASK &&
                                complain_non_aggregate)
                            {   cc_warn(vargen_warn_init_non_aggregate);
                                complain_non_aggregate = 0;
                            }
                            if (!(attributes_(l) & CB_BASE) ||
                                tagbindmems_(typespectagbind_(princtype(memtype_(l)))) != NULL)
                                initsubstatic(memtype_(l), 0,
                                    !(tagbindbits_(b) & TB_UNALIGNED), 0);
                            woffset = memwoff_(l) + sizeoftype(memtype_(l));
                        }
                        /* only the 1st field of a union can be initialised */
                        if (is_union) break;
                      }
                    if (bfsize) initbitfield(bfval, bfsize, is_union);
                    if (is_union)
                        gendc0(sizeoftype(t) - (l==0 ? 0 : /* empty union!! */
                             bfsize ? sizeof_int : sizeoftype(memtype_(l))));
                    /* See sem.c(sizeoftype) -- check this agrees   */
                    else
                        if (bfsize == 0 && woffset == 0)
                            gendc0(1); /* empty C++ struct.   */
                    syn_end_agg(note);
                    padstatic(alignoftype(t));  /* often, alignof_struct */
                    break;
                }
                case bitoftype_(s_typedefname):
                    initsubstatic(bindtype_(typespecbind_(t)),
                                  whole, aligned, einit);
                    break;
                default:
                    syserr(syserr_initstatic, (long)h0_(t), (long)m);
                    break;
            }
            break;
case t_unknown:
    /* stash it away */
    {   Expr *e = (einit == 0 && syn_canrdinit()) ? rdinit(t, whole, 0) : einit;
        if (whole)
            bindconst_(whole) = e;
        break;
    }
case t_fnap:  /* spotted earlier */
default:
        syserr(syserr_initstatic1, (long)h0_(t));
case t_subscript:
        {   int32 note = syn_begin_agg();          /* skips and notes if '{' */
            int32 i, m = (typesubsize_(t) && h0_(typesubsize_(t)) != s_binder) ?
                evaluate(typesubsize_(t)):0xffffff;
            TypeExpr *t2;
            if (m == 0)
            {   syn_end_agg(note);
/* Be careful with struct { char x; int y[0]; char y; } even if ANSI illegal */
                break;
            }
/* N.B. the code here updates the size of an initialised [] array          */
/* with the size of its initialiser.  initstaticvar()                      */
/* ensures (by copying types if necessary) that this does not clobber      */
/* a typedef in things like: typedef int a[]; a b = {1,2};                 */
            if (!syn_canrdinit())
            {   if (typesubsize_(t) == 0 || h0_(typesubsize_(t)) == s_binder)
                    cc_err(vargen_err_open_array);
            }
            else if (t2 = princtype(typearg_(t)), isprimtype_(t2,s_char))
            {   String *s = string_of_init(rdinit(0,0,1), 0);
                if (s)
                {   int32 k = genstring(s, m);
                    if (s != string_of_init(rdinit(0,0,0), 0))
                        syserr("vargen(string-peep)");
                    if (typesubsize_(t) == 0 || h0_(typesubsize_(t)) == s_binder )
                        typesubsize_(t) = globalize_int(k);
                    syn_end_agg(note);
                    break;
                }
                /* ANSI say m > 0 so rdinit(peek) is re-read.           */
            }
/* t2 is maybe const/volatile 'signed T' or 'T', where T is the type of */
/* wchar_t.  This needs to be improved if wchar_t can be some sort of   */
/* char. */
            else if (h0_(t2) == s_typespec && (typespecmap_(t2) &
                            (bitoftype_(s_int)|bitoftype_(s_long)|
                             bitoftype_(s_short)|bitoftype_(s_unsigned)))
                            == typespecmap_(te_wchar))
            {   String *s = string_of_init(rdinit(0,0,1), 1);
                if (s)
                {   int32 k = genstring(s, m);
                    if (s != string_of_init(rdinit(0,0,0), 1))
                        syserr("vargen(string-peep)");
                    if (typesubsize_(t) == 0 || h0_(typesubsize_(t)) == s_binder)
                        typesubsize_(t) = globalize_int(k);
                    syn_end_agg(note);
                    break;
                }
                /* ANSI say m > 0 so rdinit(peek) is re-read.           */
            }
/* Maybe generalise this one day:                                       */
#define vg_init_to_null(t) (TARGET_NULL_BITPATTERN == 0)
            for (i = 0; i < m; i++)
            {   if (!syn_canrdinit())
                {   if (typesubsize_(t) == 0 || h0_(typesubsize_(t)) == s_binder)
                    {   typesubsize_(t) = globalize_int(i);
                        break;  /* set size to number of elements read. */
                    }
                    if (vg_init_to_null(typearg_(t)))
                    {   gendc0((m-i)*sizeoftype(typearg_(t)));
                        break;  /* optimise multi-zero initialisation.  */
                    }
                }
                initsubstatic(typearg_(t), 0, aligned, 0);
            }
            syn_end_agg(note);
            break;
        }
case t_content:
case t_ref:
        {   Expr *init = rdinit(t,whole,0);
            if (init == 0)
                gendcI(sizeof_ptr, TARGET_NULL_BITPATTERN);
            else if (h0_(init) == s_integer)
                gendcI(sizeof_ptr, intval_(init)); /* casted int to pointer */
            else
                genpointer(init);
            break;
        }
    }
}

static void initstaticvar_1(
    Binder *b, bool topflag, TentativeDefn *tentative, Expr *einit)
{
    TypeExpr *btype = bindtype_(b);
    bool changingtoconst = LanguageIsCPlusPlus && !is_constdata()
                           && (qualifiersoftype(btype) & bitoftype_(s_const));
    DataInit *oldtail;
    int32 oldsize;
    DataXref *oldxrefs;

    if (tentative != NULL) {
        if (changingtoconst) {
            DataAreaSort da = SetDataArea(DS_Const);
            save_vargen_state(tentative);
            SetDataArea(da);
        } else
            save_vargen_state(tentative);
    }
    if (debugging(DEBUG_DATA))
        cc_msg("%.6lx: %s%s (%s)\n", (long)get_datadesc_size(), topflag ? "" : "; ",
               symname_(bindsym_(b)),
#ifdef CONST_DATA_IN_CODE
               (is_constdata()) ? "constdata" :
#endif
               "data");
    if (b != datasegment) padstatic(alignoftype(btype));

/* ECN: Defer setting of oldtail & oldsize until after we have done padstatic
 *      because padstatic applies to the original datap so if we switch to
 *      datap = &constdata we will need to apply padstatic again and not simply
 *      reuse the old padding as this may be wrong for constdata.
 */
    if (changingtoconst) {
        labeldata(NULL);
        oldtail = get_datadesc_ht(NO);
        oldsize = get_datadesc_size();
        oldxrefs = get_datadesc_xrefs();
    }
    bindaddr_(b) = get_datadesc_size();
    if (topflag) /* note: names of local statics may clash but cannot be
                    forward refs (except for fns which don't come here) */
    {   labeldata(bindsym_(b));
        (void)obj_symref(bindsym_(b),
                bindstg_(b) & bitofstg_(s_extern) ?
                get_datadesc_xrarea()+xr_defext : get_datadesc_xrarea()+xr_defloc,
                get_datadesc_size());
    }
    if (b == datasegment) return;      /* not really tidy */
    {
    /*
     * A decl such as 'typedef char MSG[];' gets side effected by
     * 'MSG name = "A name";'.  Therefore copy type before initialiser
     * is read ... Here we go ...
     */
        if (isprimtype_(btype, s_typedefname))
        {   TypeExpr *t = prunetype(btype);
            if (h0_(t)==t_subscript &&
                (typesubsize_(t) == 0 || h0_(typesubsize_(t)) == s_binder))
            /* the next line is idle, since case is rare...             */
            /* (We must alloc. glob store since b maybe top level       */
            /*  and hence its type will already be globalised, but      */
            /*  prunetype() may alloc. local store -- globalise all.)   */
            /* Note that the next line relies on globalize_typeexpr     */
            /* NOT caching empty arrays, hence we get a fresh copy.     */
            btype = bindtype_(b) = globalize_typeexpr(t);
        }
        {
#ifdef TARGET_IS_ACW
/* The following (hackish) lines force Feature_WRStrLits (which puts     */
/* strings in data segment) for the Acorn 32000 machine) which, due to   */
/* TARGET_CALL_USES_DESCRIPTOR, are unhappy abount code segment adcons   */
/* (as opposed to descriptors) in a data segment.                        */
            bool hadWRStrLits = HasFeature(Feature_WRStrLits);
            SetFeature(Feature_WRStrLits);
#endif
            initsubstatic(btype, b, YES, einit);
/* Note that the following padstatic(alignof_toplevel) helps alignment   */
/* of (e.g.) strings (which often speeds memcpy etc.).  However it is    */
/* also assumed to happen by the code for initialising auto arrays.      */
/* See the call to trydeletezerodata().                                  */
            padstatic(alignof_toplevel_static);
#ifdef TARGET_IS_ACW
            if (!hadWRStrLits)
                ClearFeature(Feature_WRStrLits);
#endif
        }
    }
#ifdef CONST_DATA_IN_CODE
    if (changingtoconst && vg_currentdecl_inits == NULL)
    {   DataInit *newtail, *newinits;
        labeldata(NULL);
        newtail = get_datadesc_ht(NO);
        if (oldtail != NULL)
        {   newinits = oldtail->datacdr;
            oldtail->datacdr = NULL;
            set_datadesc_ht(NO, oldtail);
        }
        else
        {   newinits = get_datadesc_ht(YES);
            set_datadesc_ht(YES, NULL);
            set_datadesc_ht(NO, NULL);
        }
        SetDataArea(DS_Const);
        padstatic(alignoftype(btype));
        labeldata(NULL);
        bindaddr_(b) = get_datadesc_size();     /* constdata.size */
        /* the following lines are a hack but reused store allocated and
           fewer things to unhook */
        if (topflag)
        {   symext_(bindsym_(b))->extflags = 0;
            (void)obj_symref(bindsym_(b),
                bindstg_(b) & bitofstg_(s_extern) ?
                get_datadesc_xrarea()+xr_defext : get_datadesc_xrarea()+xr_defloc,
                get_datadesc_size());
        }

        if (newinits != NULL)
        {   if (get_datadesc_ht(YES) == NULL)
                set_datadesc_ht(YES, newinits);
            else
                get_datadesc_ht(NO)->datacdr = newinits;
            set_datadesc_ht(NO, newtail);
        }
        /* Assert: (data.xrefs == NULL) -> (data.xrefs == oldxrefs) */
        if (data_xrefs() != oldxrefs)
        {   DataXref *xref = data_xrefs();
            int32 roffdelta = constdata_size() - oldsize;
            while (xref != NULL)
            {   xref->dataxroff += roffdelta;
                if (xref->dataxrcdr == oldxrefs)
                    break;
                xref = xref->dataxrcdr;
            }
            if (xref == NULL) syserr("can't find oldxref");
            xref->dataxrcdr = constdata_xrefs();
            set_datadesc_xrefs(data_xrefs());
            SetDataArea(DS_ReadWrite); set_datadesc_xrefs(oldxrefs); SetDataArea(DS_Const);
        }
        if (debugging(DEBUG_DATA))
            cc_msg("        moved to const data %.6lx\n", (long)constdata_size());
        set_datadesc_size(constdata_size() + data_size() - oldsize);
        SetDataArea(DS_ReadWrite); set_datadesc_size(oldsize); SetDataArea(DS_Const);
        bindstg_(b) |= u_constdata;
        bindstg_(b) |= b_generated;
    }
#endif
    codeseg_flush(0/*no strlitname*/);
}

/* Should be static except for initstaticvar(datasegment) in compiler.c */
void initstaticvar(Binder *b, bool topflag)
{   initstaticvar_1(b, topflag, NULL, 0);
}

static Expr *quietaddrof(Binder *b)
/* This function exists only to keep PCC mode happy. ensurelvalue() in */
/* sem is what's really needed, but it isn't exported and whinges in   */
/* pcc mode about &<array>. In the long-term, something like this is   */
/* needed for export from simplify (a quiet force-address-of-tree opn  */
/* for trusted callers) so until then LDS leves this bodge here.       */
{   bindstg_(b) |= b_addrof;
    return mk_expr1(s_addrof, ptrtotype_(bindtype_(b)), (Expr *)b);
}

/* Auxiliary routine for initialising auto array/struct/unions */
static Expr *vg_copyobj(Binder *sb, Binder *b, int32 size)
{   /* Note that the same code suffices for array and structs as it is */
    /* quite legal to take the address of an array, implicitly or      */
    /* explicitly.  Note that b/sb both have array/struct/union type.  */
    return mk_expr2(s_fnap, primtype_(bitoftype_(s_void)), sim.memcpyfn,
              (Expr *)mkExprList(
                mkExprList(
                  mkExprList(0, mkintconst(te_int, size, 0)),
                  quietaddrof(sb)),
                quietaddrof(b)));
}

static Expr *vg_zeroobj(Binder *b, int32 offset, int32 zeros)
{   Expr *addrb = quietaddrof(b);
    return mk_expr2(s_fnap, primtype_(bitoftype_(s_void)), sim.memsetfn,
              (Expr *)mkExprList(
                mkExprList(
                  mkExprList(0, mkintconst(te_int,zeros,0)),
                  lit_zero),
                mk_expr2(s_plus, typeofexpr(addrb), addrb,
                         mkintconst(te_int, offset, 0))));
}

static DeclRhsList *defergenerating(DeclRhsList *const d, Expr *dyninit)
{   DeclRhsList *dd = (DeclRhsList *)GlobAlloc(SU_Const, sizeof(DeclRhsList));
    *dd = *d;
    dd->decltype = globalize_typeexpr(d->decltype);
    declinit_(dd) = globalize_expr(dyninit);
    return dd;
}

/* The following routine removes generated statics, which MUST have been
   instated with instate_declaration().  Dynamic initialistions are turned
   into assignments for rd_block(), by return'ing.  0 means no init.
   Ensure type errors are noticed here (for line numbers etc.) */
/* AM: the 'const's below are to police the unchanging nature of 'd'    */
/* (and its subfields stg,b).  Note that 't' can be changed.            */

Expr *genstaticparts(DeclRhsList *const d, bool topflag, bool dummy_call,
        Expr *dyninit)
{   const SET_BITMAP stg = d->declstg;
/* also note stg below has 2/3 defns bindstg/declstg.                   */
    Binder     *const b  = d->declbind;
    TypeExpr   *t  = prunetype(d->decltype);
    int hackflag;             /* only while transforming code.          */
    int32 loc = 0;
    str_lits = NULL;          /* no static string inits seen yet.       */
    init_fl = d->fileline;
    complain_non_aggregate = !dummy_call;

    /* Apr 92: this case was recently lifted out -- maybe it shows a    */
    /* bug(?) whereby s_typedef and b_fnconst can both be set?          */
    if (stg & bitofstg_(s_typedef))
    {   if (usrdbg(DBG_PROC) && topflag)
            dbg_type(bindsym_(b), bindtype_(b), d->fileline);
    }
    else if (!(stg & b_fnconst)) switch (stg & PRINCSTGBITS)
    {
case bitofstg_(s_auto):                 /* includes register vars too   */
            /*
             * Deal with arrays, structs and unions here
             * Treat auto a[5] = 2; consistently with static a[5] = 2;
             * by always trying to read an initialiser for an array.
             * @@@ maybe forbid above for C++
             */
            if ( syn_canrdinit() &&
                 ( h0_(t) == t_subscript ||
                   ( curlex.sym == s_lbrace && isclasstype_(t))))
            {   /* For an initialised auto array/struct/union generate    */
                /* the whole object (ANSI 3rd draft say initialising one  */
                /* component of an object initialises it all) in static   */
                /* space and generate a run-time copy.   We treat large   */
                /* terminal zero segments specially.                      */
                /* For consistency this is a source-to-source translation. */
                int32 size, zeros;
/* NB the use of bindtype_(b) in the next line instead of t avoids        */
/* updating a possible open array typedef.                                */
                Binder *sb = mk_binder(gensymval(0), bitofstg_(s_static),
                                       bindtype_(b));
                DataInit *start;
                /* It suffices to allocate sb like any other local static. */
#ifdef TARGET_IS_HELIOS
/*
 * A strange option needed with Helios (for building a shared library) can
 * make this mechanism fall apart (the forged static may not get set up)
 * so I generate a diagnostic to warn people.  Yuk at the break of modularity.
 */
                {   extern bool suppress_module;
                    if (suppress_module)
                        cc_err(vg_err_dynamicinit);
                }
#endif
#ifdef CONST_DATA_IN_CODE
                if ( /*!LanguageIsCPlusPlus &&*/
                     (!(config & CONFIG_REENTRANT_CODE) ||
                      pointerfree_type(bindtype_(b))))
                {   SetDataArea(DS_Const);
                    binduses_(sb) |= u_constdata;
                    cur_initlhs = b;
                }
#endif
                start = (get_datadesc_ht(YES) == NULL) ? NULL : get_datadesc_ht(NO);
                /*
                 * Create hidden static for auto initialiser.
                 */
                initstaticvar(sb, NO);
                cur_initlhs = 0;
/* Update bindtype_(b) in case it was typedef to open array which       */
/* would have been copied (cloned) by initstaticvar().                  */
                t = bindtype_(b) = bindtype_(sb);
                size = sizeoftype(t);    /* size of auto [] now known.  */

/* The following line is helpful for initialising auto char arrays.     */
/* We pad the size for initialisation purposes up to a multiple of      */
/* alignof_toplevel, safe (in the assumption) that flowgraf.c has padded*/
/* the stack object and that initstaticvar() below has done the same    */
/* for the statically allocated template.                               */
/* The effect is to encourage cg.c to optimised word-oriented copies.   */
                size = padsize(size, alignof_toplevel_auto);

/* If less than 8 words of zeros in array, struct or union then do not  */
/* remove trailing zeros.  trydeletezerodata() is a multiple of 4.      */
                zeros = trydeletezerodata(start, 32);
                if (dyninit) syserr("dyninit");
                if (zeros == 0)
                    dyninit = vg_copyobj(sb, b, size);
                else
                {   /*
                     * Call function to copy trailing zeros to the data
                     * structure.
                     */
                    dyninit = vg_zeroobj(b, size-zeros, zeros);
                    /*
                     * Copy hidden static to auto array, struct or union
                     * without any trailing zeros.
                     */
                    if (size>zeros)
                        dyninit = mkbinary(s_comma,
                                           vg_copyobj(sb, b, size-zeros),
                                           dyninit);
                }
                {   Expr *e = vg_get_dyninit(topflag);
                    if (e != 0)
                        dyninit = mkbinary(s_comma, dyninit, e);
                }
                SetDataArea(DS_ReadWrite);
            }
            else
            {   Expr *e = syn_rdinit(d->decltype, b, 0);   /* no optimise0 */
                if (e)
                {  if (dyninit) syserr("dyninit");
                   dyninit = e;
                }
            }
            break;
#ifndef NON_CODEMIST_MIDDLE_END
case b_globalregvar:
            vg_acton_globreg(d, b);
            loc = bindxx_(b);
            break;
#endif

default:
            syserr(syserr_rd_decl_init, (long)stg);
            /* assume static */
case bitofstg_(s_static):
case bitofstg_(s_extern):
    {   bool dyninit_is_const = NO;
        Expr *orig_dyninit = dyninit;
        if (LanguageIsCPlusPlus)
/* @@@ This isn't right for local statics!                              */
        {   /* pick up any initialiser expressions passed in...         */
            if (dyninit)
            {   Expr *rhs;
                if (issimpletype_(t) &&
                    (h0_(rhs = reduce(dyninit, b)) == s_integer ||
                     h0_(rhs) == s_floatcon))
                {   dyninit = rhs;
                    if (stg & bitofstg_(s_static))
                        dyninit_is_const = YES;
                    else
                        dyninit_is_const = NO;
                }
                else
                    dynamic_init(dyninit, 1), dyninit = 0;
            }
        }

        if (!(d->declstg & b_undef))    /* explicit initialisation      */
        {                               /* (or small tentative).        */
#ifdef CONST_DATA_IN_CODE
            if ((!LanguageIsCPlusPlus || dyninit) &&
                (qualifiersoftype(d->decltype) & bitoftype_(s_const)) &&
                ( !(config & CONFIG_REENTRANT_CODE) ||
                  pointerfree_type(d->decltype)) )
            {
                bindstg_(b) |= u_constdata;
            }
#endif
            if (LanguageIsCPlusPlus)
            {   /* similar code to auto for "static class A x, y = x;"  */
                if (isclasstype_(t))
                {   if (curlex.sym != s_lbrace && syn_canrdinit())
                    {   Expr *e = syn_rdinit(d->decltype, b, 0);
                           /* no optimise0 */
                        if (e) dynamic_init(e, 1), e = 0;
                        else syserr("genstatic(static-class)");
                    }
                }
                vg_note_topdtor(b, topflag);
                    /* no-op unless t is a class or array-of-class type */
                if (var_cc_private_flags & 2L)
                    dyninit_is_const = 0;     /* in C++, disable if set */
            }

            if (dyninit_is_const &&
                (bindstg_(b) & u_constdata) && !(bindstg_(b) & b_generated))
            {   /* an eliminatable const definition... for now...       */
                bindaddr_(b) = (IPtr)defergenerating(d, orig_dyninit);
                return 0;
            }
            else
            {
#ifdef CONST_DATA_IN_CODE
                if (bindstg_(b) & u_constdata)
                {   bindstg_(b) |= b_generated;
                    SetDataArea(DS_Const);
                }
#endif
                initstaticvar_1(b, topflag, d->tentative, dyninit);
            }
            /* Put out debug info AFTER initialised array size has      */
            /* been filled in by initstaticvar():                       */
            hackflag = 1;
        }
        else    /* declaration with no explicit initialisation.         */
        {
            if (HasFeature(Feature_PCC))
            {   TypeExpr *t = princtype(bindtype_(b));
                /*
                 * Found a declaration like int foo; with no initialiser.
                 * PCC regards this as common which is encoded as an
                 * undefined external data reference with a non-0 size.
                 * BUT BEWARE: int foo[]; is NOT a common variable - it
                 * is an extern decl. Thus, we have a look for undefined
                 * arrays.  (e.g. xxx[1][3][]), possibly via a leading
                 * typedef. If we find one then we exit.
                 * AM: @@@ use is_openarray() soon?  I would now, but
                 * am nervous about int a[][]; in pcc mode.
                 */
                for (; h0_(t) == t_subscript; t = princtype(typearg_(t)))
                {   if (typesubsize_(t) == 0 || h0_(typesubsize_(t)) == s_binder)
                    {
#ifndef TARGET_IS_UNIX
                        /* Add debug info for open arrays (ASD only) */
                        if (usrdbg(DBG_PROC) && topflag)
#ifdef TARGET_HAS_BSS
                            dbg_topvar(bindsym_(b),0,bindtype_(b),DS_EXT+DS_UNDEF,d->fileline);
#else
/* Not all Codemist clients unix interfaces have BSS yet (e.g. COFF)    */
                            dbg_topvar(bindsym_(b),0,bindtype_(b),1,d->fileline);
#endif
#endif
                        goto switch_break;
                    }
                }
                /*
                 *  Generate a special extern reference for PCC style
                 *  common variables.
                 */
/* @@@ This is a genuine feature or config which other systems may want. */
/* Provide a switch one day soon.                                       */
                if ((stg & bitofstg_(s_extern)) && (stg & b_implicitstg))
                    (void)obj_symref(bindsym_(b), xr_data+xr_comref,
                                      sizeoftype(bindtype_(b)));
            }
            /* Add debug information for common and extern variables */
            hackflag = 0;
        }
    }
        if (LanguageIsCPlusPlus)
        /* The next line should be a result of initstaticvar!       */
            dyninit = vg_get_dyninit(topflag);
        loc = bindaddr_(b);
        break;
    }

    if (usrdbg(DBG_PROC) && topflag &&
        !(stg & (b_fnconst|bitofstg_(s_typedef))))
    {   /* Note that local (to a proc) statics are dealt with       */
        /* in flowgraph.c                                           */
#ifdef TARGET_HAS_BSS
/* @@@ AM Memo: do the BSS mods in a more principled way.               */
/* The following code (tidied Jul-93 but not changed in effect) does    */
/* several silly things: it sets DS_BSS even when the var is later      */
/* given a definition.                                                  */
        SET_BITMAP stg = bindstg_(b);
        if (curlex_member && realbinder_(curlex_member) == b)
            bindparent_(b) = bindparent_(curlex_member);
        dbg_topvar(bindsym_(b), loc, bindtype_(b),
                   stg & b_globalregvar ? DS_REG :
                   ( (stg & bitofstg_(s_extern) ? DS_EXT : 0) |
                     (stg & u_bss ? DS_BSS :
                      stg & u_constdata ? DS_CODE : 0) |
                     (stg & b_undef ? DS_UNDEF : 0)), d->fileline);
#else
        if (hackflag)
            dbg_topvar(bindsym_(b), bindaddr_(b), bindtype_(b),
                       (bindstg_(b) & bitofstg_(s_extern)) != 0, d->fileline);
        else
            dbg_topvar(bindsym_(b), 0, bindtype_(b), 1, d->fileline);
#endif
        bindparent_(b) = 0;
    }
switch_break:
/* AM Aug 90: bug fix to stop initialisation of a tentative to be a     */
/* string pointer leaving the string pointer in the wrong place in the  */
/* data segment in Feature_WRStrLits mode.  Now that the ANSI std       */
/* has appeared, the whole tentative/bss/vargen edifice ought to be     */
/* rationally reconstructed.                                            */
   /*
    * The next call is part of a disgusting fix for tentative
    * static and extern decls.  What happens is as follows:
    * We parse along until we find a decl with no initialiser.
    * We then set 'b_undef' for this symbol and pass it to
    * 'instate_declaration()' above.  This symbol is then entered
    * into the symbol table and 'b_undef' is UNSET if it is a
    * tentative decl so that 'genstaticparts()' WILL allocate it
    * some store.
    * Now if sometime later a REAL initialiser is found for
    * this symbol, this is detected by is_tentative() in mip/bind.c
    * which removes the zeros from the 'data.head/tail' lists and then call
    * 'genstaticparts()' to read the initialiser and finally we call
    * 'reset_vg_after_init_of_...()' below to fix the tables.
    */
    reset_vg_after_init_of_tentative_defn();
    SetDataArea(DS_ReadWrite);
    /*
     * Now generate the string literals we have delayed generating.
     * Also, we relocate the references to them by updating the
     * values in the data-generation templates that will cause those
     * references to be dumped in the data area... Note that we reverse
     * the work list so literals are generated in source order.
     * Note also that the following is a no-op unless Feature_WRStrLits.
     */
    {   struct StrLit *p = (struct StrLit *) dreverse((List *)str_lits);
        for (; p != NULL;  p = p->next)
        {   p->d->val += data_size();      /* real offset of generated lit */
            genstring(p->s, 0xffffff);   /* literal dumped in data area  */
            padstatic(alignof_toplevel_static);
        }
    }
    return dyninit ? optimise0(dyninit) : 0;
}

void vg_generate_deferred_const(Binder *b)
{   DeclRhsList *d = (DeclRhsList *)(IPtr)bindaddr_(b);  /* see defergenerating() uses */
    Expr *dyninit = declinit_(d);
    bindstg_(b) |= b_generated;            /* note reuse of b_generated */
    bindaddr_(b) = 0;
    declinit_(d) = 0;
    (void) genstaticparts(d, YES, NO, dyninit);
}

#ifndef NO_DUMP_STATE
void Vargen_LoadState(FILE *f) {
    if (LanguageIsCPlusPlus)
        Vargen_cpp_LoadState(f);
    else
        IGNORE(f);
}

void Vargen_DumpState(FILE *f) {
    if (LanguageIsCPlusPlus)
        Vargen_cpp_DumpState(f);
    else
        IGNORE(f);
}
#endif

/* end of vargen.c */
