/*
 * sem.c: semantic analysis phase of the C/C++ compiler
 * Copyright (C) Codemist Ltd, 1988-1992
 * Copyright (C) Acorn Computers Ltd., 1988-1990.
 * Copyright (C) Advanced RISC Machines Limited, 1991-1992.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$ Codemist 167
 * Checkin $Date$
 * Revising $Author$
 */

/* @@@ worry about the type of: const struct { int a[10]; } x; &x.a;    */
/*     in pcc mode.                                                     */
/* New routine 'princtype' which acts like old prunetype for users who  */
/* just wish to the 'shape' of a type and not its qualifiers.           */

/* AM Aug 88: Overflow during constant reduction (ANSI Dec 88, section  */
/* 3.4) is now trapped.  It currently gives only a cc_warn message in   */
/* spite of it being a 'constraint violation'.  This is because AM is   */
/* a little fearful of faulting (e.g.) 1<<31, (char)257, -1u, etc.      */
/* It may be that these messages are a little aggressive, let's see.    */
/* Currently, explicit casts give no warning.                           */
/* Find all strings of the form '_overflow' to study.                   */
/* There is also the problem of 'static a = 1 || 1000000*1000000;'.     */
/* AM believe the draft spec to be ambiguous here.                      */
/* Hence the use of cc_ansi_warn not cc_ansi_rerr which sadly deletes   */
/* the object file.                                                     */

/* Nov 88: Rework Feature_SignedChar so it is ansi-conformant too.      */
/* Nov 88: Rework optional double alignment, see TARGET_ALIGNS_DOUBLES. */

#ifndef _SEM_H
#include <string.h>                            /* for memset and strcmp */
#include "globals.h"
#include "sem.h"
#include "bind.h"
#include "aetree.h"
#include "builtin.h"
#include "aeops.h"
#include "store.h"
#include "errors.h"
#include "util.h"     /* for padsize */
#include "simplify.h"
#include "vargen.h"

#ifdef PASCAL /*ECN*/
#include "syn.h"      /* No comments please, its already under the axe */
#include "lib.h"
#include "synbind.h"
#include "passem.h"
#endif

/* and for C-only compilers... */
#define cpp_mkbinaryorop(op,a,b) 0
#define cpp_ptrcast(a,b,c,d,e) 0
#define cpp_ptrtomemcast(a,b,c,d,e) 0
#define cpp_mkcast(op,ep,tr) 0
#define nullptr(cl) 0
#define ovld_resolve_addr(a, t) 0
#define ovld_resolve_addr_2(op, t,l,b) ((Binder *)0)
#define exprlist_of_default_args(d, i) ((ExprList *)0)
#define pointerkeepnull(ee,e,gen) 0
#define common_pointer_type(op,t1,e1,newe1,t2,e2,newe2,common) 0
#define common_reference_type(op,t1,e1,newe1,t2,e2,newe2,common) 0
#define allowable_boolean_conversion(a) 0
#define call_dependency_type(a,b) 0
#define call_dependency_val(a,b) 0
#define is_comparable_specialization(a,b) 0
#endif /* _SEM_H */

#define exprdotmemfn_(p) arg2_(p)

/* Discussion on "int" and "signed int".  In most cases these are      */
/* identical, hence rather tortuous code in equivtype (find all        */
/* occurrences of s_signed below).  However, they differ in bitfield   */
/* context ("signed" selects signed bitfield, plain implementation     */
/* dependent signed/unsigned) and hence typedef context.  Hence syn.c  */
/* cannot simply normalise so that all int's are signed.               */
/* Note similarly "signed short" == short and "signed long" == long.   */
/* #define'ing SIGNEDNESS_MATTERS can cause this not to happen.        */
/* However, "char", "signed char" and "unsigned char" all differ.      */

#define addrsignmap_ (TARGET_ADDRESSES_UNSIGNED ? \
                        bitoftype_(s_int)|bitoftype_(s_unsigned) : \
                        bitoftype_(s_int)|bitoftype_(s_signed))

/* The following macro is used to default the signedness for 'plain'   */
/* char and 'plain' int bit fields.                                    */
#define issignedchar_(m) ((m) & bitoftype_(s_signed) || \
          (HasFeature(Feature_SignedChar) && !((m) & bitoftype_(s_unsigned))))

Expr *errornode;

/* memo: re-insert check on fn returning fn!!!                         */
/* AM aug-88: Allow expansion of offsetof to be compile-time constant. */
/* BIG thing to do soon: get correct op in error message for things
               like 3[4], !(struct ...).                               */
/* AM 6-2-87:  check args to printf/scanf!                             */
/* AM 24-6-86: Treat 'float' as 'short double' internally.             */

/* forward references */
static Expr *mkassign(AEop op, Expr *a, Expr *b);
static Expr *mkaddr(Expr *a);
static Expr *mkincdec(AEop op, Expr *a);
static Expr *bitfieldvalue(Expr *ebf, SET_BITMAP m, Expr *ewd);

#define orig_(p)  arg1_(p)
#define compl_(p) arg2_(p)

/* type-like things... */

extern void typeclash(AEop op)
{    cc_err(sem_err_typeclash, op);
}

/* Type manipulation -- these are becoming more of an abstract type.    */
/* Exact routine partition in flux.                                     */

#define QUALIFIER_MASK CVBITS

TypeExpr *princtype(TypeExpr *t)
/* Remove 'typedef's from top of type.  Ignore any qualifiers on the    */
/* typedef to the type so qualified.                                    */
/* FW: What is the rationale for this?                                  */
{   Binder *b;
    while (isprimtype_(t,s_typedefname))
    {   if (debugging(DEBUG_TYPE)) cc_msg("Pruning typedef...\n");
        b = typespecbind_(t);
        t = bindtype_(b);
    }
    return t;
}

static SET_BITMAP typedef_qualifiers(TypeExpr *x)
{   SET_BITMAP q = 0;
    while (isprimtype_(x, s_typedefname))
    {   Binder *b = typespecbind_(x);
        q |= typespecmap_(x) & QUALIFIER_MASK;
        x = bindtype_(b);
    }
    return q;
}

SET_BITMAP qualifiersoftype(TypeExpr *x)
{   SET_BITMAP q;
    while (h0_(x) == t_subscript) x = typearg_(x);
    q = typedef_qualifiers(x);
    x = princtype(x);
    while (h0_(x) == t_subscript) x = typearg_(x);
/* AM would like to put typespecmap_ and typeptrmap_ in same place.     */
    return q | QUALIFIER_MASK &
        ((h0_(x) == s_typespec || h0_(x) == t_unknown) ? typespecmap_(x) :
         h0_(x) == t_content || h0_(x) == t_ref
                             || h0_(x) == t_fnap ? typeptrmap_(x) : 0);
}

SET_BITMAP recursivequalifiers(TypeExpr *x)
{   SET_BITMAP q = 0;
    for (;;) {
        while (h0_(x) == t_subscript) x = typearg_(x);
        q |= typedef_qualifiers(x);
        x = princtype(x);
        while (h0_(x) == t_subscript) x = typearg_(x);
        if (h0_(x) == t_content || h0_(x) == t_ref) {
            q |= (QUALIFIER_MASK & typeptrmap_(x));
            x = typearg_(x);
            continue;
        } else if (h0_(x) == t_fnap) {
            q |= (QUALIFIER_MASK & typeptrmap_(x));
        } else if (h0_(x) == s_typespec) {
            q |= (QUALIFIER_MASK & typespecmap_(x));
        }
        return q;
    }
}

#define qualifier_subset(t1, t2) (qualifiers_lost(t1, t2) == 0)

static SET_BITMAP qualifiers_lost(TypeExpr *t1, TypeExpr *t2)
{   SET_BITMAP m1 = qualifiersoftype(t1), m2 = qualifiersoftype(t2);
    return m1 & ~m2;
}

static TypeExpr *mkqualifiedtype_1(TypeExpr *t, SET_BITMAP qualifiers, SET_BITMAP unqualifiers)
{   TypeExpr *p, *q, *r;
    if (qualifiers == 0 && unqualifiers == 0 || h0_(t) == t_ovld) return t;  /* @@@ AM mumble! */
    p = r = NULL;
    for (;;)
    {   /* should there be a routine to clone top-of-a-type?            */
        q = h0_(t) == t_fnap ?
                mkTypeExprfn(t_fnap, typearg_(t), typeptrmap_(t),
                             typefnargs_(t), &typefnaux_(t)) :
                mk_typeexpr1(h0_(t), typearg_(t), (Expr *)typespecbind_(t));
        if (r == NULL)
            r = q;
        else
            typearg_(p) = q;
        p = q;
        switch (h0_(q))
        {
default:    syserr(syserr_mkqualifiedtype, h0_(t));
case t_unknown:
case s_typespec:
            /* NB. this may place the type on another typedef           */
            typespecmap_(q) = (typespecmap_(q) | qualifiers) & ~unqualifiers;
            return r;
case t_content:
case t_ref:
case t_fnap:            /* C++ const (member) functions */
            typeptrmap_(q) = (typeptrmap_(q) | qualifiers) & ~unqualifiers;
            return r;
case t_subscript:
            /* this next line probably indicates that space for a       */
            /* qualifier map field in an array type would be useful.    */
            t = typearg_(t); break;
        }
    }
}

extern TypeExpr *mkqualifiedtype(TypeExpr *t, SET_BITMAP qualifiers)
{
    return mkqualifiedtype_1(t, qualifiers, (SET_BITMAP)0);
}

TypeExpr *prunetype(TypeExpr *t)
/* Remove 'typedef's from top of type.  Add any qualifiers on the       */
/* typedef to the type so qualified -- these are assumed to be          */
/* relatively rare (maybe one day re-implement).                        */
{
    return mkqualifiedtype(princtype(t), typedef_qualifiers(t));
}

bool isvolatile_type(TypeExpr *x)
{   return (qualifiersoftype(x) & bitoftype_(s_volatile)) != 0;
}

bool isunaligned_type(TypeExpr *x)
{   if (qualifiersoftype(x) & bitoftype_(s_unaligned)) return YES;
    x = princtype(x);
    if isclasstype_(x)
      return (tagbindbits_(typespectagbind_(x)) & TB_UNALIGNED) != 0;
    return NO;
}

bool pointerfree_type(TypeExpr *t) {
    t = princtype(t);
    switch (h0_(t))
    {
case t_content:
case t_ref:       return NO;
case t_subscript: return pointerfree_type(typearg_(t));
case s_typespec:  if (typespecmap_(t) & CLASSBITS)
                  {   ClassMember *l = tagbindmems_(typespectagbind_(t));
                      for (; l != 0; l = memcdr_(l))
                          if (!pointerfree_type(memtype_(l))) return NO;
                  }
default:          return YES;
    }
}

#define typeisbitfield_(m) (m & BITFIELD)

bool isbitfield_type(TypeExpr *t)
{   t = princtype(t);
/* Beware: BITFIELD should never qualify a typedef (syn.c ensures)      */
/* (BITFIELD can only occur at the top level in types taken from        */
/* struct/unions).  Else princtype() risks skipping a 'BITFIELD'.       */
    return (h0_(t) == s_typespec && (typespecmap_(t) & BITFIELD));
}

/* The call to unbitfield_type() replaces a use of 'te_int'.            */
TypeExpr *unbitfield_type(TypeExpr *t)
{   /* Return the corresponding simple type, for a pseudo-cast in       */
    /* assignment and initialisation, for e.g. implicit cast err/warn.  */
    if (h0_(t) == s_typespec)
    {   SET_BITMAP m = typespecmap_(t);
        if (typeisbitfield_(m))
#ifdef ONE_DAY_SOON /* including C++? */
            return primtype2_(m & ~BITFIELD, typespectagbind_(t));
#endif
            return m & bitoftype_(s_enum) ?
                     primtype2_(m & ~BITFIELD, typespectagbind_(t))
                   : int_islonglong_(m) ?
                     te_llint
                   : te_int;
    }
    syserr(syserr_unbitfield, t);
    return te_int;
}

static TypeExpr *bf_promotedtype2(
    SET_BITMAP m, int32 sparebits, TypeExpr *signedtype, TypeExpr *unsignedtype) {
    if (issignedchar_(m)
        || (sparebits != 0 && !HasFeature(Feature_PCC)))
        return signedtype;
    else
        return unsignedtype;
}

  /* Merge unbitfield_type() and bf_promotedtype()?                       */
static TypeExpr *bf_promotedtype(TypeExpr *t, int32 size)
{   /* caller ensures that 't' is a s_typespec of BITFIELD.             */
    /* promote: enum bit fields to enum, else int/unsigned int.         */
    /* Maybe long bit fields (in C++) should promote to long.           */
    if (h0_(t) == s_typespec)
    {   SET_BITMAP m = typespecmap_(t);
        if (typeisbitfield_(m))
            return
                (m & bitoftype_(s_enum)) ?
                    primtype2_(m & ~BITFIELD, typespectagbind_(t))
                : int_islonglong_(m) ?
                    bf_promotedtype2(m, 8 * sizeof_longlong - size, te_llint, te_ullint)
                : (m & bitoftype_(s_long)) ?
                    bf_promotedtype2(m, 8 * sizeof_long - size, te_lint, te_ulint)
                :   bf_promotedtype2(m, 8 * sizeof_int - size, te_int, te_uint);
    }
    syserr(syserr_bf_promote, t);
    return te_int;
}

bool isvoidtype(TypeExpr *t)
{   t = princtype(t);
    return (h0_(t) == s_typespec && (typespecmap_(t) & bitoftype_(s_void)));
}

/* Note: true for 'void*' and 'void*const' but not 'const void*'        */
bool isptrtovoidtype(TypeExpr *t)
{   t = princtype(t);
    return h0_(t) == t_content && equivtype(typearg_(t), te_void);
}

static bool indexable(TypeExpr *t)
{   t = princtype(t);           /* can ignore typedef qualifiers.       */
    return (h0_(t) == t_content

            /* but not x after 'int A::*x' etc.                         */
            && h0_(princtype(typearg_(t))) != t_coloncolon

           );
}

static bool isptrtomember(TypeExpr *t)
{   t = princtype(t);           /* can ignore typedef qualifiers.       */
    return (h0_(t) == t_content &&
            h0_(princtype(typearg_(t))) == t_coloncolon);
}

/* For the two following functions/macros, t must satisfy indexable()   */
#define indexee(t) (typearg_(princtype(t)))
#define strideofindexee(t) (sizeoftype(indexee(t)))

static bool indexer(TypeExpr *t)
{   /* the type reading routine 'or's the 'int' bit
       in if we read unsigned/signed/short/long and no honest type.
       Moreover, we assume 'unary coercions' to be done - so no char/enum.
    */
    t = princtype(t);           /* can ignore typedef qualifiers.       */
    return isprimtypein_(t,bitoftype_(s_int)|bitoftype_(s_bool));
}

static bool sameenum(TypeExpr *a, TypeExpr *b)
{   a = princtype(a), b = princtype(b);
    return isprimtype_(a,s_enum) && isprimtype_(b,s_enum) &&
        typespectagbind_(a) == typespectagbind_(b);
}

/* AE-tree oriented things... */

TypeExpr *typeofexpr(Expr *x)
{   AEop op;
    TypeExpr *t;
    switch (op = h0_(x))
    {   case s_binder:
            t = bindtype_(exb_(x));
            break;

        case s_member:
            if (bindparent_(exb_(x)) == NULL)
                syserr("Orphan member $b", exb_(x));
/* Note that we can't do the next line for t_ovld (in s_binder above).  */
            t = (TypeExpr *)syn_list3(t_coloncolon, bindtype_(exb_(x)),
                                      bindparent_(exb_(x)));
            break;

        case s_floatcon:
/* perhaps slave all three combinations - or put a type_ field in s_floatcon */
            t = exf_(x)->floatlen == bitoftype_(s_double) ?
                te_double : primtype_(exf_(x)->floatlen);
            break;
        case s_int64con:
          t = (int64map_(x) & bitoftype_(s_unsigned)) ? te_ullint : te_llint;
          break;
        case s_string:
          { int32 n = 0; StringSegList *p;
            for (p = exs_(x)->strseg; p != 0; p = p->strsegcdr)
                n += p->strseglen;
#ifdef PASCAL /*ECN*/
            t = mkArrayType(te_char, mkintconst(te_int, n+1, 0),
                  mkOrdType(bitoftype_(s_int), s_ellipsis, te_int,
                    lit_one,
                    mkintconst(te_int, n, 0)), b_packed);
#else
            t = mk_typeexpr1(t_subscript, te_stringchar, mkintconst(te_int,n+1,0));
#endif
          } break;
#ifdef EXTENSION_UNSIGNED_STRINGS
        case s_ustring:
          { int32 n = 0; StringSegList *p;
            for (p = exs_(x)->strseg; p != 0; p = p->strsegcdr)
                n += p->strseglen;
            t = mk_typeexpr1(t_subscript, te_ustringchar, mkintconst(te_int,n+1,0));
          } break;
#endif
        case s_wstring:
          { int32 n = 0; StringSegList *p;
            for (p = exs_(x)->strseg; p != 0; p = p->strsegcdr)
                n += p->strseglen;
            t = mk_typeexpr1(t_subscript, te_wstringchar,
                             mkintconst(te_int, n/sizeof_wchar + 1, 0));
          } break;
        case s_error:            /* @@@ remove soon? */
            t = te_int; break;   /* for sizeof() or sizeof(1.0%2.0) */
#ifdef PASCAL /*ECN*/
        case s_set:
#endif
        case s_typespec:
        case s_integer:
            t = type_(x); break;
        default:
            if (hastypefield_(op)) { t = type_(x); break; }
            syserr(syserr_typeof, (long)op);
            t = te_int;
            break;
    }
/* The clever macro for debugging() means that the next line generates  */
/* no code if ENABLE_TYPE is not #defined.                              */
    if (debugging(DEBUG_TYPE))
    {   eprintf("Type of "); pr_expr(x);
        eprintf(" is "); pr_typeexpr_nl(t, 0);
    }
    return t;
}

/* @@@ contemplate a routine 'TypeExpr -> AEop' to avoid
   2-level switches and make code more representation independent
*/


SET_BITMAP typeofenumcontainer(TagBinder *tb)
{   static SET_BITMAP const a[] = {
        bitoftype_(s_char),
        bitoftype_(s_short)|bitoftype_(s_int),
        bitoftype_(s_int),
        bitoftype_(s_long)|bitoftype_(s_int),
        bitoftype_(s_unsigned)|bitoftype_(s_char),
        bitoftype_(s_unsigned)|bitoftype_(s_short)|bitoftype_(s_int),
        bitoftype_(s_unsigned)|bitoftype_(s_int),
        bitoftype_(s_unsigned)|bitoftype_(s_long)|bitoftype_(s_int)
    };
    return a[(tagbindbits_(tb) & TB_CONTAINER) >> TB_CONTAINER_SHIFT];
}

static int32 alignofclass(TagBinder *b)
{   int32 n = alignof_struct;
    if (tagbindbits_(b) & TB_UNALIGNED)
        return 1;

    /* Short circuit the code if it can never update 'n':         */
    if (alignof_max > alignof_struct)
    {   ClassMember *l = tagbindmems_(b);
/* This code should never be called when the struct/union is not defined, */
/* but, even if it is no harm will occur as then l==0.  (!TB_DEFD)        */
/* Note we can safely treat bit field members as non-bit field members.   */
        for (; l != 0; l = memcdr_(l))
            if (is_datamember_(l))
                n = max(n, alignoftype(memtype_(l)));
    }
    return n;
}

/* Beware alignoftype(t_ref) == alignoftype(t_content).                 */
int32 alignoftype(TypeExpr *x)
/* Gives mininum alignment (power of 2) for object of type. The current view
   is given in mip/defaults.h. Arrays get aligned as members (ANSI require).
   "alignof_double" may be set to 4 or 8 in target.h.
   Internal contents of structs are always examined, to give the struct the
   alignment of the most strictly aligned member (or alignof_struct, if that's
   stricter). Bitfields are treated as requiring the alignment of the type of
   the member (or its container if the type is an enumeration): in strict ansi
   mode, always alignof_int, since some signedness of int is the only
   permitted type. Minimal alignment of alignof_struct (normally 4) means
   "sizeof(struct {char x}[6])" is normally 24.
   (But alignof_struct is user-alterable).
*/
{   SET_BITMAP m;
    Binder *b;
    switch (h0_(x))
    {
case s_typespec:
        m = typespecmap_(x);
        switch (m & -m)    /* LSB - unsigned/long etc. are higher */
        {
    case bitoftype_(s_typedefname):
            b = typespecbind_(x);
            return alignoftype(bindtype_(b));
    case bitoftype_(s_char):
            return 1;
    case bitoftype_(s_enum):
            m = typeofenumcontainer(typespectagbind_(x));
            if (m & bitoftype_(s_char)) return 1;
            /* drop through */
    case bitoftype_(s_bool):
    case bitoftype_(s_int):
            return int_decodealign_(m);
    case bitoftype_(s_double):
            return m & bitoftype_(s_short) ? alignof_float :
                   m & bitoftype_(s_long) ? alignof_ldble : alignof_double;
    case bitoftype_(s_struct):
    case bitoftype_(s_class):
    case bitoftype_(s_union):
          return alignofclass(typespectagbind_(x));
    case bitoftype_(s_void):            /* pure cowardice */
            cc_rerr(sem_rerr_sizeof_void);
            return alignof_int;
    default:
            break;
        }
case t_unknown:
    /* same as te_void */
    return alignof_int;
default:
        syserr(syserr_alignoftype, (long)h0_(x), (long)typespecmap_(x));
case t_content:
case t_ref:
        return alignof_ptr;
case t_subscript:
        return alignoftype(typearg_(x));
    }
}

/* NB. this (structfield()) MUST be kept in step with initstaticvar (q.v.).
   Everyone else (sizeoftype, findfield, dbg_structrep) needing
   to know about position and size of fields in structures uses
   this function. */

void structpos_init(StructPos *p, TagBinder *tb) {
    p->n = p->bitoff = 0;
    p->padded = NO;
    /* this initialization is special in that static data mem gets described
       almost as if it is a s_member. */
    p->bsize = 0;
    /* tb is NULL for call from debug-table generator to handle undefined */
    /* structs                                                            */
    p->nopadding = tb != NULL &&
                   (tagbindbits_(tb) & TB_UNALIGNED) != 0;
    p->endofcontainer = 0;
}

static int32 sizeofintegraltype(TypeExpr *x, SET_BITMAP m)
{
    switch (m & -m)    /* LSB - unsigned/long etc. are higher */
    {
    case bitoftype_(s_char):
        break;
    case bitoftype_(s_enum):
        m = typeofenumcontainer(typespectagbind_(x));
        if (m & bitoftype_(s_char)) break;
        /* drop through */
    case bitoftype_(s_bool):
    case bitoftype_(s_int):
        return int_decodelength_(m);
    }
    return 1;
}

bool structfield(ClassMember *l, int32 sort, StructPos *p)
{   /* 2nd arg should probably be a bool (struct/class vs union).       */
    int32 n = p->n, bitoff = p->bitoff;
    TypeExpr *te = memtype_(l);
    p->padded = NO;
    if (!is_datamember_(l)) return NO;
    /*if (istypevar(te)) { p->woffset = 0; return YES; }*/
    if (isbitfield_type(te))
    {   /* Bitfields are packed into objects having the type of the member */
        /* (for enumerations, the type of the enumeration's container).    */
        /* In strict ANSI C, this is always (some sign of) int.            */
        int32 k = membits_(l);
        int32 sizeofcontainer = sizeofintegraltype(te, typespecmap_(te));
        int32 szmask = sizeofcontainer*8 - 1;
        int32 boff;
        if (bitoff == 0)
        {   int32 oldn = n;
            n = padsize(n, alignof_member);        /* min member alignment */
            if (oldn != n) p->padded = YES;
            p->endofcontainer = n + sizeofcontainer;
            if ((n & (alignof_int-1)) != 0)
            {   /* though a field's container may start on any boundary,   */
                /* the structpos representation requires bit offset within */
                /* the containing int.                                     */
                bitoff = (n & (alignof_int-1)) * 8;
                n &= ~(alignof_int-1);
            }
        }
        /* A zero-sized bifield in ANSI mode says "pack no more here".     */
        /* (We now interpret as "no more into this container", rather than */
        /* "no more into this word").                                      */
        /* We ignore this directive if nothing has yet been packed.        */
        if (k == 0 && bitoff > 0) {
            int32 endofcontainer = (bitoff + szmask) & ~szmask;
            k = endofcontainer - bitoff;
        }

        /* If this bitfield would overflow its container, start a new one  */
        if (((bitoff & szmask) + k) > (szmask+1)) {
            int32 end;
            bitoff = (bitoff + szmask + 1) & ~szmask;
            if (bitoff >= 8 * sizeof_int) {
                int32 words = bitoff / (8 * sizeof_int);
                n += words * sizeof_int;
                bitoff -= words * (8 * sizeof_int);
            }
            end = n + (bitoff/8) + sizeofcontainer;
            /* If we're packing from the opposite end of the container,    */
            /* containers can't be allowed to overlap                      */
            if (HasFeature(Feature_ReverseBitfields))
                end = p->endofcontainer;
            if (end > p->endofcontainer) p->endofcontainer = end;
        } else {
            int32 wordbits = sizeofcontainer == sizeof_longlong ? 8 * sizeof_longlong :
                                                                  8 * sizeof_int;
            if (bitoff >= wordbits) {
                n += (bitoff / (8 * sizeof_int)) * sizeof_int;
                bitoff = 0;
                p->endofcontainer = n + sizeofcontainer;
            }
        }
        if (HasFeature(Feature_ReverseBitfields)) {
          /* Pack from the opposite end of the container */
            int32 endcontaineroffset = (p->endofcontainer & (alignof_int-1)) * 8;
            int32 containerbits = sizeofcontainer * 8;
            int32 startcontaineroffset = endcontaineroffset - containerbits;
            boff = endcontaineroffset - (bitoff - startcontaineroffset + k);
        } else
            boff = bitoff;

        p->woffset = n, p->boffset = boff, p->bsize = k, p->typesize = 0;
        if (sort != bitoftype_(s_union)) bitoff += k;
    }
    else
    {   if (bitoff != 0) {
            /* The unused part of a trailing bitfield container is allowed */
            /* to overlap non-bitfield fields                              */
            if (HasFeature(Feature_ReverseBitfields))
                n = p->endofcontainer;
            else
                n += (bitoff+7) / 8;
            bitoff = 0;
        }
#ifdef PASCAL /*ECN*/
        n = l->offset;
#else
        if (!p->nopadding)
        {   int32 oldn = n;
            n = padsize(n, alignof_member);     /* min member alignment */
            n = padsize(n, alignoftype(te));
            if (oldn != n) p->padded = YES;
        }
#endif
        p->woffset = n, p->boffset = 0, p->bsize = 0;

        if ((attributes_(l) & CB_BASE) &&
            tagbindmems_(typespectagbind_(princtype(te))) == NULL)
            p->typesize = 0;
        else
            p->typesize = sizeoftype(te);
        if (sort != bitoftype_(s_union)) n += p->typesize;
    }
    p->n = n, p->bitoff = bitoff;
    return YES;
}

int32 sizeofclass(TagBinder *b, bool *padded)
{   ClassMember *l;
    int32 n = 0;
    bool pad = NO;
    if (tagbindbits_(b) & TB_OPAQUE)
        cc_rerr(sem_rerr_sizeof_opaque, b);
    if (tagbindbits_(b) & TB_SIZECACHED)
    {   int32 n = b->cachedsize;
        if (n < 0) {
          if (padded != NULL) *padded = YES;
          return -n;
        } else {
          if (padded != NULL) *padded = NO;
          return n;
        }
    }
    if (!(tagbindbits_(b) & (TB_DEFD|TB_UNDEFMSG)))
    {   cc_err(sem_err_sizeof_struct, b);
        tagbindbits_(b) |= TB_UNDEFMSG;
    }
    if (tagbindbits_(b) & bitoftype_(s_union))
    {
        for (l = tagbindmems_(b); l != 0; l = memcdr_(l))
            if (is_datamemberoranon_(l)) {
                TypeExpr *te = memtype_(l);
                if (isbitfield_type(te))
                    n = max(n, sizeofintegraltype(te, typespecmap_(te)));
                else
                    n = max(n, sizeoftype(te));
                memwoff_(l) = 0;
            }
            /* Use the next line for C too?  OK by ANSI.    */
        if (n == 0) n = 1;          /* empty C++ union.     */

        n = padsize(n, alignofclass(b));
               /* often alignof_struct */
    } else
    {   StructPos p;
        structpos_init(&p, b);
        for (l = tagbindmems_(b); l != 0; l = memcdr_(l))
        {   if (!structfield(l, bitoftype_(s_struct), &p)) {
               if (is_datamemberoranon_(l))
                   memwoff_(l) = p.woffset;
               continue;
            }
            memboff_(l) = (uint8)p.boffset; membits_(l) = (uint8)p.bsize;
            memwoff_(l) = p.woffset;
            pad = pad | p.padded;
            if (p.n > n) n = p.n;
        }
#ifdef PASCAL /*ECN*/
        p.n = n;
#endif
        if (p.bitoff != 0) p.n = p.endofcontainer;

        /* Use the next line for C too?  OK by ANSI.    */
        if (p.n == 0) p.n = 1;          /* empty C++ struct.    */

        if (p.nopadding)
            n = p.n;
        else
        {   n = padsize(p.n, alignofclass(b));
                      /* often alignof_struct */
            if (n != p.n) pad = YES;
            if (pad && padded != NULL)
                *padded = YES;
        }
    }
    if (tagbindbits_(b) & TB_DEFD) {
        b->cachedsize = pad ? -n : n;
        tagbindbits_(b) |= TB_SIZECACHED;
    }
    return n;
}

/* Beware sizeoftype(t_ref) == sizeoftype(t_content).                   */
/* syn.c(cpp_sizeoftype) takes care of C++ rules about sizeof.          */
int32 sizeoftypenotepadding(TypeExpr *x, bool *padded)
{   SET_BITMAP m;
    switch (h0_(x))
    {
case t_unknown:
       /* treated as void but without the diagnostic. */
        return 1;

case s_typespec:
        m = typespecmap_(x);
        if (m & BITFIELD)
            cc_rerr(sem_rerr_sizeof_bitfield);
        switch (m & -m)    /* LSB - unsigned/long etc. are higher */
        {
        case bitoftype_(s_char):
            if (m & BITFIELD)
                cc_rerr(sem_rerr_sizeof_bitfield);
            return 1;
        case bitoftype_(s_enum):
            if (m & BITFIELD)
                cc_rerr(sem_rerr_sizeof_bitfield);
            m = typeofenumcontainer(typespectagbind_(x));
            if (m & bitoftype_(s_char)) return 1;
            /* drop through */
        case bitoftype_(s_bool):
        case bitoftype_(s_int):
            if (m & BITFIELD)
                cc_rerr(sem_rerr_sizeof_bitfield);
            return int_decodelength_(m);
        case bitoftype_(s_double):
            return (m & bitoftype_(s_short)) ? sizeof_float :
                   (m & bitoftype_(s_long)) ? sizeof_ldble : sizeof_double;
        case bitoftype_(s_struct):
        case bitoftype_(s_class):
        case bitoftype_(s_union):
            return sizeofclass(typespectagbind_(x), padded);
        case bitoftype_(s_typedefname):
            return sizeoftype(bindtype_(typespecbind_(x)));
        case bitoftype_(s_void):
            cc_rerr(sem_rerr_sizeof_void);
            return 1;
        default:
            break;
        }
default:
        syserr(syserr_sizeoftype, (long)h0_(x), (long)typespecmap_(x));
case t_subscript:
        {   int32 n = sizeoftype(typearg_(x));
            if (typesubsize_(x))
                n *= (h0_(typesubsize_(x)) == s_binder &&
                      is_template_arg_binder(typesubsize_(x))) ? 1 : evaluate(typesubsize_(x));
            /* pretensions, don't matter cos there is no template obj anyway. */
            else
                typesubsize_(x) = globalize_int(1),
                cc_rerr(sem_rerr_sizeof_array);
            return n;
        }
case t_coloncolon:
        /* For int A::*x; ... x+1; ... and sizeof(B::b).            */
        return sizeoftype(typearg_(x));
case t_ovld:
case t_fnap:
        cc_rerr(sem_rerr_sizeof_function);
        /* drop through */
case t_content:
case t_ref:
        return sizeof_ptr;
    }
}

bool sizeoftypelegal(TypeExpr *x)
{   SET_BITMAP m;
    x = princtype(x);
    switch (h0_(x))
    {   case s_typespec:
            m = typespecmap_(x);
            if (m & BITFIELD) return NO;
            switch (m & -m)    /* LSB - unsigned/long etc. are higher */
            {   case bitoftype_(s_struct):
                case bitoftype_(s_class):
                case bitoftype_(s_union):
                    if (tagbindbits_(typespectagbind_(x)) & (TB_DEFD|TB_UNDEFMSG))
                        return YES;
                    break;
                case bitoftype_(s_void):
                    break;
                default:
                    return YES;
            }
            break;
        case t_subscript:
            if (typesubsize_(x) != 0 && h0_(typesubsize_(x)) != s_binder) return YES;
            break;
        case t_coloncolon:
            /* For int A::*x; ... x+1; ... and sizeof(B::b).            */
            return sizeoftypelegal(typearg_(x));
        case t_ovld:
        case t_fnap:
            break;
        case t_content:
        case t_ref:
            return YES;
    }
    return NO;
}

/* the C rules on type equivalence mean that equivtype does not have
   to worry about circularity */
/* equivtype notionally returns a boolean, but the true case is separated */
/* into result 2, identical (LISP equal) and result 1, merely equivalent. */
/* BEWARE: now (maybe temporarily) differing qualifiers on fn args can    */
/* still give result 2.                                                   */
/* AM:  @@@ In the long term, equivtype should also compute the unified   */
/*      type of t1 and t2, but beware store lifetime use, and cacheing.   */
static int equivtype_4(TypeExpr *t1, TypeExpr *t2,
                       SET_BITMAP m1, SET_BITMAP m2,
                       bool widenformals)
{   int sofar = 2;
    for (;; (t1 = typearg_(t1), t2 = typearg_(t2)))
    {   m1 |= typedef_qualifiers(t1), m2 |= typedef_qualifiers(t2);
        t1 = princtype(t1),           t2 = princtype(t2);
        if (h0_(t1) != h0_(t2)) return 0;

        switch (h0_(t1))
        {
    case s_typespec:
                m1 |= typespecmap_(t1), m2 |= typespecmap_(t2);
#define CLASSORSTRUCT (bitoftype_(s_class)|bitoftype_(s_struct))
                if (m1 & CLASSORSTRUCT) m1 |= CLASSORSTRUCT;
                if (m2 & CLASSORSTRUCT) m2 |= CLASSORSTRUCT;
#undef CLASSORSTRUCT
                /* this next line does a lot:
                   1) it checks same basic type (struct/unsigned int/etc)
                      via set equality on type specifiers.
                   2) it tests pointer equality on tag binders.
                   3) it relies on typespecbind_() being 0 for simple types */
                return (m1 == m2 && (typespecbind_(t1) == typespecbind_(t2) ||
                    (LanguageIsCPlusPlus && is_comparable_specialization(t1, t2)))) ?
                              sofar :
#ifndef SIGNEDNESS_MATTERS
                       /* the 1 result here is slight paranoia re typedefs */
                       (m1 & m2 & bitoftype_(s_int) &&
                          (m1 & ~bitoftype_(s_signed)) ==
                          (m2 & ~bitoftype_(s_signed)))     ? 1 :
#endif
                              0;
    case t_coloncolon:
            if (typespecbind_(t1) != typespecbind_(t2)) return 0;
            continue;         /* now check elt types, with qualifiers */
    case t_unknown:
        return (t1 == t2 && m1 == m2) ? 2 : 1;
    case t_content:
    case t_ref:
                /* two pointers match if they have the same const/volatile  */
                /* attribute and point to compatible types.  Ditto refs.    */
#ifdef PASCAL /*ECN*/
                if (t1 == t2) return 2;
#endif
                if ((m1|typeptrmap_(t1)) != (m2|typeptrmap_(t2))) return 0;
                m1 = m2 = 0;
                continue;
    case t_subscript:                /* should check sizes (if any) match   */
            {   Expr *e1 = typesubsize_(t1), *e2 = typesubsize_(t2);
                /* masquerade as open arrays */
                if (e1 && h0_(e1) == s_binder) e1 = NULL;
                if (e2 && h0_(e2) == s_binder) e2 = NULL;
                if (e1 != 0 && e2 != 0)
                {   if (evaluate(e1) != evaluate(e2)) return 0;
                }
                else
                {   if (e1 != e2) sofar = 1;
                }
            }
            continue;         /* now check elt types, with qualifiers */
    case t_fnap:
/* Latest ANSI draft (Dec 88) is finally precise about type             */
/* equivalence.  Note that allowing () to be equivalent to non-()       */
/* things makes 'equivtype' not an equivalence relation!!!              */
            {   /* check arg types match... */
                FormTypeList *d1 = typefnargs_(t1), *d2 = typefnargs_(t2);
                bool old1 = (t1->fnaux.oldstyle != 0);
                bool old2 = (t2->fnaux.oldstyle != 0);
                if (maxargs_(t1) != maxargs_(t2) ||
                    minargs_(t1) != minargs_(t2) ||
                    t1->fnaux.variad != t2->fnaux.variad ||
                    t1->fnaux.flags != t2->fnaux.flags ||
                    t1->fnaux.oldstyle != t2->fnaux.oldstyle) sofar = 1;
/* The next 3 lines ensure "int f(); int f(x) char x; {}" is OK, but    */
/* that "int f(); int f(char x) {}" and "int f(); int f(int x,...) {}"  */
/* give the required ANSI errors.                                       */
                if (fntypeisvariadic(t1) != fntypeisvariadic(t2)) return 0;
                if (d1 == 0 && maxargs_(t1) == 999) d1 = d2, old1 = 1;
                if (d2 == 0 && maxargs_(t2) == 999) d2 = d1, old2 = 1;
                while (d1 && d2)
                {   TypeExpr *ft1 = d1->fttype, *ft2 = d2->fttype;
/* Function and array types were promoted to pointers by rd_declrhslist */
                    if (old1 || widenformals) ft1 = promoted_formaltype(ft1);
                    if (old2 || widenformals)
#if 0
                    {   TypeExpr *promoted = promoted_formaltype(ft2);
                        if (old2 && !old1 && HasFeature(FeaturePCC) &&
                            !qualfree_equivtype(ft1, promoted))
                            cc_pccwarn("type $t doesn't match promoted type", ft1);
                        else
                            ft2 = promoted;
                    }
#else
                        ft2 = promoted_formaltype(ft2);
#endif
                    switch (qualfree_equivtype(ft1, ft2))
                    { default: return 0;
                      case 1: sofar = 1;
                      case 2: d1 = cdr_(d1), d2 = cdr_(d2);
                    }
                }
                /*
                 * Check either both fn's have or omit '...'
                 */
                if (d1 != d2) return 0;
            }
            if ((m1|typeptrmap_(t1)) != (m2|typeptrmap_(t2))) return 0;
            m1 = m2 = 0;
            continue;    /* now check results */
    default:
            syserr(syserr_equivtype, (long)h0_(t1));
            return 0;
        }
    }
}

/* equivtype notionally returns a boolean, but the true case is separated */
/* into result 2, identical (LISP equal) and result 1, merely equivalent. */
/* BEWARE: now (maybe temporarily) differing qualifiers on fn args can    */
/* still give result 2.                                                   */
int equivtype(TypeExpr *t1, TypeExpr *t2)
{
   return equivtype_4(t1, t2, 0, 0, NO);
}

/* @@@ I wish the use of this was documented!                           */
int widened_equivtype(TypeExpr *t1, TypeExpr *t2)
{
   return equivtype_4(t1, t2, 0, 0, !HasFeature(Feature_Fussy) &&
                                    !(config & CONFIG_UNWIDENED_NARROW_ARGS));
}

/* BEWARE: there is a sordid little ambiguity/accident in the Dec 88    */
/* ANSI draft (see equality ops (ignoring qualifiers) and type          */
/* qualifiers on array types) concerned with t1 (or t2) being a const   */
/* qualified array via typedef) and the other an array of const.        */
int qualfree_equivtype(TypeExpr *t1, TypeExpr *t2)
{   /* forcing ON all qualifiers effectively ignores them.              */
    return equivtype_4(t1, t2, QUALIFIER_MASK, QUALIFIER_MASK, NO)/* != 0*/;
    /* HCM see above (case t_fnap of equivtype_4) why normalising the   */
    /* result to 0/1 isn't a good idea                                  */
}

static FormTypeList *compositetypelist(FormTypeList *d1, FormTypeList *d2,
                                       bool old1, bool old2);

/* t3 = compositetype(t1,t2) forms the composite type of t1 and t2      */
/* into t3, if t1 and t2 are compatible(equivtype), otherwise it        */
/* returns 0.  See ANSI draft.                                          */
/* In implementation, the routine tries to return t1 if this is the     */
/* composite type to save store.                                        */
/* 'u' is set if top-level qualifiers are merely to be unioned.         */
/* 'm1' and 'm2' keep up with typedefs which have been pruned -- note   */
/* the behaviour for arrays (t_subscript).                              */
static TypeExpr *compositetype_5(TypeExpr *t1, TypeExpr *t2,
                          SET_BITMAP m1, SET_BITMAP m2, bool u)
{   TypeExpr *t3;
    if (t1 == t2 && m1 == m2) return t1;
    m1 |= typedef_qualifiers(t1), m2 |= typedef_qualifiers(t2);
    t1 = princtype(t1),           t2 = princtype(t2);
    if (h0_(t1) != h0_(t2)) return 0;
    switch (h0_(t1))
    {
case s_typespec:
            m1 |= typespecmap_(t1), m2 |= typespecmap_(t2);
            if (u) m1 |= m2 & QUALIFIER_MASK, m2 |= m1 & QUALIFIER_MASK;
            /* this next line does a lot:
               1) it checks same basic type (struct/unsigned int/etc)
                  via set equality on type specifiers.
               2) it tests pointer equality on tag binders.
               3) it relies on typespecbind_() being 0 for simple types */
            if (!(m1 == m2 && typespecbind_(t1) == typespecbind_(t2)
#ifndef SIGNEDNESS_MATTERS
                    || (m1 & m2 & bitoftype_(s_int) &&
                         ((m1^m2) & ~bitoftype_(s_signed)) == 0)
#endif
                   )) return 0;
            return
#ifdef REUSE
                typespecmap_(t1) == m1 ? t1 :
                typespecmap_(t2) == m1 ? t2 :
#endif
                primtype2_(m1, typespecbind_(t1));
    case t_content:
    case t_ref:
            m1 |= typeptrmap_(t1), m2 |= typeptrmap_(t2);
            if (u) m1 |= m2 & QUALIFIER_MASK, m2 |= m1 & QUALIFIER_MASK;
            if (m1 != m2) return 0;
            t3 = compositetype_5(typearg_(t1),typearg_(t2),0,0,0);
            return t3 == 0 ? 0 :
#ifdef REUSE
                   t3 == typearg_(t1) && m1 == typeptrmap_(t1) ? t1 :
#endif
                   mk_typeexpr1(h0_(t1), typearg_(t1), (Expr *)(IPtr)m1);
    case t_subscript:
          { Expr *e1 = typesubsize_(t1), *e2 = typesubsize_(t2), *e3;
            if (e1 && h0_(e1) == s_binder) e1 = NULL;
            if (e2 && h0_(e2) == s_binder) e2 = NULL;
            if (e1 != 0 && e2 != 0)
            {   if (evaluate(e1) != evaluate(e2)) return 0;
            }
            e3 = e1 ? e1 : e2;
            t3 = compositetype_5(typearg_(t1),typearg_(t2),m1,m2,u);
            return t3 == 0 ? 0 :
#ifdef REUSE
                   t3 == typearg_(t1) && e3 == e1 && m1 == 0 ? t1 :
#endif
                 mk_typeexpr1(t_subscript, typearg_(t1), (Expr *)e3);
          }
    case t_fnap:
          { TypeExprFnAux s;
            FormTypeList *d1 = typefnargs_(t1), *d2 = typefnargs_(t2), *d3;
            bool old1 = (t1->fnaux.oldstyle != 0);
            bool old2 = (t2->fnaux.oldstyle != 0);
            int32 max1 = maxargs_(t1), max2 = maxargs_(t2), max3 = max1;
            m1 |= typeptrmap_(t1), m2 |= typeptrmap_(t2);
            if (u) m1 |= m2 & QUALIFIER_MASK, m2 |= m1 & QUALIFIER_MASK;
            if (m1 != m2) return 0;
/* The code here mirrors that in equivtype().                           */
            if (fntypeisvariadic(t1) != fntypeisvariadic(t2)) return 0;
            if (d1 == 0 && max1 == 999) d1 = d2, old1 = 1, max3 = max2;
            if (d2 == 0 && max2 == 999) d2 = d1, old2 = 1, max3 = max1;
            if (d1 == 0 && d2 == 0)
                d3 = 0;
            else
            {   d3 = compositetypelist(d1,d2,old1,old2);
                if (d3 == 0) return 0;
            }
            t3 = compositetype_5(typearg_(t1),typearg_(t2),0,0,0);
            return t3 == 0 ? 0 :
#ifdef REUSE
/*                 t3 == typearg_(t1) && d3 == d1 && ... ? t1 :         */
#endif
                mkTypeExprfn(t_fnap, t3, m1, d3,
                    packTypeExprFnAux(s,
                                (int)length((List *)d3),     /* vestige */
                                (int)max3,
                                0,      /* variad: not special          */
                                0,      /* oldstyle: new                */
                                0       /* flags: none */
                             ));
          }
    default:
            syserr(syserr_compositetype, (long)h0_(t1));
            return 0;
    }
}

static TypeExpr *qualunion_compositetype(TypeExpr *t1, TypeExpr *t2)
{    return compositetype_5(t1,t2,0,0,1);
}

static FormTypeList *compositetypelist(FormTypeList *d1, FormTypeList *d2,
                                       bool old1, bool old2)
{   if (d1==0 || d2==0) return 0;
    {   TypeExpr *ft1 = d1->fttype, *ft2 = d2->fttype, *tc;
        FormTypeList *d3;
/* Function and array types were promoted to pointers by rd_declrhslist */
        if (old1) ft1 = promoted_formaltype(ft1);
        if (old2) ft2 = promoted_formaltype(ft2);
        tc = qualunion_compositetype(ft1, ft2);
        if (tc == 0) return 0;
        d3 = mkFormTypeList(0, d1->ftname, tc,
                            d1->ftdefault ? d1->ftdefault : d2->ftdefault);
        if (cdr_(d1) != 0 || cdr_(d2) != 0)
        {   FormTypeList *d4 = compositetypelist(cdr_(d1), cdr_(d2),
                                                 old1, old2);
            if (d4 == 0) return 0;
            cdr_(d3) = d4;
        }
        return d3;
    }
}

/* lubtype() and friends return a type if OK, or give an error message
   and return 0.  Worry that they are still rather ragged.
   Note that 'the usual unary coercions' omit 'char' and (possibly) float.
   BEWARE: result type is ASSUMED to be princtype'd by caller. Since
   result is an r-value qualifiers are irrelevant.
*/
static TypeExpr *lubtype(AEop op, TypeExpr *t1, TypeExpr *t2)
/* Take care of 'the usual coercions' for e.g. s_times.
   Relations are done separately, as are the pointer cases of s_plus */
{   TypeExpr *x1 = princtype(t1), *x2 = princtype(t2);
    SET_BITMAP m1 = typespecmap_(x1), m2 = typespecmap_(x2);
    if (h0_(x1) == s_typespec && h0_(x2) == s_typespec &&
        (m1 & ARITHTYPEBITS) != 0 && (m2 & ARITHTYPEBITS) != 0)
    {   if ((m1 | m2) & bitoftype_(s_double))
        {   if (!floatableop_(op))  /* % << >> etc. */
            {   typeclash(op); return 0; }
            /* The 2 next lines fix a bug in pre-1.60a versions whereby   */
            /* (long)op(double) was incorrectly treated as (long double). */
            if (is_longdouble_(m1) || is_longdouble_(m2)) return te_ldble;
            if (is_double_(m1) || is_double_(m2)) return te_double;
            /* the next line is an ANSI draft (May 86) feature.
               In the PCC case coerceunary would have ensured that any
               such arguments would have already been coerced to double */
            return te_float;
        }
        /* the next line is an ANSI special case */
        if (op == s_leftshift || op == s_rightshift) return x1;
        if ((m1 | m2) & bitoftype_(s_long))
        {   int32 l1 = int_decodelength_(m1),
                  l2 = int_decodelength_(m2);
            if (l1 == l2) {
            /* Both operands the same size (at least long): result type */
            /* is unsigned if either operand is, else signed            */
                if ((m1 | m2) & bitoftype_(s_unsigned))
                    return l1 == sizeof_long ? te_ulint : te_ullint;
                else
                    return l1 == sizeof_long ? te_lint : te_llint;
            }
            /* One operand is longer than the other, the longer operand  */
            /* is at least long. ANSI rule says the result is unsigned   */
            /* if the longer operand is, else signed (regardless of the  */
            /* signedness of the other operand)                          */
            /* shouldn't the PCC rule say if either operand is unsigned, */
            /* so is the result? The old (pre-longlong) code didn't      */
            {   int32 l = l1;
                SET_BITMAP m = m1;
                if (l2 > l1) { l = l2; m = m2; }
                if (m & bitoftype_(s_unsigned))
                    return l == sizeof_long ? te_ulint : te_ullint;
                else
                    return l == sizeof_long ? te_lint : te_llint;
            }
#if 0        /* @@@ save for possible later warn on <unsigned>op<signed> */
             /* as recommended to implementers by ANSI.                  */
>>>>    if ((m1^m2) & bitoftype_(s_unsigned) &&
>>>>        (op == s_div || op == s_rem ||  /* s_rightshift done above */
>>>>         op == s_less || op == s_lessequal ||
>>>>         op == s_greater || op == s_greaterequal))
>>>>        /* This warning combats AM (and others?) getting confused */
>>>>        /* that "-1L < 5U" is true.  NO longer true (Oct 88).     */
>>>>        cc_warn(sem_warn_unsigned, op);
#endif
        }
        if ((m1 | m2) & bitoftype_(s_unsigned)) return te_uint;
        return te_int;  /* only case left */
    }

    /* If one of them is a type var, it does not matter what we return. */
    if (istypevar(x1) || istypevar(x2)) return x1;

    /* Apr 92: some old error recovery retired here...                  */
    typeclash(op);
    return 0;
}

/* patch up for special treatment of types of formal parameters at defn */
TypeExpr *modify_formaltype(TypeExpr *t)
{   TypeExpr *t1 = princtype(t);
    switch (h0_(t1))
    {   case t_fnap:       /* turn f() to (*f)() */
            return ptrtotype_(t);
        case t_subscript:  /* turn a[] to *a     */
            /* We also turn a const array (only via typedef) into a     */
            /* pointer to const components.  Beware, ANSI is unclear.   */
            return ptrtotype_(mkqualifiedtype(typearg_(t1),
                                              typedef_qualifiers(t)));
        default:
            return t;
    }
}

/* patch up for special treatment of argument types for overloading */
TypeExpr *modify_actualtype(TypeExpr *t, const Expr *e)
{   TypeExpr *t1 = princtype(t);
    IGNORE(e);
    switch (h0_(t1))
    {   case s_typespec:
            if (typespecmap_(t1) & BITFIELD)
                /* should this add "unsigned" to plain 'short', 'int' and 'long'?
                   draft is unclear --sad */
                return primtype2_(typespecmap_(t1) & ~BITFIELD, typespectagbind_(t1));
            else
                return t;
        case t_fnap:       /* turn f() to (*f)() */
            return ptrtotype_(t);
        case t_subscript:  /* turn a[] to *a     */
            /* We also turn a const array (only via typedef) into a     */
            /* pointer to const components.  Beware, ANSI is unclear.   */
            return ptrtotype_(mkqualifiedtype(typearg_(t1),
                                              typedef_qualifiers(t)));
        default:
            return t;
    }
}

/* For safety w.r.t. prototype and non-prototype forms, we pass all
   short ints/chars and floats as repectively ints and doubles and
   do callee narrowing.
*/
TypeExpr *promoted_formaltype(TypeExpr *t)
{   TypeExpr *t1 = princtype(t);      /* can ignore typedef qualifiers? */
    if (h0_(t1) == s_typespec)
    {   SET_BITMAP m1 = typespecmap_(t1);
        if (is_float_(m1))
            return te_double;
/* Should Feature_PCC do anything here re unsigned preserving?          */
        if (m1 & bitoftype_(s_char))
            /* turn 'char' to 'int'. */
            return te_int;
        if (m1 & bitoftype_(s_int))
            /* turn 'short' to 'int'. */
            return int_isshort_(m1) ?
                    (sizeof_short==sizeof_int &&
                     m1 & bitoftype_(s_unsigned) ? te_uint:te_int) : t;
        return t;
    }
    return t;
}

TypeExpr *widen_formaltype(TypeExpr *t) {
    return (config & CONFIG_UNWIDENED_NARROW_ARGS) ? t :
                                                     promoted_formaltype(t);
}

/* printf/scanf format checker... (belongs in a separate file?) */

typedef enum { FMT_INT, FMT_LINT, FMT_LLINT, FMT_FLT, FMT_PTR } FmtSort;

static void fmt1chk(char *buf, int bufp, Expr *arg, FmtSort sort, int argindex)
{   TypeExpr *t = princtype(typeofexpr(arg));
    switch (h0_(t))
    {
case t_content:
        if (sort == FMT_PTR) return;
        break;
case s_typespec:
        {   SET_BITMAP m = typespecmap_(t);
            if ((m & bitoftype_(s_int) &&
                   sort == (FmtSort) /* cast to silence gcc        */
                         (int_islonglong_(m) ? FMT_LLINT :
                    (m & bitoftype_(s_long)) ? FMT_LINT:
                                               FMT_INT))

/* In C enums coerceunary() to ints.  We suppress this, so that C++ is  */
/* easy (and so that we can warn as ANSI suggest, but we need to allow  */
/* printf("%d", enumconst) in C (although not C++? -- unclear).         */
/* See also the uses of COERCE_ARG in mkfnap()/coerceunary.             */
                || ( !HasFeature(Feature_PCC) ?
                     ((m & bitoftype_(s_enum)) && sort == FMT_INT) : 0
                   )

                || ((m & bitoftype_(s_double)) &&
                    sort == FMT_FLT))
              return;
        }
        break;
    }
    cc_warn(sem_warn_format_type, t, (int)bufp, argindex, buf);
}

#ifdef STRING_COMPRESSION
static unsigned short int compression_info[128] = {
    0x6520, 0x7468, 0x7320, 0x696e, 0x2081, 0x6420, 0x7420, 0x616e,
    0x6572, 0x6f6e, 0x6f72, 0x656e, 0x8480, 0x6172, 0x7265, 0x7469,
    0x6585, 0x616c, 0x6982, 0x6f6d, 0x8367, 0x746f, 0x6669, 0x7920,
    0x6573, 0x6f66, 0x6120, 0x2c20, 0x7374, 0x8f89, 0x6174, 0x6368,
    0x6582, 0x2020, 0x6563, 0x6f75, 0x6393, 0x656c, 0x8a20, 0x7488,
    0x8785, 0x8764, 0x9420, 0x6163, 0x8180, 0x616d, 0x6564, 0xa46d,
    0x966c, 0x9520, 0x6578, 0x5468, 0x6c20, 0x7769, 0x726f, 0x7365,
    0x6465, 0x6162, 0x6c69, 0x756c, 0x7573, 0x6469, 0x9920, 0x756d,
    0x8820, 0x668a, 0xb581, 0x7368, 0x7369, 0x8465, 0x6c6f, 0x7370,
    0x6e6f, 0x7768, 0x8d80, 0x7572, 0x6d61, 0x9d20, 0x8b86, 0xb96c,
    0x8720, 0x6974, 0x8320, 0x5c73, 0xb380, 0x2ea1, 0x6182, 0x8b74,
    0x756e, 0x708e, 0x6280, 0x6f6c, 0x7375, 0x8b20, 0xafa9, 0x6173,
    0x9873, 0x9f20, 0x70b6, 0x7574, 0x7691, 0xafa8, 0x7293, 0x6ead,
    0x8e63, 0x66a6, 0x9120, 0x6167, 0x652e, 0x6986, 0x998c, 0x8d67,
    0x4966, 0x6f70, 0x696c, 0x6574, 0xb866, 0xc3a5, 0x6389, 0xb080,
    0x6186, 0x656d, 0x9062, 0xe475, 0x6164, 0xa269, 0x6c97, 0x66e6
};

#define REPEAT_CH       29
#define REPEAT_SP       30
#define LITERAL_CHAR    31

static bool compress_fmt(String *fmt)
{
    StringSegList *z;
    char *s;
    int i, j, l;
    unsigned k;
    int ba, bb;
    int c;

    if (var_cc_private_flags & 32768) return 0;
    for (z = fmt->strseg; z; z = z->strsegcdr) {
        s = z->strsegbase;
        l = z->strseglen;
        for (j = 0 ; j < l;) {
            c = s[j];
            k = j + 1;
            while (k < l && c == s[k]) k++;
            if (k - j > 3 || (c == ' ' && k - j > 2)) {
                s[j++] = (c == ' ') ? REPEAT_SP : REPEAT_CH;
                s[j] = k - j;
                j++;
                if (c != ' ') s[j++] = c;
                memcpy(&s[j], &s[k], l-k);
                l -= k-j;
            } else j++;
        }
        z->strseglen = l;
    }
    for (z = fmt->strseg; z; z = z->strsegcdr) {
        s = z->strsegbase;
        l = z->strseglen;
        for (i = 0; i < 128; i++) {
            k = compression_info[i];
            ba = k >> 8; bb = k & 0xff;
            for (j = 1; j < l; j++) {
                if (s[j-1] == '%') {
                    do {
                        c = s[j];
                        j++;
                        if (c == '%' || c == 'c' || c == 'd' || c == 'e' ||
                                c == 'f' || c == 'g' || c == 'i' || c == 'n' ||
                                c == 'o' || c == 'p' || c == 's' || c == 'u' ||
                                c == 'x')
                            break;
                    } while (j < l);
                } else if (s[j-1] == ba && s[j] == bb) {
                    s[j-1] = i+128;
                    l -= 1;
                    memcpy(&s[j], &s[j+1], l-j);
                }
            }
        }
        z->strseglen = l;
    }
    return 1;
}
#endif

static bool fmtchk(String *fmt, ExprList *l, int32 flavour, int fmtindex)
{   /* flavour=1 => s/f/printf, flavour=2 => s/f/scanf - see stdio.h pragma */
    /* fmtindex = argument number of the format string argument */
    /* returns TRUE if no floating point will be used & printf case */
    StringSegList *z;
    int state = 0; int nformals = 0, nactuals = fmtindex;
    bool no_fp_conversions = (flavour == 1);
    char buf[20]; int bufp = 1;   /* 0..20 */
    FmtSort xint = FMT_INT;
    for (z = fmt->strseg; z!=NULL; z = z->strsegcdr)
    {   char *s = z->strsegbase;
        int32 len = z->strseglen;
        while (len-- > 0)
        {   int ch = char_untranslation(*s++);
#ifndef NO_SELF_CHECKS
/* The following lines augment printf checks to cover cc_err, syserr &c */
/* via #pragma -v3 present in mip/globals.h.                            */
/* #define'ing NO_SELF_CHECKS disables this and saves about 100 bytes.  */
            if (ch == '$' && flavour == 3 && state == 0)
            {   /* the next line is ugly because it assumes string not split */
                if (char_untranslation(*s) != 'l')   /* 'l' => use curlex */
                {   nformals++;
                    if (l != NULL) nactuals++, l = cdr_(l);
                }
            }
            else
#endif
            if (ch == '%')
                bufp=1, buf[0]=ch,
                state = state==0 ? 1 : 0,
                xint = FMT_INT;
            else if (state != 0) switch ((bufp<20 ? buf[bufp++] = ch:0), ch)
            {   case '*':
                    if (flavour==2) { state = 9; break; }
                    nformals++;
                    if (l)
                    {   fmt1chk(buf, bufp, exprcar_(l), FMT_INT, ++nactuals);
                        l = cdr_(l);
                    }
                    break;
                case '.':
                    break;
                case '+': case '-': case ' ': case '#':
                    state = state==1 ? 2 : 99; break;
                case 'l':
                    if (xint == FMT_LINT)
                        xint = FMT_LLINT;
                    else
                        xint = FMT_LINT;
                    /* drop through */
                case 'h': case 'L':
                    /* not treated properly yet */
                    state = state < 5 ? 5 : 99;
                    break;
                case 'd': case 'i': case 'o': case 'u': case 'x': case 'X':
                case 'c':
                    if (state == 9) { state = 0; break; } /* scanf suppressed */
                    nformals++;
                    if (l != NULL)
                    {   fmt1chk(buf, bufp, exprcar_(l), flavour==2 ? FMT_PTR :
                                     ch=='c' ? FMT_INT:xint, ++nactuals);
                        l = cdr_(l);
                    }
                    state = 0;
                    break;
                case 'f': case 'e': case 'E': case 'g': case 'G':
                    no_fp_conversions = 0;
                    if (state == 9) { state = 0; break; } /* scanf suppressed */
                    nformals++;
                    if (l != NULL)
                    {   fmt1chk(buf, bufp, exprcar_(l),
                                flavour==2 ? FMT_PTR:FMT_FLT, ++nactuals);
                        l = cdr_(l);
                    }
                    state = 0;
                    break;
                case 's': case 'p': case 'n':
                    if (state == 9) { state = 0; break; } /* scanf suppressed */
                    nformals++;
                    if (l != NULL)
                    {   fmt1chk(buf, bufp, exprcar_(l), FMT_PTR, ++nactuals);
                        l = cdr_(l);
                    }
                    state = 0;
                    break;
                case '[':
                    if (state == 9) { state = 0; break; } /* scanf suppressed */
                    if (flavour==2) /* scanf only */
                    {   /* check well-formed one day */
                        nformals++;
                        if (l != NULL)
                        {   fmt1chk(buf, bufp, exprcar_(l), FMT_PTR, ++nactuals);
                            l = cdr_(l);
                        }
                        state = 0;
                        break;
                    }
                    /* else drop through */
                default:
                    if ('0'<=ch && ch<='9') break;
                    cc_warn(sem_warn_bad_format, (int)ch);
                    state = 0;
                    break;
            }
        }
    }
    if (state != 0) cc_warn(sem_warn_incomplete_format);
    nactuals += length(l) - fmtindex;
    if (nactuals != nformals)
      switch (nformals) {
      case 0:
        cc_warn(sem_warn_format_nargs_0, (long)nactuals);
        break;
      case 1:
        cc_warn(sem_warn_format_nargs_1,(long)nactuals);
        break;
      default:
        cc_warn(sem_warn_format_nargs_n, (long)nformals, (long)nactuals);
        break;
      }
    return no_fp_conversions;
}

static Expr *formatcheck(Expr *e, ExprList *l, FormTypeList *d, int32 flavour)
{   Expr *fmt = NULL;
    ExprList *ll = l;
    int fmtindex = 0;
#ifdef STRING_COMPRESSION
    bool no_fp;
    bool compress;

#endif
    for (; d != NULL && ll != NULL; d = cdr_(d), ll = cdr_(ll)) {
        fmt = exprcar_(ll);
        fmtindex++;
    }
    if (d == NULL && fmt != NULL)
    {   for (;;)
        {   switch (h0_(fmt))
            {
    case s_invisible:
                    fmt = compl_(fmt); continue;
    case s_cast:
    case s_addrof:  fmt = arg1_(fmt); continue;
#ifdef STRING_COMPRESSION
    case s_string:  no_fp = fmtchk(exs_(fmt), ll, flavour, fmtindex);
/* Here we had a printf, sprintf or fprintf where the format string was    */
/* a literal string that showed that no floating point conversions would   */
/* be required. Convert to a call to _printf, _sprintf or _fprintf, which  */
/* are restricted (smaller) versions of the relevant library functions.    */
/* NB that this conversion is enabled by a #pragma present in <stdio.h>    */
/* and so will not confuse users who avoid #pragma and who redefine        */
/* their own printf etc without the benefit of the standard header file.   */
/* The following test gives false (hence no "else syserr()") for calls     */
/* like  (**printf)("hi");  we could catch this, but not really worth it.  */
                    if (h0_(e) == s_invisible &&
                            h0_(orig_(e)) == s_binder)
                    {   Symstr *fname = bindsym_(exb_(orig_(e)));
/* @@@ Why be paranoid to avoid sharing the sim.printf(s_addrof)??         */
/* Can simplify() corrupt otherwise?                                       */
/* Review the names 'printf' for C++ name munging too.                     */
                        compress = (flavour == 1 && compress_fmt(exs_(fmt)));
                        if (compress || no_fp) {
                            if (fname == sim.yprintf) {
                                if (compress)
                                    e = mkaddr(arg1_(no_fp ? sim.xprintf_z : sim.yprintf_z));
                                else
                                    e = mkaddr(arg1_(sim.xprintf));
                            } else if (fname == sim.yfprintf) {
                                if (compress)
                                    e = mkaddr(arg1_(no_fp ? sim.xfprintf_z : sim.yfprintf_z));
                                else
                                    e = mkaddr(arg1_(sim.xfprintf));
                            } else if (fname == sim.ysprintf) {
                                if (compress)
                                    e = mkaddr(arg1_(no_fp ? sim.xsprintf_z : sim.ysprintf_z));
                                else
                                    e = mkaddr(arg1_(sim.xsprintf));
                            }
                        }
                        /* this is a valid drop through place, for */
                        /* scanf, eprintf (norcroft internal) &c.  */
                    }
                    break;
#else
    case s_string:  if (fmtchk(exs_(fmt), ll, flavour, fmtindex))
/* Here we had a printf, sprintf or fprintf where the format string was    */
/* a literal string that showed that no floating point conversions would   */
/* be required. Convert to a call to _printf, _sprintf or _fprintf, which  */
/* are restricted (smaller) versions of the relevant library functions.    */
/* NB that this conversion is enabled by a #pragma present in <stdio.h>    */
/* and so will not confuse users who avoid #pragma and who redefine        */
/* their own printf etc without the benefit of the standard header file.   */
/* The following test gives false (hence no "else syserr()") for calls     */
/* like  (**printf)("hi");  we could catch this, but not really worth it.  */
                    {   if (h0_(e) == s_invisible &&
                            h0_(orig_(e)) == s_binder)
                        {   Symstr *fname = bindsym_(exb_(orig_(e)));
/* @@@ Why be paranoid to avoid sharing the sim.printf(s_addrof)??         */
/* Can simplify() corrupt otherwise?                                       */
/* Review the names 'printf' for C++ name munging too.                     */
                            if (fname == sim.yprintf)
                                e = mkaddr(arg1_(sim.xprintf));
                            else if (fname == sim.yfprintf)
                                e = mkaddr(arg1_(sim.xfprintf));
                            else if (fname == sim.ysprintf)
                                e = mkaddr(arg1_(sim.xsprintf));
                            /* this is a valid drop through place, for */
                            /* scanf, eprintf (norcroft internal) &c.  */
                        }
                    }
                    break;
#endif
/*
 * The warning message generated here will arise only if the -fussy -ansi
 * switches are set and indicates that a printf/scanf has been given where
 * the a format that is not a literal string and so which can not be checked
 * for validity by the compiler.  It is also necessary in this case to
 * link to the version of printf (etc) that supports floating point
 * conversions even in cases where store could have been saved by using
 * the integer-only version.
 */
    default:        if (1<=flavour && flavour<=3 &&
                        HasFeature(Feature_Fussy) &&
                        !HasFeature(Feature_PCC))
                    { cc_warn(sem_warn_uncheckable_format);
                    }
                    break;
            }
            break;
        }
    }
    return e;
}

/* l-value like stuff ... */

/* The need for skip_invisible is largely because of the nastiness      */
/* of storing information about the sort of field selection (bitfield   */
/* or C++ member fn) in the s_dot node, which can be protected by       */
/* an s_invisible (e.g. when 'this->a' is written just as 'a').         */
Expr *skip_invisible(Expr *e)
{   for (;;)
        if (h0_(e) == s_invisible)
            e = compl_(e);
        else if (h0_(e) == s_evalerror)
            e = arg1_(e);
        else
            return e;
}

Expr *skip_invisible_or_cast(Expr *e)
{
    for (;;)
        if (h0_(e) == s_invisible)
            e = compl_(e);
        else if (h0_(e) == s_evalerror)
            e = arg1_(e);
        else if (h0_(e) == s_cast)
            e = arg1_(e);
        else
            return e;
}

#define allowvolatile 1
#define allowcontents 2
#define allowpostinc 4
static bool isverysimplelvalue(Expr *e, int flags)
{
    while (h0_(e) == s_dot) e = arg1_(e);  /* x.a.b is simple if x is ...   */
                                           /* and lvalues do not have casts */
    if ((flags & allowcontents) && h0_(e) == s_content)
        e = arg1_(e);
    if (h0_(e) == s_binder)
        return (flags & allowvolatile) || !isvolatile_type(bindtype_(exb_(e)));
    else if (h0_(e) == s_content && h0_(arg1_(e)) == s_integer)
        return (flags & allowvolatile) || !isvolatile_type(typearg_(princtype(type_(arg1_(e)))));
    else if ((flags & allowpostinc) && h0_(e) == s_displace)
        return isverysimplelvalue(arg1_(e), 0);
    else
        return NO;
}

static bool issimplevalue_i(Expr *e, int flags)
{   AEop op;
    e = skip_invisible_or_cast(e);
    op = h0_(e);
    return op == s_integer || op == s_int64con
           || isverysimplelvalue(e, flags)
           || (op == s_addrof
               && isverysimplelvalue(skip_invisible_or_cast(arg1_(e)), flags | allowcontents))
           || ( (op == s_times || op == s_plus || op == s_minus || op == s_div
                 || op == s_rem || op == s_leftshift || op == s_rightshift || op == s_and)
                && issimplevalue_i(arg1_(e), flags)
                && issimplevalue_i(arg2_(e), flags))
           || ( (op == s_neg || op == s_bitnot || op == s_boolnot)
                && issimplevalue_i(arg1_(e), flags));
}

bool issimplevalue(Expr *e)     /* @@@ should be static! */
{   return issimplevalue_i(e, 0);
}

static bool issimplelvalue_i(Expr *e, int flags)
{
    while (h0_(e) == s_dot) e = skip_invisible_or_cast(arg1_(e));
    if (isverysimplelvalue(e, allowvolatile))
        return YES;
    else if (h0_(e) == s_content)
    {   e = skip_invisible_or_cast(arg1_(e));
        if ( isverysimplelvalue(e, flags)
            || ( (h0_(e) == s_plus || h0_(e) == s_minus)
                && issimplevalue_i(arg1_(e), flags)
                && issimplevalue_i(arg2_(e), flags) ) )
            return YES;
    }
    return NO;
}

bool issimplelvalue(Expr *e)    /* @@@ should be static! */
{   return issimplelvalue_i(e, 0);
}

static Expr *RemovePostincs(Expr *e, Expr **incs) {
    switch h0_(e) {
    case s_integer: case s_binder:
        return e;
    case s_displace:
      { Expr *inc = mk_expr2(s_assign, type_(e), arg1_(e), arg2_(e));
        *incs = (*incs == 0) ? inc :
                               mkbinary(s_comma, *incs, inc);
        return arg1_(e);
      }

    case s_cast: case s_content: case s_addrof:
      { Expr *a1 = skip_invisible(arg1_(e));
        Expr *newa1 = RemovePostincs(a1, incs);
        return (a1 == newa1) ? e:
                               mk_expr1(h0_(e), type_(e), newa1);
      }

    case s_dot:         /* s_arrow gone? */
      { Expr *a1 = skip_invisible(arg1_(e));
        Expr *newa1 = RemovePostincs(a1, incs);
        return (a1 == newa1) ? e:
            mk_exprwdot(s_dot, type_(e), newa1, exprdotoff_(e));
      }

    case s_times: case s_div: case s_rem:
    case s_leftshift: case s_rightshift: case s_and:
    case s_plus: case s_minus:
      { Expr *a1 = skip_invisible(arg1_(e)),
             *a2 = skip_invisible(arg2_(e));
        Expr *newa1 = RemovePostincs(a1, incs),
             *newa2 = RemovePostincs(a2, incs);
        return (a1 == newa1 && a2 == newa2) ? e :
            mk_expr2(h0_(e), type_(e), newa1, newa2);
      }

/* @@@ AM: I am not convinced by these routines and even less convinced */
/* that they should appear here in sem.  simplify.c must be better.     */
    case s_dotstar:     /* s_arrowstar gone? */
    default:
        pr_expr(e); syserr("help");
        return e;
    }
}

/* Expression AE tree node creators and associated functions */

Expr *mkintconst(TypeExpr *te, int32 n, Expr *e)
{   /* Assumes a te_int in case of a t_unknown. */
    return mk_expr2(s_integer, (istypevar(te))? te_int : te, (Expr *)(IPtr)n, e);
}

static Expr *mkinvisible(TypeExpr *t, Expr *olde, Expr *newe)
/* The purpose of s_invisible nodes in the tree is to compile one thing */
/* whilst retaining the original expression for error messages.         */
/* Thus ++x can compile as x=x+1 but produce an error about ++ in &++x. */
/* @@@ beware: most calls guard with oldop != newop && newop != s_error */
{   /* The next line may be useful one day...                      */
    /*          if (h0_(newe) == s_error) return errornode;        */
    /* but we'd have to remove argument 't'.                       */
    /* s_integer nodes have a special invisible representation:    */
    if (h0_(newe) == s_integer)
        return mkintconst(t, intval_(newe), olde);
/* how about:   if (h0_(newe) == h0_(olde)) return newe;   ??           */
    return mk_expr2(s_invisible, t, olde, newe);
}

/* ensurelvalue() the is the lvalue checking (and coercing, for C++     */
/* t_ref's) routine analogous to coerceunary() which coerces and checks */
/* rvalues.                                                             */
/* It has two phases -- first it must check from the type info          */
/* that e is not a array, function or other 'const' type.               */
/* However, note that & can still be applied to such things.                */
/* This is the difference between lvalue and modifiable lvalue.             */
/* Note also that in PCC given 'int a[10]' then &a has type (int *), the    */
/* same as 'a' in expression context, whereas ANSI say it is 'int (*)[10]). */
/* which is more uniform (and always puts a * on the type).                 */
/* The ANSI choice reduces confusion in multi-dimensional arrays.           */
 /* The following example may help:
  *         struct { int r[7], s[7] } x;
  *         f() { printf("%d\n", &x.s - &x.r);
  *               printf("%d\n", x.s - x.r);   }
  * under ANSI prints 1 then 7, under PCC 7 then 7.
  */
/* Secondly it must check that the expression really can be an lvalue --    */
/* care must be taken for things like (e.a.b.c).                            */
/* It currently either returns its arg unchanged, or errornode.   LIE C++   */
/* In C++ (LanguageIsCPlusPlus) it converts refs to indirections...         */
/* /* but not all callers are fixed to use this properly yet..              */

Expr *ensurelvalue(Expr *e, AEop op)
{   Expr *x;
    if ((h0_(e) == s_binder || h0_(e) == s_member && op != s_addrof) &&
                attributes_(exb_(e)) & CB_ANON)
        e = mkfieldselector(s_dot, (Expr *)realbinder_(exb_(e)),
                                   (ClassMember *)bindsym_(exb_(e)));
        /* The s_addrof/s_member case is done in mkaddr (q.v.).         */
    if (h0_(e) == s_error) return errornode;

    {   TypeExpr *t = princtype(typeofexpr(e));
        if (h0_(t) == t_ref)
        {   TypeExpr *t2 = typearg_(t);
            e = mkinvisible(t2, e, mk_expr1(s_content,t2,e));
            /* map a ref to a implicit content thereby losing t_ref.    */
            /* maybe we should use a form of coerceunary?               */
            /* @@@ recall [ES,p138,l-1] suggests t2 may be fn/array!    */
        }
    }

    {   TypeExpr *t = typeofexpr(e);

        while (h0_(t) == t_coloncolon) t = typearg_(t);

        if (op != s_addrof && op != s_init &&
                (qualifiersoftype(t) & bitoftype_(s_const)))
            cc_rerr(sem_rerr_assign_const, e);
        if (op == s_addrof && isbitfield_type(t))
        {   cc_err(sem_err_bitfield_address);
            return errornode;
        }
        t = princtype(t);
        if (h0_(t) == t_subscript || h0_(t) == t_fnap || h0_(t) == t_ovld)
        {   if (op != s_addrof)
            {   cc_err(sem_err_lvalue, e);
                return errornode;
            }
/* This code catches things like &(a.b) where "struct {int b[4];} a" */
/* but, oh misfortune, that is just what happens inside the macro    */
/* for offsetof(). Ah well.                                          */
            if (HasFeature(Feature_PCC)) cc_warn(sem_warn_addr_array, e);
            /* remember &(f().m) with m an array member is OK!       */
        }
    }
    for (x = e;;) switch (h0_(x))
    {   case s_member:
/* Always valid as member -- there are no enumconst s_member's          */
/* (s_binder used) or register members.                                 */
/* Maybe could fix the implicit 'this' here though.                     */
            return e;
        case s_binder:
        {   Binder *b = exb_(x);
            if (isenumconst_(b))
            /* will always be seen via a s_integer nodes */
            {   cc_err(sem_err_lvalue1, b);
                return errornode;
            }
            /* make sure it's not a nullbinder */
            if (bindsym_(b) != NULL && !(bindstg_(b) & ~u_referenced))
            {   cc_err(sem_err_template_nontype_storage, b);
                return errornode;
            }
            if (op == s_addrof)
            {   if (bindstg_(b) & bitofstg_(s_register))
                {    /* In spite of the real PCC giving a hard error,   */
                     /* for taking a reg var address (or at least       */
                     /* generating bad code); PCC mode gives a          */
                     /* (suppressible) warning!  Makefiles beware.      */

                     if (!LanguageIsCPlusPlus) cc_pccwarn(sem_rerr_addr_regvar, b);

                     bindstg_(b) &= ~bitofstg_(s_register);
                }
                if (bindstg_(b) & b_globalregvar)
                {   cc_err(sem_err_addr_globalvar, b);
                    return errornode;
                }
                bindstg_(b) |= b_addrof;
                if ((bindstg_(b) & u_constdata) && !(bindstg_(b) & b_generated))
                    vg_generate_deferred_const(b);
                if (debugging(DEBUG_TYPE)) cc_msg("addrof $b\n", b);
            }
            return e;
        }
        case_s_any_string      /* &"abc" seems legal */
        case s_subscript:
        case s_arrow:
        case s_content:
            return e;
        case s_comma:           /* CPlusPlus only, introduced for side-effects*/
            if (LanguageIsCPlusPlus)
            {   x = arg2_(x);
                break;
            }
            else goto defaultcase;
        case s_dot:
        case s_qualdot:
            if (h0_(type_(x)) == t_ovld)
                /* exprdotmemfn */
                x = exprdotmemfn_(x);
            else
                x = arg1_(x);
            break;
        case s_arrowstar:       /* don't believe [ES,p71,l-1]!          */
            return e;
        case s_dotstar:         /* don't believe [ES,p71,l-1]!          */
            x = arg1_(x);
            break;
        case s_assign:
            if (LanguageIsCPlusPlus)
                x = arg1_(x);
            else goto defaultcase;
            break;
        case s_invisible:

#if !defined(ensurelvalue_s_invisible)
#define ensurelvalue_s_invisible (void)0;
#endif
            ensurelvalue_s_invisible
            return ((h0_(ensurelvalue(orig_(x), op)) == s_error)
                         ? errornode : e);
            break;
        case s_integer:
            if (intorig_(x) != 0) /* i.e. if previously simplified */
            {   x = intorig_(x);
                break;            /* only to give correct error message */
            }
            /* drop through */
        defaultcase:
        default:
/* The next line could improve s_integer to s_boolean/s_character.      */
/* see the cases in mkvoided().                                         */
            if (!istypevar(typeofexpr(x)))
                cc_err(sem_err_lvalue2, h0_(x));
            return errornode;
        case s_cond:                          /* needs fixing */
            if (!LanguageIsCPlusPlus)
                cc_rerr(sem_err_lvalue2, h0_(x));
                /* But otherwise treat as C++ */
            {   Expr *e1 = arg2_(x);
                Expr *e2 = arg3_(x);
                while (h0_(e1) == s_cast) e1 = arg1_(e1);
                while (h0_(e2) == s_cast) e2 = arg1_(e2);
                if (ensurelvalue(e1, s_addrof) == errornode ||
                    ensurelvalue(e2, s_addrof) == errornode)
                    return errornode;
                else
                    return e;
            }
        case s_cast:
/* @@@ LDS: I hope this all works...                                        */
/* Casts in l-values get special error fixup code since pcc allows. The fix */
/* is ugly: If the context is ++ or -- (pre- or post) then the cast expr    */
/* will later have its address taken, so here we lie about the operator to  */
/* force b_addrof in any binders recursively encountered...                 */
/* AM: bug here: (float)x = 1; syserrs.                                     */
            cc_pccwarn(sem_rerr_lcast);
            if (HasFeature(Feature_PCC))
            {
                if (monadneedslvalue_(op)) op = s_addrof;
                return ((h0_(ensurelvalue(arg1_(x), op)) == s_error)
                         ? errornode : e);
            } else return errornode;
    }
}

Expr *mk1fnap(Expr *fn, ExprList *args)
{
   TypeExpr *t = princtype(typeofexpr(fn));  /* typedefs irrelevant */
/* @@@ someone is also paranoid here about sharing of &sim.fns.         */
/* No sense in an invisible node when the whole functioon call wasn't   */
/* what was written.                                                    */
   fn = mk_expr1(s_addrof, ptrtotype_(t), fn);
   return mk_expr2(s_fnap, typearg_(t), fn, (Expr *)args);
}

/* The following routine tidies up pre-existing code, later improve for */
/* other lengths of floating point.                                     */
static void fltrep_to_widest(DbleBin *dest, FloatCon *src)
{   /* Consider extending this interface for long double > double.      */
    if (sizeof_double == 4 ||
          sizeof_float < sizeof_double && src->floatlen & bitoftype_(s_short))
       fltrep_widen(&src->floatbin.fb, dest);
    else
       flt_move(dest, &src->floatbin.db);
}

static FloatCon *fltrep_from_widest(
                        DbleBin *src, SET_BITMAP flag, char *floatstr)
{   /* Consider extending this interface for long double > double.      */
    /* Binary representation is definitive, but keep any text form.     */
    FloatCon *m = real_of_string(floatstr ? floatstr : "<expr>", 0);
    m->floatlen = flag;
    if (sizeof_double == 4 ||
          sizeof_float < sizeof_double && flag & bitoftype_(s_short))
    {   int status = fltrep_narrow(src, &m->floatbin.fb);
        if (status > flt_ok) flt_report_error(status);
    } else
        flt_move(&m->floatbin.db, src);
    return m;
}

#define mk_expr2_ptr(op,t,a,b) trydiadreduce(mk_expr2(op,t,a,b),addrsignmap_)
#define isboolean_(op) ((op)==s_andand || (op)==s_oror)

static bool isknownzero(Expr *e)
{   e = skip_invisible_or_cast(e);
    return (h0_(e) == s_integer && intval_(e) == 0) ||
         (h0_(e) == s_int64con && int64val_(e).i.lo == 0 && int64val_(e).i.hi == 0);
}

static bool isunsignedtypespec(SET_BITMAP m)
{  return ((m & bitoftype_(s_unsigned)) ||
           ((m & -m) == bitoftype_(s_char) &&
            !(m & bitoftype_(s_signed)) &&
            !HasFeature(Feature_SignedChar)));
}

static bool iswidenedunsigned(Expr *e)
    /*/* this doesn't notice unsigned bitfields yet */
{   int32 origwidth;
    TypeExpr *t = princtype(typeofexpr(e));
    if (!isintegraltype_(t))
        return false;
    origwidth = sizeoftype(t);
    if (origwidth == 1)
        return false;
    for (;;)
        if (h0_(e) == s_invisible)
            e = compl_(e);
        else if (h0_(e) == s_evalerror)
            e = arg1_(e);
        else if (h0_(e) == s_cast)
        {   e = arg1_(e);
            t = princtype(typeofexpr(e));
            if (!isintegraltype_(t))
                return false;
            if (isunsignedtypespec(typespecmap_(t)) &&
                sizeoftype(t) < origwidth)
                return true;
        }
        else
        {   t = princtype(typeofexpr(e));
            break;
        }

    return isintegraltype_(t) && isunsignedtypespec(typespecmap_(t)) &&
           sizeoftype(t) < origwidth;
}

static Expr *MarkError(Expr *e, Expr *errorexpr, msg_t msg)
{ /* We now never produce either errors or warnings from within constant */
  /* folding. Instead, we save in a s_evalerror node the identity of the */
  /* message we would have produced, and leave the caller to generate it */
  /* (as an error if it's a constant expression, else as a warning)      */
  if (errorexpr == NULL)
    return e;
  return mk_expr3(s_evalerror, typeofexpr(e), e, errorexpr, (Expr *)msg);
}

static Expr *trydiadreduce(Expr *c, SET_BITMAP flag)
{ AEop op = h0_(c);
  Expr *a = arg1_(c), *b = arg2_(c);
  Expr *errorexpr = NULL;
  msg_t errormsg = NULL;
  if (h0_(a) == s_evalerror)
  { errorexpr = arg2_(a);
    errormsg = (msg_t)arg3_(a);
    a = arg1_(a);
  }
  if (h0_(b) == s_evalerror)
  { errorexpr = arg2_(b);
    errormsg = (msg_t)arg3_(b);
    b = arg1_(b);
  }
  /* h0_(b) == s_int64con has already been turned into h0_(b) == s_integer */
  /* by mkbinary */
  if ((op == s_leftshift || op == s_rightshift) && h0_(b) == s_integer)
  {  uint32 n = intval_(b);
     if (n >= (uint32)(8 * int_decodelength_(flag)))
        /* see ANSI spec, valid shifts are 0..31 */
       if (errorexpr == NULL)
       { errormsg = sem_errwarn_bad_shift;
         errorexpr = c;
       }
     if (n == 0 && h0_(a) != s_integer)  /* int case reduced below */
       /* the s_invisible node allows detection of "(x<<0)=1" lvalue error */
       return mkinvisible(type_(c), c, a);
  }
  if ((op == s_div || op == s_rem) && isknownzero(b))
  {  int32 n = intval_(b);
     if (n == 0 && errorexpr == NULL)
     {  errormsg = sem_errwarn_divrem_0;
        errorexpr = c;
     }
  }
/* The rationale here is that unsigned values are in the range 0, 1, .. */
/* and so a proper discrimination for counters is either n==0 vs. n!=0  */
/* or n==0 vs. n>0.  Anything that might suggest that negative values   */
/* might exist is WRONG, thus n<0, n<=0, n>=0, 0<=n, 0>n, 0>=n will all */
/* lead to diagnostics here.                                            */
  if (isinequality_(op))
  {  if (((flag & bitoftype_(s_unsigned)) || iswidenedunsigned(a)) && isknownzero(b))
     {  /* n op 0 */
        if (op == s_less)
        { errormsg = sem_errwarn_ucomp_0_false;
          errorexpr = c;
        }
        else if (op == s_greaterequal)
        { errormsg = sem_errwarn_ucomp_0_true;
          errorexpr = c;
        }
        else if (op == s_lessequal)
        { errormsg = sem_errwarn_ucomp_0;
          errorexpr = c;
        }
     }
     else if (((flag & bitoftype_(s_unsigned)) || iswidenedunsigned(b)) && isknownzero(a))
     {  /* 0 op n */
        if (op == s_greater)
        { errormsg = sem_errwarn_ucomp_0_false;
          errorexpr = c;
        }
        else if (op == s_lessequal)
        { errormsg = sem_errwarn_ucomp_0_true;
          errorexpr = c;
        }
        else if (op == s_greaterequal)
        { errormsg = sem_errwarn_ucomp_0;
          errorexpr = c;
        }
     }
  }
/* The following two lines reduce (e.g.) (2 || 1/0) to 1.  Similar code */
/* exists in mkcond() (q.v.).  @@@ However, it would seem that they can */
/* contravene the ANSI draft in that they also reduce                   */
/* int x[(2 || (0,1))] to int x[1], which silently misses a constraint  */
/* violation that the comma operator shall not appear in const exprs.   */
/* Similarly x[2 || f()].  AM thinks the ANSI draft is a mess here.     */
/* Note: mktest() has transformed (e.g.) (3.4 || e) to (3.4!=0 || e).   */
  if (op == s_oror && h0_(a) == s_integer && intval_(a) != 0)
      return MarkError(mkintconst(type_(c),1,c),
                       errorexpr, errormsg);
   if (op == s_andand  && h0_(a) == s_integer && intval_(a) == 0)
      return MarkError(mkintconst(type_(c),0,c),
                       errorexpr, errormsg);


  if (h0_(a) == s_integer && h0_(b) == s_integer &&
                             (flag & bitoftype_(s_unsigned)))
  { unsigned32 m = intval_(a), n = intval_(b), r;
    bool ok = YES;
/*
 * All this is HORRID if I have a 64 bit machine and I happen to have
 * allowed unsigned32 to be a 64 bit datatype.
 */
    m = just32bits_(m);
    n = just32bits_(n); /* force to 32 bits if unsigned32 is 64 bits wide */
    switch (op)
    {   case s_plus:        r = just32bits_(m+n); ok = r>=m && r>=n;  break;
        case s_minus:       r = just32bits_(m-n); ok = r<=m;          break;
        case s_times:       r = just32bits_(m*n); ok = m==0 || r/m==n; break;
        case s_div:         if (n==0) return c; r = m/n; break;
        case s_rem:         if (n==0) return c; r = m%n; break;
        case s_power:       return c;
        case s_and:         r = m&n;  break;
        case s_or:          r = m|n;  break;
        case s_xor:         r = m^n;  break;
        case s_andand:      r = m&&n; break;
        case s_oror:        r = m||n; break;
        case s_leftshift:   r = just32bits_(m<<n); ok = (r>>n) == m; break;
        case s_rightshift:  r = m>>n; break;
        case s_equalequal:  r = m==n; break;
        case s_notequal:    r = m!=n; break;
        case s_less:        r = m<n;  break;
        case s_lessequal:   r = m<=n; break;
        case s_greater:     r = m>n;  break;
        case s_greaterequal:r = m>=n; break;
        default: syserr(syserr_trydiadicreduce, (long)op);
                 return c;
    }
    r = widen32bitint_(r);
    if (sizeof_int == 2)
    {   if (!(flag & bitoftype_(s_long)) && (r & 0xffff0000))
            r &= 0x0000ffff, ok = NO;
    }
    if (!ok && errorexpr == NULL)
    {   errormsg = sem_errwarn_udiad_overflow;
        errorexpr = c;
    }
    return MarkError(mkintconst(type_(c),r,c),  /* always has a type_ field */
                     errorexpr, errormsg);
  }

  if (h0_(a) == s_integer && h0_(b) == s_integer)
  { int32 m = intval_(a), n = intval_(b), r;
    bool ok = YES;
/* @@@ The next lines assume that host 'int' overflow wraps round silently.  */
    switch (op)
    {   case s_plus:        r = m+n;
             r = widen32bitint_(r);
             ok = (m^n) < 0 || (m|n|r) >= 0 || (m&n&r) < 0; break;
        case s_minus:       r = m-n;
             r = widen32bitint_(r);
             ok = (n>=0 ? r<=m : r>m);                      break;
        case s_times:       r = m*n;
             r = widen32bitint_(r);
             ok = m==0 || n==0 || (m^n^r) >= 0 && r/m == n; break;
        case s_div:         if (n==0) return c;
/* The only case where division can give overflow is when the greatest  */
/* possible negative number is divided by -1.  I.e. iff n,m,r all -ve.  */
                            if (m == ~0x7fffffff && n == -1) r = m, ok = 0;
                            else r = m/n, ok = 1;
                            break;
/* Interesting ANSI question: what should effect of                     */
/* (signed)0x80000000%-1 be?  Mathematically 0, but maybe the division  */
/* overflowed and so we got a trap.  See if ANSI boobed!                */
        case s_rem:         if (n==0) return c; r = m%n;    break;
        case s_power:       return c;
        case s_and:         r = m&n;  break;
        case s_or:          r = m|n;  break;
        case s_xor:         r = m^n;  break;
        case s_andand:      r = m&&n; break;
        case s_oror:        r = m||n; break;
        case s_leftshift:   r = m<<n;
             r = widen32bitint_(r);
             ok = signed_rightshift_(r,n)==m; break;
        case s_rightshift:  r = TARGET_RIGHTSHIFT(m,n); break;
        case s_equalequal:  r = m==n; break;
        case s_notequal:    r = m!=n; break;
        case s_less:        r = m<n;  break;
        case s_lessequal:   r = m<=n; break;
        case s_greater:     r = m>n;  break;
        case s_greaterequal:r = m>=n; break;
        default: syserr(syserr_trydiadicreduce1, (long)op);
                 return c;
    }
    r = widen32bitint_(r);
    if (sizeof_int == 2)
    {   if (!(flag & bitoftype_(s_long)) && r != (int16)r)
            r = (int16)r, ok = NO;
    }
    if (!ok && errorexpr == NULL)
    {   errormsg = sem_errwarn_diad_overflow;
        errorexpr = c;
    }
    return MarkError(mkintconst(type_(c),r,c),
                     errorexpr, errormsg);
  }

  if ((h0_(a) == s_integer || h0_(a) == s_int64con)
      && (h0_(b) == s_integer || h0_(b) == s_int64con)
      && (flag & bitoftype_(s_unsigned)))
  { uint64 av, bv, rv, tv;
    I64_Status ok = i64_ok;
    uint32 n;
    if (h0_(a) == s_integer)
      I64_IToU(&av, intval_(a));
    else
      av = int64val_(a).u;
    if (h0_(b) == s_integer)
      I64_IToU(&bv, intval_(b));
    else
      bv = int64val_(b).u;
    switch (op)
    {   case s_plus:        ok = I64_UAdd(&rv, &av, &bv); break;
        case s_minus:       ok = I64_USub(&rv, &av, &bv); break;
        case s_times:       ok = I64_UMul(&rv, &av, &bv); break;
        case s_div:         ok = I64_UDiv(&rv, &tv, &av, &bv); break;
        case s_rem:         ok = I64_UDiv(&tv, &rv, &av, &bv); break;
        case s_and:         I64_And((int64 *)&rv, (int64 *)&av, (int64 *)&bv); break;
        case s_or:          I64_Or((int64 *)&rv, (int64 *)&av, (int64 *)&bv); break;
        case s_xor:         I64_Eor((int64 *)&rv, (int64 *)&av, (int64 *)&bv); break;
        case s_leftshift:   ok = I64_UToI(&n, &bv);
                            ok = ok | I64_Lsh((int64 *)&rv, (int64 *)&av, n); break;
        case s_rightshift:  ok = I64_UToI(&n, &bv);
                            ok = ok | I64_URsh(&rv, &av, n); break;
        case s_equalequal:  return mkintconst(type_(c), I64_UComp(&av, &bv) == 0, c);
        case s_notequal:    return mkintconst(type_(c), I64_UComp(&av, &bv) != 0, c);
        case s_less:        return mkintconst(type_(c), I64_UComp(&av, &bv) <  0, c);
        case s_lessequal:   return mkintconst(type_(c), I64_UComp(&av, &bv) <= 0, c);
        case s_greater:     return mkintconst(type_(c), I64_UComp(&av, &bv) >  0, c);
        case s_greaterequal:return mkintconst(type_(c), I64_UComp(&av, &bv) >= 0, c);
        default: syserr(syserr_trydiadicreduce, (long)op);
                 return c;
    }
    if (ok != i64_ok && errorexpr == NULL)
    {   errormsg = sem_errwarn_udiad_overflow;
        errorexpr = c;
    }
    return MarkError((Expr *)mkint64const(flag, (int64 *)&rv),
                     errorexpr, errormsg);
  }

  if ((h0_(a) == s_integer || h0_(a) == s_int64con)
      && (h0_(b) == s_integer || h0_(b) == s_int64con))
  { int64 av, bv, rv, tv;
    I64_Status ok = i64_ok;
    uint32 n;
    if (h0_(a) == s_integer)
      I64_IToS(&av, intval_(a));
    else
      av = int64val_(a).i;
    if (h0_(b) == s_integer)
      I64_IToS(&bv, intval_(b));
    else
      bv = int64val_(b).i;
    switch (op)
    {   case s_plus:        ok = I64_SAdd(&rv, &av, &bv); break;
        case s_minus:       ok = I64_SSub(&rv, &av, &bv); break;
        case s_times:       ok = I64_SMul(&rv, &av, &bv); break;
        case s_div:         ok = I64_SDiv(&rv, &tv, &av, &bv); break;
        case s_rem:         ok = I64_SDiv(&tv, &rv, &av, &bv); break;
        case s_and:         I64_And(&rv, &av, &bv); break;
        case s_or:          I64_Or(&rv, &av, &bv); break;
        case s_xor:         I64_Eor(&rv, &av, &bv); break;
        case s_leftshift:   ok = I64_UToI(&n, (uint64 *)&bv);
                            ok = ok | I64_Lsh(&rv, &av, n); break;
        case s_rightshift:  ok = I64_UToI(&n, (uint64 *)&bv);
                            ok = ok | I64_SRsh(&rv, &av, n); break;
        case s_equalequal:  return mkintconst(type_(c), I64_SComp(&av, &bv) == 0, c);
        case s_notequal:    return mkintconst(type_(c), I64_SComp(&av, &bv) != 0, c);
        case s_less:        return mkintconst(type_(c), I64_SComp(&av, &bv) <  0, c);
        case s_lessequal:   return mkintconst(type_(c), I64_SComp(&av, &bv) <= 0, c);
        case s_greater:     return mkintconst(type_(c), I64_SComp(&av, &bv) >  0, c);
        case s_greaterequal:return mkintconst(type_(c), I64_SComp(&av, &bv) >= 0, c);
        default: syserr(syserr_trydiadicreduce, (long)op);
                 return c;
    }
    if (ok != i64_ok && errorexpr == NULL)
    {   errormsg = sem_errwarn_diad_overflow;
        errorexpr = c;
    }
    return MarkError((Expr *)mkint64const(flag, &rv),
                     errorexpr, errormsg);
  }

  if ((h0_(a) == s_integer && is_template_arg_binder(b))
      || (is_template_arg_binder(a) && h0_(b) == s_integer))
  {   Expr *e = (h0_(a) == s_integer) ? a : b;
      errorexpr = (e == a) ? b : a;
      return MarkError(mkintconst(type_(c), isrelational_(op) ? 1 : intval_(e), c),
                       errorexpr, errormsg);
  }

  a = skip_invisible(a);
  b = skip_invisible(b);

  if (h0_(a) == s_floatcon && h0_(b) == s_floatcon)
  { DbleBin d,e,r;
    int status;
    fltrep_to_widest(&d, exf_(a));
    fltrep_to_widest(&e, exf_(b));
    switch (op)
    {   case s_plus:  status = flt_add(&r,&d,&e); break;
        case s_minus: status = flt_subtract(&r,&d,&e); break;
        case s_times: status = flt_multiply(&r,&d,&e); break;
        case s_div:   status = flt_divide(&r,&d,&e); break;
        case s_power: return c;
#define SEM_FLTCMP(op) mkintconst(type_(c),flt_compare(&d,&e) op 0,c);
        case s_equalequal:   return SEM_FLTCMP(==);
        case s_notequal:     return SEM_FLTCMP(!=);
        case s_less:         return SEM_FLTCMP(<);
        case s_lessequal:    return SEM_FLTCMP(<=);
        case s_greater:      return SEM_FLTCMP(>);
        case s_greaterequal: return SEM_FLTCMP(>=);
#undef SEM_FLTCMP
        default: syserr(syserr_trydiadicreduce2, (long)op);
                 return c;
    }
    if (status > flt_ok) {
        if (status == flt_very_small)
            flt_report_error(status);
        else {
            if (errorexpr == NULL)
            {   errormsg = sem_errwarn_fp_overflow;
                errorexpr = c;
            }
            /* improve */
            return MarkError(mk_expr2(op, type_(c), a, b),
                             errorexpr, errormsg);
        }
    }
    /* Safety, I presume (possibly can remove things like volatile?):   */
    flag &= bitoftype_(s_double)|bitoftype_(s_short)|bitoftype_(s_long);
    {   FloatCon *m = fltrep_from_widest(&r, flag, 0);
        return MarkError(mkinvisible(type_(c), c, (Expr *)m),
                         errorexpr, errormsg);
    }
  }
  if ((flag & bitoftype_(s_int)) && int_islonglong_(flag)) {
    Expr *fname, *revfname;
    if (flag & bitoftype_(s_unsigned))
      switch (op) {
      case s_plus:        revfname = fname = sim.lladd;               break;
      case s_minus:       revfname = sim.llrsb; fname = sim.llsub;    break;
      case s_times:       revfname = fname = sim.llmul;               break;
      case s_div:         revfname = sim.llurdv; fname = sim.lludiv;  break;
      case s_rem:         revfname = sim.llurrem; fname = sim.llurem; break;
      case s_and:         revfname = fname = sim.lland;               break;
      case s_or:          revfname = fname = sim.llor;                break;
      case s_xor:         revfname = fname = sim.lleor;               break;
      case s_leftshift:   revfname = NULL; fname = sim.llshiftl;      break;
      case s_rightshift:  revfname = NULL; fname = sim.llushiftr;     break;
      case s_equalequal:  revfname = fname = sim.llcmpeq;             break;
      case s_notequal:    revfname = fname = sim.llcmpne;             break;
      case s_less:        revfname = sim.llucmpgt; fname = sim.llucmplt; break;
      case s_lessequal:   revfname = sim.llucmpge; fname = sim.llucmple; break;
      case s_greater:     revfname = sim.llucmplt; fname = sim.llucmpgt; break;
      case s_greaterequal:revfname = sim.llucmple; fname = sim.llucmpge; break;
      default:            syserr(syserr_fp_op, (long)op);
                          revfname = fname = NULL;   /* To keep compiler quiet */
      }
    else
      switch (op) {
      case s_plus:        revfname = fname = sim.lladd;               break;
      case s_minus:       revfname = sim.llrsb; fname = sim.llsub;    break;
      case s_times:       revfname = fname = sim.llmul;               break;
      case s_div:         revfname = sim.llsrdv; fname = sim.llsdiv;  break;
      case s_rem:         revfname = sim.llsrrem; fname = sim.llsrem; break;
      case s_and:         revfname = fname = sim.lland;               break;
      case s_or:          revfname = fname = sim.llor;                break;
      case s_xor:         revfname = fname = sim.lleor;               break;
      case s_leftshift:   revfname = NULL; fname = sim.llshiftl;      break;
      case s_rightshift:  revfname = NULL; fname = sim.llsshiftr;     break;
      case s_equalequal:  revfname = fname = sim.llcmpeq;             break;
      case s_notequal:    revfname = fname = sim.llcmpne;             break;
      case s_less:        revfname = sim.llscmpgt; fname = sim.llscmplt; break;
      case s_lessequal:   revfname = sim.llscmpge; fname = sim.llscmple; break;
      case s_greater:     revfname = sim.llscmplt; fname = sim.llscmpgt; break;
      case s_greaterequal:revfname = sim.llscmple; fname = sim.llscmpge; break;
      default:            syserr(syserr_fp_op, (long)op);
                          revfname = fname = NULL;   /* To keep compiler quiet */
      }
    if (revfname != NULL && h0_(b) == s_fnap) {
      /* (invisible nodes have been removed from the head of a and b) */
      Expr *e = a;
      a = b; b = e; fname = revfname;
    }
    return MarkError(mk1fnap(fname, mkExprList2(a, b)),
                     errorexpr, errormsg);
  }
  { Expr *fname = NULL, *revfname = NULL;
    if (software_floats_enabled && is_float_(flag))
      switch(op)
      {
/* It may be that raising to a power will be done by a library call
   that will be introduced later, and so I do not need to map it onto
   a function call here... whatever else it seems a bit ugly, but it does
   not make any difference to C, only Fortran */
        case s_plus:        revfname = fname = sim.fadd;                break;
        case s_minus:       revfname = sim.frsb; fname = sim.fsubtract; break;
        case s_times:       revfname = fname = sim.fmultiply;           break;
        case s_div:         revfname = sim.frdiv; fname = sim.fdivide;  break;
        case s_power:       return c;  /* probably wrong */
        case s_equalequal:  revfname = fname = sim.fequal;              break;
        case s_notequal:    revfname = fname = sim.fneq;                break;
        case s_less:        revfname = sim.fgreater; fname = sim.fless; break;
        case s_lessequal:   revfname = sim.fgeq; fname = sim.fleq;      break;
        case s_greater:     revfname = sim.fless; fname = sim.fgreater; break;
        case s_greaterequal:revfname = sim.fleq; fname = sim.fgeq;      break;
        default:            syserr(syserr_fp_op, (long)op);
                            revfname = fname = NULL;   /* To keep compiler quiet */
      }
    else if (software_doubles_enabled && is_anydouble_(flag))
      switch(op)
      {
        case s_plus:        revfname = fname = sim.dadd;                break;
        case s_minus:       revfname = sim.drsb; fname = sim.dsubtract; break;
        case s_times:       revfname = fname = sim.dmultiply;           break;
        case s_div:         revfname = sim.drdiv; fname = sim.ddivide;  break;
        case s_power:       return c;  /* probably wrong */
        case s_equalequal:  revfname = fname = sim.dequal;              break;
        case s_notequal:    revfname = fname = sim.dneq;                break;
        case s_less:        revfname = sim.dgreater; fname = sim.dless; break;
        case s_lessequal:   revfname = sim.dgeq; fname = sim.dleq;      break;
        case s_greater:     revfname = sim.dless; fname = sim.dgreater; break;
        case s_greaterequal:revfname = sim.dleq; fname = sim.dgeq;      break;
        default:            syserr(syserr_fp_op, (long)op);
                            revfname = fname = NULL;   /* To keep compiler quiet */
      }
    if (revfname != NULL && h0_(b) == s_fnap) {
     /* (invisible nodes have been removed from the head of a and b) */
      Expr *e = a;
      a = b; b = e; fname = revfname;
    }
    if (fname != NULL)
      return MarkError(mk1fnap(fname, mkExprList2(a, b)),
                       errorexpr, errormsg);
  }
  return errorexpr == NULL ? c : MarkError(mk_expr2(op, type_(c), a, b),
                                           errorexpr, errormsg);
}

static Expr *trymonadreduce(AEop op, Expr *a, Expr *c, SET_BITMAP flag)
{ Expr *errorexpr = NULL;
  msg_t errormsg = NULL;
  if (h0_(a) == s_evalerror)
  { errorexpr = arg2_(a);
    errormsg = (msg_t)arg3_(a);
    a = arg1_(a);
  }
  if (h0_(a) == s_integer)
  { unsigned32 m = intval_(a), r;
    bool ok = YES;
    switch (op)   /* BEWARE: 2's complement means signed == unsigned */
    {   case s_monplus:  r = m; break;
        case s_neg:      r = 0-m;
                         if (!(flag & bitoftype_(s_unsigned)))
                             ok = (int32)(m&r&0x80000000) == 0;
                         break;
        case s_bitnot:   r = ~m; break;
        case s_boolnot:  r = !m; break;
        default:         syserr(syserr_trymonadicreduce, (long)op);
        case s_content:  return c;
    }
    r = widen32bitint_(r);
    if (sizeof_int == 2)
    {   if (flag & bitoftype_(s_unsigned))
        {   if (!(flag & bitoftype_(s_long)) && (r & 0xffff0000))
                r &= 0x0000ffff, ok = NO;
        }
        else
        {   if (!(flag & bitoftype_(s_long)) && r != (unsigned32)(int16)r)
                r = (int16)r, ok = NO;
        }
    }
    if (!ok && errorexpr == NULL)
    {   errormsg = (flag & bitoftype_(s_unsigned))
            ? sem_errwarn_umonad_overflow
            : sem_errwarn_monad_overflow;
    }
    return MarkError(mkintconst(type_(c),r,c),
                     errorexpr, errormsg);
  }
  if (h0_(a) == s_int64con)
  { int64 av = int64val_(a).i;
    int64 rv;
    I64_Status ok = i64_ok;
    switch (op)
    {   case s_monplus:  rv = av; break;
        case s_neg:      ok = I64_Neg(&rv, &av); break;
        case s_bitnot:   I64_Not(&rv, &av); break;
        default: syserr(syserr_trymonadicreduce1, (long)op);
                 return c;
    }
    if (ok != i64_ok && errorexpr == NULL)
    {   errormsg = (flag & bitoftype_(s_unsigned))
            ? sem_errwarn_umonad_overflow
            : sem_errwarn_monad_overflow;
    }
    return MarkError((Expr *)mkint64const(flag, &rv),
                     errorexpr, errormsg);
  }


  a = skip_invisible(a);
  if (h0_(a) == s_floatcon)
  { int32 flag = exf_(a)->floatlen;     /* same as type info.   */
    DbleBin d,r;
    int status;
    fltrep_to_widest(&d, exf_(a));
    switch (op)
    {   case s_monplus:  status = flt_move(&r,&d); break;
        case s_neg:      status = flt_negate(&r,&d); break;
        default: syserr(syserr_trymonadicreduce1, (long)op);
                 return c;
    }
    if (status > flt_ok)
    { if (errorexpr == NULL)
      { errormsg = sem_errwarn_fp_overflow;
        errorexpr = c;
      }
      return MarkError(mk_expr1(op, type_(c), a),
                       errorexpr, errormsg);
    }
    {   FloatCon *m = fltrep_from_widest(&r, flag, 0);
        return MarkError(mkinvisible(type_(c), c, (Expr *)m),
                         errorexpr, errormsg);
    }
  }
  if ((flag & ts_longlong) == ts_longlong) {
    TypeExpr *t = princtype(typeofexpr(a));     /* hmm */
    SET_BITMAP m = h0_(t)==s_typespec ? typespecmap_(t) : 0;
    if ((m & ts_longlong) == ts_longlong) {
      Expr *fname;
      switch (op) {
      case s_monplus:     return a;
      case s_neg:         fname = sim.llneg; break;
      case s_bitnot:      fname = sim.llnot; break;
      default:            syserr(syserr_trymonadicreduce, (long)op);
                          fname = NULL;   /* To keep compiler quiet */
      }
      return MarkError(mk1fnap(fname, mkExprList1(a)),
                       errorexpr, errormsg);
    }
  }
  { TypeExpr *t = princtype(typeofexpr(a));     /* hmm */
    SET_BITMAP m = h0_(t)==s_typespec ? typespecmap_(t) : 0;
    Expr *fname = NULL;
    if (software_floats_enabled && is_float_(m))
      switch (op)
      {
        case s_monplus: return a;
        case s_neg:     fname = sim.fnegate;    break;
        default:        syserr(syserr_fp_op, (long)op);
      }
    else if (software_doubles_enabled && is_anydouble_(m))
      switch (op)
      {
        case s_monplus: return a;
        case s_neg:     fname = sim.dnegate;    break;
        default:        syserr(syserr_fp_op, (long)op);
      }
    if (fname != NULL)
      return MarkError(mk1fnap(fname, mkExprList1(a)),
                       errorexpr, errormsg);
  }
  return errorexpr == NULL ? c : MarkError(mk_expr1(op, type_(c), a),
                                           errorexpr, errormsg);
}

static Expr *castfn(Expr *e)
{
    TypeExpr *t1, *t2;
    Expr *a = arg1_(e), *fname = NULL;
    SET_BITMAP m1, m2;
    if (h0_(e) != s_cast) return e;
    t1 = princtype(type_(e));           /* hmm (SOFTWARE_FLOATING_POINT) */
    t2 = princtype(typeofexpr(a));      /* hmm (SOFTWARE_FLOATING_POINT) */
    if (h0_(t1) != s_typespec || h0_(t2) != s_typespec) return e;
    m1 = typespecmap_(t1);
    if (m1 & bitoftype_(s_void)) return e; /* cast to void: leave alone  */
    m2 = typespecmap_(t2);
    if (int_islonglong_(m1)) {
        if (m2 & bitoftype_(s_double)) {
            fname = (m1 & bitoftype_(s_unsigned))
                ? ((m2 & bitoftype_(s_short)) ? sim.llufromf : sim.llufromd)
                : ((m2 & bitoftype_(s_short)) ? sim.llsfromf : sim.llsfromd);

        } else if (int_islonglong_(m2)) {
            if ((m1 ^ m2) & (bitoftype_(s_signed) | bitoftype_(s_unsigned)))
            /* Change of signedness : cast must stay */
                return e;
            else
                return a;
        } else
            fname = (m2 & bitoftype_(s_unsigned)) ? sim.llfromu : sim.llfroml;

    } else if (int_islonglong_(m2)) {
        if (m1 & bitoftype_(s_double))
            fname = (m2 & bitoftype_(s_unsigned))
                ? ((m1 & bitoftype_(s_short)) ? sim.llutof : sim.llutod)
                : ((m1 & bitoftype_(s_short)) ? sim.llstof : sim.llstod);
        else
            return mkcast(s_cast, mk1fnap(sim.lltol, mkExprList1(a)), t1);

    } else if (is_float_(m1)) {
        if (is_float_(m2))
            return a;
        else if (software_floating_point_enabled && is_anydouble_(m2))
            fname = sim.fnarrow;
        else if (software_floats_enabled)
            fname = (m2 & bitoftype_(s_unsigned)) ? sim.ffloatu : sim.ffloat;
#ifdef TARGET_LACKS_UNSIGNED_FIX
        else if (software_doubles_enabled && (m2 & bitoftype_(s_unsigned)))
            fname = sim.ffloatu;
#endif
    } else if (is_anydouble_(m1)) {
        if (software_floating_point_enabled && is_float_(m2))
            fname = sim.dwiden;
        else if (is_anydouble_(m2))
            return a;
        else if (software_doubles_enabled)
            fname = (m2 & bitoftype_(s_unsigned)) ? sim.dfloatu : sim.dfloat;
    }
    if (fname != NULL) return mk1fnap(fname, mkExprList1(a));

    if (software_floats_enabled && is_float_(m2))
        fname = (m1 & bitoftype_(s_unsigned)) ? sim.ffixu : sim.ffix;
    else if (software_doubles_enabled && is_anydouble_(m2))
        fname = (m1 & bitoftype_(s_unsigned)) ? sim.dfixu : sim.dfix;
#ifdef TARGET_LACKS_UNSIGNED_FIX
    else if (software_doubles_enabled && is_float_(m2) && (m1 & bitoftype_(s_unsigned)))
        fname = sim.ffixu;
#endif
    if (fname != NULL)
        return mkcast(s_cast, mk1fnap(fname, mkExprList1(a)), type_(e));

    return e;
}

static Expr *trycastreduce(Expr *a, TypeExpr *tc, Expr *c, bool explicit)
/* Args somewhat redundant -- c = (s_cast,tc,a)                       */
{ TypeExpr *x = princtype(tc);          /* type being cast to.        */
                             /* (can ignore typedef qualifiers).      */
  if (h0_(a) == s_integer || h0_(a) == s_int64con)
  { bool truncated = NO;
    unsigned32 n, r;
    SET_BITMAP m, ta;
    if (h0_(a) == s_integer) {
      ta = typespecmap_(princtype(type_(a)));
      n = intval_(a);
    } else {
      ta = int64map_(a);
      truncated = I64_UToI(&n, &int64val_(a).u);
    }
    r = n;
    switch (h0_(x))          /* signed/unsigned shouldn't matter here */
    {
case s_typespec:
        m = typespecmap_(x);
        switch (m & -m)    /* LSB - unsigned/long etc. are higher */
        {
    case bitoftype_(s_char):
            r = (issignedchar_(m) && (n & 0x80))
                ? (n | ~(int32)0xff) : (n & 0xff);
            break;
    case bitoftype_(s_enum):    /* ansi C says treat like 'int'.        */
    case bitoftype_(s_int):
            if (int_islonglong_(m)) {
                if (h0_(a) == s_int64con) {
                    return (Expr *)mkint64const(m, &int64val_(a).i);
                } else if (ta & bitoftype_(s_unsigned)) {
                    uint64 u;
                    I64_IToU(&u, n);
                    return (Expr *)mkint64const(m, (int64 *)&u);
                } else {
                    int64 i;
                    I64_IToS(&i, n);
                    return (Expr *)mkint64const(m, &i);
                }
            }
            if ((int_isshort_(m) ? sizeof_short :
                 (m & bitoftype_(s_long)) ? sizeof_long : sizeof_int) == 2)
                r = (!(m & bitoftype_(s_unsigned)) && (n & 0x8000))
                    ? (n | ~(int32)0xffff) : (n & 0xffff);
            break;
    case bitoftype_(s_void):
            r = 0;
            goto omit_check;            /* mkvoided did it for us.      */
    case bitoftype_(s_double):
            /* remember (double)(-1u) != (double)(-1) ... */
/* Use int_to_real() rather than flt_itod() or flt_utod() since it fills */
/* in a string with the number etc etc etc.                              */
            if (ta & ARITHTYPEBITS)
                return mkinvisible(tc, c, (Expr *)int_to_real(
                    n, ta & bitoftype_(s_unsigned), m));
            /* drop through */
            default: return c;     /* always harmless to return cast */
        }
        if (!explicit && (truncated || r != n))
            cc_ansi_warn(sem_rerr_implicit_cast_overflow(x,n,r));
        break;
case t_content:
        r = n==0 ? TARGET_NULL_BITPATTERN : n;
        break;        /* cast to pointer                */
default:
        return c;     /* should not happen (prev error) */
    }
omit_check:
    return mkintconst(tc,r,c);
  }

  a = skip_invisible(a);
  if (h0_(a) == s_floatcon)
  { /* We have a cast (possibly implicit) on a floating constant value. */
    /* Produce a new FloatCon value with the new type.                  */
    if (h0_(x) == s_typespec)
    {   SET_BITMAP m = typespecmap_(x);
        int32 n; int status;
        DbleBin d;
        fltrep_to_widest(&d, exf_(a));
        switch (m & -m)
        {   case bitoftype_(s_char):
                status = (issignedchar_(m)) ? flt_dtoi(&n, &d)
                                            : flt_dtou((unsigned32 *)&n, &d);
/* I do not complain about (char)258.0, but I will moan at (char)1.e11   */
/* where 1.e11 will not fit in an int. This is at least compatible with  */
/* run-time behaviour on casts.                                          */
                n = (issignedchar_(m) && (n & 0x80))
                    ? (n | ~(int32)0xff) : (n & 0xff);
                break;
            case bitoftype_(s_int):
                status = (m & bitoftype_(s_unsigned)) ? flt_dtou((unsigned32 *)&n, &d)
                                                      : flt_dtoi(&n, &d);
                if ((int_isshort_(m) ? sizeof_short :
                     (m & bitoftype_(s_long)) ? sizeof_long : sizeof_int) == 2)
                    n = (!(m & bitoftype_(s_unsigned)) && (n & 0x8000))
                        ? (n | ~(int32)0xffff) : (n & 0xffff);
                break;
            case bitoftype_(s_enum):
                status = flt_dtoi(&n, &d); /* This case seems pretty dodgy! */
                break;
            case bitoftype_(s_double):
              { char *oldfloatstr = exf_(a)->floatstr;
                FloatCon *fc = fltrep_from_widest(&d, m, oldfloatstr);
                return mkinvisible(tc, c, (Expr *)fc);
              }
            default:
                /* this includes the (void)1.3 case for which warning has */
                /* already been given.  Could do ok=1, n=0 instead.       */
                return c;
        }
        if (status > flt_ok)
        {   cc_warn(sem_warn_fix_fail);
            n = 0;
        }
        return mkintconst(tc,n,c);
    }
    return c;   /* nothing doing */
  }
  return c;
}

/* check_index_overflow checks if an address computation (possibly via  */
/* a subscript operation) indexes an array whose size, n, is manifest.  */
/* If so then it checks that a (constant) offset is in the range 0..n.  */
/* IF a dereference later occurs, then we moan at the use of offset n   */
/* too.  At this time, though, the stride will have been multiplied     */
/* into the offset, so we have to compensate.  Argument 'stride' is     */
/* a TypeExpr * for the stride type or NULL if not dereferenced (yet).  */
/* Note also that modify_formal_type makes this hard to do (and less    */
/* justifiable) in  "int f(int a[4]) { return a[-1]; }".  Hence don't.  */
static void check_index_overflow(Expr *ptr, Expr *disp, int posneg,
                                 bool deref)
{   TypeExpr *t0;
    if (HasFeature(Feature_PCC)) return;
    t0 = typeofexpr(ptr);
    ptr = skip_invisible_or_cast(ptr); /* @@@ skip_invisible doesn't work? */
    if (h0_(disp) == s_integer && h0_(ptr) == s_addrof)
    {   TypeExpr *t = type_(ptr);
        if (h0_(t) == t_content)
        {   TypeExpr *t2 = princtype(typearg_(t));
            /* princtype since array type may be typedef'd.             */
            if (h0_(t2) == t_subscript)
            {   Expr *bound = typesubsize_(t2);
                int32 k = sizeoftype(typearg_(princtype(t0)));
                int32 n = posneg * intval_(disp);
                if (bound && h0_(bound) == s_binder) bound = NULL;
                if (k == 0) k = 1; /* paranoia */
                if (!deref)
                {   /* always whinge for n<0 or n>limit...              */
                    if (n < 0 || bound && n * k> evaluate(bound) * sizeoftype(typearg_(t2)))
                        cc_warn(sem_warn_index_ovfl, n);
                }
                else
                {   /* ... but also if n=limit AND dereferencing.       */
                   if (bound && n == evaluate(bound) * k)
                        cc_warn(sem_warn_index_ovfl, n/k);
                }
            }
        }
    }
}

static void check_index_dereference(Expr *e)
{   if (!HasFeature(Feature_PCC) && h0_(e) == s_content)
    {   Expr *a = arg1_(e);
        if (h0_(a) == s_plus)
#ifdef OLD_POINTER_CODE
            check_index_overflow(arg2_(a), arg1_(a), 1, YES),
#endif
            check_index_overflow(arg1_(a), arg2_(a), 1, YES);
        if (h0_(a) == s_minus)
            check_index_overflow(arg1_(a), arg2_(a), -1, YES);
    }
}

static Expr *nonconst1(Expr *e)
/* make this table driven */
{   Expr *e1;
    for (;;) switch (h0_(e))
    {   default: return e;
        case s_integer: return 0;
        case s_invisible: e = orig_(e); break;
        case s_cast:
        case s_monplus:
        case s_neg:
        case s_bitnot:
        case s_boolnot: e = arg1_(e); break;
        case s_plus:
        case s_minus:
        case s_times:
        case s_div:
        case s_rem:
        case s_and:
        case s_or:
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
        case s_comma: if ((e1 = nonconst1(arg1_(e))) != 0) return e1;
                      e = arg2_(e); break;
        case s_cond:  if ((e1 = nonconst1(arg1_(e))) != 0) return e1;
                      if ((e1 = nonconst1(arg2_(e))) != 0) return e1;
                      e = arg3_(e); break;
    }
}

void moan_nonconst(Expr *e, msg_t nonconst_msg,
                   msg_t nonconst1_msg, msg_t nonconst2_msg)
{
    if (debugging(DEBUG_TYPE))
    { eprintf("moan_nonconst on "); pr_expr(e); }
    e = nonconst1(e);
    if (e == 0) cc_err(nonconst_msg);
    else if (h0_(e) == s_binder)
        cc_err(nonconst1_msg, (exb_(e)));
    else
        cc_err(nonconst2_msg, h0_(e));
}

static bool check_narrow_subterm(Expr *e, TypeExpr *te, TypeExpr *tt)
{   tt = princtype(tt), te = princtype(te);     /* ignore qualifiers */
    if (h0_(tt) == s_typespec && h0_(te) == s_typespec &&
        (/* moan at int/long ops in any float context */
           typespecmap_(tt) & ~typespecmap_(te) & bitoftype_(s_double) ||
         /* moan at plain ops in long context, both same floatiness. */
           !((typespecmap_(tt) ^ typespecmap_(te)) & bitoftype_(s_double)) &&
           typespecmap_(tt) & ~typespecmap_(te) & bitoftype_(s_long) ||
         /* moan at (float) short double in other float context */
           typespecmap_(tt) & bitoftype_(s_double) &&
           typespecmap_(te) & ~typespecmap_(tt) & bitoftype_(s_short)
         ))
    {
retry:  switch h0_(e)
        {
    case s_invisible:
            e = orig_(e); goto retry;
    case s_comma:
            e = arg2_(e); goto retry;
    case s_monplus:
            e = arg1_(e); goto retry;
    case s_and: case s_or: case s_xor:
    case s_leftshift: case s_rightshift:
    case s_plus: case s_minus: case s_times: case s_div:
    /* but not s_ptrdiff -- since long a = ptr1-ptr2 is always ok */
    case s_rem:
    case s_neg: case s_bitnot:
#ifdef EXTENSION_VALOF
    case s_valof:
#endif
#ifndef FORTRAN         /* re-instate something like this for f77 soon  */
            if (SuppressDB_Has(Suppress_LowerInWider)) xwarncount++;
            else
                cc_warn(sem_warn_low_precision, h0_(e));
#endif
            return 1;
    case s_cond:
            /* "long x = p() ? 1 : 2;" cannot reasonably give a warning */
            /* but think more about "long x = p() ? 33000 : 1".         */
            return check_narrow_subterm(arg2_(e), te, tt) ? 1 :
                   check_narrow_subterm(arg3_(e), te, tt);
#ifdef never
    case s_integer:
            if ((e = intorig_(e)) != 0) goto retry;
            /* drop through */
    case s_andand: case s_oror:
    case s_equalequal: case s_notequal: /* + other relops */
#endif
    default:
            break;
        }
    }
    return 0;
}

static int32 bf_container_bits(TypeExpr *t)
{   SET_BITMAP m = typespecmap_(t);
    if (m & bitoftype_(s_char))  return 8;
    if (int_islonglong_(m)) return 8 * sizeof_longlong;
#ifdef TARGET_LACKS_HALFWORD_STORE
    if (target_lacks_halfword_store) return MAXBITSIZE;
#endif
    if (int_isshort_(m)) return sizeof_short*8;
    return MAXBITSIZE;
}

static Expr *bf_container(Expr *e, SET_BITMAP m)
{   if (!(h0_(e) == s_dot && m & BITFIELD)) syserr(syserr_bf_container);
    /* @@@ te_int is OK while sizeof_int == sizeof_long.                */
    /* in the longer term move to an 'unbitfield_type()' container?     */
    {   int32 maxsize = bf_container_bits(type_(e));
        if (maxsize >= MAXBITSIZE)
            return mk_exprwdot(s_dot,
                           mkqualifiedtype(int_islonglong_(m) ? te_llint : te_int,
                                           m & QUALIFIER_MASK),
                           arg1_(e), exprdotoff_(e));
        else {
            int32 off = exprdotoff_(e);
            TypeExpr *te = primtype2_(m & ~BITFIELD, typespectagbind_(type_(e)));
            int32 byteoff = (exprmsboff_(e) / maxsize) * (maxsize / 8);
            if (target_lsbytefirst) byteoff = sizeof_int - (maxsize / 8) - byteoff;
            return mk_exprwdot(s_dot, te, arg1_(e), off+byteoff);
        }
    }
}

static Expr *coerce2(Expr *e, TypeExpr *t)
  /* does NOT check consistent - use mkcast for this */
  /* really only for implicit arithmetic casts       */
{   Expr *r;
    TypeExpr *te = princtype(typeofexpr(e));   /* ignore cast qualifiers   */
    if (equivtype(t,te) == 2) return e;        /* identical types, no cast */
    if (isbitfield_type(te)) {
      SET_BITMAP m = typespecmap_(te);
      e = bitfieldvalue(e, m, bf_container(e, m));
    }
    (void)check_narrow_subterm(e, te, t);
    r = mk_expr1(s_cast, t, e);
    r = trycastreduce(e,t,r,NO);
    return castfn(r);
/* the invisible node in the following should never be seen and
   needs re-thinking re constant reduction.                          */
/*     return mkinvisible(t, e, mk_expr1(s_cast, t, e));         */
}

/* The complications below for coercion context are due to AM's         */
/* implementation of the fact that in most contexts fns/arrays are      */
/* coerced to pointers exactly when char/short/bitfield are widened to  */
/* int.  (I.e. neither for lvalue (inlcuding sizeof) context, both for  */
/* rvalue context).  The exception is comma context, where ANSI have    */
/* (foolishly?) specified that, given char a[10], we have               */
/* sizeof(0,a)==sizeof(char *), sizeof(0,a[0])==sizeof(char).  Yuk.     */
/* The implementation chosen is further encouraged by the observation   */
/* that otherwise we would make comma-context the only non-lvalue       */
/* phrase to have non-widened types, which seems like a bug invitation. */
/* For C++ errors, and also C *warnings*, for abuse of int/enum we      */
/* now defer widening of enum to int.                                   */
enum Coerce_Context { COERCE_NORMAL, COERCE_ARG, COERCE_COMMA,
                      COERCE_ASSIGN,
                      COERCE_VOIDED };
/* COERCE_VOIDED is the same as COERCE_NORMAL, except that non lvalue   */
/* array objects are permitted and C++ refs are not deref'd             */

/* coerceunary ought to be idempotent for its uses.                     */
/* Its caller has ensured that 'e' is not s_error (errornode).          */
static Expr *coerceunary_2(Expr *e, enum Coerce_Context c)
{   TypeExpr *qt = typeofexpr(e), *t = princtype(qt);
    /* NB. in principle coerceunary() converts lvalues to rvalues and   */
    /* hence could remove top level qualifiers.  However, this would    */
    /* turn over (a little?) more store and routines elsewhere happily  */
    /* manage to ignore such qualifiers.                                */
    /* Surprisingly, 'qt' is needed for coercing lvalues such as x in   */
    /* "typedef int t[3][4]; const t x;".  This must coerce x to        */
    /* type (const int (*)[4]).  See t_subscript case.                  */
    SET_BITMAP m;
    if (debugging(DEBUG_TYPE))
        {   eprintf("Coerceunary called: "); pr_expr_nl(e); }
    /* Here is just the place to check that "a[n]" is (in)valid given   */
    /* the declaration "int a[n]".                                      */
    check_index_dereference(e);
    if (LanguageIsCPlusPlus)
    {
        if (h0_(e) == s_binder && bindconst_(exb_(e)))
            e = mkinvisible(qt, e, bindconst_(exb_(e)));
    }
    if (LanguageIsCPlusPlus)
    {   if ((h0_(e) == s_binder || h0_(e) == s_member) &&
            attributes_(exb_(e)) & CB_ANON)
            e = mkfieldselector(s_dot, (Expr *)realbinder_(exb_(e)),
                                       (ClassMember *)bindsym_(exb_(e)));
        /* do 'enum' constant name -> integer const here too?               */
    }
    switch (h0_(t))
    {
case s_typespec:
        m = typespecmap_(t);
        switch (m & -m)    /* LSB - unsigned/long etc. are higher */
        {
    case bitoftype_(s_char):            /* INTEGRALTYPEBITS             */
    case bitoftype_(s_bool):
    case bitoftype_(s_int):
    case bitoftype_(s_enum):
/* For explanation of the next line see the comment for COERCE_COMMA.   */
            if (c == COERCE_COMMA) return e;
/* As part of the previous line, we now have to unravel char/bitfields  */
/* in NORMAL/ARG context, but they may be embedded inside s_comma:s.    */
/* This is needed to avoid s_dot syserr() and to preserve the useful    */
/* fact that only l-value and fn-return aetrees can have narrow values. */
            if (h0_(e) == s_comma && m & (BITFIELD|
                   bitoftype_(s_char)|bitoftype_(s_short)|bitoftype_(s_enum))
                                  && !(m & bitoftype_(s_long)))
            {   /* BEWARE: smashing of tree known to be unshared.       */
                arg2_(e) = coerceunary_2(arg2_(e), c);
                type_(e) = typeofexpr(arg2_(e));
                return e;
            }
/* bitfieldvalue can promote to signed or unsigned int.                 */
/* For C++ it can also promote to enum.   @@@ review long bit fields.   */
/* @@@ For systems in which sizeof_long>sizeof_int then maybe we should */
/* allow long bit values and promotion to (unsigned)long as an ANSI-    */
/* conformant extension.  See what the ANSI C++ committee think.        */
            if (m & BITFIELD)  /* rvalue context here */
            {   Expr *ee = skip_invisible(e);
                return bitfieldvalue(ee, m, bf_container(ee, m));
            }
/* C++: it is arguable that COERCE_ARG (unchecked params) should        */
/* not promote its arg here.  Then we could warn on printf("%d", enum)  */
/* In C, of course, this is perfectly OK.                               */
            if (m & bitoftype_(s_enum) && c == COERCE_ASSIGN) return e;
/* ANSI says coerce unsigned or signed char (or short) to (signed) int  */
/* if shorter.  PCC says unsigned char (or short) coerce to unsigned.   */
/* This code now copes with sizeof_int==sizeof_short.                   */
/* It does not cope with sizeof_int==sizeof_char in ANSI mode.          */
/* In C++ enums promote to int or unsigned int depending on their       */
/* container type.  @@@ Promoting enums to long or unsigned long is not */
/* yet handled.                                                         */
            if (m & (bitoftype_(s_char)|bitoftype_(s_short)
                                       |bitoftype_(s_enum)) &&
                    /* next line copes with "long long" encoding.       */
                    !(m & bitoftype_(s_long)))
                e = HasFeature(Feature_PCC) ?
                    /* Someone might like to worry about the case       */
                    /* where default char is unsigned in PCC mode       */
                    /* does it then promote to signed int (as now) or   */
                    /* unsigned int?  K&R say (signed) int.             */
                    coerce2(e,
                        (m & bitoftype_(s_unsigned)) ? te_uint:te_int) :
                    coerce2(e,
                        ((sizeof_short==sizeof_int && int_isshort_(m)
                          && m & bitoftype_(s_unsigned))
                         || (LanguageIsCPlusPlus
                             && (m & bitoftype_(s_enum))
                             && ((tagbindbits_(typespectagbind_(t))
                                  & TB_CONTAINER) == TB_CONTAINER_UINT))) ?
                            te_uint:te_int);
            return e;
    case bitoftype_(s_double):
/* The pcc mode code here may need improving (as char above) if PCC has */
/* sizeof(0,(float)0)==sizeof(float) -- this code gives sizeof(double). */
            if ((c == COERCE_ARG || HasFeature(Feature_PCC)) &&
                (m & bitoftype_(s_short)))
                return coerce2(e, te_double);
            return e;
    case bitoftype_(s_struct):
    case bitoftype_(s_class):
    case bitoftype_(s_union):
    case bitoftype_(s_void):
            return e;
    default:
            break;
        }
        break;
case t_unknown:
case t_content:
        return e;
case t_subscript:
        if (!HasFeature(Feature_PCC) && c != COERCE_VOIDED)
                                        /* recovery better be good.     */
            (void)ensurelvalue(e, s_addrof);
        /* Complications here coercing a const array into a pointer to  */
        /* a const element.  Use "t a[n]" -> "(t *)&a"                  */
        {   TypeExpr *t1 = ptrtotype_(
                  mkqualifiedtype(typearg_(t), typedef_qualifiers(qt)));
            return mkinvisible(t1, e,
                               mk_expr1(s_cast, t1, mkaddr(e)));
        }
case t_ref:
        {   if (c == COERCE_COMMA || c == COERCE_VOIDED)
                return e;
            else
            {   TypeExpr *t2 = typearg_(t);
                /* recursion allows for ref to array/fn [ES,p128,l-1]!!?    */
                return coerceunary_2(
                      mkinvisible(t2, e, mk_expr1(s_content,t2,e)),  c);
            }
        }
case t_coloncolon:
/*      if (!LanguageIsCPlusPlus) break; -- must be C++ */
        return thisify(e);
case t_ovld:
/*      if (!LanguageIsCPlusPlus) break; -- must be C++ */
        /* It's never the right thing to do to change a generic into a
           specific just because there's only one.  But we do it here
           (ovld_resolve_addr, actually) to make some cases work that we
           haven't implemented in general (n-way overloaded) yet. */
        {   BindList *bl = typeovldlist_(t);
            if (cdr_(bl) == NULL) /* hack to allow single static memfn */
            {   Expr *tmp = (Expr *)ovld_resolve_addr(e, typeovldlist_(t));
                if (h0_(tmp) != s_binder ||
                    (bindparent_((Binder*)tmp) != NULL &&
                     !(bindstg_((Binder*)tmp) & b_memfns)))
                    return e;
                /* same as t_fnap case */
                e = tmp;
                t = typeofexpr(e);
    #if NEVER
                return coerceunary_2(
                       (Expr *)ovld_resolve_addr(e, typeovldlist_(t)), c);
    #endif
                /* fall through to case t_fnap */
            }
            else /* no coersion from 'T::f' to '&T::f' */
                return e;
        }
case t_fnap:
        if (LanguageIsCPlusPlus)
        {   if (h0_(e) == s_dot)        /* C++ member function          */
            /* @@@ give a type warning on the next line?                */
                return coerceunary_2(exprdotmemfn_(e),c);
            if (h0_(e) == s_dotstar)    /* see [ES, p71]                */
            {   cc_err(sem_err_noncallsite_function);
                return errornode;
            }
/* Note re thisify(): &memfn2 is legal even in a static member fn.     */
            if (h0_(e) == s_binder && bindstg_(exb_(e)) & b_impl)
            {   Binder *b = realbinder_(exb_(e));
                if (bindstg_(b) & b_memfna)
                    t = (TypeExpr *)syn_list3(t_coloncolon, t,
                                              bindparent_(exb_(e)));
/* Take address of implementation but use type of member.               */
/* Making a memfn behave like s_member in typeofexpr() would help here. */
                e = (Expr *)b;
            }
        }
        {   TypeExpr *t2 = ptrtotype_(t);
            return mkinvisible(t2, e, mk_expr1(s_addrof,t2,e));
        }
default:;
    }
    syserr(syserr_coerceunary1, (long)h0_(t), (long)typespecmap_(t));
    return e;
}

Expr *coerceunary(Expr* e)
{ return coerceunary_2(e, COERCE_NORMAL); }

/* Null pointer constants are defined in Dec 88 draft, section 3.2.2.3. */
/* This routine accepts (void *)(int *)0 as NPC, drafts leave undef'd.  */
bool isnullptrconst(const Expr *e)
{   if (h0_(e) == s_integer)
    {   TypeExpr *t = princtype(type_(e));   /* type_(e)==typeofexpr(e) */
        if (h0_(t) == s_typespec && typespecmap_(t) & INTEGRALTYPEBITS &&
                                    intval_(e) == 0 ||
/* Note: (void *)0 is a NPC, but (const void *)0 isn't.  We assume      */
/* (void *const)0 is a NPC, because qualifiers are ignored on non-      */
/* lvalues, of which casts are an example.                              */
            isptrtovoidtype(t) && intval_(e) == TARGET_NULL_BITPATTERN)
          return 1;
    }
    return 0;
}

static Expr *pointerofint(Expr *e, AEop op, TypeExpr *t)
{   if (!isnullptrconst(e) || (op != s_equalequal && op != s_notequal))
        cc_pccwarn(sem_rerr_pointer_compare, op);
    return coerce2(e,t);
}

Expr *mkintegral(AEop op, Expr *a)     /* op in {s_switch, s_subscript} */
{   if (h0_(a = coerceunary(a)) == s_error) return a;
    {
/* @@@ We should check warnings (C++ errs!) for switch(enum) etc here.  */
        TypeExpr *t = princtype(typeofexpr(a));
        if (h0_(t) == s_typespec)
        {   SET_BITMAP m = typespecmap_(t);
            switch (m & -m)
            {   case bitoftype_(s_int):       /* possibly long/unsigned */
                    if (!int_islonglong_(m))
                        return a;
            }
        }
/* It is debatable whether 'int' is the right type on the next line,    */
/* but observe that only erroneous cases (flts/pointers/etc) go here.   */
        return mkcast(op, a, te_int);
    }
}

/* mktest() is used for exprs in conditional (0/non-0) context.
   It does two things.
   1) warns (optionally later) of '=' if '==' could be more sensible.
   2) adds a !=0 node to any non-boolean values, so result is always 0/1
      which also takes care of type-checking modulo error messages.
*/
Expr *mktest(AEop opreason, Expr *a)
{   Expr *x;
    AEop op;
    for (x=a;;) switch (op = h0_(x))
    {   case s_invisible:
           x = orig_(x); break;
        case s_comma:
           x = arg2_(x); break;
        case s_oror:
        case s_andand:
        case s_boolnot:
            return a;   /* type must be OK.  Args already done.  */
        case s_assign:
        case s_bitnot:
            if (SuppressDB_Has(Suppress_AssignTest)) xwarncount++;
            else cc_warn(sem_warn_odd_condition, op);
            /* drop through */
        default:
        {   IGNORE(opreason);      /* re-think whether this is useful */
            if (isrelational_(op)) return a;  /* type OK */
            if (LanguageIsCPlusPlus)
            {   TypeExpr *t = princtype(typeofexpr(a));
                if (isprimtype_(t, s_bool))
                    return mkbinary(s_notequal, a, lit_false);
                a = coerceunary(a);
                t = princtype(typeofexpr(a));
                if (isclasstype_(t))
                    a = allowable_boolean_conversion(a);
                else if (!((h0_(t) == s_typespec) &&
                        (typespecmap_(t) & ARITHTYPEBITS)) &&
                        h0_(t) != t_content &&
                        !isptrtomember(t))
                {   if (h0_(t) != t_unknown) typeclash(s_notequal);
                    a = errornode;
                }
            }
            /* Beware TARGET_NULL_BITPATTERN */
            return LanguageIsCPlusPlus ?
                cpp_mkbinaryorop(s_notequal, a, lit_zero) :
                mkbinary(s_notequal, a, lit_zero);
        }
    }
}

static Expr *mkvoided(Expr *e)
/* currently always returns its arg */
{   Expr *x; AEop op;
    for (x = e;;) switch (op = h0_(x))
    {   case s_invisible:
            x = orig_(x); break;
        case s_cast:    /* This could otherwise moan about the wrong    */
                        /* operator since coerce2 can insert s_cast:s   */
                        /* without an s_invisible node.                 */
            x = arg1_(x); break;
        case s_fnap:    /* Only non-void results come here: moan?       */
            return e;
        case s_let:
        case s_comma:
            x = arg2_(x); break;
        case s_cond:
            (void)mkvoided(arg2_(x)); x = arg3_(x); break;
        case s_integer:
            if (intorig_(x)) { x = intorig_(x); break; } /* (void)(1+2); */
/* treat 0 specially because (e ? f() : 0) is common (indeed necessary)  */
/* in macro:s (e.g. assert) which must be an expression, not command.    */
            {   TypeExpr* t = princtype(typeofexpr(x));
                if (isprimtype_(t, s_int) && intval_(x) == 0)
                    return e;
                else if (isprimtype_(t, s_char))
                    op = s_character;
                else if (isprimtype_(t, s_bool))
                    op = intval_(x) ? s_true : s_false;
                    /* and drop through */
            }
            /* else drop through */
        default:
/* Suppression of warnings for explicit casts is now done by caller.    */
            if (
#ifdef FOR_ACORN
                !cplusplus_flag &&
#endif
                !(isassignop_(op) || isincdec_(op)
                  || (op == s_binder && isgensym(bindsym_(exb_(x))))))
                cc_warn(sem_warn_void_context, op);
            /* drop through */
        case s_assign: case s_init:
            return e;
#ifdef EXTENSION_VALOF
        case s_valof:
            return e;
#endif
    }
}

static Expr *mklet(Binder *v, TypeExpr *t, Expr *e)
{   if (h0_(e) == s_error) return errornode;
    return mk_exprlet(s_let, t, mkSynBindList(0, v), e);
}

static Expr *mkletmany(TypeExpr *t, Expr *e, ...) /* Binder *v, ..., 0 */
{   va_list ap;
    SynBindList *l = 0;
    Binder *v;
    if (h0_(e) == s_error) return errornode;
    va_start(ap, e);
    while ((v = va_arg(ap, Binder *)) != 0)
        l = mkSynBindList(l, v);
    va_end(ap);
    return mk_exprlet(s_let, t, l, e);
}

static Expr *appendlet(Expr *let, Expr *e)
{   TypeExpr* te;
    if (let == 0) return e;
    if (h0_(let) == s_error || h0_(e) == s_error) return errornode;
    if (h0_(let) != s_let) syserr("appendlet %ld", h0_(let));
    te = typeofexpr(e);
    if (arg2_(let) != 0)
    {   /* like mkbinary(s_comma, arg2_(let), e); but don't coerceunary(e) */
        Expr* a = arg2_(let);
        if (h0_(a = coerceunary(a)) == s_error) return errornode;
        a = mkcast(s_comma, a, te_void);
        if (h0_(a) == s_error) return errornode;
        e = mk_expr2(s_comma, te, a, e);
    }
    return mk_exprlet(s_let, te, exprletbind_(let), e);
}


Expr *mkunary(AEop op, Expr *a)
{   Expr *c;
    TypeExpr *t;
    if (monadneedslvalue_(op))    /* & ++ -- */
    {   c = ensurelvalue(a, op);
        c = (op == s_addrof) ? mkaddr(c) : mkincdec(op, c);
        /* add an invisible node if expression was transformed (for errors) */
        return (h0_(c) == s_error) ? errornode :
               (h0_(c) == op) ? c :
               (t = typeofexpr(c), mkinvisible(t, mk_expr1(op,t,a), c));
    }
/* The next line treats monadic + as coercing enum->int.  Check C++.    */
    if (h0_(a = coerceunary(a)) == s_error) return a;
    t = typeofexpr(a);
    /* the operators below all take rvalues in which qualifiers are ignored */
    switch (op)        /*  + - ~ ! *  */
    {   case s_content:
            if (indexable(t))
            {   t = indexee(t);
                /* kill all accesses via (qualified) void pointers. */
                if (isvoidtype(t))
                    {   cc_err(sem_rerr_void_indirection);
                        return errornode;
                    }
                break;
            }
            if (!istypevar(t)) typeclash(op);
            return errornode;
        case s_boolnot:
            a = mktest(op,a);
            if (h0_(a) == s_error) return errornode;
            t = typeofexpr(a);
            break;
     /* case s_monplus: */
     /*     ANSI have ruled that +ptr is illegal, but 0+ptr is OK! ...  */
     /*     ... to make +ptr valid add:     if (indexable(t)) break;    */
     /* case s_bitnot: */
     /* case s_neg:    */
        default:               /* (s_bitnot(~), s_neg(-), s_monplus(+) */
            t = princtype(t);
            if (h0_(t) == s_typespec && (typespecmap_(t) &
                 (op == s_bitnot ? INTEGRALTYPEBITS : ARITHTYPEBITS)))
                break;
            if (!istypevar(t)) typeclash(op);
            return errornode;
    }
    c = mk_expr1(op,t,a);
/* AM: I wonder if we should do the transformations
       +e => 0+e; -e => 0-e; !e => 0==e; ~e = (-1)^e;
   here?  This would only leave & and * as monads.
   It would certainly simplify type checking for (e.g. +x
   as it would say that int/float/pointer were ok only).
   Then cg.c could get to undo it (and catch similar cases too!).
*/
    return trymonadreduce(op,a,c,
         h0_(t)==s_typespec ? typespecmap_(t) : addrsignmap_);
}

static Expr *mkshift(AEop op, Expr *a, int32 n) /* for bitfields only!  */
{
    if (n == 0) return a;
/* @@@ The next line is a hack to avoid spurious error messages when    */
/* 1<<31 is used to mask off a bitfield, as in x.a=1.                   */
    else if (h0_(a) == s_integer && type_(a) == te_int && op==s_leftshift)
        return mkintconst(te_int, (unsigned32)(intval_(a)) << n, 0);
    else return mkbinary(op, a, mkintconst(te_int, n, 0));
}

static void I64_LSBMask(int64 *n, int32 size) {
    int64 one;
    I64_IToS(&one, 1);
    I64_Lsh(n, &one, size);
    I64_SSub(n, n, &one);
}

static Expr *OtherBitsMask(int32 size, int32 maxsize, int32 lspos) {
    if (maxsize <= MAXBITSIZE)
        return mkintconst(te_int, ~(lsbmask(size) << lspos), 0);
    else {
        int64 n;
        I64_LSBMask(&n, size);
        I64_Lsh(&n, &n, lspos);
        I64_Not(&n, &n);
        return (Expr *)mkint64const(ts_longlong, &n);
    }
}

static Expr *LSBMask(int32 size, int32 maxsize) {
    if (maxsize <= MAXBITSIZE)
        return mkintconst(te_int, lsbmask(size), 0);
    else {
        int64 n;
        I64_LSBMask(&n, size);
        return (Expr *)mkint64const(ts_longlong, &n);
    }
}

static Expr *bitfieldvalue(Expr *ebf, SET_BITMAP m, Expr *ewd)
{ /*
   * MEMO: exprbsize_ is size; exprmsboff_ is offset from msb;
   * (ebf must be s_dot of bits, ewd yields the word containing bitfield).
   * ANSI require 'int' bit fields treated as 'unsigned' or 'signed' just
   * when chars would be.  E.g. that { unsigned a:7,b:32 } gives x.a type int,
   * and x.b unsigned, whereas PCC gives both unsigned (cf. unsigned char).
   * tr is type of result.
   * (We use an explicit cast to ensure the type of the value is right,
   * rather than relying on the invisible node to hold it, lest the
   * invisible node be optimised away while the type info is still needed).
   */
    int32 size = exprbsize_(ebf);
    int32 maxsize = bf_container_bits(type_(ebf));
    TypeExpr *tr = bf_promotedtype(type_(ebf), size);
    int32 maxbitsize = int_islonglong_(m) ? sizeof_longlong*8 : sizeof_int*8;
/* AM @@@ There is work to be done (e.g. in the next line) so that we   */
/* choose signed/unsigned enum bit fields depending on set of values?   */
/* Currently enum bit fields act as plain int (i.e. may/maynot extend). */
    Expr *e;
    if (issignedchar_(m)) {
        e = mkshift(s_rightshift,
              mkshift(s_leftshift, ewd, (exprmsboff_(ebf) % maxsize) + ((sizeof_int / (maxsize/8)) - 1) * maxsize),
              maxbitsize-size);
    } else if
#ifdef TARGET_HAS_SCALED_OPS
           /* expand to a pair of shifts except when the field occupies */
           /* the low-order bits of the container (so no shift needed   */
           /* for shift+mask extraction                                 */
           (maxsize-size-(exprmsboff_(ebf) % maxsize) != 0)
#else
           /* expand to shift + mask, except when the field occupies    */
           /* the high-order bits of the container (so just a rightshift*/
           /* needed for shift+shift extraction).                       */
           (exprmsboff_(ebf) != 0 || maxsize != maxbitsize)
#endif
    {   if ((exprmsboff_(ebf) % maxsize) == 0) {
            e = mkshift(s_rightshift,
                  mkcast(s_cast, ewd, int_islonglong_(m) ? te_ullint : te_uint),
                  maxsize-size);
        } else {
            e = mkshift(s_rightshift,
                  mkcast(s_cast,
                    mkshift(s_leftshift, ewd, (exprmsboff_(ebf) % maxsize) + (maxbitsize / maxsize - 1) * maxsize),
                    int_islonglong_(m) ? te_ullint : te_uint),
                  maxbitsize-size);
        }
    } else if (size == maxsize) {
        e = ewd;
    } else {
        e = mkbinary(s_and,
              mkshift(s_rightshift, ewd, maxsize-size-(exprmsboff_(ebf) % maxsize)),
              LSBMask(size, maxsize));
    }
    return mkinvisible(tr, ebf, mkcast(s_cast, e, tr));
}

static Expr *bitfieldinsert(AEop op, Expr *ebf, Expr *ewd, Expr *val)
{   int32 size = exprbsize_(ebf);
    int32 maxsize = bf_container_bits(type_(ebf));
    int32 lspos = maxsize-size-(exprmsboff_(ebf)%maxsize);
    return
        mkassign(op,    /* not mkbinary (else x.bit = 1 gives 2 errs).  */
            ewd,
            size == maxsize ?
                val :
                mkbinary(s_or,
                   mkbinary(s_and, ewd, OtherBitsMask(size, maxsize, lspos)),
                   mkshift(s_leftshift,
                        mkbinary(s_and, val, LSBMask(size, maxsize)),
                        lspos)));
}

/* bitfieldstuff() has been so re-arranged to show its similarity to    */
/* to mkopassign (q.v.).   Rationalise the two one day.                 */
static Expr *bitfieldstuff(AEop op, Expr *a, SET_BITMAP m,
                           Expr *ewd, Expr *b)
/* special case: op==s_postinc has b = 1 or -1 according to ++ or -- */
{   /* note that 'ewd' must not have side effects as it is duplicated */
    Expr *bb = op == s_assign ? b :
            mkbinary(op == s_postinc ? s_plus : unassignop_(op),
                     bitfieldvalue(a, m, ewd),
                     b);
    return bitfieldinsert(op == s_postinc ? s_displace : s_assign,
                          a, ewd, mkcast(op, bb, int_islonglong_(m) ? te_llint : te_int));
}

static Expr *bitfieldassign(AEop op, Expr *a, TypeExpr *ta, Expr *b)
/* special case: op==s_postinc has b = 1 or -1 according to ++ or --    */
/* NB: ta == typeofexpr(a), eliminate this arg?                         */
{   Expr *bitword, *r;
    SET_BITMAP m;
/* /* BEWARE: the next line can lose top-level qualifiers.  This only   */
/* really affects volatile (const done in ensurelvalue()), but more     */
/* seriously the code to access bitfields needs review for volatile.    */
    ta = prunetype(ta);
    if (h0_(a) != s_dot || h0_(ta) != s_typespec)
    {   syserr(syserr_bitfieldassign);
        return errornode;  /* note the curious a/ta spread of info */
    }
    m = typespecmap_(ta);
    bitword = bf_container(a, m);
/* @@@ AM: the expression (x.b = 1) where x.b has bitfield type here    */
/* has promoted type of x.b, maybe it shouldn't (e.g. sizeof).          */
    if (issimplelvalue(a))
        r = bitfieldvalue(a, m, bitfieldstuff(op, a, m, bitword, b));
    else
    {   Binder *gen = gentempbinder(ptrtotype_(typeofexpr(bitword)));
        r = bitfieldvalue(a, m,
            mklet(gen, te_int,
                mkbinary(s_comma,
                    mkbinary(s_assign, (Expr *)gen, mkunary(s_addrof,bitword)),
                    bitfieldstuff(op, a, m,
                        mkunary(s_content, (Expr *)gen), b))));
    }
    if (h0_(r) == s_error) return errornode;
    /* for correct error messages and absence of warnings when assignment
       is voided.  We rely on the form of r (and hence bitfieldvalue).  */
    return mkinvisible(type_(r), mk_expr2(op, ta, a, b), r);
}


/* mkincdec, mkaddr and mkassign deal with monadic and diadic operators which
   require an lvalue operand (this is assumed already checked).  Many of these
   may turn into the pseudo-operator s_let to reduce CG complexity.
   Consider nasties like "int *f(); double *g(); *f() /= *g();"
*/

/* mkincdec and mkaddr never insert s_invisible nodes -- they leave the */
/* caller to do it -- is this right in retrospect?                      */
static Expr *mkincdec(AEop op, Expr *a)              /* op can be ++ -- */
{   TypeExpr *t = princtype(typeofexpr(a));
    if (h0_(a) == s_error) return errornode;
    if (LanguageIsCPlusPlus && isprimtype_(t, s_bool))
    {   if (incdecisinc_(op))
        {   cc_warn(sem_warn_deprecated_bool, op);
            if (incdecispre_(op))
                return mkbinary(s_comma,
                                mkassign(s_assign, a, lit_true), a);
            else
            {   Binder *gen = gentempbinder(te_boolean);
                Expr *b;
                b = mkbinary(s_comma,
                      mkbinary(s_comma,
                               mkassign(s_assign, (Expr *)gen, a),
                               mkassign(s_assign, a, lit_true)),
                             (Expr *)gen);
                return mklet(gen, te_boolean, b);
            }
        }
        else
            cc_rerr(sem_rerr_postdecr_bool, op);
    }
    {   /* type check enough here for correct error msgs or extra param */
        Expr *b = mkintconst(te_int, (incdecisinc_(op) ? 1 : -1), 0);
/* The following test avoids warnings for "u--" where u is unsigned int */
/* and where -1 should be the bit pattern 0xffff.                       */
/* @@@ Reconsider the use of "--x" ==> "x=x+(-1) in the light of this.  */
        if (sizeof_int == 2 && !incdecisinc_(op))
        {   if (h0_(t) == s_typespec)
            {   SET_BITMAP m = typespecmap_(t);
                if ((m & (bitoftype_(s_int)|bitoftype_(s_unsigned)|
                                            bitoftype_(s_long))) ==
                         (bitoftype_(s_int)|bitoftype_(s_unsigned)) ||
                    (m & (bitoftype_(s_char)|bitoftype_(s_unsigned))) ==
                         (bitoftype_(s_char)|bitoftype_(s_unsigned)) &&
                    HasFeature(Feature_PCC))
                  b = mkintconst(te_uint, 0xffff, 0);
            }
        }
        if (incdecispre_(op))   /* turn ++x to x+=1 */
            return mkassign(s_plusequal, a, b);
        else return mkassign(s_postinc, a, b);
             /* let mkassign() do it - note that it 'knows' about s_postinc */
    }
}

/* Add extra arg 'implicit' to mkaddr to unify code with coerceunary?   */
static Expr *mkaddr(Expr *a)
{   TypeExpr *t, *tp;
    if (h0_(a) == s_error) return errornode;
    t = typeofexpr(a);
    tp = princtype(t);
    /* last_seen is a botch. Seen a type store reused! */
    if (LanguageIsCPlusPlus) switch (h0_(tp))
    {
case t_coloncolon:
        {   TagBinder *cl = typespectagbind_(tp);
            ClassMember *m = (ClassMember *)a;
/* This (&A::a) is really just offsetof!                                */
/* Note, given class D:B {}, that the curious def of &D::b [ES, p55]    */
/* being &B::b is necessary because of virtual bases.                   */
/* /* We accidentally get the type of &(B::b) wrong here.  It should be */
/* as &(this->B::b) not as &B::b.                                       */
            a = mkaddr(mkfieldselector(s_arrow, nullptr(cl), m));
/* LDS - was:  attributes_(m) & CB_ANON ? realbinder_(m) : m))          */
            return h0_(a) == s_error ? errornode :
                mk_expr2_ptr(s_plus, ptrtotype_(t), a, lit_one);
        }
case t_ovld:
    /*  return mkaddr((Expr *)ovld_resolve_addr(a, typeovldlist_(tp))); */
        if (h0_(a = (Expr *)ovld_resolve_addr(a, typeovldlist_(tp))) == s_error)
            return a;
        t = typeofexpr(a);
        if (h0_(princtype(t)) == t_ovld) break;
        /* else fall through */

case t_fnap:
        if (h0_(a) == s_dot)                  /* C++ member function    */
            return mkaddr(exprdotmemfn_(a));
        if (h0_(a) == s_dotstar)        /* see [ES, p71]                */
        {   cc_err(sem_err_noncallsite_function);
            return errornode;
        }
        if (h0_(a) == s_binder && bindstg_(exb_(a)) & b_impl)
        {   Binder *b = realbinder_(exb_(a));
            if (!SuppressDB_Has(Suppress_CFrontCaller))
                cc_warn(sem_warn_addr_of_memfn, b);
            if (bindstg_(b) & b_memfna)
            {
                if (bindstg_(b) & bitofstg_(s_virtual))
                    b = generate_wrapper(exb_(a));
                t = (TypeExpr *)syn_list3(t_coloncolon, t,
                                          bindparent_(exb_(a)));
            }
/* Take address of implementation but use type of member.               */
/* Making a memfn behave like s_member in typeofexpr() would help here. */
            a = (Expr *)b;
        }
        /* drop through */
    }
/* The following line handles the big kludge whereby pcc treats &a as    */
/* &a[0].  Note that then we lie somewhat about the type as given, say,  */
/* int a[5]; f(&a); we have a node &a with type (int *) but whose son    */
/* is (int [5]).  Still this does not worry optimise, the only code to   */
/* look inside an & node.                                                */
    if (HasFeature(Feature_PCC) && h0_(tp) == t_subscript) t = typearg_(tp);

    /* The next line allows the offsetof() macro to reduce to a compile- */
    /* time constant as ANSI require.  @@@ Think a little more --        */
    /* AM would like to keep all reductions together in trydiadreduce,   */
    /* but this means that re-arrangements have to be spotted early.     */
    /* This is the classical phase-order problem recurring.              */
/* There are also ANSI-dubious things here about WHICH constant exprs.   */
/* are allowed in various contexts.   (e.g. array size, initialiser...)  */
    {   int32 n = 0;
        Expr *q, *p = a;
        for (; p != NULL && (p = skip_invisible_or_cast(p)) != NULL; p = arg1_(p))
        {   if (h0_(p) == s_dot) {
                n += exprdotoff_(p);
                if (!(h0_(arg1_(p)) == s_content &&
                     h0_(arg1_(arg1_(p))) == s_integer))
                    continue;
                p = arg1_(arg1_(p));
            } else if (h0_(p) == s_content && h0_(arg1_(p)) == s_plus &&
                       h0_(q = skip_invisible_or_cast(arg1_(arg1_(p)))) == s_integer &&
                       h0_(arg2_(arg1_(p))) == s_integer) {
                n += intval_(arg2_(arg1_(p)));
                p = q;
            } else
                break;

            return mk_expr2_ptr(s_plus, ptrtotype_(t), p,
                                        mkintconst(te_int, n, 0));
        }
    }
/* note that it has already been verified that a is an l-value if that is */
/* important.                                                             */
    return mk_expr1(s_addrof, ptrtotype_(t), a);
}

static Expr *mkopassign(AEop op, Expr *asimple, Expr *b)
{   /* asimple must have passed issimplelvalue() or be otherwise reevalable */
/* @@@ review s_postinc the light of clumsy code for sizeof_int == 2.       */
    if (op == s_postinc) {
        b = mkbinary(s_plus, asimple, b);
        if ((mcrepofexpr(asimple) & MCR_SORT_MASK) == MCR_SORT_STRUCT)
        {   TypeExpr *t = typeofexpr(asimple);
            Binder *gen = gentempbinder(t);
            b = mkbinary(s_comma,
                  mkbinary(s_comma,
                           mkassign(s_assign, (Expr *)gen, asimple),
                           mkassign(s_assign, asimple, b)),
                         (Expr *)gen);
            return mklet(gen, t, b);
        }
        return mkassign(s_displace, asimple, b);
    } else
        return mkassign(s_assign, asimple,
                        mkbinary(unassignop_(op), asimple, b));
}

static Expr *mkassign(AEop op, Expr *a, Expr *b)
                    /* for = += *= ... also s_displace and s_postinc */
{   TypeExpr *t1, *t1x;
    Expr *r;
    if (h0_(a) == s_error || h0_(b) == s_error) return errornode;
    check_index_dereference(a);
    t1 = typeofexpr(a);  /* un-coerced type */
    t1x = princtype(t1);

    if (!SuppressDB_Has(Suppress_StructAssign)
        && (mcrepoftype(t1x) & MCR_SORT_MASK) == MCR_SORT_STRUCT)
        cc_warn(sem_warn_structassign);

    if (LanguageIsCPlusPlus && istypevar(t1x))
        return mk_expr2(op, t1, a, b);

    if (LanguageIsCPlusPlus && isprimtype_(t1x, s_bool) &&
        op != s_assign && op != s_displace && op != s_init)
    {   cc_rerr(sem_rerr_opequal_bool, op);
        return errornode;
    }
/* @@@  not clear this is in the right place -- ensurelvalue/mkassign   */
    if (LanguageIsCPlusPlus && h0_(t1) == t_coloncolon)
    {   a = thisify(a);
        if (h0_(a) == s_error) return a;
        t1 = typeofexpr(a);
    }
    if (isbitfield_type(t1))
    {   TypeExpr *t2 = unbitfield_type(t1);
/* @@@ Beware: the next cast to t2 may worsen code for char bitfields,  */
/* but it is more correct than using te_int (e.g. warnings/enums).      */
/* regalloc.c now optimises char casts followed by masks.               */
/* However this doesn't happen yet (see the ONE_DAY_SOON test above).   */
        Expr *bb = mkcast(op, b, t2);
        a = skip_invisible(a);
        if (issimplevalue(b))
            return bitfieldassign(op, a, t1, bb);
        else
        {   TypeExpr *tt = bf_promotedtype(t1, exprbsize_(a));
            Binder *gen = gentempbinder(tt);  /* bf_promotedtype?    */
/* The let statement here is so that any possible side-effects in the    */
/* rhs can not cause confusion with the expansion of the bitfield        */
/* assignment into shifts and masks. Without it x.a = x.b = nn can give  */
/* trouble as the integer holding x can be loaded for the outer          */
/* assignment before it is updated by the inner one.                     */
            Expr *e = mkbinary(s_comma,
                          mkbinary(s_init, (Expr *)gen, bb),
                          bitfieldassign(op, a, t1, (Expr *)gen));
            r = mklet(gen, typeofexpr(e), e);
        }
    } else if (h0_(a) == s_cond && op == s_assign)
    { /* This can only legitimately happen in C++, but the error action  */
      /* for C faced with i ? j : k = l is to generate the same tree as  */
      /* C++ does.                                                       */
        if (h0_(b) == s_binder)
            r = mkcond(arg1_(a),
                  mkbinary(s_assign, arg2_(a), b),
                  mkbinary(s_assign, arg3_(a), b));

        else if ((mcrepofexpr(b) & MCR_SORT_MASK) == MCR_SORT_STRUCT)
            r = mkbinary(s_assign,
                mkunary(s_content,
                    mkcond(arg1_(a), mkaddr(arg2_(a)), mkaddr(arg3_(a)))), b);
        else
        /* We now expand to (let v = l in i ? j = l : k = l)             */
        /* in optimise1, since then there will be extra cases which      */
        /* don't at this stage have s_cond as top operator on the lhs    */
            r = mk_expr2(op, t1, a, b);
    }
    else if (op == s_assign || op == s_displace || op == s_init)
    {   r = 0;
/* not dead code */
        if (LanguageIsCPlusPlus && op == s_init)
        {   TypeExpr *pta = princtype(t1);
            if (isclasstype_(pta))
                r = mkopap(op, typespectagbind_(pta), a, mkExprList1(b));
        }
        if (r == 0)
        {   b = mkcast(op, b, t1);
            r = (h0_(b) == s_error) ? errornode : mk_expr2(op, t1, a, b);
        }
    }
    else if (issimplelvalue_i(a, 0))
        r = mkopassign(op, a, b);
    else if (issimplelvalue_i(a, allowpostinc))
    {   Expr *inc = NULL;
        Binder *gen = gentempbinder(t1);
        a = RemovePostincs(a, &inc);
        r = mklet(gen, t1,
            mkbinary(s_comma,
                mkbinary(s_comma,
                    mkbinary(s_init, (Expr *)gen, mkopassign(op, a, b)),
                    inc),
                (Expr *)gen));
    }
    else
    {   /* otherwise use a pointer in case side-effects - e.g. *f()+=1. */
        Binder *gen = gentempbinder(ptrtotype_(t1));
        r = mklet(gen, t1,
            mkbinary(s_comma,
                mkbinary(s_init, (Expr *)gen, mkaddr(a)),
                mkopassign(op, mkunary(s_content, (Expr *)gen), b)));
    }
    return h0_(r) == s_error ? errornode :
           h0_(r) == op ? r :
           mkinvisible(type_(r), mk_expr2(op, type_(r), a, b), r);
}

/* mkindex copes with indexing on a machine in which sizeof int and     */
/* and sizeof long differ.  Then we need a widen/narrow before index.   */
/* The last two arguments provide for (constant) index checking.        */
static Expr *mkindex(Expr *e, int32 stride, Expr *array, int posneg)
{   /* The code is marginally perverse here so that no tests are        */
    /* generated if sizeof_ptr/int/long are equal.                      */
    if (sizeof_ptr == sizeof_int || sizeof_ptr == sizeof_long
                                 || sizeof_ptr == sizeof_longlong)
    {   int32 n = sizeoftype(typeofexpr(e));
        if (sizeof_ptr == sizeof_long && n != sizeof_long)
            e = coerce2(e, te_lint);
        if (sizeof_ptr == sizeof_int && n != sizeof_int)
            e = coerce2(e, te_int);
    }
    else
        syserr(syserr_mkindex);
    check_index_overflow(array, e, posneg, NO);
    return mkbinary(s_times, e,
        mkintconst((sizeof_ptr==sizeof_int ? te_int:te_lint),stride,0));
}


Expr *mkbinary(AEop op, Expr *a, Expr *b)
{   TypeExpr *t1,*t2,*t3;
    if (op == s_init)           /* merge with diadneedslvalue below?    */
    {   Expr *c = mkassign(s_init, a, b);
/* @@@ do we need an ensurelvalue() on a above for meminit of anonu's?  */
        if (/*LanguageIsCPlusPlus &&*/
/* We *need* to do this for "const int x = 8; int A[x];" etc.           */
/* (But [ES] doesn't seem to say so.)                                   */
/* Currently just save int/float values (possibly reduced from exprs)   */
/* associated with 'const' binders.  Should we do 'int *const x = &y;'? */
            h0_(c) == s_init && arg1_(c) == a && h0_(a) == s_binder)
                                  /* and not b_member?                  */
        {   Expr *bb = skip_invisible(arg2_(c));
            TypeExpr *t = bindtype_(exb_(a));
            if ((h0_(bb) == s_integer || h0_(bb) == s_floatcon) &&
                (qualifiersoftype(t) & bitoftype_(s_const) || istypevar(t)))
            {   Expr *gb = globalize_expr(bb);      /* @@@ over-sloppy! */
/* @@@ Binder's should have a bit to tell us local/global?              */
                bindconst_(exb_(a)) = gb;
                if (debugging(DEBUG_SYN)) cc_msg("const $b = $e\n", a, gb);
            }
        }
        return c;
    }
    if (diadneedslvalue_(op))
    {   Expr *c = mkassign(op, ensurelvalue(a,op), b);
        /* add an invisible node if expression was transformed (for errors) */
        return (h0_(c) == s_error) ? errornode :
               (h0_(c) == op) ? c : (t1 = typeofexpr(c),
                       mkinvisible(t1, mk_expr2(op,t1,a,b), c));
    }
    if (h0_(a = coerceunary(a)) == s_error) return a;
    if (h0_(b = coerceunary_2(b, op==s_comma ? COERCE_COMMA : COERCE_NORMAL))
                                == s_error) return b;
    /* the next line checks and inserts !=0 in && ||.                 */
    if (isboolean_(op))
    {   a = mktest(op,a);
        b = mktest(op,b);
        if (h0_(a) == s_error || h0_(b) == s_error) return errornode;
    }
    t1 = typeofexpr(a);
    t2 = typeofexpr(b);
    switch (op)
    /* special case type rules...  generalise to table like lexclass? */
    {   case s_comma:
            a = mkcast(s_comma, a, te_void);
            if (h0_(a) == s_error) return errornode;
            /* note: ANSI forbids reduction of ',' operators */
            return mk_expr2(op, t2, a, b);
        case s_subscript:
            if ((indexable(t1) && indexer(t2)) ||
                (indexable(t2) && indexer(t1)))
                /* note that mkbinary() may permute (a,b)               */

                return mkunary(s_content, mkbinary(s_plus, a, b));

            /* drop through */
            typeclash(op);
            return errornode;
        case s_arrowstar:
            /* map x->*e to (*x).*e, i.e. fixup a,t1 and drop through.  */
            if (!indexable(t1)) goto clash;
            t1 = indexee(t1);
            a = mk_expr1(s_content, t1, a);
            /* drop through */
        case s_dotstar:
/* Here f().*e gives the same complications as in f().mem -- we want    */
/* to select a field from a class which does not have an lvalue.        */
/* Moreover, we don't wish to disturb the parse tree too much while     */
/* we might still give errors.  Hence leave s_dotstar for optimise()    */
/* to remove since optimise() now ensures that such structs do get an   */
/* l-value (beware 1-word ones!).  Note that nowadays optimise should   */
/* also transform s_dot to s_content too!  Finally, we have to remember */
/* to check the use of s_dotstar on a 1-word structure in simplify.c.   */
/* @@@ beware this code is (obviously) very similar to findfield UNIFY! */
            {   TypeExpr *t1c = princtype(t1), *t2e = princtype(t2);
                SET_BITMAP q = qualifiersoftype(t1);
                if (!(isclasstype_(t1c) && h0_(t2e) == t_content)) goto clash;
                t2e = typearg_(t2e);
/* Do we need prunetype(t2e) here?  Can one "typedef A::p, A::*q?;"     */
                if (h0_(t2e) != t_coloncolon) goto clash;
                if (typespectagbind_(t2e) != typespectagbind_(t1c))
                {   if (derived_from(typespectagbind_(t2e),
                                     typespectagbind_(t1c)))
                    {   t1c = tagbindtype_(typespectagbind_(t2e));
                        a = mkcast(s_cast, a, t1c);
                    } else if (istypevar(tagbindtype_(typespectagbind_(t2e))) ||
                               istypevar(tagbindtype_(typespectagbind_(t1c))))
                        return errornode;
                }
                if (typespectagbind_(t2e) == typespectagbind_(t1c))
                {   TypeExpr *tr = mkqualifiedtype(typearg_(t2e), q);
/* If second arg is a constant we should diadreduce to s_dot??          */
                    return mk_expr2(s_dotstar, tr, a, b);
                }
            }
clash:      typeclash(op);
            return errornode;
        case s_plus:
            if (indexable(t1) && indexer(t2))
                return mk_expr2_ptr(op, t1, a,
                             mkindex(b, strideofindexee(t1), a, 1));
            if (indexable(t2) && indexer(t1))
#ifdef OLD_POINTER_PLUS
                return mk_expr2_ptr(op, t2,
                             mkindex(a, strideofindexee(t2), b, 1),
                             b);
#else
/* int+ptr is now treated as ptr+int, hence i[p], p[i] as *(p+i).      */
                return mk_expr2_ptr(op, t2, b,
                             mkindex(a, strideofindexee(t2), b, 1));
#endif
            break;
        case s_minus:
            if (indexable(t1) && indexer(t2))
                return mk_expr2_ptr(op, t1, a,
                             mkindex(b, strideofindexee(t1), a, -1));
            if (indexable(t1) && indexable(t2))
            {   /* Ignore top-level qualifiers as vals are rvalues.     */
                /* Also ignore (by unioning) qualifiers on pointed-to   */
                /* types.  Use compositetype() to establish stride.     */
/* @@@ ANSI is ambiguous on f(int (*a)[], int (*b)[3]) { return a-b; }  */
                TypeExpr *t3 = qualunion_compositetype(indexee(t1),
                                                       indexee(t2));
                if (t3)
                {   /* The following line is the only use of s_ptrdiff   */
                    /* which is only serves to stop check_narrow_subterm */
                    /* from issuing spurious warnings on                 */
                    /*         long x = offsetof(..)                     */
                    Expr *actual = mk_expr2(s_ptrdiff, te_int, a, b);
                    Expr *r = mk_expr2_ptr(op, te_int, a, b);
                    int32 sizeof_t3 = sizeoftype(t3);
                    /* the following helps the offsetof() macro used in */
                    /* static initialisers...                           */
                    if (sizeof_t3 != 1)
                        r = mkbinary(s_div, r,
                                    mkintconst(te_int, sizeof_t3, 0));
                    if (sizeof_ptr != sizeof_int &&
                        sizeof_ptr != sizeof_longlong)
                        /* Fix this more seriously one day?             */
                        /* If so then review te_int in term for 'r'.    */
                        syserr(syserr_ptrdiff);
                    if (h0_(r) == s_error) return errornode;
                    /* The invisible node is for correct error msgs */
                    return mkinvisible(te_int, actual, r);
                }
            }
            break;
        default:
            if (isrelational_(op))
            {   /* unify code with mkcond()... */
                if (indexable(t1) && indexable(t2))
                {   /* ignore top-level qualifiers as vals are rvalues  */
                    TypeExpr *t1a = indexee(t1), *t2a = indexee(t2);
/* Now ignore qualifiers on pointed-to types, but see                   */
/* qualfree_equivtype() for a warning.                                  */
                    if (!qualfree_equivtype(t1a,t2a))
                    {   /* looks like a type error, but first check for */
                        /* C++ pointers to derived types                */
                        TypeExpr* unused;
                        if (!LanguageIsCPlusPlus ||
                            !common_pointer_type(op, t1, a, &a,
                                                     t2, b, &b, &unused))
                        /* then if equality op and one arg is (void *)  */
/* Note that (void *) types are tricky -- the null pointer constant     */
/* (void *)0 is comparable with a fn, but no other (void *)values are.  */
                        {   if (!((op == s_equalequal || op == s_notequal) &&
                                  (isvoidtype(t1a) &&
                                   (!isfntype(t2a) || isnullptrconst(a))) ||
                                  (isvoidtype(t2a) &&
                                   (!isfntype(t1a) || isnullptrconst(b)))))
                              cc_pccwarn(sem_rerr_different_pointers, op);
                        }
                    }
                    return mk_expr2_ptr(op, te_boolean, a, b);
                }
/* The following lines handle the case NULL == 0 (of integral type).    */
                if (indexable(t1) && indexer(t2))
                    return mk_expr2_ptr(op, te_boolean, a, pointerofint(b,op,t1));
                if (indexable(t2) && indexer(t1))
                    return mk_expr2_ptr(op, te_boolean, pointerofint(a,op,t2), b);
                if (!isinequality_(op) && isptrtomember(t1) && indexer(t2))
                    return mk_expr2_ptr(op, t1, a, pointerofint(b,op,t1));
                if (!isinequality_(op) && isptrtomember(t2) && indexer(t1))
                    return mk_expr2_ptr(op, t2, pointerofint(a,op,t1), b);
            }
            break;
    }
    /* all that SHOULD be left are the arithmetic types */
    t3 = lubtype(op,t1,t2);           /* BEWARE - see trydiadreduce below */
    if (t3 == 0) return errornode;
    if (op == s_leftshift || op == s_rightshift) {   /* done by lubtype() */
        t2 = princtype(t2);
        if (int_islonglong_(typespecmap_(t2)))
            b = mkcast(s_leftshift, b, te_uint);
    }
    else a = coerce2(a, t3), b = coerce2(b, t3);
    {
        Expr *c = mk_expr2(op, ((isrelational_(op) || isboolean_(op)) ?
                                                       te_boolean : t3), a, b);
        /* the next line relies on the form of result of lubtype() (q.v.) */
        return trydiadreduce(c, typespecmap_(t3));
    }
}

static int is_unrooted(Expr *e)
{   if (e == 0)
        return 1;
    else
    {   Binder *b = exb_(e);
        if (h0_(b) == s_binder && bindsym_(b) == 0)
            /* nullbinder(cl)... */
            return 1;
        if (h0_(e) != s_dot)
            return 0;
    }
    return is_unrooted(arg1_(e));
}

Expr *mkfnap(Expr *e, ExprList *l)
{   TypeExpr *t;
    FormTypeList *d;
    bool curried = NO;
    Binder *fnb = NULL;
    Expr *let = NULL;
    Expr *firstarg = NULL;
    TypeExpr *tt;
    ScopeSaver tactuals = NULL;
    bool hasimplicitthis = NO;

    if (h0_(e) == s_error) return errornode;
    if (LanguageIsCPlusPlus)
    {   TagBinder *cl = current_member_scope();
        Expr *ee;
        ExprList *const origl = l;
        e = mkfnap_cpp(e, &l, &curried, &let, &firstarg);
        hasimplicitthis = origl != l;
        ee = skip_invisible(e);
        if (cl != NULL && tagactuals_(cl) != NULL &&
            (h0_(ee) == s_binder && !is_local_binder(exb_(ee))) &&
            !call_dependency_type(princtype(typeofexpr(ee)), tagactuals_(cl)))
            tactuals = tagactuals_(cl);
    }

    if (h0_(e) == s_binder) fnb = exb_(e);
    if (h0_(e = coerceunary(e)) == s_error) return e;
    t = typeofexpr(e);
    if (LanguageIsCPlusPlus &&
        curried && h0_(t = princtype(t)) == t_content
                && h0_(tt = princtype(typearg_(t))) == t_coloncolon
                && h0_(t = princtype(typearg_(tt))) == t_fnap)
        d = mkFormTypeList(typefnargs_(t), 0,
/* /* qualifiers? */
                ptrtotype_(tagbindtype_(typespectagbind_(tt))), 0);
    else if (!curried && indexable(t) &&
             (t = princtype(indexee(t)), h0_(t) == t_fnap))
        d = typefnargs_(t);
    else
    {   TagBinder *cl = current_member_scope();
        if (!istypevar(t) && (!cl || !(tagbindbits_(cl) & TB_TEMPLATE)))
          cc_err(sem_err_nonfunction);
        return errornode;
    }

/* Here we know: e is a (possibly instance of generic) function         */
/* 'l' is the arg list (possibly adorned with 'this'), 'd' is the       */
/* formal list (similarly adorned).  'curried' is a hack for C++ '->*'  */
/* and 't' is the t_fnap type of 'e' (used for TypeFnAux).              */
  { /* Beware: this routine side-effects the structure of 'l'.          */
    /* @@@ This routine should also add default args.                   */
    ExprList *ll, *lq = NULL;
    int argindex = hasimplicitthis ? 0 : 1;
    push_fnap_context(fnb);
    for (ll = l; ll != NULL; argindex++, lq = ll, ll = cdr_(ll))
    {   Expr *elt = exprcar_(ll);
        TypeExpr *formtype = NULL;
        /* avoid other error messages due to wrong no of args. */
        if (h0_(elt) == s_error)
        {   pop_fnap_context();
            return errornode;   /* e.g. syntax error */
        }
        set_fnap_arg(argindex);
        /* For functions with narrow parameters (float, short, char), we normally
         * widen the corresponging actual arguments before passing, and narrow in
         * the called function (callee-narrowing). This is to some extent a space
         * against time tradeoff, but it also has the effect of
         *  - allowing a function with narrow parameters to be called in the scope
         *    of a declaration without prototype, or no declaration. (of course,
         *    only if the corresponding arguments promote to the right type).
         *  - making f(x) float x; {} function correctly when called in the scope
         *    of a prototypr f(float x), even though the types aren't compatible.
         *    (for which reason we merely warn of this incompatibility except in
         *     strict ANSI conformance mode).
         * This behaviour is altered if CONFIG_UNWIDENED_NARROW_ARGS is set, in
         * which case arguments corresponding to narrow parameters are expected
         * to have been narrowed by the caller (and the warning above becomes an
         * error always).
         */
        if (d != NULL)  /* type of arg visible: prototype or previous K&R defn.  */
        {   if (!typefnaux_(t).oldstyle)
            {   /* prototype parameter */
                Expr *x = elt, *originalx = elt;
                TypeExpr *fttype = d->fttype, *t2 = princtype(fttype);
#ifdef PASCAL
                if ( h0_(fttype) != s_content ||
                     !is_conformant(typearg_(fttype))) {
                    if (h0_(fttype->pun.type) == s_var)
                        x = mkunary(s_addrof, x);
                    if (h0_(fttype->pun.type) == s_addrof) {
                        Binder *b;

                        block_binders = syn_list2(block_binders,
                            b = inst_decl(gensymval(1), typearg_(fttype),
                                                            bitofstg_(s_auto), 0));
                        x = mkbinary(s_comma,
                                mk_pas_assign(s_assign, (Expr *)b, x),
                                mkunary(s_addrof, (Expr *)b));
                    }
                }
#endif
                if (!(config & CONFIG_UNWIDENED_NARROW_ARGS)
                    && h0_(t2) == s_typespec && is_float_(typespecmap_(t2))) {
                    /* This code is to avoid a spurious warning when     */
                    /* (float)+(float) is passed to a function with a    */
                    /* prototype 'float' parameter with callee-narrowing */
                        TypeExpr *t1 = princtype(typeofexpr(x));
                        if (h0_(t1) == s_typespec  &&  is_float_(typespecmap_(t1)))
                             x = mkcast(s_cast, x, te_float);
                    }
                x = mkcast(s_fnap, x, widen_formaltype(fttype));

                if (tactuals != NULL &&
                    !call_dependency_type(typeofexpr(x), tactuals) &&
                    !call_dependency_val(originalx, tactuals))
                {   cc_err(sem_err_call_dependency, e, current_member_scope());
                    pop_fnap_context();
                    return errornode;
                }
/*                x = mkcast(s_fnap, coerceunary_2(x, COERCE_ASSIGN),    */
/*                    widen_formaltype(fttype));                         */
                if (h0_(x) != s_error)
                {   TypeExpr *t1 = princtype(typeofexpr(x));
                    if (isclasstype_(t1))
                    {   TagBinder *cla = typespectagbind_(t1);
/* class types which require construction are passed by reference and    */
/* copy-constructed in the callee (see syn.c::rd_fndef()).               */
                        if (TB_NOTPODU_(cla, TB_NEEDSCCTOR)) x = mkaddr(x);
                    }
                    exprcar_(ll) = x;
                }
                d = cdr_(d);
                continue;
            }
            else /* K&R style defn in scope: check if requested below.   */
                formtype = d->fttype, d = cdr_(d);
        } else if (h0_(tt = princtype(typeofexpr(elt))) == t_content &&
                   h0_(tt = typearg_(tt)) == t_ovld)
            /* The following line does a couple of things: it forces a
               diagnostic (no fn type can be te_void), and does a recoverery
               by forcing a choice of an overloaded instance.
             */
            elt = mkaddr((Expr *)ovld_resolve_addr_2(s_fnap, te_void,
                       typeovldlist_(tt), exb_(elt)));


        /* unchecked parameter or K&R (olde) style fn defn in scope.     */
        if (isvoidtype(typeofexpr(elt)))  /* includes "const void" etc.  */
        {   cc_err(sem_err_void_argument);
            pop_fnap_context();
            return errornode;
        }
        /* unchecked or olde-style paramaters get a special coercion,    */
        /* which includes converting float to double.                    */
        if (h0_(elt = coerceunary_2(elt, COERCE_ARG)) == s_error)
        {   pop_fnap_context();
            return elt;
        }
        exprcar_(ll) = elt;
        if (formtype != NULL &&
            !(HasFeature(Feature_PCC) && !HasFeature(Feature_Fussy)) &&
            !qualfree_equivtype(promoted_formaltype(formtype),
                                typeofexpr(elt)))
                cc_warn(sem_warn_olde_mismatch, e);
/* if TARGET_NULL_BITPATTERN != 0 and actual is (int)0 then warn if ...  */
/* ... Feature_Predeclare or some such.                                  */
    }
    if (LanguageIsCPlusPlus)
    {   if (lq != NULL)
            cdr_(lq) = exprlist_of_default_args(d, argindex);
        else
            l = exprlist_of_default_args(d, argindex);
    }
    { int32 len = length(l) - curried;
    /* we have to discount the addition to 'l' if curried (only).        */
    /* perhaps all non-static memfns should be seen as curried?          */
      if (debugging(DEBUG_TYPE))
        cc_msg("fn $e(%ld..%ld) gets %ld args\n", e,
            (long)minargs_(t), (long)maxargs_(t), (long)len);
      if (!(minargs_(t) <= len && len <= maxargs_(t)))
      {
        if (typefnaux_(t).oldstyle)
        {   if (!(HasFeature(Feature_PCC) && !HasFeature(Feature_Fussy)))
                cc_warn(sem_rerr_wrong_no_args, e);
        }
        else
            cc_rerr(sem_rerr_wrong_no_args, e);
      }
    }
    if (!curried && fntypeisvariadic(t) && typefnaux_(t).variad > 0)
        /* ho-hum, lets see if there's an illegal printf/scanf! */
        e = formatcheck(e, l, typefnargs_(t), typefnaux_(t).variad);
    e = mk_expr2(s_fnap, typearg_(t), e, (Expr *)l);
    pop_fnap_context();
  }
    e = appendlet(let, e);

    /* The rationale for the following line (relevance to C++ only)
       In e.f(), e has to be evaluated. If f is a static member,
       e will not be in the args list and has to be explicitly
       captured in a s_comma node such that e.f() ==> (e,f()).
       It used to be e.f() => (e,f)() but that prevents static
       inlining from happening.
    */

    return (firstarg) ? mkbinary(s_comma,
                                 /* cast to void to avoid no side-effect warning    */
                                 mkcast(s_cast|s_qualified, firstarg, te_void), e) : e;
}

static Expr *pointercast(AEop op, Expr *e, TypeExpr *te, TypeExpr *tr)
{   int err;
/* Here we have a cast from pointer-to-te to a pointer-to-tr.           */
/* Moan while doing so for unsuitable implicit casts.                   */
/* The Oct 88 draft clarifies that void pointers ARE required           */
/* to respect const/volatile qualification too.                         */
    if (op == s_cast)
        err = 0;
    else
    {   SET_BITMAP q = qualifiers_lost(te, tr);
        int errq = (q == 0) ? 0 : 1;
        if (qualfree_equivtype(te, tr) || isvoidtype(tr))
        {   if (q == bitoftype_(s_unaligned) && isprimtype_(tr, s_char))
              err = 0;
            else
              err = errq;
        } else if (!HasFeature(Feature_PCC) && isvoidtype(te))
        {   /* illegal in C++, so (later optionally) warn in ANSI C.    */
#ifndef FOR_ACORN
            if (!errq) cc_ansi_warn(sem_warn_narrow_voidstar);
#endif
            err = errq;
        }
        else if (istypevar(te) || istypevar(tr))
            err = 0;
        else
            err = errq | 2;
        if (err && !SuppressDB_Has(Suppress_ImplicitCast))
        {   if (err & 2)
                cc_pccwarn(sem_rerr_implicit_cast1, op);
            else if (LanguageIsCPlusPlus &&
                     q == bitoftype_(s_const) &&
                     h0_(e) == s_invisible && isstring_(h0_(orig_(e))))
                cc_warn(sem_warn_depr_string, op);
            else
                cc_pccwarn(sem_rerr_implicit_cast5, op, q);
        }
    }
    return e;
}

static void check_narrowing_cast(AEop op, SET_BITMAP from, SET_BITMAP to)
{   if (op == s_cast); /* all OK */
    else if (to & bitoftype_(s_enum))
    {   /* A cast from a type to itself cannot come here, so this is   */
        /* implicit cast from arith type to a different enum type.     */
        cc_rerr_cwarn(sem_rerr_casttoenum, op, from);
    }
    else
      if (/* moan at long int -> int/char */
          ((to & (bitoftype_(s_long)|bitoftype_(s_int)))
               == bitoftype_(s_int) ||
           (to & bitoftype_(s_char)) != 0) &&
             (from & (bitoftype_(s_long)|bitoftype_(s_int)))
                == (bitoftype_(s_long)|bitoftype_(s_int))
         ||
          /* any floating type to any shorter floating type */
          (to & bitoftype_(s_double)) &&
            (from & bitoftype_(s_double)) &&
            (to & ~from & bitoftype_(s_short) ||
             from & ~to & bitoftype_(s_long))
         ||
          /* any floating type to any integral type */
          (to & INTEGRALTYPEBITS &&
            (from & bitoftype_(s_double)))
          /* any other ideas at what to moan at? */
         )
    {   if (SuppressDB_Has(Suppress_ImplicitNarrowing)) xwarncount++;
        else cc_warn(sem_warn_narrowing, op);
    }
}

/* tidy up relationship with coerce2() */
Expr *mkcast(AEop op, Expr *e, TypeExpr *tr)
{   TypeExpr *te, *x, *y, *xp, *yp;
    Expr *r;
    SET_BITMAP m;
    bool no_redundant = (op != s_cast);  /* note s_cast|s_qualified */

    if (h0_(e) == s_error) return errornode;

    op &= ~s_qualified;
    if (LanguageIsCPlusPlus && (r = cpp_mkcast(op, &e, tr)) != NULL)
        return r;

    e = isvoidtype(tr) ? coerceunary_2(e, COERCE_VOIDED) :
        (op == s_cast) ? coerceunary(e) :
        /* coerce most things but not enum->int.                    */
                         coerceunary_2(e, COERCE_ASSIGN);
    if (h0_(e) == s_error) return e;
    te = typeofexpr(e);
    /* check te,tr match enough ... */
    switch (qualfree_equivtype(te,tr))
    {
case 2: if (no_redundant)
            /* if no_redundant and te and tr are IDENTICAL types
               we needn't store the cast.
            */
            return e;
        if (HasFeature(Feature_TellPtrInt))
            cc_warn(sem_warn_cast_sametype);
        /* drop through */
case 1: /* permissible cast */
        break;
case 0: /* not obviously permissible, check more */
        x = princtype(tr), y = princtype(te);   /* lose quals as rvalues */

        /* If one of them is an unknown type, just turn it into an
           error but without reporting as such.
         */
        if (h0_(x) == t_unknown || h0_(y) == t_unknown)
            return errornode;

#ifdef TARGET_IS_ARM_OR_THUMB          /* /* LDS: for now, until policy is agreed */
        if (op != s_cast || HasFeature(Feature_Anomoly))
#endif
            (void)check_narrow_subterm(e, y, x);
        switch (h0_(x))
        {
    case t_content:                                 /* cast to pointer. */
            if (isnullptrconst(e));                        /* always ok */
            else if (xp = princtype(x = typearg_(x)),
                     h0_(y) == t_content || h0_(xp) == t_fnap)
            {   /* cast from ptr type or any cast to fn ptr...          */
/* AM finds the dataflow hard to follow here...                         */
                if (h0_(y) == t_content)
                    yp = princtype(y = typearg_(y));
                else
                    yp = y;
                if ((h0_(xp) == t_fnap) != (h0_(yp) == t_fnap))
                {   if (op != s_cast)
                    {   if (SuppressDB_Has(Suppress_Cast))
                            cc_warn(sem_warn_fn_cast, op);
                        else
                            cc_pccwarn(sem_warn_fn_cast, op);
                    }
                    else if (!( (HasFeature(Feature_PCC) || HasFeature(Feature_LimitedPCC)) ||
                                   SuppressDB_Has(Suppress_ImplicitCast)))
                        cc_warn(sem_warn_fn_cast, op);
/* AM: the following reflects a bug (fix) in the interface aetree->cg.     */
/* There is danger here if a local static array, or address of a local var */
/* is being cast to a fn ptr type - the Expr tree will contain a structure */
/* like (addrof (binder name)) or (binder name) with type t_subscript ...  */
/* which cg.c will interpret as a literal name of a function, fatally...   */
/* (Indeed such a thing MUST NOT become external for fear of name clashes) */
/* To fool cg.c into generating a J_CALLR with an appropriate expression,  */
/* we turn such structures into (plus (addrof (binder name)) 0). The + 0   */
/* gets optimised out, so this costs nothing in the generated code.        */
/* N.B. Doing this so calls to extern arrays still get done via  J_CALLK   */
/* is tricky... it's not clear that it's worth it...                       */
/*/* would this be better inside an invisible node?                     */
/* the s_plus is visible when you do                                    */
/*'typedef void (*FP)(); int a[]; void f() { (FP)a; }' */
                    if (h0_(xp) == t_fnap &&
                        (h0_(e) == s_cast || h0_(princtype(te)) == t_content))
                    {   /* possible cast of dangerous expr to fn type... */
                        /* ...unless straight cast to extern array...    */
                        if (h0_(e) != s_invisible ||
                            h0_(r = arg1_(e)) != s_binder ||
                            !(bindstg_(exb_(r)) & bitoftype_(s_extern)))
                            e = mk_expr2(s_plus, te, e, globalize_int(0));
                    }
                }
                else
                {   /* e has type pointer-to-y and tr is pointer-to-x.  */
                    if (LanguageIsCPlusPlus)
                        e = cpp_ptrcast(op,e,y,x,t_content);
                    else
                        e = pointercast(op,e,y,x);
                }
            }
#ifdef TARGET_IS_ALPHA
/* These TARGET_IS_ALPHA parts are temporary; (a) while porting         */
/* to 64-bit hosting and (b) until we decide what we really want.       */
            else if (isprimtypein_(y,bitoftype_(s_int)))
                     /* bool and char (should have) been widened here.  */
                     /* check this is so >>> s_bool <<<                 */
            {   SET_BITMAP m = typespecmap_(y);
/* The next line is probably a noop if sizeof_int==sizeof_ptr, but     */
/* is overkeen on the alpha (e.g. faults (int *)1;)                    */
                if (sizeof_ptr > int_decodelength_(m))
                    cc_rerr("cast to pointer from too-small $m", m); /* PTRINT */
                else if (op != s_cast)
                {   if (!(suppress & D_IMPLICITCAST))
                        cc_pccwarn(sem_rerr_implicit_cast2, op);
                }
            }
#else /* TARGET_IS_ALPHA */
            else if (isprimtypein_(y,bitoftype_(s_int)|bitoftype_(s_bool)))
            {   if (op != s_cast)
                {   if (!SuppressDB_Has(Suppress_ImplicitCast))
                        cc_pccwarn(sem_rerr_implicit_cast2, op);
                }
            }
#endif /* TARGET_IS_ALPHA */
            else
            {   if (!SuppressDB_Has(Suppress_Cast)) {
                  cc_err(sem_err_bad_cast, op, y);
                  return errornode;
                }
                cc_warn(sem_err_bad_cast, op, y);
            }
            break;
    case s_typespec:
            m = typespecmap_(x);
            switch (m & -m)    /* LSB - unsigned/long etc. are higher */
            {   case bitoftype_(s_bool):
                    if (!isprimtype_(y, s_bool))
                    {   if ((h0_(e) != s_integer ||
                             (intval_(e) != 0 && intval_(e) != 1)))
                            cc_warn(sem_warn_unusual_bool, op);
                        e = mktest(op, e);
                    }
                    break;
                case bitoftype_(s_int):
#ifdef TARGET_IS_ALPHA
                    if (h0_(y) == t_content)
                    {   /* cast ptr->int: check enough bits.            */
                        if (sizeof_ptr > int_decodelength_(m))
                            cc_rerr("cast from pointer to too-small $m", m);
                        else if (op == s_cast)
#else /* TARGET_IS_ALPHA */
                    if (h0_(y) == t_content && !int_isshort_(m))
                    {   /* the only valid coercion from pointer */
                        if (op == s_cast)
#endif /* TARGET_IS_ALPHA */
                        { if (HasFeature(Feature_TellPtrInt))
                            /* police pointer purity */
                            cc_warn(sem_warn_pointer_int);
                        }
                        else
                        {   if (!SuppressDB_Has(Suppress_ImplicitCast))
                                cc_pccwarn(sem_rerr_implicit_cast3, op);
                        }
                        break;
                    }
/* For some odd reason 'case 3.4:' is a constraint violation in ANSI C  */
/* but seems valid in C++ (but it will give a warning for implicit      */
/* cast to the (INTEGRAL) type of the controlling switch.               */
                    if ((op == s_switch || op == s_subscript ||
                          (op == s_case && !LanguageIsCPlusPlus)) &&
                        isprimtype_(y,s_double))
                    {   cc_pccwarn(sem_rerr_implicit_cast4,op,y);
                        break;
                    }
                    /* drop through */
                case bitoftype_(s_char):
                case bitoftype_(s_enum):
                case bitoftype_(s_double):
                    if (h0_(y) != s_typespec ||
                        !(typespecmap_(y) & ARITHTYPEBITS))
                    {
/* This recovery is by and large OK for all Codemist back-ends.           */
/* /* @@@ AM However, it currently kills (syserr()) cg.c if just one of   */
/* x and y is an integer-like struct.  Fix.                               */
/* Also consider making a fn out of the following to remove               */
/* near duplication of code in the next case, but only if the text of     */
/* the ...cast1 and ...cast2 messages can be unified.                     */
/* @@@ relaxation guarded by Feature_PCC until cg.c can stop syserr()ing. */
                        if (HasFeature(Feature_PCC) &&
                            sizeoftype(x) == sizeoftype(y) &&
                            alignoftype(x) <= alignoftype(y))
                        {   /* same size, dest no more aligned than src */
                            cc_pccwarn(sem_err_bad_cast1, op, x);
                            break;
                        } else
                        {   if (!SuppressDB_Has(Suppress_Cast)) {
                              cc_err(sem_err_bad_cast1, op, x);
                              return errornode;
                            }
                            cc_warn(sem_err_bad_cast1, op, x);
                        }
                    }
                    check_narrowing_cast(op, typespecmap_(y), typespecmap_(x));
                    break;
                case bitoftype_(s_struct):
                case bitoftype_(s_class):
                case bitoftype_(s_union):
/* @@@ relaxation guarded by Feature_PCC until cg.c can stop syserr()ing. */
                    if (HasFeature(Feature_PCC) &&
                        sizeoftype(x) == sizeoftype(y) &&
                        alignoftype(x) <= alignoftype(y))
                        /* same size, dest no more aligned than src */
                        cc_pccwarn(sem_err_bad_cast2, op, x);
                    else
                    {   cc_err(sem_err_bad_cast2, op, x);
                        return errornode;
                    }
                    break;
                case bitoftype_(s_void):
                    /* Warn for casts unless explicit or already voided */
                    /* Macro:s like getc() or pop() in void context     */
                    /* need explicit casts to suppress warnings.        */
                    if (op != s_cast && !isprimtype_(y,s_void))
                        e = mkvoided(e);
                    break;
                default:
                    syserr(syserr_mkcast,
                           (long)h0_(x), (long)typespecmap_(x));
                    return errornode;
            }
            break;
    default:
            syserr(syserr_mkcast1, (long)h0_(x));
            return errornode;
    case t_fnap:
    case t_subscript:
            cc_err(sem_err_bad_cast1, op, x);
            return errornode;    /* improve */
        }
    }
    r = mk_expr1(s_cast, tr, e);
    r = trycastreduce(e, tr, r, op==s_cast);
    return castfn(r);
}

static Expr *findfield(AEop op, TypeExpr *te, ClassMember *member)
{   Expr *path;
    TagBinder *b;
    TypeExpr *t = princtype(te);
    if (!isclasstype_(t))
    {   if (!istypevar(t))
            cc_err(sem_err_illegal_loperand, op);
        return errornode;
    }
    b = typespectagbind_(t);
    if (!(tagbindbits_(b) & TB_DEFD))
    {   cc_err(sem_err_undef_struct, b);
        return errornode;
    }
#if 0
    /* get rid of path_t0_member handling memfn call */
    if (h0_(member) == s_binder && isfntype(bindtype_(member)))
    {   if (bindstg_(member) & b_memfna)
            path = mk_exprwdot(s_dot, bindtype_(member),
                               (Expr *)mk_binder(0, u_referenced, t), (IPtr)member);
        else
            path = (Expr *)member;
    }
    else
#endif
        path = path_to_member(member, b, INDERIVATION);
    if (path == NULL)
    {   /* failed to find a real data member... */
        cc_err(sem_err_unknown_field, b,
               h0_(member) == s_identifier ? (Symstr *)member:memsv_(member));
        path = errornode;
    }
    return path;
}

static Expr *mkdotable(AEop op, Expr *e)
{   TypeExpr *te;
/* The next line effectively a no-op for C but C++ can coerce values    */
/* of type (struct x &) implicitly to type (struct x).                  */
/* It needs to be done for case s_arrow anyway (e.g. array->foo).       */
    if (h0_(e = coerceunary(e)) == s_error) return e;
    te = princtype(typeofexpr(e));
    if (op == s_arrow)
    {   /* treat x->a as (*x).a. */
        if (indexable(te))
            return mk_expr1(s_content, indexee(te), e);
    }
    else if ((op == s_dot || op == s_qualdot) && isclasstype_(te))
        return e;
    if (!istypevar(te)) typeclash(op);
    return errornode;
}

Expr *rooted_path(Expr *path, SET_BITMAP qualifiers, Expr *root)
{   Expr *e = path;
    TypeExpr *rt = typeofexpr(root);
    for (e = path;
            (h0_(e) == s_dot || h0_(e) == s_qualdot || h0_(e) == s_content);
                e = arg1_(e))
    {   Binder *b = exb_(arg1_(e));
        if (b == NULL || qualfree_equivtype(typeofexpr(arg1_(e)), rt) ||
            h0_(b) == s_binder && bindsym_(b) == 0)
        {   /* unrooted or rooted in a class nullbinder()... */
/* the case for qualfree_equivtype, considers struct B {T m;}; struct D : B {};
   T B::*x = &D::m;
   also the following adjustment is required, considers struct Z : D {}; Z z; z.*x;
 */
            if (b != NULL && isclasstype_(bindtype_(b)) && isclasstype_(rt)
                && (b = (ClassMember *) derived_from(typespectagbind_(bindtype_(b)),
                                typespectagbind_(rt))) != 0)
                root = mkfieldselector(s_dot, root, b);
            /* @@@ rely upon interchangeable layout of core of C and C here */
            arg1_(e) = root;
            if (h0_(type_(path)) == t_coloncolon)
                type_(path) = typearg_(type_(path));
            if (qualifiers != 0)
                type_(e) = mkqualifiedtype(type_(e), qualifiers);
            break;
        }
    }
    return path;
}

Expr *mkfieldselector(AEop op, Expr *e, ClassMember *mem)
{   TypeExpr *te;
    Expr *path;
    e = mkdotable(op, e);
    if (h0_(e) == s_error) return errornode;
    te = typeofexpr(e);
    if (h0_(mem) == s_identifier ||
        h0_(mem) == s_binder || h0_(mem) == s_member)
            path = findfield(op, te, mem);
    else
        path = (Expr *)mem;
    {   SET_BITMAP q = qualifiersoftype(te);
        if (isunaligned_type(te)) q |= bitoftype_(s_unaligned);
        return rooted_path(path, q, e);
    }
}

Expr *mkcond(Expr *a, Expr *b, Expr *c)
{   Expr *r;
    TypeExpr *t, *t1, *t2;
    a = mktest(s_cond, a);   /* checks type of a */
    if (h0_(a) == s_error) return a;
/* Slightly odd code for C++ cond: if b and c are same enum, then one   */
/* presumes result is enum, otherwise int.  [ES] silent, check std. @@@ */
/* ANSI C doesn't care since implicit int->enum is OK.                  */
    if (sameenum(t1 = typeofexpr(b), t2 = typeofexpr(c))) {
      if (isbitfield_type(t1)) {
        t1 = princtype(t1);
        t = primtype2_(typespecmap_(t1) & ~BITFIELD, typespectagbind_(t1));
      } else
        t = t1;
    } else if (h0_(b = coerceunary(b)) == s_error) return b;
    else if (h0_(c = coerceunary(c)) == s_error) return c;
    else if (t1 = typeofexpr(b), t2 = typeofexpr(c),
/* C++: the next line is a lie [ES book]. (Because Lvalue conds?)       */
/* since we are in r-value context, we can ignore qualifiers:           */
             t1 = princtype(t1), t2 = princtype(t2),
      (isclasstype_(t1) && isclasstype_(t2)) &&
      ((t = qualunion_compositetype(t1,t2)) != 0 ||
       common_reference_type(s_cond, t1, b, &b, t2, c, &c, &t)))
          /* nothing */;
/* for C++ lvalue cond the next lines need changing too.                */
       /* Since cond's give rvalues the qualifiers on the result are    */
       /* irrelevant.  However, if you wish to support (for PCC mode)   */
       /*     "struct s { int m[10]; }; const struct s x;"              */
       /*     "volatile struct s y;  int *q = (p()?x:y).m"              */
       /* then you had better review the princtype() above and decide   */
       /* which qualifiers q needs to have.                             */
/* @@@ unify code with isrelational_() call above?                      */
    else if (indexable(t1) && indexable(t2))
    {   /* Note this includes x?(void *)0:(void *)0 which the dec 88    */
        /* ansi draft leaves (seemingly to AM) undefined.               */
        /* Note also that (x?(void *)0:(int *)z) has type (int *) but   */
        /* (x?(void *)y:(int *)z has type (void *).                     */
        /* The rationale is that nullpointer constants (0 or (void*)0)  */
        /* must behave the same, but that void * values may be wider    */
        /* that int * values (e.g. a word-addressed machine).           */
        TypeExpr *t1x = indexee(t1), *t2x = indexee(t2);
        if (isnullptrconst(b)) t = t2;
        else if (isnullptrconst(c)) t = t1;
        else if (isvoidtype(t1x) && !isfntype(t2x))
            t = ptrtotype_(mkqualifiedtype(t1x, qualifiersoftype(t2x)));
        else if (isvoidtype(t2x) && !isfntype(t1x))
            t = ptrtotype_(mkqualifiedtype(t2x, qualifiersoftype(t1x)));
        else if ((t = qualunion_compositetype(t1x,t2x)) != 0)
            t = ptrtotype_(t);
        else if (!LanguageIsCPlusPlus ||
                 !common_pointer_type(s_cond,
                                      t1, b, &b,
                                      t2, c, &c, &t))
            /* fix up to *some* type.                                   */
            t = t1, cc_rerr(sem_rerr_cant_balance, s_cond);
    }
    else if (indexable(t1))
        /* Similarly note x?0:(void *)0 is unclear.                     */
        c = mkcast(s_cond, c, t1), t = (h0_(c) == s_error ? 0 : t1);
    else if (indexable(t2))
        b = mkcast(s_cond, b, t2), t = (h0_(b) == s_error ? 0 : t2);
    else if (isvoidtype(t1) && isvoidtype(t2))
        /* note t1/t2 may be qualified void, but irrelevant on rvalues. */
        t = te_void;
    else if (LanguageIsCPlusPlus &&
             (isptrtomember(t1) || isptrtomember(t2)))
    {   if (isnullptrconst(b)) t = t2;
        else if (isnullptrconst(c)) t = t1;
        else if (equivtype(t1, t2)) t = t1;/* @@@ need to allow 'int D::* p = &B::i;', etc. */
        else
            /* fix up to *some* type.                                   */
            t = t1, cc_rerr(sem_rerr_cant_balance, s_cond);
    }
    else t = lubtype(s_cond,t1,t2);
    if (t == 0) return errornode;
    b = coerce2(b,t);
    c = coerce2(c,t);
    r = mk_expr3(s_cond,t,a,b,c);
    if (h0_(a) != s_integer) return r;
    /* else simplify.  However, we must not allow (1 ? x : 2) look like
       an lvalue.  Moreover, given we have already reduced b and c
       these may have divided by zero.  Think more.
       Leave an s_invisible node or an s_integer node (the later
       if further reductions may be possible)
    */
/* @@@ (See also trydiadreduce()).  It would seem that the following    */
/* code can contravene the ANSI draft in that it also reduces           */
/* int x[(1 ? 2:(0,1))] to int x[2], which silently misses a constraint */
/* violation that the comma operator shall not appear in const exprs.   */
/* Similarly x[1 ? 2 : f()].  AM thinks the ANSI draft is a mess here.  */
    return mkinvisible(t, r, intval_(a) ? b : c);
}

void sem_init(void)
{   static Expr errorexpr = { s_error };
    errornode = &errorexpr;
}

/* End of sem.c */
