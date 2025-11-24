/*
 * overload.c: semantic analysis phase of C++ compiler
 * Copyright (C) Codemist Ltd, 1991
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$ Codemist 11
 * Checkin $Date$
 * Revising $Author$
 */

/* The file is logically part of sem.c, and imported by it and syn.c    */
/* It is (intended to be) only used by C++ extensions of C.             */

#include <string.h>             /* for strncpy                          */
#include <ctype.h>              /* for isdigit                          */
#include <stdlib.h>             /* for atoi                             */

#include "globals.h"
#include "sem.h"
#include "bind.h"
#include "aetree.h"
#include "builtin.h"
#include "aeops.h"
#include "store.h"
#include "errors.h"
#include "simplify.h"

/* the following avoids warning for AEops being 'long' (why are they?)  */
/* ... probably to guarantee storage layout if sizeof(int)==2.          */
#define E3(a,b,c) { a, (int)b, (int)c}
#define E2(a,b)   { a, (int)b, 0}
static struct { char name[6]; unsigned char op,op2; } opnametab[] =
{  /* ordering matches aeops.h, not [ES] random(?) order                */
   E2( "__aa",  s_andand                 ),
   E2( "__cm",  s_comma                  ),
   E2( "__oo",  s_oror                   ),
   E2( "__eq",  s_equalequal             ),
   E2( "__ne",  s_notequal               ),
   E2( "__gt",  s_greater                ),
   E2( "__ge",  s_greaterequal           ),
   E2( "__lt",  s_less                   ),
   E2( "__le",  s_lessequal              ),
   E3( "__ad",  s_and,        s_addrof   ),     /* type disambiguates   */
   E3( "__ml",  s_times,      s_content  ),     /* type disambiguates   */
   E3( "__pl",  s_plus,       s_monplus  ),     /* type disambiguates   */
   E3( "__mi",  s_minus,      s_neg      ),     /* type disambiguates   */
   E2( "__dv",  s_div                    ),
   E2( "__ls",  s_leftshift              ),
   E2( "__or",  s_or                     ),
   E2( "__md",  s_rem                    ),
   E2( "__rs",  s_rightshift             ),
   E2( "__er",  s_xor                    ),
   E2( "__aad", s_andequal               ),
   E2( "__aml", s_timesequal             ),
   E2( "__apl", s_plusequal              ),
   E2( "__ami", s_minusequal             ),
   E2( "__adv", s_divequal               ),
   E2( "__als", s_leftshiftequal         ),
   E2( "__aor", s_orequal                ),
   E2( "__amd", s_remequal               ),
   E2( "__ars", s_rightshiftequal        ),
   E2( "__aer", s_xorequal               ),
   E2( "__as",  s_assign                 ),
   E2( "__co",  s_bitnot                 ),
   E2( "__nt",  s_boolnot                ),
   E3( "__pp",  s_plusplus,   s_postinc  ),      /* type disambiguates   */
   E3( "__mm",  s_minusminus, s_postdec  ),      /* type disambiguates   */
   E2( "__rf",  s_arrow                  ),
   E2( "__rm",  s_arrowstar              ),
/* now the specials, not fully done...                                   */
   E2( "__cl",  s_fnap                   ),
   E2( "__vc",  s_subscript              ),
   E2( "__ct",  s_ctor                   ),
   E2( "__dt",  s_dtor                   ),
   E2( "__nw",  s_new                    ),
   E2( "__dl",  s_delete                 ),
   E2( "__op",  /* s_typespec */0        )
};

Symstr *operator_name(AEop op)
{   /* Linear search suffices (hmm) since operator is rare?             */
    /* Similarly look up in hash table as if name read each time.       */
    /* Maybe add to bind.c(sym_name_table)                              */
    unsigned int i;
    for (i = 0; i < sizeof(opnametab)/sizeof(opnametab[0]); i++)
        if (op == opnametab[i].op || op == opnametab[i].op2)
            return sym_insert_id(opnametab[i].name);
    cc_err(syn_err_illegal_operator, op);
    return sym_insert_id("__bad_operator_name");
}

bool is_operator_name(Symstr *opname)
{   unsigned int i;
    for (i = 0; i < sizeof(opnametab)/sizeof(opnametab[0]); i++)
        if (strcmp(symname_(opname), opnametab[i].name) == 0)
            return YES;
    return NO;
}

static char *spr_int(int32 n, char *p, char *q)
{   char v[20], *s;
    sprintf(v, "%ld", (long)n);
    if (v[0] == '-') v[0] = 'n';        /* that's what cfront does      */
    for (s = v; p != q && *s;) *p++ = *s++;
    return p;
}

#define stuffsig_(ch) { if (p != q) *p++ = (ch); }

static char *spr_class(TagBinder *b, unsigned n, char *p, char *q)
{   if (n > 9) syserr("10 nested classes/loop");
    else if (b == 0)
    {   if (n > 1)
        {   stuffsig_('Q')
            stuffsig_(n + '0')
        }
    }
    else
    {   char *s = symname_(bindsym_(b));
/* Print parents out ancestor-first.                                    */
        p = spr_class(b->tagparent, n+1, p, q);
        p = spr_int((int32)strlen(s), p, q);
        while (p != q && *s) *p++ = *s++;
    }
    return p;
}

static char *spr_binder(Binder *b, char *p, char *q)
{   char *s = symname_(bindsym_(b));

    while (p != q && *s) *p++ = *s++;
    return p;
}

static char *type_pos[256];
static int type_pos_index;

static bool isPtrToFn(TypeExpr *t)
{
    t = princtype(t);
    return h0_(t) == s_content && isfntype(typearg_(t));
}

/* still to do qualifiers const/vol/signed/unsigned                     */
static char *type_signature1(TypeExpr *t, char *p, char *q, bool skiptop)
{    SET_BITMAP m;
     int a_type_declarator = 0;
     Binder *unknown_tag = NULL;
     SET_BITMAP quals_unknown = 0;

     for (; ; t = typearg_(t)) {
     if (type_pos_index == 255) syserr("type_pos out of bound");
     /* a_type_declarator is possibly a misnomer, it's used to indicate
        whether or not the following type pos should be remembered.
      */
     if (skiptop == 0 && !a_type_declarator) type_pos[type_pos_index++] = p;

     if (h0_(t) == s_typespec &&
         typespecmap_(t) & bitoftype_(s_typedefname) && istypevar(t))
     {   unknown_tag = typespecbind_(t);
         quals_unknown = typespecmap_(t);
     }

     switch (t = prunetype(t), h0_(t))
     {
case s_typespec:
        a_type_declarator = 0;
        m = typespecmap_(t);
/* N.B. perhaps we should omit const/volatile for fn args, since        */
/* int f(int) and int f(const int) are compatible.                      */
/* (I.e. const/volatile in args is not part of the fn type.)            */
/* BUT!!! [ES, p122] contradicts this (accidentally?).                  */
        if (m & bitoftype_(s_const)) stuffsig_('C')
/* remember 'signed int' == 'int', so omit for int (but not char).      */
        if (m & bitoftype_(s_signed) &&
            m & bitoftype_(s_char)) stuffsig_('S')
        if (m & bitoftype_(s_unsigned)) stuffsig_('U')
        if (m & bitoftype_(s_volatile)) stuffsig_('V')
        switch (m & -m)
        {
    case bitoftype_(s_bool):
            stuffsig_('b'); break;
    case bitoftype_(s_char):
            stuffsig_('c'); break;
    case bitoftype_(s_int):
            stuffsig_(int_islonglong_(m) ? 'x' :
                      m & bitoftype_(s_short) ? 's' :
                      m & bitoftype_(s_long) ?  'l' : 'i'); break;
    case bitoftype_(s_double):
            stuffsig_(m & bitoftype_(s_short) ? 'f' :
                      m & bitoftype_(s_long) ?  'r' : 'd'); break;
    case bitoftype_(s_void):
            stuffsig_('v'); break;
    case bitoftype_(s_struct):
    case bitoftype_(s_class):
    case bitoftype_(s_union):
    case bitoftype_(s_enum):
            p = spr_class(typespectagbind_(t), 0, p, q);
            break;
    default: goto defolt;
        }
        return p;
default:
defolt: stuffsig_('!');
        return p;
case t_unknown:
        if (!unknown_tag) syserr("Unknown type id!!");
        if (quals_unknown)
        {   if (quals_unknown & bitoftype_(s_const)) stuffsig_('C');
            if (quals_unknown & bitoftype_(s_volatile)) stuffsig_('V');
        }
        p = spr_int((int32)strlen(symname_(bindsym_(unknown_tag))), p, q);
        p = spr_binder(unknown_tag, p, q);
        a_type_declarator = 0;
        return p;
case t_subscript:
        {   Expr *subsz = typesubsize_(t);
            stuffsig_('A');
            /* Hmmm, can't use is_template_arg_binder() here. Wrong scope. */
            p = spr_int((subsz == 0 || h0_(subsz) == s_binder ||
                         (h0_(subsz) == s_cast && h0_(arg1_(subsz)) == s_binder)) ? 0 :
                        evaluate(subsz), p, q);
            stuffsig_('_');
            a_type_declarator = 1;
            break;
        }
case t_content:
        if (typeptrmap_(t) & bitoftype_(s_const)) stuffsig_('C')
        if (typeptrmap_(t) & bitoftype_(s_volatile)) stuffsig_('V')
        if (h0_(typearg_(t)) == t_coloncolon)
        {   t = typearg_(t);
            stuffsig_('M');
            p = spr_class(typespectagbind_(t), 0, p, q);
        }
        else
            stuffsig_('P');
        a_type_declarator = 1;
        break;
case t_ref:
        stuffsig_('R');
        a_type_declarator = 1;
        break;
case t_fnap:
/* We prefix a function type with its qualifiers so that                */
/*  "int f() const;" becomes f__CFv.  This is compatible with [ES] but  */
/* not defined there.  Such a scheme is vital for member fns [ES,p321]. */
/* Maybe put on the implicit 'this' type on b_impl implementations?     */
        if (typeptrmap_(t) & bitoftype_(s_const)) stuffsig_('C')
        if (typeptrmap_(t) & bitoftype_(s_volatile)) stuffsig_('V')
        stuffsig_('F');
        {   FormTypeList *l = typefnargs_(t);
/* [ES] ambiguity: does f(...) map to f__Fe or f__Fve?  Former here.    */
            if (l == NULL && !fntypeisvariadic(t))
            {   type_pos[type_pos_index++] = p;
                stuffsig_('v')
            }
            else for (; l != NULL; l = cdr_(l))
                p = type_signature1(l->fttype, p, q, 0);
            if (fntypeisvariadic(t)) stuffsig_('e');
        }
        if (skiptop) return p;
        stuffsig_('_');
        a_type_declarator = (isPtrToFn(typearg_(t))) ? 0 : 1;
        break;
     }
     }
}

typedef struct {int m, w; const unsigned char *cptr;} TT;

static TT folds(const unsigned char *rptr)
{
    TT tt;
    char tmp[2];
    int n1;

    tmp[1] = '\0';
    tmp[0] = *rptr++;
    n1 = atoi(tmp);
    tt.m = 1;
    tt.w = n1;
    tt.cptr = rptr;
    while (*rptr == 'T' && isdigit(*(rptr + 1)))
    {   int n2;
        tmp[0] = *++rptr;
        n2 = atoi(tmp);
        if (n1 == n2)
        {   tt.m++;
            tt.cptr = ++rptr;
        } else
            break;
    }
    return tt;
}


static int isPFtype(char *t)
{   int ptr = 0;
    while (*t == 'P') (ptr++, t++);
    /* PPF is considered a PF type */
    return (*t == 'F' && ptr) ? (ptr - 1) : -1;
}

static int type_len(int index, int upb, char *begin, char *end, char *tp[])
{   int res = ((index + 1 != upb) ? tp[index + 1] : end) - begin;
    return res;
}

struct PFtypes {
    char *type_pos[256];
    int type_pos_index;
    struct PFtypes *next;
};

typedef struct PFtypes PFtypes;

static PFtypes *pftypes;

/* This can only be called in a PF in PF context */
static int pf_upb(int i, char *tp[], int upb)
{
    char *t = tp[i++];
    char *res = strchr(t, '_');
    int start = i;
    while (i < upb && tp[i] < res) ++i;
    return i - start;
}

/* remove all PF relative types, returns adjusted upper bound */
static int PF_reduction(int upb, char*tp[])
{   int i = 0;
    while (i < upb)
    {   char *cur_type = tp[i];
        if (isPFtype(cur_type) >= 0)
        {   int where, displacement, w;
            char *res = strchr(cur_type, '_');  /* warning: just a hint */
            PFtypes *pft = (PFtypes *)SynAlloc(sizeof(PFtypes));

            if (pftypes == 0)
                pftypes = pft;
            else
            {   PFtypes *pptr = pftypes;
                while (pptr->next != 0) pptr = pptr->next;
                pptr->next = pft;
            }
            w = where = ++i;
            pft->next = (PFtypes *)0;
            pft->type_pos_index = 0;
            while (i < upb && tp[i] < res)
            {   char *t = tp[i];
                if (pft->type_pos_index == 255) syserr("type_pos out of bound");
                pft->type_pos[pft->type_pos_index++] = t;
                if (isPFtype(t) >= 0)
                {   int lupb = pf_upb(i, tp, upb), tmp;
                    tmp = PF_reduction(lupb + 1, &tp[i]);
                    i += lupb + 1;
                    /* re-adjust res */
                    res = strchr(tp[i], '_');
                } else
                    i++;
            }
            displacement = i - where;
            for(; i < upb;) tp[where++] = tp[i++];
            upb -= displacement;
            i = w;
        }
        else
            ++i;
    }
    return upb;
}

#define stuff_buf_(t, l)  {int _tmp = l; char *_tmpt = t; \
                while (_tmp-- && (buf < end)) *buf++ = *_tmpt++; *buf=0;}
#define stuff_buf_T_(n)   {int _tmp = n; *buf++ = 'T'; \
                        buf = spr_int(_tmp, buf, end); *buf=0;}

static char *N_reduction(const unsigned char*, char*, char*, char*);

static char *T_reduction(int upb, char *tp[], char* tend, char *buf, char *end)
{
    int i = 0;
    while (i < upb)
    {   int j = 0, done = 0, len, nptrs;
        char *cur_type = tp[i], *t;

        len = type_len(i, upb, cur_type, tend, tp);

        while ((t = tp[j]) < cur_type && !done && j < 9)
        {   int tlen = type_len(j++, upb, t, tend, tp);
            if (strncmp(t, cur_type, tlen) == 0)
            {   int res_len = len - tlen;
                stuff_buf_T_(j);
                if (res_len > 0)
                {   cur_type += tlen;
                    stuff_buf_(cur_type, res_len);
                }
                done = 1;
            }
        }
        if (!done)
        {   if ((nptrs = isPFtype(cur_type)) >= 0)
            {   char *PF = "PF", *P = "P";
                char lbuffer[256], *lbuf;
                PFtypes *lpft;

                while (nptrs--) stuff_buf_(P, 1);
                stuff_buf_(PF, 2)
                if (!pftypes) syserr("T_reduction: empty pftyes");
                lpft = pftypes; pftypes = pftypes->next;
                lbuf = T_reduction(lpft->type_pos_index, lpft->type_pos,
                        (i + 1 != upb) ? tp[i+1] : tend,
                        lbuffer, lbuffer + sizeof lbuffer);
                buf = N_reduction((const unsigned char *)lbuffer, lbuf, buf, end);
            }
            else
                stuff_buf_(cur_type, len);
        }
        ++i;
    }
    return buf;
}

static char *N_reduction(const unsigned char *rptr, char *buf, char *wptr, char *end)
{
    while (rptr < (const unsigned char *)buf)
    {   if (*rptr == 'T' && isdigit(*(rptr + 1)))
        {   TT t = folds(rptr + 1);
            if (t.m > 1)
            {   int m = t.m;
                while (m > 9)
                {   *wptr++ = 'N';
                    wptr = spr_int(9, wptr, end);
                    wptr = spr_int(t.w, wptr, end);
                     m -= 9;
                }
                if (m != 0)
                {   *wptr++ = (m == 1) ? 'T' : 'N';
                    if (m != 1) wptr = spr_int(m, wptr, end);
                    wptr = spr_int(t.w, wptr, end);
                    rptr = t.cptr;
                }
            } else
            {   *wptr++ = 'T';
                wptr = spr_int(t.w, wptr, end);
                rptr = t.cptr;
            }
        } else
            *wptr++ = *rptr++;
    }
    return wptr;
}

static char *type_signature(TypeExpr *t, char *p, char *q, bool skiptop)
{   type_pos_index = 0;
    p = type_signature1(t, p, q, skiptop);
    if (type_pos_index <= 1)
        return p;
    else
    {   char T_buffer[256], *buf;
        pftypes = 0;
        type_pos_index = PF_reduction(type_pos_index, type_pos);
        if (!type_pos_index) return p;
        buf = T_reduction(type_pos_index, type_pos, p,
                          T_buffer, T_buffer + sizeof T_buffer);
        return N_reduction((const unsigned char *)T_buffer, buf, type_pos[0], q);
    }
}

static char *value_signature(Expr *e, char *p, char *q)
{   if (h0_(e) == s_cast) e = arg1_(e);
    stuffsig_('X');
    /* cfront adds the type of the parameter here (why?).               */
    /* (and it uses a different encoding of values).                    */

    switch (h0_(e)) {
    case s_integer:
        p = spr_int(intval_(e), p, q);  /* use evaluate(e)?             */
        break;
    case s_content:
    case s_addrof:
        e = arg1_(e);
        /* @@@ fix the next line */
        if (h0_(e) != s_binder)
            goto defolt;
    case s_binder:
        {   Binder *b = exb_(e);
            p = spr_binder(b, p, q);    /*/* what if binder contains a 'Y'?*/
            break;
        }
    defolt:
    default:
        stuffsig_('?');
    }
    stuffsig_('Y');
    return p;
}

static const char tmpt_encoding[] = "__t";
#define tmpt_encoding_length 3
static const char tmpt_fn_encoding[] = "__tF";
#define tmpt_fn_encoding_length 4
static const char tmpt_fn_targs_encoding[] = "_<";
#define tmpt_fn_targs_encoding_length 2
#define OVLD_TEMP_FUNC_NAME_SIZE 128

Symstr *ovld_function_template_name(Symstr *sv, TypeExpr *t)
{   char v[OVLD_TEMP_FUNC_NAME_SIZE*2], *p, *q;         /* RW uses very long param names */
    size_t namelen = strlen(symname_(sv));
    if (!isfntype(t)) syserr("Fn type expected, $t instead", t);
    if (sizeof(v) - tmpt_encoding_length - 1 < namelen)
        syserr("name is too long to encode template args: '%s'", symname_(sv));
    strcpy(v, symname_(sv)); strcpy(v + namelen, tmpt_encoding);
    p = v+namelen+tmpt_encoding_length; q = v+sizeof(v)-1;
    p = type_signature(t, p, q, 1);
    /* DWP Oct95 required return type as well */
    if (p < q)
        *p++ = '_';
    p = type_signature(typearg_(t), p, q, 0);
    *p = 0;
    return sym_insert_id(v);
}

Symstr *ovld_tmptfn_instance_name(Symstr *sv, ScopeSaver f)
{   char v[OVLD_TEMP_FUNC_NAME_SIZE], *p, *q;
    size_t namelen = strlen(symname_(sv));
    if (sizeof(v) - tmpt_fn_targs_encoding_length - 2 < namelen)
        syserr("name is too long to encode template args: '%s'", symname_(sv));
    strcpy(v, symname_(sv)); strcpy(v + namelen, tmpt_fn_targs_encoding);
    p = v+namelen+tmpt_fn_targs_encoding_length; q = v+sizeof(v)-2;
    for (; f != NULL; f = bindcdr_(f))
        if (bindconst_(f) != NULL)
            p = value_signature(bindconst_(f), p, q);
        else
            p = type_signature(h0_(bindtype_(f)) == t_unknown ?
                        primtype2_(bitoftype_(s_typedefname), f) : princtype(bindtype_(f)),
                               p, q, 0);
    *p++ = '>', *p = 0;
    return sym_insert_id(v);
}

Symstr *specialized_name_of(TagBinder *tmptb)
{   ScopeSaver f = tagformals_(tmptb);
    char v[128], *p, *q;
    size_t namelen = strlen(symname_(bindsym_(tmptb)));
    if (sizeof(v) - tmpt_encoding_length - 1 < namelen)
        syserr("name is too long to specialize: '%s'", symname_(bindsym_(tmptb)));
    strcpy(v, symname_(bindsym_(tmptb))); strcpy(v + namelen, tmpt_encoding);
    p = v+namelen+tmpt_encoding_length; q = v+sizeof(v)-1;
    for(; f != NULL; f = bindcdr_(f))
    {   if (h0_(bindtype_(f)) == t_unknown)
            p = type_signature(primtype2_(bitoftype_(s_typedefname), f), p, q, 0);
        else
            p = value_signature((Expr *)f, p, q);
    }
    *p = 0;
    return sym_insert_id(v);
}

Symstr *ovld_template_app(Symstr *sv, ScopeSaver f, ExprList *a)
{   char v[128], *p, *q;
    Binder *tactualp = NULL, *tactualq = NULL;
    int template_paras = env_size(f), template_args = 0;

    strcpy(v, symname_(sv)); strcat(v, tmpt_encoding);
    p = v+strlen(v); q = v+sizeof(v)-1;
    for (; f != NULL; f = bindcdr_(f))
    {   Expr *e = (a && exprcar_(a)) ? exprcar_(a) : bindconst_(f);
        Binder *temp;

        /* Note use of s_typespec for a 'type' template actual. */
        if (!e) {
            cc_err(sem_err_type_arg_expected);
            /* should return a qualified sv to suppress further diagnostics.    */
            return sv;
        }

        temp = mk_binder(bindsym_(f), bindstg_(f), bindtype_(f));

        if (!tactualp)
            tactualp = tactualq = temp;
        else
            bindcdr_(tactualq) = temp, tactualq = temp;

        if (h0_(bindtype_(f)) == t_unknown)
        {
            if (h0_(e) != s_typespec ||
                (typespecmap_(bindtype_(f)) && !istypevar(type_(e)) &&
                !(typespecmap_(bindtype_(f)) &
                  typespecmap_(princtype(type_(e))))))
            {   cc_err(sem_err_typeclash_1, typespecmap_(bindtype_(f)),
                       typespecmap_(princtype(typeofexpr(e))));
                /* @@@ return a qualified sv to suppress further diagnostics */
                return sv;
            }

            if (h0_(type_(e)) == t_unknown)
                syserr("ovld_template_app: bare t_unknown");
            if (istypevar(type_(e)) &&
                bindsym_(f) == bindsym_(typespecbind_(type_(e))))
            {   template_args++;
                binduses_(typespecbind_(type_(e))) |= u_referenced;
            }
            bindtype_(temp) = type_(e);
            if (e && h0_(e) == s_typespec && e == bindconst_(f) &&
                istypevar(bindtype_(temp)))
            {   bindtype_(temp) = clone_typeexpr(bindtype_(temp));
                fixup_template_arg_type(bindtype_(temp), tactualp);
            }
            p = type_signature(bindtype_(temp), p, q, 0);

        } else if (isclasstype_(bindtype_(f)) &&
                   tagbindbits_(typespectagbind_(bindtype_(f))) & TB_TEMPLATE)
        {   TypeExpr *argtype = princtype(type_(e));
            TagBinder *arg = NULL;
            if (h0_(e) != s_typespec ||
                !isclasstype_(argtype) ||
                !(tagbindbits_(arg = typespectagbind_(princtype(type_(e)))) & TB_TEMPLATE) ||
                !comparable_templates(typespectagbind_(bindtype_(f)), arg))
            {   if (h0_(e) != s_typespec)
                    cc_err(sem_err_typeclash_2, e);
                else
                    cc_err(sem_err_typeclash_3, argtype);
                return sv;
            }
            bindtype_(temp) = type_(e);
            p = type_signature(bindtype_(temp), p, q, 0);
        } else {
            if (h0_(princtype(bindtype_(f))) == t_ref && !issimplelvalue(e))
            {   cc_err(sem_err_lvalue_needed);
                return sv;
            }

            bindtype_(temp) = clone_typeexpr(bindtype_(f));
            fixup_template_arg_type(bindtype_(temp), tactualp);

            /* The reason for the next line: consider,
                template <class T, T x> struct X {};
                X<double, 1> x;
            */
            if (isprimtypein_(princtype(bindtype_(temp)),
                              bitoftype_(s_double)|bitoftype_(s_float)))
            {   cc_err(sem_err_temp_type_float);
                return sv;
            }

            e = mkcast(s_template, e, widen_formaltype(bindtype_(temp)));
            if (h0_(e) == s_error || h0_(e) == s_typespec)
                return sv;

            e = optimise0(e);
            if ((p = value_signature(e, p, q)) == 0) return sv;
            if (h0_(e) == s_binder && bindsym_(f) == bindsym_(exb_(e)))
            {   template_args++;
                binduses_(exb_(e)) |= u_referenced;
            }
            if (a)
                exprcar_(a) = e;
#if NEVER
            else
                bindconst_(f) = e;
#endif
        }

        if (a) a = cdr_(a);
    }
    *p = 0;
    if (a)
        cc_warn(syn_rerr_extra_template_actuals);

    return (template_paras == template_args) ? sv : sym_insert_id(v);
}

Symstr *conversion_name(TypeExpr *t)
{   char v[128];
    strcpy(v, "__op");
    *type_signature(t, v+4, v+127, 0) = 0;
    return sym_insert_id(v);
}

String *exception_name(TypeExpr *t)
{   StringSegList *s;
    char v[128], *p = v, *q = type_signature(t, v, v+127, 0);
    *q = 0;
    if (*p == 'C') p++;
    if (*p == 'V') p++;         /* lose const/volatile */
    if (*p == 'R') p++;         /* *then* lose t_ref   */
/* We maybe should also save the strings corresponding to base classes  */
/* for the implicit coercions.                                          */
    {   size_t n =  q - p;
/* See syn.c(rd_ANSIstring) for the following comment.                  */
/* Note that the list of string segments must last longer than most     */
/* other parts of the parse tree, hence use binder_list3() here.        */
        char *w = (char *)BindAlloc(n);
        if (n != 0) memcpy(w, p, n);
        s = (StringSegList *)binder_list3(0, w, n);
    }
    return (String *)syn_list2(s_string, s);
}

Symstr *ovld_add_memclass(Symstr *sv, TagBinder *scope, bool staticfn)
{   char v[128], *p = v, *q = v+127;
    const char *s = symname_(sv);
/* This function is a hack to add type scope to top-level forms of      */
/* member functions which have already been overload-disambiguated      */
/* but only within class scopes.  E.g. f -> f__v -> f__3FOOv.           */
/*   (It is nasty in case user names have '__' within.)                 */
/*   ^^^No more!!!                                                      */
/* It also turns class A { static int x; } into x__1A.                  */
    char *x;
    for (; *s == '_'; s++) stuffsig_(*s) /* copy leading '_'s */
    for (x = strstr(s, tmpt_fn_encoding);
         x != NULL;
         x = strstr(x, tmpt_fn_encoding))
    {   x += tmpt_fn_encoding_length;
        for (; s < x; s++) stuffsig_(*s)
    }
    for (; *s != 0; s++)
    {   if (s[0] == '_' && s[1] == '_') { s += 2; break; }
        stuffsig_(*s)
    }
    /* syserr here if *s = '\0' ? */
    stuffsig_('_')
    stuffsig_('_')
    p = spr_class(scope, 0, p, q);
/* The next line attempts to interpolate between [ES] and CFront:       */
/*           class A { static int x, f(); int g(); };                   */
/*                     x__1A, f__1ASFv, g__1AFv.                        */
/* Although [ES] don't use 'S' here, it clearly adds to safety.         */
    if (staticfn) stuffsig_('S')
    for (; *s != 0; s++) stuffsig_(*s)
    *p = 0;
    return sym_insert_id(v);
}

Symstr *ovld_instance_name_1(const char *name, TypeExpr *t)
{   char v[1024], *p;
/* @@@ Nasty hack: class member fns get the arg types added to their    */
/* names for overload resolution within classes.  It is convenient to   */
/* add their class-name also (since this will give the external name).  */
/* However, this must be up for review w.r.t.                           */
/*              typedef { int f(),f(int); } t;                          */
/* which is a curio (possibly unreasonably so) in which we don't know   */
/* the class-name until after the overloaded def has been made.         */
/* We should probably also beware (at top-level)                        */
/*              T::typedefname f();                                     */
/* i.e. check the scope of T.                                           */
/*         @@@ the above comment is suspended!                          */
/*         TagBinder *scope = current_member_scope();                   */
    size_t namelen = strlen(name);
    if (sizeof(v) - 3 < namelen)
        syserr("name too long to mangle: '%s'", name);
    strcpy(v, name); strcpy(v + namelen, "__");
    p = v+namelen+2;
/*           if (scope) p = spr_class(scope, p, v+127);                 */
/* @@@ remember here things like "int f() const {}"...                  */
    *type_signature(t, p, v+sizeof(v)-1, 1) = 0;
    {   Symstr *sv = sym_insert_id(v);
        return sv;
    }
}

Symstr *ovld_instance_name(Symstr *sv, TypeExpr *t)
{   Symstr *sv2 = ovld_instance_name_1(symname_(sv), t);
    if (sv == sv2) syserr("ovld_instance_name");
    return sv2;
}

static void chk_ovld_access(Binder *bm)
{   if (bindparent_(bm) != 0)
    {   accessOK &= ~1;
        check_access((ClassMember *)bm, 0);
        if (accessOK == 0)
            diagnose_access(bindsym_(bm), bindparent_(bm));
    }
}

/* This needs merging with a more-general mechanism for "t p = &f;".    */
Expr *ovld_picknullary(Binder *bgeneric)
{   TypeExpr *t = bindtype_(bgeneric);
    BindList *bl;
    if (h0_(t) != t_ovld) syserr("ovld_picktype");
    for (bl = typeovldlist_(t); bl; bl = cdr_(bl))
    {   Binder *b = bl->bindlistcar;
        TypeExpr *t = princtype(bindtype_(b));
        if (h0_(t) == t_fnap && typefnargs_(t) == NULL)
        {   chk_ovld_access(b);
            if (bindstg_(b) & b_impl) b = realbinder_(b);
            return mkunary(s_addrof, (Expr *)b);
        }
    }
    return 0;
}

typedef struct TypeList TypeList;
struct TypeList {
    TypeList *cdr;
    TypeExpr *tltype;
};

/* add a type to a list of unique types... really a set of types */
static TypeList *mk_typelist(TypeList *tlp, TypeExpr *tltype)
{   TypeList *l;
    for (l = tlp;  l != 0;  l = cdr_(l))
        if (equivtype(tltype, l->tltype)) return tlp;
    return (TypeList *)syn_cons2(tlp, tltype);
}

/* here we just find the set of all convfn types... filter later */
/* assume t has been princtype'd by the caller...                */
static TypeList *convtypes_of_class(TypeExpr *t, TypeList *tl)
{   TagBinder *b = typespectagbind_(t);
    ClassMember *l;
    for (l = tagbindmems_(b);  l != 0;  l = memcdr_(l))
    {   if (attributes_(l) & (CB_CORE|CB_BASE|CB_VBASE))
            tl = convtypes_of_class(memtype_(l), tl);
        else if ((attributes_(l) & CB_TCONV) && (bindstg_(l) && b_impl))
            /* Assert: h0_(bindype_(l)) is t_fnap... */
            tl = mk_typelist(tl, typearg_(bindtype_(l)));
    }
    return tl;
}

Expr *allowable_boolean_conversion(Expr *e)
{
    TypeExpr *cvntype = NULL, *t = princtype(typeofexpr(e));
    TypeList *convtypes = convtypes_of_class(t, NULL);
    TagBinder *cla = typespectagbind_(t);
    int conv_nmatch = 0;
    for (; convtypes != NULL;
                convtypes = (TypeList *)discard2(convtypes))
    {   t = convtypes->tltype;
        if (isprimtype_(t, s_bool)) {conv_nmatch = 1; cvntype = t; break;}
        if (h0_(t) == t_content || (h0_(t) == s_typespec &&
                !(typespecmap_(t) & bitoftype_(s_void)) &&
                !(typespecmap_(t) & ENUMORCLASSBITS)))
        {   conv_nmatch++;
            cvntype = t;
        }
    }
    if (conv_nmatch > 1)
    {   cc_rerr(syn_rerr_multi_convfn_bool, conv_nmatch, cla);
        return errornode;
    }
    else if (cvntype != NULL)
    {   Binder *b = class_has_conversion(cla, cvntype, YES);
        return mkfnap(mkfieldselector(s_dot, e, b), 0);
    }
    return e;
}

/* assume t has been princtype'd by the caller...                */
static TypeList *convtypes_of_type(TypeExpr *t)
{   if (isclasstype_(t))
        return convtypes_of_class(t, NULL);
    else
        return mk_typelist(NULL, t);
}

typedef struct OvldCandidate {
    Binder *binder;
    FormTypeList *fnarg;
} OvldCandidate;

#define candidate_(l) ((OvldCandidate *)car_(l))

static OvldCandidate *mk_candidate(Binder *b, FormTypeList *ft)
{   return (OvldCandidate *)syn_list3(b, ft, 0);
}

static List *ocl_cons(List *l, OvldCandidate *c)
{   return (List *)syn_cons2(l, c);
}

static List *ocl_discard(List *member)
{   discard3(candidate_(member));
    return (List *)discard2(member);
}

List *mk_candidates(BindList *alternatives,
                int nargs, int adjust_for_static_memfn, List *ocl)
{   BindList *p;
    for (p = alternatives; p != NULL; p = cdr_(p))
    {   Binder *btry = p->bindlistcar;
        TypeExpr *ttry = princtype(bindtype_(
            (bindstg_(btry) & (b_memfna|b_memfns)) ? realbinder_(btry) : btry));
        int n = (bindstg_(btry) & b_memfns) && adjust_for_static_memfn ?
            nargs-1 : nargs;
        if (h0_(ttry) != t_fnap)
            syserr("overload::mk_candidates(nonfn %ld)", h0_(ttry));
        if (minargs_(ttry) <= n && n <= maxargs_(ttry))
            ocl = ocl_cons(ocl, mk_candidate(btry, typefnargs_(ttry)));
    }
    return ocl;
}

static Binder *operator_candidate(AEop op, TypeExpr *t1, TypeExpr *t2)
{   return (Binder *) syn_list3(op, t1, t2);
}

static FormTypeList *binop_fnargs(TypeExpr *t1, TypeExpr *t2)
{   /* Keep in step with FormTypeList... */
    return (FormTypeList *) syn_list3(syn_list3(0, 0, t2), 0, t1);
}

static FormTypeList *unop_fnargs(TypeExpr *t1)
{   /* Keep in step with FormTypeList... */
    return (FormTypeList *) syn_list3(0, 0, t1);
}

static TypeExpr *builtin_formaltype(TypeExpr *t)
{   t = prunetype(promoted_formaltype(t));
    if (h0_(t) == s_typespec &&
        (typespecmap_(t) & bitoftype_(s_enum)))
        t = te_int;
    return t;
}

static bool binop_exists(AEop op, TypeExpr *t1, TypeExpr *t2,
                         TypeExpr **t1p, TypeExpr **t2p)
{
    bool result = NO;

    t1 = princtype(t1);
    t2 = princtype(t2);

    /*/* this is just a small part of over.builtin */
    switch (op) {
    case s_rem:
    case s_and:
    case s_xor:
    case s_or:
    case s_leftshift:
    case s_rightshift:
        if (h0_(t1) == t_ref)
            t1 = princtype(typearg_(t1));
        if (isintegraltype_(t1))
        {
            if (h0_(t2) == t_ref)
                t2 = princtype(typearg_(t2));
            result = isintegraltype_(t2);
        }
        break;

    default:
        result = YES; /*/* builtin operators, optimistic for now */
        break;
    }

    if (result)
    {   *t1p = builtin_formaltype(t1);
        *t2p = builtin_formaltype(t2);
    }

if (var_cc_private_flags & 16384)
    cc_msg("binop_exists: $s($t,$t) => %s\n", op, t1, t2, result ? "YES" : "NO");
    return result;
}

static bool unop_exists(AEop op, TypeExpr *t, TypeExpr **tp)
{
    bool result = NO;

    t = princtype(t);

    /*/* this is just a part of over.builtin */
    switch (op) {
    case s_bitnot:
        if (h0_(t) == t_ref)
            t = princtype(typearg_(t));
        result = isintegraltype_(t);
        break;

    case s_minus:
        if (h0_(t) == t_ref)
            t = princtype(typearg_(t));
        result = isarithtype_(t);
        break;

    case s_plus:
        if (h0_(t) == t_ref)
            t = princtype(typearg_(t));
        result = h0_(t) == t_content || h0_(t) == t_fnap || isarithtype_(t);
        break;

    default:
        /*/* other builtin operators, optimistic for now */
        result = !isclasstype_(t);
        break;
    }

    if (result)
        *tp = builtin_formaltype(t);
if (var_cc_private_flags & 16384)
    cc_msg("unop_exists: $s($t) => %s\n", op, t, result ? "YES" : "NO");
    return result;
}

static List *mk_binop_candidates(AEop op,TypeExpr *t1, TypeExpr *t2, List *ocl)
{
    TypeList *tl1 = (op == s_assign) ?
         mk_typelist(0, t1) : convtypes_of_type(princtype(t1));
    TypeList *tl2 = convtypes_of_type(princtype(t2)), *l;

    for (;  tl1 != 0;  tl1 = (TypeList *)discard2(tl1))
    {   for (l = tl2;  l != 0;  l = cdr_(l))
        {   TypeExpr *t1p, *t2p;
            if (binop_exists(op, tl1->tltype, l->tltype, &t1p, &t2p))
                ocl = ocl_cons(ocl, mk_candidate(
                        operator_candidate(op, tl1->tltype, l->tltype),
                        binop_fnargs(t1p, t2p)));
        }
    }
    for (;  tl2 != 0;  tl2 = (TypeList *)discard2(tl2));
    return ocl;
}

static List *mk_unop_candidates(AEop op, TypeExpr *t1, List *ocl)
{
    TypeList *tl1 = convtypes_of_type(princtype(t1));

    for (;  tl1 != 0;  tl1 = (TypeList *)discard2(tl1))
    {   TypeExpr *tp;
        if (unop_exists(op, tl1->tltype, &tp))
            ocl = ocl_cons(ocl, mk_candidate(
                    operator_candidate(op, tl1->tltype, 0),
                    unop_fnargs(tp)));
    }
    return ocl;
}

List *mk_operator_candidates(AEop op, TypeExpr *t1, TypeExpr *t2, List *ocl)
{   TagBinder *b = isclassenumorref_type(t1);
    if (b != 0) t1 = tagbindtype_(b);
    if (t2 != 0)
    {   b = isclassenumorref_type(t2);
        if (b != 0) t2 = tagbindtype_(b);
        return mk_binop_candidates(op, t1, t2, ocl);
    }
    else
        return mk_unop_candidates(op, t1, ocl);
}

static int compute_match_value(OvldCandidate *c, TypeExpr *t, const Expr *e,
        int arg_is_this, int convfn_is_OK, int is_lvalue);

#define DISTINCT_DLEVELS                100
#define MLevels                         8
#define MATCH_THIS  (24+(MLevels*DISTINCT_DLEVELS)+1)
    /* match value returned for match of 'this' with static member fn.  */
    /* NOTE: MUST be greater than the greatest match value returnable.  */
#define MATCH_TYPEVAR   (0+((MLevels-7)*DISTINCT_DLEVELS)+1)
#define MATCH_VARIADIC  (4+((MLevels-7)*DISTINCT_DLEVELS))
#define MATCH_4     ( 8+((MLevels-6)*DISTINCT_DLEVELS)+1)
#define MATCH_3_V   (10+((MLevels-5)*DISTINCT_DLEVELS)+1)
#define MATCH_3     (12+((MLevels-4)*DISTINCT_DLEVELS)+1)
#define MATCH_2_B   (14+((MLevels-3)*DISTINCT_DLEVELS)+1)
#define MATCH_2     (16+((MLevels-2)*DISTINCT_DLEVELS)+1)
#define MATCH_1     (20+((MLevels-1)*DISTINCT_DLEVELS)+1)
#define SLIGHTLY_WORSE_THAN(x)  ((x) & ~1)
#define NO_MATCH        0

static int conv_matchval, conv_nmatch;

static Binder *class_has_convfn(TagBinder *cl, TypeExpr *t, int pick_best)
{   ClassMember *m, *vbases = 0;
    OvldCandidate cc;
    FormTypeList ft;
    int best_match = NO_MATCH, nmatch = 0;
    Binder *best = 0;

    cc.fnarg = &ft;
    ft.cdr = 0;
    ft.fttype = t;

    m = tagbindmems_(cl);
    if (m != 0 && attributes_(m) & CB_CORE)
    {   vbases = memcdr_(m);
        cl = typespectagbind_(memtype_(m));
    }

/* first look for suitable conversion functions in the CORE class... */
    for (m = tagbindmems_(cl);  m != 0;  m = memcdr_(m))
    {   if (attributes_(m) & CB_TCONV)
        {   TypeExpr *mt = memtype_(m), *res = typearg_(mt);
            Binder *b = (Binder *)m;
            int matchval;
            mt = bindtype_(b);
            cc.binder = b;
            matchval = compute_match_value(&cc, res, NULL, NO, NO,
                                           h0_(prunetype(res)) == t_ref);
if (var_cc_private_flags & 16384)
    cc_msg("$t has conversion to $t sees $t -> %d\n",
        tagbindtype_(cl), t, typearg_(mt), matchval);
            if (matchval > best_match)
            {   best = b;
                best_match = matchval;
                nmatch = 1;
                if (!pick_best) break;
            }
            else if (matchval == best_match)
                ++nmatch;
        }
    }

/* if found none, then look for inherited conversion functions... */
    if (best_match == NO_MATCH)
    {   for (m = tagbindmems_(cl);  m != 0;)
        {   if (attributes_(m) & (CB_BASE|CB_VBASE))
            {   Binder *b;
                conv_matchval = conv_nmatch = 0;
                b = class_has_conversion(
                    typespectagbind_(memtype_(m)), t, pick_best);
                if (conv_matchval > best_match)
                {   best = b;
                    best_match = conv_matchval;
                    nmatch = conv_nmatch;
                    if (!pick_best) break;
                }
                else if (conv_matchval == best_match)
                    ++nmatch;
            }
            else
            {   m = vbases;
                vbases = 0;
                continue;
            }
            m = memcdr_(m);
        }
    }
    conv_matchval = best_match;
    conv_nmatch = nmatch;
    return best;
}

Binder *class_has_conversion(TagBinder *cl, TypeExpr *t, int pick_best)
{   Binder *best;
    conv_matchval = conv_nmatch = 0;
    best = class_has_convfn(cl, t, pick_best);
    if (conv_matchval > 0 && conv_nmatch > 1)
        cc_err(syn_err_multi_convfn_ovld, conv_nmatch, cl, t);
    else if (pick_best && best != 0)
        best = findbinding(bindsym_(best), cl, INDERIVATION);
    if (best != NULL) chk_ovld_access(best);
    return best;
}

Binder *class_has_ctor_1(TagBinder *cl, TypeExpr *t, const Expr *e, int pick_best, bool silent)
{   OvldCandidate cc;
    FormTypeList ft;
    int best_match, nmatch;
    Binder *best, *ct;
    BindList *bl;

    if (!(tagbindbits_(cl) & TB_NEEDSCTOR))
        return 0;
    ct = findbinding(ctorsym, cl, INCLASSONLY);
    t = modify_actualtype(t, e);
    cc.fnarg = &ft;
    ft.cdr = 0;
    best_match = nmatch = 0;
    best = NULL;

    for (bl = typeovldlist_(bindtype_(ct));  bl != 0;  bl = cdr_(bl))
    {   Binder *b = bl->bindlistcar;
        TypeExpr *bt = bindtype_(b);
        int matchval;
        if (h0_(bt) != t_fnap) continue;
        if (minargs_(bt) > 1 || maxargs_(bt) == 0) continue;
        cc.binder = b;

        /* FW: Gauged the orig intention from the value assigned. */
#if 0
        if (minargs_(bt) == 0)
#else
        if (fntypeisvariadic(bt))
#endif
            matchval = MATCH_VARIADIC;
        else
        {   ft.fttype = typefnargs_(bt)->fttype;
            matchval = compute_match_value(&cc, t, e, NO, NO, YES);
        }
        if (var_cc_private_flags & 16384)
            cc_msg("$t has ctor from $t%s sees $t -> %d\n",
                   tagbindtype_(cl), t, isnullptrconst(e) ? "(null ptr const)" : "",
                   ft.fttype, matchval);
        if (matchval > best_match)
        {   best = b;
            best_match = matchval;
            nmatch = 1;
            if (!pick_best) break;
        }
        else if (matchval == best_match)
            ++nmatch;
    }
    if (best_match > 0 && nmatch > 1 && !silent)
        cc_err(syn_err_multi_ctor_ovld, nmatch, t, cl);
    if (best != NULL && pick_best) chk_ovld_access(best);
    return best;
}

Binder *class_has_ctor(TagBinder *cl, TypeExpr *t, const Expr *e, int pick_best)
{   return class_has_ctor_1(cl, t, e, pick_best, NO);
}

static int compute_match_value(OvldCandidate *c, TypeExpr *t, const Expr *e,
        int arg_is_this, int convfn_is_OK, int is_lvalue)
{   Binder *btry = c->binder;

    if (c->fnarg == 0)
        /* and anything matches a '...', but only very weakly...        */
        return MATCH_VARIADIC;
    else
    {   TypeExpr *f = prunetype(c->fnarg->fttype);
        t = prunetype(t);
        if (arg_is_this && (bindstg_(btry) & b_memfna))
        {   if (h0_(f) != t_content)
                syserr("overload: what sort of 'this' is this?");
/* make an X& actual 'this' overload-match an (X *) formal 'this'.      */
/* also make an X actual '*this' overload macth an (X *) formal...      */
            if (h0_(t) == t_ref || isclasstype_(t)) f = typearg_(f);
        }
/* function types (in arg lists) either match exactly or not at all.    */
        if (h0_(t) == t_ovld)
        {   BindList *p;
            if (h0_(f) == t_content) f = typearg_(f);
            for (p = typeovldlist_(t); p != NULL; p = cdr_(p))
                if (equivtype(f, bindtype_(p->bindlistcar))) break;
            if (p != 0) return MATCH_1;
            else if (istypevar(f)) return MATCH_TYPEVAR;
        }
/* conversion of T& <-> T does not affect the match value...            */
/* Note that there are no refs to functions so delaying to here is OK.  */
        if (h0_(f) == t_ref)
        {   /* Throw out cases where reference init. is impossible */
            if (!(qualifiersoftype(typearg_(f)) & bitoftype_(s_const)) &&
                !is_lvalue) return NO_MATCH;
            f = prunetype(typearg_(f));
        }
        if (h0_(t) == t_ref) t = prunetype(typearg_(t));

/* Exact match - some trivial conversions make is slightly worse.       */
        {   SET_BITMAP qt = qualifiersoftype(t);
            SET_BITMAP qf = qualifiersoftype(f);
            TypeExpr *tt = princtype(t);
            TypeExpr *ff = princtype(f);
            if (h0_(tt) == t_content && h0_(ff) == t_content)
            {   tt = typearg_(tt);  qt = qualifiersoftype(tt);
                ff = typearg_(ff);  qf = qualifiersoftype(ff);
/* The following line is needed - e.g. in typedef struct S {f()} T;     */
/* T t; return T->f() - we need equality between T* and S*...           */
                tt = princtype(tt); ff = princtype(ff);
            }
            if (qualfree_equivtype(tt, ff))
                return (qt == qf) ? MATCH_1 : SLIGHTLY_WORSE_THAN(MATCH_1);
            else if (istypevar(tt) || istypevar(ff))
                return MATCH_TYPEVAR;
        }

/* Match with promotions - integral promotions, float->double and       */
/* trivial conversions are best...                                      */
        {   TypeExpr *ff = princtype(promoted_formaltype(f));
            TypeExpr *tt = princtype(promoted_formaltype(t));
            if (h0_(ff) == s_typespec && h0_(tt) == s_typespec)
            {   SET_BITMAP fm = typespecmap_(ff) & ~CVBITS;
                SET_BITMAP em = typespecmap_(tt) & ~CVBITS;
                if (fm == em && typespectagbind_(f) == typespectagbind_(t) ||
                        !(fm & ENUMORCLASSBITS) && !(em & CLASSBITS))
                {   /* exact or arithmetic conversion */
                    return MATCH_2;
                }
/* now match with conversions, a subtle distinction for arithmetic vals */
                if ((fm & (bitoftype_(s_int)|bitoftype_(s_double))) &&
                        (em & (bitoftype_(s_int)|bitoftype_(s_double)))
                        ||
                        (fm & CLASSBITS) && (em && CLASSBITS) &&
                        (derivation_level = 0, type_derived_from(f, t)))
                    return MATCH_2_B - derivation_level;
            }
        }

/* now match with conversions for pointer types...                      */
        if (h0_(f) == t_content && h0_(t) == t_content)
        {   SET_BITMAP qt, qf;
            int match = NO_MATCH;
            f = typearg_(f);  qf = qualifiersoftype(f);
            t = typearg_(t);  qt = qualifiersoftype(t);
            if ((h0_(f) == s_coloncolon) && (h0_(t) == s_coloncolon) &&
                qualfree_equivtype(princtype(typearg_(f)), princtype(typearg_(t))))
            {   TypeExpr *tmp = t;
                t = tagbindtype_(typespectagbind_(f)),
                f = tagbindtype_(typespectagbind_(tmp));
            }
            if ((derivation_level = 0, type_derived_from(f, t)))
                match = MATCH_3 - (2*derivation_level);
            else if (qualfree_equivtype(f, te_void) ||
                    HasFeature(Feature_CFront) &&
                    cfront_allows_pointercast(t, f))
                match = MATCH_3_V;
            else if (istypevar(t) || istypevar(f))
                match = MATCH_TYPEVAR;
            return (qt == qf) ? match : SLIGHTLY_WORSE_THAN(match);
        }
        else if (h0_(f) == t_content && e != NULL && isnullptrconst(e))
            return MATCH_3;
        else if (arg_is_this)
        {   if (isclasstype_(t) && isclasstype_(f) &&
                typespectagbind_(t) == core_class(typespectagbind_(f)))
                return MATCH_1;
        }
        else if (convfn_is_OK /* && !arg_is_this */)
/* finally, match with user-defined conversions - but never via 'this'  */
/* or if invoked recursively via class_has_{conversion,ctor}.           */
        {   if (isclasstype_(t) &&
                    class_has_conversion(typespectagbind_(t),
                        prunetype(c->fnarg->fttype), NO))
            {   /* a direct match is always better than others */
                return (conv_matchval == MATCH_1) ? MATCH_4 : SLIGHTLY_WORSE_THAN(MATCH_4);
            }
            if (isclasstype_(f) &&
                    class_has_ctor(typespectagbind_(f), t, e, NO))
                return MATCH_4;
        }
        if (istypevar(t) || istypevar(f))
            return MATCH_TYPEVAR;
        else
            return NO_MATCH;
    }
}

#define is_derived_match_(i)    (i<=MATCH_3 && MATCH_4<i)
#define MAX_NO_ARGS 32
Binder *ovld_reduce(Binder *b, List *candidates, ExprList *l, ExprList *ll)
{   /* if there is only one candidate we take it as the best match even though
       it may not match -- this gives us better error messages */
    if (cdr_(candidates) != 0 || h0_(b) == s_init)
    {   List *c, *prev, *next;
        ExprList *p;
        int best_match_vec[MAX_NO_ARGS];
        TypeExpr *type_arg_vec[MAX_NO_ARGS];
        bool is_lvtype_vec[MAX_NO_ARGS];
        int max_arg_info = -1;

        for (prev = 0, c = candidates; c != 0; c = next)
        {   int candidate_match_vec[MAX_NO_ARGS];
            bool better = NO, worse = NO, failed_match = NO;
            OvldCandidate *x = candidate_(c);
            FormTypeList *btryfnargs = x->fnarg;
            int nargs = 0;

            for (p = ll; p != 0; p = cdr_(p), ++nargs)
            {   Expr *e = exprcar_(p);
                Binder *btry = x->binder;
                int arg_is_this = (p == ll) && (l != ll);
                TypeExpr *etype;
                int is_lvt;
                int matchval;

                if (nargs > MAX_NO_ARGS)
                {   cc_rerr(sem_rerr_too_many_args_ovld);
                    cdr_(ll) = 0;
                    break;
                }

        /* builtin and global operators have no 'this' pointer... unconditionally.     */
                if (h0_(btry) != s_binder || !(bindstg_(btry) & (b_memfna|b_memfns)))
                    arg_is_this = 0;

                if (max_arg_info < nargs)
                {   best_match_vec[nargs] = (nargs == 0 && ll != l) ?
                        MATCH_VARIADIC : NO_MATCH;
                    etype = type_arg_vec[nargs] =
                        modify_actualtype(typeofexpr(e), e);
                    is_lvt = is_lvtype_vec[nargs] = lvalue_type(e) != NULL;
                    ++max_arg_info;
                    if (max_arg_info != nargs)
                        syserr("ovld_reduce: %d, %d", max_arg_info, nargs);
                }
                else
                {   etype = type_arg_vec[nargs];
                    is_lvt = is_lvtype_vec[nargs];
                }

                /* static member functions match 'this' is a special way...     */
                if (arg_is_this && (bindstg_(btry) & b_memfns))
                    matchval = MATCH_THIS;
                else
                    matchval = compute_match_value(x, etype, e, arg_is_this,
                                                   YES, is_lvt);
                if (matchval == NO_MATCH)
                {   failed_match = YES;
                    if (var_cc_private_flags & 16384)
                        cc_msg("$b  arg %d  failed match\n",
                               candidate_(c)->binder, nargs+1);
                    break;
                }
                candidate_match_vec[nargs] = matchval;
                if (matchval != MATCH_THIS && x->fnarg != 0)
                    x->fnarg = cdr_(x->fnarg);
            }
            x->fnarg = btryfnargs;
            if (!failed_match)
            {   FormTypeList *bestfnargs = (prev) ? candidate_(prev)->fnarg : 0;
                int i = 0, len;
                len = length(ll);
                for (; i < len; ++i)
                {
                    if (bestfnargs && btryfnargs)
                    {   TypeExpr *t1 = btryfnargs->fttype,
                                 *t2 = bestfnargs->fttype;
                        bestfnargs = cdr_(bestfnargs);
                        btryfnargs = cdr_(btryfnargs);
                        if (is_derived_match_(candidate_match_vec[i]) &&
                             is_derived_match_(best_match_vec[i]) &&
                             h0_(t1) == h0_(t2) && (h0_(t1) == t_content ||
                                h0_(t1) == t_ref) &&
                                !(t1 = typearg_(t1), t2 = typearg_(t2),
                                isvoidtype(t1) || isvoidtype(t2) ||
                                qualfree_equivtype(t1, t2) ||
                                type_derived_from(t1, t2) ||
                                type_derived_from(t2, t1)))
                        {   if (var_cc_private_flags & 16384)
                                cc_msg("$b arg %d not comparable to current best's\n",
                                    x->binder, i+1);
                            continue;
                        }
                    }
                    /* Can there be MATCH_THIS other than i == 0? Over-zealous. */
                    if (i == 0 && candidate_match_vec[i] == MATCH_THIS)
                    {   if (var_cc_private_flags & 16384)
                            cc_msg("skipped 'this' pointer for static fn $b\n",
                                   candidate_(c)->binder);
                        continue;
                    }
                    if (var_cc_private_flags & 16384)
                        cc_msg("$b  arg %d  match value = %3d vs. %3d",
                            candidate_(c)->binder, i+1, candidate_match_vec[i],
                                best_match_vec[i]);
                    if (candidate_match_vec[i] > best_match_vec[i])
                    {   better = YES;
                        if (var_cc_private_flags & 16384) cc_msg(" -> better");
                    }
                    else if (candidate_match_vec[i] < best_match_vec[i])
                    {   worse = YES;
                        if (var_cc_private_flags & 16384) cc_msg(" -> worse");
                    }
                    if (var_cc_private_flags & 16384) cc_msg("\n");
                }
            }
            /* elimination phrase: the best match candidates, if any, are always
               at the top of the list */
            if (failed_match || (!better && worse))
            {   /* discarded */
                if (var_cc_private_flags & 16384)
                    cc_msg("   dropped $b\n", candidate_(c)->binder);
                if (h0_(candidate_(c)->binder) != s_binder)
                    (void) discard3(candidate_(c)->binder);
                next = ocl_discard(c);
                if (prev != 0) cdr_(prev) = next; else candidates = next;
            }
            else if (better && !worse)
            {   /* displaced (the lot) */
                int i = 0;
                for (; i < length(ll); ++i)
                    best_match_vec[i] = candidate_match_vec[i];
                if (var_cc_private_flags & 16384)
                    cc_msg("   best so far is $b\n", candidate_(c)->binder);
                candidates = c;
                prev = c;
                next = cdr_(c);
            }
            else
            {   /* retained */
                if (var_cc_private_flags & 16384)
                    cc_msg("   retaining $b\n", candidate_(c)->binder);
                prev = c;
                next = cdr_(c);
            }
        }
        for (c = candidates; c != 0; c = cdr_(c))
        {   OvldCandidate *x = candidate_(c);
            if (h0_(x->binder) != s_binder)
                while (x->fnarg) x->fnarg = (FormTypeList *)discard3(x->fnarg);
        }
    }
    {   Binder *bmatch = (Binder *)errornode;
                                              /* inhibit cascade errors */
        if (candidates == 0)
        {   if (h0_(b) == s_binder)
                cc_err(syn_err_incomp_arg_ovld, b);
            else
                bmatch = 0;                        /* allowable failure */
        }
        else
        {   /* Prefers the non-template version */
            if (length(candidates) == 2 && h0_(b) == s_binder &&
                (bindenv_(candidate_(candidates)->binder) ||
                 bindenv_(candidate_(cdr_(candidates))->binder)))
            {   if (bindenv_(candidate_(candidates)->binder) == NULL)
                {   (void)ocl_discard(cdr_(candidates));
                    cdr_(candidates) = NULL;
                } else
                    candidates = ocl_discard(candidates);
            }

            if (cdr_(candidates) != 0 &&
                (bindparent_(b) == NULL ||
                 !(tagbindbits_(bindparent_(b)) & TB_TEMPLATE)))
            {   int n = length(candidates);
                if (h0_(b) == s_binder)
                    cc_err(syn_err_multi_overload_call, n, b);
                else
                    cc_err(syn_err_multi_operator_ovld, n, h0_(b));
            }
            else
            {   bmatch = candidate_(candidates)->binder;
                /* beware pseudo-fns for builtin operators... */
                if (h0_(bmatch) == s_binder) chk_ovld_access(bmatch);
            }
        }
/* clean up any remaining detritus...                                   */
        while (candidates) candidates = ocl_discard(candidates);
        return bmatch;
    }
}

Binder *ovld_resolve(Binder *b, BindList *alternatives,
                     ExprList *l, ExprList *ll, bool silent)
{   int nargs;
    List *candidates;
/* Don't even try for overload resolution if previous (hard) error.     */
    {   ExprList *p = ll;       /* always contains all of 'l'.          */
        for (nargs = 0;  p != 0;  nargs++, p = cdr_(p))
            if (h0_(exprcar_(p)) == s_error) return (Binder *)errornode;
    }
    if ((candidates = mk_candidates(alternatives, nargs, (l != ll), 0)) == 0)
    {   Binder *b = (Binder *)errornode;
        if (!silent)
        {   if (alternatives != NULL && cdr_(alternatives) == NULL)
                b = alternatives->bindlistcar;  /* wrong # args reported by sem */
            else if (!silent)
                cc_err(syn_err_wrong_args_ovld, b);
        }
        return b;
    }
    return ovld_reduce(b, candidates, l, ll);
}

/* End of cfe/overload.c */
