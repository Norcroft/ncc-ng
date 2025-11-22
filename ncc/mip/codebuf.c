/*
 * C compiler file codebuf.c.
 * Copyright (C) Codemist Ltd, 1988-1992.
 * Copyright (C) Acorn Computers Ltd., 1988-1990.
 * Copyright (C) Advanced RISC Machines Limited, 1990-1992.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$ Codemist 30
 * Checkin $Date$
 * Revising $Author$
 */

/* Memo to AM: 1. tidy up mustlitby interface (only arm uses so far).      */
/*             also observe 2 "transsex compilation worry"s (AM check).    */
/* AM Dec 90: remove much BSS code since now unified in mip/bind.c         */
/* AM May 89: remove packing of (24 bit) pointer and LIT_xxx flags.        */
/* All 'aux' fields below are ONLY for producing nicely formatted asm --   */
/* they are NOT to be used for object output for which code_flag_ is still */
/* appropriate.                                                            */
/* AM July 88: elide setlabel(litlab) if empty pool (space/asm listing).   */
/* AM June 88: bug fix: move call to optimise_code() to gen.c case ENDPROC */
/* AM April 88:  change codeseg_flush interface with vargen.c          */
/* AM 10-oct-86: this file contains (hopefully) machine independent
   code buffering routines, literal buffering etc.
*/

/* Memo: should we conditionally (TARGET_IS_ARM) compile count_name et al? */

/* exports - for reading only: codebase, codep, litpoolp */

#ifdef __STDC__
#  include <string.h>
#else
#  include <strings.h>
#endif
#include "globals.h"
#include "codebuf.h"
#include "cgdefs.h"
#include "store.h"
#include "xrefs.h"
#include "bind.h"           /* for sym_insert_id in ACW case, and ARM case */
#include "builtin.h"        /* for codesegment */
#include "util.h"
#include "mcdep.h"
#include "errors.h"
#include "aeops.h"          /* bitofstg_ */

#ifdef PUT_FILE_NAME_IN_AREA_NAME
#  include "fname.h"
#  include "compiler.h"
#endif

static DataDesc data, *datap, extable, exhandler;
#ifdef CONST_DATA_IN_CODE
static DataDesc constdata;         /* ensure not used by accident                */
#endif

ExceptionEnv *currentExceptionEnv;

int32 code_area_idx;        /* exported for armcc -S -ZO ... */

static bool codebuf_inroutine;

/* codeloc and codeseg_flush added by AM (to old emit.c),
   *** probably in a silly position ***
   The idea is that declarations of the form 'static char *a = "abc";'
   put "abc" in the code segment and just put a pointer in the data
   segment (it is as non modifyable as other strings)  */

/* codeandflagvec and codeasmauxvec are doubly indexed by a BYTE address: */
struct CodeAndFlag *codeandflagvec[CODEVECSEGMAX];

#ifndef NO_ASSEMBLER_OUTPUT     /* i.e. lay off otherwise */
VoidStar (*(codeasmauxvec[CODEVECSEGMAX])) [CODEVECSEGSIZE];
#endif // !NO_ASSEMBLER_OUTPUT

static int32 codeveccnt;
int32 codebase, codep;
static int32 maxprocsize;
static char *maxprocname;

/* litpool is of fixed size (LITPOOLSEGMAX*LITPOOLSEGSIZE),                */
/* but with overflow taken care of.                                        */
typedef struct {
    int32 val, type; Symstr *xref;
    VoidStar litaux;      /* Only used #ifndef NO_ASSEMBLER_OUTPUT         */
                          /* Could in principle share with xref field?     */
} LitPoolEntry;
static LitPoolEntry (*(litpool[LITPOOLSEGMAX]))[LITPOOLSEGSIZE];
#define litpool_(n) (*litpool[(n)>>LITPOOLSEGBITS])[(n)&LITPOOLSEGSIZE-1]
static int32 litveccnt;
static int32 litalign;
int32 litpoolp;

LabelNumber *litlab;
static int32 next_label_name;

LabList *asm_lablist;         /* @@@ This is not really part of codebuf */
                              /* One day it might join obj_symref in    */
                              /* here as "gen/obj/asm support.          */

/* For the sake of a cleaner separation between the FE and the BE       */
DataInit *get_datadesc_ht(bool head)
{   return (head) ? datap->head : datap->tail;
}

void set_datadesc_ht(bool head, DataInit *val)
{   if (head) datap->head = val; else datap->tail = val;
}

int32 get_datadesc_size(void)
{   return datap->size;
}

void set_datadesc_size(int32 val)
{   datap->size = val;
}

DataXref *get_datadesc_xrefs(void)
{   return datap->xrefs;
}

void set_datadesc_xrefs(DataXref *val)
{   datap->xrefs = val;
}

int get_datadesc_xrarea(void)
{   return datap->xrarea;
}

void set_datadesc_xrarea(int val)
{   datap->xrarea = val;
}

DataDesc *get_datadesc(void)
{   return datap;
}

void copy_datadesc(DataDesc *dest)
{   *dest = data;
}

void restore_datadesc(DataDesc *src)
{   data = *src;
}

int32 data_size(void)
{   return data.size;
}

DataInit *data_head(void)
{   return data.head;
}

DataXref *data_xrefs(void)
{   return data.xrefs;
}

DataInit *get_extable_ht(bool head)
{   return (head) ? extable.head : extable.tail;
}

void set_extable_ht(bool head, DataInit *val)
{   if (head) extable.head = val; else extable.tail = val;
}

void set_extable_size(int32 val)
{   extable.size = val;
}

int32 extable_size(void)
{   return extable.size;
}

DataInit *extable_head(void)
{   return extable.head;
}

DataXref *extable_xrefs(void)
{   return extable.xrefs;
}

bool is_extable(void)
{   return (datap == &extable);
}

DataInit *get_exhandler_ht(bool head)
{   return (head) ? exhandler.head : exhandler.tail;
}

void set_exhandler_ht(bool head, DataInit *val)
{   if (head) exhandler.head = val; else exhandler.tail = val;
}

void set_exhandler_size(int32 val)
{   exhandler.size = val;
}

int32 exhandler_size(void)
{   return exhandler.size;
}

DataInit *exhandler_head(void)
{   return exhandler.head;
}

DataXref *exhandler_xrefs(void)
{   return exhandler.xrefs;
}

bool is_exhandler(void)
{   return (datap == &exhandler);
}

#ifdef CONST_DATA_IN_CODE
int32 constdata_size(void)
{   return constdata.size;
}

DataInit *constdata_head(void)
{   return constdata.head;
}

DataXref *constdata_xrefs(void)
{   return constdata.xrefs;
}

bool is_constdata(void)
{   return (datap == &constdata);
}

DataAreaSort SetDataArea(DataAreaSort sort) {
    DataAreaSort oldsort = is_constdata() ? DS_Const : DS_ReadWrite;
    if (sort == DS_Const)
        datap = &constdata;
    else if (sort == DS_ReadWrite)
        datap = &data;
    return oldsort;
}

#else

DataAreaSort SetDataArea(DataAreaSort sort) {
    datap = &data;
    return DS_ReadWrite;
}

#endif

/* obj/asm calls totargetsex() to get host word (as used internally     */
/* in the compiler) into target sex for asm output or object file.      */
/* It acts as a no-op if host sex is the same as target sex.            */
int32 totargetsex(int32 w, int flag)
{   /* casts in next lines ensure host byte sex independence */
    unsigned8 *pb = (unsigned8 *)&w;
    unsigned16 *ph = (unsigned16 *)&w;
    typedef unsigned32 u;
    if (target_lsbytefirst == host_lsbytefirst) return w;  /* short cut */
#ifdef TARGET_HAS_HALFWORD_INSTRUCTIONS
    if (flag == LIT_OPCODE) flag = LIT_HH;
#endif
#ifdef TARGET_HAS_BYTE_INSTRUCTIONS
    if (flag == LIT_OPCODE) flag = LIT_BBBB;
#endif
    switch (flag)
    {
default:        syserr(syserr_totarget, flag); return w;

case LIT_BXXX:
case LIT_BBX:
case LIT_BBBX:
case LIT_BBBB:  return target_lsbytefirst ?
                       (u)pb[0] | (u)pb[1]<<8 | (u)pb[2]<<16 | (u)pb[3]<<24 :
                       (u)pb[0]<<24 | (u)pb[1]<<16 | (u)pb[2]<<8 | (u)pb[3];
case LIT_HH:    return target_lsbytefirst ?
                       (u)ph[0] | (u)ph[1]<<16 :
                       (u)ph[0]<<16 | (u)ph[1];
case LIT_BBH:   return target_lsbytefirst ?
                       (u)pb[0] | (u)pb[1]<<8 | (u)ph[1]<<16 :
                       (u)pb[0]<<24 | (u)pb[1]<<16 | (u)ph[1];
case LIT_HX:
case LIT_HBX:
case LIT_HBB:   return target_lsbytefirst ?
                       (u)ph[0] | (u)pb[2]<<16 | (u)pb[3]<<24 :
                       (u)ph[0]<<16 | (u)pb[2]<<8 | (u)pb[3];

#ifdef THUMB_CPLUSPLUS
case LIT_OPCODE_32:
#endif
case LIT_OPCODE:
case LIT_RELADDR:
case LIT_NUMBER:
case LIT_ADCON:
case LIT_FPNUM:
case LIT_FPNUM1:
case LIT_FPNUM2:
case LIT_INT64_1:
case LIT_INT64_2:
                return w;
    }
}

static void adddata1(DataInit *x)
{
#ifndef FORTRAN /* blows up f77 formats, which aren't aligned -- MRC.   */
/* AM thinks this is because fortran currently puts out non-aligned labels */
    if (datap->wpos != 0) syserr(syserr_vg_wpos, (long)datap->wpos);  /* consistency */
#endif
    if (datap->head == 0) datap->head = datap->tail = x;
    else datap->tail->datacdr = x, datap->tail = x;
}

static void adddata(DataInit *a, int32 b, int32 c, IPtr d, IPtr e)
{   DataInit *x = (DataInit *) GlobAlloc(SU_Data, sizeof(DataInit));
    x->datacdr = a, x->rpt = b, x->sort = c, x->len = d, x->val = e;
    adddata1(x);
}

/* (sizeof_ptr == 2) or unaligned */
/* This routine outputs a LIT_BBX or LIT_HX just before a LIT_ADCON in   */
/* the case where pointers are 2 bytes long.  In this case not all data  */
/* initialisations can be bundled into units of 4 bytes.                 */
/* Maybe this code is useful for APRM too?                               */
static void vg_wflush(void)
{   unsigned bytes = datap->wpos & 3;
    if (bytes != 0)
    {   int lit_flag;
        switch (datap->wtype)
        {   default:  syserr(syserr_vg_wflush, datap->wtype);
            case 1:  lit_flag = bytes == 1 ? LIT_BXXX : LIT_HX;  break;
            case 3:  lit_flag = bytes == 2 ? LIT_BBX  : LIT_HBX; break;
            case 7:  lit_flag = LIT_BBBX;    break;
        }
        switch (bytes) {
            case 1:  datap->wbuff.w8[1] = 0;
            case 2:  datap->wbuff.w16[1] = 0; break;
            case 3:  datap->wbuff.w8[3] = 0;
        }
        datap->wpos = 0, datap->wtype = 0;
        adddata(0, 1, lit_flag, bytes, datap->wbuff.w32[0]);
    }
}

void gendcI_a(int32 len, int32 val, bool aligned)
{
    if (debugging(DEBUG_DATA))
        cc_msg("%.6lx:   DC FL%ld'%ld'\n",
               (long)datap->size, (long)len, (long)val);
#if (alignof_int < 2)
  #error alignof_int unexpectedly low     /* cross sex code fails */
#endif
    if (len == 8)               /* temporary code */
    {   if (target_lsbytefirst) gendcI(4, val), gendcI(4, 0);
                           else gendcI(4, 0), gendcI(4, val);
        return;
    }
    if (datap->wpos & (len-1)) vg_wflush();
    if ((len != 1 && len != 2 && len != 4) ||
        (aligned && (datap->wpos & len-1 & alignof_int-1)))
        /* check consistent - includes integral alignment */
        syserr(syserr_gendcI, (long)len, (long)datap->wpos);


    switch (len)
    {   case 1: datap->wbuff.w8[datap->wpos] = (unsigned8)val; break;
        case 2: datap->wbuff.w16[datap->wpos>>1] = (unsigned16)val; break;
        case 4: datap->wbuff.w32[0] = val; break;
    }
    datap->wtype = (datap->wtype << len) | 1;    /* flag 'byte' boundaries */
    datap->wpos += (unsigned)len;
    if (datap->wpos == 4)
    {   int32 lit_flag;
/* the following values could be coded into the LIT_xxx values             */
        switch (datap->wtype)
        {   default:  syserr(syserr_vg_wtype, datap->wtype);
            case 1:  lit_flag = LIT_NUMBER; break;
            case 5:  lit_flag = LIT_HH;     break;
            case 15: lit_flag = LIT_BBBB;   break;
            case 7:  lit_flag = LIT_HBB;    break;
            case 13: lit_flag = LIT_BBH;    break;
        }
        datap->wpos = 0, datap->wtype = 0;
        adddata(0, 1, lit_flag, 4, datap->wbuff.w32[0]);
    }
    datap->size += len;
}

void gendcE(int32 len, FloatCon *val)
{   vg_wflush();                /* only if sizeof_ptr == 2 */
    adddata(0, 1, LIT_FPNUM, len, (IPtr)val);
    if (debugging(DEBUG_DATA))
    { cc_msg("%.6lx:  ", (long)datap->size);
      { int32 *p = val -> floatbin.irep;
        cc_msg(" %.8lx", (long)p[0]);
        if (len == 8) cc_msg(" %.8lx", (long)p[1]);
        cc_msg(" DC %ldEL%ld'%s'\n", (long)1, (long)len, val -> floatstr);
      }
    }
    datap->size += len;
}

#ifdef TARGET_CALL_USES_DESCRIPTOR
void gendcF(Symstr *sv, int32 offset)
{   /* (possibly external) function name + (illegal) offset */
    if (offset != 0) cc_err(vargen_err_badinit, sv, offset);
    (void)obj_symref(sv, xr_code, 0);
    datap->xrefs = (DataXref *) global_list3(SU_Xref, datap->xrefs, datap->size, sv);
    vg_wflush();                /* only if sizeof_ptr == 2 */
    adddata(0, 1, LIT_FNCON, (int32)sv, offset);
    if (debugging(DEBUG_DATA))
        cc_msg("%.6lx:   DC FNA(%s+%ld)\n",
               (long)datap->size, symname_(sv), (long)offset);
    datap->size += sizeof_ptr;
}

static int32 fnconlab;

int32 genfncon(Symstr* sv)
{   int32 d = datap->size;
    Symstr *ss;
    char s[20];
    sprintf(s, "_FNC%ld", fnconlab++);
    ss = sym_insert_id(s);
    labeldata(ss);
    (void)obj_symref(ss, xr_data+xr_defloc, d);
    gendcF(sv, 0);
    return d;
}

#endif /* TARGET_CALL_USES_DESCRIPTOR */

void gendcAX(Symstr *sv, int32 offset, int xrflavour)
{   /* (possibly external) name + offset, flavour is xr_data or xr_code */
    (void)obj_symref(sv, xrflavour, 0);
#ifdef TARGET_IS_RISC_OS
    /* This could be a more generally useful re-entrancy type fragment. */
    if (arthur_module && (xrflavour & xr_data))
       cc_rerr(vargen_rerr_datadata_reloc, sv);
#endif
    if (sizeof_ptr == 8 && !target_lsbytefirst) gendcI(4, 0);

    datap->xrefs = (DataXref *) global_list3(SU_Xref, datap->xrefs, datap->size, sv);
    vg_wflush();                /* only if sizeof_ptr == 2 */
    adddata(0, 1, LIT_ADCON, (IPtr)sv, offset);
    if (debugging(DEBUG_DATA))
        cc_msg("%.6lx:   DC A(%s+%ld)\n",
               (long)datap->size, symname_(sv), (long)offset);
    if (sizeof_ptr == 8 && target_lsbytefirst)
/* As what may be a short-term expedient I will leave the gendcI to my caller */
        datap->size += sizeof_ptr-4 /* , gendcI(4, 0) */;
    else
        datap->size += sizeof_ptr;
}

void gendc0(int32 nbytes)
{   if (debugging(DEBUG_DATA))
        cc_msg("%.6lx:   DC %ldX'00'\n", (long)datap->size, (long)nbytes);
    while (nbytes != 0 && datap->wpos != 0) gendcI(1,0), nbytes--;
    if ((nbytes>>2) != 0)
        adddata(0, nbytes>>2, LIT_NUMBER, 4, 0);
    while (nbytes & 3) gendcI(1,0), nbytes--;
    datap->size += nbytes;
}

void vg_genstring(StringSegList *p, int32 size, int pad)
{
    int32 planted = 0;
    for (; p != 0; p = p->strsegcdr)
    {   unsigned char *s = (unsigned char *)p->strsegbase;
        int32 n = p->strseglen;
        while (n-- > 0)
        {   if (planted < size)
                gendcI(1,*s++), planted++;
            else
                return;
        }
    }
    if (planted < size)
    {   if (pad == 0)
            gendc0(size-planted);
        else while (planted++ < size)
            gendcI(1, pad);
    }
}

void padstatic(int32 align)
{
    if (datap->size & (align-1)) gendc0((-datap->size) & (align-1));
    if (align == 4) vg_wflush();
}

void labeldata(Symstr *s)
{
    vg_wflush();                /* only if sizeof_ptr == 2 */
    if (asmstream != NULL       /* nasty space-saving hack */
        && s != NULL)           /* labeldata(NULL) provides access to vg_wflush() externally */
        adddata1((DataInit *)global_list5(SU_Data, (DataInit *)0, s, LIT_LABEL, 0, 0));
}

/* The following procedure is used to delete trailing zeros in
 * auto structs, unions and arrays. It carries a PLG Heath Warning !!
 * In short it just (optionally) hacks the trailing zeros off the last
 * static data item defined.  AM has (partly) house trained it.
 * 'previous' should be the place preceeding where to start searching
 * for zeros -- i.e. data.tail before call or 0 if no previous statics.
 * AM: maybe we should hold datainit backwards and then this code
 * would be nearly trivial, but compatibility problems.
 * Note that it currently misses floating point zeros.
 */

int32 trydeletezerodata(DataInit *previous, int32 minsize)
{   int32 size = 0;
    DataInit *p,*q = previous;
    for (p = q ? q->datacdr : datap->head; p; p = p->datacdr)
        switch (p->sort)
        {   case LIT_BBBB: case LIT_HH: case LIT_BBH: case LIT_HBB:
            case LIT_NUMBER:
                if (p->val == 0) { size += p->rpt * 4; break; }
                /* else drop through */
            default:
                size = 0, q = p;
        }
    if (size >= minsize)
    {   if (q==0) datap->head = 0; else datap->tail=q, q->datacdr=0;
        datap->size -= size;
        return size;
    }
    return 0;
}

void show_entry(Symstr *name, int flags)
{   /* slightly specious for a routine, but tail recursion is free */
    (void)obj_symref(name, flags, codebase);
}

void show_code(Symstr *name)
{   if (name == NULL && codep == 0) return;
#ifndef NO_ASSEMBLER_OUTPUT
    if (asmstream) display_assembly_code(name);
#endif
#ifndef NO_OBJECT_OUTPUT
    if (objstream) obj_codewrite(name);
#endif
/* test name to avoid counting char *s = "abc"-like things. */
    if (name != NULL)
    {   if (codep > maxprocsize)
        {   maxprocsize = codep;
            maxprocname = symname_(name);
        }
    }
    codebase += codep;
    codep = 0;               /* for static init by string constants */
}

LabelNumber *nextlabel(void)
{
    LabelNumber *w = (LabelNumber *) BindAlloc(sizeof(LabelNumber));
    w->block = (BlockHead *) DUFF_ADDR;  /* unset label - illegal ptr */
    w->u.frefs = NULL;             /* no forward refs yet              */
    w->name = next_label_name++;   /* name + union discriminator for u */
    return w;
}

void outcodeword(int32 w, int32 f)      /* macro soon? */
{   outcodewordaux(w, f, 0);
}

void outcodewordaux(int32 w, int32 f, VoidStar aux)
{
#ifndef TARGET_IS_NULL
    int32 q = codep;    /* byte address */
/* ECN: q+2 below allows q to be halfword aligned */
    if (((q+2) >> (2+CODEVECSEGBITS)) >= codeveccnt)
    {   if (codeveccnt >= CODEVECSEGMAX) syserr(syserr_codevec);
#ifndef NO_ASSEMBLER_OUTPUT
/* Only set up codeasmauxvec to store aux items if asmstream is active. */
        codeasmauxvec[codeveccnt] = (VoidStar (*)[CODEVECSEGSIZE]) (
            asmstream ? BindAlloc(sizeof(*codeasmauxvec[0])) : DUFF_ADDR);
#endif // !NO_ASSEMBLER_OUTPUT
        codeandflagvec[codeveccnt] =
            (struct CodeAndFlag *) BindAlloc(sizeof(*codeandflagvec[0]));
#ifdef TARGET_HAS_HALFWORD_INSTRUCTIONS
/* ECN: If we have halfword instructions a codeandflagvec object may contain
 *      either a word (represented as two halfwords with a single flag) or
 *      a halfword. If it is a word we must ensure that the flag for the
 *      second halfword contains 0.
 */
        memset(codeandflagvec[codeveccnt], 0, sizeof(*codeandflagvec[0]));
#endif
        codeveccnt++;
    }
    set_code_inst_(q,w);
    code_flag_(q) = (CodeFlag_t)f;
#ifndef NO_ASSEMBLER_OUTPUT
    if (asmstream) code_aux_(q) = aux;
#endif
    codep += 4;
#else
    IGNORE(f); IGNORE(w); IGNORE(aux);
#endif
}

int32 codeloc(void)
{
    /* for the use of vargen.c: but consider rationalisation later */
    return codebase + codep + litpoolp*4;
}

int32 lit_findadcon(Symstr *name, int32 offset, int32 wherefrom)
/* looks for a previous adcon literal from wherefrom to codebase+codep */
/* returns a byte address from wherefrom to codebase+codep or -1       */
{   CodeXref *x;
    for (x = codexrefs; x!=NULL; x = x->codexrcdr)
    {   if (x->codexrsym == name)
        {   int32 k = x->codexroff;
/* See comments later in this file re x->codexrlitoff with X_backaddrlit    */
            if ((k & 0xff000000)==X_backaddrlit && x->codexrlitoff==offset)
            {   /* adcon already in memory at byte address k */
                k &= 0x00ffffff;
                return (k >= wherefrom ? k : -1);
            }
        }
    }
    return -1;
}

static char *count_name_table[16];
static int count_name_pointer;

int lit_of_count_name(char *s)
{
/* This records an index number for each of the most recent few source     */
/* files used in the current compilation. These numbers are used with      */
/* the count option as enabled by the -K command-line option.              */
    int i;
    for (i = 0; i < count_name_pointer; i++)
       if (strcmp(s, count_name_table[i]) == 0) return i;
    i = count_name_pointer++;
/* The next line duplicates ACN's functionality, should be OK as J_COUNT   */
/* should always be incode (arg to dumplits2()).                           */
    if (i >= 16) dumplits2(YES), i = count_name_pointer++;
    count_name_table[i] = s;
    return i;
}

void dump_count_names(void)
{
    int i;
    if (count_name_pointer == 0) return;
    outcodeword(0xfff12340 | (count_name_pointer - 1L), LIT_NUMBER);
    for (i = 0; i<count_name_pointer; i++)
    {   char *file_name = count_name_table[i];
        StringSegList x;
        x.strsegbase = file_name;
        x.strseglen = strlen(file_name);
        x.strsegcdr = NULL;
        codeseg_stringsegs(&x, NO);
    }
    outcodeword(0x31415926, LIT_NUMBER);
    count_name_pointer = 0;
}

typedef struct LitPool {
    struct LitPool *next;
    int32 base;   /* absolute address in code segment of pool base */
    int32 size;   /* size of pool (words) */
    LitPoolEntry entries[1]; /* really variable */
} LitPool;

#define poolbase_(p) (p)->base
#define poolsize_(p) (p)->size
#define poolentry_(p, i) (p)->entries[i]

static LitPool *prevpools;

static void dumplits_inner(void)
{
    int32 i;
    LitPool *q = (LitPool *) GlobAlloc(SU_Other, sizeof(LitPool) + (litpoolp-1)*sizeof(LitPoolEntry));
    q->next = prevpools; prevpools = q;
    poolbase_(q) = codebase + codep; poolsize_(q) = litpoolp;
    for (i=0; i<litpoolp; i++)
    {   LitPoolEntry *p = &litpool_(i);
        int32 f = p->type;
        poolentry_(q, i) = *p;

        if (f == LIT_ADCON || f == LIT_FNCON)
/* Note that xref list entries of type X_backaddrlit have an extra word  */
/* that indicates a numeric offset relative to the named symbol. This    */
/* field should ONLY be relevant when scanning to see if an existing     */
/* literal pool entry can be reused. For object file generation the      */
/* relevant offset will appear in codevec.                               */
        {   codexrefs = (CodeXref *) global_list4(SU_Xref, codexrefs,
                                     X_backaddrlit | (codebase+codep),
                                     p->xref,
                                     p->val);    /* codexrlitoff */
#ifdef TARGET_CALL_USES_DESCRIPTOR /*@@@ AM thinks useful for pcc too */
/* /* bugs here ? */
            if (f == LIT_FNCON)
                (void)obj_symref(p->xref, xr_code, 0);
            else
#endif
                (void)obj_symref(p->xref, xr_data, 0);
        }
#if defined(TARGET_IS_ARM) || defined(TARGET_IS_THUMB)
        if (f != LIT_STRING) {
            outcodewordaux(p->val, f, p->litaux);
        } else {
            int32 j;
            char b[8];

#define word_has_nullbyte(w) (((w) - 0x01010101) & ~(w) & 0x80808080)
            j = i;
            while (j<litpoolp) {
                p = &litpool_(j);
                j++;
                if (p->type != LIT_STRING || word_has_nullbyte(p->val))
                    break;
            }
            sprintf(b, "$S%ld", (j-i)*4);
            obj_symdef(sym_insert_id(b), xr_code+xr_defloc+xr_dataincode, codebase+codep);
            while (i<litpoolp) {
                p = &litpool_(i);
                poolentry_(q, i) = *p;
                outcodewordaux(p->val, p->type, p->litaux);
                i++;
                if (p->type != LIT_STRING || word_has_nullbyte(p->val))
                    break;
            }
            i--;
        }
#else
        /* transfer relocation info (if any) to the planted literal */
        outcodewordaux(p->val, f, p->litaux);
#endif
    }
    litpoolp = 0;
    localcg_newliteralpool();
    if (count_name_pointer >= 15)
        dump_count_names();    /* else will overflow next time anyway */
}

static void dumplits0(void)
{
#ifdef TARGET_HAS_HALFWORD_INSTRUCTIONS
    if ((codebase+codep) & 2) {
        if ((codep & 2) == 0) {
            outcodeword(0, LIT_OPCODE);
            codep -= 4;  /* ensure room */
            code_flag_(codep+2) = LIT_OPCODE;
        }
        code_hword_(codep) = 0;
        codep += 2;
    }
#endif
    /* ECN: Change | to + as codebase need not be aligned */
    if ((codebase+codep) & 3) syserr(syserr_dumplits);
    while (codebase+codep & litalign-1) outcodeword(0, LIT_NUMBER);
    setlabel(litlab);
    dumplits_inner();
    litlab = nextlabel();
}

void dumplits2(bool needsjump)
{   if (needsjump)
    {   LabelNumber *ll = nextlabel();
        if (litlab->u.frefs == NULL) syserr(syserr_dumplits1);
        localcg_newliteralpool();
        branch_round_literals(ll);
        /* That probably evaluated a J_B (AL) jopcode, which caused literals
         * to be dumped, so now there are none left - but the interface isn't
         * defined, so for safety we must check.
         */
        if (litpoolp != 0) dumplits0();
        setlabel(ll);
    }
    else
    {
        if (litlab->u.frefs == NULL)
        {   if (litpoolp != 0) syserr(syserr_dumplits2);
        }
        else {
            localcg_newliteralpool();
            dumplits0();
        }
    }
}

static LabelNumber *litoverflowlab;
static int32 litsincode;

/* All words between LITF_FIRST and LITF_LAST are guaranteed contiguous */
void outlitword(int32 w, int32 flavour, Symstr *sym, VoidStar aux,
                       int32 flag)
{   if (!codebuf_inroutine)
    {   /* /* Find 'codexrefs' above to see what should have been done. */
        if (flavour == LIT_ADCON) syserr(syserr_outlitword);
        outcodewordaux(w, flavour, aux);
        return;
    }
    if (flag & LITF_DOUBLE)
    {   litalign = alignof_double;      /* IEEE 16byte long double soon? */
        while ((litpoolp<<2) & litalign-1)
            outlitword(0, LIT_NUMBER, 0, (VoidStar)0,
                       (flag&LITF_INCODE)|LITF_FIRST|LITF_LAST);
    }
    if (flag & LITF_FIRST)
       litoverflowlab = 0, litsincode = flag & LITF_INCODE;
    if ((litpoolp >> LITPOOLSEGBITS) >= litveccnt)
    {   if (litveccnt < LITPOOLSEGMAX)
            litpool[litveccnt++] = (LitPoolEntry (*)[LITPOOLSEGSIZE])
                                    BindAlloc(sizeof(*litpool[0]));
        else
        {   localcg_newliteralpool();
            if (litsincode)
            {   branch_round_literals(litoverflowlab = nextlabel());
/* LDS observes that branch_round_literals() generates an unconditional */
/* branch which flushes the literal pool (currently on the ARM).        */
/* On such a target the next test never succeeds.                       */
/* AM: this is true on the ARM, but note that some targets save all     */
/* their literals to J_ENDPROC (i.e. J_B does not flush) but lots of    */
/* J_STRING opcodes may force a LITPOOLSEGMAX overflow and hence this   */
/* code to be activated.  See comment in dumplits2().                   */
                if (litpoolp != 0)
                {
                  if (litlab->u.frefs == NULL) syserr(syserr_dumplits3);
                  dumplits0();
                }
                litsincode = 0;
            }
            else dumplits_inner();
        }
    }
    {   LitPoolEntry *p = &litpool_(litpoolp);
        p->val = w, p->type = flavour, p->xref = sym, p->litaux = aux;
        litpoolp++;
    }
    if (flag & LITF_LAST)
    {   if (!litsincode) dumplits_inner();   /* if overflow then flush all */
        if (litoverflowlab) setlabel(litoverflowlab);
    }
}

static int32 lit_findword5(int32 w, int32 flavour, Symstr *sym,
                           VoidStar aux, int32 flag)
{   /* try to re-use literal in current pool */
    int32 i;
    if ((flag & LITF_FIRST+LITF_LAST+LITF_NEW) == LITF_FIRST+LITF_LAST)
      /* only re-use one word, non-NEW, literals so far */
      for (i=0; i<litpoolp; i++)
      {   LitPoolEntry *p = &litpool_(i);
          if (p->type == flavour && p->val == w && p->xref == sym)
          {   /* adcon (or other lit) available in current literal pool */
              /* if previous ref was addressable this one will be.      */
              if (p->litaux == 0) p->litaux = aux;      /* best asm.    */
              return 4*i;
          }
      }
    if (flag & LITF_PEEK) return -1;            /* just window shopping */
    outlitword(w, flavour, sym, aux, flag);
    return 4*litpoolp-4;    /* beware using this for multiword literals */
}

/* lit_findword (and lit_findwordaux) is now the approved route for gen.c  */
/* It returns a BYTE offset into the current literal table                 */

int32 lit_findword(int32 w, int32 flavour, Symstr *sym, int32 flag)
{   return lit_findword5(w, flavour, sym, (VoidStar)0, flag);
}

int32 lit_findwordaux(int32 w, int32 flavour, VoidStar aux, int32 flag)
{   return lit_findword5(w, flavour, 0, aux, flag);
}

int32 lit_findwordsincurpool(int32 w[], int32 count, int32 flavour)
{   /* look for literal in current pool.  Must be the same sort of thing,
       to avoid worries about byte sex change.  Floats and doubles are
       similarly separate.  Double word order has already been arranged
       in target order by struct DbleBin in mip/defs.h.
       Returns (byte) offset of literal in the pool if found, -1 otherwise.
       Does NOT carry litaux info for asm printing.
       Never refers to ADCONs hence xref==NULL test below.
     */
    int32 i, j;
    for (i=0; i<litpoolp; i++) {
        for (j = 0 ; (i+j) < litpoolp ; j++) {
            LitPoolEntry *p = &litpool_(i+j);
            int32 f = ((flavour==LIT_FPNUM && count==2)
                         ? (j==0 ? LIT_FPNUM1 : LIT_FPNUM2) :
                       (flavour == LIT_INT64_1 && count == 2 && j == 1)
                         ? LIT_INT64_2 :
                           flavour);
            if (!(p->type == f && p->val == w[j] && p->xref == NULL))
                break;
            if (j == count-1)
            {   /* adcon available in current literal pool */
                /* if previous ref was addressable this one will be */
                /* set litaux a la lit_findword5()?                     */
                return 4*i;
            }
        }
    }
    return -1; /* Not there - will be inserted by calls of findword */
}

int32 lit_findwordsinprevpools(int32 w[], int32 count, int32 flavour,
                               int32 earliest)
{   /* Look for literal in any previous pool in the SAME function.
       Must be the same sort of thing, to avoid worries about byte sex change.
       Must be at a codesegment address greater than or equal to earliest.
       Returns (absolute) address of literal if found, -1 otherwise.
       Does NOT carry litaux info for asm printing.
       Never refers to ADCONs hence xref==NULL test below.
     */
    LitPool *q;
    for (q = prevpools ; q != NULL ; q = q->next) {
        int32 i = (earliest - poolbase_(q))/4;
        int32 size = poolsize_(q);
        if (i >= size) break;
        if (i < 0) i = 0;
        for (; i < size ; i++) {
            int32 j;
            for (j = 0 ; (i+j) < size ; j++) {
                LitPoolEntry *p = &poolentry_(q, i+j);
                int32 f = ((flavour==LIT_FPNUM && count==2)
                             ? (j==0 ? LIT_FPNUM1 : LIT_FPNUM2) :
                           (flavour == LIT_INT64_1 && count == 2 && j == 1)
                             ? LIT_INT64_2 :
                               flavour);
                if (!(p->type == f && p->val == w[j] && p->xref == NULL))
                    break;
                if (j == count-1) return poolbase_(q)+4*i;
                /* set litaux a la lit_findword5()?                     */
            }
        }
    }
    return -1;
}

static int32 nextstringword(StringSegList **s, int32 *ip, int32 *np)
{
    StringSegList *x = *s;
    int32 i = *ip;
    int32 n = 0;
    union { char c[4]; int32 i; } w;
    for (w.i = 0; x != NULL; x = x->strsegcdr, i = 0)
    {   char *p = x->strsegbase;
        int32 len = x->strseglen;
        for (; i < len; i++) {
            w.c[n] = p[i];
            ++n;
            if (n >= 4) {
                if (++i == len && x->strsegcdr != NULL) {
                    *s = x->strsegcdr; *ip = 0;
                } else {
                    *s = x; *ip = i;
                }
                return w.i;
            }
        }
    }
    *s = NULL; *ip = 0; *np = n;
    return w.i;
}

int32 lit_findstringincurpool(StringSegList *s)
{   /* look for literal string in current pool.
       Returns (byte) offset of literal in the pool if found, -1 otherwise.
     */
    int32 i;
    int32 n = 0;
    int32 dummy;
    int32 w = nextstringword(&s, &n, &dummy);
    for (i = 0; i < litpoolp; i++) {
        int32 j = i;
        StringSegList *s1 = s;
        int32 n1 = n;
        int32 w1 = w;
        for ( ; j < litpoolp ; j++) {
            LitPoolEntry *p = &litpool_(j);
            if (p->type != LIT_STRING || p->val != w1) break;
            if (s1 == NULL) return 4*i;
            w1 = nextstringword(&s1, &n1, &dummy);
        }
    }
    return -1; /* Not there - will be inserted by calls of findword */
}

int32 lit_findstringinprevpools(StringSegList *s, int32 earliest)
{   /* Look for literal in any previous pool in the SAME function.
       Must be the same sort of thing, to avoid worries about byte sex change.
       Must be at a codesegment address greater than or equal to earliest.
       Returns (absolute) address of literal if found, -1 otherwise.
     */
    LitPool *q;
    int32 n = 0;
    int32 dummy;
    int32 w = nextstringword(&s, &n, &dummy);
    for (q = prevpools ; q != NULL ; q = q->next) {
        int32 i = (earliest - poolbase_(q))/4;
        int32 size = poolsize_(q);
        if (i >= size) break;
        if (i < 0) i = 0;
        for (; i < size; i++) {
            int32 j = i;
            StringSegList *s1 = s;
            int32 n1 = n;
            int32 w1 = w;
            for ( ; j < size; j++) {
                LitPoolEntry *p = &poolentry_(q, j);
                if (p->type != LIT_STRING || p->val != w1) break;
                if (s1 == NULL) return poolbase_(q)+4*i;
                w1 = nextstringword(&s1, &n1, &dummy);
            }
        }
    }
    return -1;
}

/* codeseg_stringsegs is exported to vargen.c and xxxgen.c */

void codeseg_stringsegs(StringSegList *x, bool incode)
{
    int32 i = 0;
    int32 litf = incode ? LITF_INCODE+LITF_FIRST : LITF_FIRST;
    for ( ; ; ) {
        int32 n;
        int32 w = nextstringword(&x, &i, &n);
#define lit_strnbytes(n) LIT_STRING
        if (x == NULL) {
            outlitword(w, lit_strnbytes(n), 0, 0, litf | LITF_LAST);
            return;
        }
        outlitword(w, lit_strnbytes(3), 0, 0, litf);
        litf &= ~LITF_FIRST;
    }
}

void codeseg_flush(Symstr *strlitname)
{   /* strlitname will usually be 0, but putting a symbol here enables  */
    /* re-assemblable code on machines whose assemblers change lengths. */
    if (strlitname) show_entry(strlitname, xr_code+xr_defloc);
    dumplits_inner();
    show_code(strlitname);
}

/* the following routine is related to these */
/* One day the nargwords argument may be sensibly the function type info */
int32 codeseg_function_name(Symstr *name, int32 nargwords)
{      int32 result = codebase;
    char *sname = symname_(name);
    union { char c[4]; int32 i; } w;
    int32 p, length;
    for (p = w.i = length = 0; *sname;)
    {   w.c[p] = *sname++;
        ++p;
        if (p == 4)
        {   outcodeword(w.i, LIT_STRING);
            p = w.i = 0;
            length += 4;
        }
    }
    outcodeword(w.i, LIT_STRING);
#ifndef FORBS_CALL_STANDARD
/*
 * This word is intended to let backtrace code (etc) find the string that
 * names the current function even though it knows where the string ends
 * but not (save for this length word) where it starts.
 */
    outcodeword(0xff000000 | (length + 4), LIT_NUMBER);
#endif
    show_code(NULL);
    IGNORE(nargwords);
    return result;
}

int32 stringlength(StringSegList *s)
{   int32 n = 0;
    for ( ; s != NULL ; s = s->strsegcdr) n += s->strseglen;
    return n;
}

#ifdef TARGET_HAS_BSS

int32 bss_size;

void padbss(int32 align)
{
    if (bss_size & (align-1)) bss_size += (-bss_size) & (align-1);
}

static void endbssobject(int32 size)
{
    bss_size += size;
    padbss(alignof_toplevel_static);
}

int32 addbsssym(Symstr *sym, int32 size, int32 align, bool statik, bool local)
{
    if (local) {
        int32 offset;
        if (bss_size == 0)
            obj_symref(bindsym_(bsssegment), xr_bss+xr_defloc, 0);
        obj_symref(sym, xr_bss+(statik ? xr_defloc : xr_defext), bss_size);
        padbss(align);
        offset = bss_size;
        endbssobject(size);
        return offset;
    } else {
        padbss(align);
        obj_symref(sym, xr_bss+(statik ? xr_defloc : xr_defext), bss_size);
        endbssobject(size);
        return BINDADDR_UNSET;
    }
}

#endif

/* This has to be called before the front-end so that initialised     */
/* statics (e.g. pointers to strings) can be put in the code segment. */
void codebuf_reinit1(char *codeseg_label)
{
    codebuf_inroutine = NO;
    codeveccnt = codep = 0;               /* for static inits         */
    litveccnt = litpoolp = 0;
    asm_lablist = NULL;
    litlab = (LabelNumber *) DUFF_ADDR;
    litalign = 4;
#ifdef TARGET_HAS_MULTIPLE_CODE_AREAS
    if (codeseg_label != NULL)
    {   Symstr * sv;
        localcg_endcode();
        sv = bindsym_(codesegment) = sym_insert_id(codeseg_label);
#ifndef NO_OBJECT_OUTPUT
        if (objstream) obj_codewrite(NULL);
#endif                                    /* beware reinit, in effect */
#ifndef NO_ASSEMBLER_OUTPUT
        if (asmstream) display_assembly_code(NULL);
#endif                                    /* beware reinit, in effect */
        obj_symref(sv, xr_code+xr_defloc+xr_dataincode, 0L);
        prevpools = NULL;
        codebase = 0;
        codexrefs = NULL;
    }
#endif
}

/* This has to be called before the front-end so that initialised     */
/* statics (e.g. pointers to strings) can be put in the code segment. */
void codebuf_reinit(void)
{
    codebuf_inroutine = NO;
    codeveccnt = codep = 0;               /* for static inits         */
    litveccnt = litpoolp = 0;
    asm_lablist = NULL;
    litlab = (LabelNumber *) DUFF_ADDR;
    litalign = 4;
#ifdef TARGET_HAS_MULTIPLE_CODE_AREAS
    if (codebase > 0 &&
        ((feature & FEATURE_AOF_AREA_PER_FN) ||
         (var_aof_code_area > code_area_idx)))
#ifdef PUT_FILE_NAME_IN_AREA_NAME
    {   int32 n = var_aof_code_area;
        char filename[256];
        char name[256];
        UnparsedName un;
        fname_parse(sourcefile, FNAME_INCLUDE_SUFFIXES, &un);
        memcpy(filename, un.root, un.rlen);
        filename[un.rlen] = 0;
        if (n < code_area_idx) n = code_area_idx;
        ++code_area_idx;
        sprintf(name, "x$c_%s_%lu", filename, n);
        codebuf_reinit1(name);
    }
#else
    {   int32 n = var_aof_code_area;
        char name[32];
        if (n < code_area_idx) n = code_area_idx;
        ++code_area_idx;
        sprintf(name, "x$code_%lu", n);
        codebuf_reinit1(name);
    }
#endif
    else
#endif
        codebuf_reinit1(NULL);
}

void codebuf_reinit2(void)
{   codebuf_inroutine = YES;
    codeveccnt = codep = 0;               /* for static inits         */
    litveccnt = litpoolp = 0;
    next_label_name = 1;
    asm_lablist = NULL;
    litlab = nextlabel();
}

void codebuf_init(void)
{
    data.head = NULL;  data.tail = NULL;
    data.size = 0; data.xrefs = NULL; data.xrarea = xr_data;
    data.wpos = 0, data.wtype = 0, data.wbuff.w32[0] = 0;
    extable.head = NULL; extable.size = 0;
    extable.xrefs = NULL; extable.xrarea = xr_constdata;
    extable.wpos = 0; extable.wtype = 0; extable.wbuff.w32[0] = 0;
    exhandler.head = NULL; exhandler.size = 0;
    exhandler.xrefs = NULL; exhandler.xrarea = xr_constdata;
    exhandler.wpos = 0; exhandler.wtype = 0; exhandler.wbuff.w32[0] = 0;
#ifdef CONST_DATA_IN_CODE
    constdata.head = NULL; constdata.size = 0;
    constdata.xrefs = NULL; constdata.xrarea = xr_constdata;
    constdata.wpos = 0; constdata.wtype = 0; constdata.wbuff.w32[0] = 0;
#endif
    datap = &data;
#ifdef TARGET_CALL_USES_DESCRIPTOR
    fnconlab = 0;                                  /* WGD 27-3-88 */
#endif
#ifdef TARGET_HAS_BSS
    bss_size = 0;
#endif
    codebase = 0;
    maxprocsize = 0, maxprocname = "<none>";
    codebuf_reinit();      /* in case mcdep_init() is wild */
    count_name_pointer = 0;
    prevpools = NULL;
    code_area_idx = 1;
    currentExceptionEnv = 0;
}

void codebuf_tidy(void)
{
    if (debugging(DEBUG_STORE)) {
        cc_msg( "Code/data generated (%ld,%ld) bytes\n",
            (long)codeloc(), (long)data.size);
        cc_msg( "Max procedure (%s) size %ld bytes\n",
            maxprocname, (long)maxprocsize);
    }
}

/* end of codebuf.c */
