/* thumb/asm.c: Copyright (C) Codemist Ltd., 1994.                       */
/* SPDX-Licence-Identifier: Apache-2.0 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

/* Assembler output is routed to asmstream, annotated if Feature_Annotate.  */


/* exports: asmstream,
            display_assembly_code, asm_header, asm_trailer */

#include <errno.h>

#ifdef __STDC__
#  include <string.h>
#else
#  include <strings.h>
#endif
#include <ctype.h>
#include <assert.h>

#include "globals.h"
#include "mcdep.h"
#include "xrefs.h"
#include "store.h"
#include "codebuf.h"
#include "ops.h"
#include "mcdpriv.h"
#include "builtin.h"
#include "version.h"
#include "errors.h"
#include "disass.h"
#include "bind.h"
#ifdef CPLUSPLUS
#include "unmangle.h"
#endif

FILE *asmstream;
static bool headerdone;

static bool first_area;
static bool new_area;

#ifndef NO_ASSEMBLER_OUTPUT

#define toevensex(x,y) (x)    /* for cross compilation one day */

static bool asm_error;

static Symstr const *out_codeseg;


static void asm_blank(int32 n)
{   while (n-- > 0) fprintf(asmstream, "\n");
}

static int32 asm_padcol9(int32 n)
{
    while (n<9) fputc(' ',asmstream), n++;
    return n;
}

static void pr_string(int32 w)
{
  int i;
  union fudge { int32 i; unsigned char c[4]; } ff;

  ff.i = w;
  for (i = 0; i < 4; i++) {
    if (i) fputc(',', asmstream);
    fprintf(asmstream, "0x%02x", ff.c[i]);
  }
}

static void pr_chars(int32 w)   /* works on both sex machines */
{
  int i, c;
  union fudge { int32 i; unsigned char c[4]; } ff;
  ff.i = w;
  fputc('\'', asmstream);
  for (i=0; i<sizeof(int32); i++)
  { switch(c = ff.c[i])
    {
case '\\':
case '\'':
case '\"':
        break;
case '\a':
        c = 'a';
        break;
case '\b':
        c = 'b';
        break;
case CHAR_FF:
        c = 'f';
        break;
case '\n':
        c = 'n';
        break;
case CHAR_CR:
        c = 'r';
        break;
case '\t':
        c = 't';
        break;
case CHAR_VT:
        c = 'v';
        break;
default:
        if (c < ' ' || c >= 127) fprintf(asmstream, "\\%o", (int)c);
        else putc(c, asmstream);
        continue;
    }
    putc('\\', asmstream);
    putc(c, asmstream);
  }
  fputc('\'', asmstream);
}

static void *aux;

static void spr_asmname(char *buf, char const *s)
{   const char *s1 = s;
    char c;
    bool oddchars = NO;
    if (!isalpha(*s) && *s != '_')
        oddchars = YES;
    else
        while ((c = *s1++) != 0)
            if (!isalnum(c) && c != '_')
            {   oddchars=YES;
                break;
            }
    if (oddchars)
        sprintf(buf, "|%s|", s);
    else
        strcpy(buf, s);
}

static void pr_asmname(Symstr const *sym)
{   char const *s = sym == 0 ? (asm_error = 1, "?") : symname_(sym);
    char buf[256];
    spr_asmname(buf, s);
    fputs(buf, asmstream);
}

#ifdef CPLUSPLUS
static void pr_unmangled_name(const Symstr *sym) {
    char buf[256];
    if (LanguageIsCPlusPlus && HasFeature(Feature_Annotate)) {
        char const *name = unmangle2(symname_(sym), buf, sizeof buf);
        if (name != symname_(sym))
            fprintf(asmstream, " ; %s", buf);
    }
}
#else
#define pr_unmangled_name(sym) ((void)0)
#endif

/* decode_external checks if (and by what) a location is to be relocated.  */
static Symstr *decode_external(int32 p)
{
    CodeXref *x;
    for (x = codexrefs; x!=NULL; x = x->codexrcdr)    /* SLOW loop !!! */
        if (p == (x->codexroff & 0x00ffffff))
            return x->codexrsym;
    return 0;        /* not an external reference */
}

/* Disassembler routines                                                 */

static int32 destination_label;

static char *disass_cb(dis_cb_type type, int32 offset, unsigned32 address,
                       int w, void *cb_arg, char *buf)
{
    switch (type)
    {
case D_LOAD:
case D_STORE:
case D_SWI:
        return buf;
    }
    if (destination_label != -1)
    {   if ((destination_label & 0xfff00000) == 0)
            sprintf(buf, "F%ldL%ld",
                    (long)current_procnum, (long)destination_label & 0xfffff);
        else sprintf(buf, "F%ldL%ld+%ld",
                     (long)current_procnum, (long)destination_label & 0xfffff,
                     (long)((destination_label >> 20) & 0xfff));
        buf += strlen(buf);
    } else {
        if (aux == 0 && (type == D_LOADPCREL || type == D_STOREPCREL))
            sprintf(buf, "[pc, #%ld]", offset);
        else if (aux != 0)
            spr_asmname(buf, symname_((Symstr *) aux));
        else
            asm_error = YES;
        buf += strlen(buf);
        *buf = 0;
    }
    return buf;
}

static void decode_DC(int32 w)
{   int32 col = fprintf(asmstream, "DCD");
    col = asm_padcol9(col);
    fprintf(asmstream, "0x%.8lx", (long)w);
}

static void decode_DCA(Symstr *s, int32 w)
{   int32 col = fprintf(asmstream, "DCD");
    col = asm_padcol9(col);
    pr_asmname(s);
    if (w!=0) fprintf(asmstream, "%+ld", (long)w);
}

/* exported functions ...*/

void display_assembly_code(Symstr const *name)
{   int32 q, ilen;
    LabList *asm_lablist2 = 0;
    List3 *w1, *w2;
    char buf[256];

    if (codep == 0)
    {
        new_area = YES;
        return;
    }
    if (new_area)
    {
        Symstr *sym = bindsym_(codesegment);

        asm_blank(1);
        if (!first_area)
            fprintf(asmstream, "        AREA |C$$%s| %sCODE, READONLY\n", symname_(sym) + 2,
                    (obj_iscommoncode() ? "COMDEF, " : ""));
        asm_blank(1);
        pr_asmname(sym);
        fprintf(asmstream, " DATA");
        pr_unmangled_name(sym);
        asm_blank(1);
        first_area = NO;
        new_area = NO;
    }
    asm_blank(1);
    if (name != NULL) {
        /* may be NULL for string literals from static inits   */
        asm_lablist2 = asm_lablist;
        if (StrEq(symname_(name), "main"))
            obj_symref(libentrypoint, xr_code, 0);
        if (HasFeature(Feature_Annotate))
            fprintf(asmstream, "%.6lx  %20s", (long)codebase, "");
        pr_asmname(name);
        pr_unmangled_name(name);
        asm_blank(1);
    }

/*
 * The following crude quadratic loop identifies all the labels that are
 * actually referenced, so that any other ones do not get printed out to
 * make the assembly code look ugly.
 */
    label_values = (List3 *)dreverse((List *)label_values);
    label_references = (List3 *)dreverse((List *)label_references);
    for (w1=label_references; w1!=NULL; w1=(List3 *)cdr_(w1))
    {   for (w2=label_values; w2!=NULL; w2=(List3 *)cdr_(w2))
        {   int32 nn = w2->csr;
            if (nn < 0) continue;
            if (nn == w1->csr & 0xfffff)
            {   w2->csr = nn | 0x80000000;
                break;
            }
        }
    }
    for (q=0; q < codep; q+=ilen)    /* q is now a BYTE offset */
    {   const int32 f = code_flag_(q);
        int32 w;

        aux = code_aux_(q & (-2));
        while (label_values != NULL && car_(label_values) < q)
            label_values = (List3 *)label_values->cdr;
        while (label_values != NULL && car_(label_values) == q) {
            if (label_values->csr < 0) {
              if (HasFeature(Feature_Annotate)) fprintf(asmstream, "%28s", "");
              fprintf(asmstream, "F%ldL%ld\n",
                                 (long)current_procnum,
                                 (long)label_values->csr & 0x7fffffff);
            }
            label_values = (List3 *)label_values->cdr;
        }
        destination_label = -1;
        while (label_references != NULL && car_(label_references) < q)
            label_references = (List3 *)label_references->cdr;
        if (label_references != NULL && car_(label_references) == q)
            destination_label = label_references->csr;
/*
 * Yeah well - I call disass here so I can decide how long the instruction
 * is pretending to be.
 */
        if (f == LIT_OPCODE) ilen = disass_16(code_hword_(q), code_hword_(q+2),
                                              q, buf, (void *)0, disass_cb);
        else if (f == LIT_BB || f == LIT_H) {
            w = code_hword_(q);
            ilen = 2;
        } else {
            w = code_inst_(q);
            ilen = 4;
        }
        if (HasFeature(Feature_Annotate))
        {   int32 i;
            fprintf(asmstream, "%.6lx  ", (long)(codebase+q));
            switch (f)
            { case LIT_OPCODE:
                for (i = 0; i < 8; i += 2)
                    if (i < ilen)
                        fprintf(asmstream, "%.4lx ", (long)code_hword_(q+i));
                    else
                        fprintf(asmstream, "     ");
                break;
              case LIT_STRING:
                fprintf(asmstream, "%.8lx            ",
                                   (long)toevensex(w,LIT_BBBB));
                break;
              default:
                if (ilen == 2)
                    fprintf(asmstream, "%.4lx            ", (long)toevensex(w, LIT_BB));
                else
                    fprintf(asmstream, "%.8lx            ", (long)toevensex(w, LIT_H));
                break;
            }
        }
        fputs("        ", asmstream);
        switch (f)
        {
#ifdef THUMB_CPLUSPLUS
    case LIT_OPCODE_32:
            disass(w, q, buf, (void *)0, disass_cb);
            fputs(buf, asmstream);
            break;
#endif

    case LIT_OPCODE:
/*
 * (in fact this has been done already)
 *          disass_16(code_hword_(q), code_hword_(q+2), q,
 *                    buf, (void *)0, disass_cb);
 */
            fputs(buf, asmstream);
            break;
    case LIT_STRING: {
            int32 col = fprintf(asmstream, "DCB");
            col = asm_padcol9(col);
            pr_string(w);
            if (HasFeature(Feature_Annotate))
                fprintf(asmstream, " ; "), pr_chars(w);
            break;
    }
    case LIT_BB: {
            unsigned char b[2];

            *(unsigned16 *)b = (unsigned16)w;
            fprintf(asmstream, "DCB       %#.2x,%#.2x", b[0], b[1]);
            break;
    }
    case LIT_H:
            fprintf(asmstream, "DCW       %#.4lx", (long)w);
            break;
    case LIT_NUMBER:
            decode_DC(w);
            break;
    case LIT_ADCON:
            decode_DCA(decode_external(codebase+q), w);
            break;
    case LIT_FPNUM:
            decode_DC(w);
            if (HasFeature(Feature_Annotate))
                fprintf(asmstream, " ; E'%s'", (char *)aux);
            break;
    case LIT_FPNUM1:
            decode_DC(w);
            if (HasFeature(Feature_Annotate))
                fprintf(asmstream, " ; D'%s'",(char *)aux);
            break;
    case LIT_FPNUM2:    /* all printed by the FPNUM1 */
            decode_DC(w);
            break;
    case LIT_INT64_1:
            fprintf(asmstream, "DCD      0x%.8lx, 0x%.8lx", w, code_inst_(q+4));
            break;
    case LIT_INT64_2:    /* all printed by the LIT_INT64_2 */
            if (HasFeature(Feature_Annotate)) break; else continue;
    case LIT_RELADDR:
    default:
            syserr("syserr_display_asm %ld", (long)f);
            fprintf(asmstream, "?");
        }
        fprintf(asmstream, "\n");
    }
    if (asm_lablist2) syserr("syserr_asmlab");
    asm_lablist = 0;    /* stop confusion when called from vargen.c  */
}

static char const *regnames[] = {
  "r0", "r1", "r2", "r3", "r4", "r5", "r6", "r7",
  "r8", "r9", "r10", "r11", "ip", "sp", "lr", "pc"
};

static char const *annotate_regnames[] = {
  "r0", "r1", "r2", "r3", "r4", "r5", "r6", "r7",
  "r8", "r9", "r10", "r11", "ip", "sp", "lr", "pc"
};

char const **regnamev = regnames;

void asm_setregname(int regno, char const *name) {
    if (headerdone) fprintf(asmstream, "%s RN %d\n", name, regno);
    regnamev[regno] = name;
}

void asm_header()
{
    char b[64];
    asm_error = 0;
    first_area = YES;
    new_area = NO;
    regnamev = HasFeature(Feature_Annotate) ? annotate_regnames : regnames;
    disass_sethexprefix("&");
    disass_setregnames(regnamev, NULL);
    headerdone = YES;
    strcpy(b, "Lib$$Request$$armlib$$");
    target_lib_variant(&b[22]);
    obj_symref(sym_insert_id(b), xr_code+xr_weak, 0);
    fprintf(asmstream, "; generated by %s\n", CC_BANNER);
    if (HasFeature(Feature_Annotate)) return;   /* do not bore interactive user */
    asm_blank(1);
    fprintf(asmstream, "        CODE16\n");
    asm_blank(1);
    fprintf(asmstream, "        AREA |C$$code|, CODE, READONLY");
}

/* (not exported) */

static void asm_outextern()
{   ExtRef *x;
    for (x = obj_symlist; x != 0; x = x->extcdr)
    {   int32 flags = x->extflags;
        if (!(flags & xr_objflg) && !(flags & xr_defloc) && (flags & xr_defext))
        {   fprintf(asmstream, "        EXPORT ");
            pr_asmname(x->extsym);
            fprintf(asmstream, "\n");
        }
    }
    asm_blank(1);
    for (x = obj_symlist; x != 0; x = x->extcdr)
    {   int32 flags = x->extflags;
        if (!(flags & xr_objflg) && !(flags & xr_defloc) &&
            !(flags & xr_defext) && x->extsym != bindsym_(constdatasegment))
        {
            /* COMMON data dealt with earlier */
            if (!(flags & xr_code) && (x->extoffset > 0)) continue;
            fprintf(asmstream, "        IMPORT ");
            pr_asmname(x->extsym);
            if (x->extflags & xr_weak)
              fprintf(asmstream, ", WEAK");
            fprintf(asmstream, "\n");
        }
    }
}

typedef struct ExtRefList {
        struct ExtRefList *cdr;
        ExtRef *car;
} ExtRefList;

static void asm_pad(int32 len)
{
  asm_padcol9(1);
  fprintf(asmstream, "%% %ld\n", (long)len);
}

static void asm_data(DataInit *p, int constdata)
{
  int32 offset = 0;

  for (; p != 0; p = p->datacdr) {
    int32 rpt = p->rpt, sort = p->sort, len = p->len;
    union { unsigned32 l;
            unsigned16 w[2];
            unsigned8 b[4];
            FloatCon *f;
          } val;

    val.l = p->val;
    if (sort != LIT_LABEL) asm_padcol9(1);
    switch (sort) {
        case LIT_LABEL:
            pr_asmname((Symstr *)rpt);
            /* Below it used to say constdata ... */
            if (constdata)
              fprintf(asmstream, " DATA");

            break;
        default:  syserr(syserr_asm_trailer, (long)sort);
        case LIT_BBBB:
            if (rpt == 1) {
                fprintf(asmstream, "DCB      %#.2x,%#.2x,%#.2x,%#.2x", val.b[0], val.b[1], val.b[2], val.b[3]);
                break;
            }
        case LIT_BBBX:
            if (rpt == 1) {
                fprintf(asmstream, "DCB      %#.2x,%#.2x,%#.2x", val.b[0], val.b[1], val.b[2]);
                break;
            }
        case LIT_BBX:
            if (rpt == 1) {
                fprintf(asmstream, "DCB      %#.2x,%#.2x", val.b[0], val.b[1]);
                break;
            }
        case LIT_BXXX:
            if (rpt == 1) {
                fprintf(asmstream, "DCB      %#.2x", val.b[0]);
                break;
            }
        case LIT_HH:
            if (rpt == 1) {
                fprintf(asmstream, "DCW      %#.4x,%#.4x", val.w[0], val.w[1]);
                break;
            }
        case LIT_HX:
            if (rpt == 1) {
                fprintf(asmstream, "DCW%c     %#.4x", offset & 1 ? 'U' : ' ', val.w[0]);
                break;
            }
        case LIT_BBH:
            if (rpt == 1) {
                fprintf(asmstream, "DCB      %#.2x,%#.2x\n", val.b[0], val.b[1]);
                asm_padcol9(1);
                fprintf(asmstream, "DCW      %#.4x", val.w[1]);
                break;
            }
        case LIT_HBX:
            if (rpt == 1) {
                fprintf(asmstream, "DCW%c     %#.4x\n", offset & 1 ? 'U' : ' ', val.w[0]);
                asm_padcol9(1);
                fprintf(asmstream, "DCB      %#.2x", val.b[2]);
                break;
            }
        case LIT_HBB:
            if (rpt == 1) {
                fprintf(asmstream, "DCW      %#.4x\n", val.w[0]);
                asm_padcol9(1);
                fprintf(asmstream, "DCB      %#.2x,%#.2x", val.b[2], val.b[3]);
                break;
            }
        case LIT_NUMBER:
            if (len != 4) syserr(syserr_asm_data, (long)len);
            if (rpt == 1) {
                fprintf(asmstream, "DCD%c     %#.8lx", offset & 3 ? 'U' : ' ', (long)val.l);
            } else if (val.l == 0) {
                fprintf(asmstream, "%%        %ld", (long)rpt*len);
            }
            else syserr(syserr_asm_trailer1, (long)rpt, (long)val.l);
            break;
        case LIT_FPNUM:
        {   int32 *p = ((FloatCon *)val.l) -> floatbin.irep;
            decode_DC(p[0]);
            if (HasFeature(Feature_Annotate))
                fprintf(asmstream, " ; %s", ((FloatCon *)val.l) -> floatstr);
            if (len == 8) fprintf(asmstream, "\n"),
                          asm_padcol9(1), decode_DC(p[1]);
            break;
        }
        case LIT_ADCON:              /* (possibly external) name + offset */
            if (rpt != 1) syserr("syserr_asm_trailer2");
            decode_DCA((Symstr *)len, val.l);
            break;
    }
    offset = (offset + len) & 3;
    fprintf(asmstream, "\n");
  }
}

void asm_trailer()
{
  if (constdata_size() != 0) {
    asm_blank(1);
    fprintf(asmstream, "        AREA |C$$constdata|, DATA, READONLY\n");
    asm_blank(1);
    pr_asmname(bindsym_(constdatasegment));
    asm_blank(1);
    asm_data(constdata_head(), 0);
  }
  if (data_size() != 0)
  {
    asm_blank(1);
    fprintf(asmstream, "        AREA |C$$data|, DATA\n");
    asm_blank(1);
    asm_data(data_head(), 0);
  }
  if (bss_size != 0)
  { int32 n = 0;
    ExtRef *x = obj_symlist;
    ExtRefList *zisyms = NULL;
    asm_blank(1);
    fprintf(asmstream, "        AREA |C$$zinit|, NOINIT\n");
    asm_blank(1);
    for (; x != NULL; x = x->extcdr)
      if (x->extflags & xr_bss) {
        ExtRefList **prev = &zisyms;
        ExtRefList *p;
        for (; (p = *prev) != 0; prev = &cdr_(p))
          if (x->extoffset < car_(p)->extoffset) break;
        *prev = (ExtRefList *) syn_cons2(*prev, x);
      }
    for (; zisyms != NULL; zisyms = cdr_(zisyms))
    { x = car_(zisyms);
      if (x->extoffset != n) asm_pad(x->extoffset-n);
      n = x->extoffset;
#if 0
      maybe_export(x->extsym);
      indent_18_if_annotating();
#endif
      pr_asmname(x->extsym);
      fprintf(asmstream, "\n");
    }
    if (n != bss_size) asm_pad(bss_size-n);
  }
  { ExtRef *x;
    for (x = obj_symlist; x != NULL; x = x->extcdr)
    { int32 flags = x->extflags;
      if ((flags & (xr_defloc + xr_defext)) == 0) {
        /* not defined... */
        Symstr *s = x->extsym;
        int32 len = x->extoffset;
        if (!(flags & xr_code) && (len > 0))
        { /* common data... */
          fputs("        EXPORT  ", asmstream);
          pr_asmname(s);
          asm_blank(1);
          fprintf(asmstream, "        AREA ");
          pr_asmname(s);
          fprintf(asmstream, ",COMMON, NOINIT\n");
          asm_pad(len);
        }
      }
    }
  }
  asm_blank(1);
  if (!HasFeature(Feature_Annotate))
      asm_outextern();
  asm_blank(1);
  fprintf(asmstream, "        END\n");
  headerdone = NO;
  if (asm_error) syserr("syserr_asm_confused");
}

#endif

/* end of thumb/asm.c */
