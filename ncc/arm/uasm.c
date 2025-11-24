/*
 * arm/uasm.c,  version 1b
 * Copyright (C) Acorn Computers Ltd., 1988.
 * Copyright (C) Codemist Ltd., 1988.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

#ifndef NO_VERSION_STRINGS
extern char uasm_version[];
char uasm_version[] = "\narm/uasm.c $Revision$ 1a\n";
#endif

/*
 *(hacked from c.armasm by M. Clemoes to output unix arm assembler)
 *@@@ AM: the files are sufficiently similar that I would have thought
 *@@@ conditional assembly sufficed.  Moreover this eases maintenance
 *@@@ Moreover, the maybe_import/export junk acquired from the arthur
 *@@@ assembler bug could be much simplified here.
 */

/* Assembler output is routed to asmstream, annotated if Feature_Annotate.  */
/* /* ACN: Alignment of the diaplyed output is inconsistent in this case.   */
/* See c.armobj for more details of data structures.                        */

/* exports: asmstream,
            display_assembly_code, asm_header, asm_trailer
            also decode_instruction(w, 0, 0) for use outside compiler */


#ifdef __STDC__
#include <string.h>            /* for strncmp */
#else
#include <strings.h>            /* for strncmp */
#endif
#include <ctype.h>

#include "globals.h"
#include "mcdep.h"
#include "store.h"
#include "codebuf.h"
#include "builtin.h"
#include "xrefs.h"
#include "ops.h"
#include "version.h"
#include "mcdpriv.h"
#include "errors.h"

#include "disass.h"

FILE *asmstream;

#ifndef NO_ASSEMBLER_OUTPUT

static char *regnames[16] = {"r0","r1","r2","r3","r4","r5","r6","r7",
                             "r8","r9",0,0,0,0,"lr","pc"};
                                         /* others filled in when pcs is set */

static char * const fregnames[8] = {"f0","f1","f2","f3","f4","f5","f6","f7"};

static void newline() {
    fputc('\n', asmstream);
}

void asm_setregname(int regno, char *name) {
    regnames[regno] = name;
}

#define INSTRUC 1
#define NUMB    0

static void pr_chars(int32 w, int n)
/* works on both sex machines */
{
  int i, c;
  fputc('\"', asmstream);
  for (i = 0; i < n; i++)
  { switch (c = ((unsigned char *)&w)[i])
    {
case '\\':
case '\'':
case '\"':
        break;
case BELL:
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
        if (c < ' ' || c >= 127) fprintf(asmstream, "\\%o", c);
        else putc(c, asmstream);
        continue;
    }
    putc('\\', asmstream);
    putc(c, asmstream);
  }
  fputc('\"', asmstream);
}

static void spr_asmname(char *buf, Symstr const *sym)
{
    char const *s = symname_(sym);
    if (sym == bindsym_(datasegment))
        sprintf(buf, "L__dataseg");
    else if (strncmp( s, "x$", 2) != 0)
        sprintf(buf, "_%s",  s);
    else
        sprintf(buf, "%s", s+2);
}

static void pr_asmname(Symstr const *sym) {
    char buf[256];
    spr_asmname(buf, sym);
    fputs(buf, asmstream);
}

static Symstr *find_extsym(int32 p)
{   CodeXref  *x;
    for (x = codexrefs; x != NULL; x = x->codexrcdr) {
        if (p == (x->codexroff & 0x00ffffffL)) return(x->codexrsym);
    }
    syserr(syserr_find_extsym);
    return(NULL);
}

static List *litlabels;
static int32 asm_codesize;    /*@@@ AM: never really used. */
static char  *asm_needslabel; /* a bitmap */
static List  *asm_imported;

#define needslabel(widx) (asm_needslabel[(widx) >> 3] &  (1 << ((widx)&7)))
#define setlabbit(widx)  (asm_needslabel[(widx) >> 3] |= (1 << ((widx)&7)))


static int32 LiteralBefore(int32 target) {
    List *p;
    for (p = litlabels; p != NULL; p = cdr_(p))
        if (car_(p) <= target) return car_(p);
    return 0;
}

static void NoteLiteralLabel(int32 q) {
    if (needslabel(q / 4))
        litlabels = (List *)global_cons2(SU_Other, litlabels, q+codebase);
}

static void printlabelname(char *buf, char const *before, char const *after, int32 offset, Symstr const *sym)
{
/* For data references, ignore the function name: it will be wrong for backward
 * references to the literal pool of another function.  (Labels which are the
 * subject of data references have already been removed from asm_lablist).
 * For code references, generate a label of the form L<address>.J<label>.<proc>.
 */
    LabList *p;
    char const *s;
    if (sym == NULL) s = "__OutsideFunction__";
    else s = symname_(sym);
    for ( p = asm_lablist ; p != NULL ; p = p->labcdr) {
        LabelNumber *lab = p->labcar;
        if ((lab->u.defn & 0x00ffffff) == offset)
            sprintf(buf, "%sL%06lx.J%ld.%s%s",
                         before, offset+codebase, lab_name_(lab) & 0x7fffffff,
                         s, after);
    }
    sprintf(buf, "%sL%06lx%s", before, offset+codebase, after);
}

static Symstr *procname;

typedef struct RelAddrRec {
    Symstr *sym;
    int32 count;
    int32 offset;
    char *buf;
    char *dis_limit;
} RelAddrRec;

static char *disass_adrl(RelAddrRec *r, char *buf, int32 offset) {
    int pos = (r->buf[3] == 'S' || r->buf[3] == ' ') ? 3 : 5;
    int c = r->buf[pos];
    do buf--; while (buf[-1] != ',');
    memcpy(r->buf, "ADR", 3);
    while (--r->count >= 0) r->buf[pos++] = 'L';
    r->buf[pos] = c;
    sprintf(buf, "%ld+", offset);
    buf += strlen(buf);
    spr_asmname(buf, r->sym);
    return buf;
}

static char *disass_cb(dis_cb_type type, int32 offset, unsigned32 address, int w, void *cb_arg, char *buf) {
    RelAddrRec *r = (RelAddrRec *)cb_arg;
    IGNORE(w);
    *buf = 0;
    if (type == D_BORBL) {
        r->dis_limit = buf;
        if (r->sym == NULL)
            printlabelname(buf, "", "", address, procname);
        else
            spr_asmname(buf, r->sym);
    } else if (type == D_ADDPCREL) {
        r->dis_limit = buf;
        if (r->sym != NULL)
            buf = disass_adrl(r, buf, offset + r->offset + address);
        else
            printlabelname(buf, "#", "-.-8", address+offset, procname);
    } else if (type == D_SUBPCREL) {
        r->dis_limit = buf;
        if (r->sym != NULL)
            buf = disass_adrl(r, buf, address - offset - r->offset);
        else {
        /* Backward reference to a string may be to an address part way through
           a literal in a different function, for which therefore no label was
           generated.  (Hence the list litlabels).
         */
            int32 target = address - offset + codebase;
            int32 litaddr = LiteralBefore(target);
            if (litaddr == target)
                printlabelname(buf, "#.+8-", "", address - offset, procname);
            else {
                char b[8];
                sprintf(b, "+%ld)", target - litaddr);
                printlabelname(buf, "#.+8-(", b, litaddr - codebase, procname);
            }
        }
    } else if (type == D_LOADPCREL || type == D_STOREPCREL) {
        /* Backward references here can't currently be to an address for which
           no label was generated (loading as an integer the second word of a
           double constant or some non-initial word of a string are the
           possibilities, which literal pool management currently precludes).
           Still, we allow the possibility for safety.
         */
        int32 target = address + codebase;
        int32 litaddr = offset >= 0 ? target : LiteralBefore(target);
        r->dis_limit = buf;
        if (litaddr == target)
            printlabelname(buf, "[pc, #", "-.-8]", address, procname);
        else {
            char b[8];
            sprintf(b, "+%ld)-.-8", target - litaddr);
            printlabelname(buf, "[pc, #(", b, litaddr - codebase, procname);
        }
    } else if (type == D_LOAD || type == D_STORE) {
        if (r->sym != NULL) {
            r->dis_limit = buf;
            sprintf(buf, "%ld+", offset);
            buf += strlen(buf);
            spr_asmname(buf, r->sym);
        }
    }
    return buf+strlen(buf);
}

static void maybe_export(Symstr *sym)
{   char  *p = symname_(sym);
    char  c;
    ExtRef *x;

/* Unless external there is nothing to do here. */
    if ((x = symext_(sym)) != 0 &&
        (x->extflags & xr_defext) == 0) return;

/*@@@ AM does not see how the following can ever now happen as x$dataseg etc. */
/*@@@ are very local statics.  Is this if error recovery inserted gensyms?    */
    while ((c = *p++) != 0) { /* look for odd characters in x$dataseg etc */
        if (!(isalnum(c) || (c == '_'))) return;
    }
    {
        FILE  *as = asmstream;
        fprintf(as, "        .global "); pr_asmname(sym); fputs("\n", as);
    }
}

static void killasmlabel(int32 wordoffset)
{
/* Ensure that jopcode labels are present only for instructions, not data items */
    LabList *p, *prev = NULL;
    int32 offset = wordoffset * 4L;
    for ( p = asm_lablist ; p != NULL ; prev = p, p = p->labcdr)
        if ((p->labcar->u.defn & 0x00ffffff) == offset) {
            p = (LabList *) discard2((List *) p);
            if (prev == NULL)
                asm_lablist = p;
            else
                prev->labcdr = p;
            return;
        }
}

static void asm_scancode(void)
{   int32 p;
    int bitmapsize;
    char  *x;

    bitmapsize = (int)((codep + 127) >> 5); /* > 1 bit per word of code */
    asm_needslabel = x = (char *)BindAlloc(bitmapsize);
    memclr((VoidStar)x, bitmapsize);

    for (p = 0; p < codep; p += 4) {
        int32 w = code_inst_(p);
        int32 f = code_flag_(p);
        switch (f) {
        case LIT_RELADDR:
            break;
        case LIT_OPCODE:
            switch (w & 0x0f000000) {
            case OP_B: case OP_BL:
                if (w & 0x00800000L) w |= 0xff000000L; else w &= 0x00ffffffL;
                w = (p / 4L) + 2L + w; /* word index */
                setlabbit(w);
                break;

            case OP_PREN:
                if (((w >> 16L) & 0xfL) == R_PC) {
                    int32 d = w & 0xfffL;
                    if ((w & F_UP)==0) d = -d;
                    w = (p + 8L + d) / 4L;
                    setlabbit(w);
                    killasmlabel(w);
                }
                break;

            case 0x02000000L:
                {   int32 op = w & (0xfL << 21L);
                    if ( (op == F_ADD || op == F_SUB) &&
                         (((w >> 16L) & 0xfL) == R_PC)) {
                        int32 shift = (w & 0xf00)>>7, val = w & 0xff;
                        val = (val>>shift) | (val<<(32-shift));
                        if (op == F_SUB) val = -val;
                        w = (p + 8L + val) / 4L;
                        setlabbit(w);
                        killasmlabel(w);
                    }
                }
                break;

            case OP_CPPRE:
                if (((w >> 16L) & 0xfL) == R_PC) {
                    int32 d = w & 0xffL;
                    if ((w & F_UP)==0) d = -d;
                    w = (p + 8L) / 4L + d;
                    setlabbit(w);
                    killasmlabel(w);
                }
                break;

            default:
                break;
            }
        default:
            break;
        }
    }
}

static void pr_common_defs(void)
{   ExtRef  *x;
    FILE    *as = asmstream;
    int  n_comm = 0;
    obj_symlist = (ExtRef *)dreverse((List *)obj_symlist);
                  /* oldest = smallest numbered first */

    for (x = obj_symlist; x != 0; x = x->extcdr)
    {
        int flags = x->extflags;
        int32  sz = x->extoffset;
        if ((x->extindex > 1) && (sz > 0) &&
            ((flags & (xr_defloc | xr_defext)) == 0))
        {
            if (n_comm == 0) {++n_comm;  fputs("\n", as);}
            fprintf(as, "        .comm   ");
            pr_asmname(x->extsym);
            fprintf(as, ", %lu\n", sz);
        }
    }
}

/* exported functions ...*/

static void disassemble(int32 w, int32 q, Symstr *sym, RelAddrRec *r) {
    r->sym = sym; r->offset = 0; r->count = 0;
    r->dis_limit = NULL;
    disass(w, q, r->buf, (void *)r, disass_cb);
    {   char *cp, *end = (r->dis_limit == 0) ? r->buf + strlen(r->buf) : r->dis_limit;
        for (cp = r->buf; cp != end; cp++) {
            char ch = *(unsigned char *)cp;
            if (isupper(ch)) *cp = tolower(ch);
        }
    }
    fprintf(asmstream, "        %s", r->buf);
}

void display_assembly_code(Symstr *name)
{   int32  q, lastline = -1;
    FILE   *as = asmstream;
    Symstr *sym;
    RelAddrRec r;
    char buf[256];
    r.buf = buf;

    newline();
    asm_scancode();
    if (name != 0 && name != bindsym_(codesegment))
                   /* name may be 0 for string literals from static inits   */
    {
        newline();
        maybe_export(name);
        if (HasFeature(Feature_Annotate)) fprintf(as, "                ");
        pr_asmname(name);
        fprintf(as, ":\n\n");
    }
    for (q = 0; q < codep; q += 4)    /* q is now a BYTE offset */
    {   int32 w = code_inst_(q),
              f = code_flag_(q);
        VoidStar aux = code_aux_(q);
        if (needslabel(q / 4)) {
            printlabelname(buf, "", ":\n", q, name);
            fputs(buf, as);
        }
        if (HasFeature(Feature_Annotate))
            fprintf(as, "%.6lx  %.8lx  ", (long)(q + codebase), (long)w);
        switch(f)
        {
    case LIT_RELADDR:
            if (lastline == NUMB) newline();
            disassemble(w, q, (Symstr *)aux, &r);
            lastline = INSTRUC;
            break;
    case LIT_OPCODE:
            if (lastline == NUMB) newline();
            disassemble(w, q, NULL, &r);
            lastline = INSTRUC;
            break;
    case LIT_STRING:
            if (lastline == INSTRUC) newline();
            fprintf(as, "        .ascii  ");
            NoteLiteralLabel(q);
            if (host_lsbytefirst != target_lsbytefirst)
            /* already sex_reversed, so reverse back */
                w = totargetsex(w, LIT_BBBB);
            pr_chars(w, 4);
            lastline = NUMB;
            break;
    case LIT_NUMBER:
            if (lastline == INSTRUC) newline();
            NoteLiteralLabel(q);
            fprintf(as, "        .word   %#.8lx", (long)w);
            lastline = NUMB;
            break;
    case LIT_ADCON:
            if (lastline == INSTRUC) newline();
            NoteLiteralLabel(q);
            sym = find_extsym(codebase+q);
            fprintf(as, "        .word   "); pr_asmname(sym);
            if (w != 0) fprintf(as, "+%#lx", (long)w);
            lastline = NUMB;
            break;
    case LIT_FPNUM:
            if (lastline == INSTRUC) newline();
            NoteLiteralLabel(q);
            {   char *s = (char *)aux;
                if (*s != '<') {
                    fprintf(as, "        .float  %s", s);
                } else {
                    fprintf(as, "        .word   %#.8lx", w);
                }
            }
            lastline = NUMB;
            break;
    case LIT_FPNUM1:
            if (lastline == INSTRUC) newline();
            NoteLiteralLabel(q);
            {   char *s = (char *)aux;
                if (*s != '<') {
                    fprintf(as, "        .double %s", s);
                } else {
                    fprintf(as, "        .word   %#.8lx, %#.8lx",
                                w, code_inst_(q+4) );
                }
            }
            lastline = NUMB;
            break;
    case LIT_FPNUM2:    /* all printed by the FPNUM1 */
            if (HasFeature(Feature_Annotate)) break; else continue;
    default:
            fprintf(as, "\n        ????\n");
        }
        newline();
    }
    asm_codesize += codep;
}

void asm_header(void)
{   asm_codesize = 0;
    asm_imported = NULL;
    litlabels = NULL;
    disass_sethexprefix("0x");
    disass_setregnames(regnames, (char **)fregnames);

    if (HasFeature(Feature_Annotate)) return;   /* do not bore interactive user */
    fprintf(asmstream, "@ generated by %s\n\n", CC_BANNER);
    fprintf(asmstream, "        .text");
}

typedef struct ExtRefList {
        struct ExtRefList *cdr;
        ExtRef *car;
} ExtRefList;

static void pr_onehalf(FILE *as, unsigned short w)
{   union {
        int32 l;
        unsigned short w[2];
    } val;
    fprintf(as, "        .half   %#.4x                  @ ", w);
    val.w[0] = w;
    pr_chars(val.l, 2);
}

static void pr_onebyte(FILE *as, unsigned char b)
{   union {
        int32 l;
        unsigned char b[4];
    } val;
    fprintf(as, "        .byte   %#.2x                    @ ", b);
    val.b[0] = b;
    pr_chars(val.l, 1);
}

static void pr_twobytes(FILE *as, unsigned char b, unsigned char c)
{   union {
        int32 l;
        unsigned char b[4];
    } val;
    fprintf(as, "        .byte   %#.2x, %#.2x              @ ", b, c);
    val.b[0] = b; val.b[1] = c;
    pr_chars(val.l, 2);
}

static void asm_checklenandrpt(int32 len, int lenwanted, int32 rpt, int32 val) {
    bool norpt = NO;
    if (lenwanted < 0) norpt = YES, lenwanted = -lenwanted;
    if (len != lenwanted)
        syserr(syserr_asm_data, (long)len);
     if (rpt != 1 && (val != 0 || norpt))
        syserr(syserr_asm_trailer1, (long)rpt, (long)val);
}

static void asm_data(DataInit *p) {
  FILE *as = asmstream;
  int32 adr;
  for (; p != 0; p = p->datacdr)
  { int32 rpt = p->rpt, sort = p->sort, len = p->len;
    union { unsigned32 l;
            unsigned16 w[2];
            unsigned8 b[4];
            FloatCon *f;
          } val;
    val.l = p->val;
    switch (sort)
    {   case LIT_LABEL:
            newline();
/* All LIT_LABEL's get more properly registered with the preceding  */
/* obj_symref() -- e.g. in vargen.c.                                */
            {   ExtRef *x = symext_((Symstr *)rpt);
                if (x == 0) syserr(syserr_duff_lab);
                adr = x->extoffset;
            }
            maybe_export((Symstr *)rpt);
            if (adr & 3) {
              fprintf(as, "L%.3lx:\n", adr & ~3L);
              pr_asmname((Symstr *)rpt);
              fprintf(as, "   .equ   L%.3lx + %ld\n", adr & ~3L, adr & 3L);
            } else {
              pr_asmname((Symstr *)rpt);
              fprintf(as, ":\n");
            }
            break;
        default:  syserr(syserr_asm_trailer, (long)sort);
        case LIT_BBBB:
            asm_checklenandrpt(len, -4, rpt, val.l);
            fprintf(as, "        .byte   %#.2x, %#.2x, %#.2x, %#.2x  @ ",
                        val.b[0], val.b[1], val.b[2], val.b[3]);
            pr_chars(val.l, 4);
            break;
        case LIT_BBBX:
            asm_checklenandrpt(len, -3, rpt, val.l);
            fprintf(as, "        .byte   %#.2x, %#.2x, %#.2x        @ ", val.b[0], val.b[1], val.b[2]);
            pr_chars(val.l, 3);
            break;
        case LIT_BBX:
            asm_checklenandrpt(len, -2, rpt, val.l);
            pr_twobytes(as, val.b[0], val.b[1]);
            break;
        case LIT_BXXX:
            asm_checklenandrpt(len, -1, rpt, val.l);
            pr_onebyte(as, val.b[0]);
            break;
        case LIT_HH:
            asm_checklenandrpt(len, -4, rpt, val.l);
            fprintf(as, "        .half   %#.4x, %#.4x           @ ", val.w[0], val.w[1]);
            pr_chars(val.l, 4);
            break;
        case LIT_HX:
            asm_checklenandrpt(len, -2, rpt, val.l);
            pr_onehalf(as, val.w[0]);
            break;
        case LIT_BBH:
            asm_checklenandrpt(len, -4, rpt, val.l);
            pr_twobytes(as, val.b[0], val.b[1]); newline();
            pr_onehalf(as, val.w[1]);
            break;
        case LIT_HBX:
            asm_checklenandrpt(len, -3, rpt, val.l);
            pr_onehalf(as, val.w[0]); newline();
            pr_onebyte(as, val.b[2]);
            break;
        case LIT_HBB:
            asm_checklenandrpt(len, -4, rpt, val.l);
            pr_onehalf(as, val.w[0]); newline();
            pr_twobytes(as, val.b[2], val.b[3]);
            break;
        case LIT_NUMBER:
            asm_checklenandrpt(len, 4, rpt, val.l);
            if (len != 4) syserr(syserr_asm_data, (long)len);
            if (rpt == 1) {
                fprintf(as, "        .word   %#.8lx              @ ", (long)val.l);
                pr_chars(val.l, 4);
            } else /* val.l already checked to be zero */
                fprintf(as, "        .space  %ld", (long)(rpt*len));
            break;
        case LIT_FPNUM:
        {   char *s = val.f->floatstr;
            if (*s != '<') {
                fprintf(as, "        .%s %s",
                            (len == 8) ? "double" : "float ", s);
            } else if (len == 4) {
                fprintf(as, "        .word   %#.8lx",
                            val.f->floatbin.fb.val);
            } else {
                fprintf(as, "        .word   %#.8lx, %#.8lx",
                            val.f->floatbin.db.msd,
                            val.f->floatbin.db.lsd);
            }
            break;
        }
        case LIT_ADCON:              /* (possibly external) name + offset */
            while (rpt--)
            {   fprintf(as, "        .word   ");
                pr_asmname((Symstr *)len);
                fprintf(as, "+%ld", (long)val.l);
            }
            break;
    }
    newline();
  }

}

void asm_trailer(void)
{
#ifndef TARGET_IS_HELIOS
  FILE     *as = asmstream;
#ifdef CONST_DATA_IN_CODE
  asm_data(constdata_head());
#endif
  fprintf(as, "\n        .data\n");
  pr_common_defs();
  asm_data(data_head());
  if (bss_size != 0)
  { int32 n = 0;
    ExtRef *x = obj_symlist;
    ExtRefList *zisyms = NULL;
    fprintf(as, "\n        .bss\n");
    for (; x != NULL; x = x->extcdr)
      if (x->extflags & xr_bss) {
        ExtRefList **prev = &zisyms;
        ExtRefList *p;
        for (; (p = *prev) != 0; prev = &cdr_(p))
          if (x->extoffset < car_(p)->extoffset) break;
        *prev = (ExtRefList *)syn_cons2(*prev, x);
      }
    for (; zisyms != NULL; zisyms = cdr_(zisyms))
    { x = car_(zisyms);
      if (x->extoffset != n)
        fprintf(as, "        .space %ld\n", x->extoffset-n);
      n = x->extoffset;
      maybe_export(x->extsym);
      pr_asmname(x->extsym);
      fprintf(as, ":\n");
    }
    if (n != bss_size)
      fprintf(as, "        .space %ld\n", bss_size-n);
  }
  newline();
#endif  /* TARGET_IS_HELIOS */
}

#endif /* NO_ASSEMBLER_OUTPUT */

/* To avoid messy conditional compilation in arm/gen.c */

DataDesc adconpool;
Symstr *adconpool_lab;

int adconpool_find(int32 w, int32 flavour, Symstr *sym) {
  IGNORE(w); IGNORE(flavour); IGNORE(sym);
  syserr("adconpool_find");
  return 0;
}

void adconpool_flush(void) {}

void adconpool_init(void) {}

/* end of arm/uasm.c */
