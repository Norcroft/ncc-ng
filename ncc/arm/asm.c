/*
 * arm/asm.c: ARM assembly language output,  Codemist version 21
 * Copyright (C) Codemist Ltd., 1987-1993
 * Copyright (C) Advanced RISC Machines Limited., 1990-1993
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

/* Assembler output is routed to asmstream, annotated if Feature_Annotate.  */
/* See c.armobj for more details on datastructures.                         */

/* exports: asmstream, display_assembly_code, asm_header, asm_trailer.      */

#ifdef __STDC__
#  include <string.h>
#else
#  include <strings.h>
#endif
#include <ctype.h>

#include "globals.h"
#include "mcdep.h"
#include "mcdpriv.h"
#include "xrefs.h"
#include "store.h"
#include "codebuf.h"
#include "armops.h"
#include "version.h"
#include "builtin.h"                  /* for codesegment, code_area_idx... */
#include "errors.h"
#include "disass.h"
#include "bind.h"
#ifdef CPLUSPLUS
#include "unmangle.h"
#endif

#define lx_arg(x) ((unsigned long)((x) & 0xfffffffful))

FILE *asmstream;

#ifndef NO_ASSEMBLER_OUTPUT

static char const spaces_18[20] = "                  \0";  /* 18 blanks and 2 NULs */
static char const *regnames[16] = {"a1","a2","a3","a4","v1","v2","v3","v4",
                                   "v5","v6","fp","sl","ip","sp","lr","pc"};
                                         /* fp and sl may change when pcs is set */

static char const *fregnames[8] = {"f0","f1","f2","f3","f4","f5","f6","f7"};

static Symstr *out_codeseg;
static bool first_area;
static bool new_area;
#if RECORD_SOURCE_LOCATION
// Records the last outputted location to avoid duplication.
static MiniFileLine last_fileline;
#endif

static void newline(void)
{
    fputc('\n', asmstream);
}

static void indent_18_if_annotating(void)
{
    if (HasFeature(Feature_Annotate))
        fputs(spaces_18, asmstream);
}

static void padtocol8(unsigned32 n)
{
    if (n > 8) n = 8;
    fputs(spaces_18 + 18 - 8 + n, asmstream);
}

static void indent8(void)
{
    padtocol8(0);
}

static void pr_chars(int32 w)
/* Works on both sexes of host machine. */
/* Assumes ASCII target machine.        */
{   unsigned i, c;
    FILE *as = asmstream;

    fputc('\'', as);
    for (i=0; i<sizeof(int32); i++)
    {   c = ((uint8 *)&w)[i];
        if (c < ' ' || c >= 127)
        {    if (c >= 7 && c <= 13)
             {   c = "abtnvfr"[c-7];
                 goto escape;
             }
             else
             {   fprintf(as, "\\%o", c);
                 continue;
             }
        }
        else if (c == '\\' || c == '\'' || c == '\"')
escape:     fputc('\\', as);
        fputc(c, as);
    }
    fputc('\'', as);
}

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

static void spr_asmsym(char *buf, Symstr const *sym) {
    spr_asmname(buf, symname_(sym));
}

static void pr_asmname(char const *s) {
    char buf[256];
    spr_asmname(buf, s);
    fputs(buf, asmstream);
}

static void pr_asmsym(Symstr const *sym) {
    char buf[256];
    spr_asmsym(buf, sym);
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


static Symstr *find_extsym(int32 p)
{   CodeXref  *x;
    for (x = codexrefs; x != NULL; x = x->codexrcdr) {
        if (p == (x->codexroff & 0x00ffffffL)) return(x->codexrsym);
    }
    syserr(syserr_find_extsym);
    return(NULL);
}

static void printlabelname(char *buf, const char *before, const char *after, int32 offset, const Symstr *sym)
{
/* For data references, ignore the function name: it will be wrong for backward
 * references to the literal pool of another function.  (Labels which are the
 * subject of data references have already been removed from asm_lablist).
 * For code refs, generate a label of the form L<address>.J<label>.<proc>.
 */
    LabList *p;
/*
 * in various places showcode(NULL) gets called - the following lines arrange
 * that the stuff printed here is nevertheless at least textual.
 */
    if (sym != NULL)
    {   for ( p = asm_lablist ; p != NULL ; p = p->labcdr) {
            LabelNumber *lab = p->labcar;
            if ((lab->u.defn & 0x00ffffff) == offset)
            {   sprintf(buf, "%s|L%.6lx.J%ld.%s|%s",
                        before, offset+codebase, lab_name_(lab) & 0x7fffffff,
                        symname_(sym), after);
                return;
            }
        }
    }
    sprintf(buf, "%sL%lx%.5lx%s", before,
        code_area_idx == 1 ? 0L : code_area_idx, offset+codebase, after);
}

static Symstr const *procname;

typedef struct RelAddrRec {
    Symstr *sym;
    int32 count;
    int32 offset;
    char *buf;
} RelAddrRec;

static char *disass_adrl(RelAddrRec *r, char *buf, int32 offset) {
    int pos = (r->buf[3] == 'S' || r->buf[3] == ' ') ? 3 : 5;
    int c = r->buf[pos];
    do buf--; while (buf[-1] != ',');
    memcpy(r->buf, "ADR", 3);
    while (--r->count >= 0) r->buf[pos++] = 'L';
    r->buf[pos] = c;
    if (offset != 0) {
        sprintf(buf, "%ld+", offset);
        buf += strlen(buf);
    }
    spr_asmsym(buf, r->sym);
    return buf;
}

static List *litlabels;

static int32 LiteralBefore(int32 target) {
    List *p;
    for (p = litlabels; p != NULL; p = cdr_(p))
        if (car_(p) <= target) return car_(p);
    return 0;
}

static char *disass_cb(dis_cb_type type, int32 offset, unsigned32 address, int w, void *cb_arg, char *buf) {
    RelAddrRec *r = (RelAddrRec *)cb_arg;
    IGNORE(w);
    *buf = 0;
    if (type == D_BORBL) {
        if (cb_arg == NULL)
            printlabelname(buf, "", "", address, procname);
        else
            spr_asmsym(buf, r->sym);
    } else if (type == D_ADDPCREL) {
        if (r != NULL)
            buf = disass_adrl(r, buf, address + offset + r->offset);
        else
            printlabelname(buf, "#", "-.-8", address+offset, procname);
    } else if (type == D_SUBPCREL) {
        if (r != NULL)
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
        if (litaddr == target)
            printlabelname(buf, "[pc, #", "-.-8]", address, procname);
        else {
            char b[8];
            sprintf(b, "+%ld)-.-8", target - litaddr);
            printlabelname(buf, "[pc, #(", b, litaddr - codebase, procname);
        }
    } else if (type == D_LOAD || type == D_STORE) {
        if (r != NULL) {
            sprintf(buf, "%ld+", offset);
            buf += strlen(buf);
            spr_asmsym(buf, r->sym);
        }
    }
    return buf+strlen(buf);
}

typedef struct Import {
    struct Import *next;
    Symstr  *sym;
    int32   patch;
} Import;

static char  *asm_needslabel; /* a bitmap, 1 bit per code word */

#define needslabel(widx) (((widx) & 0x80000000) ? 0 : (asm_needslabel[(widx) >> 3] &  (1 << ((widx)&7))))
#define setlabbit(widx)  (((widx) & 0x80000000) ? 0 : (asm_needslabel[(widx) >> 3] |= (1 << ((widx)&7))))

static void NoteLiteralLabel(int32 q) {
    if (needslabel(q / 4))
        litlabels = (List *)global_cons2(SU_Other, litlabels, q+codebase);
}

static void killasmlabel(int32 wordoffset)
{
/* Ensure that jopcode labels are present only for instructions, not data items */
    LabList *p, *prev = NULL;
    int32 offset = wordoffset * 4L;
    for ( p = asm_lablist ; p != NULL ; prev = p, p = p->labcdr)
        if ((p->labcar->u.defn & 0x00ffffff) == offset) {
            p = (LabList *) discard2((VoidStar) p);
            if (prev == NULL)
                asm_lablist = p;
            else
                prev->labcdr = p;
            return;
        }
}

static int32 immediateval(int32 w) {
    int32 shift = (w & 0xf00)>>7, val = w & 0xff;
    return (val>>shift) | (val<<(32-shift));
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
        case LIT_ADCON:
            {   Symstr *sym = find_extsym(codebase+p);
                ExtRef *xr = symext_(sym);
                if (xr->extflags & xr_defloc) setlabbit(xr->extoffset/4);
                break;
            }
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
                        int32 val = immediateval(w);
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

/* exported functions ...*/

static bool headerdone;

#if RECORD_SOURCE_LOCATION
static void output_location(MiniFileLine* fl, FILE* as)
{
    const char *file = fl->f;
    unsigned int line = fl->l;
    unsigned int col  = fl->column;

    if (file == NULL)
        return;

    if (last_fileline.f == NULL || strcmp(last_fileline.f, file) != 0) {
        indent8();
        fprintf(as, "; source-file: \"%s\", line %u\n", file, line);
        last_fileline.f = file;
        last_fileline.l = line;
        last_fileline.column = col;
    } else if (line > 0 && (line != last_fileline.l || col != last_fileline.column)) {
        indent8();
        fprintf(as, "; line: %u %u\n", line, col);
        last_fileline.l = line;
        last_fileline.column = col;
    }
}
#endif

static void asm_areadef(char const *name, char const *attrib1, char const *attrib2)
{
    newline();
    indent8();
    indent_18_if_annotating();
    fputs("AREA ", asmstream);
    pr_asmname(name);
    fprintf(asmstream, "%s, %s\n", attrib1, attrib2);
}


static void asm_areaname(Symstr const *name, char const *attributes, bool export_area)
{   char const *s = symname_(name);
    if (export_area) {
        newline();
        indent8();
        indent_18_if_annotating();
        fputs("EXPORT  ", asmstream);
        pr_asmname(s);
        pr_unmangled_name(name);
    }
    asm_areadef(s, "", attributes);
}


void display_assembly_code(Symstr const *name)
{   uint32 q, qend;
    FILE   *as = asmstream;
    char buf[255];

    if (codep == 0)
    {
        new_area = YES;
        return;
    }
    if (new_area)
    {
        Symstr *sym = bindsym_(codesegment);
        char segname[255];

        sprintf(segname, "C$$%s", symname_(sym) + 2);
        if (!first_area)
            asm_areadef(segname, (obj_iscommoncode() ? ", COMDEF" : ""),
                        "CODE, READONLY");
        newline();
        pr_asmname(symname_(sym));
        fprintf(as, " DATA");
        pr_unmangled_name(sym);
        newline();
        first_area = NO;
        new_area = NO;
    }
    newline();
    if (name != NULL) {
        /* may be NULL for string literals from static inits   */
        procname = name;
        if (StrEq(symname_(name), "main"))
            obj_symref(libentrypoint, xr_code, 0);
        indent_18_if_annotating();
        pr_asmsym(name);
        pr_unmangled_name(name);
        newline();
#if RECORD_SOURCE_LOCATION
        if (HasFeature(Feature_AsmIncludesLocation))
            output_location(&currentfunction.start_fl, as);
#endif
    }
    asm_scancode();
    for (q = 0, qend = codep; q < qend; q += 4)    /* q is now a BYTE offset */
    {   int32 w = code_inst_(q),
              f = code_flag_(q);
        VoidStar aux = code_aux_(q);

#if RECORD_SOURCE_LOCATION
        if (HasFeature(Feature_AsmIncludesLocation) &&
            code_fileline_f(q) != NULL &&
            (f == LIT_RELADDR || f == LIT_OPCODE))
        {
            output_location(&code_fileline_(q), as);
        }
#endif

        if (needslabel(q / 4))
        {   indent_18_if_annotating();
            printlabelname(buf, "", "\n", q, name);
            fputs(buf, as);
        }
        if (HasFeature(Feature_Annotate))
            fprintf(as, "%.6lx  %.8lx  ", (long)(q + codebase), lx_arg(w));
        if (f != LIT_FPNUM2) indent8();
        switch(f)
        {
    case LIT_RELADDR:
            {   unsigned32 oldq = q;
                RelAddrRec r;
                r.sym = (Symstr *)aux; r.offset = 0; r.count = 0;
                r.buf = buf;
                if ((w & 0x0f000000L) == 0x02000000L) {
                    int32 rd = (w >> 12) & 0xfL;
                    while (q+4 < qend && code_flag_(q+4) == LIT_OPCODE &&
                           !needslabel((q+4)/4)) {
                        int32 w1 = code_inst_(q+4);
                        if (((w1 ^ w) & 0xfff00000L) != 0 ||
                            ((w1 >> 12) & 0xfL) != rd ||
                            ((w1 >> 16) & 0xfL) != rd)
                            break;
                        q += 4;
                        r.count++; r.offset += immediateval(w1);
                    }
                }
                disass(w, oldq, buf, (void *)&r, disass_cb);
                fputs(buf, as);
                pr_unmangled_name((Symstr *)aux);
                break;
            }
    case LIT_OPCODE:
            disass(w, q, buf, (void *)0, disass_cb);
            fputs(buf, as);
            break;
    case LIT_STRING:
            NoteLiteralLabel(q);
            {   int32 tmpw = w;
                unsigned char *uc = (unsigned char *)&tmpw;
                fprintf(as, "DCB      0x%.2x,0x%.2x,0x%.2x,0x%.2x",
                    uc[0], uc[1], uc[2], uc[3]);
            }
            if (HasFeature(Feature_Annotate))
                fprintf(as, "         ; "), pr_chars(w);
            break;
    case LIT_NUMBER:
            NoteLiteralLabel(q);
            fprintf(as, "DCD      0x%.8lx", lx_arg(w));
            break;
    case LIT_ADCON:
            NoteLiteralLabel(q);
            {   Symstr *sym = find_extsym(codebase+q);
                fputs("DCD      ", as); pr_asmsym(sym);
                if (w != 0) fprintf(as, "+0x%lx", lx_arg(w));
                pr_unmangled_name(sym);
            }
            break;
    case LIT_FPNUM:
            NoteLiteralLabel(q);
            {   char *s = (char *)aux;
                if (*s != '<') {
                    fprintf(as, "DCFS     %s", s);
                } else {
                    fprintf(as, "DCD      0x%.8lx", lx_arg(w));
                }
            }
            break;
    case LIT_FPNUM1:
            NoteLiteralLabel(q);
            {   char *s = (char *)aux;
                if (*s != '<') {
                    fprintf(as, "DCFD     %s", s);
                } else {
                    fprintf(as, "DCD      0x%.8lx, 0x%.8lx",
                                lx_arg(w), lx_arg(code_inst_(q+4)) );
                }
            }
            break;
    case LIT_FPNUM2:    /* all printed by the FPNUM1 */
            if (HasFeature(Feature_Annotate)) break; else continue;
    case LIT_INT64_1:
            NoteLiteralLabel(q);
            fprintf(as, "DCD      0x%.8lx, 0x%.8lx", lx_arg(w), lx_arg(code_inst_(q+4)) );
            break;
    case LIT_INT64_2:    /* all printed by the FPNUM1 */
            if (HasFeature(Feature_Annotate)) break; else continue;
    default:
            fputs("???", as);
        }
        newline();
    }
}

void asm_header(void)
{
    char b[64];
    litlabels = NULL;
    first_area = YES;
    new_area = NO;
    disass_sethexprefix("&");
    disass_setregnames(regnames, fregnames);
    headerdone = YES;
    strcpy(b, "Lib$$Request$$armlib$$");
    target_lib_variant(&b[22]);
    obj_symref(sym_insert_id(b), xr_code+xr_weak, 0);
    fprintf(asmstream, "; generated by %s\n", CC_BANNER);
    if (HasFeature(Feature_Annotate)) return;   /* do not bore interactive user */
    asm_areadef("C$$code", (obj_iscommoncode() ? ", COMDEF" : ""),
                "CODE, READONLY");
}

static void asm_outextern(void)
{
    ExtRef *x;
    int first;

    first = 1;
    for (x = obj_symlist; x != 0; x = x->extcdr) {
        int32 flags = x->extflags;

        if (!(flags & xr_objflg) && !(flags & xr_defloc) && (flags & xr_defext)) {
            if (first) newline();
            first = 0;
            indent8();
            indent_18_if_annotating();
            fprintf(asmstream, "EXPORT ");
            pr_asmsym(x->extsym);
            fprintf(asmstream, "\n");
        }
    }
    first = 1;
    for (x = obj_symlist; x != 0; x = x->extcdr) {
        int32 flags = x->extflags;

        if (!(flags & xr_objflg) && !(flags & xr_defloc)
            && !(flags & xr_defext)
#ifdef CONST_DATA_IN_CODE
            && x->extsym != bindsym_(constdatasegment)
#endif
            ) {
            /* COMMON data dealt with earlier */
            if (!(flags & xr_code) && (x->extoffset > 0)) continue;
            if (first) newline();
            first = 0;
            indent8();
            indent_18_if_annotating();
            fprintf(asmstream, "IMPORT ");
            pr_asmsym(x->extsym);
            if (x->extflags & xr_weak)
              fprintf(asmstream, ", WEAK");
            fprintf(asmstream, "\n");
        }
    }
}

void asm_setregname(int regno, char const *name) {
    if (regno < R_F0) {
        if (headerdone) fprintf(asmstream, "%s RN %d\n", name, regno);
        regnames[regno] = name;
    } else {
        regno -= R_F0;
        if (headerdone) fprintf(asmstream, "%s FN %d\n", name, regno);
        fregnames[regno] = name;
    }
}

static void asm_checklenandrpt(int32 len, int lenwanted, int32 rpt, int32 val) {
    bool norpt = NO;
    if (lenwanted < 0) norpt = YES, lenwanted = -lenwanted;
    if (len != lenwanted)
        syserr(syserr_asm_data, (long)len);
     if (rpt != 1 && (val != 0 || norpt))
        syserr(syserr_asm_trailer1, (long)rpt, (long)val);
}

static void asm_data(DataInit *p, int constdata)
{ FILE *as = asmstream;
  int32 offset = 0;
  for (; p != 0; p = p->datacdr)
  { int32 sort = p->sort;
    IPtr rpt = p->rpt, len = p->len;
    FloatCon *ptrval = (FloatCon *)p->val;
    union { unsigned32 l;
            unsigned16 w[2];
            unsigned8 b[4];
            /* FloatCon *f; may be bigger than unsigned32 */
          } val;
    val.l = p->val;
    indent_18_if_annotating();
    if (sort != LIT_LABEL) indent8();
    switch (sort)
    {   case LIT_LABEL:
            pr_asmsym((Symstr *)rpt);
            if (constdata) fprintf(as, " DATA");
            pr_unmangled_name((Symstr *)rpt);
            break;
        default:  syserr(syserr_asm_trailer, (long)sort);
        case LIT_BBBB:
            asm_checklenandrpt(len, -4, rpt, val.l);
            fprintf(as, "DCB      0x%.2x,0x%.2x,0x%.2x,0x%.2x",
                        val.b[0], val.b[1], val.b[2], val.b[3]);
            break;
        case LIT_BBBX:
            asm_checklenandrpt(len, -3, rpt, val.l);
            fprintf(as, "DCB      0x%.2x,0x%.2x,0x%.2x", val.b[0], val.b[1], val.b[2]);
            break;
        case LIT_BBX:
            asm_checklenandrpt(len, -2, rpt, val.l);
            fprintf(as, "DCB      0x%.2x,0x%.2x", val.b[0], val.b[1]);
            break;
        case LIT_BXXX:
            asm_checklenandrpt(len, -1, rpt, val.l);
            fprintf(as, "DCB      0x%.2x", val.b[0]);
            break;
        case LIT_HH:
            asm_checklenandrpt(len, -4, rpt, val.l);
            fprintf(as, "DCW%c     0x%.4x,0x%.4x", offset & 1 ? 'U' : ' ',
                                  val.w[0], val.w[1]);
            break;
        case LIT_HX:
            asm_checklenandrpt(len, -2, rpt, val.l);
            fprintf(as, "DCW%c     0x%.4x", offset & 1 ? 'U' : ' ', val.w[0]);
            break;
        case LIT_BBH:
            asm_checklenandrpt(len, -4, rpt, val.l);
            fprintf(as, "DCB      0x%.2x,0x%.2x", val.b[0], val.b[1]);
            newline(); indent_18_if_annotating(); indent8();
            fprintf(as, "DCW%c     0x%.4x", offset & 1 ? 'U' : ' ', val.w[1]);
            break;
        case LIT_HBX:
            asm_checklenandrpt(len, -3, rpt, val.l);
            fprintf(as, "DCW%c     0x%.4x", offset & 1 ? 'U' : ' ', val.w[0]);
            newline(); indent_18_if_annotating(); indent8();
            fprintf(as, "DCB      0x%.2x", val.b[2]);
            break;
        case LIT_HBB:
            asm_checklenandrpt(len, -4, rpt, val.l);
            fprintf(as, "DCW%c     0x%.4x", offset & 1 ? 'U' : ' ', val.w[0]);
            newline(); indent_18_if_annotating(); indent8();
            fprintf(as, "DCB      0x%.2x,0x%.2x", val.b[2], val.b[3]);
            break;
        case LIT_NUMBER:
            asm_checklenandrpt(len, 4, rpt, val.l);
            if (len != 4) syserr(syserr_asm_data, (long)len);
            if (rpt == 1)
                fprintf(as, "DCD%c     0x%.8lx", offset & 3 ? 'U' : ' ', lx_arg(val.l));
            else /* val.l already checked to be zero */
                fprintf(as, "%%        %ld", (long)(rpt*len));
            break;
        case LIT_FPNUM:
        {   FloatCon *f = ptrval;
            char *s = f->floatstr;
            if (*s != '<') {
                fprintf(as, "DCF%c     %s", (len == 8) ? 'D' : 'S', s);
            } else if (len == 4) {
                fprintf(as, "DCD      0x%.8lx", lx_arg(f->floatbin.fb.val));
            } else {
                fprintf(as, "DCD      0x%.8lx, 0x%.8lx",
                        lx_arg(f->floatbin.db.msd), lx_arg(f->floatbin.db.lsd));
            }
            break;
        }
        case LIT_ADCON:              /* (possibly external) name + offset */
            while (rpt--)
            {
#if (sizeof_ptr == 2)
                fputs("DCW      ", as);
#else
                fputs("DCD      ", as);
#endif
                pr_asmsym((Symstr *)len);
                pr_unmangled_name((Symstr *)len);
                if (val.l != 0) fprintf(as, "+0x%lx", lx_arg(val.l));
                if (rpt) {newline();  indent_18_if_annotating();  indent8(); }
            }
            break;
    }
    offset = (offset + len) & 3;
    newline();
  }
}

typedef struct ExtRefList {
        struct ExtRefList *cdr;
        ExtRef *car;
} ExtRefList;

static void asm_pad(int32 len)
{   indent8();
    indent_18_if_annotating();
    fprintf(asmstream, "%% %ld\n", (long)len);
}

void asm_trailer(void)
{ FILE *as = asmstream;
#ifdef CONST_DATA_IN_CODE
  if (constdata_size() != 0) {
    asm_areadef("C$$constdata", "", "DATA, READONLY");
    newline();
    pr_asmsym(bindsym_(constdatasegment));
    newline();
    asm_data(constdata_head(), 0);
  }
#endif
  if (data_size() != 0)
  {
    asm_areaname(data_sym, "DATA", NO);
    newline();
    asm_data(data_head(), 0);
  }
  if (bss_size != 0)
  { int32 n = 0;
    ExtRef *x = obj_symlist;
    ExtRefList *zisyms = NULL;
    asm_areaname(bss_sym, "NOINIT", NO);
    newline();
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
      indent_18_if_annotating();
      pr_asmsym(x->extsym);
      pr_unmangled_name(x->extsym);
      newline();
    }
    if (n != bss_size) asm_pad(bss_size-n);
  }
  if (adconpool.size != 0) {
    asm_areaname(adcon_sym, "BASED sb", NO);
    asm_data(adconpool.head, 0);
  }
  { CommonDef *p;
    for (p = commondefs; p != NULL; p = p->next)
    { asm_areaname(p->name, "COMDEF", YES);
      asm_data(p->data.head, 0);
    }
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
          asm_areaname(s, "COMMON, NOINIT", YES);
          asm_pad(len);
        }
      }
    }
  }
  if (!HasFeature(Feature_Annotate))
      asm_outextern();
  newline();
  indent8();
  indent_18_if_annotating();
  fputs("END\n", as);
  headerdone = NO;
}

#endif

/* end of arm/asm.c */
