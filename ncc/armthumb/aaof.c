/*
 * C compiler file aaof.c, version 18d
 * Copyright (C) CodeMist Ltd., 1988
 * Copyright (C) Acorn Computers Ltd., 1988
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

#ifdef __STDC__
#include <string.h>
#else
#define SEEK_SET  0
#include <strings.h>
#include <stddef.h>
#endif

#include "globals.h"
#include "mcdep.h"
#include "mcdpriv.h"
#include "errors.h"
#include "xrefs.h"
#include "store.h"
#include "codebuf.h"
#include "version.h"
#include "builtin.h"             /* for codesegment... */
#include "bind.h"                /* for sym_insert_id() */
#include "errors.h"
#include "chunkfmt.h"
#include "aof.h"
#include "cg.h"                  /* has_main */
#include "armops.h"
#include "vargen.h"

#ifdef PUT_FILE_NAME_IN_AREA_NAME
#  include "fname.h"
#  include "compiler.h"
#endif

static int32 obj_fwrite_cnt;

static bool byte_reversing = 0;
    /* byte_reversing == (host_lsbytefirst != target_lsbytefirst).        */
    /* (But faster to test one static per word than 2 externs per word).  */

static void obj_fwrite(void const *buff, int32 n, int32 m, FILE *f)
{   if (debugging(DEBUG_OBJ))
    {   int32 i;
        fprintf(f, "%.6lx:", (long)obj_fwrite_cnt);
        obj_fwrite_cnt += n*m;
        for (i=0; i<n*m; i++)
          fprintf(f, " %.2x", ((uint8 const *)buff)[i]);
        fprintf(f, "\n");
    }
    else if (n == 4 && byte_reversing)
    {   /* word by word output */
        uint32 const *p;
        for (p = (uint32 const *)buff;  m > 0;  --m, ++p)
        {   uint32 w, v = *p;
        /* Amazingly, this generates better code on an ARM than the more  */
        /* obvious and transparent way to reverse the bytes. A future cse */
        /* may turn the simulations of ROR into ROR, giving optimal code. */
        /* t = v^(v ROR 16); t &= ~0xff0000; v = v ROR 8; v = v^(t >> 8). */
            uint32 t = v ^ ((v << 16) | (v >> 16));        /* ...v ROR 16 */
            t &= ~0xff0000;
            v = (v << 24) | (v >> 8);                      /* v = v ROR 8 */
            w = v ^ (t >> 8);
            fwrite(&w, 4, 1, f);
        }
    }
    else if (n == 2 && byte_reversing) {
        uint16 const *p;
        for (p = (uint16 const *)buff; m > 0; --m, ++p) {
            uint16 v = *p;
            v = (v >> 8) | (v << 8);
            fwrite(&v, 2, 1, f);
        }
    }
    else
        fwrite(buff, (size_t)n, (size_t)m, f);
}

#ifdef TARGET_HAS_HALFWORD_INSTRUCTIONS
static int32 obj_pad(int32 size)
{
    int buff = 0;

    if (size & 3) obj_fwrite(&buff, 1, 4 - (size & 3), objstream);
    size = (size + 3) & ~3;
    return size;
}
#endif

FILE *objstream;

typedef struct DebugAreaDesc DebugAreaDesc;
struct DebugAreaDesc {
    DebugAreaDesc *cdr;
    Symstr *sym;
    Symstr *refsym;
    int32 size, nrelocs;
};
static DebugAreaDesc *debugareas, **debugareas_tail;
static DebugAreaDesc *curdebugarea;

#ifdef TARGET_HAS_DEBUGGER
void obj_writedebug(void const *p, int32 n)
/* for armdbg.c */
{   if (n & DBG_INTFLAG) {
        obj_fwrite(p, 4, n & ~DBG_INTFLAG, objstream);
        n *= 4;
    } else if (n & DBG_SHORTFLAG) {
        obj_fwrite(p, 2, n & ~DBG_SHORTFLAG, objstream);
        n = (n & ~DBG_SHORTFLAG) * 2;
    } else
        obj_fwrite(p, 1, n, objstream);
    curdebugarea->size += n;
}
#endif

/* AOF output routines:  Note that much of the nastiness here
 * is due to ACORN's AOF file spec which requires AOF files to
 * output areas contiguously followed by their relocation directives.
 * For a better alternative see the IBM 360 object file format in
 * which they may be mixed at a big saving in store in each compiler
 * and only marginal cost to the linker.
 */

#define OBJ_DUMMYSYM   xr_objflg
#define OBJ_REPLACEBYAREA xr_objflg4
#define OBJ_DELETED    xr_objflg5
#define OBJ_MAXCHUNKS  8
#define OBJ_NUMCHUNKS  5

/* imports: codebase, dataloc, bss_size */
static int32 constdatabase, extablebase, exhandlerbase;
static int32 ncommonareas, ncodeareas, nareas, codeareasize;
static int32 ndatarelocs, nadconrelocs;
static int32 obj_stringpos, obj_symcount, aof_hdr_offset;
Symstr *data_sym, *bss_sym, *adcon_sym, *ddtor_sym,
  *extable_sym, *exhandler_sym;

ExtRef *obj_symlist;
CodeXref *codexrefs;
DataXref *dbgxrefs;

/* An aof_xarea is an aof_area with a chain field and a Symstr field.   */
/* area_size, area_nrelocs, area_attributes are set early and later     */
/* area_base and area_name (these shared with asv and anext once).      */
typedef struct aof_xarea {
    aof_area aaxa;
    struct { Symstr *asv; struct aof_xarea *anext; } aaxb;
} aof_xarea;

static aof_xarea _areahdr_, *codeareap, *codeareaq;

static void obj_end_codearea(void);
static void obj_start_codearea(void);

static bool thisCodeAreaIsEmpty;

void obj_codewrite(Symstr *name)
/* (name == 0 && codep == 0) => called from codebuf_reinit1()             */
/*                bindsym_(codesegment) is the new code segment name.     */
/* (name == 0 && codep != 0) => called after string literal...            */
/* (name != 0) => called from show_code() for function 'name'.            */
/*                called after each function or string lit is compiled.   */
{
    if (codep == 0)
    {   if (name == 0)
        {   obj_end_codearea();
            obj_start_codearea();
            thisCodeAreaIsEmpty = YES;
        }
        return;
    }
    thisCodeAreaIsEmpty = NO;
    if (byte_reversing)
    {   int32 i = 0, n = codep, w;
        while (i < n)
        {
/* ECN: Support for halfword stream */
#ifdef TARGET_HAS_HALFWORD_INSTRUCTIONS
            int32 f = code_flag_(i);
            /* If this is a halfword style thing */
            if (f == LIT_OPCODE || f == LIT_BB || f == LIT_H) {
                unsigned16 hw;

                hw = code_hword_(i);
                if (f == LIT_BB) hw = (hw >> 8) | (hw << 8);
                obj_fwrite(&hw, 2, 1, objstream);
                i += 2;
                continue;
            }
#endif
            w = totargetsex(code_inst_(i), code_flag_(i));
            obj_fwrite(&w, 4, 1, objstream);
            i += 4;
        }
    }
    else
    {   int32 i = 0;
        while ((codep>>2) - CODEVECSEGSIZE*i > CODEVECSEGSIZE)
            obj_fwrite(code_instvec_(i), 4, CODEVECSEGSIZE, objstream), i++;
/* ECN: code block may not be a multiple of 4 */
#ifdef TARGET_HAS_HALFWORD_INSTRUCTIONS
        obj_fwrite(code_instvec_(i), 2, (codep>>1)-CODEVECSEGSIZE*i*2, objstream);
#else
        obj_fwrite(code_instvec_(i), 4, (codep>>2)-CODEVECSEGSIZE*i, objstream);
#endif
    }
    if (ferror(objstream)) cc_fatalerr(obj_fatalerr_io_object);
}

static CommonDef dataarea;
CommonDef *commondefs;
static CommonDef *curcommon;

static void setcurcommon(CommonDef *com)
{
    copy_datadesc(&curcommon->data);
    restore_datadesc(&com->data);
    curcommon = com;
}

static CommonDef *findcommondef(int32 i)
{
    CommonDef *p = commondefs;
    int32 n;
    for (n = i; --n > 0; p = p->next)
        if (p == NULL) syserr(syserr_commondef, (long)i);
    return p;
}

void obj_common_start(Symstr *name)
{
    CommonDef *p; CommonDef **q = &commondefs;
    int i;
    for (p = commondefs, i = 1; p != NULL; q = &p->next, p = p->next, i++)
        if (p->name == name)
        {    cc_err(obj_err_common, name);
             break;
        }
    if (p == NULL)
    {   p = (CommonDef *) GlobAlloc(SU_Data, sizeof(CommonDef));
        p->next = NULL;
        p->data.head = p->data.tail = NULL; p->data.size = 0;
        p->name = name; p->index = i;
        setcurcommon(p);
        *q = p;
        obj_symref(name, xr_data+xr_defext+xr_cblock, 0);
    } else
        setcurcommon(p);
}

void obj_common_end(void)
{   if (curcommon->refsize != 0 && data_size() < curcommon->refsize)
        cc_err(obj_err_common1, curcommon->name);
    setcurcommon(&dataarea);
}

/* the remaining fns are intended to be internal only */

static int32 obj_checksym_1(Symstr *s)
{   ExtRef *x = symext_(s);
    if (x != NULL) {
      if (x->extflags & OBJ_DUMMYSYM) return x->extoffset;
      if (!(x->extflags & OBJ_REPLACEBYAREA)) return REL_A + x->extindex;
      s = x->codesym;
      x = symext_(s);
      if (x != NULL) return x->extindex-1;
    }
    syserr(syserr_obj_checksym, s);
    return 0;
}

static int32 obj_checksym(Symstr *s) {
    int32 res = obj_checksym_1(s);
    if (res >= 0) return res;
    syserr(syserr_obj_checksym, s);
    return 0;
}

static void obj_outsymtab(void)
{   ExtRef *x;
    int32 stringpos = 4;
    obj_symlist = (ExtRef *)dreverse((List *)obj_symlist);
                  /* oldest = smallest numbered first */
    for (x = obj_symlist; x != NULL; x = x->extcdr)
    {   Symstr *s = x->extsym;
        if (x->extflags & OBJ_DUMMYSYM) x->extoffset = stringpos;
        if (!(x->extflags & OBJ_DELETED))
            stringpos += (int32) strlen(symname_(s)) + 1;
    }
    stringpos = 4;
    for (x = obj_symlist; x != NULL; x = x->extcdr)
    {   Symstr *s = x->extsym;
        int32 flags = x->extflags;
        if (debugging(DEBUG_OBJ))
            cc_msg("sym$r%lx ", s, (long)flags);
        if (!(flags & (OBJ_DUMMYSYM+OBJ_DELETED)))
        { aof_symbol sym;
#ifdef TARGET_IS_THUMB
          int32 at = flags & xr_defloc ? SYM_LOCALDEFAT + SYM_THUMB :
                     flags & xr_defext ? SYM_GLOBALDEFAT + SYM_THUMB :
                     flags & xr_weak   ? SYM_WEAKAT+SYM_REFAT :
                                         SYM_REFAT;
#ifdef THUMB_CPLUSPLUS
          if (flags & xr_code_32) at &= ~SYM_THUMB;
#endif
#else
          int32 at = flags & xr_defloc ? SYM_LOCALDEFAT :
                     flags & xr_defext ? SYM_GLOBALDEFAT :
                     flags & xr_weak   ? SYM_WEAKAT+SYM_REFAT :
                                         SYM_REFAT;
#endif
          sym.sym_name = stringpos;
          /* revision soon to set data if (code & dataincode) ? */
          if ((flags & xr_code) && (flags & xr_dataincode)) at |= SYM_DATAAT;
          /* ECN: constdata must have data bit set too otherwise linker may generate
           *      wrong value (ie address + 1)
           */
          if (flags & xr_constdata) at |= SYM_DATAAT;
          if (flags & aof_fpreg) at |= SYM_FPREGAT;
          if (!(flags & aof_usessb) && (flags & aof_leaf)) at |= SYM_LEAFAT;
          sym.sym_value = x->extoffset;
              /* always zero unless xr_defloc+xr_defext */
          if (xr_flagtoidx_(flags) != 0)
          {   CommonDef *p = findcommondef(xr_flagtoidx_(flags));
              if (flags & xr_cblock) p->stringpos = stringpos;
              sym.sym_areaname = p->stringpos;
          }
          /* The next line knows there are no symbols in the dbg segment */
          else if (flags & (xr_defloc+xr_defext))
          {   Symstr *area;
              if (flags & xr_code)
                  area = x->codesym;
              else if (flags & xr_data)
                  area = data_sym;
              else if (flags & xr_constdata)
                  area = codeareaq->aaxb.asv,
                  sym.sym_value += constdatabase;
              else if (flags & xr_bss)
                  area = bss_sym;
              else
                  area = adcon_sym;
              sym.sym_areaname = obj_checksym(area);

          } else if (x->extoffset != 0)
          {   /* common block */
              at = SYM_LOCALDEFAT;
              sym.sym_value = 0;             /* offset MUST be 0...         */
              sym.sym_areaname = stringpos;  /* relative to the common AREA */
/* Hack: place a small int in pointer field x->codesym (find 'IPtr').   */
              x->codesym = (Symstr *)(IPtr)stringpos;
          }
          else
              sym.sym_areaname = 0;
          sym.sym_AT = at;
          obj_fwrite(&sym, 4, sizeof(sym)/4, objstream);
        }
        if (!(x->extflags & OBJ_DELETED))
            stringpos += (int32) strlen(symname_(s)) + 1;
    }
    obj_stringpos = stringpos;
    obj_fwrite(&obj_stringpos, 4, 1, objstream);
    for (x = obj_symlist; x != NULL; x = x->extcdr)
    {   Symstr *s = x->extsym;
        if (!(x->extflags & OBJ_DELETED))
            obj_fwrite(symname_(s), 1, (int32)strlen(symname_(s))+1, objstream);
    }
    while (stringpos & 3) {putc(0, objstream);  ++stringpos;}
    obj_stringpos = stringpos;
}

static void obj_outcommonheaders(bool output)
{
    if (ncommonareas) {
        ExtRef *x;
        aof_area a;
        CommonDef *p;

        /* got at least one so worth counting properly... */
        ncommonareas = 0;
        a.area_nrelocs = 0;
        a.area_base = 0;
        for (p = commondefs; p != NULL; p = p->next) {
            ++ncommonareas;
            if (output == NO) continue;
            a.area_name = p->stringpos;
            a.area_attributes = 2 + AOF_COMDEFAT;
            a.area_size = (p->data.size + 3) & ~3; /* must be a multiple of 4 */
            obj_fwrite(&a, 4, sizeof(a)/4, objstream);
        }
        for (x = obj_symlist; x != NULL; x = x->extcdr)
        {   int32 flags = x->extflags;
            int32 len = x->extoffset;
            if (!(flags & (xr_defloc + xr_defext + xr_code +
                           OBJ_DELETED + OBJ_DUMMYSYM + OBJ_REPLACEBYAREA)) &&
                len > 0) {
                  /* common reference ... */
                ++ncommonareas;
                if (output == NO) continue;
/* Hack: get a small int from pointer field x->codesym (find 'IPtr').   */
                a.area_name = (int32)(IPtr)x->codesym;
                a.area_attributes = 2 + AOF_COMREFAT + AOF_0INITAT;
                a.area_size = (len + 3) & ~3;
                    /* must be a multiple of 4 */
                obj_fwrite(&a, 4, sizeof(a)/4, objstream);
            }
        }
    }
}

typedef struct RelocationPatch RelocationPatch;

struct RelocationPatch {
    RelocationPatch *cdr;
    long fpos;
    Symstr *sym;
    int32 flags;
};

static RelocationPatch *relocationpatches;

static int32 obj_coderelocation(void)
{   CodeXref *x;
    int32 n = 0;
    aof_reloc r;
    for (x = codexrefs; x!=NULL; x = x->codexrcdr)
    {   Symstr *s = x->codexrsym;
        int32 ix = obj_checksym_1(s);
        RelocationPatch *p = NULL;
        if (ix < 0) {
          p = (RelocationPatch *)GlobAlloc(SU_Xref, sizeof(RelocationPatch));
          ix = 0;
        }
        r.rel_offset = x->codexroff & 0xffffff;
        r.rel_flags = REL_TYPE2 + REL_LONG + ix;
        switch (x->codexroff & 0xff000000)
        {
#ifdef TARGET_HAS_DATA_VTABLES
case X_absreloc:    /* DCD <sym> - for vtables */
            if (debugging(DEBUG_OBJ)) cc_msg("absreloc$r ", s);
            break;
#endif
case X_DataAddr1:   /* PC rel ref to external: sequence to be relocated = 2 */
            r.rel_flags |= REL_R | REL_INSTR | (2<<29);
            if (debugging(DEBUG_OBJ)) cc_msg("pcreloc2$r ", s);
            break;
case X_PCreloc:     /* PC rel ref to external */
#ifdef TARGET_IS_THUMB
            /* ECN: disgusting bodge really, bit 0 of offset => Thumb reloc */
            r.rel_offset += 1; /* ??? */
#ifdef THUMB_CPLUSPLUS
case X_PCreloc_32:
#endif
#endif
            r.rel_flags |= REL_R | REL_INSTR;
            if (debugging(DEBUG_OBJ)) cc_msg("pcreloc$r ", s);
            break;
case X_TailCall:     /* as PCreloc, but used in tailcall */
            r.rel_flags |= REL_R | REL_B | REL_INSTR;
            if (debugging(DEBUG_OBJ)) cc_msg("tailcall$r ", s);
            break;
case X_DataVal:
            r.rel_flags |= REL_B | REL_INSTR;
#ifdef TARGET_IS_THUMB
            r.rel_offset += 1;
#endif
            if (debugging(DEBUG_OBJ)) cc_msg("basereloc$r ", s);
            break;
case X_backaddrlit: /* abs ref to external */
            if (debugging(DEBUG_OBJ)) cc_msg("addreloc$r ", s);
            break;
default:
            syserr(syserr_obj_codereloc, (long)x->codexroff);
            continue;
        }
        if (p != NULL) {
          obj_fwrite(&r.rel_offset, 4, 1, objstream);
          cdr_(p) = relocationpatches;
          p->fpos = ftell(objstream);
          p->sym = s;
          p->flags = r.rel_flags;
          relocationpatches = p;
          obj_fwrite(&r.rel_flags, 4, 1, objstream);
        } else
          obj_fwrite(&r, 4, sizeof(r)/4, objstream);
        n++;
    }
    codexrefs = 0;
    return n;
}

/* obj_datarelocation() is now also used for debug table relocation. */
static int32 obj_datarelocation(DataXref *x, int32 offset)
{   int32 n = 0;
    aof_reloc r;
    for (; x!=NULL; x = x->dataxrcdr)
    {   Symstr *s = x->dataxrsym;
        /* all data relocs are X_backaddrlit (abs ref) so far */
        r.rel_offset = x->dataxroff+offset;
        r.rel_flags = REL_TYPE2 + REL_LONG + obj_checksym(s);
        obj_fwrite(&r, 4, sizeof(r)/4, objstream);
        if (debugging(DEBUG_OBJ)) cc_msg("data reloc $r ", s);
        n++;
    }
    return n;
}

static void obj_writedata(DataInit *p)
/* follows gendc exactly! */
{ for (; p != NULL; p = p->datacdr)
  { int32 rpt = p->rpt, sort = p->sort, len = p->len;
    unsigned32 val = p->val;
    IPtr ptrval = p->val;
    switch (sort)
    {   case LIT_LABEL:   /* name only present for c.armasm */
            break;
        default:  syserr(syserr_obj_gendata, (long)sort);
        case LIT_BXXX:    /* The following are the same as LIT_NUMBER       */
        case LIT_BBX:     /* for cross-sex compilation                      */
        case LIT_BBBX:
        case LIT_BBBB:
        case LIT_HX:
        case LIT_HH:
        case LIT_BBH:
        case LIT_HBX:
        case LIT_HBB:
            if (byte_reversing) {
                unsigned32 t;
                val = totargetsex(val, (int)sort);
                t = val ^ ((val << 16) | (val >> 16));       /* ...v ROR 16 */
                t &= ~0xff0000;
                val = (val << 24) | (val >> 8);              /* v = v ROR 8 */
                val = val ^ (t >> 8);
            }
            while (rpt-- != 0) obj_fwrite(&val, 1, len, objstream);
            break;
        case LIT_NUMBER:
            if (len != 4) syserr(syserr_obj_datalen, (long)len);
            /* drop through */
        case LIT_ADCON:              /* (possibly external) name + offset */
            /* beware: sex dependent... */
            while (rpt-- != 0) obj_fwrite(&val, 4, 1, objstream);
            break;
        case LIT_FPNUM:
          { FloatCon *fc = (FloatCon *)ptrval;
            /* do we need 'len' when the length is in fc->floatlen?? */
            if (len != 4 && len != 8)
                syserr(syserr_obj_data1, (long)rpt, (long)len, fc->floatstr);
            /* The following strage code ensures that doubles are correctly */
            /* sex-reversed if required to be - obj_fwrite() only reverses  */
            /* items of length 4... This is a trap for the unwary.          */
            while (rpt-- != 0)
            {   obj_fwrite(&(fc->floatbin.db.lsd), 4, 1, objstream);
                if (len == 4) continue;
                obj_fwrite(&(fc->floatbin.db.msd), 4, 1, objstream);
            }
          }
          break;
    }
  }
}

static int32 obj_outcommonareas(void)
{
    CommonDef *p;
    int32 size = 0;
    for (p = commondefs; p != NULL; p = p->next) {
        obj_writedata(p->data.head);
        size += p->data.size;
    }
    return size;
}

/* exported functions... */
int32 obj_symref(Symstr *s, int flags, int32 loc)
{   ExtRef *x;
    if ((x = symext_(s)) == NULL) /* saves a quadratic loop */
    {   if (obj_symcount >= 0x10000)
            cc_fatalerr(armobj_fatalerr_toomany);
        x = (ExtRef*) GlobAlloc(SU_Xsym, sizeof(ExtRef));
        x->extcdr = obj_symlist,
        x->extsym = s,
        x->extflags = 0,
        x->extoffset = 0,
        x->codesym = 0;
        reg_setallused(&x->usedregs);
        if (flags & OBJ_DUMMYSYM)
            x->extindex = 0;
        else if (s == bindsym_(datasegment))
            flags |= OBJ_REPLACEBYAREA | OBJ_DELETED,
            x->extindex = 0,
            x->codesym = data_sym;
        else if (s == bindsym_(ddtorsegment))
            flags |= OBJ_REPLACEBYAREA | OBJ_DELETED,
            x->extindex = 0,
            x->codesym = ddtor_sym;
        else if (s == bindsym_(bsssegment))
            flags |= OBJ_REPLACEBYAREA | OBJ_DELETED,
            x->extindex = 0,
            x->codesym = bss_sym;
        else if (s == bindsym_(codesegment))
            flags |= OBJ_REPLACEBYAREA | OBJ_DELETED,
            x->extindex = 0;
            /* codesym filled in later */
        else if (s == adconpool_lab)
            flags |= OBJ_REPLACEBYAREA | OBJ_DELETED,
            x->extindex = 0,
            x->codesym = adcon_sym;
        else if (s == extable_sym)
            flags |= OBJ_REPLACEBYAREA | OBJ_DELETED,
            x->extindex = 0,
            x->codesym = extable_sym;
        else if (s == exhandler_sym)
            flags |= OBJ_REPLACEBYAREA | OBJ_DELETED,
            x->extindex = 0,
            x->codesym = exhandler_sym;
        else {
            DebugAreaDesc *p = debugareas;
            for (; p != NULL; p = cdr_(p))
                if (s == p->refsym) {
                    flags |= OBJ_REPLACEBYAREA | OBJ_DELETED,
                    x->extindex = 0,
                    x->codesym = p->sym;
                    break;
                }
            if (p == NULL) {
#ifdef CONST_DATA_IN_CODE
                if (s == bindsym_(constdatasegment))
                    flags |= xr_dataincode;
#endif
#ifdef THUMB_CPLUSPLUS
            /* ECN: This is not pretty. What we need is something like
             * b_constdata in the binder which can be converted to
             * xr_dataincode when obj_symref is called. Can we use
             * b_memfns for this???
             */
                if (strncmp(symname_(s), "__VTABLE", 8) == 0)
                    flags |= xr_dataincode;
#endif
                x->extindex = obj_symcount++;
            }
        }
        obj_symlist = symext_(s) = x;
    }
/* The next few lines cope with further ramifications of the abolition of */
/* xr_refcode/refdata in favour of xr_code/data without xr_defloc/defext  */
/* qualification.  This reduces the number of bits, but needs more        */
/* checking in that a symbol defined as data, and then called via         */
/* casting to a code pointer may acquire defloc+data and then get         */
/* xr_code or'ed in.  Suffice it to say this causes confusion.            */
/* AM wonders if gen.c ought to be more careful instead.                  */
    if (flags & (xr_defloc+xr_defext)) {
        if (x->extflags & (xr_defloc+xr_defext)) {
        /* can only legitimately happen for a tentatively defined object  */
        /* in which case both flags and x->extflags should have type      */
        /* xr_data.  Perhaps I should check ?                             */
        } else
            x->extflags &= ~(xr_code+xr_data);
    } else if (x->extflags & (xr_defloc+xr_defext))
        flags &= ~(xr_code+xr_data);
/* end of fix.                                                            */
    x->extflags |= flags;   /* do some checking here */
    if (flags & xr_defloc+xr_defext) {     /* private or public data/code */
        if (flags & xr_code)
            x->codesym = codeareaq->aaxb.asv;
        else if (curcommon->index > 0) {
            x->extflags |= (xr_idxtoflag_(curcommon->index));
            if ((flags & xr_cblock) && x->extoffset == 0)
                ++ncommonareas;
            else
                curcommon->refsize = x->extoffset;
        }
        x->extoffset = loc;
    } else if ((loc > 0) && !(flags & xr_code)) { /* common data */
        /*
         * NOTE: 'loc' is the size of the referenced common area.
         */
        if (x->extflags & xr_cblock) {
            CommonDef *p = findcommondef(xr_flagtoidx_((int32)x->extflags));
            if (p->data.size < loc) cc_err(obj_err_common2, s);
        } else {
            int32 oldsize = x->extoffset;
            if (oldsize ==0) ++ncommonareas; /* first occurrence */
            if (loc > oldsize) x->extoffset = loc;
        }
    }
    /* The next line returns the offset of a function in the codesegment */
    /* if it has been previously defined -- this saves store on the arm  */
    /* and allows short branches on other machines.  Otherwise it        */
    /* returns -1 for undefined objects or data objects.                 */
    return ((x->extflags & (xr_defloc+xr_defext)) && (x->extflags & xr_code) &&
            (x->codesym == codeareaq->aaxb.asv) ? x->extoffset : -1);
}

/* Add a symbol even if it already exists */
int32 obj_symdef(Symstr *s, int flags, int32 loc)
{
    symext_(s) = NULL;
    return obj_symref(s, flags, loc);
}

static void obj_end_codearea()
{
    aof_area *aa = &codeareaq->aaxa;
    if (debugging(DEBUG_OBJ)) cc_msg("coderelocation\n");
#ifdef TARGET_HAS_HALFWORD_INSTRUCTIONS
    /* ECN: Individual code blocks may not be word size but the AREA must be */
    codebase = obj_pad(codebase);
#endif
    codeareasize += (aa->area_size = codebase);
    codeareasize += (aa->area_nrelocs =
                     obj_coderelocation()) * sizeof(aof_reloc);
    if (aa->area_size != 0)
        ++ncodeareas;
}

static void obj_start_codearea()
{
    Symstr *sv;
    char name[256];
    size_t l;
    aof_xarea *h = (aof_xarea *) GlobAlloc(SU_Other, sizeof(aof_xarea));
    codeareaq->aaxb.anext = h;
    codeareaq = h;
    memset(&h->aaxa, 0, sizeof(h->aaxa));
    h->aaxb.anext = NULL;
    l = strlen(symname_(bindsym_(codesegment)))+1;
    if (l > (sizeof(name)-1)) l = sizeof(name)-1;
    strncpy(name+1, symname_(bindsym_(codesegment)), l);  name[l] = 0;
    name[0] = 'C'; name[1] = '$';
    h->aaxb.asv = sv = sym_insert_id(name);
    h->aaxa.area_attributes |= AOF_CODEAT;
    if (obj_iscommoncode())
        h->aaxa.area_attributes |= AOF_COMDEFAT;
#ifdef TARGET_IS_THUMB
    if (!obj_isvtable())
        h->aaxa.area_attributes |= AOF_THUMB;
#endif
    obj_symref(sv, OBJ_DUMMYSYM, 0L);
}

#ifdef PUT_FILE_NAME_IN_AREA_NAME
static void putfilenameinareaname(char *buffer, char *basename, char *sourcefile)
{
    UnparsedName un;
    int baselen = strlen(basename); /* remember how long the basename is */
    fname_parse(sourcefile, FNAME_INCLUDE_SUFFIXES, &un);
    memcpy(buffer, basename, baselen); /* put it in the buffer */
    memcpy(&buffer[baselen], un.root, un.rlen);
    buffer[baselen+un.rlen] = 0;
}
#endif

static void obj_add_extable_area(void)
{   if (extable_size() == 0) return;
#ifdef PUT_FILE_NAME_IN_AREA_NAME
    {   char name[256];
        putfilenameinareaname(name, "x$et_", sourcefile);
        codebuf_reinit1(name);
    }
#else
    codebuf_reinit1(symname_(bindsym_(extablesegment)));
#endif
}

static void obj_add_exhandler_area(void)
{   if (exhandler_size() == 0) return;
#ifdef PUT_FILE_NAME_IN_AREA_NAME
    {   char name[256];
        putfilenameinareaname(name, "x$et_", sourcefile);
        codebuf_reinit1(name);
    }
#else
    codebuf_reinit1(symname_(bindsym_(exhandlersegment)));
#endif
}

#ifdef CONST_DATA_IN_CODE
static void obj_add_constdata_area(void)
{   if (constdata_size() == 0) return;
    obj_clearcommoncode();
#ifdef PUT_FILE_NAME_IN_AREA_NAME
    {   char name[256];
        putfilenameinareaname(name, "x$cd_", sourcefile);
        codebuf_reinit1(name);
    }
#else
    codebuf_reinit1(symname_(bindsym_(constdatasegment)));
#endif
    codeareaq->aaxa.area_attributes &= ~(AOF_CODEAT+AOF_THUMB);
}
#endif

void obj_startdebugarea(char const *name) {
    DebugAreaDesc *p = debugareas;
    for (; p != NULL; p = cdr_(p))
        if (strcmp(name, symname_(p->sym)) == 0)
            break;
    if (p == NULL) syserr("obj_startdebugarea %s", name);
    curdebugarea = p;
}

void obj_enddebugarea(char const *name, DataXref *relocs) {
    DebugAreaDesc *p = curdebugarea;
    if (p == NULL) syserr("obj_enddebugarea %s", name);
    if (p->size & 3) syserr("area %s size %x", name, p->size);
    curdebugarea = NULL;
    p->nrelocs = obj_datarelocation(relocs, 0L);
}

Symstr *obj_notedebugarea(char const *name)
{
    DebugAreaDesc *p = (DebugAreaDesc *)GlobAlloc(SU_Dbg, sizeof(*p));
    *debugareas_tail = p; debugareas_tail = &cdr_(p);
    cdr_(p) = NULL; p->sym = sym_insert_id(name);
    p->size = 0; p->nrelocs = 0;
    obj_symref(p->sym, OBJ_DUMMYSYM, 0L);
    { char s[64]; s[0] = s[1] = '$';
      strcpy(&s[2], name);
      p->refsym = sym_insert_id(s);
      obj_symref(p->refsym, xr_data, 0L);
    }
    return p->refsym;
}

void obj_init(void)
{
    debugareas = NULL; debugareas_tail = &debugareas;
    ncommonareas = ncodeareas = nareas = 0;
    codeareasize = 0, ndatarelocs = 0, nadconrelocs = 0;
    obj_stringpos = 0, obj_symcount = 0, aof_hdr_offset = 0;
    obj_symlist = NULL;
    codexrefs = NULL, dbgxrefs = NULL;
    commondefs = NULL; curcommon = &dataarea;
    dataarea.index = -1;
    codeareap = codeareaq = &_areahdr_; _areahdr_.aaxb.anext = NULL;
    memset(&_areahdr_.aaxa, 0, sizeof(_areahdr_.aaxa));
#ifdef TARGET_IS_THUMB
    _areahdr_.aaxa.area_attributes |= AOF_CODEAT+AOF_THUMB;
#else
    _areahdr_.aaxa.area_attributes |= AOF_CODEAT;
#endif
    relocationpatches = NULL;
#ifdef PUT_FILE_NAME_IN_AREA_NAME
    {
    /* BJS: Find the leaf name */
        char name[256];
        putfilenameinareaname(name, "C$$c_", sourcefile);
        obj_symref(_areahdr_.aaxb.asv = sym_insert_id(name),
                   OBJ_DUMMYSYM, 0L);
        putfilenameinareaname(name, "C$$data_", sourcefile);
        obj_symref(data_sym = sym_insert_id(name), OBJ_DUMMYSYM, 0L);
        putfilenameinareaname(name, "C$$zidata_", sourcefile);
        obj_symref(bss_sym = sym_insert_id(name), OBJ_DUMMYSYM, 0L);
        putfilenameinareaname(name, "C$$extable_", sourcefile);
        obj_symref(extable_sym = sym_insert_id(name), OBJ_DUMMYSYM, 0L);
        putfilenameinareaname(name, "C$$exhandler_", sourcefile);
        obj_symref(exhandler_sym = sym_insert_id(name), OBJ_DUMMYSYM, 0L);
    }
#else
        obj_symref(_areahdr_.aaxb.asv = sym_insert_id("C$$code"),
                   OBJ_DUMMYSYM, 0L);
        obj_symref(data_sym = sym_insert_id("C$$data"), OBJ_DUMMYSYM, 0L);
        obj_symref(bss_sym = sym_insert_id("C$$zidata"), OBJ_DUMMYSYM, 0L);
        obj_symref(extable_sym = sym_insert_id("C$$extable"), OBJ_DUMMYSYM,0L);
        obj_symref(exhandler_sym = sym_insert_id("C$$exhandler"), OBJ_DUMMYSYM,0L);
#endif
    obj_symref(ddtor_sym = sym_insert_id("C$$ddtorvec"), OBJ_DUMMYSYM, 0L);
    obj_symref(adcon_sym= sym_insert_id("sb$$adcons"),OBJ_DUMMYSYM, 0L);
    adconpool_lab = sym_insert_id("x$adcons");
    byte_reversing = (target_lsbytefirst != host_lsbytefirst);
    thisCodeAreaIsEmpty = YES;
}

static void obj_cf_header(int32 areachunk_size)
{
    char space[sizeof(cf_header) + (OBJ_MAXCHUNKS-1)*sizeof(cf_entry)];
    /* Beware alignment problems here (non-portable C).                 */
    cf_header *cfh = (cf_header *)space;
    cf_entry *cfe = cfh->cf_chunks;
    int32 i, offset, size;
    char *chunknames = "OBJ_HEADOBJ_AREAOBJ_IDFNOBJ_SYMTOBJ_STRT";

    memset(space, 0, sizeof(space));
    cfh->cf_magic     = CF_MAGIC;
    cfh->cf_maxchunks = OBJ_MAXCHUNKS;
    cfh->cf_numchunks = OBJ_NUMCHUNKS;

    for (i = 0; i < OBJ_NUMCHUNKS; i++)
    {   memcpy(cfe[i].cfe_key, chunknames + i*8, 8);
        if (byte_reversing)
        {   int32 *p = (int32 *)(cfe[i].cfe_key);
            p[0] = totargetsex(p[0], LIT_BBBB);
            p[1] = totargetsex(p[1], LIT_BBBB);
        }
    }

    cfe[0].cfe_offset = aof_hdr_offset;
    cfe[0].cfe_size =offsetof(aof_header,aof_areas) + nareas*sizeof(aof_area);

    offset = sizeof(space);
    cfe[1].cfe_offset = offset;
    cfe[1].cfe_size   = areachunk_size;

    offset += areachunk_size;
    size = CC_BANNERlen;
    cfe[2].cfe_offset = offset;
    cfe[2].cfe_size   = size;

    offset += size;
    size = obj_symcount * sizeof(aof_symbol);
    cfe[3].cfe_offset = offset;
    cfe[3].cfe_size   = size;

    offset += size;
    cfe[4].cfe_offset = offset;
    cfe[4].cfe_size   = obj_stringpos;

    obj_fwrite_cnt = 0;
    obj_fwrite(space, 4, sizeof(space)/4, objstream);
}

void obj_header(void)
{
    obj_cf_header(0);
}

static int SetExtIndex(int32 size, Symstr *s, int i) {
    ExtRef *x = symext_(s);
    if (x == NULL)
        syserr(syserr_obj_checksym, s);
    else if (size != 0)
        x->extindex = i++;
    else
        x->extflags |= OBJ_DELETED;
    return i;
}

static void number_areas(void) {
    aof_xarea *a; int i = 1;
    for (a = codeareap;  a != NULL;  a = a->aaxb.anext)
        i = SetExtIndex(a->aaxa.area_size, a->aaxb.asv, i);

    i = SetExtIndex(data_size(), data_sym, i);
    i = SetExtIndex(bss_size, bss_sym, i);
    i = SetExtIndex(adconpool.size, adcon_sym, i);
    i = SetExtIndex(ddtor_vecsize(), ddtor_sym, i);
    i = SetExtIndex(extable_size(), extable_sym, i);
    i = SetExtIndex(exhandler_size(), exhandler_sym, i);
    {   DebugAreaDesc *p = debugareas;
        for (; p != NULL; p = cdr_(p))
            i = SetExtIndex(dbg_debugareaexists(symname_(p->sym)), p->sym, i);
    }
}

static void obj_aof_header(void)
{
    aof_header h;
    aof_area d;
    aof_xarea *a;

    obj_outcommonheaders(NO);        /* to count ncommonareas reliably */

    nareas = ncodeareas + ncommonareas;
    if (data_size() != 0) ++nareas;
    if (bss_size != 0) ++nareas;
    if (adconpool.size != 0) ++nareas;
    if (ddtor_vecsize() != 0) ++nareas;
    {   DebugAreaDesc *p = debugareas;
        for (; p != NULL; p = cdr_(p))
            if (dbg_debugareaexists(symname_(p->sym))) ++nareas;
    }

    h.aof_type        = AOF_RELOC;          /* relocatable object file */
    h.aof_vsn         = AOF_VERSION;                        /* version */
    h.aof_nareas      = nareas;
    h.aof_nsyms       = obj_symcount;
    h.aof_entryarea   = 0;
    h.aof_entryoffset = 0;                     /* start address offset */
    obj_fwrite(&h, 4, offsetof(aof_header,aof_areas)/4, objstream);

/* now the code area decls */
    {   int32 attributes = 2 + AOF_CODEAT + AOF_RONLYAT;
        if (pcs_flags & PCS_CALLCHANGESPSR) attributes |= AOF_32bitAT;
        if (pcs_flags & PCS_REENTRANT) attributes |= AOF_REENTAT | AOF_PICAT;
        if (pcs_flags & PCS_FPE3) attributes |= AOF_FP3AT;
        if (pcs_flags & PCS_NOSTACKCHECK) attributes |= AOF_NOSWSTKCK;
        if (pcs_flags & PCS_INTERWORK) attributes |= AOF_INTERWORK;
        for (a = codeareap;  a != NULL;  a = a->aaxb.anext)
        {   aof_area *aa = &a->aaxa;
            aa->area_base = 0;
            aa->area_name = obj_checksym(a->aaxb.asv);
            if (aa->area_attributes & AOF_CODEAT)
                aa->area_attributes |= attributes;
            else
                aa->area_attributes |= 2 + AOF_RONLYAT;
            if (aa->area_size == 0) continue;
/* ALPHA: dodgy size -- find all aof_area's */
            obj_fwrite(aa, 4, sizeof(aof_area)/4, objstream);
        }
    }

/* ... and the data */
    if (data_size() != 0)
    {   memset(&d, 0, sizeof(d));
        d.area_name    = obj_checksym(data_sym);
        d.area_attributes = 2;      /* 4-align */
        d.area_size    = data_size();
        d.area_nrelocs = ndatarelocs;
        obj_fwrite(&d, 4, sizeof(aof_area)/4, objstream);
    }

/* ... and the data */
    if (bss_size != 0)
    {   memset(&d, 0, sizeof(d));
        d.area_name    = obj_checksym(bss_sym);
        d.area_attributes = 2 + AOF_0INITAT;
        d.area_size    = bss_size;
        /*d.area_nrelocs = 0;*/
        obj_fwrite(&d, 4, sizeof(aof_area)/4, objstream);
    }

/* ... and the adcon table (if apcs_flags & REENTRANT) */
    if (adconpool.size != 0)
    {   memset(&d, 0, sizeof(d));
        d.area_name    = obj_checksym(adcon_sym);
        d.area_attributes = 2 + AOF_RONLYAT+AOF_BASEDAT+(R_SB<<AOF_BASESHIFT);
        d.area_size    = adconpool.size;
        d.area_nrelocs = nadconrelocs;
        obj_fwrite(&d, 4, sizeof(aof_area)/4, objstream);
    }

/* ... and the ddtorvec */
    memset(&d, 0, sizeof(d));
    if ((d.area_size = ddtor_vecsize()) != 0)
    {   d.area_name = obj_checksym(ddtor_sym);
        d.area_attributes = 2 + AOF_0INITAT;
        obj_fwrite(&d, 4, sizeof(aof_area)/4, objstream);
    }

/* ... and the extable */
    memset(&d, 0, sizeof(d));
    if ((d.area_size = extable_size()) != 0)
    {   d.area_name = obj_checksym(extable_sym);
        d.area_attributes = 2 + AOF_RONLYAT;
        obj_fwrite(&d, 4, sizeof(aof_area)/4, objstream);
    }

/* ... and the exhandler */
    memset(&d, 0, sizeof(d));
    if ((d.area_size = exhandler_size()) != 0)
    {   d.area_name = obj_checksym(exhandler_sym);
        d.area_attributes = 2 + AOF_RONLYAT;
        obj_fwrite(&d, 4, sizeof(aof_area)/4, objstream);
    }

/* ... and the debug areas */
    {   DebugAreaDesc *p = debugareas;
        for (; p != NULL; p = cdr_(p))
            if (dbg_debugareaexists(symname_(p->sym))) {
                memset(&d, 0, sizeof(d));
                d.area_size = p->size;
                d.area_name = obj_checksym(p->sym);
                d.area_attributes = 2 + AOF_RONLYAT + AOF_DEBUGAT;
                d.area_nrelocs = p->nrelocs;
                obj_fwrite(&d, 4, sizeof(aof_area)/4, objstream);
            }
    }
    obj_outcommonheaders(YES);
}

void obj_trailer(void)
{
    int32 area_siz;
    char b[64];
    if (has_main) obj_symref(libentrypoint, xr_code, 0);
    strcpy(b, "Lib$$Request$$armlib$$");
    target_lib_variant(&b[22]);
    obj_symref(sym_insert_id(b), xr_code+xr_weak, 0);
    /* just a reference to __main is enough to cause the library module    */
    /* containing it to be loaded.                                         */
    localcg_endcode();
#ifdef CONST_DATA_IN_CODE
    obj_add_constdata_area();
    {   int32 n;
        constdatabase = codebase;
        if (constdata_size() != 0) {
            obj_symref(bindsym_(constdatasegment), xr_code+xr_defloc, constdatabase);
            obj_writedata(constdata_head());
            codebase += constdata_size();
        }
#endif
        obj_end_codearea();
        number_areas();
#ifdef CONST_DATA_IN_CODE
        n = obj_datarelocation(constdata_xrefs(), constdatabase);
        codeareaq->aaxa.area_nrelocs += n;
        codeareasize += n * sizeof(aof_reloc);
    }
#endif
    if (relocationpatches != NULL)
    {   long fpos = ftell(objstream);
        RelocationPatch *p;
        for (p = relocationpatches; p != NULL; p = cdr_(p)) {
            fseek(objstream, p->fpos, SEEK_SET);
            p->flags |= obj_checksym(p->sym);
            obj_fwrite(&p->flags, 4, 1, objstream);
        }
        fseek(objstream, fpos, SEEK_SET);
    }
    area_siz = codeareasize;
    if (debugging(DEBUG_OBJ)) cc_msg("writedata\n");
    obj_writedata(data_head());
    if (debugging(DEBUG_OBJ)) cc_msg("datarelocation\n");
    ndatarelocs = obj_datarelocation(data_xrefs(), 0L);
    area_siz += data_size() + ndatarelocs*sizeof(aof_reloc);
    if (adconpool.size != 0) {
        if (debugging(DEBUG_OBJ)) cc_msg("writeadcons\n");
        adconpool_flush();
        if (debugging(DEBUG_OBJ)) cc_msg("adconrelocation\n");
        nadconrelocs = obj_datarelocation(adconpool.xrefs, 0L);
        area_siz += adconpool.size + nadconrelocs*sizeof(aof_reloc);
    }
    if (extable_size() != 0)
      {
        obj_add_extable_area();
        obj_symref(bindsym_(extablesegment), xr_constdata, extablebase);
        obj_writedata(extable_head());
        area_siz += extable_size();
      }
    /*extable and exhandler segments will both be present or both absent.*/
    if (exhandler_size() != 0)
      {
        obj_add_exhandler_area();
        obj_symref(bindsym_(exhandlersegment), xr_constdata, exhandlerbase);
        obj_writedata(exhandler_head());
        area_siz += exhandler_size();
      }
#ifdef TARGET_HAS_DEBUGGER
    if (debugging(DEBUG_OBJ)) cc_msg("writedebug\n");
    dbg_writedebug();
    {   DebugAreaDesc *p = debugareas;
        for (; p != NULL; p = cdr_(p))
            area_siz += p->size + p->nrelocs * sizeof(aof_reloc);
    }

#endif
    area_siz += obj_outcommonareas();
    if (debugging(DEBUG_OBJ)) cc_msg("symtab\n");
    obj_fwrite(CC_BANNER, 1, CC_BANNERlen, objstream);
    obj_outsymtab();
    aof_hdr_offset = ftell(objstream);
    obj_aof_header();
    if (debugging(DEBUG_OBJ)) cc_msg("rewind\n");
/* It is (unexpectedly) vital to use fseek here rather than rewind, since  */
/* rewind clears error flags. Note further that if there is a partially    */
/* full buffer just before the rewind & flushing that data causes an error */
/* (e.g. because there is no room on disc for it) this error seems to get  */
/* lost. This looks to me like a shambles in the October 1986 ANSI draft!  */
    fseek(objstream, 0L, SEEK_SET);   /* works for hex format too */
/* The next line represents a balance between neurotic overchecking and    */
/* the fact that it would be nice to detect I/O errors before the end of   */
/* compilation.                                                            */
    if (ferror(objstream)) cc_fatalerr(obj_fatalerr_io_object);
    if (debugging(DEBUG_OBJ)) cc_msg("rewriting header\n");
    obj_cf_header(area_siz);/* re-write header at top of file */
    /* file now closed in main() where opened */
}

/* end of armobj.c */

DataDesc adconpool;

Symstr *adconpool_lab;

int adconpool_find(int32 w, int32 flavour, Symstr *sym)
{   int i;
    DataInit *p;

    if (adconpool.size == 0)
        obj_symref(adconpool_lab, xr_defloc+xr_adcon, 0);
    else for (i = 0, p = adconpool.head; p != 0; p = p->datacdr) {
        if (p->sort == flavour && p->val == w && (Symstr *)p->len == sym)
              return i; /* allow for label as first item */
        if (p->sort != LIT_LABEL) i += 4;
    }

    {   int32 offset = adconpool.size;
        adconpool.xrefs = (DataXref *)global_list3(SU_Xref, adconpool.xrefs, offset, sym);
        p = (DataInit *)global_list5(SU_Other, NULL, 1, flavour, sym, w);

        adconpool.tail->datacdr = p;
        adconpool.tail = p;
        adconpool.size += 4;
        return (int)offset;
    }
}

void adconpool_flush(void)
{
    obj_writedata(adconpool.head);
}

void adconpool_init(void)
{   adconpool.head = adconpool.tail = (DataInit *)global_list3(SU_Other, NULL, adconpool_lab, LIT_LABEL);
    adconpool.size = 0;
    adconpool.xrefs = NULL;
    adconpool.xrarea = 0;
}

