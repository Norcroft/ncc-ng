/*
 * C compiler file arm/coff.c
 * Copyright (C) Codemist Ltd, 1988
 * Copyright (C) Advanced Risc Machines Limited, 1993
 * 'COFF' (system V unix) output routines
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$ Codemist 13j
 * Checkin $Date$
 * Revising $Author$
 */

/* AM: Feb 90: add AUX items for sections.  Fix bug in common refs      */
/* (find #if (R_DIR32 == 17) below for detailed explanation).           */
/* Memo: stuff CC_BANNER in the object file in the .comment section. */
/* Put the COFF style debug info in the file too.      */
/* This will cause review of the ordering of symbols   */

/* target.h shall specify: TARGET_HAS_COFF, target_coff_magic = <number>, */
/* and (optionally) target_coff_prefix.                                   */
/* maybe (one day) also the target_coff_<relocations> below too.          */

#ifndef __STDC__
#  include <strings.h>
#  define  SEEK_SET 0
#else
#  include <string.h>
#endif
#include <stddef.h>
#include <time.h>              /* see time() below */

#include "globals.h"    /* loads host.h,options.h,target.h,defaults.h   */
#include "mcdep.h"
#include "mcdpriv.h"
#include "aeops.h"
#include "store.h"
#include "codebuf.h"
#include "regalloc.h"
#include "util.h"
#include "bind.h"      /* evaluate */
#include "sem.h"       /* alignoftype, sizeoftype, structfield */
#include "builtin.h"
#include "xrefs.h"
#include "errors.h"
#include "simplify.h"

#include "coff.h"            /* Codemist private version */

#include "fname.h"

/* The following values are suitable for the 88000 ocs, but act as      */
/* suitable defaults.  Values are best specified in 'target.h'.         */
#ifndef R_DIR32
#  define R_DIR32  133         /* absolute relocation.                  */
#endif
#ifndef R_PCRLONG
#  define R_PCRLONG 129        /* pc relative relocation.               */
#endif
#ifndef R_REFHI
#  define R_REFHI  131         /* R_HVRT16 */
#endif
#ifndef R_REFLO
#  define R_REFLO  132         /* R_LVRT16 */
#endif

#ifndef target_coff_prefix
#  define target_coff_prefix "_"
#endif

/* We now follow 'as' and always generate a BSS section which is        */
/* usually empty.  There MAY be common ext. ref. problems otherwise.    */
#ifdef TARGET_IS_STARDENT
#define NSCNS  2
#else
#define NSCNS  3
#endif
#define N_TEXT 1
#define N_DATA 2
#define N_BSS  3

#define HDRSIZE (sizeof(struct filehdr) + NSCNS*sizeof(struct scnhdr))
#define xr_section xr_objflg
#define xr_deleted xr_objflg1

/* The following #defines give the logical section origins.             */
#define ORG_TEXT 0
#define ORG_DATA 0
#define ORG_BSS  0

#define SYM_FULLY_RELOCATED ((Symstr *)0)       /* internal PCreloc ref */

static bool byte_reversing = 0;
    /* byte_reversing == (host_lsbytefirst != target_lsbytefirst).        */
    /* (But faster to test one static per word than 2 externs per word).  */

/* Private interfaces to debug table generator */
static int32 dbg_fixup(ExtRef *syms, int32 symcount);
static void dbg_outsymtab(void);
static int32 dbg_lineinfo(void);

static int32 obj_fwrite_cnt;

#define ROR(x, n) (((x) << (32-(n))) | ((x) >> (n)))

static unsigned32 TargetWord(unsigned32 w) {
  if (byte_reversing) {
    unsigned32 t = w ^ ROR(w, 16);
    t &= ~0xff0000;
    w = ROR(w, 8);
    return w ^ (t >> 8);
  } else
    return w;
}

static unsigned TargetHalf(unsigned32 w) {
  if (byte_reversing) {
    return (unsigned)(((w >> 8) & 0xff) | ((w & 0xff) << 8));
  } else
    return (unsigned)w;
}

static void obj_fwrite(void *buff, int32 n, int32 m, FILE *f) {
  if (debugging(DEBUG_OBJ)) {
    int32 i;
    fprintf(f, "%.6lx:", (long)obj_fwrite_cnt);
    obj_fwrite_cnt += n*m;
    for (i=0; i<n*m; i++)
      fprintf(f, " %.2x", (int)((unsigned8 *)buff)[i]);
    fprintf(f, "\n");
  } else if (n == 4 && byte_reversing) {
    /* word by word output */
    unsigned32 v, t, *p, w;
    for (p = (unsigned32 *)buff;  m > 0;  --m, ++p) {
      v = *p;
      t = v ^ ROR(v, 16);
      t &= ~0xff0000;
      v = ROR(v, 8);
      w = v ^ (t >> 8);
      fwrite(&w, 4, 1, f);
    }
  } else
    fwrite(buff, (size_t)n, (size_t)m, f);
}

FILE *objstream;

/* imports: codebase, dataloc */
static unsigned32 ncoderelocs, ndatarelocs, obj_symcount;
static unsigned32 constdatabase;
ExtRef *obj_symlist;
CodeXref *codexrefs;
static int32 obj_lnno;

/* In general, COFF requires references to symbols which are defined    */
/* in codeseg, dataseg or bssseg to be replaced by a reference to       */
/* segment+offset.  Hence the code for a C routine with an 'extern'     */
/* reference is not complete until we know whether it was truly extern  */
/* or merely 'forward'.  So buffer the code (in codevec) from each fn   */
/* into 'xcodevec' and then call relocate_code_refs_to_locals() before  */
/* writing xcodevec into the COFF .o file.                              */

#define MAXCODESEGS 256
static int32 (*(xcodevec[MAXCODESEGS]))[CODEVECSEGSIZE], codesize;

#ifdef TARGET_HAS_BYTE_INSTRUCTIONS
#define xcode_byte_(q) ((unsigned8 *)(*xcodevec[CODE_SEG_INDEX(q)]))[CODE_BYTE_INDEX((q)]
#else
#define xcode_inst_(q) (*xcodevec[CODE_SEG_INDEX(q)])[CODE_ELEM_INDEX(q)]
#endif

#define get_code(q)   xcode_inst_(q)
#define set_code(q,n) xcode_inst_(q)=n

/* The following code is in flux and allows for the generic compiler    */
/* interfaces to use byte addresses which are corrected here.  It now   */
/* occurs to AM that we could have used word addresses more, but this   */
/* could also be a can of worms.  Let's try this way FIRST.             */
#ifdef TARGET_IS_ADENART
#  define machine_address_(v,f) ((v)/((f) & xr_code ? 3:8))
#else
#  define machine_address_(v,f) (v)
#endif

static void buffer_code(int32 *src, int32 nwords) {
  int32 *p;
  for (p = src; nwords > 0; --nwords) {
    int32 hi = codesize >> (CODEVECSEGBITS+2);
    int32 lo = (codesize >> 2) & (CODEVECSEGSIZE-1);
    if (lo == 0) { /* need another segment */
      if (hi >= MAXCODESEGS) cc_fatalerr(coff_fatalerr_toobig);
      xcodevec[hi] = (int32(*)[CODEVECSEGSIZE]) GlobAlloc(
                                        SU_Other, sizeof(*xcodevec[0]));
    }
    (*xcodevec[hi])[lo] = *p++; codesize += 4;
  }
}


static int32 obj_checksym(Symstr *s);

/* @@@ The code here is getting silly.  X_JmpAddr is not really        */
/* a PCreloc.                                                          */
static void relocate_code_refs_to_locals(void) {
    /* This proc. should soon callback to a routine in gen.c:          */
  CodeXref *cxr;
  for (cxr = codexrefs;  cxr != NULL;  cxr = cxr->codexrcdr)
  { Symstr *s = cxr->codexrsym;
    ExtRef *x = ((void)obj_checksym(s), symext_(s));
    int32 codeoff = cxr->codexroff & 0xffffff;
    int32 w = get_code(codeoff);
    switch (cxr->codexroff & 0xff000000) {
    case X_PCreloc: /* on the MIPS also means X_JmpAddr -- rationalise  */
        /* pcrelative code ref (presumed to) to code.               */
        /* @@@ cast of array to code pointer causes the following   */
        /* syserr().  Needs fixing properly.                        */
      if (!(x->extflags & xr_code))
        syserr(syserr_coff_reloc);
      if (x->extflags & (xr_defloc | xr_defext)) {
                 /* defined in this compilation unit so relocate... */
        cxr->codexrsym = SYM_FULLY_RELOCATED;
/* @@@ AM: before 'rationalising' this code, it is IMPORTANT to build   */
/* in the 29000 or 88000 32 bits in 64 bits relocation modes.           */
/* AM: note that in all the following cases any offset in the code is   */
/* ignored and simply overwritten.  Change this one day?                */
#ifdef TARGET_IS_ARM
/* On the ARM relocate a B or BL; offset in WORDs; prefetch 8 bytes.    */
#define obj_codeupdate(n) \
            set_code(codeoff, (w & 0xff000000) | (((n)-8) >> 2) & 0x00ffffff)
#endif
        obj_codeupdate(x->extoffset-codeoff);
      } else {
        /* Branch to external symbol.  Most Unices expect to be     */
        /* tight branch to self.  (On the ARM, the Unix linker      */
        /* expects unrelocated branch to be -2 words,               */
        obj_codeupdate(0);
      }
      if (debugging(DEBUG_OBJ))
        cc_msg("Fixup %.8lx extoff=%.8lx, codeoff=%.8lx, make %.8lx\n",
               (long)w, (long)x->extoffset, (long)codeoff,
               (long)get_code(codeoff));
      break;
    case X_absreloc:
    case X_backaddrlit: /* abs ref to external */
/* Code here may need changing if you set ORG_TEXT &c to non-zero.      */
      if (x->extflags & (xr_defloc | xr_defext)) {
          /* code ref to local code or data via address literal...
           * (or clipper/vax absolute 32 bit branch).
           * Unix linker cannot cope with filling in the address literal
           * with the value of a locally defined symbol: we have to convert
           * it into a reference relative to v$codeseg or v$dataseg.
           * This process is completed by obj_checksym().
           * AM: note that we do take notice of the old value here.
           */
        if (x->extflags & xr_constdata) w += constdatabase;
        set_code(codeoff, w + x->extoffset);
      }
      break;
    }
  }
}

static void obj_writecode(void) {
  int i = 0;
#if (alignof_double > 4)      /* TARGET_ALIGNS_DOUBLES */
  if (codesize & 7) {
    static int32 pad[] = {0,0,0};
    buffer_code(pad, 1); /* Double word aligned */
  }
#endif
  relocate_code_refs_to_locals();

  while ((codesize>>2) - CODEVECSEGSIZE*i > CODEVECSEGSIZE)
    obj_fwrite(xcodevec[i++], 4, CODEVECSEGSIZE, objstream);
  obj_fwrite(xcodevec[i], 4,(codesize>>2)-CODEVECSEGSIZE*i, objstream);
  if (ferror(objstream)) cc_fatalerr(driver_fatalerr_io_object);
}


void obj_codewrite(Symstr *name) {
    /* Called after each routine is compiled -- code_instvec_ (doubly    */
    /* indexed) has codep (multiple of 4) bytes of code.                 */
    /* In BSD a.out, this has to be buffered to the end of compilation   */
    /* so that the BSD linker can be cow-towed to.                       */
    /* #define COMPILING_ON_SMALL_MEMORY can be used to buffer on disc.  */
  int32 i, nwords;
  IGNORE(name);
  if (byte_reversing) {
    int32 n = codep, w;
    for (i = 0; i < n; i += 4) {
      w = totargetsex(code_inst_(i), code_flag_(i));
      buffer_code(&w, 1);
    }
  } else
    for (i = 0, nwords = codep>>2; nwords > 0; ++i) {
      int32 seg = nwords > CODEVECSEGSIZE ? CODEVECSEGSIZE : nwords;
      buffer_code(code_instvec_(i), seg); nwords -= seg;
    }
}

/* the remaining fns are intended to be internal only */

/* In COFF, the data segment label is required to be .data etc.         */
#define coffname_(s) ((s) == bindsym_(codesegment) ? ".text" : \
                      (s) == bindsym_(datasegment) ? ".data" : \
                      (s) == bindsym_(bsssegment) ? ".bss" : \
                      symname_(s))

/* TEMPHACK: */
typedef union AuxEnt {
  struct syment pad;
  struct { long int x_scnlen;
           unsigned short x_nreloc;
           unsigned short x_nlinno;
         } x_scn;
} AuxEnt;

typedef struct StringTabEntry StringTabEntry;
struct StringTabEntry {
  StringTabEntry *cdr;
  char name[1];
};

static StringTabEntry *stringtab;
static unsigned32 stringtabpos;

static void obj_stab(char *name, int32 val, int sect, int type, int sclass, void *auxp) {
  size_t n = strlen(name),
         k = sclass != C_EXT || name[0]=='.' ? 0 : sizeof(target_coff_prefix)-1;
  struct syment v;
  memclr(&v, SYMESZ);
  if (debugging(DEBUG_OBJ)) cc_msg("sym %s ", name);
  if (n+k > SYMNMLEN) {           /* NB: '>' (not '>=') is OK here */
      /* do the long form, name in the string table */
    StringTabEntry *p = (StringTabEntry *)SynAlloc((int32)sizeof(StringTabEntry)+n+k);
    if (k > 0) memcpy(p->name, target_coff_prefix, k);
    memcpy(&p->name[k], name, n+1);
    v.n_zeroes = 0;
    v.n_offset = TargetWord(stringtabpos);
    stringtabpos += (size_t)(n+k+1);
    cdr_(p) = stringtab;
    stringtab = p;
  } else {
    if (k > 0) strncpy(v.n_name, target_coff_prefix, k);
    strncpy(v.n_name+k, name, SYMNMLEN-k);
  }
  v.n_value = TargetWord(val);
  v.n_scnum = TargetHalf(sect);
  v.n_type = TargetHalf(type);         /* not set yet */
  v.n_sclass = sclass;
  v.n_numaux = auxp == NULL ? 0 : 1;
  obj_fwrite(&v, 1, SYMESZ, objstream);
  if (auxp != NULL) obj_fwrite(auxp, 1, SYMESZ, objstream);
}

/* TEMPHACK: */
static void SetSegAux(AuxEnt *p, int32 seglen, int32 nrelocs, int32 nlno) {
  memclr(p, sizeof(*p));
  p->x_scn.x_scnlen = TargetWord(seglen);
  p->x_scn.x_nreloc = TargetHalf(nrelocs);
  p->x_scn.x_nlinno = TargetHalf(nlno);
}

static void obj_outsymtab(int32 mask, int32 maskedval) {
  ExtRef *x;
  for (x = obj_symlist; x != 0; x = x->extcdr) {
    Symstr *s = x->extsym;
    int32 flags = x->extflags;
    if ((flags & mask) == maskedval) {
      char *name = coffname_(s);
/* The next line stores the value (= offset in segment) for code or     */
/* data definitions, and stores zero for external refs, except for      */
/* pcc-style common refs, in which it stores the length.                */
      int32 val = x->extoffset;
      /* note that C_EXTDEF is documented as "internal to C, use C_EXT". */
      int sclass = flags & xr_defloc ? C_STAT : C_EXT;
      AuxEnt *auxp = NULL;
      AuxEnt aux;
      int sect;
      if (!(flags & xr_defloc+xr_defext))
        sect = N_UNDEF;
      else if (flags & xr_code)
        sect = N_TEXT, val += ORG_DATA;
      else if (flags & xr_constdata)
        sect = N_TEXT, val += ORG_DATA+constdatabase;
      else if (flags & xr_bss)
        sect = N_BSS, val += ORG_BSS;
      else
        sect = N_DATA, val += ORG_DATA;
/* TEMPHACK: */ if (s == bindsym_(codesegment)) SetSegAux(auxp = &aux, codesize, ncoderelocs, obj_lnno);
/* TEMPHACK: */ if (s == bindsym_(datasegment)) SetSegAux(auxp = &aux, data.size, ndatarelocs, 0);
/* TEMPHACK: */ if (s == bindsym_(bsssegment)) SetSegAux(auxp = &aux, bss_size, 0, 0);
      obj_stab(name, val, sect, T_NULL, sclass, auxp);
    }
  }
}

static void obj_outstringtab(void) {  /* write the string table, preceded by its length */
  obj_fwrite(&stringtabpos, sizeof(stringtabpos), 1, objstream);
  { StringTabEntry *p;
    stringtab = (StringTabEntry *)dreverse((List *)stringtab);
    for (p = stringtab; p != 0; p = cdr_(p))
      obj_fwrite(p->name, 1, (int32)strlen(p->name)+1, objstream);
  }
}

static int32 obj_checksym(Symstr *s) {
  ExtRef *x = symext_(s);
  if (x != 0) {
    if (!(x->extflags & xr_defloc+xr_defext) ||
        s==bindsym_(codesegment) || s==bindsym_(datasegment) || s==bindsym_(bsssegment))
        /* honest external or segment defining symbol */
      return x->extindex;
    else
      return obj_checksym(x->extflags & (xr_code+xr_constdata) ? bindsym_(codesegment) :
                          x->extflags & xr_bss ?  bindsym_(bsssegment) :
                                                  bindsym_(datasegment));
  }
  syserr(syserr_coff_checksym, s);
  return 0;
}

static void obj_wr_reloc(struct reloc *p, int r) {
  p->r_type = TargetHalf(r);
    /* NB note that sizeof(struct reloc) > RELSZ on many machines */
  obj_fwrite(p, 1, RELSZ, objstream);
  ncoderelocs++;
}

static void obj_coderelocation() {
  CodeXref *x;
  struct reloc v;
  for (x = codexrefs; x!=NULL; x = x->codexrcdr) {
    Symstr *s = x->codexrsym;
    if (s == SYM_FULLY_RELOCATED) continue;
    v.r_vaddr = TargetWord((x->codexroff & 0xffffff) + ORG_TEXT);
    v.r_symndx = TargetWord(obj_checksym(s));
    switch (x->codexroff & 0xff000000) {
    case X_PCreloc:  /* PC rel ref to external */
      if (debugging(DEBUG_OBJ)) cc_msg("pcreloc$r ", s);
      obj_wr_reloc(&v, R_PCRLONG);    /* target_coff_pcrel? */
      break;
    case X_absreloc:    /* abs ref to external */
    case X_backaddrlit: /* ditto, but literal  */
      if (debugging(DEBUG_OBJ)) cc_msg("addreloc$r ", s);
      obj_wr_reloc(&v, R_DIR32);      /* target_coff_abs? */
      break;
    default:
      syserr(syserr_coff_reloc1, (long)x->codexroff);
      break;
    }
  }
}

static int32 obj_datarelocation(DataXref *x, int32 offset) {
  struct reloc v;
  int32 n = 0;
  for (; x != NULL; x = x->dataxrcdr, n++) {
    Symstr *s = x->dataxrsym;
    /* all data relocs are implicitly X_absreloc so far */
    if (debugging(DEBUG_OBJ)) cc_msg("data reloc $r ", s);
    v.r_type = TargetHalf(R_DIR32);                       /* target_coff_abs? */
    v.r_vaddr = TargetWord(x->dataxroff+offset+ORG_DATA); /* & 0xffffff ? */
    v.r_symndx = TargetWord(obj_checksym(s));
    /* NB note that sizeof(struct reloc) > RELSZ on many machines */
    obj_fwrite(&v, 1, RELSZ, objstream);
  }
  return n;
}

static void obj_writedata(DataInit *p) { /* follows gendc exactly! */
  for (; p != 0; p = p->datacdr)
  { int32 rpt = p->rpt, sort = p->sort, len = p->len;
    unsigned32 val = p->val;
    switch (sort) {
    case LIT_LABEL:   /* name only present for c.xxxasm */
      break;
    default:  syserr(syserr_coff_gendata, (long)sort);
      case LIT_BXXX:    /* The following are the same as LIT_NUMBER       */
      case LIT_BBX:     /* except for cross-sex compilation               */
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
            t = val ^ ROR(val, 16);
            t &= ~0xff0000;
            val = ROR(val, 8);
            val = val ^ (t >> 8);
        }
        while (rpt-- != 0) obj_fwrite(&val, 1, len, objstream);
        break;
    case LIT_NUMBER:
      if (len != 4) syserr(syserr_coff_datalen, (long)len);
      /* beware: sex dependent... */
      while (rpt-- != 0) obj_fwrite(&val, 4, 1, objstream);
      break;
    case LIT_ADCON:              /* (possibly external) name + offset */
      { Symstr *sv = (Symstr *)len;  /* this reloc also in dataxrefs */
        ExtRef *xr= symext_(sv);
        (void)obj_checksym(sv);
        if (xr->extflags & (xr_defloc|xr_defext)) {
          val += xr->extoffset;
          if (xr->extflags & xr_constdata) val += constdatabase;
        }
        /* beware: sex dependent... */
        while (rpt-- != 0) obj_fwrite(&val, 4, 1, objstream);
        break;
      }
    case LIT_FPNUM:
      { FloatCon *fc = (FloatCon *)val;
            /* do we need 'len' when the length is in fc->floatlen?? */
        if (len != 4 && len != 8)
          syserr(syserr_coff_data, (long)rpt, (long)len, fc->floatstr);
        /* The following strange code ensures that doubles are correctly */
        /* sex-reversed if required to be - obj_fwrite() only reverses  */
        /* items of length 4... This is a trap for the unwary.          */
        while (rpt-- != 0) {
          obj_fwrite(&(fc->floatbin.irep[0]), 4, 1, objstream);
          if (len == 4) continue;
          obj_fwrite(&(fc->floatbin.irep[1]), 4, 1, objstream);
        }
        break;
      }
    }
  }
}

/* exported functions... */

int32 obj_symref(Symstr *s, int flags, int32 loc) {
  ExtRef *x;
  if ((x = symext_(s)) == 0) {   /* saves a quadratic loop */
    if (obj_symcount > 0x7fffffff)
      cc_fatalerr(coff_fatalerr_toomany);
    x = (ExtRef *)GlobAlloc(SU_Xref, sizeof(ExtRef));
    x->extcdr = obj_symlist,
      x->extsym = s,
      x->extindex = obj_symcount++,
      x->extflags = 0,
      x->extoffset = 0;
    obj_symlist = symext_(s) = x;
/* TEMPHACK: */
    if (s == bindsym_(codesegment) || s == bindsym_(datasegment) || s == bindsym_(bsssegment)) {
      x->extflags |= xr_section;
      obj_symcount++;
    }
  }
/* The next two lines cope with further ramifications of the abolition of */
/* xr_refcode/refdata in favour of xr_code/data without xr_defloc/defext  */
/* qualification.  This reduces the number of bits, but needs more        */
/* checking in that a symbol defined as data, and then called via         */
/* casting to a code pointer may acquire defloc+data and then get         */
/* xr_code or'ed in.  Suffice it to say this causes confusion.            */
/* AM wonders if gen.c ought to be more careful instead.                  */
  if (flags & (xr_defloc+xr_defext)) x->extflags &= ~(xr_code+xr_data);
  if (x->extflags & (xr_defloc+xr_defext)) flags &= ~(xr_code+xr_data);
/* end of fix, but perhaps we should be more careful about mult. defs.?   */
  x->extflags |= flags;
  if (flags & xr_defloc+xr_defext) {
    /* private or public data or code */
    x->extoffset = machine_address_(loc,flags);

  } else if ((loc > 0) && !(flags & xr_code) &&
             !(x->extflags & xr_defloc+xr_defext)) {
    /* common data, not already defined */
    /* -- put length in x->extoffset    */
    if (loc > x->extoffset) x->extoffset = machine_address_(loc,flags);
  }
  /* The next line returns the offset of a function in the codesegment */
  /* if it has been previously defined -- this saves store on the arm  */
  /* and allows short branches on other machines.  Otherwise it        */
  /* returns -1 for undefined objects or data objects.                 */
  return ((x->extflags & (xr_defloc+xr_defext)) && (x->extflags & xr_code) ?
          x->extoffset : -1);
}

/* For fortran... */
void obj_common_start(Symstr *name) {
    /* There is no real support in COFF for common definitions (BLOCK   */
    /* DATA).  What needs to be done is to turn the block name into     */
    /* an exported symbol in the normal data area (.data).              */
  labeldata(name);
  obj_symref(name, xr_data+xr_defext, data.size);
}

void obj_common_end(void) {}

void obj_init() {
  ncoderelocs = 0, ndatarelocs = 0, obj_symcount = 0;
  obj_symlist = 0;
  data.xrefs = 0;
  codexrefs = 0;
  codesize = 0;     /* remove */
  stringtabpos = sizeof(stringtabpos);
  stringtab = NULL;
  obj_lnno = 0;
  byte_reversing = (target_lsbytefirst != host_lsbytefirst);
  /* codesegment and datasegment are arranged elsewhere */
  obj_symref(bindsym_(bsssegment), xr_bss+xr_defloc, 0L);
}

void obj_header() {
  struct filehdr h;
  struct scnhdr s;
  if ((ncoderelocs | ndatarelocs) & ~(unsigned32)(unsigned short)-1)
    cc_fatalerr(coff_fatalerr_toomany);
  obj_fwrite_cnt = 0;
  h.f_magic = TargetHalf(target_coff_magic);
  h.f_nscns = TargetHalf(NSCNS);
  h.f_timdat = TargetWord(time(NULL));    /* hope unix format -- norcroft use too. */
  h.f_symptr = TargetWord(HDRSIZE + codesize + data.size +
               /* @@@ round to multiple of 4? (RELSZ = 10) */
               ncoderelocs*RELSZ + ndatarelocs*RELSZ + obj_lnno*6);
  h.f_nsyms = TargetWord(obj_symcount);
  h.f_opthdr = 0;             /* no optional header */
  h.f_flags = 0;              /* default F_xxxx flags */
  obj_fwrite(&h, 1, sizeof(h), objstream);
  /* code section header */
  strncpy(s.s_name, ".text", sizeof(s.s_name));
  s.s_paddr = s.s_vaddr = TargetWord(ORG_TEXT);
  s.s_size = TargetWord(codesize);
  s.s_scnptr = TargetWord(HDRSIZE);
  s.s_relptr = TargetWord(HDRSIZE + codesize + data.size);
  s.s_lnnoptr = TargetWord(obj_lnno == 0 ? 0 : HDRSIZE + codesize + data.size +
                                               ncoderelocs*RELSZ + ndatarelocs*RELSZ);
  s.s_nreloc = TargetHalf(ncoderelocs);
  s.s_nlnno = TargetHalf(obj_lnno);
  s.s_flags = TargetWord(STYP_TEXT);
  obj_fwrite(&s, 1, sizeof(s), objstream);
  /* data section header */
  strncpy(s.s_name, ".data", sizeof(s.s_name));
  s.s_paddr = s.s_vaddr = TargetWord(ORG_DATA);
  s.s_size = TargetWord(data.size);
  s.s_scnptr = TargetWord(HDRSIZE + codesize);
  s.s_relptr = TargetWord(HDRSIZE + codesize + data.size + ncoderelocs*RELSZ);
  s.s_lnnoptr = 0;            /* no line number info */
  s.s_nreloc = TargetHalf(ndatarelocs);
  s.s_nlnno = 0;              /* no line number info */
  s.s_flags = TargetWord(STYP_DATA);
  obj_fwrite(&s, 1, sizeof(s), objstream);
  /* bss section header */
  strncpy(s.s_name, ".bss", sizeof(s.s_name));
  s.s_paddr = s.s_vaddr = TargetWord(ORG_BSS);
  s.s_size = TargetWord(bss_size);
  s.s_scnptr = 0;
  s.s_relptr = 0;
  s.s_lnnoptr = 0;            /* no line number info */
  s.s_nreloc = 0;             /* no relocations      */
  s.s_nlnno = 0;              /* no line number info */
  s.s_flags = TargetWord(STYP_BSS);
  obj_fwrite(&s, 1, sizeof(s), objstream);
}

void obj_trailer() {
  codexrefs = (CodeXref *)dreverse((List *)codexrefs);
  data.xrefs = (DataXref *)dreverse((List *)data.xrefs);
  constdata.xrefs = (DataXref *)dreverse((List *)constdata.xrefs);
  obj_symlist = (ExtRef *)dreverse((List *)obj_symlist);
                /* oldest = smallest numbered first */
  obj_symcount = dbg_fixup(obj_symlist, obj_symcount);
  if (debugging(DEBUG_OBJ)) cc_msg("writecode\n");
  constdatabase = codesize;
  obj_writecode();
  obj_writedata(constdata.head);
  codesize += constdata.size;
  if (debugging(DEBUG_OBJ)) cc_msg("writedata\n");
  obj_writedata(data.head);
  if (debugging(DEBUG_OBJ)) cc_msg("coderelocation\n");
  obj_coderelocation();
  ncoderelocs += obj_datarelocation(constdata.xrefs, constdatabase);
  if (debugging(DEBUG_OBJ)) cc_msg("datarelocation\n");
  ndatarelocs = obj_datarelocation(data.xrefs, 0L);
  obj_lnno = dbg_lineinfo();
  if (debugging(DEBUG_OBJ)) cc_msg("symtab\n");
  dbg_outsymtab();
  if (debugging(DEBUG_OBJ)) cc_msg("rewind\n");
  rewind(objstream);   /* works for hex format too */
  if (debugging(DEBUG_OBJ)) cc_msg("rewriting header\n");
  obj_header();        /* re-write header at top of file */
  /* file now opened and closed in main(). */
}

#ifdef TARGET_HAS_DEBUGGER

/* Storage classes */
#define C_NULL          0
#define C_AUTO          1
/*#define C_EXT         2*/     /* extern (ref) (in coff.h) */
/*#define C_STAT        3*/     /* static (in coff.h) */
#define C_REG           4
#define C_EXTDEF        5
#define C_LABEL         6
#define C_ULABEL        7       /* undefined label (?) */
#define C_MOS           8       /* member of structure */
#define C_ARG           9
#define C_STRTAG        10      /* structure tag */
#define C_MOU           11      /* member of union */
#define C_UNTAG         12      /* union tag */
#define C_TPDEF         13      /* typedef */
#define C_USTATIC       14      /* unitialised static - what is this? */
#define C_ENTAG         15      /* enumeration tag */
#define C_MOE           16      /* member of enumeration */
#define C_REGPARM       17      /* register param */
#define C_FIELD         18      /* bitfield (presumably also implicitly MOS) */
#define C_BLOCK         100
#define C_FCN           101
#define C_EOS           102     /* end of structure (enumeration, union?) */
#define C_FILE          103
#define C_HIDDEN        106     /* static with possibly clashing name */

/* Section numbers */
#define N_DEBUG         (-2)
#define N_ABS           (-1)
/*#define N_UNDEF         0*/   /* in coff.h */
/*#define N_TEXT          1*/   /* see above */
/*#define N_DATA          2*/   /* see above */
/*#define N_BSS           3*/   /* see above */

/* fundamental types */
/*#define T_NULL          0*/   /* in coff.h */
#define T_LDOUBLE       1
#define T_CHAR          2       /* (signed) */
#define T_SHORT         3
#define T_INT           4
#define T_LONG          5
#define T_FLOAT         6
#define T_DOUBLE        7
#define T_STRUCT        8
#define T_UNION         9
#define T_ENUM          10
#define T_MOE           11
#define T_UCHAR         12
#define T_USHORT        13
#define T_UINT          14
#define T_ULONG         15

/* derived types */
#define DT_NON          0
#define DT_PTR          1
#define DT_FCN          2
#define DT_ARRAY        3

int usrdbgmask;

static int32 anonindex;

#define DbgAlloc(n) GlobAlloc(SU_Dbg, n)

typedef struct DbgList DbgList;

typedef struct {
  int w;
  unsigned8 modct, dimct;
  DbgList *tag;
  int32 *dims;
} Dbg_Type;

typedef struct StructElt StructElt;
typedef struct EnumElt EnumElt;

struct StructElt {
  StructElt *cdr;     /* must be first for dreverse */
  int32 val;
  char *name;
  Dbg_Type type;
};

struct EnumElt {
  EnumElt *cdr;     /* must be first for dreverse */
  int32 val;
  char *name;
};

typedef struct FileCoord FileCoord;
struct FileCoord {
  FileCoord *cdr;
  int line;
  int32 codeaddr;
};

#define DbgListVarSize(variant) \
    ((size_t)(sizeof(p->car.variant)+offsetof(DbgList,car)))

/* The following is the *internal* data structure in which debug info. */
/* is buffered.                                                        */
#define S_Undef 16
typedef enum {
  Ignore,
  File,
  Proc,
  EndProc,
  BlockStart,
  BlockEnd,
  Var,
  Type,
  Enum,
  Union,
  Struct,
  UndefEnum = Enum+S_Undef,
  UndefUnion = Union+S_Undef,
  UndefStruct = Struct+S_Undef,
  UndefVar = Var+S_Undef
} DbgListSort;

struct DbgList {
  DbgList *cdr;
  DbgListSort sort;
  int32 index;
  union {
    struct {
      char *name;
      DbgList *next;
    } File;
    struct {
      Dbg_Type type;
      int stgclass;
      Symstr *name;
      unsigned8 oldstyle;
      int sourcepos;
      int32 filepos;
      int32 entryaddr, bodyaddr;   /* see dbg_bodyproc */
      DbgList *end;                /* corresponding EndProc item */
      FileCoord *linelist;
    } Proc;
    struct {
      int sourcepos;
      int32 endaddr;
      char *fileentry;
    } EndProc;
    struct {
      Dbg_Type type;
      int stgclass;
      Symstr *name;
      int32 location;
      int section;
      int sourcepos;
    } Var;
    struct {
      int32 entries;
      int32 size;
      bool named;
      union {
        int32 anonindex;
        char *name;
      } tag;
      union {
        StructElt *s;
        EnumElt *e;
      } elts;
    } Tag;
    struct {
      union {
        DbgList *next;
        int32 codeaddr;
      } s;
      DbgList *p;  /* block starts only: previous block start if */
                   /* not yet closed, else block end             */
    } Block;
  } car;
};

static DbgList *locdbglist, *globdbglist, *statdbglist, *dbglistproc;
static DbgList *dbglistblockstart;
static DbgList *dbglistfile;

static void CheckFile(char *f) {
  if (dbglistfile == NULL || dbglistfile->car.File.name != f) {
    if (locdbglist == NULL || locdbglist != dbglistfile || statdbglist != NULL) {
    /* A file containing something of interest (otherwise lose it) */
      DbgList *p = (DbgList *)DbgAlloc(DbgListVarSize(File));
      locdbglist = (DbgList *)nconc((List *)statdbglist, (List *)locdbglist);
      statdbglist = NULL;
      cdr_(p) = locdbglist;
      p->sort = File;
      p->index = 0;
      p->car.File.next = NULL;
      if (dbglistfile != NULL) dbglistfile->car.File.next = p;
      locdbglist = p;
      dbglistfile = p;
    }
    dbglistfile->car.File.name = f;
  }
}

VoidStar dbg_notefileline(FileLine fl) {
  if (usrdbg(DBG_LINE) && dbglistproc != NULL) {
    FileCoord *p, *l = dbglistproc->car.Proc.linelist;
      /* @@@ beware - odd use of #line *MAY* (check) set off the syserr() */
    if (l != NULL && l->line > fl.l) syserr(syserr_debugger_line);
    p = (FileCoord *)DbgAlloc(sizeof(FileCoord));
    cdr_(p) = l; p->line = fl.l; p->codeaddr = -1;
    dbglistproc->car.Proc.linelist = p;
    return (VoidStar)p;
  }
  return DUFF_ADDR;
}

static DbgList *dbglistscope;

/* The 'dbgaddr' arg has type 'void *' to keep the debugger types local to */
/* this file.  This does not make it any less of a (ANSI approved) hack.   */
void dbg_addcodep(VoidStar dbgaddr, int32 codeaddr) {
  if (dbgaddr == NULL) { /* J_INFOSCOPE */
    /* c.flowgraf outputs a J_INFOSCOPE immediately after calling
     * dbg_scope, to mark the relevant code address.
     */
    if (debugging(DEBUG_Q)) cc_msg("-- scope at 0x%lx\n", codeaddr);
    { DbgList *next, *p = dbglistscope;
      for (; p != NULL; p = next) {
        next = p->car.Block.s.next;
        p->car.Block.s.codeaddr = codeaddr;
      }
      dbglistscope = NULL;
    }
  } else if (usrdbg(DBG_LINE)) {
    FileCoord *p = (FileCoord *)dbgaddr;
    if (debugging(DEBUG_Q))
      cc_msg("%p (line %u) @ %.6lx\n", p, p->line, (long)codeaddr);
    /* The following test avoids setting nextincode/codeaddr twice */
    /* This is currently needed in case FileLine's are duplicated. */
    if (p->codeaddr == -1) p->codeaddr = codeaddr;
  }
}

static int32 dbg_lineinfo(void) {
  DbgList *p = locdbglist;
  struct { int32 addr; int16 line; } lineno;
  int32 count = 0;
  if (usrdbg(DBG_LINE))
    for (; p != NULL; p = cdr_(p)) {
      if (p->sort == Proc) {
        int startline = p->car.Proc.sourcepos;
        int lastline = startline;
        int32 addr = 0;
        FileCoord *coord = (FileCoord *)dreverse((List *)p->car.Proc.linelist);
        lineno.addr = TargetWord(p->index);
        lineno.line = 0;
        obj_fwrite(&lineno, 1, 6, objstream);
        count++;
        for (; coord != NULL; coord = cdr_(coord))
          if (coord->line > lastline && coord->codeaddr > addr) {
            addr = coord->codeaddr;
            lastline = coord->line;
            lineno.addr = TargetWord(addr);
            lineno.line = TargetHalf((int32)lastline - startline);
            obj_fwrite(&lineno, 1, 6, objstream);
            count++;
          }
      }
    }
    return count;
}

/* End of file/line co-ordinate code */

static int32 AuxEntryCount(Dbg_Type *t) {
  return t->dimct != 0 ? 1 :
         t->tag != NULL ? 1 :
         0;
}

static void TypeRep(TypeExpr *, Dbg_Type *, DbgList **);

static void StructEntry(DbgList *p, TagBinder *b, SET_BITMAP sort, int32 size, DbgList **list) {
  ClassMember *l = tagbindmems_(b);
  StructElt *elts = NULL;
  int32 count = 0;

  StructPos sp;
  structpos_init(&sp, b);
  for (; l != 0; l = memcdr_(l)) {
    structfield(l, sort, &sp);
    if (memsv_(l)) {   /* memsv is 0 for padding bit fields */
      StructElt *el = (StructElt *)DbgAlloc(sizeof(StructElt));
      cdr_(el) = elts;
      el->val = sp.woffset;
      TypeRep(sp.bsize != 0 ? te_int : memtype_(l), &el->type, list);
      el->name = symname_(memsv_(l));
      elts = el;
      count += 1 + AuxEntryCount(&el->type);
    }
  }
  p->car.Tag.size = size;
  p->car.Tag.elts.s = (StructElt *)dreverse((List *)elts);
  p->car.Tag.entries = count;
}

static void EnumEntry(DbgList *p, TagBinder *b) {
  BindList *l = tagbindenums_(b);
  EnumElt *elts = NULL;
  int32 count = 0;

  for (; l != NULL; l = l->bindlistcdr, count++) {
    EnumElt *el = (EnumElt *)DbgAlloc(sizeof(EnumElt));
    Binder *elt = l->bindlistcar;
    cdr_(el) = elts;
    el->name = symname_(bindsym_(elt));
    el->val = bindenumval_(elt);
    elts = el;
  }
  p->car.Tag.entries = count;
  p->car.Tag.elts.e = (EnumElt *)dreverse((List *)elts);
}

static DbgList *StructRep(TagBinder *b, int32 size, DbgList **list) {
  DbgList *p = (DbgList *)b->tagbinddbg;
  if (p == NULL) {
    DbgListSort sort = (attributes_(b) & bitoftype_(s_enum)) ? Enum :
                       (attributes_(b) & bitoftype_(s_union)) ? Union :
                                                                Struct;
    p = (DbgList*)DbgAlloc(DbgListVarSize(Tag));
    p->sort = (attributes_(b) & TB_DEFD) ? sort : (DbgListSort)(sort+S_Undef);
    p->index = -1;
    p->car.Tag.elts.e = NULL;
    if (isgensym(tagbindsym_(b))) {
      p->car.Tag.named = NO;
      p->car.Tag.tag.anonindex = anonindex++;
    } else {
      p->car.Tag.named = YES;
      p->car.Tag.tag.name = symname_(tagbindsym_(b));
    }
    cdr_(p) = *list;
    *list = p;
    b->tagbinddbg = (int32)p;
  } else if ((attributes_(b) & TB_DEFD) && (p->sort & S_Undef))
    /* Previously forward referenced and now defined */
    p->sort = (DbgListSort)(p->sort & ~S_Undef);
  else
    return p;

  if (attributes_(b) & bitoftype_(s_enum))
    EnumEntry(p, b);
  else
    StructEntry(p, b, attributes_(b) & CLASSBITS, size, list);
  return p;
}

#define SetDerivedType(p, n) (((p)->w |= (n) << ((p)->modct*2+4)), (p)->modct++)
#define SetBaseType(p, n) ((p)->w |= (n))

static void TypeRep_Struct(TypeExpr *x, Dbg_Type *typep, int tagtype, DbgList **list) {
  TagBinder *b = typespectagbind_(x);
  int32 size = attributes_(b) & TB_DEFD ? sizeoftype(x) : 0;
  typep->tag = StructRep(b, size, list);
  SetBaseType(typep, tagtype);
}

static void TypeRep(TypeExpr *x, Dbg_Type *typep, DbgList **list) {
  int32 dim[4], size = 0;
  int dimct = 0;
  typep->modct = 0;
  typep->w = 0;
  typep->tag = NULL;
  for (;; x = typearg_(x)) {
    x = princtype(x);  /* lose intermediate typedefs */
    switch (h0_(x)) {
    case t_content:
    case t_ref:         /* @@@ OK? */
      SetDerivedType(typep, DT_PTR);
      break;
    case t_subscript:
      SetDerivedType(typep, DT_ARRAY);
      if (dimct == 0) size = sizeoftype(x);
      dim[dimct++] = typesubsize_(x) == NULL ? 1 : evaluate(typesubsize_(x));
      break;
    case t_fnap:
      SetDerivedType(typep, DT_FCN);
      break;
    case s_typespec:
      { SET_BITMAP m = typespecmap_(x);
        switch (m & -m) {   /* LSB - unsigned32/long etc. are higher */
        case bitoftype_(s_char):
          { int32 mcr = mcrepoftype(x);
            SetBaseType(typep, (mcr & MCR_SORT_MASK) == MCR_SORT_SIGNED ?
                                            T_CHAR : T_UCHAR);
            goto ExitLoop;
          }
        case bitoftype_(s_int):
          if (m & BITFIELD) syserr(syserr_dbg_bitfield);
          { int32 mcr = mcrepoftype(x);
            int32 n = mcr & MCR_SIZE_MASK;
            SetBaseType(typep, (mcr & MCR_SORT_MASK) == MCR_SORT_SIGNED ?
                                               (n == 2 ? T_SHORT : T_INT) :
                                               (n == 2 ? T_USHORT : T_UINT));
            goto ExitLoop;
          }
        case bitoftype_(s_double):
          SetBaseType(typep, (m & bitoftype_(s_short)) ? T_FLOAT : T_DOUBLE);
          goto ExitLoop;
        case bitoftype_(s_enum):
          TypeRep_Struct(x, typep, T_ENUM, list);
          goto ExitLoop;
        case bitoftype_(s_struct):
        case bitoftype_(s_class):
          TypeRep_Struct(x, typep, T_STRUCT, list);
          goto ExitLoop;
        case bitoftype_(s_union):
          TypeRep_Struct(x, typep, T_UNION, list);
          goto ExitLoop;
        case bitoftype_(s_void):
          SetBaseType(typep, T_NULL); /* ? no T_VOID */
          goto ExitLoop;
        default:
          break;
        }
      }
        /* drop through */
    default:
      syserr(syserr_dbg_typerep, (VoidStar)x, (long)typespecmap_(x));
      SetBaseType(typep, T_NULL);
      goto ExitLoop;
    }
  }
ExitLoop:
  typep->dimct = dimct;
  if (dimct == 0)
    typep->dims = NULL;
  else {
    typep->dims = (int32 *)DbgAlloc(((int32)dimct+1)*sizeof(int32));
    typep->dims[0] = size;
    memcpy(&typep->dims[1], &dim[0], dimct*sizeof(int32));
  }
}

static void AddVar(Symstr *name, int sourcepos, int stgclass,
                   int base, int32 addr, TypeExpr *type, int32 undef,
                   DbgList **list) {
  DbgList *p = (DbgList *)DbgAlloc(DbgListVarSize(Var));
  p->sort = (DbgListSort)(Var+undef);
  p->car.Var.stgclass = stgclass;
  p->car.Var.sourcepos = sourcepos;
  p->car.Var.location = addr;
  p->car.Var.name = name;
  p->car.Var.section = base;
  p->cdr = *list;
  *list = p;
  TypeRep(type, &p->car.Var.type, list);
}

void dbg_topvar(Symstr *name, int32 addr, TypeExpr *t, int stgclass,
                FileLine fl) {
  if (usrdbg(DBG_PROC)) {
    int base = N_UNDEF;
    int stg = (stgclass & DS_REG) ? C_REG :
              (stgclass & DS_EXT) ? C_EXT:
                                    C_STAT;
    if (stgclass & DS_BSS)
      base = N_BSS;
    else if (stgclass & DS_CODE)
      base = N_TEXT;
    else if (!(stgclass & DS_REG) && (stgclass & (DS_EXT+DS_UNDEF)) != DS_EXT+DS_UNDEF)
      base = N_DATA;

    if (debugging(DEBUG_Q)) cc_msg("top var $r %x @ %.6lx\n", name, stgclass, (long)addr);
    CheckFile(fl.f);
    { DbgList **list = stgclass & DS_EXT ? &globdbglist : &statdbglist;
      int32 undef = stgclass & DS_UNDEF ? S_Undef : 0;
      if (stgclass != 0 && stg != C_REG) {
        DbgList *p;
        for (p = *list ; p != NULL ; p = cdr_(p))
          if ( (p->sort == UndefVar || p->sort == Var) &&
               p->car.Var.stgclass == stg &&
               p->car.Var.name == name) {
            if (!undef) {
              p->sort = Var;
              p->car.Var.location = addr;
              p->car.Var.section = base;
              p->car.Var.sourcepos = fl.l;
            }
            return;
          }
      }
      AddVar(name, fl.l, stg, base, addr, t, undef, list);
    }
  }
}

void dbg_type(Symstr *name, TypeExpr *t, FileLine fl) {
/* This only gets called on top-level types */
  DbgList *p = (DbgList*) DbgAlloc(DbgListVarSize(Var));
  Dbg_Type type;
  if (debugging(DEBUG_Q)) cc_msg("type $r\n", name);
  CheckFile(fl.f);
  TypeRep(t, &type, &globdbglist);
  if (!isgensym(name)) {
    p->sort = Type;
    p->car.Var.name = name;
    p->car.Var.type = type;
    p->car.Var.sourcepos = fl.l;
    p->cdr = globdbglist;
    globdbglist = p;
  }
}

static DbgList *locvars;

void dbg_proc(Symstr *name, TypeExpr *t, bool ext, FileLine fl) {
  if (usrdbg(DBG_ANY)) {
    DbgList *p = (DbgList*) DbgAlloc(DbgListVarSize(Proc));
    if (debugging(DEBUG_Q)) cc_msg("startproc $r\n", name);
    CheckFile(fl.f);
    t = princtype(t);
    p->sort = Proc;
    if (h0_(t) != t_fnap) syserr(syserr_dbg_proc);
    TypeRep(t, &p->car.Proc.type, &locdbglist);
    p->car.Proc.oldstyle = typefnaux_(t).oldstyle;
    p->car.Proc.sourcepos = fl.l;
    p->car.Proc.filepos = fl.filepos;
    p->car.Proc.entryaddr = 0;       /* fill in at dbg_enterproc */
    p->car.Proc.bodyaddr = 0;        /* fill in at dbg_bodyproc */
    p->car.Proc.end = 0;             /* fill in at dbg_endproc   */
    p->car.Proc.name = name;
    p->car.Proc.stgclass = ext ? C_EXT : C_STAT;
    p->car.Proc.linelist = NULL;
    p->cdr = locdbglist;             /* do this last (typerep above) */
    dbglistproc = locdbglist = p;    /* so can be filled in */
    locvars = NULL;
  }
}

void dbg_enterproc(void)
{   if (usrdbg(DBG_ANY))
    {   DbgList *p = dbglistproc;
        if (p == 0 || p->sort != Proc || p->car.Proc.entryaddr != 0)
            syserr(syserr_dbg_proc1);
        if (debugging(DEBUG_Q))
            cc_msg("enter $r @ %.6lx\n",
                    p->car.Proc.name, (long)codebase);
        p->car.Proc.entryaddr = codebase;
    }
}

/* The following routine records the post-entry codeaddr of a proc */
void dbg_bodyproc(void)
{   if (usrdbg(DBG_ANY))
    {   DbgList *p = dbglistproc;
        if (p == 0 || p->sort != Proc || p->car.Proc.bodyaddr != 0)
            syserr(syserr_dbg_proc1);
        if (debugging(DEBUG_Q))
            cc_msg("body $r @ %.6lx\n",
                    p->car.Proc.name, (long)(codebase+codep));
        p->car.Proc.bodyaddr = codebase+codep;
    }
}

void dbg_return(int32 addr) {
  IGNORE(addr);
}

void dbg_xendproc(FileLine fl) {
  if (usrdbg(DBG_ANY)) {
    DbgList *q = dbglistproc;
    DbgList *p = (DbgList*) DbgAlloc(DbgListVarSize(EndProc));
    if (q == 0 || q->sort != Proc || q->car.Proc.end != 0)
        syserr(syserr_dbg_proc1);
    if (debugging(DEBUG_Q))
        cc_msg("endproc $r @ %.6lx\n",
                q->car.Proc.name, (long)(codebase+codep));
    q->car.Proc.end = p;
    p->sort = EndProc;
    p->car.EndProc.sourcepos = fl.l;
    p->car.EndProc.endaddr = codebase+codep;
    p->car.EndProc.fileentry = fl.f;
    p->cdr = locdbglist;
    locdbglist = p;
    dbglistproc = NULL;
  }
}

/* dbg_locvar() registers the name and line of a declaration, and internalises
 * the type.  Location info cannot be added until after register allocation.
 * See also dbg_scope which completes.
 * (Type internalisation cannot be done then, because by that time the tree
 * has evaporated).
 * Also remember that dead code elimination may remove some decls.
 */
void dbg_locvar(Binder *b, FileLine fl) {
  Symstr *name = bindsym_(b);
  if (usrdbg(DBG_VAR)) {
    if (isgensym(name)) {
      if (bindstg_(b) & bitofstg_(s_typedef)) {
        Dbg_Type type;
        TypeRep(bindtype_(b), &type, &locdbglist);
      }
    } else if (!(bindstg_(b) & bitofstg_(s_extern))) {
      if (debugging(DEBUG_Q)) cc_msg("note loc var $b\n", b);
      AddVar((Symstr *)b, fl.l, 0, NULL, 0, bindtype_(b), S_Undef, &locvars);
    }
  }
}

static DbgList *FindLocVar(Binder *b) {
  DbgList *p, **pp = &locvars;
  for (; (p = *pp) != NULL; pp = &cdr_(p))
    if (p->sort == UndefVar && (Binder *)p->car.Var.name == b) {
      *pp = cdr_(p);
      return p;
    }
  return NULL;
}

void dbg_locvar1(Binder *b) {
  Symstr *name = bindsym_(b);
  int base = N_UNDEF;
  DbgList *p = FindLocVar(b);
  int stgclass;
  int stgclassname;
  int32 addr = bindaddr_(b);
  if (p == NULL || p->car.Var.sourcepos == -1) {
    if (debugging(DEBUG_Q)) cc_msg(" omitted");
    return;   /* invented variable name (e.g. s_let) */
  }
  cdr_(p) = locdbglist;
  locdbglist = p;
  p->sort = Var;
  p->car.Var.name = name;
  switch (bindstg_(b) & PRINCSTGBITS) {
  case bitofstg_(s_typedef):
    if (debugging(DEBUG_Q)) cc_msg(" <typedef>");
    p->sort = Type;
    return;
  case bitofstg_(s_static):
    stgclass = C_HIDDEN, stgclassname = 'S';
    base = (bindstg_(b) & u_constdata) ? N_TEXT :
           (bindstg_(b) & u_bss) ? N_BSS :
                                   N_DATA;
    break;
  case bitofstg_(s_auto):
    if (bindxx_(b) != GAP) {
      stgclass = (addr & BINDADDR_MASK) == BINDADDR_ARG ? C_REGPARM : C_REG;
      stgclassname = 'R', addr = register_number(bindxx_(b));
    } else switch (addr & BINDADDR_MASK) {
      case BINDADDR_ARG:
        stgclass = C_ARG, stgclassname = 'A', addr = local_fpaddress(addr);
        break;
      case BINDADDR_LOC:
        stgclass = C_AUTO, stgclassname = 'P', addr = local_fpaddress(addr);
        break;
      case 0:
        /* probably declared but not used case (where addr is still a bindlist) */
        p->sort = Ignore;
        if (bindstg_(b) & b_bindaddrlist) {
          if (debugging(DEBUG_Q)) cc_msg(" unused - omitted");
          return;
        }
        /* otherwise, fall into internal error case */
      default:
        syserr(syserr_dbg_table, name, (long)bindstg_(b), (long)addr);
        return;
    }
    break;
  default:
    syserr(syserr_dbg_table, name, (long)bindstg_(b), (long)addr);
    return;
  }
  if (debugging(DEBUG_Q)) cc_msg(" %c %lx", stgclassname, (long)addr);
  p->car.Var.stgclass = stgclass;
  p->car.Var.location = addr;
  p->car.Var.section = base;
}

bool dbg_scope(BindListList *newbll, BindListList *oldbll)
{   int32 entering = length((List *)newbll) - length((List *)oldbll);
    if (entering == 0) return NO;
    if (entering < 0)
    {   BindListList *t = newbll;
        newbll = oldbll, oldbll = t;
    }
    if (length((List *)oldbll) > 0) {
        BindListList *bll = newbll;
        DbgList *last = NULL;
        for (bll = newbll; bll != oldbll; bll = bll->bllcdr) {
            if (bll == 0) syserr(syserr_dbg_scope);
            if (bll->bllcar != 0) {
                DbgList *p = (DbgList *)DbgAlloc(DbgListVarSize(Block));
                dbglistscope = p;
                cdr_(p) = locdbglist;
                if (entering > 0) {
                  p->sort = BlockStart;
                  p->car.Block.p = dbglistblockstart;
                  dbglistblockstart = p;
                } else {
                  DbgList *q = dbglistblockstart;
                  p->sort = BlockEnd;
                  p->car.Block.p = NULL;
                  dbglistblockstart = q->car.Block.p;
                  q->car.Block.p = p;
                }
                p->car.Block.s.next = last; /* filled in soon by INFOSCOPE */
                locdbglist = p;
                last = p;
            }
        }
    }
    if (debugging(DEBUG_Q)) cc_msg("scope %ld\n", entering);
    for (; newbll != oldbll; newbll = newbll->bllcdr)
    {   SynBindList *bl;
        if (newbll == 0) syserr(syserr_dbg_scope);
        for (bl = newbll->bllcar; bl; bl = bl->bindlistcdr)
        {   Binder *b = bl->bindlistcar;
            if (bindstg_(b) & b_dbgbit) continue; /* for this and next line */
            bindstg_(b) |= b_dbgbit;              /* see end of routine cmt */
            if (debugging(DEBUG_Q))
                cc_msg("  %s $b",
                        entering>=0 ? "binding" : "unbinding",
                        b);
            if (entering >= 0)
                dbg_locvar1(b);
            if (debugging(DEBUG_Q))
                cc_msg("\n");
        }
    }
    return YES;
    /* Ask for INFOSCOPE item to get called back more or less immediately */
    /* from the local cg (INFOSCOPE item) to fill in the codeaddr         */
}

/* Dummy procedure not yet properly implemented, included here to keep in */
/* step with dbx.c */
void dbg_commblock(Binder *b, SynBindList *members, FileLine fl) {
  IGNORE(b); IGNORE(members); IGNORE(fl);
}

static union {
  char c[18];
  unsigned8 b[18];
  unsigned16 h[9];
  unsigned32 w[5];
} aux;

static void ClearAux() {
  memset(&aux, 0, 18);
}

static void SetNextIndex(DbgList *p, int n) {
  aux.w[3] = (p == NULL) ? 0 : TargetWord(p->index+n);
}

static void SetSourcePos(int32 n) {
  aux.h[2] = TargetHalf(n);
}

static void SetStructSize(DbgList *p) {
  aux.h[3] = TargetHalf(p->car.Tag.size);
}

static void SetStructRef(DbgList *p) {
  aux.w[0] = TargetWord(p->index);
  SetStructSize(p);
}

static void *TypeAuxEntry(Dbg_Type *t, int pos) {
  if (AuxEntryCount(t) == 0) return NULL;
  ClearAux();
  if (t->tag != NULL) SetStructRef(t->tag);
  if (t->dimct != 0) {
    int i = 0;
    for (; i <= t->dimct; i++)
      aux.h[3+i] = TargetHalf(t->dims[i]);
    SetSourcePos(pos);
  }
  return &aux;
}

static int32 globindex;

typedef enum {
  ne_all,
  ne_def,
  ne_undef
} NEType;

static void WriteEntries(DbgList *p, NEType flag) {
  for (; p != NULL; p = cdr_(p))
    if (flag == ne_all ||
        (flag == ne_def ? p->sort != UndefVar : p->sort == UndefVar))
      switch (p->sort) {
      default:
        syserr(syserr_dbg_write, (long)p->sort);
        break;
      case File:
        ClearAux();
        { UnparsedName un;
          fname_parse(p->car.File.name, "c C h H", &un);
          un.plen = un.vlen = 0;
          un.vol = un.path = NULL;
          fname_unparse(&un, FNAME_AS_NAME, aux.c, 15);
        }
        obj_stab(".file", p->car.File.next == NULL ? globindex : p->car.File.next->index,
                 N_DEBUG, T_NULL, C_FILE, &aux);
        break;
      case Proc:
        ClearAux();
        TypeAuxEntry(&p->car.Proc.type, 0);
        aux.w[1] = TargetWord(p->car.Proc.end->car.EndProc.endaddr - p->car.Proc.entryaddr);
        aux.w[2] = TargetWord(p->car.Proc.filepos);
        aux.h[8] = TargetHalf(p->car.Proc.oldstyle ? 14 : 15);
          /* Normal arithmetic promotions, 64 bit IEEE fp (what does this mean?) */
        SetNextIndex(p->car.Proc.end, 2);
        obj_stab(symname_(p->car.Proc.name), p->car.Proc.entryaddr, N_TEXT,
                 p->car.Proc.type.w, p->car.Proc.stgclass, &aux);
        ClearAux();
        SetSourcePos(p->car.Proc.sourcepos);
        SetNextIndex(p->car.Proc.end, 2);
        obj_stab(".bf", p->car.Proc.bodyaddr, N_TEXT, T_NULL, C_FCN, &aux);
        break;
      case EndProc:
        ClearAux();
        SetSourcePos(p->car.EndProc.sourcepos);
        obj_stab(".ef", p->car.EndProc.endaddr, N_TEXT, T_NULL, C_FCN, &aux);
        break;
      case UndefVar:
        obj_stab(symname_(p->car.Var.name), 0, N_UNDEF, p->car.Var.type.w, C_EXT,
                 TypeAuxEntry(&p->car.Var.type, p->car.Var.sourcepos));
        break;
      case Var:
        obj_stab(symname_(p->car.Var.name), p->car.Var.location, p->car.Var.section,
                 p->car.Var.type.w, p->car.Var.stgclass,
                 TypeAuxEntry(&p->car.Var.type, p->car.Var.sourcepos));
        break;
      case Type:
        obj_stab(symname_(p->car.Var.name), 0, N_DEBUG, p->car.Var.type.w,
                 C_TPDEF, TypeAuxEntry(&p->car.Var.type, p->car.Var.sourcepos));
        break;
      case Struct:
      case Union:
      case UndefStruct:
      case UndefUnion:
        { char b[16];
          char *name;
          int t, cl;
          if (p->sort == Struct || p->sort == UndefStruct)
            t = T_STRUCT, cl = C_STRTAG;
          else
            t = T_UNION, cl = C_UNTAG;
          if (p->car.Tag.named)
            name = p->car.Tag.tag.name;
          else {
            sprintf(b, ".%ldfake", p->car.Tag.tag.anonindex);
            name = b;
          }
          ClearAux();
          SetStructSize(p);
          SetNextIndex(cdr_(p), 0);
          obj_stab(name, 0, N_DEBUG, t, cl, &aux);
          { StructElt *q = p->car.Tag.elts.s;
            for (; q != NULL; q = cdr_(q))
              obj_stab(q->name, q->val, N_ABS, q->type.w, C_MOS, TypeAuxEntry(&q->type, 0));
          }
          ClearAux();
          SetStructRef(p);
          obj_stab(".eos", p->car.Tag.size, N_ABS, T_NULL, C_EOS, &aux);
          break;
        }
      case Enum:
        { char b[16];
          char *name;
          if (p->car.Tag.named)
            name = p->car.Tag.tag.name;
          else {
            sprintf(b, ".%ldfake", p->car.Tag.tag.anonindex);
            name = b;
          }
          ClearAux();
          SetStructSize(p);
          SetNextIndex(cdr_(p), 0);
          obj_stab(name, 0, N_DEBUG, T_ENUM, C_ENTAG, &aux);
          { EnumElt *q = p->car.Tag.elts.e;
            for (; q != NULL; q = cdr_(q))
              obj_stab(q->name, q->val, N_ABS, T_MOE, C_MOE, NULL);
          }
          ClearAux();
          SetStructRef(p);
          obj_stab(".eos", p->car.Tag.size, N_ABS, T_NULL, C_EOS, &aux);
          break;
        }
      case BlockStart:
        ClearAux();
        SetNextIndex(p->car.Block.p, 2);
        obj_stab(".bb",
                 p->car.Block.s.codeaddr, N_TEXT, T_NULL, C_BLOCK, &aux);
        break;
      case BlockEnd:
        ClearAux();
        obj_stab(".eb",
                 p->car.Block.s.codeaddr, N_TEXT, T_NULL, C_BLOCK, &aux);
        break;
      }
}

static void FixDbgList(DbgList *p) {
  for (; p != NULL; p = cdr_(p)) {
    if (p->sort == UndefVar) {
      ExtRef *x = symext_(p->car.Var.name);
      if (x != NULL && (x->extflags & (xr_defloc+xr_defext))) {
        p->sort = Var;
        p->car.Var.location = x->extoffset;
        p->car.Var.section = x->extflags & xr_bss ? N_BSS : N_DATA;
      }
    }
    if (p->sort == Proc || p->sort == Var || p->sort == UndefVar) {
      ExtRef *x = symext_(p->car.Var.name);
      if (x != NULL) x->extflags |= xr_deleted;
    }
  }
}

static void RenumberExtRef(Symstr *sym, int32 index) {
  ExtRef *x = symext_(sym);
  if (x != NULL) {
    if (!(x->extflags & xr_deleted)) syserr("Missed duplicate symbol");
    x->extindex = index;
  }
}

static int32 NumberEntries(DbgList *p, int32 index, NEType flag) {
  for (; p != NULL; p = cdr_(p)) {
    if (flag == ne_all ||
        (flag == ne_def ? p->sort != UndefVar : p->sort == UndefVar)) {
      p->index = index;
      switch (p->sort) {
      case Ignore:  break;
      case Proc:    RenumberExtRef(p->car.Proc.name, index);
                    index += 4; break; /* .bf entry too */
      case BlockStart:
      case BlockEnd:
      case File:
      case EndProc: index += 2; break;
      case UndefVar:
      case Var:     RenumberExtRef(p->car.Var.name, index);
                    /* and fall through */
      case Type:    index += 1 + AuxEntryCount(&p->car.Var.type); break;
      case Enum:    index += 2 + p->car.Tag.entries + 2; break;
      case UndefUnion:
      case UndefStruct:
      case Union:
      case Struct:  { StructElt *q = p->car.Tag.elts.s;
                      index += 4;  /* tag + .eos */
                      for (; q != NULL; q = cdr_(q))
                        index += 1+AuxEntryCount(&q->type);
                      break;
                    }
      default:      syserr("%d in NumberEntries", p->sort);
      }
    }
  }
  return index;
}

static int32 RenumberSyms(ExtRef *x, int32 index, int32 mask, int32 maskedval) {
  for (; x != NULL; x = x->extcdr)
    if ((x->extflags & mask) == maskedval) {
      x->extindex = index++;
      if (x->extflags & xr_section) index++;
    }
  return index;
}

static int32 dbg_fixup(ExtRef *symlist, int32 index) {
  /* Mark symbols with entries in symlist also present in a dbglist.
     If symbols in a dbglist are marked as undefined, but the symlist entry is
     marked as defined, fix up position and storage class in the dbglist entry
     (bss and tentatives: maybe someone should call dbg_topvar when the
      placement finally gets made).
     Number the symbols in dbglists, and the remaining unmarked symbols in
     symlist (locdbglist, then defloc things in symlist (should be just sections),
     then defined things in globdbglist, then defext things in symlist, then
     undefined things in globdbglist then symlist). Rewrite the index of marked
     symbols in symlist.
   */
  if (usrdbg(DBG_ANY)) {
    locdbglist = (DbgList *)dreverse(nconc((List *)statdbglist, (List *)locdbglist));
    globdbglist = (DbgList *)dreverse((List *)globdbglist);
    FixDbgList(locdbglist);
    FixDbgList(globdbglist);
    index = NumberEntries(locdbglist, 0, ne_all);
    globindex = index = RenumberSyms(symlist, index, xr_deleted+xr_defloc+xr_defext, xr_defloc);
    index = NumberEntries(globdbglist, index, ne_def);
    index = RenumberSyms(symlist, index, xr_deleted+xr_defloc+xr_defext, xr_defext);
    index = NumberEntries(globdbglist, index, ne_undef);
    return RenumberSyms(symlist, index, xr_deleted+xr_defloc+xr_defext, 0);
  } else
    return index;
}

static void dbg_outsymtab() {
  if (usrdbg(DBG_ANY)) {
    WriteEntries(locdbglist, ne_all);
    obj_outsymtab(xr_deleted+xr_defloc+xr_defext, xr_defloc);
    WriteEntries(globdbglist, ne_def);
    obj_outsymtab(xr_deleted+xr_defloc+xr_defext, xr_defext);
    WriteEntries(globdbglist, ne_undef);
    obj_outsymtab(xr_deleted+xr_defloc+xr_defext, 0);
  } else
    obj_outsymtab(0, 0);
  obj_outstringtab();
}

void dbg_init(void) {
  anonindex = 0;
  locdbglist = statdbglist = globdbglist = NULL;
  dbglistfile = dbglistproc = dbglistblockstart = NULL;
  dbglistscope = NULL;
}

#endif /* TARGET_HAS_DEBUGGER */

/* end of coffobj.c */
