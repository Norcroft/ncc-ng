/*
 * C pre-processor, cfe/pp.c
 * Copyright (C) Codemist Ltd., 1988-1992.
 * Copyright (C) Acorn Computers Ltd., 1988-1990.
 * Copyright (C) Advanced RISC Machines Ltd., 1990-1992.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$ Codemist 167
 * Checkin $Date$
 * Revising $Author$
 */

/* AM, july 90: fix pp recursion problem in macro args.                 */

/* AM: ansi ambiguities:                                                */
/*  #defines: i(x)=[x]  a=( b=) does i(i a 3 b)->[[3]] or [i(3)]?       */
/* AM: bugs:                                                            */
/* 1. #error/#ident/#pragma do not parse strings.                       */
/* 2. #define: j(x)=i(x) i(x)=h##x f=g+f  then j(f) *should* be hg+f!   */
/* AM: beware the different ANSI/PCC rules for PP_TOKSEP.               */
/* AM: memo: rework/kill PP_NOEXPAND in favour of pp_noexpand.  Also,   */
/*    does the use of pp_hashalive resolve ANSI ambiguities as we want? */
/* AM: memo: rework the pp_unrdch() call in pp_checkid(no '(').         */

#undef ISO8859
#ifdef COMPILING_ON_ACORN_KIT
#  define ISO8859  1
#endif
#ifdef COMPILING_ON_UNIX
#  define ISO8859  1
#endif

/* The following hack supports ebcdic, pure ascii or iso8859.           */
/* We could (more portably) turn each macro into a test on compiler     */
/* (not preprocessor) character constants.                              */
#if 'A' == 193          /* nasty, ansi-non-guaranteed test for ebcdic   */
#  define legal_non_isprint(ch) 0
#else                                            /* ascii-like presumed */
#  ifdef ISO8859
#    define legal_non_isprint(ch) ((ch) >= 128+32)
#  else                                                /* Mac, PC, etc. */
#    define legal_non_isprint(ch) ((ch) >= 128)
#  endif
#endif

/*
 * NOTE: This file will need adjustment for use with Pascal and Fortran.
 * For now, it is left almost unaltered, but with some conversions disabled
 * in a crude manner, contingent on #ifdef PASCAL, #ifdef FORTRAN, etc.
 */

/* N.B. This pre-processor conforms to the May 86 draft ANSI spec.       */
/* However, there it was defined by example and the Oct 86 draft gave    */
/* a more stringent definition by (more) examples!  I doubt that it is   */
/* up to the latter spec, but propose to do nothing about this until the */
/* next draft spec or standard as further changes are proposed.          */
/* AM Jan 90: AM believes that the macro processing is very close to     */
/* the latest (Dec 88) ANSI draft modulo ambiguities.                    */
/* 29-Dec-87: AM has put the profile_xxx stuff here while it is in flux  */
/* so that he can try to understand them!  In a separate file one day?   */
/* Observation: the profile instrumentation fails (due to strcmp) if     */
/* a file is included more than once or #line is used.                   */
/* Memo: chase out '@@@'s.  Also abuf for non-essential uses.            */

#include <stdio.h>
#include <ctype.h>
#include <stddef.h>
#include <time.h>
#ifdef __STDC__
#  include <string.h>
#  include <stdlib.h>
#  define uint HIDE_HPs_uint
#  include <limits.h>             /* for UCHAR_MAX */
#  undef uint
#else
#  define UCHAR_MAX 255
#  include <strings.h>
#endif
#include "globals.h"
#include "pp.h"
#include "lex.h"
#include "syn.h"
#include "store.h"
#include "errors.h"
#include "mcdep.h"
#include "dump.h"
#include "compiler.h"
#include "trackfil.h"

#ifndef NO_INSTORE_FILES
#include "headers.c"        /* Tables for in-store headers */
#endif

#ifdef CALLABLE_COMPILER
#include "clbcomp.h"
#endif

#define NOT_A_CHARACTER  (512)                 /* cannot be saved in a char */
                                               /* only to be used in exprs  */
#ifdef PASCAL
#  define PASCAL_OR_FORTRAN  1
#  define COMMENT_START     '('
#  define COMMENT_END       ')'
#else
#  ifdef FORTRAN
#    define PASCAL_OR_FORTRAN  1
#    define COMMENT_START  NOT_A_CHARACTER     /* this will NEVER be found! */
#    define COMMENT_END    NOT_A_CHARACTER     /* this will NEVER be found! */
#  else
#    define COMMENT_START   '/'
#    define COMMENT_END     '/'
#  endif
#endif

/*
 * Note that there is much nastiness (probably necessary in C) in the odd
 * interface of the pre-processor having a back-route into the parser
 * and HENCE back into itself!!!
 */

#define PP_HASHSIZE  259L
#define PP_DIRLEN     16L
/*
 * PP_DEFLEN is max number of significant chars in an identifier.
 * It must be LESS than min(PP_ABUFINITSIZ,PP_DBUFSIZ)-UNRDCHMAX.
 */
#define PP_DEFLEN    250L
#define PP_UNRDCHMAX  16L  /* see pp_checkid and #pragma force_top_level */
/*
 * PP_NOEXPAND is a pseudo character to inhibit re-expansion of the
 * following name (may change to preceding soon).  It conspires with
 * the list pp_noexpand to inhibit recursive expansion.
 * Two mechanisms are needed in so that in #define i(x) x; #define f +f
 * the call i(f) causes arg f to re-write to +f(NOEXPAND) and the
 * re-scan of +f does not cause re-expansion to ++f.
 * Similarly, PP_TOKSEP is used to represent invisible space in
 *  "M-- where #define M -" which need to be spaces to lex but vanish
 * in stringify.  It also represents elided comments in pcc mode.
 * AM regards it as odd that the draft (dec 88) seems to say that
 * stringification (#s) of the above should yield "---" not "- --".
 * Changing PP_TOKSEP to ' ' in ANSI mode restores the more logical code.
 *
 * To avoid stealing characters from the source set, we use '\f' and '\v'
 * which are only quasi-illegal in ANSI input and which are converted early
 * (by pp_rdch1()) to '\n', when executing in ANSI mode.
 *
 * In -pcc mode, we use the same characters, but pp_rdch() uses '\b' as an
 * escape code, converting '\b', '\f' and '\v' to PP_ESC PP_ESC, PP_ESC '\t'
 * and PP_ESC ' ', respectively. The escape sequences are later undone by
 * pp_process(). BUT ONLY in -pcc mode.
 */

#define PP_ESC       '\b'
#define PP_NOEXPAND  '\f'
#define PP_TOKSEP    '\v'

#define PP_EOM       0          /* value 0 exploited by strcpy/'%s'.    */

#define PP_MACSTART  1
#define PP_CIDCHAR   2
#define PP_WHITE     4
static char pp_ctype[UCHAR_MAX+1];
/* ch & 0xff used to be (unsigned char)ch in the macros below, but some
   compilers seem not to handle that correctly, and there seems no
   overwhelming reason for preferring one form to the other.
 */
#define pp_macstart(ch) (pp_ctype[ch & 0xff] & PP_MACSTART)
#define pp_cidchar(ch)  (pp_ctype[ch & 0xff] & PP_CIDCHAR)
#define pp_white(ch)    (pp_ctype[ch & 0xff] & PP_WHITE)
#define pp_translation(ch) (pp_translate[ch & 0xff])

#define PP_EOLP(ch) ((ch) == '\n')

#define HASH(hash, ch) (((hash * 39) + ch) & 0xffffff)

#define PP_ARGLINES_WARN_VAL  10        /* warn after 10 lines of arguments */

#ifdef COMPILING_ON_MAC
/* some Mac compilers admit that some high-bit set chars are printable */
/* and some others don't define isprint, etc. above 0x7f (which is non-ANSI) */
#  define isdigit(c) ((c & ~0x7f) == 0 && (isdigit)(c))
#  define isalpha(c) ((c & ~0x7f) == 0 && (isalpha)(c))
#  define isalnum(c) ((c & ~0x7f) == 0 && (isalnum)(c))
#  define isspace(c) ((c & ~0x7f) == 0 && (isspace)(c))
#  define isprint(c) ((c & ~0x7f) == 0 && (isprint)(c))
#endif

/*
 * structures - local to this file ...
 */

typedef struct arglist {
  char *argname;
  struct arglist *argchain;
  int32 argactual;   /* now offset into pp_abufbase */
#define DUFF_OFFSET 0x01010101
/* beware: it is only our expansion strategy that allows us to
   use shallow binding of actual/formal correspondence.
   See later changes in pp_arg_link.
*/
} PP_ARGENTRY;

#define pp_argname_(p)    ((p)->argname)
#define pp_argchain_(p)   ((p)->argchain)
#define pp_argactual_(p)  ((p)->argactual)

typedef union {
  uint32 w;
  struct {
/* I limit the reference count to 16 bits so that there can not be any     */
/* trouble on machines with sizeof(int)==2                                 */
    unsigned int uses:16,   /* incremented on reference */
/* ismagic is 14 bits so that this whole field is 32 bits wide */
                 ismagic:13,/* things like __TIME__     */
                 noifdef:1, /* 1 if not allowed to #ifdef xxx */
                 noargs:1,  /* 1 if noargs              */
                 alive:1;   /* 0 => undef'd, 1 => def'd */
  } b;
} PP_HASHBITS;

typedef struct hashentry {
  char *name;
  union { char const *s; int32 i; } body;  /* #define text or magic (e.g PP__LINE) */
  struct hashentry *chain;
  PP_HASHBITS u;
  struct hashentry *defchain;  /* chain in definition order */
/* AM: the next two fields solely cope with ANSI inhibition of macro    */
/* definitions during rescanning.  It would be more space efficient     */
/* to use a separate list (next/name/len).  Moreover, this current      */
/* structure requires a definition to be suppressed only once at any    */
/* one time to work.  This would seem to be the case, but consider      */
/* #define f g(f); #define g(x) x; (@@@ seemingly ANSI ambiguity).      */
/* We expand 'f' above to 'f', but there is a good case for the 'f(g)'  */
/* interpretation too.                                                  */
  struct hashentry *unchain;   /* used to inhibit recursive expansion */
  int32 sleepleft;             /* ditto -- chars to read in ebuf.     */
#define PP_NOARGHASHENTRY  offsetof(PP_HASHENTRY,arglist)
  struct arglist *arglist;     /* only if noargs==0   */
} PP_HASHENTRY;
typedef PP_HASHENTRY *(PP_HASHTABLE[PP_HASHSIZE]);

#define pp_hashname_(p) ((p)->name)
#define pp_hasharglist_(p) ((p)->arglist)
#define pp_hashbody_(p) ((p)->body.s)
#define pp_hashmagic_(p) ((p)->body.i)
#define pp_hashchain_(p) ((p)->chain)
#define pp_hashnoargs_(p) ((p)->u.b.noargs)
#define pp_hashalive_(p) ((p)->u.b.alive)
#define pp_hashismagic_(p) ((p)->u.b.ismagic)
#define pp_noifdef_(p) ((p)->u.b.noifdef)
#define pp_hashuses_(p)  ((p)->u.b.uses)
#define pp_unchain_(p)  ((p)->unchain)
#define pp_sleepleft_(p)  ((p)->sleepleft)
#define pp_hashdefchain_(p) ((p)->defchain)

/* The following constants really are ints, or maybe enums */
#define PP__LINE (-1)
#define PP__FILE (-2)
#define PP__DATE (-3)
#define PP__TIME (-4)
#define PP__ZERO (-6)
#define PP__ONE  (-7)

typedef struct ifstack {
  struct ifstack *chain;
  bool seenelse;
  bool oldskip;
  bool skipelse;
} PP_IFSTACK;

#define pp_ifchain_(p)    ((p)->chain)
#define pp_ifseenelse_(p) ((p)->seenelse)
#define pp_ifoldskip_(p)  ((p)->oldskip)
#define pp_ifskipelse_(p) ((p)->skipelse)

typedef struct filestack {
  struct filestack *chain;
  FILE *stream;
  FileLine fl;
#ifndef NO_LISTING_OUTPUT
  int32 propoint;
  int32 filenumber;
#endif
  PP_IFSTACK *ifstart;
  char const *ifdefname;        /* name of macro guarding this #include (if any) */
  PP_IFSTACK *guard_ifndef;
  pp_uncompression_record *stringfile;
} PP_FILESTACK;

#define pp_filchain_(p)   ((p)->chain)
#define pp_filstream_(p)  ((p)->stream)
#define pp_fileline_(p)   ((p)->fl)
#define pp_propoint_(p)   ((p)->propoint)
#define pp_filenumber_(p) ((p)->filenumber)
#define pp_stringfile_(p) ((p)->stringfile)

int pp_inhashif;              /*/*should this really belong to syn_hashif? */

static PP_HASHTABLE *pp_hashtable;
static PP_HASHENTRY *pp_noexpand,
             *pp_hashfirst, *pp_hashlast, *pp_hashone, *pp_hashzero;
static PP_IFSTACK *pp_ifstack, *pp_freeifstack;
static PP_FILESTACK *pp_filestack, *pp_freefilestack;

static int32 pp_nsubsts;
static bool pp_skipping, pp_instring;
typedef enum { NO_COMMENT, BALANCED_COMMENT, EOL_COMMENT } PP_CommentKind;
static PP_CommentKind pp_incomment = NO_COMMENT;
static bool seen_pp_token;
static bool minus_e;

static FILE *pp_cis;
static FileLine *pp_fl;
int32 pp_pragmavec['z'-'a'+1];

static char pp_datetime[26];

/*
 * Diagnostics and free store package...
 */

static VoidStar pp_alloc(int32 n)
{   return GlobAlloc(SU_PP, n);
}

/*
 * ACN's listing option code...
 */
#ifndef NO_LISTING_OUTPUT
bool list_this_file;           /* exported copy of MSB of pp_filenumber    */
/*
 * @@@ This depends on the ARM-dependent output of _write_profile
 * and is read directly in binary. (Hmm).
 */
typedef struct XCount
{ unsigned32 count;
  unsigned line:16,
           filename:16;
} XCount;
static XCount *profile_data = NULL;    /* profile data table         */
static int32 profile_count = 0;        /* size thereof (0 => no map) */
static char **profile_files = NULL;    /* file name table            */
static uint32 profile_nfiles = 0;      /* size thereof               */
static int32 profile_ptr = 0;  /* profile_data index ( < profile_count)    */
static uint32 pp_filenumber;   /* profile_files index ( < profile_nfiles)  */
                               /* also gets 0x80000000 bit set (>= 0 test) */
                               /* ... only used for listing on/off.        */

static int Exec_Rec_Compare(ConstVoidStar a, ConstVoidStar b)
{
    const XCount *aa = (const XCount *)a, *bb = (const XCount *)b;
    int32 k = (int32)aa->filename - (int32)bb->filename;
    if (k == 0) k = (int32)aa->line - (int32)bb->line;
/* The following line ensures that I return an int value that makes sense  */
/* even if plain int is 16 bits. This is needed if I am to use the built-  */
/* in qsort sort procedure.                                                */
    return k == 0 ? 0 : k < 0 ? -1 : 1;
}

bool map_init(FILE *mapstream)
{
/* Data for annotation source listings to indicate how many times various  */
/* lines of code is global to the compilation.                             */
    uint32 w;
    XCount *data;
    char *namebodies;
    union map_filetable { int32 offset; char *addr; } *names;
    struct map_header { char magic[12];
                        uint32 namebytes, nfiles, ncounts; } h;
    profile_count = 0;  /* To disable the option */
    if (mapstream == NULL) return 1;
    if (fread(&h, sizeof(h), 1, mapstream) != 1 ||
        memcmp("\xff*COUNTFILE*", h.magic, 12) != 0) return 0;
    w = h.namebytes + 4*h.nfiles + 8*h.ncounts;
    namebodies = (char *)PermAlloc(w);
    if (namebodies == NULL) return 0;
    names = (union map_filetable *)(namebodies + h.namebytes);
    data = (XCount *)(names + h.nfiles);
    if (fread(namebodies, 1, (size_t)h.namebytes, mapstream) != h.namebytes ||
        fread(names, 4, (size_t)h.nfiles, mapstream) != h.nfiles ||
        fread(data, 8, (size_t)h.ncounts, mapstream) != h.ncounts ||
        fread(h.magic, 1, 12, mapstream) != 12 ||
        memcmp("\xff*ENDCOUNT*\n", h.magic, 12) != 0)
    {
        return 0;
    }
    for (w = 0; w < h.nfiles; w++)
        names[w].addr = namebodies + names[w].offset;
/* Now the data is read in - sort it by file name and line number so it    */
/* will be easier to access later.                                         */
    qsort((VoidStar)data, (size_t)h.ncounts, sizeof(XCount), Exec_Rec_Compare);
    profile_data = data;
    profile_count = h.ncounts;
    profile_files = (char **)names;
    profile_nfiles = h.nfiles;
    return 1;
}

#define CHARS_FOR_COUNTS 16

static void listing_nextline(uint32 ll)
{   uint32 line = ll + 1;
    int pos = 0;
    while (profile_data[profile_ptr].line < line &&
           profile_data[profile_ptr].filename == pp_filenumber &&
           profile_ptr < profile_count)
        profile_ptr++;
    while (profile_data[profile_ptr].line == line &&
           profile_data[profile_ptr].filename == pp_filenumber &&
           profile_ptr < profile_count)
        (pos += fprintf(listingstream, "%lu ",
                        profile_data[profile_ptr].count)),
        profile_ptr++;
    if (pos >= CHARS_FOR_COUNTS) fprintf(listingstream, "\n"), pos = 0;
    fprintf(listingstream, "%*s| ", (int)(CHARS_FOR_COUNTS-pos), "");
}

static void profile_find(char const *fname)
{   unsigned i = 0;
    int32 p = 0;
    if (profile_count == 0) return;
    while (!StrEq(fname, profile_files[i]) &&
        i < profile_nfiles) i++;            /* syserr(dropping off the end) */
    while (profile_data[p].filename != i &&
           p < profile_count) p++;
    pp_filenumber = i;
    profile_ptr = p;
}

#endif /* NO_LISTING_OUTPUT */


/*
 * buffers:  dbuf (defns) ebuf (expansions) abuf (args)
 * Maybe optimise later.
 */
#define PP_DBUFSIZ         1024L    /* default chunk for definitions */
#define PP_ABUFINITSIZ      512L
#define PP_EBUFINITSIZ      256L

#define pp_new_(type)      (pp_alloc(type))

static char *pp_dbufend, *pp_dbufseg, *pp_dbufptr;
#define pp_stuffid_(ch) \
    (pp_dbufptr==pp_dbufend ? pp_newdbuf(ch) : (*pp_dbufptr++ = (ch)))

static int pp_newdbuf(int x)
{ char *dbufbase;
  unsigned32 size = pp_dbufptr-pp_dbufseg;   /* size used in current dbuf */
  unsigned32 allocsize = PP_DBUFSIZ;         /* default size for new dbuf */
  /* allocate 1024 for small requests, but 2048 for 512-1023, etc. */
  while (size >= allocsize/2) allocsize *= 2;
  if (size > allocsize)
     syserr(syserr_newdbuf, (long)size, (long)allocsize);
  dbufbase = (char *)pp_alloc(allocsize);
#ifdef ENABLE_PP                /* spurious: deadcode elimination fixes */
  if (debugging(DEBUG_PP))
      cc_msg("new pp_dbuf(%ld)\n", (long)allocsize);
#endif
  if (size != 0) memcpy(dbufbase, pp_dbufseg, (size_t)size);
  pp_dbufseg = dbufbase;
  pp_dbufptr = dbufbase+size;
  pp_dbufend = dbufbase+allocsize;
  return (*pp_dbufptr++ = x);
}

static char *pp_closeid(void)
{ char *result;
  pp_stuffid_(0);
  result = pp_dbufseg;
  pp_dbufseg = pp_dbufptr;
  return result;
}

static char *pp_ebufbase, *pp_ebufptr, *pp_ebuftop, *pp_ebufend;
static char *pp_abufbase, *pp_abufoptr, *pp_abufptr, *pp_abufend;
static int32 pp_scanidx, pp_expand_level;

static void pp_abuf_ensure(int32 n)
{   while (pp_abufptr + n >= pp_abufend)
    {   int32 k = pp_abufend - pp_abufbase;
        char *d = (char *)pp_alloc(2*k);
#ifdef ENABLE_PP                /* spurious: deadcode elimination fixes */
        if (debugging(DEBUG_PP))
            cc_msg("up pp_abuf to %ld\n", (long)(2*k));
#endif
        memcpy(d, pp_abufbase, (size_t)k);
        pp_abufend = d + 2*k;
        pp_abufptr = d + (pp_abufptr - pp_abufbase);
        pp_abufoptr = d + (pp_abufoptr - pp_abufbase);
        pp_abufbase = d;
    }
}

static void pp_wrch(int ch)
{   if (pp_abufptr >= pp_abufend) pp_abuf_ensure(1);
    *pp_abufptr++ = ch;
}

static void pp_wrbuf(void *buf, int32 len)
{   pp_abuf_ensure(len);
    pp_abufptr = (char *) memcpy(pp_abufptr, buf, (size_t)len) + len;
}

static void pp_ebuf_ensure(int32 n)
{   while (pp_ebuftop + n >= pp_ebufend)
    {   int32 k = pp_ebufend - pp_ebufbase;
        char *d = (char *)pp_alloc(2*k);
#ifdef ENABLE_PP                /* spurious: deadcode elimination fixes */
        if (debugging(DEBUG_PP))
            cc_msg("up pp_ebuf to %ld\n", (long)(2*k));
#endif
        memcpy(d, pp_ebufbase, (size_t)k);
        pp_ebufend = d + 2*k;
        pp_ebuftop = d + (pp_ebuftop - pp_ebufbase);
        pp_ebufptr = d + (pp_ebufptr - pp_ebufbase);
        pp_ebufbase = d;
    }
}

static void pp_savch(int ch)
{   if (pp_ebuftop >= pp_ebufend) pp_ebuf_ensure(1);
    *pp_ebuftop++ = ch;
}

static void pp_savbuf(void const *buf, int32 len)
{   pp_ebuf_ensure(len);
    pp_ebuftop = (char *) memcpy(pp_ebuftop, buf, (size_t)len) + len;
}

#ifdef ENABLE_PP
static void pp_showsleep(void)
{   PP_HASHENTRY *p;
    for (p = pp_noexpand; p != 0; p = pp_unchain_(p))
        cc_msg("<sleeping %s %ld>", pp_hashname_(p), pp_sleepleft_(p));
}
#else
#define pp_showsleep() 0
#endif

static void pp_addsleep(int32 n)
{   PP_HASHENTRY *p;
    for (p = pp_noexpand; p != 0; p = pp_unchain_(p))
        pp_sleepleft_(p) += n;
}

static void pp_subsleep(int32 n)
{   PP_HASHENTRY *p;
    for (p = pp_noexpand; p != 0; p = pp_unchain_(p))
    {   pp_sleepleft_(p) -= n;
        if (debugging(DEBUG_PP) && pp_sleepleft_(p) < 0)
            cc_msg("<overslept %s %ld>\n", pp_hashname_(p), pp_sleepleft_(p));
    }
}

static void pp_awaken_all(void)
{   /* Maybe this should be a syserr() one day if pp_noexpand != 0.     */
    while (pp_noexpand)
    {   PP_HASHENTRY *p = pp_noexpand;
        pp_noexpand = pp_unchain_(p), pp_unchain_(p) = 0;
        pp_hashalive_(p) = 1;
    }
}

static void pp_sleep_name(PP_HASHENTRY *p, int32 n)
    {   /* suppress recursive invocations in ANSI mode -- PCC loops!    */
        if (pp_unchain_(p)) syserr(syserr_pp_recursion, pp_hashname_(p));
        pp_unchain_(p) = pp_noexpand;
        pp_sleepleft_(p) = 0;
        pp_hashalive_(p) = 0;
        pp_noexpand = p;
        pp_addsleep(n);
        if (debugging(DEBUG_PP))
            cc_msg("<sleep name %s, result size %ld>\n", pp_hashname_(p),
                   (long)n);
    }

/*
 * Support for built-in header files
 */

static pp_uncompression_record *active_string_file = NO;

struct pp_uncompression_record
{
    uint8 stack[32];
    uint8 const *pointer;
    uint8 compressed;
    uint32 height;
    uint16 const *compression_info;
};

static int pp_fetch_string_char(pp_uncompression_record *ur)
{
    int c, k;
    c = (ur->height == 0) ? *ur->pointer++ :
                            ur->stack[--ur->height];
    for (;;)
    {   k = ur->compression_info[c];
        if (k == c || ur->compressed == 0) return c;
/*
 * When genhdrs is establishes the greatest possible depth needed in
 * this stack and arranges to define HDRSTACKDEPTH suitably - thus no
 * run-time check for stack overflow is needed.
 */
        ur->stack[ur->height++] = k;
        c = k >> 8;
    }
}

FILE *new_compressed_header(FILE *f, pp_uncompression_record **urp) {
  uint32 stackdepth;
  uint32 size;
  pp_uncompression_record *ur;
  fread(&stackdepth, sizeof(uint32), 1, f);
  fread(&size, sizeof(uint32), 1, f);
  ur = (pp_uncompression_record *)GlobAlloc(SU_Other, sizeof(pp_uncompression_record) + 256 * sizeof(uint16) + size);
  { uint8 *b = (uint8 *)(ur + 1);
    fread(b, 1, 256 * sizeof(uint16) + (size_t)size, f);
    fclose(f);
    ur->compression_info = (uint16 *)b;
    ur->pointer = b + 256 * sizeof(uint16);
    ur->compressed = 1;
    ur->height = 0;
    *urp = ur;
    return stdin;
  }
}

#ifndef NO_INSTORE_FILES

static pp_uncompression_record hdrfile;

FILE *open_builtin_header(const char *name, pp_uncompression_record **urp)
{   int count;
    if (HasFeature(Feature_PCC) && StrEq(name, "strings.h"))
        name = "string.h";
    for (count=0; builtin_headers[count].name != 0; count++) {
        if (StrEq(name, builtin_headers[count].name))
        {   *urp = &hdrfile;
            hdrfile.height = 0;
            hdrfile.compressed = 1;
            hdrfile.pointer = &string_data[builtin_headers[count].content];
            hdrfile.compression_info = compression_info;
/*
 * The result (which is of type FILE *) must be handed back as a non-zero
 * value since it is compared against zero to check for success here.  But
 * when a string file has been opened the regular file pointer will never be
 * used, so the (non-zero) value returned is not very important.
 * The arbitrary use of 'stdin' is thus OK since ANSI say 'stdin' != NULL.
 */
            return stdin;
        }
    }
    return NULL;
}

#endif

/*
 * I/O routines, including ANSI trigraph routine. Built for speed.
 *
 * The idea we exploit here is that (i) only whole lines are interleaved by
 * #include and (ii) after a #included file has been processed, we continue
 * reading the NEXT line of the including file. By buffering whole lines,
 * we can reduce most overhead to once per line, rather than one per char.
 * As lines average 30-40 chars, this gives a major reduction in per-char
 * overhead. We also take the opportunity to unify in-store files with
 * regular files at this point. The only difference is that we don't copy
 * in-store files to the (partial) line buffer. The critical routines
 * are pp_fillbuf, pp_rdch1 and pp_rdch. pp_translate_1, pp_comment
 * and pp_comment_nl play supporting roles. The best order to read for
 * understanding is pp_rdch, pp_rdch1, pp_fillbuf, others.
 */

static int32 pp_rdcnt;                          /* the input buffer count */
static char  *pp_rdptr;                       /* the input buffer pointer */
static char  pp_linebuf[64];                     /* the input line buffer */
static char  pp_translate[256];
static int   pp_rdch1nls,                  /* count of \<NL>s outstanding */
             pp_rdch3nls;            /* count of <NL>s in current comment */
static bool  pp_in_directive;        /* pend pp_rdch3nls after '#'.       */

static void init_pp_fl(char const *filename)
{   pp_fl->f = filename;
    pp_fl->l = 1;
    pp_fl->column = 1;
    pp_fl->filepos = 0;
    /* ### morally right here ? */
    pp_fl->p = 0;
    pp_rdcnt = 0;
    pp_rdptr = NULL;
}

/* After a call to pp_fillbuf(), pp_rdptr points to the tail of a line or */
/* part thereof, pp_rdcnt is the number of chars left in the buffer and   */
/* the first character of the buffer (or EOF) is returned (we do this     */
/* because EOF cannot be stored as a character).                          */

static int pp_fillbuf(void)
{   uint32 n;
    char *s;

#ifdef NO_MLS_XDEVT_1823
/*
 * move the progress to cfe/rd_topdecl() to reduce overhead
 */
    UpdateProgress();
#endif

/* We now count \n when we read it (since file positions are now sampled
 * by lex at the start of each symbol).
 */
    s = pp_linebuf;

#ifndef NO_INSTORE_FILES
    if (active_string_file != NULL)
/* If reading from a compressed, in-memory, string file then get the next */
/* line. Note that we know that lines are terminated by \n, that a \n     */
/* precedes EOF, and that there are NO imbedded #includes.                */
    {   int ch;
        for (n = 0;  n < sizeof(pp_linebuf);)
        {   ch = pp_fetch_string_char(active_string_file);
            if (ch == 0) break;
            s[n++] = ch;
            if (ch == '\n') break;
        }
    }
    else
#endif
#ifdef CALLABLE_COMPILER
    if (expr_string != NULL) {
        strncpy(s, expr_string, sizeof(pp_linebuf));
        n = strlen(s);
        expr_string += n;
    } else
#endif
/* Reading from a real file. Here, pp_rdcnt == 0 OR pp_rdcnt == 1 and   */
/* the last character in the buffer should be saved before reading more */
/* (it's either '\' or '?'). Any other value of pp_rdcnt is ignored.    */
    {   FILE *cis = pp_cis;
        int ch;
        if ((n = pp_rdcnt) == 1)
            s[0] = pp_rdptr[-1];
        else n = 0;
        /* Read until EOF OR buffer full OR end of line character found */
        for (;;)
        {   ch = getc(cis);
            if (feof(cis)) break;
            s[n++] = ch;
            if (ch == '\n' ||
                ch == '\r' ||
                n >= sizeof(pp_linebuf)) break;
        }
        if (ferror(cis)) cc_fatalerr(pp_fatalerr_readfail);
        if (n == 0)                                      /* end of file */
        {   if (pp_rdptr != NULL && pp_rdptr[-1] != '\n')
            {
#ifndef HOST_DOES_NOT_FORCE_TRAILING_NL
                if (HasFeature(Feature_Fussy))
                    cc_pccwarn(pp_rerr_newline_eof);
#endif
                s[n++] = '\n';                    /* fake nl before EOF */
            }
        }
        else if ((ch == '\n' || ch == '\r') && !pp_instring && !inputfromtty)
        {   int nextch = getc(cis);               /* This read-ahead is */
            if ((ch + nextch) == ('\r' + '\n'))   /* tough on cc -S -   */
                s[n-1] = '\n';                    /* if the following   */
            else ungetc(nextch, cis);             /* ungetc() happens.. */
        }
    }

#ifndef NO_LISTING_OUTPUT
    /* The following predicate is now once/line, rather than once/char. */
    if (listingstream &&
        (n > 0) &&                                        /* => NOT EOF */
        !(pp_filenumber & 0x80000000) &&
        HasFeature(Feature_UnexpandedListing))
    {   fwrite(s, 1, (size_t)n, listingstream);
        /* we may be listing part of a line, so care with \n condition. */
        if (s[n-1] == '\n')
        {   listing_diagnostics();
            if (profile_count) listing_nextline(pp_fl->l);
            fprintf(listingstream, "%6u  ", pp_fl->l+1);
        }
    }
#endif /* NO_LISTING_OUTPUT */

    if (n == 0)
    {   pp_rdcnt = 0;
        pp_rdptr = NULL;
        return PP_EOF;
    }
    else
    {   pp_rdcnt = n-1;
        pp_rdptr = s+1;
        return (*s &0xff);
    }
}

static int pp_translate_1(int ch)
{
/* Translate COMMENT_START, '\n', ANSI tri-glyphs and \<nl>. Note that */
/* \<nl> can't occur in a tri-glyph, but ?? / can occur before \n...   */
#ifdef PASCAL
    if (ch == '{')
        return ch;
#endif
    if (ch == COMMENT_START)
        return ch;
    if (ch == '\n')
    {   ++pp_fl->l;
        pp_fl->filepos += (int32) pp_fl->column;
        pp_fl->column = 1;
        if (pp_rdch1nls > 0)        /* return a \n saved up from \<nl> */
        {   --pp_rdch1nls;          /* one less to return next time... */
            ++pp_rdcnt;             /* and unget the pending '\n'...   */
            --pp_rdptr;
        }
        return ch;
    }
#ifndef PASCAL
    else if (ch == '?')                     /* possible triglyph alert */
    {   int32 n = pp_rdcnt;                 /* NB - only in ANSI mode. */
        char *s = pp_rdptr;
        if (n == 0 || n == 1 && s[0] == '?')
        {   if (n == 0) ++pp_rdcnt;         /* Seen '?' - copy to buffer */
            pp_fillbuf();                   /* skip 1st char of buffer   */
            if (n == 1)                     /* Seen ?? - point to second */
            {   ++pp_rdcnt;  --pp_rdptr;    /* '?'... either way, end up */
            }                               /* pointing at 'x' of ?x...  */
            n = pp_rdcnt;
            if (n < 2) return '?';
            s = pp_rdptr;
        }
        if (s[0] != '?') return '?';
/* If we really wanted to compile this code in an environment where    */
/* 7 bit ascii chars were not available, then we have have to change   */
/* the following character constants to their trigraph form too.       */
        switch(s[1])
        {
default:    return '?';
case '=':   ch = '#';   break;
case '(':   ch = '[';   break;
case '/':   ch = '\\';  break;
case ')':   ch = ']';   break;
case '\'':  ch = '^';   break;
case '<':   ch = '{';   break;
case '!':   ch = '|';   break;
case '>':   ch = '}';   break;
case '-':   ch = '~';   break;
        }
        pp_rdcnt = n - 2;
        pp_rdptr = s + 2;
        pp_fl->column += 2;
        if (pp_incomment == NO_COMMENT)
          cc_warn(pp_warn_triglyph,(int)'?', (int)'?', (int)s[1], (int)ch);
        if (ch != '\\') return ch;
        /* else ch == '\\' so drop through in case next char is '\n' */
    }
    if (ch == '\\')
    {   int32 n = pp_rdcnt;
        if (n == 0)
        {   ++pp_rdcnt;
            pp_fillbuf();
            n = pp_rdcnt;
            if (n == 0) return '\\';
        }
        if (pp_rdptr[0] != '\n') return '\\';
        if (pp_incomment == EOL_COMMENT)
          cc_warn(pp_warn_continued_comment);
        ++pp_rdptr;
        pp_rdcnt = n - 1;
        ++pp_rdch1nls;
        return PP_EOF;
    }
#endif
    /* In -pcc mode, can get here with ch == PP_TOKSEP - should not fault.  */
    /* Otherwise, this function never gets called in -pcc mode (see pp_init */
    /* and how it sets pp_translate[] for an explanation).                  */
    if (!HasFeature(Feature_PCC))
    {
        if (pp_incomment != NO_COMMENT) cc_warn(pp_rerr_nonprint_char, ch);
        else
        {   cc_rerr(pp_rerr_nonprint_char, ch);
            return PP_EOF;
        }
    }
    return ch;
}

static int pp_rdch1(void)
{   int ch, trch;
/* This function embodies much critical per-character overhead so we work    */
/* hard to make it fast in the common cases, even at the cost of making      */
/* uncommon cases (such as '\n', '?', '\\' and EOF) slower. The idea is that */
/* exception (PP_TOKSEP) entries in a translate table flag complex cases.    */
    for (;;)
    {   if (--pp_rdcnt >= 0)
        {   ch = *pp_rdptr++;
            ++pp_fl->column;
        }
        else
        {   ch = pp_fillbuf();
            if (ch == PP_EOF) return ch;
        }
        if ((trch = pp_translation(ch)) != PP_TOKSEP) return trch;
        /* In -pcc mode, we only get here if ch == PP_TOKSEP, literally.    */
        trch = pp_translate_1(ch);
        if (trch != PP_EOF) return trch;
    }
}

static int pp_comment(int ch)
/* After recognising a comment start, this function is called to read the   */
/* remainder of it. We do this to save per-character overhead in pp_rdch(), */
/* which is, otherwise, burdened with this monster's procedure prologue...  */
{   int comment_nest = 1;
    if (HasFeature(Feature_PPComment))
    {   /* Assert: ch == '{' || ch == '*' */
        /* N.B. output to stdout BY DEFINITION of cc -C. Similarly below */
        if (ch != '{') putc(COMMENT_START, stdout);
        putc(ch, stdout);
    }
    pp_incomment = BALANCED_COMMENT;
    ch = pp_rdch1();
    for (;;)
    {   if (ch != PP_EOF && HasFeature(Feature_PPComment)) putc(ch, stdout);
        switch (ch)
        {   case PP_EOF: cc_err(pp_err_eof_comment); return PP_EOF;
            case '\n':
                if (!HasFeature(Feature_PPComment)) ++pp_rdch3nls;
                break;
            default:
                break;
#ifdef PASCAL
            case '}':
            case '{':
                if (ch == '{')
                {
                    cc_warn(pp_warn_nested_comment);
                } else {
                    --comment_nest;
                    if (comment_nest == 0) {
                        if (HasFeature(Feature_PPComment)) putc(ch, stdout);
                        return ' ';
                    }
                }
                break;
#endif
            case COMMENT_START:
                ch = pp_rdch1();
                if (ch == '*')
                {
                    if (!HasFeature(Feature_PCC))
                        cc_warn(pp_warn_nested_comment, "/*");
                }
                continue;
            case '*':
                ch = pp_rdch1();
                if (ch == COMMENT_END) --comment_nest;
                if (comment_nest == 0)
                {
                    if (HasFeature(Feature_PPComment)) putc(ch, stdout);
                    if (HasFeature(Feature_PCC) || HasFeature(Feature_PPComment))
                        return PP_TOKSEP;      /* comments vanish but have */
                    else                       /* separating value...      */
                        return ' ';            /* comments -> single space */
                }
                continue;
        }
        ch = pp_rdch1();
    }
    pp_incomment = NO_COMMENT;
}

/*
 * pp_rdch() selects the next character from one of two buffers (during
 * macro expansion) or reads the next character from the input stream
 * (notionally pp_rdch1()). If it takes a character from the input stream,
 * its job is also to reduce comments to single spaces (ANSI) or PP_TOKSEP
 * (pcc mode). This is the most critical function called once per character
 * and its implementation is slightly twisted to save cycles.
 */

static int pp_rdch_la = 0;

static int pp_rdch(void)
{   int ch, trch;
    if ((ch = pp_rdch_la) != 0)
    {   pp_rdch_la = 0;
        return ch;
    }
/* AM: perform special case code if we are rescanning:                  */
    if (!(pp_scanidx < 0 && pp_ebufptr==pp_ebuftop))
    {   PP_HASHENTRY *p;
/* AM: note that we rely on PP_TOKSEP at end of expansions to stop      */
/* read-ahead for more isalnum's reading via pp_rdch() and so           */
/* defeating recursion trapping in #define f f.                         */
/* Note pp_unchain/pp_sleepleft comment re stack nature of sleep.       */
        if (pp_noexpand)
        {   /* move following code to pp_subsleep? Beware pp_argexpand().  */
            while (pp_noexpand && pp_sleepleft_(pp_noexpand) <= 0)
            {   p = pp_noexpand;
                pp_noexpand = pp_unchain_(p), pp_unchain_(p) = 0;
                pp_hashalive_(p) = 1;
            }
            pp_subsleep(1);
        }
        return (pp_scanidx >= 0) ? pp_abufbase[pp_scanidx++] : *pp_ebufptr++;
    }
    /* pp_noexpand is notionally 0 here -- insert syserr() soon?        */
    /* For the time being leave the nice safe code:                     */
    if (pp_noexpand) pp_awaken_all();
/* And now we drop through into the remnants of pp_rdch3()...            */
    if (pp_rdch3nls > 0 && !pp_in_directive)
    {   /* output saved nls from within comments, but wait until end    */
        /* of '#' directive before doing so.                            */
        --pp_rdch3nls;
        return '\n';
    }
    if (pp_rdcnt > 0)
/* The usual case - the line buffer is non-empty... */
    {   ch = *pp_rdptr;
        if ((trch = pp_translation(ch)) != PP_TOKSEP)
/* The usual case of a non-exceptional character, so take the short cut. */
/* (i.e. not '\n', '\\', COMMENT_START, EOF, or, in ANSI mode, '?').     */
        {   ++pp_rdptr;
            --pp_rdcnt;
            ++pp_fl->column;
            return trch;
        }
    }
    ch = pp_rdch1();
    /* In ANSI mode, the following code is never executed: PP_TOKSEP and */
    /* PP_NOEXPAND have been mapped to '\n' and PP_ESC has been faulted  */
    /* and ignored. In -pcc mode, the literal chars are mapped to escape */
    /* sequences and later mapped back by pp_process().                  */
    if (ch == PP_ESC || ch == PP_TOKSEP || ch == PP_NOEXPAND)
    {   pp_rdch_la = ch == PP_ESC ? PP_ESC : ch == PP_TOKSEP ? ' ' : '\t';
        return PP_ESC;
    }
    if ((ch != COMMENT_START
#ifdef PASCAL
         && ch != '{'
#endif
         ) || pp_instring) return ch;
#ifdef PASCAL
    if (ch != '{')
#endif
    {   ch = pp_rdch1();
        if (LanguageIsCPlusPlus || !HasFeature(Feature_Fussy))
            if (ch == '/')
            {   pp_incomment = EOL_COMMENT;
                if (HasFeature(Feature_PPComment))
                { putc('/', stdout); putc(ch, stdout); }
                for (;;)
                    {   if ((ch = pp_rdch1()) == '\n' || ch == PP_EOF)
                        {   pp_incomment = NO_COMMENT;
                            if (HasFeature(Feature_PPComment) && ch == '\n')
                                putc(ch, stdout);
                            return ch;
                        }
                        else if (HasFeature(Feature_PPComment)) putc(ch, stdout);
                    }
            }
            if (ch != '*')             /* unget ch... */
            {   ++pp_rdcnt;            /* which is    */
                --pp_rdptr;            /* always safe */
                --pp_fl->column;
                if (ch == '\n')
                    --pp_fl->l; /* pp_fl->column is zero but not for long */
                return COMMENT_START;
            }
    }
    return pp_comment(ch);
}

/* Do not call pp_unrdch() more than UNRDCHMAX times.                   */
/* Jun 90: pp_unrdch probably shouldn't write to pp_abufbase[]          */
/* following fix to "fnlikemacro <non lparen>", but leave for now.      */
static void pp_unrdch(int ch)
{   if (ch == PP_EOF);      /* safety when input from file              */
    else if (pp_scanidx > 0)
    {   pp_addsleep(1);  pp_abufbase[--pp_scanidx] = ch;
    }
    else
    {   pp_addsleep(1);  *--pp_ebufptr = ch;
    }
}

static int pp_skipb0(void)
{   int ch;
    do {ch = pp_rdch();} while (ch != PP_EOF && pp_white(ch));
    return ch;
}

static int pp_skipb1(int ch)
{   while (ch != PP_EOF && pp_white(ch)) ch = pp_rdch();
    return ch;
}

/* Note the following (required by ANSI draft of Dec 88) causes the     */
/* text "0xee+getchar()" NOT to expand getchar.                         */
/* The routine pp_number corresponds to ANSI pp-number save that        */
/* the caller has already passed on any leading '.'.  The pp_ch arg     */
/* is presumed to satisfy 'isdigit'.                                    */
/* In PCC mode we allow characters after E+/e- to be expanded (note     */
/*             this allows X to be expanded both in 0xee+X and 3.4e+X). */
static void pp_number(int pp_ch)
{   while (isdigit(pp_ch) || pp_cidchar(pp_ch) || pp_ch == '.')
    {   int c = pp_ch;
        if (!pp_skipping) pp_wrch(pp_ch);
        pp_ch = pp_rdch();
        if ((c == 'e' || c == 'E') && (pp_ch == '+' || pp_ch == '-') &&
                                      !HasFeature(Feature_PCC))
        {   if (!pp_skipping) pp_wrch(pp_ch);
            pp_ch = pp_rdch();
        }
    }
    pp_unrdch(pp_ch);
}

static int32 pp_savnumber(char const *p)
/* p is a buffer holding a number in text form.  Return offset beyond it */
/* and copy into expansion buffer.                                       */
/* Only used from pp_argexpand (and hence in ANSI mode).                 */
{   int32 i = 0;
    int ch = p[i++];
    while (isdigit(ch) || pp_cidchar(ch) || ch == '.')
    {   int c = ch;
        ch = p[i++];
        if ((c == 'e' || c == 'E') && (ch == '+' || ch == '-'))
            ch = p[i++];
    }
    i--;        /* because 'i' is now one beyond first non-digit.       */
    pp_savbuf(p, i);
    return i;
}

#define pp_widestrbeg(a,b) ((a) == 'L' && ((b) == '"' || (b) == '\''))

/* pp_copystring notionally returns type void, but so that things like  */
/*  ... "nonterminated string <nl>#define ..." can be recognised it     */
/* returns a suitable char for pp_process to use as pp_lastch.          */
static int pp_copystring(int quote)
{ int pp_ch;
  pp_instring = 1;
  if (!pp_skipping) pp_wrch(quote);
  while ((pp_ch = pp_rdch()) != quote)
  { switch (pp_ch)
    { case PP_EOF: cc_err(pp_err_eof_string); goto out;
      case '\n': --pp_fl->l; /* correct line numbers in following msgs */
                 if (HasFeature(Feature_PCC))
                     quote = 0;
                 else if (pp_skipping && !HasFeature(Feature_Fussy))
                 {   cc_warn(pp_warn_eol_string_skipped, (int)quote);
                     quote = 0;
                 }
                 else
                     cc_err(pp_err_eol_string, (int)quote);
                 ++pp_fl->l;
                 goto out;
      default: if (!pp_skipping) pp_wrch(pp_ch); break;
#ifndef PASCAL
      case '\\':
        if (!pp_skipping) pp_wrch('\\');
        switch (pp_ch = pp_rdch())
        { case PP_EOF: cc_err(pp_err_eof_escape); goto out;
          case '\n': pp_wrch(pp_ch); break;
          default: if (!pp_skipping) pp_wrch(pp_ch); break;
        }
#endif
    }
  }
out:
  if (!pp_skipping && (quote != 0)) pp_wrch(quote);
  if (pp_ch == '\n') pp_wrch(pp_ch);
  pp_instring = 0;
  return pp_ch;
}

static void pp_stuffstring(int quote, bool dequote, bool discard)
/* dequote = 0: leave quotes alone; dequote = 1: remove " for #include. */
/* For #include we treat \ escapes specially for msdos file specs.      */
/*   [ANSI says escapes in #include/#line are undefined.]               */
/* We arrange that #include both "a:\\foo\\baz" and "a:\foo\baz" work   */
/* by collapsing \\ to \ but \a to \a if dequote == 1.  (Of course,     */
/* things like ...include "abc\<nl>def"... will be glued earlier.)      */
/* For filenames (dequote true) we also discard all whitespace. This is */
/* to be kind to #include <  stdio  .  h  > in case (for instance) it   */
/* has been created via macro-expansion where stray whitespace may be   */
/* hard to control and understand.                                      */
{ int pp_ch; bool err = 0;
  pp_instring = 1;
  if (!dequote & !discard) pp_stuffid_(quote);
  while ((pp_ch = pp_rdch()) != quote)
  { switch (pp_ch)
    { case PP_EOF:
      case '\n': err = 1; goto out;
      default:   if (!discard
#ifndef ALLOW_WHITESPACE_IN_FILENAMES
                     && (!dequote || !isspace(pp_ch))
#endif
                    )
                    pp_stuffid_(pp_ch);
                 break;
#ifndef PASCAL /*ECN*/
      case '\\':
        if (!discard) pp_stuffid_('\\');
        switch (pp_ch = pp_rdch())
        { case PP_EOF:
          case '\n': err = 1; goto out;
          case '\\': if (dequote) break;
                     /* drop through */
          default:   if (!discard) pp_stuffid_(pp_ch);
                     break;
        }
#endif
    }
  }
out:
  if (err) pp_unrdch(pp_ch), cc_err(pp_err_missing_quote, (int)quote);
  if (!dequote && !discard) pp_stuffid_(quote);
  pp_instring = 0;
}

static int32 pp_savstring(char const *p)
/* p is a buffer holding a string in text form.  Copy into expansion    */
/* buffer and return length copied.                                     */
{   int quote = *p;
    int32 i = 0;
    for (;;)
    { int ch = p[++i];
      if (ch == quote) { ++i; break; }
      if (ch == 0) break;                           /* really malformed */
#ifndef PASCAL
      if (ch == '\\') if (p[++i] == 0) break;       /* really malformed */
#endif
    }
    pp_savbuf(p, i);
    return i;
}


static bool pp_eqname(char const *s, char const *v, int32 n)
                 /* like strcmp but 2nd arg is base/length format */
{ while (n-- > 0) if (*s++ != *v++) return 0;
  if (*s != 0) return 0;
  return 1;
}

static char *pp_special(int32 n, char *s)
{   switch (n)
    {   default:       syserr(syserr_pp_special, (long)n);
                       return "";
        case PP__LINE: sprintf(s, "%d", pp_fl->l);
                       return s;
        case PP__FILE: /* double '\' from msdos file names for lex.c:   */
                       /* escape '"' to '\"' to keep sane too.          */
                       /* notionally: sprintf(s, "\"%s\"", pp_fl->f);    */
            {   char *p = s; char const *q = pp_fl->f; int ch;
                *p++ = '\"';
                while ((ch = *q++) != 0)
                {   if (ch == '\\' || ch == '"') *p++ = '\\';
                    *p++ = ch;
                }
                *p++ = '\"';
                *p++ = 0;
                return s;
            }
/* see the spec of asctime for the following numbers */
        case PP__DATE: sprintf(s, "\"%.7s%.4s\"",
                               pp_datetime+4, pp_datetime+20);
                       return s;
        case PP__TIME: sprintf(s, "\"%.8s\"", pp_datetime+11);
                       return s;
        case PP__ZERO: return "0";
        case PP__ONE:  return "1";
    }
}

/* Some re-ordering of routines desirable... */
static bool pp_checkid(int ch);
static PP_ARGENTRY *pp_findarg(PP_ARGENTRY *a, char const *id, int32 n);

#ifdef ENABLE_PP
static void pp_show_buffers(char const *msg)
{
  char *s;
  cc_msg("%s: %*s(ebuf = '", msg, (int)pp_expand_level*2, "");
  for (s = pp_ebufbase+PP_UNRDCHMAX; s != pp_ebufptr; ++s) cc_msg("%c", *s);
  cc_msg("!");
  for (;s != pp_ebuftop;  ++s) cc_msg("%c", *s);
  cc_msg("', abuf = '");
  for (s = pp_abufbase;  s != pp_abufptr; ++s) cc_msg("%c", *s);
  cc_msg("')\n");
}
#else
#define pp_show_buffers(x)
#endif

static void pp_argexpand(int32 ap)
{
  /* arg (ap) is an offset into abuf, pp_scanidx>=0 iff rescanning.     */
  /* result is put into ebuf.                                           */
  /* AM: (ANSI ambiguity) it is not clear whether expansion should be   */
  /* depth-first or breadth-first: consider a(b) where a=f b=) f(x)=3.  */
  /* We now do depth-first to match top-level.                          */
  /* N.b. there is scope for re-organising buffer (ap) reuse.           */
  int32 scanidx = pp_scanidx;
  int32 doneseg = 0;
  for (;;)      /* retry until no more macros expand.                   */
  { int32 sav_ebuftop = pp_ebuftop - pp_ebufbase;
    int32 sav_abufptr = pp_abufptr - pp_abufbase;
    int32 apsleepbase = ap + doneseg;
    if (debugging(DEBUG_PP))
       cc_msg("pp_argexpand('%s'+%lu) %lu ", pp_abufbase+ap, doneseg, ap),
       pp_showsleep(),
       cc_msg("\n");
    /* copy previously substituted text in arg: */
    if (doneseg != 0)           /* test technically spurious            */
    {   pp_savbuf(pp_abufbase+ap, doneseg), ap += doneseg;
    }
/* copy tokens literally, but stopping after first substitution:        */
/* @@@ nastiness: the direct use of pp_abufbase[] instead of pp_rdch()  */
/* is an efficiency hack beyond its sense.  It causes the miserable     */
/* pp_subsleep(...apsleepbase...) calls.                                */
    for (;;)
    { int ch = pp_abufbase[ap];
      if (ch == PP_EOM)         /* no expansions this time round.       */
      { pp_subsleep(ap-apsleepbase);    /* OK, but ignored by caller.   */
        pp_abufptr = pp_abufbase + sav_abufptr;
        pp_scanidx = scanidx;
        return;
      }
      else if (pp_macstart(ch) || ch == PP_NOEXPAND)
      { bool changes;
        doneseg = (pp_ebuftop - pp_ebufbase) - sav_ebuftop;
        pp_subsleep(ap+1 - apsleepbase);
        pp_scanidx = ap+1;  changes = pp_checkid(ch);  ap = pp_scanidx;
        apsleepbase = ap;
        /* copy chars after any macro substitution and rescan.          */
        if (changes)
        {   int32 n = strlen(pp_abufbase+ap);
            pp_savbuf(pp_abufbase+ap, n+1);
            break;
        }
      }
      else if (isdigit(ch)) ap += pp_savnumber(pp_abufbase+ap);
      else if (ch == '"' || ch == '\'') ap += pp_savstring(pp_abufbase+ap);
      else pp_savch(ch), ++ap;
    }
    pp_abufptr = pp_abufbase + sav_abufptr;
/* reset 'ap' to result of ebuf expansion and repeat.                   */
    ap = pp_abufptr - pp_abufbase;
    pp_wrbuf(pp_ebufbase + sav_ebuftop,
             pp_ebuftop - (pp_ebufbase + sav_ebuftop));
    pp_ebuftop = pp_ebufbase + sav_ebuftop;
    pp_wrch(PP_EOM);
  }
}

/* pp_expand expands a macro whose args are in abuf into ebuf.          */
static void pp_expand(PP_HASHENTRY *p, int32 nlsinargs)
{ int dch;
  int hashflag = 0;             /* always 0 in PCC mode.                */
  int in_string = 0;            /* always 0 in ANSI mode                */
  char const *dp; char specialbuf[256];
  int32 aftercallchars = pp_ebuftop-pp_ebufptr;
/* n.b. at top level (scanidx==-1), aftercall chars are the '+asd'      */
/* caused after expanding f with #define f x+asd; #define x <whatever>. */
/* When in pp_argexpand this can include both pre- and post- call chars */
  int32 sav_abufptr = pp_abufptr-pp_abufbase;  /* aftercallchars' home  */
  pp_hashuses_(p)++;
  if (debugging(DEBUG_PP))
  { if (aftercallchars != 0)
        cc_msg("aftercallchars(idx %ld) = '%.*s' at %d\n",
               (long)pp_scanidx, (int)aftercallchars, pp_ebufptr,
               pp_ebufptr-pp_ebufbase);
  }

  if (pp_scanidx < 0)
  { /* first copy stuff in ebuf after the macro call to after last actual */
    pp_wrbuf(pp_ebufptr, aftercallchars);
    pp_ebufptr = pp_ebuftop = pp_ebufbase + PP_UNRDCHMAX;
  }
  dp = pp_hashismagic_(p) ? pp_special(pp_hashmagic_(p), specialbuf)
                          : pp_hashbody_(p);
#ifdef ENABLE_PP                /* spurious: deadcode elimination fixes */
  if (debugging(DEBUG_PP))
  { cc_msg("pp_expand(%s) = '%s'\n", pp_hashname_(p), dp);
    pp_show_buffers("e1");
  }
  ++pp_expand_level;
#endif
  if (!HasFeature(Feature_PCC)) pp_savch(PP_TOKSEP);    /* no glueing   */
  while ((dch = *dp) != 0) switch (dch)
  {
    case '%':
        if (HasFeature(Feature_PCC) || dp[1] != ':')
          goto defaultcase;
        if (dp[2] == '%' && dp[3] == ':') {
          hashflag |= 2;
          dp += 4;
        } else if (pp_hashnoargs_(p)) {
          goto defaultcase;
        } else {
          hashflag |= 1;
          dp += 2;
        }
        while (*dp == ' ') dp++;    /* whitespace ANSI normalised.  */
        break;
    case '#':
        if (HasFeature(Feature_PCC) ||
            (pp_hashnoargs_(p) && dp[1] != '#'))
            goto defaultcase;
        /* no '#' operators in pcc-mode macro-expansion... */
        /* or inside non-function macros */

        /* consider cases like f(a,b) == a ## # b.       */
        ++dp;
        if (*dp == '#') {hashflag |= 2; ++dp;} else hashflag |= 1;
        while (*dp == ' ') dp++;    /* whitespace ANSI normalised.  */
        break;
    case '\'':
    case '"':
        if (!HasFeature(Feature_PCC))
        { dp += pp_savstring(dp);
          hashflag = 0;
          break;
        }
        if (dch == in_string && dp[-1] != '\\')
            in_string = 0;
        else if (in_string == 0)
            in_string = dch;
        /* if in pcc mode then fall through to default case */
    defaultcase:
    default:
        if (pp_macstart(dch))
        { int32 i = 0;
          PP_ARGENTRY *a;
          do i++, dp++; while (pp_cidchar(*dp));
          a = pp_hashnoargs_(p) ? 0 :
                  pp_findarg(pp_hasharglist_(p), dp-i, i);
          if (hashflag == 0 &&  /* not # or ## prefixed, maybe suffixed */
              !HasFeature(Feature_PCC))
          { char const *s = dp;
            while (*s == ' ') ++s;      /* whitespace ANSI normalised.  */
            if ((s[0] == '#' && s[1] == '#')
                || (s[0] == '%' && s[1] == ':' && s[2] == '%' && s[3] == ':'))
              hashflag = 2;
          }
          if (hashflag & 1) pp_savch('"');
          if (a == 0) pp_savbuf(dp-i, i);               /* not an arg   */
          else
          { /* an arg 'a' to include/expand */
            int32 ap = pp_argactual_(a);
            if (in_string)
            {   cc_warn(pp_warn_macro_arg_exp_in_string,
                    pp_argname_(a), pp_hashname_(p), in_string, in_string);
            }
            if (hashflag == 0 && !HasFeature(Feature_PCC))
            { PP_HASHENTRY *oldsleepers = pp_noexpand;
              pp_noexpand = 0;
              pp_savch(PP_TOKSEP);                      /* no glueing   */
              pp_argexpand(ap);
              pp_savch(PP_TOKSEP);                      /* no glueing   */
              pp_awaken_all();
              pp_noexpand = oldsleepers;
              if (debugging(DEBUG_PP))
              { cc_msg("pp_argexpanded(%s)\n", pp_abufbase+ap);
                pp_show_buffers("r1");
              }
            }
            else
            { int ch, lastch = 0, in_string = 0;
              while ((ch = pp_abufbase[ap++]) != 0)     /* PP_EOM       */
              { if (!in_string)
                {   if (ch == '"' || ch == '\'') in_string = ch;
                }
                else if (lastch != '\\' && ch == in_string)
                    in_string = 256;
                if ((hashflag & 1) && in_string && (ch == '"' || ch == '\\'))
                    /* Note hashflag == 0 in PCC mode.                  */
                    /* When stringising escape '"' and '\' so that      */
                    /* stringise('\"') and stringise(\) work.           */
                    pp_savch('\\');
/* @@@ bug: next line is wrong removing all PP_NOEXPAND: see file head. */
                if (!(hashflag & 2 && ch == PP_NOEXPAND ||
                      hashflag & 1 && ch == PP_TOKSEP)) pp_savch(ch);
                lastch = ch;
                if (in_string == 256) in_string = 0;
              }
            }
          }
          if (hashflag & 1) pp_savch('"');
        }
        else        /* i.e. any char but "'# */
        { /* note: dch cannot be PP_TOKSEP in ANSI mode.                */
          if (dch != PP_TOKSEP) pp_savch(*dp);
          ++dp;
        }
        /* The next line rests on ANSI whitespace normalisation.        */
        if (dp[0] == ' ' &&
            ((dp[1] == '#' && dp[2] == '#') ||
             (dp[1] == '%' && dp[2] == ':' && dp[3] == '%' && dp[4] == ':')) &&
            !HasFeature(Feature_PCC)) dp++;
        hashflag = 0;
        break;
  }
  if (!HasFeature(Feature_PCC)) pp_savch(PP_TOKSEP);    /* no glueing   */
  if (!pp_hashnoargs_(p))
  { PP_ARGENTRY *a;
    for (a = pp_hasharglist_(p); a != 0; a = pp_argchain_(a))
    { int32 i = pp_argactual_(a);
      pp_argactual_(a) = *((int32 *)(pp_abufbase+i-sizeof(int32)));
    }
  }
  if (pp_scanidx < 0)
  {
    while (nlsinargs-- > 0) pp_savch('\n');  /* save up the NL's in args */
    if (!HasFeature(Feature_PCC))
        /* suppress recursive invocations in ANSI mode -- PCC loops!    */
        pp_sleep_name(p, pp_ebuftop - (pp_ebufbase + PP_UNRDCHMAX));
    if (debugging(DEBUG_PP))
        cc_msg("restore aftercall(%.*s)\n",
               (int)aftercallchars, pp_abufbase+sav_abufptr);
    pp_savbuf(pp_abufbase+sav_abufptr, aftercallchars);
    pp_abufptr = pp_abufbase;    /* clear for (top level) rescan */
  }
  else
    if (!HasFeature(Feature_PCC))
        /* suppress recursive invocations in ANSI mode -- PCC loops!    */
        pp_sleep_name(p, pp_ebuftop - (pp_ebufbase + PP_UNRDCHMAX)
                                    - aftercallchars);
  pp_nsubsts++;
#ifdef ENABLE_PP                /* spurious: deadcode elimination fixes */
  --pp_expand_level;
  if (debugging(DEBUG_PP)) pp_show_buffers("e2");
#endif
}

static PP_HASHENTRY *pp_lookup(char const *name, int32 hash)
{   PP_HASHENTRY *p;
    for (p = (*pp_hashtable)[hash % PP_HASHSIZE]; p != 0; p = pp_hashchain_(p))
        if (pp_hashalive_(p) && StrEq(pp_hashname_(p),name)) break;
    return p;
}

static PP_HASHENTRY *pp_lookup_name(char const *name)
{   int32 i = 0, hash = 0;
    for (;;)
    {   int ch = name[i];
        if (!pp_cidchar(ch)) break;
        if (i < PP_DEFLEN) hash = HASH(hash, ch);
        ++i;
    }
    return pp_lookup(name, hash);
}

/* The following routines are just used by pp_checkid:                  */
static void pp_arg_align(void)
{
  while ((IPtr)pp_abufptr & (sizeof(IPtr)-1)) pp_wrch(0);
  pp_abufptr += sizeof(int32);      /* IPtr? */
}

static void pp_arg_link(PP_ARGENTRY *a, int32 arg)
{
  *((int32 *)(pp_abufbase + arg - sizeof(int32))) = pp_argactual_(a);
  pp_argactual_(a) = arg;
}

/* AM Jan 90: These routines hopefully preserve previous PCC behaviour  */
/* but maybe ought to be reviewed as sysV PCC seems to differ.          */
static void pp_trimarg(char *abufarg)
{   while (pp_abufptr != abufarg &&
            (pp_abufptr[-1] == ' ' || pp_abufptr[-1] == PP_TOKSEP))
        pp_abufptr--;   /* trim off trailing spaces/token separators.   */
}

static void pp_spacearg(int ch)
{   /* Adds a space to the end of an argument, but keeps it in normal   */
    /* form (at most one space or PP_TOKSEP at end).                    */
    /* A space takes priority over PP_TOKSEP due to ANSI rules.         */
    /* Caller ensures pp_abufptr[-1] valid.  ch is space or PP_TOKSEP.  */
    if (pp_abufptr[-1] == PP_TOKSEP) pp_abufptr--;
    if (pp_abufptr[-1] != ' ') pp_wrch(ch);
}

static void pp_rd_args(PP_HASHENTRY *p, int32 uselinect)
{ int32 sav_abufptr = pp_abufptr - pp_abufbase;
  PP_ARGENTRY *a = pp_hasharglist_(p);         /* macro with parameters */
  int32 parcnt = 0, arglinect = 0;
  int32 abufarg;   /* now offset into pp_abufbase */
  int ch;
  int lastch = 0;
  pp_arg_align();
  abufarg = pp_abufptr - pp_abufbase;
  for (ch = pp_rdch();;)           /* read args */
  { int thisch = ch;
    switch (ch)
    { case PP_EOM: /* e.g. i(f) where i(x)=x and f=i(.                  */
                /* maybe the following line should pp_unrdch()?         */
                if (pp_scanidx > 0) pp_scanidx--;
      case PP_EOF: cc_err(pp_err_rpar_eof, pp_hashname_(p), (long)uselinect);
                while (parcnt-- > 0) pp_wrch(')');
                goto endofargs;
      case '\n': ++arglinect;
                 if (pp_in_directive && !HasFeature(Feature_PCC))
/* This helps to force a diagnostic in #if f(1,<nl>2) as required by    */
/* the ANSI C standard. Constraint: #if ... occupies only one line.     */
                 {  pp_wrch(ch);
                    break;
                 }
                 if (arglinect == PP_ARGLINES_WARN_VAL)
                     cc_warn(pp_warn_many_arglines, arglinect);
                            /* drop through - treat nl in arg as space  */
      case '\t': ch = ' ';  /* drop through - treat tab in arg as space */
      case ' ': /* Ignore leading or multiple spaces within an arg.     */
                /* (Only visible via ansi stringify (#) so PCC mode ok) */
ansitoksep:     if (pp_abufptr != pp_abufbase+abufarg)
                    pp_spacearg(ch);
                break;
      case '%': if (PP_EOLP(lastch))
                {   ch = pp_rdch();
                    if (ch == ':')
                        cc_warn(pp_warn_directive_in_args);
                    pp_wrch('%');
                    lastch = '%';
                    continue;
                } else
                {   pp_wrch(ch);
                    break;
                }
      case '#': if (PP_EOLP(lastch))
                    cc_warn(pp_warn_directive_in_args);
                /* drop through to default case */
      default:  /* NB: we do not need to use pp_number here.            */
                if (ch == PP_TOKSEP)
                {   if (!HasFeature(Feature_PCC)) goto ansitoksep;
                    /* else for PCC ignore PP_TOKSEP in args.  Why?     */
                }
                else pp_wrch(ch);
                break;
      case '\'':
      case '"': (void)pp_copystring(ch); break;
      case '(': parcnt++; pp_wrch(ch); break;
      case ',': if (parcnt > 0) { pp_wrch(ch); break; }
                pp_trimarg(pp_abufbase+abufarg);
                pp_wrch(0);
                if (a != 0) pp_arg_link(a, abufarg),
                            pp_arg_align(),
                            abufarg = pp_abufptr - pp_abufbase,
                            a = pp_argchain_(a);
                if (a == 0)
                { cc_err(pp_err_many_args, pp_hashname_(p), (long)uselinect);
                  pp_abufptr = pp_abufbase + sav_abufptr;
                  return;
                }
                break;
      case ')': if (parcnt-- > 0) { pp_wrch(ch); break; }
      endofargs:
                pp_trimarg(pp_abufbase+abufarg);
                if (a == 0 && pp_abufptr != pp_abufbase+abufarg)
                {   /* no tokens allowed as arg in calls of #define f() ... */
                    cc_err(pp_err_many_args, pp_hashname_(p), (long)uselinect);
                    pp_abufptr = pp_abufbase + sav_abufptr;
                }
                pp_wrch(0);
                if (a != 0) pp_arg_link(a, abufarg),
                            a = pp_argchain_(a);
                if (a != 0)
                { cc_err(pp_err_few_args, pp_hashname_(p), (long)uselinect);
                    while (a != 0)
                    {   /* default missing arguments to "" */
                        pp_arg_align();
                        abufarg = pp_abufptr - pp_abufbase;
                        pp_wrch(0);
                        pp_arg_link(a, abufarg);
                        a = pp_argchain_(a);
                    }
                }
                return;
    }
    if (thisch == '\n' || ch != ' ') lastch = thisch;
    ch = pp_rdch();
  }
}

/* pp_checkid reads in a source id to see if it is a macro name, either
   outputting it unchanged or expanding it.  BEWARE - reuse of abuf.
   It notionally expands into ebuf, but there is a special case for
   speed (and to inhibit infinitely repeatedly trying to expand)
   for identifiers when the output is to abuf for pp_process().
*/
static bool pp_checkid(int pp_ch)
{ PP_HASHENTRY *p;
  int32 i = 0, hash = 0;
  int32 uselinect;
  int whitech;
  bool noexpandflag = 0;
/* @@@ currently pp_checkid() removes all PP_NOEXPAND chars, and adds   */
/* them again if we are argexpanding.  Is this what we want?            */
  if (pp_ch == PP_NOEXPAND)
    noexpandflag = 1,
    pp_ch = pp_rdch();  /* @@@ do/while below optimistic/buggy! */

  pp_abuf_ensure(PP_DEFLEN+1);
  do { if (i<PP_DEFLEN)
       { hash = HASH(hash, pp_ch);
         pp_abufptr[i++] = pp_ch;
       }
       do pp_ch = pp_rdch(); while (pp_ch == PP_NOEXPAND);
     } while pp_cidchar(pp_ch);
  pp_abufptr[i] = 0;
#ifdef ENABLE_PP                /* spurious: deadcode elimination fixes */
  if (debugging(DEBUG_PP))
    cc_msg("pp_checkid(%s%s)", pp_abufptr, noexpandflag ? "/noexpand":""),
       pp_showsleep(),
       cc_msg("\n");
#endif
  if (i == 1 && pp_widestrbeg(pp_abufptr[0], pp_ch) &&
      !HasFeature(Feature_PCC)) noexpandflag = 1;
  p = noexpandflag ? NULL : pp_lookup(pp_abufptr, hash);
  if (p == NULL)
  { if (!(pp_inhashif && StrEq("defined",pp_abufptr)))
    { if (pp_scanidx < 0)
          /* The following line is notionally pp_wrbuf() but is so      */
          /* written for efficiency (main loop).                        */
          pp_abufptr += i;              /* leave chars in output buffer */
      else
      {   /* the following line looks a little odd, but currently       */
          /* we put a NOEXPAND quote around every id not expanded as    */
          /* part of a macro-arg so that IF it was suppressed then it   */
          /* will not get expanded for the body rescan of an outermore  */
          /* macro.  See comment at top of file.                        */
          pp_savch(PP_NOEXPAND);
          pp_savbuf(pp_abufptr, i);
      }
      pp_unrdch(pp_ch);
    }
    else                   /* poxy "defined id" or "defined(id)" in #if */
    { bool parens = 0;
      pp_ch = pp_skipb1(pp_ch);
      if (pp_ch == '(') { parens = 1; pp_ch = pp_skipb0(); }
      if (!pp_macstart(pp_ch)) cc_err(pp_err_if_defined);
      else
      { i = 0, hash = 0;
        pp_abuf_ensure(PP_DEFLEN+1);
        do { if (i<PP_DEFLEN)
                 hash = HASH(hash, pp_ch), pp_abufptr[i++] = pp_ch;
             pp_ch = pp_rdch();
           } while pp_cidchar(pp_ch);
        pp_abufptr[i] = 0;
        p = pp_lookup(pp_abufptr, hash);
        if (parens)
        { pp_ch = pp_skipb1(pp_ch);
          if (pp_ch == ')'); /* nothing to do */
          else cc_err(pp_err_if_defined1);
        }
        else pp_unrdch(pp_ch);
      }
      pp_expand(p != 0 ? pp_hashone : pp_hashzero, 0);
    }
    return 0;
  }
  if (pp_hashnoargs_(p))           /* macro with no parameters */
  { pp_unrdch(pp_ch);
    pp_expand(p,0);
    return 1;
  }
  uselinect = pp_fl->l;
/* AM, Jun 90: ensure ensure whitech sufficiently accurate so that      */
/* calls to unrdch() work when pp_argexpanding.                         */
  whitech = 0;
  if (pp_white(pp_ch)) whitech = pp_ch, pp_ch = pp_skipb0();
/* We have to be rather careful here with fn-like macros with no        */
/* following parens, especially since they may be followed by a #-line. */
/* The draft isn't especially clear, but since '(' is required to be    */
/* the next pp-token if it is present the draft seems unambiguous.      */
/* Consider examples like "f(getchar <nl>#whatever <nl> )".             */
/* Note the related "f(getchar( <nl>#whatever <nl> ))" is undefined.    */
  if (!pp_in_directive)
      while (pp_ch == '\n') whitech = '\n', pp_ch = pp_skipb0();
  if (pp_ch != '(')                /* ANSI says ignore if no '(' present */
  { if (debugging(DEBUG_PP))
        cc_msg("pp_checkid(%s%c/%.2x not '(')\n", pp_abufptr, pp_ch, pp_ch);
    if (pp_scanidx < 0)
        pp_abufptr += i;                /* leave chars in output buffer */
    else
        pp_savbuf(pp_abufptr, i);
    pp_unrdch(pp_ch);                   /* hence PP_UNRDCHMAX>=2        */
    if (whitech) pp_unrdch(whitech);    /* don't lose poss. whitespace  */
    return 0;
  }
  else
  { /* @@@ later improve store efficiency by save/restore of pp_abufptr */
    pp_rd_args(p, uselinect);
    pp_expand(p, pp_fl->l-uselinect);
    return 1;
  }
}

static PP_ARGENTRY *pp_addtoarglist(char *id, PP_ARGENTRY *a);

static PP_HASHENTRY *pp_predefine2(char const *s, int n)
{ PP_HASHENTRY *p;
  int32 i = 0, hash = 0;
  int ch;
  while (ch = *s++, n<0 ? ch!=0 : pp_cidchar(ch))
     { if (i<PP_DEFLEN)
       { hash = HASH(hash, ch);
         pp_stuffid_(ch);
       }
     }
  { char *name = pp_closeid();
    if (ch != '(')
      p = (PP_HASHENTRY *) pp_new_(PP_NOARGHASHENTRY), pp_hashnoargs_(p) = 1;
    else
    { char const *sarg = s;
      int32 params = 0;
      p = (PP_HASHENTRY *) pp_new_(sizeof(PP_HASHENTRY));
      pp_hashnoargs_(p) = 0;
      pp_hasharglist_(p) = 0;
      do
       { ch = *sarg++;;
         if (!pp_macstart(ch))
         { if (ch == ')' && params == 0) break;
           goto illopt;
         }
         do { pp_stuffid_(ch); ch = *sarg++;
            } while (pp_cidchar(ch));
         pp_hasharglist_(p) =
             pp_addtoarglist(pp_closeid(), pp_hasharglist_(p));
         params++;
       } while (ch == ',');
      if (ch != ')') goto illopt;
      s = sarg;
      ch = *s++;
    }
illopt:
    pp_hashname_(p) = name;
  }
  pp_hashuses_(p) = 0;
  pp_hashalive_(p) = 1;
  pp_hashismagic_(p) = n < 0;
/* @@@ LDS - because of #define __STDC__ 0 chaos, it may be useful to set */
/* pp_noifdef_(p) to 1 for some pre-defines. Should depend on -f?.        */
  pp_noifdef_(p) = 0;
  if (n < 0) pp_hashmagic_(p) = n; else pp_hashbody_(p) = "1";
  pp_hashdefchain_(p) = 0;
  pp_unchain_(p) = 0, pp_sleepleft_(p) = 0;     /* (init only to check) */
  switch (ch)
  {  default:  if (n >= 0)
                   cc_rerr(pp_rerr_illegal_option, pp_hashname_(p), s-1);
               /* drop through */
     case 0:   break;
     case '=': pp_hashbody_(p) = s; break;
  }
  pp_hashchain_(p) = (*pp_hashtable)[hash % PP_HASHSIZE];
  (*pp_hashtable)[hash % PP_HASHSIZE] = p;
  if (pp_hashfirst == 0) pp_hashfirst = pp_hashlast = p;
  else pp_hashdefchain_(pp_hashlast) = p, pp_hashlast = p;
  if (usrdbg(DBG_PP) && !pp_hashismagic_(p)) {
    if (pp_hashnoargs_(p))
      dbg_define(pp_hashname_(p), YES, pp_hashbody_(p), NULL, curlex.fl);
    else
      dbg_define(pp_hashname_(p), NO, pp_hashbody_(p),
                 (dbg_ArgList *)pp_hasharglist_(p), curlex.fl);
  }
  return p;
}

static PP_ARGENTRY *pp_addtoarglist(char *id, PP_ARGENTRY *a)
{   PP_ARGENTRY *p, *q;
    bool seen = 0;
    for ((p = a, q = 0);  p != 0;  (q = p, p = pp_argchain_(p)))
        if (StrEq(pp_argname_(p),id) && !seen)
            seen = 1, cc_rerr(pp_rerr_nonunique_formal, id);
    p = (PP_ARGENTRY *)pp_new_(sizeof(PP_ARGENTRY));
    pp_argchain_(p) = 0;
    pp_argname_(p) = id;
    pp_argactual_(p) = DUFF_OFFSET;
    return q==0 ? p : (pp_argchain_(q) = p, a);
}

static bool pp_eqarglist(PP_ARGENTRY *p, PP_ARGENTRY *q)
{   for (; p && q; p = pp_argchain_(p), q = pp_argchain_(q))
        if (!StrEq(pp_argname_(p), pp_argname_(q))) return 0;
    return (p == q);
}

static PP_ARGENTRY *pp_findarg(PP_ARGENTRY *a, char const *id, int32 n)
{   for (; a; a = pp_argchain_(a))
        if (pp_eqname(pp_argname_(a), id, n)) return a;
    return 0;
}

/* @@@ re-order next routine */
static void pp_skip_linetokens(int pp_ch)
{   for (;;) switch (pp_ch)
    {   case '\n': case PP_EOF: pp_unrdch(pp_ch);
                             return;
        case '\'': case '"': pp_stuffstring(pp_ch,0,1);
                             /* drop through */
        default:             pp_ch = pp_rdch();
                             break;
    }
}

/*
 * One routine per pre-processor command...
 */

static void pp_define(int pp_ch, bool noifdef)
{ int32 i = 0, hash = 0;
  FileLine saved_fl;
  if (usrdbg(DBG_PP)) { saved_fl = *pp_fl; saved_fl.p = dbg_notefileline(saved_fl); }
  if (!pp_macstart(pp_ch))
  { cc_err(pp_err_missing_identifier); pp_skip_linetokens(pp_ch); return; }
  if (pp_skipping)
  {   /* This code is untidy, but corresponds to the ANSI rationale */
      /* that PP only needs to check for the name of a directive.   */
      /* However, improve on this behaviour one day!!!              */
      pp_skip_linetokens(pp_ch);
      return;
  }
  do { if (i<PP_DEFLEN)
       { hash = HASH(hash, pp_ch);
         pp_stuffid_(pp_ch);
         i++;
       }
       pp_ch = pp_rdch();
     } while (pp_cidchar(pp_ch));
  { char *name = pp_closeid();
    PP_HASHENTRY *p;
    PP_ARGENTRY *arglist = 0;
    enum { FIRST_TOKEN, NORMAL, SEEN_HASH, SEEN_HASHHASH } state = FIRST_TOKEN;
    bool feature_comment = HasFeature(Feature_PPComment);
    ClearFeature(Feature_PPComment);
    if (pp_ch != '(')
      p = (PP_HASHENTRY *) pp_new_(PP_NOARGHASHENTRY), pp_hashnoargs_(p) = 1;
    else
    { int32 params = 0;
      p = (PP_HASHENTRY *) pp_new_(sizeof(PP_HASHENTRY));
      pp_hashnoargs_(p) = 0;
      pp_hasharglist_(p) = 0;
      do
       { pp_ch = pp_skipb0();
         if (!pp_macstart(pp_ch))
         { if (pp_ch == ')' && params == 0) break;
           cc_err(pp_err_missing_parameter, name);
           pp_skip_linetokens(pp_ch);
           if (feature_comment) SetFeature(Feature_PPComment);
           return;
         }
         do { pp_stuffid_(pp_ch); pp_ch = pp_rdch();
            } while (pp_cidchar(pp_ch));
         pp_hasharglist_(p) = arglist =
             pp_addtoarglist(pp_closeid(), pp_hasharglist_(p));
         params++;
         pp_ch = pp_skipb1(pp_ch);
       } while (pp_ch == ',');
      if (pp_ch != ')')
      {   cc_err(pp_err_missing_comma, name);
          pp_skip_linetokens(pp_ch);
          if (feature_comment) SetFeature(Feature_PPComment);
          return;
      }
      pp_ch = pp_rdch();
    }
    pp_noifdef_(p) = noifdef;
    pp_hashalive_(p) = 1;
    pp_hashismagic_(p) = 0;
    pp_hashuses_(p) = 0;
    pp_hashdefchain_(p) = 0;
    pp_unchain_(p) = 0, pp_sleepleft_(p) = 0;   /* (init only to check) */
    pp_hashname_(p) = name;
    pp_ch = pp_skipb1(pp_ch);
    for (;;)
    {
/* Turn multiple spaces (or tabs) to one space, lose trailing spaces.   */
/* Initial spaces have already been removed and comments are now space. */
/* Beware warnings for differing white space in pcc-mode (like Reiser?) */
        if ((pp_ch == ' ' || pp_ch == '\t') && !HasFeature(Feature_PCC))
        {        pp_ch = pp_skipb1(pp_ch);
                 if (!(pp_ch == '\n' || pp_ch == PP_EOF)) pp_stuffid_(' ');
        }
        if (state == SEEN_HASH && !pp_macstart(pp_ch))
                 state = NORMAL, cc_rerr(pp_rerr_define_hash_arg);
        switch (pp_ch)
        {
    default:     if (pp_macstart(pp_ch))
                 {   int32 n = 0;
                     do n++, pp_stuffid_(pp_ch), pp_ch = pp_rdch();
                       while (pp_cidchar(pp_ch));
                     if (state == SEEN_HASH &&
                         !pp_findarg(arglist, pp_dbufptr-n, n))
                       cc_rerr(pp_rerr_define_hash_arg);
                     state = NORMAL;
                     continue;
                 }
    defolt:      pp_stuffid_(pp_ch);
                 break;
    case '\'':
    case '"':    pp_stuffstring(pp_ch,0,0);
                 break;

    case '%':    if (HasFeature(Feature_PCC)) goto defolt;
                 pp_ch = pp_rdch();
                 pp_stuffid_('%');
                 if (pp_ch != ':')
                 { state = NORMAL;
                   continue;
                 }
                 pp_stuffid_(':');
                 pp_ch = pp_rdch();
                 if (pp_ch != '%')
                   state = pp_hashnoargs_(p) ? NORMAL : SEEN_HASH;
                 else
                 { pp_ch = pp_rdch();
                   pp_stuffid_('%');
                   if (pp_ch != ':')
                   { cc_rerr(pp_rerr_define_hash_arg);
                     state = NORMAL;
                   } else
                   { if (state == FIRST_TOKEN)
                       cc_rerr(pp_rerr_define_hashhash);
                     pp_stuffid_(':');
                     pp_ch = pp_rdch();
                     state = SEEN_HASHHASH;
                   }
                 }
                 continue;
    case '#':    if (HasFeature(Feature_PCC)) goto defolt;
                 pp_ch = pp_rdch();
                 pp_stuffid_('#');
                 if (pp_ch != '#')
                   state = pp_hashnoargs_(p) ? NORMAL : SEEN_HASH;
                 else
                 { if (state == FIRST_TOKEN)
                       cc_rerr(pp_rerr_define_hashhash);
                   pp_stuffid_('#');
                   pp_ch = pp_rdch();
                   state = SEEN_HASHHASH;
                 }
                 continue;
    case '\n':
    case PP_EOF:
            if (state == SEEN_HASHHASH)
                cc_rerr(pp_rerr_define_hashhash);
            pp_hashbody_(p) = pp_closeid();
            { PP_HASHENTRY *q = pp_lookup(pp_hashname_(p), hash);
              if (q)
              { if (usrdbg(DBG_PP)) dbg_undef(pp_hashname_(q), saved_fl);
                pp_hashalive_(q) = 0;   /* omit for a #define def. stack */
                if (pp_hashismagic_(q)  /* union => must be first test   */
                    || !StrEq(pp_hashbody_(p), pp_hashbody_(q))
                    || pp_hashnoargs_(p) != pp_hashnoargs_(q)
                    || (!pp_hashnoargs_(p) &&
                        !pp_eqarglist(pp_hasharglist_(p),pp_hasharglist_(q))))
                {   if (SuppressDB_Has(Suppress_MPWCompatible))
                      cc_warn(pp_rerr_redefinition, pp_hashname_(p));
                    else
                      cc_pccwarn(pp_rerr_redefinition, pp_hashname_(p));
                }
                else if (HasFeature(Feature_Fussy) || HasFeature(Feature_Predeclare))
                  cc_warn(pp_warn_redefinition, pp_hashname_(p));
              }
            }
            if (usrdbg(DBG_PP))
            { if (pp_hashnoargs_(p))
                dbg_define(pp_hashname_(p), YES, pp_hashbody_(p), NULL, saved_fl);
              else
                dbg_define(pp_hashname_(p), NO, pp_hashbody_(p),
                           (dbg_ArgList *)pp_hasharglist_(p), saved_fl);
            }
            pp_hashchain_(p) = (*pp_hashtable)[hash % PP_HASHSIZE];
            (*pp_hashtable)[hash % PP_HASHSIZE] = p;
            if (pp_hashfirst == 0) pp_hashfirst = pp_hashlast = p;
            else pp_hashdefchain_(pp_hashlast) = p, pp_hashlast = p;
            pp_unrdch(pp_ch);
            if (feature_comment)
                SetFeature(Feature_PPComment);
            return;               /* gasp */
        }
        state = NORMAL;
        pp_ch = pp_rdch();
    }
  }
}

static void pp_undef(int pp_ch)
{ int32 i = 0, hash = 0;
  if (!pp_macstart(pp_ch))
  { cc_err(pp_err_undef); pp_skip_linetokens(pp_ch); return; }
/* Assumption on ABUFSIZE implies  pp_abuf_ensure(PP_DEFLEN+1) OK.      */
  do { if (i<PP_DEFLEN)
       { hash = HASH(hash, pp_ch);
         pp_abufbase[i++] = pp_ch;
       }
       pp_ch = pp_rdch();
     } while (pp_cidchar(pp_ch));
  pp_unrdch(pp_ch);
  pp_abufbase[i++] = 0;
  if (!pp_skipping)
  { PP_HASHENTRY *p = pp_lookup(pp_abufbase, hash);
    if (p) {
      pp_hashalive_(p) = 0;
      if (usrdbg(DBG_PP)) {
        (void)dbg_notefileline(*pp_fl);
        dbg_undef(pp_hashname_(p), *pp_fl);
      }
    }
  }
}

static void pp_addconditional(bool skipelsepart)
{ PP_IFSTACK *q = pp_freeifstack;
  if (q) pp_freeifstack = pp_ifchain_(q);
  else q = (PP_IFSTACK *) pp_new_(sizeof(PP_IFSTACK));
  pp_ifchain_(q) = pp_ifstack;
  pp_ifseenelse_(q) = 0;
  pp_ifoldskip_(q) = pp_skipping;               /* caller pp_skipping */
  pp_ifskipelse_(q) = pp_skipping || skipelsepart;     /* 'else' part */
  pp_ifstack = q;
  pp_skipping = pp_skipping || !skipelsepart;          /* 'then' part */
}

static char *static_copy(const char *s)
{
    return strcpy((char *)pp_alloc(strlen(s)+1L), s);
}

static void pp_h_ifdef(int pp_ch, bool skipelsepart)
{ PP_HASHENTRY *p;
  int32 i = 0, hash = 0;

  if (pp_macstart(pp_ch))
  {
/* Assumption on ABUFSIZE implies  pp_abuf_ensure(PP_DEFLEN+1) OK.      */
      do { if (i<PP_DEFLEN)
           { hash = HASH(hash, pp_ch);
             pp_abufbase[i++] = pp_ch;
           }
           pp_ch = pp_rdch();
         } while (pp_cidchar(pp_ch));
      pp_unrdch(pp_ch);
      pp_abufbase[i++] = 0;
      p = pp_lookup(pp_abufbase, hash);
      if (!skipelsepart &&                  /* #ifndef ...              */
          !seen_pp_token &&                 /* no tokens before #ifndef */
          pp_filestack != 0 &&              /* an included file...      */
          pp_filestack->ifdefname == 0)     /* ifdefname not yet set    */
      {
          pp_filestack->ifdefname = static_copy(pp_abufbase);
          pp_filestack->guard_ifndef = pp_ifstack;
          seen_pp_token = 1;
      }
#ifdef MACH_EXTNS
      if (p != 0 && pp_noifdef_(p))
          cc_warn(pp_warn_ifvaldef, pp_abufbase);
#endif
  }
  else
  {   p = NULL;
      if (HasFeature(Feature_PCC))
          cc_warn(pp_err_ifdef);    /* @@@ is this really suppressible? */
      else
          cc_err(pp_err_ifdef);
      pp_skip_linetokens(pp_ch);
  }
  if (p != 0 && !pp_skipping) pp_hashuses_(p)++;
  pp_addconditional((p != 0) == skipelsepart);
}

static void pp_h_if(int pp_ch)
{   bool b = YES; /* YES/NO is arbitrary */
    if (pp_skipping)
        pp_skip_linetokens(pp_ch);
    else
    {   pp_unrdch(pp_ch);
        pp_inhashif = YES;
        b = syn_hashif();
        pp_inhashif = NO;
    }
    pp_addconditional(b);
    /* Assert: after syn_hashif(), at end of line or at end of file */
}

static void pp_h_else(int pp_ch)
{ if (pp_ifstack == 0 || pp_ifseenelse_(pp_ifstack))
      cc_rerr(pp_rerr_spurious_else);
  else { pp_skipping = pp_ifskipelse_(pp_ifstack);
         pp_ifseenelse_(pp_ifstack) = 1;}
  pp_unrdch(pp_ch);
}

static void pp_h_elif(int pp_ch)
{   if (pp_ifstack == 0 || pp_ifseenelse_(pp_ifstack))
    {   cc_rerr(pp_rerr_spurious_elif);
        pp_skip_linetokens(pp_ch);
    }
    else if (pp_ifskipelse_(pp_ifstack))
    {   pp_skipping = YES;
        pp_skip_linetokens(pp_ch);
    }
    else
    {   bool b;
        pp_unrdch(pp_ch);
        pp_skipping = NO;
        pp_inhashif = YES;
        b = syn_hashif();
        pp_inhashif = NO;
        if (b)
            pp_ifskipelse_(pp_ifstack) = YES;
        else
            pp_skipping = YES;
        /* Assert: after syn_hashif(), at end of line or at end of file */
    }
}

static void pp_h_endif(int pp_ch)
{ if (pp_ifstack == 0) cc_rerr(pp_rerr_spurious_endif);
  else { pp_skipping = pp_ifoldskip_(pp_ifstack);
         { PP_IFSTACK *q = pp_ifchain_(pp_ifstack);
           /* discard old */
           pp_ifchain_(pp_ifstack) = pp_freeifstack,
           pp_freeifstack = pp_ifstack;
           pp_ifstack = q;
           if (pp_filestack != NULL && q == pp_filestack->guard_ifndef)
           { seen_pp_token = 0;          /* reset after matching #endif */
             pp_filestack->guard_ifndef = (PP_IFSTACK *)DUFF_ADDR;
           }                             /* inspect (pp_process) at EOF */
         }
       }
  pp_unrdch(pp_ch);
}

static int pp_directive_expand(int ch)
{   pp_abufptr = pp_abufbase;
    while (pp_macstart(ch))
    {   pp_checkid(ch);
        if (pp_abufptr != pp_abufbase)
        {   /* This means an identifier did not expand (see pp_checkid) */
            /* undo the special treatment in pp_checkid().              */
            pp_abufptr = pp_abufbase;
            return PP_NOEXPAND;         /* sufficient for giving error. */
        }
        ch = pp_skipb0();
    }
    return ch;
}

static void pp_h_line(int pp_ch)
{ if (pp_skipping) { pp_skip_linetokens(pp_ch); return; }
  pp_ch = pp_directive_expand(pp_ch);
  if (isdigit(pp_ch))
  { int n = 0;
    while (isdigit(pp_ch)) n = n*10 + pp_ch-'0', pp_ch = pp_rdch();
    pp_ch = pp_skipb1(pp_ch);
    pp_ch = pp_directive_expand(pp_ch);
    if (pp_ch == '"')
    { pp_stuffstring('"',1,pp_skipping);
      pp_fl->f = pp_closeid();    /* ensure done always */
      pp_ch = pp_directive_expand(pp_skipb0());
    }
    /* Oh dear... this conditional is the price we pay to centralise the */
    /* diagnosis of trailing junk in pp_directive(). Really, that should */
    /* be pulled out of pp_directive and called from each pp_h_thing().  */
    /* See also the "Oh woe" comment at the end of pp_directive().       */
    pp_fl->l = (pp_ch == '\n') ? n : n-1;
    pp_unrdch(pp_ch);
  }
  else
  { cc_rerr(pp_rerr_hash_line);
    pp_skip_linetokens(pp_ch);
  }
}

/* Code in flux -- move typedef to top or merge with pp_filestack?      */
typedef struct file_name_list
{   struct file_name_list *cdr;
    char const *ifdefname;
    bool stringfile;
    char fname[1];
} file_name_list;

static file_name_list *seen_before = NULL;

static int fnameEQ(char const *s, char const *t)
{   int chs, cht;
    for (;;)
    {   chs = *s++;
        cht = *t++;
#ifndef COMPILING_ON_UNIX
        /* host file names are case INsensitive... */
        chs = safe_tolower(chs);
        cht = safe_tolower(cht);
#endif
        if (chs != cht) return 0;
        if (chs == 0) return 1;
    }
}

static void include_only_once(char const *fname, char const *ifdefname, pp_uncompression_record *stringfile)
{   file_name_list *p;

    for (p = seen_before;  p != NULL;  p = p->cdr)
        if (p->stringfile == (stringfile != NULL) && fnameEQ(p->fname, fname))
            return;

    p = (file_name_list *)pp_alloc((int32)offsetof(file_name_list, fname) +
                                   (int32)strlen(fname) + 1);
    p->cdr = seen_before;
    strcpy(p->fname, fname);
    p->ifdefname = ifdefname;
    p->stringfile = (stringfile != NULL);
    seen_before = p;
    if (debugging(DEBUG_FILES))
    {   if (ifdefname == NULL)
            cc_msg("include_only_once '%s'\n", fname);
        else
            cc_msg("file '%s' guarded by '#ifndef %s'\n", fname, ifdefname);
    }
}

void pp_push_include(char const *fname, int lquote, FileLine fl)
{
  FILE *fp;
  int rquote = (lquote == '<' ? '>' : lquote);
  char const *hostname;

  if (lquote == '<' &&
      !(HasFeature(Feature_PCC) || SuppressDB_Has(Suppress_PPNoSysIncludeCheck)))
  {   static char const * const ansiheaders[] = {
            "assert.h", "ctype.h", "errno.h", "float.h", "iso646.h",
            "limits.h", "locale.h", "math.h", "setjmp.h", "signal.h",
            "stdarg.h", "stddef.h", "stdio.h", "stdlib.h", "string.h",
            "time.h"
      };
      bool found = 0;
      unsigned i;
      for (i = 0; i < sizeof(ansiheaders)/sizeof(*ansiheaders); i++)
          if (StrEq(fname, ansiheaders[i]))
          {   found = 1;
              break;
          }
#ifndef TARGET_IS_ALPHA
/*
 * When using some other vendor's header files it is common for
 * (eg) stdio.h to include some other <sys/xxx.h> files, and these
 * cause moans from here. What I really want, I think, is to have
 * this warning disabled if I am already inside some header file
 * that has been picked out of the standard place.  Meanwhile I will
 * put an improper target specific test here to cause Alan or somebody
 * to do something better!   ACN.
 */
      if (!found) cc_warn(pp_warn_nonansi_header, fname);
#endif
  }

/*
 * Here a null name is checked for specially lest sticking bits of a
 * search path onto it lead #include "" into getting treated as (for
 * instance) #include "./", where one could imagine the current directory
 * being opened for reading and the (binary?) junk in it leading to
 * large numbers of odd error messages. If somebody thinks of a good idea
 * for a USEFUL meaning for #include "" or #include <> here is where it
 * could be hooked in.  I probably vote against any such magic!
 */


  { pp_uncompression_record *ur = NULL;
    if (fname[0] != 0 &&
        (fp = pp_inclopen(fname, lquote=='<', &ur, &hostname, fl)) != NULL)
    {
    /* the following block is notionally a recursive call to pp_process()
       but that would mean a co-routine structure if used with the cc. */
      PP_FILESTACK *fs;
      file_name_list *p;
      for (p = seen_before;  p != NULL;  p = p->cdr)
      { if (!fnameEQ(p->fname, hostname)) continue;
        if (p->ifdefname != 0)
        { PP_HASHENTRY *h = pp_lookup_name(p->ifdefname);
          if (h == NULL || !pp_hashalive_(h)) break;
        }
        else if (p->stringfile != (ur != NULL))
          break;
        if (ur == NULL) trackfile_close(fp);
        if (debugging(DEBUG_FILES))
        { if (p->ifdefname == 0)
            cc_msg("Not including '%s' again\n", hostname);
          else
            cc_msg("Not including '%s' again, guard '%s' is #defined\n", hostname, p->ifdefname);
        }
        pp_wrch('\n');
        pp_inclclose(*pp_fl);
        return;
      }
      if (var_cc_private_flags & 0x1000000)
        include_only_once(hostname, NULL, active_string_file);
      fs = pp_freefilestack;
      if (fs != NULL)
        pp_freefilestack = pp_filchain_(fs);
      else
        fs = (PP_FILESTACK *) pp_new_(sizeof(PP_FILESTACK));
      pp_filchain_(fs) = pp_filestack;    pp_filestack = fs;
      pp_filstream_(fs) = pp_cis;         pp_cis = fp;
      pp_fileline_(fs)  = *pp_fl;
      pp_stringfile_(fs) = active_string_file;
      active_string_file = ur;
      init_pp_fl(hostname);
      fs->ifstart = pp_ifstack;
      fs->ifdefname = 0;
      fs->guard_ifndef = (PP_IFSTACK *)DUFF_ADDR;
      seen_pp_token = 0;
#ifndef NO_LISTING_OUTPUT
      pp_filenumber_(fs) = pp_filenumber;
      /* NB profile_find() sets profile_ptr & pp_filenumber */
      pp_propoint_(fs) = profile_ptr; profile_find(fname);
      /* Set MSB of pp_filenumber if listing is not wanted at this level */
      if (!((lquote != '<' && HasFeature(Feature_UserIncludeListing)) ||
            HasFeature(Feature_SysIncludeListing)))
      { pp_filenumber |= 0x80000000;
        list_this_file = 0;
      }
      else list_this_file = 1;
#endif /* NO_LISTING_OUTPUT */
    } else
      cc_err(pp_err_include_file, (int)lquote,fname,(int)rquote);
  }
}

static void pp_include(int pp_ch)
{ /* AM: pp_include() now reads up to and including its terminating NL. */
  int lquote, rquote;
  char *fname;
  FileLine saved_fl;

  if (!pp_skipping) {
    if (usrdbg(DBG_PP)) { saved_fl = *pp_fl; saved_fl.p = dbg_notefileline(saved_fl); }
    pp_ch = pp_directive_expand(pp_ch);
  }

  switch (lquote = pp_ch)
  { case '"': rquote = '"'; break;
    case '<': rquote = '>'; break;
    default:  if (!pp_skipping) cc_err(pp_err_include_quote);
              pp_skip_linetokens(pp_ch);
              return;
  }
  pp_stuffstring(rquote,1,pp_skipping);
  fname = pp_closeid();    /* ensure done always */
  pp_ch = pp_directive_expand(pp_skipb0());
  if (!PP_EOLP(pp_ch) && pp_ch != PP_EOF)
  {
    if (!pp_skipping)
      cc_err(pp_err_include_junk, (int)lquote, fname, (int)rquote);
    pp_skip_linetokens(pp_ch);
    (void)pp_rdch();
  }
  if (pp_skipping)
    pp_wrch('\n');
  else
    pp_push_include(fname, lquote, saved_fl);
}

/* Pragmas: syntax allowed (we can argue more later) is:
 * "#pragma -<letter><optional digit> Argument_List -<letter><optional digit>".
 * The effect of "#pragma -<letter>" is to set pp_pragmavec[letter-a] to -1
 * and "#pragma -<letter><digit>" to set pp_pragmavec[letter-a] to <digit>-0.
 * For the majority of these options a long-winded spelt out word can also
 * be given, as in
 * "#pragma no_warn_deprecated no_warn_implicit_fns"
 * where the particular words that are recognised and their expansions into
 * the more primitive -xn form are given in a table here.
 * (note: does anybody want to change these names? 21 March 89 is ACN's
 *  first bash at such a list and is probably in need of further refinement)
 */

static PragmaSpelling const pragma_words[] =
{
#ifdef FORTRAN
/*
 * The FORTRAN pragmas are treated a bit specially since they represent
 * bits in just two flag words - see where they are set somewhere below
 * for how #pragma auto and #pragma no_auto (say) set and clear the 0x100
 * bit.
 */
    {"double_complex",              'x', 0x1},
    {"hinteger",                    'x', 0x2},
    {"case_fold",                   'x', 0x4},
    {"lc_keywords",                 'x', 0x8},
    {"lc_ids",                      'x', 0x10},
    {"free_format",                 'x', 0x20},
    {"imp_undef",                   'x', 0x40},
    {"recursion",                   'x', 0x80},
    {"auto",                        'x', 0x100},
    {"hollerith",                   'x', 0x200},
    {"top_express",                 'x', 0x400},
    {"f66",                         'x', 0x800},
    {"mixed_common",                'x', 0x1000},
    {"vms_chars",                   'x', 0x2000},
    {"vms_casts",                   'x', 0x4000},
    {"vms_io",                      'x', 0x8000},
    {"vms_types",                   'x', 0x10000},
    {"static_locals",               'x', 0x100000},
    {"all_hinteger",                'x', 0x200000},
    {"all_double",                  'x', 0x400000},
    {"all_undefined",               'x', 0x800000},
    {"check_subscripts",            'x', 0x1000000},
    {"noargalias",                  'x', 0x2000000},
    {"long_lines",                  'x', 0x4000000},
    {"f66_onetrip",                 'w', 1},
    {"f66_iosublist",               'w', 2},
    {"f66_intrinsgo",               'w', 4},
#endif
    { "warn_implicit_fn_decls",     'a', 1},
    { "check_memory_accesses",      'c', 1},
    { "warn_deprecated",            'd', 1},
    { "continue_after_hash_error",  'e', 1},
    { "include_only_once",          'i', 1}, /* @@@ freeze soon!        */
    { "once",                       'i', 1}, /* common with other compilers */
    { "optimise_crossjump",         'j', 1},
#ifdef TARGET_IS_ARM_OR_THUMB
    { "optimise_multiple_loads",    'm', 1},
#endif
    { "disable_tailcalls",          'n', 1}, /* ECN: for pSOS, generically useful? */
    { "profile",                    'p', 1},
    { "profile_statements",         'p', 2},
#ifdef TARGET_IS_ARM_OR_THUMB
    { "check_stack",                's', 0},
#endif
    { "force_top_level",            't', 1}, /* @@@ freeze soon!        */
    { "pcrel_vtables",              'u', 1},
    { "check_printf_formats",       'v', 1},
    { "check_scanf_formats",        'v', 2},
    { "__compiler_msg_format_check", 'v', 3}, /* not for public use     */
    { "side_effects",               'y', 0},
    { "optimise_cse",               'z', 1}
};

#define NPRAGMAS (sizeof(pragma_words)/sizeof(PragmaSpelling))

PragmaSpelling const *keyword_pragma(char const *name, bool *negp) {
  Uint p;
  if (name[0] == 'n' && name[1] == 'o') {
    name += 2;
    if (name[0] == '_') name++;
    *negp = YES;
  } else
    *negp = NO;
/* For the small number of available options linear search seems OK */
  for (p = 0; p < NPRAGMAS; p++)
    if (StrEq(pragma_words[p].name, name))
      return &pragma_words[p];
  return NULL;
}

/* In the medium term the following routine is moving to compiler.c     */
/* Precondition: 'pragchar' is a lower case letter.                     */
static void main_pragma_set(int pragchar, int32 pragval)
{
#ifdef FORTRAN
/*
 * For FORTRAN purposes I need to be able to set and clear bits in
 * a single word, at least via wordy pragmas.
 */
    if (pragchar == 'x' || pragchar == 'w')
    {   if (pragval == 0) pp_pragmavec[pragchar - 'a'] = -1;
        else if (pragval > 0) pp_pragmavec[pragchar - 'a'] |= pragval;
        else pp_pragmavec[pragchar - 'a'] &= pragval;
    }
    else
#endif
    pp_pragmavec[pragchar - 'a'] =  pragval;
#ifdef INMOSC
    /* Support for obsolete Norcroft C error suppression pragmas:       */
    switch (pragchar)
    {
case 'b':
        if (pragval) suppress &= ~D_IMPLICITCAST;
        else
        {   if (!(suppress & D_IMPLICITCAST))
                cc_warn(pp_warn_pragma_suppress);
            suppress |= D_IMPLICITCAST;
        }
        break;
    }
#endif
}

static int pp_pragmardch(void) {
    int ch = pp_rdch();
    if (minus_e) fputc(ch, stdout);
    return ch;
}

static void pp_pragma(int pp_ch)
{   /* note that ANSI say it is NOT an error to fail to parse a #pragma */
    /* that does not stop us warning on syntax we fail to recognise     */
    if (pp_skipping)
    {   pp_skip_linetokens(pp_ch);
        return;
    }
    if (minus_e) {
        fputs("#pragma ", stdout);
        fputc(pp_ch, stdout);
    }
    for (;;)
    {   int pragchar; int32 pragval;
        while (pp_ch != PP_EOF && pp_white(pp_ch))
            pp_ch = pp_pragmardch();
        switch (pp_ch)
        {
    default:
            {   char pragma_name[32];
                unsigned p = 0;
                PragmaSpelling const *prag;
                bool negate;
 /*
 * Read a word starting with whatever non-blank character happens, but
 * following on through alphanumeric characters plus _ (plus maybe $).
 * Case fold the word that is read, and truncate it to 30 characters.
 */
                do
                {   if (p<30) pragma_name[p++] = safe_tolower(pp_ch);
                    pp_ch = pp_pragmardch();
                } while (pp_cidchar(pp_ch));
                pragma_name[p] = 0;
                prag = keyword_pragma(pragma_name, &negate);
                if (prag != NULL)
                {   pragval = prag->value;
                    if (negate) {
#ifdef FORTRAN
                        if (pragchar == 'x' || pragchar == 'w')
                            pragval = ~pragval;
                        else
#endif
                            pragval = !pragval;
                    }
                    pragchar = prag->code;
                    main_pragma_set(pragchar, pragval);
                    continue;           /* try for more pragmas on line */
                }
                cc_warn(pp_warn_bad_pragma);
                break;
            }
    case '\n':
            break;
    case '-':
            {   int32 n = 0; bool seen = 0;
                pp_ch = pp_pragmardch();
                if (isalpha(pp_ch)) pragchar = safe_tolower(pp_ch);
                else { cc_warn(pp_warn_bad_pragma1, (int)pp_ch);
                       break; }
                pp_ch = pp_pragmardch();
                while (isdigit(pp_ch))
                    seen = 1,
                    n = n*10 + (int)(pp_ch - '0'),
                    pp_ch = pp_pragmardch();
                pragval = seen ? n : -1;
                main_pragma_set(pragchar, pragval);
                continue;               /* try for more pragmas on line */
            }
        }
        pp_skip_linetokens(pp_ch);
        break;
    }
/*
 * #pragma force_top_level
 * inserts the token ___toplevel into the input stream (and in the
 * process puts a constraint on UNRDCHMAX), which symbol is supposed
 * to tell the parser to moan if it is within any nested construction.
 * This is done this way since it seems nicer to publish that a #pragma
 * can be used to assert top-level-ness, but pp.c is not aware of
 * just where we are in a program, so must pass the checking on to syn.c.
 * The main intended use is to put #pragma force_top_level as the first
 * line of all standard header files so that
 *       junk
 *       #include <stdio.h>
 * can be handled better than was previously possible.
 * The insertion is now handled at the end of pp_directive to avoid line
 * number problems.
 */

/*
 *       #pragma include_only_once
 * indicate that the current file should not be included again. The
 * name is taken as pp_fl->f (which does not have quote marks or <>
 * around it).  Expected to be good for speed in some cases.
 * Note for those concerned with ANSI small print - the files names found
 * within "" and <> here are treated in an implementation defined manner
 * and that means that #pragma can change the interpretation - I deem
 * the include_only_once option to change the mapping to direct some
 * file names onto a notional empty file the second time around.
 */
    if (var_include_once > 0)
    {   include_only_once(pp_fl->f, NULL, active_string_file);
        if (pp_filestack) pp_filestack->ifdefname = (char *)DUFF_ADDR;
        var_include_once = 0;
    }
}

static void pp_h_error_ident(int pp_ch, bool iserror)
{   int32 n = 0;
    char msg[256];
    while (pp_ch != '\n' && pp_ch != PP_EOF)
    {   if (n < 255) msg[n++] = pp_ch == '\t' ? ' ' : pp_ch;
        pp_ch = pp_rdch();
    }
    /* fill in terminator, and continue if last char was space */
    do msg[n] = 0; while (--n >= 0 && msg[n] == ' ');
/* the next line treats sysV #ident as a never moaning #error.         */
    if (iserror && !pp_skipping)
    {   /* Groan: the ANSI rationale recommends that #error terminates */
        /* compilation, but provides no way of fixup and continue.     */
        /* The following (hopefully) temporary fix provides #pragma -e */
        /* to continue.                                                */
        if (pp_pragmavec['e'-'a'] > 0)
            cc_rerr(pp_rerr_hash_error, msg);
        else
            cc_fatalerr(pp_fatalerr_hash_error, msg);
    }
    pp_skip_linetokens(pp_ch);          /* @@@ why? already at newline. */
}

static void pp_h_error(int pp_ch)
{   pp_h_error_ident(pp_ch,1);
}

#ifdef EXTENSION_SYSV
static void pp_h_ident(int pp_ch)
{   /* should we inhibit this when in a system include file?            */
 #ifdef NEVER
    if (!HasFeature(Feature_PCC)) cc_rerr(pp_rerr_hash_ident);
 #endif
    pp_h_error_ident(pp_ch,0);
}
#endif

static void pp_directive(void)
{
  int32 i=0;
  int pp_ch, cpp_allows_junk=0;
  char v[PP_DIRLEN+1];
  bool old_seen = seen_pp_token;

  pp_in_directive = 1;
  seen_pp_token = 1;
  pp_ch = pp_skipb0();
  for (i=0; isalpha(pp_ch); )
  {
    if (i<PP_DIRLEN) v[i++] = pp_ch;  pp_ch = pp_rdch();
  }
  v[i] = 0;
  pp_ch = pp_skipb1(pp_ch);
  if (StrEq(v, "include"))
  { pp_include(pp_ch);
    pp_in_directive = 0;
/* Note re cc -E only: it is arguable that we should set pp_rdch3nls=0  */
/* here so NL's in comments are not output after the "#line" from       */
/* pp_inclopen().  But then it would be wrong if file didn't open.      */
    return;
  }
  else if (StrEq(v, "define"))  pp_define(pp_ch, 0);
#ifdef MACH_EXTNS
  else if (StrEq(v, "defineval"))  pp_define(pp_ch, 1);
#endif
  else if (StrEq(v, "undef"))   pp_undef(pp_ch), cpp_allows_junk=1;
  else if (StrEq(v, "if"))
  { pp_h_if(pp_ch);
    /* Assert: after pp_h_if(), at end of line or at end of file */
    pp_in_directive = 0;
    return;
  }
  else if (StrEq(v, "ifdef"))   pp_h_ifdef(pp_ch, 1);
  else if (StrEq(v, "ifndef"))
      seen_pp_token = old_seen, pp_h_ifdef(pp_ch, 0);
  else if (StrEq(v, "else"))    pp_h_else(pp_ch), cpp_allows_junk=1;
  else if (StrEq(v, "elif"))
  { pp_h_elif(pp_ch);
    /* Assert: after pp_h_elif(), at end of line or at end of file */
    pp_in_directive = 0;
    return;
  }
  else if (StrEq(v, "endif"))   pp_h_endif(pp_ch), cpp_allows_junk=1;
  else if (StrEq(v, "line"))    pp_h_line(pp_ch);
  else if (StrEq(v, "pragma"))  pp_pragma(pp_ch);
  else if (StrEq(v, "error"))   pp_h_error(pp_ch);
#ifdef EXTENSION_SYSV
  else if (StrEq(v, "ident"))   pp_h_ident(pp_ch);    /* non-ansi */
#endif
  else if (StrEq(v, ""))
  {   /* If chars left assume a #line (but only in pcc mode).           */
      /* Oughtn't we to discourage #<number> in f77?  PCC mode?         */
      if (!PP_EOLP(pp_ch)
#ifndef FORTRAN
           && HasFeature(Feature_PCC)
#endif
         )
          pp_h_line(pp_ch);
      else
          pp_unrdch(pp_ch);
  }
  else
  { /* AM: @@@ ANSI ambiguity.  Is #if 0; #wombat; #endif ok?           */
    if (!pp_skipping) cc_err(pp_err_unknown_directive, v);
    else if (HasFeature(Feature_Predeclare))
        /* tick off the user anyway if (s)he asked for it!              */
        cc_warn(pp_err_unknown_directive, v);
    pp_skip_linetokens(pp_ch);
  }
  pp_ch = pp_skipb0();
  if (!PP_EOLP(pp_ch) && pp_ch != PP_EOF)
  {
      if (!(cpp_allows_junk &&
              (HasFeature(Feature_PCC) || HasFeature(Feature_LimitedPCC) ||
               SuppressDB_Has(Suppress_PPAllowJunk))))
          cc_rerr(pp_rerr_junk_eol, v);
      pp_skip_linetokens(pp_ch);
  }
  else
      pp_unrdch(pp_ch);
  pp_in_directive = 0;
  /* It is woeful we need to do this here instead of in pp_pragma() */
  /* but it needs to be done after the above checks. The earlier    */
  /* alterative involved fiddling with pp_fl->l, and was broken.    */
  if (var_force_top_level > 0
#ifdef FOR_ACORN
      && !cplusplus_preprocessing()
#endif
     )
  {   pp_wrbuf("___toplevel", 11L);
      var_force_top_level = 0;
  }
}

#ifdef FORTRAN
/*
 * F77 INCLUDEs require *currently* sticky EOFs, or statement assembly
 * becomes screwed up.
 * The sticky condition is cleared (for one read) by pp_pop_include().
 */
static int pp_stick_at_eof;

void pp_pop_include(void)
{
    pp_stick_at_eof = 0;
}
#endif

/* pp_process() behaves like _filbuf in stdio.
   Analogously it could collect larger bits of text before returning.
   But beware the interaction via recursive calls via #if.
*/

/* pp_lastch really keeps a record of a preceding newline (or file start) */
/* for #<directive>.  Note that it is not updated on <space> or <tab>.    */
static int pp_lastch;   /* perhaps could be done via unrdch(). */

static int pp_process(void)
{   int pp_ch;
    pp_abufptr = pp_abufbase;
    while (pp_abufptr == pp_abufbase) /* do {} while really. */
    {   pp_ch = pp_rdch();
        switch (pp_ch)
        {
    case PP_EOF:
              if (pp_filestack != 0 && pp_filestack->ifdefname != DUFF_ADDR)
              { if (!seen_pp_token && pp_filestack->ifdefname != 0)
                { PP_HASHENTRY* h = pp_lookup_name(pp_filestack->ifdefname);
                  include_only_once(pp_fl->f,
                      pp_filestack->ifdefname, active_string_file);
                  if (h == NULL || !pp_hashalive_(h))
                      cc_warn(pp_warn_guard_not_defined, pp_filestack->ifdefname);
                }
                else if (!SuppressDB_Has(Suppress_GuardedInclude) &&
                         !fnameEQ(pp_fl->f, "assert.h"))
                  cc_warn(pp_warn_not_guarded);
              }
              if (active_string_file == NULL && pp_cis != NULL)
                trackfile_close(pp_cis);    /* see pp_include() */
/* @@@ ANSI do not specify whether #if's must match in a #include file.   */
/* hence only check all #if's closed on real EOF.                         */
              if (pp_filestack == 0)
              { if (pp_ifstack != 0) cc_err(pp_err_endif_eof);
                return PP_EOF;
              }
              else if (pp_filestack->ifstart != pp_ifstack)
                  cc_warn(pp_warn_unbalanced);
#ifdef FORTRAN
              if (pp_stick_at_eof) return PP_EOF;
              pp_stick_at_eof = 1;
#endif
              pp_cis = pp_filstream_(pp_filestack);
              *pp_fl = pp_fileline_(pp_filestack);
#ifndef NO_LISTING_OUTPUT
              profile_ptr = pp_propoint_(pp_filestack);
              pp_filenumber = pp_filenumber_(pp_filestack);
              list_this_file = !(pp_filenumber & 0x80000000);
              active_string_file = pp_stringfile_(pp_filestack);
#endif /* NO_LISTING_OUTPUT */
              { PP_FILESTACK *q = pp_filchain_(pp_filestack);
                /* discard old */
                pp_filchain_(pp_filestack) = pp_freefilestack,
                pp_freefilestack = pp_filestack;
                pp_filestack = q;
              }
              /* there is an #include in the file we've just popped to */
              seen_pp_token = 1;
              pp_rdptr = NULL;
              pp_rdcnt = 0;
              pp_ch = '\n';             /* to set pp_lastch later...    */
/* The next line resets the (BSD-style) -I list in compiler.c           */
              pp_inclclose(*pp_fl);
              break;
    case '#': if (PP_EOLP(pp_lastch))
              { pp_directive(); pp_ch = '\n'; }
              else if (!pp_skipping) pp_wrch(pp_ch);
              break;
    case ' ':
    case '\t':if (!pp_skipping) pp_wrch(pp_ch);
#ifndef PASCAL_OR_FORTRAN
              if (!HasFeature(Feature_PCC))
#endif
                  /* spaces may precede '#' only in ANSI C */
                  pp_ch = pp_lastch;
              break;
    case '\n':pp_wrch(pp_ch);
              break;  /* output nl even if skipping */
#ifndef FORTRAN
    case '\'':
    case '"': pp_ch = pp_copystring(pp_ch);
              break;
/* The following line is not needed to make pp_number work.             */
/*  case '.': if (!pp_skipping) pp_wrch(pp_ch); break;                  */
#endif
    case '%': if (PP_EOLP(pp_lastch))
              {   int nextch = pp_rdch();
                  if (nextch == ':')
                  {   pp_directive();
                      pp_ch = '\n';
                      break;
                  } else
                  {   if (!pp_skipping) pp_wrch('%');
                      pp_unrdch(nextch);
                      break;
                  }
              }
              /* otherwise, fall through */
    default:  if (!pp_skipping)
              {
#ifndef FORTRAN
                if (pp_macstart(pp_ch) || pp_ch == PP_NOEXPAND)
                    pp_checkid(pp_ch);
                else if(isdigit( (unsigned char)pp_ch ))
                    pp_number(pp_ch);
                else
#endif
                if (pp_ch == PP_TOKSEP)
                {   if (!HasFeature(Feature_PCC)) pp_wrch(' ');
                    /* else lose it in PCC mode.                        */
                }
                else
                    pp_wrch(pp_ch);
              }
        }
        pp_lastch = pp_ch;
        if (!isspace(pp_ch)) seen_pp_token = 1;     /* significant token */
    }
    pp_abufoptr = pp_abufbase;
    return *pp_abufoptr++;
}

#ifndef NO_LISTING_OUTPUT
static int pp_listchar(int ch)
{   /* AM: merge this code with other FEATURE_UNEXPANDED... code above? */
    if (!(pp_filenumber & 0x80000000) &&
        !HasFeature(Feature_UnexpandedListing))
    {   if (ch != PP_EOF)
        {   putc(ch, listingstream);
            if (ch == '\n')
            {   listing_diagnostics();
                if (profile_count) listing_nextline(pp_fl->l);
                fprintf(listingstream, "%6u  ", pp_fl->l + 1);
            }
        } else putc('\n', listingstream);
    }
    return ch;
}
#endif

/*
 * Exported things ...
 */

int pp_nextchar(void)
{   int ch;
    /* pp_process() cannot do the PP_NOEXPAND/PP_ESC removal, because   */
    /* these are embedded within pp tokens, not just between them.      */
    do
    {   ch = ((pp_abufoptr < pp_abufptr) ? *pp_abufoptr++ : pp_process());
    }
    while (ch == PP_NOEXPAND);
    if (ch == PP_ESC)
    {   ch = ((pp_abufoptr < pp_abufptr) ? *pp_abufoptr++ : pp_process());
        if (ch == ' ')
            ch = PP_TOKSEP;
        else if (ch == '\t')
            ch = PP_NOEXPAND;
    }
#ifndef NO_LISTING_OUTPUT
    /* AM presumes that pp_listchar is an identity fn to help regalloc  */
    /* compile this routine into fast code?  Hmm.                       */
    if (listingstream) return pp_listchar(ch);
#endif /* NO_LISTING_OUTPUT */
    return ch;
}

void pp_predefine(char *s)
{
    (void)pp_predefine2(s, 1);
}

void pp_preundefine(char *s)
{
  int32 i = 0, hash = 0;
/* Assumption on ABUFSIZE implies  pp_abuf_ensure(PP_DEFLEN+1) OK.      */
  for (;;)
  {   int ch = *s++;
      if (!pp_cidchar(ch)) break;
      if (i < PP_DEFLEN) hash = HASH(hash, ch), pp_abufbase[i++] = ch;
  }
  pp_abufbase[i] = 0;

  if (!pp_skipping)                            /* @@@ duh? */
  {
      PP_HASHENTRY *p = pp_lookup(pp_abufbase, hash);
      if (p) {
        pp_hashalive_(p) = 0;
        if (usrdbg(DBG_PP)) dbg_undef(pp_hashname_(p), curlex.fl);
      }
  }
}

#ifndef NO_DUMP_STATE
void PP_LoadState(FILE *f) {
    for (;;) {
      file_name_list *p;
      uint16 fnamelen, ifdeflen;
      uint8 stringfile;
      fread(&fnamelen, sizeof(uint16), 1, f);
      if (fnamelen == 0) break;
      fread(&ifdeflen, sizeof(uint16), 1, f);
      p = (file_name_list *)pp_alloc((int32)sizeof(file_name_list)+fnamelen+ifdeflen+1);
      fread(&stringfile, sizeof(uint8), 1, f);
      p->stringfile = stringfile;
      Dump_LoadString(p->fname, fnamelen, f);
      if (ifdeflen == 0)
        p->ifdefname = NULL;
      else {
        char *ifdefname = &p->fname[fnamelen+1];
        p->ifdefname = ifdefname;
        Dump_LoadString(ifdefname, ifdeflen, f);
      }
      cdr_(p) = seen_before;
      seen_before = p;
    }
    pp_hashfirst = pp_hashlast = NULL;
    for (;;) {
      uint16 nlen; int32 bodylen;
      PP_HASHENTRY *h;
      uint32 hash = 0;
      unsigned i;
      char *name;
      fread(&nlen, sizeof(uint16), 1, f);
      if (nlen == 0) break;
      fread(&bodylen, sizeof(int32), 1, f);
      { PP_HASHBITS u;
        uint32 size;
        fread(&u.w, sizeof(uint32), 1, f);
        size = u.b.noargs ? PP_NOARGHASHENTRY : sizeof(PP_HASHENTRY);
        h = (PP_HASHENTRY *)pp_alloc(u.b.ismagic ? size+nlen+1 : size+nlen+bodylen+2);
        pp_hashname_(h) = name = (char *)h + size;
        pp_unchain_(h) = NULL; pp_sleepleft_(h) = 0;
        pp_hashdefchain_(h) = NULL;
        h->u.w = u.w;
        if (pp_hashlast == NULL)
          pp_hashfirst = h;
        else
          pp_hashdefchain_(pp_hashlast) = h;
        pp_hashlast = h;
        Dump_LoadString(name, nlen, f);
        if (!pp_hashismagic_(h)) {
          char *hashbody = &name[nlen+1];
          pp_hashbody_(h) = hashbody;
          Dump_LoadString(hashbody, (size_t)bodylen, f);
        } else
          pp_hashmagic_(h) = bodylen;
      }
      for (i = 0; i < nlen; i++)
        hash = HASH(hash, name[i]);

      if (!pp_hashnoargs_(h)) {
        PP_ARGENTRY *a, **ap = &pp_hasharglist_(h);
        pp_hasharglist_(h) = NULL;
        for (;; ap = &pp_argchain_(a)) {
          fread(&nlen, sizeof(uint16), 1, f);
          if (nlen == 0) break;
          a = (PP_ARGENTRY *)pp_alloc((int32)sizeof(PP_ARGENTRY)+nlen+1);
          pp_argname_(a) = (char *)(a+1);
          pp_argchain_(a) = NULL;
          pp_argactual_(a) = DUFF_OFFSET;
          *ap = a;
          Dump_LoadString(pp_argname_(a), nlen, f);
        }
      }
      { PP_HASHENTRY *q = pp_lookup(name, hash);
        if (q) pp_hashalive_(q) = 0;
        pp_hashchain_(h) = (*pp_hashtable)[hash % PP_HASHSIZE];
        (*pp_hashtable)[hash % PP_HASHSIZE] = h;
      }
    }
}

void PP_DumpState(FILE *f) {
  { file_name_list *p;
    uint16 fnamelen;
    for (p = seen_before;  p != NULL;  p = cdr_(p)) {
      uint16 ifdeflen = 0;
      uint8 stringfile = (uint8)p->stringfile;
      fnamelen = (uint16)strlen(p->fname);
      if (p->ifdefname != NULL) ifdeflen = (uint16)strlen(p->ifdefname);
      fwrite(&fnamelen, sizeof(uint16), 1, f);
      fwrite(&ifdeflen, sizeof(uint16), 1, f);
      fwrite(&stringfile, sizeof(uint8), 1, f);
      fwrite(p->fname, 1, fnamelen, f);
      if (ifdeflen > 0) fwrite(p->ifdefname, 1, ifdeflen, f);
    }
    fnamelen = 0;
    fwrite(&fnamelen, sizeof(uint16), 1, f);
  }
  { PP_HASHENTRY *h = pp_hashfirst;
    uint16 nlen;
    for (; h != NULL; h = h->defchain) {
      int32 bodylen = pp_hashismagic_(h) ? pp_hashmagic_(h) :
                                           strlen(pp_hashbody_(h));
      nlen = (uint16)strlen(pp_hashname_(h));
      fwrite(&nlen, sizeof(uint16), 1, f);
      fwrite(&bodylen, sizeof(int32), 1, f);
      fwrite(&h->u.w, sizeof(uint32), 1, f);
      fwrite(pp_hashname_(h), 1, nlen, f);
      if (!pp_hashismagic_(h)) fwrite(pp_hashbody_(h), 1, (size_t)bodylen, f);
      if (!pp_hashnoargs_(h)) {
        PP_ARGENTRY *a = pp_hasharglist_(h);
        for (; a != NULL; a = pp_argchain_(a)) {
          nlen = strlen(pp_argname_(a));
          fwrite(&nlen, sizeof(uint16), 1, f);
          fwrite(pp_argname_(a), 1, nlen, f);
        }
        nlen = 0;
        fwrite(&nlen, sizeof(uint16), 1, f);
      }
    }
    nlen = 0;
    fwrite(&nlen, sizeof(uint16), 1, f);
  }
}
#endif /* NO_DUMP_STATE */

void pp_tidyup(void)
{ PP_HASHENTRY *p;
  if (HasFeature(Feature_PPNoUse))
      for (p = pp_hashfirst; p != 0; p = pp_hashdefchain_(p))
      { if (pp_hashuses_(p) == 0)
          cc_warn(pp_warn_unused_macro, pp_hashname_(p));
      }
#ifndef NO_LISTING_OUTPUT
  /* This next line must happen after all diagnostics have been produced */
  if (listingstream != NULL)
  {   listing_diagnostics();
      if (profile_count != 0) putc('\n', listingstream);
  }
#endif
#ifdef ENABLE_PP                /* spurious: deadcode elimination fixes */
  if (debugging(DEBUG_PP))
  { int32 i, argcnt;
    PP_ARGENTRY *a;
    cc_msg("%ld substitutions\n", (long)pp_nsubsts);
    cc_msg("Hash table:\n");
    for (i=0; i<PP_HASHSIZE; i++)
      for (p = (*pp_hashtable)[i]; p != 0; p = pp_hashchain_(p))
        { cc_msg("%ld: %s", (long)i, pp_hashname_(p));
          if (!pp_hashnoargs_(p))
          { cc_msg("(");
            for (a = pp_hasharglist_(p), argcnt=0; a != 0; a=pp_argchain_(a))
              cc_msg("%s%s", (argcnt++ == 0 ? "" : ","), pp_argname_(a));
            cc_msg(")");
          }
          cc_msg(" '%s'%s uses %ld\n",
                 (pp_hashismagic_(p) ? "<magic>" : pp_hashbody_(p)),
                 (pp_hashalive_(p) ? "" : " (undef'd)"),
                 (long)pp_hashuses_(p));
        }
  }
#endif
}

void pp_copy(void) {
  int ch;
  minus_e = YES;
  while ((ch = pp_nextchar()) != PP_EOF) fputc(ch, stdout);
}

void pp_init(FileLine *fl)
{ time_t t0 = time(0);
  minus_e = FALSE;
  strncpy(pp_datetime, ctime(&t0), 26-1);   /* be cautious */
  pp_fl = fl;
  pp_hashtable = (PP_HASHTABLE *)pp_alloc(sizeof(*pp_hashtable));
  ClearToNull((void **)pp_hashtable, sizeof(*pp_hashtable)/sizeof(void **));
  pp_hashfirst = pp_hashlast = pp_noexpand = 0;
  pp_dbufend = pp_dbufseg = pp_dbufptr = 0;
  pp_ebufbase = (char *)pp_alloc(PP_EBUFINITSIZ);
  pp_ebufptr = pp_ebuftop = pp_ebufbase + PP_UNRDCHMAX;
  pp_ebufend = pp_ebufbase + PP_EBUFINITSIZ;
  pp_abufptr = pp_abufoptr = pp_abufbase = (char *)pp_alloc(PP_ABUFINITSIZ);
  pp_abufend = pp_abufbase + PP_ABUFINITSIZ;
  pp_scanidx = -1;
  pp_nsubsts = 0;
  pp_instring = 0;
  pp_inhashif = NO;
  pp_expand_level = 0;
  pp_ifstack = 0; pp_freeifstack = 0; pp_skipping = 0;
  pp_filestack = 0; pp_freefilestack = 0;
#ifdef FORTRAN
  pp_stick_at_eof = 1;
#endif
  seen_before = NULL;
  {   int ch;
      for (ch = 0; ch <= UCHAR_MAX; ch++)
      {   int i = 0;
          if (isalpha(ch) || ch == '_') i = PP_MACSTART + PP_CIDCHAR;
          if (isalnum(ch)) i |= PP_CIDCHAR;
          pp_ctype[ch] = i;
      }
  }
  pp_ctype[' ']  = PP_WHITE;
  pp_ctype['\t'] = PP_WHITE;
  pp_ctype[PP_TOKSEP & 0xff] = PP_WHITE;
/* args, options... */
  {  int i;     /* @@@ AM migrated to mip/compiler.c, going again... */
     for (i=0; i <= 'z'-'a'; i++) pp_pragmavec[i] = -1;
  }
  active_string_file = NULL;
  if (usrdbg(DBG_PP)) (void)dbg_notefileline(curlex.fl);
  (void)pp_predefine2("__LINE__", PP__LINE);
  (void)pp_predefine2("__FILE__", PP__FILE);
  (void)pp_predefine2("__DATE__", PP__DATE);
  (void)pp_predefine2("__TIME__", PP__TIME);
  /* __STDC__ gets set up after -zi command line pre-include file!      */
  pp_hashone = pp_predefine2("!!ONE!!",  PP__ONE);  /* for #if defined(...) */
  pp_hashzero = pp_predefine2("!!ZERO!!", PP__ZERO);
}

static void pp_init2(FILE *stream, bool preinclude)
{ int ch;
  IGNORE(stream);
/* The strange order here has to do with the definedness of conversions */
/* between int and signed/unsigned char. See early comment re RARE_char.*/
  for (ch = 0;  ch <= UCHAR_MAX;  ++ch)
  {   int tch;
      if (isprint(ch)             ||  /* most common case */
          HasFeature(Feature_PCC) ||  /* no more conversion */
          ch == '\t'              ||  /* allowable space ch */
          legal_non_isprint(ch))
          tch = ch;
      else if (isspace(ch))
          /* convert all other end-of-line chars to '\n' */
          tch = '\n';
      else
          tch = PP_TOKSEP;
      pp_translate[ch] = tch;
  }
#ifdef PASCAL
  pp_translate['\\'] = '\\';
#else
  pp_translate['\\'] = PP_TOKSEP;
#endif
  pp_translate['\n'] = PP_TOKSEP;
#ifndef FORTRAN
  pp_translate[COMMENT_START] = PP_TOKSEP;
#endif
#ifdef PASCAL
  pp_translate['{']  = PP_TOKSEP;
#endif
  if (HasFeature(Feature_PCC))
  {   pp_ctype['$']  = PP_MACSTART + PP_CIDCHAR;
      pp_translate[PP_TOKSEP]  = PP_TOKSEP;
      pp_translate[PP_NOEXPAND]  = PP_TOKSEP;
      pp_translate[PP_ESC]  = PP_TOKSEP;
  }
  else
  {   if (!preinclude)
      {
#ifdef PASCAL
          (void)pp_predefine2("__ISO__", PP__ONE);
#else
          (void)pp_predefine2("__STDC__", PP__ONE);
#endif
          if (LanguageIsCPlusPlus)
/* [ES] requires the following to be set, note that __STDC__ is too!.   */
          {   (void)pp_predefine2("__cplusplus", PP__ONE);
              if (HasFeature(Feature_CFront))
                  (void)pp_predefine2("__CFRONT_LIKE", PP__ONE);
          }
      }
#ifndef PASCAL_OR_FORTRAN
      pp_translate['?'] = PP_TOKSEP;             /* translate triglyphs */
#endif
  }
  pp_lastch = '\n';
  pp_rdch1nls = pp_rdch3nls = pp_rdch_la = 0;
  pp_in_directive = 0;
  seen_pp_token = 0;
}

/* Perhaps better another external function than partial init on        */
/* notesource (which sounds innocent)                                   */
#ifdef INMOSC
void pp_notesource(char const *filename)      /* preserve interface           */
{   FILE *stream = stdin;
#else
void pp_notesource(char const *filename, FILE *stream, bool preinclude)
{
#endif
    init_pp_fl(filename);
    pp_cis = stream;
    pp_init2(stream, preinclude);
    if (preinclude) return; /* pre-include case.. */
#ifndef NO_LISTING_OUTPUT
    profile_find(filename);      /* sets profile_ptr, pp_filenumber */
#endif
}

/* end of pp.c */
