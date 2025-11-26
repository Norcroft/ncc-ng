/*
 * C compiler file lex.c
 * Copyright (C) Codemist Ltd., 1988-1992
 * Copyright (C) Acorn Computers Ltd., 1988-1990
 * Copyright (C) Advanced RISC Machines Ltd., 1990-1992
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$ Codemist 61
 * Checkin $Date$
 * Revising $Author$
 */

/*
 *   AM Feb 92: add some C++-isms when CPLUSPLUS is #defined.
 *              When not defined only effect is a warning for C++ keywords.
 *   AM Nov 89: treat ANSI pp-number conversion errors properly.
 *   AM Jun 89: add 16 bit int support
 *   13.x.88   Pascal split off
 *   AM 23-10-86: Fix bug in string wrap round segments, add cc_rerr() calls.
 *   AM 28-7-86: Recognise += in lexer without whitespace, glue (nextsym)
 *               '+ =' with space/tab white space.  Problematic here
 *               to recognise '+\n='.  A #if would clobber things.
 */

#ifndef _LEX_H
#ifdef __STDC__
#  include <stddef.h>
#  include <string.h>
#else
#  include "stddef.h"
#  include <strings.h>
#endif
#include <ctype.h>

#include "globals.h"
#include "lex.h"
#include "bind.h"
#include "pp.h"
#include "store.h"
#include "util.h"
#include "aeops.h"
#include "errors.h"
#ifdef TARGET_HAS_INLINE_ASSEMBLER
#  include "inlnasm.h"
#endif

#define lex_getbodysym() ((void) 0)
#define lex_putbodysym() ((void) 0)
#define save_names(a)    ((void) 0)
#endif

/* 2 worlds stuff */
typedef struct SymBuf {
  struct SymBuf *prev; SymInfo prevsym;         /* for save/restore     */
  SymInfo *buf;
  int size, pos, count;
  bool dup_hack;    /* template and d-or-e uses have diverged (sigh!)   */
  int old_put_handle; /* used to stop recording while playing (or while recording d-or-e */
} SymBuf;

static SymBuf *lexbuf_vec, *nextsym_lookaside;
static int nextsym_put_handle;  /* only one template can be active      */
static int lexbuf_max;
static int buffersym_bufidx;
/* */

static FileLine endofsym_fl;

/* exports: nextsym(), curlex, nextsym_for_hashif(),
            lex_init(),            and some more! */

/* utilities */
static int intofxdigit(int c)
/* convert hex digit to integer  */
{   return(isdigit(c) ? (c) - '0' :
           islower(c) ? (c) - 'a' + 10 :
           isupper(c) ? (c) - 'A' + 10 :
           -1);
}

#define NOTACHAR        0

#define LEX_STRBUFSIZE  256  /* (multiple of 4) initial size lex_strbuf */
static char *lex_strptr;     /* next free char in lex_strbuf            */
static char *lex_strend;     /* one beyond end of lex_strbuf            */

static SymInfo prevlex, prevlex_hif, nextlex = {s_nothing};

static int curchar;          /* The look-ahead character */
/* The next 3 variables are notionally a single tuple. Export to misc. */
SymInfo curlex;              /* Current token and aux. info.            */
#ifdef EXTENSION_VALOF
bool inside_valof_block;
static Symstr *resultisword;
#endif

#ifdef TARGET_HAS_INLINE_ASSEMBLER
int asm_mode = ASM_NONE;
static bool in_asm_string = NO;
#endif

int errs_on_this_sym;    /* To help error recovery */


/* the +4 in the next line is slop so we do not check on dec. pt. etc.  */
static char namebuf[NAMEMAX+4];     /* Buffer for reading identifiers   */

static unsigned32 lexclass[1+255];
                                    /* Character table, yielding:
                                       glue-ishness (low 8 bits),
                                       corresponding symbol (next 8 bits),
                                       doubled symbol (next 8 bits)
                                       relop equal symbol (top 8 bits)     */
#define lexclass_(ch) lexclass[ch & 0xff]
/* or [(unsigned char)ch], but there are compilers which have difficulty
   with that
 */

/* 'curlex.a2.flag' values - only exported for make_integer (q.v.) */
/* the values are chosen for easy punning into sem.c types  */

#define NUM_FLOAT  bitoftype_(s_double)
#define NUM_INT    bitoftype_(s_int)
#define NUM_LONG   bitoftype_(s_long)
#define NUM_SHORT  bitoftype_(s_short)
#define NUM_UNSIGN bitoftype_(s_unsigned)
#define NUM_LONGLONG bitoftype_(s_longlong)
#define NUM_CHAR   (LanguageIsCPlusPlus ? bitoftype_(s_char) : NUM_INT)
                           /* Type of 'a' is int in C, char in C++.     */

/* Note that NUM_WCHAR is defined in defaults.h.                        */


/* lexical classes - local to this file */

#define l_illegal   0L
#define l_noglue    1L
#define l_selfglue  2L
#define l_idstart   3L
#define l_digit0    4L
#define l_digit1    5L
#define l_quote1    6L
#define l_quote2    7L
#define l_dot       8L
#define l_shifter   9L
#define l_eqglue    10L
#define l_minus     11L
#define l_lpar      12L
#define l_less      13L
#define l_hash      14L
#define l_colon     15L
#define l_coloncpp  16L
#define l_percent   17L

#define LEX_CHTYPE  31L  /* mask */
#define l_idcont    32L  /* orable */
#define mklc(l,t1,t2,t3) (((unsigned32)(l)) | ((unsigned32)(t1) << 8) | \
                          ((unsigned32)(t2) << 16) | ((unsigned32)(t3) << 24))

/* lex 'semantic' routines... */

/* make_floating uses GLOBAL store for its value.  Is this reasonable? */
static AEop make_floating(char *s, int32 flag)
{   FloatCon *x = real_of_string(s,flag);
    curlex.a1.fc = x;
    return x->h0;
}

/* make_integer does not use GLOBAL or LOCAL store.  It could use
   the former (but this could be wasteful), or LOCAL, but beware placement
   of alloc_reinit() in driver.c and lookahead tokens.
   Currently it just assumes that syn.c will look at curlex.a2.flag.
*/
static AEop make_integer(int32 radix, int32 flag)
/* Numbers that overflow 2**32-1 lead to a diagnostic.                 */
/* Otherwise their type suffix (in flag) is modified to yield a type.  */
/* Note that octal and hex numbers sometimes have different types.     */
/* I have allowed the digits '8' and '9' to build up even in           */
/* octal numbers - this is checked for here.                           */
/* BEWARE: possible two's complement dependency.                       */
{
    bool overflow = NO, badoct = NO, overflow_warned = NO;
    uint64 val64, t64, radix64;
    uint32 value;
    char c, *cp = namebuf;
    I64_IToU(&radix64, radix);
    I64_IToU(&val64, 0);
    while ((c = *cp++) != 0) {
        int32 n = 0;
        switch (radix) {
        case 8:
            if (c>='8') badoct = YES;
            n = intofdigit(c);
            break;
        case 10:
            n = intofdigit(c);
            break;
        case 16:
            n = intofxdigit(c);
            break;
        }
        overflow = overflow | (I64_UMul(&val64, &val64, &radix64) != i64_ok);
        I64_IToU(&t64, n);
        overflow = overflow | (I64_UAdd(&val64, &val64, &t64) != i64_ok);
    }
    if (badoct) cc_rerr(lex_rerr_8_or_9);
    if (overflow) {
        cc_err(lex_err_ioverflow_64, namebuf);
        overflow_warned = YES;
    }

/* Now modify 'flag' (if necessary) to get a type for the constant.     */
    /* ANSI rules (bracketted cases cannot happen if int==long):
     *             (10) int, [long], unsigned long.
     *             (8,16) int, unsigned, [long], [unsigned long].
     *             (u)  unsigned, [unsigned long].
     *             (l)  long, unsigned long.
     *             (ul) unsigned long.
     */
    overflow = I64_UToI(&value, &val64) != i64_ok;
    if (HasFeature(Feature_Fussy)) {
        if (!overflow_warned && overflow) {
            cc_err(lex_err_ioverflow, namebuf);
            overflow_warned = YES;
        }
    } else if (overflow
               || (radix == 10 && (value & 0x80000000) && !(flag & NUM_UNSIGN))
               || (flag & NUM_LONGLONG)) {
        bool warned = false;
        if (!(flag & NUM_LONGLONG) && !SuppressDB_Has(Suppress_LongLongConst))
        {   if (val64.hi & 0x80000000)
                cc_warn(lex_warn_force_ulonglong, namebuf, namebuf);
            else
                cc_warn(lex_warn_force_longlong, namebuf, namebuf);
            warned = true;
        }
        if (val64.hi & 0x80000000)
        {   flag |= NUM_UNSIGN;
            if (!warned)
                cc_warn(lex_warn_force_ulonglong, namebuf, namebuf);
        }
        curlex.a1.i64 = mkint64const(flag ^ (NUM_LONGLONG|NUM_SHORT|NUM_LONG), (int64 *)&val64);
        return s_int64con;
    }

    if (sizeof_int == 2)                /* TARGET_HAS_16_BIT_INT        */
    {   if (value & 0xffff0000 || flag & NUM_LONG)
        {   flag |= NUM_LONG;
            if (value & 0x80000000 && !(flag & NUM_UNSIGN))
            {   if (radix == 10)
                    if (!overflow)     /* only 1 error message */
                        cc_ansi_warn(lex_warn_force_unsigned, namebuf, namebuf);
                flag |= NUM_UNSIGN;
            }
        }
        else
        {   if (value & 0x8000 && !(flag & NUM_UNSIGN))
            {   /* warnings here?                                       */
                flag |= (radix == 10) ? NUM_LONG : NUM_UNSIGN;
            }
        }
    }
    else                                /* TARGET_HAS_32_BIT_INT        */
    {   /* (As above) the rules simplify if sizeof_int == sizeof_long == 4. */
        /* Since if value is +ve or unsigned then 'flag' is OK, else        */
        /* we need to convert to 'ul' (decimal) else 'flag+u' otherwise.    */
        if ((value & 0x80000000)  && !(flag & NUM_UNSIGN))
        {   flag |= NUM_UNSIGN;    /* add 'U' - see ANSI spec */
            if (radix == 10)       /* but for base 10 add 'L' too */
            {   flag |= NUM_LONG;
                if (!overflow_warned)     /* only 1 error message */
                    cc_ansi_warn(lex_warn_force_unsigned, namebuf, namebuf);
            }
        }
    }
    curlex.a1.i = value;
    curlex.a2.flag = flag;
    return s_integer;
}

/* The following routine does checks for 'constraint violation' when    */
/* coverting a pp_number to a token, caller has already checked for     */
/* illegal uses of 'e+' in fp or hex numbers.                           */
static void lex_check_pp_number(void)
{   if (curchar == '.' ||
        curchar != PP_EOF && (lexclass_(curchar) & l_idcont))
            cc_ansi_rerr(lex_rerr_pp_number);
}

/* reading routines */

static int nextchar(void)
/* I may also want to buffer some recently read characters so that I   */
/* can display them when I notice an error.                            */
{
    if (curchar==PP_EOF) return curchar;
    curchar = pp_nextchar();
    return curchar;
}

#define is_e(c)                         /* e or E (exponent marker) */ \
    (((c) == 'e') || ((c) == 'E'))

#define is_x(c)                         /* x or X (hex num marker)  */ \
    (((c) == 'x') || ((c) == 'X'))


static int32 read_floating(int32 k)
{   int32 flag = NUM_FLOAT;
    while (isdigit(curchar))
    {   if (k < NAMEMAX)
        {   namebuf[k++] = curchar;
            nextchar();
        }
        else
        {   cc_err(lex_err_overlong_fp);
            while (isdigit(curchar)) nextchar();
        }
    }
    if (is_e(curchar))
    {
        namebuf[k++] = 'e';  /* normalize case of the exponent mark */
        nextchar();
        if ((curchar == '+') | (curchar=='-'))
        {   namebuf[k++] = curchar;
            nextchar();
        }
        if (!isdigit(curchar))
        {   cc_err(lex_err_fp_syntax1);
            /* Assume exponent of zero */
            namebuf[k++] = '0';
        }
        else
        {   while (isdigit(curchar))
            {   if (k < NAMEMAX)
                {   namebuf[k++] = curchar;
                    nextchar();
                }
                else
                {   cc_err(lex_err_overlong_fp);
                    while (isdigit(curchar)) nextchar();
                }
            }
        }
    }
    /* note that calls ensure that k > 0 here. */
    namebuf[k] = '\0';
    switch (curchar)
    {   case 'l': case 'L': flag |= NUM_LONG; nextchar(); break;
        case 'f': case 'F': flag |= NUM_SHORT; nextchar(); break;
    }
/* Note that a fp number ending in 'E' above has already been diagnosed */
    lex_check_pp_number();
    return flag;
}

static AEop read_number(int radix)
{   int32 flag = NUM_INT, k = 0;        /* namebuf useful to collect chars */
    if (radix == 16)
    {   while (isxdigit(curchar))
        {   if (k < NAMEMAX)
            {   namebuf[k++] = curchar;
                nextchar();
            }
            else
            {   cc_err(lex_err_overlong_hex);
                while (isxdigit(curchar)) nextchar();
            }
        }
        if (k==0)
        {   cc_err(lex_err_need_hex_dig);
            namebuf[k++] = '0';         /* treat as 0x0 */
        }
        namebuf[k] = '\0';
/* ANSI (Dec 88 draft) require a diagnostic for 0xee+1 or 0xee+spqr.    */
        if (is_e(namebuf[k-1]) && (curchar == '+' || curchar == '-'))
            cc_ansi_rerr(lex_rerr_hex_exponent);
    }
    else
    {   while (isdigit(curchar))
        {   if (k < NAMEMAX)
            {   namebuf[k++] = curchar;
                nextchar();
            }
            else
            {   cc_err(lex_err_overlong_int);
                while (isdigit(curchar)) nextchar();
            }
        }
        if (curchar=='.')
        {   nextchar();
            if (k == 0) namebuf[k++] = '0'; /* consider '0.' */
            namebuf[k++] = '.';
            flag = read_floating(k);
        }
        else if (is_e(curchar))
        {   if (k == 0) namebuf[k++] = '0'; /* consider '0e5' */
            flag = read_floating(k);
        }
        else
        {   if (k == 0) namebuf[k++] = '0'; /* consider '0'   */
            namebuf[k] = '\0';
        }
    }
    if (flag & NUM_FLOAT) return make_floating(namebuf,flag);
    for (;;)
    {
        if (curchar == 'l' || curchar == 'L') {
            if (!HasFeature(Feature_Fussy) && (flag & NUM_LONG)) {
                flag ^= NUM_LONG|NUM_LONGLONG; nextchar(); continue;
            } else if (!(flag & (NUM_LONGLONG|NUM_LONG))) {
                flag |= NUM_LONG; nextchar(); continue;
            }
        }
        if ((curchar == 'u' || curchar == 'U') && !(flag & NUM_UNSIGN))
        {   flag |= NUM_UNSIGN; nextchar(); continue;
        }
        lex_check_pp_number();
        return make_integer(radix, flag);
    }
}

/* string and char reading (unified reading & semantic routines) ... */

/* The wide character support below supports wchar_t == target int.     */
/* You can change this via mip/defaults.h.                              */
static unsigned32 lex_string_insert(char *where, int size, unsigned32 what)
{   switch (size)
    {   case 4: {   uint32 val = what;
                    if (target_lsbytefirst != host_lsbytefirst) {
                      val =   ((what & 0xff) << 24)
                            | ((what & 0xff00) << 8)
                            | ((what & 0xff0000) >> 8)
                            | (what >> 24);
                    }
                    *(uint32 *)where = val;
                    return what;
                }
        case 2: {   uint16 val = (uint16)what;
                    if (target_lsbytefirst != host_lsbytefirst) {
                      val =   ((what & 0xff) << 8)
                            | (what >> 8);
                    }
                    *(uint16 *)where = val;
                    return (uint16)what;
                }
        case 1: return *(uint8 *)where = (uint8)what;
        default: syserr(syserr_lex_string); return what;
    }
}

static bool lex_string_char(char *where, int size, bool escaped)
/* read a possibly escaped (with backslash (\)) character for a           */
/* character or string literal (possibly wide).  If read succeeds         */
/* result is placed in where (if char) and (<size> *)where (if wide char).*/
/* Caller aligns if wide.  Result is 1 if succeeds, 0 if null escape read */
{
    int ch = curchar;
    if (escaped) switch (ch)     /* (next character has already been read) */
    {
case 'a':       ch = BELL;      break;  /* attn (otherwise known as bell) */
case 'b':       ch = '\b';      break;  /* backspace                      */
case 'f':       ch = CHAR_FF;   break;  /* form feed                      */
case 'n':       ch = CHAR_NL;   break;  /* newline                        */
case 'r':       ch = CHAR_CR;   break;  /* carriage return                */
case 't':       ch = '\t';      break;  /* (horizontal) tab               */
case 'v':       ch = CHAR_VT;   break;  /* vertical tab                   */

case '\\':      ch = '\\';      break;  /* backslash                      */
case '\'':      ch = '\'';      break;  /* single quote mark              */
case '\"':      ch = '\"';      break;  /* double quote mark              */
case '?':       ch = '?';       break;  /* '?' in case \?\?\? is needed   */

case 'x':
        {   bool ovfl = 0;
            unsigned32 escch, resultch;
            if (!isxdigit(ch = nextchar()))
            {   cc_err(lex_err_need_hex_dig1);
                ch = 'x';
                goto return_ch;       /* "\xg" -> "xg": any better ideas? */
            }
            escch = intofxdigit(ch);
            /* ANSI (3rd review draft) say any any number of digits.      */
            while (isxdigit(nextchar()))
            {   if (((escch << 4) >> 4) != escch) ovfl = 1;
                escch = (escch<<4) + intofxdigit(curchar);
            }
            /* Never translate \x escapes.                                */
            resultch = lex_string_insert(where, size, escch);
            if (ovfl || escch != resultch)    /* constraint violation     */
                cc_rerr(lex_rerr_esc16_truncated, ovfl ? "...": "",
                        (long)escch, (long)resultch);
            return 1;
        }

case '0':       case '1':
case '2':       case '3':               /* octal escapes                  */
case '4':       case '5':
case '6':       case '7':
/* This code is simpler than that for \x since 3 digits make overflow hard */
        {   unsigned32 resultch;
            unsigned escch = intofdigit(ch);
            if (isodigit(nextchar()))       /* second & third digits  */
            {   escch = (escch<<3) + intofdigit(curchar);
                if (isodigit(nextchar())) {
                    escch = (escch<<3) + intofdigit(curchar);
                    nextchar();
                }
            }
            /* Never translate \ooo escapes.                              */
            resultch = lex_string_insert(where, size, escch);
            if (escch != resultch)                /* constraint violation */
                cc_rerr(lex_rerr_esc8_truncated, escch, (int)resultch);
            return 1;
        }

/* note that the sequence \<nl> (but not \<space><nl>) is now removed at
   all possible occasions by the preprocessor.   However, code for handling
   such situations is left here so that \<space><nl> is removed with just a
   warning message.
   Moreover we have to take care that (e.g.) \\<nl><nl> gives an error.
*/
case ' ':  /* In pcc mode, allow '\ ' to appease XOpen test suite */
           if (HasFeature(Feature_PCC)) break;
case '\t':
           cc_err(lex_err_backslash_blank);

/* If I see \<space> I generate a warning message. I then skip over any
 * following whitespace, up to one newline.  Thus the effect is that
 * \(space|tab)*(nl|) are ignored just as \nl.
 */
           do nextchar(); while ((curchar==' ') || (curchar=='\t'));
           if (curchar=='\n') nextchar();
case '\n': /* drop through.  note no nextchar() here so read_string()
              will give an error message. */
           return 0;

default:  /* pp.c removes control chars if !Feature_PCC */
          cc_ansi_rerr(lex_rerr_illegal_esc, (int)ch, (int)ch);
          break;      /* i.e. treat unknown escape "\Q" as "Q"            */
    }
    nextchar();
    /* note the next line translates all chars except \ooo and \xooo */
return_ch:
    (void)lex_string_insert(where, size, char_translation(ch));
    return 1;
}

static void read_string(int quote, AEop type, bool lengthwanted)
{   char *symstrp = lex_strptr, *val = lex_strptr;
#ifdef EXTENSION_COUNTED_STRINGS
    bool isCountedString = NO;
    if (lengthwanted) {
        curchar = 0;
        isCountedString = YES;
    } else
#else
    IGNORE(lengthwanted);
#endif
    nextchar();
    while (curchar!=quote)
    {   bool escaped = curchar == '\\';
        if ((curchar=='\n') || (curchar==PP_EOF))
        {   cc_err(lex_err_unterminated_string);
            break;   /* slightly untidy about nextchar() below, but OK */
        }
/* If I run off the end of this segment of lex_strbuf I allocate another  */
/* and copy the part-string into it, doubling the size if necessary.      */
        if (symstrp >= lex_strend)
        {   size_t n = symstrp - val, allocsize = LEX_STRBUFSIZE;
            while (n*2 > allocsize) allocsize *= 2;
            {   char *oval = val;
                val = (char *)BindAlloc(allocsize);
                if (n != 0) memcpy(val, oval, n);
                lex_strptr = symstrp = val + n;
                lex_strend = val + allocsize;
            }
        }
        if (escaped) nextchar();
#ifdef EXTENSION_COUNTED_STRINGS
        if (val == symstrp && escaped && curchar == 'p' &&
            HasFeature(Feature_AllowCountedStrings))
        { /* "\p" at start of string */
            isCountedString = YES;
#ifdef EXTENSION_UNSIGNED_STRINGS
            if (type == s_string) type = s_ustring;
#endif
            escaped = NO;  /* discard the '\' : 'p' will be planted in the */
                           /* string and overwritten at the end            */
        }
#endif
        if (lex_string_char(symstrp, (type == s_wstring ? sizeof_wchar : 1),
                            escaped))
            symstrp += (type == s_wstring ? sizeof_wchar : 1);
    }
    nextchar();
    if (quote == '"')
    {   curlex.a2.len = symstrp - val;
#ifdef EXTENSION_COUNTED_STRINGS
        if (isCountedString)  /* treat wide strings rationally        */
            lex_string_insert(val, (type == s_wstring ? sizeof_wchar : 1),
                              curlex.a2.len-1);
#endif
        lex_strptr = &val[pad_to_word(curlex.a2.len)];   /* commit usage */
        curlex.a1.s = val;
        curlex.sym = type;
    }
    else
    {   int32 k = 0, n = symstrp - val;
/* note that for char constants we do not commit symstrp to lex_strptr */
/* The following line deals host-independently with single char        */
/* constants, at least if host char is 8 bits.                         */
        if (type == s_wstring)
        {   if (n != sizeof_wchar) cc_rerr(lex_rerr_not1wchar);
            if (n != 0)
            {   if (sizeof_wchar == 4)
                {   k = *(uint32 *)val;
                    if (target_lsbytefirst != host_lsbytefirst) {
                        k =   ((k & 0xff) << 24)
                            | ((k & 0xff00) << 8)
                            | ((k & 0xff0000) >> 8)
                            | (k >> 24);
                    }
                } else {
                    k = *(uint16 *)val;
                    if (target_lsbytefirst != host_lsbytefirst) {
                        k =   ((k & 0xff) << 8)
                            | (k >> 8);
                    }
                }
            }
        }
        else if (n == 1)
            k = HasFeature(Feature_SignedChar) ? *(int8 *)val
                                               : *(unsigned8 *)val;
        else
        {   /* The effect of n>1 is implementation-defined */
            int32 i;
            if (n == 0)
                cc_rerr(lex_rerr_empty_char);
            else if (n > sizeof_int)
                cc_rerr(lex_rerr_overlong_char), n = sizeof_int;
            else if (!SuppressDB_Has(Suppress_MultiChar))
                cc_warn(lex_warn_multi_char);
            /* The following code follows pcc, and is host independent  */
            /* but assembles bytes 'backwards' on 68000-sex machines.   */
            /*   (It agrees with previous code on intel-sex hosts.)     */
            /* It is arguable that we should sign-extend the last char  */
            /* (only!) if Feature_SignedChar (merges in n==1 case).    */
            for (i=0; i<n; i++)
                k = (unsigned32)k << 8 | ((unsigned8 *)val)[i];
            if (sizeof_int == 2) k = (int16)k;  /* normalise, eg for cmp.   */
        }
        curlex.a1.i = k;
        curlex.a2.flag = (type == s_wstring) ? NUM_WCHAR : NUM_CHAR;
                                      /* perhaps NUM_INT|NUM_LONG if n=4?   */
        curlex.sym = s_integer;       /* chars give produce int consts.     */
/* returning s_character/s_wcharacter would improve messages for int'a';    */
    }
}

#define CPP_word 256      /* identifier (but warned) for C, keyword for C++ */
#define CPP_word2 512     /* keyword for C++, but currently warned+ident.   */
#define CPP_word3 1024    /* keyword for C++, but currently warn that       */
                          /* feature is not fully implemented.              */

static AEop next_basic_sym(void)
/* all of nextsym() except debug info */
{   unsigned32 charinfo;
    int32 savechar;
    FileLine startofsym_fl;

    if (endofsym_fl.filepos != -1 && !pp_inhashif)
        curlex.fl = endofsym_fl;

    if (curchar == NOTACHAR) nextchar();
    startofsym_fl = curlex.fl;
    for (;;)
    {   if (curchar == PP_EOF)  return (curlex.sym = s_eof);
        if (!isspace(curchar)) break;
        if (curchar == '\n')
        {
            if (pp_inhashif) return (curlex.sym = s_eol);
#ifdef TARGET_HAS_INLINE_ASSEMBLER
            if (asm_mode == ASM_BLOCK)
            {
                endofsym_fl = curlex.fl;        /* save for next call */
                curlex.fl.l--;                  /* move back to current line */
                curchar = NOTACHAR;
                return (curlex.sym = s_eol);
            }
#endif
        }
        nextchar();
    }
    /* Not just startofsym_fl = curlex.fl below, because we want the column
       to be that of the first whitespace character preceding the symbol on
       the same line, not that of the first character of the symbol (so that
       a debugger may see the whitespace preceding a statement as part of it).
     */
    if (startofsym_fl.l != curlex.fl.l)
    {   startofsym_fl = curlex.fl;
        startofsym_fl.column = 1;
    }
    switch ((charinfo = lexclass_(curchar)) & LEX_CHTYPE)
    {
default:    if (curchar == '#' || curchar == '\\')
                cc_err(lex_err_bad_hash, (int)curchar);
            else if (isprint(curchar))  /* can only happen if Feature_PCC */
                 cc_err(lex_err_bad_char, (long)curchar, (int)curchar);
            else cc_err(lex_err_bad_noprint_char, (int)curchar);
            nextchar();
            next_basic_sym();
            break;
case l_idstart:
        {   int k = 0;          /* number of characters read */
            do
            {   if (k < NAMEMAX)
                {
                    namebuf[k++] = curchar;
                }
                nextchar();
            } while (lexclass_(curchar) & l_idcont);
            namebuf[k] = 0;
/* Check if ANSI wide string/char -- illegal syntax in olde-C.             */
            if (k == 1 && namebuf[0] == 'L'
                       && (curchar == '"' || curchar == '\''))
                read_string(curchar, s_wstring, NO);
#ifdef EXTENSION_UNSIGNED_STRINGS
            else if (k == 1 && namebuf[0] == 'U' && curchar == '"')
                read_string(curchar, s_ustring, NO);
            else if (k == 1 && namebuf[0] == 'B' && curchar == '"')
                read_string(curchar, s_ustring, YES);
#endif
            else
            {   int32 type;
                curlex.a1.sv = sym_lookup(namebuf, SYM_GLOBAL);
                type = symtype_(curlex.a1.sv);
/* To prepare for C++, give a warning ONCE per file in ANSI mode when a */
/* C++ keyword is used as a C identifier.                               */
                if (type & (CPP_word|CPP_word2|CPP_word3)) {
                    if (LanguageIsCPlusPlus)
                    {   if (type & CPP_word2)
                        {   symtype_(curlex.a1.sv) = type = s_identifier;
                            cc_ansi_warn(lex_warn_cplusplusid, curlex.a1.sv);
                        } else if (type & CPP_word3) {
                          /* Temporary check for C++ features that are known */
                          /* to not be fully implemented. Will go away when  */
                          /* C++ implementation has progressed. AC           */
                          symtype_(curlex.a1.sv) = s_identifier;
                          cc_ansi_warn(lex_warn_cplusplusimpl, curlex.a1.sv);
                          symtype_(curlex.a1.sv) = type = type^CPP_word3;
                        }
                    }
                    else {
                        int32 tflag = type & (CPP_word|CPP_word2);
                        symtype_(curlex.a1.sv) = type = s_identifier;
#ifndef FOR_ACORN
                        if (tflag != (CPP_word|CPP_word2))
                            /* don't warn for wchar_t which appears       */
                            /* stdlib.h and stddef.h in C mode.           */
                            cc_ansi_warn(lex_warn_cplusplusid, curlex.a1.sv);
#endif
                    }
                }
/* There are no keywords during pp (including #if), following ANSI/Reiser. */
/* Consider adding a new s_ppidentifier which could aid lex.c.             */
#ifdef ALLOW_KEYWORDS_IN_HASHIF
                curlex.sym = type;
#else
                curlex.sym = pp_inhashif ? s_identifier : type;
#endif
                curlex.a2.flag = 0;
#ifdef EXTENSION_VALOF
/* The following represents a rather nasty piece of context-sensitive      */
/* hackery - inside a valof block the word 'resultis' is recognized as a   */
/* keyword, but otherwise (as required in regular ANSI C) it is just       */
/* another ordinary symbol. I wonder if there is a better solution to this */
/* issue........... ??                                                     */
                if (inside_valof_block && curlex.sym == s_identifier &&
                    curlex.a1.sv == resultisword) curlex.sym = s_resultis;
#endif
            }
            break;
        }
case l_digit0:                  /* octal or hex or floating     */
            nextchar();         /* N.B. initial 0 not buffered  */
            if (is_x(curchar))
            {   nextchar();
                curlex.sym = read_number(16);   /* hex */
            }
            else
                curlex.sym = read_number(8);    /* octal or float */
            break;
case l_digit1:                  /* decimal int or floating */
            curlex.sym = read_number(10);
            break;
case l_dot:     nextchar();

                if (curchar == '*')
                        curlex.sym = s_dotstar,
                        curchar = NOTACHAR;
                else

                if (isdigit(curchar))
                {   int32 flag, k = 0;
                    namebuf[k++] = '.';
                    namebuf[k++] = curchar;
                    nextchar();
                    flag = read_floating(k); /* change to use read_number()? */
                    curlex.sym = make_floating(namebuf, flag);
                }
                else
                {   int32 n = 1;
                    while (curchar=='.') n++, nextchar();
                    switch (n)
                    {   case 1: curlex.sym = s_dot; break;
                        default: cc_err(lex_err_ellipsis);
                                /* drop through */
                        case 3: curlex.sym = s_ellipsis; break;
                    }
                }
                break;
case l_noglue:
                curlex.sym = charinfo >> 8 & 255;
                curchar = NOTACHAR;
                break;
case l_eqglue:  nextchar();
                if (curchar == '=')
                    curlex.sym = charinfo >> 16,
                    curchar = NOTACHAR;
                else curlex.sym = charinfo >> 8 & 255;
                break;
case l_selfglue:
                savechar = curchar;
                nextchar();
                if (curchar == savechar)
                    curlex.sym = charinfo >> 16 & 255,
                    curchar = NOTACHAR;
                /* all selfgluer's '+' have a '+=' form except C++ ':=' */
                else if (curchar == '=' && (charinfo >> 24) != 0)
                    curlex.sym = charinfo >> 24,
                    curchar = NOTACHAR;
                else curlex.sym = charinfo >> 8 & 255;
                break;
case l_less:    nextchar();
                if (curchar == ':')
                {   curlex.sym = s_lbracket;
                    curchar = NOTACHAR;
                } else if (curchar == '%')
                {   curlex.sym = s_lbrace;
                    curchar = NOTACHAR;
                } else
                {   savechar = '<';
                    goto handleshift;
                }
                break;
case l_shifter: savechar = curchar;            /* very much like l_selfglue */
                nextchar();                    /* (32 bits is too few)      */
handleshift:
                if (curchar == '=')
                    curlex.sym = charinfo >> 24,
                    curchar = NOTACHAR;
                else if (curchar == savechar)
                {   curlex.sym = charinfo >> 16 & 255;
                    nextchar();
                    if (curchar == '=')
                        curlex.sym = assignop_(curlex.sym), /* >> to >>= etc */
                        curchar = NOTACHAR;
                }
                else curlex.sym = charinfo >> 8 & 255;
                break;
case l_minus:   nextchar();   /* l_selfglue but for "->", (C++)"->*". */
                if (curchar=='-')
                    curlex.sym = s_minusminus,
                    curchar = NOTACHAR;
                else if (curchar=='>')
                  { nextchar();

                    if (curchar=='*')
                        curlex.sym = s_arrowstar,
                        curchar = NOTACHAR;
                    else

                        curlex.sym = s_arrow;
                  }
                else
                  {
                    if (curchar=='=')
                        curlex.sym = s_minusequal,
                        curchar = NOTACHAR;
                    else curlex.sym = s_minus;
                  }
                break;
case l_colon:   nextchar();
                if (curchar == '>')
                    curlex.sym = s_rbracket,
                    curchar = NOTACHAR;
                else
                    curlex.sym = s_colon;
                break;
case l_coloncpp: nextchar();
                if (curchar == '>')
                    curlex.sym = s_rbracket,
                    curchar = NOTACHAR;
                else if (curchar == ':')
                    curlex.sym = s_coloncolon,
                        curchar = NOTACHAR;
                else
                    curlex.sym = s_colon;
                break;
case l_percent: nextchar();
                if (curchar == '>')
                    curlex.sym = s_rbrace,
                    curchar = NOTACHAR;
                else if (curchar == '=')
                    curlex.sym = s_remequal,
                    curchar = NOTACHAR;
                else
                    curlex.sym = s_rem;
                break;
case l_quote1:  read_string(curchar, s_string, NO);
                break;
case l_quote2:
#ifndef TARGET_HAS_INLINE_ASSEMBLER
                read_string(curchar, s_string, NO);
                break;
#else
                if (asm_mode != ASM_STRING)
                {   in_asm_string = NO;
                    read_string(curchar, s_string, NO);
                }
                else
                {   in_asm_string = !in_asm_string;
                    curchar = NOTACHAR;
                    curlex.sym = s_quote;
                }
                break;
case l_hash:    if (asm_mode == ASM_STRING || asm_mode == ASM_BLOCK)
                {   curlex.sym = s_hash;
                    curchar = NOTACHAR;
                }
                else
                {   cc_err(lex_err_bad_hash, (int)curchar);
                    nextchar();
                    next_basic_sym();
                }
                break;
#endif  /* TARGET_HAS_INLINE_ASSEMBLER */
    }
    if (can_have_becomes(curlex.sym) && HasFeature(Feature_PCC))
    {   /* recognise whitespace (but NOT newlines) in += etc */
        /* as a sop to olde-style (K&R) C.                   */
        /* BEWARE & = and * = in C++ default argument lists. */
        /* So, this may only be done in cc -pcc mode...      */
        if (curchar == NOTACHAR) nextchar();
        while (curchar == ' ' || curchar == '\t') nextchar();
        if (curchar == '=')
        {   curlex.sym = and_becomes(curlex.sym);
            curchar = NOTACHAR;
        }
    }
    endofsym_fl = curlex.fl;     /* save for next call */
    if (!pp_inhashif)
      curlex.fl = startofsym_fl; /* reset to start of symbol */
    return curlex.sym;
}


void ungetsym(void)
{   if (nextlex.sym != s_nothing) syserr("too many ungetsyms");
    if (debugging(DEBUG_LEX))
        cc_msg("<ungetsym: $l>\n");
    nextlex = curlex;    /* Surprisingly, this copying is as efficient */
                         /* as pointer juggling - perhaps more so.     */
    if (pp_inhashif) curlex = prevlex_hif; else curlex = prevlex;
}

AEop nextsym(void)
/* sets curlex.sym to next symbol */
{
    errs_on_this_sym = 0;
    if (pp_inhashif) prevlex_hif = curlex; else prevlex = curlex;
    if (nextlex.sym != s_nothing)
    {   curlex = nextlex;
        nextlex.sym = s_nothing;
    }
    else
    {   if (LanguageIsCPlusPlus && !pp_inhashif && nextsym_lookaside != NULL)
            lex_getbodysym();
        else
            next_basic_sym();
        if (LanguageIsCPlusPlus && !pp_inhashif && nextsym_put_handle >= 0)
            lex_putbodysym();
    }
    if (debugging(DEBUG_LEX))
        {   cc_msg("<nextsym: $l");
            if (LanguageIsCPlusPlus && !pp_inhashif)
            {   if (nextsym_lookaside != NULL)
                    cc_msg(" from [%d]", (int)(nextsym_lookaside - lexbuf_vec));
            }
            cc_msg(">\n");
        }
    return curlex.sym;
}

AEop nextsym_for_hashif(void)
{   curchar = NOTACHAR;   /* could only have been '\n' or NOTACHAR */
    return nextsym();
}

/* exported initialiser lex_init() is language dependent ... */

static void setuplexclass1(char *s, unsigned32 l)
{   unsigned char ch;
    while ((ch = *s++) != 0) lexclass_(ch) = l | l_idcont;
}

static void init_sym_name_table(void)
{   /* add entries for error messages for non-reserved words, e.g. block */
    /* (currently) non-table driven... */
    sym_name_table[s_error]       = msg_lookup(errname_error);       /* <previous error> */
    sym_name_table[s_invisible]   = msg_lookup(errname_invisible);   /* <invisible> */
    sym_name_table[s_let]         = msg_lookup(errname_let);         /* <let> */
    sym_name_table[s_character]   = msg_lookup(errname_character);   /* <character constant> */
    sym_name_table[s_wcharacter]  = msg_lookup(errname_wcharacter);  /* <wide character constant> */
    sym_name_table[s_boolean]     = msg_lookup(errname_boolean);     /* <boolean constant> */
    sym_name_table[s_integer]     = msg_lookup(errname_integer);     /* <integer constant> */
    sym_name_table[s_int64con]    = msg_lookup(errname_int64con);    /* <integer constant> */
    sym_name_table[s_floatcon]    = msg_lookup(errname_floatcon);    /* <floating constant> */
    sym_name_table[s_string]      = msg_lookup(errname_string);      /* <string constant> */
    sym_name_table[s_wstring]     = msg_lookup(errname_wstring);     /* <wide string constant> */
    sym_name_table[s_identifier]  = msg_lookup(errname_identifier);  /* <identifier> */
    sym_name_table[s_pseudoid]    = msg_lookup(errname_identifier);  /* <identifier> */
    sym_name_table[s_binder]      = msg_lookup(errname_binder);      /* <variable> */
    sym_name_table[s_tagbind]     = msg_lookup(errname_tagbind);     /* <struct/union tag> */
    sym_name_table[s_cond]        = msg_lookup(errname_cond);        /* _?_:_ */
    sym_name_table[s_displace]    = msg_lookup(errname_displace);    /* ++ or -- */
    sym_name_table[s_postinc]     = msg_lookup(errname_postinc);     /* ++ */
    sym_name_table[s_postdec]     = msg_lookup(errname_postdec);     /* -- */
    sym_name_table[s_arrow]       = msg_lookup(errname_arrow);       /* -> */
    sym_name_table[s_arrowstar]   = msg_lookup(errname_arrowstar);   /* ->* */
    sym_name_table[s_dotstar]     = msg_lookup(errname_dotstar);     /* .* */
    sym_name_table[s_ctor]        = msg_lookup(errname_constructor); /* <constructor> */
    sym_name_table[s_dtor]        = msg_lookup(errname_destructor);  /* <destructor> */
    sym_name_table[s_addrof]      = msg_lookup(errname_addrof);      /* unary & */
    sym_name_table[s_content]     = msg_lookup(errname_content);     /* unary * */
    sym_name_table[s_monplus]     = msg_lookup(errname_monplus);     /* unary + */
    sym_name_table[s_neg]         = msg_lookup(errname_neg);         /* unary - */
    sym_name_table[s_fnap]        = msg_lookup(errname_fnap);        /* <function argument> */
    sym_name_table[s_subscript]   = msg_lookup(errname_subscript);   /* <subscript> */
    sym_name_table[s_cast]        = msg_lookup(errname_cast);        /* <cast> */
    sym_name_table[s_sizeoftype]  = msg_lookup(errname_sizeoftype);  /* sizeof */
    sym_name_table[s_sizeofexpr]  = msg_lookup(errname_sizeofexpr);  /* sizeof */
    sym_name_table[s_ptrdiff]     = msg_lookup(errname_ptrdiff);     /* - */   /*  for (a-b)=c msg */
    sym_name_table[s_endcase]     = msg_lookup(errname_endcase);     /* break */
    sym_name_table[s_block]       = msg_lookup(errname_block);       /* <block> */
    sym_name_table[s_decl]        = msg_lookup(errname_decl);        /* decl */
    sym_name_table[s_fndef]       = msg_lookup(errname_fndef);       /* fndef */
    sym_name_table[s_typespec]    = msg_lookup(errname_typespec);    /* typespec */
    sym_name_table[s_typedefname] = msg_lookup(errname_typedefname); /* typedefname */
#ifdef EXTENSION_VALOF
    sym_name_table[s_valof]       = msg_lookup(errname_valof);       /* valof */
#endif
    sym_name_table[s_ellipsis]    = msg_lookup(errname_ellipsis);    /* ... */
    sym_name_table[s_eol]         = msg_lookup(errname_eol);         /* \\n */
    sym_name_table[s_eof]         = msg_lookup(errname_eof);         /* <eof> */
#ifdef RANGECHECK_SUPPORTED
    sym_name_table[s_rangecheck]  = msg_lookup(errname_rangecheck);  /* <rangecheck> */
    sym_name_table[s_checknot]    = msg_lookup(errname_checknot);    /* <check> */
#endif
    sym_name_table[s_init]        = msg_lookup(errname_init);        /* = */
}

void lex_init()         /* C version  */
{
    int32 i;
    static const struct { unsigned32 lc; char name[2], name1[3], name2[3]; }
      sp[] = {
        { mklc(l_noglue, s_lpar, 0, 0),      "(" },
        { mklc(l_noglue, s_rpar, 0, 0),      ")" },
        { mklc(l_noglue, s_lbracket, 0, 0),  "[" },
        { mklc(l_noglue, s_rbracket, 0, 0),  "]" },
        { mklc(l_noglue, s_lbrace, 0, 0),    "{" },
        { mklc(l_noglue, s_rbrace, 0, 0),    "}" },
        { mklc(l_noglue, s_semicolon, 0, 0), ";" },
        { mklc(l_noglue, s_comma, 0, 0),     "," },
        { mklc(l_noglue, s_bitnot, 0, 0),    "~" },
        { mklc(l_noglue, s_cond, 0, 0),      "?" },
        /* now the assignable nongluers */
        { mklc(l_eqglue, s_times, s_timesequal, 0), "*", "*=" },
        { mklc(l_eqglue, s_div, s_divequal, 0),     "/", "/=" },
        { mklc(l_percent,s_rem, s_remequal, 0),     "%", "%=" }, /* charinfo not really used */
        { mklc(l_eqglue, s_xor, s_xorequal, 0),     "^", "^=" },
        { mklc(l_eqglue, s_boolnot, s_notequal, 0), "!", "!=" },
        /* now the self-gluers (only the single form is assignable) */
        { mklc(l_selfglue, s_assign, s_equalequal, s_equalequal),
                                                    "=", "==", "==" },
        { mklc(l_selfglue, s_and,  s_andand, s_andequal),
                                                    "&", "&&", "&=" },
        { mklc(l_selfglue, s_or,   s_oror, s_orequal),
                                                    "|", "||", "|=" },
        { mklc(l_selfglue, s_plus, s_plusplus, s_plusequal),
                                                    "+", "++", "+=" },
        /* shifts/relops - both the single and double form is assignable */
        { mklc(l_less, s_less, s_leftshift, s_lessequal),
                                                         "<", "<<", "<=" },
        { mklc(l_shifter, s_greater, s_rightshift, s_greaterequal),
                                                         ">", ">>", ">=" },
        /* magic chars - 1 per class */
        { mklc(l_quote1, 0, 0, 0),       "'" },
        { mklc(l_quote2, s_quote, 0, 0),       "\"" },
        { mklc(l_minus,  s_minus, s_minusminus, s_minusequal),
                                                    "-", "--", "-=" },
        { mklc(l_dot,    s_dot, 0, 0),   "." },
        { mklc(l_colon,  s_colon, 0, 0), ":" }, /* charinfo not really used */
        { mklc(l_hash,   s_hash, 0, 0),  "#" }


    };
    static const struct keyword { const char *name; AEop sym; } ns[] = {
/* ANSI keywords which also were in PCC.                                */
        { "auto",     s_auto },
        { "break",    s_break },
        { "case",     s_case },
        { "char",     s_char },
        { "continue", s_continue },
        { "default",  s_default },
        { "do",       s_do },
        { "double",   s_double },
        { "else",     s_else },
        { "enum",     s_enum },
        { "extern",   s_extern },
        { "float",    s_float },
        { "for",      s_for },
        { "goto",     s_goto },
        { "if",       s_if },
        { "int",      s_int },
        { "long",     s_long },
        { "register", s_register },
        { "return",   s_return },
        { "short" ,   s_short },
        { "sizeof",   s_sizeof },
        { "static",   s_static },
        { "struct",   s_struct },
        { "switch",   s_switch },
        { "typedef",  s_typedef },
        { "union",    s_union },
        { "unsigned", s_unsigned },
        { "void",     s_void },
        { "while",    s_while },
/* C extension:                                                         */
        { "__int64", s_longlong},
/* specials to help the compiler/library.                               */
        { "___toplevel",s_toplevel },
        { "___type",  s_typestartsym },
        { "___typeof",s_typeof },
        { "___weak",  s_weak },
        { "__pure",    s_pure },
        { "__value_in_regs", s_structreg },
        { "__packed", s_unaligned},
        { "__opaque", s_opaque },
#ifdef TARGET_HAS_INLINE_ASSEMBLER
        { "__asm",    s_asm },
#endif
#ifdef TARGET_IS_ARM_OR_THUMB
        { "__swi",    s_swi },
        { "__swi_indirect", s_swi_i },
#else
        /* give traps reasonable names on Unix... */
        { "__systrap",s_swi },
        { "__systrap_indirect", s_swi_i },
#endif
        { "__irq", s_irq },
        { "__global_reg", s_globalreg },
        { "__global_freg", s_globalfreg },
        { "__inline",   s_inline }
#ifdef EXTENSION_VALOF
        , { "resultis", s_resultis }
#endif
    };
    static const struct keyword ns2[] = {
/* The following are ANSI C keywords, but old PCC (unix) sources        */
/* (compile with -pcc -fussy) may treat them as identifiers!            */
        { "const",    s_const },
        { "signed",   s_signed },
        { "volatile", s_volatile }
    };
    static const struct keyword ns3[] = {
/* C++ only keywords (redeclared as s_identifier on use in C mode)      */
        { "asm",      CPP_word|s_asm },
        { "bool",     CPP_word|s_bool },
        { "catch",    CPP_word|s_catch },
        { "class",    CPP_word|s_class },
        { "delete",   CPP_word|s_delete },
        { "false",    CPP_word|s_false },
        { "friend",   CPP_word|s_friend },
        { "inline",   CPP_word|s_inline },
        { "new",      CPP_word|s_new },
        { "operator", CPP_word|s_operator },
        { "private",  CPP_word|s_private },
        { "protected",CPP_word|s_protected },
        { "public",   CPP_word|s_public },
        { "template", CPP_word|s_template },
        { "this",     CPP_word|s_this },
        { "throw",    CPP_word3|s_throw },
        { "true",     CPP_word|s_true },
        { "try",      CPP_word|s_try },
        { "virtual",  CPP_word|s_virtual },
        { "typename", CPP_word|s_typename },
        { "export",   CPP_word|s_export },
/* ANSI C++ draft 950428 adds operator alternative representations...     */
/* minor nit:  these will appear tranformed in error messages */
        { "bitand",   CPP_word|s_and },
        { "and",      CPP_word|s_andand },
        { "bitor",    CPP_word|s_or },
        { "or",       CPP_word|s_oror },
        { "xor",      CPP_word|s_xor },
        { "compl",    CPP_word|s_bitnot },
        { "and_eq",   CPP_word|s_andequal },
        { "or_eq",    CPP_word|s_orequal },
        { "xor_eq",   CPP_word|s_xorequal },
        { "not",      CPP_word|s_boolnot },
        { "not_eq",   CPP_word|s_notequal },
/* ANSI C++ draft 950428 adds the following keywords (just warn for now). */
/* CPP_word3 indicates partial implementation.                            */
        { "const_cast",       CPP_word3|s_const_cast },
        { "dynamic_cast",     CPP_word3|s_dynamic_cast },
        { "mutable",          CPP_word2|s_error },
        { "namespace",        CPP_word2|s_error },
        { "reinterpret_cast", CPP_word3|s_reinterpret_cast },
        { "static_cast",      CPP_word3|s_static_cast },
        { "typeid",           CPP_word3|s_typeid },
        { "explicit",         CPP_word2|s_error },
        { "using",            CPP_word3|s_using },
        { "wchar_t",          CPP_word|CPP_word2|s_error }
    };

  {
    char *unset=msg_lookup(errname_unset); /* for speed */
    for (i = 0; i < s_NUMSYMS; i++) sym_name_table[i] = unset;
  }
    init_sym_name_table();  /* language independent inits... */

    /* although lexclass[] is notionally constant, C's initialisation
       facilities do not conveniently enable us to initialise it... */
    for (i = 0; i <= 255; i++) lexclass[i] = l_illegal;
    setuplexclass1("ABCDEFGHIJKLMNOPQRSTUVWXYZ_", l_idstart);
    setuplexclass1("abcdefghijklmnopqrstuvwxyz",  l_idstart);
    setuplexclass1("123456789", l_digit1);
    setuplexclass1("0",         l_digit0);
    /*
     * The following line is for the sake of SUN NeWS !
     *   This is because SUN NeWS allows the use of '$'
     *   in variable names (yuk !)
     */
    if (HasFeature(Feature_PCC) || HasFeature(Feature_LimitedPCC))
        setuplexclass1("$", l_idstart);

    {   unsigned int u;
        for (u = 0; u < sizeof(ns)/sizeof(ns[0]); ++u)
        {   const char *name = ns[u].name; int32 sym = ns[u].sym;
            sym_insert(name, sym);
            sym_name_table[sym] = name;
        }
        if (!(HasFeature(Feature_PCC) && HasFeature(Feature_Fussy)))
        {   for (u = 0; u < sizeof(ns2)/sizeof(ns2[0]); ++u)
            {   const char *name = ns2[u].name; int32 sym = ns2[u].sym;
                sym_insert(name, sym);
                sym_name_table[sym] = name;
            }
            if (LanguageIsCPlusPlus || !SuppressDB_Has(Suppress_Future))
            {   for (u = 0; u < sizeof(ns3)/sizeof(ns3[0]); ++u)
                {   const char *name = ns3[u].name; int32 sym = ns3[u].sym;
                    if (LanguageIsCPlusPlus)
                        sym &= ~CPP_word;
                    sym_insert(name, sym);
                    sym_name_table[sym & ~(CPP_word|CPP_word2|CPP_word3)] = name;
                }
            }
        }
        if (!HasFeature(Feature_Fussy))
            sym_name_table[s_longlong] = "long long";
    }
    {   unsigned int u;
        for (u = 0; u < sizeof(sp)/sizeof(sp[0]); u++)
        {   const char *name = sp[u].name; unsigned32 lc = sp[u].lc;
            AEop s;
            lexclass_(*name) = lc;
            if ((s = (lc >>  8) & 255) != 0) sym_name_table[s] = name;
            if ((s = (lc >> 16) & 255) != 0) sym_name_table[s] = sp[u].name1;
            if ((s = (lc >> 24) & 255) != 0) sym_name_table[s] = sp[u].name2;
        }
        if (LanguageIsCPlusPlus)
        {   lexclass[':'] = mklc(l_coloncpp, s_colon, s_coloncolon, 0); /* charinfo not really used */
            sym_name_table[s_coloncolon] = "::";
        }
    }
#ifdef EXTENSION_VALOF
/* 'resultis' is a funny (experimental) syntax extension */
    resultisword = sym_insert_id("resultis");
#endif
    curchar = NOTACHAR; /* Kill lookahead  */
    curlex.sym = s_nothing;
    errs_on_this_sym = 0;
    lex_strend = lex_strptr = (char *)DUFF_ADDR;
    endofsym_fl.filepos = -1;  /* mark as invalid */

    lexbuf_max = 0; lexbuf_vec = (SymBuf *)DUFF_ADDR; nextsym_lookaside = 0;
    buffersym_bufidx = -1;
    nextsym_put_handle = -1;

#ifdef CPLUSPLUS
    {   restorable_names_list = NULL;
        template_old_sv = template_new_sv = NULL;
        save_names(YES);
    }
#endif
}

void lex_beware_reinit()
{   /* this routine patches the fact that an (illegal) C program of the */
    /* form 'int a = 1 "abc"' or 'f(){} "abc"' needs to be able to      */
    /* print out "abc" in an error message even though Local store will */
    /* have been clobbered by alloc_reinit().  Move it to Global store! */
    if (isstring_(curlex.sym))
    {   char *oval = curlex.a1.s;
        curlex.a1.s = (char *)GlobAlloc(SU_Other, pad_to_word(curlex.a2.len));
        memcpy(curlex.a1.s, oval, (size_t)curlex.a2.len);
    }
}

void lex_reinit()
{
    lex_strend = lex_strptr = (char *)DUFF_ADDR;   /* better to use ""? */
    nextlex.sym = s_nothing;
#ifdef CALLABLE_COMPILER
    curchar = NOTACHAR;
#endif
}

/* End of lex.c */

