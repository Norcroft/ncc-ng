/*
 * codebuf.h : target-independent part of object code generation, version 23
 * Copyright (C) Acorn Computers Ltd., 1988-1990.
 * Copyright (C) Codemist Ltd, 1988-1992.
 * Copyright (C) Advanced Risc Machines Ltd., 1991-1992.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

#ifndef _codebuf_LOADED
#define _codebuf_LOADED 1

#ifndef _defs_LOADED
#  include "defs.h"
#endif
#include "xrefs.h"

typedef struct DataDesc {
    DataInit *head, *tail;
    int32 size;
    DataXref *xrefs;
    int xrarea;

    union { int32 w32[1]; int16 w16[2]; int8 w8[4]; } wbuff;
    uint8 wpos;
    uint8 wtype;
} DataDesc;

typedef enum {
  DS_None
  , DS_ReadWrite
#ifdef CONST_DATA_IN_CODE
  , DS_Const
#endif
} DataAreaSort;

#if defined(CALLABLE_COMPILER)
#define get_datadesc_ht(head)                   ((DataInit *)0)
#define set_datadesc_ht(head,val)               ((void)0)
#define get_datadesc_size()                     ((int32) 0)
#define set_datadesc_size(val)                  ((void)0)
#define get_datadesc_xrefs()                    ((DataXref *)0)
#define set_datadesc_xrefs(val)                 ((void)0)
#define get_datadesc_xrarea()                   ((int)0)
#define set_datadesc_xrarea(val)                ((void)0)
#define get_datadesc()                          ((DataDesc *)0)
#define copy_datadesc(dest)                     ((void)0)
#define restore_datadesc(src)                   ((void)0)
#define data_size()                             ((int32)0)
#define data_head()                             ((DataInit *)0)
#define data_xrefs()                            ((DataXref *)0)
#define constdata_size()                        ((int32)0)
#define constdata_head()                        ((DataInit *)0)
#define constdata_xrefs()                       ((DataXref *)0)
#define is_constdata()                          ((bool)0)
#define SetDataArea(x)                          DS_ReadWrite
#else
extern DataInit *get_datadesc_ht(bool head);
extern void set_datadesc_ht(bool head, DataInit *val);
extern int32 get_datadesc_size(void);
extern void set_datadesc_size(int32 val);
extern DataXref *get_datadesc_xrefs(void);
extern void set_datadesc_xrefs(DataXref *val);
extern int get_datadesc_xrarea(void);
extern void set_datadesc_xrarea(int val);
extern DataDesc *get_datadesc(void);
extern void copy_datadesc(DataDesc *dest);
extern void restore_datadesc(DataDesc *src);
extern int32 data_size(void);
extern DataInit *data_head(void);
extern DataXref *data_xrefs(void);
extern DataInit *get_extable_ht(bool head);
extern void set_extable_ht(bool head, DataInit *val);
extern void set_extable_size(int32 val);
extern int32 extable_size(void);
extern DataInit *extable_head(void);
extern DataXref *extable_xrefs(void);
extern bool is_extable(void);
extern DataInit *get_exhandler_ht(bool head);
extern void set_exhandler_ht(bool head, DataInit *val);
extern void set_exhandler_size(int32 val);
extern int32 exhandler_size(void);
extern DataInit *exhandler_head(void);
extern DataXref *exhandler_xrefs(void);
extern bool is_exhandler(void);
#  ifdef CONST_DATA_IN_CODE
extern int32 constdata_size(void);
extern DataInit *constdata_head(void);
extern DataXref *constdata_xrefs(void);
extern bool is_constdata(void);
#  else
#define dataloc   (get_datadesc_size())   /* compatibility with other back ends.  */
#define datainitp (get_datadesc_ht(YES))
#define dataxrefs (get_datadesc_xrefs())
#  endif
extern DataAreaSort SetDataArea(DataAreaSort);

#endif

extern int32 code_area_idx;     /* for armcc -S -ZO ... */

extern int32 codebase;
extern struct LabelNumber *litlab;
extern int32 litpoolp;
extern int32 codep;

#ifdef TARGET_HAS_BSS
extern int32 bss_size;
#endif

/* xxx/gen.c obj.c and asm.c should now only access 'codeandflagvec'    */
/* via the macros code_xxx_() below.                                    */

/* Helper macros for segment and index calculations */
#define CODE_SEG_INDEX(q)       ((q) >> (CODEVECSEGBITS + 2))
#define CODE_BYTE_INDEX(q)      ((q) & (CODEVECSEGSIZE*4 - 1))
#define CODE_HWORD_INDEX(q)     (((q) >> 1) & (CODEVECSEGSIZE*2 - 1))
#define CODE_ELEM_INDEX(q)      (((q) >> 2) & (CODEVECSEGSIZE - 1))

/* ECN: Modified to allow non-aligned words if TARGET_HAS_HALFWORD_INSTRUCTIONS
 *      Unfortunately there are large scale assumptions elsewhere that
 *      codeandflagvec addresses an array of 32 bit words.
 */
#ifdef TARGET_HAS_HALFWORD_INSTRUCTIONS
#  define CodeFlag_t unsigned char
extern struct CodeAndFlag {
    unsigned16 code[CODEVECSEGSIZE*2];
    CodeFlag_t flag[CODEVECSEGSIZE*2];
} *codeandflagvec[CODEVECSEGMAX];

#define code_byte_(q) ((unsigned8 *)(codeandflagvec[CODE_SEG_INDEX(q)]->code)) [CODE_BYTE_INDEX(q)]
#define code_hword_(q) (codeandflagvec[CODE_SEG_INDEX(q)])->code[CODE_HWORD_INDEX(q)]
#define code_flag_(q) (codeandflagvec[CODE_SEG_INDEX(q)])->flag[CODE_HWORD_INDEX(q)]
#define code_inst_(q) (host_lsbytefirst ? \
                        (code_hword_(q) | (code_hword_(q+2) << 16)) : \
                        ((code_hword_(q) << 16) | code_hword_(q+2)))
#define set_code_inst_(q,v) (host_lsbytefirst ? \
        ((code_hword_(q) = (unsigned16)(v)), (code_hword_((q)+2) = (v) >> 16)) : \
        ((code_hword_(q) = (v) >> 16), (code_hword_((q)+2) = (unsigned16)(v))))
#else

#ifdef TARGET_HAS_BYTE_INSTRUCTIONS
#  define CodeFlag_t int32      /* dying?  */
#else
#  define CodeFlag_t unsigned char
#endif

extern struct CodeAndFlag {
    int32      code[CODEVECSEGSIZE];
    CodeFlag_t flag[CODEVECSEGSIZE];
} *codeandflagvec[CODEVECSEGMAX];

#define code_inst_(q) (codeandflagvec[CODE_SEG_INDEX(q)])->code[CODE_ELEM_INDEX(q)]
#define set_code_inst_(q,v) (code_inst_(q)=v)
#define code_flag_(q) (codeandflagvec[CODE_SEG_INDEX(q)])->flag[CODE_ELEM_INDEX(q)]
#endif // TARGET_HAS_HALFWORD_INSTRUCTIONS

#ifndef NO_ASSEMBLER_OUTPUT     /* i.e. lay off otherwise */
extern VoidStar (*(codeasmauxvec[CODEVECSEGMAX])) [CODEVECSEGSIZE];
# define code_aux_(q) (*codeasmauxvec[CODE_SEG_INDEX(q)]) [CODE_ELEM_INDEX(q)]
#endif // !NO_ASSEMBLER_OUTPUT

/* The following macros provide easy access to blocks for xxx/obj.c     */
#define code_instvec_(i)   (&(codeandflagvec[i]->code)[0])
#define code_flagvec_(i)   (&(codeandflagvec[i]->flag)[0])

#ifdef TARGET_HAS_BYTE_INSTRUCTIONS
#define code_byte_(q) ((unsigned char *)(codeandflagvec[CODE_SEG_INDEX(q)]->code)) [CODE_BYTE_INDEX(q)]
/* miserable macro to interpret int32 flags as 4 byte flags.  Hmm.      */
#define flag_byte_(q) ((unsigned char *)(codeandflagvec[CODE_SEG_INDEX(q)]->flag)) [CODE_BYTE_INDEX(q)]
#endif
extern struct LabList *asm_lablist; /* exported to xxxgen.c */

extern struct LabelNumber *nextlabel(void);

extern void labeldata(Symstr *b);
extern int32 trydeletezerodata(DataInit *previous, int32 minsize);

extern void gendcAX(Symstr *sv, int32 offset, int xrflavour);
 /* (possibly external) name + offset, flavour is xr_data or xr_code */
#ifdef CALLABLE_COMPILER
#define gendc0(n)               ((void)0)
#else
extern void gendc0(int32 nbytes);
#endif
extern void gendcI_a(int32 len, int32 val, bool aligned);
#define gendcI(len, val) gendcI_a(len, val, YES)
extern void gendcE(int32 len, FloatCon *val);
#ifdef TARGET_CALL_USES_DESCRIPTOR
extern void gendcF(Symstr *sv, int32 offset);
extern int32 genfncon(Symstr* sv);
#else /* TARGET_CALL_USES_DESCRIPTOR */
#  define gendcF(sym, off, strength) gendcAX(sym, off, xr_code|(strength))
#endif /* TARGET_CALL_USES_DESCRIPTOR */
#define gendcA(sym, off, strength) gendcAX(sym, off, xr_data|(strength))

extern void vg_genstring(StringSegList *s, int32 size, int pad);

extern void padstatic(int32 align);

#ifdef TARGET_HAS_BSS
extern void padbss(int32 align);
#endif

int32 totargetsex(int32 w, int flag);

extern void codeseg_stringsegs(StringSegList *x, bool incode);
extern void codeseg_flush(Symstr *strlitname);
extern int32 codeseg_function_name(Symstr *name, int32 argn);
extern void show_entry(Symstr *name, int flags);
extern void show_code(Symstr *name);
extern void outcodeword(int32 w, int32 f);
extern void outcodewordaux(int32 w, int32 f, VoidStar aux);
extern void outlitword(int32 w, int32 flavour, Symstr *sym, VoidStar aux,
                       int32 flag);
extern int32 codeloc(void);
extern int32 lit_findadcon(Symstr *name, int32 offset, int32 wherefrom);
extern void dumplits2(bool needsjump);
extern int lit_of_count_name(char *s);
extern void dump_count_names(void);
extern int32 lit_findword(int32 w, int32 flavour, Symstr *sym, int32 flag);
extern int32 lit_findwordaux(int32 w, int32 flavour, VoidStar aux, int32 flag);
extern int32 lit_findwordsincurpool(int32 w[], int32 count, int32 flavour);
extern int32 lit_findwordsinprevpools(int32 w[], int32 count,
                                      int32 flavour, int32 earliest);
extern int32 lit_findstringincurpool(StringSegList *s);
extern int32 lit_findstringinprevpools(StringSegList *s, int32 earliest);

extern int32 stringlength(StringSegList *s);

extern int32 addbsssym(Symstr *sym, int32 size, int32 align, bool statik, bool local);

extern void codebuf_init(void);
extern void codebuf_reinit(void);
extern void codebuf_reinit1(char * codeseg_name);   /* for C++ dynamic inits */
extern void codebuf_reinit2(void);
extern void codebuf_tidy(void);

#ifdef TARGET_IS_ACW
extern void outbytef(int32 w, int f);
#endif

#endif

/* end of codebuf.h */
