/* Copyright 2025 Piers Wombwell
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#pragma once

// ARM Symbolic Debugging Format.

// Acorn's spec:
// http://www.riscos.com/support/developers/prm/objectformat.html

// 'debugversion' field. Acorn used up to 2, but ARM's extended it (
#define ASD_FORMAT_VERSION 2

// [INVENTED] Fileinfo short format, max line length.
// In short format, two byte are used to store 'lineinfo'. See end of Acorn's
// spec. One byte is the number of bytes of code generated, and the second
// byte is the number of source lines.
//
// However, ARM have clearly extended this is to combine col and lines
// into one byte, if "OldAsdTables" is not true (it is set when using -asd-old
// on the command line, as opposed to -asd).
//
// Make up a number for now - I suppose you're more likely to have lots of
// characters than lines, for a statement, but since it's the law that everyone
// has a line length limit of 80, I'll use that.
#define Asd_LineInfo_Short_MaxLine 80

#define LANG_ASM        0
#define LANG_C          1
#define LANG_PASCAL     2
#define LANG_FORTRAN77  3

// Item kind codes ("itemsort") stored in low 16 bits of the first word.
// (High 16 bits are the byte length of the item.)
#define ITEMSECTION        0x0001  // section
#define ITEMPROC           0x0002  // procedure/function definition
#define ITEMENDPROC        0x0003  // endproc
#define ITEMVAR            0x0004  // variable
#define ITEMTYPE           0x0005  // type
#define ITEMSTRUCT         0x0006  // struct
#define ITEMARRAY          0x0007  // array
#define ITEMSUBRANGE       0x0008  // subrange (also used for C enums)
#define ITEMSET            0x0009  // set
#define ITEMFILEINFO       0x000A  // fileinfo
#define ITEMENUMC          0x000B  // contiguous enumeration
#define ITEMENUMD          0x000C  // discontiguous enumeration
#define ITEMPROCDECL       0x000D  // procedure/function declaration
#define ITEMSCOPEBEGIN     0x000E  // begin naming scope
#define ITEMSCOPEEND       0x000F  // end naming scope
#define ITEMBITFIELD       0x0010  // bitfield
#define ITEMDEFINE         0x0011  // macro definition
#define ITEMUNDEF          0x0012  // macro undefinition
#define ITEMCLASS          0x0013  // class
#define ITEMUNION          0x0014  // union
#define ITEMFPMAPFRAG      0x0020  // FP map fragment

// First word of each item: top 16 bits = byte length, low 16 bits = item code.
#define asd_len_(w)   ((uint32_t)((w) >> 16))
#define asd_code_(w)  ((uint16_t)((w) & 0xFFFFu))

// This might be a frame pointer map fragment? For stack unwinding. Who knows!
// [INVENTED] No clue what the order of this struct should be.
typedef struct ItemFPMapFragment {
    int32 marker;      // low = ITEMFPMAPFRAG; high = bytes+6*4.
    uint64_t codestart;
    uint64_t codesize;
    uint64_t saveaddr;
    int32 initoffset;
    int32 bytes;       // num of bytes that follow in b[], rounded up to a word.
    char  b[1];
} ItemFPMapFragment;

// Primitive base types. The groupings are actually in base ten, not hex.
typedef enum {
    TYPEVOID        = 0,
    TYPESBYTE       = 10,
    TYPESHALF       = 11,
    TYPESWORD       = 12,
    TYPEUBYTE       = 20,
    TYPEUHALF       = 21,
    TYPEUWORD       = 22,
    TYPEUDWORD      = 23, // [INVENTED] Seems the most plausible value.
    TYPEFLOAT       = 30,
    TYPEDOUBLE      = 31,
    TYPEFUNCTION    = 100
} asd_Type;

// TYPE_TYPEWORD — pack type and pointer depth into one 32-bit field
#define TYPE_TYPEWORD(TYPE, PTR_COUNT) (((TYPE) << 8) | (PTR_COUNT))

// TYPE_TYPECODE, TYPE_PTRCOUNT - desconstruct a type.
#define TYPE_TYPECODE(TYPE) ((TYPE) >> 8)
#define TYPE_PTRCOUNT(TYPE) ((TYPE) & 0xff)

#define TYPESTRING TYPE_TYPEWORD(TYPEUBYTE, 1)

// Storage classes of variables.
typedef enum {
    C_EXTERN            = 1,
    C_STATIC            = 2,
    C_AUTO              = 3,
    C_REG               = 4,
    PASCAL_VAR          = 5,
    FORTRAN_ARGS        = 6,
    FORTRAN_CHAR_ARGS   = 7,
    C_VAR               = 8  // [INVENTED]
} StgClass;

// No idea what asd_Address means - its only use it to create NoSaveAddr
// "#define NoSaveAddr ((asd_Address)-1)".
//
// NoSaveAddr is then only used to assign and compare against an int32.
//
// The name would imply it should be a pointer type, but then the use-cases
// fail to compile. It's most likely a 32-bit int, but it could be zero
// to create 0-1 = -1.
typedef int32_t asd_Address;

typedef struct {
    uint8_t length;
    const char *namep;
} asd_String;

typedef struct {
    uint32_t c;           // length+code word (ITEMSECTION)
    uint8_t  lang;
    uint8_t  flags;
    uint8_t  unused;
    uint8_t  asdversion;

    uint32_t codestart;
    uint32_t datastart;
    uint32_t codesize;
    uint32_t datasize;
    uint32_t fileinfo;
    uint32_t debugsize;

    // Followed by name string OR nsyms depending on lang; keep as packed string.
    asd_String n;
} ItemSection;

typedef struct {
    uint32_t c;           // length+code word (ITEMPROC)

    asd_Type type;        // return type if function, else 0
    uint32_t args;        // number of arguments
    uint32_t sourcepos;   // packed source position
    uint32_t startaddr;   // start of prologue
    uint32_t entry;       // first instruction of body
    uint32_t endproc;     // offset of matching endproc item (0 if label)
    uint32_t fileentry;   // offset of file list entry
    asd_String n;         // name
} ItemProc;

typedef struct {
    uint32_t id;           // length+code word (ITEMVAR)

    asd_Type type;
    uint32_t sourcepos;
    uint32_t storageclass;
    union {
        uint32_t address; // static/extern: absolute address (relocated)
        int32_t  offset;  // auto/var args: FP-relative offset; reg vars: reg num
    } location;

    asd_String n;         // name
} ItemVar;

typedef struct {
    uint32_t c;     // length+code word (ITEMTYPE)
    asd_Type type;
    asd_String n;
} ItemType;

// Array bounds are stored as a small tagged value in the ASD tables; `interp.c`
// expects to access the integer member via `.i`.
typedef union {
    int32_t  i;
    uint32_t u;
} asd_Bound;

typedef struct {
    uint32_t  size;
    uint32_t  arrayflags;
    uint32_t  basetype;
    asd_Bound lowerbound;
    asd_Bound upperbound;
} ItemArray;

typedef struct {
    uint32_t offset;
    asd_Type type;
    asd_String n;
} StructField;

typedef struct {
    uint32_t fields;
    uint32_t size;
    StructField fieldtable[1];
} SUC;

typedef struct {
    uint32_t c;      // length+code word
    uint8_t  b[1];   // start of payload (lets interp.c do &ip->b + asd_len_(ip->c))

    // Overlays used by interp.c (layout correctness can be fixed later).
    ItemArray a;
    SUC s;
    ItemType t;
    ItemVar v;
    ItemProc p;
} Item;
