/* bfd back-end for HP PA-RISC SOM objects.
   Copyright (C) 1990-2025 Free Software Foundation, Inc.

   Contributed by the Center for Software Science at the
   University of Utah.

   This file is part of BFD, the Binary File Descriptor library.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street - Fifth Floor, Boston, MA
   02110-1301, USA.  */

#include "sysdep.h"
#include "bfd.h"
#include "libiberty.h"
#include "libbfd.h"
#include "som.h"
#include "safe-ctype.h"
#include "som/reloc.h"
#include "aout/ar.h"

static bfd_reloc_status_type hppa_som_reloc
  (bfd *, arelent *, asymbol *, void *, asection *, bfd *, char **);
static bool som_mkobject (bfd *);
static bool som_is_space (asection *);
static bool som_is_subspace (asection *);
static int compare_subspaces (const void *, const void *);
static uint32_t som_compute_checksum (struct som_external_header *);
static bool som_build_and_write_symbol_table (bfd *);
static unsigned int som_slurp_symbol_table (bfd *);

/* Magic not defined in standard HP-UX header files until 8.0.  */

#ifndef CPU_PA_RISC1_0
#define CPU_PA_RISC1_0 0x20B
#endif /* CPU_PA_RISC1_0 */

#ifndef CPU_PA_RISC1_1
#define CPU_PA_RISC1_1 0x210
#endif /* CPU_PA_RISC1_1 */

#ifndef CPU_PA_RISC2_0
#define CPU_PA_RISC2_0 0x214
#endif /* CPU_PA_RISC2_0 */

#ifndef _PA_RISC1_0_ID
#define _PA_RISC1_0_ID CPU_PA_RISC1_0
#endif /* _PA_RISC1_0_ID */

#ifndef _PA_RISC1_1_ID
#define _PA_RISC1_1_ID CPU_PA_RISC1_1
#endif /* _PA_RISC1_1_ID */

#ifndef _PA_RISC2_0_ID
#define _PA_RISC2_0_ID CPU_PA_RISC2_0
#endif /* _PA_RISC2_0_ID */

#ifndef _PA_RISC_MAXID
#define _PA_RISC_MAXID	0x2FF
#endif /* _PA_RISC_MAXID */

#ifndef _PA_RISC_ID
#define _PA_RISC_ID(__m_num)		\
    (((__m_num) == _PA_RISC1_0_ID) ||	\
     ((__m_num) >= _PA_RISC1_1_ID && (__m_num) <= _PA_RISC_MAXID))
#endif /* _PA_RISC_ID */

/* HIUX in it's infinite stupidity changed the names for several "well
   known" constants.  Work around such braindamage.  Try the HPUX version
   first, then the HIUX version, and finally provide a default.  */
#ifdef HPUX_AUX_ID
#define EXEC_AUX_ID HPUX_AUX_ID
#endif

#if !defined (EXEC_AUX_ID) && defined (HIUX_AUX_ID)
#define EXEC_AUX_ID HIUX_AUX_ID
#endif

#ifndef EXEC_AUX_ID
#define EXEC_AUX_ID 0
#endif

/* Size (in chars) of the temporary buffers used during fixup and string
   table writes.   */

#define SOM_TMP_BUFSIZE 8192

/* Size of the hash table in archives.  */
#define SOM_LST_HASH_SIZE 31

/* Max number of SOMs to be found in an archive.  */
#define SOM_LST_MODULE_LIMIT 1024

/* Generic alignment macro.  */
#define SOM_ALIGN(val, alignment) \
  (((val) + (alignment) - 1) &~ ((unsigned long) (alignment) - 1))

/* SOM allows any one of the four previous relocations to be reused
   with a "R_PREV_FIXUP" relocation entry.  Since R_PREV_FIXUP
   relocations are always a single byte, using a R_PREV_FIXUP instead
   of some multi-byte relocation makes object files smaller.

   Note one side effect of using a R_PREV_FIXUP is the relocation that
   is being repeated moves to the front of the queue.  */
static struct reloc_queue
{
  unsigned char *reloc;
  unsigned int size;
} reloc_queue[4];

/* This fully describes the symbol types which may be attached to
   an EXPORT or IMPORT directive.  Only SOM uses this formation
   (ELF has no need for it).  */
typedef enum
{
  SYMBOL_TYPE_UNKNOWN,
  SYMBOL_TYPE_ABSOLUTE,
  SYMBOL_TYPE_CODE,
  SYMBOL_TYPE_DATA,
  SYMBOL_TYPE_ENTRY,
  SYMBOL_TYPE_MILLICODE,
  SYMBOL_TYPE_PLABEL,
  SYMBOL_TYPE_PRI_PROG,
  SYMBOL_TYPE_SEC_PROG,
} pa_symbol_type;

struct section_to_type
{
  const char *section;
  char type;
};

/* Assorted symbol information that needs to be derived from the BFD symbol
   and/or the BFD backend private symbol data.  */
struct som_misc_symbol_info
{
  unsigned int symbol_type;
  unsigned int symbol_scope;
  unsigned int arg_reloc;
  unsigned int symbol_info;
  unsigned int symbol_value;
  unsigned int priv_level;
  unsigned int secondary_def;
  unsigned int is_comdat;
  unsigned int is_common;
  unsigned int dup_common;
};

/* Map SOM section names to POSIX/BSD single-character symbol types.

   This table includes all the standard subspaces as defined in the
   current "PRO ABI for PA-RISC Systems", $UNWIND$ which for
   some reason was left out, and sections specific to embedded stabs.  */

static const struct section_to_type stt[] =
{
  {"$TEXT$", 't'},
  {"$SHLIB_INFO$", 't'},
  {"$MILLICODE$", 't'},
  {"$LIT$", 't'},
  {"$CODE$", 't'},
  {"$UNWIND_START$", 't'},
  {"$UNWIND$", 't'},
  {"$PRIVATE$", 'd'},
  {"$PLT$", 'd'},
  {"$SHLIB_DATA$", 'd'},
  {"$DATA$", 'd'},
  {"$SHORTDATA$", 'g'},
  {"$DLT$", 'd'},
  {"$GLOBAL$", 'g'},
  {"$SHORTBSS$", 's'},
  {"$BSS$", 'b'},
  {"$GDB_STRINGS$", 'N'},
  {"$GDB_SYMBOLS$", 'N'},
  {0, 0}
};

/* About the relocation formatting table...

   There are 256 entries in the table, one for each possible
   relocation opcode available in SOM.  We index the table by
   the relocation opcode.  The names and operations are those
   defined by a.out_800 (4).

   Right now this table is only used to count and perform minimal
   processing on relocation streams so that they can be internalized
   into BFD and symbolically printed by utilities.  To make actual use
   of them would be much more difficult, BFD's concept of relocations
   is far too simple to handle SOM relocations.  The basic assumption
   that a relocation can be completely processed independent of other
   relocations before an object file is written is invalid for SOM.

   The SOM relocations are meant to be processed as a stream, they
   specify copying of data from the input section to the output section
   while possibly modifying the data in some manner.  They also can
   specify that a variable number of zeros or uninitialized data be
   inserted on in the output segment at the current offset.  Some
   relocations specify that some previous relocation be re-applied at
   the current location in the input/output sections.  And finally a number
   of relocations have effects on other sections (R_ENTRY, R_EXIT,
   R_UNWIND_AUX and a variety of others).  There isn't even enough room
   in the BFD relocation data structure to store enough information to
   perform all the relocations.

   Each entry in the table has three fields.

   The first entry is an index into this "class" of relocations.  This
   index can then be used as a variable within the relocation itself.

   The second field is a format string which actually controls processing
   of the relocation.  It uses a simple postfix machine to do calculations
   based on variables/constants found in the string and the relocation
   stream.

   The third field specifys whether or not this relocation may use
   a constant (V) from the previous R_DATA_OVERRIDE rather than a constant
   stored in the instruction.

   Variables:

   L = input space byte count
   D = index into class of relocations
   M = output space byte count
   N = statement number (unused?)
   O = stack operation
   R = parameter relocation bits
   S = symbol index
   T = first 32 bits of stack unwind information
   U = second 32 bits of stack unwind information
   V = a literal constant (usually used in the next relocation)
   P = a previous relocation

   Lower case letters (starting with 'b') refer to following
   bytes in the relocation stream.  'b' is the next 1 byte,
   c is the next 2 bytes, d is the next 3 bytes, etc...
   This is the variable part of the relocation entries that
   makes our life a living hell.

   numerical constants are also used in the format string.  Note
   the constants are represented in decimal.

   '+', "*" and "=" represents the obvious postfix operators.
   '<' represents a left shift.

   Stack Operations:

   Parameter Relocation Bits:

   Unwind Entries:

   Previous Relocations:  The index field represents which in the queue
   of 4 previous fixups should be re-applied.

   Literal Constants:  These are generally used to represent addend
   parts of relocations when these constants are not stored in the
   fields of the instructions themselves.  For example the instruction
   addil foo-$global$-0x1234 would use an override for "0x1234" rather
   than storing it into the addil itself.  */

struct fixup_format
{
  int D;
  const char *format;
};

static const struct fixup_format som_fixup_formats[256] =
{
  /* R_NO_RELOCATION.  */
  {  0, "LD1+4*=" },		/* 0x00 */
  {  1, "LD1+4*=" },		/* 0x01 */
  {  2, "LD1+4*=" },		/* 0x02 */
  {  3, "LD1+4*=" },		/* 0x03 */
  {  4, "LD1+4*=" },		/* 0x04 */
  {  5, "LD1+4*=" },		/* 0x05 */
  {  6, "LD1+4*=" },		/* 0x06 */
  {  7, "LD1+4*=" },		/* 0x07 */
  {  8, "LD1+4*=" },		/* 0x08 */
  {  9, "LD1+4*=" },		/* 0x09 */
  { 10, "LD1+4*=" },		/* 0x0a */
  { 11, "LD1+4*=" },		/* 0x0b */
  { 12, "LD1+4*=" },		/* 0x0c */
  { 13, "LD1+4*=" },		/* 0x0d */
  { 14, "LD1+4*=" },		/* 0x0e */
  { 15, "LD1+4*=" },		/* 0x0f */
  { 16, "LD1+4*=" },		/* 0x10 */
  { 17, "LD1+4*=" },		/* 0x11 */
  { 18, "LD1+4*=" },		/* 0x12 */
  { 19, "LD1+4*=" },		/* 0x13 */
  { 20, "LD1+4*=" },		/* 0x14 */
  { 21, "LD1+4*=" },		/* 0x15 */
  { 22, "LD1+4*=" },		/* 0x16 */
  { 23, "LD1+4*=" },		/* 0x17 */
  {  0, "LD8<b+1+4*=" },	/* 0x18 */
  {  1, "LD8<b+1+4*=" },	/* 0x19 */
  {  2, "LD8<b+1+4*=" },	/* 0x1a */
  {  3, "LD8<b+1+4*=" },	/* 0x1b */
  {  0, "LD16<c+1+4*=" },	/* 0x1c */
  {  1, "LD16<c+1+4*=" },	/* 0x1d */
  {  2, "LD16<c+1+4*=" },	/* 0x1e */
  {  0, "Ld1+=" },		/* 0x1f */
  /* R_ZEROES.  */
  {  0, "Lb1+4*=" },		/* 0x20 */
  {  1, "Ld1+=" },		/* 0x21 */
  /* R_UNINIT.  */
  {  0, "Lb1+4*=" },		/* 0x22 */
  {  1, "Ld1+=" },		/* 0x23 */
  /* R_RELOCATION.  */
  {  0, "L4=" },		/* 0x24 */
  /* R_DATA_ONE_SYMBOL.  */
  {  0, "L4=Sb=" },		/* 0x25 */
  {  1, "L4=Sd=" },		/* 0x26 */
  /* R_DATA_PLABEL.  */
  {  0, "L4=Sb=" },		/* 0x27 */
  {  1, "L4=Sd=" },		/* 0x28 */
  /* R_SPACE_REF.  */
  {  0, "L4=" },		/* 0x29 */
  /* R_REPEATED_INIT.  */
  {  0, "L4=Mb1+4*=" },		/* 0x2a */
  {  1, "Lb4*=Mb1+L*=" },	/* 0x2b */
  {  2, "Lb4*=Md1+4*=" },	/* 0x2c */
  {  3, "Ld1+=Me1+=" },		/* 0x2d */
  {  0, "" },			/* 0x2e */
  {  0, "" },			/* 0x2f */
  /* R_PCREL_CALL.  */
  {  0, "L4=RD=Sb=" },		/* 0x30 */
  {  1, "L4=RD=Sb=" },		/* 0x31 */
  {  2, "L4=RD=Sb=" },		/* 0x32 */
  {  3, "L4=RD=Sb=" },		/* 0x33 */
  {  4, "L4=RD=Sb=" },		/* 0x34 */
  {  5, "L4=RD=Sb=" },		/* 0x35 */
  {  6, "L4=RD=Sb=" },		/* 0x36 */
  {  7, "L4=RD=Sb=" },		/* 0x37 */
  {  8, "L4=RD=Sb=" },		/* 0x38 */
  {  9, "L4=RD=Sb=" },		/* 0x39 */
  {  0, "L4=RD8<b+=Sb=" },	/* 0x3a */
  {  1, "L4=RD8<b+=Sb=" },	/* 0x3b */
  {  0, "L4=RD8<b+=Sd=" },	/* 0x3c */
  {  1, "L4=RD8<b+=Sd=" },	/* 0x3d */
  /* R_SHORT_PCREL_MODE.  */
  {  0, "" },			/* 0x3e */
  /* R_LONG_PCREL_MODE.  */
  {  0, "" },			/* 0x3f */
  /* R_ABS_CALL.  */
  {  0, "L4=RD=Sb=" },		/* 0x40 */
  {  1, "L4=RD=Sb=" },		/* 0x41 */
  {  2, "L4=RD=Sb=" },		/* 0x42 */
  {  3, "L4=RD=Sb=" },		/* 0x43 */
  {  4, "L4=RD=Sb=" },		/* 0x44 */
  {  5, "L4=RD=Sb=" },		/* 0x45 */
  {  6, "L4=RD=Sb=" },		/* 0x46 */
  {  7, "L4=RD=Sb=" },		/* 0x47 */
  {  8, "L4=RD=Sb=" },		/* 0x48 */
  {  9, "L4=RD=Sb=" },		/* 0x49 */
  {  0, "L4=RD8<b+=Sb=" },	/* 0x4a */
  {  1, "L4=RD8<b+=Sb=" },	/* 0x4b */
  {  0, "L4=RD8<b+=Sd=" },	/* 0x4c */
  {  1, "L4=RD8<b+=Sd=" },	/* 0x4d */
  /* R_RESERVED.  */
  {  0, "" },			/* 0x4e */
  {  0, "" },			/* 0x4f */
  /* R_DP_RELATIVE.  */
  {  0, "L4=SD=" },		/* 0x50 */
  {  1, "L4=SD=" },		/* 0x51 */
  {  2, "L4=SD=" },		/* 0x52 */
  {  3, "L4=SD=" },		/* 0x53 */
  {  4, "L4=SD=" },		/* 0x54 */
  {  5, "L4=SD=" },		/* 0x55 */
  {  6, "L4=SD=" },		/* 0x56 */
  {  7, "L4=SD=" },		/* 0x57 */
  {  8, "L4=SD=" },		/* 0x58 */
  {  9, "L4=SD=" },		/* 0x59 */
  { 10, "L4=SD=" },		/* 0x5a */
  { 11, "L4=SD=" },		/* 0x5b */
  { 12, "L4=SD=" },		/* 0x5c */
  { 13, "L4=SD=" },		/* 0x5d */
  { 14, "L4=SD=" },		/* 0x5e */
  { 15, "L4=SD=" },		/* 0x5f */
  { 16, "L4=SD=" },		/* 0x60 */
  { 17, "L4=SD=" },		/* 0x61 */
  { 18, "L4=SD=" },		/* 0x62 */
  { 19, "L4=SD=" },		/* 0x63 */
  { 20, "L4=SD=" },		/* 0x64 */
  { 21, "L4=SD=" },		/* 0x65 */
  { 22, "L4=SD=" },		/* 0x66 */
  { 23, "L4=SD=" },		/* 0x67 */
  { 24, "L4=SD=" },		/* 0x68 */
  { 25, "L4=SD=" },		/* 0x69 */
  { 26, "L4=SD=" },		/* 0x6a */
  { 27, "L4=SD=" },		/* 0x6b */
  { 28, "L4=SD=" },		/* 0x6c */
  { 29, "L4=SD=" },		/* 0x6d */
  { 30, "L4=SD=" },		/* 0x6e */
  { 31, "L4=SD=" },		/* 0x6f */
  { 32, "L4=Sb=" },		/* 0x70 */
  { 33, "L4=Sd=" },		/* 0x71 */
  /* R_DATA_GPREL.  */
  {  0, "L4=Sd=" },		/* 0x72 */
  /* R_RESERVED.  */
  {  0, "" },			/* 0x73 */
  {  0, "" },			/* 0x74 */
  {  0, "" },			/* 0x75 */
  {  0, "" },			/* 0x76 */
  {  0, "" },			/* 0x77 */
  /* R_DLT_REL.  */
  {  0, "L4=Sb=" },		/* 0x78 */
  {  1, "L4=Sd=" },		/* 0x79 */
  /* R_RESERVED.  */
  {  0, "" },			/* 0x7a */
  {  0, "" },			/* 0x7b */
  {  0, "" },			/* 0x7c */
  {  0, "" },			/* 0x7d */
  {  0, "" },			/* 0x7e */
  {  0, "" },			/* 0x7f */
  /* R_CODE_ONE_SYMBOL.  */
  {  0, "L4=SD=" },		/* 0x80 */
  {  1, "L4=SD=" },		/* 0x81 */
  {  2, "L4=SD=" },		/* 0x82 */
  {  3, "L4=SD=" },		/* 0x83 */
  {  4, "L4=SD=" },		/* 0x84 */
  {  5, "L4=SD=" },		/* 0x85 */
  {  6, "L4=SD=" },		/* 0x86 */
  {  7, "L4=SD=" },		/* 0x87 */
  {  8, "L4=SD=" },		/* 0x88 */
  {  9, "L4=SD=" },		/* 0x89 */
  { 10, "L4=SD=" },		/* 0x8q */
  { 11, "L4=SD=" },		/* 0x8b */
  { 12, "L4=SD=" },		/* 0x8c */
  { 13, "L4=SD=" },		/* 0x8d */
  { 14, "L4=SD=" },		/* 0x8e */
  { 15, "L4=SD=" },		/* 0x8f */
  { 16, "L4=SD=" },		/* 0x90 */
  { 17, "L4=SD=" },		/* 0x91 */
  { 18, "L4=SD=" },		/* 0x92 */
  { 19, "L4=SD=" },		/* 0x93 */
  { 20, "L4=SD=" },		/* 0x94 */
  { 21, "L4=SD=" },		/* 0x95 */
  { 22, "L4=SD=" },		/* 0x96 */
  { 23, "L4=SD=" },		/* 0x97 */
  { 24, "L4=SD=" },		/* 0x98 */
  { 25, "L4=SD=" },		/* 0x99 */
  { 26, "L4=SD=" },		/* 0x9a */
  { 27, "L4=SD=" },		/* 0x9b */
  { 28, "L4=SD=" },		/* 0x9c */
  { 29, "L4=SD=" },		/* 0x9d */
  { 30, "L4=SD=" },		/* 0x9e */
  { 31, "L4=SD=" },		/* 0x9f */
  { 32, "L4=Sb=" },		/* 0xa0 */
  { 33, "L4=Sd=" },		/* 0xa1 */
  /* R_RESERVED.  */
  {  0, "" },			/* 0xa2 */
  {  0, "" },			/* 0xa3 */
  {  0, "" },			/* 0xa4 */
  {  0, "" },			/* 0xa5 */
  {  0, "" },			/* 0xa6 */
  {  0, "" },			/* 0xa7 */
  {  0, "" },			/* 0xa8 */
  {  0, "" },			/* 0xa9 */
  {  0, "" },			/* 0xaa */
  {  0, "" },			/* 0xab */
  {  0, "" },			/* 0xac */
  {  0, "" },			/* 0xad */
  /* R_MILLI_REL.  */
  {  0, "L4=Sb=" },		/* 0xae */
  {  1, "L4=Sd=" },		/* 0xaf */
  /* R_CODE_PLABEL.  */
  {  0, "L4=Sb=" },		/* 0xb0 */
  {  1, "L4=Sd=" },		/* 0xb1 */
  /* R_BREAKPOINT.  */
  {  0, "L4=" },		/* 0xb2 */
  /* R_ENTRY.  */
  {  0, "Te=Ue=" },		/* 0xb3 */
  {  1, "Uf=" },		/* 0xb4 */
  /* R_ALT_ENTRY.  */
  {  0, "" },			/* 0xb5 */
  /* R_EXIT.  */
  {  0, "" },			/* 0xb6 */
  /* R_BEGIN_TRY.  */
  {  0, "" },			/* 0xb7 */
  /* R_END_TRY.  */
  {  0, "R0=" },		/* 0xb8 */
  {  1, "Rb4*=" },		/* 0xb9 */
  {  2, "Rd4*=" },		/* 0xba */
  /* R_BEGIN_BRTAB.  */
  {  0, "" },			/* 0xbb */
  /* R_END_BRTAB.  */
  {  0, "" },			/* 0xbc */
  /* R_STATEMENT.  */
  {  0, "Nb=" },		/* 0xbd */
  {  1, "Nc=" },		/* 0xbe */
  {  2, "Nd=" },		/* 0xbf */
  /* R_DATA_EXPR.  */
  {  0, "L4=" },		/* 0xc0 */
  /* R_CODE_EXPR.  */
  {  0, "L4=" },		/* 0xc1 */
  /* R_FSEL.  */
  {  0, "" },			/* 0xc2 */
  /* R_LSEL.  */
  {  0, "" },			/* 0xc3 */
  /* R_RSEL.  */
  {  0, "" },			/* 0xc4 */
  /* R_N_MODE.  */
  {  0, "" },			/* 0xc5 */
  /* R_S_MODE.  */
  {  0, "" },			/* 0xc6 */
  /* R_D_MODE.  */
  {  0, "" },			/* 0xc7 */
  /* R_R_MODE.  */
  {  0, "" },			/* 0xc8 */
  /* R_DATA_OVERRIDE.  */
  {  0, "V0=" },		/* 0xc9 */
  {  1, "Vb=" },		/* 0xca */
  {  2, "Vc=" },		/* 0xcb */
  {  3, "Vd=" },		/* 0xcc */
  {  4, "Ve=" },		/* 0xcd */
  /* R_TRANSLATED.  */
  {  0, "" },			/* 0xce */
  /* R_AUX_UNWIND.  */
  {  0,"Sd=Ve=Ee=" },	       /* 0xcf */
  /* R_COMP1.  */
  {  0, "Ob=" },		/* 0xd0 */
  /* R_COMP2.  */
  {  0, "Ob=Sd=" },		/* 0xd1 */
  /* R_COMP3.  */
  {  0, "Ob=Ve=" },		/* 0xd2 */
  /* R_PREV_FIXUP.  */
  {  0, "P" },			/* 0xd3 */
  {  1, "P" },			/* 0xd4 */
  {  2, "P" },			/* 0xd5 */
  {  3, "P" },			/* 0xd6 */
  /* R_SEC_STMT.  */
  {  0, "" },			/* 0xd7 */
  /* R_N0SEL.  */
  {  0, "" },			/* 0xd8 */
  /* R_N1SEL.  */
  {  0, "" },			/* 0xd9 */
  /* R_LINETAB.  */
  {  0, "Eb=Sd=Ve=" },		/* 0xda */
  /* R_LINETAB_ESC.  */
  {  0, "Eb=Mb=" },		/* 0xdb */
  /* R_LTP_OVERRIDE.  */
  {  0, "" },			/* 0xdc */
  /* R_COMMENT.  */
  {  0, "Ob=Vf=" },		/* 0xdd */
  /* R_RESERVED.  */
  {  0, "" },			/* 0xde */
  {  0, "" },			/* 0xdf */
  {  0, "" },			/* 0xe0 */
  {  0, "" },			/* 0xe1 */
  {  0, "" },			/* 0xe2 */
  {  0, "" },			/* 0xe3 */
  {  0, "" },			/* 0xe4 */
  {  0, "" },			/* 0xe5 */
  {  0, "" },			/* 0xe6 */
  {  0, "" },			/* 0xe7 */
  {  0, "" },			/* 0xe8 */
  {  0, "" },			/* 0xe9 */
  {  0, "" },			/* 0xea */
  {  0, "" },			/* 0xeb */
  {  0, "" },			/* 0xec */
  {  0, "" },			/* 0xed */
  {  0, "" },			/* 0xee */
  {  0, "" },			/* 0xef */
  {  0, "" },			/* 0xf0 */
  {  0, "" },			/* 0xf1 */
  {  0, "" },			/* 0xf2 */
  {  0, "" },			/* 0xf3 */
  {  0, "" },			/* 0xf4 */
  {  0, "" },			/* 0xf5 */
  {  0, "" },			/* 0xf6 */
  {  0, "" },			/* 0xf7 */
  {  0, "" },			/* 0xf8 */
  {  0, "" },			/* 0xf9 */
  {  0, "" },			/* 0xfa */
  {  0, "" },			/* 0xfb */
  {  0, "" },			/* 0xfc */
  {  0, "" },			/* 0xfd */
  {  0, "" },			/* 0xfe */
  {  0, "" },			/* 0xff */
};

static const int comp1_opcodes[] =
{
  0x00,
  0x40,
  0x41,
  0x42,
  0x43,
  0x44,
  0x45,
  0x46,
  0x47,
  0x48,
  0x49,
  0x4a,
  0x4b,
  0x60,
  0x80,
  0xa0,
  0xc0,
  -1
};

static const int comp2_opcodes[] =
{
  0x00,
  0x80,
  0x82,
  0xc0,
  -1
};

static const int comp3_opcodes[] =
{
  0x00,
  0x02,
  -1
};

/* These apparently are not in older versions of hpux reloc.h (hpux7).  */

/* And these first appeared in hpux10.  */
#ifndef R_SHORT_PCREL_MODE
#define NO_PCREL_MODES
#define R_SHORT_PCREL_MODE 0x3e
#endif

#define SOM_HOWTO(SIZE, TYPE)	\
  HOWTO(TYPE, 0, SIZE, 32, false, 0, 0, hppa_som_reloc, \
	#TYPE, false, 0, 0, false)

static reloc_howto_type som_hppa_howto_table[] =
{
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_NO_RELOCATION),
  SOM_HOWTO (0, R_ZEROES),
  SOM_HOWTO (0, R_ZEROES),
  SOM_HOWTO (0, R_UNINIT),
  SOM_HOWTO (0, R_UNINIT),
  SOM_HOWTO (4, R_RELOCATION),
  SOM_HOWTO (4, R_DATA_ONE_SYMBOL),
  SOM_HOWTO (4, R_DATA_ONE_SYMBOL),
  SOM_HOWTO (4, R_DATA_PLABEL),
  SOM_HOWTO (4, R_DATA_PLABEL),
  SOM_HOWTO (4, R_SPACE_REF),
  SOM_HOWTO (0, R_REPEATED_INIT),
  SOM_HOWTO (0, R_REPEATED_INIT),
  SOM_HOWTO (0, R_REPEATED_INIT),
  SOM_HOWTO (0, R_REPEATED_INIT),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (4, R_PCREL_CALL),
  SOM_HOWTO (4, R_PCREL_CALL),
  SOM_HOWTO (4, R_PCREL_CALL),
  SOM_HOWTO (4, R_PCREL_CALL),
  SOM_HOWTO (4, R_PCREL_CALL),
  SOM_HOWTO (4, R_PCREL_CALL),
  SOM_HOWTO (4, R_PCREL_CALL),
  SOM_HOWTO (4, R_PCREL_CALL),
  SOM_HOWTO (4, R_PCREL_CALL),
  SOM_HOWTO (4, R_PCREL_CALL),
  SOM_HOWTO (4, R_PCREL_CALL),
  SOM_HOWTO (4, R_PCREL_CALL),
  SOM_HOWTO (4, R_PCREL_CALL),
  SOM_HOWTO (4, R_PCREL_CALL),
  SOM_HOWTO (0, R_SHORT_PCREL_MODE),
  SOM_HOWTO (0, R_LONG_PCREL_MODE),
  SOM_HOWTO (4, R_ABS_CALL),
  SOM_HOWTO (4, R_ABS_CALL),
  SOM_HOWTO (4, R_ABS_CALL),
  SOM_HOWTO (4, R_ABS_CALL),
  SOM_HOWTO (4, R_ABS_CALL),
  SOM_HOWTO (4, R_ABS_CALL),
  SOM_HOWTO (4, R_ABS_CALL),
  SOM_HOWTO (4, R_ABS_CALL),
  SOM_HOWTO (4, R_ABS_CALL),
  SOM_HOWTO (4, R_ABS_CALL),
  SOM_HOWTO (4, R_ABS_CALL),
  SOM_HOWTO (4, R_ABS_CALL),
  SOM_HOWTO (4, R_ABS_CALL),
  SOM_HOWTO (4, R_ABS_CALL),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DP_RELATIVE),
  SOM_HOWTO (4, R_DATA_GPREL),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (4, R_DLT_REL),
  SOM_HOWTO (4, R_DLT_REL),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (4, R_CODE_ONE_SYMBOL),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (4, R_MILLI_REL),
  SOM_HOWTO (4, R_MILLI_REL),
  SOM_HOWTO (4, R_CODE_PLABEL),
  SOM_HOWTO (4, R_CODE_PLABEL),
  SOM_HOWTO (4, R_BREAKPOINT),
  SOM_HOWTO (0, R_ENTRY),
  SOM_HOWTO (0, R_ENTRY),
  SOM_HOWTO (0, R_ALT_ENTRY),
  SOM_HOWTO (0, R_EXIT),
  SOM_HOWTO (0, R_BEGIN_TRY),
  SOM_HOWTO (0, R_END_TRY),
  SOM_HOWTO (0, R_END_TRY),
  SOM_HOWTO (0, R_END_TRY),
  SOM_HOWTO (0, R_BEGIN_BRTAB),
  SOM_HOWTO (0, R_END_BRTAB),
  SOM_HOWTO (0, R_STATEMENT),
  SOM_HOWTO (0, R_STATEMENT),
  SOM_HOWTO (0, R_STATEMENT),
  SOM_HOWTO (4, R_DATA_EXPR),
  SOM_HOWTO (4, R_CODE_EXPR),
  SOM_HOWTO (0, R_FSEL),
  SOM_HOWTO (0, R_LSEL),
  SOM_HOWTO (0, R_RSEL),
  SOM_HOWTO (0, R_N_MODE),
  SOM_HOWTO (0, R_S_MODE),
  SOM_HOWTO (0, R_D_MODE),
  SOM_HOWTO (0, R_R_MODE),
  SOM_HOWTO (0, R_DATA_OVERRIDE),
  SOM_HOWTO (0, R_DATA_OVERRIDE),
  SOM_HOWTO (0, R_DATA_OVERRIDE),
  SOM_HOWTO (0, R_DATA_OVERRIDE),
  SOM_HOWTO (0, R_DATA_OVERRIDE),
  SOM_HOWTO (0, R_TRANSLATED),
  SOM_HOWTO (0, R_AUX_UNWIND),
  SOM_HOWTO (0, R_COMP1),
  SOM_HOWTO (0, R_COMP2),
  SOM_HOWTO (0, R_COMP3),
  SOM_HOWTO (0, R_PREV_FIXUP),
  SOM_HOWTO (0, R_PREV_FIXUP),
  SOM_HOWTO (0, R_PREV_FIXUP),
  SOM_HOWTO (0, R_PREV_FIXUP),
  SOM_HOWTO (0, R_SEC_STMT),
  SOM_HOWTO (0, R_N0SEL),
  SOM_HOWTO (0, R_N1SEL),
  SOM_HOWTO (0, R_LINETAB),
  SOM_HOWTO (0, R_LINETAB_ESC),
  SOM_HOWTO (0, R_LTP_OVERRIDE),
  SOM_HOWTO (0, R_COMMENT),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED),
  SOM_HOWTO (0, R_RESERVED)
};

/* Initialize the SOM relocation queue.  By definition the queue holds
   the last four multibyte fixups.  */

static void
som_initialize_reloc_queue (struct reloc_queue *queue)
{
  int i;

  for (i = 0; i < 4; i++)
    {
      queue[i].reloc = NULL;
      queue[i].size = 0;
    }
}

/* Insert a new relocation into the relocation queue.  */

static void
som_reloc_queue_insert (unsigned char *p,
			unsigned int size,
			struct reloc_queue *queue)
{
  const int QUEUE_STATIC_SIZE = 4;

  for (int i = QUEUE_STATIC_SIZE - 1; i > 0; --i) {
    queue[i].reloc = queue[i-1].reloc;
    queue[i].size = queue[i-1].size;
  }

  queue[0].reloc = p;
  queue[0].size = size;
}

/* When an entry in the relocation queue is reused, the entry moves
   to the front of the queue.  */

static void
som_reloc_queue_fix (struct reloc_queue *queue, unsigned int idx)
{
  if (idx == 0)
    {
      return;
    }

  // The original code explicitly handles idx values 1, 2, and 3.
  // Any other non-zero idx (i.e., idx > 3) causes the program to abort.
  // This check ensures that array accesses (e.g., queue[idx]) remain
  // within the implicitly defined bounds of the original logic's intent,
  // preventing potential out-of-bounds access for unhandled indices
  // before the abort behavior is triggered.
  if (idx > 3)
    {
      abort ();
    }

  // The pattern for idx = 1, 2, 3 is a right cyclic shift of the sub-array
  // queue[0...idx] by one position.
  // Specifically, elements at indices [0, 1, ..., idx] transform into
  // [idx, 0, 1, ..., idx-1].

  // Store the original first element to be reinserted later.
  // Using a local struct variable improves readability and type safety
  // compared to separate pointers and sizes.
  struct reloc_queue saved_q0 = queue[0];

  // Move the element currently at the 'idx' position to the front of the queue.
  queue[0] = queue[idx];

  // Shift elements from index 1 up to 'idx - 1' one position to the right.
  // For example: queue[1] moves to queue[2], queue[2] moves to queue[3], etc.
  // The loop iterates downwards to prevent overwriting elements prematurely.
  // If idx is 1, the loop condition (i > 1) is false, so it correctly does not run,
  // as no further shifting is needed beyond the effective swap.
  for (unsigned int i = idx; i > 1; --i)
    {
      queue[i] = queue[i-1];
    }

  // Insert the saved original first element into the second position
  // (which is now index 1).
  queue[1] = saved_q0;
}

/* Search for a particular relocation in the relocation queue.  */

#include <string.h>

static const int RELOC_QUEUE_CAPACITY = 4;

static int
som_reloc_queue_find (unsigned char *p,
                      unsigned int size,
                      struct reloc_queue *queue)
{
  for (int i = 0; i < RELOC_QUEUE_CAPACITY; ++i)
    {
      if (queue[i].reloc != NULL &&
          queue[i].size == size &&
          memcmp(p, queue[i].reloc, (size_t)size) == 0)
        {
          return i;
        }
    }

  return -1;
}

static unsigned char *
try_prev_fixup (bfd *abfd,
		unsigned int *subspace_reloc_sizep,
		unsigned char *p,
		unsigned int size,
		struct reloc_queue *queue)
{
  int queue_index = som_reloc_queue_find (p, size, queue);
  unsigned int p_increment;
  unsigned int size_counter_increment;

  if (queue_index != -1)
    {
      bfd_put_8 (abfd, R_PREV_FIXUP + queue_index, p);
      som_reloc_queue_fix (queue, queue_index);

      p_increment = 1;
      size_counter_increment = 1;
    }
  else
    {
      som_reloc_queue_insert (p, size, queue);

      p_increment = size;
      size_counter_increment = size;
    }

  p += p_increment;
  *subspace_reloc_sizep += size_counter_increment;

  return p;
}

/* Emit the proper R_NO_RELOCATION fixups to map the next SKIP
   bytes without any relocation.  Update the size of the subspace
   relocation stream via SUBSPACE_RELOC_SIZE_P; also return the
   current pointer into the relocation stream.  */

static unsigned char *
som_reloc_skip (bfd *abfd,
		unsigned int skip,
		unsigned char *p,
		unsigned int *subspace_reloc_sizep,
		struct reloc_queue *queue)
{
  const unsigned int LARGE_SKIP_THRESHOLD = 0x1000000;
  const unsigned int MAX_1BYTE_VAL_DIV4_MINUS1 = 0x17; // Corresponds to skip <= 0x60
  const unsigned int MAX_2BYTE_VAL_DIV4_MINUS1 = 0x3FF; // Corresponds to skip <= 0x1000

  if (skip >= LARGE_SKIP_THRESHOLD)
    {
      skip -= LARGE_SKIP_THRESHOLD;
      bfd_put_8 (abfd, R_NO_RELOCATION + 31, p);
      bfd_put_8 (abfd, 0xff, p + 1);
      bfd_put_16 (abfd, (bfd_vma) 0xffff, p + 2);
      p = try_prev_fixup (abfd, subspace_reloc_sizep, p, 4, queue);

      while (skip >= LARGE_SKIP_THRESHOLD)
	{
	  skip -= LARGE_SKIP_THRESHOLD;
	  bfd_put_8 (abfd, R_PREV_FIXUP, p);
	  p++;
	  *subspace_reloc_sizep += 1;
	}
    }

  if (skip > 0)
    {
      unsigned int val_to_encode;
      unsigned char header_byte;
      int entry_size;

      if ((skip & 3) == 0 && skip <= 0xc0000)
	{
	  val_to_encode = (skip >> 2) - 1;

	  if (val_to_encode <= MAX_1BYTE_VAL_DIV4_MINUS1)
	    {
	      header_byte = R_NO_RELOCATION + val_to_encode;
	      entry_size = 1;
	      bfd_put_8 (abfd, header_byte, p);
	    }
	  else if (val_to_encode <= MAX_2BYTE_VAL_DIV4_MINUS1)
	    {
	      header_byte = R_NO_RELOCATION + 24 + (val_to_encode >> 8);
	      entry_size = 2;
	      bfd_put_8 (abfd, header_byte, p);
	      bfd_put_8 (abfd, val_to_encode & 0xFF, p + 1);
	    }
	  else
	    {
	      header_byte = R_NO_RELOCATION + 28 + (val_to_encode >> 16);
	      entry_size = 3;
	      bfd_put_8 (abfd, header_byte, p);
	      bfd_put_16 (abfd, (bfd_vma) val_to_encode, p + 1);
	    }
	}
      else
	{
	  val_to_encode = skip - 1;
	  header_byte = R_NO_RELOCATION + 31;
	  entry_size = 4;
	  bfd_put_8 (abfd, header_byte, p);
	  bfd_put_8 (abfd, val_to_encode >> 16, p + 1);
	  bfd_put_16 (abfd, (bfd_vma) val_to_encode, p + 2);
	}

      p = try_prev_fixup (abfd, subspace_reloc_sizep, p, entry_size, queue);
    }
  return p;
}

/* Emit the proper R_DATA_OVERRIDE fixups to handle a nonzero addend
   from a BFD relocation.  Update the size of the subspace relocation
   stream via SUBSPACE_RELOC_SIZE_P; also return the current pointer
   into the relocation stream.  */

static unsigned char *
som_reloc_addend (bfd *abfd,
		  bfd_vma addend,
		  unsigned char *p,
		  unsigned int *subspace_reloc_sizep,
		  struct reloc_queue *queue)
{
  const bfd_vma THRESHOLD_1BYTE = 0x80;
  const bfd_vma THRESHOLD_2BYTES = 0x8000;
  const bfd_vma THRESHOLD_3BYTES = 0x800000;

  unsigned int data_override_suffix;

  if (addend < THRESHOLD_1BYTE)
    {
      data_override_suffix = 1;
      bfd_put_8 (abfd, addend, p + 1);
    }
  else if (addend < THRESHOLD_2BYTES)
    {
      data_override_suffix = 2;
      bfd_put_16 (abfd, addend, p + 1);
    }
  else if (addend < THRESHOLD_3BYTES)
    {
      data_override_suffix = 3;
      bfd_put_8 (abfd, addend >> 16, p + 1);
      bfd_put_16 (abfd, addend, p + 2);
    }
  else
    {
      data_override_suffix = 4;
      bfd_put_32 (abfd, addend, p + 1);
    }

  bfd_put_8 (abfd, R_DATA_OVERRIDE + data_override_suffix, p);
  p = try_prev_fixup (abfd, subspace_reloc_sizep, p, 1 + data_override_suffix, queue);

  return p;
}

/* Handle a single function call relocation.  */

static unsigned char *
som_reloc_call (bfd *abfd,
                unsigned char *p,
                unsigned int *subspace_reloc_sizep,
                const arelent *bfd_reloc,
                int sym_num,
                struct reloc_queue *queue)
{
  if (abfd == NULL || p == NULL || subspace_reloc_sizep == NULL || bfd_reloc == NULL || queue == NULL || bfd_reloc->howto == NULL)
    {
      return p;
    }

  #define SYM_NUM_SIMPLE_RELOC_MAX            0x100

  #define SIMPLE_RELOC_LOWEST_BIT_MASK        0x1
  #define SIMPLE_RELOC_RETURN_TYPE_OFFSET     5
  #define SIMPLE_RELOC_EMITTED_SIZE           2

  #define ARG_BITS_SIMPLE_CASE_0_PATTERN      0x0
  #define ARG_BITS_SIMPLE_CASE_1_PATTERN      (1 << 8)
  #define ARG_BITS_SIMPLE_CASE_2_PATTERN      ((1 << 8) | (1 << 6))
  #define ARG_BITS_SIMPLE_CASE_3_PATTERN      ((1 << 8) | (1 << 6) | (1 << 4))
  #define ARG_BITS_SIMPLE_CASE_4_PATTERN      ((1 << 8) | (1 << 6) | (1 << 4) | (1 << 2))

  #define HPPA_R_RTN_BITS_MASK                0x3

  #define ARG_BITS_FIELD1_SHIFT               8
  #define ARG_BITS_FIELD1_MASK                0x3
  #define ARG_BITS_FIELD2_SHIFT               6
  #define ARG_BITS_FIELD2_MASK                0x3
  #define ARG_BITS_FIELD3_SHIFT               4
  #define ARG_BITS_FIELD3_MASK                0x3
  #define ARG_BITS_FIELD4_SHIFT               2
  #define ARG_BITS_FIELD4_MASK                0x3

  #define ARG_BITS_SPECIAL_FIELD1_SHIFT       6
  #define ARG_BITS_SPECIAL_FIELD1_MASK        0xF
  #define ARG_BITS_SPECIAL_FIELD1_VALUE       0xE
  #define ARG_BITS_SPECIAL_FIELD1_ADDEND      (9 * 40)

  #define ARG_BITS_NORMAL_FIELD1_COEF_A       3
  #define ARG_BITS_NORMAL_FIELD1_COEF_B       40

  #define ARG_BITS_SPECIAL_FIELD2_SHIFT       2
  #define ARG_BITS_SPECIAL_FIELD2_MASK        0xF
  #define ARG_BITS_SPECIAL_FIELD2_VALUE       0xE
  #define ARG_BITS_SPECIAL_FIELD2_ADDEND      (9 * 4)

  #define ARG_BITS_NORMAL_FIELD2_COEF_A       3
  #define ARG_BITS_NORMAL_FIELD2_COEF_B       4

  #define HARD_RELOC_BASE_TYPE_ADDEND         10
  #define HARD_RELOC_SYM_GE_MAX_TYPE_ADDEND   2
  #define HARD_RELOC_TYPE_GE_MAX_TYPE_ADDEND  1

  #define HARD_RELOC_SYM_LT_MAX_EMITTED_SIZE  3
  #define HARD_RELOC_SYM_GE_MAX_EMITTED_SIZE  5

  #define SYM_NUM_HIGH_BYTE_SHIFT             16
  #define SYM_NUM_LOW_16_BITS_MASK            0xFFFF


  const int arg_bits = HPPA_R_ARG_RELOC (bfd_reloc->addend);
  const int rtn_bits = arg_bits & HPPA_R_RTN_BITS_MASK;
  int type = -1;
  unsigned int reloc_size = 0;

  if (sym_num < SYM_NUM_SIMPLE_RELOC_MAX)
    {
      const int simple_arg_pattern = arg_bits & ~SIMPLE_RELOC_LOWEST_BIT_MASK;

      switch (simple_arg_pattern)
        {
        case ARG_BITS_SIMPLE_CASE_0_PATTERN:
          type = 0;
          break;
        case ARG_BITS_SIMPLE_CASE_1_PATTERN:
          type = 1;
          break;
        case ARG_BITS_SIMPLE_CASE_2_PATTERN:
          type = 2;
          break;
        case ARG_BITS_SIMPLE_CASE_3_PATTERN:
          type = 3;
          break;
        case ARG_BITS_SIMPLE_CASE_4_PATTERN:
          type = 4;
          break;
        default:
          break;
        }

      if (type != -1)
        {
          if (rtn_bits)
            {
              type += SIMPLE_RELOC_RETURN_TYPE_OFFSET;
            }

          bfd_put_8 (abfd, bfd_reloc->howto->type + type, p);
          bfd_put_8 (abfd, (unsigned char)sym_num, p + 1);
          reloc_size = SIMPLE_RELOC_EMITTED_SIZE;
          p = try_prev_fixup (abfd, subspace_reloc_sizep, p, reloc_size, queue);
          return p;
        }
    }

  type = rtn_bits;
  if (((arg_bits >> ARG_BITS_SPECIAL_FIELD1_SHIFT) & ARG_BITS_SPECIAL_FIELD1_MASK) == ARG_BITS_SPECIAL_FIELD1_VALUE)
    {
      type += ARG_BITS_SPECIAL_FIELD1_ADDEND;
    }
  else
    {
      type += (ARG_BITS_NORMAL_FIELD1_COEF_A * ((arg_bits >> ARG_BITS_FIELD1_SHIFT) & ARG_BITS_FIELD1_MASK)
               + ((arg_bits >> ARG_BITS_FIELD2_SHIFT) & ARG_BITS_FIELD2_MASK)) * ARG_BITS_NORMAL_FIELD1_COEF_B;
    }

  if (((arg_bits >> ARG_BITS_SPECIAL_FIELD2_SHIFT) & ARG_BITS_SPECIAL_FIELD2_MASK) == ARG_BITS_SPECIAL_FIELD2_VALUE)
    {
      type += ARG_BITS_SPECIAL_FIELD2_ADDEND;
    }
  else
    {
      type += (ARG_BITS_NORMAL_FIELD2_COEF_A * ((arg_bits >> ARG_BITS_FIELD3_SHIFT) & ARG_BITS_FIELD3_MASK)
               + ((arg_bits >> ARG_BITS_FIELD4_SHIFT) & ARG_BITS_FIELD4_MASK)) * ARG_BITS_NORMAL_FIELD2_COEF_B;
    }

  bfd_put_8 (abfd,
             bfd_reloc->howto->type
             + HARD_RELOC_BASE_TYPE_ADDEND
             + (sym_num >= SYM_NUM_SIMPLE_RELOC_MAX ? HARD_RELOC_SYM_GE_MAX_TYPE_ADDEND : 0)
             + (type >= SYM_NUM_SIMPLE_RELOC_MAX ? HARD_RELOC_TYPE_GE_MAX_TYPE_ADDEND : 0),
             p);
  bfd_put_8 (abfd, (unsigned char)type, p + 1);

  if (sym_num < SYM_NUM_SIMPLE_RELOC_MAX)
    {
      bfd_put_8 (abfd, (unsigned char)sym_num, p + 2);
      reloc_size = HARD_RELOC_SYM_LT_MAX_EMITTED_SIZE;
    }
  else
    {
      bfd_put_8 (abfd, (unsigned char)(sym_num >> SYM_NUM_HIGH_BYTE_SHIFT), p + 2);
      bfd_put_16 (abfd, (bfd_vma) (sym_num & SYM_NUM_LOW_16_BITS_MASK), p + 3);
      reloc_size = HARD_RELOC_SYM_GE_MAX_EMITTED_SIZE;
    }

  p = try_prev_fixup (abfd, subspace_reloc_sizep, p, reloc_size, queue);

  return p;
}

/* Return the logarithm of X, base 2, considering X unsigned,
   if X is a power of 2.  Otherwise, returns -1.  */

static int
exact_log2 (unsigned int x)
{
  // Handle the special case where x is 0, which is not a power of 2.
  if (x == 0) {
    return -1;
  }

  // Check if x is a power of 2.
  // For x > 0, x is a power of 2 if and only if it has only one bit set.
  // This can be efficiently checked by (x & (x - 1)) == 0.
  // If it's not a power of 2, return -1.
  if ((x & (x - 1)) != 0) {
    return -1;
  }

  // At this point, x is guaranteed to be a positive power of 2.
  // Calculate log2 by counting the number of right shifts needed to reach 0.
  int log = 0;
  while ((x >>= 1) != 0) {
    log++;
  }
  return log;
}

static bfd_reloc_status_type
hppa_som_reloc (bfd *abfd ATTRIBUTE_UNUSED,
		arelent *reloc_entry,
		asymbol *symbol_in ATTRIBUTE_UNUSED,
		void *data ATTRIBUTE_UNUSED,
		asection *input_section,
		bfd *output_bfd,
		char **error_message ATTRIBUTE_UNUSED)
{
  if (reloc_entry == NULL)
    {
      return bfd_reloc_bad_value;
    }

  if (input_section == NULL)
    {
      return bfd_reloc_bad_value;
    }

  if (output_bfd)
    {
      reloc_entry->address += input_section->output_offset;
    }

  return bfd_reloc_ok;
}

/* Given a generic HPPA relocation type, the instruction format,
   and a field selector, return one or more appropriate SOM relocations.  */

static int *
alloc_and_set_int (bfd *abfd, int value)
{
  int *ptr = bfd_alloc (abfd, (bfd_size_type) sizeof (int));
  if (ptr)
    *ptr = value;
  return ptr;
}

int **
hppa_som_gen_reloc_type (bfd *abfd,
			 int base_type,
			 int format,
			 enum hppa_reloc_field_selector_type_alt field,
			 int sym_diff,
			 asymbol *sym)
{
  int **reloc_list = bfd_alloc (abfd, (bfd_size_type) sizeof (int *) * 6);
  if (!reloc_list)
    return NULL;

  int *core_reloc_type_ptr = alloc_and_set_int(abfd, base_type);
  if (!core_reloc_type_ptr)
    return NULL;

  int current_list_idx = 0;

  if (sym_diff && (base_type == R_HPPA || base_type == R_HPPA_COMPLEX))
    {
      int *r0_ptr = alloc_and_set_int(abfd, 0);
      int *r1_ptr = alloc_and_set_int(abfd, R_COMP2);
      int *r2_ptr = alloc_and_set_int(abfd, R_COMP2);
      int *r3_ptr = alloc_and_set_int(abfd, R_COMP1);
      int *r4_ptr = alloc_and_set_int(abfd, (format == 32) ? R_DATA_EXPR : R_CODE_EXPR);

      if (!r0_ptr || !r1_ptr || !r2_ptr || !r3_ptr || !r4_ptr)
        return NULL;

      if (field == e_fsel)
        *r0_ptr = R_FSEL;
      else if (field == e_rsel)
        *r0_ptr = R_RSEL;
      else if (field == e_lsel)
        *r0_ptr = R_LSEL;

      reloc_list[0] = r0_ptr;
      reloc_list[1] = r1_ptr;
      reloc_list[2] = r2_ptr;
      reloc_list[3] = r3_ptr;
      reloc_list[4] = r4_ptr;
      reloc_list[5] = NULL;
    }
  else if (base_type == R_HPPA_PCREL_CALL)
    {
#ifndef NO_PCREL_MODES
      int *pcrel_mode_ptr = alloc_and_set_int(abfd, (format == 17) ? R_SHORT_PCREL_MODE : R_LONG_PCREL_MODE);
      if (!pcrel_mode_ptr)
        return NULL;

      reloc_list[0] = pcrel_mode_ptr;
      reloc_list[1] = core_reloc_type_ptr;
      reloc_list[2] = NULL;
#endif
    }
  else
    {
      switch (field)
        {
        case e_fsel:
        case e_psel:
        case e_lpsel:
        case e_rpsel:
          reloc_list[current_list_idx++] = core_reloc_type_ptr;
          break;

        case e_tsel:
        case e_ltsel:
        case e_rtsel:
          {
            int prefix_val;
            if (field == e_tsel)       prefix_val = R_FSEL;
            else if (field == e_ltsel) prefix_val = R_LSEL;
            else                        prefix_val = R_RSEL;
            reloc_list[current_list_idx] = alloc_and_set_int(abfd, prefix_val);
            if (!reloc_list[current_list_idx]) return NULL;
            current_list_idx++;
            reloc_list[current_list_idx++] = core_reloc_type_ptr;
          }
          break;

        case e_lssel: case e_rssel:
          reloc_list[current_list_idx] = alloc_and_set_int(abfd, R_S_MODE);
          if (!reloc_list[current_list_idx]) return NULL;
          current_list_idx++;
          reloc_list[current_list_idx++] = core_reloc_type_ptr;
          break;

        case e_lsel: case e_rsel:
          reloc_list[current_list_idx] = alloc_and_set_int(abfd, R_N_MODE);
          if (!reloc_list[current_list_idx]) return NULL;
          current_list_idx++;
          reloc_list[current_list_idx++] = core_reloc_type_ptr;
          break;

        case e_ldsel: case e_rdsel:
          reloc_list[current_list_idx] = alloc_and_set_int(abfd, R_D_MODE);
          if (!reloc_list[current_list_idx]) return NULL;
          current_list_idx++;
          reloc_list[current_list_idx++] = core_reloc_type_ptr;
          break;

        case e_lrsel: case e_rrsel:
          reloc_list[current_list_idx] = alloc_and_set_int(abfd, R_R_MODE);
          if (!reloc_list[current_list_idx]) return NULL;
          current_list_idx++;
          reloc_list[current_list_idx++] = core_reloc_type_ptr;
          break;

        case e_nsel:
          reloc_list[current_list_idx] = alloc_and_set_int(abfd, R_N1SEL);
          if (!reloc_list[current_list_idx]) return NULL;
          current_list_idx++;
          reloc_list[current_list_idx++] = core_reloc_type_ptr;
          break;

        case e_nlsel: case e_nlrsel:
          reloc_list[current_list_idx] = alloc_and_set_int(abfd, R_N0SEL);
          if (!reloc_list[current_list_idx]) return NULL;
          current_list_idx++;

          int second_prefix_val;
          if (field == e_nlsel)    second_prefix_val = R_N_MODE;
          else                      second_prefix_val = R_R_MODE;
          reloc_list[current_list_idx] = alloc_and_set_int(abfd, second_prefix_val);
          if (!reloc_list[current_list_idx]) return NULL;
          current_list_idx++;
          reloc_list[current_list_idx++] = core_reloc_type_ptr;
          break;

        case e_ltpsel:
        case e_rtpsel:
          abort ();
        }

      reloc_list[current_list_idx] = NULL;

      switch (base_type)
        {
        case R_HPPA:
          if (field == e_psel || field == e_lpsel || field == e_rpsel)
            *core_reloc_type_ptr = (format == 32) ? R_DATA_PLABEL : R_CODE_PLABEL;
          else if (field == e_tsel || field == e_ltsel || field == e_rtsel)
            *core_reloc_type_ptr = R_DLT_REL;
          else if (format == 32)
            {
              *core_reloc_type_ptr = R_DATA_ONE_SYMBOL;

              if (sym && som_symbol_data (sym)->som_type == SYMBOL_TYPE_UNKNOWN
                  && (sym->flags & BSF_SECTION_SYM) == 0
                  && (sym->flags & BSF_FUNCTION) == 0
                  && ! bfd_is_com_section (sym->section))
                som_symbol_data (sym)->som_type = SYMBOL_TYPE_DATA;
            }
          break;

        case R_HPPA_GOTOFF:
          if (field == e_psel || field == e_lpsel || field == e_rpsel)
            *core_reloc_type_ptr = R_DATA_PLABEL;
          else if (field == e_fsel && format == 32)
            *core_reloc_type_ptr = R_DATA_GPREL;
          break;

        case R_HPPA_COMPLEX:
        case R_HPPA_NONE:
        case R_HPPA_ABS_CALL:
        case R_HPPA_PCREL_CALL:
          break;
        }
    }

  return reloc_list;
}

/* Return the address of the correct entry in the PA SOM relocation
   howto table.  */

static reloc_howto_type *
som_bfd_reloc_type_lookup (bfd *abfd ATTRIBUTE_UNUSED,
			   bfd_reloc_code_real_type code)
{
  static const int max_reloc_code_exclusive_bound = (int)R_NO_RELOCATION + 255;
  const int code_val = (int)code;

  if (code_val >= 0 && code_val < max_reloc_code_exclusive_bound)
    {
      BFD_ASSERT(som_hppa_howto_table[code_val].type == code_val);
      return &som_hppa_howto_table[code_val];
    }

  return NULL;
}

static reloc_howto_type *
som_bfd_reloc_name_lookup (bfd *abfd ATTRIBUTE_UNUSED,
                           const char *r_name)
{
  if (r_name == NULL)
    {
      return NULL;
    }

  const size_t table_size = sizeof (som_hppa_howto_table) / sizeof (som_hppa_howto_table[0]);
  size_t i;

  for (i = 0; i < table_size; i++)
    {
      if (som_hppa_howto_table[i].name != NULL
          && strcasecmp (som_hppa_howto_table[i].name, r_name) == 0)
        {
          return &som_hppa_howto_table[i];
        }
    }

  return NULL;
}

static void
som_swap_clock_in (struct som_external_clock *src,
		   struct som_clock *dst)
{
  if (src == ((void*)0) || dst == ((void*)0))
    {
      return;
    }

  dst->secs = bfd_getb32 (src->secs);
  dst->nanosecs = bfd_getb32 (src->nanosecs);
}

static void
som_swap_clock_out (struct som_clock *src,
		    struct som_external_clock *dst)
{
  if (src == NULL || dst == NULL)
    {
      return;
    }

  bfd_putb32 (src->secs, dst->secs);
  bfd_putb32 (src->nanosecs, dst->nanosecs);
}

#define SWAP_SOM_U16(field) dst->field = bfd_getb16(&src->field)
#define SWAP_SOM_U32(field) dst->field = bfd_getb32(&src->field)

static void
som_swap_header_in (struct som_external_header *src,
		    struct som_header *dst)
{
  SWAP_SOM_U16(system_id);
  SWAP_SOM_U16(a_magic);
  SWAP_SOM_U32(version_id);
  som_swap_clock_in (&src->file_time, &dst->file_time);
  SWAP_SOM_U32(entry_space);
  SWAP_SOM_U32(entry_subspace);
  SWAP_SOM_U32(entry_offset);
  SWAP_SOM_U32(aux_header_location);
  SWAP_SOM_U32(aux_header_size);
  SWAP_SOM_U32(som_length);
  SWAP_SOM_U32(presumed_dp);
  SWAP_SOM_U32(space_location);
  SWAP_SOM_U32(space_total);
  SWAP_SOM_U32(subspace_location);
  SWAP_SOM_U32(subspace_total);
  SWAP_SOM_U32(loader_fixup_location);
  SWAP_SOM_U32(loader_fixup_total);
  SWAP_SOM_U32(space_strings_location);
  SWAP_SOM_U32(space_strings_size);
  SWAP_SOM_U32(init_array_location);
  SWAP_SOM_U32(init_array_total);
  SWAP_SOM_U32(compiler_location);
  SWAP_SOM_U32(compiler_total);
  SWAP_SOM_U32(symbol_location);
  SWAP_SOM_U32(symbol_total);
  SWAP_SOM_U32(fixup_request_location);
  SWAP_SOM_U32(fixup_request_total);
  SWAP_SOM_U32(symbol_strings_location);
  SWAP_SOM_U32(symbol_strings_size);
  SWAP_SOM_U32(unloadable_sp_location);
  SWAP_SOM_U32(unloadable_sp_size);
  SWAP_SOM_U32(checksum);
}

#define SOM_SWAP_U16(FIELD) bfd_putb16(src->FIELD, dst->FIELD)
#define SOM_SWAP_U32(FIELD) bfd_putb32(src->FIELD, dst->FIELD)

static void
som_swap_header_out (struct som_header *src,
		    struct som_external_header *dst)
{
  if (!src || !dst)
    {
      return;
    }

  SOM_SWAP_U16 (system_id);
  SOM_SWAP_U16 (a_magic);
  SOM_SWAP_U32 (version_id);
  som_swap_clock_out (&src->file_time, &dst->file_time);
  SOM_SWAP_U32 (entry_space);
  SOM_SWAP_U32 (entry_subspace);
  SOM_SWAP_U32 (entry_offset);
  SOM_SWAP_U32 (aux_header_location);
  SOM_SWAP_U32 (aux_header_size);
  SOM_SWAP_U32 (som_length);
  SOM_SWAP_U32 (presumed_dp);
  SOM_SWAP_U32 (space_location);
  SOM_SWAP_U32 (space_total);
  SOM_SWAP_U32 (subspace_location);
  SOM_SWAP_U32 (subspace_total);
  SOM_SWAP_U32 (loader_fixup_location);
  SOM_SWAP_U32 (loader_fixup_total);
  SOM_SWAP_U32 (space_strings_location);
  SOM_SWAP_U32 (space_strings_size);
  SOM_SWAP_U32 (init_array_location);
  SOM_SWAP_U32 (init_array_total);
  SOM_SWAP_U32 (compiler_location);
  SOM_SWAP_U32 (compiler_total);
  SOM_SWAP_U32 (symbol_location);
  SOM_SWAP_U32 (symbol_total);
  SOM_SWAP_U32 (fixup_request_location);
  SOM_SWAP_U32 (fixup_request_total);
  SOM_SWAP_U32 (symbol_strings_location);
  SOM_SWAP_U32 (symbol_strings_size);
  SOM_SWAP_U32 (unloadable_sp_location);
  SOM_SWAP_U32 (unloadable_sp_size);
  SOM_SWAP_U32 (checksum);
}

static void
som_swap_space_dictionary_in (struct som_external_space_dictionary_record *src,
			      struct som_space_dictionary_record *dst)
{
  if (src == NULL || dst == NULL)
    {
      return;
    }

  unsigned int flags;

  dst->name = bfd_getb32 (src->name);
  flags = bfd_getb32 (src->flags);
  dst->is_loadable = (flags & SOM_SPACE_IS_LOADABLE) != 0;
  dst->is_defined = (flags & SOM_SPACE_IS_DEFINED) != 0;
  dst->is_private = (flags & SOM_SPACE_IS_PRIVATE) != 0;
  dst->has_intermediate_code = (flags & SOM_SPACE_HAS_INTERMEDIATE_CODE) != 0;
  dst->is_tspecific = (flags & SOM_SPACE_IS_TSPECIFIC) != 0;
  dst->reserved = 0;
  dst->sort_key = (flags >> SOM_SPACE_SORT_KEY_SH) & SOM_SPACE_SORT_KEY_MASK;
  dst->reserved2 = 0;
  dst->space_number = bfd_getb32 (src->space_number);
  dst->subspace_index = bfd_getb32 (src->subspace_index);
  dst->subspace_quantity = bfd_getb32 (src->subspace_quantity);
  dst->loader_fix_index = bfd_getb32 (src->loader_fix_index);
  dst->loader_fix_quantity = bfd_getb32 (src->loader_fix_quantity);
  dst->init_pointer_index = bfd_getb32 (src->init_pointer_index);
  dst->init_pointer_quantity = bfd_getb32 (src->init_pointer_quantity);
}

static void
som_swap_space_dictionary_out (const struct som_space_dictionary_record *src,
			       struct som_external_space_dictionary_record *dst)
{
  if (!src || !dst)
    {
      return;
    }

  unsigned int flags;

  bfd_putb32 (src->name, dst->name);

  flags = (src->is_loadable ? SOM_SPACE_IS_LOADABLE : 0)
        | (src->is_defined ? SOM_SPACE_IS_DEFINED : 0)
        | (src->is_private ? SOM_SPACE_IS_PRIVATE : 0)
        | (src->has_intermediate_code ? SOM_SPACE_HAS_INTERMEDIATE_CODE : 0)
        | (src->is_tspecific ? SOM_SPACE_IS_TSPECIFIC : 0)
        | ((src->sort_key & SOM_SPACE_SORT_KEY_MASK) << SOM_SPACE_SORT_KEY_SH);

  bfd_putb32 (flags, dst->flags);
  bfd_putb32 (src->space_number, dst->space_number);
  bfd_putb32 (src->subspace_index, dst->subspace_index);
  bfd_putb32 (src->subspace_quantity, dst->subspace_quantity);
  bfd_putb32 (src->loader_fix_index, dst->loader_fix_index);
  bfd_putb32 (src->loader_fix_quantity, dst->loader_fix_quantity);
  bfd_putb32 (src->init_pointer_index, dst->init_pointer_index);
  bfd_putb32 (src->init_pointer_quantity, dst->init_pointer_quantity);
}

#include <assert.h>

static void
som_swap_subspace_dictionary_in
  (struct som_external_subspace_dictionary_record *src,
   struct som_subspace_dictionary_record *dst)
{
  assert(src != NULL);
  assert(dst != NULL);

  unsigned int flags;

  dst->space_index = bfd_getb32 (src->space_index);

  flags = bfd_getb32 (src->flags);
  dst->access_control_bits = (flags >> SOM_SUBSPACE_ACCESS_CONTROL_BITS_SH)
    & SOM_SUBSPACE_ACCESS_CONTROL_BITS_MASK;
  dst->memory_resident = (flags & SOM_SUBSPACE_MEMORY_RESIDENT) != 0;
  dst->dup_common = (flags & SOM_SUBSPACE_DUP_COMMON) != 0;
  dst->is_common = (flags & SOM_SUBSPACE_IS_COMMON) != 0;
  dst->is_loadable = (flags & SOM_SUBSPACE_IS_LOADABLE) != 0;
  dst->quadrant = (flags >> SOM_SUBSPACE_QUADRANT_SH)
    & SOM_SUBSPACE_QUADRANT_MASK;
  dst->initially_frozen = (flags & SOM_SUBSPACE_INITIALLY_FROZEN) != 0;
  dst->is_first = (flags & SOM_SUBSPACE_IS_FIRST) != 0;
  dst->code_only = (flags & SOM_SUBSPACE_CODE_ONLY) != 0;
  dst->sort_key = (flags >> SOM_SUBSPACE_SORT_KEY_SH)
    & SOM_SUBSPACE_SORT_KEY_MASK;
  dst->replicate_init = (flags & SOM_SUBSPACE_REPLICATE_INIT) != 0;
  dst->continuation = (flags & SOM_SUBSPACE_CONTINUATION) != 0;
  dst->is_tspecific = (flags & SOM_SUBSPACE_IS_TSPECIFIC) != 0;
  dst->is_comdat = (flags & SOM_SUBSPACE_IS_COMDAT) != 0;

  dst->reserved = 0;

  dst->file_loc_init_value = bfd_getb32 (src->file_loc_init_value);
  dst->initialization_length = bfd_getb32 (src->initialization_length);
  dst->subspace_start = bfd_getb32 (src->subspace_start);
  dst->subspace_length = bfd_getb32 (src->subspace_length);
  dst->alignment = bfd_getb32 (src->alignment);
  dst->name = bfd_getb32 (src->name);
  dst->fixup_request_index = bfd_getb32 (src->fixup_request_index);
  dst->fixup_request_quantity = bfd_getb32 (src->fixup_request_quantity);
}

static void
som_swap_subspace_dictionary_record_out
  (struct som_subspace_dictionary_record *src,
   struct som_external_subspace_dictionary_record *dst)
{
  unsigned int flags;

  if (src == NULL || dst == NULL)
    {
      return;
    }

  bfd_putb32 (src->space_index, dst->space_index);

  flags = ((src->access_control_bits & SOM_SUBSPACE_ACCESS_CONTROL_BITS_MASK)
           << SOM_SUBSPACE_ACCESS_CONTROL_BITS_SH)
        | ((src->quadrant & SOM_SUBSPACE_QUADRANT_MASK)
           << SOM_SUBSPACE_QUADRANT_SH)
        | ((src->sort_key & SOM_SUBSPACE_SORT_KEY_MASK)
           << SOM_SUBSPACE_SORT_KEY_SH);

  if (src->memory_resident)
    flags |= SOM_SUBSPACE_MEMORY_RESIDENT;
  if (src->dup_common)
    flags |= SOM_SUBSPACE_DUP_COMMON;
  if (src->is_common)
    flags |= SOM_SUBSPACE_IS_COMMON;
  if (src->is_loadable)
    flags |= SOM_SUBSPACE_IS_LOADABLE;
  if (src->initially_frozen)
    flags |= SOM_SUBSPACE_INITIALLY_FROZEN;
  if (src->is_first)
    flags |= SOM_SUBSPACE_IS_FIRST;
  if (src->code_only)
    flags |= SOM_SUBSPACE_CODE_ONLY;
  if (src->replicate_init)
    flags |= SOM_SUBSPACE_REPLICATE_INIT;
  if (src->continuation)
    flags |= SOM_SUBSPACE_CONTINUATION;
  if (src->is_tspecific)
    flags |= SOM_SUBSPACE_IS_TSPECIFIC;
  if (src->is_comdat)
    flags |= SOM_SUBSPACE_IS_COMDAT;

  bfd_putb32 (flags, dst->flags);
  bfd_putb32 (src->file_loc_init_value, dst->file_loc_init_value);
  bfd_putb32 (src->initialization_length, dst->initialization_length);
  bfd_putb32 (src->subspace_start, dst->subspace_start);
  bfd_putb32 (src->subspace_length, dst->subspace_length);
  bfd_putb32 (src->alignment, dst->alignment);
  bfd_putb32 (src->name, dst->name);
  bfd_putb32 (src->fixup_request_index, dst->fixup_request_index);
  bfd_putb32 (src->fixup_request_quantity, dst->fixup_request_quantity);
}

static void
som_swap_aux_id_in (struct som_external_aux_id *src,
		    struct som_aux_id *dst)
{
  if (src == NULL || dst == NULL)
    {
      return;
    }

  unsigned int flags = bfd_getb32 (src->flags);

  dst->mandatory = (flags & SOM_AUX_ID_MANDATORY) != 0;
  dst->copy = (flags & SOM_AUX_ID_COPY) != 0;
  dst->append = (flags & SOM_AUX_ID_APPEND) != 0;
  dst->ignore = (flags & SOM_AUX_ID_IGNORE) != 0;
  dst->type = (flags >> SOM_AUX_ID_TYPE_SH) & SOM_AUX_ID_TYPE_MASK;
  dst->length = bfd_getb32 (src->length);
}

static void
som_swap_aux_id_out (struct som_aux_id *src,
		    struct som_external_aux_id *dst)
{
  if (src == NULL || dst == NULL)
    {
      return;
    }

  unsigned int flags = 0;

  flags |= src->mandatory ? SOM_AUX_ID_MANDATORY : 0;
  flags |= src->copy ? SOM_AUX_ID_COPY : 0;
  flags |= src->append ? SOM_AUX_ID_APPEND : 0;
  flags |= src->ignore ? SOM_AUX_ID_IGNORE : 0;
  flags |= (src->type & SOM_AUX_ID_TYPE_MASK) << SOM_AUX_ID_TYPE_SH;

  bfd_putb32 (flags, dst->flags);
  bfd_putb32 (src->length, dst->length);
}

static void
som_swap_string_auxhdr_out (const struct som_string_auxhdr *src,
			    struct som_external_string_auxhdr *dst)
{
  assert(src != NULL);
  assert(dst != NULL);
  som_swap_aux_id_out (&src->header_id, &dst->header_id);
  bfd_putb32 (src->string_length, dst->string_length);
}

static int
som_swap_compilation_unit_out (struct som_compilation_unit *src,
                               struct som_external_compilation_unit *dst)
{
  if (src == NULL || dst == NULL)
    {
      /*
       * In a production environment, consider logging an error here
       * to provide insights into why the operation failed.
       * For reliability, explicitly checking for NULL inputs and
       * returning an error status is crucial.
       */
      return 1; /* Indicate failure due to invalid input pointers. */
    }

  bfd_putb32 (src->name.strx, dst->name);
  bfd_putb32 (src->language_name.strx, dst->language_name);
  bfd_putb32 (src->product_id.strx, dst->product_id);
  bfd_putb32 (src->version_id.strx, dst->version_id);
  bfd_putb32 (src->flags, dst->flags);
  som_swap_clock_out (&src->compile_time, &dst->compile_time);
  som_swap_clock_out (&src->source_time, &dst->source_time);

  return 0; /* Indicate success. */
}

static int
som_swap_exec_auxhdr_in (struct som_external_exec_auxhdr *src,
			 struct som_exec_auxhdr *dst)
{
  if (src == NULL || dst == NULL)
    {
      return -1;
    }

  som_swap_aux_id_in (&src->som_auxhdr, &dst->som_auxhdr);

  dst->exec_tsize = bfd_getb32 (src->exec_tsize);
  dst->exec_tmem = bfd_getb32 (src->exec_tmem);
  dst->exec_tfile = bfd_getb32 (src->exec_tfile);
  dst->exec_dsize = bfd_getb32 (src->exec_dsize);
  dst->exec_dmem = bfd_getb32 (src->exec_dmem);
  dst->exec_dfile = bfd_getb32 (src->exec_dfile);
  dst->exec_bsize = bfd_getb32 (src->exec_bsize);
  dst->exec_entry = bfd_getb32 (src->exec_entry);
  dst->exec_flags = bfd_getb32 (src->exec_flags);
  dst->exec_bfill = bfd_getb32 (src->exec_bfill);

  return 0;
}

static void
som_swap_exec_auxhdr_out (struct som_exec_auxhdr *src,
			 struct som_external_exec_auxhdr *dst)
{
  if (src == NULL || dst == NULL)
    {
      return;
    }

  som_swap_aux_id_out (&src->som_auxhdr, &dst->som_auxhdr);
  bfd_putb32 (src->exec_tsize, dst->exec_tsize);
  bfd_putb32 (src->exec_tmem, dst->exec_tmem);
  bfd_putb32 (src->exec_tfile, dst->exec_tfile);
  bfd_putb32 (src->exec_dsize, dst->exec_dsize);
  bfd_putb32 (src->exec_dmem, dst->exec_dmem);
  bfd_putb32 (src->exec_dfile, dst->exec_dfile);
  bfd_putb32 (src->exec_bsize, dst->exec_bsize);
  bfd_putb32 (src->exec_entry, dst->exec_entry);
  bfd_putb32 (src->exec_flags, dst->exec_flags);
  bfd_putb32 (src->exec_bfill, dst->exec_bfill);
}

static void
som_swap_lst_header_in (struct som_external_lst_header *src,
			struct som_lst_header *dst)
{
  if (src == NULL || dst == NULL)
    {
      return;
    }

  dst->system_id = bfd_getb16 (src->system_id);
  dst->a_magic = bfd_getb16 (src->a_magic);
  dst->version_id = bfd_getb32 (src->version_id);
  som_swap_clock_in (&src->file_time, &dst->file_time);
  dst->hash_loc = bfd_getb32 (src->hash_loc);
  dst->hash_size = bfd_getb32 (src->hash_size);
  dst->module_count = bfd_getb32 (src->module_count);
  dst->module_limit = bfd_getb32 (src->module_limit);
  dst->dir_loc = bfd_getb32 (src->dir_loc);
  dst->export_loc = bfd_getb32 (src->export_loc);
  dst->export_count = bfd_getb32 (src->export_count);
  dst->import_loc = bfd_getb32 (src->import_loc);
  dst->aux_loc = bfd_getb32 (src->aux_loc);
  dst->aux_size = bfd_getb32 (src->aux_size);
  dst->string_loc = bfd_getb32 (src->string_loc);
  dst->string_size = bfd_getb32 (src->string_size);
  dst->free_list = bfd_getb32 (src->free_list);
  dst->file_end = bfd_getb32 (src->file_end);
  dst->checksum = bfd_getb32 (src->checksum);
}

/* Perform some initialization for an object.  Save results of this
   initialization in the BFD.  */

static bfd_cleanup
som_object_setup (bfd *abfd,
		  struct som_header *file_hdrp,
		  struct som_exec_auxhdr *aux_hdrp,
		  unsigned long current_offset)
{
  asection *section;

  if (! som_mkobject (abfd))
    return NULL;

  abfd->flags = BFD_NO_FLAGS;
  if (file_hdrp->symbol_total)
    abfd->flags |= HAS_LINENO | HAS_DEBUG | HAS_SYMS | HAS_LOCALS;

  switch (file_hdrp->a_magic)
    {
    case DEMAND_MAGIC:
      abfd->flags |= (D_PAGED | WP_TEXT | EXEC_P);
      break;
    case SHARE_MAGIC:
      abfd->flags |= (WP_TEXT | EXEC_P);
      break;
    case EXEC_MAGIC:
      abfd->flags |= (EXEC_P);
      break;
    case RELOC_MAGIC:
      abfd->flags |= HAS_RELOC;
      break;
#ifdef SHL_MAGIC
    case SHL_MAGIC:
#endif
#ifdef DL_MAGIC
    case DL_MAGIC:
#endif
      abfd->flags |= DYNAMIC;
      break;

    default:
      break;
    }

  obj_som_exec_hdr (abfd) = aux_hdrp;

  obj_som_exec_data (abfd) = bfd_zalloc (abfd, (bfd_size_type) sizeof (struct som_exec_data));
  if (obj_som_exec_data (abfd) == NULL)
    return NULL;

  if (aux_hdrp)
    {
      bool entry_found_in_code_section = false;
      bfd_vma effective_entry_address = aux_hdrp->exec_entry + aux_hdrp->exec_tmem;

      for (section = abfd->sections; section; section = section->next)
	{
	  if ((section->flags & SEC_CODE) == 0)
	    continue;
	  if (effective_entry_address >= section->vma
	      && effective_entry_address < section->vma + section->size)
	    {
	      entry_found_in_code_section = true;
	      break;
	    }
	}

      bool is_main_program = !(abfd->flags & DYNAMIC);
      bool is_entry_zero_and_main_program = (aux_hdrp->exec_entry == 0 && is_main_program);
      bool is_entry_unaligned = (aux_hdrp->exec_entry & 0x3) != 0;
      bool assume_linker_bug = is_entry_zero_and_main_program || is_entry_unaligned || !entry_found_in_code_section;

      if (assume_linker_bug)
	{
	  abfd->start_address = aux_hdrp->exec_flags;
	  obj_som_exec_data (abfd)->exec_flags = aux_hdrp->exec_entry;
	}
      else
	{
	  abfd->start_address = aux_hdrp->exec_entry + current_offset;
	  obj_som_exec_data (abfd)->exec_flags = aux_hdrp->exec_flags;
	}
    }

  obj_som_exec_data (abfd)->version_id = file_hdrp->version_id;

  bfd_default_set_arch_mach (abfd, bfd_arch_hppa, pa10);
  abfd->symcount = file_hdrp->symbol_total;

  obj_som_stringtab (abfd) = NULL;
  obj_som_symtab (abfd) = NULL;
  obj_som_sorted_syms (abfd) = NULL;
  obj_som_stringtab_size (abfd) = file_hdrp->symbol_strings_size;
  obj_som_sym_filepos (abfd) = file_hdrp->symbol_location + current_offset;
  obj_som_str_filepos (abfd) = (file_hdrp->symbol_strings_location
				+ current_offset);
  obj_som_reloc_filepos (abfd) = (file_hdrp->fixup_request_location
				  + current_offset);
  obj_som_exec_data (abfd)->system_id = file_hdrp->system_id;

  return _bfd_no_cleanup;
}

/* Convert all of the space and subspace info into BFD sections.  Each space
   contains a number of subspaces, which in turn describe the mapping between
   regions of the exec file, and the address space that the program runs in.
   BFD sections which correspond to spaces will overlap the sections for the
   associated subspaces.  */

static bool
read_bfd_file_offset(bfd *abfd, void *buf, size_t size, bfd_vma file_offset)
{
  if (bfd_seek(abfd, file_offset, SEEK_SET) != 0) {
    return false;
  }
  if (bfd_read(buf, size, abfd) != size) {
    return false;
  }
  return true;
}

static asection *
create_bfd_section_from_name(bfd *abfd, const char *original_name)
{
  size_t len = strlen(original_name) + 1;
  char *newname = bfd_alloc(abfd, len);
  if (!newname) {
    bfd_set_error(bfd_error_no_memory);
    return NULL;
  }
  strcpy(newname, original_name);
  asection *section = bfd_make_section_anyway(abfd, newname);
  if (!section) {
    // bfd_make_section_anyway is expected to set BFD error on failure.
    // Memory for newname is BFD-managed, no manual free needed.
  }
  return section;
}

static bool
set_subspace_section_flags(asection *subspace_asect,
                           const struct som_subspace_dictionary_record *subspace)
{
  switch (subspace->access_control_bits >> 4) {
    case 0x0:
      subspace_asect->flags |= SEC_DATA | SEC_READONLY;
      break;
    case 0x1:
      subspace_asect->flags |= SEC_DATA;
      break;
    case 0x2:
    case 0x4:
    case 0x5:
    case 0x6:
    case 0x7:
      subspace_asect->flags |= SEC_CODE | SEC_READONLY;
      break;
    case 0x3:
      subspace_asect->flags |= SEC_CODE;
      break;
  }

  if (subspace->is_comdat || subspace->is_common || subspace->dup_common)
    subspace_asect->flags |= SEC_LINK_ONCE;

  if (subspace->subspace_length > 0)
    subspace_asect->flags |= SEC_HAS_CONTENTS;

  if (subspace->is_loadable)
    subspace_asect->flags |= SEC_ALLOC | SEC_LOAD;
  else
    subspace_asect->flags |= SEC_DEBUGGING;

  if (subspace->code_only)
    subspace_asect->flags |= SEC_CODE;

  if (subspace->file_loc_init_value == 0 && subspace->initialization_length == 0)
    subspace_asect->flags &= ~(SEC_DATA | SEC_LOAD | SEC_HAS_CONTENTS);

  if (subspace->fixup_request_quantity != 0) {
    subspace_asect->flags |= SEC_RELOC;
    subspace_asect->rel_filepos = subspace->fixup_request_index;
    som_section_data(subspace_asect)->reloc_size = subspace->fixup_request_quantity;
    subspace_asect->reloc_count = (unsigned) -1;
  }
  return true;
}

static bool
setup_sections (bfd *abfd,
		struct som_header *file_hdr,
		unsigned long current_offset)
{
  char *space_strings = NULL;
  asection **subspace_sections = NULL;
  bool success = false;

  size_t space_strings_amt = file_hdr->space_strings_size;
  if (space_strings_amt == (size_t) -1) {
    bfd_set_error(bfd_error_no_memory);
    goto cleanup;
  }
  if (bfd_seek(abfd, current_offset + file_hdr->space_strings_location, SEEK_SET) != 0) {
    goto cleanup;
  }
  space_strings = (char *) _bfd_malloc_and_read(abfd, space_strings_amt + 1, space_strings_amt);
  if (space_strings == NULL) {
    goto cleanup;
  }
  space_strings[space_strings_amt] = 0;

  unsigned int total_subspaces = 0;

  for (unsigned int space_index = 0; space_index < file_hdr->space_total; ++space_index) {
    struct som_space_dictionary_record space;
    struct som_external_space_dictionary_record ext_space;
    asection *space_asect = NULL;
    bfd_size_type space_size_accumulated = 0;
    
    bfd_vma space_record_file_offset = current_offset + file_hdr->space_location + space_index * sizeof(ext_space);
    if (!read_bfd_file_offset(abfd, &ext_space, sizeof(ext_space), space_record_file_offset)) {
      goto cleanup;
    }
    som_swap_space_dictionary_in(&ext_space, &space);

    if (space.name >= file_hdr->space_strings_size) {
      bfd_set_error(bfd_error_bad_value);
      goto cleanup;
    }
    char *space_name = space.name + space_strings;

    space_asect = create_bfd_section_from_name(abfd, space_name);
    if (!space_asect) {
      goto cleanup;
    }

    if (space.is_loadable == 0) {
      space_asect->flags |= SEC_DEBUGGING;
    }

    if (!bfd_som_set_section_attributes(space_asect, space.is_defined,
                                        space.is_private, space.sort_key,
                                        space.space_number)) {
      goto cleanup;
    }

    if (space.subspace_quantity == 0) {
      continue;
    }

    struct som_external_subspace_dictionary_record ext_subspace;
    struct som_subspace_dictionary_record subspace;
    struct som_subspace_dictionary_record save_subspace_for_size_calc;

    memset(&save_subspace_for_size_calc, 0, sizeof(save_subspace_for_size_calc));

    bfd_vma first_subspace_record_file_offset = current_offset + file_hdr->subspace_location + space.subspace_index * sizeof(ext_subspace);
    if (bfd_seek(abfd, first_subspace_record_file_offset, SEEK_SET) != 0) {
        goto cleanup;
    }

    for (unsigned int subspace_idx = 0; subspace_idx < space.subspace_quantity; ++subspace_idx) {
      asection *subspace_asect = NULL;

      size_t amt_ext_subspace = sizeof(ext_subspace);
      if (bfd_read(&ext_subspace, amt_ext_subspace, abfd) != amt_ext_subspace) {
        goto cleanup;
      }
      som_swap_subspace_dictionary_in(&ext_subspace, &subspace);

      if (subspace_idx == 0) {
        space_asect->vma = subspace.subspace_start;
        space_asect->filepos = subspace.file_loc_init_value + current_offset;
        space_asect->alignment_power = exact_log2(subspace.alignment);
        if (space_asect->alignment_power == (unsigned) -1) {
          bfd_set_error(bfd_error_bad_value);
          goto cleanup;
        }
      }

      if (subspace.name >= file_hdr->space_strings_size) {
        bfd_set_error(bfd_error_bad_value);
        goto cleanup;
      }
      char *subspace_name = subspace.name + space_strings;

      subspace_asect = create_bfd_section_from_name(abfd, subspace_name);
      if (!subspace_asect) {
        goto cleanup;
      }

      if (!bfd_som_set_subsection_attributes(subspace_asect, space_asect,
                                             subspace.access_control_bits,
                                             subspace.sort_key,
                                             subspace.quadrant,
                                             subspace.is_comdat,
                                             subspace.is_common,
                                             subspace.dup_common)) {
        goto cleanup;
      }

      total_subspaces++;
      subspace_asect->target_index = bfd_tell(abfd) - sizeof(ext_subspace);

      if (!set_subspace_section_flags(subspace_asect, &subspace)) {
        goto cleanup;
      }

      if (subspace.file_loc_init_value > save_subspace_for_size_calc.file_loc_init_value) {
        save_subspace_for_size_calc = subspace;
      }

      subspace_asect->vma = subspace.subspace_start;
      subspace_asect->size = subspace.subspace_length;
      subspace_asect->filepos = (subspace.file_loc_init_value + current_offset);
      subspace_asect->alignment_power = exact_log2(subspace.alignment);
      if (subspace_asect->alignment_power == (unsigned) -1) {
        bfd_set_error(bfd_error_bad_value);
        goto cleanup;
      }

      space_size_accumulated += subspace.subspace_length;
    }

    if (!save_subspace_for_size_calc.file_loc_init_value) {
      space_asect->size = 0;
    } else {
      if (file_hdr->a_magic != RELOC_MAGIC) {
        space_asect->size = (save_subspace_for_size_calc.subspace_start
                             - space_asect->vma
                             + save_subspace_for_size_calc.subspace_length);
      } else {
        space_asect->size = space_size_accumulated;
      }
    }
  }

  if (total_subspaces > 0) {
    size_t amt_subspace_sections_mem;
    if (_bfd_mul_overflow(total_subspaces, sizeof(asection *), &amt_subspace_sections_mem)) {
      bfd_set_error(bfd_error_file_too_big);
      goto cleanup;
    }
    subspace_sections = bfd_malloc(amt_subspace_sections_mem);
    if (subspace_sections == NULL) {
      bfd_set_error(bfd_error_no_memory);
      goto cleanup;
    }

    unsigned int current_subspace_count = 0;
    for (asection *section = abfd->sections; section; section = section->next) {
      if (som_is_subspace(section)) {
        if (current_subspace_count >= total_subspaces) {
          bfd_set_error(bfd_error_bad_value);
          goto cleanup;
        }
        subspace_sections[current_subspace_count] = section;
        current_subspace_count++;
      }
    }
    if (current_subspace_count != total_subspaces) {
        bfd_set_error(bfd_error_bad_value);
        goto cleanup;
    }

    qsort(subspace_sections, total_subspaces, sizeof(asection *), compare_subspaces);

    for (unsigned int i = 0; i < total_subspaces; ++i) {
      subspace_sections[i]->target_index = i;
    }
  }

  success = true;

cleanup:
  free(space_strings);
  free(subspace_sections);
  return success;
}


/* Read in a SOM object and make it into a BFD.  */

static bfd_boolean som_read_data(bfd *abfd, void *buf, size_t amt) {
    if (bfd_read(buf, amt, abfd) != amt) {
        if (bfd_get_error() != bfd_error_system_call) {
            bfd_set_error(bfd_error_wrong_format);
        }
        return FALSE;
    }
    return TRUE;
}

static bfd_boolean som_seek_file(bfd *abfd, file_ptr offset) {
    if (bfd_seek(abfd, offset, SEEK_SET) != 0) {
        if (bfd_get_error() != bfd_error_system_call) {
            bfd_set_error(bfd_error_wrong_format);
        }
        return FALSE;
    }
    return TRUE;
}

static bfd_boolean som_handle_execlib_magic(bfd *abfd,
                                            struct som_external_header *ext_file_hdr_ptr,
                                            struct som_header *file_hdr_ptr,
                                            unsigned long *current_offset_ptr) {
    struct som_external_lst_header ext_lst_header;
    struct som_external_som_entry ext_som_entry;
    unsigned int loc;

    if (!som_seek_file(abfd, 0)) {
        return FALSE;
    }
    if (!som_read_data(abfd, &ext_lst_header, sizeof(ext_lst_header))) {
        return FALSE;
    }

    loc = bfd_getb32(ext_lst_header.dir_loc);
    if (!som_seek_file(abfd, loc)) {
        return FALSE;
    }
    if (!som_read_data(abfd, &ext_som_entry, sizeof(ext_som_entry))) {
        return FALSE;
    }

    *current_offset_ptr = bfd_getb32(ext_som_entry.location);
    if (!som_seek_file(abfd, *current_offset_ptr)) {
        return FALSE;
    }

    if (!som_read_data(abfd, ext_file_hdr_ptr, sizeof(*ext_file_hdr_ptr))) {
        return FALSE;
    }
    som_swap_header_in(ext_file_hdr_ptr, file_hdr_ptr);

    return TRUE;
}

static void *
som_object_p (bfd *abfd)
{
  struct som_external_header ext_file_hdr;
  struct som_header file_hdr;
  struct som_exec_auxhdr *aux_hdr_ptr = NULL;
  unsigned long current_offset = 0;

  if (!som_read_data(abfd, &ext_file_hdr, sizeof(ext_file_hdr))) {
    return NULL;
  }
  som_swap_header_in(&ext_file_hdr, &file_hdr);

  if (!_PA_RISC_ID(file_hdr.system_id)) {
    bfd_set_error(bfd_error_wrong_format);
    return NULL;
  }

  switch (file_hdr.a_magic) {
    case RELOC_MAGIC:
    case EXEC_MAGIC:
    case SHARE_MAGIC:
    case DEMAND_MAGIC:
    case DL_MAGIC:
    case SHL_MAGIC:
#ifdef SHARED_MAGIC_CNX
    case SHARED_MAGIC_CNX:
#endif
      break;

    case EXECLIBMAGIC:
      if (!som_handle_execlib_magic(abfd, &ext_file_hdr, &file_hdr, &current_offset)) {
        return NULL;
      }
      break;

    default:
      bfd_set_error(bfd_error_wrong_format);
      return NULL;
  }

  if (file_hdr.version_id != OLD_VERSION_ID && file_hdr.version_id != NEW_VERSION_ID) {
    bfd_set_error(bfd_error_wrong_format);
    return NULL;
  }

  if (file_hdr.aux_header_size != 0) {
    struct som_external_exec_auxhdr ext_exec_auxhdr;

    aux_hdr_ptr = bfd_zalloc(abfd, (bfd_size_type)sizeof(*aux_hdr_ptr));
    if (aux_hdr_ptr == NULL) {
      return NULL;
    }
    if (!som_read_data(abfd, &ext_exec_auxhdr, sizeof(ext_exec_auxhdr))) {
      return NULL;
    }
    som_swap_exec_auxhdr_in(&ext_exec_auxhdr, aux_hdr_ptr);
  }

  if (!setup_sections(abfd, &file_hdr, current_offset)) {
    bfd_set_error(bfd_error_bad_value);
    return NULL;
  }

  return som_object_setup(abfd, &file_hdr, aux_hdr_ptr, current_offset);
}

/* Create a SOM object.  */

static bool
som_mkobject (bfd *abfd)
{
  abfd->tdata.som_data = bfd_zalloc (abfd, (bfd_size_type) sizeof (struct som_data_struct));
  return abfd->tdata.som_data != NULL;
}

/* Initialize some information in the file header.  This routine makes
   not attempt at doing the right thing for a full executable; it
   is only meant to handle relocatable objects.  */

static bool som_prep_space_section(bfd *abfd, asection *section);
static bool som_prep_subspace_section(bfd *abfd, asection *section);

static bool
som_prep_space_section (bfd *abfd, asection *section)
{
  struct som_section_data *sd = som_section_data (section);
  if (sd == NULL)
    return false;

  sd->space_dict = bfd_zalloc (abfd, sizeof (struct som_space_dictionary_record));
  if (sd->space_dict == NULL)
    return false;

  sd->space_dict->loader_fix_index = -1;
  sd->space_dict->init_pointer_index = -1;

  const struct som_section_copy_data *scd = sd->copy_data;
  if (scd == NULL)
    return false;

  sd->space_dict->sort_key = scd->sort_key;
  sd->space_dict->is_defined = scd->is_defined;
  sd->space_dict->is_private = scd->is_private;
  sd->space_dict->space_number = scd->space_number;

  return true;
}

static bool
som_prep_subspace_section (bfd *abfd, asection *section)
{
  struct som_section_data *sd = som_section_data (section);
  if (sd == NULL)
    return false;

  sd->subspace_dict = bfd_zalloc (abfd, sizeof (struct som_subspace_dictionary_record));
  if (sd->subspace_dict == NULL)
    return false;

  if (section->flags & SEC_ALLOC)
    sd->subspace_dict->is_loadable = 1;
  if (section->flags & SEC_CODE)
    sd->subspace_dict->code_only = 1;

  sd->subspace_dict->subspace_start = section->vma;
  sd->subspace_dict->subspace_length = section->size;
  sd->subspace_dict->initialization_length = section->size;
  sd->subspace_dict->alignment = 1 << section->alignment_power;

  const struct som_section_copy_data *scd = sd->copy_data;
  if (scd == NULL)
    return false;

  sd->subspace_dict->sort_key = scd->sort_key;
  sd->subspace_dict->access_control_bits = scd->access_control_bits;
  sd->subspace_dict->quadrant = scd->quadrant;
  sd->subspace_dict->is_comdat = scd->is_comdat;
  sd->subspace_dict->is_common = scd->is_common;
  sd->subspace_dict->dup_common = scd->dup_common;

  return true;
}

static bool
som_prep_headers (bfd *abfd)
{
  struct som_header *file_hdr;
  asection *section;

  file_hdr = bfd_zalloc (abfd, sizeof (struct som_header));
  if (file_hdr == NULL)
    return false;
  obj_som_file_hdr (abfd) = file_hdr;

  if (abfd->flags & (EXEC_P | DYNAMIC))
    {
      obj_som_exec_hdr (abfd) = bfd_zalloc (abfd, sizeof (struct som_exec_auxhdr));
      if (obj_som_exec_hdr (abfd) == NULL)
	return false;

      if (abfd->flags & D_PAGED)
	file_hdr->a_magic = DEMAND_MAGIC;
      else if (abfd->flags & WP_TEXT)
	file_hdr->a_magic = SHARE_MAGIC;
#ifdef SHL_MAGIC
      else if (abfd->flags & DYNAMIC)
	file_hdr->a_magic = SHL_MAGIC;
#endif
      else
	file_hdr->a_magic = EXEC_MAGIC;
    }
  else
    file_hdr->a_magic = RELOC_MAGIC;

  file_hdr->file_time.secs = 0;
  file_hdr->file_time.nanosecs = 0;
  file_hdr->entry_space = 0;
  file_hdr->entry_subspace = 0;
  file_hdr->entry_offset = 0;
  file_hdr->presumed_dp = 0;

  for (section = abfd->sections; section != NULL; section = section->next)
    {
      if (som_is_space (section))
	{
	  if (!som_prep_space_section (abfd, section))
	    return false;
	}
      else if (som_is_subspace (section))
	{
	  if (!som_prep_subspace_section (abfd, section))
	    return false;
	}
    }
  return true;
}

/* Return TRUE if the given section is a SOM space, FALSE otherwise.  */

static bool
som_is_space (asection *section)
{
  /* Improve Reliability and Security: Add a defensive NULL check for the input 'section'.
     Passing NULL to internal utility functions often leads to undefined behavior. */
  if (section == NULL)
    return false;

  /* Improve Maintainability: Store the result of som_section_data(section) in a local variable
     to avoid repeated calls and improve readability, especially if som_section_data
     is a complex or potentially expensive operation. */
  struct som_section_data_struct *section_data = som_section_data (section);

  /* The original logic implies that som_section_data(section) always returns a valid
     pointer to struct som_section_data_struct, but its 'copy_data' member can be NULL.
     This check handles that first condition. */
  if (section_data->copy_data == NULL)
    return false;

  /* Improve Maintainability: Store the 'copy_data' pointer in a local variable
     to simplify the subsequent logic and prevent redundant dereferences. */
  struct som_copy_data_struct *copy_data = section_data->copy_data;

  /* Simplify complex logic: The original second condition returned 'false' if
     (copy_data->container != section) AND (copy_data->container->output_section != section).
     This is logically equivalent to returning 'true' if
     (copy_data->container == section) OR (copy_data->container->output_section == section).
     This single return statement makes the boolean logic clearer and more concise. */
  return copy_data->container == section || copy_data->container->output_section == section;
}

/* Return TRUE if the given section is a SOM subspace, FALSE otherwise.  */

static bool
som_is_subspace (asection *section)
{
  struct som_section_info *info = som_section_data(section);
  struct som_copy_data *copy_data = info->copy_data;

  if (copy_data == NULL) {
    return false;
  }

  asection *container = copy_data->container;

  if (container == section || container->output_section == section) {
    return false;
  }

  return true;
}

/* Return TRUE if the given space contains the given subspace.  It
   is safe to assume space really is a space, and subspace really
   is a subspace.  */

static bool
som_is_container (asection *space, asection *subspace)
{
  struct section_data *sd = som_section_data(subspace);
  if (sd == NULL)
    {
      return false;
    }

  struct copy_data *cd = sd->copy_data;
  if (cd == NULL)
    {
      return false;
    }

  if (cd->container == space)
    {
      return true;
    }

  if (cd->container != NULL && cd->container->output_section == space)
    {
      return true;
    }

  return false;
}

/* Count and return the number of spaces attached to the given BFD.  */

static unsigned long
som_count_spaces (bfd *abfd)
{
  unsigned long count = 0;
  asection *section;

  if (abfd == NULL)
  {
    return 0;
  }

  for (section = abfd->sections; section != NULL; section = section->next)
  {
    count += som_is_space (section);
  }

  return count;
}

/* Count the number of subspaces attached to the given BFD.  */

static unsigned long
som_count_subspaces (bfd *abfd)
{
  if (abfd == NULL) {
    return 0;
  }

  unsigned long count = 0;
  asection *section;

  for (section = abfd->sections; section != NULL; section = section->next) {
    count += (unsigned long) som_is_subspace (section);
  }

  return count;
}

/* Return -1, 0, 1 indicating the relative ordering of sym1 and sym2.

   We desire symbols to be ordered starting with the symbol with the
   highest relocation count down to the symbol with the lowest relocation
   count.  Doing so compacts the relocation stream.  */

static unsigned int
get_symbol_reloc_count (const asymbol *sym)
{
  if (sym->flags & BSF_SECTION_SYM)
    return sym->udata.i;
  else
    return som_symbol_data (sym)->reloc_count;
}

static int
compare_syms (const void *arg1, const void *arg2)
{
  const asymbol *sym1 = *(const asymbol **) arg1;
  const asymbol *sym2 = *(const asymbol **) arg2;

  unsigned int count1 = get_symbol_reloc_count (sym1);
  unsigned int count2 = get_symbol_reloc_count (sym2);

  if (count1 < count2)
    return 1;
  else if (count1 > count2)
    return -1;
  return 0;
}

/* Return -1, 0, 1 indicating the relative ordering of subspace1
   and subspace.  */

static int
compare_subspaces (const void *arg1, const void *arg2)
{
  asection *subspace1 = *(asection **) arg1;
  asection *subspace2 = *(asection **) arg2;

  return subspace1->target_index - subspace2->target_index;
}

/* Perform various work in preparation for emitting the fixup stream.  */

static inline void
initialize_symbol_data_for_reloc_counting(asymbol *sym)
{
  if (som_symbol_data(sym) == NULL || (sym->flags & BSF_SECTION_SYM))
    {
      sym->flags |= BSF_SECTION_SYM;
      sym->udata.i = 0;
    }
  else
    {
      som_symbol_data(sym)->reloc_count = 0;
    }
}

static inline void
increment_symbol_reloc_count(asymbol *sym, int scale)
{
  if (sym->flags & BSF_SECTION_SYM)
    {
      sym->udata.i += scale;
    }
  else
    {
      som_symbol_data(sym)->reloc_count += scale;
    }
}

static inline void
set_symbol_index_after_sort(asymbol *sym, unsigned long index_val)
{
  if (sym->flags & BSF_SECTION_SYM)
    {
      sym->udata.i = (int)index_val;
    }
  else
    {
      som_symbol_data(sym)->index = index_val;
    }
}

static bool
som_prep_for_fixups (bfd *abfd, asymbol **syms, unsigned long num_syms)
{
  unsigned long i;
  asection *section;
  asymbol **sorted_syms;
  size_t sorted_syms_byte_size;

  if (num_syms == 0)
    {
      return true;
    }

  for (i = 0; i < num_syms; ++i)
    {
      initialize_symbol_data_for_reloc_counting(syms[i]);
    }

  for (section = abfd->sections; section != NULL; section = section->next)
    {
      if (section->reloc_count == 0)
        {
          continue;
        }

      for (unsigned int j = 1; j < section->reloc_count; ++j)
        {
          arelent *reloc = section->orelocation[j];
          asymbol *target_sym;
          int scale;

          if (reloc->sym_ptr_ptr == NULL)
            {
              continue;
            }

          target_sym = *reloc->sym_ptr_ptr;

          if (bfd_is_abs_section (target_sym->section))
            {
              continue;
            }

          if (reloc->howto->type == R_DP_RELATIVE || reloc->howto->type == R_CODE_ONE_SYMBOL)
            {
              scale = 2;
            }
          else
            {
              scale = 1;
            }

          increment_symbol_reloc_count(target_sym, scale);
        }
    }

  if (_bfd_mul_overflow (num_syms, sizeof (asymbol *), &sorted_syms_byte_size))
    {
      bfd_set_error (bfd_error_no_memory);
      return false;
    }

  sorted_syms = bfd_zalloc (abfd, sorted_syms_byte_size);
  if (sorted_syms == NULL)
    {
      bfd_set_error (bfd_error_no_memory);
      return false;
    }

  memcpy (sorted_syms, syms, sorted_syms_byte_size);
  qsort (sorted_syms, num_syms, sizeof (asymbol *), compare_syms);
  obj_som_sorted_syms (abfd) = sorted_syms;

  for (i = 0; i < num_syms; ++i)
    {
      set_symbol_index_after_sort(sorted_syms[i], i);
    }

  return true;
}

static bool
flush_som_relocs (bfd *abfd, unsigned char **p_ptr, unsigned char *tmp_space)
{
  size_t amt = *p_ptr - tmp_space;
  if (amt == 0)
    return true;

  if (bfd_write (tmp_space, amt, abfd) != amt)
    return false;

  *p_ptr = tmp_space;
  som_initialize_reloc_queue (reloc_queue);
  return true;
}

static int
get_symbol_number (arelent *bfd_reloc)
{
  if ((*bfd_reloc->sym_ptr_ptr)->flags & BSF_SECTION_SYM)
    return (*bfd_reloc->sym_ptr_ptr)->udata.i;
  return som_symbol_data (*bfd_reloc->sym_ptr_ptr)->index;
}

static bool
ensure_buffer_space (bfd *abfd, unsigned char **p_ptr, unsigned char *tmp_space)
{
  // BFD_WRITE_BUFFER_SIZE_THRESHOLD needs to be defined, e.g., 300 to accommodate largest single relocations.
  // Assuming SOM_TMP_BUFSIZE is also defined.
  if ((size_t)(*p_ptr - tmp_space) + 300 > SOM_TMP_BUFSIZE)
    {
      return flush_som_relocs (abfd, p_ptr, tmp_space);
    }
  return true;
}

static unsigned char *
handle_code_symbol_relocation (bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                               arelent *bfd_reloc, int sym_num)
{
  // SOM_SYM_INDEX_SHORT_THRES (0x20), SOM_SYM_INDEX_BYTE_THRES (0x100), SOM_SYM_INDEX_WORD_THRES (0x10000000)
  // are assumed to be defined constants or magic numbers here.
  const unsigned int som_sym_index_short_thres = 0x20;
  const unsigned int som_sym_index_byte_thres = 0x100;
  const unsigned int som_sym_index_word_thres = 0x10000000;

  if (bfd_reloc->addend)
    p = som_reloc_addend (abfd, bfd_reloc->addend, p, subspace_reloc_size, reloc_queue);

  if (sym_num < som_sym_index_short_thres)
    {
      bfd_put_8 (abfd, bfd_reloc->howto->type + sym_num, p);
      *subspace_reloc_size += 1;
      p += 1;
    }
  else if (sym_num < som_sym_index_byte_thres)
    {
      bfd_put_8 (abfd, bfd_reloc->howto->type + 32, p);
      bfd_put_8 (abfd, sym_num, p + 1);
      p = try_prev_fixup (abfd, subspace_reloc_size, p, 2, reloc_queue);
    }
  else if (sym_num < som_sym_index_word_thres)
    {
      bfd_put_8 (abfd, bfd_reloc->howto->type + 33, p);
      bfd_put_8 (abfd, sym_num >> 16, p + 1);
      bfd_put_16 (abfd, (bfd_vma) sym_num, p + 2);
      p = try_prev_fixup (abfd, subspace_reloc_size, p, 4, reloc_queue);
    }
  else
    {
      _bfd_error_handler (_("%pB: Symbol index 0x%x too large for R_CODE_ONE_SYMBOL"), abfd, sym_num);
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }
  return p;
}

static unsigned char *
handle_data_gprel_relocation (bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                              arelent *bfd_reloc, int sym_num)
{
  const unsigned int som_sym_index_word_thres = 0x10000000;

  if (bfd_reloc->addend)
    p = som_reloc_addend (abfd, bfd_reloc->addend, p, subspace_reloc_size, reloc_queue);

  if (sym_num < som_sym_index_word_thres)
    {
      bfd_put_8 (abfd, bfd_reloc->howto->type, p);
      bfd_put_8 (abfd, sym_num >> 16, p + 1);
      bfd_put_16 (abfd, (bfd_vma) sym_num, p + 2);
      p = try_prev_fixup (abfd, subspace_reloc_size, p, 4, reloc_queue);
    }
  else
    {
      _bfd_error_handler (_("%pB: Symbol index 0x%x too large for R_DATA_GPREL"), abfd, sym_num);
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }
  return p;
}

static unsigned char *
handle_data_plabel_relocation (bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                               arelent *bfd_reloc, int sym_num)
{
  const unsigned int som_sym_index_byte_thres = 0x100;
  const unsigned int som_sym_index_word_thres = 0x10000000;

  if (bfd_reloc->howto->type != R_DATA_ONE_SYMBOL && bfd_reloc->addend)
    p = som_reloc_addend (abfd, bfd_reloc->addend, p, subspace_reloc_size, reloc_queue);

  if (sym_num < som_sym_index_byte_thres)
    {
      bfd_put_8 (abfd, bfd_reloc->howto->type, p);
      bfd_put_8 (abfd, sym_num, p + 1);
      p = try_prev_fixup (abfd, subspace_reloc_size, p, 2, reloc_queue);
    }
  else if (sym_num < som_sym_index_word_thres)
    {
      bfd_put_8 (abfd, bfd_reloc->howto->type + 1, p);
      bfd_put_8 (abfd, sym_num >> 16, p + 1);
      bfd_put_16 (abfd, (bfd_vma) sym_num, p + 2);
      p = try_prev_fixup (abfd, subspace_reloc_size, p, 4, reloc_queue);
    }
  else
    {
      _bfd_error_handler (_("%pB: Symbol index 0x%x too large for data/plabel relocation"), abfd, sym_num);
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }
  return p;
}

static unsigned char *
handle_entry_relocation (bfd *abfd, asection *subsection, unsigned char *p, unsigned int *subspace_reloc_size,
                         arelent *bfd_reloc, unsigned int reloc_index)
{
  unsigned int tmp;
  arelent *tmp_reloc = NULL;

  bfd_put_8 (abfd, R_ENTRY, p);
  bfd_put_32 (abfd, bfd_reloc->addend, p + 1);

  for (tmp = reloc_index; tmp < subsection->reloc_count; tmp++)
    {
      tmp_reloc = subsection->orelocation[tmp];
      if (tmp_reloc->howto->type == R_EXIT)
        break;
    }

  if (tmp == subsection->reloc_count)
    {
      _bfd_error_handler (_("%pB(%pA+%#" PRIx64 "): R_ENTRY without matching R_EXIT"),
                          abfd, subsection, (uint64_t) bfd_reloc->address);
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }

  bfd_put_32 (abfd, tmp_reloc->addend, p + 5);
  p = try_prev_fixup (abfd, subspace_reloc_size, p, 9, reloc_queue);
  return p;
}

static unsigned char *
handle_rounding_mode_relocation (bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                                 arelent *bfd_reloc, unsigned int *current_rounding_mode)
{
  if (bfd_reloc->howto->type != *current_rounding_mode)
    {
      bfd_put_8 (abfd, bfd_reloc->howto->type, p);
      *subspace_reloc_size += 1;
      p += 1;
      *current_rounding_mode = bfd_reloc->howto->type;
    }
  return p;
}

#ifndef NO_PCREL_MODES
static unsigned char *
handle_pcrel_mode_relocation (bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                              arelent *bfd_reloc, unsigned int *current_call_mode)
{
  if (bfd_reloc->howto->type != *current_call_mode)
    {
      bfd_put_8 (abfd, bfd_reloc->howto->type, p);
      *subspace_reloc_size += 1;
      p += 1;
      *current_call_mode = bfd_reloc->howto->type;
    }
  return p;
}
#endif

static unsigned char *
handle_end_try_relocation (bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                           arelent *bfd_reloc)
{
  const unsigned int som_end_try_addend_short_thres = 1024;

  if (bfd_reloc->addend == 0)
    {
      bfd_put_8 (abfd, bfd_reloc->howto->type, p);
      *subspace_reloc_size += 1;
      p += 1;
    }
  else if (bfd_reloc->addend < som_end_try_addend_short_thres)
    {
      bfd_put_8 (abfd, bfd_reloc->howto->type + 1, p);
      bfd_put_8 (abfd, bfd_reloc->addend / 4, p + 1);
      p = try_prev_fixup (abfd, subspace_reloc_size, p, 2, reloc_queue);
    }
  else
    {
      bfd_put_8 (abfd, bfd_reloc->howto->type + 2, p);
      bfd_put_8 (abfd, (bfd_reloc->addend / 4) >> 16, p + 1);
      bfd_put_16 (abfd, bfd_reloc->addend / 4, p + 2);
      p = try_prev_fixup (abfd, subspace_reloc_size, p, 4, reloc_queue);
    }
  return p;
}

static unsigned char *
handle_comp1_relocation (bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                         arelent *bfd_reloc)
{
  const unsigned char som_comp1_operand = 0x44;

  bfd_put_8 (abfd, bfd_reloc->howto->type, p);
  bfd_put_8 (abfd, som_comp1_operand, p + 1);
  p = try_prev_fixup (abfd, subspace_reloc_size, p, 2, reloc_queue);
  return p;
}

static unsigned char *
handle_comp2_relocation (bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                         arelent *bfd_reloc, int sym_num)
{
  const unsigned char som_comp2_operand = 0x80;

  bfd_put_8 (abfd, bfd_reloc->howto->type, p);
  bfd_put_8 (abfd, som_comp2_operand, p + 1);
  bfd_put_8 (abfd, sym_num >> 16, p + 2);
  bfd_put_16 (abfd, (bfd_vma) sym_num, p + 3);
  p = try_prev_fixup (abfd, subspace_reloc_size, p, 5, reloc_queue);
  return p;
}

static unsigned char *
handle_expr_relocation (bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                        arelent *bfd_reloc)
{
  bfd_put_8 (abfd, bfd_reloc->howto->type, p);
  *subspace_reloc_size += 1;
  p += 1;
  return p;
}

static unsigned char *
handle_simple_relocation (bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                          arelent *bfd_reloc)
{
  bfd_put_8 (abfd, bfd_reloc->howto->type, p);
  *subspace_reloc_size += 1;
  p += 1;
  return p;
}

static unsigned char *
handle_unknown_relocation (bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                           arelent *bfd_reloc)
{
  _bfd_error_handler (_("%pB(%pA+%#" PRIx64 "): Unknown relocation type 0x%x encountered"),
                      abfd, bfd_reloc->section, (uint64_t) bfd_reloc->address,
                      bfd_reloc->howto->type);
  bfd_put_8 (abfd, 0xff, p); // Place R_RESERVED as per original comment.
  *subspace_reloc_size += 1;
  p += 1;
  return p;
}

static bool
som_write_fixups (bfd *abfd,
                  unsigned long current_offset,
                  unsigned int *total_reloc_sizep)
{
  unsigned char tmp_space[SOM_TMP_BUFSIZE];
  unsigned char *p;
  unsigned int total_reloc_size = 0;

  memset (tmp_space, 0, SOM_TMP_BUFSIZE);
  p = tmp_space;

  asection *current_space_section = abfd->sections;
  while (current_space_section != NULL)
    {
      if (!som_is_space (current_space_section))
        {
          current_space_section = current_space_section->next;
          continue;
        }

      asection *current_subspace_section = abfd->sections;
      while (current_subspace_section != NULL)
        {
          if (!som_is_subspace (current_subspace_section)
              || !som_is_container (current_space_section, current_subspace_section))
            {
              current_subspace_section = current_subspace_section->next;
              continue;
            }

          if ((current_subspace_section->flags & SEC_HAS_CONTENTS) == 0)
            {
              som_section_data (current_subspace_section)->subspace_dict->fixup_request_index = -1;
              current_subspace_section = current_subspace_section->next;
              continue;
            }

          som_section_data (current_subspace_section)->subspace_dict->fixup_request_index
            = total_reloc_size;

          if (bfd_seek (abfd, current_offset + total_reloc_size, SEEK_SET) != 0)
            return false;

          unsigned int subspace_reloc_size = 0;
          unsigned int reloc_offset = 0;
          unsigned int current_rounding_mode = R_N_MODE;
#ifndef NO_PCREL_MODES
          unsigned int current_call_mode = R_SHORT_PCREL_MODE;
#endif

          som_initialize_reloc_queue (reloc_queue);
          p = tmp_space;

          for (unsigned int j = 0; j < current_subspace_section->reloc_count; j++)
            {
              arelent *bfd_reloc = current_subspace_section->orelocation[j];
              unsigned char *p_next = NULL;
              unsigned int skip_bytes;
              int sym_num;

              if (bfd_reloc->address < reloc_offset)
                {
                  _bfd_error_handler
                    (_("%pB(%pA+%#" PRIx64 "): %s relocation offset out of order"),
                     abfd, current_subspace_section, (uint64_t) bfd_reloc->address,
                     bfd_reloc->howto->name);
                  bfd_set_error (bfd_error_bad_value);
                  return false;
                }
              if (!bfd_reloc_offset_in_range (bfd_reloc->howto,
                                              abfd, current_subspace_section,
                                              bfd_reloc->address))
                {
                  _bfd_error_handler
                    (_("%pB(%pA+%#" PRIx64 "): %s relocation offset out of range"),
                     abfd, current_subspace_section, (uint64_t) bfd_reloc->address,
                     bfd_reloc->howto->name);
                  bfd_set_error (bfd_error_bad_value);
                  return false;
                }

              sym_num = get_symbol_number (bfd_reloc);

              if (!ensure_buffer_space (abfd, &p, tmp_space))
                return false;

              skip_bytes = bfd_reloc->address - reloc_offset;
              p = som_reloc_skip (abfd, skip_bytes, p, &subspace_reloc_size, reloc_queue);

              reloc_offset = bfd_reloc->address + bfd_reloc->howto->size;

              switch (bfd_reloc->howto->type)
                {
                case R_PCREL_CALL:
                case R_ABS_CALL:
                  p_next = som_reloc_call (abfd, p, &subspace_reloc_size, bfd_reloc, sym_num, reloc_queue);
                  break;

                case R_CODE_ONE_SYMBOL:
                case R_DP_RELATIVE:
                  p_next = handle_code_symbol_relocation (abfd, p, &subspace_reloc_size, bfd_reloc, sym_num);
                  break;

                case R_DATA_GPREL:
                  p_next = handle_data_gprel_relocation (abfd, p, &subspace_reloc_size, bfd_reloc, sym_num);
                  break;

                case R_DATA_ONE_SYMBOL:
                case R_DATA_PLABEL:
                case R_CODE_PLABEL:
                case R_DLT_REL:
                  p_next = handle_data_plabel_relocation (abfd, p, &subspace_reloc_size, bfd_reloc, sym_num);
                  break;

                case R_ENTRY:
                  p_next = handle_entry_relocation (abfd, current_subspace_section, p, &subspace_reloc_size, bfd_reloc, j);
                  break;

                case R_N_MODE:
                case R_S_MODE:
                case R_D_MODE:
                case R_R_MODE:
                  p_next = handle_rounding_mode_relocation (abfd, p, &subspace_reloc_size, bfd_reloc, &current_rounding_mode);
                  break;

#ifndef NO_PCREL_MODES
                case R_LONG_PCREL_MODE:
                case R_SHORT_PCREL_MODE:
                  p_next = handle_pcrel_mode_relocation (abfd, p, &subspace_reloc_size, bfd_reloc, &current_call_mode);
                  break;
#endif

                case R_EXIT:
                case R_ALT_ENTRY:
                case R_FSEL:
                case R_LSEL:
                case R_RSEL:
                case R_BEGIN_BRTAB:
                case R_END_BRTAB:
                case R_BEGIN_TRY:
                case R_N0SEL:
                case R_N1SEL:
                  p_next = handle_simple_relocation (abfd, p, &subspace_reloc_size, bfd_reloc);
                  break;

                case R_END_TRY:
                  p_next = handle_end_try_relocation (abfd, p, &subspace_reloc_size, bfd_reloc);
                  break;

                case R_COMP1:
                  p_next = handle_comp1_relocation (abfd, p, &subspace_reloc_size, bfd_reloc);
                  break;

                case R_COMP2:
                  p_next = handle_comp2_relocation (abfd, p, &subspace_reloc_size, bfd_reloc, sym_num);
                  break;

                case R_CODE_EXPR:
                case R_DATA_EXPR:
                  p_next = handle_expr_relocation (abfd, p, &subspace_reloc_size, bfd_reloc);
                  break;

                default:
                  p_next = handle_unknown_relocation (abfd, p, &subspace_reloc_size, bfd_reloc);
                  break;
                }

              if (p_next == NULL)
                return false;
              p = p_next;
            }

          p = som_reloc_skip (abfd, current_subspace_section->size - reloc_offset,
                              p, &subspace_reloc_size, reloc_queue);

          if (!flush_som_relocs (abfd, &p, tmp_space))
            return false;

          total_reloc_size += subspace_reloc_size;
          som_section_data (current_subspace_section)->subspace_dict->fixup_request_quantity
            = subspace_reloc_size;

          current_subspace_section = current_subspace_section->next;
        }
      current_space_section = current_space_section->next;
    }

  *total_reloc_sizep = total_reloc_size;
  return true;
}

/* Write the length of STR followed by STR to P which points into
   *BUF, a buffer of *BUFLEN size.  Track total size in *STRINGS_SIZE,
   setting *STRX to the current offset for STR.  When STR can't fit in
   *BUF, flush the buffer to ABFD, possibly reallocating.  Return the
   next available location in *BUF, or NULL on error.  */

#define BFD_ALIGN_BYTES 4U
#define BFD_UINT32_SIZE BFD_ALIGN_BYTES

static char *
ensure_buffer_space (char *current_ptr, bfd *abfd, char **buffer, size_t *buffer_len, size_t needed_space)
{
  size_t current_used_bytes = (size_t)(current_ptr - *buffer);

  if (current_used_bytes + needed_space > *buffer_len)
    {
      if (current_used_bytes > 0)
        {
          if ((size_t) bfd_write (*buffer, current_used_bytes, abfd) != current_used_bytes)
            return NULL;
        }

      if (needed_space > *buffer_len)
        {
          size_t new_buffer_len = *buffer_len * 2;
          if (new_buffer_len < needed_space)
            new_buffer_len = needed_space;
          
          void *new_buffer = bfd_malloc (new_buffer_len);
          if (new_buffer == NULL)
            return NULL;

          bfd_free (*buffer); 
          *buffer = new_buffer;
          *buffer_len = new_buffer_len;
        }
      
      current_ptr = *buffer;
    }
  return current_ptr;
}

static char *
add_string (char *p, const char *str, bfd *abfd, char **buf, size_t *buflen,
	    unsigned int *strings_size, unsigned int *strx)
{
  size_t str_len = strlen (str);
  size_t entry_data_len = str_len + 1;

  size_t pad_len = 0;
  if (entry_data_len % BFD_ALIGN_BYTES != 0)
    pad_len = BFD_ALIGN_BYTES - (entry_data_len % BFD_ALIGN_BYTES);

  size_t total_entry_size = BFD_UINT32_SIZE + entry_data_len + pad_len;

  p = ensure_buffer_space(p, abfd, buf, buflen, total_entry_size);
  if (p == NULL)
    return NULL;

  *strx = *strings_size + BFD_UINT32_SIZE;

  bfd_put_32 (abfd, (unsigned int)str_len, p);
  *strings_size += BFD_UINT32_SIZE;
  p += BFD_UINT32_SIZE;

  memcpy (p, str, entry_data_len);
  p += entry_data_len;
  *strings_size += entry_data_len;

  if (pad_len > 0)
    {
      memset (p, 0, pad_len);
      *strings_size += pad_len;
      p += pad_len;
    }

  return p;
}

/* Write out the space/subspace string table.  */

static bool
som_write_space_strings (bfd *abfd,
			 unsigned long current_offset,
			 unsigned int *strings_size)
{
  size_t tmp_space_size = SOM_TMP_BUFSIZE;
  char *tmp_space = bfd_malloc (tmp_space_size);
  char *p = tmp_space;
  asection *section;

  if (tmp_space == NULL)
    {
      return false;
    }

  if (bfd_seek (abfd, current_offset, SEEK_SET) != 0)
    {
      free (tmp_space);
      return false;
    }

  *strings_size = 0;
  for (section = abfd->sections; section != NULL; section = section->next)
    {
      unsigned int *strx;

      if (som_is_space (section))
	{
	  strx = &som_section_data (section)->space_dict->name;
	}
      else if (som_is_subspace (section))
	{
	  strx = &som_section_data (section)->subspace_dict->name;
	}
      else
	{
	  continue;
	}

      p = add_string (p, section->name, abfd, &tmp_space, &tmp_space_size,
		      strings_size, strx);
      if (p == NULL)
	{
	  free (tmp_space);
	  return false;
	}
    }

  size_t bytes_to_write = p - tmp_space;

  if (bytes_to_write > 0)
    {
      if (bfd_write (tmp_space, bytes_to_write, abfd) != bytes_to_write)
        {
          free (tmp_space);
          return false;
        }
    }

  free (tmp_space);
  return true;
}

/* Write out the symbol string table.  */

static bool
som_write_symbol_strings (bfd *abfd,
                          unsigned long current_offset,
                          asymbol **syms,
                          unsigned int num_syms,
                          unsigned int *strings_size,
                          struct som_compilation_unit *compilation_unit)
{
  char *tmp_space = bfd_malloc (SOM_TMP_BUFSIZE);
  if (tmp_space == NULL)
    return false;

  size_t tmp_space_size = SOM_TMP_BUFSIZE;
  char *p = tmp_space;

  if (bfd_seek (abfd, current_offset, SEEK_SET) != 0)
    {
      free (tmp_space);
      return false;
    }

  *strings_size = 0;

  if (compilation_unit != NULL)
    {
      struct som_name_pt *comp_unit_names[] = {
        &compilation_unit->name,
        &compilation_unit->language_name,
        &compilation_unit->product_id,
        &compilation_unit->version_id
      };
      const unsigned int NUM_COMP_UNIT_NAMES =
        sizeof (comp_unit_names) / sizeof (comp_unit_names[0]);

      for (unsigned int i = 0; i < NUM_COMP_UNIT_NAMES; i++)
        {
          p = add_string (p, comp_unit_names[i]->name, abfd,
                          &tmp_space, &tmp_space_size,
                          strings_size, &comp_unit_names[i]->strx);
          if (p == NULL)
            {
              free (tmp_space);
              return false;
            }
        }
    }

  for (unsigned int i = 0; i < num_syms; i++)
    {
      p = add_string (p, syms[i]->name, abfd,
                      &tmp_space, &tmp_space_size,
                      strings_size,
                      &som_symbol_data (syms[i])->stringtab_offset);
      if (p == NULL)
        {
          free (tmp_space);
          return false;
        }
    }

  size_t amt = p - tmp_space;
  if (amt > 0)
    {
      if (bfd_write (tmp_space, amt, abfd) != amt)
        {
          free (tmp_space);
          return false;
        }
    }

  free (tmp_space);
  return true;
}

/* Compute variable information to be placed in the SOM headers,
   space/subspace dictionaries, relocation streams, etc.  Begin
   writing parts of the object file.  */

static bool
seek_to_offset (bfd *abfd, unsigned long offset)
{
  if (bfd_seek (abfd, offset, SEEK_SET) != 0)
    return false;
  return true;
}

static bool
write_data (bfd *abfd, const void *data, bfd_size_type len)
{
  if (bfd_write (data, len, abfd) != len)
    return false;
  return true;
}

static bool
write_som_string_aux_header (bfd *abfd, struct som_string_auxhdr *som_hdr,
                             unsigned long *current_offset_ptr)
{
  if (som_hdr == NULL)
    return true;

  struct som_external_string_auxhdr ext_string_auxhdr;
  bfd_size_type hdr_len = sizeof (struct som_external_string_auxhdr);
  bfd_size_type string_len = som_hdr->header_id.length - 4;

  if (!seek_to_offset (abfd, *current_offset_ptr))
    return false;

  obj_som_file_hdr (abfd)->aux_header_size += hdr_len;
  *current_offset_ptr += hdr_len;
  som_swap_string_auxhdr_out (som_hdr, &ext_string_auxhdr);
  if (!write_data (abfd, &ext_string_auxhdr, hdr_len))
    return false;

  obj_som_file_hdr (abfd)->aux_header_size += string_len;
  *current_offset_ptr += string_len;
  if (!write_data (abfd, som_hdr->string, string_len))
    return false;

  return true;
}

static bool
setup_initial_headers (bfd *abfd, unsigned long *current_offset_ptr,
                       struct som_exec_auxhdr **exec_header_ptr)
{
  *current_offset_ptr += sizeof (struct som_external_header);

  obj_som_file_hdr (abfd)->aux_header_location = *current_offset_ptr;
  obj_som_file_hdr (abfd)->aux_header_size = 0;

  if (abfd->flags & (EXEC_P | DYNAMIC))
    {
      *current_offset_ptr += sizeof (struct som_external_exec_auxhdr);
      obj_som_file_hdr (abfd)->aux_header_size
        += sizeof (struct som_external_exec_auxhdr);
      *exec_header_ptr = obj_som_exec_hdr (abfd);
      (*exec_header_ptr)->som_auxhdr.type = EXEC_AUX_ID;
      (*exec_header_ptr)->som_auxhdr.length = 40;
    }

  if (!write_som_string_aux_header (abfd, obj_som_version_hdr (abfd), current_offset_ptr))
    return false;
  if (!write_som_string_aux_header (abfd, obj_som_copyright_hdr (abfd), current_offset_ptr))
    return false;

  obj_som_file_hdr (abfd)->init_array_location = *current_offset_ptr;
  obj_som_file_hdr (abfd)->init_array_total = 0;

  return true;
}

static bool
setup_space_and_subspace_dictionaries (bfd *abfd, unsigned long *current_offset_ptr)
{
  unsigned long num_spaces = som_count_spaces (abfd);
  obj_som_file_hdr (abfd)->space_location = *current_offset_ptr;
  obj_som_file_hdr (abfd)->space_total = num_spaces;
  *current_offset_ptr += num_spaces * sizeof (struct som_external_space_dictionary_record);

  unsigned long num_subspaces = som_count_subspaces (abfd);
  obj_som_file_hdr (abfd)->subspace_location = *current_offset_ptr;
  obj_som_file_hdr (abfd)->subspace_total = num_subspaces;
  *current_offset_ptr += num_subspaces * sizeof (struct som_external_subspace_dictionary_record);

  if (*current_offset_ptr % 4)
    *current_offset_ptr += (4 - (*current_offset_ptr % 4));

  obj_som_file_hdr (abfd)->space_strings_location = *current_offset_ptr;

  unsigned int strings_size = 0;
  if (!som_write_space_strings (abfd, *current_offset_ptr, &strings_size))
    return false;

  obj_som_file_hdr (abfd)->space_strings_size = strings_size;
  *current_offset_ptr += strings_size;

  return true;
}

static bool
setup_compilation_unit (bfd *abfd, unsigned long *current_offset_ptr)
{
  obj_som_file_hdr (abfd)->compiler_location = *current_offset_ptr;
  obj_som_file_hdr (abfd)->compiler_total = 0;
  if (obj_som_compilation_unit (abfd))
    {
      obj_som_file_hdr (abfd)->compiler_total = 1;
      *current_offset_ptr += sizeof (struct som_external_compilation_unit);
    }
  return true;
}

static bool
process_loadable_subspaces (bfd *abfd, unsigned long *current_offset_ptr,
                            struct som_exec_auxhdr *exec_header,
                            unsigned int *total_subspaces_ptr)
{
  unsigned long num_spaces = som_count_spaces (abfd);
  asection *section = abfd->sections;

  for (unsigned long i = 0; i < num_spaces; i++)
    {
      while (section && !som_is_space (section))
        section = section->next;

      if (!section)
        return false;

      bool first_subspace_in_space = true;
      unsigned long subspace_offset_within_space = 0;

      for (asection *subsection = abfd->sections;
           subsection != NULL;
           subsection = subsection->next)
        {
          if (!som_is_subspace (subsection)
              || !som_is_container (section, subsection)
              || !(subsection->flags & SEC_ALLOC))
            continue;

          if (first_subspace_in_space && (abfd->flags & (EXEC_P | DYNAMIC)))
            {
              if ((abfd->flags & (D_PAGED | DYNAMIC))
                  || (subsection->flags & SEC_CODE)
                  || ((abfd->flags & WP_TEXT)
                      && (subsection->flags & SEC_DATA)))
                *current_offset_ptr = SOM_ALIGN (*current_offset_ptr, PA_PAGESIZE);

              if (subsection->flags & SEC_CODE && exec_header->exec_tfile == 0)
                {
                  exec_header->exec_tmem = section->vma;
                  exec_header->exec_tfile = *current_offset_ptr;
                }
              if (subsection->flags & SEC_DATA && exec_header->exec_dfile == 0)
                {
                  exec_header->exec_dmem = section->vma;
                  exec_header->exec_dfile = *current_offset_ptr;
                }

              subspace_offset_within_space = subsection->vma;
              first_subspace_in_space = false;
            }
          else if (abfd->flags & (EXEC_P | DYNAMIC))
            {
              if (subsection->vma > subspace_offset_within_space)
                {
                  unsigned long hole_size = subsection->vma - subspace_offset_within_space;
                  *current_offset_ptr += hole_size;
                  if (subsection->flags & SEC_CODE)
                    exec_header->exec_tsize += hole_size;
                  else
                    exec_header->exec_dsize += hole_size;
                  subspace_offset_within_space += hole_size;
                }
            }

          subsection->target_index = (*total_subspaces_ptr)++;

          if (subsection->flags & SEC_LOAD)
            {
              if ((abfd->flags & (EXEC_P | DYNAMIC)))
                {
                  if (subsection->flags & SEC_CODE)
                    exec_header->exec_tsize += subsection->size;
                  else if (subsection->flags & SEC_DATA)
                    exec_header->exec_dsize += subsection->size;
                }
              som_section_data (subsection)->subspace_dict->file_loc_init_value
                = *current_offset_ptr;
              subsection->filepos = *current_offset_ptr;
              *current_offset_ptr += subsection->size;
              subspace_offset_within_space += subsection->size;
            }
          else
            {
              if (abfd->flags & (EXEC_P | DYNAMIC))
                exec_header->exec_bsize += subsection->size;

              som_section_data (subsection)->subspace_dict->file_loc_init_value
                = 0;
              som_section_data (subsection)->subspace_dict->initialization_length
                = 0;
            }
        }
      section = section->next;
    }
  return true;
}

static bool
process_unloadable_subspaces (bfd *abfd, unsigned long *current_offset_ptr,
                              unsigned int *total_subspaces_ptr)
{
  if (abfd->flags & (EXEC_P | DYNAMIC))
    *current_offset_ptr = SOM_ALIGN (*current_offset_ptr, PA_PAGESIZE);

  obj_som_file_hdr (abfd)->unloadable_sp_location = *current_offset_ptr;
  unsigned long num_spaces = som_count_spaces (abfd);
  asection *section = abfd->sections;

  for (unsigned long i = 0; i < num_spaces; i++)
    {
      while (section && !som_is_space (section))
        section = section->next;

      if (!section)
        return false;

      if (abfd->flags & (EXEC_P | DYNAMIC))
        *current_offset_ptr = SOM_ALIGN (*current_offset_ptr, PA_PAGESIZE);

      for (asection *subsection = abfd->sections;
           subsection != NULL;
           subsection = subsection->next)
        {
          if (!som_is_subspace (subsection)
              || !som_is_container (section, subsection)
              || (subsection->flags & SEC_ALLOC) != 0)
            continue;

          subsection->target_index = (*total_subspaces_ptr)++;

          if ((subsection->flags & SEC_LOAD) == 0)
            {
              som_section_data (subsection)->subspace_dict->file_loc_init_value
                = *current_offset_ptr;
              subsection->filepos = *current_offset_ptr;
              *current_offset_ptr += subsection->size;
            }
          else
            {
              som_section_data (subsection)->subspace_dict->file_loc_init_value
                = 0;
              som_section_data (subsection)->subspace_dict->initialization_length
                = subsection->size;
            }
        }
      section = section->next;
    }
  return true;
}

static bool
finalize_som_file (bfd *abfd, unsigned long current_offset)
{
  if (abfd->flags & (EXEC_P | DYNAMIC))
    current_offset = SOM_ALIGN (current_offset, PA_PAGESIZE);

  if (!seek_to_offset (abfd, current_offset - 1))
    return false;
  if (!write_data (abfd, "", 1))
    return false;

  obj_som_file_hdr (abfd)->unloadable_sp_size
    = current_offset - obj_som_file_hdr (abfd)->unloadable_sp_location;

  obj_som_file_hdr (abfd)->loader_fixup_location = 0;
  obj_som_file_hdr (abfd)->loader_fixup_total = 0;

  obj_som_file_hdr (abfd)->som_length = current_offset;

  return true;
}

static bool
som_begin_writing (bfd *abfd)
{
  unsigned long current_offset = 0;
  struct som_exec_auxhdr *exec_header = NULL;
  unsigned int total_subspaces = 0;

  if (!setup_initial_headers (abfd, &current_offset, &exec_header))
    return false;

  if (!setup_space_and_subspace_dictionaries (abfd, &current_offset))
    return false;

  if (!setup_compilation_unit (abfd, &current_offset))
    return false;

  if (!process_loadable_subspaces (abfd, &current_offset, exec_header,
                                   &total_subspaces))
    return false;

  if (!process_unloadable_subspaces (abfd, &current_offset,
                                     &total_subspaces))
    return false;

  if (!finalize_som_file (abfd, current_offset))
    return false;

  return true;
}

/* Finally, scribble out the various headers to the disk.  */

static bool som_bfd_seek(bfd *abfd, file_ptr location, enum bfd_seek_howto whence) {
  if (bfd_seek(abfd, location, whence) != 0) {
    return false;
  }
  return true;
}

static bool som_bfd_write(bfd *abfd, const void *buf, size_t size) {
  if (bfd_write(buf, size, abfd) != size) {
    return false;
  }
  return true;
}

static unsigned long som_align_offset(unsigned long offset, unsigned int alignment) {
  if (alignment == 0) return offset;
  if (offset % alignment) {
    offset += (alignment - (offset % alignment));
  }
  return offset;
}

static bool som_set_file_version_id(struct som_file_header *file_hdr, struct som_exec_data *exec_data) {
  if (exec_data && exec_data->version_id) {
    file_hdr->version_id = exec_data->version_id;
  } else {
    file_hdr->version_id = NEW_VERSION_ID;
  }
  return true;
}

static bool som_write_symbol_data_and_update_offset(bfd *abfd, struct som_file_header *file_hdr, unsigned long *current_offset_ptr) {
  unsigned long current_offset = *current_offset_ptr;
  asymbol **syms = bfd_get_outsymbols(abfd);
  int num_syms = bfd_get_symcount(abfd);
  unsigned int strings_size;

  current_offset = som_align_offset(current_offset, 4);
  file_hdr->symbol_location = current_offset;
  file_hdr->symbol_total = num_syms;
  current_offset += num_syms * sizeof(struct som_external_symbol_dictionary_record);

  current_offset = som_align_offset(current_offset, 4);
  file_hdr->symbol_strings_location = current_offset;

  if (!som_write_symbol_strings(abfd, current_offset, syms, num_syms, &strings_size, obj_som_compilation_unit(abfd))) {
    return false;
  }

  file_hdr->symbol_strings_size = strings_size;
  current_offset += strings_size;

  *current_offset_ptr = current_offset;
  return true;
}

static bool som_write_fixup_stream_and_update_offset(bfd *abfd, struct som_file_header *file_hdr, unsigned long *current_offset_ptr) {
  unsigned long current_offset = *current_offset_ptr;
  unsigned int total_reloc_size;

  if (!som_prep_for_fixups(abfd, bfd_get_outsymbols(abfd), bfd_get_symcount(abfd))) {
    return false;
  }

  current_offset = som_align_offset(current_offset, 4);
  file_hdr->fixup_request_location = current_offset;

  if (!som_write_fixups(abfd, current_offset, &total_reloc_size)) {
    return false;
  }

  file_hdr->fixup_request_total = total_reloc_size;
  current_offset += total_reloc_size;

  *current_offset_ptr = current_offset;
  return true;
}

static bool som_write_subspace_dictionary_records(bfd *abfd, struct som_file_header *file_hdr, int num_spaces, int *subspace_index_ptr, bool for_loadable) {
  if (!som_bfd_seek(abfd, file_hdr->subspace_location, SEEK_SET)) {
    return false;
  }

  asection *current_section_ptr = abfd->sections;
  for (int i = 0; i < num_spaces; i++) {
    asection *subsection;

    while (current_section_ptr && !som_is_space(current_section_ptr)) {
      current_section_ptr = current_section_ptr->next;
    }
    if (!current_section_ptr) {
      bfd_set_error(bfd_error_internal_error);
      return false;
    }

    for (subsection = abfd->sections; subsection != NULL; subsection = subsection->next) {
      struct som_external_subspace_dictionary_record ext_subspace_dict;

      bool skip_due_to_flags = (for_loadable && !(subsection->flags & SEC_ALLOC)) ||
                               (!for_loadable && (subsection->flags & SEC_ALLOC));

      if (!som_is_subspace(subsection) ||
          !som_is_container(current_section_ptr, subsection) ||
          skip_due_to_flags) {
        continue;
      }

      struct som_section_data *section_data = som_section_data(current_section_ptr);
      if (section_data->space_dict->subspace_quantity == 0) {
        section_data->space_dict->is_loadable = for_loadable ? 1 : 0;
        section_data->space_dict->subspace_index = *subspace_index_ptr;
      }

      (*subspace_index_ptr)++;
      section_data->space_dict->subspace_quantity++;
      som_section_data(subsection)->subspace_dict->space_index = i;

      som_swap_subspace_dictionary_record_out(som_section_data(subsection)->subspace_dict, &ext_subspace_dict);
      if (!som_bfd_write(abfd, &ext_subspace_dict, sizeof(struct som_subspace_dictionary_record))) {
        return false;
      }
    }
    current_section_ptr = current_section_ptr->next;
  }
  return true;
}

static bool som_write_space_dictionary_records(bfd *abfd, struct som_file_header *file_hdr, int num_spaces) {
  if (!som_bfd_seek(abfd, file_hdr->space_location, SEEK_SET)) {
    return false;
  }

  asection *current_section_ptr = abfd->sections;
  for (int i = 0; i < num_spaces; i++) {
    struct som_external_space_dictionary_record ext_space_dict;

    while (current_section_ptr && !som_is_space(current_section_ptr)) {
      current_section_ptr = current_section_ptr->next;
    }
    if (!current_section_ptr) {
      bfd_set_error(bfd_error_internal_error);
      return false;
    }

    som_swap_space_dictionary_out(som_section_data(current_section_ptr)->space_dict, &ext_space_dict);
    if (!som_bfd_write(abfd, &ext_space_dict, sizeof(struct som_external_space_dictionary_record))) {
      return false;
    }
    current_section_ptr = current_section_ptr->next;
  }
  return true;
}

static bool som_write_compilation_unit_record(bfd *abfd, struct som_file_header *file_hdr, struct som_compilation_unit *comp_unit) {
  if (comp_unit) {
    struct som_external_compilation_unit ext_comp_unit;

    if (!som_bfd_seek(abfd, file_hdr->compiler_location, SEEK_SET)) {
      return false;
    }

    som_swap_compilation_unit_out(comp_unit, &ext_comp_unit);
    if (!som_bfd_write(abfd, &ext_comp_unit, sizeof(struct som_external_compilation_unit))) {
      return false;
    }
  }
  return true;
}

static bool som_set_system_id(bfd *abfd, struct som_file_header *file_hdr, struct som_exec_data *exec_data) {
  if ((abfd->flags & (EXEC_P | DYNAMIC)) && exec_data) {
    file_hdr->system_id = exec_data->system_id;
  } else {
    switch (bfd_get_mach(abfd)) {
      case pa20:
        file_hdr->system_id = CPU_PA_RISC2_0;
        break;
      case pa11:
        file_hdr->system_id = CPU_PA_RISC1_1;
        break;
      default:
        file_hdr->system_id = CPU_PA_RISC1_0;
        break;
    }
  }
  return true;
}

static bool som_write_main_file_header(bfd *abfd, struct som_file_header *file_hdr) {
  struct som_external_header ext_header;
  som_swap_header_out(file_hdr, &ext_header);
  bfd_putb32(som_compute_checksum(&ext_header), (bfd_byte *)ext_header.checksum);

  if (!som_bfd_seek(abfd, 0, SEEK_SET)) {
    return false;
  }
  if (!som_bfd_write(abfd, &ext_header, sizeof(struct som_external_header))) {
    return false;
  }
  return true;
}

static bool som_write_exec_header(bfd *abfd, struct som_file_header *file_hdr, struct som_exec_data *exec_data) {
  if (abfd->flags & (EXEC_P | DYNAMIC)) {
    long tmp;
    struct som_exec_auxhdr *exec_header = obj_som_exec_hdr(abfd);
    struct som_external_exec_auxhdr ext_exec_header;

    exec_header->exec_entry = bfd_get_start_address(abfd);
    if (exec_data) {
      exec_header->exec_flags = exec_data->exec_flags;
    }

    tmp = exec_header->exec_dsize;
    tmp = SOM_ALIGN(tmp, PA_PAGESIZE);
    exec_header->exec_bsize -= (tmp - exec_header->exec_dsize);
    if (exec_header->exec_bsize < 0) {
      exec_header->exec_bsize = 0;
    }
    exec_header->exec_dsize = tmp;

    if (exec_header->exec_tfile + exec_header->exec_tsize > file_hdr->som_length ||
        exec_header->exec_dfile + exec_header->exec_dsize > file_hdr->som_length) {
      bfd_set_error(bfd_error_bad_value);
      return false;
    }

    som_swap_exec_auxhdr_out(exec_header, &ext_exec_header);

    if (!som_bfd_seek(abfd, file_hdr->aux_header_location, SEEK_SET)) {
      return false;
    }
    if (!som_bfd_write(abfd, &ext_exec_header, sizeof(ext_exec_header))) {
      return false;
    }
  }
  return true;
}

static bool
som_finish_writing (bfd *abfd)
{
  struct som_file_header *file_hdr = obj_som_file_hdr(abfd);
  struct som_exec_data *exec_data = obj_som_exec_data(abfd);
  struct som_compilation_unit *comp_unit = obj_som_compilation_unit(abfd);

  if (!som_set_file_version_id(file_hdr, exec_data)) return false;

  unsigned long current_offset = file_hdr->som_length;
  if (!som_write_symbol_data_and_update_offset(abfd, file_hdr, &current_offset)) return false;

  if (!som_write_fixup_stream_and_update_offset(abfd, file_hdr, &current_offset)) return false;

  file_hdr->som_length = current_offset;

  if (!som_build_and_write_symbol_table (abfd)) return false;

  int num_spaces = som_count_spaces(abfd);
  int subspace_index = 0;

  if (!som_write_subspace_dictionary_records(abfd, file_hdr, num_spaces, &subspace_index, true)) return false;
  if (!som_write_subspace_dictionary_records(abfd, file_hdr, num_spaces, &subspace_index, false)) return false;

  if (!som_write_space_dictionary_records(abfd, file_hdr, num_spaces)) return false;

  if (!som_write_compilation_unit_record(abfd, file_hdr, comp_unit)) return false;

  if (!som_set_system_id(abfd, file_hdr, exec_data)) return false;

  if (!som_write_main_file_header(abfd, file_hdr)) return false;

  if (!som_write_exec_header(abfd, file_hdr, exec_data)) return false;

  return true;
}

/* Compute and return the checksum for a SOM file header.  */

static uint32_t
som_compute_checksum (const struct som_external_header *hdr)
{
  uint32_t checksum = 0;
  const uint8_t *byte_ptr = (const uint8_t *) hdr;
  size_t total_bytes = sizeof(*hdr);
  size_t i;

  size_t num_words = total_bytes / sizeof(uint32_t);

  for (i = 0; i < num_words; ++i) {
    uint32_t word;
    memcpy(&word, byte_ptr + (i * sizeof(uint32_t)), sizeof(uint32_t));
    checksum ^= word;
  }

  return checksum;
}

static void
som_bfd_derive_misc_symbol_info (bfd *abfd ATTRIBUTE_UNUSED,
				 asymbol *sym,
				 struct som_misc_symbol_info *info)
{
  memset (info, 0, sizeof (struct som_misc_symbol_info));

  struct som_backend_data *sym_data = som_symbol_data(sym);
  bfd_section *section = sym->section;

  bool is_section_sym = (sym->flags & BSF_SECTION_SYM) != 0;
  bool is_function_sym = (sym->flags & BSF_FUNCTION) != 0;
  bool is_common_section = bfd_is_com_section(section);
  bool is_undefined_section = bfd_is_und_section(section);
  bool is_absolute_section = bfd_is_abs_section(section);
  enum som_symbol_type som_type = SYMBOL_TYPE_UNKNOWN;
  if (sym_data) {
    som_type = sym_data->som_type;
  }

  if (is_section_sym)
    {
      info->symbol_type = ST_DATA;
    }
  else if (is_common_section)
    {
      info->symbol_type = ST_STORAGE;
      info->symbol_scope = SS_UNSAT;
    }
  else if (is_undefined_section && is_function_sym
           && (som_type == SYMBOL_TYPE_UNKNOWN || som_type == SYMBOL_TYPE_CODE))
    {
      info->symbol_type = ST_CODE;
    }
  else if (som_type == SYMBOL_TYPE_ENTRY
           || (is_function_sym && (som_type == SYMBOL_TYPE_CODE || som_type == SYMBOL_TYPE_UNKNOWN)))
    {
      info->symbol_type = ST_ENTRY;
      if (sym_data) {
        info->arg_reloc = sym_data->tc_data.ap.hppa_arg_reloc;
        info->priv_level = sym_data->tc_data.ap.hppa_priv_level;
      }
    }
  else if (som_type == SYMBOL_TYPE_UNKNOWN)
    {
      if (is_absolute_section)
        info->symbol_type = ST_ABSOLUTE;
      else if (section->flags & SEC_CODE)
        info->symbol_type = ST_CODE;
      else
        info->symbol_type = ST_DATA;
    }
  else
    {
      switch (som_type)
        {
        case SYMBOL_TYPE_ABSOLUTE:
          info->symbol_type = ST_ABSOLUTE;
          break;
        case SYMBOL_TYPE_CODE:
          info->symbol_type = ST_CODE;
          break;
        case SYMBOL_TYPE_DATA:
          info->symbol_type = ST_DATA;
          break;
        case SYMBOL_TYPE_MILLICODE:
          info->symbol_type = ST_MILLICODE;
          break;
        case SYMBOL_TYPE_PLABEL:
          info->symbol_type = ST_PLABEL;
          break;
        case SYMBOL_TYPE_PRI_PROG:
          info->symbol_type = ST_PRI_PROG;
          break;
        case SYMBOL_TYPE_SEC_PROG:
          info->symbol_type = ST_SEC_PROG;
          break;
        default:
          break;
        }
    }

  if (!is_common_section)
    {
      if (is_undefined_section)
        info->symbol_scope = SS_UNSAT;
      else if ((sym->flags & (BSF_EXPORT | BSF_WEAK)) != 0)
        info->symbol_scope = SS_UNIVERSAL;
      else
        info->symbol_scope = SS_LOCAL;
    }

  if (is_common_section || is_undefined_section || is_absolute_section)
    info->symbol_info = 0;
  else
    info->symbol_info = section->target_index;

  info->symbol_value = sym->value + section->vma;

  info->secondary_def = (sym->flags & BSF_WEAK) != 0;

  struct som_section_info *sec_info = som_section_data(section);
  if (sec_info
      && sec_info->subspace_dict
      && info->symbol_scope == SS_UNIVERSAL
      && (info->symbol_type == ST_ENTRY
	  || info->symbol_type == ST_CODE
	  || info->symbol_type == ST_DATA))
    {
      info->is_comdat = sec_info->subspace_dict->is_comdat;
      info->is_common = sec_info->subspace_dict->is_common;
      info->dup_common = sec_info->subspace_dict->dup_common;
    }
}

/* Build and write, in one big chunk, the entire symbol table for
   this BFD.  */

static bool
som_build_and_write_symbol_table (bfd *abfd)
{
  unsigned int num_syms = bfd_get_symcount (abfd);
  file_ptr symtab_location = obj_som_file_hdr (abfd)->symbol_location;
  asymbol **bfd_syms = obj_som_sorted_syms (abfd);
  struct som_external_symbol_dictionary_record *som_symtab = NULL;
  bfd_size_type symtab_data_size;

  if (_bfd_mul_overflow (num_syms,
			 sizeof (struct som_external_symbol_dictionary_record),
			 &symtab_data_size))
    {
      bfd_set_error (bfd_error_no_memory);
      return false;
    }

  som_symtab = bfd_zmalloc (symtab_data_size);

  if (som_symtab == NULL && num_syms > 0)
    {
      bfd_set_error (bfd_error_no_memory);
      return false;
    }

  for (unsigned int i = 0; i < num_syms; i++)
    {
      struct som_misc_symbol_info info;
      unsigned int flags_field1;
      unsigned int flags_field2;

      bfd_putb32 (som_symbol_data (bfd_syms[i])->stringtab_offset,
		  som_symtab[i].name);

      som_bfd_derive_misc_symbol_info (abfd, bfd_syms[i], &info);

      flags_field1 = (info.symbol_type << SOM_SYMBOL_TYPE_SH)
	| (info.symbol_scope << SOM_SYMBOL_SCOPE_SH)
	| (info.arg_reloc << SOM_SYMBOL_ARG_RELOC_SH)
	| (3 << SOM_SYMBOL_XLEAST_SH)
	| (info.secondary_def ? SOM_SYMBOL_SECONDARY_DEF : 0)
	| (info.is_common ? SOM_SYMBOL_IS_COMMON : 0)
	| (info.dup_common ? SOM_SYMBOL_DUP_COMMON : 0);
      bfd_putb32 (flags_field1, som_symtab[i].flags);

      flags_field2 = (info.symbol_info << SOM_SYMBOL_SYMBOL_INFO_SH)
	| (info.is_comdat ? SOM_SYMBOL_IS_COMDAT : 0);
      bfd_putb32 (flags_field2, som_symtab[i].info);
      bfd_putb32 (info.symbol_value | info.priv_level,
		  som_symtab[i].symbol_value);
    }

  if (bfd_seek (abfd, symtab_location, SEEK_SET) != 0)
    {
      free (som_symtab);
      return false;
    }

  if (bfd_write (som_symtab, symtab_data_size, abfd) != symtab_data_size)
    {
      free (som_symtab);
      return false;
    }

  free (som_symtab);
  return true;
}

/* Write an object in SOM format.  */

static bool
som_write_object_contents (bfd *abfd)
{
  if (!abfd->output_has_begun)
    {
      if (!som_prep_headers (abfd))
        {
          return false;
        }

      if (!som_begin_writing (abfd))
        {
          return false;
        }

      abfd->output_has_begun = true;
    }

  return som_finish_writing (abfd);
}

/* Read and save the string table associated with the given BFD.  */

static bool
som_slurp_string_table (bfd *abfd)
{
  char *stringtab;
  bfd_size_type amt_read;
  bfd_size_type amt_alloc;

  if (obj_som_stringtab (abfd) != NULL)
    return true;

  amt_read = obj_som_stringtab_size (abfd);

  if (amt_read == 0)
    {
      bfd_set_error (bfd_error_no_symbols);
      return false;
    }

  if (amt_read == (bfd_size_type)-1)
    {
      bfd_set_error (bfd_error_invalid_value);
      return false;
    }
  amt_alloc = amt_read + 1;

  if (bfd_seek (abfd, obj_som_str_filepos (abfd), SEEK_SET) != 0)
    return false;

  stringtab = _bfd_malloc_and_read (abfd, amt_alloc, amt_read);
  if (stringtab == NULL)
    return false;

  stringtab[amt_read] = 0;

  obj_som_stringtab (abfd) = stringtab;
  return true;
}

/* Return the amount of data (in bytes) required to hold the symbol
   table for this object.  */

#include <limits.h>

static long
som_get_symtab_upper_bound (bfd *abfd)
{
  if (!som_slurp_symbol_table (abfd))
    {
      return -1;
    }

  long sym_count = bfd_get_symcount (abfd);

  if (sym_count < 0)
    {
      return -1;
    }

  if (sym_count == LONG_MAX)
    {
      return -1;
    }
  long num_elements = sym_count + 1;

  long element_size = (long) sizeof (asymbol *);

  if (element_size > 0 && num_elements > LONG_MAX / element_size)
    {
      return -1;
    }

  return num_elements * element_size;
}

/* Convert from a SOM subspace index to a BFD section.  */

asection *
bfd_section_from_som_symbol
  (bfd *abfd, struct som_external_symbol_dictionary_record *symbol)
{
  asection *section;

  if (abfd == NULL || symbol == NULL)
    {
      return bfd_abs_section_ptr;
    }

  unsigned int flags = bfd_getb32 (symbol->flags);
  unsigned int symbol_type = (flags >> SOM_SYMBOL_TYPE_SH) & SOM_SYMBOL_TYPE_MASK;

  int is_executable_or_dynamic = (abfd->flags & (EXEC_P | DYNAMIC)) != 0;
  int is_function_symbol = (symbol_type == ST_ENTRY ||
                            symbol_type == ST_PRI_PROG ||
                            symbol_type == ST_SEC_PROG ||
                            symbol_type == ST_MILLICODE);

  /* If the object is an executable or dynamic library, and the symbol is a
     function, we must use the symbol's address to locate its section. */
  if (is_executable_or_dynamic && is_function_symbol)
    {
      unsigned int value = bfd_getb32 (symbol->symbol_value);

      for (section = abfd->sections; section != NULL; section = section->next)
        {
          if (som_is_subspace (section) &&
              value >= section->vma &&
              value <= section->vma + section->size)
            {
              return section;
            }
        }
    }
  else /* Otherwise (e.g., a relocatable object, or a non-function symbol),
          we can use the symbol_info field as a direct index. */
    {
      int idx = (bfd_getb32 (symbol->info) >> SOM_SYMBOL_SYMBOL_INFO_SH)
        & SOM_SYMBOL_SYMBOL_INFO_MASK;

      for (section = abfd->sections; section != NULL; section = section->next)
        {
          if (section->target_index == idx && som_is_subspace (section))
            {
              return section;
            }
        }
    }

  /* If no matching section was found after trying both methods,
     return the absolute section pointer. */
  return bfd_abs_section_ptr;
}

/* Read and save the symbol table associated with the given BFD.  */

static unsigned int
som_slurp_symbol_table (bfd *abfd)
{
  unsigned int symbol_count = bfd_get_symcount (abfd);
  size_t symsize = sizeof (struct som_external_symbol_dictionary_record);
  char *stringtab = NULL;
  struct som_external_symbol_dictionary_record *buf = NULL;
  som_symbol_type *sym = NULL, *symbase = NULL;
  size_t amt;
  unsigned int ret_val = 0; /* Initialize to false, assuming failure */

  /* Return saved value if it exists. */
  if (obj_som_symtab (abfd) != NULL)
    return 1; /* true */

  /* Special case. This is *not* an error. */
  if (symbol_count == 0)
    return 1; /* true */

  if (!som_slurp_string_table (abfd))
    goto cleanup;

  stringtab = obj_som_stringtab (abfd);

  /* Read in the external SOM representation. */
  if (_bfd_mul_overflow (symbol_count, symsize, &amt))
    {
      bfd_set_error (bfd_error_file_too_big);
      goto cleanup;
    }
  if (bfd_seek (abfd, obj_som_sym_filepos (abfd), SEEK_SET) != 0)
    goto cleanup;
  buf = (struct som_external_symbol_dictionary_record *)
    _bfd_malloc_and_read (abfd, amt, amt);
  if (buf == NULL)
    goto cleanup;

  if (_bfd_mul_overflow (symbol_count, sizeof (som_symbol_type), &amt))
    {
      bfd_set_error (bfd_error_file_too_big);
      goto cleanup;
    }
  symbase = bfd_zmalloc (amt);
  if (symbase == NULL)
    goto cleanup;

  /* Iterate over all the symbols and internalize them. */
  struct som_external_symbol_dictionary_record *bufp;
  struct som_external_symbol_dictionary_record *endbufp = buf + symbol_count;
  for (bufp = buf, sym = symbase; bufp < endbufp; ++bufp)
    {
      unsigned int flags = bfd_getb32 (bufp->flags);
      unsigned int symbol_type =
	(flags >> SOM_SYMBOL_TYPE_SH) & SOM_SYMBOL_TYPE_MASK;
      unsigned int symbol_scope =
	(flags >> SOM_SYMBOL_SCOPE_SH) & SOM_SYMBOL_SCOPE_MASK;
      bfd_vma offset;

      /* I don't think we care about these. */
      if (symbol_type == ST_SYM_EXT || symbol_type == ST_ARG_EXT)
	continue;

      /* Set some private data we care about. */
      switch (symbol_type)
        {
        case ST_NULL:
          som_symbol_data (sym)->som_type = SYMBOL_TYPE_UNKNOWN;
          break;
        case ST_ABSOLUTE:
          som_symbol_data (sym)->som_type = SYMBOL_TYPE_ABSOLUTE;
          break;
        case ST_DATA:
          som_symbol_data (sym)->som_type = SYMBOL_TYPE_DATA;
          break;
        case ST_CODE:
          som_symbol_data (sym)->som_type = SYMBOL_TYPE_CODE;
          break;
        case ST_PRI_PROG:
          som_symbol_data (sym)->som_type = SYMBOL_TYPE_PRI_PROG;
          break;
        case ST_SEC_PROG:
          som_symbol_data (sym)->som_type = SYMBOL_TYPE_SEC_PROG;
          break;
        case ST_ENTRY:
          som_symbol_data (sym)->som_type = SYMBOL_TYPE_ENTRY;
          break;
        case ST_MILLICODE:
          som_symbol_data (sym)->som_type = SYMBOL_TYPE_MILLICODE;
          break;
        case ST_PLABEL:
          som_symbol_data (sym)->som_type = SYMBOL_TYPE_PLABEL;
          break;
        default:
          som_symbol_data (sym)->som_type = SYMBOL_TYPE_UNKNOWN;
          break;
        }

      som_symbol_data (sym)->tc_data.ap.hppa_arg_reloc =
	(flags >> SOM_SYMBOL_ARG_RELOC_SH) & SOM_SYMBOL_ARG_RELOC_MASK;

      /* Some reasonable defaults. */
      sym->symbol.the_bfd = abfd;
      offset = bfd_getb32 (bufp->name);
      if (offset < obj_som_stringtab_size (abfd))
	sym->symbol.name = offset + stringtab;
      else
	{
	  bfd_set_error (bfd_error_bad_value);
	  goto cleanup;
	}
      sym->symbol.value = bfd_getb32 (bufp->symbol_value);
      sym->symbol.section = NULL;
      sym->symbol.flags = 0;

      switch (symbol_type)
	{
	case ST_ENTRY:
	case ST_MILLICODE:
	  sym->symbol.flags |= BSF_FUNCTION;
	  som_symbol_data (sym)->tc_data.ap.hppa_priv_level =
	    sym->symbol.value & 0x3;
	  sym->symbol.value &= ~0x3;
	  break;

	case ST_STUB:
	case ST_CODE:
	case ST_PRI_PROG:
	case ST_SEC_PROG:
	  som_symbol_data (sym)->tc_data.ap.hppa_priv_level =
	    sym->symbol.value & 0x3;
	  sym->symbol.value &= ~0x3;
	  /* If the symbol's scope is SS_UNSAT, then these are
	     undefined function symbols. */
	  if (symbol_scope == SS_UNSAT)
	    sym->symbol.flags |= BSF_FUNCTION;
	  break;

	default:
	  break;
	}

      /* Handle scoping and section information. */
      switch (symbol_scope)
	{
	/* symbol_info field is undefined for SS_EXTERNAL and SS_UNSAT symbols,
	   so the section associated with this symbol can't be known. */
	case SS_EXTERNAL:
	  if (symbol_type != ST_STORAGE)
	    sym->symbol.section = bfd_und_section_ptr;
	  else
	    sym->symbol.section = bfd_com_section_ptr;
	  sym->symbol.flags |= (BSF_EXPORT | BSF_GLOBAL);
	  break;

	case SS_UNSAT:
	  if (symbol_type != ST_STORAGE)
	    sym->symbol.section = bfd_und_section_ptr;
	  else
	    sym->symbol.section = bfd_com_section_ptr;
	  break;

	case SS_UNIVERSAL:
	  sym->symbol.flags |= (BSF_EXPORT | BSF_GLOBAL);
	  sym->symbol.section = bfd_section_from_som_symbol (abfd, bufp);
          if (sym->symbol.section == NULL)
            {
              bfd_set_error(bfd_error_bad_value);
              goto cleanup;
            }
	  sym->symbol.value -= sym->symbol.section->vma;
	  break;

	case SS_LOCAL:
	  sym->symbol.flags |= BSF_LOCAL;
	  sym->symbol.section = bfd_section_from_som_symbol (abfd, bufp);
          if (sym->symbol.section == NULL)
            {
              bfd_set_error(bfd_error_bad_value);
              goto cleanup;
            }
	  sym->symbol.value -= sym->symbol.section->vma;
	  break;

	default:
	  sym->symbol.section = bfd_und_section_ptr;
	  break;
	}

      /* Check for a weak symbol. */
      if (flags & SOM_SYMBOL_SECONDARY_DEF)
	sym->symbol.flags |= BSF_WEAK;
      /* Mark section symbols and symbols used by the debugger.
	 Note $START$ is a magic code symbol, NOT a section symbol. */
      if (sym->symbol.name[0] == '$'
	  && sym->symbol.name[strlen (sym->symbol.name) - 1] == '$'
	  && !strcmp (sym->symbol.name, sym->symbol.section->name))
	sym->symbol.flags |= BSF_SECTION_SYM;
      else if (startswith (sym->symbol.name, "L$0\002"))
	{
	  sym->symbol.flags |= BSF_SECTION_SYM;
	  sym->symbol.name = sym->symbol.section->name;
	}
      else if (startswith (sym->symbol.name, "L$0\001"))
	sym->symbol.flags |= BSF_DEBUGGING;
      /* Note increment at bottom of loop, since we skip some symbols
	 we can not include it as part of the for statement. */
      sym++;
    }

  /* We modify the symbol count to record the number of BFD symbols we
     created. */
  abfd->symcount = sym - symbase;

  /* Save our results and return success. */
  obj_som_symtab (abfd) = symbase;
  ret_val = 1; /* true */

cleanup:
  /* `buf` is always freed, regardless of success or failure. */
  free (buf);
  /* `symbase` is only freed on error, as on success its ownership is transferred. */
  if (ret_val == 0)
    free (symbase);

  return ret_val;
}

/* Canonicalize a SOM symbol table.  Return the number of entries
   in the symbol table.  */

static long
som_canonicalize_symtab (bfd *abfd, asymbol **location)
{
  long symbol_count;
  som_symbol_type *symbase;

  if (abfd == NULL || location == NULL)
    return -1;

  if (!som_slurp_symbol_table (abfd))
    return -1;

  symbol_count = bfd_get_symcount (abfd);

  if (symbol_count == 0)
  {
    *location = 0;
    return 0;
  }

  symbase = obj_som_symtab (abfd);

  if (symbase == NULL)
  {
    return -1;
  }

  for (long i = 0; i < symbol_count; ++i)
  {
    *location = &symbase->symbol;
    location++;
    symbase++;
  }

  *location = 0;
  return symbol_count;
}

/* Make a SOM symbol.  There is nothing special to do here.  */

static asymbol *
som_make_empty_symbol (bfd *abfd)
{
  som_symbol_type *new_symbol_type = bfd_zalloc (abfd, sizeof (som_symbol_type));

  if (new_symbol_type == NULL)
    return NULL;
  new_symbol_type->symbol.the_bfd = abfd;

  return &new_symbol_type->symbol;
}

/* Print symbol information.  */

static void
som_print_symbol (bfd *abfd,
		  void *afile,
		  asymbol *symbol,
		  bfd_print_symbol_type how)
{
  if (afile == NULL || symbol == NULL)
    {
      return;
    }

  FILE *file = (FILE *) afile;
  const char *symbol_name = (symbol->name != NULL) ? symbol->name : "(null_symbol_name)";

  switch (how)
    {
    case bfd_print_symbol_name:
      fprintf (file, "%s", symbol_name);
      break;

    case bfd_print_symbol_more:
      fprintf (file, "som %08" PRIx64 " %x", (uint64_t) symbol->value, symbol->flags);
      break;

    case bfd_print_symbol_all:
      {
	const char *section_name;

	if (symbol->section != NULL && symbol->section->name != NULL)
	  {
	    section_name = symbol->section->name;
	  }
	else if (symbol->section != NULL) // section exists, but its name is NULL
	  {
	    section_name = "(*null_section_name*)";
	  }
	else // symbol->section == NULL
	  {
	    section_name = "(*none*)";
	  }

	bfd_print_symbol_vandf (abfd, (void *) file, symbol);
	fprintf (file, " %s\t%s", section_name, symbol_name);
	break;
      }
    }
}

static bool
som_bfd_is_local_label_name (bfd *abfd ATTRIBUTE_UNUSED,
			     const char *name)
{
  if (name == NULL)
    {
      return false;
    }

  if (name[0] == '\0' || name[1] == '\0')
    {
      return false;
    }

  return name[0] == 'L' && name[1] == '$';
}

/* Count or process variable-length SOM fixup records.

   To avoid code duplication we use this code both to compute the number
   of relocations requested by a stream, and to internalize the stream.

   When computing the number of relocations requested by a stream the
   variables rptr, section, and symbols have no meaning.

   Return the number of relocations requested by the fixup stream.  When
   not just counting

   This needs at least two or three more passes to get it cleaned up.  */

#include <stdbool.h>
#include <string.h>
#include <stdlib.h>
#include <ctype.h> // For ISUPPER, ISLOWER, ISDIGIT

// Forward declarations for external types/functions.
// These are minimal definitions needed for the refactored code to compile
// and reflect the external dependencies and their assumed structures.
typedef struct arelent arelent;
typedef struct asection asection;
typedef struct asymbol asymbol;
typedef struct fixup_format fixup_format;
typedef struct howto_struct howto_struct;

typedef unsigned char bfd_byte; // Common type for byte arrays in BFD

// Placeholder for bfd type, usually bfd_bfd
typedef struct bfd bfd;

// External struct definitions (simplified/placeholder)
struct arelent {
  unsigned int address;
  const struct howto_struct *howto;
  unsigned int addend;
  asymbol **sym_ptr_ptr;
};

struct asection {
  unsigned int flags;
  unsigned int size;
  bfd *owner;
  bfd_byte *contents; // Using bfd_byte* for consistency
};

struct asymbol {
  // Placeholder members for a symbol, actual structure would be in bfd.h
  int value;
};

// Placeholder for bfd_abs_section_ptr_type, assuming it holds a symbol.
// The original code implies it's a pointer to a struct containing a 'symbol' member.
typedef struct {
  asymbol symbol;
} bfd_abs_section_ptr_type;

// Placeholder for fixup_format and reloc_queue_type.
// The original code implies som_fixup_formats is an array.
struct fixup_format {
  const char *format; // Format string for parsing fixup data
  unsigned int D;     // Opcode class index or queue index
};

// Placeholder for a reloc queue entry, as implied by usage.
struct reloc_queue_entry {
  unsigned char *reloc;
  unsigned int length;
};
// Assuming reloc_queue is an array of reloc_queue_entry, indexed by D.
// The size [256] is an assumption based on typical byte-sized opcodes.
typedef struct reloc_queue_entry reloc_queue_type[256];

// Placeholder for howto_struct, assuming it has a 'type' member for relocation type.
struct howto_struct {
  unsigned int type;
  // Other members would be here in actual bfd.h
};

// Global/external variables assumed to be available from other modules.
extern const struct fixup_format som_fixup_formats[];
extern const struct howto_struct som_hppa_howto_table[];
extern bfd_abs_section_ptr_type *bfd_abs_section_ptr;
extern reloc_queue_type reloc_queue; // Assuming it's an actual array type

// External function declarations assumed to exist.
extern void som_initialize_reloc_queue(reloc_queue_type *queue);
extern void som_reloc_queue_fix(reloc_queue_type *queue, unsigned int index);
extern void som_reloc_queue_insert(unsigned char *fixup_start, unsigned int length, reloc_queue_type *queue);
extern unsigned int sign_extend(unsigned int value, int bits);
extern unsigned int HPPA_R_ADDEND(unsigned int addend_value, unsigned int flags);
extern bool bfd_malloc_and_get_section(bfd *abfd, asection *sec, bfd_byte **buf);
extern unsigned int bfd_get_32(bfd *abfd, const bfd_byte *data);

// External constant arrays for specific relocation types' sub-opcodes.
extern const int comp1_opcodes[];
extern const int comp2_opcodes[];
extern const int comp3_opcodes[];

// Placeholder values for flags and relocation types, should come from bfd.h or similar.
#define SEC_HAS_CONTENTS   0x01
#define R_NO_RELOCATION    0
#define R_DATA_OVERRIDE    1
#define R_PCREL_CALL       2
#define R_ABS_CALL         3
#define R_ENTRY            4
#define R_EXIT             5
#define R_DATA_ONE_SYMBOL  6
#define R_COMP1            7
#define R_COMP2            8
#define R_COMP3            9

// Constants for variable array indices for improved readability.
// These correspond to the single-character variable names used in format strings.
#define VAR_A_INDEX 'A' // Base index for 'A'
#define VAR_L_INDEX 'L' // Input length
#define VAR_D_INDEX 'D' // Opcode class index
#define VAR_U_INDEX 'U' // Saved unwind bits
#define VAR_S_INDEX 'S' // Symbol index
#define VAR_R_INDEX 'R' // Argument relocation bits
#define VAR_O_INDEX 'O' // Linker expression stack (opcode dependent)
#define VAR_V_INDEX 'V' // Value for addend
#define VAR_T_INDEX 'T' // Value for R_ENTRY addend

// Max number of variables (A-Z) in the `variables` array.
#define VAR_ALPHA_COUNT 26
// Max depth for the operand stack during format string evaluation.
#define OPERAND_STACK_SIZE 20

// Custom Stack implementation for format string parsing.
// Provides bounds checking for reliability.
typedef struct {
    int data[OPERAND_STACK_SIZE];
    int top; // Points to the next free slot (current size of stack).
} OperandStack;

static inline void stack_init(OperandStack *s) {
    s->top = 0;
}

static inline bool stack_push(OperandStack *s, int value) {
    if (s->top >= OPERAND_STACK_SIZE) {
        // Stack overflow detection.
        return false;
    }
    s->data[s->top++] = value;
    return true;
}

static inline bool stack_pop(OperandStack *s, int *value) {
    if (s->top <= 0) {
        // Stack underflow detection.
        return false;
    }
    *value = s->data[--s->top];
    return true;
}

// Helper to calculate relocation addend for 'R' (argument relocation bits) logic.
// This encapsulates complex bit manipulation logic, improving maintainability.
static void calculate_reloc_addend_value(arelent *rptr, unsigned int opcode, unsigned int r_val) {
    rptr->addend = 0;

    // Define the range of opcodes for "simple encoding" call types.
    const unsigned int PCREL_CALL_MIN_TYPE = R_PCREL_CALL;
    const unsigned int ABS_CALL_MIN_TYPE = R_ABS_CALL;
    const unsigned int CALL_TYPE_RANGE = 10; // R_PCREL_CALL through R_PCREL_CALL + 9

    if ((som_hppa_howto_table[opcode].type >= PCREL_CALL_MIN_TYPE && som_hppa_howto_table[opcode].type < PCREL_CALL_MIN_TYPE + CALL_TYPE_RANGE)
        || (som_hppa_howto_table[opcode].type >= ABS_CALL_MIN_TYPE && som_hppa_howto_table[opcode].type < ABS_CALL_MIN_TYPE + CALL_TYPE_RANGE))
    {
        // Simple encoding for R_PCREL_CALL and R_ABS_CALL family.
        if (r_val > 4) {
            r_val -= 5;
            rptr->addend |= 1;
        }
        // Apply specific bit masks based on the adjusted r_val.
        if (r_val == 4)
            rptr->addend |= (1 << 8) | (1 << 6) | (1 << 4) | (1 << 2);
        else if (r_val == 3)
            rptr->addend |= (1 << 8) | (1 << 6) | (1 << 4);
        else if (r_val == 2)
            rptr->addend |= (1 << 8) | (1 << 6);
        else if (r_val == 1)
            rptr->addend |= (1 << 8);
    } else {
        // Complex encoding for other R_RELOC_BITS types.
        unsigned int temp_r_val = r_val;
        unsigned int part_val1, part_val2;

        // Extract low order two bits.
        rptr->addend = temp_r_val & 0x3; // Mask for 0b11.
        temp_r_val >>= 2;

        // Process the second part of the value.
        part_val1 = temp_r_val / 10;
        temp_r_val -= part_val1 * 10; // Remainder for the third part.
        if (part_val1 == 9)
            rptr->addend += (0xE << 6); // 0xE is 0b1110.
        else {
            part_val2 = part_val1 / 3;
            part_val1 -= part_val2 * 3;
            rptr->addend += (part_val2 << 8) + (part_val1 << 6);
        }

        // Process the third part of the value.
        if (temp_r_val == 9)
            rptr->addend += (0xE << 2);
        else {
            part_val2 = temp_r_val / 3;
            temp_r_val -= part_val2 * 3;
            rptr->addend += (part_val2 << 4) + (temp_r_val << 2);
        }
    }
    rptr->addend = HPPA_R_ADDEND(rptr->addend, 0);
}


static unsigned int
som_set_reloc_info (unsigned char *fixup_stream,
		    unsigned int stream_length,
		    arelent *internal_relocs,
		    asection *section,
		    asymbol **symbols,
		    unsigned int symcount,
		    bool just_count)
{
  unsigned int deallocate_contents = 0;
  unsigned char *current_fixup_ptr = fixup_stream;
  unsigned char *end_of_fixup_stream = &fixup_stream[stream_length];
  
  // `variables` array acts as temporary registers (A-Z) for fixup processing.
  // 'L': input length, 'D': opcode class index, 'U': saved unwind bits, etc.
  int variables[VAR_ALPHA_COUNT];
  OperandStack operand_stack; // Stack for evaluating format string expressions.
  int relocation_count = 0;
  unsigned int current_output_offset = 0; // Tracks the address in the output section.
  int saved_unwind_bits = 0; // This variable holds the persistent 'U' value across fixups.

  arelent *current_reloc_entry_ptr = internal_relocs;

  som_initialize_reloc_queue (&reloc_queue);
  
  // Initialize all 'variables' to zero before starting the main loop.
  memset (variables, 0, sizeof (variables));
  stack_init(&operand_stack);

  while (current_fixup_ptr < end_of_fixup_stream)
    {
      // `initial_fixup_pos` stores the start of the current fixup for queueing later.
      unsigned char *initial_fixup_pos = current_fixup_ptr;

      // Ensure there's at least one byte available to read the opcode.
      if (current_fixup_ptr >= end_of_fixup_stream) {
        if (deallocate_contents) free(section->contents);
        return (unsigned int) -1; // Malformed input: unexpected end of stream.
      }
      unsigned int opcode = *current_fixup_ptr++;
      const struct fixup_format *format_info = &som_fixup_formats[opcode];

      bool prev_fixup_referenced = false;
      if (*format_info->format == 'P') // 'P' indicates a back-reference to a previous fixup.
	{
	  // Handle a request for a previous fixup (back-reference).
	  // Validate queue index and check if the referenced fixup exists.
	  if (format_info->D >= sizeof(reloc_queue)/sizeof(reloc_queue[0]) || !reloc_queue[format_info->D].reloc)
	    {
	      // Broken object file (likely fuzzed data). Ignore this fixup.
	      // `current_fixup_ptr` has already advanced past the 'P' opcode.
	      continue;
	    }

	  // Adjust `current_fixup_ptr` to point to the referenced fixup, and reorder it in the queue.
	  current_fixup_ptr = reloc_queue[format_info->D].reloc;
	  som_reloc_queue_fix (&reloc_queue, format_info->D);
	  prev_fixup_referenced = true;

          // Re-read the opcode and format information for the actual fixup referenced.
          if (current_fixup_ptr >= end_of_fixup_stream) {
             if (deallocate_contents) free(section->contents);
             return (unsigned int) -1; // Malformed: back-reference points outside the stream.
          }
	  opcode = *current_fixup_ptr++;
	  format_info = &som_fixup_formats[opcode];
	}

      // Initialize/reset per-fixup state for the `variables` array and `operand_stack`.
      // 'L' is input length, 'D' is opcode class index.
      variables[VAR_L_INDEX - VAR_A_INDEX] = 0;
      variables[VAR_D_INDEX - VAR_A_INDEX] = format_info->D;
      // 'U' (unwind bits) is loaded from its persistent storage.
      variables[VAR_U_INDEX - VAR_A_INDEX] = saved_unwind_bits;
      stack_init(&operand_stack); // Ensure stack is clean for new format string evaluation.

      // If this fixup corresponds to a BFD relocation, set up its default attributes.
      if (!just_count && som_hppa_howto_table[opcode].type != R_NO_RELOCATION && som_hppa_howto_table[opcode].type != R_DATA_OVERRIDE)
	{
	  current_reloc_entry_ptr->address = current_output_offset;
	  current_reloc_entry_ptr->howto = &som_hppa_howto_table[opcode];
	  current_reloc_entry_ptr->addend = 0;
	  current_reloc_entry_ptr->sym_ptr_ptr = &bfd_abs_section_ptr->symbol;
	}

      const char *format_code_ptr = format_info->format;

      // Parse and execute the format string to populate variables.
      while (*format_code_ptr)
	{
	  unsigned int target_var_char = *format_code_ptr++; // The variable (LHS) to assign to.
	  int operand1, operand2, assignment_value;

	  // Process the Right-Hand Side (RHS) expression of the assignment.
	  do
	    {
	      if (*format_code_ptr == '\0') {
	          if (deallocate_contents) free(section->contents);
	          return (unsigned int) -1; // Malformed: unexpected end of format string.
	      }
	      char current_format_char = *format_code_ptr++;

	      if (ISUPPER (current_format_char))
		{
		  // Push variable's current value onto the operand stack.
		  if (!stack_push(&operand_stack, variables[current_format_char - VAR_A_INDEX])) {
                      if (deallocate_contents) free(section->contents);
		      return (unsigned int) -1; // Stack overflow.
		  }
		}
	      else if (ISLOWER (current_format_char))
		{
		  // Read additional data from the fixup stream.
		  int bytes_to_read = current_format_char - 'a';
		  unsigned int value_from_stream = 0;
		  for (int i = 0; i < bytes_to_read; ++i) {
		      if (current_fixup_ptr >= end_of_fixup_stream) {
                          if (deallocate_contents) free(section->contents);
		          return (unsigned int) -1; // Malformed: ran out of fixup bytes mid-value read.
		      }
		      value_from_stream = (value_from_stream << 8) | *current_fixup_ptr++;
		  }
		  // Apply sign extension if the target variable is 'V' (Value).
		  if (target_var_char == VAR_V_INDEX)
		    value_from_stream = sign_extend (value_from_stream, bytes_to_read * 8);

		  if (!stack_push(&operand_stack, (int)value_from_stream)) {
                      if (deallocate_contents) free(section->contents);
		      return (unsigned int) -1; // Stack overflow.
		  }
		}
	      else if (ISDIGIT (current_format_char))
		{
		  // Parse and push a decimal constant.
		  unsigned int decimal_constant = current_format_char - '0';
		  while (*format_code_ptr && ISDIGIT (*format_code_ptr)) {
		    decimal_constant = (decimal_constant * 10) + (*format_code_ptr++ - '0');
                  }
		  if (!stack_push(&operand_stack, (int)decimal_constant)) {
                      if (deallocate_contents) free(section->contents);
		      return (unsigned int) -1; // Stack overflow.
		  }
		}
	      else
		{
		  // Operator found: pop two operands, perform operation, push result.
		  if (!stack_pop(&operand_stack, &operand2)) {
                      if (deallocate_contents) free(section->contents);
		      return (unsigned int) -1; // Stack underflow.
		  }
		  if (!stack_pop(&operand_stack, &operand1)) {
                      if (deallocate_contents) free(section->contents);
		      return (unsigned int) -1; // Stack underflow.
		  }

		  switch (current_format_char)
		    {
		    case '+': assignment_value = operand1 + operand2; break;
		    case '*': assignment_value = operand1 * operand2; break;
		    case '<': assignment_value = operand1 << operand2; break;
		    default:
                        if (deallocate_contents) free(section->contents);
		        return (unsigned int) -1; // Invalid operator in format string.
		    }
		  if (!stack_push(&operand_stack, assignment_value)) {
                      if (deallocate_contents) free(section->contents);
		      return (unsigned int) -1; // Stack overflow.
		  }
		}
	    }
	  while (*format_code_ptr && *format_code_ptr != '=');

	  // Expect an '=' operator to separate RHS from the next LHS.
	  if (*format_code_ptr != '=') {
              if (deallocate_contents) free(section->contents);
	      return (unsigned int) -1; // Malformed format string: Expected '='.
	  }
	  format_code_ptr++; // Move past '='.

	  // Pop the final computed value from the stack for assignment.
	  if (!stack_pop(&operand_stack, &assignment_value)) {
              if (deallocate_contents) free(section->contents);
	      return (unsigned int) -1; // Stack underflow (should not happen if RHS was well-formed).
	  }

	  // Perform the assignment and handle specific side effects based on the target variable.
	  variables[target_var_char - VAR_A_INDEX] = assignment_value;

	  switch (target_var_char)
	    {
	    case VAR_L_INDEX: // 'L': Consume bytes from the input space (advance output offset).
	      current_output_offset += assignment_value;
	      break;
	    case VAR_S_INDEX: // 'S': Set the symbol for the relocation.
	      if (!just_count && symbols != NULL && (unsigned int)assignment_value < symcount)
		current_reloc_entry_ptr->sym_ptr_ptr = &symbols[assignment_value];
	      break;
	    case VAR_R_INDEX: // 'R': Set argument relocation bits for a function call.
	      if (!just_count) {
		calculate_reloc_addend_value(current_reloc_entry_ptr, opcode, (unsigned int)assignment_value);
              }
	      break;
	    case VAR_O_INDEX: // 'O': Handle linker expression stack (opcode dependent).
	      const int *sub_op_array;
	      switch (opcode)
		{
		case R_COMP1: sub_op_array = comp1_opcodes; break;
		case R_COMP2: sub_op_array = comp2_opcodes; break;
		case R_COMP3: sub_op_array = comp3_opcodes; break;
		default:
                    if (deallocate_contents) free(section->contents);
		    return (unsigned int) -1; // Invalid opcode for 'O' variable.
		}
              // This loop searches `sub_op_array`. The result (`sub_op_array` pointer) is discarded.
              // This matches the original behavior, suggesting it might be dead code or an implicit external side-effect.
	      while (*sub_op_array <= (unsigned char)assignment_value)
		++sub_op_array;
	      --sub_op_array;
	      break;
	    case VAR_U_INDEX: // 'U': Update the persistent unwind bits.
	      saved_unwind_bits = assignment_value;
	      break;
	    default:
	      // Other variables ('D', 'V', 'T', etc.) have no special side effects at this point.
	      break;
	    }
	} // End of format string parsing for the current fixup.

      // If a previous fixup was referenced, restore `current_fixup_ptr` to continue
      // from the byte immediately after the 'P' opcode of the back-reference.
      if (prev_fixup_referenced)
	{
	  current_fixup_ptr = initial_fixup_pos + 1;
	}
      // Otherwise, if this fixup consumed more than just its initial opcode byte, queue it.
      else if (current_fixup_ptr > initial_fixup_pos + 1)
	som_reloc_queue_insert (initial_fixup_pos, current_fixup_ptr - initial_fixup_pos, &reloc_queue);

      // Process and count the relocation if its type is not R_DATA_OVERRIDE or R_NO_RELOCATION.
      if (som_hppa_howto_table[opcode].type != R_DATA_OVERRIDE && som_hppa_howto_table[opcode].type != R_NO_RELOCATION)
	{
	  if (!just_count)
	    {
	      if (som_hppa_howto_table[opcode].type == R_ENTRY)
		current_reloc_entry_ptr->addend = variables[VAR_T_INDEX - VAR_A_INDEX];
	      else if (som_hppa_howto_table[opcode].type == R_EXIT)
		current_reloc_entry_ptr->addend = variables[VAR_U_INDEX - VAR_A_INDEX];
	      else if (som_hppa_howto_table[opcode].type == R_PCREL_CALL || som_hppa_howto_table[opcode].type == R_ABS_CALL)
		; // Addend for call types is set by `calculate_reloc_addend_value` during 'R' processing.
	      else if (som_hppa_howto_table[opcode].type == R_DATA_ONE_SYMBOL)
		{
		  // Use value from 'V' variable first.
		  current_reloc_entry_ptr->addend = variables[VAR_V_INDEX - VAR_A_INDEX];

		  if (current_reloc_entry_ptr->addend == 0 && (section->flags & SEC_HAS_CONTENTS) != 0)
		    {
		      if (!section->contents)
			{
			  bfd_byte *contents_buffer = NULL;
			  if (!bfd_malloc_and_get_section (section->owner, section, &contents_buffer))
			    {
                              if (deallocate_contents) free(section->contents);
			      return (unsigned int) -1; // Error reading section contents.
			    }
			  section->contents = contents_buffer;
			  deallocate_contents = 1; // Mark for deallocation at function exit.
			}
                      // Calculate the exact address within section contents for reading.
                      unsigned int data_read_address = current_output_offset - variables[VAR_L_INDEX - VAR_A_INDEX];
		      if (data_read_address <= section->size && section->size - data_read_address >= 4)
			current_reloc_entry_ptr->addend = bfd_get_32 (section->owner,
						   (section->contents + data_read_address));
		    }
		}
	      else
		current_reloc_entry_ptr->addend = variables[VAR_V_INDEX - VAR_A_INDEX];
	      
              current_reloc_entry_ptr++; // Advance to the next relocation entry.
	    }
	  relocation_count++; // Increment count of processed relocations.

          // Reset the 'variables' array for the next "full" relocation.
          // 'saved_unwind_bits' is not part of this array and retains its state separately.
          memset (variables, 0, sizeof (variables));
	}
      // Re-load the persistent unwind bits into the 'U' variable for the *next* fixup's processing cycle.
      variables[VAR_U_INDEX - VAR_A_INDEX] = saved_unwind_bits;

    } // End of main while loop over fixup stream.

  // Clean up dynamically allocated section contents if necessary.
  if (deallocate_contents)
    {
      free (section->contents);
      section->contents = NULL;
    }

  return relocation_count;
}

/* Read in the relocs (aka fixups in SOM terms) for a section.

   som_get_reloc_upper_bound calls this routine with JUST_COUNT
   set to TRUE to indicate it only needs a count of the number
   of actual relocations.  */

static const unsigned int SOM_RELOC_COUNT_UNPARSED = (unsigned int) -1;

static bool
som_slurp_reloc_table (bfd *abfd,
                       asection *section,
                       asymbol **symbols,
                       bool just_count)
{
  struct som_section_data *sec_data = som_section_data (section);
  unsigned char *external_reloc_stream = NULL;
  arelent *internal_relocs_buffer = NULL;
  unsigned int num_relocs;
  size_t internal_relocs_alloc_size;

  if (sec_data->reloc_size == 0 || section->reloc_count == 0)
    return true;

  if (section->reloc_count == SOM_RELOC_COUNT_UNPARSED)
    {
      if (bfd_seek (abfd, obj_som_reloc_filepos (abfd) + section->rel_filepos, SEEK_SET) != 0)
        {
          bfd_set_error (bfd_error_system_call);
          return false;
        }

      external_reloc_stream = _bfd_malloc_and_read (abfd, sec_data->reloc_size, sec_data->reloc_size);
      if (external_reloc_stream == NULL)
        {
          return false;
        }

      section->reloc_count = som_set_reloc_info (external_reloc_stream,
                                                 sec_data->reloc_size,
                                                 NULL, NULL, NULL, 0, true);

      sec_data->reloc_stream = external_reloc_stream;
    }
  else
    {
      external_reloc_stream = sec_data->reloc_stream;
      if (external_reloc_stream == NULL)
        {
          bfd_set_error (bfd_error_bad_value);
          return false;
        }
    }

  if (just_count)
    return true;

  if (section->relocation != NULL)
    return true;

  num_relocs = section->reloc_count;

  if (_bfd_mul_overflow (num_relocs, sizeof (arelent), &internal_relocs_alloc_size))
    {
      bfd_set_error (bfd_error_file_too_big);
      return false;
    }

  internal_relocs_buffer = bfd_zalloc (abfd, internal_relocs_alloc_size);
  if (internal_relocs_buffer == NULL)
    {
      return false;
    }

  som_set_reloc_info (external_reloc_stream,
                      sec_data->reloc_size,
                      internal_relocs_buffer,
                      section,
                      symbols,
                      bfd_get_symcount (abfd),
                      false);

  free (sec_data->reloc_stream);
  sec_data->reloc_stream = NULL;

  section->relocation = internal_relocs_buffer;
  return true;
}

/* Return the number of bytes required to store the relocation
   information associated with the given section.  */

static long
som_get_reloc_upper_bound (bfd *abfd, sec_ptr asect)
{
  const long single_ptr_size = (long) sizeof (arelent *);

  if (single_ptr_size <= 0)
    {
      return -1;
    }

  if (asect->flags & SEC_RELOC)
    {
      if (! som_slurp_reloc_table (abfd, asect, NULL, true))
	{
	  return -1;
	}

      unsigned long num_elements = (unsigned long) asect->reloc_count;

      if (num_elements == ULONG_MAX)
        {
          return -1;
        }
      num_elements++;

      if (num_elements > (unsigned long) LONG_MAX / single_ptr_size)
        {
          return -1;
        }

      return (long) (num_elements * single_ptr_size);
    }

  return single_ptr_size;
}

/* Convert relocations from SOM (external) form into BFD internal
   form.  Return the number of relocations.  */

static long
som_canonicalize_reloc (bfd *abfd,
			sec_ptr section,
			arelent **relptr,
			asymbol **symbols)
{
  if (! som_slurp_reloc_table (abfd, section, symbols, false))
    return -1;

  if (section->reloc_count > 0 && section->relocation == NULL)
    return -1;

  arelent *src_ptr = section->relocation;
  arelent **dest_ptr = relptr;

  for (int i = 0; i < section->reloc_count; ++i) {
    *dest_ptr++ = src_ptr++;
  }

  *dest_ptr = NULL;

  return section->reloc_count;
}

extern const bfd_target hppa_som_vec;

/* A hook to set up object file dependent section information.  */

static bool
som_new_section_hook (bfd *abfd, asection *newsect)
{
  const size_t section_data_size = sizeof (struct som_section_data_struct);
  const unsigned int default_alignment_power = 3;

  newsect->used_by_bfd = bfd_zalloc (abfd, section_data_size);
  if (!newsect->used_by_bfd)
    return false;

  newsect->alignment_power = default_alignment_power;

  return _bfd_generic_new_section_hook (abfd, newsect);
}

/* Copy any private info we understand from the input symbol
   to the output symbol.  */

static bool
som_bfd_copy_private_symbol_data (bfd *ibfd,
				  asymbol *isymbol,
				  bfd *obfd,
				  asymbol *osymbol)
{
  if (!ibfd || !isymbol || !obfd || !osymbol)
    {
      return false;
    }

  struct som_symbol *input_symbol = (struct som_symbol *) isymbol;
  struct som_symbol *output_symbol = (struct som_symbol *) osymbol;

  if (!ibfd->xvec || !obfd->xvec)
    {
      return false;
    }

  if (ibfd->xvec->flavour != bfd_target_som_flavour
      || obfd->xvec->flavour != bfd_target_som_flavour)
    {
      return false;
    }

  output_symbol->tc_data.ap.hppa_arg_reloc =
    input_symbol->tc_data.ap.hppa_arg_reloc;

  return true;
}

/* Copy any private info we understand from the input section
   to the output section.  */

static bool
som_bfd_copy_private_section_data (bfd *ibfd,
                                   asection *isection,
                                   bfd *obfd,
                                   asection *osection,
                                   struct bfd_link_info *link_info)
{
  if (link_info != NULL
      || ibfd->xvec->flavour != bfd_target_som_flavour
      || obfd->xvec->flavour != bfd_target_som_flavour
      || (!som_is_space (isection) && !som_is_subspace (isection)))
    return true;

  struct som_section_data *isection_som_data = som_section_data(isection);
  struct som_section_data *osection_som_data = som_section_data(osection);

  if (isection_som_data->copy_data == NULL)
    {
      _bfd_error_handler (_("BFD: %pB[%pA]: source section has no SOM private data to copy to %pA"),
                          ibfd, isection, osection);
      return false;
    }

  size_t amt = sizeof (struct som_copyable_section_data_struct);
  osection_som_data->copy_data = bfd_zalloc (obfd, amt);
  if (osection_som_data->copy_data == NULL)
    {
      return false;
    }

  memcpy (osection_som_data->copy_data,
          isection_som_data->copy_data,
          amt);

  struct som_copyable_section_data_struct *copied_data = osection_som_data->copy_data;
  if (copied_data->container)
    {
      if (copied_data->container->output_section)
        copied_data->container = copied_data->container->output_section;
      else
        {
          _bfd_error_handler (_("%pB[%pA]: no output section for space %pA"),
                              obfd, osection, copied_data->container);
          return false;
        }
    }

  return true;
}

/* Copy any private info we understand from the input bfd
   to the output bfd.  */

static bool
som_bfd_copy_private_bfd_data (bfd *ibfd, bfd *obfd)
{
  if (ibfd->xvec->flavour != bfd_target_som_flavour ||
      obfd->xvec->flavour != bfd_target_som_flavour)
    {
      return true;
    }

  struct som_exec_data *obfd_som_data = bfd_zalloc (obfd, (bfd_size_type) sizeof (struct som_exec_data));
  if (obfd_som_data == NULL)
    {
      return false;
    }

  obj_som_exec_data (obfd) = obfd_som_data;

  struct som_exec_data *ibfd_som_data = obj_som_exec_data (ibfd);
  if (ibfd_som_data != NULL)
    {
      memcpy (obfd_som_data, ibfd_som_data, sizeof (struct som_exec_data));
    }

  return true;
}

/* Display the SOM header.  */

static bool
som_bfd_print_private_bfd_data (bfd *abfd, void *farg)
{
  struct som_exec_auxhdr *exec_header;
  struct som_aux_id* auxhdr;
  FILE *f;

  f = (FILE *) farg;

  exec_header = obj_som_exec_hdr (abfd);
  if (exec_header)
    {
      fprintf (f, _("\nExec Auxiliary Header\n"));
      fprintf (f, "  flags              ");
      auxhdr = &exec_header->som_auxhdr;
      if (auxhdr->mandatory)
	fprintf (f, "mandatory ");
      if (auxhdr->copy)
	fprintf (f, "copy ");
      if (auxhdr->append)
	fprintf (f, "append ");
      if (auxhdr->ignore)
	fprintf (f, "ignore ");
      fprintf (f, "\n");
      fprintf (f, "  type               %#x\n", auxhdr->type);
      fprintf (f, "  length             %#x\n", auxhdr->length);

      fprintf (f, "  text size          %#" BFD_VMA_FMT "\n", exec_header->exec_tsize);
      fprintf (f, "  text memory offset %#" BFD_VMA_FMT "\n", exec_header->exec_tmem);
      fprintf (f, "  text file offset   %#" BFD_VMA_FMT "\n", exec_header->exec_tfile);
      fprintf (f, "  data size          %#" BFD_VMA_FMT "\n", exec_header->exec_dsize);
      fprintf (f, "  data memory offset %#" BFD_VMA_FMT "\n", exec_header->exec_dmem);
      fprintf (f, "  data file offset   %#" BFD_VMA_FMT "\n", exec_header->exec_dfile);
      fprintf (f, "  bss size           %#" BFD_VMA_FMT "\n", exec_header->exec_bsize);
      fprintf (f, "  entry point        %#" BFD_VMA_FMT "\n", exec_header->exec_entry);
      fprintf (f, "  loader flags       %#" BFD_VMA_FMT "\n", exec_header->exec_flags);
      fprintf (f, "  bss initializer    %#" BFD_VMA_FMT "\n", exec_header->exec_bfill);
    }

  return true;
}

/* Set backend info for sections which can not be described
   in the BFD data structures.  */

bool
bfd_som_set_section_attributes (asection *section,
				int defined,
				int private,
				unsigned int sort_key,
				int spnum)
{
  struct som_section_data *som_data = som_section_data (section);
  struct som_copyable_section_data_struct *copy_data_ptr = som_data->copy_data;

  if (copy_data_ptr == NULL)
    {
      size_t amt = sizeof (struct som_copyable_section_data_struct);
      copy_data_ptr = bfd_zalloc (section->owner, amt);
      if (copy_data_ptr == NULL)
	{
	  return false;
	}
      som_data->copy_data = copy_data_ptr;
    }

  copy_data_ptr->sort_key = sort_key;
  copy_data_ptr->is_defined = defined;
  copy_data_ptr->is_private = private;
  copy_data_ptr->container = section;
  copy_data_ptr->space_number = spnum;

  return true;
}

/* Set backend info for subsections which can not be described
   in the BFD data structures.  */

bool
bfd_som_set_subsection_attributes (asection *section,
				   asection *container,
				   int access_ctr,
				   unsigned int sort_key,
				   int quadrant,
				   int comdat,
				   int common,
				   int dup_common)
{
  struct som_section_data_struct *data = som_section_data (section);

  if (data->copy_data == NULL)
    {
      size_t amt = sizeof (struct som_copyable_section_data_struct);

      data->copy_data = bfd_zalloc (section->owner, amt);
      if (data->copy_data == NULL)
	return false;
    }
  data->copy_data->sort_key = sort_key;
  data->copy_data->access_control_bits = access_ctr;
  data->copy_data->quadrant = quadrant;
  data->copy_data->container = container;
  data->copy_data->is_comdat = comdat;
  data->copy_data->is_common = common;
  data->copy_data->dup_common = dup_common;
  return true;
}

/* Set the full SOM symbol type.  SOM needs far more symbol information
   than any other object file format I'm aware of.  It is mandatory
   to be able to know if a symbol is an entry point, millicode, data,
   code, absolute, storage request, or procedure label.  If you get
   the symbol type wrong your program will not link.  */

void
bfd_som_set_symbol_type (asymbol *symbol, unsigned int type)
{
  if (symbol != NULL)
    {
      som_symbol_data (symbol)->som_type = type;
    }
}

/* Attach an auxiliary header to the BFD backend so that it may be
   written into the object file.  */

static struct som_string_auxhdr *
bfd_som_create_string_aux_hdr_internal(bfd *abfd, int type, const char *string_val)
{
  size_t len = strlen(string_val);
  size_t pad = (4 - (len % 4)) % 4;
  size_t total_alloc_size = sizeof(struct som_string_auxhdr) + len + pad;

  struct som_string_auxhdr *hdr = bfd_zalloc(abfd, total_alloc_size);
  if (hdr == NULL)
    {
      return NULL;
    }

  hdr->header_id.type = (unsigned int)type;
  hdr->header_id.length = (unsigned int)(4 + len + pad);
  hdr->string_length = (unsigned int)len;

  memcpy(hdr->string, string_val, len);
  memset(hdr->string + len, 0, pad);

  return hdr;
}

bool
bfd_som_attach_aux_hdr (bfd *abfd, int type, char *string)
{
  struct som_string_auxhdr *new_hdr;

  if (type == VERSION_AUX_ID)
    {
      new_hdr = bfd_som_create_string_aux_hdr_internal(abfd, type, string);
      if (new_hdr == NULL)
        {
          return false;
        }
      obj_som_version_hdr(abfd) = new_hdr;
    }
  else if (type == COPYRIGHT_AUX_ID)
    {
      new_hdr = bfd_som_create_string_aux_hdr_internal(abfd, type, string);
      if (new_hdr == NULL)
        {
          return false;
        }
      obj_som_copyright_hdr(abfd) = new_hdr;
    }
  return true;
}

/* Attach a compilation unit header to the BFD backend so that it may be
   written into the object file.  */

static char *
som_bfd_strdup (bfd *abfd, const char *s)
{
  char *new_s;
  if (s == NULL)
    return NULL;

  bfd_size_type len = (bfd_size_type) strlen (s) + 1;
  new_s = bfd_alloc (abfd, len);
  if (new_s == NULL)
    return NULL;

  strcpy (new_s, s);
  return new_s;
}

bool
bfd_som_attach_compilation_unit (bfd *abfd,
				 const char *name,
				 const char *language_name,
				 const char *product_id,
				 const char *version_id)
{
  struct som_compilation_unit *n;

  n = (struct som_compilation_unit *) bfd_zalloc
    (abfd, (bfd_size_type) sizeof (*n));
  if (n == NULL)
    return false;

  n->name.name = som_bfd_strdup (abfd, name);
  if (name != NULL && n->name.name == NULL)
    return false;

  n->language_name.name = som_bfd_strdup (abfd, language_name);
  if (language_name != NULL && n->language_name.name == NULL)
    return false;

  n->product_id.name = som_bfd_strdup (abfd, product_id);
  if (product_id != NULL && n->product_id.name == NULL)
    return false;

  n->version_id.name = som_bfd_strdup (abfd, version_id);
  if (version_id != NULL && n->version_id.name == NULL)
    return false;

  obj_som_compilation_unit (abfd) = n;

  return true;
}

static bool
som_get_section_contents (bfd *abfd,
			  sec_ptr section,
			  void *location,
			  file_ptr offset,
			  bfd_size_type count)
{
  if (count == 0 || !(section->flags & SEC_HAS_CONTENTS))
    {
      return true;
    }

  if (offset > section->size)
    {
      return false;
    }

  if (count > section->size - offset)
    {
      return false;
    }

  if (bfd_seek (abfd, section->filepos + offset, SEEK_SET) != 0)
    {
      return false;
    }

  if (bfd_read (location, count, abfd) != count)
    {
      return false;
    }

  return true;
}

static bool
som_set_section_contents (bfd *abfd,
			  sec_ptr section,
			  const void *location,
			  file_ptr offset,
			  bfd_size_type count)
{
  if (!abfd->output_has_begun)
    {
      som_prep_headers (abfd);
      abfd->output_has_begun = true;
      som_begin_writing (abfd);
    }

  if (!som_is_subspace (section)
      || ((section->flags & SEC_HAS_CONTENTS) == 0))
    {
      return true;
    }

  som_section_data_ptr section_data = som_section_data (section);
  if (section_data == NULL)
    {
      _bfd_error_handler (_("Internal BFD error: SOM section data is missing for section '%s'.",
                            section ? section->name : "<unknown>"));
      bfd_set_error (bfd_error_invalid_value);
      return false;
    }

  if (section_data->subspace_dict == NULL)
    {
      _bfd_error_handler (_("Internal BFD error: Subspace dictionary is missing for section '%s'.",
                            section ? section->name : "<unknown>"));
      bfd_set_error (bfd_error_invalid_value);
      return false;
    }

  offset += section_data->subspace_dict->file_loc_init_value;

  if (bfd_seek (abfd, offset, SEEK_SET) != 0)
    {
      return false;
    }

  if (bfd_write (location, count, abfd) != count)
    {
      return false;
    }

  return true;
}

static inline bool
som_set_arch_mach (bfd *abfd,
		   enum bfd_architecture arch,
		   unsigned long machine)
{
  return bfd_default_set_arch_mach (abfd, arch, machine);
}

static bool
som_find_nearest_line (bfd *abfd,
                       asymbol **symbols,
                       asection *section,
                       bfd_vma offset,
                       const char **filename_ptr,
                       const char **functionname_ptr,
                       unsigned int *line_ptr,
                       unsigned int *discriminator_ptr)
{
  bool stab_found;
  asymbol *func;
  bfd_vma low_func;
  asymbol **p;

  if (discriminator_ptr)
    *discriminator_ptr = 0;

  if (! _bfd_stab_section_find_nearest_line (abfd, symbols, section, offset,
                                             & stab_found, filename_ptr,
                                             functionname_ptr, line_ptr,
                                             & somdata (abfd).line_info))
    return false;

  if (stab_found)
    return true;

  if (symbols == NULL)
    return false;

  func = NULL;
  low_func = 0;

  for (p = symbols; *p != NULL; p++)
    {
      som_symbol_type *q = (som_symbol_type *) *p;

      if (q->som_type == SYMBOL_TYPE_ENTRY
          && q->symbol.section == section
          && q->symbol.value >= low_func
          && q->symbol.value <= offset)
        {
          func = (asymbol *) q;
          low_func = q->symbol.value;
        }
    }

  if (func == NULL)
    return false;

  *filename_ptr = NULL;
  *functionname_ptr = bfd_asymbol_name (func);
  *line_ptr = 0;

  return true;
}

#include <stdlib.h> // For exit

static int
som_sizeof_headers (bfd *abfd ATTRIBUTE_UNUSED,
		    struct bfd_link_info *info ATTRIBUTE_UNUSED)
{
  _bfd_error_handler (_("som_sizeof_headers unimplemented"));
  exit(EXIT_FAILURE);
}

/* Return the single-character symbol type corresponding to
   SOM section S, or '?' for an unknown SOM section.  */

static char
som_section_type (const char *s)
{
  const struct section_to_type *t;

  if (s == NULL)
    {
      return '?';
    }

  for (t = &stt[0]; t->section != NULL; ++t)
    {
      if (strcmp (s, t->section) == 0)
        {
          return t->type;
        }
    }
  return '?';
}

static int
som_decode_symclass (asymbol *symbol)
{
  char c;

  if (symbol == NULL || symbol->section == NULL)
    return '?';

  if (bfd_is_com_section (symbol->section))
    return 'C';

  if (bfd_is_und_section (symbol->section))
    {
      if (symbol->flags & BSF_WEAK)
	{
	  return (symbol->flags & BSF_OBJECT) ? 'v' : 'w';
	}
      else
	{
	  return 'U';
	}
    }

  if (bfd_is_ind_section (symbol->section))
    return 'I';

  if (symbol->flags & BSF_WEAK)
    {
      return (symbol->flags & BSF_OBJECT) ? 'V' : 'W';
    }

  if (!(symbol->flags & (BSF_GLOBAL | BSF_LOCAL)))
    return '?';

  struct som_symbol_data *sym_data = som_symbol_data (symbol);
  if (bfd_is_abs_section (symbol->section) ||
      (sym_data != NULL && sym_data->som_type == SYMBOL_TYPE_ABSOLUTE))
    {
      c = 'a';
    }
  else
    {
      c = som_section_type (symbol->section->name);
    }

  if (symbol->flags & BSF_GLOBAL)
    {
      c = TOUPPER (c);
    }

  return c;
}

/* Return information about SOM symbol SYMBOL in RET.  */

static void
som_get_symbol_info (bfd *ignore_abfd ATTRIBUTE_UNUSED,
		     asymbol *symbol,
		     symbol_info *ret)
{
  ret->type = som_decode_symclass (symbol);

  ret->value = 0;

  if (ret->type != 'U')
    {
      if (symbol->section != NULL)
        {
          ret->value = symbol->value + symbol->section->vma;
        }
    }
  ret->name = symbol->name;
}

/* Count the number of symbols in the archive symbol table.  Necessary
   so that we can allocate space for all the carsyms at once.  */

static bool
som_bfd_count_ar_symbols (bfd *abfd,
			  struct som_lst_header *lst_header,
			  symindex *count)
{
  unsigned char *hash_table = NULL;
  size_t amt;
  file_ptr lst_filepos;
  bool success = true;

  lst_filepos = bfd_tell (abfd) - sizeof (struct som_external_lst_header);

  if (_bfd_mul_overflow (lst_header->hash_size, 4, &amt))
    {
      bfd_set_error (bfd_error_file_too_big);
      success = false;
    }
  else if (lst_header->hash_size > 0)
    {
      hash_table = _bfd_malloc_and_read (abfd, amt, amt);
      if (hash_table == NULL)
        {
          success = false;
        }
    }

  if (!success)
    {
      return false;
    }

  *count = 0;

  for (unsigned int i = 0; i < lst_header->hash_size; i++)
    {
      struct som_external_lst_symbol_record ext_lst_symbol;
      unsigned int hash_val = bfd_getb32 (hash_table + 4 * i);

      if (hash_val == 0)
	continue;

      if (bfd_seek (abfd, lst_filepos + hash_val, SEEK_SET) != 0)
        {
          success = false;
          break;
        }

      amt = sizeof (ext_lst_symbol);
      if (bfd_read (&ext_lst_symbol, amt, abfd) != amt)
        {
          success = false;
          break;
        }

      (*count)++;

      while (true)
	{
	  unsigned int next_entry = bfd_getb32 (ext_lst_symbol.next_entry);

	  if (next_entry == 0)
	    break;

	  if (next_entry < hash_val + sizeof (ext_lst_symbol))
	    {
	      bfd_set_error (bfd_error_bad_value);
	      success = false;
	      break;
	    }
	  hash_val = next_entry;

	  if (bfd_seek (abfd, lst_filepos + next_entry, SEEK_SET) != 0)
	    {
	      success = false;
	      break;
	    }

	  amt = sizeof (ext_lst_symbol);
	  if (bfd_read (&ext_lst_symbol, amt, abfd) != amt)
	    {
	      success = false;
	      break;
	    }

	  (*count)++;
	}

      if (!success)
        {
          break;
        }
    }

  free (hash_table);
  return success;
}

/* Fill in the canonical archive symbols (SYMS) from the archive described
   by ABFD and LST_HEADER.  */

static bool
som_bfd_fill_in_ar_symbols (bfd *abfd,
                            struct som_lst_header *lst_header,
                            carsym **syms)
{
  carsym *current_sym = syms[0];
  unsigned char *hash_table = NULL;
  struct som_external_som_entry *som_dict = NULL;
  bool success = false;
  size_t required_amt;
  file_ptr lst_filepos;
  unsigned int string_table_base_loc;

  lst_filepos = bfd_tell (abfd) - sizeof (struct som_external_lst_header);
  string_table_base_loc = lst_header->string_loc;

  if (_bfd_mul_overflow (lst_header->hash_size, 4, &required_amt))
    {
      bfd_set_error (bfd_error_file_too_big);
      goto cleanup;
    }
  if (lst_header->hash_size != 0)
    {
      hash_table = _bfd_malloc_and_read (abfd, required_amt, required_amt);
      if (hash_table == NULL)
        goto cleanup;
    }

  if (bfd_seek (abfd, lst_filepos + lst_header->dir_loc, SEEK_SET) != 0)
    goto cleanup;

  if (_bfd_mul_overflow (lst_header->module_count,
                         sizeof (struct som_external_som_entry), &required_amt))
    {
      bfd_set_error (bfd_error_file_too_big);
      goto cleanup;
    }
  if (lst_header->module_count != 0)
    {
      som_dict = (struct som_external_som_entry *)
        _bfd_malloc_and_read (abfd, required_amt, required_amt);
      if (som_dict == NULL)
        goto cleanup;
    }

  for (unsigned int i = 0; i < lst_header->hash_size; i++)
    {
      unsigned int hash_chain_offset = bfd_getb32 (hash_table + 4 * i);
      if (hash_chain_offset == 0)
        continue;

      unsigned int current_entry_offset = hash_chain_offset;

      while (current_entry_offset != 0)
        {
          struct som_external_lst_symbol_record lst_symbol;
          size_t name_len;
          unsigned char ext_len_buf[4];
          char *name_str;
          unsigned int som_idx;

          if (bfd_seek (abfd, lst_filepos + current_entry_offset, SEEK_SET) != 0)
            goto cleanup;

          if (bfd_read (&lst_symbol, sizeof (lst_symbol), abfd) != sizeof (lst_symbol))
            goto cleanup;

          if (bfd_seek (abfd, (lst_filepos + string_table_base_loc
                               + bfd_getb32 (lst_symbol.name) - 4), SEEK_SET) != 0)
            goto cleanup;

          if (bfd_read (&ext_len_buf, 4, abfd) != 4)
            goto cleanup;
          name_len = bfd_getb32 (ext_len_buf);

          if (name_len == (size_t) -1)
            {
              bfd_set_error (bfd_error_no_memory);
              goto cleanup;
            }
          
          name_str = (char *) _bfd_alloc_and_read (abfd, name_len + 1, name_len);
          if (name_str == NULL)
            goto cleanup;
          name_str[name_len] = '\0';
          current_sym->name = name_str;

          som_idx = bfd_getb32 (lst_symbol.som_index);
          if (som_idx >= lst_header->module_count)
            {
              bfd_set_error (bfd_error_bad_value);
              goto cleanup;
            }
          current_sym->file_offset = bfd_getb32 (som_dict[som_idx].location) - sizeof (struct ar_hdr);

          current_sym++;

          current_entry_offset = bfd_getb32 (lst_symbol.next_entry);
        }
    }

  success = true;

cleanup:
  free (hash_table);
  free (som_dict);
  return success;
}

/* Read in the LST from the archive.  */

static bool
som_slurp_armap (bfd *abfd)
{
  struct som_external_lst_header ext_lst_header;
  struct som_lst_header lst_header;
  struct ar_hdr ar_header;
  unsigned int parsed_size;
  struct artdata *ardata = bfd_ardata (abfd);
  
  const size_t AR_NAME_LENGTH = 16;
  const char *AR_SYMTAB_NAME_PREFIX = "/               ";
  const size_t AR_FMAG_LENGTH = 2;
  const int STRTO_BASE = 10;

  char nextname_buffer[AR_NAME_LENGTH + 1]; /* +1 for potential null termination if needed by helper */
  bfd_size_type bytes_read;
  file_ptr_t current_pos;
  long l_parsed_size;
  char *endptr;
  size_t allocation_size;

  bytes_read = bfd_read (nextname_buffer, AR_NAME_LENGTH, abfd);
  if (bytes_read == 0)
    {
      return true; /* Empty archive or no more members, considered a valid state without an armap. */
    }
  if (bytes_read != AR_NAME_LENGTH)
    {
      if (bfd_get_error () == bfd_error_no_error)
        bfd_set_error (bfd_error_malformed_archive);
      return false;
    }

  if (bfd_seek (abfd, -(bfd_off_t)AR_NAME_LENGTH, SEEK_CUR) != 0)
    {
      return false; /* bfd_seek sets bfd_error on failure. */
    }

  if (strncmp (nextname_buffer, AR_SYMTAB_NAME_PREFIX, AR_NAME_LENGTH) != 0)
    {
      abfd->has_armap = false;
      return true; /* Member is not the archive symbol table. */
    }

  const size_t AR_HDR_SIZE = sizeof (struct ar_hdr);
  bytes_read = bfd_read (&ar_header, AR_HDR_SIZE, abfd);
  if (bytes_read != AR_HDR_SIZE)
    {
      if (bfd_get_error () == bfd_error_no_error)
        bfd_set_error (bfd_error_malformed_archive);
      return false;
    }

  if (strncmp (ar_header.ar_fmag, ARFMAG, AR_FMAG_LENGTH) != 0)
    {
      bfd_set_error (bfd_error_malformed_archive);
      return false;
    }

  errno = 0;
  l_parsed_size = strtol (ar_header.ar_size, &endptr, STRTO_BASE);
  if (errno == ERANGE || l_parsed_size < 0 || (unsigned long)l_parsed_size > UINT_MAX
      || (l_parsed_size == 0 && endptr == ar_header.ar_size)) /* Catches "  " or "abc" */
    {
      bfd_set_error (bfd_error_malformed_archive);
      return false;
    }
  parsed_size = (unsigned int) l_parsed_size;

  current_pos = bfd_tell (abfd);
  if (current_pos == (file_ptr_t) -1)
    {
      return false; /* bfd_tell sets bfd_error on failure. */
    }
  ardata->first_file_filepos = current_pos + parsed_size;

  const size_t EXT_LST_HDR_SIZE = sizeof (struct som_external_lst_header);
  bytes_read = bfd_read (&ext_lst_header, EXT_LST_HDR_SIZE, abfd);
  if (bytes_read != EXT_LST_HDR_SIZE)
    {
      if (bfd_get_error () == bfd_error_no_error)
        bfd_set_error (bfd_error_malformed_archive);
      return false;
    }

  som_swap_lst_header_in (&ext_lst_header, &lst_header);

  if (lst_header.a_magic != LIBMAGIC)
    {
      bfd_set_error (bfd_error_malformed_archive);
      return false;
    }

  if (!som_bfd_count_ar_symbols (abfd, &lst_header, &ardata->symdef_count))
    {
      return false; /* Assumed som_bfd_count_ar_symbols sets bfd_error. */
    }

  file_ptr_t symtab_member_start = ardata->first_file_filepos - parsed_size;
  file_ptr_t seek_to_sym_entries = symtab_member_start + (file_ptr_t)EXT_LST_HDR_SIZE;
  if (bfd_seek (abfd, seek_to_sym_entries, SEEK_SET) != 0)
    {
      return false; /* bfd_seek sets bfd_error on failure. */
    }

  ardata->cache = 0;

  if (_bfd_mul_overflow (ardata->symdef_count, sizeof (carsym), &allocation_size))
    {
      bfd_set_error (bfd_error_file_too_big);
      return false;
    }

  ardata->symdefs = bfd_alloc (abfd, allocation_size);
  if (!ardata->symdefs)
    {
      /* bfd_alloc should set bfd_error_no_memory on failure. */
      return false;
    }

  if (!som_bfd_fill_in_ar_symbols (abfd, &lst_header, &ardata->symdefs))
    {
      return false; /* Assumed som_bfd_fill_in_ar_symbols sets bfd_error. */
    }

  if (bfd_seek (abfd, ardata->first_file_filepos, SEEK_SET) != 0)
    {
      return false; /* bfd_seek sets bfd_error on failure. */
    }

  abfd->has_armap = true;
  return true;
}

/* Begin preparing to write a SOM library symbol table.

   As part of the prep work we need to determine the number of symbols
   and the size of the associated string section.  */

static bool
is_som_eligible_for_library_symbol_table (bfd *abfd, som_symbol_type *som_sym)
{
  struct som_misc_symbol_info info;

  som_bfd_derive_misc_symbol_info (abfd, &som_sym->symbol, &info);

  if (info.symbol_type == ST_NULL
      || info.symbol_type == ST_SYM_EXT
      || info.symbol_type == ST_ARG_EXT)
    {
      return false;
    }

  if (info.symbol_scope != SS_UNIVERSAL
      && info.symbol_type != ST_STORAGE)
    {
      return false;
    }

  if (bfd_is_und_section (som_sym->symbol.section))
    {
      return false;
    }

  return true;
}

#define ROUND_UP_TO_4(val) (((val) + 3U) & ~3U)

static bool
som_bfd_prep_for_ar_write (bfd *abfd,
			   unsigned int *num_syms,
			   unsigned int *stringsize)
{
  bfd *curr_bfd = abfd->archive_head;

  *num_syms = 0;
  *stringsize = 0;

  while (curr_bfd != NULL)
    {
      if (curr_bfd->format != bfd_object
	  || curr_bfd->xvec == NULL
	  || curr_bfd->xvec->flavour != bfd_target_som_flavour)
	{
	  curr_bfd = curr_bfd->archive_next;
	  continue;
	}

      if (! som_slurp_symbol_table (curr_bfd))
	{
	  return false;
	}

      som_symbol_type *som_syms = obj_som_symtab (curr_bfd);
      unsigned int curr_count = bfd_get_symcount (curr_bfd);

      if (curr_count > 0 && som_syms == NULL)
        {
          return false;
        }

      for (unsigned int i = 0; i < curr_count; i++)
	{
	  som_symbol_type *current_sym = &som_syms[i];

	  if (! is_som_eligible_for_library_symbol_table (curr_bfd, current_sym))
	    {
	      continue;
	    }

	  if (*num_syms == UINT_MAX)
	    {
	      return false;
	    }
	  (*num_syms)++;

	  size_t name_len = strlen (current_sym->symbol.name);
	  unsigned int temp_val_for_round;

	  if (name_len > UINT_MAX - 5)
	    {
	      return false;
	    }
	  temp_val_for_round = (unsigned int)name_len + 5;

	  if (UINT_MAX - *stringsize < temp_val_for_round)
	    {
	      return false;
	    }

	  unsigned int new_stringsize_candidate = *stringsize + temp_val_for_round;
	  *stringsize = ROUND_UP_TO_4(new_stringsize_candidate);
	}

      curr_bfd = curr_bfd->archive_next;
    }
  return true;
}

/* Hash a symbol name based on the hashing algorithm presented in the
   SOM ABI.  */

static unsigned int
som_bfd_ar_symbol_hash (asymbol *symbol)
{
  if (symbol == NULL || symbol->name == NULL) {
    return 0U;
  }

  unsigned int len = strlen(symbol->name);

  if (len == 0) {
    return 0U;
  }

  if (len == 1) {
    unsigned int char0 = (unsigned char)symbol->name[0];
    return 0x1000100U | (char0 << 16) | char0;
  }

  unsigned int char1 = (unsigned char)symbol->name[1];
  unsigned int char_len_minus_2 = (unsigned char)symbol->name[len - 2];
  unsigned int char_len_minus_1 = (unsigned char)symbol->name[len - 1];

  return ((len & 0x7fU) << 24)
         | (char1 << 16)
         | (char_len_minus_2 << 8)
         | char_len_minus_1;
}

/* Do the bulk of the work required to write the SOM library
   symbol table.  */

static bool
som_bfd_ar_write_symbol_stuff (bfd *abfd,
                               unsigned int nsyms,
                               unsigned int string_size,
                               struct som_external_lst_header lst,
                               unsigned elength)
{
  char *strings = NULL;
  char *current_string_ptr = NULL;
  struct som_external_lst_symbol_record *lst_syms = NULL;
  struct som_external_lst_symbol_record *current_lst_sym = NULL;
  bfd *current_archive_member_bfd = NULL;
  unsigned char *hash_table = NULL;
  struct som_external_som_entry *som_dictionary = NULL;
  struct som_external_lst_symbol_record **last_hash_entry_ptr_array = NULL;
  unsigned int current_som_file_offset = 0;
  unsigned int som_index = 0;
  size_t required_allocation_size;
  unsigned int module_count = 0;
  unsigned int hash_table_size = 0;
  bool operation_success = false;

  hash_table_size = bfd_getb32 (lst.hash_size);
  module_count = bfd_getb32 (lst.module_count);

  if (hash_table_size > 0)
    {
      if (_bfd_mul_overflow (hash_table_size, 4, &required_allocation_size))
        {
          bfd_set_error (bfd_error_no_memory);
          goto cleanup;
        }
      hash_table = bfd_zmalloc (required_allocation_size);
      if (hash_table == NULL)
        {
          bfd_set_error (bfd_error_no_memory);
          goto cleanup;
        }
    }

  if (module_count > 0)
    {
      if (_bfd_mul_overflow (module_count, sizeof (struct som_external_som_entry), &required_allocation_size))
        {
          bfd_set_error (bfd_error_no_memory);
          goto cleanup;
        }
      som_dictionary = bfd_zmalloc (required_allocation_size);
      if (som_dictionary == NULL)
        {
          bfd_set_error (bfd_error_no_memory);
          goto cleanup;
        }
    }

  if (hash_table_size > 0)
    {
      if (_bfd_mul_overflow (hash_table_size, sizeof (struct som_external_lst_symbol_record *), &required_allocation_size))
        {
          bfd_set_error (bfd_error_no_memory);
          goto cleanup;
        }
      last_hash_entry_ptr_array = bfd_zmalloc (required_allocation_size);
      if (last_hash_entry_ptr_array == NULL)
        {
          bfd_set_error (bfd_error_no_memory);
          goto cleanup;
        }
    }

  if (nsyms > 0)
    {
      if (_bfd_mul_overflow (nsyms, sizeof (struct som_external_lst_symbol_record), &required_allocation_size))
        {
          bfd_set_error (bfd_error_no_memory);
          goto cleanup;
        }
      lst_syms = bfd_malloc (required_allocation_size);
      if (lst_syms == NULL)
        {
          bfd_set_error (bfd_error_no_memory);
          goto cleanup;
        }
    }

  if (string_size > 0)
    {
      strings = bfd_malloc (string_size);
      if (strings == NULL)
        {
          bfd_set_error (bfd_error_no_memory);
          goto cleanup;
        }
      current_string_ptr = strings;
    }
  else
    {
      current_string_ptr = NULL;
    }

  current_lst_sym = lst_syms;

  current_som_file_offset = 8 + 2 * sizeof (struct ar_hdr) + bfd_getb32 (lst.file_end);

  if (elength)
    current_som_file_offset += elength;

  current_som_file_offset = (current_som_file_offset + 1U) & ~1U;

  size_t start_of_lst_syms_in_file = (size_t)sizeof(struct som_external_lst_header)
                                     + (size_t)hash_table_size * 4
                                     + (size_t)module_count * sizeof (struct som_external_som_entry);


  current_archive_member_bfd = abfd->archive_head;
  while (current_archive_member_bfd != NULL)
    {
      unsigned int member_symbol_count;
      som_symbol_type *symbol_iterator;

      if (current_archive_member_bfd->format != bfd_object
	  || current_archive_member_bfd->xvec->flavour != bfd_target_som_flavour)
	{
	  current_archive_member_bfd = current_archive_member_bfd->archive_next;
	  continue;
	}

      if (! som_slurp_symbol_table (current_archive_member_bfd))
	goto cleanup;

      symbol_iterator = obj_som_symtab (current_archive_member_bfd);
      member_symbol_count = bfd_get_symcount (current_archive_member_bfd);

      for (unsigned int i = 0; i < member_symbol_count; i++, symbol_iterator++)
	{
	  struct som_misc_symbol_info symbol_info;
	  unsigned int flags = 0;
	  const char *symbol_name_str = symbol_iterator->symbol.name;
	  size_t name_len;
	  size_t name_len_with_null;
	  size_t name_len_padded;
	  size_t remaining_string_buffer_space;
	  unsigned int symbol_hash_key;
          size_t current_symbol_record_file_offset;

          if (nsyms == 0 || current_lst_sym >= lst_syms + nsyms)
            {
              bfd_set_error (bfd_error_system_call);
              goto cleanup;
            }

	  som_bfd_derive_misc_symbol_info (current_archive_member_bfd, &symbol_iterator->symbol, &symbol_info);

	  if (symbol_info.symbol_type == ST_NULL
	      || symbol_info.symbol_type == ST_SYM_EXT
	      || symbol_info.symbol_type == ST_ARG_EXT)
	    continue;

	  if (symbol_info.symbol_scope != SS_UNIVERSAL
	      && symbol_info.symbol_type != ST_STORAGE)
	    continue;

	  if (bfd_is_und_section (symbol_iterator->symbol.section))
	    continue;

	  if (bfd_getb32 (som_dictionary[som_index].location) == 0)
	    {
	      bfd_putb32 (current_som_file_offset, som_dictionary[som_index].location);
	      bfd_putb32 (arelt_size (current_archive_member_bfd), som_dictionary[som_index].length);
	    }

	  symbol_hash_key = som_bfd_ar_symbol_hash (&symbol_iterator->symbol);

	  if (symbol_info.secondary_def)
	    flags |= LST_SYMBOL_SECONDARY_DEF;
	  flags |= symbol_info.symbol_type << LST_SYMBOL_SYMBOL_TYPE_SH;
	  flags |= symbol_info.symbol_scope << LST_SYMBOL_SYMBOL_SCOPE_SH;
	  if (bfd_is_com_section (symbol_iterator->symbol.section))
	    flags |= LST_SYMBOL_IS_COMMON;
	  if (symbol_info.dup_common)
	    flags |= LST_SYMBOL_DUP_COMMON;
	  flags |= 3 << LST_SYMBOL_XLEAST_SH;
	  flags |= symbol_info.arg_reloc << LST_SYMBOL_ARG_RELOC_SH;
	  bfd_putb32 (flags, current_lst_sym->flags);

          if (current_string_ptr != NULL)
            bfd_putb32 ((current_string_ptr - strings) + 4, current_lst_sym->name);
          else
            bfd_putb32 (0, current_lst_sym->name);

	  bfd_putb32 (0, current_lst_sym->qualifier_name);
	  bfd_putb32 (symbol_info.symbol_info, current_lst_sym->symbol_info);
	  bfd_putb32 (symbol_info.symbol_value | symbol_info.priv_level, current_lst_sym->symbol_value);
	  bfd_putb32 (0, current_lst_sym->symbol_descriptor);
	  current_lst_sym->reserved = 0;
	  bfd_putb32 (som_index, current_lst_sym->som_index);
	  bfd_putb32 (symbol_hash_key, current_lst_sym->symbol_key);
	  bfd_putb32 (0, current_lst_sym->next_entry);

          current_symbol_record_file_offset = start_of_lst_syms_in_file
                                            + (size_t)(current_lst_sym - lst_syms) * sizeof(struct som_external_lst_symbol_record);

	  struct som_external_lst_symbol_record *last_in_hash_chain = last_hash_entry_ptr_array[symbol_hash_key % hash_table_size];
	  if (last_in_hash_chain != NULL)
	    {
	      bfd_putb32 (current_symbol_record_file_offset, last_in_hash_chain->next_entry);
	    }
	  else
	    {
	      bfd_putb32 (current_symbol_record_file_offset, hash_table + 4 * (symbol_hash_key % hash_table_size));
	    }

	  last_hash_entry_ptr_array[symbol_hash_key % hash_table_size] = current_lst_sym;

          if (current_string_ptr == NULL)
            {
              bfd_set_error (bfd_error_no_memory);
              goto cleanup;
            }

	  name_len = strlen (symbol_name_str);
	  name_len_with_null = name_len + 1;
	  name_len_padded = (name_len_with_null + 3) & ~3U;

          remaining_string_buffer_space = string_size - (current_string_ptr - strings);

          if (name_len_with_null + 4 > remaining_string_buffer_space)
            {
              bfd_set_error (bfd_error_no_memory);
              goto cleanup;
            }
          if (name_len_padded + 4 > remaining_string_buffer_space)
            {
              bfd_set_error (bfd_error_no_memory);
              goto cleanup;
            }

	  bfd_put_32 (abfd, name_len, current_string_ptr);
	  current_string_ptr += 4;
	  memcpy (current_string_ptr, symbol_name_str, name_len_with_null);
	  current_string_ptr += name_len_with_null;
	  
	  while ((current_string_ptr - strings) % 4 != 0)
	    {
	      bfd_put_8 (abfd, 0, current_string_ptr);
	      current_string_ptr++;
	    }
	  
	  current_lst_sym++;
	}

      current_som_file_offset += arelt_size (current_archive_member_bfd) + sizeof (struct ar_hdr);
      current_som_file_offset = (current_som_file_offset + 1U) & ~1U;
      current_archive_member_bfd = current_archive_member_bfd->archive_next;
      som_index++;
    }

  required_allocation_size = (size_t) hash_table_size * 4;
  if (required_allocation_size > 0 && bfd_write (hash_table, required_allocation_size, abfd) != required_allocation_size)
    {
      bfd_set_error (bfd_error_system_call);
      goto cleanup;
    }

  required_allocation_size = (size_t) module_count * sizeof (struct som_external_som_entry);
  if (required_allocation_size > 0 && bfd_write (som_dictionary, required_allocation_size, abfd) != required_allocation_size)
    {
      bfd_set_error (bfd_error_system_call);
      goto cleanup;
    }

  required_allocation_size = (size_t) nsyms * sizeof (struct som_external_lst_symbol_record);
  if (required_allocation_size > 0 && bfd_write (lst_syms, required_allocation_size, abfd) != required_allocation_size)
    {
      bfd_set_error (bfd_error_system_call);
      goto cleanup;
    }

  if (string_size > 0 && bfd_write (strings, string_size, abfd) != string_size)
    {
      bfd_set_error (bfd_error_system_call);
      goto cleanup;
    }

  operation_success = true;

cleanup:
  free (hash_table);
  free (som_dictionary);
  free (last_hash_entry_ptr_array);
  free (lst_syms);
  free (strings);
  return operation_success;
}

/* Write out the LST for the archive.

   You'll never believe this is really how armaps are handled in SOM...  */

static bool
som_write_armap (bfd *abfd,
		 unsigned int elength,
		 struct orl *map ATTRIBUTE_UNUSED,
		 unsigned int orl_count ATTRIBUTE_UNUSED,
		 int stridx ATTRIBUTE_UNUSED)
{
  struct stat statbuf;
  struct som_external_lst_header lst = {0};
  struct ar_hdr hdr = {0};

  size_t header_size;
  size_t hash_table_size;
  size_t dir_table_size;
  size_t symbol_records_size;
  size_t string_table_size;
  size_t total_lst_size;
  size_t bytes_written;

  unsigned int nsyms = 0;
  unsigned int stringsize = 0;
  unsigned int module_count = 0;
  unsigned int csum = 0;
  unsigned int i;

  if (stat (bfd_get_filename (abfd), &statbuf) != 0)
    {
      bfd_set_error (bfd_error_system_call);
      return false;
    }
  bfd_ardata (abfd)->armap_timestamp = statbuf.st_mtime + 60;

  header_size = sizeof(struct som_external_lst_header);
  hash_table_size = (size_t)4 * SOM_LST_HASH_SIZE;

  bfd *curr_bfd = abfd->archive_head;
  while (curr_bfd != NULL)
    {
      if (curr_bfd->format == bfd_object && curr_bfd->xvec->flavour == bfd_target_som_flavour)
        module_count++;
      curr_bfd = curr_bfd->archive_next;
    }
  dir_table_size = sizeof(struct som_external_som_entry) * module_count;

  if (!som_bfd_prep_for_ar_write (abfd, &nsyms, &stringsize))
    {
      return false;
    }
  symbol_records_size = sizeof(struct som_external_lst_symbol_record) * nsyms;
  string_table_size = stringsize;

  bfd_putb16 (CPU_PA_RISC1_0, &lst.system_id);
  bfd_putb16 (LIBMAGIC, &lst.a_magic);
  bfd_putb32 (VERSION_ID, &lst.version_id);
  bfd_putb32 (0, &lst.file_time.secs);
  bfd_putb32 (0, &lst.file_time.nanosecs);

  bfd_putb32 (header_size, &lst.hash_loc);
  bfd_putb32 (SOM_LST_HASH_SIZE, &lst.hash_size);

  bfd_putb32 (header_size + hash_table_size, &lst.dir_loc);
  bfd_putb32 (module_count, &lst.module_count);
  bfd_putb32 (module_count, &lst.module_limit);

  bfd_putb32 (0, &lst.export_loc);
  bfd_putb32 (0, &lst.export_count);
  bfd_putb32 (0, &lst.import_loc);
  bfd_putb32 (0, &lst.aux_loc);
  bfd_putb32 (0, &lst.aux_size);

  bfd_putb32 (header_size + hash_table_size + dir_table_size + symbol_records_size, &lst.string_loc);
  bfd_putb32 (string_table_size, &lst.string_size);

  bfd_putb32 (0, &lst.free_list);

  total_lst_size = header_size + hash_table_size + dir_table_size + symbol_records_size + string_table_size;
  bfd_putb32 (total_lst_size, &lst.file_end);

  unsigned char *p = (unsigned char *) &lst;
  for (i = 0; i < sizeof(struct som_external_lst_header) - sizeof(lst.checksum); i += 4)
    csum ^= bfd_getb32 (&p[i]);
  bfd_putb32 (csum, &lst.checksum);

  snprintf (hdr.ar_name, sizeof(hdr.ar_name), "/              ");
  _bfd_ar_spacepad (hdr.ar_date, sizeof (hdr.ar_date), "%-12ld",
                    bfd_ardata (abfd)->armap_timestamp);
  _bfd_ar_spacepad (hdr.ar_uid, sizeof (hdr.ar_uid), "%ld",
                    (long)statbuf.st_uid);
  _bfd_ar_spacepad (hdr.ar_gid, sizeof (hdr.ar_gid), "%ld",
                    (long)statbuf.st_gid);
  _bfd_ar_spacepad (hdr.ar_mode, sizeof (hdr.ar_mode), "%-8o",
                    (unsigned int)statbuf.st_mode);
  _bfd_ar_spacepad (hdr.ar_size, sizeof (hdr.ar_size), "%-10ld",
                    (long)total_lst_size);
  hdr.ar_fmag[0] = '`';
  hdr.ar_fmag[1] = '\012';

  for (i = 0; i < sizeof (struct ar_hdr); i++)
    if (((char *) &hdr)[i] == '\0')
      ((char *) &hdr)[i] = ' ';

  bytes_written = bfd_write (&hdr, sizeof(struct ar_hdr), abfd);
  if (bytes_written != sizeof(struct ar_hdr))
    {
      return false;
    }

  bytes_written = bfd_write (&lst, sizeof(struct som_external_lst_header), abfd);
  if (bytes_written != sizeof(struct som_external_lst_header))
    {
      return false;
    }

  if (!som_bfd_ar_write_symbol_stuff (abfd, nsyms, stringsize, lst, elength))
    {
      return false;
    }

  return true;
}

/* Throw away some malloc'd information for this BFD.  */

static bool
som_bfd_free_cached_info (bfd *abfd)
{
  if (abfd == NULL)
    {
      return true;
    }

  bfd_format format = bfd_get_format (abfd);

  if (format == bfd_object || format == bfd_core)
    {
      void *symtab_ptr = obj_som_symtab(abfd);
      if (symtab_ptr != NULL)
        {
          free (symtab_ptr);
          obj_som_symtab(abfd) = NULL;
        }

      void *stringtab_ptr = obj_som_stringtab(abfd);
      if (stringtab_ptr != NULL)
        {
          free (stringtab_ptr);
          obj_som_stringtab(abfd) = NULL;
        }

      for (asection *o = abfd->sections; o != NULL; o = o->next)
        {
          struct som_section_data_struct *section_private_data = som_section_data(o);
          if (section_private_data != NULL)
            {
              void *reloc_stream_ptr = section_private_data->reloc_stream;
              if (reloc_stream_ptr != NULL)
                {
                  free (reloc_stream_ptr);
                  section_private_data->reloc_stream = NULL;
                }
            }
          o->reloc_count = (unsigned int) -1;
        }
    }

  return true;
}

/* End of miscellaneous support functions.  */

/* Linker support functions.  */

static bool
som_bfd_link_split_section (bfd *abfd ATTRIBUTE_UNUSED, asection *sec)
{
  const unsigned long MIN_SPLIT_SECTION_SIZE = 240000UL;
  return som_is_subspace (sec) && sec->size > MIN_SPLIT_SECTION_SIZE;
}

#define som_find_line				_bfd_nosymbols_find_line
#define som_get_symbol_version_string		_bfd_nosymbols_get_symbol_version_string
#define som_close_and_cleanup			_bfd_generic_close_and_cleanup
#define som_read_ar_hdr				_bfd_generic_read_ar_hdr
#define som_write_ar_hdr			_bfd_generic_write_ar_hdr
#define som_openr_next_archived_file		bfd_generic_openr_next_archived_file
#define som_get_elt_at_index			_bfd_generic_get_elt_at_index
#define som_generic_stat_arch_elt		bfd_generic_stat_arch_elt
#define som_truncate_arname			bfd_bsd_truncate_arname
#define som_slurp_extended_name_table		_bfd_slurp_extended_name_table
#define som_construct_extended_name_table	_bfd_archive_coff_construct_extended_name_table
#define som_update_armap_timestamp		_bfd_bool_bfd_true
#define som_bfd_is_target_special_symbol        _bfd_bool_bfd_asymbol_false
#define som_get_lineno				_bfd_nosymbols_get_lineno
#define som_bfd_make_debug_symbol		_bfd_nosymbols_bfd_make_debug_symbol
#define som_read_minisymbols			_bfd_generic_read_minisymbols
#define som_minisymbol_to_symbol		_bfd_generic_minisymbol_to_symbol
#define som_bfd_get_relocated_section_contents	bfd_generic_get_relocated_section_contents
#define som_bfd_relax_section			bfd_generic_relax_section
#define som_bfd_link_hash_table_create		_bfd_generic_link_hash_table_create
#define som_bfd_link_add_symbols		_bfd_generic_link_add_symbols
#define som_bfd_link_just_syms			_bfd_generic_link_just_syms
#define som_bfd_copy_link_hash_symbol_type \
  _bfd_generic_copy_link_hash_symbol_type
#define som_bfd_final_link			_bfd_generic_final_link
#define som_bfd_gc_sections			bfd_generic_gc_sections
#define som_bfd_lookup_section_flags		bfd_generic_lookup_section_flags
#define som_bfd_merge_sections			bfd_generic_merge_sections
#define som_bfd_is_group_section		bfd_generic_is_group_section
#define som_bfd_group_name			bfd_generic_group_name
#define som_bfd_discard_group			bfd_generic_discard_group
#define som_section_already_linked		_bfd_generic_section_already_linked
#define som_bfd_define_common_symbol		bfd_generic_define_common_symbol
#define som_bfd_link_hide_symbol		_bfd_generic_link_hide_symbol
#define som_bfd_define_start_stop		bfd_generic_define_start_stop
#define som_bfd_merge_private_bfd_data		_bfd_generic_bfd_merge_private_bfd_data
#define som_bfd_copy_private_header_data	_bfd_generic_bfd_copy_private_header_data
#define som_bfd_set_private_flags		_bfd_generic_bfd_set_private_flags
#define som_find_inliner_info			_bfd_nosymbols_find_inliner_info
#define som_bfd_link_check_relocs		_bfd_generic_link_check_relocs
#define som_set_reloc				_bfd_generic_set_reloc

const bfd_target hppa_som_vec =
{
  "som",			/* Name.  */
  bfd_target_som_flavour,
  BFD_ENDIAN_BIG,		/* Target byte order.  */
  BFD_ENDIAN_BIG,		/* Target headers byte order.  */
  (HAS_RELOC | EXEC_P |		/* Object flags.  */
   HAS_LINENO | HAS_DEBUG |
   HAS_SYMS | HAS_LOCALS | WP_TEXT | D_PAGED | DYNAMIC),
  (SEC_CODE | SEC_DATA | SEC_ROM | SEC_HAS_CONTENTS | SEC_LINK_ONCE
   | SEC_ALLOC | SEC_LOAD | SEC_RELOC),		/* Section flags.  */

  /* Leading_symbol_char: is the first char of a user symbol
     predictable, and if so what is it.  */
  0,
  '/',				/* AR_pad_char.  */
  14,				/* AR_max_namelen.  */
  0,				/* match priority.  */
  TARGET_KEEP_UNUSED_SECTION_SYMBOLS, /* keep unused section symbols.  */
  bfd_getb64, bfd_getb_signed_64, bfd_putb64,
  bfd_getb32, bfd_getb_signed_32, bfd_putb32,
  bfd_getb16, bfd_getb_signed_16, bfd_putb16,	/* Data.  */
  bfd_getb64, bfd_getb_signed_64, bfd_putb64,
  bfd_getb32, bfd_getb_signed_32, bfd_putb32,
  bfd_getb16, bfd_getb_signed_16, bfd_putb16,	/* Headers.  */
  {_bfd_dummy_target,
   som_object_p,		/* bfd_check_format.  */
   bfd_generic_archive_p,
   _bfd_dummy_target
  },
  {
    _bfd_bool_bfd_false_error,
    som_mkobject,
    _bfd_generic_mkarchive,
    _bfd_bool_bfd_false_error
  },
  {
    _bfd_bool_bfd_false_error,
    som_write_object_contents,
    _bfd_write_archive_contents,
    _bfd_bool_bfd_false_error,
  },
#undef som

  BFD_JUMP_TABLE_GENERIC (som),
  BFD_JUMP_TABLE_COPY (som),
  BFD_JUMP_TABLE_CORE (_bfd_nocore),
  BFD_JUMP_TABLE_ARCHIVE (som),
  BFD_JUMP_TABLE_SYMBOLS (som),
  BFD_JUMP_TABLE_RELOCS (som),
  BFD_JUMP_TABLE_WRITE (som),
  BFD_JUMP_TABLE_LINK (som),
  BFD_JUMP_TABLE_DYNAMIC (_bfd_nodynamic),

  NULL,

  NULL
};

