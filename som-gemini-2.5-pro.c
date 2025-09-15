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
  for (int i = 0; i < 4; ++i)
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
  if (!queue)
    {
      return;
    }

  for (unsigned int i = 3; i > 0; i--)
    {
      queue[i] = queue[i - 1];
    }

  queue[0].reloc = p;
  queue[0].size = size;
}

/* When an entry in the relocation queue is reused, the entry moves
   to the front of the queue.  */

#include <stdlib.h>

struct reloc_queue
{
  unsigned char *reloc;
  unsigned int size;
};

static void
som_reloc_queue_fix (struct reloc_queue *queue, unsigned int idx)
{
  if (idx == 0)
    {
      return;
    }

  if (idx > 3)
    {
      abort ();
    }

  struct reloc_queue last = queue[idx];

  for (unsigned int i = idx; i > 0; --i)
    {
      queue[i] = queue[i - 1];
    }

  queue[0] = last;
}

/* Search for a particular relocation in the relocation queue.  */

static int
som_reloc_queue_find (unsigned char *p,
		      unsigned int size,
		      struct reloc_queue *queue)
{
  for (int i = 0; i < 4; ++i)
    {
      if (queue[i].reloc != NULL
	  && size == queue[i].size
	  && memcmp (p, queue[i].reloc, size) == 0)
	{
	  return i;
	}
    }
  return -1;
}

static unsigned char *
try_prev_fixup (bfd *abfd ATTRIBUTE_UNUSED,
		unsigned int *subspace_reloc_sizep,
		unsigned char *p,
		unsigned int size,
		struct reloc_queue *queue)
{
  if (!p || !subspace_reloc_sizep || !queue)
    {
      return p;
    }

  const int queue_index = som_reloc_queue_find (p, size, queue);

  if (queue_index != -1)
    {
      bfd_put_8 (abfd, R_PREV_FIXUP + queue_index, p);
      p += 1;
      *subspace_reloc_sizep += 1;
      som_reloc_queue_fix (queue, queue_index);
    }
  else
    {
      som_reloc_queue_insert (p, size, queue);
      *subspace_reloc_sizep += size;
      p += size;
    }
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
  if (skip >= 0x1000000)
    {
      skip -= 0x1000000;
      bfd_put_8 (abfd, R_NO_RELOCATION + 31, p);
      bfd_put_8 (abfd, 0xff, p + 1);
      bfd_put_16 (abfd, (bfd_vma) 0xffff, p + 2);
      p = try_prev_fixup (abfd, subspace_reloc_sizep, p, 4, queue);

      while (skip >= 0x1000000)
	{
	  skip -= 0x1000000;
	  bfd_put_8 (abfd, R_PREV_FIXUP, p);
	  p++;
	  *subspace_reloc_sizep += 1;
	}
    }

  if (skip == 0)
    {
      return p;
    }

  if ((skip & 3) == 0 && skip <= 0xc0000)
    {
      const unsigned int val = (skip >> 2) - 1;
      if (skip <= 0x60)
	{
	  bfd_put_8 (abfd, R_NO_RELOCATION + val, p);
	  *subspace_reloc_sizep += 1;
	  p++;
	}
      else if (skip <= 0x1000)
	{
	  bfd_put_8 (abfd, R_NO_RELOCATION + 24 + (val >> 8), p);
	  bfd_put_8 (abfd, val, p + 1);
	  p = try_prev_fixup (abfd, subspace_reloc_sizep, p, 2, queue);
	}
      else
	{
	  bfd_put_8 (abfd, R_NO_RELOCATION + 28 + (val >> 16), p);
	  bfd_put_16 (abfd, (bfd_vma) val, p + 1);
	  p = try_prev_fixup (abfd, subspace_reloc_sizep, p, 3, queue);
	}
    }
  else
    {
      const bfd_vma val = skip - 1;
      bfd_put_8 (abfd, R_NO_RELOCATION + 31, p);
      bfd_put_8 (abfd, val >> 16, p + 1);
      bfd_put_16 (abfd, val, p + 2);
      p = try_prev_fixup (abfd, subspace_reloc_sizep, p, 4, queue);
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
  unsigned int override_code;
  unsigned int total_size;

  if (addend + 0x80 < 0x100)
    {
      override_code = 1;
    }
  else if (addend + 0x8000 < 0x10000)
    {
      override_code = 2;
    }
  else if (addend + 0x800000 < 0x1000000)
    {
      override_code = 3;
    }
  else
    {
      override_code = 4;
    }

  total_size = override_code + 1;
  bfd_put_8 (abfd, R_DATA_OVERRIDE + override_code, p);

  switch (override_code)
    {
    case 1:
      bfd_put_8 (abfd, addend, p + 1);
      break;
    case 2:
      bfd_put_16 (abfd, addend, p + 1);
      break;
    case 3:
      bfd_put_8 (abfd, addend >> 16, p + 1);
      bfd_put_16 (abfd, addend, p + 2);
      break;
    case 4:
      bfd_put_32 (abfd, addend, p + 1);
      break;
    }

  return try_prev_fixup (abfd, subspace_reloc_sizep, p, total_size, queue);
}

/* Handle a single function call relocation.  */

static const int SIMPLE_SYM_NUM_LIMIT = 0x100;
static const int RTN_BITS_MASK = 0x3;
static const int RETURN_VALUE_RELOC_OFFSET = 5;

static const int SIMPLE_ARG_RELOC_MASK = ~1;
static const int SIMPLE_ARG_RELOC_0_ARGS = 0;
static const int SIMPLE_ARG_RELOC_1_ARG = 1 << 8;
static const int SIMPLE_ARG_RELOC_2_ARGS = (1 << 8) | (1 << 6);
static const int SIMPLE_ARG_RELOC_3_ARGS = (1 << 8) | (1 << 6) | (1 << 4);
static const int SIMPLE_ARG_RELOC_4_ARGS = (1 << 8) | (1 << 6) | (1 << 4) | (1 << 2);

static const int HARD_RELOC_SPECIAL_CASE_CHECK = 0xe;
static const int HARD_RELOC_SPECIAL_CASE_VAL_1 = 9;
static const int HARD_RELOC_SPECIAL_CASE_VAL_2 = 4;
static const int HARD_RELOC_FACTOR_1 = 40;
static const int HARD_RELOC_FACTOR_2 = 3;

static const int HARD_RELOC_TYPE_BASE = 10;
static const int HARD_RELOC_TYPE_SYM_NUM_FLAG = 2;

static int
get_simple_reloc_type (int arg_bits)
{
  int type;
  switch (arg_bits & SIMPLE_ARG_RELOC_MASK)
    {
    case SIMPLE_ARG_RELOC_0_ARGS:
      type = 0;
      break;
    case SIMPLE_ARG_RELOC_1_ARG:
      type = 1;
      break;
    case SIMPLE_ARG_RELOC_2_ARGS:
      type = 2;
      break;
    case SIMPLE_ARG_RELOC_3_ARGS:
      type = 3;
      break;
    case SIMPLE_ARG_RELOC_4_ARGS:
      type = 4;
      break;
    default:
      return -1;
    }

  if (arg_bits & RTN_BITS_MASK)
    {
      type += RETURN_VALUE_RELOC_OFFSET;
    }
  return type;
}

static int
calculate_hard_reloc_type (int arg_bits, int rtn_bits)
{
  int type = rtn_bits;

  if (((arg_bits >> 6) & 0xf) == HARD_RELOC_SPECIAL_CASE_CHECK)
    {
      type += HARD_RELOC_SPECIAL_CASE_VAL_1 * HARD_RELOC_FACTOR_1;
    }
  else
    {
      int bits9_8 = (arg_bits >> 8) & 3;
      int bits7_6 = (arg_bits >> 6) & 3;
      type += (HARD_RELOC_FACTOR_2 * bits9_8 + bits7_6) * HARD_RELOC_FACTOR_1;
    }

  if (((arg_bits >> 2) & 0xf) == HARD_RELOC_SPECIAL_CASE_CHECK)
    {
      type += HARD_RELOC_SPECIAL_CASE_VAL_1 * HARD_RELOC_SPECIAL_CASE_VAL_2;
    }
  else
    {
      int bits5_4 = (arg_bits >> 4) & 3;
      int bits3_2 = (arg_bits >> 2) & 3;
      type += (HARD_RELOC_FACTOR_2 * bits5_4 + bits3_2) * HARD_RELOC_SPECIAL_CASE_VAL_2;
    }

  return type;
}

static unsigned char *
som_reloc_call (bfd *abfd,
		unsigned char *p,
		unsigned int *subspace_reloc_sizep,
		arelent *bfd_reloc,
		int sym_num,
		struct reloc_queue *queue)
{
  int arg_bits = HPPA_R_ARG_RELOC (bfd_reloc->addend);

  if (sym_num < SIMPLE_SYM_NUM_LIMIT)
    {
      int type = get_simple_reloc_type (arg_bits);
      if (type != -1)
	{
	  bfd_put_8 (abfd, bfd_reloc->howto->type + type, p);
	  bfd_put_8 (abfd, sym_num, p + 1);
	  return try_prev_fixup (abfd, subspace_reloc_sizep, p, 2, queue);
	}
    }

  int rtn_bits = arg_bits & RTN_BITS_MASK;
  int type = calculate_hard_reloc_type (arg_bits, rtn_bits);
  int is_large_sym = (sym_num >= SIMPLE_SYM_NUM_LIMIT);
  int is_large_type = (type >= 0x100);

  bfd_put_8 (abfd, bfd_reloc->howto->type + HARD_RELOC_TYPE_BASE
	     + HARD_RELOC_TYPE_SYM_NUM_FLAG * is_large_sym + is_large_type,
	     p);
  bfd_put_8 (abfd, type, p + 1);

  if (!is_large_sym)
    {
      bfd_put_8 (abfd, sym_num, p + 2);
      return try_prev_fixup (abfd, subspace_reloc_sizep, p, 3, queue);
    }
  else
    {
      bfd_put_8 (abfd, sym_num >> 16, p + 2);
      bfd_put_16 (abfd, (bfd_vma) sym_num, p + 3);
      return try_prev_fixup (abfd, subspace_reloc_sizep, p, 5, queue);
    }
}

/* Return the logarithm of X, base 2, considering X unsigned,
   if X is a power of 2.  Otherwise, returns -1.  */

static int
exact_log2(unsigned int x)
{
  if (__builtin_popcount(x) != 1)
    {
      return -1;
    }
  return __builtin_ctz(x);
}

static bfd_reloc_status_type
hppa_som_reloc (bfd *abfd ATTRIBUTE_UNUSED,
                arelent *reloc_entry,
                asymbol *symbol_in ATTRIBUTE_UNUSED,
                void *data ATTRIBUTE_UNUSED,
                const asection *input_section,
                const bfd *output_bfd,
                char **error_message ATTRIBUTE_UNUSED)
{
  if (output_bfd != NULL)
    {
      reloc_entry->address += input_section->output_offset;
    }

  return bfd_reloc_ok;
}

/* Given a generic HPPA relocation type, the instruction format,
   and a field selector, return one or more appropriate SOM relocations.  */

static int *
alloc_reloc (bfd *abfd)
{
  return bfd_alloc (abfd, (bfd_size_type) sizeof (int));
}

static bool
handle_sym_diff (bfd *abfd,
                 int **final_types,
                 int *final_type,
                 int format,
                 enum hppa_reloc_field_selector_type_alt field)
{
  final_types[0] = alloc_reloc (abfd);
  final_types[1] = alloc_reloc (abfd);
  final_types[2] = alloc_reloc (abfd);
  final_types[3] = alloc_reloc (abfd);

  if (!final_types[0] || !final_types[1] || !final_types[2] || !final_types[3])
    return false;

  switch (field)
    {
    case e_fsel:
      *final_types[0] = R_FSEL;
      break;
    case e_rsel:
      *final_types[0] = R_RSEL;
      break;
    case e_lsel:
      *final_types[0] = R_LSEL;
      break;
    default:
      break;
    }

  *final_types[1] = R_COMP2;
  *final_types[2] = R_COMP2;
  *final_types[3] = R_COMP1;
  final_types[4] = final_type;
  *final_types[4] = (format == 32) ? R_DATA_EXPR : R_CODE_EXPR;
  final_types[5] = NULL;

  return true;
}

int **
hppa_som_gen_reloc_type (bfd *abfd,
			 int base_type,
			 int format,
			 enum hppa_reloc_field_selector_type_alt field,
			 int sym_diff,
			 asymbol *sym)
{
  int **final_types = bfd_alloc (abfd, (bfd_size_type) sizeof (int *) * 6);
  int *final_type = alloc_reloc (abfd);

  if (!final_types || !final_type)
    return NULL;

  *final_type = base_type;

  switch (field)
    {
    case e_fsel:
    case e_psel:
    case e_lpsel:
    case e_rpsel:
      final_types[0] = final_type;
      final_types[1] = NULL;
      final_types[2] = NULL;
      break;

    case e_nlsel:
    case e_nlrsel:
      final_types[0] = alloc_reloc (abfd);
      final_types[1] = alloc_reloc (abfd);
      if (!final_types[0] || !final_types[1])
	return NULL;
      *final_types[0] = R_N0SEL;
      *final_types[1] = (field == e_nlsel) ? R_N_MODE : R_R_MODE;
      final_types[2] = final_type;
      final_types[3] = NULL;
      break;

    case e_ltpsel:
    case e_rtpsel:
      abort ();

    default:
      {
	int first_reloc_val;
	final_types[0] = alloc_reloc (abfd);
	if (!final_types[0])
	  return NULL;

	switch (field)
	  {
	  case e_tsel:
	    first_reloc_val = R_FSEL;
	    break;
	  case e_ltsel:
	    first_reloc_val = R_LSEL;
	    break;
	  case e_rtsel:
	    first_reloc_val = R_RSEL;
	    break;
	  case e_lssel:
	  case e_rssel:
	    first_reloc_val = R_S_MODE;
	    break;
	  case e_lsel:
	  case e_rsel:
	    first_reloc_val = R_N_MODE;
	    break;
	  case e_ldsel:
	  case e_rdsel:
	    first_reloc_val = R_D_MODE;
	    break;
	  case e_lrsel:
	  case e_rrsel:
	    first_reloc_val = R_R_MODE;
	    break;
	  case e_nsel:
	    first_reloc_val = R_N1SEL;
	    break;
	  default:
	    abort ();
	  }

	*final_types[0] = first_reloc_val;
	final_types[1] = final_type;
	final_types[2] = NULL;
	break;
      }
    }

  switch (base_type)
    {
    case R_HPPA:
    case R_HPPA_COMPLEX:
      if (sym_diff)
	{
	  if (!handle_sym_diff (abfd, final_types, final_type, format, field))
	    return NULL;
	  break;
	}

      if (base_type == R_HPPA_COMPLEX)
	break;

      if (field == e_psel || field == e_lpsel || field == e_rpsel)
	*final_type = (format == 32) ? R_DATA_PLABEL : R_CODE_PLABEL;
      else if (field == e_tsel || field == e_ltsel || field == e_rtsel)
	*final_type = R_DLT_REL;
      else if (format == 32)
	{
	  *final_type = R_DATA_ONE_SYMBOL;
	  if (som_symbol_data (sym)->som_type == SYMBOL_TYPE_UNKNOWN
	      && (sym->flags & (BSF_SECTION_SYM | BSF_FUNCTION)) == 0
	      && !bfd_is_com_section (sym->section))
	    som_symbol_data (sym)->som_type = SYMBOL_TYPE_DATA;
	}
      break;

    case R_HPPA_GOTOFF:
      if (field == e_psel || field == e_lpsel || field == e_rpsel)
	*final_type = R_DATA_PLABEL;
      else if (field == e_fsel && format == 32)
	*final_type = R_DATA_GPREL;
      break;

    case R_HPPA_PCREL_CALL:
#ifndef NO_PCREL_MODES
      final_types[0] = alloc_reloc (abfd);
      if (!final_types[0])
	return NULL;
      *final_types[0] = (format == 17) ? R_SHORT_PCREL_MODE : R_LONG_PCREL_MODE;
      final_types[1] = final_type;
      final_types[2] = NULL;
#endif
      break;

    case R_HPPA_NONE:
    case R_HPPA_ABS_CALL:
      break;
    }

  return final_types;
}

/* Return the address of the correct entry in the PA SOM relocation
   howto table.  */

static reloc_howto_type *
som_bfd_reloc_type_lookup (bfd *abfd ATTRIBUTE_UNUSED,
			   bfd_reloc_code_real_type code)
{
  const size_t howto_table_size = sizeof (som_hppa_howto_table) / sizeof (som_hppa_howto_table[0]);

  if (code >= 0 && (size_t) code < howto_table_size)
    {
      BFD_ASSERT ((int) som_hppa_howto_table[code].type == (int) code);
      return &som_hppa_howto_table[code];
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

  const size_t howto_count = sizeof (som_hppa_howto_table) / sizeof (som_hppa_howto_table[0]);
  for (size_t i = 0; i < howto_count; i++)
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
som_swap_clock_in (const struct som_external_clock *src,
		   struct som_clock *dst)
{
  if (src == NULL || dst == NULL)
    {
      return;
    }

  dst->secs = bfd_getb32 (src->secs);
  dst->nanosecs = bfd_getb32 (src->nanosecs);
}

static void
som_swap_clock_out (const struct som_clock *src,
		    struct som_external_clock *dst)
{
  if (src && dst)
    {
      bfd_putb32 (src->secs, dst->secs);
      bfd_putb32 (src->nanosecs, dst->nanosecs);
    }
}

#include <assert.h>

static void
som_swap_b32_fields_in (struct som_header *dst,
			const struct som_external_header *src)
{
  dst->version_id = bfd_getb32 (src->version_id);
  dst->entry_space = bfd_getb32 (src->entry_space);
  dst->entry_subspace = bfd_getb32 (src->entry_subspace);
  dst->entry_offset = bfd_getb32 (src->entry_offset);
  dst->aux_header_location = bfd_getb32 (src->aux_header_location);
  dst->aux_header_size = bfd_getb32 (src->aux_header_size);
  dst->som_length = bfd_getb32 (src->som_length);
  dst->presumed_dp = bfd_getb32 (src->presumed_dp);
  dst->space_location = bfd_getb32 (src->space_location);
  dst->space_total = bfd_getb32 (src->space_total);
  dst->subspace_location = bfd_getb32 (src->subspace_location);
  dst->subspace_total = bfd_getb32 (src->subspace_total);
  dst->loader_fixup_location = bfd_getb32 (src->loader_fixup_location);
  dst->loader_fixup_total = bfd_getb32 (src->loader_fixup_total);
  dst->space_strings_location = bfd_getb32 (src->space_strings_location);
  dst->space_strings_size = bfd_getb32 (src->space_strings_size);
  dst->init_array_location = bfd_getb32 (src->init_array_location);
  dst->init_array_total = bfd_getb32 (src->init_array_total);
  dst->compiler_location = bfd_getb32 (src->compiler_location);
  dst->compiler_total = bfd_getb32 (src->compiler_total);
  dst->symbol_location = bfd_getb32 (src->symbol_location);
  dst->symbol_total = bfd_getb32 (src->symbol_total);
  dst->fixup_request_location = bfd_getb32 (src->fixup_request_location);
  dst->fixup_request_total = bfd_getb32 (src->fixup_request_total);
  dst->symbol_strings_location = bfd_getb32 (src->symbol_strings_location);
  dst->symbol_strings_size = bfd_getb32 (src->symbol_strings_size);
  dst->unloadable_sp_location = bfd_getb32 (src->unloadable_sp_location);
  dst->unloadable_sp_size = bfd_getb32 (src->unloadable_sp_size);
  dst->checksum = bfd_getb32 (src->checksum);
}

static void
som_swap_header_in (const struct som_external_header *src,
		    struct som_header *dst)
{
  assert (src != NULL && dst != NULL);

  dst->system_id = bfd_getb16 (src->system_id);
  dst->a_magic = bfd_getb16 (src->a_magic);

  som_swap_clock_in (&src->file_time, &dst->file_time);

  som_swap_b32_fields_in (dst, src);
}

static void
som_swap_all_b32 (const struct som_header *src,
		  struct som_external_header *dst)
{
  bfd_putb32 (src->version_id, dst->version_id);
  bfd_putb32 (src->entry_space, dst->entry_space);
  bfd_putb32 (src->entry_subspace, dst->entry_subspace);
  bfd_putb32 (src->entry_offset, dst->entry_offset);
  bfd_putb32 (src->aux_header_location, dst->aux_header_location);
  bfd_putb32 (src->aux_header_size, dst->aux_header_size);
  bfd_putb32 (src->som_length, dst->som_length);
  bfd_putb32 (src->presumed_dp, dst->presumed_dp);
  bfd_putb32 (src->space_location, dst->space_location);
  bfd_putb32 (src->space_total, dst->space_total);
  bfd_putb32 (src->subspace_location, dst->subspace_location);
  bfd_putb32 (src->subspace_total, dst->subspace_total);
  bfd_putb32 (src->loader_fixup_location, dst->loader_fixup_location);
  bfd_putb32 (src->loader_fixup_total, dst->loader_fixup_total);
  bfd_putb32 (src->space_strings_location, dst->space_strings_location);
  bfd_putb32 (src->space_strings_size, dst->space_strings_size);
  bfd_putb32 (src->init_array_location, dst->init_array_location);
  bfd_putb32 (src->init_array_total, dst->init_array_total);
  bfd_putb32 (src->compiler_location, dst->compiler_location);
  bfd_putb32 (src->compiler_total, dst->compiler_total);
  bfd_putb32 (src->symbol_location, dst->symbol_location);
  bfd_putb32 (src->symbol_total, dst->symbol_total);
  bfd_putb32 (src->fixup_request_location, dst->fixup_request_location);
  bfd_putb32 (src->fixup_request_total, dst->fixup_request_total);
  bfd_putb32 (src->symbol_strings_location, dst->symbol_strings_location);
  bfd_putb32 (src->symbol_strings_size, dst->symbol_strings_size);
  bfd_putb32 (src->unloadable_sp_location, dst->unloadable_sp_location);
  bfd_putb32 (src->unloadable_sp_size, dst->unloadable_sp_size);
  bfd_putb32 (src->checksum, dst->checksum);
}

static void
som_swap_header_out (const struct som_header *src,
		    struct som_external_header *dst)
{
  if (src == NULL || dst == NULL)
    {
      return;
    }

  bfd_putb16 (src->system_id, dst->system_id);
  bfd_putb16 (src->a_magic, dst->a_magic);
  som_swap_clock_out (&src->file_time, &dst->file_time);
  som_swap_all_b32 (src, dst);
}

static void
som_swap_space_dictionary_in (struct som_external_space_dictionary_record *src,
			      struct som_space_dictionary_record *dst)
{
  if (src == NULL || dst == NULL)
    {
      return;
    }

  const unsigned int flags = bfd_getb32 (src->flags);

  dst->name = bfd_getb32 (src->name);
  dst->space_number = bfd_getb32 (src->space_number);
  dst->subspace_index = bfd_getb32 (src->subspace_index);
  dst->subspace_quantity = bfd_getb32 (src->subspace_quantity);
  dst->loader_fix_index = bfd_getb32 (src->loader_fix_index);
  dst->loader_fix_quantity = bfd_getb32 (src->loader_fix_quantity);
  dst->init_pointer_index = bfd_getb32 (src->init_pointer_index);
  dst->init_pointer_quantity = bfd_getb32 (src->init_pointer_quantity);

  dst->is_loadable = (flags & SOM_SPACE_IS_LOADABLE) != 0;
  dst->is_defined = (flags & SOM_SPACE_IS_DEFINED) != 0;
  dst->is_private = (flags & SOM_SPACE_IS_PRIVATE) != 0;
  dst->has_intermediate_code = (flags & SOM_SPACE_HAS_INTERMEDIATE_CODE) != 0;
  dst->is_tspecific = (flags & SOM_SPACE_IS_TSPECIFIC) != 0;

  dst->sort_key = (flags >> SOM_SPACE_SORT_KEY_SH) & SOM_SPACE_SORT_KEY_MASK;

  dst->reserved = 0;
  dst->reserved2 = 0;
}

static void
som_swap_space_dictionary_out (struct som_space_dictionary_record *src,
			       struct som_external_space_dictionary_record *dst)
{
  bfd_putb32 (src->name, dst->name);

  const unsigned int flags =
    (src->is_loadable ? SOM_SPACE_IS_LOADABLE : 0)
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

static void
som_swap_subspace_dictionary_in
  (struct som_external_subspace_dictionary_record *src,
   struct som_subspace_dictionary_record *dst)
{
  if (!src || !dst)
    {
      return;
    }

  dst->space_index = bfd_getb32 (src->space_index);
  const unsigned int flags = bfd_getb32 (src->flags);
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
  unsigned int flags =
    ((src->access_control_bits & SOM_SUBSPACE_ACCESS_CONTROL_BITS_MASK)
     << SOM_SUBSPACE_ACCESS_CONTROL_BITS_SH)
    | (src->memory_resident ? SOM_SUBSPACE_MEMORY_RESIDENT : 0)
    | (src->dup_common ? SOM_SUBSPACE_DUP_COMMON : 0)
    | (src->is_common ? SOM_SUBSPACE_IS_COMMON : 0)
    | (src->is_loadable ? SOM_SUBSPACE_IS_LOADABLE : 0)
    | ((src->quadrant & SOM_SUBSPACE_QUADRANT_MASK) << SOM_SUBSPACE_QUADRANT_SH)
    | (src->initially_frozen ? SOM_SUBSPACE_INITIALLY_FROZEN : 0)
    | (src->is_first ? SOM_SUBSPACE_IS_FIRST : 0)
    | (src->code_only ? SOM_SUBSPACE_CODE_ONLY : 0)
    | ((src->sort_key & SOM_SUBSPACE_SORT_KEY_MASK) << SOM_SUBSPACE_SORT_KEY_SH)
    | (src->replicate_init ? SOM_SUBSPACE_REPLICATE_INIT : 0)
    | (src->continuation ? SOM_SUBSPACE_CONTINUATION : 0)
    | (src->is_tspecific ? SOM_SUBSPACE_IS_TSPECIFIC : 0)
    | (src->is_comdat ? SOM_SUBSPACE_IS_COMDAT : 0);

  bfd_putb32 (src->space_index, dst->space_index);
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
  if (!src || !dst)
    {
      return;
    }

  const unsigned int flags = bfd_getb32 (src->flags);

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
  const unsigned int flags =
    (src->mandatory ? SOM_AUX_ID_MANDATORY : 0U) |
    (src->copy      ? SOM_AUX_ID_COPY      : 0U) |
    (src->append    ? SOM_AUX_ID_APPEND    : 0U) |
    (src->ignore    ? SOM_AUX_ID_IGNORE    : 0U) |
    (((unsigned int) src->type & SOM_AUX_ID_TYPE_MASK) << SOM_AUX_ID_TYPE_SH);

  bfd_putb32 (flags, dst->flags);
  bfd_putb32 (src->length, dst->length);
}

static void
som_swap_string_auxhdr_out (const struct som_string_auxhdr *src,
			    struct som_external_string_auxhdr *dst)
{
  if (src == NULL || dst == NULL)
    {
      return;
    }

  som_swap_aux_id_out (&src->header_id, &dst->header_id);
  bfd_putb32 (src->string_length, dst->string_length);
}

static void
som_swap_compilation_unit_out (const struct som_compilation_unit *src,
			       struct som_external_compilation_unit *dst)
{
  if (src == NULL || dst == NULL)
    {
      return;
    }

  bfd_putb32 (src->name.strx, dst->name);
  bfd_putb32 (src->language_name.strx, dst->language_name);
  bfd_putb32 (src->product_id.strx, dst->product_id);
  bfd_putb32 (src->version_id.strx, dst->version_id);
  bfd_putb32 (src->flags, dst->flags);
  som_swap_clock_out (&src->compile_time, &dst->compile_time);
  som_swap_clock_out (&src->source_time, &dst->source_time);
}

static void
som_swap_exec_auxhdr_in(const struct som_external_exec_auxhdr *src,
                        struct som_exec_auxhdr *dst)
{
    if (src == NULL || dst == NULL) {
        return;
    }

    som_swap_aux_id_in(&src->som_auxhdr, &dst->som_auxhdr);
    dst->exec_tsize = bfd_getb32(src->exec_tsize);
    dst->exec_tmem = bfd_getb32(src->exec_tmem);
    dst->exec_tfile = bfd_getb32(src->exec_tfile);
    dst->exec_dsize = bfd_getb32(src->exec_dsize);
    dst->exec_dmem = bfd_getb32(src->exec_dmem);
    dst->exec_dfile = bfd_getb32(src->exec_dfile);
    dst->exec_bsize = bfd_getb32(src->exec_bsize);
    dst->exec_entry = bfd_getb32(src->exec_entry);
    dst->exec_flags = bfd_getb32(src->exec_flags);
    dst->exec_bfill = bfd_getb32(src->exec_bfill);
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

  const bfd_uint32_t *src_fields = &src->exec_tsize;
  unsigned char *dst_fields = (unsigned char *) &dst->exec_tsize;

  for (size_t i = 0; i < 10; ++i)
    {
      bfd_putb32 (src_fields[i], dst_fields + (i * sizeof (bfd_uint32_t)));
    }
}

static void
som_swap_lst_header_in (const struct som_external_lst_header *src,
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

static bfd_boolean
is_entry_in_code_section (bfd *abfd, bfd_vma entry)
{
  asection *section;

  for (section = abfd->sections; section; section = section->next)
    {
      if (((section->flags & SEC_CODE) != 0)
	  && (entry >= section->vma)
	  && (entry < section->vma + section->size))
	{
	  return TRUE;
	}
    }
  return FALSE;
}

static bfd_boolean
are_som_entry_and_flags_swapped (bfd *abfd,
				 const struct som_exec_auxhdr *aux_hdrp)
{
  bfd_boolean is_buggy_entry_zero;
  bfd_boolean is_entry_unaligned;
  bfd_boolean is_entry_in_code;
  bfd_vma entry;

  entry = aux_hdrp->exec_entry + aux_hdrp->exec_tmem;
  is_entry_in_code = is_entry_in_code_section (abfd, entry);

  is_buggy_entry_zero = (aux_hdrp->exec_entry == 0
			 && (abfd->flags & DYNAMIC) == 0);
  is_entry_unaligned = (aux_hdrp->exec_entry & 0x3) != 0;

  return is_buggy_entry_zero || is_entry_unaligned || !is_entry_in_code;
}

static bfd_cleanup
som_object_setup (bfd *abfd,
		  struct som_header *file_hdrp,
		  struct som_exec_auxhdr *aux_hdrp,
		  unsigned long current_offset)
{
  if (!som_mkobject (abfd))
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

  obj_som_exec_data (abfd) =
    bfd_zalloc (abfd, (bfd_size_type) sizeof (struct som_exec_data));
  if (obj_som_exec_data (abfd) == NULL)
    return NULL;

  if (aux_hdrp)
    {
      if (are_som_entry_and_flags_swapped (abfd, aux_hdrp))
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
  obj_som_str_filepos (abfd) =
    (file_hdrp->symbol_strings_location + current_offset);
  obj_som_reloc_filepos (abfd) =
    (file_hdrp->fixup_request_location + current_offset);
  obj_som_exec_data (abfd)->system_id = file_hdrp->system_id;

  return _bfd_no_cleanup;
}

/* Convert all of the space and subspace info into BFD sections.  Each space
   contains a number of subspaces, which in turn describe the mapping between
   regions of the exec file, and the address space that the program runs in.
   BFD sections which correspond to spaces will overlap the sections for the
   associated subspaces.  */

static asection *
create_section_from_name (bfd *abfd, const char *name)
{
  size_t len = strlen (name) + 1;
  char *newname = bfd_alloc (abfd, len);
  if (!newname)
    return NULL;
  memcpy (newname, name, len);
  return bfd_make_section_anyway (abfd, newname);
}

static void
set_subspace_flags (asection *subsect,
		    const struct som_subspace_dictionary_record *subspace)
{
  switch (subspace->access_control_bits >> 4)
    {
    case 0x0:
      subsect->flags |= SEC_DATA | SEC_READONLY;
      break;
    case 0x1:
      subsect->flags |= SEC_DATA;
      break;
    case 0x2:
    case 0x4:
    case 0x5:
    case 0x6:
    case 0x7:
      subsect->flags |= SEC_CODE | SEC_READONLY;
      break;
    case 0x3:
      subsect->flags |= SEC_CODE;
      break;
    }

  if (subspace->is_comdat || subspace->is_common || subspace->dup_common)
    subsect->flags |= SEC_LINK_ONCE;
  if (subspace->subspace_length > 0)
    subsect->flags |= SEC_HAS_CONTENTS;
  if (subspace->is_loadable)
    subsect->flags |= SEC_ALLOC | SEC_LOAD;
  else
    subsect->flags |= SEC_DEBUGGING;
  if (subspace->code_only)
    subsect->flags |= SEC_CODE;
  if (subspace->file_loc_init_value == 0
      && subspace->initialization_length == 0)
    subsect->flags &= ~(SEC_DATA | SEC_LOAD | SEC_HAS_CONTENTS);
  if (subspace->fixup_request_quantity != 0)
    {
      subsect->flags |= SEC_RELOC;
      subsect->rel_filepos = subspace->fixup_request_index;
      som_section_data (subsect)->reloc_size = subspace->fixup_request_quantity;
      subsect->reloc_count = (unsigned) -1;
    }
}

static bool
process_one_subspace (bfd *abfd, unsigned long current_offset,
		      struct som_header *file_hdr, const char *space_strings,
		      asection *space_asect, unsigned int *total_subspaces,
		      struct som_subspace_dictionary_record *save_subspace,
		      bfd_size_type *space_size)
{
  struct som_external_subspace_dictionary_record ext_subspace;
  struct som_subspace_dictionary_record subspace;
  asection *subspace_asect;

  if (bfd_read (&ext_subspace, sizeof (ext_subspace), abfd)
      != sizeof (ext_subspace))
    return false;

  som_swap_subspace_dictionary_in (&ext_subspace, &subspace);

  if (subspace.name >= file_hdr->space_strings_size)
    return false;

  const char *subspace_name = subspace.name + space_strings;
  subspace_asect = create_section_from_name (abfd, subspace_name);
  if (!subspace_asect)
    return false;

  if (!bfd_som_set_subsection_attributes (
	  subspace_asect, space_asect, subspace.access_control_bits,
	  subspace.sort_key, subspace.quadrant, subspace.is_comdat,
	  subspace.is_common, subspace.dup_common))
    return false;

  (*total_subspaces)++;
  subspace_asect->target_index = bfd_tell (abfd) - sizeof (subspace);

  set_subspace_flags (subspace_asect, &subspace);

  subspace_asect->vma = subspace.subspace_start;
  subspace_asect->size = subspace.subspace_length;
  subspace_asect->filepos = subspace.file_loc_init_value + current_offset;
  subspace_asect->alignment_power = exact_log2 (subspace.alignment);
  if (subspace_asect->alignment_power == (unsigned) -1)
    return false;

  if (subspace.file_loc_init_value > save_subspace->file_loc_init_value)
    *save_subspace = subspace;

  *space_size += subspace.subspace_length;
  return true;
}

static void
set_space_size (asection *space_asect, const struct som_header *file_hdr,
		const struct som_subspace_dictionary_record *save_subspace,
		bfd_size_type space_size)
{
  if (save_subspace->file_loc_init_value == 0)
    space_asect->size = 0;
  else if (file_hdr->a_magic != RELOC_MAGIC)
    space_asect->size = (save_subspace->subspace_start - space_asect->vma
			 + save_subspace->subspace_length);
  else
    space_asect->size = space_size;
}

static bool
process_subspaces_for_space (bfd *abfd, unsigned long current_offset,
			     struct som_header *file_hdr,
			     const char *space_strings,
			     asection *space_asect,
			     const struct som_space_dictionary_record *space,
			     unsigned int *total_subspaces)
{
  struct som_subspace_dictionary_record first_subspace, save_subspace;
  struct som_external_subspace_dictionary_record ext_subspace;
  bfd_size_type space_size = 0;
  file_ptr subspace_loc =
    current_offset + file_hdr->subspace_location
    + space->subspace_index * sizeof (ext_subspace);

  if (bfd_seek (abfd, subspace_loc, SEEK_SET) != 0)
    return false;

  if (bfd_read (&ext_subspace, sizeof (ext_subspace), abfd)
      != sizeof (ext_subspace))
    return false;

  som_swap_subspace_dictionary_in (&ext_subspace, &first_subspace);

  space_asect->vma = first_subspace.subspace_start;
  space_asect->filepos = first_subspace.file_loc_init_value + current_offset;
  space_asect->alignment_power = exact_log2 (first_subspace.alignment);
  if (space_asect->alignment_power == (unsigned) -1)
    return false;

  if (bfd_seek (abfd, subspace_loc, SEEK_SET) != 0)
    return false;

  memset (&save_subspace, 0, sizeof (save_subspace));
  for (unsigned int i = 0; i < space->subspace_quantity; i++)
    {
      if (!process_one_subspace (abfd, current_offset, file_hdr, space_strings,
				 space_asect, total_subspaces, &save_subspace,
				 &space_size))
	return false;
    }

  set_space_size (space_asect, file_hdr, &save_subspace, space_size);
  return true;
}

static bool
process_space (bfd *abfd, unsigned long current_offset,
	       struct som_header *file_hdr, const char *space_strings,
	       unsigned int space_index, unsigned int *total_subspaces)
{
  struct som_space_dictionary_record space;
  struct som_external_space_dictionary_record ext_space;
  asection *space_asect;

  file_ptr space_loc = current_offset + file_hdr->space_location
		       + space_index * sizeof (ext_space);
  if (bfd_seek (abfd, space_loc, SEEK_SET) != 0)
    return false;

  if (bfd_read (&ext_space, sizeof (ext_space), abfd) != sizeof (ext_space))
    return false;

  som_swap_space_dictionary_in (&ext_space, &space);

  if (space.name >= file_hdr->space_strings_size)
    return false;

  const char *space_name = space.name + space_strings;
  space_asect = create_section_from_name (abfd, space_name);
  if (!space_asect)
    return false;

  if (space.is_loadable == 0)
    space_asect->flags |= SEC_DEBUGGING;

  if (!bfd_som_set_section_attributes (space_asect, space.is_defined,
				       space.is_private, space.sort_key,
				       space.space_number))
    return false;

  if (space.subspace_quantity > 0)
    return process_subspaces_for_space (
      abfd, current_offset, file_hdr, space_strings, space_asect, &space,
      total_subspaces);

  return true;
}

static char *
read_space_strings (bfd *abfd, struct som_header *file_hdr,
		    unsigned long current_offset)
{
  size_t amt = file_hdr->space_strings_size;
  if (amt == (size_t) -1)
    {
      bfd_set_error (bfd_error_no_memory);
      return NULL;
    }

  if (bfd_seek (abfd, current_offset + file_hdr->space_strings_location,
		SEEK_SET) != 0)
    return NULL;

  char *strings = (char *) _bfd_malloc_and_read (abfd, amt + 1, amt);
  if (strings == NULL)
    return NULL;

  strings[amt] = '\0';
  return strings;
}

static bool
sort_and_reindex_subspaces (bfd *abfd, unsigned int total_subspaces,
			    asection ***subspace_sections_ptr)
{
  size_t amt;
  if (_bfd_mul_overflow (total_subspaces, sizeof (asection *), &amt))
    {
      bfd_set_error (bfd_error_file_too_big);
      return false;
    }

  asection **sections = bfd_malloc (amt);
  if (sections == NULL)
    return false;

  *subspace_sections_ptr = sections;

  unsigned int i = 0;
  for (asection *section = abfd->sections; section; section = section->next)
    {
      if (som_is_subspace (section))
	sections[i++] = section;
    }

  qsort (sections, total_subspaces, sizeof (asection *), compare_subspaces);

  for (i = 0; i < total_subspaces; i++)
    sections[i]->target_index = i;

  return true;
}

static bool
setup_sections (bfd *abfd,
		struct som_header *file_hdr,
		unsigned long current_offset)
{
  char *space_strings = NULL;
  asection **subspace_sections = NULL;
  unsigned int total_subspaces = 0;
  bool success = false;

  space_strings = read_space_strings (abfd, file_hdr, current_offset);
  if (space_strings == NULL)
    goto cleanup;

  for (unsigned int i = 0; i < file_hdr->space_total; i++)
    {
      if (!process_space (abfd, current_offset, file_hdr, space_strings, i,
			  &total_subspaces))
	goto cleanup;
    }

  if (total_subspaces > 0)
    {
      if (!sort_and_reindex_subspaces (abfd, total_subspaces,
				       &subspace_sections))
	goto cleanup;
    }

  success = true;

cleanup:
  free (space_strings);
  free (subspace_sections);
  return success;
}


/* Read in a SOM object and make it into a BFD.  */

static bool
som_bfd_read_or_fail (void *ptr, size_t size, bfd *abfd)
{
  if (bfd_read (ptr, size, abfd) != size)
    {
      if (bfd_get_error () != bfd_error_system_call)
	bfd_set_error (bfd_error_wrong_format);
      return false;
    }
  return true;
}

static bool
som_bfd_seek_or_fail (bfd *abfd, file_ptr offset, int whence)
{
  if (bfd_seek (abfd, offset, whence) != 0)
    {
      if (bfd_get_error () != bfd_error_system_call)
	bfd_set_error (bfd_error_wrong_format);
      return false;
    }
  return true;
}

static bool
handle_execlibmagic (bfd *abfd,
		     struct som_external_header *ext_file_hdr,
		     struct som_header *file_hdr,
		     unsigned long *current_offset)
{
  struct som_external_lst_header ext_lst_header;
  struct som_external_som_entry ext_som_entry;

  if (!som_bfd_seek_or_fail (abfd, 0, SEEK_SET))
    return false;

  if (!som_bfd_read_or_fail (&ext_lst_header, sizeof (ext_lst_header), abfd))
    return false;

  unsigned long loc = bfd_getb32 (ext_lst_header.dir_loc);
  if (!som_bfd_seek_or_fail (abfd, (file_ptr) loc, SEEK_SET))
    return false;

  if (!som_bfd_read_or_fail (&ext_som_entry, sizeof (ext_som_entry), abfd))
    return false;

  *current_offset = bfd_getb32 (ext_som_entry.location);
  if (!som_bfd_seek_or_fail (abfd, (file_ptr) *current_offset, SEEK_SET))
    return false;

  if (!som_bfd_read_or_fail (ext_file_hdr, sizeof (*ext_file_hdr), abfd))
    return false;

  som_swap_header_in (ext_file_hdr, file_hdr);
  return true;
}

static bfd_cleanup
som_object_p (bfd *abfd)
{
  struct som_external_header ext_file_hdr;
  struct som_header file_hdr;
  struct som_exec_auxhdr *aux_hdr_ptr = NULL;
  unsigned long current_offset = 0;

  if (!som_bfd_read_or_fail (&ext_file_hdr, sizeof (ext_file_hdr), abfd))
    return NULL;

  som_swap_header_in (&ext_file_hdr, &file_hdr);

  if (!_PA_RISC_ID (file_hdr.system_id))
    {
      bfd_set_error (bfd_error_wrong_format);
      return NULL;
    }

  switch (file_hdr.a_magic)
    {
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
      if (!handle_execlibmagic (abfd, &ext_file_hdr, &file_hdr, &current_offset))
	return NULL;
      break;

    default:
      bfd_set_error (bfd_error_wrong_format);
      return NULL;
    }

  if (file_hdr.version_id != OLD_VERSION_ID
      && file_hdr.version_id != NEW_VERSION_ID)
    {
      bfd_set_error (bfd_error_wrong_format);
      return NULL;
    }

  if (file_hdr.aux_header_size != 0)
    {
      struct som_external_exec_auxhdr ext_exec_auxhdr;

      aux_hdr_ptr = bfd_zalloc (abfd, (bfd_size_type) sizeof (*aux_hdr_ptr));
      if (aux_hdr_ptr == NULL)
	return NULL;

      if (!som_bfd_read_or_fail (&ext_exec_auxhdr, sizeof (ext_exec_auxhdr), abfd))
	return NULL;

      som_swap_exec_auxhdr_in (&ext_exec_auxhdr, aux_hdr_ptr);
    }

  if (!setup_sections (abfd, &file_hdr, current_offset))
    {
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }

  return som_object_setup (abfd, &file_hdr, aux_hdr_ptr, current_offset);
}

/* Create a SOM object.  */

static bool
som_mkobject (bfd *abfd)
{
  abfd->tdata.som_data = bfd_zalloc (abfd, sizeof (struct som_data_struct));
  return abfd->tdata.som_data != NULL;
}

/* Initialize some information in the file header.  This routine makes
   not attempt at doing the right thing for a full executable; it
   is only meant to handle relocatable objects.  */

static unsigned int
som_get_magic (flagword flags)
{
  if (flags & D_PAGED)
    return DEMAND_MAGIC;
  if (flags & WP_TEXT)
    return SHARE_MAGIC;
#ifdef SHL_MAGIC
  if (flags & DYNAMIC)
    return SHL_MAGIC;
#endif
  return EXEC_MAGIC;
}

static bool
som_prep_space_section (bfd *abfd, asection *section)
{
  struct som_section_data *sdata = som_section_data (section);
  const struct som_section_copy_data *copy_data = sdata->copy_data;
  struct som_space_dictionary_record *space_dict;

  space_dict = bfd_zalloc (abfd, sizeof (*space_dict));
  if (space_dict == NULL)
    return false;

  sdata->space_dict = space_dict;
  space_dict->loader_fix_index = -1;
  space_dict->init_pointer_index = -1;

  space_dict->sort_key = copy_data->sort_key;
  space_dict->is_defined = copy_data->is_defined;
  space_dict->is_private = copy_data->is_private;
  space_dict->space_number = copy_data->space_number;
  return true;
}

static bool
som_prep_subspace_section (bfd *abfd, asection *section)
{
  struct som_section_data *sdata = som_section_data (section);
  const struct som_section_copy_data *copy_data = sdata->copy_data;
  struct som_subspace_dictionary_record *subspace_dict;

  subspace_dict = bfd_zalloc (abfd, sizeof (*subspace_dict));
  if (subspace_dict == NULL)
    return false;

  sdata->subspace_dict = subspace_dict;

  subspace_dict->is_loadable = (section->flags & SEC_ALLOC) != 0;
  subspace_dict->code_only = (section->flags & SEC_CODE) != 0;

  subspace_dict->subspace_start = section->vma;
  subspace_dict->subspace_length = section->size;
  subspace_dict->initialization_length = section->size;
  subspace_dict->alignment = 1 << section->alignment_power;

  subspace_dict->sort_key = copy_data->sort_key;
  subspace_dict->access_control_bits = copy_data->access_control_bits;
  subspace_dict->quadrant = copy_data->quadrant;
  subspace_dict->is_comdat = copy_data->is_comdat;
  subspace_dict->is_common = copy_data->is_common;
  subspace_dict->dup_common = copy_data->dup_common;
  return true;
}

static bool
som_prep_headers (bfd *abfd)
{
  struct som_header *file_hdr;

  file_hdr = bfd_zalloc (abfd, sizeof (struct som_header));
  if (file_hdr == NULL)
    return false;
  obj_som_file_hdr (abfd) = file_hdr;

  if (abfd->flags & (EXEC_P | DYNAMIC))
    {
      obj_som_exec_hdr (abfd) = bfd_zalloc (abfd, sizeof (struct som_exec_auxhdr));
      if (obj_som_exec_hdr (abfd) == NULL)
	return false;
      file_hdr->a_magic = som_get_magic (abfd->flags);
    }
  else
    {
      file_hdr->a_magic = RELOC_MAGIC;
    }

  file_hdr->file_time.secs = 0;
  file_hdr->file_time.nanosecs = 0;
  file_hdr->entry_space = 0;
  file_hdr->entry_subspace = 0;
  file_hdr->entry_offset = 0;
  file_hdr->presumed_dp = 0;

  for (asection *section = abfd->sections; section != NULL; section = section->next)
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
  const struct som_copy_data *copy_data = som_section_data (section)->copy_data;

  if (copy_data == NULL)
    {
      return false;
    }

  const asection *container = copy_data->container;
  if (container == NULL)
    {
      return false;
    }

  return container == section || container->output_section == section;
}

/* Return TRUE if the given section is a SOM subspace, FALSE otherwise.  */

static bool
som_is_subspace (asection *section)
{
  struct som_copy_data *copy_data = som_section_data (section)->copy_data;
  asection *container;

  if (copy_data == NULL)
    {
      return false;
    }

  container = copy_data->container;

  return (container != NULL
	  && container != section
	  && container->output_section != section);
}

/* Return TRUE if the given space contains the given subspace.  It
   is safe to assume space really is a space, and subspace really
   is a subspace.  */

static bool
som_is_container (asection *space, asection *subspace)
{
  const asection *container;
  const void *subspace_data;

  if (!space || !subspace)
    {
      return false;
    }

  subspace_data = som_section_data (subspace);

  /*
   * The original code implies a structure like:
   *   struct some_data { asection *container; ... };
   *   struct som_section_data { struct some_data *copy_data; ... };
   * We must check each pointer in the chain before dereferencing it.
   * The explicit type names are omitted as they are not provided,
   * but the compiler in the target environment will know them.
   */
  if (!subspace_data
      || !(((const struct { struct { asection *container; } *copy_data; } *)subspace_data)->copy_data)
      || !(((const struct { struct { asection *container; } *copy_data; } *)subspace_data)->copy_data->container))
    {
      return false;
    }

  container = ((const struct { struct { asection *container; } *copy_data; } *)subspace_data)->copy_data->container;

  return (container == space) || (container->output_section == space);
}

/* Count and return the number of spaces attached to the given BFD.  */

static unsigned long
som_count_spaces (const bfd *abfd)
{
  if (!abfd)
    {
      return 0;
    }

  unsigned long count = 0;
  for (const asection *section = abfd->sections; section != NULL; section = section->next)
    {
      if (som_is_space (section))
        {
          count++;
        }
    }

  return count;
}

/* Count the number of subspaces attached to the given BFD.  */

static unsigned long
som_count_subspaces (bfd *abfd)
{
  if (!abfd)
    {
      return 0;
    }

  unsigned long count = 0;
  for (asection *section = abfd->sections; section != NULL; section = section->next)
    {
      count += som_is_subspace (section);
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
  if ((sym->flags & BSF_SECTION_SYM) != 0)
    {
      return sym->udata.i;
    }
  return som_symbol_data (sym)->reloc_count;
}

static int
compare_syms (const void *arg1, const void *arg2)
{
  const asymbol *sym1 = *(const asymbol **) arg1;
  const asymbol *sym2 = *(const asymbol **) arg2;

  const unsigned int count1 = get_symbol_reloc_count (sym1);
  const unsigned int count2 = get_symbol_reloc_count (sym2);

  if (count1 < count2)
    {
      return 1;
    }
  if (count1 > count2)
    {
      return -1;
    }
  return 0;
}

/* Return -1, 0, 1 indicating the relative ordering of subspace1
   and subspace.  */

static int
compare_subspaces (const void *arg1, const void *arg2)
{
  const asection *s1 = *(const asection **) arg1;
  const asection *s2 = *(const asection **) arg2;

  if (s1->target_index < s2->target_index)
    return -1;
  if (s1->target_index > s2->target_index)
    return 1;
  return 0;
}

/* Perform various work in preparation for emitting the fixup stream.  */

static int compare_syms (const void *, const void *);

static void
initialize_symbol_counters (asymbol **syms, unsigned long num_syms)
{
  for (unsigned long i = 0; i < num_syms; i++)
    {
      asymbol *sym = syms[i];
      struct som_symbol_info *info = som_symbol_data (sym);

      if (info == NULL || (sym->flags & BSF_SECTION_SYM))
        {
          sym->flags |= BSF_SECTION_SYM;
          sym->udata.i = 0;
        }
      else
        {
          info->reloc_count = 0;
        }
    }
}

static void
count_one_relocation (arelent *reloc)
{
  if (reloc->sym_ptr_ptr == NULL)
    {
      return;
    }

  asymbol *sym = *reloc->sym_ptr_ptr;
  if (bfd_is_abs_section (sym->section))
    {
      return;
    }

  int scale = (reloc->howto->type == R_DP_RELATIVE
               || reloc->howto->type == R_CODE_ONE_SYMBOL)
              ? 2 : 1;

  if (sym->flags & BSF_SECTION_SYM)
    {
      sym->udata.i += scale;
    }
  else
    {
      som_symbol_data (sym)->reloc_count += scale;
    }
}

static void
count_all_relocations (bfd *abfd)
{
  for (asection *sec = abfd->sections; sec != NULL; sec = sec->next)
    {
      for (bfd_size_type j = 1; j < sec->reloc_count; j++)
        {
          count_one_relocation (sec->orelocation[j]);
        }
    }
}

static asymbol **
create_and_sort_symbols (bfd *abfd, asymbol **syms, unsigned long num_syms)
{
  size_t amt;
  if (_bfd_mul_overflow (num_syms, sizeof (asymbol *), &amt))
    {
      bfd_set_error (bfd_error_no_memory);
      return NULL;
    }

  asymbol **sorted_syms = bfd_zalloc (abfd, amt);
  if (sorted_syms == NULL)
    {
      return NULL;
    }

  memcpy (sorted_syms, syms, amt);
  qsort (sorted_syms, num_syms, sizeof (asymbol *), compare_syms);
  return sorted_syms;
}

static void
assign_symbol_indices (asymbol **sorted_syms, unsigned long num_syms)
{
  for (unsigned long i = 0; i < num_syms; i++)
    {
      asymbol *sym = sorted_syms[i];
      if (sym->flags & BSF_SECTION_SYM)
        {
          sym->udata.i = i;
        }
      else
        {
          som_symbol_data (sym)->index = i;
        }
    }
}

static bool
som_prep_for_fixups (bfd *abfd, asymbol **syms, unsigned long num_syms)
{
  if (num_syms == 0)
    {
      return true;
    }

  initialize_symbol_counters (syms, num_syms);
  count_all_relocations (abfd);

  asymbol **sorted_syms = create_and_sort_symbols (abfd, syms, num_syms);
  if (sorted_syms == NULL)
    {
      return false;
    }

  obj_som_sorted_syms (abfd) = sorted_syms;
  assign_symbol_indices (sorted_syms, num_syms);

  return true;
}

static int
get_symbol_index (arelent *reloc)
{
  bfd_symbol *sym = *reloc->sym_ptr_ptr;
  if ((sym->flags & BSF_SECTION_SYM) != 0)
    return sym->udata.i;
  return som_symbol_data (sym)->index;
}

static bool
validate_reloc_offset (bfd *abfd, asection *s, arelent *r,
		       unsigned int last_offset)
{
  if (r->address < last_offset)
    {
      _bfd_error_handler (_("%pB(%pA+%#" PRIx64 "): "
			    "%s relocation offset out of order"),
			  abfd, s, (uint64_t) r->address, r->howto->name);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  if (!bfd_reloc_offset_in_range (r->howto, abfd, s, r->address))
    {
      _bfd_error_handler (_("%pB(%pA+%#" PRIx64 "): "
			    "%s relocation offset out of range"),
			  abfd, s, (uint64_t) r->address, r->howto->name);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  return true;
}

static bool
flush_fixup_buffer (bfd *abfd, unsigned char **p_ptr,
		    unsigned char *buffer_start)
{
  size_t amt = *p_ptr - buffer_start;
  if (amt > 0 && bfd_write (buffer_start, amt, abfd) != amt)
    return false;

  *p_ptr = buffer_start;
  return true;
}

static unsigned char *
emit_code_style_symbol_reloc (bfd *abfd, unsigned char *p,
			      unsigned int *subspace_reloc_sizep,
			      int sym_num, unsigned int type,
			      reloc_queue_type *reloc_queue)
{
  if (sym_num < 0x20)
    {
      bfd_put_8 (abfd, type + sym_num, p);
      (*subspace_reloc_sizep)++;
      p++;
    }
  else if (sym_num < 0x100)
    {
      bfd_put_8 (abfd, type + 32, p);
      bfd_put_8 (abfd, sym_num, p + 1);
      p = try_prev_fixup (abfd, subspace_reloc_sizep, p, 2, reloc_queue);
    }
  else if (sym_num < 0x10000000)
    {
      bfd_put_8 (abfd, type + 33, p);
      bfd_put_8 (abfd, sym_num >> 16, p + 1);
      bfd_put_16 (abfd, (bfd_vma) sym_num, p + 2);
      p = try_prev_fixup (abfd, subspace_reloc_sizep, p, 4, reloc_queue);
    }
  else
    {
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }
  return p;
}

static unsigned char *
emit_data_style_symbol_reloc (bfd *abfd, unsigned char *p,
			      unsigned int *subspace_reloc_sizep,
			      int sym_num, unsigned int type,
			      reloc_queue_type *reloc_queue)
{
  if (sym_num < 0x100)
    {
      bfd_put_8 (abfd, type, p);
      bfd_put_8 (abfd, sym_num, p + 1);
      p = try_prev_fixup (abfd, subspace_reloc_sizep, p, 2, reloc_queue);
    }
  else if (sym_num < 0x10000000)
    {
      bfd_put_8 (abfd, type + 1, p);
      bfd_put_8 (abfd, sym_num >> 16, p + 1);
      bfd_put_16 (abfd, (bfd_vma) sym_num, p + 2);
      p = try_prev_fixup (abfd, subspace_reloc_sizep, p, 4, reloc_queue);
    }
  else
    {
      bfd_set_error (bfd_error_bad_value);
      return NULL;
    }
  return p;
}

static bool
process_subspace_fixups (bfd *abfd, asection *subsection,
			 unsigned long fixup_stream_offset,
			 unsigned int *subspace_reloc_size_out)
{
  unsigned char tmp_space[SOM_TMP_BUFSIZE];
  unsigned char *p = tmp_space;
  unsigned int subspace_reloc_size = 0;
  unsigned int reloc_offset = 0;
  unsigned int current_rounding_mode = R_N_MODE;
#ifndef NO_PCREL_MODES
  unsigned int current_call_mode = R_SHORT_PCREL_MODE;
#endif

  if (bfd_seek (abfd, fixup_stream_offset, SEEK_SET) != 0)
    return false;

  som_initialize_reloc_queue (reloc_queue);

  for (unsigned int j = 0; j < subsection->reloc_count; j++)
    {
      arelent *bfd_reloc = subsection->orelocation[j];
      int sym_num;

      if (!validate_reloc_offset (abfd, subsection, bfd_reloc, reloc_offset))
	return false;

      if ((size_t) (p - tmp_space) + 512 > SOM_TMP_BUFSIZE)
	{
	  if (!flush_fixup_buffer (abfd, &p, tmp_space))
	    return false;
	  som_initialize_reloc_queue (reloc_queue);
	}

      p = som_reloc_skip (abfd, bfd_reloc->address - reloc_offset, p,
			  &subspace_reloc_size, reloc_queue);

      reloc_offset = bfd_reloc->address + bfd_reloc->howto->size;
      sym_num = get_symbol_index (bfd_reloc);

      switch (bfd_reloc->howto->type)
	{
	case R_PCREL_CALL:
	case R_ABS_CALL:
	  p = som_reloc_call (abfd, p, &subspace_reloc_size, bfd_reloc,
			      sym_num, reloc_queue);
	  break;

	case R_CODE_ONE_SYMBOL:
	case R_DP_RELATIVE:
	  if (bfd_reloc->addend != 0)
	    p = som_reloc_addend (abfd, bfd_reloc->addend, p,
				  &subspace_reloc_size, reloc_queue);
	  if (p != NULL)
	    p = emit_code_style_symbol_reloc (
		abfd, p, &subspace_reloc_size, sym_num,
		bfd_reloc->howto->type, reloc_queue);
	  break;

	case R_DATA_GPREL:
	  if (bfd_reloc->addend != 0)
	    p = som_reloc_addend (abfd, bfd_reloc->addend, p,
				  &subspace_reloc_size, reloc_queue);

	  if (p != NULL && sym_num < 0x10000000)
	    {
	      bfd_put_8 (abfd, bfd_reloc->howto->type, p);
	      bfd_put_8 (abfd, sym_num >> 16, p + 1);
	      bfd_put_16 (abfd, (bfd_vma) sym_num, p + 2);
	      p = try_prev_fixup (abfd, &subspace_reloc_size, p, 4,
				  reloc_queue);
	    }
	  else if (p != NULL)
	    {
	      bfd_set_error (bfd_error_bad_value);
	      p = NULL;
	    }
	  break;

	case R_DATA_ONE_SYMBOL:
	case R_DATA_PLABEL:
	case R_CODE_PLABEL:
	case R_DLT_REL:
	  if (bfd_reloc->howto->type != R_DATA_ONE_SYMBOL
	      && bfd_reloc->addend != 0)
	    p = som_reloc_addend (abfd, bfd_reloc->addend, p,
				  &subspace_reloc_size, reloc_queue);
	  if (p != NULL)
	    p = emit_data_style_symbol_reloc (
		abfd, p, &subspace_reloc_size, sym_num,
		bfd_reloc->howto->type, reloc_queue);
	  break;

	case R_ENTRY:
	  bfd_put_8 (abfd, R_ENTRY, p);
	  bfd_put_32 (abfd, bfd_reloc->addend, p + 1);
	  p[9] = 0; /* Avoid uninitialized warning.  */
	  for (unsigned int tmp = j; tmp < subsection->reloc_count; tmp++)
	    if (subsection->orelocation[tmp]->howto->type == R_EXIT)
	      {
		bfd_put_32 (abfd, subsection->orelocation[tmp]->addend,
			    p + 5);
		p = try_prev_fixup (abfd, &subspace_reloc_size, p, 9,
				    reloc_queue);
		break;
	      }
	  if (p[9] != 9) /* Check if loop completed.  */
	    {
	      bfd_set_error (bfd_error_bad_value);
	      p = NULL;
	    }
	  break;

	case R_N_MODE: case R_S_MODE: case R_D_MODE: case R_R_MODE:
	  if (bfd_reloc->howto->type != current_rounding_mode)
	    {
	      bfd_put_8 (abfd, bfd_reloc->howto->type, p);
	      subspace_reloc_size++;
	      p++;
	      current_rounding_mode = bfd_reloc->howto->type;
	    }
	  break;

#ifndef NO_PCREL_MODES
	case R_LONG_PCREL_MODE: case R_SHORT_PCREL_MODE:
	  if (bfd_reloc->howto->type != current_call_mode)
	    {
	      bfd_put_8 (abfd, bfd_reloc->howto->type, p);
	      subspace_reloc_size++;
	      p++;
	      current_call_mode = bfd_reloc->howto->type;
	    }
	  break;
#endif

	case R_EXIT: case R_ALT_ENTRY: case R_FSEL: case R_LSEL:
	case R_RSEL: case R_BEGIN_BRTAB: case R_END_BRTAB: case R_BEGIN_TRY:
	case R_N0SEL: case R_N1SEL: case R_CODE_EXPR: case R_DATA_EXPR:
	  bfd_put_8 (abfd, bfd_reloc->howto->type, p);
	  subspace_reloc_size++;
	  p++;
	  break;

	case R_END_TRY:
	  if (bfd_reloc->addend == 0)
	    {
	      bfd_put_8 (abfd, bfd_reloc->howto->type, p);
	      subspace_reloc_size++;
	      p++;
	    }
	  else if (bfd_reloc->addend < 1024)
	    {
	      bfd_put_8 (abfd, bfd_reloc->howto->type + 1, p);
	      bfd_put_8 (abfd, bfd_reloc->addend / 4, p + 1);
	      p = try_prev_fixup (abfd, &subspace_reloc_size, p, 2,
				  reloc_queue);
	    }
	  else
	    {
	      bfd_put_8 (abfd, bfd_reloc->howto->type + 2, p);
	      bfd_put_8 (abfd, (bfd_reloc->addend / 4) >> 16, p + 1);
	      bfd_put_16 (abfd, bfd_reloc->addend / 4, p + 2);
	      p = try_prev_fixup (abfd, &subspace_reloc_size, p, 4,
				  reloc_queue);
	    }
	  break;

	case R_COMP1:
	  bfd_put_8 (abfd, bfd_reloc->howto->type, p);
	  bfd_put_8 (abfd, 0x44, p + 1);
	  p = try_prev_fixup (abfd, &subspace_reloc_size, p, 2, reloc_queue);
	  break;

	case R_COMP2:
	  bfd_put_8 (abfd, bfd_reloc->howto->type, p);
	  bfd_put_8 (abfd, 0x80, p + 1);
	  bfd_put_8 (abfd, sym_num >> 16, p + 2);
	  bfd_put_16 (abfd, (bfd_vma) sym_num, p + 3);
	  p = try_prev_fixup (abfd, &subspace_reloc_size, p, 5, reloc_queue);
	  break;

	default:
	  bfd_put_8 (abfd, 0xff, p);
	  subspace_reloc_size++;
	  p++;
	  break;
	}
      if (p == NULL)
	return false;
    }

  p = som_reloc_skip (abfd, subsection->size - reloc_offset, p,
		      &subspace_reloc_size, reloc_queue);

  if (!flush_fixup_buffer (abfd, &p, tmp_space))
    return false;

  *subspace_reloc_size_out = subspace_reloc_size;
  return true;
}

static bool
som_write_fixups (bfd *abfd,
		  unsigned long current_offset,
		  unsigned int *total_reloc_sizep)
{
  unsigned int total_reloc_size = 0;
  unsigned int num_spaces = obj_som_file_hdr (abfd)->space_total;
  asection *space_section = abfd->sections;

  for (unsigned int i = 0; i < num_spaces; i++)
    {
      while (space_section && !som_is_space (space_section))
	space_section = space_section->next;
      if (!space_section)
	break;

      for (asection *subsection = abfd->sections;
	   subsection != NULL;
	   subsection = subsection->next)
	{
	  if (!som_is_subspace (subsection)
	      || !som_is_container (space_section, subsection))
	    continue;

	  if ((subsection->flags & SEC_HAS_CONTENTS) == 0)
	    {
	      som_section_data (subsection)->subspace_dict->fixup_request_index
		= -1;
	      continue;
	    }

	  som_section_data (subsection)->subspace_dict->fixup_request_index
	    = total_reloc_size;

	  unsigned int subspace_reloc_size;
	  if (!process_subspace_fixups (abfd, subsection,
					current_offset + total_reloc_size,
					&subspace_reloc_size))
	    return false;

	  som_section_data (subsection)->subspace_dict->fixup_request_quantity
	    = subspace_reloc_size;
	  total_reloc_size += subspace_reloc_size;
	}
      space_section = space_section->next;
    }

  *total_reloc_sizep = total_reloc_size;
  return true;
}

/* Write the length of STR followed by STR to P which points into
   *BUF, a buffer of *BUFLEN size.  Track total size in *STRINGS_SIZE,
   setting *STRX to the current offset for STR.  When STR can't fit in
   *BUF, flush the buffer to ABFD, possibly reallocating.  Return the
   next available location in *BUF, or NULL on error.  */

static char *
ensure_buffer_space (char *p, size_t needed, bfd *abfd, char **buf, size_t *buflen)
{
  const size_t BUFFER_GROWTH_FACTOR = 2;
  size_t current_offset = p - *buf;

  if (current_offset + needed <= *buflen)
    {
      return p;
    }

  if (current_offset > 0)
    {
      if (bfd_write (*buf, current_offset, abfd) != current_offset)
        {
          return NULL;
        }
    }

  if (needed > *buflen)
    {
      size_t new_buflen = *buflen * BUFFER_GROWTH_FACTOR;
      if (new_buflen < needed)
        {
          new_buflen = needed;
        }

      free (*buf);
      char *new_buf = bfd_malloc (new_buflen);
      if (new_buf == NULL)
        {
          *buf = NULL;
          *buflen = 0;
          return NULL;
        }
      *buf = new_buf;
      *buflen = new_buflen;
    }

  return *buf;
}

static char *
add_string (char *p, const char *str, bfd *abfd, char **buf, size_t *buflen,
	    unsigned int *strings_size, unsigned int *strx)
{
  const size_t ALIGNMENT = 4;
  const size_t LENGTH_PREFIX_SIZE = 4;

  size_t str_len_with_null = strlen (str) + 1;
  size_t unaligned_size = LENGTH_PREFIX_SIZE + str_len_with_null;
  size_t entry_size = (unaligned_size + ALIGNMENT - 1) & ~(ALIGNMENT - 1);

  char *current_p = ensure_buffer_space (p, entry_size, abfd, buf, buflen);
  if (current_p == NULL)
    {
      return NULL;
    }
  p = current_p;

  bfd_put_32 (abfd, str_len_with_null - 1, p);
  *strx = *strings_size + LENGTH_PREFIX_SIZE;
  p += LENGTH_PREFIX_SIZE;

  memcpy (p, str, str_len_with_null);
  p += str_len_with_null;

  size_t padding_size = entry_size - unaligned_size;
  if (padding_size > 0)
    {
      memset (p, 0, padding_size);
      p += padding_size;
    }

  *strings_size += entry_size;

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
  char *p;
  bool ok = false;

  if (tmp_space == NULL)
    return false;

  p = tmp_space;

  if (bfd_seek (abfd, current_offset, SEEK_SET) != 0)
    goto cleanup;

  *strings_size = 0;
  for (asection *section = abfd->sections; section != NULL; section = section->next)
    {
      unsigned int *strx;

      if (som_is_space (section))
	strx = &som_section_data (section)->space_dict->name;
      else if (som_is_subspace (section))
	strx = &som_section_data (section)->subspace_dict->name;
      else
	continue;

      p = add_string (p, section->name, abfd, &tmp_space, &tmp_space_size,
		      strings_size, strx);
      if (p == NULL)
	goto cleanup;
    }

  size_t amt = p - tmp_space;
  if (amt > 0)
    {
      if (bfd_write (tmp_space, amt, abfd) != amt)
	goto cleanup;
    }

  ok = true;

cleanup:
  free (tmp_space);
  return ok;
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
  bool success = false;
  size_t tmp_space_size = SOM_TMP_BUFSIZE;
  char *tmp_space = bfd_malloc (tmp_space_size);
  char *p = tmp_space;

  if (tmp_space == NULL)
    goto cleanup;

  if (bfd_seek (abfd, current_offset, SEEK_SET) != 0)
    goto cleanup;

  *strings_size = 0;

  if (compilation_unit)
    {
      struct som_name_pt *names[] = {
	&compilation_unit->name,
	&compilation_unit->language_name,
	&compilation_unit->product_id,
	&compilation_unit->version_id
      };

      for (size_t i = 0; i < sizeof (names) / sizeof (names[0]); ++i)
	{
	  p = add_string (p, names[i]->name, abfd, &tmp_space, &tmp_space_size,
			  strings_size, &names[i]->strx);
	  if (p == NULL)
	    goto cleanup;
	}
    }

  for (unsigned int i = 0; i < num_syms; i++)
    {
      p = add_string (p, syms[i]->name, abfd, &tmp_space, &tmp_space_size,
		      strings_size,
		      &som_symbol_data (syms[i])->stringtab_offset);
      if (p == NULL)
	goto cleanup;
    }

  size_t remaining_bytes = p - tmp_space;
  if (remaining_bytes > 0)
    {
      if (bfd_write (tmp_space, remaining_bytes, abfd) != remaining_bytes)
	goto cleanup;
    }

  success = true;

cleanup:
  free (tmp_space);
  return success;
}

/* Compute variable information to be placed in the SOM headers,
   space/subspace dictionaries, relocation streams, etc.  Begin
   writing parts of the object file.  */

static bool
write_string_aux_header (bfd *abfd,
			 struct som_string_auxhdr *hdr,
			 unsigned long *current_offset)
{
  if (hdr == NULL)
    return true;

  if (bfd_seek (abfd, *current_offset, SEEK_SET) != 0)
    return false;

  struct som_external_string_auxhdr ext_string_auxhdr;
  bfd_size_type len;

  len = sizeof (struct som_external_string_auxhdr);
  obj_som_file_hdr (abfd)->aux_header_size += len;
  *current_offset += len;
  som_swap_string_auxhdr_out (hdr, &ext_string_auxhdr);
  if (bfd_write (&ext_string_auxhdr, len, abfd) != len)
    return false;

  len = hdr->header_id.length - 4;
  obj_som_file_hdr (abfd)->aux_header_size += len;
  *current_offset += len;
  if (bfd_write (hdr->string, len, abfd) != len)
    return false;

  return true;
}

static bool
som_write_aux_headers (bfd *abfd, unsigned long *current_offset)
{
  obj_som_file_hdr (abfd)->aux_header_location = *current_offset;
  obj_som_file_hdr (abfd)->aux_header_size = 0;

  if (abfd->flags & (EXEC_P | DYNAMIC))
    {
      *current_offset += sizeof (struct som_external_exec_auxhdr);
      obj_som_file_hdr (abfd)->aux_header_size
	+= sizeof (struct som_external_exec_auxhdr);
      struct som_exec_auxhdr *exec_header = obj_som_exec_hdr (abfd);
      exec_header->som_auxhdr.type = EXEC_AUX_ID;
      exec_header->som_auxhdr.length = 40;
    }

  if (!write_string_aux_header (abfd, obj_som_version_hdr (abfd), current_offset)
      || !write_string_aux_header (abfd, obj_som_copyright_hdr (abfd),
				   current_offset))
    return false;

  return true;
}

static void
som_layout_dictionaries (bfd *abfd, unsigned long *current_offset,
			 unsigned long num_spaces,
			 unsigned long num_subspaces)
{
  obj_som_file_hdr (abfd)->space_location = *current_offset;
  obj_som_file_hdr (abfd)->space_total = num_spaces;
  *current_offset += num_spaces * sizeof (struct som_external_space_dictionary_record);

  obj_som_file_hdr (abfd)->subspace_location = *current_offset;
  obj_som_file_hdr (abfd)->subspace_total = num_subspaces;
  *current_offset += num_subspaces * sizeof (struct som_external_subspace_dictionary_record);
}

static bool
som_write_space_string_table (bfd *abfd, unsigned long *current_offset)
{
  unsigned int strings_size = 0;

  if (*current_offset % 4)
    *current_offset += (4 - (*current_offset % 4));

  obj_som_file_hdr (abfd)->space_strings_location = *current_offset;

  if (!som_write_space_strings (abfd, *current_offset, &strings_size))
    return false;

  obj_som_file_hdr (abfd)->space_strings_size = strings_size;
  *current_offset += strings_size;
  return true;
}

static void
som_layout_compilation_unit (bfd *abfd, unsigned long *current_offset)
{
  obj_som_file_hdr (abfd)->compiler_location = *current_offset;
  obj_som_file_hdr (abfd)->compiler_total = 0;
  if (obj_som_compilation_unit (abfd))
    {
      obj_som_file_hdr (abfd)->compiler_total = 1;
      *current_offset += sizeof (struct som_external_compilation_unit);
    }
}

static void
som_layout_loadable_subspaces (bfd *abfd, unsigned long num_spaces,
			       unsigned long *current_offset,
			       unsigned int *total_subspaces)
{
  asection *section = abfd->sections;
  struct som_exec_auxhdr *exec_header = obj_som_exec_hdr (abfd);
  bool is_exec = (abfd->flags & (EXEC_P | DYNAMIC)) != 0;

  for (unsigned long i = 0; i < num_spaces; i++)
    {
      while (section != NULL && !som_is_space (section))
	section = section->next;
      if (section == NULL)
	break;

      unsigned int subspace_offset = 0;
      bool first_subspace = true;

      for (asection *subsection = abfd->sections; subsection != NULL;
	   subsection = subsection->next)
	{
	  if (!som_is_subspace (subsection)
	      || !som_is_container (section, subsection)
	      || (subsection->flags & SEC_ALLOC) == 0)
	    continue;

	  if (is_exec)
	    {
	      if (first_subspace)
		{
		  if (abfd->flags & (D_PAGED | DYNAMIC)
		      || (subsection->flags & SEC_CODE)
		      || ((abfd->flags & WP_TEXT)
			  && (subsection->flags & SEC_DATA)))
		    *current_offset = SOM_ALIGN (*current_offset, PA_PAGESIZE);

		  if ((subsection->flags & SEC_CODE)
		      && exec_header->exec_tfile == 0)
		    {
		      exec_header->exec_tmem = section->vma;
		      exec_header->exec_tfile = *current_offset;
		    }
		  if ((subsection->flags & SEC_DATA)
		      && exec_header->exec_dfile == 0)
		    {
		      exec_header->exec_dmem = section->vma;
		      exec_header->exec_dfile = *current_offset;
		    }
		  subspace_offset = subsection->vma;
		  first_subspace = false;
		}
	      else
		{
		  unsigned long hole_size = subsection->vma - subspace_offset;
		  *current_offset += hole_size;
		  if (subsection->flags & SEC_CODE)
		    exec_header->exec_tsize += hole_size;
		  else
		    exec_header->exec_dsize += hole_size;
		  subspace_offset += hole_size;
		}
	    }

	  subsection->target_index = (*total_subspaces)++;
	  if (subsection->flags & SEC_LOAD)
	    {
	      if (is_exec)
		{
		  if (subsection->flags & SEC_CODE)
		    exec_header->exec_tsize += subsection->size;
		  else if (subsection->flags & SEC_DATA)
		    exec_header->exec_dsize += subsection->size;
		}
	      som_section_data (subsection)->subspace_dict->file_loc_init_value = *current_offset;
	      subsection->filepos = *current_offset;
	      *current_offset += subsection->size;
	      subspace_offset += subsection->size;
	    }
	  else
	    {
	      if (is_exec)
		exec_header->exec_bsize += subsection->size;
	      som_section_data (subsection)->subspace_dict->file_loc_init_value = 0;
	      som_section_data (subsection)->subspace_dict->initialization_length = 0;
	    }
	}
      section = section->next;
    }
}

static void
som_layout_unloadable_subspaces (bfd *abfd, unsigned long num_spaces,
				 unsigned long *current_offset,
				 unsigned int *total_subspaces)
{
  asection *section = abfd->sections;

  if (abfd->flags & (EXEC_P | DYNAMIC))
    *current_offset = SOM_ALIGN (*current_offset, PA_PAGESIZE);

  obj_som_file_hdr (abfd)->unloadable_sp_location = *current_offset;

  for (unsigned long i = 0; i < num_spaces; i++)
    {
      while (section != NULL && !som_is_space (section))
	section = section->next;
      if (section == NULL)
	break;

      if (abfd->flags & (EXEC_P | DYNAMIC))
	*current_offset = SOM_ALIGN (*current_offset, PA_PAGESIZE);

      for (asection *subsection = abfd->sections; subsection != NULL;
	   subsection = subsection->next)
	{
	  if (!som_is_subspace (subsection)
	      || !som_is_container (section, subsection)
	      || (subsection->flags & SEC_ALLOC) != 0)
	    continue;

	  subsection->target_index = (*total_subspaces)++;
	  if ((subsection->flags & SEC_LOAD) == 0)
	    {
	      som_section_data (subsection)->subspace_dict->file_loc_init_value = *current_offset;
	      subsection->filepos = *current_offset;
	      *current_offset += subsection->size;
	    }
	  else
	    {
	      som_section_data (subsection)->subspace_dict->file_loc_init_value = 0;
	      som_section_data (subsection)->subspace_dict->initialization_length = subsection->size;
	    }
	}
      section = section->next;
    }
  obj_som_file_hdr (abfd)->unloadable_sp_size = *current_offset - obj_som_file_hdr (abfd)->unloadable_sp_location;
}

static bool
som_finalize_file (bfd *abfd, unsigned long *current_offset)
{
  if (abfd->flags & (EXEC_P | DYNAMIC))
    {
      *current_offset = SOM_ALIGN (*current_offset, PA_PAGESIZE);
      if (*current_offset > 0)
	{
	  if (bfd_seek (abfd, *current_offset - 1, SEEK_SET) != 0)
	    return false;
	  if (bfd_write ("", 1, abfd) != 1)
	    return false;
	}
    }

  obj_som_file_hdr (abfd)->loader_fixup_location = 0;
  obj_som_file_hdr (abfd)->loader_fixup_total = 0;
  obj_som_file_hdr (abfd)->som_length = *current_offset;
  return true;
}

static bool
som_begin_writing (bfd *abfd)
{
  unsigned long current_offset = 0;
  unsigned int total_subspaces = 0;

  current_offset += sizeof (struct som_external_header);

  if (!som_write_aux_headers (abfd, &current_offset))
    return false;

  obj_som_file_hdr (abfd)->init_array_location = current_offset;
  obj_som_file_hdr (abfd)->init_array_total = 0;

  unsigned long num_spaces = som_count_spaces (abfd);
  unsigned long num_subspaces = som_count_subspaces (abfd);
  som_layout_dictionaries (abfd, &current_offset, num_spaces, num_subspaces);

  if (!som_write_space_string_table (abfd, &current_offset))
    return false;

  som_layout_compilation_unit (abfd, &current_offset);

  som_layout_loadable_subspaces (abfd, num_spaces, &current_offset, &total_subspaces);

  som_layout_unloadable_subspaces (abfd, num_spaces, &current_offset, &total_subspaces);

  if (!som_finalize_file (abfd, &current_offset))
    return false;

  return true;
}

/* Finally, scribble out the various headers to the disk.  */

static file_ptr
align_to_word (file_ptr offset)
{
  return (offset + 3) & ~3;
}

static void
set_version_id (bfd *abfd)
{
  if (obj_som_exec_data (abfd) && obj_som_exec_data (abfd)->version_id)
    obj_som_file_hdr (abfd)->version_id = obj_som_exec_data (abfd)->version_id;
  else
    obj_som_file_hdr (abfd)->version_id = NEW_VERSION_ID;
}

static bool
layout_symbols_and_fixups (bfd *abfd, file_ptr *current_offset)
{
  asymbol **syms = bfd_get_outsymbols (abfd);
  int num_syms = bfd_get_symcount (abfd);
  unsigned int strings_size;
  unsigned int total_reloc_size;

  *current_offset = align_to_word (*current_offset);
  obj_som_file_hdr (abfd)->symbol_location = *current_offset;
  obj_som_file_hdr (abfd)->symbol_total = num_syms;
  *current_offset += num_syms * sizeof (struct som_external_symbol_dictionary_record);

  *current_offset = align_to_word (*current_offset);
  obj_som_file_hdr (abfd)->symbol_strings_location = *current_offset;

  if (!som_write_symbol_strings (abfd, *current_offset, syms, num_syms,
				 &strings_size, obj_som_compilation_unit (abfd)))
    return false;

  obj_som_file_hdr (abfd)->symbol_strings_size = strings_size;
  *current_offset += strings_size;

  if (!som_prep_for_fixups (abfd, syms, num_syms))
    return false;

  *current_offset = align_to_word (*current_offset);
  obj_som_file_hdr (abfd)->fixup_request_location = *current_offset;

  if (!som_write_fixups (abfd, *current_offset, &total_reloc_size))
    return false;

  obj_som_file_hdr (abfd)->fixup_request_total = total_reloc_size;
  *current_offset += total_reloc_size;

  return true;
}

static bool
write_subspaces_of_type (bfd *abfd, int num_spaces, int *subspace_index, bool loadable)
{
  asection *section = abfd->sections;
  for (int i = 0; i < num_spaces; i++)
    {
      while (section && !som_is_space (section))
	section = section->next;
      if (!section)
	return false;

      for (asection *subsection = abfd->sections; subsection != NULL; subsection = subsection->next)
	{
	  bool is_loadable_subsection = (subsection->flags & SEC_ALLOC) != 0;
	  if (!som_is_subspace (subsection)
	      || !som_is_container (section, subsection)
	      || is_loadable_subsection != loadable)
	    continue;

	  struct som_external_subspace_dictionary_record ext_subspace_dict;
	  struct space_dictionary_record *space_dict = som_section_data(section)->space_dict;

	  if (space_dict->subspace_quantity == 0)
	    {
	      space_dict->is_loadable = loadable;
	      space_dict->subspace_index = *subspace_index;
	    }

	  space_dict->subspace_quantity++;
	  (*subspace_index)++;

	  som_section_data(subsection)->subspace_dict->space_index = i;

	  som_swap_subspace_dictionary_record_out (som_section_data(subsection)->subspace_dict, &ext_subspace_dict);
	  size_t amt = sizeof (struct som_subspace_dictionary_record);
	  if (bfd_write (&ext_subspace_dict, amt, abfd) != amt)
	    return false;
	}
      section = section->next;
    }
  return true;
}

static bool
write_space_dicts (bfd *abfd, int num_spaces)
{
  if (bfd_seek (abfd, obj_som_file_hdr (abfd)->space_location, SEEK_SET) != 0)
    return false;

  asection *section = abfd->sections;
  for (int i = 0; i < num_spaces; i++)
    {
      struct som_external_space_dictionary_record ext_space_dict;

      while (section && !som_is_space (section))
	section = section->next;
      if (!section)
	return false;

      som_swap_space_dictionary_out (som_section_data (section)->space_dict, &ext_space_dict);
      size_t amt = sizeof (struct som_external_space_dictionary_record);
      if (bfd_write (&ext_space_dict, amt, abfd) != amt)
	return false;

      section = section->next;
    }
  return true;
}

static bool
write_dictionary_records (bfd *abfd)
{
  int num_spaces = som_count_spaces (abfd);
  int subspace_index = 0;

  if (bfd_seek (abfd, obj_som_file_hdr (abfd)->subspace_location, SEEK_SET) != 0)
    return false;

  if (!write_subspaces_of_type (abfd, num_spaces, &subspace_index, true))
    return false;

  if (!write_subspaces_of_type (abfd, num_spaces, &subspace_index, false))
    return false;

  return write_space_dicts (abfd, num_spaces);
}

static bool
write_compilation_unit (bfd *abfd)
{
  if (!obj_som_compilation_unit (abfd))
    return true;

  struct som_external_compilation_unit ext_comp_unit;

  if (bfd_seek (abfd, obj_som_file_hdr (abfd)->compiler_location, SEEK_SET) != 0)
    return false;

  som_swap_compilation_unit_out (obj_som_compilation_unit (abfd), &ext_comp_unit);

  size_t amt = sizeof (struct som_external_compilation_unit);
  return bfd_write (&ext_comp_unit, amt, abfd) == amt;
}

static void
set_system_id (bfd *abfd)
{
  if ((abfd->flags & (EXEC_P | DYNAMIC)) && obj_som_exec_data (abfd))
    obj_som_file_hdr (abfd)->system_id = obj_som_exec_data (abfd)->system_id;
  else if (bfd_get_mach (abfd) == pa20)
    obj_som_file_hdr (abfd)->system_id = CPU_PA_RISC2_0;
  else if (bfd_get_mach (abfd) == pa11)
    obj_som_file_hdr (abfd)->system_id = CPU_PA_RISC1_1;
  else
    obj_som_file_hdr (abfd)->system_id = CPU_PA_RISC1_0;
}

static bool
write_exec_header_if_needed (bfd *abfd)
{
  if (!(abfd->flags & (EXEC_P | DYNAMIC)))
    return true;

  struct som_exec_auxhdr *exec_header = obj_som_exec_hdr (abfd);
  struct som_external_exec_auxhdr ext_exec_header;
  long tmp;

  exec_header->exec_entry = bfd_get_start_address (abfd);
  if (obj_som_exec_data (abfd))
    exec_header->exec_flags = obj_som_exec_data (abfd)->exec_flags;

  tmp = exec_header->exec_dsize;
  tmp = SOM_ALIGN (tmp, PA_PAGESIZE);
  exec_header->exec_bsize -= (tmp - exec_header->exec_dsize);
  if (exec_header->exec_bsize < 0)
    exec_header->exec_bsize = 0;
  exec_header->exec_dsize = tmp;

  long som_length = obj_som_file_hdr (abfd)->som_length;
  if (exec_header->exec_tfile + exec_header->exec_tsize > som_length
      || exec_header->exec_dfile + exec_header->exec_dsize > som_length)
    {
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  som_swap_exec_auxhdr_out (exec_header, &ext_exec_header);

  if (bfd_seek (abfd, obj_som_file_hdr (abfd)->aux_header_location, SEEK_SET) != 0)
    return false;

  size_t amt = sizeof (ext_exec_header);
  return bfd_write (&ext_exec_header, amt, abfd) == amt;
}

static bool
write_final_headers (bfd *abfd)
{
  struct som_external_header ext_header;
  size_t amt;

  set_system_id (abfd);

  som_swap_header_out (obj_som_file_hdr (abfd), &ext_header);
  bfd_putb32 (som_compute_checksum (&ext_header), ext_header.checksum);

  if (bfd_seek (abfd, 0, SEEK_SET) != 0)
    return false;

  amt = sizeof (struct som_external_header);
  if (bfd_write (&ext_header, amt, abfd) != amt)
    return false;

  return write_exec_header_if_needed (abfd);
}

static bool
som_finish_writing (bfd *abfd)
{
  file_ptr current_offset;

  set_version_id (abfd);

  current_offset = obj_som_file_hdr (abfd)->som_length;
  if (!layout_symbols_and_fixups (abfd, &current_offset))
    return false;

  obj_som_file_hdr (abfd)->som_length = current_offset;

  if (!som_build_and_write_symbol_table (abfd))
    return false;

  if (!write_dictionary_records (abfd))
    return false;

  if (!write_compilation_unit (abfd))
    return false;

  return write_final_headers (abfd);
}

/* Compute and return the checksum for a SOM file header.  */

static uint32_t
som_compute_checksum(const struct som_external_header *hdr)
{
    if (hdr == NULL) {
        return 0;
    }

    uint32_t checksum = 0;
    const unsigned char *buffer = (const unsigned char *)hdr;
    
    for (size_t i = 0; i < sizeof(*hdr); i += sizeof(uint32_t)) {
        uint32_t word;
        memcpy(&word, buffer + i, sizeof(uint32_t));
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

  if (sym->flags & BSF_SECTION_SYM)
    {
      info->symbol_type = ST_DATA;
    }
  else
    {
      const struct som_symbol_data_struct *som_data = som_symbol_data (sym);
      const symbol_type_class som_type = som_data->som_type;
      const bfd_boolean is_function = (sym->flags & BSF_FUNCTION) != 0;

      if (bfd_is_com_section (sym->section))
	{
	  info->symbol_type = ST_STORAGE;
	  info->symbol_scope = SS_UNSAT;
	}
      else if ((som_type == SYMBOL_TYPE_UNKNOWN || som_type == SYMBOL_TYPE_CODE)
	       && bfd_is_und_section (sym->section)
	       && is_function)
	{
	  info->symbol_type = ST_CODE;
	}
      else if (som_type == SYMBOL_TYPE_ENTRY
	       || (is_function && (som_type == SYMBOL_TYPE_CODE
				   || som_type == SYMBOL_TYPE_UNKNOWN)))
	{
	  info->symbol_type = ST_ENTRY;
	  info->arg_reloc = som_data->tc_data.ap.hppa_arg_reloc;
	  info->priv_level= som_data->tc_data.ap.hppa_priv_level;
	}
      else if (som_type == SYMBOL_TYPE_UNKNOWN)
	{
	  if (bfd_is_abs_section (sym->section))
	    info->symbol_type = ST_ABSOLUTE;
	  else if (sym->section->flags & SEC_CODE)
	    info->symbol_type = ST_CODE;
	  else
	    info->symbol_type = ST_DATA;
	}
      else
	{
	  switch (som_type)
	    {
	    case SYMBOL_TYPE_ABSOLUTE:  info->symbol_type = ST_ABSOLUTE;  break;
	    case SYMBOL_TYPE_CODE:      info->symbol_type = ST_CODE;      break;
	    case SYMBOL_TYPE_DATA:      info->symbol_type = ST_DATA;      break;
	    case SYMBOL_TYPE_MILLICODE: info->symbol_type = ST_MILLICODE; break;
	    case SYMBOL_TYPE_PLABEL:    info->symbol_type = ST_PLABEL;    break;
	    case SYMBOL_TYPE_PRI_PROG:  info->symbol_type = ST_PRI_PROG;  break;
	    case SYMBOL_TYPE_SEC_PROG:  info->symbol_type = ST_SEC_PROG;  break;
	    default:
	      break;
	    }
	}
    }

  if (!bfd_is_com_section (sym->section))
    {
      if (bfd_is_und_section (sym->section))
	info->symbol_scope = SS_UNSAT;
      else if (sym->flags & (BSF_EXPORT | BSF_WEAK))
	info->symbol_scope = SS_UNIVERSAL;
      else
	info->symbol_scope = SS_LOCAL;
    }

  const bfd_boolean is_special_section =
    bfd_is_com_section (sym->section)
    || bfd_is_und_section (sym->section)
    || bfd_is_abs_section (sym->section);

  info->symbol_info = is_special_section ? 0 : sym->section->target_index;

  info->symbol_value = sym->value + sym->section->vma;

  info->secondary_def = (sym->flags & BSF_WEAK) != 0;

  const struct som_section_data_struct *sec_data = som_section_data (sym->section);
  if (sec_data && sec_data->subspace_dict)
    {
      const bfd_boolean is_relevant_type = (info->symbol_type == ST_ENTRY
					    || info->symbol_type == ST_CODE
					    || info->symbol_type == ST_DATA);

      if (info->symbol_scope == SS_UNIVERSAL && is_relevant_type)
	{
	  const struct som_subspace_dict_struct *subspace = sec_data->subspace_dict;
	  info->is_comdat = subspace->is_comdat;
	  info->is_common = subspace->is_common;
	  info->dup_common = subspace->dup_common;
	}
    }
}

/* Build and write, in one big chunk, the entire symbol table for
   this BFD.  */

static void
populate_som_symbol_record (bfd *abfd,
			    struct som_external_symbol_dictionary_record *som_sym,
			    asymbol *bfd_sym)
{
  struct som_misc_symbol_info info;
  unsigned int flags;

  bfd_putb32 (som_symbol_data (bfd_sym)->stringtab_offset, som_sym->name);

  som_bfd_derive_misc_symbol_info (abfd, bfd_sym, &info);

  flags = (info.symbol_type << SOM_SYMBOL_TYPE_SH)
    | (info.symbol_scope << SOM_SYMBOL_SCOPE_SH)
    | (info.arg_reloc << SOM_SYMBOL_ARG_RELOC_SH)
    | (3 << SOM_SYMBOL_XLEAST_SH)
    | (info.secondary_def ? SOM_SYMBOL_SECONDARY_DEF : 0)
    | (info.is_common ? SOM_SYMBOL_IS_COMMON : 0)
    | (info.dup_common ? SOM_SYMBOL_DUP_COMMON : 0);
  bfd_putb32 (flags, som_sym->flags);

  flags = (info.symbol_info << SOM_SYMBOL_SYMBOL_INFO_SH)
    | (info.is_comdat ? SOM_SYMBOL_IS_COMDAT : 0);
  bfd_putb32 (flags, som_sym->info);

  bfd_putb32 (info.symbol_value | info.priv_level, som_sym->symbol_value);
}

static bool
som_build_and_write_symbol_table (bfd *abfd)
{
  unsigned int num_syms = bfd_get_symcount (abfd);
  if (num_syms == 0)
    return true;

  bfd_size_type symtab_size;
  if (_bfd_mul_overflow (num_syms,
			 sizeof (struct som_external_symbol_dictionary_record),
			 &symtab_size))
    {
      bfd_set_error (bfd_error_no_memory);
      return false;
    }

  struct som_external_symbol_dictionary_record *som_symtab =
    bfd_zmalloc (symtab_size);
  if (som_symtab == NULL)
    return false;

  asymbol **bfd_syms = obj_som_sorted_syms (abfd);
  for (unsigned int i = 0; i < num_syms; i++)
    {
      populate_som_symbol_record (abfd, &som_symtab[i], bfd_syms[i]);
    }

  bool success = false;
  file_ptr symtab_location = obj_som_file_hdr (abfd)->symbol_location;
  if (bfd_seek (abfd, symtab_location, SEEK_SET) == 0
      && bfd_write (som_symtab, symtab_size, abfd) == symtab_size)
    {
      success = true;
    }

  free (som_symtab);
  return success;
}

/* Write an object in SOM format.  */

static bool
som_write_object_contents (bfd *abfd)
{
  if (!abfd)
    {
      return false;
    }

  if (!abfd->output_has_begun)
    {
      if (!som_prep_headers (abfd) || !som_begin_writing (abfd))
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
  if (obj_som_stringtab (abfd) != NULL)
    {
      return true;
    }

  const bfd_size_type amt = obj_som_stringtab_size (abfd);

  if (amt == 0)
    {
      bfd_set_error (bfd_error_no_symbols);
      return false;
    }

  if (amt == (bfd_size_type) -1)
    {
      bfd_set_error (bfd_error_no_memory);
      return false;
    }

  if (bfd_seek (abfd, obj_som_str_filepos (abfd), SEEK_SET) != 0)
    {
      return false;
    }

  char *stringtab = _bfd_malloc_and_read (abfd, amt + 1, amt);
  if (stringtab == NULL)
    {
      return false;
    }

  stringtab[amt] = '\0';

  obj_som_stringtab (abfd) = stringtab;
  return true;
}

/* Return the amount of data (in bytes) required to hold the symbol
   table for this object.  */

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

  unsigned long num_pointers = (unsigned long)sym_count + 1;
  const unsigned long pointer_size = sizeof (asymbol *);
  const unsigned long max_size = (unsigned long)LONG_MAX;

  if (num_pointers > max_size / pointer_size)
    {
      return -1;
    }

  return (long)(num_pointers * pointer_size);
}

/* Convert from a SOM subspace index to a BFD section.  */

asection *
bfd_section_from_som_symbol
  (bfd *abfd, struct som_external_symbol_dictionary_record *symbol)
{
  const unsigned int flags = bfd_getb32 (symbol->flags);
  const unsigned int symbol_type = (flags >> SOM_SYMBOL_TYPE_SH) & SOM_SYMBOL_TYPE_MASK;
  const int is_executable_or_dynamic = (abfd->flags & (EXEC_P | DYNAMIC)) != 0;
  const int is_function_symbol = (symbol_type == ST_ENTRY
                                || symbol_type == ST_PRI_PROG
                                || symbol_type == ST_SEC_PROG
                                || symbol_type == ST_MILLICODE);

  if (is_executable_or_dynamic && is_function_symbol)
    {
      const bfd_vma value = bfd_getb32 (symbol->symbol_value);
      for (asection *section = abfd->sections; section; section = section->next)
        {
          if (som_is_subspace (section)
              && value >= section->vma
              && (value - section->vma) <= section->size)
            {
              return section;
            }
        }
    }
  else
    {
      const int idx = (bfd_getb32 (symbol->info) >> SOM_SYMBOL_SYMBOL_INFO_SH)
                    & SOM_SYMBOL_SYMBOL_INFO_MASK;
      for (asection *section = abfd->sections; section; section = section->next)
        {
          if (som_is_subspace (section) && section->target_index == idx)
            {
              return section;
            }
        }
    }

  return bfd_abs_section_ptr;
}

/* Read and save the symbol table associated with the given BFD.  */

static unsigned int
som_slurp_symbol_table (bfd *abfd)
{
  unsigned int symbol_count;
  struct som_external_symbol_dictionary_record *buf = NULL;
  som_symbol_type *symbase = NULL;
  bool success = false;

  if (obj_som_symtab (abfd) != NULL)
    return true;

  symbol_count = bfd_get_symcount (abfd);
  if (symbol_count == 0)
    return true;

  if (!som_slurp_string_table (abfd))
    return false;

  char *stringtab = obj_som_stringtab (abfd);
  size_t amt;

  if (_bfd_mul_overflow (symbol_count, sizeof (struct som_external_symbol_dictionary_record), &amt))
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

  const struct som_external_symbol_dictionary_record *endbufp = buf + symbol_count;
  som_symbol_type *sym = symbase;
  for (const struct som_external_symbol_dictionary_record *bufp = buf;
       bufp < endbufp; ++bufp)
    {
      unsigned int flags = bfd_getb32 (bufp->flags);
      unsigned int symbol_type =
	(flags >> SOM_SYMBOL_TYPE_SH) & SOM_SYMBOL_TYPE_MASK;
      unsigned int symbol_scope =
	(flags >> SOM_SYMBOL_SCOPE_SH) & SOM_SYMBOL_SCOPE_MASK;

      if (symbol_type == ST_SYM_EXT || symbol_type == ST_ARG_EXT)
	continue;

      switch (symbol_type)
	{
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
	case ST_NULL:
	default:
	  som_symbol_data (sym)->som_type = SYMBOL_TYPE_UNKNOWN;
	  break;
	}

      som_symbol_data (sym)->tc_data.ap.hppa_arg_reloc =
	(flags >> SOM_SYMBOL_ARG_RELOC_SH) & SOM_SYMBOL_ARG_RELOC_MASK;

      sym->symbol.the_bfd = abfd;
      bfd_vma offset = bfd_getb32 (bufp->name);
      if (offset >= obj_som_stringtab_size (abfd))
	{
	  bfd_set_error (bfd_error_bad_value);
	  goto cleanup;
	}
      sym->symbol.name = stringtab + offset;
      sym->symbol.value = bfd_getb32 (bufp->symbol_value);
      sym->symbol.section = NULL;
      sym->symbol.flags = 0;

      bool is_code_like = false;
      switch (symbol_type)
	{
	case ST_ENTRY:
	case ST_MILLICODE:
	  sym->symbol.flags |= BSF_FUNCTION;
	  is_code_like = true;
	  break;
	case ST_STUB:
	case ST_CODE:
	case ST_PRI_PROG:
	case ST_SEC_PROG:
	  if (symbol_scope == SS_UNSAT)
	    sym->symbol.flags |= BSF_FUNCTION;
	  is_code_like = true;
	  break;
	default:
	  break;
	}

      if (is_code_like)
	{
	  som_symbol_data (sym)->tc_data.ap.hppa_priv_level =
	    sym->symbol.value & 0x3;
	  sym->symbol.value &= ~0x3;
	}

      switch (symbol_scope)
	{
	case SS_EXTERNAL:
	  sym->symbol.flags |= (BSF_EXPORT | BSF_GLOBAL);
	case SS_UNSAT:
	  sym->symbol.section = (symbol_type != ST_STORAGE)
	    ? bfd_und_section_ptr : bfd_com_section_ptr;
	  break;
	case SS_UNIVERSAL:
	case SS_LOCAL:
	  if (symbol_scope == SS_UNIVERSAL)
	    sym->symbol.flags |= (BSF_EXPORT | BSF_GLOBAL);
	  else
	    sym->symbol.flags |= BSF_LOCAL;
	  sym->symbol.section = bfd_section_from_som_symbol (abfd, bufp);
	  if (sym->symbol.section)
	    sym->symbol.value -= sym->symbol.section->vma;
	  else
	    sym->symbol.section = bfd_und_section_ptr;
	  break;
	default:
	  sym->symbol.section = bfd_und_section_ptr;
	  break;
	}

      if (flags & SOM_SYMBOL_SECONDARY_DEF)
	sym->symbol.flags |= BSF_WEAK;

      if (sym->symbol.name[0] == '$'
	  && sym->symbol.name[strlen (sym->symbol.name) - 1] == '$'
	  && sym->symbol.section
	  && !strcmp (sym->symbol.name, sym->symbol.section->name))
	sym->symbol.flags |= BSF_SECTION_SYM;
      else if (startswith (sym->symbol.name, "L$0\002"))
	{
	  sym->symbol.flags |= BSF_SECTION_SYM;
	  if (sym->symbol.section)
	    sym->symbol.name = sym->symbol.section->name;
	}
      else if (startswith (sym->symbol.name, "L$0\001"))
	sym->symbol.flags |= BSF_DEBUGGING;

      sym++;
    }

  abfd->symcount = sym - symbase;
  obj_som_symtab (abfd) = symbase;
  success = true;

cleanup:
  free (buf);
  if (!success)
    free (symbase);
  return success;
}

/* Canonicalize a SOM symbol table.  Return the number of entries
   in the symbol table.  */

static long
som_canonicalize_symtab (bfd *abfd, asymbol **location)
{
  if (!som_slurp_symbol_table (abfd))
    {
      return -1;
    }

  long symcount = bfd_get_symcount (abfd);
  if (symcount < 0)
    {
      return -1;
    }

  if (symcount > 0)
    {
      som_symbol_type *symbase = obj_som_symtab (abfd);
      for (long i = 0; i < symcount; ++i)
        {
          location[i] = &symbase[i].symbol;
        }
    }

  location[symcount] = NULL;

  return symcount;
}

/* Make a SOM symbol.  There is nothing special to do here.  */

static asymbol *
som_make_empty_symbol (bfd *abfd)
{
  som_symbol_type *new_symbol_type = bfd_zalloc (abfd, sizeof (*new_symbol_type));

  if (new_symbol_type == NULL)
    {
      return NULL;
    }

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
  FILE *file = (FILE *) afile;

  if (file == NULL || symbol == NULL)
    {
      return;
    }

  const char *name = symbol->name ? symbol->name : "(*no name*)";

  switch (how)
    {
    case bfd_print_symbol_name:
      fprintf (file, "%s", name);
      break;

    case bfd_print_symbol_more:
      fprintf (file, "som %08" PRIx64 " %x",
	       (uint64_t) symbol->value, symbol->flags);
      break;

    case bfd_print_symbol_all:
      {
	const char *section_name = symbol->section ? symbol->section->name : "(*none*)";
	bfd_print_symbol_vandf (abfd, afile, symbol);
	fprintf (file, " %s\t%s", section_name, name);
	break;
      }

    default:
      break;
    }
}

static bool
som_bfd_is_local_label_name (bfd *abfd ATTRIBUTE_UNUSED,
			     const char *name)
{
  return name != NULL && name[0] == 'L' && name[1] == '$';
}

/* Count or process variable-length SOM fixup records.

   To avoid code duplication we use this code both to compute the number
   of relocations requested by a stream, and to internalize the stream.

   When computing the number of relocations requested by a stream the
   variables rptr, section, and symbols have no meaning.

   Return the number of relocations requested by the fixup stream.  When
   not just counting

   This needs at least two or three more passes to get it cleaned up.  */

#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <ctype.h>

#define STACK_CAPACITY 20
#define VARIABLES_COUNT 26
#define RELOC_QUEUE_CAPACITY 16
#define FIXUP_FORMATS_CAPACITY 256
#define HPPA_HOWTO_TABLE_CAPACITY 256

static bool
stack_push (int **sp, int *stack_end, int value)
{
  if (*sp >= stack_end)
    {
      return false;
    }
  *(*sp)++ = value;
  return true;
}

static bool
stack_pop (int **sp, int *stack_start, int *value)
{
  if (*sp <= stack_start)
    {
      return false;
    }
  *value = *--(*sp);
  return true;
}

static unsigned int
decode_call_reloc_bits (unsigned int op, unsigned int r_val)
{
  unsigned int addend = 0;
  unsigned int tmp = r_val;

  if ((som_hppa_howto_table[op].type == R_PCREL_CALL
       && op < R_PCREL_CALL + 10)
      || (som_hppa_howto_table[op].type == R_ABS_CALL
	  && op < R_ABS_CALL + 10))
    {
      if (tmp > 4)
	{
	  tmp -= 5;
	  addend |= 1;
	}
      if (tmp >= 4)
	addend |= 1 << 8 | 1 << 6 | 1 << 4 | 1 << 2;
      else if (tmp == 3)
	addend |= 1 << 8 | 1 << 6 | 1 << 4;
      else if (tmp == 2)
	addend |= 1 << 8 | 1 << 6;
      else if (tmp == 1)
	addend |= 1 << 8;
    }
  else
    {
      unsigned int tmp1, tmp2;

      addend = tmp & 0x3;
      tmp >>= 2;

      tmp1 = tmp / 10;
      tmp -= tmp1 * 10;
      if (tmp1 == 9)
	{
	  addend += (0xe << 6);
	}
      else
	{
	  tmp2 = tmp1 / 3;
	  tmp1 -= tmp2 * 3;
	  addend += (tmp2 << 8) + (tmp1 << 6);
	}

      if (tmp == 9)
	{
	  addend += (0xe << 2);
	}
      else
	{
	  tmp2 = tmp / 3;
	  tmp -= tmp2 * 3;
	  addend += (tmp2 << 4) + (tmp << 2);
	}
    }

  return HPPA_R_ADDEND (addend, 0);
}

static bool
get_data_symbol_addend (asection *section,
			unsigned int reloc_offset,
			bool *deallocate_contents,
			bfd_vma *addend_out)
{
  if ((section->flags & SEC_HAS_CONTENTS) == 0)
    {
      return true;
    }

  if (!section->contents)
    {
      bfd_byte *contents = NULL;
      if (!bfd_malloc_and_get_section (section->owner, section, &contents))
	{
	  return false;
	}
      section->contents = contents;
      *deallocate_contents = true;
    }

  if (reloc_offset <= section->size && section->size - reloc_offset >= 4)
    {
      *addend_out = bfd_get_32 (section->owner,
				section->contents + reloc_offset);
    }

  return true;
}

static unsigned int
som_set_reloc_info (unsigned char *fixup,
		    unsigned int end,
		    arelent *internal_relocs,
		    asection *section,
		    asymbol **symbols,
		    unsigned int symcount,
		    bool just_count)
{
  bool deallocate_contents = false;
  unsigned char *const end_fixups = &fixup[end];
  int variables[VARIABLES_COUNT];
  int stack[STACK_CAPACITY];
  int *const stack_start = stack;
  int *const stack_end = stack + STACK_CAPACITY;
  int *sp;
  unsigned int count = 0;
  int saved_unwind_bits = 0;
  arelent *rptr = internal_relocs;
  unsigned int offset = 0;

  som_initialize_reloc_queue (reloc_queue);
  memset (variables, 0, sizeof (variables));
  sp = stack_start;

  while (fixup < end_fixups)
    {
      const char *cp;
      unsigned int op;
      const struct fixup_format *fp;
      unsigned char *save_fixup = fixup;
      bool is_prev_fixup = false;

      op = *fixup++;
      if (op >= FIXUP_FORMATS_CAPACITY)
	return (unsigned int) -1;

      fp = &som_fixup_formats[op];

      if (*fp->format == 'P')
	{
	  if (fp->D < 0 || fp->D >= RELOC_QUEUE_CAPACITY
	      || !reloc_queue[fp->D].reloc)
	    {
	      continue;
	    }
	  fixup = reloc_queue[fp->D].reloc;
	  som_reloc_queue_fix (reloc_queue, fp->D);
	  is_prev_fixup = true;

	  if (fixup >= end_fixups)
	    return (unsigned int) -1;

	  op = *fixup++;
	  if (op >= FIXUP_FORMATS_CAPACITY)
	    return (unsigned int) -1;
	  fp = &som_fixup_formats[op];
	}

      if (op >= HPPA_HOWTO_TABLE_CAPACITY)
	return (unsigned int) -1;
      int reloc_type = som_hppa_howto_table[op].type;

      if (!just_count
	  && reloc_type != R_NO_RELOCATION && reloc_type != R_DATA_OVERRIDE)
	{
	  rptr->address = offset;
	  rptr->howto = &som_hppa_howto_table[op];
	  rptr->addend = 0;
	  rptr->sym_ptr_ptr = &bfd_abs_section_ptr->symbol;
	}

      variables['L' - 'A'] = 0;
      variables['D' - 'A'] = fp->D;
      variables['U' - 'A'] = saved_unwind_bits;

      cp = fp->format;

      while (*cp)
	{
	  char varname = *cp++;
	  int c;

	  do
	    {
	      unsigned int v;
	      c = *cp++;

	      if (isupper (c))
		{
		  if (!stack_push (&sp, stack_end, variables[c - 'A']))
		    return (unsigned int) -1;
		}
	      else if (islower (c))
		{
		  int bits = (c - 'a') * 8;
		  v = 0;
		  for (int i = 'a'; i < c && fixup < end_fixups; i++)
		    v = (v << 8) | *fixup++;
		  if (varname == 'V')
		    v = sign_extend (v, bits);
		  if (!stack_push (&sp, stack_end, v))
		    return (unsigned int) -1;
		}
	      else if (isdigit (c))
		{
		  v = c - '0';
		  while (isdigit (*cp))
		    v = (v * 10) + (*cp++ - '0');
		  if (!stack_push (&sp, stack_end, v))
		    return (unsigned int) -1;
		}
	      else
		{
		  int op1, op2;
		  if (!stack_pop (&sp, stack_start, &op2)
		      || !stack_pop (&sp, stack_start, &op1))
		    return (unsigned int) -1;

		  switch (c)
		    {
		    case '+': v = op1 + op2; break;
		    case '*': v = op1 * op2; break;
		    case '<': v = op1 << op2; break;
		    default: return (unsigned int) -1;
		    }
		  if (!stack_push (&sp, stack_end, v))
		    return (unsigned int) -1;
		}
	    }
	  while (*cp && *cp != '=');

	  cp++;
	  if (!stack_pop (&sp, stack_start, &c))
	    return (unsigned int) -1;

	  variables[varname - 'A'] = c;

	  switch (varname)
	    {
	    case 'L':
	      offset += c;
	      break;
	    case 'S':
	      if (!just_count && symbols != NULL && (unsigned int) c < symcount)
		rptr->sym_ptr_ptr = &symbols[c];
	      break;
	    case 'R':
	      if (!just_count)
		rptr->addend = decode_call_reloc_bits (op, c);
	      break;
	    case 'O':
	      {
		const int *subop;
		switch (op)
		  {
		  case R_COMP1: subop = comp1_opcodes; break;
		  case R_COMP2: subop = comp2_opcodes; break;
		  case R_COMP3: subop = comp3_opcodes; break;
		  default: return (unsigned int) -1;
		  }
		while (*subop != -1 && (unsigned int)*subop <= (unsigned char) c)
		  ++subop;
		if (*subop != -1)
		  --subop;
	      }
	      break;
	    case 'U':
	      saved_unwind_bits = c;
	      break;
	    default:
	      break;
	    }
	}

      if (is_prev_fixup)
	{
	  fixup = save_fixup + 1;
	}
      else if (fixup > save_fixup + 1)
	{
	  som_reloc_queue_insert (save_fixup, fixup - save_fixup,
				  reloc_queue);
	}

      if (reloc_type != R_DATA_OVERRIDE && reloc_type != R_NO_RELOCATION)
	{
	  if (!just_count)
	    {
	      if (reloc_type == R_ENTRY)
		rptr->addend = variables['T' - 'A'];
	      else if (reloc_type == R_EXIT)
		rptr->addend = variables['U' - 'A'];
	      else if (reloc_type == R_PCREL_CALL || reloc_type == R_ABS_CALL)
		{
		}
	      else if (reloc_type == R_DATA_ONE_SYMBOL)
		{
		  bfd_vma addend = variables['V' - 'A'];
		  if (addend == 0)
		    {
		      unsigned int reloc_offset = offset - variables['L' - 'A'];
		      if (!get_data_symbol_addend (section, reloc_offset,
						   &deallocate_contents,
						   &addend))
			{
			  if (deallocate_contents)
			    {
			      free (section->contents);
			      section->contents = NULL;
			    }
			  return (unsigned int) -1;
			}
		    }
		  rptr->addend = addend;
		}
	      else
		{
		  rptr->addend = variables['V' - 'A'];
		}
	      rptr++;
	    }
	  count++;
	  memset (variables, 0, sizeof (variables));
	  sp = stack_start;
	}
    }
  if (deallocate_contents)
    {
      free (section->contents);
      section->contents = NULL;
    }

  return count;
}

/* Read in the relocs (aka fixups in SOM terms) for a section.

   som_get_reloc_upper_bound calls this routine with JUST_COUNT
   set to TRUE to indicate it only needs a count of the number
   of actual relocations.  */

static bool
som_parse_reloc_stream (bfd *abfd,
			asection *section)
{
  size_t fixup_stream_size = som_section_data (section)->reloc_size;
  unsigned char *external_relocs;

  if (bfd_seek (abfd, obj_som_reloc_filepos (abfd) + section->rel_filepos,
		SEEK_SET) != 0)
    return false;

  external_relocs = _bfd_malloc_and_read (abfd, fixup_stream_size,
					  fixup_stream_size);
  if (external_relocs == NULL)
    return false;

  section->reloc_count = som_set_reloc_info (external_relocs,
					     fixup_stream_size,
					     NULL, NULL, NULL, 0, true);

  som_section_data (section)->reloc_stream = external_relocs;
  return true;
}

static arelent *
som_internalize_relocations (bfd *abfd,
			     asection *section,
			     asymbol **symbols)
{
  unsigned int num_relocs = section->reloc_count;
  unsigned char *external_relocs = som_section_data (section)->reloc_stream;
  unsigned int fixup_stream_size = som_section_data (section)->reloc_size;
  size_t amt;
  arelent *internal_relocs;

  if (_bfd_mul_overflow (num_relocs, sizeof (arelent), &amt))
    {
      bfd_set_error (bfd_error_file_too_big);
      return NULL;
    }

  internal_relocs = bfd_zalloc (abfd, amt);
  if (internal_relocs == NULL)
    return NULL;

  som_set_reloc_info (external_relocs, fixup_stream_size,
		      internal_relocs, section, symbols,
		      bfd_get_symcount (abfd), false);

  free (external_relocs);
  som_section_data (section)->reloc_stream = NULL;

  return internal_relocs;
}

static bool
som_slurp_reloc_table (bfd *abfd,
		       asection *section,
		       asymbol **symbols,
		       bool just_count)
{
  if (section->reloc_count == 0)
    return true;

  if (section->reloc_count == (unsigned) -1)
    {
      if (!som_parse_reloc_stream (abfd, section))
	return false;
    }

  if (just_count || section->relocation != NULL)
    return true;

  arelent *internal_relocs =
    som_internalize_relocations (abfd, section, symbols);
  if (internal_relocs == NULL)
    return false;

  section->relocation = internal_relocs;
  return true;
}

/* Return the number of bytes required to store the relocation
   information associated with the given section.  */

static long
som_get_reloc_upper_bound (bfd *abfd, sec_ptr asect)
{
  if ((asect->flags & SEC_RELOC) == 0)
    {
      return sizeof (arelent *);
    }

  if (!som_slurp_reloc_table (abfd, asect, NULL, true))
    {
      return -1;
    }

  return (asect->reloc_count + 1) * sizeof (arelent *);
}

/* Convert relocations from SOM (external) form into BFD internal
   form.  Return the number of relocations.  */

static long
som_canonicalize_reloc (bfd *abfd,
			sec_ptr section,
			arelent **relptr,
			asymbol **symbols)
{
  if (section == NULL || relptr == NULL)
    {
      return -1;
    }

  if (!som_slurp_reloc_table (abfd, section, symbols, false))
    {
      return -1;
    }

  const long reloc_count = section->reloc_count;
  arelent * const relocations = section->relocation;

  for (long i = 0; i < reloc_count; i++)
    {
      relptr[i] = &relocations[i];
    }

  relptr[reloc_count] = NULL;

  return reloc_count;
}

extern const bfd_target hppa_som_vec;

/* A hook to set up object file dependent section information.  */

static bool
som_new_section_hook (bfd *abfd, asection *newsect)
{
  const unsigned int default_alignment_power = 3;

  newsect->used_by_bfd = bfd_zalloc (abfd, sizeof (struct som_section_data_struct));
  if (newsect->used_by_bfd == NULL)
    {
      return false;
    }

  newsect->alignment_power = default_alignment_power;

  /* We allow more than three sections internally.  */
  return _bfd_generic_new_section_hook (abfd, newsect);
}

/* Copy any private info we understand from the input symbol
   to the output symbol.  */

static bool
som_bfd_copy_private_symbol_data (const bfd *ibfd,
				  const asymbol *isymbol,
				  const bfd *obfd,
				  asymbol *osymbol)
{
  if (!ibfd || !isymbol || !obfd || !osymbol
      || !ibfd->xvec || !obfd->xvec)
    return false;

  if (ibfd->xvec->flavour != bfd_target_som_flavour
      || obfd->xvec->flavour != bfd_target_som_flavour)
    return false;

  const struct som_symbol *input_symbol = (const struct som_symbol *) isymbol;
  struct som_symbol *output_symbol = (struct som_symbol *) osymbol;

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
      || !(som_is_space (isection) || som_is_subspace (isection)))
    {
      return true;
    }

  const size_t data_size = sizeof (struct som_copyable_section_data_struct);
  struct som_section_data_struct *osec_data = som_section_data (osection);

  osec_data->copy_data = bfd_zalloc (obfd, data_size);
  if (osec_data->copy_data == NULL)
    {
      return false;
    }

  struct som_section_data_struct *isec_data = som_section_data (isection);
  if (isec_data->copy_data != NULL)
    {
      memcpy (osec_data->copy_data, isec_data->copy_data, data_size);
    }

  asection *container = osec_data->copy_data->container;
  if (container == NULL)
    {
      return true;
    }

  if (container->output_section == NULL)
    {
      _bfd_error_handler (_("%pB[%pA]: no output section for space %pA"),
                          obfd, osection, container);
      return false;
    }

  osec_data->copy_data->container = container->output_section;
  return true;
}

/* Copy any private info we understand from the input bfd
   to the output bfd.  */

static bool
som_bfd_copy_private_bfd_data (bfd *ibfd, bfd *obfd)
{
  if (ibfd->xvec->flavour != bfd_target_som_flavour
      || obfd->xvec->flavour != bfd_target_som_flavour)
    {
      return true;
    }

  const struct som_exec_data *input_data = obj_som_exec_data (ibfd);
  if (input_data == NULL)
    {
      obj_som_exec_data (obfd) = NULL;
      return true;
    }

  bfd_size_type size = sizeof (struct som_exec_data);
  struct som_exec_data *output_data = bfd_zalloc (obfd, size);

  if (output_data == NULL)
    {
      return false;
    }

  obj_som_exec_data (obfd) = output_data;
  memcpy (output_data, input_data, size);

  return true;
}

/* Display the SOM header.  */

static bool
som_bfd_print_private_bfd_data (bfd *abfd, void *farg)
{
  if (!farg)
    {
      return false;
    }
  FILE *f = (FILE *) farg;

  struct som_exec_auxhdr *exec_header = obj_som_exec_hdr (abfd);
  if (!exec_header)
    {
      return true;
    }

  fprintf (f, _("\nExec Auxiliary Header\n"));

  struct som_aux_id *auxhdr = &exec_header->som_auxhdr;
  fprintf (f, "  %-18s ", "flags");
  if (auxhdr->mandatory)
    {
      fputs ("mandatory ", f);
    }
  if (auxhdr->copy)
    {
      fputs ("copy ", f);
    }
  if (auxhdr->append)
    {
      fputs ("append ", f);
    }
  if (auxhdr->ignore)
    {
      fputs ("ignore ", f);
    }
  fputc ('\n', f);

  fprintf (f, "  %-18s %#x\n", "type", auxhdr->type);
  fprintf (f, "  %-18s %#x\n", "length", auxhdr->length);

  struct
  {
    const char *label;
    unsigned long value;
  }
  const long_fields[] =
  {
    { "text size", (unsigned long) exec_header->exec_tsize },
    { "text memory offset", (unsigned long) exec_header->exec_tmem },
    { "text file offset", (unsigned long) exec_header->exec_tfile },
    { "data size", (unsigned long) exec_header->exec_dsize },
    { "data memory offset", (unsigned long) exec_header->exec_dmem },
    { "data file offset", (unsigned long) exec_header->exec_dfile },
    { "bss size", (unsigned long) exec_header->exec_bsize },
    { "entry point", (unsigned long) exec_header->exec_entry },
    { "loader flags", (unsigned long) exec_header->exec_flags },
    { "bss initializer", (unsigned long) exec_header->exec_bfill }
  };

  for (size_t i = 0; i < sizeof (long_fields) / sizeof (long_fields[0]); ++i)
    {
      fprintf (f, "  %-18s %#lx\n", long_fields[i].label,
               long_fields[i].value);
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
  struct som_section_data_struct *som_data = som_section_data (section);
  struct som_copyable_section_data_struct *copy_data = som_data->copy_data;

  if (copy_data == NULL)
    {
      copy_data = bfd_zalloc (section->owner,
			      sizeof (struct som_copyable_section_data_struct));
      if (copy_data == NULL)
	return false;
      som_data->copy_data = copy_data;
    }

  copy_data->sort_key = sort_key;
  copy_data->is_defined = defined;
  copy_data->is_private = private;
  copy_data->container = section;
  copy_data->space_number = spnum;

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
  struct som_section_data_struct *ssd = som_section_data (section);
  struct som_copyable_section_data_struct *copy_data = ssd->copy_data;

  if (copy_data == NULL)
    {
      copy_data = bfd_zalloc (section->owner,
			      sizeof (struct som_copyable_section_data_struct));
      if (copy_data == NULL)
	return false;
      ssd->copy_data = copy_data;
    }

  copy_data->sort_key = sort_key;
  copy_data->access_control_bits = access_ctr;
  copy_data->quadrant = quadrant;
  copy_data->container = container;
  copy_data->is_comdat = comdat;
  copy_data->is_common = common;
  copy_data->dup_common = dup_common;

  return true;
}

/* Set the full SOM symbol type.  SOM needs far more symbol information
   than any other object file format I'm aware of.  It is mandatory
   to be able to know if a symbol is an entry point, millicode, data,
   code, absolute, storage request, or procedure label.  If you get
   the symbol type wrong your program will not link.  */

void bfd_som_set_symbol_type(asymbol *symbol, unsigned int type)
{
    if (symbol != NULL)
    {
        void *data = som_symbol_data(symbol);
        if (data != NULL)
        {
            ((struct bfd_symbol_data *)data)->som_type = type;
        }
    }
}

/* Attach an auxiliary header to the BFD backend so that it may be
   written into the object file.  */

bool
bfd_som_attach_aux_hdr (bfd *abfd, int type, char *string)
{
  struct som_string_auxhdr **hdr_ptr;

  if (string == NULL)
    return false;

  switch (type)
    {
    case VERSION_AUX_ID:
      hdr_ptr = &obj_som_version_hdr (abfd);
      break;
    case COPYRIGHT_AUX_ID:
      hdr_ptr = &obj_som_copyright_hdr (abfd);
      break;
    default:
      return true;
    }

  size_t len = strlen (string);
  size_t pad = (4 - (len & 3)) & 3;
  size_t padded_len;

  if (__builtin_add_overflow (len, pad, &padded_len))
    return false;

  size_t amt;
  if (__builtin_add_overflow (sizeof (struct som_string_auxhdr),
			      padded_len, &amt))
    return false;

  *hdr_ptr = bfd_zalloc (abfd, amt);
  if (*hdr_ptr == NULL)
    return false;

  (*hdr_ptr)->header_id.type = type;
  (*hdr_ptr)->header_id.length = sizeof ((*hdr_ptr)->string_length) + padded_len;
  (*hdr_ptr)->string_length = len;
  memcpy ((*hdr_ptr)->string, string, len);

  return true;
}

/* Attach a compilation unit header to the BFD backend so that it may be
   written into the object file.  */

static bool
bfd_som_strdup_field (bfd *abfd, char **dest, const char *src)
{
  if (src == NULL)
    {
      *dest = NULL;
      return true;
    }

  size_t len = strlen (src);
  *dest = (char *) bfd_alloc (abfd, (bfd_size_type) len + 1);
  if (*dest == NULL)
    {
      return false;
    }

  memcpy (*dest, src, len + 1);
  return true;
}

bool
bfd_som_attach_compilation_unit (bfd *abfd,
				 const char *name,
				 const char *language_name,
				 const char *product_id,
				 const char *version_id)
{
  struct som_compilation_unit *unit;

  unit = (struct som_compilation_unit *) bfd_zalloc
    (abfd, (bfd_size_type) sizeof (*unit));
  if (unit == NULL)
    {
      return false;
    }

  if (bfd_som_strdup_field (abfd, &unit->name.name, name)
      && bfd_som_strdup_field (abfd, &unit->language_name.name, language_name)
      && bfd_som_strdup_field (abfd, &unit->product_id.name, product_id)
      && bfd_som_strdup_field (abfd, &unit->version_id.name, version_id))
    {
      obj_som_compilation_unit (abfd) = unit;
      return true;
    }

  return false;
}

static bool
som_get_section_contents (bfd *abfd,
			  sec_ptr section,
			  void *location,
			  file_ptr offset,
			  bfd_size_type count)
{
  if (count == 0 || (section->flags & SEC_HAS_CONTENTS) == 0)
    {
      return true;
    }

  if ((bfd_size_type) offset > section->size
      || count > section->size - (bfd_size_type) offset)
    {
      return false;
    }

  if (bfd_seek (abfd, section->filepos + offset, SEEK_SET) != 0)
    {
      return false;
    }

  return bfd_read (location, count, abfd) == count;
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
      som_begin_writing (abfd);
      abfd->output_has_begun = true;
    }

  const bool is_writable_subspace = som_is_subspace (section)
    && ((section->flags & SEC_HAS_CONTENTS) != 0);

  if (!is_writable_subspace)
    {
      return true;
    }

  offset += som_section_data (section)->subspace_dict->file_loc_init_value;

  if (bfd_seek (abfd, offset, SEEK_SET) != 0)
    {
      return false;
    }

  return bfd_write (location, count, abfd) == count;
}

static bool
som_set_arch_mach (bfd *abfd,
                   enum bfd_architecture arch,
                   unsigned long machine)
{
  return bfd_default_set_arch_mach (abfd, arch, machine);
}

static asymbol *
find_function_for_offset (asymbol **symbols, asection *section, bfd_vma offset)
{
  asymbol *best_func = NULL;
  bfd_vma best_func_addr = 0;

  if (symbols == NULL)
    {
      return NULL;
    }

  for (asymbol **p = symbols; *p != NULL; p++)
    {
      som_symbol_type *q = (som_symbol_type *) *p;

      if (q->som_type == SYMBOL_TYPE_ENTRY
          && q->symbol.section == section
          && q->symbol.value <= offset
          && q->symbol.value >= best_func_addr)
        {
          best_func = (asymbol *) q;
          best_func_addr = q->symbol.value;
        }
    }

  return best_func;
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
  if (discriminator_ptr)
    {
      *discriminator_ptr = 0;
    }

  bool found = false;
  if (!_bfd_stab_section_find_nearest_line (abfd, symbols, section, offset,
					    &found, filename_ptr,
					    functionname_ptr, line_ptr,
					    &somdata (abfd).line_info))
    {
      return false;
    }

  if (found)
    {
      return true;
    }

  asymbol *func = find_function_for_offset (symbols, section, offset);
  if (func == NULL)
    {
      return false;
    }

  *filename_ptr = NULL;
  *functionname_ptr = bfd_asymbol_name (func);
  *line_ptr = 0;

  return true;
}

static int
som_sizeof_headers (bfd *abfd ATTRIBUTE_UNUSED,
		    struct bfd_link_info *info ATTRIBUTE_UNUSED)
{
  bfd_set_error (bfd_error_invalid_operation);
  return -1;
}

/* Return the single-character symbol type corresponding to
   SOM section S, or '?' for an unknown SOM section.  */

static char
som_section_type (const char *s)
{
  if (s == NULL)
  {
    return '?';
  }

  for (const struct section_to_type *t = stt; t->section; t++)
  {
    if (strcmp(s, t->section) == 0)
    {
      return t->type;
    }
  }

  return '?';
}

static int
som_decode_symclass (asymbol *symbol)
{
  if (symbol == NULL || symbol->section == NULL)
    return '?';

  if (bfd_is_com_section (symbol->section))
    return 'C';

  if (bfd_is_und_section (symbol->section))
    {
      if (symbol->flags & BSF_WEAK)
        return (symbol->flags & BSF_OBJECT) ? 'v' : 'w';
      return 'U';
    }

  if (bfd_is_ind_section (symbol->section))
    return 'I';

  if (symbol->flags & BSF_WEAK)
    return (symbol->flags & BSF_OBJECT) ? 'V' : 'W';

  if (!(symbol->flags & (BSF_GLOBAL | BSF_LOCAL)))
    return '?';

  char c;
  const som_symbol_info_type *info = som_symbol_data (symbol);

  if (bfd_is_abs_section (symbol->section)
      || (info != NULL && info->som_type == SYMBOL_TYPE_ABSOLUTE))
    c = 'a';
  else
    c = som_section_type (symbol->section->name);

  if (symbol->flags & BSF_GLOBAL)
    c = TOUPPER (c);

  return c;
}

/* Return information about SOM symbol SYMBOL in RET.  */

static void
som_get_symbol_info (bfd *ignore_abfd ATTRIBUTE_UNUSED,
		     asymbol *symbol,
		     symbol_info *ret)
{
  if (symbol == NULL || ret == NULL)
    {
      return;
    }

  ret->type = som_decode_symclass (symbol);

  if (ret->type != 'U' && symbol->section != NULL)
    {
      ret->value = symbol->value + symbol->section->vma;
    }
  else
    {
      ret->value = 0;
    }

  ret->name = symbol->name;
}

/* Count the number of symbols in the archive symbol table.  Necessary
   so that we can allocate space for all the carsyms at once.  */

static bool
process_hash_chain (bfd *abfd,
		    file_ptr lst_filepos,
		    unsigned int offset,
		    symindex *count)
{
  while (offset != 0)
    {
      struct som_external_lst_symbol_record ext_lst_symbol;
      unsigned int next_offset;

      if (bfd_seek (abfd, lst_filepos + offset, SEEK_SET) != 0)
	return false;

      if (bfd_read (&ext_lst_symbol, sizeof (ext_lst_symbol), abfd)
	  != sizeof (ext_lst_symbol))
	return false;

      (*count)++;

      next_offset = bfd_getb32 (ext_lst_symbol.next_entry);
      if (next_offset != 0 && next_offset <= offset)
	{
	  bfd_set_error (bfd_error_bad_value);
	  return false;
	}
      offset = next_offset;
    }
  return true;
}

static bool
som_bfd_count_ar_symbols (bfd *abfd,
			  struct som_lst_header *lst_header,
			  symindex *count)
{
  unsigned char *hash_table = NULL;
  size_t amt;
  bool success = false;
  file_ptr lst_filepos;

  *count = 0;
  if (lst_header->hash_size == 0)
    return true;

  lst_filepos = bfd_tell (abfd) - sizeof (struct som_external_lst_header);

  if (_bfd_mul_overflow (lst_header->hash_size, 4, &amt))
    {
      bfd_set_error (bfd_error_file_too_big);
      return false;
    }

  hash_table = _bfd_malloc_and_read (abfd, amt, amt);
  if (hash_table == NULL)
    return false;

  success = true;
  for (unsigned int i = 0; i < lst_header->hash_size; i++)
    {
      unsigned int offset = bfd_getb32 (hash_table + 4 * i);
      if (offset == 0)
	continue;

      if (!process_hash_chain (abfd, lst_filepos, offset, count))
	{
	  success = false;
	  break;
	}
    }

  free (hash_table);
  return success;
}

/* Fill in the canonical archive symbols (SYMS) from the archive described
   by ABFD and LST_HEADER.  */

static bool
process_one_symbol (bfd *abfd,
		    carsym *set,
		    const struct som_external_lst_symbol_record *lst_symbol,
		    const struct som_external_som_entry *som_dict,
		    unsigned int module_count,
		    file_ptr lst_filepos,
		    unsigned int string_loc)
{
  size_t len;
  unsigned char ext_len[4];
  char *name;
  unsigned int ndx;
  file_ptr name_pos;
  uint32_t name_offset = bfd_getb32 (lst_symbol->name);

  name_pos = lst_filepos + string_loc + name_offset - 4;
  if (bfd_seek (abfd, name_pos, SEEK_SET) != 0)
    return false;

  if (bfd_read (&ext_len, 4, abfd) != 4)
    return false;
  len = bfd_getb32 (ext_len);

  if (len == (size_t) -1)
    {
      bfd_set_error (bfd_error_no_memory);
      return false;
    }

  name = (char *) _bfd_alloc_and_read (abfd, len + 1, len);
  if (!name)
    return false;
  name[len] = '\0';
  set->name = name;

  ndx = bfd_getb32 (lst_symbol->som_index);
  if (ndx >= module_count)
    {
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  set->file_offset
    = bfd_getb32 (som_dict[ndx].location) - sizeof (struct ar_hdr);

  return true;
}

static bool
som_bfd_fill_in_ar_symbols (bfd *abfd,
			    struct som_lst_header *lst_header,
			    carsym **syms)
{
  carsym *set = syms[0];
  unsigned char *hash_table = NULL;
  struct som_external_som_entry *som_dict = NULL;
  size_t amt;
  bool success = false;
  file_ptr lst_filepos;

  lst_filepos = bfd_tell (abfd) - sizeof (struct som_external_lst_header);

  if (_bfd_mul_overflow (lst_header->hash_size, 4, &amt))
    {
      bfd_set_error (bfd_error_file_too_big);
      goto cleanup;
    }
  hash_table = _bfd_malloc_and_read (abfd, amt, amt);
  if (hash_table == NULL && lst_header->hash_size != 0)
    goto cleanup;

  if (bfd_seek (abfd, lst_filepos + lst_header->dir_loc, SEEK_SET) != 0)
    goto cleanup;

  if (_bfd_mul_overflow (lst_header->module_count,
			 sizeof (struct som_external_som_entry), &amt))
    {
      bfd_set_error (bfd_error_file_too_big);
      goto cleanup;
    }
  som_dict = (struct som_external_som_entry *)
    _bfd_malloc_and_read (abfd, amt, amt);
  if (som_dict == NULL && lst_header->module_count != 0)
    goto cleanup;

  for (unsigned int i = 0; i < lst_header->hash_size; i++)
    {
      unsigned int current_offset = bfd_getb32 (hash_table + 4 * i);

      while (current_offset != 0)
	{
	  struct som_external_lst_symbol_record lst_symbol;

	  if (bfd_seek (abfd, lst_filepos + current_offset, SEEK_SET) != 0)
	    goto cleanup;

	  if (bfd_read (&lst_symbol, sizeof (lst_symbol), abfd)
	      != sizeof (lst_symbol))
	    goto cleanup;

	  if (!process_one_symbol (abfd, set, &lst_symbol, som_dict,
				  lst_header->module_count, lst_filepos,
				  lst_header->string_loc))
	    goto cleanup;

	  set++;
	  current_offset = bfd_getb32 (lst_symbol.next_entry);
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
  const size_t AR_NAME_SIZE = 16;
  const char * const ARMAP_NAME = "/               ";
  char member_name[AR_NAME_SIZE];
  struct artdata *ardata = bfd_ardata (abfd);
  struct ar_hdr ar_header;
  unsigned long armap_member_size;
  file_ptr armap_start_pos;
  struct som_external_lst_header ext_lst_header;
  struct som_lst_header lst_header;
  file_ptr symbol_list_start_pos;
  size_t symbols_size;

  if (bfd_read (member_name, AR_NAME_SIZE, abfd) != AR_NAME_SIZE)
    {
      return bfd_tell (abfd) == 0;
    }

  if (bfd_seek (abfd, -(long)AR_NAME_SIZE, SEEK_CUR) != 0)
    return false;

  if (strncmp (member_name, ARMAP_NAME, AR_NAME_SIZE) != 0)
    {
      abfd->has_armap = false;
      return true;
    }

  if (bfd_read (&ar_header, sizeof (ar_header), abfd) != sizeof (ar_header))
    return false;

  if (strncmp (ar_header.ar_fmag, ARFMAG, sizeof (ar_header.ar_fmag)) != 0)
    {
      bfd_set_error (bfd_error_malformed_archive);
      return false;
    }

  errno = 0;
  armap_member_size = strtoul (ar_header.ar_size, NULL, 10);
  if (errno != 0)
    {
      bfd_set_error (bfd_error_malformed_archive);
      return false;
    }

  armap_start_pos = bfd_tell (abfd);
  ardata->first_file_filepos = armap_start_pos + armap_member_size;

  if (bfd_read (&ext_lst_header, sizeof (ext_lst_header), abfd) != sizeof (ext_lst_header))
    return false;

  som_swap_lst_header_in (&ext_lst_header, &lst_header);

  if (lst_header.a_magic != LIBMAGIC)
    {
      bfd_set_error (bfd_error_malformed_archive);
      return false;
    }

  if (!som_bfd_count_ar_symbols (abfd, &lst_header, &ardata->symdef_count))
    return false;

  symbol_list_start_pos = armap_start_pos + sizeof (ext_lst_header);
  if (bfd_seek (abfd, symbol_list_start_pos, SEEK_SET) != 0)
    return false;

  ardata->cache = NULL;
  if (_bfd_mul_overflow (ardata->symdef_count, sizeof (carsym), &symbols_size))
    {
      bfd_set_error (bfd_error_file_too_big);
      return false;
    }

  ardata->symdefs = bfd_alloc (abfd, symbols_size);
  if (ardata->symdefs == NULL)
    return false;

  if (!som_bfd_fill_in_ar_symbols (abfd, &lst_header, &ardata->symdefs))
    return false;

  if (bfd_seek (abfd, ardata->first_file_filepos, SEEK_SET) != 0)
    return false;

  abfd->has_armap = true;
  return true;
}

/* Begin preparing to write a SOM library symbol table.

   As part of the prep work we need to determine the number of symbols
   and the size of the associated string section.  */

static bool
is_som_object_bfd (const bfd *abfd)
{
  return abfd->format == bfd_object
    && abfd->xvec != NULL
    && abfd->xvec->flavour == bfd_target_som_flavour;
}

static bool
should_include_in_archive_symtab (bfd *abfd, const som_symbol_type *sym)
{
  struct som_misc_symbol_info info;
  som_bfd_derive_misc_symbol_info (abfd, &sym->symbol, &info);

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

  if (bfd_is_und_section (sym->symbol.section))
    {
      return false;
    }

  return true;
}

static bool
som_bfd_prep_for_ar_write (bfd *abfd,
			   unsigned int *num_syms,
			   unsigned int *stringsize)
{
  *num_syms = 0;
  *stringsize = 0;

  for (bfd *curr_bfd = abfd->archive_head; curr_bfd != NULL;
       curr_bfd = curr_bfd->archive_next)
    {
      if (!is_som_object_bfd (curr_bfd))
	{
	  continue;
	}

      if (!som_slurp_symbol_table (curr_bfd))
	{
	  return false;
	}

      som_symbol_type *sym = obj_som_symtab (curr_bfd);
      unsigned int curr_count = bfd_get_symcount (curr_bfd);

      for (unsigned int i = 0; i < curr_count; i++, sym++)
	{
	  if (should_include_in_archive_symtab (curr_bfd, sym))
	    {
	      (*num_syms)++;
	      *stringsize += strlen (sym->symbol.name) + 5;
	      *stringsize = (*stringsize + 3) & ~3U;
	    }
	}
    }
  return true;
}

/* Hash a symbol name based on the hashing algorithm presented in the
   SOM ABI.  */

static unsigned int
som_bfd_ar_symbol_hash (asymbol *symbol)
{
  if (!symbol || !symbol->name || symbol->name[0] == '\0')
    {
      return 0;
    }

  const char * const name = symbol->name;
  const size_t len = strlen (name);

  if (len == 1)
    {
      const unsigned int SINGLE_CHAR_BASE = 0x1000100;
      const int SINGLE_CHAR_SHIFT = 16;
      const unsigned char c = name[0];

      return SINGLE_CHAR_BASE | ((unsigned int) c << SINGLE_CHAR_SHIFT) | c;
    }

  const unsigned int LEN_MASK = 0x7f;
  const int LEN_SHIFT = 24;
  const int CHAR2_SHIFT = 16;
  const int PENULTIMATE_CHAR_SHIFT = 8;

  const unsigned int len_part = (len & LEN_MASK) << LEN_SHIFT;
  const unsigned char second_char = name[1];
  const unsigned char penultimate_char = name[len - 2];
  const unsigned char last_char = name[len - 1];

  return len_part
         | ((unsigned int) second_char << CHAR2_SHIFT)
         | ((unsigned int) penultimate_char << PENULTIMATE_CHAR_SHIFT)
         | last_char;
}

/* Do the bulk of the work required to write the SOM library
   symbol table.  */

struct symbol_ar_data
{
  char *strings;
  struct som_external_lst_symbol_record *lst_syms;
  unsigned char *hash_table;
  struct som_external_som_entry *som_dict;
  struct som_external_lst_symbol_record **last_hash_entry;
};

static void
free_symbol_ar_data (struct symbol_ar_data *data)
{
  free (data->strings);
  free (data->lst_syms);
  free (data->hash_table);
  free (data->som_dict);
  free (data->last_hash_entry);
}

static bool
allocate_symbol_ar_data (struct symbol_ar_data *data,
			 unsigned int nsyms,
			 unsigned int string_size,
			 unsigned int hash_size,
			 unsigned int module_count)
{
  size_t amt;

  if (_bfd_mul_overflow (hash_size, 4, &amt))
    goto no_mem;
  data->hash_table = bfd_zmalloc (amt);
  if (data->hash_table == NULL && hash_size != 0)
    return false;

  if (_bfd_mul_overflow (module_count, sizeof (struct som_external_som_entry), &amt))
    goto no_mem;
  data->som_dict = bfd_zmalloc (amt);
  if (data->som_dict == NULL && module_count != 0)
    return false;

  if (_bfd_mul_overflow (hash_size, sizeof (struct som_external_lst_symbol_record *), &amt))
    goto no_mem;
  data->last_hash_entry = bfd_zmalloc (amt);
  if (data->last_hash_entry == NULL && hash_size != 0)
    return false;

  if (_bfd_mul_overflow (nsyms, sizeof (struct som_external_lst_symbol_record), &amt))
    goto no_mem;
  data->lst_syms = bfd_malloc (amt);
  if (data->lst_syms == NULL && nsyms != 0)
    return false;

  data->strings = bfd_malloc (string_size);
  if (data->strings == NULL && string_size != 0)
    return false;

  return true;

no_mem:
  bfd_set_error (bfd_error_no_memory);
  return false;
}

static bool
should_skip_symbol (const struct som_misc_symbol_info *info,
		    const bfd_symbol *sym)
{
  return info->symbol_type == ST_NULL
      || info->symbol_type == ST_SYM_EXT
      || info->symbol_type == ST_ARG_EXT
      || (info->symbol_scope != SS_UNIVERSAL && info->symbol_type != ST_STORAGE)
      || bfd_is_und_section (sym->section);
}

static void
fill_lst_symbol_record (struct som_external_lst_symbol_record *rec,
			const struct som_misc_symbol_info *info,
			const bfd_symbol *sym,
			unsigned int som_index,
			unsigned int name_offset,
			unsigned int symbol_key)
{
  unsigned int flags = 0;

  if (info->secondary_def)
    flags |= LST_SYMBOL_SECONDARY_DEF;
  if (bfd_is_com_section (sym->section))
    flags |= LST_SYMBOL_IS_COMMON;
  if (info->dup_common)
    flags |= LST_SYMBOL_DUP_COMMON;

  flags |= (unsigned int) info->symbol_type << LST_SYMBOL_SYMBOL_TYPE_SH;
  flags |= (unsigned int) info->symbol_scope << LST_SYMBOL_SYMBOL_SCOPE_SH;
  flags |= 3 << LST_SYMBOL_XLEAST_SH;
  flags |= (unsigned int) info->arg_reloc << LST_SYMBOL_ARG_RELOC_SH;

  bfd_putb32 (flags, rec->flags);
  bfd_putb32 (name_offset, rec->name);
  bfd_putb32 (0, rec->qualifier_name);
  bfd_putb32 (info->symbol_info, rec->symbol_info);
  bfd_putb32 (info->symbol_value | info->priv_level, rec->symbol_value);
  bfd_putb32 (0, rec->symbol_descriptor);
  rec->reserved = 0;
  bfd_putb32 (som_index, rec->som_index);
  bfd_putb32 (symbol_key, rec->symbol_key);
  bfd_putb32 (0, rec->next_entry);
}

static bool
write_symbol_data (bfd *abfd,
		   const struct symbol_ar_data *data,
		   unsigned int nsyms,
		   unsigned int string_size,
		   unsigned int hash_size,
		   unsigned int module_count)
{
  size_t amt;

  amt = (size_t) hash_size * 4;
  if (bfd_write (data->hash_table, amt, abfd) != amt)
    return false;

  amt = (size_t) module_count * sizeof (struct som_external_som_entry);
  if (bfd_write (data->som_dict, amt, abfd) != amt)
    return false;

  amt = (size_t) nsyms * sizeof (struct som_external_lst_symbol_record);
  if (bfd_write (data->lst_syms, amt, abfd) != amt)
    return false;

  amt = string_size;
  if (bfd_write (strings, amt, abfd) != amt)
    return false;

  return true;
}

static bool
som_bfd_ar_write_symbol_stuff (bfd *abfd,
			       unsigned int nsyms,
			       unsigned int string_size,
			       struct som_external_lst_header lst,
			       unsigned elength)
{
  struct symbol_ar_data data = { NULL, NULL, NULL, NULL, NULL };
  bool success = false;
  unsigned int hash_size = bfd_getb32 (lst.hash_size);
  unsigned int module_count = bfd_getb32 (lst.module_count);

  if (!allocate_symbol_ar_data (&data, nsyms, string_size,
				hash_size, module_count))
    goto cleanup;

  char *p = data.strings;
  struct som_external_lst_symbol_record *curr_lst_sym = data.lst_syms;
  bfd *curr_bfd;
  unsigned int som_index = 0;
  unsigned int curr_som_offset;

  curr_som_offset = 8 + 2 * sizeof (struct ar_hdr) + bfd_getb32 (lst.file_end);
  if (elength)
    curr_som_offset += elength;
  curr_som_offset = (curr_som_offset + 1) & ~1U;

  for (curr_bfd = abfd->archive_head; curr_bfd != NULL;
       curr_bfd = curr_bfd->archive_next)
    {
      som_symbol_type *sym;
      unsigned int curr_count;
      bool first_symbol_in_som = true;

      if (curr_bfd->format != bfd_object
	  || curr_bfd->xvec->flavour != bfd_target_som_flavour)
	continue;

      if (!som_slurp_symbol_table (curr_bfd))
	goto cleanup;

      sym = obj_som_symtab (curr_bfd);
      curr_count = bfd_get_symcount (curr_bfd);

      for (unsigned int i = 0; i < curr_count; i++, sym++)
	{
	  struct som_misc_symbol_info info;
	  som_bfd_derive_misc_symbol_info (curr_bfd, &sym->symbol, &info);

	  if (should_skip_symbol (&info, &sym->symbol))
	    continue;

	  if (first_symbol_in_som)
	    {
	      bfd_putb32 (curr_som_offset, data.som_dict[som_index].location);
	      bfd_putb32 (arelt_size (curr_bfd), data.som_dict[som_index].length);
	      first_symbol_in_som = false;
	    }

	  unsigned int symbol_key = som_bfd_ar_symbol_hash (&sym->symbol);
	  fill_lst_symbol_record (curr_lst_sym, &info, &sym->symbol, som_index,
				  (unsigned int) (p - data.strings + 4),
				  symbol_key);

	  unsigned int symbol_pos =
	    (curr_lst_sym - data.lst_syms)
	    * sizeof (struct som_external_lst_symbol_record)
	    + hash_size * 4
	    + module_count * sizeof (struct som_external_som_entry)
	    + sizeof (struct som_external_lst_header);
	  unsigned int hash_index = symbol_key % hash_size;
	  struct som_external_lst_symbol_record *last =
	    data.last_hash_entry[hash_index];
	  if (last != NULL)
	    bfd_putb32 (symbol_pos, last->next_entry);
	  else
	    bfd_putb32 (symbol_pos, data.hash_table + 4 * hash_index);
	  data.last_hash_entry[hash_index] = curr_lst_sym;

	  unsigned int slen = strlen (sym->symbol.name);
	  bfd_put_32 (abfd, slen, p);
	  p += 4;
	  slen++;
	  memcpy (p, sym->symbol.name, slen);
	  p += slen;
	  while (slen % 4 != 0)
	    {
	      *p++ = 0;
	      slen++;
	    }
	  BFD_ASSERT (p <= data.strings + string_size);

	  curr_lst_sym++;
	}

      curr_som_offset += arelt_size (curr_bfd) + sizeof (struct ar_hdr);
      curr_som_offset = (curr_som_offset + 1) & ~1U;
      som_index++;
    }

  if (!write_symbol_data (abfd, &data, nsyms, string_size,
			  hash_size, module_count))
    goto cleanup;

  success = true;

cleanup:
  free_symbol_ar_data (&data);
  return success;
}

/* Write out the LST for the archive.

   You'll never believe this is really how armaps are handled in SOM...  */

static unsigned int
count_som_modules (bfd *abfd)
{
  bfd *curr_bfd;
  unsigned int module_count = 0;

  for (curr_bfd = abfd->archive_head; curr_bfd != NULL;
       curr_bfd = curr_bfd->archive_next)
    {
      if (curr_bfd->format == bfd_object
	  && curr_bfd->xvec->flavour == bfd_target_som_flavour)
	{
	  module_count++;
	}
    }
  return module_count;
}

static void
initialize_lst_header (struct som_external_lst_header *lst)
{
  bfd_putb16 (CPU_PA_RISC1_0, &lst->system_id);
  bfd_putb16 (LIBMAGIC, &lst->a_magic);
  bfd_putb32 (VERSION_ID, &lst->version_id);
  bfd_putb32 (0, &lst->file_time.secs);
  bfd_putb32 (0, &lst->file_time.nanosecs);
  bfd_putb32 (0, &lst->export_loc);
  bfd_putb32 (0, &lst->export_count);
  bfd_putb32 (0, &lst->import_loc);
  bfd_putb32 (0, &lst->aux_loc);
  bfd_putb32 (0, &lst->aux_size);
  bfd_putb32 (0, &lst->free_list);
}

static unsigned int
populate_lst_sizes_and_locations (struct som_external_lst_header *lst,
                                  unsigned int module_count,
                                  unsigned int nsyms,
                                  unsigned int stringsize)
{
  unsigned int lst_size = sizeof (struct som_external_lst_header);

  bfd_putb32 (lst_size, &lst->hash_loc);
  bfd_putb32 (SOM_LST_HASH_SIZE, &lst->hash_size);
  lst_size += sizeof (bfd_vma) * SOM_LST_HASH_SIZE;

  bfd_putb32 (module_count, &lst->module_count);
  bfd_putb32 (module_count, &lst->module_limit);
  bfd_putb32 (lst_size, &lst->dir_loc);
  lst_size += sizeof (struct som_external_som_entry) * module_count;

  lst_size += sizeof (struct som_external_lst_symbol_record) * nsyms;

  bfd_putb32 (lst_size, &lst->string_loc);
  bfd_putb32 (stringsize, &lst->string_size);
  lst_size += stringsize;

  bfd_putb32 (lst_size, &lst->file_end);

  return lst_size;
}

static void
compute_and_set_lst_checksum (struct som_external_lst_header *lst)
{
  unsigned char *p = (unsigned char *) lst;
  unsigned int csum = 0;
  size_t i;

  for (i = 0; i < sizeof (*lst) - sizeof (lst->checksum);
       i += sizeof (bfd_vma))
    {
      csum ^= bfd_getb32 (&p[i]);
    }

  bfd_putb32 (csum, &lst->checksum);
}

static bool
create_and_write_ar_header (bfd *abfd,
			    const struct stat *statbuf,
			    unsigned int lst_size)
{
  struct ar_hdr hdr;
  char *hdr_ptr = (char *) &hdr;
  size_t i;

  strncpy (hdr.ar_name, "/              ", sizeof (hdr.ar_name));
  _bfd_ar_spacepad (hdr.ar_date, sizeof (hdr.ar_date), "%-12ld",
		    bfd_ardata (abfd)->armap_timestamp);
  _bfd_ar_spacepad (hdr.ar_uid, sizeof (hdr.ar_uid), "%-6ld",
		    (long) statbuf->st_uid);
  _bfd_ar_spacepad (hdr.ar_gid, sizeof (hdr.ar_gid), "%-6ld",
		    (long) statbuf->st_gid);
  _bfd_ar_spacepad (hdr.ar_mode, sizeof (hdr.ar_mode), "%-8o",
		    (unsigned int) statbuf->st_mode);
  _bfd_ar_spacepad (hdr.ar_size, sizeof (hdr.ar_size), "%-10u",
		    lst_size);
  hdr.ar_fmag[0] = '`';
  hdr.ar_fmag[1] = '\n';

  for (i = 0; i < sizeof (hdr); i++)
    {
      if (hdr_ptr[i] == '\0')
	{
	  hdr_ptr[i] = ' ';
	}
    }

  return bfd_write (&hdr, sizeof (hdr), abfd) == sizeof (hdr);
}

static bool
som_write_armap (bfd *abfd,
		 unsigned int elength,
		 struct orl *map ATTRIBUTE_UNUSED,
		 unsigned int orl_count ATTRIBUTE_UNUSED,
		 int stridx ATTRIBUTE_UNUSED)
{
  struct stat statbuf;
  unsigned int nsyms, stringsize, module_count, lst_size;
  struct som_external_lst_header lst;
  const int ARMAP_TIMESTAMP_FUDGE_SECONDS = 60;

  if (stat (bfd_get_filename (abfd), &statbuf) != 0)
    {
      bfd_set_error (bfd_error_system_call);
      return false;
    }

  bfd_ardata (abfd)->armap_timestamp =
    statbuf.st_mtime + ARMAP_TIMESTAMP_FUDGE_SECONDS;

  if (!som_bfd_prep_for_ar_write (abfd, &nsyms, &stringsize))
    {
      return false;
    }

  module_count = count_som_modules (abfd);

  initialize_lst_header (&lst);

  lst_size =
    populate_lst_sizes_and_locations (&lst, module_count, nsyms,
				      stringsize);

  compute_and_set_lst_checksum (&lst);

  if (!create_and_write_ar_header (abfd, &statbuf, lst_size))
    {
      return false;
    }

  if (bfd_write (&lst, sizeof (lst), abfd) != sizeof (lst))
    {
      return false;
    }

  return som_bfd_ar_write_symbol_stuff (abfd, nsyms, stringsize, lst,
					elength);
}

/* Throw away some malloc'd information for this BFD.  */

#include <limits.h>

static bool
som_bfd_free_cached_info (bfd *abfd)
{
  const bfd_format format = bfd_get_format (abfd);
  if (format == bfd_object || format == bfd_core)
    {
      /* Free the native string and symbol tables.  */
      free (obj_som_symtab (abfd));
      obj_som_symtab (abfd) = NULL;
      free (obj_som_stringtab (abfd));
      obj_som_stringtab (abfd) = NULL;

      for (asection *o = abfd->sections; o != NULL; o = o->next)
	{
	  /* Free the native relocations.  */
	  o->reloc_count = UINT_MAX;
	  free (som_section_data (o)->reloc_stream);
	  som_section_data (o)->reloc_stream = NULL;
	  /* Do not free the generic relocations as they are objalloc'ed.  */
	}
    }

  /* Do not call _bfd_generic_bfd_free_cached_info here.
     som_write_armap needs to access the bfd objalloc memory.  */
  return true;
}

/* End of miscellaneous support functions.  */

/* Linker support functions.  */

#define SUBSPACE_SPLIT_THRESHOLD 240000

static bool
som_bfd_link_split_section (bfd *abfd, asection *sec)
{
  (void) abfd;

  if (sec == NULL)
    {
      return false;
    }

  return som_is_subspace (sec) && sec->size > SUBSPACE_SPLIT_THRESHOLD;
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

