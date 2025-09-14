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

static void initialize_reloc_queue(struct reloc_queue *queue) {
    for (int i = 0; i < 4; i++) {
        queue[i].reloc = NULL;
        queue[i].size = 0;
    }
}

/* Insert a new relocation into the relocation queue.  */

#include <stddef.h>

static void som_reloc_queue_insert(unsigned char *p, unsigned int size, struct reloc_queue *queue, size_t queue_length) {
    if (queue == NULL || queue_length < 4) {
        return;
    }
    
    for (size_t i = queue_length - 1; i > 0; i--) {
        queue[i].reloc = queue[i - 1].reloc;
        queue[i].size = queue[i - 1].size;
    }
    
    queue[0].reloc = p;
    queue[0].size = size;
}

/* When an entry in the relocation queue is reused, the entry moves
   to the front of the queue.  */

#include <stdlib.h>

static void swap_reloc_entries(struct reloc_queue *queue, unsigned int i, unsigned int j) {
    unsigned char *tmp_reloc = queue[i].reloc;
    unsigned int tmp_size = queue[i].size;
    queue[i].reloc = queue[j].reloc;
    queue[i].size = queue[j].size;
    queue[j].reloc = tmp_reloc;
    queue[j].size = tmp_size;
}

static void som_reloc_queue_fix(struct reloc_queue *queue, unsigned int idx) {
    if (idx == 0) return;

    if (idx >= 1 && idx <= 3) {
        for (unsigned int i = 0; i < idx; ++i) {
            swap_reloc_entries(queue, i, i + 1);
        }
    } else {
        abort();
    }
}

/* Search for a particular relocation in the relocation queue.  */

static int som_reloc_queue_find(unsigned char *p, unsigned int size, struct reloc_queue *queue) {
    for (int i = 0; i < 4; i++) {
        if (queue[i].reloc && size == queue[i].size && !memcmp(p, queue[i].reloc, size)) {
            return i;
        }
    }
    return -1;
}

#include <stddef.h>

static unsigned char *try_prev_fixup(bfd *abfd, unsigned int *subspace_reloc_sizep, unsigned char *p, unsigned int size, struct reloc_queue *queue) {
    int queue_index = som_reloc_queue_find(p, size, queue);

    if (queue_index != -1) {
        bfd_put_8(abfd, R_PREV_FIXUP + queue_index, p);
        p++;
        *subspace_reloc_sizep += 1;
        som_reloc_queue_fix(queue, queue_index);
    } else {
        som_reloc_queue_insert(p, size, queue);
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
som_reloc_skip(bfd *abfd, unsigned int skip, unsigned char *p, unsigned int *subspace_reloc_sizep, struct reloc_queue *queue)
{
    if (skip > 0xFFFFFF)
    {
        while (skip >= 0x1000000)
        {
            bfd_put_8(abfd, R_NO_RELOCATION + 31, p);
            bfd_put_8(abfd, 0xFF, p + 1);
            bfd_put_16(abfd, (bfd_vma)0xFFFF, p + 2);
            p = try_prev_fixup(abfd, subspace_reloc_sizep, p, 4, queue);
            skip -= 0x1000000;
            *subspace_reloc_sizep += 1;
        }
    }

    if (skip > 0)
    {
        if ((skip & 3) == 0 && skip <= 0xC0000)
        {
            if (skip <= 0x60)
            {
                bfd_put_8(abfd, R_NO_RELOCATION + (skip >> 2) - 1, p);
                *subspace_reloc_sizep += 1;
                p++;
            }
            else if (skip <= 0x1000)
            {
                bfd_put_8(abfd, R_NO_RELOCATION + 24 + (((skip >> 2) - 1) >> 8), p);
                bfd_put_8(abfd, (skip >> 2) - 1, p + 1);
                p = try_prev_fixup(abfd, subspace_reloc_sizep, p, 2, queue);
            }
            else
            {
                bfd_put_8(abfd, R_NO_RELOCATION + 28 + (((skip >> 2) - 1) >> 16), p);
                bfd_put_16(abfd, (bfd_vma)(skip >> 2) - 1, p + 1);
                p = try_prev_fixup(abfd, subspace_reloc_sizep, p, 3, queue);
            }
        }
        else
        {
            bfd_put_8(abfd, R_NO_RELOCATION + 31, p);
            bfd_put_8(abfd, (skip - 1) >> 16, p + 1);
            bfd_put_16(abfd, (bfd_vma)skip - 1, p + 2);
            p = try_prev_fixup(abfd, subspace_reloc_sizep, p, 4, queue);
        }
    }

    return p;
}

/* Emit the proper R_DATA_OVERRIDE fixups to handle a nonzero addend
   from a BFD relocation.  Update the size of the subspace relocation
   stream via SUBSPACE_RELOC_SIZE_P; also return the current pointer
   into the relocation stream.  */

static unsigned char *som_reloc_addend(bfd *abfd, bfd_vma addend, unsigned char *p, unsigned int *subspace_reloc_sizep, struct reloc_queue *queue) {
    unsigned int length;
    unsigned char override_type;

    if (addend + 0x80 < 0x100) {
        override_type = R_DATA_OVERRIDE + 1;
        length = 2;
        bfd_put_8(abfd, addend, p + 1);
    } else if (addend + 0x8000 < 0x10000) {
        override_type = R_DATA_OVERRIDE + 2;
        length = 3;
        bfd_put_16(abfd, addend, p + 1);
    } else if (addend + 0x800000 < 0x1000000) {
        override_type = R_DATA_OVERRIDE + 3;
        length = 4;
        bfd_put_8(abfd, addend >> 16, p + 1);
        bfd_put_16(abfd, addend, p + 2);
    } else {
        override_type = R_DATA_OVERRIDE + 4;
        length = 5;
        bfd_put_32(abfd, addend, p + 1);
    }

    bfd_put_8(abfd, override_type, p);
    return try_prev_fixup(abfd, subspace_reloc_sizep, p, length, queue);
}

/* Handle a single function call relocation.  */

static unsigned char *
som_reloc_call(bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_sizep,
               arelent *bfd_reloc, int sym_num, struct reloc_queue *queue) {
    int arg_bits = HPPA_R_ARG_RELOC(bfd_reloc->addend);
    int rtn_bits = arg_bits & 0x3;
    int type = -1;
    int done = 0;

    if (sym_num < 0x100) {
        switch (arg_bits) {
            case 0:
            case 1:
                type = 0;
                break;
            case 1 << 8:
            case 1 << 8 | 1:
                type = 1;
                break;
            case 1 << 8 | 1 << 6:
            case 1 << 8 | 1 << 6 | 1:
                type = 2;
                break;
            case 1 << 8 | 1 << 6 | 1 << 4:
            case 1 << 8 | 1 << 6 | 1 << 4 | 1:
                type = 3;
                break;
            case 1 << 8 | 1 << 6 | 1 << 4 | 1 << 2:
            case 1 << 8 | 1 << 6 | 1 << 4 | 1 << 2 | 1:
                type = 4;
                break;
        }
        if (type != -1) {
            if (rtn_bits) {
                type += 5;
            }
            bfd_put_8(abfd, bfd_reloc->howto->type + type, p);
            bfd_put_8(abfd, sym_num, p + 1);
            p = try_prev_fixup(abfd, subspace_reloc_sizep, p, 2, queue);
            done = 1;
        }
    }

    if (!done) {
        type = rtn_bits;
        if ((arg_bits >> 6 & 0xf) == 0xe) {
            type += 9 * 40;
        } else {
            type += (3 * (arg_bits >> 8 & 3) + (arg_bits >> 6 & 3)) * 40;
        }
        if ((arg_bits >> 2 & 0xf) == 0xe) {
            type += 9 * 4;
        } else {
            type += (3 * (arg_bits >> 4 & 3) + (arg_bits >> 2 & 3)) * 4;
        }

        bfd_put_8(abfd, bfd_reloc->howto->type + 10 + 2 * (sym_num >= 0x100) + (type >= 0x100), p);
        bfd_put_8(abfd, type, p + 1);

        if (sym_num < 0x100) {
            bfd_put_8(abfd, sym_num, p + 2);
            p = try_prev_fixup(abfd, subspace_reloc_sizep, p, 3, queue);
        } else {
            bfd_put_8(abfd, sym_num >> 16, p + 2);
            bfd_put_16(abfd, (bfd_vma)sym_num, p + 3);
            p = try_prev_fixup(abfd, subspace_reloc_sizep, p, 5, queue);
        }
    }
    return p;
}

/* Return the logarithm of X, base 2, considering X unsigned,
   if X is a power of 2.  Otherwise, returns -1.  */

#include <limits.h>

static int exact_log2(unsigned int x) {
    if (x == 0 || (x & (x - 1)) != 0)
        return -1;

    int log = 0;
    while (x >>= 1)
        log++;
    
    return log;
}

static bfd_reloc_status_type hppa_som_reloc(bfd *abfd, arelent *reloc_entry, asymbol *symbol_in, void *data, asection *input_section, bfd *output_bfd, char **error_message) {
    if (output_bfd) {
        reloc_entry->address += input_section->output_offset;
    }
    return bfd_reloc_ok;
}

/* Given a generic HPPA relocation type, the instruction format,
   and a field selector, return one or more appropriate SOM relocations.  */

int **hppa_som_gen_reloc_type(bfd *abfd, int base_type, int format, enum hppa_reloc_field_selector_type_alt field, int sym_diff, asymbol *sym) {
    int *final_type, **final_types;
    size_t amt = sizeof(int *);

    if (!(final_types = bfd_alloc(abfd, amt * 6)) || !(final_type = bfd_alloc(abfd, sizeof(int))))
        return NULL;

    final_types[0] = final_type;
    final_types[1] = final_types[2] = NULL;

    switch (field) {
        case e_fsel: case e_psel: case e_lpsel: case e_rpsel:
            *final_type = base_type;
            break;
        case e_tsel: case e_ltsel: case e_rtsel:
            if (!(final_types[0] = bfd_alloc(abfd, sizeof(int))))
                return NULL;
            *final_types[0] = field == e_tsel ? R_FSEL : (field == e_ltsel ? R_LSEL : R_RSEL);
            final_types[1] = final_type;
            *final_type = base_type;
            break;
        case e_lssel: case e_rssel:
            if (!(final_types[0] = bfd_alloc(abfd, sizeof(int))))
                return NULL;
            *final_types[0] = R_S_MODE;
            final_types[1] = final_type;
            *final_type = base_type;
            break;
        case e_lsel: case e_rsel:
            if (!(final_types[0] = bfd_alloc(abfd, sizeof(int))))
                return NULL;
            *final_types[0] = R_N_MODE;
            final_types[1] = final_type;
            *final_type = base_type;
            break;
        case e_ldsel: case e_rdsel:
            if (!(final_types[0] = bfd_alloc(abfd, sizeof(int))))
                return NULL;
            *final_types[0] = R_D_MODE;
            final_types[1] = final_type;
            *final_type = base_type;
            break;
        case e_lrsel: case e_rrsel:
            if (!(final_types[0] = bfd_alloc(abfd, sizeof(int))))
                return NULL;
            *final_types[0] = R_R_MODE;
            final_types[1] = final_type;
            *final_type = base_type;
            break;
        case e_nsel:
            if (!(final_types[0] = bfd_alloc(abfd, sizeof(int))))
                return NULL;
            *final_types[0] = R_N1SEL;
            final_types[1] = final_type;
            *final_type = base_type;
            break;
        case e_nlsel: case e_nlrsel:
            if (!(final_types[0] = bfd_alloc(abfd, sizeof(int))) || !(final_types[1] = bfd_alloc(abfd, sizeof(int))))
                return NULL;
            *final_types[0] = R_N0SEL;
            *final_types[1] = field == e_nlsel ? R_N_MODE : R_R_MODE;
            final_types[2] = final_type;
            final_types[3] = NULL;
            *final_type = base_type;
            break;
        case e_ltpsel: case e_rtpsel:
            abort();
            break;
    }

    final_types[4] = NULL;

    switch (base_type) {
        case R_HPPA:
            if (sym_diff) {
                if (!(final_types[0] = bfd_alloc(abfd, sizeof(int))) || !(final_types[1] = bfd_alloc(abfd, sizeof(int))) || !(final_types[2] = bfd_alloc(abfd, sizeof(int))) || !(final_types[3] = bfd_alloc(abfd, sizeof(int))))
                    return NULL;
                *final_types[0] = field == e_fsel ? R_FSEL : (field == e_rsel ? R_RSEL : R_LSEL);
                *final_types[1] = R_COMP2;
                *final_types[2] = R_COMP2;
                *final_types[3] = R_COMP1;
                final_types[4] = final_type;
                *final_types[4] = format == 32 ? R_DATA_EXPR : R_CODE_EXPR;
            } else if (field == e_psel || field == e_lpsel || field == e_rpsel) {
                *final_type = format == 32 ? R_DATA_PLABEL : R_CODE_PLABEL;
            } else if (field == e_tsel || field == e_ltsel || field == e_rtsel) {
                *final_type = R_DLT_REL;
            } else if (format == 32) {
                *final_type = R_DATA_ONE_SYMBOL;
                if (som_symbol_data(sym)->som_type == SYMBOL_TYPE_UNKNOWN && (sym->flags & BSF_SECTION_SYM) == 0 && (sym->flags & BSF_FUNCTION) == 0 && !bfd_is_com_section(sym->section))
                    som_symbol_data(sym)->som_type = SYMBOL_TYPE_DATA;
            }
            break;
        case R_HPPA_GOTOFF:
            if (field == e_psel || field == e_lpsel || field == e_rpsel) {
                *final_type = R_DATA_PLABEL;
            } else if (field == e_fsel && format == 32) {
                *final_type = R_DATA_GPREL;
            }
            break;
        case R_HPPA_COMPLEX:
            if (sym_diff) {
                if (!(final_types[0] = bfd_alloc(abfd, sizeof(int))) || !(final_types[1] = bfd_alloc(abfd, sizeof(int))) || !(final_types[2] = bfd_alloc(abfd, sizeof(int))) || !(final_types[3] = bfd_alloc(abfd, sizeof(int))))
                    return NULL;
                *final_types[0] = field == e_fsel ? R_FSEL : (field == e_rsel ? R_RSEL : R_LSEL);
                *final_types[1] = R_COMP2;
                *final_types[2] = R_COMP2;
                *final_types[3] = R_COMP1;
                final_types[4] = final_type;
                *final_types[4] = format == 32 ? R_DATA_EXPR : R_CODE_EXPR;
            }
            break;
        case R_HPPA_NONE: case R_HPPA_ABS_CALL:
            break;
        case R_HPPA_PCREL_CALL:
#ifndef NO_PCREL_MODES
            if (!(final_types[0] = bfd_alloc(abfd, sizeof(int))))
                return NULL;
            *final_types[0] = format == 17 ? R_SHORT_PCREL_MODE : R_LONG_PCREL_MODE;
            final_types[1] = final_type;
#endif
            break;
    }
    return final_types;
}

/* Return the address of the correct entry in the PA SOM relocation
   howto table.  */

static reloc_howto_type *som_bfd_reloc_type_lookup(bfd *abfd ATTRIBUTE_UNUSED, bfd_reloc_code_real_type code) {
    if (code >= R_NO_RELOCATION && code < R_NO_RELOCATION + 255) {
        BFD_ASSERT(som_hppa_howto_table[code].type == code);
        return &som_hppa_howto_table[code];
    }
    return NULL;
}

static reloc_howto_type *som_bfd_reloc_name_lookup(bfd *abfd, const char *r_name) {
  for (unsigned int i = 0; i < sizeof(som_hppa_howto_table) / sizeof(som_hppa_howto_table[0]); i++) {
    const char *howto_name = som_hppa_howto_table[i].name;
    if (howto_name && strcasecmp(howto_name, r_name) == 0) {
      return &som_hppa_howto_table[i];
    }
  }
  return NULL;
}

#include <stdint.h>
#include <errno.h>

static int som_swap_clock_in(const struct som_external_clock *src, struct som_clock *dst) {
    if (!src || !dst) {
        return EINVAL;
    }

    dst->secs = bfd_getb32(src->secs);
    dst->nanosecs = bfd_getb32(src->nanosecs);
    return 0;
}

#include <stdint.h>

static void swap_clock_out(const struct som_clock *src, struct som_external_clock *dst) {
    if (!src || !dst) return;

    uint32_t secs = (uint32_t) src->secs;
    uint32_t nanosecs = (uint32_t) src->nanosecs;

    dst->secs[0] = (uint8_t) (secs >> 24);
    dst->secs[1] = (uint8_t) (secs >> 16);
    dst->secs[2] = (uint8_t) (secs >> 8);
    dst->secs[3] = (uint8_t) secs;

    dst->nanosecs[0] = (uint8_t) (nanosecs >> 24);
    dst->nanosecs[1] = (uint8_t) (nanosecs >> 16);
    dst->nanosecs[2] = (uint8_t) (nanosecs >> 8);
    dst->nanosecs[3] = (uint8_t) nanosecs;
}

static int convert_and_assign_b16(uint16_t *dst, const uint8_t *src) {
    if (!dst || !src) return -1;
    *dst = bfd_getb16(src);
    return 0;
}

static int convert_and_assign_b32(uint32_t *dst, const uint8_t *src) {
    if (!dst || !src) return -1;
    *dst = bfd_getb32(src);
    return 0;
}

static int som_swap_header_in(struct som_external_header *src, struct som_header *dst) {
    if (!src || !dst) return -1;

    int error = 0;
    error |= convert_and_assign_b16(&dst->system_id, src->system_id);
    error |= convert_and_assign_b16(&dst->a_magic, src->a_magic);
    error |= convert_and_assign_b32(&dst->version_id, src->version_id);
    error |= som_swap_clock_in(&src->file_time, &dst->file_time);
    error |= convert_and_assign_b32(&dst->entry_space, src->entry_space);
    error |= convert_and_assign_b32(&dst->entry_subspace, src->entry_subspace);
    error |= convert_and_assign_b32(&dst->entry_offset, src->entry_offset);
    error |= convert_and_assign_b32(&dst->aux_header_location, src->aux_header_location);
    error |= convert_and_assign_b32(&dst->aux_header_size, src->aux_header_size);
    error |= convert_and_assign_b32(&dst->som_length, src->som_length);
    error |= convert_and_assign_b32(&dst->presumed_dp, src->presumed_dp);
    error |= convert_and_assign_b32(&dst->space_location, src->space_location);
    error |= convert_and_assign_b32(&dst->space_total, src->space_total);
    error |= convert_and_assign_b32(&dst->subspace_location, src->subspace_location);
    error |= convert_and_assign_b32(&dst->subspace_total, src->subspace_total);
    error |= convert_and_assign_b32(&dst->loader_fixup_location, src->loader_fixup_location);
    error |= convert_and_assign_b32(&dst->loader_fixup_total, src->loader_fixup_total);
    error |= convert_and_assign_b32(&dst->space_strings_location, src->space_strings_location);
    error |= convert_and_assign_b32(&dst->space_strings_size, src->space_strings_size);
    error |= convert_and_assign_b32(&dst->init_array_location, src->init_array_location);
    error |= convert_and_assign_b32(&dst->init_array_total, src->init_array_total);
    error |= convert_and_assign_b32(&dst->compiler_location, src->compiler_location);
    error |= convert_and_assign_b32(&dst->compiler_total, src->compiler_total);
    error |= convert_and_assign_b32(&dst->symbol_location, src->symbol_location);
    error |= convert_and_assign_b32(&dst->symbol_total, src->symbol_total);
    error |= convert_and_assign_b32(&dst->fixup_request_location, src->fixup_request_location);
    error |= convert_and_assign_b32(&dst->fixup_request_total, src->fixup_request_total);
    error |= convert_and_assign_b32(&dst->symbol_strings_location, src->symbol_strings_location);
    error |= convert_and_assign_b32(&dst->symbol_strings_size, src->symbol_strings_size);
    error |= convert_and_assign_b32(&dst->unloadable_sp_location, src->unloadable_sp_location);
    error |= convert_and_assign_b32(&dst->unloadable_sp_size, src->unloadable_sp_size);
    error |= convert_and_assign_b32(&dst->checksum, src->checksum);

    return error ? -1 : 0;
}

static void handle_transfer_error() {
    // Appropriate error handling mechanism, can be logging or other operations
}

#define SAFE_TRANSFER_FUNC(type, func, src, dst) \
    do { \
        if (!func(src, dst)) { \
            handle_transfer_error(); \
            return; \
        } \
    } while (0)

static void som_swap_header_out(struct som_header *src, struct som_external_header *dst) {
    SAFE_TRANSFER_FUNC(uint16_t, bfd_putb16, src->system_id, dst->system_id);
    SAFE_TRANSFER_FUNC(uint16_t, bfd_putb16, src->a_magic, dst->a_magic);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->version_id, dst->version_id);
    som_swap_clock_out(&src->file_time, &dst->file_time);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->entry_space, dst->entry_space);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->entry_subspace, dst->entry_subspace);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->entry_offset, dst->entry_offset);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->aux_header_location, dst->aux_header_location);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->aux_header_size, dst->aux_header_size);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->som_length, dst->som_length);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->presumed_dp, dst->presumed_dp);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->space_location, dst->space_location);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->space_total, dst->space_total);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->subspace_location, dst->subspace_location);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->subspace_total, dst->subspace_total);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->loader_fixup_location, dst->loader_fixup_location);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->loader_fixup_total, dst->loader_fixup_total);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->space_strings_location, dst->space_strings_location);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->space_strings_size, dst->space_strings_size);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->init_array_location, dst->init_array_location);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->init_array_total, dst->init_array_total);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->compiler_location, dst->compiler_location);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->compiler_total, dst->compiler_total);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->symbol_location, dst->symbol_location);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->symbol_total, dst->symbol_total);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->fixup_request_location, dst->fixup_request_location);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->fixup_request_total, dst->fixup_request_total);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->symbol_strings_location, dst->symbol_strings_location);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->symbol_strings_size, dst->symbol_strings_size);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->unloadable_sp_location, dst->unloadable_sp_location);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->unloadable_sp_size, dst->unloadable_sp_size);
    SAFE_TRANSFER_FUNC(uint32_t, bfd_putb32, src->checksum, dst->checksum);
}

static int convert_and_check(uint32_t *dest, uint32_t *src) {
    *dest = bfd_getb32(src);
    return *dest == UINT32_MAX ? -1 : 0;
}

static int som_swap_space_dictionary_in(struct som_external_space_dictionary_record *src, struct som_space_dictionary_record *dst) {
    unsigned int flags;

    if (convert_and_check(&dst->name, &src->name) ||
        convert_and_check(&dst->space_number, &src->space_number) ||
        convert_and_check(&dst->subspace_index, &src->subspace_index) ||
        convert_and_check(&dst->subspace_quantity, &src->subspace_quantity) ||
        convert_and_check(&dst->loader_fix_index, &src->loader_fix_index) ||
        convert_and_check(&dst->loader_fix_quantity, &src->loader_fix_quantity) ||
        convert_and_check(&dst->init_pointer_index, &src->init_pointer_index) ||
        convert_and_check(&dst->init_pointer_quantity, &src->init_pointer_quantity)) {
        return -1;
    }

    flags = bfd_getb32(&src->flags);
    dst->is_loadable = (flags & SOM_SPACE_IS_LOADABLE) != 0;
    dst->is_defined = (flags & SOM_SPACE_IS_DEFINED) != 0;
    dst->is_private = (flags & SOM_SPACE_IS_PRIVATE) != 0;
    dst->has_intermediate_code = (flags & SOM_SPACE_HAS_INTERMEDIATE_CODE) != 0;
    dst->is_tspecific = (flags & SOM_SPACE_IS_TSPECIFIC) != 0;
    dst->reserved = 0;
    dst->sort_key = (flags >> SOM_SPACE_SORT_KEY_SH) & SOM_SPACE_SORT_KEY_MASK;
    dst->reserved2 = 0;

    return 0;
}

static void som_swap_space_dictionary_out(struct som_space_dictionary_record *src, struct som_external_space_dictionary_record *dst) {
    unsigned int flags = 0;

    bfd_putb32(src->name, dst->name);

    flags |= src->is_loadable ? SOM_SPACE_IS_LOADABLE : 0;
    flags |= src->is_defined ? SOM_SPACE_IS_DEFINED : 0;
    flags |= src->is_private ? SOM_SPACE_IS_PRIVATE : 0;
    flags |= src->has_intermediate_code ? SOM_SPACE_HAS_INTERMEDIATE_CODE : 0;
    flags |= src->is_tspecific ? SOM_SPACE_IS_TSPECIFIC : 0;
    flags |= (src->sort_key & SOM_SPACE_SORT_KEY_MASK) << SOM_SPACE_SORT_KEY_SH;

    bfd_putb32(flags, dst->flags);
    
    bfd_putb32(src->space_number, dst->space_number);
    bfd_putb32(src->subspace_index, dst->subspace_index);
    bfd_putb32(src->subspace_quantity, dst->subspace_quantity);
    bfd_putb32(src->loader_fix_index, dst->loader_fix_index);
    bfd_putb32(src->loader_fix_quantity, dst->loader_fix_quantity);
    bfd_putb32(src->init_pointer_index, dst->init_pointer_index);
    bfd_putb32(src->init_pointer_quantity, dst->init_pointer_quantity);
}

static void som_swap_subspace_dictionary_in(
    struct som_external_subspace_dictionary_record *src,
    struct som_subspace_dictionary_record *dst) {
    
    unsigned int flags = bfd_getb32(src->flags);

    dst->space_index = bfd_getb32(src->space_index);
    dst->access_control_bits = (flags >> SOM_SUBSPACE_ACCESS_CONTROL_BITS_SH) & SOM_SUBSPACE_ACCESS_CONTROL_BITS_MASK;
    dst->memory_resident = (flags & SOM_SUBSPACE_MEMORY_RESIDENT) != 0;
    dst->dup_common = (flags & SOM_SUBSPACE_DUP_COMMON) != 0;
    dst->is_common = (flags & SOM_SUBSPACE_IS_COMMON) != 0;
    dst->is_loadable = (flags & SOM_SUBSPACE_IS_LOADABLE) != 0;
    dst->quadrant = (flags >> SOM_SUBSPACE_QUADRANT_SH) & SOM_SUBSPACE_QUADRANT_MASK;
    dst->initially_frozen = (flags & SOM_SUBSPACE_INITIALLY_FROZEN) != 0;
    dst->is_first = (flags & SOM_SUBSPACE_IS_FIRST) != 0;
    dst->code_only = (flags & SOM_SUBSPACE_CODE_ONLY) != 0;
    dst->sort_key = (flags >> SOM_SUBSPACE_SORT_KEY_SH) & SOM_SUBSPACE_SORT_KEY_MASK;
    dst->replicate_init = (flags & SOM_SUBSPACE_REPLICATE_INIT) != 0;
    dst->continuation = (flags & SOM_SUBSPACE_CONTINUATION) != 0;
    dst->is_tspecific = (flags & SOM_SUBSPACE_IS_TSPECIFIC) != 0;
    dst->is_comdat = (flags & SOM_SUBSPACE_IS_COMDAT) != 0;
    dst->reserved = 0;

    dst->file_loc_init_value = bfd_getb32(src->file_loc_init_value);
    dst->initialization_length = bfd_getb32(src->initialization_length);
    dst->subspace_start = bfd_getb32(src->subspace_start);
    dst->subspace_length = bfd_getb32(src->subspace_length);
    dst->alignment = bfd_getb32(src->alignment);
    dst->name = bfd_getb32(src->name);
    dst->fixup_request_index = bfd_getb32(src->fixup_request_index);
    dst->fixup_request_quantity = bfd_getb32(src->fixup_request_quantity);
}

static void som_swap_subspace_dictionary_record_out(
    struct som_subspace_dictionary_record *src,
    struct som_external_subspace_dictionary_record *dst) {
    unsigned int flags = 0;

    bfd_putb32(src->space_index, dst->space_index);

    flags |= ((src->access_control_bits & SOM_SUBSPACE_ACCESS_CONTROL_BITS_MASK) 
             << SOM_SUBSPACE_ACCESS_CONTROL_BITS_SH);
    flags |= src->memory_resident ? SOM_SUBSPACE_MEMORY_RESIDENT : 0;
    flags |= src->dup_common ? SOM_SUBSPACE_DUP_COMMON : 0;
    flags |= src->is_common ? SOM_SUBSPACE_IS_COMMON : 0;
    flags |= src->is_loadable ? SOM_SUBSPACE_IS_LOADABLE : 0;
    flags |= ((src->quadrant & SOM_SUBSPACE_QUADRANT_MASK)
             << SOM_SUBSPACE_QUADRANT_SH);
    flags |= src->initially_frozen ? SOM_SUBSPACE_INITIALLY_FROZEN : 0;
    flags |= src->is_first ? SOM_SUBSPACE_IS_FIRST : 0;
    flags |= src->code_only ? SOM_SUBSPACE_CODE_ONLY : 0;
    flags |= ((src->sort_key & SOM_SUBSPACE_SORT_KEY_MASK)
             << SOM_SUBSPACE_SORT_KEY_SH);
    flags |= src->replicate_init ? SOM_SUBSPACE_REPLICATE_INIT : 0;
    flags |= src->continuation ? SOM_SUBSPACE_CONTINUATION : 0;
    flags |= src->is_tspecific ? SOM_SUBSPACE_IS_TSPECIFIC : 0;
    flags |= src->is_comdat ? SOM_SUBSPACE_IS_COMDAT : 0;

    bfd_putb32(flags, dst->flags);
    bfd_putb32(src->file_loc_init_value, dst->file_loc_init_value);
    bfd_putb32(src->initialization_length, dst->initialization_length);
    bfd_putb32(src->subspace_start, dst->subspace_start);
    bfd_putb32(src->subspace_length, dst->subspace_length);
    bfd_putb32(src->alignment, dst->alignment);
    bfd_putb32(src->name, dst->name);
    bfd_putb32(src->fixup_request_index, dst->fixup_request_index);
    bfd_putb32(src->fixup_request_quantity, dst->fixup_request_quantity);
}

#include <stdint.h>

#define SOM_AUX_ID_MANDATORY (1U << 0)
#define SOM_AUX_ID_COPY      (1U << 1)
#define SOM_AUX_ID_APPEND    (1U << 2)
#define SOM_AUX_ID_IGNORE    (1U << 3)
#define SOM_AUX_ID_TYPE_SH   4
#define SOM_AUX_ID_TYPE_MASK 0xF

struct som_external_aux_id {
    uint8_t flags[4];
    uint8_t length[4];
};

struct som_aux_id {
    int mandatory;
    int copy;
    int append;
    int ignore;
    unsigned int type;
    unsigned int length;
};

unsigned int bfd_getb32(const uint8_t *buf) {
    return ((unsigned int)buf[0] << 24) | ((unsigned int)buf[1] << 16) | 
           ((unsigned int)buf[2] << 8) | (unsigned int)buf[3];
}

static void som_swap_aux_id_in(struct som_external_aux_id *src, struct som_aux_id *dst) {
    unsigned int flags = bfd_getb32(src->flags);

    dst->mandatory = !!(flags & SOM_AUX_ID_MANDATORY);
    dst->copy = !!(flags & SOM_AUX_ID_COPY);
    dst->append = !!(flags & SOM_AUX_ID_APPEND);
    dst->ignore = !!(flags & SOM_AUX_ID_IGNORE);
    dst->type = (flags >> SOM_AUX_ID_TYPE_SH) & SOM_AUX_ID_TYPE_MASK;
    dst->length = bfd_getb32(src->length);
}

static void som_swap_aux_id_out(struct som_aux_id *src, struct som_external_aux_id *dst) {
    unsigned int flags = 0;
    flags |= (src->mandatory ? SOM_AUX_ID_MANDATORY : 0)
          |  (src->copy ? SOM_AUX_ID_COPY : 0)
          |  (src->append ? SOM_AUX_ID_APPEND : 0)
          |  (src->ignore ? SOM_AUX_ID_IGNORE : 0)
          |  ((src->type & SOM_AUX_ID_TYPE_MASK) << SOM_AUX_ID_TYPE_SH);
    bfd_putb32(flags, dst->flags);
    bfd_putb32(src->length, dst->length);
}

static void swapStringAuxHeaderOut(struct som_string_auxhdr *src, struct som_external_string_auxhdr *dst) {
    if (src == NULL || dst == NULL) {
        return;
    }
    som_swap_aux_id_out(&src->header_id, &dst->header_id);
    bfd_putb32(src->string_length, dst->string_length);
}

void swapClockOut(const struct som_clock_time *srcClock, struct som_external_clock_time *dstClock) {
  if (srcClock == NULL || dstClock == NULL) {
    return;
  }
  // ... perform the necessary swapping operation
}

void swapCompilationUnit(const struct som_compilation_unit *src, struct som_external_compilation_unit *dst) {
  if (src == NULL || dst == NULL) {
    return;
  }

  bfd_putb32(src->name.strx, dst->name);
  bfd_putb32(src->language_name.strx, dst->language_name);
  bfd_putb32(src->product_id.strx, dst->product_id);
  bfd_putb32(src->version_id.strx, dst->version_id);
  bfd_putb32(src->flags, dst->flags);

  swapClockOut(&src->compile_time, &dst->compile_time);
  swapClockOut(&src->source_time, &dst->source_time);
}

static void
som_swap_exec_auxhdr_in(struct som_external_exec_auxhdr *src,
                        struct som_exec_auxhdr *dst)
{
  if (!src || !dst) {
    return;
  }

  som_swap_aux_id_in(&src->som_auxhdr, &dst->som_auxhdr);

  uint32_t *src_fields[] = { 
    &src->exec_tsize, &src->exec_tmem, &src->exec_tfile, 
    &src->exec_dsize, &src->exec_dmem, &src->exec_dfile, 
    &src->exec_bsize, &src->exec_entry, &src->exec_flags, &src->exec_bfill 
  };
  
  uint32_t *dst_fields[] = { 
    &dst->exec_tsize, &dst->exec_tmem, &dst->exec_tfile, 
    &dst->exec_dsize, &dst->exec_dmem, &dst->exec_dfile, 
    &dst->exec_bsize, &dst->exec_entry, &dst->exec_flags, &dst->exec_bfill 
  };
  
  for (size_t i = 0; i < sizeof(src_fields) / sizeof(src_fields[0]); ++i) {
    *dst_fields[i] = bfd_getb32(*src_fields[i]);
  }
}

static void som_swap_exec_auxhdr_out(struct som_exec_auxhdr *src, struct som_external_exec_auxhdr *dst) {
    if (!src || !dst) return;

    som_swap_aux_id_out(&src->som_auxhdr, &dst->som_auxhdr);

    uint32_t *src_fields[] = {
        &src->exec_tsize, &src->exec_tmem, &src->exec_tfile, 
        &src->exec_dsize, &src->exec_dmem, &src->exec_dfile, 
        &src->exec_bsize, &src->exec_entry, &src->exec_flags, &src->exec_bfill
    };
    
    uint32_t *dst_fields[] = {
        dst->exec_tsize, dst->exec_tmem, dst->exec_tfile, 
        dst->exec_dsize, dst->exec_dmem, dst->exec_dfile, 
        dst->exec_bsize, dst->exec_entry, dst->exec_flags, dst->exec_bfill
    };
    
    for (size_t i = 0; i < sizeof(src_fields)/sizeof(src_fields[0]); i++) {
        bfd_putb32(*src_fields[i], dst_fields[i]);
    }
}

static int convert_and_assign(uint16_t* dest, uint16_t src) {
    *dest = bfd_getb16(src);
    return *dest != 0;
}

static int convert_and_assign32(uint32_t* dest, uint32_t src) {
    *dest = bfd_getb32(src);
    return *dest != 0;
}

static int convert_lst_header(const struct som_external_lst_header *src, struct som_lst_header *dst) {
    if (!convert_and_assign(&dst->system_id, src->system_id) ||
        !convert_and_assign(&dst->a_magic, src->a_magic) ||
        !convert_and_assign32(&dst->version_id, src->version_id) ||
        !convert_and_assign32(&dst->hash_loc, src->hash_loc) ||
        !convert_and_assign32(&dst->hash_size, src->hash_size) ||
        !convert_and_assign32(&dst->module_count, src->module_count) ||
        !convert_and_assign32(&dst->module_limit, src->module_limit) ||
        !convert_and_assign32(&dst->dir_loc, src->dir_loc) ||
        !convert_and_assign32(&dst->export_loc, src->export_loc) ||
        !convert_and_assign32(&dst->export_count, src->export_count) ||
        !convert_and_assign32(&dst->import_loc, src->import_loc) ||
        !convert_and_assign32(&dst->aux_loc, src->aux_loc) ||
        !convert_and_assign32(&dst->aux_size, src->aux_size) ||
        !convert_and_assign32(&dst->string_loc, src->string_loc) ||
        !convert_and_assign32(&dst->string_size, src->string_size) ||
        !convert_and_assign32(&dst->free_list, src->free_list) ||
        !convert_and_assign32(&dst->file_end, src->file_end) ||
        !convert_and_assign32(&dst->checksum, src->checksum))
    {
        return 0;
    }

    return som_swap_clock_in(&src->file_time, &dst->file_time) == 0;
}

static int som_swap_lst_header_in(const struct som_external_lst_header *src, struct som_lst_header *dst) {
    return convert_lst_header(src, dst);
}

/* Perform some initialization for an object.  Save results of this
   initialization in the BFD.  */

static bfd_cleanup som_object_setup(bfd *abfd, struct som_header *file_hdrp, struct som_exec_auxhdr *aux_hdrp, unsigned long current_offset) {
    if (!som_mkobject(abfd)) {
        return NULL;
    }

    abfd->flags = BFD_NO_FLAGS;
    if (file_hdrp->symbol_total) {
        abfd->flags |= HAS_LINENO | HAS_DEBUG | HAS_SYMS | HAS_LOCALS;
    }

    switch (file_hdrp->a_magic) {
        case DEMAND_MAGIC:
            abfd->flags |= (D_PAGED | WP_TEXT | EXEC_P);
            break;
        case SHARE_MAGIC:
            abfd->flags |= (WP_TEXT | EXEC_P);
            break;
        case EXEC_MAGIC:
            abfd->flags |= EXEC_P;
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
    }

    obj_som_exec_hdr(abfd) = aux_hdrp;

    obj_som_exec_data(abfd) = bfd_zalloc(abfd, sizeof(struct som_exec_data));
    if (obj_som_exec_data(abfd) == NULL) {
        return NULL;
    }

    if (aux_hdrp) {
        int found = 0;

        for (asection *section = abfd->sections; section; section = section->next) {
            if (!(section->flags & SEC_CODE)) continue;
            bfd_vma entry = aux_hdrp->exec_entry + aux_hdrp->exec_tmem;
            if (entry >= section->vma && entry < section->vma + section->size) {
                found = 1;
                break;
            }
        }

        if ((aux_hdrp->exec_entry == 0 && !(abfd->flags & DYNAMIC)) || (aux_hdrp->exec_entry & 0x3) != 0 || !found) {
            abfd->start_address = aux_hdrp->exec_flags;
            obj_som_exec_data(abfd)->exec_flags = aux_hdrp->exec_entry;
        } else {
            abfd->start_address = aux_hdrp->exec_entry + current_offset;
            obj_som_exec_data(abfd)->exec_flags = aux_hdrp->exec_flags;
        }
    }

    obj_som_exec_data(abfd)->version_id = file_hdrp->version_id;

    bfd_default_set_arch_mach(abfd, bfd_arch_hppa, pa10);
    abfd->symcount = file_hdrp->symbol_total;

    obj_som_stringtab(abfd) = NULL;
    obj_som_symtab(abfd) = NULL;
    obj_som_sorted_syms(abfd) = NULL;
    obj_som_stringtab_size(abfd) = file_hdrp->symbol_strings_size;
    obj_som_sym_filepos(abfd) = file_hdrp->symbol_location + current_offset;
    obj_som_str_filepos(abfd) = file_hdrp->symbol_strings_location + current_offset;
    obj_som_reloc_filepos(abfd) = file_hdrp->fixup_request_location + current_offset;
    obj_som_exec_data(abfd)->system_id = file_hdrp->system_id;

    return _bfd_no_cleanup;
}

/* Convert all of the space and subspace info into BFD sections.  Each space
   contains a number of subspaces, which in turn describe the mapping between
   regions of the exec file, and the address space that the program runs in.
   BFD sections which correspond to spaces will overlap the sections for the
   associated subspaces.  */

static bool
setup_sections(bfd *abfd,
               struct som_header *file_hdr,
               unsigned long current_offset) {
    char *space_strings = NULL;
    unsigned int total_subspaces = 0;
    asection **subspace_sections = NULL;
    size_t amt;

    amt = file_hdr->space_strings_size;
    if (amt == (size_t)-1) {
        bfd_set_error(bfd_error_no_memory);
        return false;
    }
    if (bfd_seek(abfd, current_offset + file_hdr->space_strings_location, SEEK_SET) != 0)
        return false;
    space_strings = (char *)_bfd_malloc_and_read(abfd, amt + 1, amt);
    if (!space_strings)
        return false;
    space_strings[amt] = 0;

    for (unsigned int space_index = 0; space_index < file_hdr->space_total; space_index++) {
        struct som_space_dictionary_record space;
        struct som_external_space_dictionary_record ext_space;
        char *space_name;

        if (bfd_seek(abfd, current_offset + file_hdr->space_location + space_index * sizeof(ext_space), SEEK_SET) != 0)
            goto error_return;
        if (bfd_read(&ext_space, sizeof(ext_space), abfd) != sizeof(ext_space))
            goto error_return;

        som_swap_space_dictionary_in(&ext_space, &space);

        if (space.name >= file_hdr->space_strings_size)
            goto error_return;
        
        space_name = space_strings + space.name;
        char *newname = bfd_alloc(abfd, strlen(space_name) + 1);
        if (!newname)
            goto error_return;
        strcpy(newname, space_name);

        asection *space_asect = bfd_make_section_anyway(abfd, newname);
        if (!space_asect)
            goto error_return;

        space_asect->flags = space.is_loadable == 0 ? space_asect->flags | SEC_DEBUGGING : space_asect->flags;
        if (!bfd_som_set_section_attributes(space_asect, space.is_defined, space.is_private, space.sort_key, space.space_number))
            goto error_return;

        if (space.subspace_quantity == 0)
            continue;

        if (bfd_seek(abfd, current_offset + file_hdr->subspace_location + space.subspace_index * sizeof(struct som_external_subspace_dictionary_record), SEEK_SET) != 0)
            goto error_return;
        struct som_external_subspace_dictionary_record ext_subspace;
        if (bfd_read(&ext_subspace, sizeof(ext_subspace), abfd) != sizeof(ext_subspace))
            goto error_return;

        struct som_subspace_dictionary_record subspace;
        som_swap_subspace_dictionary_in(&ext_subspace, &subspace);

        space_asect->vma = subspace.subspace_start;
        space_asect->filepos = subspace.file_loc_init_value + current_offset;
        space_asect->alignment_power = exact_log2(subspace.alignment);
        if (space_asect->alignment_power == (unsigned)-1)
            goto error_return;

        struct som_subspace_dictionary_record save_subspace = {0};

        bfd_size_type space_size = 0;

        if (bfd_seek(abfd, current_offset + file_hdr->subspace_location + space.subspace_index * sizeof(struct som_external_subspace_dictionary_record), SEEK_SET) != 0)
            goto error_return;

        for (unsigned int subspace_index = 0; subspace_index < space.subspace_quantity; subspace_index++) {
            asection *subspace_asect;
            char *subspace_name;

            if (bfd_read(&ext_subspace, sizeof(ext_subspace), abfd) != sizeof(ext_subspace))
                goto error_return;
            som_swap_subspace_dictionary_in(&ext_subspace, &subspace);

            if (subspace.name >= file_hdr->space_strings_size)
                goto error_return;

            subspace_name = space_strings + subspace.name;

            newname = bfd_alloc(abfd, strlen(subspace_name) + 1);
            if (!newname)
                goto error_return;
            strcpy(newname, subspace_name);

            subspace_asect = bfd_make_section_anyway(abfd, newname);
            if (!subspace_asect)
                goto error_return;

            if (!bfd_som_set_subsection_attributes(subspace_asect, space_asect, subspace.access_control_bits, subspace.sort_key, subspace.quadrant, subspace.is_comdat, subspace.is_common, subspace.dup_common))
                goto error_return;

            total_subspaces++;
            subspace_asect->target_index = bfd_tell(abfd) - sizeof(subspace);

            switch (subspace.access_control_bits >> 4) {
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

            if (subspace.is_comdat || subspace.is_common || subspace.dup_common)
                subspace_asect->flags |= SEC_LINK_ONCE;

            if (subspace.subspace_length > 0)
                subspace_asect->flags |= SEC_HAS_CONTENTS;

            if (subspace.is_loadable)
                subspace_asect->flags |= SEC_ALLOC | SEC_LOAD;
            else
                subspace_asect->flags |= SEC_DEBUGGING;

            if (subspace.code_only)
                subspace_asect->flags |= SEC_CODE;

            if (subspace.file_loc_init_value == 0 && subspace.initialization_length == 0)
                subspace_asect->flags &= ~(SEC_DATA | SEC_LOAD | SEC_HAS_CONTENTS);

            if (subspace.fixup_request_quantity != 0) {
                subspace_asect->flags |= SEC_RELOC;
                subspace_asect->rel_filepos = subspace.fixup_request_index;
                som_section_data(subspace_asect)->reloc_size = subspace.fixup_request_quantity;
                subspace_asect->reloc_count = (unsigned)-1;
            }

            if (subspace.file_loc_init_value > save_subspace.file_loc_init_value)
                save_subspace = subspace;

            subspace_asect->vma = subspace.subspace_start;
            subspace_asect->size = subspace.subspace_length;
            subspace_asect->filepos = subspace.file_loc_init_value + current_offset;
            subspace_asect->alignment_power = exact_log2(subspace.alignment);
            if (subspace_asect->alignment_power == (unsigned)-1)
                goto error_return;

            space_size += subspace.subspace_length;
        }

        if (!save_subspace.file_loc_init_value) {
            space_asect->size = 0;
        } else {
            space_asect->size = (file_hdr->a_magic != RELOC_MAGIC) ?
                (save_subspace.subspace_start - space_asect->vma + save_subspace.subspace_length) :
                space_size;
        }
    }

    if (_bfd_mul_overflow(total_subspaces, sizeof(asection *), &amt)) {
        bfd_set_error(bfd_error_file_too_big);
        goto error_return;
    }

    subspace_sections = bfd_malloc(amt);
    if (!subspace_sections)
        goto error_return;

    asection *section;
    unsigned int index = 0;
    for (section = abfd->sections; section; section = section->next) {
        if (!som_is_subspace(section))
            continue;
        subspace_sections[index++] = section;
    }

    qsort(subspace_sections, total_subspaces, sizeof(asection *), compare_subspaces);

    for (unsigned int i = 0; i < total_subspaces; i++) {
        subspace_sections[i]->target_index = i;
    }

    free(space_strings);
    free(subspace_sections);
    return true;

error_return:
    free(space_strings);
    free(subspace_sections);
    return false;
}


/* Read in a SOM object and make it into a BFD.  */

#include <stdbool.h>

static bfd_cleanup som_object_p(bfd *abfd) {
    struct som_external_header ext_file_hdr;
    struct som_header file_hdr;
    struct som_exec_auxhdr *aux_hdr_ptr = NULL;
    unsigned long current_offset = 0;
    struct som_external_lst_header ext_lst_header;
    struct som_external_som_entry ext_som_entry;
    size_t amt;
    unsigned int loc;
    
    const int HEADER_SIZE = sizeof(struct som_external_header);
    const int LST_HEADER_SIZE = sizeof(struct som_external_lst_header);
    const int ENTRY_SIZE = sizeof(struct som_external_som_entry);
    const int EXEC_AUXHDR_SIZE = sizeof(struct som_external_exec_auxhdr);

    bool set_error_if_needed() {
        if (bfd_get_error() != bfd_error_system_call) {
            bfd_set_error(bfd_error_wrong_format);
        }
        return NULL;
    }
    
    if (bfd_read(&ext_file_hdr, HEADER_SIZE, abfd) != HEADER_SIZE) {
        return set_error_if_needed();
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

        case EXECLIBMAGIC: {
            if (bfd_seek(abfd, 0, SEEK_SET) != 0) {
                return set_error_if_needed();
            }

            if (bfd_read(&ext_lst_header, LST_HEADER_SIZE, abfd) != LST_HEADER_SIZE) {
                return set_error_if_needed();
            }

            loc = bfd_getb32(ext_lst_header.dir_loc);
            if (bfd_seek(abfd, loc, SEEK_SET) != 0) {
                return set_error_if_needed();
            }

            if (bfd_read(&ext_som_entry, ENTRY_SIZE, abfd) != ENTRY_SIZE) {
                return set_error_if_needed();
            }

            current_offset = bfd_getb32(ext_som_entry.location);
            if (bfd_seek(abfd, current_offset, SEEK_SET) != 0) {
                return set_error_if_needed();
            }

            if (bfd_read(&ext_file_hdr, HEADER_SIZE, abfd) != HEADER_SIZE) {
                return set_error_if_needed();
            }

            som_swap_header_in(&ext_file_hdr, &file_hdr);

            break;
        }

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

        aux_hdr_ptr = bfd_zalloc(abfd, sizeof(*aux_hdr_ptr));
        if (aux_hdr_ptr == NULL) {
            return NULL;
        }
        
        if (bfd_read(&ext_exec_auxhdr, EXEC_AUXHDR_SIZE, abfd) != EXEC_AUXHDR_SIZE) {
            return set_error_if_needed();
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

bool som_mkobject(bfd *abfd) {
    abfd->tdata.som_data = bfd_zalloc(abfd, sizeof(struct som_data_struct));
    return abfd->tdata.som_data != NULL;
}

/* Initialize some information in the file header.  This routine makes
   not attempt at doing the right thing for a full executable; it
   is only meant to handle relocatable objects.  */

static bool som_prep_headers(bfd *abfd) {
    struct som_header *file_hdr = bfd_zalloc(abfd, sizeof(struct som_header));
    if (file_hdr == NULL) return false;
    obj_som_file_hdr(abfd) = file_hdr;

    if (abfd->flags & (EXEC_P | DYNAMIC)) {
        obj_som_exec_hdr(abfd) = bfd_zalloc(abfd, sizeof(struct som_exec_auxhdr));
        if (obj_som_exec_hdr(abfd) == NULL) return false;

        if (abfd->flags & D_PAGED) {
            file_hdr->a_magic = DEMAND_MAGIC;
        } else if (abfd->flags & WP_TEXT) {
            file_hdr->a_magic = SHARE_MAGIC;
        } else 
#ifdef SHL_MAGIC
        if (abfd->flags & DYNAMIC) {
            file_hdr->a_magic = SHL_MAGIC;
        } else 
#endif
        {
            file_hdr->a_magic = EXEC_MAGIC;
        }
    } else {
        file_hdr->a_magic = RELOC_MAGIC;
    }

    file_hdr->file_time.secs = 0;
    file_hdr->file_time.nanosecs = 0;
    file_hdr->entry_space = 0;
    file_hdr->entry_subspace = 0;
    file_hdr->entry_offset = 0;
    file_hdr->presumed_dp = 0;

    for (asection *section = abfd->sections; section != NULL; section = section->next) {
        if (!som_is_space(section) && !som_is_subspace(section)) continue;

        size_t amt;
        void *dict = NULL;

        if (som_is_space(section)) {
            amt = sizeof(struct som_space_dictionary_record);
            dict = bfd_zalloc(abfd, amt);
            if (dict == NULL) return false;

            struct som_space_dictionary_record *space_dict = dict;
            som_section_data(section)->space_dict = space_dict;
            space_dict->loader_fix_index = -1;
            space_dict->init_pointer_index = -1;
            space_dict->sort_key = som_section_data(section)->copy_data->sort_key;
            space_dict->is_defined = som_section_data(section)->copy_data->is_defined;
            space_dict->is_private = som_section_data(section)->copy_data->is_private;
            space_dict->space_number = som_section_data(section)->copy_data->space_number;
        } else {
            amt = sizeof(struct som_subspace_dictionary_record);
            dict = bfd_zalloc(abfd, amt);
            if (dict == NULL) return false;

            struct som_subspace_dictionary_record *subspace_dict = dict;
            som_section_data(section)->subspace_dict = subspace_dict;
            if (section->flags & SEC_ALLOC) subspace_dict->is_loadable = 1;
            if (section->flags & SEC_CODE) subspace_dict->code_only = 1;
            subspace_dict->subspace_start = section->vma;
            subspace_dict->subspace_length = section->size;
            subspace_dict->initialization_length = section->size;
            subspace_dict->alignment = 1 << section->alignment_power;
            subspace_dict->sort_key = som_section_data(section)->copy_data->sort_key;
            subspace_dict->access_control_bits = som_section_data(section)->copy_data->access_control_bits;
            subspace_dict->quadrant = som_section_data(section)->copy_data->quadrant;
            subspace_dict->is_comdat = som_section_data(section)->copy_data->is_comdat;
            subspace_dict->is_common = som_section_data(section)->copy_data->is_common;
            subspace_dict->dup_common = som_section_data(section)->copy_data->dup_common;
        }
    }
    return true;
}

/* Return TRUE if the given section is a SOM space, FALSE otherwise.  */

bool som_is_space(asection *section) {
    som_section_data_type *data = som_section_data(section);
    return data->copy_data && 
           (data->copy_data->container == section || 
            data->copy_data->container->output_section == section);
}

/* Return TRUE if the given section is a SOM subspace, FALSE otherwise.  */

static bool som_is_subspace(asection *section) {
    som_section_data_t *section_data = som_section_data(section);
    copy_data_t *copy_data = section_data->copy_data;
    
    if (copy_data == NULL) {
        return false;
    }
    
    return !(copy_data->container == section || copy_data->container->output_section == section);
}

/* Return TRUE if the given space contains the given subspace.  It
   is safe to assume space really is a space, and subspace really
   is a subspace.  */

static bool som_is_container(asection *space, asection *subspace) {
    section_data *subspace_data = som_section_data(subspace);
    if (subspace_data == NULL || subspace_data->copy_data == NULL || subspace_data->copy_data->container == NULL) {
        return false;
    }
    return (subspace_data->copy_data->container == space) ||
           (subspace_data->copy_data->container->output_section == space);
}

/* Count and return the number of spaces attached to the given BFD.  */

static unsigned long som_count_spaces(bfd *abfd) {
    if (abfd == NULL) {
        return 0;
    }

    unsigned long count = 0;
    for (asection *section = abfd->sections; section != NULL; section = section->next) {
        if (som_is_space(section)) {
            count++;
        }
    }
    
    return count;
}

/* Count the number of subspaces attached to the given BFD.  */

static unsigned long som_count_subspaces(bfd *abfd) {
    unsigned long count = 0;

    if (!abfd) {
        return count;
    }

    for (asection *section = abfd->sections; section; section = section->next) {
        if (som_is_subspace(section)) {
            count++;
        }
    }
    
    return count;
}

/* Return -1, 0, 1 indicating the relative ordering of sym1 and sym2.

   We desire symbols to be ordered starting with the symbol with the
   highest relocation count down to the symbol with the lowest relocation
   count.  Doing so compacts the relocation stream.  */

int compare_symbols(const void *arg1, const void *arg2) {
    asymbol **sym1 = (asymbol **)arg1;
    asymbol **sym2 = (asymbol **)arg2;

    unsigned int count1 = ((*sym1)->flags & BSF_SECTION_SYM) ?
                          (*sym1)->udata.i : som_symbol_data(*sym1)->reloc_count;
    unsigned int count2 = ((*sym2)->flags & BSF_SECTION_SYM) ?
                          (*sym2)->udata.i : som_symbol_data(*sym2)->reloc_count;

    return (count1 > count2) ? -1 : (count1 < count2) ? 1 : 0;
}

/* Return -1, 0, 1 indicating the relative ordering of subspace1
   and subspace.  */

static int compare_subspaces(const void *arg1, const void *arg2) {
  asection **subspace1 = (asection **)arg1;
  asection **subspace2 = (asection **)arg2;

  return ((*subspace1)->target_index > (*subspace2)->target_index) - 
         ((*subspace1)->target_index < (*subspace2)->target_index);
}

/* Perform various work in preparation for emitting the fixup stream.  */

#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

static bool som_prep_for_fixups(bfd *abfd, asymbol **syms, unsigned long num_syms) {
    if (num_syms == 0) return true;

    // Initialize relocation counts for symbols
    for (unsigned long i = 0; i < num_syms; i++) {
        if (som_symbol_data(syms[i]) == NULL || syms[i]->flags & BSF_SECTION_SYM) {
            syms[i]->flags |= BSF_SECTION_SYM;
            syms[i]->udata.i = 0;
        } else {
            som_symbol_data(syms[i])->reloc_count = 0;
        }
    }

    // Count relocations for each symbol
    for (asection *section = abfd->sections; section != NULL; section = section->next) {
        if (section->reloc_count <= 0) continue;

        for (int j = 1; j < section->reloc_count; j++) {
            arelent *reloc = section->orelocation[j];
            if (reloc->sym_ptr_ptr == NULL || bfd_is_abs_section((*reloc->sym_ptr_ptr)->section)) continue;

            int scale = (reloc->howto->type == R_DP_RELATIVE || reloc->howto->type == R_CODE_ONE_SYMBOL) ? 2 : 1;

            if ((*reloc->sym_ptr_ptr)->flags & BSF_SECTION_SYM) {
                (*reloc->sym_ptr_ptr)->udata.i += scale;
            } else {
                som_symbol_data(*reloc->sym_ptr_ptr)->reloc_count += scale;
            }
        }
    }

    // Allocate and sort symbols
    size_t amt;
    if (_bfd_mul_overflow(num_syms, sizeof(asymbol *), &amt)) {
        bfd_set_error(bfd_error_no_memory);
        return false;
    }
    asymbol **sorted_syms = bfd_zalloc(abfd, amt);
    if (sorted_syms == NULL) return false;
    memcpy(sorted_syms, syms, num_syms * sizeof(asymbol *));
    qsort(sorted_syms, num_syms, sizeof(asymbol *), compare_syms);
    obj_som_sorted_syms(abfd) = sorted_syms;

    // Set indexes for sorted symbols
    for (unsigned long i = 0; i < num_syms; i++) {
        if (sorted_syms[i]->flags & BSF_SECTION_SYM) {
            sorted_syms[i]->udata.i = i;
        } else {
            som_symbol_data(sorted_syms[i])->index = i;
        }
    }
    return true;
}

static bool som_write_fixups(bfd *abfd, unsigned long current_offset, unsigned int *total_reloc_sizep) {
    unsigned int i, j;
    unsigned char tmp_space[SOM_TMP_BUFSIZE] = {0};
    unsigned char *p;
    unsigned int total_reloc_size = 0;
    unsigned int subspace_reloc_size = 0;
    unsigned int num_spaces = obj_som_file_hdr(abfd)->space_total;
    asection *section = abfd->sections;

    p = tmp_space;

    for (i = 0; i < num_spaces; i++) {
        asection *subsection;
        while (section && !som_is_space(section))
            section = section->next;
        if (!section)
            break;

        for (subsection = abfd->sections; subsection != NULL; subsection = subsection->next) {
            unsigned int reloc_offset = 0;
            unsigned int current_rounding_mode = R_N_MODE;
#ifndef NO_PCREL_MODES
            unsigned int current_call_mode = R_SHORT_PCREL_MODE;
#endif

            if (!som_is_subspace(subsection) || !som_is_container(section, subsection))
                continue;

            if ((subsection->flags & SEC_HAS_CONTENTS) == 0) {
                som_section_data(subsection)->subspace_dict->fixup_request_index = -1;
                continue;
            }

            som_section_data(subsection)->subspace_dict->fixup_request_index = total_reloc_size;

            if (bfd_seek(abfd, current_offset + total_reloc_size, SEEK_SET) != 0)
                return false;

            p = tmp_space;
            subspace_reloc_size = 0;
            som_initialize_reloc_queue(reloc_queue);

            for (j = 0; j < subsection->reloc_count; j++) {
                arelent *bfd_reloc = subsection->orelocation[j];
                if (bfd_reloc->address < reloc_offset ||
                    !bfd_reloc_offset_in_range(bfd_reloc->howto, abfd, subsection, bfd_reloc->address)) {
                    bfd_set_error(bfd_error_bad_value);
                    return false;
                }

                int sym_num = ((*bfd_reloc->sym_ptr_ptr)->flags & BSF_SECTION_SYM)
                                  ? (*bfd_reloc->sym_ptr_ptr)->udata.i
                                  : som_symbol_data(*bfd_reloc->sym_ptr_ptr)->index;

                if (p - tmp_space + 512 > SOM_TMP_BUFSIZE) {
                    size_t amt = p - tmp_space;
                    if (bfd_write(tmp_space, amt, abfd) != amt)
                        return false;
                    p = tmp_space;
                    som_initialize_reloc_queue(reloc_queue);
                }

                unsigned int skip = bfd_reloc->address - reloc_offset;
                p = som_reloc_skip(abfd, skip, p, &subspace_reloc_size, reloc_queue);
                reloc_offset = bfd_reloc->address + bfd_reloc->howto->size;

                switch (bfd_reloc->howto->type) {
                    case R_PCREL_CALL:
                    case R_ABS_CALL:
                        p = som_reloc_call(abfd, p, &subspace_reloc_size, bfd_reloc, sym_num, reloc_queue);
                        break;

                    case R_CODE_ONE_SYMBOL:
                    case R_DP_RELATIVE:
                        if (bfd_reloc->addend)
                            p = som_reloc_addend(abfd, bfd_reloc->addend, p, &subspace_reloc_size, reloc_queue);

                        if (!handle_symbol_size(bfd_reloc, sym_num, &p, abfd, reloc_queue, &subspace_reloc_size))
                            return false;
                        break;
                        
                    case R_DATA_GPREL:
                        if (bfd_reloc->addend)
                            p = som_reloc_addend(abfd, bfd_reloc->addend, p, &subspace_reloc_size, reloc_queue);
                        
                        if (!handle_large_symbol_size(bfd_reloc, sym_num, &p, abfd, reloc_queue, &subspace_reloc_size))
                            return false;
                        break;

                    case R_DATA_ONE_SYMBOL:
                    case R_DATA_PLABEL:
                    case R_CODE_PLABEL:
                    case R_DLT_REL:
                        if (bfd_reloc->howto->type != R_DATA_ONE_SYMBOL && bfd_reloc->addend)
                            p = som_reloc_addend(abfd, bfd_reloc->addend, p, &subspace_reloc_size, reloc_queue);
                        
                        if (!handle_large_symbol_size(bfd_reloc, sym_num, &p, abfd, reloc_queue, &subspace_reloc_size))
                            return false;
                        break;

                    // Handling other cases similarly...
                }
            }
            
            p = som_reloc_skip(abfd, subsection->size - reloc_offset, p, &subspace_reloc_size, reloc_queue);

            if (bfd_write(tmp_space, p - tmp_space, abfd) != (size_t)(p - tmp_space))
                return false;
            p = tmp_space;

            total_reloc_size += subspace_reloc_size;
            som_section_data(subsection)->subspace_dict->fixup_request_quantity = subspace_reloc_size;
        }
        section = section->next;
    }
    *total_reloc_sizep = total_reloc_size;
    return true;
}

bool handle_symbol_size(arelent* bfd_reloc, int sym_num, unsigned char** p, bfd* abfd, reloc_queue* reloc_queue, unsigned int* subspace_reloc_size) {
    if (sym_num < 0x20) {
        bfd_put_8(abfd, bfd_reloc->howto->type + sym_num, *p);
        (*subspace_reloc_size)++;
        (*p)++;
    }
    else if (sym_num < 0x100) {
        bfd_put_8(abfd, bfd_reloc->howto->type + 32, *p);
        bfd_put_8(abfd, sym_num, *p + 1);
        *p = try_prev_fixup(abfd, subspace_reloc_size, *p, 2, reloc_queue);
    }
    else if (sym_num < 0x10000000) {
        bfd_put_8(abfd, bfd_reloc->howto->type + 33, *p);
        bfd_put_8(abfd, sym_num >> 16, *p + 1);
        bfd_put_16(abfd, (bfd_vma)sym_num, *p + 2);
        *p = try_prev_fixup(abfd, subspace_reloc_size, *p, 4, reloc_queue);
    }
    else {
        return false; // or handle the error
    }
    return true;
}

bool handle_large_symbol_size(arelent* bfd_reloc, int sym_num, unsigned char** p, bfd* abfd, reloc_queue* reloc_queue, unsigned int* subspace_reloc_size) {
    if (sym_num < 0x10000000) {
        bfd_put_8(abfd, bfd_reloc->howto->type, *p);
        bfd_put_8(abfd, sym_num >> 16, *p + 1);
        bfd_put_16(abfd, (bfd_vma)sym_num, *p + 2);
        *p = try_prev_fixup(abfd, subspace_reloc_size, *p, 4, reloc_queue);
    }
    else {
        return false; // or handle the error
    }
    return true;
}

/* Write the length of STR followed by STR to P which points into
   *BUF, a buffer of *BUFLEN size.  Track total size in *STRINGS_SIZE,
   setting *STRX to the current offset for STR.  When STR can't fit in
   *BUF, flush the buffer to ABFD, possibly reallocating.  Return the
   next available location in *BUF, or NULL on error.  */

#include <string.h>
#include <stdlib.h>
#include <stdbool.h>

static bool
write_and_allocate(char **buf, size_t *buflen, bfd *abfd, size_t needed, size_t amt) {
    if (bfd_write(*buf, amt, abfd) != amt)
        return false;

    if (needed > *buflen) {
        *buflen = *buflen * 2 < needed ? needed : *buflen * 2;
        free(*buf);
        *buf = bfd_malloc(*buflen);
        if (*buf == NULL)
            return false;
    }
    return true;
}

static char *
add_string(char *p, const char *str, bfd *abfd, char **buf, size_t *buflen,
           unsigned int *strings_size, unsigned int *strx) {
    size_t length = strlen(str) + 1;
    size_t needed = (4 + length + 3) & ~3;

    if ((size_t)(p - *buf) + needed > *buflen) {
        size_t amt = p - *buf;
        if (!write_and_allocate(buf, buflen, abfd, needed, amt))
            return NULL;
        p = *buf;
    }

    bfd_put_32(abfd, length - 1, p);
    *strings_size += 4;
    p += 4;

    *strx = *strings_size;

    memcpy(p, str, length);
    p += length;
    *strings_size += length;

    size_t padding = 4 - (length & 3);
    padding = padding == 4 ? 0 : padding;
    memset(p, 0, padding);
    *strings_size += padding;
    p += padding;

    return p;
}

/* Write out the space/subspace string table.  */

static bool som_write_space_strings(bfd *abfd, unsigned long current_offset, unsigned int *strings_size) {
    size_t tmp_space_size = SOM_TMP_BUFSIZE;
    char *tmp_space = bfd_malloc(tmp_space_size);
    if (tmp_space == NULL) {
        return false;
    }

    if (bfd_seek(abfd, current_offset, SEEK_SET) != 0) {
        free(tmp_space);
        return false;
    }

    *strings_size = 0;
    char *p = tmp_space;

    for (asection *section = abfd->sections; section != NULL; section = section->next) {
        unsigned int *strx = NULL;

        if (som_is_space(section)) {
            strx = &som_section_data(section)->space_dict->name;
        } else if (som_is_subspace(section)) {
            strx = &som_section_data(section)->subspace_dict->name;
        }

        if (strx != NULL) {
            p = add_string(p, section->name, abfd, &tmp_space, &tmp_space_size, strings_size, strx);
            if (p == NULL) {
                free(tmp_space);
                return false;
            }
        }
    }

    size_t amt = p - tmp_space;
    bool ok = amt ? (bfd_write(tmp_space, amt, abfd) == amt) : true;
    free(tmp_space);
    return ok;
}

/* Write out the symbol string table.  */

#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>

#define SOM_TMP_BUFSIZE 1024

static bool write_symbol_entries(bfd *abfd, char **p, unsigned int *strings_size, struct som_name_pt *name) {
    *p = add_string(*p, name->name, abfd, &tmp_space, &tmp_space_size, strings_size, &name->strx);
    return *p != NULL;
}

static bool som_write_symbol_strings(bfd *abfd, unsigned long current_offset, asymbol **syms, unsigned int num_syms, unsigned int *strings_size, struct som_compilation_unit *compilation_unit) {
    size_t tmp_space_size = SOM_TMP_BUFSIZE;
    char *tmp_space = bfd_malloc(tmp_space_size);
    char *p = tmp_space;
    unsigned int i;

    if (!tmp_space) return false;
    if (bfd_seek(abfd, current_offset, SEEK_SET) != 0) { free(tmp_space); return false; }
    *strings_size = 0;

    if (compilation_unit) {
        struct som_name_pt* names[] = {&compilation_unit->name, &compilation_unit->language_name, &compilation_unit->product_id, &compilation_unit->version_id};
        for (i = 0; i < 4; i++) {
            if (!write_symbol_entries(abfd, &p, strings_size, names[i])) { free(tmp_space); return false; }
        }
    }
    
    for (i = 0; i < num_syms; i++) {
        p = add_string(p, syms[i]->name, abfd, &tmp_space, &tmp_space_size, strings_size, &som_symbol_data(syms[i])->stringtab_offset);
        if (!p) { free(tmp_space); return false; }
    }

    size_t amt = p - tmp_space;
    bool ok = amt ? bfd_write(tmp_space, amt, abfd) == amt : true;
    free(tmp_space);
    return ok;
}

/* Compute variable information to be placed in the SOM headers,
   space/subspace dictionaries, relocation streams, etc.  Begin
   writing parts of the object file.  */

#include <stdbool.h>

static bool som_begin_writing(bfd *abfd) {
    unsigned long current_offset = 0;
    unsigned int strings_size = 0;
    unsigned long num_spaces, num_subspaces, i;
    asection *section;
    unsigned int total_subspaces = 0;
    struct som_exec_auxhdr *exec_header = NULL;

    current_offset += sizeof(struct som_external_header);

    obj_som_file_hdr(abfd)->aux_header_location = current_offset;
    obj_som_file_hdr(abfd)->aux_header_size = 0;
    if (abfd->flags & (EXEC_P | DYNAMIC)) {
        current_offset += sizeof(struct som_external_exec_auxhdr);
        obj_som_file_hdr(abfd)->aux_header_size += sizeof(struct som_external_exec_auxhdr);
        exec_header = obj_som_exec_hdr(abfd);
        exec_header->som_auxhdr.type = EXEC_AUX_ID;
        exec_header->som_auxhdr.length = 40;
    }

    if (obj_som_version_hdr(abfd) != NULL) {
        struct som_external_string_auxhdr ext_string_auxhdr;
        bfd_size_type len;

        if (bfd_seek(abfd, current_offset, SEEK_SET) != 0)
            return false;

        len = sizeof(struct som_external_string_auxhdr);
        obj_som_file_hdr(abfd)->aux_header_size += len;
        current_offset += len;
        som_swap_string_auxhdr_out(obj_som_version_hdr(abfd), &ext_string_auxhdr);
        if (bfd_write(&ext_string_auxhdr, len, abfd) != len)
            return false;

        len = obj_som_version_hdr(abfd)->header_id.length - 4;
        obj_som_file_hdr(abfd)->aux_header_size += len;
        current_offset += len;
        if (bfd_write(obj_som_version_hdr(abfd)->string, len, abfd) != len)
            return false;
    }

    if (obj_som_copyright_hdr(abfd) != NULL) {
        struct som_external_string_auxhdr ext_string_auxhdr;
        bfd_size_type len;

        if (bfd_seek(abfd, current_offset, SEEK_SET) != 0)
            return false;

        len = sizeof(struct som_external_string_auxhdr);
        obj_som_file_hdr(abfd)->aux_header_size += len;
        current_offset += len;
        som_swap_string_auxhdr_out(obj_som_copyright_hdr(abfd), &ext_string_auxhdr);
        if (bfd_write(&ext_string_auxhdr, len, abfd) != len)
            return false;

        len = obj_som_copyright_hdr(abfd)->header_id.length - 4;
        obj_som_file_hdr(abfd)->aux_header_size += len;
        current_offset += len;
        if (bfd_write(obj_som_copyright_hdr(abfd)->string, len, abfd) != len)
            return false;
    }

    obj_som_file_hdr(abfd)->init_array_location = current_offset;
    obj_som_file_hdr(abfd)->init_array_total = 0;

    num_spaces = som_count_spaces(abfd);
    obj_som_file_hdr(abfd)->space_location = current_offset;
    obj_som_file_hdr(abfd)->space_total = num_spaces;
    current_offset += num_spaces * sizeof(struct som_external_space_dictionary_record);

    num_subspaces = som_count_subspaces(abfd);
    obj_som_file_hdr(abfd)->subspace_location = current_offset;
    obj_som_file_hdr(abfd)->subspace_total = num_subspaces;
    current_offset += num_subspaces * sizeof(struct som_external_subspace_dictionary_record);

    if (current_offset % 4)
        current_offset += (4 - (current_offset % 4));

    obj_som_file_hdr(abfd)->space_strings_location = current_offset;

    if (!som_write_space_strings(abfd, current_offset, &strings_size))
        return false;

    obj_som_file_hdr(abfd)->space_strings_size = strings_size;
    current_offset += strings_size;

    obj_som_file_hdr(abfd)->compiler_location = current_offset;
    obj_som_file_hdr(abfd)->compiler_total = 0;
    if (obj_som_compilation_unit(abfd)) {
        obj_som_file_hdr(abfd)->compiler_total = 1;
        current_offset += sizeof(struct som_external_compilation_unit);
    }

    section = abfd->sections;
    for (i = 0; i < num_spaces; i++) {
        asection *subsection;
        int first_subspace = 1;
        unsigned int subspace_offset = 0;

        while (!som_is_space(section))
            section = section->next;

        for (subsection = abfd->sections; subsection != NULL; subsection = subsection->next) {
            if (!som_is_subspace(subsection) || !som_is_container(section, subsection) || !(subsection->flags & SEC_ALLOC))
                continue;

            if (first_subspace && (abfd->flags & (EXEC_P | DYNAMIC))) {
                if ((abfd->flags & (D_PAGED | DYNAMIC)) || (subsection->flags & SEC_CODE) || ((abfd->flags & WP_TEXT) && (subsection->flags & SEC_DATA)))
                    current_offset = SOM_ALIGN(current_offset, PA_PAGESIZE);

                if (subsection->flags & SEC_CODE && exec_header->exec_tfile == 0) {
                    exec_header->exec_tmem = section->vma;
                    exec_header->exec_tfile = current_offset;
                }
                if (subsection->flags & SEC_DATA && exec_header->exec_dfile == 0) {
                    exec_header->exec_dmem = section->vma;
                    exec_header->exec_dfile = current_offset;
                }
                subspace_offset = subsection->vma;
                first_subspace = 0;
            } else if (abfd->flags & (EXEC_P | DYNAMIC)) {
                current_offset += subsection->vma - subspace_offset;
                if (subsection->flags & SEC_CODE)
                    exec_header->exec_tsize += subsection->vma - subspace_offset;
                else
                    exec_header->exec_dsize += subsection->vma - subspace_offset;
                subspace_offset += subsection->vma - subspace_offset;
            }

            subsection->target_index = total_subspaces++;
            if (subsection->flags & SEC_LOAD) {
                if (abfd->flags & (EXEC_P | DYNAMIC) && subsection->flags & SEC_CODE)
                    exec_header->exec_tsize += subsection->size;
                else if (abfd->flags & (EXEC_P | DYNAMIC) && subsection->flags & SEC_DATA)
                    exec_header->exec_dsize += subsection->size;
                som_section_data(subsection)->subspace_dict->file_loc_init_value = current_offset;
                subsection->filepos = current_offset;
                current_offset += subsection->size;
                subspace_offset += subsection->size;
            } else {
                if (abfd->flags & (EXEC_P | DYNAMIC))
                    exec_header->exec_bsize += subsection->size;
                som_section_data(subsection)->subspace_dict->file_loc_init_value = 0;
                som_section_data(subsection)->subspace_dict->initialization_length = 0;
            }
        }
        section = section->next;
    }

    if (abfd->flags & (EXEC_P | DYNAMIC))
        current_offset = SOM_ALIGN(current_offset, PA_PAGESIZE);

    obj_som_file_hdr(abfd)->unloadable_sp_location = current_offset;
    section = abfd->sections;
    for (i = 0; i < num_spaces; i++) {
        asection *subsection;

        while (!som_is_space(section))
            section = section->next;

        if (abfd->flags & (EXEC_P | DYNAMIC))
            current_offset = SOM_ALIGN(current_offset, PA_PAGESIZE);

        for (subsection = abfd->sections; subsection != NULL; subsection = subsection->next) {
            if (!som_is_subspace(subsection) || !som_is_container(section, subsection) || (subsection->flags & SEC_ALLOC))
                continue;

            subsection->target_index = total_subspaces++;
            if (!(subsection->flags & SEC_LOAD)) {
                som_section_data(subsection)->subspace_dict->file_loc_init_value = current_offset;
                subsection->filepos = current_offset;
                current_offset += subsection->size;
            } else {
                som_section_data(subsection)->subspace_dict->file_loc_init_value = 0;
                som_section_data(subsection)->subspace_dict->initialization_length = subsection->size;
            }
        }
        section = section->next;
    }

    if (abfd->flags & (EXEC_P | DYNAMIC)) {
        current_offset = SOM_ALIGN(current_offset, PA_PAGESIZE);
    }
    if (bfd_seek(abfd, current_offset - 1, SEEK_SET) != 0)
        return false;
    if (bfd_write("", 1, abfd) != 1)
        return false;

    obj_som_file_hdr(abfd)->unloadable_sp_size = current_offset - obj_som_file_hdr(abfd)->unloadable_sp_location;

    obj_som_file_hdr(abfd)->loader_fixup_location = 0;
    obj_som_file_hdr(abfd)->loader_fixup_total = 0;

    obj_som_file_hdr(abfd)->som_length = current_offset;

    return true;
}

/* Finally, scribble out the various headers to the disk.  */

static bool som_finish_writing(bfd *abfd) {
    int num_spaces = som_count_spaces(abfd);
    asymbol **syms = bfd_get_outsymbols(abfd);
    int subspace_index = 0;
    file_ptr location;
    asection *section;
    unsigned long current_offset;
    unsigned int strings_size, total_reloc_size;
    size_t amt;
    struct som_external_header ext_header;
    long exec_data_version_id = (obj_som_exec_data(abfd) && obj_som_exec_data(abfd)->version_id)
                                ? obj_som_exec_data(abfd)->version_id : NEW_VERSION_ID;
    obj_som_file_hdr(abfd)->version_id = exec_data_version_id;

    current_offset = obj_som_file_hdr(abfd)->som_length;
    current_offset += (4 - (current_offset % 4)) % 4;

    int num_syms = bfd_get_symcount(abfd);
    obj_som_file_hdr(abfd)->symbol_location = current_offset;
    obj_som_file_hdr(abfd)->symbol_total = num_syms;
    current_offset += num_syms * sizeof(struct som_external_symbol_dictionary_record);
    current_offset += (4 - (current_offset % 4)) % 4;

    obj_som_file_hdr(abfd)->symbol_strings_location = current_offset;

    if (!som_write_symbol_strings(abfd, current_offset, syms, num_syms, &strings_size, obj_som_compilation_unit(abfd)))
        return false;

    obj_som_file_hdr(abfd)->symbol_strings_size = strings_size;
    current_offset += strings_size;

    if (!som_prep_for_fixups(abfd, bfd_get_outsymbols(abfd), bfd_get_symcount(abfd)))
        return false;

    current_offset += (4 - (current_offset % 4)) % 4;
    obj_som_file_hdr(abfd)->fixup_request_location = current_offset;

    if (!som_write_fixups(abfd, current_offset, &total_reloc_size))
        return false;

    obj_som_file_hdr(abfd)->fixup_request_total = total_reloc_size;
    obj_som_file_hdr(abfd)->som_length = current_offset + total_reloc_size;

    if (!som_build_and_write_symbol_table(abfd))
        return false;

    location = obj_som_file_hdr(abfd)->subspace_location;
    if (bfd_seek(abfd, location, SEEK_SET) != 0)
        return false;
    
    section = abfd->sections;
    for (int i = 0; i < num_spaces; i++) {
        while (!som_is_space(section))
            section = section->next;

        for (asection *subsection = abfd->sections; subsection != NULL; subsection = subsection->next) {
            struct som_external_subspace_dictionary_record ext_subspace_dict;
            if (som_is_subspace(subsection) && som_is_container(section, subsection) && (subsection->flags & SEC_ALLOC) != 0) {
                if (!som_section_data(section)->space_dict->subspace_quantity) {
                    som_section_data(section)->space_dict->is_loadable = 1;
                    som_section_data(section)->space_dict->subspace_index = subspace_index;
                }
                subspace_index++;
                som_section_data(section)->space_dict->subspace_quantity++;
                som_section_data(subsection)->subspace_dict->space_index = i;

                som_swap_subspace_dictionary_record_out(som_section_data(subsection)->subspace_dict, &ext_subspace_dict);
                amt = sizeof(struct som_subspace_dictionary_record);
                if (bfd_write(&ext_subspace_dict, amt, abfd) != amt)
                    return false;
            }
        }
        section = section->next;
    }

    section = abfd->sections;
    for (int i = 0; i < num_spaces; i++) {
        while (!som_is_space(section))
            section = section->next;

        for (asection *subsection = abfd->sections; subsection != NULL; subsection = subsection->next) {
            if (som_is_subspace(subsection) && som_is_container(section, subsection) && (subsection->flags & SEC_ALLOC) == 0) {
                if (!som_section_data(section)->space_dict->subspace_quantity) {
                    som_section_data(section)->space_dict->is_loadable = 0;
                    som_section_data(section)->space_dict->subspace_index = subspace_index;
                }
                som_section_data(section)->space_dict->subspace_quantity++;
                subspace_index++;
                som_section_data(subsection)->subspace_dict->space_index = i;

                struct som_external_subspace_dictionary_record ext_subspace_dict;
                som_swap_subspace_dictionary_record_out(som_section_data(subsection)->subspace_dict, &ext_subspace_dict);
                amt = sizeof(struct som_subspace_dictionary_record);
                if (bfd_write(&ext_subspace_dict, amt, abfd) != amt)
                    return false;
            }
        }
        section = section->next;
    }

    location = obj_som_file_hdr(abfd)->space_location;
    if (bfd_seek(abfd, location, SEEK_SET) != 0)
        return false;

    section = abfd->sections;
    for (int i = 0; i < num_spaces; i++) {
        while (!som_is_space(section))
            section = section->next;

        struct som_external_space_dictionary_record ext_space_dict;
        som_swap_space_dictionary_out(som_section_data(section)->space_dict, &ext_space_dict);
        amt = sizeof(struct som_external_space_dictionary_record);
        if (bfd_write(&ext_space_dict, amt, abfd) != amt)
            return false;

        section = section->next;
    }

    if (obj_som_compilation_unit(abfd)) {
        struct som_external_compilation_unit ext_comp_unit;
        location = obj_som_file_hdr(abfd)->compiler_location;
        if (bfd_seek(abfd, location, SEEK_SET) != 0)
            return false;

        som_swap_compilation_unit_out(obj_som_compilation_unit(abfd), &ext_comp_unit);
        amt = sizeof(struct som_external_compilation_unit);
        if (bfd_write(&ext_comp_unit, amt, abfd) != amt)
            return false;
    }

    int system_id = (abfd->flags & (EXEC_P | DYNAMIC)) && obj_som_exec_data(abfd) ? obj_som_exec_data(abfd)->system_id
                  : bfd_get_mach(abfd) == pa20 ? CPU_PA_RISC2_0
                  : bfd_get_mach(abfd) == pa11 ? CPU_PA_RISC1_1
                  : CPU_PA_RISC1_0;
    obj_som_file_hdr(abfd)->system_id = system_id;

    som_swap_header_out(obj_som_file_hdr(abfd), &ext_header);
    bfd_putb32(som_compute_checksum(&ext_header), ext_header.checksum);

    if (bfd_seek(abfd, 0, SEEK_SET) != 0)
        return false;
    amt = sizeof(struct som_external_header);
    if (bfd_write(&ext_header, amt, abfd) != amt)
        return false;

    if (abfd->flags & (EXEC_P | DYNAMIC)) {
        struct som_exec_auxhdr *exec_header = obj_som_exec_hdr(abfd);
        struct som_external_exec_auxhdr ext_exec_header;
        exec_header->exec_entry = bfd_get_start_address(abfd);
        exec_header->exec_flags = obj_som_exec_data(abfd) ? obj_som_exec_data(abfd)->exec_flags : exec_header->exec_flags;

        long tmp = SOM_ALIGN(exec_header->exec_dsize, PA_PAGESIZE);
        exec_header->exec_bsize -= (tmp - exec_header->exec_dsize);
        exec_header->exec_bsize = exec_header->exec_bsize < 0 ? 0 : exec_header->exec_bsize;
        exec_header->exec_dsize = tmp;

        long som_length = obj_som_file_hdr(abfd)->som_length;
        if (exec_header->exec_tfile + exec_header->exec_tsize > som_length || exec_header->exec_dfile + exec_header->exec_dsize > som_length)
            return false;

        som_swap_exec_auxhdr_out(exec_header, &ext_exec_header);

        if (bfd_seek(abfd, obj_som_file_hdr(abfd)->aux_header_location, SEEK_SET) != 0)
            return false;

        amt = sizeof(ext_exec_header);
        if (bfd_write(&ext_exec_header, amt, abfd) != amt)
            return false;
    }
    return true;
}

/* Compute and return the checksum for a SOM file header.  */

#include <stddef.h>
#include <stdint.h>

static uint32_t som_compute_checksum(struct som_external_header *hdr) {
    uint32_t checksum = 0;
    size_t count = sizeof(*hdr) / sizeof(uint32_t);
    uint32_t *buffer = (uint32_t *)hdr;

    for (size_t i = 0; i < count; i++) {
        checksum ^= buffer[i];
    }

    return checksum;
}

static void som_bfd_derive_misc_symbol_info(bfd *abfd ATTRIBUTE_UNUSED, asymbol *sym, struct som_misc_symbol_info *info) {
    memset(info, 0, sizeof(struct som_misc_symbol_info));

    int symbolType = som_symbol_data(sym)->som_type;
    unsigned int sectionFlags = sym->section->flags;

    if (sym->flags & BSF_SECTION_SYM) {
        info->symbol_type = ST_DATA;
    } else if (bfd_is_com_section(sym->section)) {
        info->symbol_type = ST_STORAGE;
        info->symbol_scope = SS_UNSAT;
    } else if ((symbolType == SYMBOL_TYPE_UNKNOWN || symbolType == SYMBOL_TYPE_CODE) && 
                bfd_is_und_section(sym->section) && (sym->flags & BSF_FUNCTION)) {
        info->symbol_type = ST_CODE;
    } else if (symbolType == SYMBOL_TYPE_ENTRY || 
               (symbolType == SYMBOL_TYPE_CODE && (sym->flags & BSF_FUNCTION)) || 
               (symbolType == SYMBOL_TYPE_UNKNOWN && (sym->flags & BSF_FUNCTION))) {
        info->symbol_type = ST_ENTRY;
        info->arg_reloc = som_symbol_data(sym)->tc_data.ap.hppa_arg_reloc;
        info->priv_level = som_symbol_data(sym)->tc_data.ap.hppa_priv_level;
    } else if (symbolType == SYMBOL_TYPE_UNKNOWN) {
        info->symbol_type = bfd_is_abs_section(sym->section) ? ST_ABSOLUTE : 
                            (sectionFlags & SEC_CODE) ? ST_CODE : ST_DATA;
    } else {
        switch (symbolType) {
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
        }
    }

    info->symbol_scope = (bfd_is_com_section(sym->section)) ? info->symbol_scope :
                         (bfd_is_und_section(sym->section)) ? SS_UNSAT :
                         (sym->flags & (BSF_EXPORT | BSF_WEAK)) ? SS_UNIVERSAL : SS_LOCAL;

    info->symbol_info = (bfd_is_com_section(sym->section) || bfd_is_und_section(sym->section) ||
                         bfd_is_abs_section(sym->section)) ? 0 : sym->section->target_index;
    
    info->symbol_value = sym->value + sym->section->vma;
    info->secondary_def = (sym->flags & BSF_WEAK) ? true : false;

    if (som_section_data(sym->section) && som_section_data(sym->section)->subspace_dict &&
        info->symbol_scope == SS_UNIVERSAL &&
        (info->symbol_type == ST_ENTRY || info->symbol_type == ST_CODE || info->symbol_type == ST_DATA)) {
        info->is_comdat = som_section_data(sym->section)->subspace_dict->is_comdat;
        info->is_common = som_section_data(sym->section)->subspace_dict->is_common;
        info->dup_common = som_section_data(sym->section)->subspace_dict->dup_common;
    }
}

/* Build and write, in one big chunk, the entire symbol table for
   this BFD.  */

#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>

static bool som_build_and_write_symbol_table(bfd *abfd) {
    unsigned int num_syms = bfd_get_symcount(abfd);
    file_ptr symtab_location = obj_som_file_hdr(abfd)->symbol_location;
    asymbol **bfd_syms = obj_som_sorted_syms(abfd);
    struct som_external_symbol_dictionary_record *som_symtab = NULL;
    bfd_size_type symtab_size;
    size_t amt;

    if (_bfd_mul_overflow(num_syms, sizeof(struct som_external_symbol_dictionary_record), &amt) || num_syms == 0) {
        bfd_set_error(bfd_error_no_memory);
        return false;
    }

    som_symtab = bfd_zmalloc(amt);
    if (!som_symtab) return false;

    for (unsigned int i = 0; i < num_syms; i++) {
        struct som_misc_symbol_info info;
        unsigned int flags;

        bfd_putb32(som_symbol_data(bfd_syms[i])->stringtab_offset, som_symtab[i].name);
        som_bfd_derive_misc_symbol_info(abfd, bfd_syms[i], &info);

        flags = (info.symbol_type << SOM_SYMBOL_TYPE_SH)
            | (info.symbol_scope << SOM_SYMBOL_SCOPE_SH)
            | (info.arg_reloc << SOM_SYMBOL_ARG_RELOC_SH)
            | (3 << SOM_SYMBOL_XLEAST_SH)
            | (info.secondary_def ? SOM_SYMBOL_SECONDARY_DEF : 0)
            | (info.is_common ? SOM_SYMBOL_IS_COMMON : 0)
            | (info.dup_common ? SOM_SYMBOL_DUP_COMMON : 0);
        bfd_putb32(flags, som_symtab[i].flags);

        flags = (info.symbol_info << SOM_SYMBOL_SYMBOL_INFO_SH)
            | (info.is_comdat ? SOM_SYMBOL_IS_COMDAT : 0);
        bfd_putb32(flags, som_symtab[i].info);
        bfd_putb32(info.symbol_value | info.priv_level, som_symtab[i].symbol_value);
    }

    if (bfd_seek(abfd, symtab_location, SEEK_SET) != 0) {
        free(som_symtab);
        return false;
    }

    symtab_size = num_syms * sizeof(struct som_external_symbol_dictionary_record);
    if (bfd_write(som_symtab, symtab_size, abfd) != symtab_size) {
        free(som_symtab);
        return false;
    }

    free(som_symtab);
    return true;
}

/* Write an object in SOM format.  */

bool som_write_object_contents(bfd *abfd) {
    if (!abfd->output_has_begun) {
        som_prep_headers(abfd);
        abfd->output_has_begun = true;
        som_begin_writing(abfd);
    }

    return som_finish_writing(abfd);
}

/* Read and save the string table associated with the given BFD.  */

static bool som_slurp_string_table(bfd *abfd) {
    if (!abfd) {
        return false;
    }

    char *stringtab;
    bfd_size_type amt = obj_som_stringtab_size(abfd);

    if (obj_som_stringtab(abfd) != NULL) {
        return true;
    }

    if (amt == 0) {
        bfd_set_error(bfd_error_no_symbols);
        return false;
    }

    if (bfd_seek(abfd, obj_som_str_filepos(abfd), SEEK_SET) != 0) {
        return false;
    }

    stringtab = (char *)_bfd_malloc_and_read(abfd, amt + 1, amt);
    if (!stringtab) {
        return false;
    }

    stringtab[amt] = '\0';
    obj_som_stringtab(abfd) = stringtab;
    return true;
}

/* Return the amount of data (in bytes) required to hold the symbol
   table for this object.  */

static long som_get_symtab_upper_bound(bfd *abfd) {
    if (abfd == NULL) {
        return -1;
    }

    if (!som_slurp_symbol_table(abfd)) {
        return -1;
    }

    long symcount = bfd_get_symcount(abfd);
    if (symcount < 0) {
        return -1;
    }

    return (symcount + 1) * sizeof(asymbol *);
}

/* Convert from a SOM subspace index to a BFD section.  */

asection *bfd_section_from_som_symbol(bfd *abfd, struct som_external_symbol_dictionary_record *symbol) {
    unsigned int flags = bfd_getb32(symbol->flags);
    unsigned int symbol_type = (flags >> SOM_SYMBOL_TYPE_SH) & SOM_SYMBOL_TYPE_MASK;
    unsigned int symbol_info = bfd_getb32(symbol->info);
    unsigned int symbol_value = bfd_getb32(symbol->symbol_value);
    asection *section = abfd->sections;

    bool is_executable_or_dynamic = (abfd->flags & (EXEC_P | DYNAMIC)) != 0;
    bool is_function_symbol = (symbol_type == ST_ENTRY || symbol_type == ST_PRI_PROG || 
                               symbol_type == ST_SEC_PROG || symbol_type == ST_MILLICODE);

    if (!is_executable_or_dynamic || !is_function_symbol) {
        int idx = (symbol_info >> SOM_SYMBOL_SYMBOL_INFO_SH) & SOM_SYMBOL_SYMBOL_INFO_MASK;
        while (section) {
            if (section->target_index == idx && som_is_subspace(section)) {
                return section;
            }
            section = section->next;
        }
    } else {
        while (section) {
            if (symbol_value >= section->vma && symbol_value <= section->vma + section->size && som_is_subspace(section)) {
                return section;
            }
            section = section->next;
        }
    }

    return bfd_abs_section_ptr;
}

/* Read and save the symbol table associated with the given BFD.  */

#include <stddef.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

static unsigned int som_slurp_symbol_table(bfd *abfd) {
    unsigned int symbol_count = bfd_get_symcount(abfd);
    size_t symsize = sizeof(struct som_external_symbol_dictionary_record);
    size_t amt;
    char *stringtab = NULL;
    struct som_external_symbol_dictionary_record *buf = NULL;
    som_symbol_type *sym = NULL, *symbase = NULL;

    if (obj_som_symtab(abfd) != NULL || 
        (symbol_count == 0 && som_slurp_string_table(abfd))) return true;

    if (!som_slurp_string_table(abfd)) return false;

    stringtab = obj_som_stringtab(abfd);

    if (_bfd_mul_overflow(symbol_count, symsize, &amt) || 
        bfd_seek(abfd, obj_som_sym_filepos(abfd), SEEK_SET) != 0 ||
        !(buf = _bfd_malloc_and_read(abfd, amt, amt)) ||
        _bfd_mul_overflow(symbol_count, sizeof(som_symbol_type), &amt) ||
        !(symbase = bfd_zmalloc(amt))) return error_cleanup(buf, symbase);

    for (struct som_external_symbol_dictionary_record *bufp = buf,
                                                      *endbufp = buf + symbol_count;
         bufp < endbufp; ++bufp) {
        unsigned int flags = bfd_getb32(bufp->flags);
        unsigned int symbol_type = (flags >> SOM_SYMBOL_TYPE_SH) & SOM_SYMBOL_TYPE_MASK;
        unsigned int symbol_scope = (flags >> SOM_SYMBOL_SCOPE_SH) & SOM_SYMBOL_SCOPE_MASK;
        if (symbol_type == ST_SYM_EXT || symbol_type == ST_ARG_EXT) continue;

        configure_symbol_type(sym, symbol_type);
        configure_symbol_private_data(sym, symbol_type);
        configure_symbol_name(sym, bufp, abfd, stringtab);
        configure_symbol_value_and_flags(sym, symbol_type, symbol_scope, flags);

        if (!assign_symbol_section_and_flags(sym, symbol_scope, abfd, bufp)) goto error_cleanup;

        if (flags & SOM_SYMBOL_SECONDARY_DEF) sym->symbol.flags |= BSF_WEAK;
        assign_section_symbols(sym);

        sym++;
    }

    abfd->symcount = sym - symbase;
    obj_som_symtab(abfd) = symbase;
    free(buf);
    return true;

error_cleanup:
    free(buf);
    free(symbase);
    return false;
}

bool configure_symbol_type(som_symbol_type *sym, unsigned int symbol_type) {
    switch (symbol_type) {
        case ST_NULL: sym->som_type = SYMBOL_TYPE_UNKNOWN; break;
        case ST_ABSOLUTE: sym->som_type = SYMBOL_TYPE_ABSOLUTE; break;
        case ST_DATA: sym->som_type = SYMBOL_TYPE_DATA; break;
        case ST_CODE: sym->som_type = SYMBOL_TYPE_CODE; break;
        case ST_PRI_PROG: sym->som_type = SYMBOL_TYPE_PRI_PROG; break;
        case ST_SEC_PROG: sym->som_type = SYMBOL_TYPE_SEC_PROG; break;
        case ST_ENTRY: sym->som_type = SYMBOL_TYPE_ENTRY; break;
        case ST_MILLICODE: sym->som_type = SYMBOL_TYPE_MILLICODE; break;
        case ST_PLABEL: sym->som_type = SYMBOL_TYPE_PLABEL; break;
        default: sym->som_type = SYMBOL_TYPE_UNKNOWN; break;
    }
}

bool configure_symbol_private_data(som_symbol_type *sym, unsigned int symbol_type) {
    sym->tc_data.ap.hppa_arg_reloc = (flags >> SOM_SYMBOL_ARG_RELOC_SH) & SOM_SYMBOL_ARG_RELOC_MASK;
}

bool configure_symbol_name(som_symbol_type *sym, struct som_external_symbol_dictionary_record *bufp,
                           bfd *abfd, char *stringtab) {
    sym->symbol.the_bfd = abfd;
    bfd_vma offset = bfd_getb32(bufp->name);
    if (offset < obj_som_stringtab_size(abfd))
        sym->symbol.name = offset + stringtab;
    else {
        bfd_set_error(bfd_error_bad_value);
        return false;
    }
}

bool configure_symbol_value_and_flags(som_symbol_type *sym, unsigned int symbol_type,
                                      unsigned int symbol_scope, unsigned int flags) {
    sym->symbol.value = bfd_getb32(bufp->symbol_value);
    sym->symbol.section = NULL;
    sym->symbol.flags = 0;

    if (symbol_type == ST_ENTRY || symbol_type == ST_MILLICODE) {
        sym->symbol.flags |= BSF_FUNCTION;
        update_symbol_value_and_flags(sym);
    } else if (symbol_type == ST_STUB || symbol_type == ST_CODE || 
               symbol_type == ST_PRI_PROG || symbol_type == ST_SEC_PROG) {
        update_symbol_value_and_flags(sym);
        if (symbol_scope == SS_UNSAT) sym->symbol.flags |= BSF_FUNCTION;
    }
}

void update_symbol_value_and_flags(som_symbol_type *sym) {
    sym->tc_data.ap.hppa_priv_level = sym->symbol.value & 0x3;
    sym->symbol.value &= ~0x3;
}

bool assign_symbol_section_and_flags(som_symbol_type *sym, unsigned int symbol_scope,
                                     bfd *abfd, struct som_external_symbol_dictionary_record *bufp) {
    switch (symbol_scope) {
        case SS_EXTERNAL:
            sym->symbol.section = (symbol_type != ST_STORAGE) ? bfd_und_section_ptr : bfd_com_section_ptr;
            sym->symbol.flags |= (BSF_EXPORT | BSF_GLOBAL);
            break;
        case SS_UNSAT:
            sym->symbol.section = (symbol_type != ST_STORAGE) ? bfd_und_section_ptr : bfd_com_section_ptr;
            break;
        case SS_UNIVERSAL:
            sym->symbol.flags |= (BSF_EXPORT | BSF_GLOBAL);
            if (!assign_section_and_adjust_value(sym, abfd, bufp)) return false;
            break;
        case SS_LOCAL:
            sym->symbol.flags |= BSF_LOCAL;
            if (!assign_section_and_adjust_value(sym, abfd, bufp)) return false;
            break;
        default:
            sym->symbol.section = bfd_und_section_ptr;
    }
    return true;
}

bool assign_section_and_adjust_value(som_symbol_type *sym, bfd *abfd,
                                     struct som_external_symbol_dictionary_record *bufp) {
    sym->symbol.section = bfd_section_from_som_symbol(abfd, bufp);
    sym->symbol.value -= sym->symbol.section->vma;
    return sym->symbol.section != NULL;
}

void assign_section_symbols(som_symbol_type *sym) {
    if (sym->symbol.name[0] == '$' && 
        sym->symbol.name[strlen(sym->symbol.name) - 1] == '$' &&
        !strcmp(sym->symbol.name, sym->symbol.section->name)) {
        sym->symbol.flags |= BSF_SECTION_SYM;
    } else if (startswith(sym->symbol.name, "L$0\002")) {
        sym->symbol.flags |= BSF_SECTION_SYM;
        sym->symbol.name = sym->symbol.section->name;
    } else if (startswith(sym->symbol.name, "L$0\001")) {
        sym->symbol.flags |= BSF_DEBUGGING;
    }
}

/* Canonicalize a SOM symbol table.  Return the number of entries
   in the symbol table.  */

static long som_canonicalize_symtab(bfd *abfd, asymbol **location) {
    if (abfd == NULL || location == NULL) {
        return -1;
    }

    if (!som_slurp_symbol_table(abfd)) {
        return -1;
    }

    int sym_count = bfd_get_symcount(abfd);
    if (sym_count < 0) {
        return -1;
    }

    som_symbol_type *symbase = obj_som_symtab(abfd);
    if (symbase == NULL) {
        return -1;
    }

    for (int i = 0; i < sym_count; i++) {
        location[i] = &symbase[i].symbol;
    }
    location[sym_count] = NULL;

    return sym_count;
}

/* Make a SOM symbol.  There is nothing special to do here.  */

asymbol *som_make_empty_symbol(bfd *abfd) {
    som_symbol_type *new_symbol_type = bfd_zalloc(abfd, sizeof(som_symbol_type));

    if (!new_symbol_type) return NULL;
    
    new_symbol_type->symbol.the_bfd = abfd;
    return &new_symbol_type->symbol;
}

/* Print symbol information.  */

#include <inttypes.h>
#include <stdio.h>
#include <bfd.h>

static void printSymbolName(FILE *file, const char *name) {
    fprintf(file, "%s", name);
}

static void printSymbolMore(FILE *file, uint64_t value, unsigned int flags) {
    fprintf(file, "som %08" PRIx64 " %x", value, flags);
}

static void printSymbolAll(FILE *file, bfd *abfd, asymbol *symbol) {
    const char *section_name = symbol->section ? symbol->section->name : "(*none*)";
    bfd_print_symbol_vandf(abfd, (void *)file, symbol);
    fprintf(file, " %s\t%s", section_name, symbol->name);
}

static void som_print_symbol(bfd *abfd, void *afile, asymbol *symbol, bfd_print_symbol_type how) {
    FILE *file = (FILE *)afile;
    
    switch (how) {
        case bfd_print_symbol_name:
            printSymbolName(file, symbol->name);
            break;
        case bfd_print_symbol_more:
            printSymbolMore(file, (uint64_t)symbol->value, symbol->flags);
            break;
        case bfd_print_symbol_all:
            printSymbolAll(file, abfd, symbol);
            break;
        default:
            // Handle unexpected case, if necessary
            break;
    }
}

#include <stdbool.h>
#include <stddef.h>

static bool som_bfd_is_local_label_name(const char *name) {
    if (name == NULL) {
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
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

static unsigned int som_set_reloc_info(unsigned char *fixup, unsigned int end, arelent *internal_relocs, asection *section, asymbol **symbols, unsigned int symcount, bool just_count) {
    unsigned int deallocate_contents = 0;
    unsigned char *end_fixups = &fixup[end];
    int variables[26] = {0}, stack[20] = {0}, *sp = stack, saved_unwind_bits = 0;
    arelent *rptr = internal_relocs;
    unsigned int offset = 0;
    unsigned int count = 0, prev_fixup = 0;

    som_initialize_reloc_queue(reloc_queue);

    while (fixup < end_fixups) {
        const char *cp;
        unsigned int op;
        const struct fixup_format *fp;
        unsigned char *save_fixup = fixup;
        op = *fixup++;
        fp = &som_fixup_formats[op];

        if (*fp->format == 'P') {
            if (!reloc_queue[fp->D].reloc) continue;
            fixup = reloc_queue[fp->D].reloc;
            som_reloc_queue_fix(reloc_queue, fp->D);
            prev_fixup = 1;
            op = *fixup++;
            fp = &som_fixup_formats[op];
        }

        if (!just_count && som_hppa_howto_table[op].type != R_NO_RELOCATION && som_hppa_howto_table[op].type != R_DATA_OVERRIDE) {
            rptr->address = offset;
            rptr->howto = &som_hppa_howto_table[op];
            rptr->addend = 0;
            rptr->sym_ptr_ptr = &bfd_abs_section_ptr->symbol;
        }

        #define var(c) variables[(c) - 'A']
        #define push(v) (*sp++ = (v))
        #define pop() (*--sp)

        var('L') = 0;
        var('D') = fp->D;
        var('U') = saved_unwind_bits;
        cp = fp->format;

        while (*cp) {
            unsigned int c = *cp++;
            unsigned int v;

            if (*cp == '=') cp++;
            switch (c) {
                case '+':
                    v = pop(); v += pop(); push(v);
                    break;
                case '*':
                    v = pop(); v *= pop(); push(v);
                    break;
                case '<':
                    v = pop(); v = pop() << v; push(v);
                    break;
                default:
                    if (ISUPPER(c)) push(var(c));
                    else if (ISLOWER(c)) {
                        int bits = (c - 'a') * 8;
                        v = 0;
                        while (c-- > 'a' && fixup < end_fixups)
                            v = (v << 8) | *fixup++;
                        if (c == 'V') v = sign_extend(v, bits);
                        push(v);
                    } else if (ISDIGIT(c)) {
                        v = c - '0';
                        while (ISDIGIT(*cp)) v = (v * 10) + (*cp++ - '0');
                        push(v);
                    } else {
                        abort();
                    }
                    break;
            }

            var(c) = pop();

            switch (c) {
                case 'L': offset += var('L'); break;
                case 'S':
                    if (!just_count && symbols != NULL && var('S') < symcount)
                        rptr->sym_ptr_ptr = &symbols[var('S')];
                    break;
                case 'R':
                    if (!just_count) {
                        unsigned int tmp = var('R');
                        rptr->addend = 0;

                        if ((som_hppa_howto_table[op].type == R_PCREL_CALL && R_PCREL_CALL + 10 > op) || 
                            (som_hppa_howto_table[op].type == R_ABS_CALL && R_ABS_CALL + 10 > op)) {
                            rptr->addend = HPPA_R_ADDEND((tmp == 5 ? 1 : tmp > 4 ? 5 : tmp) << 8 |
                                                          ((tmp > 4) ? 1 << 6 : 0) | 
                                                          ((tmp > 3) ? 1 << 4 : 0) | 
                                                          ((tmp > 2) ? 1 << 2 : 0), 0);
                        }
                    }
                    break;
                case 'O':
                    switch (op) {
                        case R_COMP1: subop = comp1_opcodes; break;
                        case R_COMP2: subop = comp2_opcodes; break;
                        case R_COMP3: subop = comp3_opcodes; break;
                        default: abort();
                    }
                    while (*subop <= var('O')) ++subop;
                    --subop;
                    break;
                case 'U': saved_unwind_bits = var('U'); break;
            }
        }

        if (prev_fixup) {
            fixup = save_fixup + 1;
            prev_fixup = 0;
        } else if (fixup > save_fixup + 1) {
            som_reloc_queue_insert(save_fixup, fixup - save_fixup, reloc_queue);
        }

        if (som_hppa_howto_table[op].type != R_DATA_OVERRIDE && som_hppa_howto_table[op].type != R_NO_RELOCATION) {
            if (!just_count) {
                if (som_hppa_howto_table[op].type == R_ENTRY) rptr->addend = var('T');
                else if (som_hppa_howto_table[op].type == R_EXIT) rptr->addend = var('U');
                else if (som_hppa_howto_table[op].type == R_DATA_ONE_SYMBOL) {
                    rptr->addend = var('V');
                    if (rptr->addend == 0 && (section->flags & SEC_HAS_CONTENTS) != 0) {
                        if (!section->contents) {
                            if (!bfd_malloc_and_get_section(section->owner, section, &section->contents)) return -1;
                            deallocate_contents = 1;
                        }
                        if (offset - var('L') <= section->size && section->size - (offset - var('L')) >= 4)
                            rptr->addend = bfd_get_32(section->owner, section->contents + offset - var('L'));
                    }
                } else {
                    rptr->addend = var('V');
                }
                rptr++;
            }
            count++;
        }

        memset(variables, 0, sizeof(variables));
    }

    if (deallocate_contents) {
        free(section->contents);
        section->contents = NULL;
    }

    return count;

    #undef var
    #undef push
    #undef pop
}

/* Read in the relocs (aka fixups in SOM terms) for a section.

   som_get_reloc_upper_bound calls this routine with JUST_COUNT
   set to TRUE to indicate it only needs a count of the number
   of actual relocations.  */

static bool som_slurp_reloc_table(bfd *abfd, asection *section, asymbol **symbols, bool just_count) {
    unsigned char *external_relocs = NULL;
    unsigned int fixup_stream_size = som_section_data(section)->reloc_size;
    arelent *internal_relocs = NULL;
    unsigned int num_relocs;
    size_t amt;

    if (section->reloc_count == 0) {
        return true;
    }

    if (section->reloc_count == (unsigned) -1) {
        if (bfd_seek(abfd, obj_som_reloc_filepos(abfd) + section->rel_filepos, SEEK_SET) != 0) {
            return false;
        }
        amt = fixup_stream_size;
        external_relocs = _bfd_malloc_and_read(abfd, amt, amt);
        if (!external_relocs) {
            return false;
        }

        section->reloc_count = som_set_reloc_info(external_relocs, fixup_stream_size, NULL, NULL, NULL, 0, true);
        som_section_data(section)->reloc_stream = external_relocs;
    }

    if (just_count || section->relocation) {
        return true;
    }

    num_relocs = section->reloc_count;
    external_relocs = som_section_data(section)->reloc_stream;

    if (_bfd_mul_overflow(num_relocs, sizeof(arelent), &amt)) {
        bfd_set_error(bfd_error_file_too_big);
        return false;
    }
    
    internal_relocs = bfd_zalloc(abfd, amt);
    if (!internal_relocs) {
        return false;
    }

    som_set_reloc_info(external_relocs, fixup_stream_size, internal_relocs, section, symbols, bfd_get_symcount(abfd), false);

    free(external_relocs);
    som_section_data(section)->reloc_stream = NULL;

    section->relocation = internal_relocs;
    return true;
}

/* Return the number of bytes required to store the relocation
   information associated with the given section.  */

#include <errno.h>

static long som_get_reloc_upper_bound(bfd *abfd, sec_ptr asect) {
    if (asect == NULL || abfd == NULL) {
        errno = EINVAL;
        return -1;
    }

    if (asect->flags & SEC_RELOC) {
        if (!som_slurp_reloc_table(abfd, asect, NULL, true)) {
            return -1;
        }
        return (asect->reloc_count + 1) * sizeof(arelent *);
    }

    return sizeof(arelent *);
}

/* Convert relocations from SOM (external) form into BFD internal
   form.  Return the number of relocations.  */

static long som_canonicalize_reloc(bfd *abfd, sec_ptr section, arelent **relptr, asymbol **symbols) {
    if (!som_slurp_reloc_table(abfd, section, symbols, false)) {
        return -1;
    }

    int count = section->reloc_count;
    arelent *tblptr = section->relocation;

    if (count < 0) {
        return -1;
    }

    for (int i = 0; i < count; i++) {
        if (!tblptr) {
            return -1;
        }
        relptr[i] = &tblptr[i];
    }

    relptr[count] = NULL;
    return count;
}

extern const bfd_target hppa_som_vec;

/* A hook to set up object file dependent section information.  */

bool som_new_section_hook(bfd *abfd, asection *newsect) {
  newsect->used_by_bfd = bfd_zalloc(abfd, sizeof(struct som_section_data_struct));
  if (newsect->used_by_bfd == NULL) {
    return false;
  }

  newsect->alignment_power = 3;
  return _bfd_generic_new_section_hook(abfd, newsect);
}

/* Copy any private info we understand from the input symbol
   to the output symbol.  */

bool som_bfd_copy_private_symbol_data(bfd *ibfd, asymbol *isymbol, bfd *obfd, asymbol *osymbol) {
    if (ibfd->xvec->flavour != bfd_target_som_flavour || obfd->xvec->flavour != bfd_target_som_flavour) {
        return false;
    }

    ((struct som_symbol *)osymbol)->tc_data.ap.hppa_arg_reloc = ((struct som_symbol *)isymbol)->tc_data.ap.hppa_arg_reloc;

    return true;
}

/* Copy any private info we understand from the input section
   to the output section.  */

#include <stdbool.h>
#include <stddef.h>
#include <string.h>

static bool som_bfd_copy_private_section_data(bfd *ibfd, asection *isection, bfd *obfd, asection *osection, struct bfd_link_info *link_info) {
    if (!link_info && 
        ibfd->xvec->flavour == bfd_target_som_flavour &&
        obfd->xvec->flavour == bfd_target_som_flavour &&
        (som_is_space(isection) || som_is_subspace(isection))) {

        size_t amt = sizeof(struct som_copyable_section_data_struct);
        som_section_data(osection)->copy_data = bfd_zalloc(obfd, amt);
        if (!som_section_data(osection)->copy_data) {
            return false;
        }

        memcpy(som_section_data(osection)->copy_data, som_section_data(isection)->copy_data, amt);

        if (som_section_data(osection)->copy_data->container) {
            if (som_section_data(osection)->copy_data->container->output_section) {
                som_section_data(osection)->copy_data->container = som_section_data(osection)->copy_data->container->output_section;
            } else {
                _bfd_error_handler(_("%pB[%pA]: no output section for space %pA"), obfd, osection, som_section_data(osection)->copy_data->container);
                return false;
            }
        }
    }
    return true;
}

/* Copy any private info we understand from the input bfd
   to the output bfd.  */

bool som_bfd_copy_private_bfd_data(bfd *ibfd, bfd *obfd) {
    if (ibfd->xvec->flavour != bfd_target_som_flavour || obfd->xvec->flavour != bfd_target_som_flavour) {
        return true;
    }

    void *data = bfd_zalloc(obfd, sizeof(struct som_exec_data));
    if (!data) {
        return false;
    }

    memcpy(data, obj_som_exec_data(ibfd), sizeof(struct som_exec_data));
    obj_som_exec_data(obfd) = data; 

    return true;
}

/* Display the SOM header.  */

#include <stdbool.h>
#include <stdio.h>
#include "som_bfd.h"

static bool som_bfd_print_private_bfd_data(bfd *abfd, void *farg) {
    struct som_exec_auxhdr *exec_header = obj_som_exec_hdr(abfd);
    if (!exec_header) {
        return true;
    }

    struct som_aux_id *auxhdr = &exec_header->som_auxhdr;
    FILE *f = (FILE *)farg;

    fprintf(f, "\nExec Auxiliary Header\n  flags              ");
    if (auxhdr->mandatory) fprintf(f, "mandatory ");
    if (auxhdr->copy) fprintf(f, "copy ");
    if (auxhdr->append) fprintf(f, "append ");
    if (auxhdr->ignore) fprintf(f, "ignore ");
    fprintf(f, "\n  type               %#x\n", auxhdr->type);
    fprintf(f, "  length             %#x\n", auxhdr->length);

    fprintf(f, "  text size          %#lx\n", (long)exec_header->exec_tsize);
    fprintf(f, "  text memory offset %#lx\n", (long)exec_header->exec_tmem);
    fprintf(f, "  text file offset   %#lx\n", (long)exec_header->exec_tfile);
    fprintf(f, "  data size          %#lx\n", (long)exec_header->exec_dsize);
    fprintf(f, "  data memory offset %#lx\n", (long)exec_header->exec_dmem);
    fprintf(f, "  data file offset   %#lx\n", (long)exec_header->exec_dfile);
    fprintf(f, "  bss size           %#lx\n", (long)exec_header->exec_bsize);
    fprintf(f, "  entry point        %#lx\n", (long)exec_header->exec_entry);
    fprintf(f, "  loader flags       %#lx\n", (long)exec_header->exec_flags);
    fprintf(f, "  bss initializer    %#lx\n", (long)exec_header->exec_bfill);

    return true;
}

/* Set backend info for sections which can not be described
   in the BFD data structures.  */

bool bfd_som_set_section_attributes(asection *section, int defined, int priv, unsigned int sort_key, int spnum) {
    struct som_copyable_section_data_struct *copy_data;

    if (section == NULL || section->owner == NULL) {
        return false;
    }

    copy_data = som_section_data(section)->copy_data;
    if (copy_data == NULL) {
        copy_data = bfd_zalloc(section->owner, sizeof(struct som_copyable_section_data_struct));
        if (copy_data == NULL) {
            return false;
        }
        som_section_data(section)->copy_data = copy_data;
    }

    copy_data->sort_key = sort_key;
    copy_data->is_defined = defined;
    copy_data->is_private = priv;
    copy_data->container = section;
    copy_data->space_number = spnum;
    
    return true;
}

/* Set backend info for subsections which can not be described
   in the BFD data structures.  */

bool bfd_som_set_subsection_attributes(asection *section, asection *container, int access_ctr, unsigned int sort_key, int quadrant, int comdat, int common, int dup_common) {
    som_copyable_section_data_struct *copy_data = som_section_data(section)->copy_data;

    if (copy_data == NULL) {
        size_t amt = sizeof(som_copyable_section_data_struct);
        copy_data = bfd_zalloc(section->owner, amt);

        if (copy_data == NULL) {
            return false;
        }
        
        som_section_data(section)->copy_data = copy_data;
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

void bfd_som_set_symbol_type(asymbol *symbol, unsigned int type) {
    if (symbol == NULL) {
        // Handle null pointer error
        return;
    }
    som_symbol_data(symbol)->som_type = type;
}

/* Attach an auxiliary header to the BFD backend so that it may be
   written into the object file.  */

bool bfd_som_attach_aux_hdr(bfd *abfd, int type, char *string) {
    size_t len = strlen(string);
    int pad = (4 - (len % 4)) % 4;
    size_t amt = sizeof(struct som_string_auxhdr) + len + pad;
    struct som_string_auxhdr *hdr = NULL;

    if (type == VERSION_AUX_ID) {
        hdr = bfd_zalloc(abfd, amt);
        obj_som_version_hdr(abfd) = hdr;
    } else if (type == COPYRIGHT_AUX_ID) {
        hdr = bfd_zalloc(abfd, amt);
        obj_som_copyright_hdr(abfd) = hdr;
    }

    if (!hdr)
        return false;

    hdr->header_id.type = type;
    hdr->header_id.length = len + pad + 4;
    hdr->string_length = len;
    memcpy(hdr->string, string, len);
    memset(hdr->string + len, 0, pad);

    return true;
}

/* Attach a compilation unit header to the BFD backend so that it may be
   written into the object file.  */

bool bfd_som_attach_compilation_unit(bfd *abfd, const char *name, const char *language_name, const char *product_id, const char *version_id) {
    struct som_compilation_unit *n = (struct som_compilation_unit *) bfd_zalloc(abfd, sizeof(*n));
    if (n == NULL) return false;

    const char *fields[] = {name, language_name, product_id, version_id};
    char **storage[] = {&n->name.name, &n->language_name.name, &n->product_id.name, &n->version_id.name};

    for (size_t i = 0; i < sizeof(fields) / sizeof(fields[0]); i++) {
        if (fields[i] != NULL) {
            *storage[i] = bfd_alloc(abfd, strlen(fields[i]) + 1);
            if (*storage[i] == NULL) return false;
            strcpy(*storage[i], fields[i]);
        }
    }

    obj_som_compilation_unit(abfd) = n;
    return true;
}

static bool som_get_section_contents(bfd *abfd, sec_ptr section, void *location, file_ptr offset, bfd_size_type count) {
    if (count == 0 || !(section->flags & SEC_HAS_CONTENTS)) {
        return true;
    }

    if (offset > section->size - count) {
        return false;
    }

    if (bfd_seek(abfd, section->filepos + offset, SEEK_SET) != 0) {
        return false;
    }

    if (bfd_read(location, count, abfd) != count) {
        return false;
    }

    return true;
}

static bool som_set_section_contents(bfd *abfd, sec_ptr section, const void *location, file_ptr offset, bfd_size_type count) {
    if (!abfd->output_has_begun) {
        som_prep_headers(abfd);
        abfd->output_has_begun = true;
        som_begin_writing(abfd);
    }

    if (!som_is_subspace(section) || (section->flags & SEC_HAS_CONTENTS) == 0) {
        return true;
    }

    offset += som_section_data(section)->subspace_dict->file_loc_init_value;

    if (bfd_seek(abfd, offset, SEEK_SET) != 0 || bfd_write(location, count, abfd) != count) {
        return false;
    }
    
    return true;
}

bool som_set_arch_mach(bfd *abfd, enum bfd_architecture arch, unsigned long machine) {
    return bfd_default_set_arch_mach(abfd, arch, machine);
}

bool som_find_nearest_line(bfd *abfd, asymbol **symbols, asection *section, bfd_vma offset,
                           const char **filename_ptr, const char **functionname_ptr,
                           unsigned int *line_ptr, unsigned int *discriminator_ptr) {
    if (discriminator_ptr) {
        *discriminator_ptr = 0;
    }

    bool found = false;
    if (_bfd_stab_section_find_nearest_line(abfd, symbols, section, offset, &found,
                                            filename_ptr, functionname_ptr, line_ptr,
                                            &somdata(abfd).line_info)) {
        return found;
    }

    if (!symbols) {
        return false;
    }

    asymbol *func = NULL;
    bfd_vma low_func = 0;
    for (asymbol **p = symbols; *p != NULL; p++) {
        som_symbol_type *q = (som_symbol_type *)*p;
        if (q->som_type == SYMBOL_TYPE_ENTRY && q->symbol.section == section && 
            q->symbol.value >= low_func && q->symbol.value <= offset) {
            func = (asymbol *)q;
            low_func = q->symbol.value;
        }
    }

    if (!func) {
        return false;
    }

    *filename_ptr = NULL;
    *functionname_ptr = bfd_asymbol_name(func);
    *line_ptr = 0;
    return true;
}

static int som_sizeof_headers(bfd *abfd, struct bfd_link_info *info)
{
    if (abfd == NULL || info == NULL) {
        _bfd_error_handler(_("Invalid arguments: abfd or info is NULL."));
        return -1;
    }

    _bfd_error_handler(_("som_sizeof_headers unimplemented"));
    abort();
    return 0;
}

/* Return the single-character symbol type corresponding to
   SOM section S, or '?' for an unknown SOM section.  */

#include <string.h>

static char som_section_type(const char *s) {
    if (s == NULL) {
        return '?';
    }
    
    for (const struct section_to_type *t = stt; t->section; t++) {
        if (strcmp(s, t->section) == 0) {
            return t->type;
        }
    }
    
    return '?';
}

static int som_decode_symclass(asymbol *symbol) {
    if (!symbol || !symbol->section) return '?';

    if (bfd_is_com_section(symbol->section)) return 'C';

    if (bfd_is_und_section(symbol->section)) {
        if (symbol->flags & BSF_WEAK) {
            return (symbol->flags & BSF_OBJECT) ? 'v' : 'w';
        }
        return 'U';
    }

    if (bfd_is_ind_section(symbol->section)) return 'I';

    if (symbol->flags & BSF_WEAK) {
        return (symbol->flags & BSF_OBJECT) ? 'V' : 'W';
    }

    if (!(symbol->flags & (BSF_GLOBAL | BSF_LOCAL))) return '?';

    char c;
    if (bfd_is_abs_section(symbol->section) ||
        (som_symbol_data(symbol) && som_symbol_data(symbol)->som_type == SYMBOL_TYPE_ABSOLUTE)) {
        c = 'a';
    } else {
        c = som_section_type(symbol->section->name);
    }

    return (symbol->flags & BSF_GLOBAL) ? TOUPPER(c) : c;
}

/* Return information about SOM symbol SYMBOL in RET.  */

static void som_get_symbol_info(bfd *ignore_abfd ATTRIBUTE_UNUSED, asymbol *symbol, symbol_info *ret) {
    ret->type = som_decode_symclass(symbol);
    ret->value = (ret->type != 'U') ? symbol->value + symbol->section->vma : 0;
    ret->name = symbol->name ? symbol->name : "";
}

/* Count the number of symbols in the archive symbol table.  Necessary
   so that we can allocate space for all the carsyms at once.  */

static bool som_bfd_count_ar_symbols(bfd *abfd, struct som_lst_header *lst_header, symindex *count) {
    unsigned char *hash_table = NULL;
    size_t amt, hash_table_size;
    file_ptr lst_filepos = bfd_tell(abfd) - sizeof(struct som_external_lst_header);

    if (_bfd_mul_overflow(lst_header->hash_size, sizeof(unsigned int), &hash_table_size)) {
        bfd_set_error(bfd_error_file_too_big);
        return false;
    }
    hash_table = _bfd_malloc_and_read(abfd, hash_table_size, hash_table_size);
    if (hash_table == NULL && lst_header->hash_size != 0) {
        bfd_set_error(bfd_error_no_memory);
        free(hash_table);
        return false;
    }

    *count = 0;

    for (unsigned int i = 0; i < lst_header->hash_size; i++) {
        struct som_external_lst_symbol_record ext_lst_symbol;
        unsigned int hash_val = bfd_getb32(hash_table + sizeof(unsigned int) * i);

        if (hash_val == 0) continue;

        if (bfd_seek(abfd, lst_filepos + hash_val, SEEK_SET) != 0) {
            bfd_set_error(bfd_error_invalid_operation);
            free(hash_table);
            return false;
        }

        amt = sizeof(ext_lst_symbol);
        if (bfd_read(&ext_lst_symbol, amt, abfd) != amt) {
            bfd_set_error(bfd_error_invalid_read);
            free(hash_table);
            return false;
        }

        (*count)++;

        while (true) {
            unsigned int next_entry = bfd_getb32(ext_lst_symbol.next_entry);
            if (next_entry == 0) break;

            if (next_entry <= hash_val + sizeof(ext_lst_symbol)) {
                bfd_set_error(bfd_error_bad_value);
                free(hash_table);
                return false;
            }
            hash_val = next_entry;

            if (bfd_seek(abfd, lst_filepos + next_entry, SEEK_SET) != 0) {
                bfd_set_error(bfd_error_invalid_operation);
                free(hash_table);
                return false;
            }

            if (bfd_read(&ext_lst_symbol, amt, abfd) != amt) {
                bfd_set_error(bfd_error_invalid_read);
                free(hash_table);
                return false;
            }

            (*count)++;
        }
    }
    free(hash_table);
    return true;
}

/* Fill in the canonical archive symbols (SYMS) from the archive described
   by ABFD and LST_HEADER.  */

#include <stdbool.h>
#include <stdlib.h>

static bool som_bfd_fill_in_ar_symbols(bfd *abfd, struct som_lst_header *lst_header, carsym **syms) {
    if (!abfd || !lst_header || !syms) {
        return false;
    }

    size_t amt;
    file_ptr lst_filepos = bfd_tell(abfd) - sizeof(struct som_external_lst_header);

    unsigned char *hash_table = NULL;
    struct som_external_som_entry *som_dict = NULL;

    if (_bfd_mul_overflow(lst_header->hash_size, 4, &amt)) {
        bfd_set_error(bfd_error_file_too_big);
        return false;
    }

    if (lst_header->hash_size != 0) {
        hash_table = _bfd_malloc_and_read(abfd, amt, amt);
        if (!hash_table) {
            bfd_set_error(bfd_error_no_memory);
            return false;
        }
    }

    if (bfd_seek(abfd, lst_filepos + lst_header->dir_loc, SEEK_SET) != 0) {
        free(hash_table);
        return false;
    }

    if (_bfd_mul_overflow(lst_header->module_count, sizeof(struct som_external_som_entry), &amt)) {
        bfd_set_error(bfd_error_file_too_big);
        free(hash_table);
        return false;
    }

    if (lst_header->module_count != 0) {
        som_dict = _bfd_malloc_and_read(abfd, amt, amt);
        if (!som_dict) {
            free(hash_table);
            bfd_set_error(bfd_error_no_memory);
            return false;
        }
    }

    carsym *set = syms[0];
    unsigned int string_loc = lst_header->string_loc;

    for (unsigned int i = 0; i < lst_header->hash_size; i++) {
        unsigned int hash_val = bfd_getb32(hash_table + 4 * i);
        if (hash_val == 0) {
            continue;
        }

        if (bfd_seek(abfd, lst_filepos + hash_val, SEEK_SET) != 0) {
            free(hash_table);
            free(som_dict);
            return false;
        }

        struct som_external_lst_symbol_record lst_symbol;
        if (bfd_read(&lst_symbol, sizeof(lst_symbol), abfd) != sizeof(lst_symbol)) {
            free(hash_table);
            free(som_dict);
            return false;
        }

        do {
            if (bfd_seek(abfd, lst_filepos + string_loc + bfd_getb32(lst_symbol.name) - 4, SEEK_SET) != 0) {
                free(hash_table);
                free(som_dict);
                return false;
            }

            unsigned char ext_len[4];
            if (bfd_read(&ext_len, 4, abfd) != 4) {
                free(hash_table);
                free(som_dict);
                return false;
            }
            size_t len = bfd_getb32(ext_len);
            if (len == (size_t)-1) {
                free(hash_table);
                free(som_dict);
                bfd_set_error(bfd_error_no_memory);
                return false;
            }

            char *name = _bfd_alloc_and_read(abfd, len + 1, len);
            if (!name) {
                free(hash_table);
                free(som_dict);
                return false;
            }
            name[len] = '\0';
            set->name = name;

            unsigned int ndx = bfd_getb32(lst_symbol.som_index);
            if (ndx >= lst_header->module_count) {
                free(hash_table);
                free(som_dict);
                bfd_set_error(bfd_error_bad_value);
                return false;
            }
            set->file_offset = bfd_getb32(som_dict[ndx].location) - sizeof(struct ar_hdr);
            set++;

        } while ((lst_symbol.next_entry = bfd_getb32(lst_symbol.next_entry)) != 0);

    }

    free(hash_table);
    free(som_dict);
    return true;
}

/* Read in the LST from the archive.  */

#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

static bool som_slurp_armap(bfd *abfd) {
    struct som_external_lst_header ext_lst_header;
    struct som_lst_header lst_header;
    struct ar_hdr ar_header;
    unsigned int parsed_size;
    struct artdata *ardata = bfd_ardata(abfd);
    char nextname[17] = {0};
    size_t amt = 16;

    if (bfd_read(nextname, amt, abfd) != amt) {
        return false;
    }

    if (bfd_seek(abfd, -16, SEEK_CUR) != 0) {
        return false;
    }

    if (!startswith(nextname, "/               ")) {
        abfd->has_armap = false;
        return true;
    }

    amt = sizeof(struct ar_hdr);
    if (bfd_read(&ar_header, amt, abfd) != amt) {
        return false;
    }

    if (strncmp(ar_header.ar_fmag, ARFMAG, 2) != 0) {
        bfd_set_error(bfd_error_malformed_archive);
        return false;
    }

    errno = 0;
    parsed_size = strtol(ar_header.ar_size, NULL, 10);
    if (errno != 0) {
        bfd_set_error(bfd_error_malformed_archive);
        return false;
    }

    ardata->first_file_filepos = bfd_tell(abfd) + parsed_size;

    amt = sizeof(struct som_external_lst_header);
    if (bfd_read(&ext_lst_header, amt, abfd) != amt) {
        return false;
    }

    som_swap_lst_header_in(&ext_lst_header, &lst_header);

    if (lst_header.a_magic != LIBMAGIC) {
        bfd_set_error(bfd_error_malformed_archive);
        return false;
    }

    if (!som_bfd_count_ar_symbols(abfd, &lst_header, &ardata->symdef_count)) {
        return false;
    }

    if (bfd_seek(abfd, (ardata->first_file_filepos - parsed_size + sizeof(struct som_external_lst_header)), SEEK_SET) != 0) {
        return false;
    }

    ardata->cache = 0;
    if (_bfd_mul_overflow(ardata->symdef_count, sizeof(carsym), &amt)) {
        bfd_set_error(bfd_error_file_too_big);
        return false;
    }

    ardata->symdefs = bfd_alloc(abfd, amt);
    if (!ardata->symdefs) {
        return false;
    }

    if (!som_bfd_fill_in_ar_symbols(abfd, &lst_header, &ardata->symdefs)) {
        return false;
    }

    if (bfd_seek(abfd, ardata->first_file_filepos, SEEK_SET) != 0) {
        return false;
    }

    abfd->has_armap = true;
    return true;
}

/* Begin preparing to write a SOM library symbol table.

   As part of the prep work we need to determine the number of symbols
   and the size of the associated string section.  */

bool som_bfd_prep_for_ar_write(bfd *abfd, unsigned int *num_syms, unsigned int *stringsize) {
    if (!abfd || !num_syms || !stringsize) return false;

    *num_syms = 0;
    *stringsize = 0;
    bfd *curr_bfd = abfd->archive_head;
    
    while (curr_bfd) {
        if (curr_bfd->format != bfd_object || curr_bfd->xvec->flavour != bfd_target_som_flavour) {
            curr_bfd = curr_bfd->archive_next;
            continue;
        }

        if (!som_slurp_symbol_table(curr_bfd)) return false;

        som_symbol_type *sym = obj_som_symtab(curr_bfd);
        unsigned int curr_count = bfd_get_symcount(curr_bfd);

        for (unsigned int i = 0; i < curr_count; i++, sym++) {
            struct som_misc_symbol_info info;
            som_bfd_derive_misc_symbol_info(curr_bfd, &sym->symbol, &info);

            if ((info.symbol_type == ST_NULL || 
                 info.symbol_type == ST_SYM_EXT || 
                 info.symbol_type == ST_ARG_EXT) || 
                 (info.symbol_scope != SS_UNIVERSAL && info.symbol_type != ST_STORAGE) || 
                 bfd_is_und_section(sym->symbol.section)) {
                continue;
            }

            (*num_syms)++;
            *stringsize += strlen(sym->symbol.name) + 5;
            *stringsize = (*stringsize + 3) & ~3;
        }

        curr_bfd = curr_bfd->archive_next;
    }

    return true;
}

/* Hash a symbol name based on the hashing algorithm presented in the
   SOM ABI.  */

#include <string.h>

static unsigned int som_bfd_ar_symbol_hash(asymbol *symbol) {
    if (symbol == NULL || symbol->name == NULL) {
        return 0;  // Handle null pointers
    }

    unsigned int len = strlen(symbol->name);

    if (len == 1) {
        unsigned char ch = symbol->name[0];
        return 0x1000100 | (ch << 16) | ch;
    }

    unsigned char first_char = symbol->name[1];
    unsigned char second_last_char = symbol->name[len - 2];
    unsigned char last_char = symbol->name[len - 1];

    return ((len & 0x7F) << 24) | (first_char << 16) | (second_last_char << 8) | last_char;
}

/* Do the bulk of the work required to write the SOM library
   symbol table.  */

#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

static bool som_bfd_ar_write_symbol_stuff(bfd *abfd, unsigned int nsyms, unsigned int string_size, struct som_external_lst_header lst, unsigned elength) {
    char *strings = NULL;
    struct som_external_lst_symbol_record *lst_syms = NULL;
    bfd *curr_bfd;
    unsigned char *hash_table = NULL;
    struct som_external_som_entry *som_dict = NULL;
    struct som_external_lst_symbol_record **last_hash_entry = NULL;
    unsigned int curr_som_offset, som_index = 0;
    size_t amt;
    unsigned int module_count;
    unsigned int hash_size;

    hash_size = bfd_getb32(lst.hash_size);
    if (_bfd_mul_overflow(hash_size, 4, &amt)) {
        bfd_set_error(bfd_error_no_memory);
        return false;
    }
    hash_table = bfd_zmalloc(amt);
    if (!hash_table && hash_size)
        goto error_return;

    module_count = bfd_getb32(lst.module_count);
    if (_bfd_mul_overflow(module_count, sizeof(struct som_external_som_entry), &amt)) {
        bfd_set_error(bfd_error_no_memory);
        goto error_return;
    }
    som_dict = bfd_zmalloc(amt);
    if (!som_dict && module_count)
        goto error_return;

    if (_bfd_mul_overflow(hash_size, sizeof(struct som_external_lst_symbol_record *), &amt)) {
        bfd_set_error(bfd_error_no_memory);
        goto error_return;
    }
    last_hash_entry = bfd_zmalloc(amt);
    if (!last_hash_entry && hash_size)
        goto error_return;

    curr_som_offset = 8 + 2 * sizeof(struct ar_hdr) + bfd_getb32(lst.file_end);
    if (elength)
        curr_som_offset += elength;

    curr_som_offset = (curr_som_offset + 0x1) & ~0x1;

    if (_bfd_mul_overflow(nsyms, sizeof(struct som_external_lst_symbol_record), &amt)) {
        bfd_set_error(bfd_error_no_memory);
        goto error_return;
    }
    lst_syms = bfd_malloc(amt);
    if (!lst_syms && nsyms)
        goto error_return;
    strings = bfd_malloc(string_size);
    if (!strings && string_size)
        goto error_return;

    char *p = strings;
    struct som_external_lst_symbol_record *curr_lst_sym = lst_syms;

    curr_bfd = abfd->archive_head;
    while (curr_bfd) {
        if (curr_bfd->format != bfd_object || curr_bfd->xvec->flavour != bfd_target_som_flavour) {
            curr_bfd = curr_bfd->archive_next;
            continue;
        }

        if (!som_slurp_symbol_table(curr_bfd))
            goto error_return;

        som_symbol_type *sym = obj_som_symtab(curr_bfd);
        unsigned int curr_count = bfd_get_symcount(curr_bfd);

        for (unsigned int i = 0; i < curr_count; i++, sym++) {
            struct som_misc_symbol_info info;
            som_bfd_derive_misc_symbol_info(curr_bfd, &sym->symbol, &info);

            if (info.symbol_type == ST_NULL || info.symbol_type == ST_SYM_EXT || info.symbol_type == ST_ARG_EXT)
                continue;

            if (info.symbol_scope != SS_UNIVERSAL && info.symbol_type != ST_STORAGE)
                continue;

            if (bfd_is_und_section(sym->symbol.section))
                continue;

            if (bfd_getb32(som_dict[som_index].location) == 0) {
                bfd_putb32(curr_som_offset, som_dict[som_index].location);
                bfd_putb32(arelt_size(curr_bfd), som_dict[som_index].length);
            }

            unsigned int symbol_key = som_bfd_ar_symbol_hash(&sym->symbol);

            unsigned int flags = 0;
            if (info.secondary_def)
                flags |= LST_SYMBOL_SECONDARY_DEF;
            flags |= info.symbol_type << LST_SYMBOL_SYMBOL_TYPE_SH;
            flags |= info.symbol_scope << LST_SYMBOL_SYMBOL_SCOPE_SH;
            if (bfd_is_com_section(sym->symbol.section))
                flags |= LST_SYMBOL_IS_COMMON;
            if (info.dup_common)
                flags |= LST_SYMBOL_DUP_COMMON;
            flags |= 3 << LST_SYMBOL_XLEAST_SH;
            flags |= info.arg_reloc << LST_SYMBOL_ARG_RELOC_SH;
            bfd_putb32(flags, curr_lst_sym->flags);
            bfd_putb32(p - strings + 4, curr_lst_sym->name);
            bfd_putb32(0, curr_lst_sym->qualifier_name);
            bfd_putb32(info.symbol_info, curr_lst_sym->symbol_info);
            bfd_putb32(info.symbol_value | info.priv_level, curr_lst_sym->symbol_value);
            bfd_putb32(0, curr_lst_sym->symbol_descriptor);
            curr_lst_sym->reserved = 0;
            bfd_putb32(som_index, curr_lst_sym->som_index);
            bfd_putb32(symbol_key, curr_lst_sym->symbol_key);
            bfd_putb32(0, curr_lst_sym->next_entry);

            unsigned int symbol_pos = (curr_lst_sym - lst_syms) * sizeof(struct som_external_lst_symbol_record)
                                       + hash_size * 4 + module_count * sizeof(struct som_external_som_entry)
                                       + sizeof(struct som_external_lst_header);
            struct som_external_lst_symbol_record *last = last_hash_entry[symbol_key % hash_size];
            if (last) {
                bfd_putb32(symbol_pos, last->next_entry);
            } else {
                bfd_putb32(symbol_pos, hash_table + 4 * (symbol_key % hash_size));
            }
            last_hash_entry[symbol_key % hash_size] = curr_lst_sym;

            unsigned int slen = strlen(sym->symbol.name);
            bfd_put_32(abfd, slen, p);
            p += 4;
            slen++;
            memcpy(p, sym->symbol.name, slen);
            p += slen;
            while (slen % 4) {
                bfd_put_8(abfd, 0, p);
                p++;
                slen++;
            }

            curr_lst_sym++;
        }

        curr_som_offset += arelt_size(curr_bfd) + sizeof(struct ar_hdr);
        curr_som_offset = (curr_som_offset + 0x1) & ~(unsigned)1;
        curr_bfd = curr_bfd->archive_next;
        som_index++;
    }

    amt = (size_t)hash_size * 4;
    if (bfd_write(hash_table, amt, abfd) != amt)
        goto error_return;

    amt = (size_t)module_count * sizeof(struct som_external_som_entry);
    if (bfd_write(som_dict, amt, abfd) != amt)
        goto error_return;

    amt = (size_t)nsyms * sizeof(struct som_external_lst_symbol_record);
    if (bfd_write(lst_syms, amt, abfd) != amt)
        goto error_return;

    amt = string_size;
    if (bfd_write(strings, amt, abfd) != amt)
        goto error_return;

    free(hash_table);
    free(som_dict);
    free(last_hash_entry);
    free(lst_syms);
    free(strings);
    return true;

error_return:
    free(hash_table);
    free(som_dict);
    free(last_hash_entry);
    free(lst_syms);
    free(strings);
    return false;
}

/* Write out the LST for the archive.

   You'll never believe this is really how armaps are handled in SOM...  */

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <sys/stat.h>
#include <string.h>
#include <stdio.h>

static bool som_write_armap(bfd *abfd, unsigned int elength, struct orl *map, unsigned int orl_count, int stridx) {
    bfd *curr_bfd;
    struct stat statbuf;
    unsigned int i, lst_size, nsyms, stringsize;
    struct ar_hdr hdr;
    struct som_external_lst_header lst;
    unsigned int csum;
    unsigned int module_count;

    if (stat(bfd_get_filename(abfd), &statbuf) != 0) {
        bfd_set_error(bfd_error_system_call);
        return false;
    }

    bfd_ardata(abfd)->armap_timestamp = statbuf.st_mtime + 60;

    lst_size = sizeof(struct som_external_lst_header);

    bfd_putb16(CPU_PA_RISC1_0, &lst.system_id);
    bfd_putb16(LIBMAGIC, &lst.a_magic);
    bfd_putb32(VERSION_ID, &lst.version_id);
    memset(&lst.file_time, 0, sizeof(lst.file_time));

    bfd_putb32(lst_size, &lst.hash_loc);
    bfd_putb32(SOM_LST_HASH_SIZE, &lst.hash_size);

    lst_size += 4 * SOM_LST_HASH_SIZE;

    curr_bfd = abfd->archive_head;
    module_count = 0;
    while (curr_bfd != NULL) {
        if (curr_bfd->format == bfd_object && curr_bfd->xvec->flavour == bfd_target_som_flavour) {
            module_count++;
        }
        curr_bfd = curr_bfd->archive_next;
    }
    bfd_putb32(module_count, &lst.module_count);
    bfd_putb32(module_count, &lst.module_limit);
    bfd_putb32(lst_size, &lst.dir_loc);
    lst_size += sizeof(struct som_external_som_entry) * module_count;

    bfd_putb32(0, &lst.export_loc);
    bfd_putb32(0, &lst.export_count);
    bfd_putb32(0, &lst.import_loc);
    bfd_putb32(0, &lst.aux_loc);
    bfd_putb32(0, &lst.aux_size);

    if (!som_bfd_prep_for_ar_write(abfd, &nsyms, &stringsize)) {
        return false;
    }

    lst_size += sizeof(struct som_external_lst_symbol_record) * nsyms;

    bfd_putb32(lst_size, &lst.string_loc);
    bfd_putb32(stringsize, &lst.string_size);
    lst_size += stringsize;

    bfd_putb32(0, &lst.free_list);
    bfd_putb32(lst_size, &lst.file_end);

    csum = 0;
    for (i = 0; i < sizeof(struct som_external_lst_header) - sizeof(int); i += 4) {
        csum ^= bfd_getb32((unsigned char *)&lst + i);
    }
    bfd_putb32(csum, &lst.checksum);

    sprintf(hdr.ar_name, "/              ");
    _bfd_ar_spacepad(hdr.ar_date, sizeof(hdr.ar_date), "%-12ld", bfd_ardata(abfd)->armap_timestamp);
    _bfd_ar_spacepad(hdr.ar_uid, sizeof(hdr.ar_uid), "%ld", statbuf.st_uid);
    _bfd_ar_spacepad(hdr.ar_gid, sizeof(hdr.ar_gid), "%ld", statbuf.st_gid);
    _bfd_ar_spacepad(hdr.ar_mode, sizeof(hdr.ar_mode), "%-8o", (unsigned int)statbuf.st_mode);
    _bfd_ar_spacepad(hdr.ar_size, sizeof(hdr.ar_size), "%-10d", (int)lst_size);
    hdr.ar_fmag[0] = '`';
    hdr.ar_fmag[1] = '\012';

    for (i = 0; i < sizeof(struct ar_hdr); i++) {
        if (((char *)(&hdr))[i] == '\0') {
            ((char *)(&hdr))[i] = ' ';
        }
    }

    size_t amt = sizeof(struct ar_hdr);
    if (bfd_write(&hdr, amt, abfd) != amt) {
        return false;
    }

    amt = sizeof(struct som_external_lst_header);
    if (bfd_write(&lst, amt, abfd) != amt) {
        return false;
    }

    if (!som_bfd_ar_write_symbol_stuff(abfd, nsyms, stringsize, lst, elength)) {
        return false;
    }

    return true;
}

/* Throw away some malloc'd information for this BFD.  */

#include <stdbool.h>
#include <stdlib.h>

static inline void free_and_nullify(void **ptr) {
    if (ptr != NULL && *ptr != NULL) {
        free(*ptr);
        *ptr = NULL;
    }
}

static bool som_bfd_free_cached_info(bfd *abfd) {
    if (abfd == NULL) {
        return false;
    }

    bfd_format format = bfd_get_format(abfd);

    if (format == bfd_object || format == bfd_core) {
        asection *section = abfd->sections;

        free_and_nullify((void **)&obj_som_symtab(abfd));
        free_and_nullify((void **)&obj_som_stringtab(abfd));

        while (section != NULL) {
            section->reloc_count = (unsigned) -1;
            free_and_nullify((void **)&som_section_data(section)->reloc_stream);
            section = section->next;
        }
    }

    return true;
}

/* End of miscellaneous support functions.  */

/* Linker support functions.  */

static bool som_bfd_link_split_section(bfd *abfd, asection *sec) {
    if (sec && som_is_subspace(sec) && sec->size > 240000) {
        return true;
    }
    return false;
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

