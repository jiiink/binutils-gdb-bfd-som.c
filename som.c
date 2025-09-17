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
  #define QUEUE_SIZE 4
  
  for (int i = 0; i < QUEUE_SIZE; i++) {
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
  for (int i = 3; i > 0; i--) {
    queue[i].reloc = queue[i - 1].reloc;
    queue[i].size = queue[i - 1].size;
  }
  queue[0].reloc = p;
  queue[0].size = size;
}

/* When an entry in the relocation queue is reused, the entry moves
   to the front of the queue.  */

static void
swap_queue_elements(struct reloc_queue *queue, unsigned int src, unsigned int dst)
{
    unsigned char *tmp_reloc = queue[dst].reloc;
    unsigned int tmp_size = queue[dst].size;
    queue[dst].reloc = queue[src].reloc;
    queue[dst].size = queue[src].size;
    queue[src].reloc = tmp_reloc;
    queue[src].size = tmp_size;
}

static void
rotate_queue_elements(struct reloc_queue *queue, unsigned int count)
{
    unsigned char *first_reloc = queue[0].reloc;
    unsigned int first_size = queue[0].size;
    
    for (unsigned int i = 0; i < count - 1; i++)
    {
        queue[i].reloc = queue[i + 1].reloc;
        queue[i].size = queue[i + 1].size;
    }
    
    queue[count - 1].reloc = first_reloc;
    queue[count - 1].size = first_size;
}

static void
som_reloc_queue_fix(struct reloc_queue *queue, unsigned int idx)
{
    #define MIN_INDEX 0
    #define MAX_INDEX 3
    
    if (idx == MIN_INDEX)
        return;

    if (idx == 1)
    {
        swap_queue_elements(queue, 0, 1);
        return;
    }

    if (idx >= 2 && idx <= MAX_INDEX)
    {
        unsigned char *first_reloc = queue[0].reloc;
        unsigned int first_size = queue[0].size;
        
        queue[0].reloc = queue[idx].reloc;
        queue[0].size = queue[idx].size;
        
        for (unsigned int i = idx; i > 1; i--)
        {
            queue[i].reloc = queue[i - 1].reloc;
            queue[i].size = queue[i - 1].size;
        }
        
        queue[1].reloc = first_reloc;
        queue[1].size = first_size;
        return;
    }
    
    abort();
}

/* Search for a particular relocation in the relocation queue.  */

static int
som_reloc_queue_find (unsigned char *p,
                     unsigned int size,
                     struct reloc_queue *queue)
{
  #define QUEUE_SIZE 4
  
  for (int i = 0; i < QUEUE_SIZE; i++)
    {
      if (queue[i].reloc && !memcmp (p, queue[i].reloc, size)
          && size == queue[i].size)
        return i;
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
  int queue_index = som_reloc_queue_find (p, size, queue);

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
write_large_skip_entries(bfd *abfd,
                        unsigned int *skip,
                        unsigned char *p,
                        unsigned int *subspace_reloc_sizep,
                        struct reloc_queue *queue)
{
    #define LARGE_SKIP_SIZE 0x1000000
    
    *skip -= LARGE_SKIP_SIZE;
    bfd_put_8(abfd, R_NO_RELOCATION + 31, p);
    bfd_put_8(abfd, 0xff, p + 1);
    bfd_put_16(abfd, (bfd_vma) 0xffff, p + 2);
    p = try_prev_fixup(abfd, subspace_reloc_sizep, p, 4, queue);
    
    while (*skip >= LARGE_SKIP_SIZE)
    {
        *skip -= LARGE_SKIP_SIZE;
        bfd_put_8(abfd, R_PREV_FIXUP, p);
        p++;
        *subspace_reloc_sizep += 1;
    }
    
    return p;
}

static unsigned char *
write_single_byte_relocation(bfd *abfd,
                            unsigned int skip,
                            unsigned char *p,
                            unsigned int *subspace_reloc_sizep)
{
    bfd_put_8(abfd, R_NO_RELOCATION + (skip >> 2) - 1, p);
    *subspace_reloc_sizep += 1;
    return p + 1;
}

static unsigned char *
write_two_byte_relocation(bfd *abfd,
                         unsigned int skip,
                         unsigned char *p,
                         unsigned int *subspace_reloc_sizep,
                         struct reloc_queue *queue)
{
    #define TWO_BYTE_OFFSET 24
    #define BYTE_SHIFT 8
    
    bfd_put_8(abfd, R_NO_RELOCATION + TWO_BYTE_OFFSET + (((skip >> 2) - 1) >> BYTE_SHIFT), p);
    bfd_put_8(abfd, (skip >> 2) - 1, p + 1);
    return try_prev_fixup(abfd, subspace_reloc_sizep, p, 2, queue);
}

static unsigned char *
write_three_byte_relocation(bfd *abfd,
                           unsigned int skip,
                           unsigned char *p,
                           unsigned int *subspace_reloc_sizep,
                           struct reloc_queue *queue)
{
    #define THREE_BYTE_OFFSET 28
    #define WORD_SHIFT 16
    
    bfd_put_8(abfd, R_NO_RELOCATION + THREE_BYTE_OFFSET + (((skip >> 2) - 1) >> WORD_SHIFT), p);
    bfd_put_16(abfd, (bfd_vma) (skip >> 2) - 1, p + 1);
    return try_prev_fixup(abfd, subspace_reloc_sizep, p, 3, queue);
}

static unsigned char *
write_four_byte_relocation(bfd *abfd,
                          unsigned int skip,
                          unsigned char *p,
                          unsigned int *subspace_reloc_sizep,
                          struct reloc_queue *queue)
{
    #define FOUR_BYTE_OFFSET 31
    #define SKIP_SHIFT 16
    
    bfd_put_8(abfd, R_NO_RELOCATION + FOUR_BYTE_OFFSET, p);
    bfd_put_8(abfd, (skip - 1) >> SKIP_SHIFT, p + 1);
    bfd_put_16(abfd, (bfd_vma) skip - 1, p + 2);
    return try_prev_fixup(abfd, subspace_reloc_sizep, p, 4, queue);
}

static unsigned char *
write_aligned_skip_relocation(bfd *abfd,
                              unsigned int skip,
                              unsigned char *p,
                              unsigned int *subspace_reloc_sizep,
                              struct reloc_queue *queue)
{
    #define SINGLE_BYTE_MAX 0x60
    #define TWO_BYTE_MAX 0x1000
    
    if (skip <= SINGLE_BYTE_MAX)
    {
        return write_single_byte_relocation(abfd, skip, p, subspace_reloc_sizep);
    }
    else if (skip <= TWO_BYTE_MAX)
    {
        return write_two_byte_relocation(abfd, skip, p, subspace_reloc_sizep, queue);
    }
    else
    {
        return write_three_byte_relocation(abfd, skip, p, subspace_reloc_sizep, queue);
    }
}

static unsigned char *
som_reloc_skip(bfd *abfd,
              unsigned int skip,
              unsigned char *p,
              unsigned int *subspace_reloc_sizep,
              struct reloc_queue *queue)
{
    #define LARGE_THRESHOLD 0x1000000
    #define ALIGNED_MAX 0xc0000
    #define ALIGNMENT_MASK 3
    
    if (skip >= LARGE_THRESHOLD)
    {
        p = write_large_skip_entries(abfd, &skip, p, subspace_reloc_sizep, queue);
    }
    
    if ((skip & ALIGNMENT_MASK) == 0 && skip <= ALIGNED_MAX && skip > 0)
    {
        p = write_aligned_skip_relocation(abfd, skip, p, subspace_reloc_sizep, queue);
    }
    else if (skip > 0)
    {
        p = write_four_byte_relocation(abfd, skip, p, subspace_reloc_sizep, queue);
    }
    
    return p;
}

/* Emit the proper R_DATA_OVERRIDE fixups to handle a nonzero addend
   from a BFD relocation.  Update the size of the subspace relocation
   stream via SUBSPACE_RELOC_SIZE_P; also return the current pointer
   into the relocation stream.  */

static unsigned char *
write_override_header(bfd *abfd, unsigned char *p, int override_size)
{
    bfd_put_8(abfd, R_DATA_OVERRIDE + override_size, p);
    return p + 1;
}

static unsigned char *
write_addend_8bit(bfd *abfd, bfd_vma addend, unsigned char *p)
{
    p = write_override_header(abfd, p, 1);
    bfd_put_8(abfd, addend, p);
    return p + 1;
}

static unsigned char *
write_addend_16bit(bfd *abfd, bfd_vma addend, unsigned char *p)
{
    p = write_override_header(abfd, p, 2);
    bfd_put_16(abfd, addend, p);
    return p + 2;
}

static unsigned char *
write_addend_24bit(bfd *abfd, bfd_vma addend, unsigned char *p)
{
    p = write_override_header(abfd, p, 3);
    bfd_put_8(abfd, addend >> 16, p);
    bfd_put_16(abfd, addend, p + 1);
    return p + 3;
}

static unsigned char *
write_addend_32bit(bfd *abfd, bfd_vma addend, unsigned char *p)
{
    p = write_override_header(abfd, p, 4);
    bfd_put_32(abfd, addend, p);
    return p + 4;
}

#define ADDEND_8BIT_LIMIT 0x100
#define ADDEND_16BIT_LIMIT 0x10000
#define ADDEND_24BIT_LIMIT 0x1000000
#define ADDEND_8BIT_OFFSET 0x80
#define ADDEND_16BIT_OFFSET 0x8000
#define ADDEND_24BIT_OFFSET 0x800000

static unsigned char *
som_reloc_addend(bfd *abfd,
                 bfd_vma addend,
                 unsigned char *p,
                 unsigned int *subspace_reloc_sizep,
                 struct reloc_queue *queue)
{
    unsigned char *start_p = p;
    int fixup_size;
    
    if (addend + ADDEND_8BIT_OFFSET < ADDEND_8BIT_LIMIT)
    {
        p = write_addend_8bit(abfd, addend, p);
        fixup_size = 2;
    }
    else if (addend + ADDEND_16BIT_OFFSET < ADDEND_16BIT_LIMIT)
    {
        p = write_addend_16bit(abfd, addend, p);
        fixup_size = 3;
    }
    else if (addend + ADDEND_24BIT_OFFSET < ADDEND_24BIT_LIMIT)
    {
        p = write_addend_24bit(abfd, addend, p);
        fixup_size = 4;
    }
    else
    {
        p = write_addend_32bit(abfd, addend, p);
        fixup_size = 5;
    }
    
    return try_prev_fixup(abfd, subspace_reloc_sizep, start_p, fixup_size, queue);
}

/* Handle a single function call relocation.  */

static int get_simple_relocation_type(int arg_bits)
{
  switch (arg_bits)
    {
    case 0:
    case 1:
      return 0;
    case 1 << 8:
    case 1 << 8 | 1:
      return 1;
    case 1 << 8 | 1 << 6:
    case 1 << 8 | 1 << 6 | 1:
      return 2;
    case 1 << 8 | 1 << 6 | 1 << 4:
    case 1 << 8 | 1 << 6 | 1 << 4 | 1:
      return 3;
    case 1 << 8 | 1 << 6 | 1 << 4 | 1 << 2:
    case 1 << 8 | 1 << 6 | 1 << 4 | 1 << 2 | 1:
      return 4;
    default:
      return -1;
    }
}

static unsigned char *emit_simple_relocation(bfd *abfd,
                                             unsigned char *p,
                                             unsigned int *subspace_reloc_sizep,
                                             int type,
                                             int sym_num,
                                             arelent *bfd_reloc,
                                             struct reloc_queue *queue)
{
  bfd_put_8 (abfd, bfd_reloc->howto->type + type, p);
  bfd_put_8 (abfd, sym_num, p + 1);
  return try_prev_fixup (abfd, subspace_reloc_sizep, p, 2, queue);
}

static int calculate_complex_type(int arg_bits, int rtn_bits)
{
  #define ARG_SHIFT_6_MASK 0xf
  #define ARG_SHIFT_2_MASK 0xf
  #define ARG_MAGIC_E 0xe
  #define TYPE_MULTIPLIER_HIGH 40
  #define TYPE_MULTIPLIER_LOW 4
  #define ARG_SHIFT_8 8
  #define ARG_SHIFT_6 6
  #define ARG_SHIFT_4 4
  #define ARG_SHIFT_2 2
  #define ARG_MASK_2BIT 3
  #define COMPLEX_FACTOR_9 9
  #define COMPLEX_FACTOR_3 3
  
  int type = rtn_bits;
  
  if ((arg_bits >> ARG_SHIFT_6 & ARG_SHIFT_6_MASK) == ARG_MAGIC_E)
    type += COMPLEX_FACTOR_9 * TYPE_MULTIPLIER_HIGH;
  else
    type += (COMPLEX_FACTOR_3 * (arg_bits >> ARG_SHIFT_8 & ARG_MASK_2BIT) + 
             (arg_bits >> ARG_SHIFT_6 & ARG_MASK_2BIT)) * TYPE_MULTIPLIER_HIGH;
  
  if ((arg_bits >> ARG_SHIFT_2 & ARG_SHIFT_2_MASK) == ARG_MAGIC_E)
    type += COMPLEX_FACTOR_9 * TYPE_MULTIPLIER_LOW;
  else
    type += (COMPLEX_FACTOR_3 * (arg_bits >> ARG_SHIFT_4 & ARG_MASK_2BIT) + 
             (arg_bits >> ARG_SHIFT_2 & ARG_MASK_2BIT)) * TYPE_MULTIPLIER_LOW;
  
  return type;
}

static unsigned char *emit_complex_relocation(bfd *abfd,
                                              unsigned char *p,
                                              unsigned int *subspace_reloc_sizep,
                                              int type,
                                              int sym_num,
                                              arelent *bfd_reloc,
                                              struct reloc_queue *queue)
{
  #define SYM_NUM_THRESHOLD 0x100
  #define TYPE_THRESHOLD 0x100
  #define HOWTO_OFFSET 10
  #define SYM_NUM_SHIFT 16
  
  bfd_put_8 (abfd, bfd_reloc->howto->type + HOWTO_OFFSET
             + 2 * (sym_num >= SYM_NUM_THRESHOLD) + (type >= TYPE_THRESHOLD),
             p);
  bfd_put_8 (abfd, type, p + 1);
  
  if (sym_num < SYM_NUM_THRESHOLD)
    {
      bfd_put_8 (abfd, sym_num, p + 2);
      return try_prev_fixup (abfd, subspace_reloc_sizep, p, 3, queue);
    }
  
  bfd_put_8 (abfd, sym_num >> SYM_NUM_SHIFT, p + 2);
  bfd_put_16 (abfd, (bfd_vma) sym_num, p + 3);
  return try_prev_fixup (abfd, subspace_reloc_sizep, p, 5, queue);
}

static unsigned char *
som_reloc_call (bfd *abfd,
		unsigned char *p,
		unsigned int *subspace_reloc_sizep,
		arelent *bfd_reloc,
		int sym_num,
		struct reloc_queue *queue)
{
  #define SYM_NUM_SIMPLE_THRESHOLD 0x100
  #define RETURN_TYPE_OFFSET 5
  #define ARG_RELOC_MASK 0x3
  
  int arg_bits = HPPA_R_ARG_RELOC (bfd_reloc->addend);
  int rtn_bits = arg_bits & ARG_RELOC_MASK;
  
  if (sym_num < SYM_NUM_SIMPLE_THRESHOLD)
    {
      int type = get_simple_relocation_type(arg_bits);
      if (type != -1)
        {
          if (rtn_bits)
            type += RETURN_TYPE_OFFSET;
          return emit_simple_relocation(abfd, p, subspace_reloc_sizep, 
                                        type, sym_num, bfd_reloc, queue);
        }
    }
  
  int type = calculate_complex_type(arg_bits, rtn_bits);
  return emit_complex_relocation(abfd, p, subspace_reloc_sizep, 
                                 type, sym_num, bfd_reloc, queue);
}

/* Return the logarithm of X, base 2, considering X unsigned,
   if X is a power of 2.  Otherwise, returns -1.  */

static int
exact_log2 (unsigned int x)
{
  if (x == 0 || x != (x & -x))
    return -1;

  int log = 0;
  while ((x >>= 1) != 0)
    log++;
    
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
  if (output_bfd)
    reloc_entry->address += input_section->output_offset;

  return bfd_reloc_ok;
}

/* Given a generic HPPA relocation type, the instruction format,
   and a field selector, return one or more appropriate SOM relocations.  */

int **
hppa_som_gen_reloc_type (bfd *abfd,
			 int base_type,
			 int format,
			 enum hppa_reloc_field_selector_type_alt field,
			 int sym_diff,
			 asymbol *sym)
{
  int *final_type, **final_types;

  final_types = bfd_alloc (abfd, (bfd_size_type) sizeof (int *) * 6);
  final_type = bfd_alloc (abfd, (bfd_size_type) sizeof (int));
  if (!final_types || !final_type)
    return NULL;

  if (!handle_field_selector(abfd, field, final_types, final_type, base_type))
    return NULL;

  if (!handle_base_type(abfd, base_type, format, field, sym_diff, sym, 
                        final_types, final_type))
    return NULL;

  return final_types;
}

static int
handle_field_selector(bfd *abfd, enum hppa_reloc_field_selector_type_alt field,
                      int **final_types, int *final_type, int base_type)
{
  switch (field)
    {
    case e_fsel:
    case e_psel:
    case e_lpsel:
    case e_rpsel:
      setup_simple_selector(final_types, final_type, base_type);
      break;

    case e_tsel:
    case e_ltsel:
    case e_rtsel:
      if (!setup_tsel_selector(abfd, field, final_types, final_type, base_type))
        return 0;
      break;

    case e_lssel:
    case e_rssel:
      if (!setup_mode_selector(abfd, R_S_MODE, final_types, final_type, base_type))
        return 0;
      break;

    case e_lsel:
    case e_rsel:
      if (!setup_mode_selector(abfd, R_N_MODE, final_types, final_type, base_type))
        return 0;
      break;

    case e_ldsel:
    case e_rdsel:
      if (!setup_mode_selector(abfd, R_D_MODE, final_types, final_type, base_type))
        return 0;
      break;

    case e_lrsel:
    case e_rrsel:
      if (!setup_mode_selector(abfd, R_R_MODE, final_types, final_type, base_type))
        return 0;
      break;

    case e_nsel:
      if (!setup_mode_selector(abfd, R_N1SEL, final_types, final_type, base_type))
        return 0;
      break;

    case e_nlsel:
    case e_nlrsel:
      if (!setup_nlsel_selector(abfd, field, final_types, final_type, base_type))
        return 0;
      break;

    case e_ltpsel:
    case e_rtpsel:
      abort ();
    }
  return 1;
}

static void
setup_simple_selector(int **final_types, int *final_type, int base_type)
{
  final_types[0] = final_type;
  final_types[1] = NULL;
  final_types[2] = NULL;
  *final_type = base_type;
}

static int
setup_tsel_selector(bfd *abfd, enum hppa_reloc_field_selector_type_alt field,
                    int **final_types, int *final_type, int base_type)
{
  final_types[0] = bfd_alloc (abfd, (bfd_size_type) sizeof (int));
  if (!final_types[0])
    return 0;
  
  if (field == e_tsel)
    *final_types[0] = R_FSEL;
  else if (field == e_ltsel)
    *final_types[0] = R_LSEL;
  else
    *final_types[0] = R_RSEL;
  
  final_types[1] = final_type;
  final_types[2] = NULL;
  *final_type = base_type;
  return 1;
}

static int
setup_mode_selector(bfd *abfd, int mode, int **final_types, 
                    int *final_type, int base_type)
{
  final_types[0] = bfd_alloc (abfd, (bfd_size_type) sizeof (int));
  if (!final_types[0])
    return 0;
  
  *final_types[0] = mode;
  final_types[1] = final_type;
  final_types[2] = NULL;
  *final_type = base_type;
  return 1;
}

static int
setup_nlsel_selector(bfd *abfd, enum hppa_reloc_field_selector_type_alt field,
                     int **final_types, int *final_type, int base_type)
{
  final_types[0] = bfd_alloc (abfd, (bfd_size_type) sizeof (int));
  if (!final_types[0])
    return 0;
  
  *final_types[0] = R_N0SEL;
  final_types[1] = bfd_alloc (abfd, (bfd_size_type) sizeof (int));
  if (!final_types[1])
    return 0;
  
  if (field == e_nlsel)
    *final_types[1] = R_N_MODE;
  else
    *final_types[1] = R_R_MODE;
  
  final_types[2] = final_type;
  final_types[3] = NULL;
  *final_type = base_type;
  return 1;
}

static int
handle_base_type(bfd *abfd, int base_type, int format,
                 enum hppa_reloc_field_selector_type_alt field,
                 int sym_diff, asymbol *sym, int **final_types, int *final_type)
{
  switch (base_type)
    {
    case R_HPPA:
      if (sym_diff)
        {
          if (!setup_sym_diff(abfd, field, format, final_types, final_type))
            return 0;
        }
      else
        handle_hppa_non_diff(field, format, sym, final_type);
      break;

    case R_HPPA_GOTOFF:
      handle_gotoff(field, format, final_type);
      break;

    case R_HPPA_COMPLEX:
      if (sym_diff)
        {
          if (!setup_sym_diff(abfd, field, format, final_types, final_type))
            return 0;
        }
      break;

    case R_HPPA_PCREL_CALL:
      {
#ifndef NO_PCREL_MODES
        if (!setup_pcrel_mode(abfd, format, base_type, final_types, final_type))
          return 0;
#endif
        break;
      }

    case R_HPPA_NONE:
    case R_HPPA_ABS_CALL:
      break;
    }
  return 1;
}

static int
setup_sym_diff(bfd *abfd, enum hppa_reloc_field_selector_type_alt field,
               int format, int **final_types, int *final_type)
{
  size_t amt = sizeof (int);

  final_types[0] = bfd_alloc (abfd, amt);
  final_types[1] = bfd_alloc (abfd, amt);
  final_types[2] = bfd_alloc (abfd, amt);
  final_types[3] = bfd_alloc (abfd, amt);
  if (!final_types[0] || !final_types[1] || !final_types[2])
    return 0;
  
  if (field == e_fsel)
    *final_types[0] = R_FSEL;
  else if (field == e_rsel)
    *final_types[0] = R_RSEL;
  else if (field == e_lsel)
    *final_types[0] = R_LSEL;
  
  *final_types[1] = R_COMP2;
  *final_types[2] = R_COMP2;
  *final_types[3] = R_COMP1;
  final_types[4] = final_type;
  
  if (format == 32)
    *final_types[4] = R_DATA_EXPR;
  else
    *final_types[4] = R_CODE_EXPR;
  
  final_types[5] = NULL;
  return 1;
}

static void
handle_hppa_non_diff(enum hppa_reloc_field_selector_type_alt field,
                     int format, asymbol *sym, int *final_type)
{
  if (field == e_psel || field == e_lpsel || field == e_rpsel)
    {
      if (format == 32)
        *final_type = R_DATA_PLABEL;
      else
        *final_type = R_CODE_PLABEL;
    }
  else if (field == e_tsel || field == e_ltsel || field == e_rtsel)
    {
      *final_type = R_DLT_REL;
    }
  else if (format == 32)
    {
      *final_type = R_DATA_ONE_SYMBOL;
      update_symbol_type_if_needed(sym);
    }
}

static void
update_symbol_type_if_needed(asymbol *sym)
{
  if (som_symbol_data (sym)->som_type == SYMBOL_TYPE_UNKNOWN
      && (sym->flags & BSF_SECTION_SYM) == 0
      && (sym->flags & BSF_FUNCTION) == 0
      && ! bfd_is_com_section (sym->section))
    som_symbol_data (sym)->som_type = SYMBOL_TYPE_DATA;
}

static void
handle_gotoff(enum hppa_reloc_field_selector_type_alt field,
              int format, int *final_type)
{
  if (field == e_psel || field == e_lpsel || field == e_rpsel)
    *final_type = R_DATA_PLABEL;
  else if (field == e_fsel && format == 32)
    *final_type = R_DATA_GPREL;
}

static int
setup_pcrel_mode(bfd *abfd, int format, int base_type,
                 int **final_types, int *final_type)
{
  size_t amt = sizeof (int);
  
  final_types[0] = bfd_alloc (abfd, amt);
  if (!final_types[0])
    return 0;
  
  if (format == 17)
    *final_types[0] = R_SHORT_PCREL_MODE;
  else
    *final_types[0] = R_LONG_PCREL_MODE;
  
  final_types[1] = final_type;
  final_types[2] = NULL;
  *final_type = base_type;
  return 1;
}

/* Return the address of the correct entry in the PA SOM relocation
   howto table.  */

static reloc_howto_type *
som_bfd_reloc_type_lookup (bfd *abfd ATTRIBUTE_UNUSED,
			   bfd_reloc_code_real_type code)
{
  const int max_relocation_code = R_NO_RELOCATION + 255;
  int code_value = (int) code;
  
  if (code_value >= max_relocation_code)
    return NULL;
    
  BFD_ASSERT (som_hppa_howto_table[code_value].type == code_value);
  return &som_hppa_howto_table[code_value];
}

static reloc_howto_type *
som_bfd_reloc_name_lookup (bfd *abfd ATTRIBUTE_UNUSED,
			   const char *r_name)
{
  const size_t table_size = sizeof(som_hppa_howto_table) / sizeof(som_hppa_howto_table[0]);
  
  for (size_t i = 0; i < table_size; i++)
    {
      if (som_hppa_howto_table[i].name != NULL
	  && strcasecmp (som_hppa_howto_table[i].name, r_name) == 0)
        return &som_hppa_howto_table[i];
    }

  return NULL;
}

static void
som_swap_clock_in (struct som_external_clock *src,
		   struct som_clock *dst)
{
  dst->secs = bfd_getb32 (src->secs);
  dst->nanosecs = bfd_getb32 (src->nanosecs);
}

static void
som_swap_clock_out (struct som_clock *src,
		    struct som_external_clock *dst)
{
  bfd_putb32 (src->secs, dst->secs);
  bfd_putb32 (src->nanosecs, dst->nanosecs);
}

static void
som_swap_header_in (struct som_external_header *src,
		    struct som_header *dst)
{
  dst->system_id = bfd_getb16 (src->system_id);
  dst->a_magic = bfd_getb16 (src->a_magic);
  dst->version_id = bfd_getb32 (src->version_id);
  som_swap_clock_in (&src->file_time, &dst->file_time);
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
som_swap_header_out (struct som_header *src,
		    struct som_external_header *dst)
{
  bfd_putb16 (src->system_id, dst->system_id);
  bfd_putb16 (src->a_magic, dst->a_magic);
  bfd_putb32 (src->version_id, dst->version_id);
  som_swap_clock_out (&src->file_time, &dst->file_time);
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
extract_space_flags(unsigned int flags, struct som_space_dictionary_record *dst)
{
  dst->is_loadable = (flags & SOM_SPACE_IS_LOADABLE) != 0;
  dst->is_defined = (flags & SOM_SPACE_IS_DEFINED) != 0;
  dst->is_private = (flags & SOM_SPACE_IS_PRIVATE) != 0;
  dst->has_intermediate_code = (flags & SOM_SPACE_HAS_INTERMEDIATE_CODE) != 0;
  dst->is_tspecific = (flags & SOM_SPACE_IS_TSPECIFIC) != 0;
  dst->sort_key = (flags >> SOM_SPACE_SORT_KEY_SH) & SOM_SPACE_SORT_KEY_MASK;
}

static void
copy_space_indices(struct som_external_space_dictionary_record *src,
                   struct som_space_dictionary_record *dst)
{
  dst->space_number = bfd_getb32 (src->space_number);
  dst->subspace_index = bfd_getb32 (src->subspace_index);
  dst->subspace_quantity = bfd_getb32 (src->subspace_quantity);
  dst->loader_fix_index = bfd_getb32 (src->loader_fix_index);
  dst->loader_fix_quantity = bfd_getb32 (src->loader_fix_quantity);
  dst->init_pointer_index = bfd_getb32 (src->init_pointer_index);
  dst->init_pointer_quantity = bfd_getb32 (src->init_pointer_quantity);
}

static void
som_swap_space_dictionary_in (struct som_external_space_dictionary_record *src,
			      struct som_space_dictionary_record *dst)
{
  unsigned int flags;

  dst->name = bfd_getb32 (src->name);
  flags = bfd_getb32 (src->flags);
  
  extract_space_flags(flags, dst);
  
  dst->reserved = 0;
  dst->reserved2 = 0;
  
  copy_space_indices(src, dst);
}

static unsigned int build_space_flags(const struct som_space_dictionary_record *src)
{
  unsigned int flags = 0;
  
  if (src->is_loadable)
    flags |= SOM_SPACE_IS_LOADABLE;
  if (src->is_defined)
    flags |= SOM_SPACE_IS_DEFINED;
  if (src->is_private)
    flags |= SOM_SPACE_IS_PRIVATE;
  if (src->has_intermediate_code)
    flags |= SOM_SPACE_HAS_INTERMEDIATE_CODE;
  if (src->is_tspecific)
    flags |= SOM_SPACE_IS_TSPECIFIC;
  
  flags |= (src->sort_key & SOM_SPACE_SORT_KEY_MASK) << SOM_SPACE_SORT_KEY_SH;
  
  return flags;
}

static void
som_swap_space_dictionary_out (struct som_space_dictionary_record *src,
			       struct som_external_space_dictionary_record *dst)
{
  bfd_putb32 (src->name, dst->name);
  bfd_putb32 (build_space_flags(src), dst->flags);
  bfd_putb32 (src->space_number, dst->space_number);
  bfd_putb32 (src->subspace_index, dst->subspace_index);
  bfd_putb32 (src->subspace_quantity, dst->subspace_quantity);
  bfd_putb32 (src->loader_fix_index, dst->loader_fix_index);
  bfd_putb32 (src->loader_fix_quantity, dst->loader_fix_quantity);
  bfd_putb32 (src->init_pointer_index, dst->init_pointer_index);
  bfd_putb32 (src->init_pointer_quantity, dst->init_pointer_quantity);
}

static void extract_flag_bit(unsigned int flags, unsigned int mask, int *dest)
{
  *dest = (flags & mask) != 0;
}

static void extract_flag_field(unsigned int flags, int shift, unsigned int mask, unsigned int *dest)
{
  *dest = (flags >> shift) & mask;
}

static void copy_32bit_fields(struct som_external_subspace_dictionary_record *src,
                              struct som_subspace_dictionary_record *dst)
{
  dst->space_index = bfd_getb32(src->space_index);
  dst->file_loc_init_value = bfd_getb32(src->file_loc_init_value);
  dst->initialization_length = bfd_getb32(src->initialization_length);
  dst->subspace_start = bfd_getb32(src->subspace_start);
  dst->subspace_length = bfd_getb32(src->subspace_length);
  dst->alignment = bfd_getb32(src->alignment);
  dst->name = bfd_getb32(src->name);
  dst->fixup_request_index = bfd_getb32(src->fixup_request_index);
  dst->fixup_request_quantity = bfd_getb32(src->fixup_request_quantity);
}

static void extract_flags(unsigned int flags, struct som_subspace_dictionary_record *dst)
{
  extract_flag_field(flags, SOM_SUBSPACE_ACCESS_CONTROL_BITS_SH, 
                    SOM_SUBSPACE_ACCESS_CONTROL_BITS_MASK, &dst->access_control_bits);
  extract_flag_bit(flags, SOM_SUBSPACE_MEMORY_RESIDENT, &dst->memory_resident);
  extract_flag_bit(flags, SOM_SUBSPACE_DUP_COMMON, &dst->dup_common);
  extract_flag_bit(flags, SOM_SUBSPACE_IS_COMMON, &dst->is_common);
  extract_flag_bit(flags, SOM_SUBSPACE_IS_LOADABLE, &dst->is_loadable);
  extract_flag_field(flags, SOM_SUBSPACE_QUADRANT_SH, 
                    SOM_SUBSPACE_QUADRANT_MASK, &dst->quadrant);
  extract_flag_bit(flags, SOM_SUBSPACE_INITIALLY_FROZEN, &dst->initially_frozen);
  extract_flag_bit(flags, SOM_SUBSPACE_IS_FIRST, &dst->is_first);
  extract_flag_bit(flags, SOM_SUBSPACE_CODE_ONLY, &dst->code_only);
  extract_flag_field(flags, SOM_SUBSPACE_SORT_KEY_SH, 
                    SOM_SUBSPACE_SORT_KEY_MASK, &dst->sort_key);
  extract_flag_bit(flags, SOM_SUBSPACE_REPLICATE_INIT, &dst->replicate_init);
  extract_flag_bit(flags, SOM_SUBSPACE_CONTINUATION, &dst->continuation);
  extract_flag_bit(flags, SOM_SUBSPACE_IS_TSPECIFIC, &dst->is_tspecific);
  extract_flag_bit(flags, SOM_SUBSPACE_IS_COMDAT, &dst->is_comdat);
  dst->reserved = 0;
}

static void
som_swap_subspace_dictionary_in
  (struct som_external_subspace_dictionary_record *src,
   struct som_subspace_dictionary_record *dst)
{
  unsigned int flags = bfd_getb32(src->flags);
  extract_flags(flags, dst);
  copy_32bit_fields(src, dst);
}

static unsigned int build_subspace_flags(struct som_subspace_dictionary_record *src)
{
    unsigned int flags = 0;
    
    flags = (src->access_control_bits & SOM_SUBSPACE_ACCESS_CONTROL_BITS_MASK)
            << SOM_SUBSPACE_ACCESS_CONTROL_BITS_SH;
    flags |= (src->quadrant & SOM_SUBSPACE_QUADRANT_MASK)
            << SOM_SUBSPACE_QUADRANT_SH;
    flags |= (src->sort_key & SOM_SUBSPACE_SORT_KEY_MASK)
            << SOM_SUBSPACE_SORT_KEY_SH;
    
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
    
    return flags;
}

static void copy_subspace_fields(struct som_subspace_dictionary_record *src,
                                 struct som_external_subspace_dictionary_record *dst)
{
    bfd_putb32(src->space_index, dst->space_index);
    bfd_putb32(src->file_loc_init_value, dst->file_loc_init_value);
    bfd_putb32(src->initialization_length, dst->initialization_length);
    bfd_putb32(src->subspace_start, dst->subspace_start);
    bfd_putb32(src->subspace_length, dst->subspace_length);
    bfd_putb32(src->alignment, dst->alignment);
    bfd_putb32(src->name, dst->name);
    bfd_putb32(src->fixup_request_index, dst->fixup_request_index);
    bfd_putb32(src->fixup_request_quantity, dst->fixup_request_quantity);
}

static void
som_swap_subspace_dictionary_record_out
  (struct som_subspace_dictionary_record *src,
   struct som_external_subspace_dictionary_record *dst)
{
    unsigned int flags = build_subspace_flags(src);
    bfd_putb32(flags, dst->flags);
    copy_subspace_fields(src, dst);
}

static void extract_aux_id_flags(unsigned int flags, struct som_aux_id *dst)
{
    dst->mandatory = (flags & SOM_AUX_ID_MANDATORY) != 0;
    dst->copy = (flags & SOM_AUX_ID_COPY) != 0;
    dst->append = (flags & SOM_AUX_ID_APPEND) != 0;
    dst->ignore = (flags & SOM_AUX_ID_IGNORE) != 0;
    dst->type = (flags >> SOM_AUX_ID_TYPE_SH) & SOM_AUX_ID_TYPE_MASK;
}

static void som_swap_aux_id_in(struct som_external_aux_id *src, struct som_aux_id *dst)
{
    unsigned int flags = bfd_getb32(src->flags);
    extract_aux_id_flags(flags, dst);
    dst->length = bfd_getb32(src->length);
}

static void
som_swap_aux_id_out (struct som_aux_id *src,
                    struct som_external_aux_id *dst)
{
  unsigned int flags = 0;

  if (src->mandatory)
    flags |= SOM_AUX_ID_MANDATORY;
  if (src->copy)
    flags |= SOM_AUX_ID_COPY;
  if (src->append)
    flags |= SOM_AUX_ID_APPEND;
  if (src->ignore)
    flags |= SOM_AUX_ID_IGNORE;
  flags |= (src->type & SOM_AUX_ID_TYPE_MASK) << SOM_AUX_ID_TYPE_SH;
  bfd_putb32 (flags, dst->flags);
  bfd_putb32 (src->length, dst->length);
}

static void
som_swap_string_auxhdr_out (struct som_string_auxhdr *src,
			    struct som_external_string_auxhdr *dst)
{
  som_swap_aux_id_out (&src->header_id, &dst->header_id);
  bfd_putb32 (src->string_length, dst->string_length);
}

static void
som_swap_compilation_unit_out (struct som_compilation_unit *src,
                              struct som_external_compilation_unit *dst)
{
  bfd_putb32 (src->name.strx, dst->name);
  bfd_putb32 (src->language_name.strx, dst->language_name);
  bfd_putb32 (src->product_id.strx, dst->product_id);
  bfd_putb32 (src->version_id.strx, dst->version_id);
  bfd_putb32 (src->flags, dst->flags);
  som_swap_clock_out (&src->compile_time, &dst->compile_time);
  som_swap_clock_out (&src->source_time, &dst->source_time);
}

static void
som_swap_exec_auxhdr_in (struct som_external_exec_auxhdr *src,
			 struct som_exec_auxhdr *dst)
{
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
}

static void
som_swap_exec_auxhdr_out (struct som_exec_auxhdr *src,
			 struct som_external_exec_auxhdr *dst)
{
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

static void
set_bfd_flags_from_magic(bfd *abfd, unsigned int magic)
{
  switch (magic)
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
}

static int
is_entry_in_code_section(bfd *abfd, struct som_exec_auxhdr *aux_hdrp)
{
  asection *section;
  bfd_vma entry = aux_hdrp->exec_entry + aux_hdrp->exec_tmem;

  for (section = abfd->sections; section; section = section->next)
    {
      if ((section->flags & SEC_CODE) == 0)
        continue;
      if (entry >= section->vma && entry < section->vma + section->size)
        return 1;
    }
  return 0;
}

#define ENTRY_ALIGNMENT_MASK 0x3

static int
is_buggy_linker_entry(bfd *abfd, struct som_exec_auxhdr *aux_hdrp)
{
  if (aux_hdrp->exec_entry == 0 && !(abfd->flags & DYNAMIC))
    return 1;
  if ((aux_hdrp->exec_entry & ENTRY_ALIGNMENT_MASK) != 0)
    return 1;
  if (!is_entry_in_code_section(abfd, aux_hdrp))
    return 1;
  return 0;
}

static void
set_start_address_and_flags(bfd *abfd, struct som_exec_auxhdr *aux_hdrp,
                            unsigned long current_offset)
{
  if (is_buggy_linker_entry(abfd, aux_hdrp))
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

static void
initialize_som_tables(bfd *abfd)
{
  obj_som_stringtab (abfd) = NULL;
  obj_som_symtab (abfd) = NULL;
  obj_som_sorted_syms (abfd) = NULL;
}

static void
save_file_offsets(bfd *abfd, struct som_header *file_hdrp,
                 unsigned long current_offset)
{
  obj_som_stringtab_size (abfd) = file_hdrp->symbol_strings_size;
  obj_som_sym_filepos (abfd) = file_hdrp->symbol_location + current_offset;
  obj_som_str_filepos (abfd) = file_hdrp->symbol_strings_location + current_offset;
  obj_som_reloc_filepos (abfd) = file_hdrp->fixup_request_location + current_offset;
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

  set_bfd_flags_from_magic(abfd, file_hdrp->a_magic);

  obj_som_exec_hdr (abfd) = aux_hdrp;

  obj_som_exec_data (abfd) = bfd_zalloc (abfd, (bfd_size_type) sizeof (struct som_exec_data));
  if (obj_som_exec_data (abfd) == NULL)
    return NULL;

  if (aux_hdrp)
    set_start_address_and_flags(abfd, aux_hdrp, current_offset);

  obj_som_exec_data (abfd)->version_id = file_hdrp->version_id;

  bfd_default_set_arch_mach (abfd, bfd_arch_hppa, pa10);
  abfd->symcount = file_hdrp->symbol_total;

  initialize_som_tables(abfd);
  save_file_offsets(abfd, file_hdrp, current_offset);
  obj_som_exec_data (abfd)->system_id = file_hdrp->system_id;

  return _bfd_no_cleanup;
}

/* Convert all of the space and subspace info into BFD sections.  Each space
   contains a number of subspaces, which in turn describe the mapping between
   regions of the exec file, and the address space that the program runs in.
   BFD sections which correspond to spaces will overlap the sections for the
   associated subspaces.  */

static bool
read_space_strings(bfd *abfd, struct som_header *file_hdr, unsigned long current_offset, char **space_strings)
{
  size_t amt = file_hdr->space_strings_size;
  if (amt == (size_t) -1)
    {
      bfd_set_error (bfd_error_no_memory);
      return false;
    }
  if (bfd_seek (abfd, current_offset + file_hdr->space_strings_location, SEEK_SET) != 0)
    return false;
  *space_strings = (char *) _bfd_malloc_and_read (abfd, amt + 1, amt);
  if (*space_strings == NULL)
    return false;
  (*space_strings)[amt] = 0;
  return true;
}

static bool
read_space_dictionary(bfd *abfd, unsigned long current_offset, struct som_header *file_hdr, 
                      unsigned int space_index, struct som_space_dictionary_record *space)
{
  struct som_external_space_dictionary_record ext_space;
  if (bfd_seek (abfd, current_offset + file_hdr->space_location + 
                space_index * sizeof (ext_space), SEEK_SET) != 0)
    return false;
  size_t amt = sizeof ext_space;
  if (bfd_read (&ext_space, amt, abfd) != amt)
    return false;
  som_swap_space_dictionary_in (&ext_space, space);
  return true;
}

static asection *
create_space_section(bfd *abfd, char *space_name, struct som_space_dictionary_record *space)
{
  size_t amt = strlen (space_name) + 1;
  char *newname = bfd_alloc (abfd, amt);
  if (!newname)
    return NULL;
  strcpy (newname, space_name);
  
  asection *space_asect = bfd_make_section_anyway (abfd, newname);
  if (!space_asect)
    return NULL;
  
  if (space->is_loadable == 0)
    space_asect->flags |= SEC_DEBUGGING;
  
  if (!bfd_som_set_section_attributes (space_asect, space->is_defined,
                                       space->is_private, space->sort_key,
                                       space->space_number))
    return NULL;
  
  return space_asect;
}

static bool
read_first_subspace(bfd *abfd, unsigned long current_offset, struct som_header *file_hdr,
                   struct som_space_dictionary_record *space, 
                   struct som_subspace_dictionary_record *subspace)
{
  struct som_external_subspace_dictionary_record ext_subspace;
  if (bfd_seek (abfd, current_offset + file_hdr->subspace_location + 
                space->subspace_index * sizeof ext_subspace, SEEK_SET) != 0)
    return false;
  size_t amt = sizeof ext_subspace;
  if (bfd_read (&ext_subspace, amt, abfd) != amt)
    return false;
  if (bfd_seek (abfd, current_offset + file_hdr->subspace_location + 
                space->subspace_index * sizeof ext_subspace, SEEK_SET) != 0)
    return false;
  som_swap_subspace_dictionary_in (&ext_subspace, subspace);
  return true;
}

static void
init_space_section_from_subspace(asection *space_asect, 
                                 struct som_subspace_dictionary_record *subspace,
                                 unsigned long current_offset)
{
  space_asect->vma = subspace->subspace_start;
  space_asect->filepos = subspace->file_loc_init_value + current_offset;
  space_asect->alignment_power = exact_log2 (subspace->alignment);
}

static void
set_subspace_flags(asection *subspace_asect, struct som_subspace_dictionary_record *subspace)
{
  switch (subspace->access_control_bits >> 4)
    {
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
  
  if (subspace->fixup_request_quantity != 0)
    {
      subspace_asect->flags |= SEC_RELOC;
      subspace_asect->rel_filepos = subspace->fixup_request_index;
      som_section_data (subspace_asect)->reloc_size = subspace->fixup_request_quantity;
      subspace_asect->reloc_count = (unsigned) -1;
    }
}

static asection *
create_subspace_section(bfd *abfd, char *subspace_name, asection *space_asect,
                       struct som_subspace_dictionary_record *subspace,
                       unsigned long current_offset)
{
  size_t amt = strlen (subspace_name) + 1;
  char *newname = bfd_alloc (abfd, amt);
  if (!newname)
    return NULL;
  strcpy (newname, subspace_name);
  
  asection *subspace_asect = bfd_make_section_anyway (abfd, newname);
  if (!subspace_asect)
    return NULL;
  
  if (!bfd_som_set_subsection_attributes (subspace_asect, space_asect,
                                          subspace->access_control_bits,
                                          subspace->sort_key,
                                          subspace->quadrant,
                                          subspace->is_comdat,
                                          subspace->is_common,
                                          subspace->dup_common))
    return NULL;
  
  set_subspace_flags(subspace_asect, subspace);
  
  subspace_asect->vma = subspace->subspace_start;
  subspace_asect->size = subspace->subspace_length;
  subspace_asect->filepos = subspace->file_loc_init_value + current_offset;
  subspace_asect->alignment_power = exact_log2 (subspace->alignment);
  
  return subspace_asect;
}

static bool
process_subspaces(bfd *abfd, struct som_header *file_hdr, unsigned long current_offset,
                 struct som_space_dictionary_record *space, asection *space_asect,
                 char *space_strings, unsigned int *total_subspaces)
{
  struct som_external_subspace_dictionary_record ext_subspace;
  struct som_subspace_dictionary_record subspace, save_subspace;
  bfd_size_type space_size = 0;
  
  memset (&save_subspace, 0, sizeof (save_subspace));
  
  for (unsigned int subspace_index = 0; subspace_index < space->subspace_quantity; subspace_index++)
    {
      size_t amt = sizeof ext_subspace;
      if (bfd_read (&ext_subspace, amt, abfd) != amt)
        return false;
      
      som_swap_subspace_dictionary_in (&ext_subspace, &subspace);
      
      if (subspace.name >= file_hdr->space_strings_size)
        return false;
      
      char *subspace_name = subspace.name + space_strings;
      
      asection *subspace_asect = create_subspace_section(abfd, subspace_name, space_asect,
                                                        &subspace, current_offset);
      if (!subspace_asect)
        return false;
      
      (*total_subspaces)++;
      subspace_asect->target_index = bfd_tell (abfd) - sizeof (subspace);
      
      if (subspace_asect->alignment_power == (unsigned) -1)
        return false;
      
      if (subspace.file_loc_init_value > save_subspace.file_loc_init_value)
        save_subspace = subspace;
      
      space_size += subspace.subspace_length;
    }
  
  if (!save_subspace.file_loc_init_value)
    space_asect->size = 0;
  else if (file_hdr->a_magic != RELOC_MAGIC)
    space_asect->size = save_subspace.subspace_start - space_asect->vma + save_subspace.subspace_length;
  else
    space_asect->size = space_size;
  
  return true;
}

static bool
assign_subspace_indices(bfd *abfd, unsigned int total_subspaces)
{
  size_t amt;
  if (_bfd_mul_overflow (total_subspaces, sizeof (asection *), &amt))
    {
      bfd_set_error (bfd_error_file_too_big);
      return false;
    }
  
  asection **subspace_sections = bfd_malloc (amt);
  if (subspace_sections == NULL)
    return false;
  
  unsigned int i = 0;
  for (asection *section = abfd->sections; section; section = section->next)
    {
      if (!som_is_subspace (section))
        continue;
      subspace_sections[i] = section;
      i++;
    }
  
  qsort (subspace_sections, total_subspaces, sizeof (asection *), compare_subspaces);
  
  for (i = 0; i < total_subspaces; i++)
    subspace_sections[i]->target_index = i;
  
  free (subspace_sections);
  return true;
}

static bool
setup_sections (bfd *abfd, struct som_header *file_hdr, unsigned long current_offset)
{
  char *space_strings = NULL;
  unsigned int total_subspaces = 0;
  
  if (!read_space_strings(abfd, file_hdr, current_offset, &space_strings))
    goto error_return;
  
  for (unsigned int space_index = 0; space_index < file_hdr->space_total; space_index++)
    {
      struct som_space_dictionary_record space;
      struct som_subspace_dictionary_record subspace;
      
      if (!read_space_dictionary(abfd, current_offset, file_hdr, space_index, &space))
        goto error_return;
      
      if (space.name >= file_hdr->space_strings_size)
        goto error_return;
      
      char *space_name = space.name + space_strings;
      asection *space_asect = create_space_section(abfd, space_name, &space);
      if (!space_asect)
        goto error_return;
      
      if (space.subspace_quantity == 0)
        continue;
      
      if (!read_first_subspace(abfd, current_offset, file_hdr, &space, &subspace))
        goto error_return;
      
      init_space_section_from_subspace(space_asect, &subspace, current_offset);
      if (space_asect->alignment_power == (unsigned) -1)
        goto error_return;
      
      if (!process_subspaces(abfd, file_hdr, current_offset, &space, space_asect,
                            space_strings, &total_subspaces))
        goto error_return;
    }
  
  if (!assign_subspace_indices(abfd, total_subspaces))
    goto error_return;
  
  free (space_strings);
  return true;
  
 error_return:
  free (space_strings);
  return false;
}


/* Read in a SOM object and make it into a BFD.  */

#define ENTRY_SIZE sizeof(struct som_external_som_entry)

static bool
is_valid_magic(unsigned int magic)
{
    switch (magic) {
    case RELOC_MAGIC:
    case EXEC_MAGIC:
    case SHARE_MAGIC:
    case DEMAND_MAGIC:
    case DL_MAGIC:
    case SHL_MAGIC:
#ifdef SHARED_MAGIC_CNX
    case SHARED_MAGIC_CNX:
#endif
        return true;
    default:
        return false;
    }
}

static bool
is_valid_version(unsigned int version_id)
{
    return version_id == OLD_VERSION_ID || version_id == NEW_VERSION_ID;
}

static void
set_format_error_if_needed(void)
{
    if (bfd_get_error() != bfd_error_system_call)
        bfd_set_error(bfd_error_wrong_format);
}

static bool
read_data(bfd *abfd, void *buffer, size_t size)
{
    if (bfd_read(buffer, size, abfd) != size) {
        set_format_error_if_needed();
        return false;
    }
    return true;
}

static bool
seek_to_position(bfd *abfd, file_ptr position)
{
    if (bfd_seek(abfd, position, SEEK_SET) != 0) {
        set_format_error_if_needed();
        return false;
    }
    return true;
}

static bool
read_header(bfd *abfd, struct som_external_header *ext_hdr, struct som_header *hdr)
{
    if (!read_data(abfd, ext_hdr, sizeof(struct som_external_header)))
        return false;
    som_swap_header_in(ext_hdr, hdr);
    return true;
}

static bool
process_execlibmagic(bfd *abfd, struct som_external_header *ext_file_hdr,
                    struct som_header *file_hdr, unsigned long *current_offset)
{
    struct som_external_lst_header ext_lst_header;
    struct som_external_som_entry ext_som_entry;
    unsigned int loc;
    
    if (!seek_to_position(abfd, 0))
        return false;
        
    if (!read_data(abfd, &ext_lst_header, sizeof(struct som_external_lst_header)))
        return false;
        
    loc = bfd_getb32(ext_lst_header.dir_loc);
    if (!seek_to_position(abfd, loc))
        return false;
        
    if (!read_data(abfd, &ext_som_entry, ENTRY_SIZE))
        return false;
        
    *current_offset = bfd_getb32(ext_som_entry.location);
    if (!seek_to_position(abfd, *current_offset))
        return false;
        
    return read_header(abfd, ext_file_hdr, file_hdr);
}

static struct som_exec_auxhdr *
read_aux_header(bfd *abfd, struct som_header *file_hdr)
{
    struct som_external_exec_auxhdr ext_exec_auxhdr;
    struct som_exec_auxhdr *aux_hdr_ptr;
    
    if (file_hdr->aux_header_size == 0)
        return NULL;
        
    aux_hdr_ptr = bfd_zalloc(abfd, (bfd_size_type)sizeof(*aux_hdr_ptr));
    if (aux_hdr_ptr == NULL)
        return NULL;
        
    if (!read_data(abfd, &ext_exec_auxhdr, sizeof(struct som_external_exec_auxhdr)))
        return NULL;
        
    som_swap_exec_auxhdr_in(&ext_exec_auxhdr, aux_hdr_ptr);
    return aux_hdr_ptr;
}

static bfd_cleanup
som_object_p(bfd *abfd)
{
    struct som_external_header ext_file_hdr;
    struct som_header file_hdr;
    struct som_exec_auxhdr *aux_hdr_ptr = NULL;
    unsigned long current_offset = 0;
    
    if (!read_header(abfd, &ext_file_hdr, &file_hdr))
        return NULL;
        
    if (!_PA_RISC_ID(file_hdr.system_id)) {
        bfd_set_error(bfd_error_wrong_format);
        return NULL;
    }
    
    if (file_hdr.a_magic == EXECLIBMAGIC) {
        if (!process_execlibmagic(abfd, &ext_file_hdr, &file_hdr, &current_offset))
            return NULL;
    } else if (!is_valid_magic(file_hdr.a_magic)) {
        bfd_set_error(bfd_error_wrong_format);
        return NULL;
    }
    
    if (!is_valid_version(file_hdr.version_id)) {
        bfd_set_error(bfd_error_wrong_format);
        return NULL;
    }
    
    aux_hdr_ptr = read_aux_header(abfd, &file_hdr);
    
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

static bool
allocate_file_header(bfd *abfd)
{
  size_t amt = sizeof(struct som_header);
  struct som_header *file_hdr = bfd_zalloc(abfd, amt);
  if (file_hdr == NULL)
    return false;
  obj_som_file_hdr(abfd) = file_hdr;
  return true;
}

static bool
allocate_exec_header(bfd *abfd)
{
  size_t amt = sizeof(struct som_exec_auxhdr);
  obj_som_exec_hdr(abfd) = bfd_zalloc(abfd, amt);
  return obj_som_exec_hdr(abfd) != NULL;
}

static void
set_file_magic(struct som_header *file_hdr, int flags)
{
  if (flags & D_PAGED)
    file_hdr->a_magic = DEMAND_MAGIC;
  else if (flags & WP_TEXT)
    file_hdr->a_magic = SHARE_MAGIC;
#ifdef SHL_MAGIC
  else if (flags & DYNAMIC)
    file_hdr->a_magic = SHL_MAGIC;
#endif
  else
    file_hdr->a_magic = EXEC_MAGIC;
}

static void
initialize_file_header_fields(struct som_header *file_hdr)
{
  file_hdr->file_time.secs = 0;
  file_hdr->file_time.nanosecs = 0;
  file_hdr->entry_space = 0;
  file_hdr->entry_subspace = 0;
  file_hdr->entry_offset = 0;
  file_hdr->presumed_dp = 0;
}

static bool
allocate_space_dictionary(bfd *abfd, asection *section)
{
  size_t amt = sizeof(struct som_space_dictionary_record);
  som_section_data(section)->space_dict = bfd_zalloc(abfd, amt);
  return som_section_data(section)->space_dict != NULL;
}

static void
set_space_attributes(asection *section)
{
  struct som_space_dictionary_record *space_dict = som_section_data(section)->space_dict;
  struct som_copyable_section_data_struct *copy_data = som_section_data(section)->copy_data;
  
  space_dict->loader_fix_index = -1;
  space_dict->init_pointer_index = -1;
  space_dict->sort_key = copy_data->sort_key;
  space_dict->is_defined = copy_data->is_defined;
  space_dict->is_private = copy_data->is_private;
  space_dict->space_number = copy_data->space_number;
}

static bool
allocate_subspace_dictionary(bfd *abfd, asection *section)
{
  size_t amt = sizeof(struct som_subspace_dictionary_record);
  som_section_data(section)->subspace_dict = bfd_zalloc(abfd, amt);
  return som_section_data(section)->subspace_dict != NULL;
}

static void
set_subspace_basic_attributes(asection *section)
{
  struct som_subspace_dictionary_record *subspace_dict = som_section_data(section)->subspace_dict;
  
  if (section->flags & SEC_ALLOC)
    subspace_dict->is_loadable = 1;
  
  if (section->flags & SEC_CODE)
    subspace_dict->code_only = 1;
  
  subspace_dict->subspace_start = section->vma;
  subspace_dict->subspace_length = section->size;
  subspace_dict->initialization_length = section->size;
  subspace_dict->alignment = 1 << section->alignment_power;
}

static void
set_subspace_private_attributes(asection *section)
{
  struct som_subspace_dictionary_record *subspace_dict = som_section_data(section)->subspace_dict;
  struct som_copyable_section_data_struct *copy_data = som_section_data(section)->copy_data;
  
  subspace_dict->sort_key = copy_data->sort_key;
  subspace_dict->access_control_bits = copy_data->access_control_bits;
  subspace_dict->quadrant = copy_data->quadrant;
  subspace_dict->is_comdat = copy_data->is_comdat;
  subspace_dict->is_common = copy_data->is_common;
  subspace_dict->dup_common = copy_data->dup_common;
}

static bool
process_space_section(bfd *abfd, asection *section)
{
  if (!allocate_space_dictionary(abfd, section))
    return false;
  set_space_attributes(section);
  return true;
}

static bool
process_subspace_section(bfd *abfd, asection *section)
{
  if (!allocate_subspace_dictionary(abfd, section))
    return false;
  set_subspace_basic_attributes(section);
  set_subspace_private_attributes(section);
  return true;
}

static bool
process_sections(bfd *abfd)
{
  asection *section;
  
  for (section = abfd->sections; section != NULL; section = section->next)
    {
      if (!som_is_space(section) && !som_is_subspace(section))
        continue;
      
      if (som_is_space(section))
        {
          if (!process_space_section(abfd, section))
            return false;
        }
      else
        {
          if (!process_subspace_section(abfd, section))
            return false;
        }
    }
  return true;
}

static bool
som_prep_headers(bfd *abfd)
{
  struct som_header *file_hdr;
  
  if (!allocate_file_header(abfd))
    return false;
  
  file_hdr = obj_som_file_hdr(abfd);
  
  if (abfd->flags & (EXEC_P | DYNAMIC))
    {
      if (!allocate_exec_header(abfd))
        return false;
      set_file_magic(file_hdr, abfd->flags);
    }
  else
    {
      file_hdr->a_magic = RELOC_MAGIC;
    }
  
  initialize_file_header_fields(file_hdr);
  
  return process_sections(abfd);
}

/* Return TRUE if the given section is a SOM space, FALSE otherwise.  */

static bool
som_is_space (asection *section)
{
  struct som_copyable_section_data_struct *copy_data;
  asection *container;
  
  copy_data = som_section_data (section)->copy_data;
  if (copy_data == NULL)
    return false;

  container = copy_data->container;
  if (container != section && container->output_section != section)
    return false;

  return true;
}

/* Return TRUE if the given section is a SOM subspace, FALSE otherwise.  */

static bool
som_is_subspace (asection *section)
{
  struct som_copyable_section_data_struct *copy_data;
  asection *container;
  
  copy_data = som_section_data (section)->copy_data;
  if (copy_data == NULL)
    return false;

  container = copy_data->container;
  if (container == section || container->output_section == section)
    return false;

  return true;
}

/* Return TRUE if the given space contains the given subspace.  It
   is safe to assume space really is a space, and subspace really
   is a subspace.  */

static bool
som_is_container (asection *space, asection *subspace)
{
  asection *container = som_section_data (subspace)->copy_data->container;
  return (container == space) || (container->output_section == space);
}

/* Count and return the number of spaces attached to the given BFD.  */

static unsigned long
som_count_spaces (bfd *abfd)
{
  unsigned long count = 0;
  asection *section;

  for (section = abfd->sections; section != NULL; section = section->next)
    count += som_is_space (section);

  return count;
}

/* Count the number of subspaces attached to the given BFD.  */

static unsigned long
som_count_subspaces (bfd *abfd)
{
  int count = 0;
  asection *section;

  for (section = abfd->sections; section != NULL; section = section->next)
    count += som_is_subspace (section);

  return count;
}

/* Return -1, 0, 1 indicating the relative ordering of sym1 and sym2.

   We desire symbols to be ordered starting with the symbol with the
   highest relocation count down to the symbol with the lowest relocation
   count.  Doing so compacts the relocation stream.  */

static unsigned int get_relocation_count(asymbol *sym)
{
  if (sym->flags & BSF_SECTION_SYM)
    return sym->udata.i;
  return som_symbol_data(sym)->reloc_count;
}

static int
compare_syms (const void *arg1, const void *arg2)
{
  asymbol **sym1 = (asymbol **) arg1;
  asymbol **sym2 = (asymbol **) arg2;
  unsigned int count1 = get_relocation_count(*sym1);
  unsigned int count2 = get_relocation_count(*sym2);

  if (count1 < count2)
    return 1;
  if (count1 > count2)
    return -1;
  return 0;
}

/* Return -1, 0, 1 indicating the relative ordering of subspace1
   and subspace.  */

static int
compare_subspaces (const void *arg1, const void *arg2)
{
  asection **subspace1 = (asection **) arg1;
  asection **subspace2 = (asection **) arg2;

  if ((*subspace1)->target_index < (*subspace2)->target_index)
    return -1;
  if ((*subspace1)->target_index > (*subspace2)->target_index)
    return 1;
  return 0;
}

/* Perform various work in preparation for emitting the fixup stream.  */

static bool
som_prep_for_fixups (bfd *abfd, asymbol **syms, unsigned long num_syms)
{
  unsigned long i;
  asection *section;
  asymbol **sorted_syms;
  size_t amt;

  if (num_syms == 0)
    return true;

  initialize_symbol_counters(syms, num_syms);
  count_symbol_relocations(abfd, syms);

  if (_bfd_mul_overflow (num_syms, sizeof (asymbol *), &amt))
    {
      bfd_set_error (bfd_error_no_memory);
      return false;
    }
  sorted_syms = bfd_zalloc (abfd, amt);
  if (sorted_syms == NULL)
    return false;
  memcpy (sorted_syms, syms, num_syms * sizeof (asymbol *));
  qsort (sorted_syms, num_syms, sizeof (asymbol *), compare_syms);
  obj_som_sorted_syms (abfd) = sorted_syms;

  assign_symbol_indexes(sorted_syms, num_syms);
  return true;
}

static void
initialize_symbol_counters(asymbol **syms, unsigned long num_syms)
{
  unsigned long i;
  for (i = 0; i < num_syms; i++)
    {
      if (is_section_symbol(syms[i]))
        {
          syms[i]->flags |= BSF_SECTION_SYM;
          syms[i]->udata.i = 0;
        }
      else
        som_symbol_data (syms[i])->reloc_count = 0;
    }
}

static bool
is_section_symbol(asymbol *sym)
{
  return som_symbol_data(sym) == NULL || (sym->flags & BSF_SECTION_SYM);
}

static void
count_symbol_relocations(bfd *abfd, asymbol **syms)
{
  asection *section;
  for (section = abfd->sections; section != NULL; section = section->next)
    {
      if ((int) section->reloc_count <= 0)
        continue;
      process_section_relocations(section);
    }
}

static void
process_section_relocations(asection *section)
{
  int j;
  for (j = 1; j < (int) section->reloc_count; j++)
    {
      arelent *reloc = section->orelocation[j];
      if (should_skip_relocation(reloc))
        continue;
      update_relocation_count(reloc);
    }
}

static bool
should_skip_relocation(arelent *reloc)
{
  return reloc->sym_ptr_ptr == NULL ||
         bfd_is_abs_section((*reloc->sym_ptr_ptr)->section);
}

static void
update_relocation_count(arelent *reloc)
{
  int scale = get_relocation_scale(reloc);
  asymbol *sym = *reloc->sym_ptr_ptr;
  
  if (sym->flags & BSF_SECTION_SYM)
    sym->udata.i = sym->udata.i + scale;
  else
    som_symbol_data(sym)->reloc_count += scale;
}

#define HIGH_PRIORITY_SCALE 2
#define NORMAL_SCALE 1

static int
get_relocation_scale(arelent *reloc)
{
  if (reloc->howto->type == R_DP_RELATIVE ||
      reloc->howto->type == R_CODE_ONE_SYMBOL)
    return HIGH_PRIORITY_SCALE;
  return NORMAL_SCALE;
}

static void
assign_symbol_indexes(asymbol **sorted_syms, unsigned long num_syms)
{
  unsigned long i;
  for (i = 0; i < num_syms; i++)
    {
      if (sorted_syms[i]->flags & BSF_SECTION_SYM)
        sorted_syms[i]->udata.i = i;
      else
        som_symbol_data(sorted_syms[i])->index = i;
    }
}

#define SOM_TMP_BUFSIZE_THRESHOLD 512
#define SYM_NUM_SMALL_THRESHOLD 0x20
#define SYM_NUM_MEDIUM_THRESHOLD 0x100
#define SYM_NUM_LARGE_THRESHOLD 0x10000000
#define END_TRY_SMALL_THRESHOLD 1024
#define RELOCATION_SIZE_4 4
#define COMP2_CONSTANT 0x80
#define COMP1_CONSTANT 0x44
#define RESERVED_RELOC 0xff

static bool
validate_relocation(bfd *abfd, asection *subsection, arelent *bfd_reloc)
{
    static unsigned int reloc_offset = 0;
    
    if (bfd_reloc->address < reloc_offset)
    {
        _bfd_error_handler
            (_("%pB(%pA+%#" PRIx64 "): "
               "%s relocation offset out of order"),
             abfd, subsection, (uint64_t) bfd_reloc->address,
             bfd_reloc->howto->name);
        bfd_set_error(bfd_error_bad_value);
        return false;
    }
    
    if (!bfd_reloc_offset_in_range(bfd_reloc->howto,
                                   abfd, subsection,
                                   bfd_reloc->address))
    {
        _bfd_error_handler
            (_("%pB(%pA+%#" PRIx64 "): "
               "%s relocation offset out of range"),
             abfd, subsection, (uint64_t) bfd_reloc->address,
             bfd_reloc->howto->name);
        bfd_set_error(bfd_error_bad_value);
        return false;
    }
    
    reloc_offset = bfd_reloc->address + bfd_reloc->howto->size;
    return true;
}

static int
get_symbol_number(arelent *bfd_reloc)
{
    if ((*bfd_reloc->sym_ptr_ptr)->flags & BSF_SECTION_SYM)
        return (*bfd_reloc->sym_ptr_ptr)->udata.i;
    return som_symbol_data(*bfd_reloc->sym_ptr_ptr)->index;
}

static unsigned char *
flush_buffer_if_needed(bfd *abfd, unsigned char *p, unsigned char *tmp_space,
                       void *reloc_queue)
{
    if (p - tmp_space + SOM_TMP_BUFSIZE_THRESHOLD > SOM_TMP_BUFSIZE)
    {
        size_t amt = p - tmp_space;
        if (bfd_write(tmp_space, amt, abfd) != amt)
            return NULL;
        som_initialize_reloc_queue(reloc_queue);
        return tmp_space;
    }
    return p;
}

static unsigned char *
write_symbol_reloc_small(bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                         int howto_type, int sym_num)
{
    bfd_put_8(abfd, howto_type + sym_num, p);
    (*subspace_reloc_size)++;
    return p + 1;
}

static unsigned char *
write_symbol_reloc_medium(bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                          int howto_type, int sym_num, void *reloc_queue)
{
    bfd_put_8(abfd, howto_type + 32, p);
    bfd_put_8(abfd, sym_num, p + 1);
    return try_prev_fixup(abfd, subspace_reloc_size, p, 2, reloc_queue);
}

static unsigned char *
write_symbol_reloc_large(bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                         int howto_type, int sym_num, void *reloc_queue)
{
    bfd_put_8(abfd, howto_type + 33, p);
    bfd_put_8(abfd, sym_num >> 16, p + 1);
    bfd_put_16(abfd, (bfd_vma) sym_num, p + 2);
    return try_prev_fixup(abfd, subspace_reloc_size, p, RELOCATION_SIZE_4, reloc_queue);
}

static unsigned char *
process_code_or_dp_reloc(bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                         arelent *bfd_reloc, int sym_num, void *reloc_queue)
{
    if (bfd_reloc->addend)
        p = som_reloc_addend(abfd, bfd_reloc->addend, p, subspace_reloc_size, reloc_queue);
    
    if (sym_num < SYM_NUM_SMALL_THRESHOLD)
        return write_symbol_reloc_small(abfd, p, subspace_reloc_size, bfd_reloc->howto->type, sym_num);
    else if (sym_num < SYM_NUM_MEDIUM_THRESHOLD)
        return write_symbol_reloc_medium(abfd, p, subspace_reloc_size, bfd_reloc->howto->type, sym_num, reloc_queue);
    else if (sym_num < SYM_NUM_LARGE_THRESHOLD)
        return write_symbol_reloc_large(abfd, p, subspace_reloc_size, bfd_reloc->howto->type, sym_num, reloc_queue);
    else
        abort();
}

static unsigned char *
process_data_gprel(bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                  arelent *bfd_reloc, int sym_num, void *reloc_queue)
{
    if (bfd_reloc->addend)
        p = som_reloc_addend(abfd, bfd_reloc->addend, p, subspace_reloc_size, reloc_queue);
    
    if (sym_num < SYM_NUM_LARGE_THRESHOLD)
    {
        bfd_put_8(abfd, bfd_reloc->howto->type, p);
        bfd_put_8(abfd, sym_num >> 16, p + 1);
        bfd_put_16(abfd, (bfd_vma) sym_num, p + 2);
        return try_prev_fixup(abfd, subspace_reloc_size, p, RELOCATION_SIZE_4, reloc_queue);
    }
    else
        abort();
}

static unsigned char *
process_data_symbol_reloc(bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                         arelent *bfd_reloc, int sym_num, void *reloc_queue)
{
    if (bfd_reloc->howto->type != R_DATA_ONE_SYMBOL && bfd_reloc->addend)
        p = som_reloc_addend(abfd, bfd_reloc->addend, p, subspace_reloc_size, reloc_queue);
    
    if (sym_num < SYM_NUM_MEDIUM_THRESHOLD)
    {
        bfd_put_8(abfd, bfd_reloc->howto->type, p);
        bfd_put_8(abfd, sym_num, p + 1);
        return try_prev_fixup(abfd, subspace_reloc_size, p, 2, reloc_queue);
    }
    else if (sym_num < SYM_NUM_LARGE_THRESHOLD)
    {
        bfd_put_8(abfd, bfd_reloc->howto->type + 1, p);
        bfd_put_8(abfd, sym_num >> 16, p + 1);
        bfd_put_16(abfd, (bfd_vma) sym_num, p + 2);
        return try_prev_fixup(abfd, subspace_reloc_size, p, RELOCATION_SIZE_4, reloc_queue);
    }
    else
        abort();
}

static arelent *
find_next_exit_reloc(asection *subsection, unsigned int start_idx)
{
    unsigned int tmp;
    for (tmp = start_idx; tmp < subsection->reloc_count; tmp++)
    {
        arelent *tmp_reloc = subsection->orelocation[tmp];
        if (tmp_reloc->howto->type == R_EXIT)
            return tmp_reloc;
    }
    abort();
}

static unsigned char *
process_entry_reloc(bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                   arelent *bfd_reloc, asection *subsection, unsigned int j, void *reloc_queue)
{
    bfd_put_8(abfd, R_ENTRY, p);
    bfd_put_32(abfd, bfd_reloc->addend, p + 1);
    
    arelent *exit_reloc = find_next_exit_reloc(subsection, j);
    bfd_put_32(abfd, exit_reloc->addend, p + 5);
    
    return try_prev_fixup(abfd, subspace_reloc_size, p, 9, reloc_queue);
}

static unsigned char *
process_mode_reloc(bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                  arelent *bfd_reloc, unsigned int *current_mode)
{
    if (bfd_reloc->howto->type != *current_mode)
    {
        bfd_put_8(abfd, bfd_reloc->howto->type, p);
        (*subspace_reloc_size)++;
        *current_mode = bfd_reloc->howto->type;
        return p + 1;
    }
    return p;
}

static unsigned char *
process_simple_reloc(bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                     arelent *bfd_reloc)
{
    bfd_put_8(abfd, bfd_reloc->howto->type, p);
    (*subspace_reloc_size)++;
    return p + 1;
}

static unsigned char *
process_end_try_reloc(bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                     arelent *bfd_reloc, void *reloc_queue)
{
    if (bfd_reloc->addend == 0)
    {
        bfd_put_8(abfd, bfd_reloc->howto->type, p);
        return p + 1;
    }
    else if (bfd_reloc->addend < END_TRY_SMALL_THRESHOLD)
    {
        bfd_put_8(abfd, bfd_reloc->howto->type + 1, p);
        bfd_put_8(abfd, bfd_reloc->addend / RELOCATION_SIZE_4, p + 1);
        return try_prev_fixup(abfd, subspace_reloc_size, p, 2, reloc_queue);
    }
    else
    {
        bfd_put_8(abfd, bfd_reloc->howto->type + 2, p);
        bfd_put_8(abfd, (bfd_reloc->addend / RELOCATION_SIZE_4) >> 16, p + 1);
        bfd_put_16(abfd, bfd_reloc->addend / RELOCATION_SIZE_4, p + 2);
        return try_prev_fixup(abfd, subspace_reloc_size, p, RELOCATION_SIZE_4, reloc_queue);
    }
}

static unsigned char *
process_comp1_reloc(bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                   arelent *bfd_reloc, void *reloc_queue)
{
    bfd_put_8(abfd, bfd_reloc->howto->type, p);
    bfd_put_8(abfd, COMP1_CONSTANT, p + 1);
    return try_prev_fixup(abfd, subspace_reloc_size, p, 2, reloc_queue);
}

static unsigned char *
process_comp2_reloc(bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                   arelent *bfd_reloc, int sym_num, void *reloc_queue)
{
    bfd_put_8(abfd, bfd_reloc->howto->type, p);
    bfd_put_8(abfd, COMP2_CONSTANT, p + 1);
    bfd_put_8(abfd, sym_num >> 16, p + 2);
    bfd_put_16(abfd, (bfd_vma) sym_num, p + 3);
    return try_prev_fixup(abfd, subspace_reloc_size, p, 5, reloc_queue);
}

static unsigned char *
process_single_relocation(bfd *abfd, unsigned char *p, unsigned int *subspace_reloc_size,
                         arelent *bfd_reloc, asection *subsection, unsigned int j,
                         unsigned int *current_rounding_mode, void *reloc_queue
#ifndef NO_PCREL_MODES
                         , unsigned int *current_call_mode
#endif
                         )
{
    int sym_num = get_symbol_number(bfd_reloc);
    
    switch (bfd_reloc->howto->type)
    {
    case R_PCREL_CALL:
    case R_ABS_CALL:
        return som_reloc_call(abfd, p, subspace_reloc_size, bfd_reloc, sym_num, reloc_queue);
        
    case R_CODE_ONE_SYMBOL:
    case R_DP_RELATIVE:
        return process_code_or_dp_reloc(abfd, p, subspace_reloc_size, bfd_reloc, sym_num, reloc_queue);
        
    case R_DATA_GPREL:
        return process_data_gprel(abfd, p, subspace_reloc_size, bfd_reloc, sym_num, reloc_queue);
        
    case R_DATA_ONE_SYMBOL:
    case R_DATA_PLABEL:
    case R_CODE_PLABEL:
    case R_DLT_REL:
        return process_data_symbol_reloc(abfd, p, subspace_reloc_size, bfd_reloc, sym_num, reloc_queue);
        
    case R_ENTRY:
        return process_entry_reloc(abfd, p, subspace_reloc_size, bfd_reloc, subsection, j, reloc_queue);
        
    case R_N_MODE:
    case R_S_MODE:
    case R_D_MODE:
    case R_R_MODE:
        return process_mode_reloc(abfd, p, subspace_reloc_size, bfd_reloc, current_rounding_mode);
        
#ifndef NO_PCREL_MODES
    case R_LONG_PCREL_MODE:
    case R_SHORT_PCREL_MODE:
        return process_mode_reloc(abfd, p, subspace_reloc_size, bfd_reloc, current_call_mode);
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
        return process_simple_reloc(abfd, p, subspace_reloc_size, bfd_reloc);
        
    case R_END_TRY:
        return process_end_try_reloc(abfd, p, subspace_reloc_size, bfd_reloc, reloc_queue);
        
    case R_COMP1:
        return process_comp1_reloc(abfd, p, subspace_reloc_size, bfd_reloc, reloc_queue);
        
    case R_COMP2:
        return process_comp2_reloc(abfd, p, subspace_reloc_size, bfd_reloc, sym_num, reloc_queue);
        
    case R_CODE_EXPR:
    case R_DATA_EXPR:
        return process_simple_reloc(abfd, p, subspace_reloc_size, bfd_reloc);
        
    default:
        bfd_put_8(abfd, RESERVED_RELOC, p);
        (*subspace_reloc_size)++;
        return p + 1;
    }
}

static bool
process_subspace_relocations(bfd *abfd, asection *subsection, unsigned char *tmp_space,
                            unsigned int current_offset, unsigned int *total_reloc_size)
{
    unsigned char *p = tmp_space;
    unsigned int subspace_reloc_size = 0;
    unsigned int reloc_offset = 0;
    unsigned int current_rounding_mode = R_N_MODE;
#ifndef NO_PCREL_MODES
    unsigned int current_call_mode = R_SHORT_PCREL_MODE;
#endif
    void *reloc_queue;
    
    som_section_data(subsection)->subspace_dict->fixup_request_index = *total_reloc_size;
    
    if (bfd_seek(abfd, current_offset + *total_reloc_size, SEEK_SET) != 0)
        return false;
    
    som_initialize_reloc_queue(reloc_queue);
    
    for (unsigned int j = 0; j < subsection->reloc_count; j++)
    {
        arelent *bfd_reloc = subsection->orelocation[j];
        
        if (!validate_relocation(abfd, subsection, bfd_reloc))
            return false;
        
        p = flush_buffer_if_needed(abfd, p, tmp_space, reloc_queue);
        if (!p)
            return false;
        
        unsigned int skip = bfd_reloc->address - reloc_offset;
        p = som_reloc_skip(abfd, skip, p, &subspace_reloc_size, reloc_queue);
        
        reloc_offset = bfd_reloc->address + bfd_reloc->howto->size;
        
        p = process_single_relocation(abfd, p, &subspace_reloc_size, bfd_reloc,
                                     subsection, j, &current_rounding_mode, reloc_queue
#ifndef NO_PCREL_MODES
                                     , &current_call_mode
#endif
                                     );
    }
    
    p = som_reloc_skip(abfd, subsection->size - reloc_offset, p, &subspace_reloc_size, reloc_queue);
    
    size_t amt = p - tmp_space;
    if (bfd_write(tmp_space, amt, abfd) != amt)
        return false;
    
    *total_reloc_size += subspace_reloc_size;
    som_section_data(subsection)->subspace_dict->fixup_request_quantity = subspace_reloc_size;
    
    return true;
}

static bool
should_process_subspace(asection *subsection, asection *section)
{
    if (!som_is_subspace(subsection) || !som_is_container(section, subsection))
        return false;
    
    if ((subsection->flags & SEC_HAS_CONTENTS) == 0)
    {
        som_section_data(subsection)->subspace_dict->fixup_request_index = -1;
        return false;
    }
    
    return true;
}

static asection *
find_next_space(asection *section)
{
    while (section && !som_is_space(section))
        section = section->next;
    return section;
}

static bool
som_write_fixups(bfd *abfd,
                unsigned long current_offset,
                unsigned int *total_reloc_sizep)
{
    unsigned char tmp_space[SOM_TMP_BUFSIZE];
    unsigned int total_reloc_size = 0;
    unsigned int num_spaces = obj_som_file_hdr(abfd)->space_total;
    asection *section = abfd->sections;
    
    memset(tmp_space, 0, SOM_TMP_BUFSIZE);
    
    for (unsigned int i = 0; i < num_spaces; i++)
    {
        section = find_next_space(section);
        if (!section)
            break;
        
        for (asection *subsection = abfd->sections; subsection != NULL; subsection = subsection->next)
        {
            if (!should_process_subspace(subsection, section))
                continue;
            
            if (!process_subspace_relocations(abfd, subsection, tmp_space, current_offset, &total_reloc_size))
                return false;
        }
        
        section = section->next;
    }
    
    *total_reloc_sizep = total_reloc_size;
    return true;
}

/* Write the length of STR followed by STR to P which points into
   *BUF, a buffer of *BUFLEN size.  Track total size in *STRINGS_SIZE,
   setting *STRX to the current offset for STR.  When STR can't fit in
   *BUF, flush the buffer to ABFD, possibly reallocating.  Return the
   next available location in *BUF, or NULL on error.  */

static char *flush_buffer(char *p, char **buf, bfd *abfd)
{
    size_t amt = p - *buf;
    if (bfd_write(*buf, amt, abfd) != amt)
        return NULL;
    return *buf;
}

static char *reallocate_buffer_if_needed(char **buf, size_t *buflen, size_t needed)
{
    if (needed <= *buflen)
        return *buf;
    
    const size_t MIN_GROWTH_FACTOR = 2;
    size_t new_size = *buflen * MIN_GROWTH_FACTOR;
    if (new_size < needed)
        new_size = needed;
    
    *buflen = new_size;
    free(*buf);
    *buf = bfd_malloc(*buflen);
    return *buf;
}

static char *ensure_buffer_space(char *p, char **buf, size_t *buflen, size_t needed, bfd *abfd)
{
    if (p - *buf + needed <= *buflen)
        return p;
    
    p = flush_buffer(p, buf, abfd);
    if (p == NULL)
        return NULL;
    
    if (reallocate_buffer_if_needed(buf, buflen, needed) == NULL)
        return NULL;
    
    return *buf;
}

static char *write_string_length(char *p, size_t length, bfd *abfd, unsigned int *strings_size)
{
    const size_t LENGTH_FIELD_SIZE = 4;
    bfd_put_32(abfd, length - 1, p);
    *strings_size += LENGTH_FIELD_SIZE;
    return p + LENGTH_FIELD_SIZE;
}

static char *write_string_data(char *p, const char *str, size_t length, unsigned int *strings_size)
{
    memcpy(p, str, length);
    *strings_size += length;
    return p + length;
}

static char *add_padding(char *p, size_t length, unsigned int *strings_size)
{
    const size_t ALIGNMENT = 4;
    size_t remainder = length & (ALIGNMENT - 1);
    if (remainder == 0)
        return p;
    
    size_t padding = ALIGNMENT - remainder;
    memset(p, 0, padding);
    *strings_size += padding;
    return p + padding;
}

static char *add_string(char *p, const char *str, bfd *abfd, char **buf, size_t *buflen,
                       unsigned int *strings_size, unsigned int *strx)
{
    size_t length = strlen(str) + 1;
    const size_t ENTRY_OVERHEAD = 4;
    const size_t ALIGNMENT_MASK = 3;
    size_t needed = (ENTRY_OVERHEAD + length + ALIGNMENT_MASK) & ~ALIGNMENT_MASK;
    
    p = ensure_buffer_space(p, buf, buflen, needed, abfd);
    if (p == NULL)
        return NULL;
    
    p = write_string_length(p, length, abfd, strings_size);
    *strx = *strings_size;
    p = write_string_data(p, str, length, strings_size);
    p = add_padding(p, length, strings_size);
    
    return p;
}

/* Write out the space/subspace string table.  */

static bool
is_space_or_subspace(asection *section, unsigned int **strx)
{
    if (som_is_space(section)) {
        *strx = &som_section_data(section)->space_dict->name;
        return true;
    }
    if (som_is_subspace(section)) {
        *strx = &som_section_data(section)->subspace_dict->name;
        return true;
    }
    return false;
}

static bool
write_section_strings(bfd *abfd, char **p, char **tmp_space, 
                     size_t *tmp_space_size, unsigned int *strings_size)
{
    asection *section;
    
    for (section = abfd->sections; section != NULL; section = section->next) {
        unsigned int *strx;
        
        if (!is_space_or_subspace(section, &strx))
            continue;
        
        *p = add_string(*p, section->name, abfd, tmp_space, tmp_space_size,
                       strings_size, strx);
        if (*p == NULL)
            return false;
    }
    return true;
}

static bool
write_partial_block(bfd *abfd, char *tmp_space, char *p)
{
    size_t amt = p - tmp_space;
    if (amt == 0)
        return true;
    return bfd_write(tmp_space, amt, abfd) == amt;
}

static bool
som_write_space_strings(bfd *abfd,
                       unsigned long current_offset,
                       unsigned int *strings_size)
{
    size_t tmp_space_size = SOM_TMP_BUFSIZE;
    char *tmp_space = bfd_malloc(tmp_space_size);
    char *p = tmp_space;
    bool ok;
    
    if (tmp_space == NULL)
        return false;
    
    if (bfd_seek(abfd, current_offset, SEEK_SET) != 0) {
        free(tmp_space);
        return false;
    }
    
    *strings_size = 0;
    
    if (!write_section_strings(abfd, &p, &tmp_space, &tmp_space_size, strings_size)) {
        free(tmp_space);
        return false;
    }
    
    ok = write_partial_block(abfd, tmp_space, p);
    free(tmp_space);
    return ok;
}

/* Write out the symbol string table.  */

static bool
write_final_block(bfd *abfd, char *tmp_space, char *p)
{
  size_t amt = p - tmp_space;
  if (amt == 0)
    return true;
  return bfd_write(tmp_space, amt, abfd) == amt;
}

static struct som_name_pt*
get_compilation_unit_name(struct som_compilation_unit *compilation_unit, unsigned int index)
{
  switch (index)
    {
    case 0:
      return &compilation_unit->name;
    case 1:
      return &compilation_unit->language_name;
    case 2:
      return &compilation_unit->product_id;
    case 3:
      return &compilation_unit->version_id;
    default:
      abort();
    }
}

static char*
write_compilation_unit_strings(bfd *abfd,
                               struct som_compilation_unit *compilation_unit,
                               char *tmp_space,
                               size_t *tmp_space_size,
                               unsigned int *strings_size,
                               char *p)
{
  const unsigned int NUM_COMPILATION_UNIT_NAMES = 4;
  unsigned int i;
  
  if (!compilation_unit)
    return p;
    
  for (i = 0; i < NUM_COMPILATION_UNIT_NAMES; i++)
    {
      struct som_name_pt *name = get_compilation_unit_name(compilation_unit, i);
      p = add_string(p, name->name, abfd, &tmp_space, tmp_space_size,
                    strings_size, &name->strx);
      if (p == NULL)
        return NULL;
    }
  return p;
}

static char*
write_symbol_strings(bfd *abfd,
                    asymbol **syms,
                    unsigned int num_syms,
                    char *tmp_space,
                    size_t *tmp_space_size,
                    unsigned int *strings_size,
                    char *p)
{
  unsigned int i;
  
  for (i = 0; i < num_syms; i++)
    {
      p = add_string(p, syms[i]->name, abfd, &tmp_space, tmp_space_size,
                    strings_size,
                    &som_symbol_data(syms[i])->stringtab_offset);
      if (p == NULL)
        return NULL;
    }
  return p;
}

static bool
som_write_symbol_strings(bfd *abfd,
                        unsigned long current_offset,
                        asymbol **syms,
                        unsigned int num_syms,
                        unsigned int *strings_size,
                        struct som_compilation_unit *compilation_unit)
{
  size_t tmp_space_size = SOM_TMP_BUFSIZE;
  char *tmp_space = bfd_malloc(tmp_space_size);
  char *p = tmp_space;
  bool ok;

  if (tmp_space == NULL)
    return false;

  if (bfd_seek(abfd, current_offset, SEEK_SET) != 0)
    {
      free(tmp_space);
      return false;
    }

  *strings_size = 0;
  
  p = write_compilation_unit_strings(abfd, compilation_unit, tmp_space,
                                     &tmp_space_size, strings_size, p);
  if (p == NULL)
    {
      free(tmp_space);
      return false;
    }

  p = write_symbol_strings(abfd, syms, num_syms, tmp_space,
                          &tmp_space_size, strings_size, p);
  if (p == NULL)
    {
      free(tmp_space);
      return false;
    }

  ok = write_final_block(abfd, tmp_space, p);
  free(tmp_space);
  return ok;
}

/* Compute variable information to be placed in the SOM headers,
   space/subspace dictionaries, relocation streams, etc.  Begin
   writing parts of the object file.  */

static bool
write_string_auxhdr(bfd *abfd, unsigned long *current_offset, 
                    struct som_string_auxhdr *hdr)
{
  struct som_external_string_auxhdr ext_string_auxhdr;
  bfd_size_type len;

  if (bfd_seek(abfd, *current_offset, SEEK_SET) != 0)
    return false;

  len = sizeof(struct som_external_string_auxhdr);
  obj_som_file_hdr(abfd)->aux_header_size += len;
  *current_offset += len;
  som_swap_string_auxhdr_out(hdr, &ext_string_auxhdr);
  if (bfd_write(&ext_string_auxhdr, len, abfd) != len)
    return false;

  len = hdr->header_id.length - 4;
  obj_som_file_hdr(abfd)->aux_header_size += len;
  *current_offset += len;
  if (bfd_write(hdr->string, len, abfd) != len)
    return false;

  return true;
}

static void
setup_exec_header(bfd *abfd, unsigned long *current_offset)
{
  struct som_exec_auxhdr *exec_header;
  
  *current_offset += sizeof(struct som_external_exec_auxhdr);
  obj_som_file_hdr(abfd)->aux_header_size += 
    sizeof(struct som_external_exec_auxhdr);
  exec_header = obj_som_exec_hdr(abfd);
  exec_header->som_auxhdr.type = EXEC_AUX_ID;
  exec_header->som_auxhdr.length = 40;
}

static bool
write_auxiliary_headers(bfd *abfd, unsigned long *current_offset)
{
  obj_som_file_hdr(abfd)->aux_header_location = *current_offset;
  obj_som_file_hdr(abfd)->aux_header_size = 0;
  
  if (abfd->flags & (EXEC_P | DYNAMIC))
    setup_exec_header(abfd, current_offset);

  if (obj_som_version_hdr(abfd) != NULL)
    if (!write_string_auxhdr(abfd, current_offset, obj_som_version_hdr(abfd)))
      return false;

  if (obj_som_copyright_hdr(abfd) != NULL)
    if (!write_string_auxhdr(abfd, current_offset, obj_som_copyright_hdr(abfd)))
      return false;

  return true;
}

static void
setup_space_records(bfd *abfd, unsigned long *current_offset)
{
  unsigned long num_spaces = som_count_spaces(abfd);
  obj_som_file_hdr(abfd)->space_location = *current_offset;
  obj_som_file_hdr(abfd)->space_total = num_spaces;
  *current_offset += 
    num_spaces * sizeof(struct som_external_space_dictionary_record);
}

static void
setup_subspace_records(bfd *abfd, unsigned long *current_offset)
{
  unsigned long num_subspaces = som_count_subspaces(abfd);
  obj_som_file_hdr(abfd)->subspace_location = *current_offset;
  obj_som_file_hdr(abfd)->subspace_total = num_subspaces;
  *current_offset += 
    num_subspaces * sizeof(struct som_external_subspace_dictionary_record);
}

static bool
write_string_table(bfd *abfd, unsigned long *current_offset)
{
  unsigned int strings_size = 0;
  
  if (*current_offset % 4)
    *current_offset += (4 - (*current_offset % 4));

  obj_som_file_hdr(abfd)->space_strings_location = *current_offset;
  
  if (!som_write_space_strings(abfd, *current_offset, &strings_size))
    return false;

  obj_som_file_hdr(abfd)->space_strings_size = strings_size;
  *current_offset += strings_size;
  
  return true;
}

static void
setup_compilation_unit(bfd *abfd, unsigned long *current_offset)
{
  obj_som_file_hdr(abfd)->compiler_location = *current_offset;
  obj_som_file_hdr(abfd)->compiler_total = 0;
  
  if (obj_som_compilation_unit(abfd))
  {
    obj_som_file_hdr(abfd)->compiler_total = 1;
    *current_offset += sizeof(struct som_external_compilation_unit);
  }
}

static void
align_for_executable(bfd *abfd, unsigned long *current_offset, asection *subsection)
{
  if (abfd->flags & (D_PAGED | DYNAMIC)
      || (subsection->flags & SEC_CODE)
      || ((abfd->flags & WP_TEXT) && (subsection->flags & SEC_DATA)))
    *current_offset = SOM_ALIGN(*current_offset, PA_PAGESIZE);
}

static void
update_exec_header_first_subspace(struct som_exec_auxhdr *exec_header,
                                  asection *section, asection *subsection,
                                  unsigned long current_offset)
{
  if (subsection->flags & SEC_CODE && exec_header->exec_tfile == 0)
  {
    exec_header->exec_tmem = section->vma;
    exec_header->exec_tfile = current_offset;
  }
  if (subsection->flags & SEC_DATA && exec_header->exec_dfile == 0)
  {
    exec_header->exec_dmem = section->vma;
    exec_header->exec_dfile = current_offset;
  }
}

static void
update_exec_header_sizes(struct som_exec_auxhdr *exec_header,
                         asection *subsection, unsigned long hole_size)
{
  if (subsection->flags & SEC_CODE)
    exec_header->exec_tsize += hole_size;
  else
    exec_header->exec_dsize += hole_size;
}

static void
process_loadable_subsection(bfd *abfd, asection *subsection,
                           unsigned long *current_offset,
                           unsigned int *subspace_offset,
                           struct som_exec_auxhdr *exec_header)
{
  if (subsection->flags & SEC_LOAD)
  {
    if (abfd->flags & (EXEC_P | DYNAMIC))
    {
      if (subsection->flags & SEC_CODE)
        exec_header->exec_tsize += subsection->size;
      else if (subsection->flags & SEC_DATA)
        exec_header->exec_dsize += subsection->size;
    }
    som_section_data(subsection)->subspace_dict->file_loc_init_value = 
      *current_offset;
    subsection->filepos = *current_offset;
    *current_offset += subsection->size;
    *subspace_offset += subsection->size;
  }
  else
  {
    if (abfd->flags & (EXEC_P | DYNAMIC))
      exec_header->exec_bsize += subsection->size;
    som_section_data(subsection)->subspace_dict->file_loc_init_value = 0;
    som_section_data(subsection)->subspace_dict->initialization_length = 0;
  }
}

static void
process_loadable_subspaces(bfd *abfd, asection *section,
                          unsigned long *current_offset,
                          unsigned int *total_subspaces,
                          struct som_exec_auxhdr *exec_header)
{
  asection *subsection;
  int first_subspace = 1;
  unsigned int subspace_offset = 0;

  for (subsection = abfd->sections; subsection; subsection = subsection->next)
  {
    if (!som_is_subspace(subsection)
        || !som_is_container(section, subsection)
        || (subsection->flags & SEC_ALLOC) == 0)
      continue;

    if (first_subspace && (abfd->flags & (EXEC_P | DYNAMIC)))
    {
      align_for_executable(abfd, current_offset, subsection);
      update_exec_header_first_subspace(exec_header, section, subsection, 
                                       *current_offset);
      subspace_offset = subsection->vma;
      first_subspace = 0;
    }
    else if (abfd->flags & (EXEC_P | DYNAMIC))
    {
      unsigned long hole_size = subsection->vma - subspace_offset;
      *current_offset += hole_size;
      update_exec_header_sizes(exec_header, subsection, hole_size);
      subspace_offset += hole_size;
    }

    subsection->target_index = (*total_subspaces)++;
    process_loadable_subsection(abfd, subsection, current_offset,
                               &subspace_offset, exec_header);
  }
}

static void
process_unloadable_subsection(asection *subsection, unsigned long *current_offset)
{
  if ((subsection->flags & SEC_LOAD) == 0)
  {
    som_section_data(subsection)->subspace_dict->file_loc_init_value = 
      *current_offset;
    subsection->filepos = *current_offset;
    *current_offset += subsection->size;
  }
  else
  {
    som_section_data(subsection)->subspace_dict->file_loc_init_value = 0;
    som_section_data(subsection)->subspace_dict->initialization_length = 
      subsection->size;
  }
}

static void
process_unloadable_subspaces(bfd *abfd, asection *section,
                            unsigned long *current_offset,
                            unsigned int *total_subspaces)
{
  asection *subsection;

  if (abfd->flags & (EXEC_P | DYNAMIC))
    *current_offset = SOM_ALIGN(*current_offset, PA_PAGESIZE);

  for (subsection = abfd->sections; subsection; subsection = subsection->next)
  {
    if (!som_is_subspace(subsection)
        || !som_is_container(section, subsection)
        || (subsection->flags & SEC_ALLOC) != 0)
      continue;

    subsection->target_index = (*total_subspaces)++;
    process_unloadable_subsection(subsection, current_offset);
  }
}

static asection *
find_next_space(asection *section)
{
  while (!som_is_space(section))
    section = section->next;
  return section;
}

static bool
finalize_file(bfd *abfd, unsigned long current_offset)
{
  if (abfd->flags & (EXEC_P | DYNAMIC))
    current_offset = SOM_ALIGN(current_offset, PA_PAGESIZE);
    
  if (bfd_seek(abfd, current_offset - 1, SEEK_SET) != 0)
    return false;
  if (bfd_write("", 1, abfd) != 1)
    return false;
    
  return true;
}

static bool
som_begin_writing(bfd *abfd)
{
  unsigned long current_offset = 0;
  unsigned long num_spaces, i;
  asection *section;
  unsigned int total_subspaces = 0;
  struct som_exec_auxhdr *exec_header = NULL;

  current_offset += sizeof(struct som_external_header);

  if (!write_auxiliary_headers(abfd, &current_offset))
    return false;

  if (abfd->flags & (EXEC_P | DYNAMIC))
    exec_header = obj_som_exec_hdr(abfd);

  obj_som_file_hdr(abfd)->init_array_location = current_offset;
  obj_som_file_hdr(abfd)->init_array_total = 0;

  setup_space_records(abfd, &current_offset);
  setup_subspace_records(abfd, &current_offset);

  if (!write_string_table(abfd, &current_offset))
    return false;

  setup_compilation_unit(abfd, &current_offset);

  num_spaces = obj_som_file_hdr(abfd)->space_total;
  section = abfd->sections;
  
  for (i = 0; i < num_spaces; i++)
  {
    section = find_next_space(section);
    process_loadable_subspaces(abfd, section, &current_offset,
                              &total_subspaces, exec_header);
    section = section->next;
  }

  if (abfd->flags & (EXEC_P | DYNAMIC))
    current_offset = SOM_ALIGN(current_offset, PA_PAGESIZE);

  obj_som_file_hdr(abfd)->unloadable_sp_location = current_offset;
  section = abfd->sections;
  
  for (i = 0; i < num_spaces; i++)
  {
    section = find_next_space(section);
    process_unloadable_subspaces(abfd, section, &current_offset,
                                &total_subspaces);
    section = section->next;
  }

  if (!finalize_file(abfd, current_offset))
    return false;

  obj_som_file_hdr(abfd)->unloadable_sp_size =
    current_offset - obj_som_file_hdr(abfd)->unloadable_sp_location;

  obj_som_file_hdr(abfd)->loader_fixup_location = 0;
  obj_som_file_hdr(abfd)->loader_fixup_total = 0;
  obj_som_file_hdr(abfd)->som_length = current_offset;

  return true;
}

/* Finally, scribble out the various headers to the disk.  */

static bool
set_version_id(bfd *abfd)
{
  if (obj_som_exec_data(abfd) && obj_som_exec_data(abfd)->version_id)
    obj_som_file_hdr(abfd)->version_id = obj_som_exec_data(abfd)->version_id;
  else
    obj_som_file_hdr(abfd)->version_id = NEW_VERSION_ID;
  return true;
}

static unsigned long
align_to_word_boundary(unsigned long offset)
{
  const int WORD_BOUNDARY = 4;
  if (offset % WORD_BOUNDARY)
    return offset + (WORD_BOUNDARY - (offset % WORD_BOUNDARY));
  return offset;
}

static unsigned long
setup_symbol_table_location(bfd *abfd, unsigned long current_offset)
{
  int num_syms = bfd_get_symcount(abfd);
  current_offset = align_to_word_boundary(current_offset);
  obj_som_file_hdr(abfd)->symbol_location = current_offset;
  obj_som_file_hdr(abfd)->symbol_total = num_syms;
  return current_offset + num_syms * sizeof(struct som_external_symbol_dictionary_record);
}

static unsigned long
write_symbol_strings_section(bfd *abfd, unsigned long current_offset)
{
  unsigned int strings_size;
  asymbol **syms = bfd_get_outsymbols(abfd);
  int num_syms = bfd_get_symcount(abfd);
  
  current_offset = align_to_word_boundary(current_offset);
  obj_som_file_hdr(abfd)->symbol_strings_location = current_offset;
  
  if (!som_write_symbol_strings(abfd, current_offset, syms, num_syms, 
                                &strings_size, obj_som_compilation_unit(abfd)))
    return 0;
  
  obj_som_file_hdr(abfd)->symbol_strings_size = strings_size;
  return current_offset + strings_size;
}

static unsigned long
write_fixup_stream(bfd *abfd, unsigned long current_offset)
{
  unsigned int total_reloc_size;
  
  if (!som_prep_for_fixups(abfd, bfd_get_outsymbols(abfd), bfd_get_symcount(abfd)))
    return 0;
  
  current_offset = align_to_word_boundary(current_offset);
  obj_som_file_hdr(abfd)->fixup_request_location = current_offset;
  
  if (!som_write_fixups(abfd, current_offset, &total_reloc_size))
    return 0;
  
  obj_som_file_hdr(abfd)->fixup_request_total = total_reloc_size;
  obj_som_file_hdr(abfd)->som_length = current_offset + total_reloc_size;
  
  return current_offset + total_reloc_size;
}

static asection*
find_next_space(asection *section)
{
  while (section && !som_is_space(section))
    section = section->next;
  return section;
}

static bool
should_write_subspace(asection *subsection, asection *space, bool loadable)
{
  if (!som_is_subspace(subsection))
    return false;
  if (!som_is_container(space, subsection))
    return false;
  
  bool has_alloc = (subsection->flags & SEC_ALLOC) != 0;
  return loadable ? has_alloc : !has_alloc;
}

static bool
write_subspace_record(bfd *abfd, asection *subsection, int space_index)
{
  struct som_external_subspace_dictionary_record ext_subspace_dict;
  size_t amt = sizeof(struct som_subspace_dictionary_record);
  
  som_section_data(subsection)->subspace_dict->space_index = space_index;
  som_swap_subspace_dictionary_record_out(som_section_data(subsection)->subspace_dict, 
                                          &ext_subspace_dict);
  return bfd_write(&ext_subspace_dict, amt, abfd) == amt;
}

static bool
process_subspace(bfd *abfd, asection *space, asection *subsection, 
                 int *subspace_index, int space_index, bool loadable)
{
  if (som_section_data(space)->space_dict->subspace_quantity == 0)
  {
    som_section_data(space)->space_dict->is_loadable = loadable ? 1 : 0;
    som_section_data(space)->space_dict->subspace_index = *subspace_index;
  }
  
  (*subspace_index)++;
  som_section_data(space)->space_dict->subspace_quantity++;
  
  return write_subspace_record(abfd, subsection, space_index);
}

static bool
write_subspaces_for_type(bfd *abfd, int num_spaces, int *subspace_index, bool loadable)
{
  asection *section = abfd->sections;
  
  for (int i = 0; i < num_spaces; i++)
  {
    section = find_next_space(section);
    if (!section)
      return false;
    
    for (asection *subsection = abfd->sections; subsection; subsection = subsection->next)
    {
      if (!should_write_subspace(subsection, section, loadable))
        continue;
      
      if (!process_subspace(abfd, section, subsection, subspace_index, i, loadable))
        return false;
    }
    
    section = section->next;
  }
  
  return true;
}

static bool
write_all_subspaces(bfd *abfd, int num_spaces)
{
  int subspace_index = 0;
  file_ptr location = obj_som_file_hdr(abfd)->subspace_location;
  
  if (bfd_seek(abfd, location, SEEK_SET) != 0)
    return false;
  
  if (!write_subspaces_for_type(abfd, num_spaces, &subspace_index, true))
    return false;
  
  return write_subspaces_for_type(abfd, num_spaces, &subspace_index, false);
}

static bool
write_space_dictionary(bfd *abfd, int num_spaces)
{
  file_ptr location = obj_som_file_hdr(abfd)->space_location;
  size_t amt = sizeof(struct som_external_space_dictionary_record);
  
  if (bfd_seek(abfd, location, SEEK_SET) != 0)
    return false;
  
  asection *section = abfd->sections;
  for (int i = 0; i < num_spaces; i++)
  {
    struct som_external_space_dictionary_record ext_space_dict;
    
    section = find_next_space(section);
    if (!section)
      return false;
    
    som_swap_space_dictionary_out(som_section_data(section)->space_dict, &ext_space_dict);
    
    if (bfd_write(&ext_space_dict, amt, abfd) != amt)
      return false;
    
    section = section->next;
  }
  
  return true;
}

static bool
write_compilation_unit(bfd *abfd)
{
  if (!obj_som_compilation_unit(abfd))
    return true;
  
  struct som_external_compilation_unit ext_comp_unit;
  file_ptr location = obj_som_file_hdr(abfd)->compiler_location;
  size_t amt = sizeof(struct som_external_compilation_unit);
  
  if (bfd_seek(abfd, location, SEEK_SET) != 0)
    return false;
  
  som_swap_compilation_unit_out(obj_som_compilation_unit(abfd), &ext_comp_unit);
  
  return bfd_write(&ext_comp_unit, amt, abfd) == amt;
}

static void
set_system_id(bfd *abfd)
{
  if ((abfd->flags & (EXEC_P | DYNAMIC)) && obj_som_exec_data(abfd))
    obj_som_file_hdr(abfd)->system_id = obj_som_exec_data(abfd)->system_id;
  else if (bfd_get_mach(abfd) == pa20)
    obj_som_file_hdr(abfd)->system_id = CPU_PA_RISC2_0;
  else if (bfd_get_mach(abfd) == pa11)
    obj_som_file_hdr(abfd)->system_id = CPU_PA_RISC1_1;
  else
    obj_som_file_hdr(abfd)->system_id = CPU_PA_RISC1_0;
}

static bool
write_file_header(bfd *abfd)
{
  struct som_external_header ext_header;
  size_t amt = sizeof(struct som_external_header);
  
  som_swap_header_out(obj_som_file_hdr(abfd), &ext_header);
  bfd_putb32(som_compute_checksum(&ext_header), ext_header.checksum);
  
  if (bfd_seek(abfd, 0, SEEK_SET) != 0)
    return false;
  
  return bfd_write(&ext_header, amt, abfd) == amt;
}

static void
adjust_exec_sizes(struct som_exec_auxhdr *exec_header)
{
  long tmp = exec_header->exec_dsize;
  tmp = SOM_ALIGN(tmp, PA_PAGESIZE);
  exec_header->exec_bsize -= (tmp - exec_header->exec_dsize);
  if (exec_header->exec_bsize < 0)
    exec_header->exec_bsize = 0;
  exec_header->exec_dsize = tmp;
}

static bool
validate_exec_header(struct som_exec_auxhdr *exec_header, long som_length)
{
  if (exec_header->exec_tfile + exec_header->exec_tsize > som_length ||
      exec_header->exec_dfile + exec_header->exec_dsize > som_length)
  {
    bfd_set_error(bfd_error_bad_value);
    return false;
  }
  return true;
}

static bool
write_exec_header(bfd *abfd)
{
  if (!(abfd->flags & (EXEC_P | DYNAMIC)))
    return true;
  
  struct som_exec_auxhdr *exec_header = obj_som_exec_hdr(abfd);
  struct som_external_exec_auxhdr ext_exec_header;
  size_t amt = sizeof(ext_exec_header);
  
  exec_header->exec_entry = bfd_get_start_address(abfd);
  if (obj_som_exec_data(abfd))
    exec_header->exec_flags = obj_som_exec_data(abfd)->exec_flags;
  
  adjust_exec_sizes(exec_header);
  
  if (!validate_exec_header(exec_header, obj_som_file_hdr(abfd)->som_length))
    return false;
  
  som_swap_exec_auxhdr_out(exec_header, &ext_exec_header);
  
  if (bfd_seek(abfd, obj_som_file_hdr(abfd)->aux_header_location, SEEK_SET) != 0)
    return false;
  
  return bfd_write(&ext_exec_header, amt, abfd) == amt;
}

static bool
som_finish_writing(bfd *abfd)
{
  int num_spaces = som_count_spaces(abfd);
  unsigned long current_offset;
  
  set_version_id(abfd);
  
  current_offset = obj_som_file_hdr(abfd)->som_length;
  current_offset = setup_symbol_table_location(abfd, current_offset);
  
  current_offset = write_symbol_strings_section(abfd, current_offset);
  if (current_offset == 0)
    return false;
  
  current_offset = write_fixup_stream(abfd, current_offset);
  if (current_offset == 0)
    return false;
  
  if (!som_build_and_write_symbol_table(abfd))
    return false;
  
  if (!write_all_subspaces(abfd, num_spaces))
    return false;
  
  if (!write_space_dictionary(abfd, num_spaces))
    return false;
  
  if (!write_compilation_unit(abfd))
    return false;
  
  set_system_id(abfd);
  
  if (!write_file_header(abfd))
    return false;
  
  return write_exec_header(abfd);
}

/* Compute and return the checksum for a SOM file header.  */

static uint32_t
som_compute_checksum (struct som_external_header *hdr)
{
  size_t count, i;
  uint32_t checksum;
  uint32_t *buffer = (uint32_t *) hdr;

  checksum = 0;
  count = sizeof (*hdr) / sizeof (*buffer);
  for (i = 0; i < count; i++)
    checksum ^= buffer[i];

  return checksum;
}

static bool is_function_symbol(asymbol *sym)
{
    return (sym->flags & BSF_FUNCTION) != 0;
}

static bool is_undefined_function(asymbol *sym)
{
    int som_type = som_symbol_data(sym)->som_type;
    return (som_type == SYMBOL_TYPE_UNKNOWN || som_type == SYMBOL_TYPE_CODE)
           && bfd_is_und_section(sym->section)
           && is_function_symbol(sym);
}

static bool is_entry_function(asymbol *sym)
{
    int som_type = som_symbol_data(sym)->som_type;
    return som_type == SYMBOL_TYPE_ENTRY
           || (som_type == SYMBOL_TYPE_CODE && is_function_symbol(sym))
           || (som_type == SYMBOL_TYPE_UNKNOWN && is_function_symbol(sym));
}

static void set_entry_symbol_info(asymbol *sym, struct som_misc_symbol_info *info)
{
    info->symbol_type = ST_ENTRY;
    info->arg_reloc = som_symbol_data(sym)->tc_data.ap.hppa_arg_reloc;
    info->priv_level = som_symbol_data(sym)->tc_data.ap.hppa_priv_level;
}

static void set_unknown_symbol_type(asymbol *sym, struct som_misc_symbol_info *info)
{
    if (bfd_is_abs_section(sym->section))
        info->symbol_type = ST_ABSOLUTE;
    else if (sym->section->flags & SEC_CODE)
        info->symbol_type = ST_CODE;
    else
        info->symbol_type = ST_DATA;
}

static void map_som_type_to_st_type(int som_type, struct som_misc_symbol_info *info)
{
    switch (som_type) {
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

static void derive_symbol_type(asymbol *sym, struct som_misc_symbol_info *info)
{
    if (sym->flags & BSF_SECTION_SYM) {
        info->symbol_type = ST_DATA;
        return;
    }

    if (bfd_is_com_section(sym->section)) {
        info->symbol_type = ST_STORAGE;
        info->symbol_scope = SS_UNSAT;
        return;
    }

    if (is_undefined_function(sym)) {
        info->symbol_type = ST_CODE;
        return;
    }

    if (is_entry_function(sym)) {
        set_entry_symbol_info(sym, info);
        return;
    }

    int som_type = som_symbol_data(sym)->som_type;
    if (som_type == SYMBOL_TYPE_UNKNOWN) {
        set_unknown_symbol_type(sym, info);
    } else {
        map_som_type_to_st_type(som_type, info);
    }
}

static void derive_symbol_scope(asymbol *sym, struct som_misc_symbol_info *info)
{
    if (bfd_is_com_section(sym->section))
        return;
    
    if (bfd_is_und_section(sym->section))
        info->symbol_scope = SS_UNSAT;
    else if (sym->flags & (BSF_EXPORT | BSF_WEAK))
        info->symbol_scope = SS_UNIVERSAL;
    else
        info->symbol_scope = SS_LOCAL;
}

static void derive_symbol_info_field(asymbol *sym, struct som_misc_symbol_info *info)
{
    if (bfd_is_com_section(sym->section)
        || bfd_is_und_section(sym->section)
        || bfd_is_abs_section(sym->section)) {
        info->symbol_info = 0;
    } else {
        info->symbol_info = sym->section->target_index;
    }
}

static bool should_set_comdat_flags(asymbol *sym, struct som_misc_symbol_info *info)
{
    return som_section_data(sym->section)
           && som_section_data(sym->section)->subspace_dict
           && info->symbol_scope == SS_UNIVERSAL
           && (info->symbol_type == ST_ENTRY
               || info->symbol_type == ST_CODE
               || info->symbol_type == ST_DATA);
}

static void derive_comdat_flags(asymbol *sym, struct som_misc_symbol_info *info)
{
    if (!should_set_comdat_flags(sym, info))
        return;
    
    struct som_subspace_dictionary_record *subspace = 
        som_section_data(sym->section)->subspace_dict;
    
    info->is_comdat = subspace->is_comdat;
    info->is_common = subspace->is_common;
    info->dup_common = subspace->dup_common;
}

static void
som_bfd_derive_misc_symbol_info (bfd *abfd ATTRIBUTE_UNUSED,
                                 asymbol *sym,
                                 struct som_misc_symbol_info *info)
{
    memset(info, 0, sizeof(struct som_misc_symbol_info));
    
    derive_symbol_type(sym, info);
    derive_symbol_scope(sym, info);
    derive_symbol_info_field(sym, info);
    
    info->symbol_value = sym->value + sym->section->vma;
    info->secondary_def = (sym->flags & BSF_WEAK) ? true : false;
    
    derive_comdat_flags(sym, info);
}

/* Build and write, in one big chunk, the entire symbol table for
   this BFD.  */

static bool
allocate_symbol_table(unsigned int num_syms, struct som_external_symbol_dictionary_record **som_symtab)
{
  size_t amt;
  
  if (_bfd_mul_overflow(num_syms,
                       sizeof(struct som_external_symbol_dictionary_record),
                       &amt))
    {
      bfd_set_error(bfd_error_no_memory);
      return false;
    }
    
  *som_symtab = bfd_zmalloc(amt);
  if (*som_symtab == NULL && num_syms != 0)
    return false;
    
  return true;
}

static unsigned int
build_symbol_flags(struct som_misc_symbol_info *info)
{
  #define SOM_SYMBOL_XLEAST_VALUE 3
  
  return (info->symbol_type << SOM_SYMBOL_TYPE_SH)
       | (info->symbol_scope << SOM_SYMBOL_SCOPE_SH)
       | (info->arg_reloc << SOM_SYMBOL_ARG_RELOC_SH)
       | (SOM_SYMBOL_XLEAST_VALUE << SOM_SYMBOL_XLEAST_SH)
       | (info->secondary_def ? SOM_SYMBOL_SECONDARY_DEF : 0)
       | (info->is_common ? SOM_SYMBOL_IS_COMMON : 0)
       | (info->dup_common ? SOM_SYMBOL_DUP_COMMON : 0);
}

static unsigned int
build_symbol_info_flags(struct som_misc_symbol_info *info)
{
  return (info->symbol_info << SOM_SYMBOL_SYMBOL_INFO_SH)
       | (info->is_comdat ? SOM_SYMBOL_IS_COMDAT : 0);
}

static void
populate_symbol_entry(bfd *abfd, asymbol *bfd_sym, 
                     struct som_external_symbol_dictionary_record *entry)
{
  struct som_misc_symbol_info info;
  
  bfd_putb32(som_symbol_data(bfd_sym)->stringtab_offset, entry->name);
  
  som_bfd_derive_misc_symbol_info(abfd, bfd_sym, &info);
  
  bfd_putb32(build_symbol_flags(&info), entry->flags);
  bfd_putb32(build_symbol_info_flags(&info), entry->info);
  bfd_putb32(info.symbol_value | info.priv_level, entry->symbol_value);
}

static void
populate_symbol_table(bfd *abfd, unsigned int num_syms,
                     struct som_external_symbol_dictionary_record *som_symtab)
{
  asymbol **bfd_syms = obj_som_sorted_syms(abfd);
  unsigned int i;
  
  for (i = 0; i < num_syms; i++)
    {
      populate_symbol_entry(abfd, bfd_syms[i], &som_symtab[i]);
    }
}

static bool
write_symbol_table(bfd *abfd, unsigned int num_syms,
                  struct som_external_symbol_dictionary_record *som_symtab)
{
  file_ptr symtab_location = obj_som_file_hdr(abfd)->symbol_location;
  bfd_size_type symtab_size;
  
  if (bfd_seek(abfd, symtab_location, SEEK_SET) != 0)
    return false;
    
  symtab_size = num_syms;
  symtab_size *= sizeof(struct som_external_symbol_dictionary_record);
  
  if (bfd_write(som_symtab, symtab_size, abfd) != symtab_size)
    return false;
    
  return true;
}

static bool
som_build_and_write_symbol_table(bfd *abfd)
{
  unsigned int num_syms = bfd_get_symcount(abfd);
  struct som_external_symbol_dictionary_record *som_symtab = NULL;
  bool result;
  
  if (!allocate_symbol_table(num_syms, &som_symtab))
    return false;
    
  populate_symbol_table(abfd, num_syms, som_symtab);
  
  result = write_symbol_table(abfd, num_syms, som_symtab);
  
  free(som_symtab);
  return result;
}

/* Write an object in SOM format.  */

static bool
som_write_object_contents (bfd *abfd)
{
  if (!abfd->output_has_begun)
    {
      som_prep_headers (abfd);
      abfd->output_has_begun = true;
      som_begin_writing (abfd);
    }

  return som_finish_writing (abfd);
}

/* Read and save the string table associated with the given BFD.  */

static bool
som_slurp_string_table (bfd *abfd)
{
  char *stringtab;
  bfd_size_type amt;

  if (obj_som_stringtab (abfd) != NULL)
    return true;

  if (obj_som_stringtab_size (abfd) == 0)
    {
      bfd_set_error (bfd_error_no_symbols);
      return false;
    }

  if (bfd_seek (abfd, obj_som_str_filepos (abfd), SEEK_SET) != 0)
    return false;
    
  amt = obj_som_stringtab_size (abfd);
  stringtab = (char *) _bfd_malloc_and_read (abfd, amt + 1, amt);
  if (stringtab == NULL)
    return false;
    
  stringtab[amt] = 0;
  obj_som_stringtab (abfd) = stringtab;
  return true;
}

/* Return the amount of data (in bytes) required to hold the symbol
   table for this object.  */

static long
som_get_symtab_upper_bound (bfd *abfd)
{
  if (!som_slurp_symbol_table (abfd))
    return -1;

  return (bfd_get_symcount (abfd) + 1) * sizeof (asymbol *);
}

/* Convert from a SOM subspace index to a BFD section.  */

asection *
bfd_section_from_som_symbol
  (bfd *abfd, struct som_external_symbol_dictionary_record *symbol)
{
  unsigned int flags = bfd_getb32 (symbol->flags);
  unsigned int symbol_type = (flags >> SOM_SYMBOL_TYPE_SH) & SOM_SYMBOL_TYPE_MASK;

  if (should_use_quick_mapping(abfd, symbol_type))
    return find_section_by_index(abfd, symbol);
  
  return find_section_by_address(abfd, symbol);
}

static int
should_use_quick_mapping(bfd *abfd, unsigned int symbol_type)
{
  if ((abfd->flags & (EXEC_P | DYNAMIC)) == 0)
    return 1;
    
  return !is_function_symbol(symbol_type);
}

static int
is_function_symbol(unsigned int symbol_type)
{
  return symbol_type == ST_ENTRY 
      || symbol_type == ST_PRI_PROG 
      || symbol_type == ST_SEC_PROG 
      || symbol_type == ST_MILLICODE;
}

static asection *
find_section_by_index(bfd *abfd, struct som_external_symbol_dictionary_record *symbol)
{
  int idx = (bfd_getb32 (symbol->info) >> SOM_SYMBOL_SYMBOL_INFO_SH) 
    & SOM_SYMBOL_SYMBOL_INFO_MASK;
    
  return find_matching_subspace(abfd, section_matches_index, &idx);
}

static asection *
find_section_by_address(bfd *abfd, struct som_external_symbol_dictionary_record *symbol)
{
  unsigned int value = bfd_getb32 (symbol->symbol_value);
  
  return find_matching_subspace(abfd, section_contains_address, &value);
}

static asection *
find_matching_subspace(bfd *abfd, 
                       int (*matcher)(asection *, void *), 
                       void *match_data)
{
  asection *section;
  
  for (section = abfd->sections; section != NULL; section = section->next)
    if (matcher(section, match_data) && som_is_subspace(section))
      return section;
      
  return bfd_abs_section_ptr;
}

static int
section_matches_index(asection *section, void *data)
{
  int *idx = (int *)data;
  return section->target_index == *idx;
}

static int
section_contains_address(asection *section, void *data)
{
  unsigned int *value = (unsigned int *)data;
  return *value >= section->vma 
      && *value <= section->vma + section->size;
}

/* Read and save the symbol table associated with the given BFD.  */

static unsigned int
som_slurp_symbol_table (bfd *abfd)
{
  unsigned int symbol_count = bfd_get_symcount (abfd);
  size_t symsize = sizeof (struct som_external_symbol_dictionary_record);
  struct som_external_symbol_dictionary_record *buf = NULL;
  som_symbol_type *symbase = NULL;
  size_t amt;

  if (obj_som_symtab (abfd) != NULL)
    goto successful_return;

  if (symbol_count == 0)
    goto successful_return;

  if (!som_slurp_string_table (abfd))
    goto error_return;

  if (!allocate_symbol_buffers (abfd, symbol_count, symsize, &buf, &symbase, &amt))
    goto error_return;

  if (!process_symbols (abfd, buf, symbase, symbol_count))
    goto error_return;

  obj_som_symtab (abfd) = symbase;

 successful_return:
  free (buf);
  return true;

 error_return:
  free (symbase);
  free (buf);
  return false;
}

static bool
allocate_symbol_buffers (bfd *abfd, unsigned int symbol_count, size_t symsize,
                         struct som_external_symbol_dictionary_record **buf,
                         som_symbol_type **symbase, size_t *amt)
{
  if (_bfd_mul_overflow (symbol_count, symsize, amt))
    {
      bfd_set_error (bfd_error_file_too_big);
      return false;
    }

  if (bfd_seek (abfd, obj_som_sym_filepos (abfd), SEEK_SET) != 0)
    return false;

  *buf = (struct som_external_symbol_dictionary_record *)
    _bfd_malloc_and_read (abfd, *amt, *amt);
  if (*buf == NULL)
    return false;

  if (_bfd_mul_overflow (symbol_count, sizeof (som_symbol_type), amt))
    {
      bfd_set_error (bfd_error_file_too_big);
      return false;
    }

  *symbase = bfd_zmalloc (*amt);
  if (*symbase == NULL)
    return false;

  return true;
}

static bool
process_symbols (bfd *abfd, struct som_external_symbol_dictionary_record *buf,
                som_symbol_type *symbase, unsigned int symbol_count)
{
  struct som_external_symbol_dictionary_record *bufp, *endbufp;
  som_symbol_type *sym;
  char *stringtab = obj_som_stringtab (abfd);

  endbufp = buf + symbol_count;
  for (bufp = buf, sym = symbase; bufp < endbufp; ++bufp)
    {
      unsigned int flags = bfd_getb32 (bufp->flags);
      unsigned int symbol_type = extract_symbol_type (flags);
      unsigned int symbol_scope = extract_symbol_scope (flags);

      if (should_skip_symbol (symbol_type))
        continue;

      if (!initialize_symbol (abfd, sym, bufp, flags, stringtab))
        return false;

      set_som_type (sym, symbol_type);
      process_symbol_type (sym, symbol_type, symbol_scope);
      process_symbol_scope (abfd, sym, bufp, symbol_type, symbol_scope);
      process_symbol_flags (sym, flags);

      sym++;
    }

  abfd->symcount = sym - symbase;
  return true;
}

static unsigned int
extract_symbol_type (unsigned int flags)
{
  return (flags >> SOM_SYMBOL_TYPE_SH) & SOM_SYMBOL_TYPE_MASK;
}

static unsigned int
extract_symbol_scope (unsigned int flags)
{
  return (flags >> SOM_SYMBOL_SCOPE_SH) & SOM_SYMBOL_SCOPE_MASK;
}

static bool
should_skip_symbol (unsigned int symbol_type)
{
  return symbol_type == ST_SYM_EXT || symbol_type == ST_ARG_EXT;
}

static bool
initialize_symbol (bfd *abfd, som_symbol_type *sym,
                  struct som_external_symbol_dictionary_record *bufp,
                  unsigned int flags, char *stringtab)
{
  bfd_vma offset = bfd_getb32 (bufp->name);

  if (offset >= obj_som_stringtab_size (abfd))
    {
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  sym->symbol.the_bfd = abfd;
  sym->symbol.name = offset + stringtab;
  sym->symbol.value = bfd_getb32 (bufp->symbol_value);
  sym->symbol.section = NULL;
  sym->symbol.flags = 0;

  som_symbol_data (sym)->tc_data.ap.hppa_arg_reloc =
    (flags >> SOM_SYMBOL_ARG_RELOC_SH) & SOM_SYMBOL_ARG_RELOC_MASK;

  return true;
}

static void
set_som_type (som_symbol_type *sym, unsigned int symbol_type)
{
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
}

#define PRIV_LEVEL_MASK 0x3

static void
process_symbol_type (som_symbol_type *sym, unsigned int symbol_type,
                    unsigned int symbol_scope)
{
  switch (symbol_type)
    {
    case ST_ENTRY:
    case ST_MILLICODE:
      sym->symbol.flags |= BSF_FUNCTION;
      som_symbol_data (sym)->tc_data.ap.hppa_priv_level =
        sym->symbol.value & PRIV_LEVEL_MASK;
      sym->symbol.value &= ~PRIV_LEVEL_MASK;
      break;

    case ST_STUB:
    case ST_CODE:
    case ST_PRI_PROG:
    case ST_SEC_PROG:
      som_symbol_data (sym)->tc_data.ap.hppa_priv_level =
        sym->symbol.value & PRIV_LEVEL_MASK;
      sym->symbol.value &= ~PRIV_LEVEL_MASK;
      if (symbol_scope == SS_UNSAT)
        sym->symbol.flags |= BSF_FUNCTION;
      break;

    default:
      break;
    }
}

static void
set_section_for_scope (som_symbol_type *sym, unsigned int symbol_type)
{
  if (symbol_type != ST_STORAGE)
    sym->symbol.section = bfd_und_section_ptr;
  else
    sym->symbol.section = bfd_com_section_ptr;
}

static void
process_symbol_scope (bfd *abfd, som_symbol_type *sym,
                     struct som_external_symbol_dictionary_record *bufp,
                     unsigned int symbol_type, unsigned int symbol_scope)
{
  switch (symbol_scope)
    {
    case SS_EXTERNAL:
      set_section_for_scope (sym, symbol_type);
      sym->symbol.flags |= (BSF_EXPORT | BSF_GLOBAL);
      break;

    case SS_UNSAT:
      set_section_for_scope (sym, symbol_type);
      break;

    case SS_UNIVERSAL:
      sym->symbol.flags |= (BSF_EXPORT | BSF_GLOBAL);
      sym->symbol.section = bfd_section_from_som_symbol (abfd, bufp);
      sym->symbol.value -= sym->symbol.section->vma;
      break;

    case SS_LOCAL:
      sym->symbol.flags |= BSF_LOCAL;
      sym->symbol.section = bfd_section_from_som_symbol (abfd, bufp);
      sym->symbol.value -= sym->symbol.section->vma;
      break;

    default:
      sym->symbol.section = bfd_und_section_ptr;
      break;
    }
}

static void
process_symbol_flags (som_symbol_type *sym, unsigned int flags)
{
  if (flags & SOM_SYMBOL_SECONDARY_DEF)
    sym->symbol.flags |= BSF_WEAK;

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
}

/* Canonicalize a SOM symbol table.  Return the number of entries
   in the symbol table.  */

static long
som_canonicalize_symtab (bfd *abfd, asymbol **location)
{
  if (!som_slurp_symbol_table (abfd))
    return -1;

  int symbol_count = bfd_get_symcount (abfd);
  som_symbol_type *symbase = obj_som_symtab (abfd);

  for (int i = 0; i < symbol_count; i++)
    location[i] = &symbase[i].symbol;

  location[symbol_count] = NULL;
  return symbol_count;
}

/* Make a SOM symbol.  There is nothing special to do here.  */

static asymbol *
som_make_empty_symbol (bfd *abfd)
{
  size_t amt = sizeof (som_symbol_type);
  som_symbol_type *new_symbol_type = bfd_zalloc (abfd, amt);

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
  FILE *file = (FILE *) afile;

  switch (how)
    {
    case bfd_print_symbol_name:
      fprintf (file, "%s", symbol->name);
      break;
    case bfd_print_symbol_more:
      fprintf (file, "som %08" PRIx64 " %x",
	       (uint64_t) symbol->value, symbol->flags);
      break;
    case bfd_print_symbol_all:
      {
	const char *section_name;

	section_name = symbol->section ? symbol->section->name : "(*none*)";
	bfd_print_symbol_vandf (abfd, (void *) file, symbol);
	fprintf (file, " %s\t%s", section_name, symbol->name);
	break;
      }
    }
}

static bool
som_bfd_is_local_label_name (bfd *abfd ATTRIBUTE_UNUSED,
			     const char *name)
{
  const char LOCAL_LABEL_PREFIX = 'L';
  const char LOCAL_LABEL_SUFFIX = '$';
  
  return name[0] == LOCAL_LABEL_PREFIX && name[1] == LOCAL_LABEL_SUFFIX;
}

/* Count or process variable-length SOM fixup records.

   To avoid code duplication we use this code both to compute the number
   of relocations requested by a stream, and to internalize the stream.

   When computing the number of relocations requested by a stream the
   variables rptr, section, and symbols have no meaning.

   Return the number of relocations requested by the fixup stream.  When
   not just counting

   This needs at least two or three more passes to get it cleaned up.  */

static unsigned int
som_set_reloc_info (unsigned char *fixup,
		    unsigned int end,
		    arelent *internal_relocs,
		    asection *section,
		    asymbol **symbols,
		    unsigned int symcount,
		    bool just_count)
{
  unsigned int deallocate_contents = 0;
  unsigned char *end_fixups = &fixup[end];
  int variables[26], stack[20], count, prev_fixup, *sp, saved_unwind_bits;
  arelent *rptr = internal_relocs;
  unsigned int offset = 0;

#define	var(c)		variables[(c) - 'A']
#define	push(v)		(*sp++ = (v))
#define	pop()		(*--sp)
#define	emptystack()	(sp == stack)
#define STACK_SIZE 20
#define VARIABLES_SIZE 26

  som_initialize_reloc_queue (reloc_queue);
  memset (variables, 0, sizeof (variables));
  memset (stack, 0, sizeof (stack));
  count = 0;
  prev_fixup = 0;
  saved_unwind_bits = 0;
  sp = stack;

  while (fixup < end_fixups)
    {
      unsigned char *save_fixup = fixup;
      unsigned int op = *fixup++;
      const struct fixup_format *fp = &som_fixup_formats[op];

      if (*fp->format == 'P')
	{
	  if (!reloc_queue[fp->D].reloc)
	    continue;

	  fixup = reloc_queue[fp->D].reloc;
	  som_reloc_queue_fix (reloc_queue, fp->D);
	  prev_fixup = 1;
	  op = *fixup++;
	  fp = &som_fixup_formats[op];
	}

      if (!just_count)
	initialize_relocation(rptr, op, offset);

      var ('L') = 0;
      var ('D') = fp->D;
      var ('U') = saved_unwind_bits;

      process_format_string(fp->format, fixup, end_fixups, variables, 
                           stack, &sp, rptr, op, symbols, symcount,
                           just_count, &offset, &saved_unwind_bits);

      if (prev_fixup)
	{
	  fixup = save_fixup + 1;
	  prev_fixup = 0;
	}
      else if (fixup > save_fixup + 1)
	som_reloc_queue_insert (save_fixup, fixup - save_fixup, reloc_queue);

      if (should_process_relocation(op))
	{
	  if (!just_count)
	    finalize_relocation(rptr, op, variables, section, offset);
	  rptr++;
	  count++;
	  memset (variables, 0, sizeof (variables));
	  memset (stack, 0, sizeof (stack));
	}
    }

  if (deallocate_contents)
    {
      free (section->contents);
      section->contents = NULL;
    }

  return count;

#undef var
#undef push
#undef pop
#undef emptystack
}

static void initialize_relocation(arelent *rptr, unsigned int op, unsigned int offset)
{
  if (som_hppa_howto_table[op].type != R_NO_RELOCATION
      && som_hppa_howto_table[op].type != R_DATA_OVERRIDE)
    {
      rptr->address = offset;
      rptr->howto = &som_hppa_howto_table[op];
      rptr->addend = 0;
      rptr->sym_ptr_ptr = &bfd_abs_section_ptr->symbol;
    }
}

static bool should_process_relocation(unsigned int op)
{
  return som_hppa_howto_table[op].type != R_DATA_OVERRIDE
         && som_hppa_howto_table[op].type != R_NO_RELOCATION;
}

static void process_format_string(const char *format, unsigned char *&fixup,
                                 unsigned char *end_fixups, int *variables,
                                 int *stack, int **sp, arelent *rptr,
                                 unsigned int op, asymbol **symbols,
                                 unsigned int symcount, bool just_count,
                                 unsigned int *offset, int *saved_unwind_bits)
{
  const char *cp = format;
  
  while (*cp)
    {
      unsigned int varname = *cp++;
      int value = compute_rhs_value(&cp, fixup, end_fixups, variables, stack, sp, varname);
      variables[varname - 'A'] = value;
      handle_side_effects(varname, value, offset, rptr, op, symbols, symcount,
                         just_count, variables, saved_unwind_bits);
    }
}

static int compute_rhs_value(const char **cp, unsigned char *&fixup,
                            unsigned char *end_fixups, int *variables,
                            int *stack, int **sp, unsigned int varname)
{
  do
    {
      int c = *(*cp)++;
      
      if (ISUPPER (c))
        push_stack(sp, variables[c - 'A']);
      else if (ISLOWER (c))
        push_stack(sp, read_fixup_data(&fixup, end_fixups, c, varname));
      else if (ISDIGIT (c))
        push_stack(sp, read_decimal(cp, c));
      else
        process_operator(c, sp);
    }
  while (**cp && **cp != '=');
  
  (*cp)++;
  return pop_stack(sp);
}

static void push_stack(int **sp, int value)
{
  *(*sp)++ = value;
}

static int pop_stack(int **sp)
{
  return *--(*sp);
}

static int read_fixup_data(unsigned char **fixup, unsigned char *end_fixups,
                          int c, unsigned int varname)
{
  int bits = (c - 'a') * 8;
  unsigned int v = 0;
  
  for (; c > 'a' && *fixup < end_fixups; --c)
    v = (v << 8) | *(*fixup)++;
    
  if (varname == 'V')
    v = sign_extend (v, bits);
    
  return v;
}

static int read_decimal(const char **cp, int c)
{
  int v = c - '0';
  while (ISDIGIT (**cp))
    v = (v * 10) + (*(*cp)++ - '0');
  return v;
}

static void process_operator(int c, int **sp)
{
  int v = pop_stack(sp);
  int v2 = pop_stack(sp);
  
  switch (c)
    {
    case '+':
      push_stack(sp, v2 + v);
      break;
    case '*':
      push_stack(sp, v2 * v);
      break;
    case '<':
      push_stack(sp, v2 << v);
      break;
    default:
      abort ();
    }
}

static void handle_side_effects(unsigned int varname, int value,
                               unsigned int *offset, arelent *rptr,
                               unsigned int op, asymbol **symbols,
                               unsigned int symcount, bool just_count,
                               int *variables, int *saved_unwind_bits)
{
  switch (varname)
    {
    case 'L':
      *offset += value;
      break;
    case 'S':
      handle_symbol_assignment(rptr, symbols, symcount, value, just_count);
      break;
    case 'R':
      handle_argument_relocation(rptr, op, value, just_count);
      break;
    case 'O':
      handle_linker_expression(op, value);
      break;
    case 'U':
      *saved_unwind_bits = variables['U' - 'A'];
      break;
    default:
      break;
    }
}

static void handle_symbol_assignment(arelent *rptr, asymbol **symbols,
                                    unsigned int symcount, int value,
                                    bool just_count)
{
  if (!just_count && symbols != NULL && (unsigned int) value < symcount)
    rptr->sym_ptr_ptr = &symbols[value];
}

static void handle_argument_relocation(arelent *rptr, unsigned int op,
                                      int value, bool just_count)
{
  if (just_count)
    return;
    
  unsigned int tmp = value;
  rptr->addend = 0;

  if (is_simple_call_encoding(op))
    encode_simple_argument(rptr, tmp);
  else
    encode_complex_argument(rptr, tmp);
    
  rptr->addend = HPPA_R_ADDEND (rptr->addend, 0);
}

static bool is_simple_call_encoding(unsigned int op)
{
  return (som_hppa_howto_table[op].type == R_PCREL_CALL && R_PCREL_CALL + 10 > op)
         || (som_hppa_howto_table[op].type == R_ABS_CALL && R_ABS_CALL + 10 > op);
}

static void encode_simple_argument(arelent *rptr, unsigned int tmp)
{
  if (tmp > 4)
    {
      tmp -= 5;
      rptr->addend |= 1;
    }
    
  if (tmp == 4)
    rptr->addend |= 1 << 8 | 1 << 6 | 1 << 4 | 1 << 2;
  else if (tmp == 3)
    rptr->addend |= 1 << 8 | 1 << 6 | 1 << 4;
  else if (tmp == 2)
    rptr->addend |= 1 << 8 | 1 << 6;
  else if (tmp == 1)
    rptr->addend |= 1 << 8;
}

static void encode_complex_argument(arelent *rptr, unsigned int tmp)
{
  rptr->addend = tmp & 0x3;
  tmp >>= 2;
  
  encode_argument_part(rptr, tmp / 10, tmp % 10, 6);
  encode_argument_part(rptr, tmp % 10 / 3, tmp % 10 % 3, 2);
}

static void encode_argument_part(arelent *rptr, unsigned int part1,
                                unsigned int part2, int shift)
{
  if (part1 == 9)
    rptr->addend += (0xe << shift);
  else
    {
      unsigned int tmp2 = part1 / 3;
      unsigned int tmp1 = part1 - tmp2 * 3;
      rptr->addend += (tmp2 << (shift + 2)) + (tmp1 << shift);
    }
}

static void handle_linker_expression(unsigned int op, int value)
{
  const int *subop;
  
  switch (op)
    {
    case R_COMP1:
      subop = comp1_opcodes;
      break;
    case R_COMP2:
      subop = comp2_opcodes;
      break;
    case R_COMP3:
      subop = comp3_opcodes;
      break;
    default:
      abort ();
    }
    
  while (*subop <= (unsigned char) value)
    ++subop;
  --subop;
}

static void finalize_relocation(arelent *rptr, unsigned int op,
                               int *variables, asection *section,
                               unsigned int offset)
{
  if (som_hppa_howto_table[op].type == R_ENTRY)
    rptr->addend = variables['T' - 'A'];
  else if (som_hppa_howto_table[op].type == R_EXIT)
    rptr->addend = variables['U' - 'A'];
  else if (som_hppa_howto_table[op].type == R_PCREL_CALL
           || som_hppa_howto_table[op].type == R_ABS_CALL)
    ;
  else if (som_hppa_howto_table[op].type == R_DATA_ONE_SYMBOL)
    handle_data_one_symbol(rptr, variables, section, offset);
  else
    rptr->addend = variables['V' - 'A'];
}

static void handle_data_one_symbol(arelent *rptr, int *variables,
                                  asection *section, unsigned int offset)
{
  rptr->addend = variables['V' - 'A'];
  
  if (rptr->addend == 0 && (section->flags & SEC_HAS_CONTENTS) != 0)
    {
      if (!section->contents)
        {
          if (!load_section_contents(section))
            return;
        }
        
      int var_l = variables['L' - 'A'];
      if (offset - var_l <= section->size
          && section->size - (offset - var_l) >= 4)
        rptr->addend = bfd_get_32 (section->owner,
                                  (section->contents + offset - var_l));
    }
}

static bool load_section_contents(asection *section)
{
  bfd_byte *contents;
  if (!bfd_malloc_and_get_section (section->owner, section, &contents))
    {
      free (contents);
      return false;
    }
  section->contents = contents;
  return true;
}

/* Read in the relocs (aka fixups in SOM terms) for a section.

   som_get_reloc_upper_bound calls this routine with JUST_COUNT
   set to TRUE to indicate it only needs a count of the number
   of actual relocations.  */

static bool
read_external_relocs(bfd *abfd, asection *section, unsigned int fixup_stream_size)
{
    size_t amt = fixup_stream_size;
    unsigned char *external_relocs;
    
    if (bfd_seek(abfd, obj_som_reloc_filepos(abfd) + section->rel_filepos, SEEK_SET) != 0)
        return false;
    
    external_relocs = _bfd_malloc_and_read(abfd, amt, amt);
    if (external_relocs == NULL)
        return false;
    
    section->reloc_count = som_set_reloc_info(external_relocs, fixup_stream_size,
                                             NULL, NULL, NULL, 0, true);
    som_section_data(section)->reloc_stream = external_relocs;
    return true;
}

static bool
allocate_internal_relocs(bfd *abfd, unsigned int num_relocs, arelent **internal_relocs)
{
    size_t amt;
    
    if (_bfd_mul_overflow(num_relocs, sizeof(arelent), &amt))
    {
        bfd_set_error(bfd_error_file_too_big);
        return false;
    }
    
    *internal_relocs = bfd_zalloc(abfd, amt);
    return (*internal_relocs != NULL);
}

static void
process_and_save_relocs(asection *section, unsigned char *external_relocs,
                       unsigned int fixup_stream_size, arelent *internal_relocs,
                       asymbol **symbols, bfd *abfd)
{
    som_set_reloc_info(external_relocs, fixup_stream_size, internal_relocs,
                      section, symbols, bfd_get_symcount(abfd), false);
    
    free(external_relocs);
    som_section_data(section)->reloc_stream = NULL;
    section->relocation = internal_relocs;
}

static bool
som_slurp_reloc_table(bfd *abfd, asection *section, asymbol **symbols, bool just_count)
{
    unsigned int fixup_stream_size;
    unsigned char *external_relocs;
    arelent *internal_relocs;
    unsigned int num_relocs;
    
    #define UNINITIALIZED_RELOC_COUNT ((unsigned)-1)
    
    fixup_stream_size = som_section_data(section)->reloc_size;
    
    if (section->reloc_count == 0)
        return true;
    
    if (section->reloc_count == UNINITIALIZED_RELOC_COUNT)
    {
        if (!read_external_relocs(abfd, section, fixup_stream_size))
            return false;
    }
    
    if (just_count)
        return true;
    
    if (section->relocation != NULL)
        return true;
    
    num_relocs = section->reloc_count;
    external_relocs = som_section_data(section)->reloc_stream;
    
    if (!allocate_internal_relocs(abfd, num_relocs, &internal_relocs))
        return false;
    
    process_and_save_relocs(section, external_relocs, fixup_stream_size,
                           internal_relocs, symbols, abfd);
    
    return true;
}

/* Return the number of bytes required to store the relocation
   information associated with the given section.  */

static long
som_get_reloc_upper_bound (bfd *abfd, sec_ptr asect)
{
  const size_t ARELENT_PTR_SIZE = sizeof (arelent *);
  
  if (!(asect->flags & SEC_RELOC))
    return ARELENT_PTR_SIZE;
    
  if (!som_slurp_reloc_table (abfd, asect, NULL, true))
    return -1;
    
  return (asect->reloc_count + 1) * ARELENT_PTR_SIZE;
}

/* Convert relocations from SOM (external) form into BFD internal
   form.  Return the number of relocations.  */

static long
som_canonicalize_reloc (bfd *abfd,
			sec_ptr section,
			arelent **relptr,
			asymbol **symbols)
{
  arelent *tblptr;
  int count;

  if (! som_slurp_reloc_table (abfd, section, symbols, false))
    return -1;

  count = section->reloc_count;
  tblptr = section->relocation;

  while (count--)
    *relptr++ = tblptr++;

  *relptr = NULL;
  return section->reloc_count;
}

extern const bfd_target hppa_som_vec;

/* A hook to set up object file dependent section information.  */

static bool
som_new_section_hook (bfd *abfd, asection *newsect)
{
  const size_t SECTION_DATA_SIZE = sizeof (struct som_section_data_struct);
  const unsigned int DEFAULT_ALIGNMENT_POWER = 3;

  newsect->used_by_bfd = bfd_zalloc (abfd, SECTION_DATA_SIZE);
  if (!newsect->used_by_bfd)
    return false;

  newsect->alignment_power = DEFAULT_ALIGNMENT_POWER;

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
  struct som_symbol *input_symbol = (struct som_symbol *) isymbol;
  struct som_symbol *output_symbol = (struct som_symbol *) osymbol;

  if (ibfd->xvec->flavour != bfd_target_som_flavour
      || obfd->xvec->flavour != bfd_target_som_flavour)
    return false;

  output_symbol->tc_data.ap.hppa_arg_reloc =
    input_symbol->tc_data.ap.hppa_arg_reloc;

  return true;
}

/* Copy any private info we understand from the input section
   to the output section.  */

static bool
is_valid_som_section(bfd *ibfd, bfd *obfd, asection *isection)
{
    return ibfd->xvec->flavour == bfd_target_som_flavour
        && obfd->xvec->flavour == bfd_target_som_flavour
        && (som_is_space(isection) || som_is_subspace(isection));
}

static bool
allocate_copy_data(bfd *obfd, asection *osection)
{
    size_t amt = sizeof(struct som_copyable_section_data_struct);
    som_section_data(osection)->copy_data = bfd_zalloc(obfd, amt);
    return som_section_data(osection)->copy_data != NULL;
}

static void
copy_section_data(asection *osection, asection *isection)
{
    memcpy(som_section_data(osection)->copy_data,
           som_section_data(isection)->copy_data,
           sizeof(struct som_copyable_section_data_struct));
}

static bool
reparent_container(bfd *obfd, asection *osection)
{
    struct som_copyable_section_data_struct *copy_data = 
        som_section_data(osection)->copy_data;
    
    if (!copy_data->container)
        return true;
    
    if (copy_data->container->output_section)
    {
        copy_data->container = copy_data->container->output_section;
        return true;
    }
    
    _bfd_error_handler(_("%pB[%pA]: no output section for space %pA"),
                       obfd, osection, copy_data->container);
    return false;
}

static bool
som_bfd_copy_private_section_data(bfd *ibfd,
                                  asection *isection,
                                  bfd *obfd,
                                  asection *osection,
                                  struct bfd_link_info *link_info)
{
    if (link_info != NULL || !is_valid_som_section(ibfd, obfd, isection))
        return true;
    
    if (!allocate_copy_data(obfd, osection))
        return false;
    
    copy_section_data(osection, isection);
    
    return reparent_container(obfd, osection);
}

/* Copy any private info we understand from the input bfd
   to the output bfd.  */

static bool
is_som_flavour(bfd *bfd_file)
{
  return bfd_file->xvec->flavour == bfd_target_som_flavour;
}

static bool
allocate_exec_data(bfd *obfd)
{
  obj_som_exec_data(obfd) = bfd_zalloc(obfd, (bfd_size_type) sizeof(struct som_exec_data));
  return obj_som_exec_data(obfd) != NULL;
}

static void
copy_exec_data(bfd *obfd, bfd *ibfd)
{
  memcpy(obj_som_exec_data(obfd), obj_som_exec_data(ibfd), sizeof(struct som_exec_data));
}

static bool
som_bfd_copy_private_bfd_data(bfd *ibfd, bfd *obfd)
{
  if (!is_som_flavour(ibfd) || !is_som_flavour(obfd))
    return true;

  if (!allocate_exec_data(obfd))
    return false;

  copy_exec_data(obfd, ibfd);
  return true;
}

/* Display the SOM header.  */

static void
print_auxhdr_flags(FILE *f, struct som_aux_id* auxhdr)
{
    fprintf(f, "  flags              ");
    if (auxhdr->mandatory)
        fprintf(f, "mandatory ");
    if (auxhdr->copy)
        fprintf(f, "copy ");
    if (auxhdr->append)
        fprintf(f, "append ");
    if (auxhdr->ignore)
        fprintf(f, "ignore ");
    fprintf(f, "\n");
}

static void
print_auxhdr_info(FILE *f, struct som_aux_id* auxhdr)
{
    fprintf(f, "  type               %#x\n", auxhdr->type);
    fprintf(f, "  length             %#x\n", auxhdr->length);
}

static void
print_exec_section_info(FILE *f, const char *section_name, long size, long mem_offset, long file_offset)
{
    fprintf(f, "  %s size          %#lx\n", section_name, size);
    fprintf(f, "  %s memory offset %#lx\n", section_name, mem_offset);
    fprintf(f, "  %s file offset   %#lx\n", section_name, file_offset);
}

static void
print_exec_header_details(FILE *f, struct som_exec_auxhdr *exec_header)
{
    print_exec_section_info(f, "text", 
                           (long) exec_header->exec_tsize,
                           (long) exec_header->exec_tmem,
                           (long) exec_header->exec_tfile);
    
    print_exec_section_info(f, "data",
                           (long) exec_header->exec_dsize,
                           (long) exec_header->exec_dmem,
                           (long) exec_header->exec_dfile);
    
    fprintf(f, "  bss size           %#lx\n", (long) exec_header->exec_bsize);
    fprintf(f, "  entry point        %#lx\n", (long) exec_header->exec_entry);
    fprintf(f, "  loader flags       %#lx\n", (long) exec_header->exec_flags);
    fprintf(f, "  bss initializer    %#lx\n", (long) exec_header->exec_bfill);
}

static bool
som_bfd_print_private_bfd_data(bfd *abfd, void *farg)
{
    struct som_exec_auxhdr *exec_header;
    FILE *f;

    f = (FILE *) farg;
    exec_header = obj_som_exec_hdr(abfd);
    
    if (exec_header)
    {
        fprintf(f, _("\nExec Auxiliary Header\n"));
        print_auxhdr_flags(f, &exec_header->som_auxhdr);
        print_auxhdr_info(f, &exec_header->som_auxhdr);
        print_exec_header_details(f, exec_header);
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
  if (som_section_data (section)->copy_data == NULL)
    {
      size_t amt = sizeof (struct som_copyable_section_data_struct);

      som_section_data (section)->copy_data = bfd_zalloc (section->owner, amt);
      if (som_section_data (section)->copy_data == NULL)
	return false;
    }
  
  struct som_copyable_section_data_struct *copy_data = som_section_data (section)->copy_data;
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
  struct som_copyable_section_data_struct *copy_data;
  
  copy_data = som_section_data (section)->copy_data;
  
  if (copy_data == NULL)
    {
      size_t amt = sizeof (struct som_copyable_section_data_struct);
      copy_data = bfd_zalloc (section->owner, amt);
      if (copy_data == NULL)
	return false;
      som_section_data (section)->copy_data = copy_data;
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

void
bfd_som_set_symbol_type (asymbol *symbol, unsigned int type)
{
  som_symbol_data (symbol)->som_type = type;
}

/* Attach an auxiliary header to the BFD backend so that it may be
   written into the object file.  */

#define ALIGNMENT_SIZE 4
#define HEADER_SIZE_OFFSET 4

static int calculate_padding(size_t len)
{
    if (len % ALIGNMENT_SIZE == 0)
        return 0;
    return ALIGNMENT_SIZE - (len % ALIGNMENT_SIZE);
}

static size_t calculate_allocation_size(size_t string_len)
{
    int pad = calculate_padding(string_len);
    return sizeof(struct som_string_auxhdr) + string_len + pad;
}

static bool setup_string_header(void *header, int type, size_t string_len, const char *string)
{
    struct som_string_auxhdr *hdr = (struct som_string_auxhdr *)header;
    int pad = calculate_padding(string_len);
    
    hdr->header_id.type = type;
    hdr->header_id.length = HEADER_SIZE_OFFSET + string_len + pad;
    hdr->string_length = string_len;
    memcpy(hdr->string, string, string_len);
    memset(hdr->string + string_len, 0, pad);
    
    return true;
}

static bool attach_version_aux_hdr(bfd *abfd, char *string)
{
    size_t len = strlen(string);
    size_t amt = calculate_allocation_size(len);
    
    obj_som_version_hdr(abfd) = bfd_zalloc(abfd, amt);
    if (!obj_som_version_hdr(abfd))
        return false;
    
    return setup_string_header(obj_som_version_hdr(abfd), VERSION_AUX_ID, len, string);
}

static bool attach_copyright_aux_hdr(bfd *abfd, char *string)
{
    size_t len = strlen(string);
    size_t amt = calculate_allocation_size(len);
    
    obj_som_copyright_hdr(abfd) = bfd_zalloc(abfd, amt);
    if (!obj_som_copyright_hdr(abfd))
        return false;
    
    return setup_string_header(obj_som_copyright_hdr(abfd), COPYRIGHT_AUX_ID, len, string);
}

bool
bfd_som_attach_aux_hdr (bfd *abfd, int type, char *string)
{
    if (type == VERSION_AUX_ID)
        return attach_version_aux_hdr(abfd, string);
    
    if (type == COPYRIGHT_AUX_ID)
        return attach_copyright_aux_hdr(abfd, string);
    
    return true;
}

/* Attach a compilation unit header to the BFD backend so that it may be
   written into the object file.  */

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

  if (!duplicate_string_field(abfd, name, &n->name.name))
    return false;
  
  if (!duplicate_string_field(abfd, language_name, &n->language_name.name))
    return false;
  
  if (!duplicate_string_field(abfd, product_id, &n->product_id.name))
    return false;
  
  if (!duplicate_string_field(abfd, version_id, &n->version_id.name))
    return false;

  obj_som_compilation_unit (abfd) = n;

  return true;
}

static bool
duplicate_string_field(bfd *abfd, const char *source, char **destination)
{
  if (source == NULL)
    return true;
    
  bfd_size_type len = strlen(source) + 1;
  *destination = bfd_alloc(abfd, len);
  
  if (*destination == NULL)
    return false;
    
  strcpy(*destination, source);
  return true;
}

static bool is_valid_section_read(sec_ptr section, file_ptr offset, bfd_size_type count)
{
    if (count == 0 || ((section->flags & SEC_HAS_CONTENTS) == 0))
        return true;
    
    return (bfd_size_type)(offset + count) <= section->size;
}

static bool perform_section_read(bfd *abfd, sec_ptr section, void *location, 
                                 file_ptr offset, bfd_size_type count)
{
    if (bfd_seek(abfd, section->filepos + offset, SEEK_SET) != 0)
        return false;
    
    return bfd_read(location, count, abfd) == count;
}

static bool som_get_section_contents(bfd *abfd, sec_ptr section, void *location,
                                     file_ptr offset, bfd_size_type count)
{
    if (!is_valid_section_read(section, offset, count))
        return count == 0 || ((section->flags & SEC_HAS_CONTENTS) == 0);
    
    return perform_section_read(abfd, section, location, offset, count);
}

static bool
initialize_output_if_needed(bfd *abfd)
{
  if (abfd->output_has_begun)
    return true;
    
  som_prep_headers(abfd);
  abfd->output_has_begun = true;
  som_begin_writing(abfd);
  return true;
}

static bool
is_writable_subspace(sec_ptr section)
{
  return som_is_subspace(section) && 
         (section->flags & SEC_HAS_CONTENTS) != 0;
}

static bool
write_section_data(bfd *abfd, sec_ptr section, const void *location,
                   file_ptr offset, bfd_size_type count)
{
  offset += som_section_data(section)->subspace_dict->file_loc_init_value;
  
  if (bfd_seek(abfd, offset, SEEK_SET) != 0)
    return false;
    
  return bfd_write(location, count, abfd) == count;
}

static bool
som_set_section_contents(bfd *abfd,
                        sec_ptr section,
                        const void *location,
                        file_ptr offset,
                        bfd_size_type count)
{
  initialize_output_if_needed(abfd);
  
  if (!is_writable_subspace(section))
    return true;
    
  return write_section_data(abfd, section, location, offset, count);
}

static bool
som_set_arch_mach (bfd *abfd,
		   enum bfd_architecture arch,
		   unsigned long machine)
{
  return bfd_default_set_arch_mach (abfd, arch, machine);
}

static bool is_valid_function_symbol(som_symbol_type *q, asection *section, bfd_vma offset, bfd_vma low_func)
{
    return q->som_type == SYMBOL_TYPE_ENTRY
           && q->symbol.section == section
           && q->symbol.value >= low_func
           && q->symbol.value <= offset;
}

static asymbol* find_function_from_symbols(asymbol **symbols, asection *section, bfd_vma offset)
{
    asymbol *func = NULL;
    bfd_vma low_func = 0;
    asymbol **p;

    for (p = symbols; *p != NULL; p++)
    {
        som_symbol_type *q = (som_symbol_type *) *p;
        
        if (is_valid_function_symbol(q, section, offset, low_func))
        {
            func = (asymbol *) q;
            low_func = q->symbol.value;
        }
    }
    
    return func;
}

static void set_function_info(const char **filename_ptr, const char **functionname_ptr, 
                              unsigned int *line_ptr, asymbol *func)
{
    *filename_ptr = NULL;
    *functionname_ptr = bfd_asymbol_name(func);
    *line_ptr = 0;
}

static bool som_find_nearest_line(bfd *abfd,
                                  asymbol **symbols,
                                  asection *section,
                                  bfd_vma offset,
                                  const char **filename_ptr,
                                  const char **functionname_ptr,
                                  unsigned int *line_ptr,
                                  unsigned int *discriminator_ptr)
{
    bool found;
    asymbol *func;

    if (discriminator_ptr)
        *discriminator_ptr = 0;

    if (!_bfd_stab_section_find_nearest_line(abfd, symbols, section, offset,
                                             &found, filename_ptr,
                                             functionname_ptr, line_ptr,
                                             &somdata(abfd).line_info))
        return false;

    if (found)
        return true;

    if (symbols == NULL)
        return false;

    func = find_function_from_symbols(symbols, section, offset);
    
    if (func == NULL)
        return false;

    set_function_info(filename_ptr, functionname_ptr, line_ptr, func);
    
    return true;
}

static int
som_sizeof_headers (bfd *abfd ATTRIBUTE_UNUSED,
		    struct bfd_link_info *info ATTRIBUTE_UNUSED)
{
  _bfd_error_handler (_("som_sizeof_headers unimplemented"));
  abort ();
  return 0;
}

/* Return the single-character symbol type corresponding to
   SOM section S, or '?' for an unknown SOM section.  */

static char
som_section_type (const char *s)
{
  const struct section_to_type *t;

  for (t = &stt[0]; t->section; t++)
    if (!strcmp (s, t->section))
      return t->type;
  return '?';
}

static char get_weak_symbol_class(asymbol *symbol)
{
    if (symbol->flags & BSF_OBJECT)
        return (symbol->flags & BSF_GLOBAL) ? 'V' : 'v';
    return (symbol->flags & BSF_GLOBAL) ? 'W' : 'w';
}

static char get_section_symbol_class(asymbol *symbol)
{
    if (bfd_is_abs_section(symbol->section) ||
        (som_symbol_data(symbol) != NULL &&
         som_symbol_data(symbol)->som_type == SYMBOL_TYPE_ABSOLUTE))
        return 'a';
    
    if (symbol->section)
        return som_section_type(symbol->section->name);
    
    return '?';
}

static char apply_global_flag(char c, asymbol *symbol)
{
    if (symbol->flags & BSF_GLOBAL)
        return TOUPPER(c);
    return c;
}

static int
som_decode_symclass(asymbol *symbol)
{
    if (symbol == NULL || symbol->section == NULL)
        return '?';

    if (bfd_is_com_section(symbol->section))
        return 'C';
    
    if (bfd_is_und_section(symbol->section))
    {
        if (symbol->flags & BSF_WEAK)
            return (symbol->flags & BSF_OBJECT) ? 'v' : 'w';
        return 'U';
    }
    
    if (bfd_is_ind_section(symbol->section))
        return 'I';
    
    if (symbol->flags & BSF_WEAK)
        return get_weak_symbol_class(symbol);
    
    if (!(symbol->flags & (BSF_GLOBAL | BSF_LOCAL)))
        return '?';
    
    char c = get_section_symbol_class(symbol);
    return apply_global_flag(c, symbol);
}

/* Return information about SOM symbol SYMBOL in RET.  */

static void
som_get_symbol_info (bfd *ignore_abfd ATTRIBUTE_UNUSED,
		     asymbol *symbol,
		     symbol_info *ret)
{
  ret->type = som_decode_symclass (symbol);
  ret->value = (ret->type != 'U') ? symbol->value + symbol->section->vma : 0;
  ret->name = symbol->name;
}

/* Count the number of symbols in the archive symbol table.  Necessary
   so that we can allocate space for all the carsyms at once.  */

static bool
read_hash_table(bfd *abfd, struct som_lst_header *lst_header, unsigned char **hash_table)
{
  size_t amt;
  
  if (_bfd_mul_overflow(lst_header->hash_size, 4, &amt))
    {
      bfd_set_error(bfd_error_file_too_big);
      return false;
    }
  
  *hash_table = _bfd_malloc_and_read(abfd, amt, amt);
  return (*hash_table != NULL || lst_header->hash_size == 0);
}

static bool
read_symbol_at_offset(bfd *abfd, file_ptr lst_filepos, unsigned int offset,
                      struct som_external_lst_symbol_record *symbol)
{
  if (bfd_seek(abfd, lst_filepos + offset, SEEK_SET) != 0)
    return false;
    
  size_t amt = sizeof(*symbol);
  return bfd_read(symbol, amt, abfd) == amt;
}

static bool
validate_next_entry(unsigned int next_entry, unsigned int current_offset,
                   size_t symbol_size)
{
  if (next_entry == 0)
    return true;
    
  if (next_entry < current_offset + symbol_size)
    {
      bfd_set_error(bfd_error_bad_value);
      return false;
    }
  return true;
}

static bool
count_chain_symbols(bfd *abfd, file_ptr lst_filepos, unsigned int hash_val,
                   symindex *count)
{
  struct som_external_lst_symbol_record ext_lst_symbol;
  
  if (hash_val == 0)
    return true;
    
  if (!read_symbol_at_offset(abfd, lst_filepos, hash_val, &ext_lst_symbol))
    return false;
    
  (*count)++;
  
  while (1)
    {
      unsigned int next_entry = bfd_getb32(ext_lst_symbol.next_entry);
      
      if (!validate_next_entry(next_entry, hash_val, sizeof(ext_lst_symbol)))
        return false;
        
      if (next_entry == 0)
        break;
        
      hash_val = next_entry;
      
      if (!read_symbol_at_offset(abfd, lst_filepos, next_entry, &ext_lst_symbol))
        return false;
        
      (*count)++;
    }
    
  return true;
}

static bool
som_bfd_count_ar_symbols(bfd *abfd,
                        struct som_lst_header *lst_header,
                        symindex *count)
{
  unsigned int i;
  unsigned char *hash_table = NULL;
  file_ptr lst_filepos;
  
  lst_filepos = bfd_tell(abfd) - sizeof(struct som_external_lst_header);
  
  if (!read_hash_table(abfd, lst_header, &hash_table))
    return false;
  
  *count = 0;
  
  for (i = 0; i < lst_header->hash_size; i++)
    {
      unsigned int hash_val = bfd_getb32(hash_table + 4 * i);
      
      if (!count_chain_symbols(abfd, lst_filepos, hash_val, count))
        {
          free(hash_table);
          return false;
        }
    }
    
  free(hash_table);
  return true;
}

/* Fill in the canonical archive symbols (SYMS) from the archive described
   by ABFD and LST_HEADER.  */

static bool
read_hash_table(bfd *abfd, struct som_lst_header *lst_header, unsigned char **hash_table)
{
  size_t amt;
  
  if (_bfd_mul_overflow(lst_header->hash_size, 4, &amt))
    {
      bfd_set_error(bfd_error_file_too_big);
      return false;
    }
  
  *hash_table = _bfd_malloc_and_read(abfd, amt, amt);
  return (*hash_table != NULL || lst_header->hash_size == 0);
}

static bool
read_som_dictionary(bfd *abfd, file_ptr lst_filepos, struct som_lst_header *lst_header,
                    struct som_external_som_entry **som_dict)
{
  size_t amt;
  
  if (bfd_seek(abfd, lst_filepos + lst_header->dir_loc, SEEK_SET) != 0)
    return false;
  
  if (_bfd_mul_overflow(lst_header->module_count,
                        sizeof(struct som_external_som_entry), &amt))
    {
      bfd_set_error(bfd_error_file_too_big);
      return false;
    }
  
  *som_dict = (struct som_external_som_entry *)_bfd_malloc_and_read(abfd, amt, amt);
  return (*som_dict != NULL || lst_header->module_count == 0);
}

static bool
read_symbol_name(bfd *abfd, file_ptr lst_filepos, unsigned int string_loc,
                 unsigned int name_offset, char **name)
{
  unsigned char ext_len[4];
  size_t len;
  
  if (bfd_seek(abfd, lst_filepos + string_loc + name_offset - 4, SEEK_SET) != 0)
    return false;
  
  if (bfd_read(&ext_len, 4, abfd) != 4)
    return false;
  
  len = bfd_getb32(ext_len);
  
  if (len == (size_t)-1)
    {
      bfd_set_error(bfd_error_no_memory);
      return false;
    }
  
  *name = (char *)_bfd_alloc_and_read(abfd, len + 1, len);
  if (!*name)
    return false;
  
  (*name)[len] = 0;
  return true;
}

static bool
set_file_offset(carsym *set, unsigned int som_index, unsigned int module_count,
                struct som_external_som_entry *som_dict)
{
  if (som_index >= module_count)
    {
      bfd_set_error(bfd_error_bad_value);
      return false;
    }
  
  set->file_offset = bfd_getb32(som_dict[som_index].location) - sizeof(struct ar_hdr);
  return true;
}

static bool
read_lst_symbol(bfd *abfd, file_ptr position,
                struct som_external_lst_symbol_record *lst_symbol)
{
  size_t amt = sizeof(*lst_symbol);
  
  if (bfd_seek(abfd, position, SEEK_SET) != 0)
    return false;
  
  return bfd_read(lst_symbol, amt, abfd) == amt;
}

static bool
process_symbol(bfd *abfd, file_ptr lst_filepos, unsigned int string_loc,
               struct som_external_lst_symbol_record *lst_symbol,
               struct som_lst_header *lst_header,
               struct som_external_som_entry *som_dict,
               carsym *set)
{
  char *name;
  unsigned int ndx;
  
  if (!read_symbol_name(abfd, lst_filepos, string_loc,
                        bfd_getb32(lst_symbol->name), &name))
    return false;
  
  set->name = name;
  
  ndx = bfd_getb32(lst_symbol->som_index);
  return set_file_offset(set, ndx, lst_header->module_count, som_dict);
}

static bool
process_chain(bfd *abfd, file_ptr lst_filepos, unsigned int hash_val,
              unsigned int string_loc, struct som_lst_header *lst_header,
              struct som_external_som_entry *som_dict, carsym **set)
{
  struct som_external_lst_symbol_record lst_symbol;
  unsigned int next_entry;
  
  if (!read_lst_symbol(abfd, lst_filepos + hash_val, &lst_symbol))
    return false;
  
  if (!process_symbol(abfd, lst_filepos, string_loc, &lst_symbol,
                      lst_header, som_dict, *set))
    return false;
  
  (*set)++;
  
  next_entry = bfd_getb32(lst_symbol.next_entry);
  while (next_entry != 0)
    {
      if (!read_lst_symbol(abfd, lst_filepos + next_entry, &lst_symbol))
        return false;
      
      if (!process_symbol(abfd, lst_filepos, string_loc, &lst_symbol,
                          lst_header, som_dict, *set))
        return false;
      
      (*set)++;
      next_entry = bfd_getb32(lst_symbol.next_entry);
    }
  
  return true;
}

static bool
som_bfd_fill_in_ar_symbols(bfd *abfd,
                          struct som_lst_header *lst_header,
                          carsym **syms)
{
  unsigned int i;
  carsym *set = syms[0];
  unsigned char *hash_table = NULL;
  struct som_external_som_entry *som_dict = NULL;
  file_ptr lst_filepos;
  unsigned int string_loc;
  bool result = false;
  
  lst_filepos = bfd_tell(abfd) - sizeof(struct som_external_lst_header);
  
  if (!read_hash_table(abfd, lst_header, &hash_table))
    goto cleanup;
  
  if (!read_som_dictionary(abfd, lst_filepos, lst_header, &som_dict))
    goto cleanup;
  
  string_loc = lst_header->string_loc;
  
  for (i = 0; i < lst_header->hash_size; i++)
    {
      unsigned int hash_val = bfd_getb32(hash_table + 4 * i);
      
      if (hash_val == 0)
        continue;
      
      if (!process_chain(abfd, lst_filepos, hash_val, string_loc,
                         lst_header, som_dict, &set))
        goto cleanup;
    }
  
  result = true;
  
cleanup:
  free(hash_table);
  free(som_dict);
  return result;
}

/* Read in the LST from the archive.  */

static bool
read_archive_name(bfd *abfd, char *nextname)
{
  size_t amt = 16;
  int bytes_read = bfd_read(nextname, amt, abfd);
  
  if (bytes_read == 0)
    return true;
  if (bytes_read != 16)
    return false;
    
  return bfd_seek(abfd, -16, SEEK_CUR) == 0;
}

static bool
has_symbol_table(const char *nextname, bfd *abfd)
{
  if (!startswith(nextname, "/               "))
  {
    abfd->has_armap = false;
    return true;
  }
  return false;
}

static bool
read_and_validate_ar_header(bfd *abfd, struct ar_hdr *ar_header)
{
  size_t amt = sizeof(struct ar_hdr);
  if (bfd_read(ar_header, amt, abfd) != amt)
    return false;
    
  if (strncmp(ar_header->ar_fmag, ARFMAG, 2))
  {
    bfd_set_error(bfd_error_malformed_archive);
    return false;
  }
  return true;
}

static bool
parse_archive_size(const char *size_str, unsigned int *parsed_size)
{
  errno = 0;
  *parsed_size = strtol(size_str, NULL, 10);
  if (errno != 0)
  {
    bfd_set_error(bfd_error_malformed_archive);
    return false;
  }
  return true;
}

static bool
read_and_validate_lst_header(bfd *abfd, struct som_lst_header *lst_header)
{
  struct som_external_lst_header ext_lst_header;
  size_t amt = sizeof(struct som_external_lst_header);
  
  if (bfd_read(&ext_lst_header, amt, abfd) != amt)
    return false;
    
  som_swap_lst_header_in(&ext_lst_header, lst_header);
  
  if (lst_header->a_magic != LIBMAGIC)
  {
    bfd_set_error(bfd_error_malformed_archive);
    return false;
  }
  return true;
}

static bool
allocate_symbol_storage(bfd *abfd, struct artdata *ardata)
{
  size_t amt;
  
  ardata->cache = 0;
  
  if (_bfd_mul_overflow(ardata->symdef_count, sizeof(carsym), &amt))
  {
    bfd_set_error(bfd_error_file_too_big);
    return false;
  }
  
  ardata->symdefs = bfd_alloc(abfd, amt);
  return ardata->symdefs != NULL;
}

static bool
seek_to_symbol_table_start(bfd *abfd, struct artdata *ardata, unsigned int parsed_size)
{
  return bfd_seek(abfd, (ardata->first_file_filepos - parsed_size
                        + sizeof(struct som_external_lst_header)),
                 SEEK_SET) == 0;
}

static bool
som_slurp_armap(bfd *abfd)
{
  struct som_lst_header lst_header;
  struct ar_hdr ar_header;
  unsigned int parsed_size;
  struct artdata *ardata = bfd_ardata(abfd);
  char nextname[17];
  
  if (!read_archive_name(abfd, nextname))
    return false;
    
  if (has_symbol_table(nextname, abfd))
    return true;
    
  if (!read_and_validate_ar_header(abfd, &ar_header))
    return false;
    
  if (!parse_archive_size(ar_header.ar_size, &parsed_size))
    return false;
    
  ardata->first_file_filepos = bfd_tell(abfd) + parsed_size;
  
  if (!read_and_validate_lst_header(abfd, &lst_header))
    return false;
    
  if (!som_bfd_count_ar_symbols(abfd, &lst_header, &ardata->symdef_count))
    return false;
    
  if (!seek_to_symbol_table_start(abfd, ardata, parsed_size))
    return false;
    
  if (!allocate_symbol_storage(abfd, ardata))
    return false;
    
  if (!som_bfd_fill_in_ar_symbols(abfd, &lst_header, &ardata->symdefs))
    return false;
    
  if (bfd_seek(abfd, ardata->first_file_filepos, SEEK_SET) != 0)
    return false;
    
  abfd->has_armap = true;
  return true;
}

/* Begin preparing to write a SOM library symbol table.

   As part of the prep work we need to determine the number of symbols
   and the size of the associated string section.  */

static bool
is_non_som_object(bfd *curr_bfd)
{
  return curr_bfd->format != bfd_object 
      || curr_bfd->xvec->flavour != bfd_target_som_flavour;
}

static bool
should_exclude_symbol(struct som_misc_symbol_info *info, som_symbol_type *sym)
{
  if (info->symbol_type == ST_NULL
      || info->symbol_type == ST_SYM_EXT
      || info->symbol_type == ST_ARG_EXT)
    return true;

  if (info->symbol_scope != SS_UNIVERSAL
      && info->symbol_type != ST_STORAGE)
    return true;

  if (bfd_is_und_section(sym->symbol.section))
    return true;

  return false;
}

static void
update_string_size(unsigned int *stringsize, const char *name)
{
  #define STRING_PADDING 5
  #define ALIGNMENT 4
  
  *stringsize += strlen(name) + STRING_PADDING;
  while (*stringsize % ALIGNMENT)
    (*stringsize)++;
}

static bool
process_bfd_symbols(bfd *curr_bfd, unsigned int *num_syms, unsigned int *stringsize)
{
  unsigned int curr_count, i;
  som_symbol_type *sym;

  if (!som_slurp_symbol_table(curr_bfd))
    return false;

  sym = obj_som_symtab(curr_bfd);
  curr_count = bfd_get_symcount(curr_bfd);

  for (i = 0; i < curr_count; i++, sym++)
    {
      struct som_misc_symbol_info info;
      
      som_bfd_derive_misc_symbol_info(curr_bfd, &sym->symbol, &info);
      
      if (should_exclude_symbol(&info, sym))
        continue;

      (*num_syms)++;
      update_string_size(stringsize, sym->symbol.name);
    }
  
  return true;
}

static bool
som_bfd_prep_for_ar_write(bfd *abfd,
                          unsigned int *num_syms,
                          unsigned int *stringsize)
{
  bfd *curr_bfd = abfd->archive_head;

  *num_syms = 0;
  *stringsize = 0;

  while (curr_bfd != NULL)
    {
      if (!is_non_som_object(curr_bfd))
        {
          if (!process_bfd_symbols(curr_bfd, num_syms, stringsize))
            return false;
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
  #define HASH_LENGTH_MASK 0x7f
  #define HASH_LENGTH_SHIFT 24
  #define HASH_CHAR1_SHIFT 16
  #define HASH_CHAR2_SHIFT 8
  #define SINGLE_CHAR_HASH_BASE 0x1000100

  unsigned int len = strlen (symbol->name);

  if (len == 1)
    return SINGLE_CHAR_HASH_BASE | (symbol->name[0] << HASH_CHAR1_SHIFT) | symbol->name[0];

  return ((len & HASH_LENGTH_MASK) << HASH_LENGTH_SHIFT) 
         | (symbol->name[1] << HASH_CHAR1_SHIFT)
         | (symbol->name[len - 2] << HASH_CHAR2_SHIFT) 
         | symbol->name[len - 1];
}

/* Do the bulk of the work required to write the SOM library
   symbol table.  */

static bool allocate_memory_with_overflow_check(size_t count, size_t elem_size, void **ptr)
{
  size_t amt;
  if (_bfd_mul_overflow(count, elem_size, &amt))
    {
      bfd_set_error(bfd_error_no_memory);
      return false;
    }
  *ptr = bfd_zmalloc(amt);
  if (*ptr == NULL && count != 0)
    return false;
  return true;
}

static void free_all_resources(unsigned char *hash_table, 
                               struct som_external_som_entry *som_dict,
                               struct som_external_lst_symbol_record **last_hash_entry,
                               struct som_external_lst_symbol_record *lst_syms,
                               char *strings)
{
  free(hash_table);
  free(som_dict);
  free(last_hash_entry);
  free(lst_syms);
  free(strings);
}

static bool allocate_archive_structures(unsigned int hash_size,
                                       unsigned int module_count,
                                       unsigned int nsyms,
                                       unsigned int string_size,
                                       unsigned char **hash_table,
                                       struct som_external_som_entry **som_dict,
                                       struct som_external_lst_symbol_record ***last_hash_entry,
                                       struct som_external_lst_symbol_record **lst_syms,
                                       char **strings)
{
  if (!allocate_memory_with_overflow_check(hash_size, 4, (void**)hash_table))
    return false;

  if (!allocate_memory_with_overflow_check(module_count, 
                                          sizeof(struct som_external_som_entry), 
                                          (void**)som_dict))
    return false;

  if (!allocate_memory_with_overflow_check(hash_size,
                                          sizeof(struct som_external_lst_symbol_record *),
                                          (void**)last_hash_entry))
    return false;

  size_t amt;
  if (_bfd_mul_overflow(nsyms, sizeof(struct som_external_lst_symbol_record), &amt))
    {
      bfd_set_error(bfd_error_no_memory);
      return false;
    }
  *lst_syms = bfd_malloc(amt);
  if (*lst_syms == NULL && nsyms != 0)
    return false;

  *strings = bfd_malloc(string_size);
  if (*strings == NULL && string_size != 0)
    return false;

  return true;
}

static unsigned int calculate_initial_som_offset(struct som_external_lst_header lst, 
                                                unsigned elength)
{
  unsigned int offset = 8 + 2 * sizeof(struct ar_hdr) + bfd_getb32(lst.file_end);
  if (elength)
    offset += elength;
  return (offset + 0x1) & ~0x1;
}

static bool should_skip_bfd(bfd *curr_bfd)
{
  return curr_bfd->format != bfd_object || 
         curr_bfd->xvec->flavour != bfd_target_som_flavour;
}

static bool should_include_symbol(struct som_misc_symbol_info *info, 
                                 som_symbol_type *sym)
{
  if (info->symbol_type == ST_NULL ||
      info->symbol_type == ST_SYM_EXT ||
      info->symbol_type == ST_ARG_EXT)
    return false;

  if (info->symbol_scope != SS_UNIVERSAL && 
      info->symbol_type != ST_STORAGE)
    return false;

  if (bfd_is_und_section(sym->symbol.section))
    return false;

  return true;
}

static void update_som_dictionary_if_first(struct som_external_som_entry *som_dict,
                                          unsigned int som_index,
                                          unsigned int curr_som_offset,
                                          bfd *curr_bfd)
{
  if (bfd_getb32(som_dict[som_index].location) == 0)
    {
      bfd_putb32(curr_som_offset, som_dict[som_index].location);
      bfd_putb32(arelt_size(curr_bfd), som_dict[som_index].length);
    }
}

#define LST_SYMBOL_XLEAST_VALUE 3

static unsigned int build_symbol_flags(struct som_misc_symbol_info *info,
                                      som_symbol_type *sym)
{
  unsigned int flags = 0;
  
  if (info->secondary_def)
    flags |= LST_SYMBOL_SECONDARY_DEF;
  flags |= info->symbol_type << LST_SYMBOL_SYMBOL_TYPE_SH;
  flags |= info->symbol_scope << LST_SYMBOL_SYMBOL_SCOPE_SH;
  if (bfd_is_com_section(sym->symbol.section))
    flags |= LST_SYMBOL_IS_COMMON;
  if (info->dup_common)
    flags |= LST_SYMBOL_DUP_COMMON;
  flags |= LST_SYMBOL_XLEAST_VALUE << LST_SYMBOL_XLEAST_SH;
  flags |= info->arg_reloc << LST_SYMBOL_ARG_RELOC_SH;
  
  return flags;
}

static void populate_lst_symbol_record(struct som_external_lst_symbol_record *curr_lst_sym,
                                      unsigned int flags,
                                      unsigned int name_offset,
                                      struct som_misc_symbol_info *info,
                                      unsigned int som_index,
                                      unsigned int symbol_key)
{
  bfd_putb32(flags, curr_lst_sym->flags);
  bfd_putb32(name_offset, curr_lst_sym->name);
  bfd_putb32(0, curr_lst_sym->qualifier_name);
  bfd_putb32(info->symbol_info, curr_lst_sym->symbol_info);
  bfd_putb32(info->symbol_value | info->priv_level, curr_lst_sym->symbol_value);
  bfd_putb32(0, curr_lst_sym->symbol_descriptor);
  curr_lst_sym->reserved = 0;
  bfd_putb32(som_index, curr_lst_sym->som_index);
  bfd_putb32(symbol_key, curr_lst_sym->symbol_key);
  bfd_putb32(0, curr_lst_sym->next_entry);
}

static unsigned int calculate_symbol_position(struct som_external_lst_symbol_record *curr_lst_sym,
                                             struct som_external_lst_symbol_record *lst_syms,
                                             unsigned int hash_size,
                                             unsigned int module_count)
{
  return (curr_lst_sym - lst_syms) * sizeof(struct som_external_lst_symbol_record)
         + hash_size * 4
         + module_count * sizeof(struct som_external_som_entry)
         + sizeof(struct som_external_lst_header);
}

static void update_hash_chain(unsigned int symbol_pos,
                             unsigned int symbol_key,
                             unsigned int hash_size,
                             unsigned char *hash_table,
                             struct som_external_lst_symbol_record **last_hash_entry,
                             struct som_external_lst_symbol_record *curr_lst_sym)
{
  unsigned int hash_index = symbol_key % hash_size;
  struct som_external_lst_symbol_record *last = last_hash_entry[hash_index];
  
  if (last != NULL)
    bfd_putb32(symbol_pos, last->next_entry);
  else
    bfd_putb32(symbol_pos, hash_table + 4 * hash_index);
    
  last_hash_entry[hash_index] = curr_lst_sym;
}

static char* update_string_table(bfd *abfd, char *p, const char *name)
{
  unsigned int slen = strlen(name);
  bfd_put_32(abfd, slen, p);
  p += 4;
  slen++;
  memcpy(p, name, slen);
  p += slen;
  while (slen % 4)
    {
      bfd_put_8(abfd, 0, p);
      p++;
      slen++;
    }
  return p;
}

static bool process_symbol(bfd *curr_bfd,
                          som_symbol_type *sym,
                          struct som_external_lst_symbol_record **curr_lst_sym,
                          struct som_external_lst_symbol_record *lst_syms,
                          char **p,
                          char *strings,
                          unsigned int string_size,
                          unsigned int hash_size,
                          unsigned int module_count,
                          unsigned int som_index,
                          unsigned int curr_som_offset,
                          struct som_external_som_entry *som_dict,
                          unsigned char *hash_table,
                          struct som_external_lst_symbol_record **last_hash_entry,
                          bfd *abfd)
{
  struct som_misc_symbol_info info;
  som_bfd_derive_misc_symbol_info(curr_bfd, &sym->symbol, &info);
  
  if (!should_include_symbol(&info, sym))
    return true;
    
  update_som_dictionary_if_first(som_dict, som_index, curr_som_offset, curr_bfd);
  
  unsigned int symbol_key = som_bfd_ar_symbol_hash(&sym->symbol);
  unsigned int flags = build_symbol_flags(&info, sym);
  
  populate_lst_symbol_record(*curr_lst_sym, flags, *p - strings + 4, 
                            &info, som_index, symbol_key);
  
  unsigned int symbol_pos = calculate_symbol_position(*curr_lst_sym, lst_syms, 
                                                     hash_size, module_count);
  
  update_hash_chain(symbol_pos, symbol_key, hash_size, hash_table, 
                   last_hash_entry, *curr_lst_sym);
  
  *p = update_string_table(abfd, *p, sym->symbol.name);
  
  BFD_ASSERT(*p <= strings + string_size);
  (*curr_lst_sym)++;
  
  return true;
}

static bool process_bfd_symbols(bfd *curr_bfd,
                               struct som_external_lst_symbol_record **curr_lst_sym,
                               struct som_external_lst_symbol_record *lst_syms,
                               char **p,
                               char *strings,
                               unsigned int string_size,
                               unsigned int hash_size,
                               unsigned int module_count,
                               unsigned int som_index,
                               unsigned int curr_som_offset,
                               struct som_external_som_entry *som_dict,
                               unsigned char *hash_table,
                               struct som_external_lst_symbol_record **last_hash_entry,
                               bfd *abfd)
{
  if (!som_slurp_symbol_table(curr_bfd))
    return false;
    
  som_symbol_type *sym = obj_som_symtab(curr_bfd);
  unsigned int curr_count = bfd_get_symcount(curr_bfd);
  
  for (unsigned int i = 0; i < curr_count; i++, sym++)
    {
      if (!process_symbol(curr_bfd, sym, curr_lst_sym, lst_syms, p, strings,
                         string_size, hash_size, module_count, som_index,
                         curr_som_offset, som_dict, hash_table, last_hash_entry, abfd))
        return false;
    }
  
  return true;
}

static bool write_archive_data(bfd *abfd,
                              unsigned char *hash_table,
                              unsigned int hash_size,
                              struct som_external_som_entry *som_dict,
                              unsigned int module_count,
                              struct som_external_lst_symbol_record *lst_syms,
                              unsigned int nsyms,
                              char *strings,
                              unsigned int string_size)
{
  size_t amt = (size_t) hash_size * 4;
  if (bfd_write(hash_table, amt, abfd) != amt)
    return false;
    
  amt = (size_t) module_count * sizeof(struct som_external_som_entry);
  if (bfd_write(som_dict, amt, abfd) != amt)
    return false;
    
  amt = (size_t) nsyms * sizeof(struct som_external_lst_symbol_record);
  if (bfd_write(lst_syms, amt, abfd) != amt)
    return false;
    
  amt = string_size;
  if (bfd_write(strings, amt, abfd) != amt)
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
  char *strings = NULL, *p;
  struct som_external_lst_symbol_record *lst_syms = NULL, *curr_lst_sym;
  bfd *curr_bfd;
  unsigned char *hash_table = NULL;
  struct som_external_som_entry *som_dict = NULL;
  struct som_external_lst_symbol_record **last_hash_entry = NULL;
  unsigned int curr_som_offset, som_index = 0;
  unsigned int module_count;
  unsigned int hash_size;

  hash_size = bfd_getb32(lst.hash_size);
  module_count = bfd_getb32(lst.module_count);

  if (!allocate_archive_structures(hash_size, module_count, nsyms, string_size,
                                  &hash_table, &som_dict, &last_hash_entry,
                                  &lst_syms, &strings))
    goto error_return;

  som_index = 0;
  curr_som_offset = calculate_initial_som_offset(lst, elength);

  p = strings;
  curr_lst_sym = lst_syms;

  curr_bfd = abfd->archive_head;
  while (curr_bfd != NULL)
    {
      if (!should_skip_bfd(curr_bfd))
        {
          if (!process_bfd_symbols(curr_bfd, &curr_lst_sym, lst_syms, &p, strings,
                                  string_size, hash_size, module_count, som_index,
                                  curr_som_offset, som_dict, hash_table, 
                                  last_hash_entry, abfd))
            goto error_return;
            
          curr_som_offset += arelt_size(curr_bfd) + sizeof(struct ar_hdr);
          curr_som_offset = (curr_som_offset + 0x1) & ~(unsigned) 1;
          som_index++;
        }
      curr_bfd = curr_bfd->archive_next;
    }

  if (!write_archive_data(abfd, hash_table, hash_size, som_dict, module_count,
                         lst_syms, nsyms, strings, string_size))
    goto error_return;

  free_all_resources(hash_table, som_dict, last_hash_entry, lst_syms, strings);
  return true;

 error_return:
  free_all_resources(hash_table, som_dict, last_hash_entry, lst_syms, strings);
  return false;
}

/* Write out the LST for the archive.

   You'll never believe this is really how armaps are handled in SOM...  */

static bool get_file_stats(bfd *abfd, struct stat *statbuf)
{
    if (stat(bfd_get_filename(abfd), statbuf) != 0)
    {
        bfd_set_error(bfd_error_system_call);
        return false;
    }
    return true;
}

static unsigned int count_som_modules(bfd *abfd)
{
    unsigned int module_count = 0;
    bfd *curr_bfd = abfd->archive_head;
    
    while (curr_bfd != NULL)
    {
        if (curr_bfd->format == bfd_object &&
            curr_bfd->xvec->flavour == bfd_target_som_flavour)
        {
            module_count++;
        }
        curr_bfd = curr_bfd->archive_next;
    }
    return module_count;
}

static void init_lst_header_basic(struct som_external_lst_header *lst)
{
    bfd_putb16(CPU_PA_RISC1_0, &lst->system_id);
    bfd_putb16(LIBMAGIC, &lst->a_magic);
    bfd_putb32(VERSION_ID, &lst->version_id);
    bfd_putb32(0, &lst->file_time.secs);
    bfd_putb32(0, &lst->file_time.nanosecs);
}

static void set_lst_unused_fields(struct som_external_lst_header *lst)
{
    bfd_putb32(0, &lst->export_loc);
    bfd_putb32(0, &lst->export_count);
    bfd_putb32(0, &lst->import_loc);
    bfd_putb32(0, &lst->aux_loc);
    bfd_putb32(0, &lst->aux_size);
    bfd_putb32(0, &lst->free_list);
}

static unsigned int calculate_lst_checksum(struct som_external_lst_header *lst)
{
    unsigned char *p = (unsigned char *)lst;
    unsigned int csum = 0;
    unsigned int i;
    
    for (i = 0; i < sizeof(struct som_external_lst_header) - sizeof(int); i += 4)
    {
        csum ^= bfd_getb32(&p[i]);
    }
    return csum;
}

static unsigned int build_lst_header(struct som_external_lst_header *lst,
                                     unsigned int module_count,
                                     unsigned int nsyms,
                                     unsigned int stringsize)
{
    unsigned int lst_size = sizeof(struct som_external_lst_header);
    
    init_lst_header_basic(lst);
    
    bfd_putb32(lst_size, &lst->hash_loc);
    bfd_putb32(SOM_LST_HASH_SIZE, &lst->hash_size);
    lst_size += 4 * SOM_LST_HASH_SIZE;
    
    bfd_putb32(module_count, &lst->module_count);
    bfd_putb32(module_count, &lst->module_limit);
    bfd_putb32(lst_size, &lst->dir_loc);
    lst_size += sizeof(struct som_external_som_entry) * module_count;
    
    set_lst_unused_fields(lst);
    
    lst_size += sizeof(struct som_external_lst_symbol_record) * nsyms;
    
    bfd_putb32(lst_size, &lst->string_loc);
    bfd_putb32(stringsize, &lst->string_size);
    lst_size += stringsize;
    
    bfd_putb32(lst_size, &lst->file_end);
    
    unsigned int csum = calculate_lst_checksum(lst);
    bfd_putb32(csum, &lst->checksum);
    
    return lst_size;
}

static void format_ar_header(struct ar_hdr *hdr,
                            struct stat *statbuf,
                            unsigned int lst_size,
                            time_t timestamp)
{
    sprintf(hdr->ar_name, "/              ");
    _bfd_ar_spacepad(hdr->ar_date, sizeof(hdr->ar_date), "%-12ld", timestamp);
    _bfd_ar_spacepad(hdr->ar_uid, sizeof(hdr->ar_uid), "%ld", statbuf->st_uid);
    _bfd_ar_spacepad(hdr->ar_gid, sizeof(hdr->ar_gid), "%ld", statbuf->st_gid);
    _bfd_ar_spacepad(hdr->ar_mode, sizeof(hdr->ar_mode), "%-8o",
                    (unsigned int)statbuf->st_mode);
    _bfd_ar_spacepad(hdr->ar_size, sizeof(hdr->ar_size), "%-10d", (int)lst_size);
    hdr->ar_fmag[0] = '`';
    hdr->ar_fmag[1] = '\012';
}

static void replace_nulls_with_spaces(void *buffer, size_t size)
{
    char *p = (char *)buffer;
    unsigned int i;
    
    for (i = 0; i < size; i++)
    {
        if (p[i] == '\0')
            p[i] = ' ';
    }
}

static bool write_header_data(bfd *abfd,
                             struct ar_hdr *hdr,
                             struct som_external_lst_header *lst)
{
    size_t amt;
    
    replace_nulls_with_spaces(hdr, sizeof(struct ar_hdr));
    
    amt = sizeof(struct ar_hdr);
    if (bfd_write(hdr, amt, abfd) != amt)
        return false;
    
    amt = sizeof(struct som_external_lst_header);
    if (bfd_write(lst, amt, abfd) != amt)
        return false;
    
    return true;
}

static bool som_write_armap(bfd *abfd,
                           unsigned int elength,
                           struct orl *map ATTRIBUTE_UNUSED,
                           unsigned int orl_count ATTRIBUTE_UNUSED,
                           int stridx ATTRIBUTE_UNUSED)
{
    struct stat statbuf;
    unsigned int lst_size, nsyms, stringsize;
    struct ar_hdr hdr;
    struct som_external_lst_header lst;
    unsigned int module_count;
    
    if (!get_file_stats(abfd, &statbuf))
        return false;
    
    bfd_ardata(abfd)->armap_timestamp = statbuf.st_mtime + 60;
    
    module_count = count_som_modules(abfd);
    
    if (!som_bfd_prep_for_ar_write(abfd, &nsyms, &stringsize))
        return false;
    
    lst_size = build_lst_header(&lst, module_count, nsyms, stringsize);
    
    format_ar_header(&hdr, &statbuf, lst_size, bfd_ardata(abfd)->armap_timestamp);
    
    if (!write_header_data(abfd, &hdr, &lst))
        return false;
    
    if (!som_bfd_ar_write_symbol_stuff(abfd, nsyms, stringsize, lst, elength))
        return false;
    
    return true;
}

/* Throw away some malloc'd information for this BFD.  */

static void free_and_nullify(void **ptr)
{
    free(*ptr);
    *ptr = NULL;
}

static void free_section_data(asection *section)
{
    section->reloc_count = (unsigned) -1;
    free_and_nullify((void**)&som_section_data(section)->reloc_stream);
}

static void free_som_object_data(bfd *abfd)
{
    asection *o;
    
    free_and_nullify((void**)&obj_som_symtab(abfd));
    free_and_nullify((void**)&obj_som_stringtab(abfd));
    
    for (o = abfd->sections; o != NULL; o = o->next)
    {
        free_section_data(o);
    }
}

static bool is_object_or_core(bfd *abfd)
{
    bfd_format format = bfd_get_format(abfd);
    return format == bfd_object || format == bfd_core;
}

static bool
som_bfd_free_cached_info (bfd *abfd)
{
    if (is_object_or_core(abfd))
    {
        free_som_object_data(abfd);
    }
    
    return true;
}

/* End of miscellaneous support functions.  */

/* Linker support functions.  */

static bool
som_bfd_link_split_section (bfd *abfd ATTRIBUTE_UNUSED, asection *sec)
{
  #define MAX_SUBSPACE_SIZE 240000
  return som_is_subspace (sec) && sec->size > MAX_SUBSPACE_SIZE;
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

