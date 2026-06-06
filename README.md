# Portable C Compiler

This repository contains **pcc**, the Portable C Compiler: a small and
fast C compiler with a portable machine-independent middle layer and
many machine-dependent back ends.

PCC descends from the original PCC by S.C. Johnson, which was the C
compiler shipped with early Unix systems. PCC became famous because it
was compact, understandable, and easy to retarget.

This tree is not, however, an old compiler preserved in amber. It has
been modernized over time with support for much more modern C
standards, Autoconf build machinery, many more targets, a rewritten
preprocessor, GCC compatibility hooks, newer ABI handling, and years
of fixes.

## What Is In This Tree

The repository is organized around the traditional PCC split between a
C front end, machine-independent compiler support, and target-specific
back ends:

- `cc/cc` - compiler driver installed as `pcc`, `pcpp`, and `p++`
- `cc/cpp` - C preprocessor
- `cc/ccom` - C compiler front end and first-pass code generation
- `cc/cxxcom` - C++ front-end sources
- `mip` - machine-independent pass 2 support, instruction matching,
  register allocation, and optimizer code
- `arch` - target back ends, including amd64, i386, i86, aarch64, arm,
  m68k, mips, mips64, powerpc, riscv, sparc64, vax, pdp10, pdp11,
  pdp7, nova, hppa, and m16c
- `os` - target operating-system configuration headers
- `common` - shared compatibility, Unicode, string-to-floating-point,
  and soft-float support
- `f77` - historical Fortran driver and front-end sources; present in
  the distribution tree but not built by the top-level `all` target

The configured operating-system targets include the major modern POSIX
operating systems, such as macOS, the BSD family, Linux, Android, and
several bare or older-system target combinations.

## Building

The checked-in `configure` script is generated, so a normal build does
not require Autoconf.

```sh
./configure
make
```

For a native install:

```sh
./configure --prefix=/usr/local --enable-native
make
make install
```

For a cross compiler, pass a target triplet:

```sh
./configure --target=vax-dec-bsd --prefix=/usr/local
make
make install
```

Useful configuration options include:

- `--target=<triplet>` - select the target CPU/OS/ABI
- `--enable-native` - build as a native compiler even when the target
  alias would otherwise make it look like a cross compiler
- `--enable-twopass` - build separate first and second compiler passes
- `--disable-gcc-compat` - turn off GCC-compatibility code paths
- `--enable-tls` - enable thread-local storage support when the target
  supports it
- `--with-incdir=<path>` and `--with-libdir=<path>` - set default
  system include and library search paths
- `--with-assembler=<path>` and `--with-linker=<path>` - set the
  assembler and linker used by the driver
- `--enable-multiarch=yes|no|auto|<triplet>` - control Linux multiarch
  path handling

Build tools normally needed are a C compiler, `make`, `yacc`/`byacc`
or compatible, and `lex`/`flex`.  Regenerating `configure`
additionally requires Autoconf.

The preprocessor has a small test target:

```sh
make -C cc/cpp test
```

Run it after configuring and building; the test target uses the
ngenerated Makefiles and the freshly built preprocessor.

## How This Differs From The Historic PCC

The original PCC was valued for being compact and retargetable, but it
was a compiler for a much smaller C and Unix world.  The current PCC
project is a long-running effort to keep that model while updating the
compiler for newer systems and ABIs.

Notable changes versus the original PCC include:

- **Autoconf and cross-build support.**  The build system understands
  host and target triples, native versus cross builds, alternate
  assemblers/linkers, sysroot-style paths, and Linux multiarch include
  directories.
- **Many more back ends.**  Alongside traditional targets such as VAX
  PDP-11 and PDP-10, this tree contains support for many new targets
  such as amd64, i386, ARM, AArch64, MIPS, MIPS64, PowerPC, SPARC64,
  and RISC-V.
- **Modernized driver behavior.**  The driver accepts many familiar
  Unix/GCC options, handles `.c`, `.i`, `.s`, `.S`, and object inputs,
  and installs `pcc`, `pcpp`, and `p++` front ends.
- **A substantially rewritten preprocessor.** The preprocessor has
  been dramatically modernized.
- **C99 and GNU compatibility work.**  The compiler has C99-oriented
  parsing and type handling, GNU statement-expression support,
  selected attributes and builtins, `__GNUC__` compatibility
  definitions when enabled, GCC-style inline assembly work, stack
  protector hooks, and many libc-facing builtin stubs.
- **Better aggregate and ABI handling.**  Improved structures, unions,
  bit-fields, arrays, function prototypes, hidden structure return
  arguments, register arguments, stack arguments, varargs, and ABI
  classification correct across targets.
- **Floating-point and complex improvements.**  The tree includes
  soft-float support, long double handling, `__float128`-related
  compatibility work, complex type fixes, IEEE64 long double options,
  and newer builtin support such as `__builtin_isinf_sign`.
- **Reworked internals.**  The pass 1 type model, prototype storage,
  argument handling, instruction needs, shape matching, liveness
  analysis, and register allocation have all been refactored over the
  years.

## Licensing

The sources are available under a mix of permissive BSD and ISC style
licenses. See `LICENSE.md` for an aggregate audit and the main license
texts.  Individual file headers remain authoritative.
