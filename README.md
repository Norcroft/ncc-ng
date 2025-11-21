# Norcroft NG

Norcroft NG is the active development branch that builds on the restored
historical Norcroft C/C++ compiler. It introduces improvements, new features,
bug fixes, and additional backends while keeping the spirit of the original.

Using the name Norcroft NG avoids version-number clashes as each vendor was
encouraged to have their own version numbering.

Code is emitted in AOF files and supports several targets: ARM's generic 32-bit
development platform, RISC OS (32-bit and 26-bit), and Apple Newton (untested).

## Contents

- **`ncc/`** — the compiler source code.

- **`ncc-support/`** — newly recreated support code and glue. These files will
  be replaced with original equivalents as they are located.

- **`tests/`** - simple test suite that can check compilation of tests in
  various ways - assembler output or assertions that the test's syntax
  correctly compiles or correctly fails to compile.

- **`external/`** - externally sourced libraries that can be built by
  here, usually imported git repositories. For instance RISC OS `stubs`.

- **`external/clib/`** — standard C library header files. The original
   Acorn/Codemist C headers have not yet been released under an open source
   licence, so these are more modern versions from the ROOL fork of
   Norcroft, lightly 'de-updated'.

- **`tools/`** - currently a python recreation of `libfile`, the
  AOF equivalent of `ar`. Useful for building libraries such as `stubs`.

- **`bin/`** and **`lib/`** destinations for binaries and library files.

## Building
C:
```
make ncc [TARGET=<arm|riscos|riscos26|newton>] [HOST=riscos]
```
C++:
```
make n++ [TARGET=<arm|riscos|riscos26|newton>] [HOST=riscos]
```

Where:
- `TARGET` selects the code generation flags for the named target
 (Generic ARM, RISC OS (32-bit or 26-bit), or Apple Newton).

- `HOST=riscos` first compiles a compiler for the current host (ncc-riscos),
   and uses that to build a native RISC OS executable (`ncc,ff8`).

### Examples:
Cross-compiler for targeting 26-bit RISC OS 3 or 4. Builds `bin/ncc-riscos26`:
```
make ncc TARGET=riscos26
```

RISC OS-native compiler to run on RISC OS 5. Builds `bin/ncc,ff8`, where ff8
is the 'Absolute' filetype for a RISC OS executable:
```
make ncc TARGET=riscos HOST=riscos
```

### Other useful make targets:
```
make all        # ncc & n++
make clean
make distclean
```

## Notes
`TARGET=riscos` produces code for RISC OS 5 with unaligned loads disabled
for broad hardware compatibility. Use `-za0` to allow unaligned loads where
appropriate.

### Contributions

Please contribute to this fork. Norcroft must be able to compile itself (easiest way to check is to build a RISC OS-hosted compiler), which
currently means strict adherence to ANSI C.


## Acknowledgements

Thanks to Lee Smith (formerly ARM), Arthur Norman (Codemist) and
Alan Mycroft (Codemist) for access to the source and general encouragement.
