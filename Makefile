# Norcroft Makefile
#
# Outputs to: ../build/{bin,obj,derived}
#
# Options are:
#   make ncc                	# C compiler (ARM backend)
#   make ntcc               	# C compiler (Thumb backend)
#   make n++                	# C++ compiler (ARM backend)
#   make nt++               	# C++ compiler (Thumb backend)
#   make interp             	# C++ interpreter
#   make clbcomp            	# C++ Callable compiler
#   make ... BUILD32=1      	# force -m32 (force 32-bit build on Linux)
#   make ... TARGET=riscos		# Cross compiler targeting RISC OS (runs on host)
#   make ... TARGET=riscos HOST=riscos	# Build a RISC OS-native compiler
#   make ... TARGET=newton		# Create cross compiler targettingApple Newton
#   make all                	# ncc + n++
#   make clean / make distclean

# config toggles ----------------
TARGET      ?= arm          # arm | riscos | newton
BUILD32     ?=
WARN        ?= minimal      # some | minimal | none
HOST    	?=              # "" | riscos

.DEFAULT_GOAL := ncc

# toolchain
CC          ?= cc
AR          ?= ar
RANLIB      ?= ranlib

# layout (this Makefile sits immediately above ncc/)
SRC_ROOT     := ncc
OUT_ROOT     := build
DERIVED_ROOT := $(OUT_ROOT)/derived

.SECONDARY:

BIN_DIR     := $(OUT_ROOT)/bin

TARGET := $(strip $(TARGET))
WARN   := $(strip $(WARN))
HOST   := $(strip $(HOST))

# Use the RISC OS-native toolchain only when TARGET=riscos and HOST=riscos
CC := $(if $(and $(filter riscos,$(TARGET)),$(filter riscos,$(HOST))),build/bin/ncc-riscos,cc)

# Additional flavour suffix when building a RISC OS-native compiler under TARGET=riscos
BIN_FLAVOUR := $(if $(and $(filter riscos,$(TARGET)),$(filter riscos,$(HOST))),-riscos,)
OBJ_FLAVOUR := $(if $(and $(filter riscos,$(TARGET)),$(filter riscos,$(HOST))),-riscos,)

# Suffix binaries when TARGET != arm (so we can build multiple variants)
BIN_SUFFIX := $(if $(filter arm,$(TARGET)),,$(addprefix -,$(TARGET)))$(BIN_FLAVOUR)

BIN_NCC    := $(BIN_DIR)/ncc$(BIN_SUFFIX)
BIN_NCPP   := $(BIN_DIR)/n++$(BIN_SUFFIX)
BIN_NTCC   := $(BIN_DIR)/ntcc$(BIN_SUFFIX)
BIN_NTCPP  := $(BIN_DIR)/nt++$(BIN_SUFFIX)
BIN_INTERP := $(BIN_DIR)/npp$(BIN_SUFFIX)
BIN_CLBCOMP:= $(BIN_DIR)/clbcomp$(BIN_SUFFIX)
.SECONDARY:

# default options.h directories per tool, used if TARGET=host
OPTIONS_ncc     := ccarm
OPTIONS_n++     := ccarm
OPTIONS_ntcc    := ccthumb
OPTIONS_nt++    := ccthumb
OPTIONS_interp  := cppint
OPTIONS_clbcomp := clbcomp

# default options.h directories if TARGET != arm. ncc/ntcc only.
OPTIONS_riscos 	 := ccacorn
OPTIONS_newton   := ccapple

# Determine the tool being built (ncc/n++/ntcc/nt++/interp/clbcomp)
BUILD_TOOL := $(firstword $(filter ncc n++ ntcc nt++ interp clbcomp,$(MAKECMDGOALS)))

# Provide a sensible default if invoked without an explicit goal (e.g. `make`)
BUILD_TOOL := $(if $(BUILD_TOOL),$(BUILD_TOOL),ncc)

# Resolve per-build-target default options dir, then override by TARGET if not "arm"
OPTIONS_DEFAULT_DIR := $(OPTIONS_$(BUILD_TOOL))
OPTIONS_OVERRIDE_DIR := $(OPTIONS_$(TARGET))
OPTIONS_DIR  := $(if $(filter arm,$(TARGET)),$(OPTIONS_DEFAULT_DIR),$(OPTIONS_OVERRIDE_DIR))

# Select backend early, based on the requested build tool
# thumb for ntcc/nt++, arm otherwise (can still be overridden by command line)
BACKEND ?= $(if $(filter ntcc nt++,$(BUILD_TOOL)),thumb,arm)
BACKEND_DIR := $(SRC_ROOT)/$(BACKEND)

DERIVED_DIR := $(DERIVED_ROOT)/$(TARGET)/$(BACKEND)
OBJ_DIR     := $(OUT_ROOT)/obj/$(TARGET)$(OBJ_FLAVOUR)/$(BACKEND)

# warnings --------------
# Minimal changes are made to the source code, but on a modern compiler that
# means suppressing many warnings.
ifeq ($(WARN),none)
  WFLAGS :=
else
  ifeq ($(WARN),minimal)
    ifneq (,$(findstring clang,$(shell $(CC) --version 2>/dev/null)))
      WFLAGS := -Wno-everything
    else
      WFLAGS := -w
    endif
  else
    WFLAGS := -Wall -Wextra -Wno-unused-parameter -Wno-missing-field-initializers -Wno-sign-compare
  endif
endif

# common flags -----------------
ifeq ($(TARGET),newton)
CFLAGS := -Dpascal="" -DMSG_TOOL_NAME=\"$(BUILD_TOOL)\"
LDLIBS :=
endif

ifeq ($(TARGET),riscos)
CFLAGS := -DCOMPILING_ON_ARM -DTARGET_IS_RISC_OS -DFOR_ACORN -D__acorn
LDLIBS :=
endif

# The default RISC OS compiler generates code for 26-bit RISC OS.
# To generate a RISC OS-hosted compiler for 32-bit RISC OS, ensure CFLAGS
# include at least: -apcs 3/32bit/fpe3 -za=1
ifeq ($(HOST),riscos)
CFLAGS += -DCOMPILING_ON_RISCOS -DCOMPILING_ON_RISC_OS -DHOST_IS_RISCOS
LDLIBS +=
else
CFLAGS += -O2 -std=gnu89 -fcommon -fno-strict-aliasing $(WFLAGS)
LDLIBS += -lm
DEPFLAGS = -MMD -MP -MF $(@:.o=.d)
endif

ifeq ($(BUILD32),1)
  CFLAGS  += -m32
  LDFLAGS += -m32
endif

C_DEFS :=
CPP_DEFS := -DCPLUSPLUS

# --- Linker selection -------------------------------------------------

# Use drlink only when we are building a RISC OS-native compiler
# i.e. TARGET=riscos and HOST=riscos
ifeq ($(filter riscos,$(TARGET) $(HOST)),riscos riscos)
  LD := drlink
  LDLIBS := lib/clib/stubsg.o
else
  LD := $(CC)
endif

# HOST_DIR contains host.h. Probably needs splitting into arm & riscos.
HOST_DIR := $(SRC_ROOT)/../ncc-support
COMPAT_DIR := $(SRC_ROOT)/../ncc-support

INC_COMMON := \
  -I$(SRC_ROOT)/mip \
  -I$(SRC_ROOT)/cfe \
  -I$(SRC_ROOT)/armthumb \
  -I$(BACKEND_DIR) \
  -I$(SRC_ROOT)/util \
  -I$(HOST_DIR) \
  -I$(SRC_ROOT)/$(OPTIONS_DIR) \
  -I$(DERIVED_DIR)

# sources ----------------------
CC_COMMON := \
  mip/aetree.c mip/cg.c mip/codebuf.c mip/compiler.c mip/cse.c mip/csescan.c \
  mip/cseeval.c mip/driver.c mip/dwarf.c mip/dwarf1.c mip/dwarf2.c \
  mip/flowgraf.c mip/inline.c mip/jopprint.c mip/misc.c mip/regalloc.c \
  mip/regsets.c mip/sr.c mip/store.c mip/main.c mip/dump.c mip/version.c \
  \
  armthumb/aaof.c armthumb/asd.c armthumb/dwasd.c \
  armthumb/asmsyn.c armthumb/asmcg.c \
  armthumb/tooledit.c armthumb/arminst.c

CFE_SOURCES := \
  mip/bind.c mip/builtin.c cfe/lex.c cfe/pp.c cfe/sem.c cfe/simplify.c \
  cfe/syn.c cfe/vargen.c

CPPFE_SOURCES := \
  cppfe/overload.c cppfe/xbind.c cppfe/xbuiltin.c \
  cppfe/xlex.c cppfe/xsem.c cppfe/xsyn.c cppfe/xvargen.c \
  cfe/pp.c cfe/simplify.c

ARM_SRCS := arm/asm.c arm/gen.c arm/mcdep.c arm/peephole.c
THUMB_SRCS := thumb/asm.c thumb/gen.c thumb/mcdep.c thumb/peephole.c

COMPAT_SRCS := \
  compat/dde.c \
  compat/dem.c \
  compat/disass.c \
  compat/filestat.c \
  compat/fname.c \
  compat/ieeeflt.c \
  compat/int64.c \
  compat/msg.c \
  compat/prgname.c \
  compat/riscos.c \
  compat/toolenv.c \
  compat/trackfil.c \
  compat/unmangle.c \

ifeq ($(filter riscos,$(TARGET) $(HOST)),riscos riscos)
COMPAT_SRCS += int64-runtime.c
endif

# Generated source and header files.
DERIVED_SRCS := $(DERIVED_DIR)/headers.c $(DERIVED_DIR)/peeppat.c
DERIVED_HDRS := $(DERIVED_DIR)/errors.h $(DERIVED_DIR)/tags.h
DERIVED_STAMP := $(DERIVED_DIR)/.generated

# Host tools to generate the above source files.
GENHDRS_EXE  := $(DERIVED_DIR)/genhdrs
PEEPGEN_EXE  := $(DERIVED_DIR)/peepgen
PEEPPAT_TXT  := $(BACKEND_DIR)/peeppat

CLIB_HDRS := assert.h ctype.h errno.h float.h iso646.h limits.h \
			 locale.h math.h setjmp.h signal.h stdarg.h stddef.h \
			 stdio.h stdlib.h string.h time.h
CLIB_RISCOS_HDRS := kernel.h stdint.h varargs.h

CLIB_HDRS    += $(if $(filter riscos,$(TARGET)),$(CLIB_RISCOS_HDRS),)

OPTIONS_DIR  := $(if $(filter arm,$(TARGET)),$(OPTIONS_DEFAULT_DIR),$(OPTIONS_OVERRIDE_DIR))

CLIB_HDRS_DIR := lib/clib/include/

# error lists
ERRS_H := \
	$(SRC_ROOT)/mip/miperrs.h \
	$(SRC_ROOT)/cfe/feerrs.h \
	$(SRC_ROOT)/armthumb/mcerrs.h

$(DERIVED_STAMP): $(DERIVED_SRCS) $(DERIVED_HDRS) | $(DERIVED_DIR)
	@touch $@

# ---- Host tools (built for and run on the build host regardless of TARGET)
CC_HOST       ?= cc
CFLAGS_HOST   ?= $(CFLAGS)
HOSTTOOLS_DIR := $(OUT_ROOT)/hosttools
GENHDRS_HOST  := $(HOSTTOOLS_DIR)/genhdrs
PEEPGEN_HOST  := $(HOSTTOOLS_DIR)/peepgen

# per-tool bundles ----------------
NCC_SRCS   := $(CC_COMMON) $(CFE_SOURCES)   $(ARM_SRCS)   $(COMPAT_SRCS)
NCPP_SRCS  := $(CC_COMMON) $(CPPFE_SOURCES) $(ARM_SRCS)   $(COMPAT_SRCS)
NTCC_SRCS  := $(CC_COMMON) $(CFE_SOURCES)   $(THUMB_SRCS)
NTCPP_SRCS := $(CC_COMMON) $(CPPFE_SOURCES) $(THUMB_SRCS)

# .o files in build/obj/<tool>/ (no subdirs)
NCC_OBJS     := $(addprefix $(OBJ_DIR)/ncc/,$(notdir $(NCC_SRCS:.c=.o))) $(OBJ_DIR)/ncc/headers.o
NCPP_OBJS    := $(addprefix $(OBJ_DIR)/n++/,$(notdir $(NCPP_SRCS:.c=.o))) $(OBJ_DIR)/n++/headers.o
NTCC_OBJS    := $(addprefix $(OBJ_DIR)/ntcc/,$(notdir $(NTCC_SRCS:.c=.o))) $(OBJ_DIR)/ntcc/headers.o
NTCPP_OBJS   := $(addprefix $(OBJ_DIR)/nt++/,$(notdir $(NTCPP_SRCS:.c=.o))) $(OBJ_DIR)/nt++/headers.o
INTERP_OBJS  := $(addprefix $(OBJ_DIR)/interp/,$(notdir $(INTERP_SRCS:.c=.o))) $(OBJ_DIR)/interp/headers.o
CLBCOMP_OBJS := $(addprefix $(OBJ_DIR)/clbcomp/,$(notdir $(CLBCOMP_SRCS:.c=.o)))

# Ensure generated sources exist before compiling anything that may include them
$(OBJ_DIR)/ncc/%.o $(OBJ_DIR)/n++/%.o $(OBJ_DIR)/ntcc/%.o $(OBJ_DIR)/nt++/%.o $(OBJ_DIR)/interp/%.o $(OBJ_DIR)/clbcomp/%.o: | $(DERIVED_STAMP)

# peeppat.c is generated and #included by peephole.c; do not compile it separately.
# Ensure each backend’s peephole.o is rebuilt if peeppat.c changes.
$(OBJ_DIR)/ncc/peephole.o \
$(OBJ_DIR)/n++/peephole.o \
$(OBJ_DIR)/ntcc/peephole.o \
$(OBJ_DIR)/nt++/peephole.o: $(DERIVED_DIR)/peeppat.c

INTERP_SRCS := \
  interp/interp.c \
  mip/builtin.c mip/aetree.c mip/misc.c mip/store.c mip/bind.c \
  mip/compiler.c cfe/pp.c \
  $(CPPFE_SOURCES) \
  $(CFE_SOURCES) \
  $(DERIVED_SRCS)

CLBCOMP_SRCS := \
	mip/aetree.c mip/misc.c mip/compiler.c clbcomp/clbcomp.c \
	clbcomp/clb_store.c cppfe/xsyn.c cppfe/xsem.c cppfe/xbuiltin.c \
	cppfe/xbind.c cppfe/overload.c cppfe/xlex.c cfe/simplify.c cfe/pp.c

#
# top-level goals
.PHONY: all ncc n++ ntcc nt++ interp clbcomp clean distclean print
all: ncc n++

ncc:     $(BIN_NCC)
n++:     $(BIN_NCPP)
ntcc:    $(BIN_NTCC)
nt++:    $(BIN_NTCPP)
interp:  $(BIN_INTERP)
clbcomp: $(BIN_CLBCOMP)

print:
	@echo "CC=$(CC)"
	@echo "CFLAGS=$(CFLAGS)"
	@echo "LDFLAGS=$(LDFLAGS)"
	@echo "TARGET=$(TARGET) BUILD32=$(BUILD32) WARN=$(WARN)"
	@echo "HOST=$(HOST)"
	@echo "BUILD_TOOL=$(BUILD_TOOL)"
	@echo "BACKEND=$(BACKEND)"
	@echo "OPTIONS_DIR=$(OPTIONS_DIR)"
	@echo "HOST_DIR=$(HOST_DIR)"
	@echo "COMPAT_DIR=$(COMPAT_DIR)"
	@echo "DERIVED_DIR=$(DERIVED_DIR)"
	@echo "OBJ_DIR=$(OBJ_DIR) BIN_DIR=$(BIN_DIR)"
	@echo "BIN_SUFFIX=$(BIN_SUFFIX)"
	@echo "BINARIES: ncc=$(BIN_NCC) n++=$(BIN_NCPP) ntcc=$(BIN_NTCC) nt++=$(BIN_NTCPP) npp=$(BIN_INTERP) clbcomp=$(BIN_CLBCOMP)"
	@echo "HOSTTOOLS_DIR=$(HOSTTOOLS_DIR)"
	@echo "GENHDRS_HOST=$(GENHDRS_HOST) PEEPGEN_HOST=$(PEEPGEN_HOST)"

# ------------- link rules ---------------------
$(BIN_NCC): $(NCC_OBJS) | $(BIN_DIR)
	$(LD) $(LDFLAGS) -o $@ $^ $(LDLIBS)

$(BIN_NCPP): $(NCPP_OBJS) | $(BIN_DIR)
	$(LD) $(LDFLAGS) -o $@ $^ $(LDLIBS)

$(BIN_NTCC): $(NTCC_OBJS) | $(BIN_DIR)
	$(LD) $(LDFLAGS) -o $@ $^ $(LDLIBS)

$(BIN_NTCPP): $(NTCPP_OBJS) | $(BIN_DIR)
	$(LD) $(LDFLAGS) -o $@ $^ $(LDLIBS)

$(BIN_INTERP): $(INTERP_OBJS) | $(BIN_DIR)
	$(LD) $(LDFLAGS) -o $@ $^ $(LDLIBS)

$(BIN_CLBCOMP): $(CLBCOMP_OBJS) | $(BIN_DIR)
	$(LD) $(LDFLAGS) -o $@ $^ $(LDLIBS)

# ------------- compile rules ------------------
# Provide explicit per-subdir patterns so make can find the sources
# and place objects in matching subfolders under obj/<tool>/...

# Helper macros to pick include dir for each tool kind
INTERP_INCS    := -I$(SRC_ROOT)/$(OPTIONS_INTERP)
CLB_INCS       := -I$(SRC_ROOT)/clbcomp

$(OBJ_DIR)/ncc/%.o: $(SRC_ROOT)/mip/%.c | $(OBJ_DIR)/ncc $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(C_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/ncc/%.o: $(SRC_ROOT)/cfe/%.c | $(OBJ_DIR)/ncc $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(C_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/ncc/%.o: $(SRC_ROOT)/arm/%.c | $(OBJ_DIR)/ncc $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(C_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/ncc/%.o: $(SRC_ROOT)/armthumb/%.c | $(OBJ_DIR)/ncc $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(C_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/ncc/%.o: $(DERIVED_DIR)/%.c | $(OBJ_DIR)/ncc $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(C_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/ncc/%.o: $(COMPAT_DIR)/%.c | $(OBJ_DIR)/ncc $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(C_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@

# n++ (ARM C++)
$(OBJ_DIR)/n++/%.o: $(SRC_ROOT)/mip/%.c | $(OBJ_DIR)/n++ $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(CPP_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/n++/%.o: $(SRC_ROOT)/cfe/%.c | $(OBJ_DIR)/n++ $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(CPP_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/n++/%.o: $(SRC_ROOT)/cppfe/%.c | $(OBJ_DIR)/n++ $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(CPP_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/n++/%.o: $(SRC_ROOT)/arm/%.c | $(OBJ_DIR)/n++ $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(CPP_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/n++/%.o: $(SRC_ROOT)/armthumb/%.c | $(OBJ_DIR)/n++ $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(CPP_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/n++/%.o: $(DERIVED_DIR)/%.c | $(OBJ_DIR)/n++ $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(CPP_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/n++/%.o: $(COMPAT_DIR)/%.c | $(OBJ_DIR)/n++ $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(CPP_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@

# ntcc (Thumb C)
$(OBJ_DIR)/ntcc/%.o: $(SRC_ROOT)/mip/%.c | $(OBJ_DIR)/ntcc $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(C_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/ntcc/%.o: $(SRC_ROOT)/cfe/%.c | $(OBJ_DIR)/ntcc $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(C_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/ntcc/%.o: $(SRC_ROOT)/thumb/%.c | $(OBJ_DIR)/ntcc $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(C_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/ntcc/%.o: $(SRC_ROOT)/armthumb/%.c | $(OBJ_DIR)/ntcc $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(C_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/ntcc/%.o: $(DERIVED_DIR)/%.c | $(OBJ_DIR)/ntcc $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(C_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@

# nt++ (Thumb C++)
$(OBJ_DIR)/nt++/%.o: $(SRC_ROOT)/mip/%.c | $(OBJ_DIR)/nt++ $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(CPP_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/nt++/%.o: $(SRC_ROOT)/cfe/%.c | $(OBJ_DIR)/nt++ $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(CPP_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/nt++/%.o: $(SRC_ROOT)/cppfe/%.c | $(OBJ_DIR)/nt++ $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(CPP_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/nt++/%.o: $(SRC_ROOT)/thumb/%.c | $(OBJ_DIR)/nt++ $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(CPP_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/nt++/%.o: $(SRC_ROOT)/armthumb/%.c | $(OBJ_DIR)/nt++ $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(CPP_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/nt++/%.o: $(DERIVED_DIR)/%.c | $(OBJ_DIR)/nt++ $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(CPP_DEFS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@

# interp
$(OBJ_DIR)/interp/%.o: $(SRC_ROOT)/interp/%.c | $(OBJ_DIR)/interp $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(INC_COMMON) $(INTERP_INCS) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/interp/%.o: $(SRC_ROOT)/mip/%.c | $(OBJ_DIR)/interp $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(INC_COMMON) $(INTERP_INCS) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/interp/%.o: $(SRC_ROOT)/cfe/%.c | $(OBJ_DIR)/interp $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(INC_COMMON) $(INTERP_INCS) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/interp/%.o: $(SRC_ROOT)/cppfe/%.c | $(OBJ_DIR)/interp $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(INC_COMMON) $(INTERP_INCS) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/interp/%.o: $(DERIVED_DIR)/%.c | $(OBJ_DIR)/interp $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(INC_COMMON) $(INTERP_INCS) $(DEPFLAGS) -c $< -o $@

# clbcomp
$(OBJ_DIR)/clbcomp/%.o: $(SRC_ROOT)/clbcomp/%.c | $(OBJ_DIR)/clbcomp $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(INC_COMMON) $(CLB_INCS) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/clbcomp/%.o: $(SRC_ROOT)/mip/%.c | $(OBJ_DIR)/clbcomp $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(INC_COMMON) $(CLB_INCS) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/clbcomp/%.o: $(SRC_ROOT)/cfe/%.c | $(OBJ_DIR)/clbcomp $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(INC_COMMON) $(CLB_INCS) $(DEPFLAGS) -c $< -o $@
$(OBJ_DIR)/clbcomp/%.o: $(SRC_ROOT)/cppfe/%.c | $(OBJ_DIR)/clbcomp $(DERIVED_STAMP)
	$(CC) $(CFLAGS) $(INC_COMMON) $(CLB_INCS) $(DEPFLAGS) -c $< -o $@

# derived generation -------------
$(HOSTTOOLS_DIR):
	mkdir -p $@

$(DERIVED_DIR) $(OBJ_DIR)/ncc $(OBJ_DIR)/n++ $(OBJ_DIR)/ntcc $(OBJ_DIR)/nt++ $(OBJ_DIR)/interp $(OBJ_DIR)/clbcomp $(BIN_DIR):
	mkdir -p $@

# genhdrs / peepgen built for and run on the host (usable even when TARGET=ronative)
$(GENHDRS_HOST): $(SRC_ROOT)/util/genhdrs.c | $(HOSTTOOLS_DIR)
	$(CC_HOST) $(CFLAGS_HOST) -O2 -o $@ $<

# mcdpriv.h is per-backend dir (PEEPGEN needs backend headers even though the tool itself is host-built)
$(PEEPGEN_HOST): $(SRC_ROOT)/util/peepgen.c $(SRC_ROOT)/mip/jopcode.h $(BACKEND_DIR)/mcdpriv.h | $(HOSTTOOLS_DIR)
	$(CC_HOST) $(CFLAGS_HOST) -O2 -I$(SRC_ROOT)/mip -I$(BACKEND_DIR) -I$(HOST_DIR) -I$(SRC_ROOT)/$(OPTIONS_DIR) -o $@ $(SRC_ROOT)/util/peepgen.c

# tags.h — minimalist compatible generator (merge any available *_errs)
$(DERIVED_DIR)/tags.h: $(ERRS_H) | $(DERIVED_DIR)
	@echo "/* generated: tags.h (compat) */" > $@
	@awk '/^#define[ \t]+[A-Z0-9_]+[ \t]+[0-9]+/ {print}' $(ERRS_H) >> $@

# errors.h — via genhdrs -e (accepts 3 inputs)
$(DERIVED_DIR)/errors.h: $(GENHDRS_HOST) $(ERRS_H) | $(DERIVED_DIR)
	$(GENHDRS_HOST) -e$@ $(foreach E,$(ERRS_H),-q$(E))

# headers.c — pack the "stdh" headers
$(DERIVED_DIR)/headers.c: $(GENHDRS_HOST) $(addprefix $(CLIB_HDRS_DIR),$(CLIB_HDRS)) | $(DERIVED_DIR)
	$(GENHDRS_HOST) -o$@ -i$(CLIB_HDRS_DIR) $(CLIB_HDRS)

# peeppat.c — from textual peephole patterns (per BACKEND)
$(DERIVED_DIR)/peeppat.c: $(PEEPGEN_HOST) $(PEEPPAT_TXT) | $(DERIVED_DIR)
	$(PEEPGEN_HOST) $(PEEPPAT_TXT) $@

# Auto-included dependency files (generated by -MMD/-MP)
-include $(OBJ_DIR)/ncc/*.d \
         $(OBJ_DIR)/n++/*.d \
         $(OBJ_DIR)/ntcc/*.d \
         $(OBJ_DIR)/nt++/*.d \
         $(OBJ_DIR)/interp/*.d \
         $(OBJ_DIR)/clbcomp/*.d

# hygiene ------------------------
clean:
	$(RM) -r $(OUT_ROOT)/obj $(BIN_DIR)

distclean: clean
	$(RM) -r $(DERIVED_ROOT) $(HOSTTOOLS_DIR)
