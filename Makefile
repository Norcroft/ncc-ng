# Norcroft Makefile
#
# Outputs to: ../build/{bin,obj,derived}
#
# Options are:
#   make ncc [<options>]       	# C compiler (ARM backend)
#   make n++ [<options>]    	# C++ compiler (ARM backend)
#   make ntcc               	# C compiler (Thumb backend)
#   make nt++               	# C++ compiler (Thumb backend)
#   make all                	# ncc & n++
#   make clean / make distclean

# ncc and n++ can be compiled to target different plaforms:
#   TARGET=newton					# Cross compiler targetting Apple Newton
#
#   TARGET=riscos					# Cross compiler targeting 32-bit RISC OS
#   TARGET=riscos26					# Cross compiler targeting 26-bit RISC OS
#   TARGET=riscos   HOST=riscos		# 32-bit RISC OS-native compiler
#   TARGET=riscos26 HOST=riscos		# 26-bit RISC OS-native compiler
#
# RISC OS native compilers first build a suitable RISC OS cross compiler,
# which then builds the native compiler.

# config toggles ----------------
TARGET      ?= arm          # arm | riscos | riscos26 | newton
WARN        ?= minimal      # some | minimal | none
HOST    	?=              # riscos | <blank>

.DEFAULT_GOAL := ncc

# layout (this Makefile sits immediately above ncc/)
SRC_ROOT     := ncc
OUT_ROOT     := build
DERIVED_ROOT := $(OUT_ROOT)/derived

.SECONDARY:

BIN_DIR     := bin

# toolchain - this is overwritten if HOST=riscos
CC          ?= cc
ifeq ($(HOST),riscos)
CC          := $(BIN_DIR)/ncc-$(TARGET)
endif

TARGET := $(strip $(TARGET))
WARN   := $(strip $(WARN))
HOST   := $(strip $(HOST))

# Suffix binaries when TARGET != arm (so we can build multiple variants)
BIN_SUFFIX := $(if $(filter arm,$(TARGET)),,$(addprefix -,$(TARGET)))

# Overide binary name for HOST=riscos -----------------------------
ifeq ($(HOST),riscos)
  # Binary is named "ncc,ff8", which is the file type for an executable.
  ifeq ($(TARGET),riscos26)
    BIN_SUFFIX := 26,ff8
  else
    BIN_SUFFIX := ,ff8
  endif

  # Objects are created in build/obj/riscos-native.
  OBJ_FLAVOUR := -native
endif # if HOST=riscos

# Target setup -----------------------------------------------------------------

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
OPTIONS_riscos26 := ccacorn
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
# HOST != riscos. ie. using host's compiler (clang or gcc)
ifneq ($(HOST),riscos)
CFLAGS := -O2 -std=gnu89 -fcommon -fno-strict-aliasing $(WFLAGS)
LDLIBS := -lm

DEPFLAGS = -MMD -MP -MF $(@:.o=.d)
endif # HOST != riscos

# TARGET=riscos or riscos26
ifneq (,$(filter riscos riscos26,$(TARGET)))
  # Flags for targeting RISC OS (cross-compiler or native)
  CFLAGS += -DCOMPILING_ON_ARM -DTARGET_IS_RISC_OS -DFOR_ACORN -D__acorn

  ifeq ($(TARGET),riscos26)
    # Configure the compiler (cross or native) to generate APCS-R (26bit).
    #
    # There's no flag for the inverse of NO_UNALIGNED_LOADS without modifying
    # the source, but aligned loads are the current default anyway.
    CFLAGS += -DPCS_DEFAULTS=0
  else
    # Configure the compiler (cross or native) to generate APCS-32.
    CFLAGS += -DPCS_DEFAULTS=3 -DNO_UNALIGNED_LOADS
  endif

  # TARGET=riscos/riscos26 HOST=riscos
  ifeq ($(HOST),riscos)
    # ie. flags passed to host's ncc-riscos or ncc-riscos26, to generate
    # ncc or n++ to run on RISC OS.
    CFLAGS += -DCOMPILING_ON_RISCOS -DCOMPILING_ON_RISC_OS -DHOST_IS_RISCOS

    ifeq ($(TARGET),riscos26)
      # 26-bit RISC OS: APCS-3, 26-bit, unaligned loads rotate
      CFLAGS += -apcs 3/26bit -za0
      STUBS_LIB := lib/stubs-26.a
    else
      # 32-bit RISC OS: APCS-3, 32-bit, FPE3, no unaligned loads.
      CFLAGS += -apcs 3/32bit/fpe3 -za1
      STUBS_LIB := lib/stubs.a
    endif

    LDLIBS := $(STUBS_LIB)

    # Make sure stubs library exists before linking the RISC OS-native compiler.
    $(BIN_NCC) $(BIN_NCPP) $(BIN_NTCC) \
    $(BIN_NTCPP) $(BIN_INTERP) $(BIN_CLBCOMP): $(STUBS_LIB)
  endif
endif

# TARGET=newton
ifeq ($(TARGET),newton)
CFLAGS += -Dpascal="" -DMSG_TOOL_NAME=\"$(BUILD_TOOL)\"
endif

# Extra defines per tool
CFLAGS_clbcomp := -DCALLABLE_COMPILER
CFLAGS_n++ := -DCPLUSPLUS
CFLAGS_nt++ := -DCPLUSPLUS

# --- Linker selection -------------------------------------------------

# Use drlink only when we are building a RISC OS-native compiler
# (supports AOF not ELF).
ifeq ($(HOST),riscos)
  LD := drlink
else
  LD := $(CC)
endif

# HOST_DIR contains host.h. Probably needs splitting into arm & riscos.
HOST_DIR := $(SRC_ROOT)/../ncc-support
SUPPORT_DIR := $(SRC_ROOT)/../ncc-support

INC_COMMON := \
  -I$(SRC_ROOT)/mip \
  -I$(SRC_ROOT)/cfe \
  -I$(SRC_ROOT)/armthumb \
  -I$(BACKEND_DIR) \
  -I$(SRC_ROOT)/util \
  -I$(HOST_DIR) \
  -I$(SRC_ROOT)/$(OPTIONS_DIR) \
  -I$(DERIVED_DIR)

# Norcroft (HOST=riscos) cannot direct dependency files with -MF, so
# generate them in a second pass using -M and redirect stdio.
# On non-RISC OS hosts, DEPCMD is a no-op and we rely on -MMD/-MP.
ifeq ($(HOST),riscos)
DEPCMD   = $(CC) $(CFLAGS) $(INC_COMMON) -M
DEPREDIR = > $(@:.o=.d)
else
DEPCMD   = @true
DEPREDIR =
endif

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

INTERP_SRCS := \
  interp/interp.c \
  mip/builtin.c mip/aetree.c mip/misc.c mip/store.c mip/bind.c mip/compiler.c \
  cfe/pp.c \
  $(CPPFE_SOURCES) \
  $(CFE_SOURCES) \

CLBCOMP_SRCS := \
	mip/aetree.c mip/misc.c mip/compiler.c clbcomp/clbcomp.c \
	clbcomp/clb_store.c cppfe/xsyn.c cppfe/xsem.c cppfe/xbuiltin.c \
	cppfe/xbind.c cppfe/overload.c cppfe/xlex.c cfe/simplify.c cfe/pp.c

SUPPORT_SRCS := \
  ncc-support/dde.c \
  ncc-support/dem.c \
  ncc-support/disass.c \
  ncc-support/disass-fpa.c \
  ncc-support/filestat.c \
  ncc-support/fname.c \
  ncc-support/ieeeflt.c \
  ncc-support/int64.c \
  ncc-support/msg.c \
  ncc-support/prgname.c \
  ncc-support/riscos.c \
  ncc-support/toolenv.c \
  ncc-support/trackfil.c \
  ncc-support/unmangle.c \

ifeq ($(HOST),riscos)
SUPPORT_SRCS += ncc-support/int64-runtime.c
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

CLIB_HDRS    += $(if $(filter riscos riscos26,$(TARGET)),$(CLIB_RISCOS_HDRS),)

OPTIONS_DIR  := $(if $(filter arm,$(TARGET)),$(OPTIONS_DEFAULT_DIR),$(OPTIONS_OVERRIDE_DIR))

CLIB_HDRS_DIR := external/clib/include/

# error lists
ERRS_H := \
	$(SRC_ROOT)/mip/miperrs.h \
	$(SRC_ROOT)/cfe/feerrs.h \
	$(SRC_ROOT)/armthumb/mcerrs.h

$(DERIVED_STAMP): $(DERIVED_SRCS) $(DERIVED_HDRS) | $(DERIVED_DIR)
	@touch $@

# When building a RISC OS-hosted compiler, ensure the host-built
# derived files exist before bootstrapping the cross ncc.
ifeq ($(HOST),riscos)
# Phony bootstrap target: builds the unix-hosted cross-compiler first.
BOOTSTRAP_NCC_RISCOS := bootstrap-ncc-riscos

# Recurse into Makefile to build host compiler without HOST=riscos.
$(BOOTSTRAP_NCC_RISCOS): $(DERIVED_STAMP)
	$(MAKE) ncc TARGET=$(TARGET) HOST=
endif

# ---- Host tools (built for and run on the build host regardless of TARGET)
CC_HOST       ?= cc
CFLAGS_HOST   ?= -O2 -std=gnu89 -fcommon -fno-strict-aliasing $(WFLAGS)
HOSTTOOLS_DIR := $(OUT_ROOT)/hosttools
GENHDRS_HOST  := $(HOSTTOOLS_DIR)/genhdrs
PEEPGEN_HOST  := $(HOSTTOOLS_DIR)/peepgen

# per-tool bundles ----------------
NCC_SRCS   := $(CC_COMMON) $(CFE_SOURCES)   $(ARM_SRCS)
NCPP_SRCS  := $(CC_COMMON) $(CPPFE_SOURCES) $(ARM_SRCS)
NTCC_SRCS  := $(CC_COMMON) $(CFE_SOURCES)   $(THUMB_SRCS)
NTCPP_SRCS := $(CC_COMMON) $(CPPFE_SOURCES) $(THUMB_SRCS)

# .o files in build/obj/<tool>/...
NCC_OBJS     := $(addprefix $(OBJ_DIR)/ncc/,$(NCC_SRCS:.c=.o))
NCPP_OBJS    := $(addprefix $(OBJ_DIR)/n++/,$(NCPP_SRCS:.c=.o))
NTCC_OBJS    := $(addprefix $(OBJ_DIR)/ntcc/,$(NTCC_SRCS:.c=.o))
NTCPP_OBJS   := $(addprefix $(OBJ_DIR)/nt++/,$(NTCPP_SRCS:.c=.o))
INTERP_OBJS  := $(addprefix $(OBJ_DIR)/interp/,$(INTERP_SRCS:.c=.o))
CLBCOMP_OBJS := $(addprefix $(OBJ_DIR)/clbcomp/,$(CLBCOMP_SRCS:.c=.o))
SUPPORT_OBJS := $(addprefix $(OBJ_DIR)/ncc-support/, $(notdir $(SUPPORT_SRCS:.c=.o)))

# Ensure generated sources exist before compiling anything that may include them
$(OBJ_DIR)/ncc/%.o \
$(OBJ_DIR)/n++/%.o \
$(OBJ_DIR)/ntcc/%.o \
$(OBJ_DIR)/nt++/%.o \
$(OBJ_DIR)/interp/%.o \
$(OBJ_DIR)/clbcomp/%.o: \
$(OBJ_DIR)/ncc-support/%.o | $(DERIVED_STAMP)

# peeppat.c is generated and #included by peephole.c; do not compile it separately.
# Ensure each backend’s peephole.o is rebuilt if peeppat.c changes.
$(OBJ_DIR)/ncc/peephole.o \
$(OBJ_DIR)/n++/peephole.o \
$(OBJ_DIR)/ntcc/peephole.o \
$(OBJ_DIR)/nt++/peephole.o: $(DERIVED_DIR)/peeppat.c

# headers.c is generated and compiled once per OBJ_DIR, not per tool.
HEADERS_OBJ := $(OBJ_DIR)/headers.o

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
	@echo "TARGET=$(TARGET) WARN=$(WARN)"
	@echo "HOST=$(HOST)"
	@echo "BUILD_TOOL=$(BUILD_TOOL)"
	@echo "BACKEND=$(BACKEND)"
	@echo "OPTIONS_DIR=$(OPTIONS_DIR)"
	@echo "HOST_DIR=$(HOST_DIR)"
	@echo "SUPPORT_DIR=$(SUPPORT_DIR)"
	@echo "DERIVED_DIR=$(DERIVED_DIR)"
	@echo "OBJ_DIR=$(OBJ_DIR) BIN_DIR=$(BIN_DIR)"
	@echo "BIN_SUFFIX=$(BIN_SUFFIX)"
	@echo "BINARIES: ncc=$(BIN_NCC) n++=$(BIN_NCPP) ntcc=$(BIN_NTCC) nt++=$(BIN_NTCPP) npp=$(BIN_INTERP) clbcomp=$(BIN_CLBCOMP)"
	@echo "HOSTTOOLS_DIR=$(HOSTTOOLS_DIR)"
	@echo "GENHDRS_HOST=$(GENHDRS_HOST) PEEPGEN_HOST=$(PEEPGEN_HOST)"

# ------------- compile rules ------------------
# Provide explicit per-subdir patterns so make can find the sources
# and place objects in matching subfolders under obj/<tool>/...

# Helper macros to pick include dir for each tool kind
INTERP_INCS    := -I$(SRC_ROOT)/$(OPTIONS_INTERP)
CLB_INCS       := -I$(SRC_ROOT)/clbcomp

# ncc: anything under $(SRC_ROOT) (mip/, cfe/, arm/, armthumb/, cppfe/)
$(OBJ_DIR)/ncc/%.o: $(SRC_ROOT)/%.c $(BOOTSTRAP_NCC_RISCOS) | $(DERIVED_STAMP)
	@mkdir -p $(dir $@)
	$(CC) $(CFLAGS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
	$(DEPCMD) $< $(DEPREDIR)

# n++ (ARM C++)
$(OBJ_DIR)/n++/%.o: $(SRC_ROOT)/%.c $(BOOTSTRAP_NCC_RISCOS) | $(DERIVED_STAMP)
	@mkdir -p $(dir $@)
	$(CC) $(CFLAGS) $(CFLAGS_n++) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
	$(DEPCMD) $(CFLAGS_n++) $< $(DEPREDIR)

# ntcc (Thumb C)
$(OBJ_DIR)/ntcc/%.o: $(SRC_ROOT)/%.c $(BOOTSTRAP_NCC_RISCOS) | $(DERIVED_STAMP)
	@mkdir -p $(dir $@)
	$(CC) $(CFLAGS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
	$(DEPCMD) $< $(DEPREDIR)

# nt++ (Thumb C++)
$(OBJ_DIR)/nt++/%.o: $(SRC_ROOT)/%.c $(BOOTSTRAP_NCC_RISCOS) | $(DERIVED_STAMP)
	@mkdir -p $(dir $@)
	$(CC) $(CFLAGS) $(CFLAGS_nt++) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
	$(DEPCMD) $(CFLAGS_nt++) $< $(DEPREDIR)

# interp
$(OBJ_DIR)/interp/%.o: $(SRC_ROOT)/%.c $(BOOTSTRAP_NCC_RISCOS) | $(DERIVED_STAMP)
	@mkdir -p $(dir $@)
	$(CC) $(CFLAGS) $(INC_COMMON) $(INTERP_INCS) $(DEPFLAGS) -c $< -o $@
	$(DEPCMD) $(INTERP_INCS) $< $(DEPREDIR)

# clbcomp
$(OBJ_DIR)/clbcomp/%.o: $(SRC_ROOT)/%.c $(BOOTSTRAP_NCC_RISCOS) | $(DERIVED_STAMP)
	@mkdir -p $(dir $@)
	$(CC) $(CFLAGS) $(CFLAGS_clbcomp) $(INC_COMMON) $(CLB_INCS) $(DEPFLAGS) -c $< -o $@
	$(DEPCMD) $(CFLAGS_clbcomp) $(CLB_INCS) $< $(DEPREDIR)

# support files (shared by all tools for a given OBJ_DIR)
$(OBJ_DIR)/ncc-support/%.o: $(SUPPORT_DIR)/%.c $(BOOTSTRAP_NCC_RISCOS) | $(DERIVED_STAMP)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
	$(DEPCMD) $< $(DEPREDIR)

# headers.c (shared by all tools for a given OBJ_DIR)
$(HEADERS_OBJ): $(DERIVED_DIR)/headers.c $(BOOTSTRAP_NCC_RISCOS) | $(DERIVED_STAMP)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(INC_COMMON) $(DEPFLAGS) -c $< -o $@
	$(DEPCMD) $< $(DEPREDIR)

# ------------- link rules ---------------------
$(BIN_NCC):     $(NCC_OBJS)     $(SUPPORT_OBJS) $(HEADERS_OBJ) | $(BIN_DIR)
	$(LD) $(LDFLAGS) -o $@ $^ $(LDLIBS)

$(BIN_NCPP):    $(NCPP_OBJS)    $(SUPPORT_OBJS) $(HEADERS_OBJ) | $(BIN_DIR)
	$(LD) $(LDFLAGS) -o $@ $^ $(LDLIBS)

$(BIN_NTCC):    $(NTCC_OBJS)    $(SUPPORT_OBJS) $(HEADERS_OBJ) | $(BIN_DIR)
	$(LD) $(LDFLAGS) -o $@ $^ $(LDLIBS)

$(BIN_NTCPP):   $(NTCPP_OBJS)   $(SUPPORT_OBJS) $(HEADERS_OBJ) | $(BIN_DIR)
	$(LD) $(LDFLAGS) -o $@ $^ $(LDLIBS)

$(BIN_INTERP):  $(INTERP_OBJS)  $(HEADERS_OBJ) | $(BIN_DIR)
	$(LD) $(LDFLAGS) -o $@ $^ $(LDLIBS)

$(BIN_CLBCOMP): $(CLBCOMP_OBJS) $(HEADERS_OBJ) | $(BIN_DIR)
	$(LD) $(LDFLAGS) -o $@ $^ $(LDLIBS)

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
DEPS := $(NCC_OBJS:.o=.d) \
        $(NCPP_OBJS:.o=.d) \
        $(NTCC_OBJS:.o=.d) \
        $(NTCPP_OBJS:.o=.d) \
        $(INTERP_OBJS:.o=.d) \
        $(CLBCOMP_OBJS:.o=.d) \
        $(SUPPORT_OBJS:.o=.d) \
        $(HEADERS_OBJ:.o=.d)

-include $(DEPS)

# hygiene ------------------------
clean:
	$(RM) -r $(OUT_ROOT)/obj $(BIN_DIR)

distclean: clean
	$(RM) -r $(DERIVED_ROOT) $(HOSTTOOLS_DIR)
