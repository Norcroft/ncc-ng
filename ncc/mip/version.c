/* mip/version.c
 * Copyright (C) Acorn Computers Ltd., 1988-1990.
 * Copyright (C) Advanced RISC Machines Limited, 1991-1992.
 * Copyright (C) Codemist Ltd, 1987-1994.
 * SPDX-Licence-Identifier: Apache-2.0
 * Defines the version string and banner for the Codemist or OEM compiler.
 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

#ifdef __STDC__
#  include <string.h>
#else
#  include <strings.h>
#endif
#include "globals.h"                    /* for TARGET_MACHINE */
#include "version.h"
#include "fevsn.h"
#include "mipvsn.h"
#include "mcvsn.h"

#ifndef __DATE__
#  include "datenow.h"
#endif
#ifndef __TIME__
#  define __TIME__ ""
#endif

#ifdef __STDC__
#  ifndef NO_STATIC_BANNER
#    define STATIC_BANNER 1       /* no string concatenation.             */
#  endif
#endif

/* AM: company-specific version strings should appear in options.h.     */
#undef VERSION_STRING
#ifdef RELEASE_VSN
#  define VERSION_STRING RELEASE_VSN
#else
#  ifdef NON_RELEASE_VSN
#    define VERSION_STRING NON_RELEASE_VSN
#  else
#    ifdef __STDC__
#      define VERSION_STRING FE_VERSION "/" MIP_VERSION "/" MC_VERSION
#    else
#      define VERSION_STRING "<unspecified>"
#    endif
#  endif
#endif


#ifdef __APPLE__
#  define HOST_SYSTEM "macOS"
#elif __linux__
#  define HOST_SYSTEM "Linux"
#elif __CC_NORCROFT
#  define HOST_SYSTEM "RISCiX"
#endif

#ifdef HOST_SYSTEM
#  define BRACKETED_HOST " (" HOST_SYSTEM ")"
#else
#  define BRACKETED_HOST ""
#endif

/* Note the comment in mip/version.h re the 4 nulls at end of string.   */

#ifdef STATIC_BANNER

static char cc_banner[] =  "Norcroft-NG " \
                           TARGET_SYSTEM " " TARGET_MACHINE " " LANGUAGE \
                           " vsn " VERSION_STRING BRACKETED_HOST \
                           " [" __DATE__ "]\0\0\0";

char *version_banner(void)
{
  return cc_banner;
}

#else  /* ! STATIC_BANNER */

/*
 * Can't build the banner using ANSI string concatenation,
 * so build it dynamically instead.
 */

static char cc_banner[128] = "";        /* expression instead of 128?   */

char *version_banner(void)
{   if (cc_banner[0]=='\0')
      {
        sprintf(cc_banner, "Norcroft-NG %s %s %s vsn %s%s [%s]\0\0\0",
                           TARGET_SYSTEM, TARGET_MACHINE, LANGUAGE,
                           VERSION_STRING, BRACKETED_HOST, __DATE__);
      }
    return(cc_banner);
}

#endif /* STATIC_BANNER */

/* end of mip/version.c */
