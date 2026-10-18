/* common cpp predefines */
#define    CPPADD    { "-Dunix", "-Dsgi", "-D__SVR4", "-D__unix", "-D__sgi", "-D__ELF__", NULL }

/* host-dependent */
#define CRT0        "crt1.o"
#define CRTBEGIN    0
#define CRTEND        0
#define CRTI        0
#define    GCRT0       0
#define    RCRT0       0

/* host-independent */
#define    DYNLINKARG    "-Bdynamic"
#define    DYNLINKLIB    "/lib32/rld"

#if defined(mach_mips)
#define    CPPMDADD { "-D__mips__", NULL, }
#else
#error defines for arch missing
#endif
