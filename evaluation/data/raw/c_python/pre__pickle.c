# 1 "_pickle.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "_pickle.c"
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 1






# 1 "/Users/parrt/tmp/Python-3.3.1/Include/patchlevel.h" 1
# 8 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/pyconfig.h" 1
# 9 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/pymacconfig.h" 1
# 10 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2

# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/limits.h" 1 3 4






# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/syslimits.h" 1 3 4
# 8 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/limits.h" 2 3 4







# 1 "/usr/include/limits.h" 1 3 4
# 63 "/usr/include/limits.h" 3 4
# 1 "/usr/include/sys/cdefs.h" 1 3 4
# 417 "/usr/include/sys/cdefs.h" 3 4
# 1 "/usr/include/sys/_symbol_aliasing.h" 1 3 4
# 418 "/usr/include/sys/cdefs.h" 2 3 4
# 494 "/usr/include/sys/cdefs.h" 3 4
# 1 "/usr/include/sys/_posix_availability.h" 1 3 4
# 495 "/usr/include/sys/cdefs.h" 2 3 4
# 64 "/usr/include/limits.h" 2 3 4
# 1 "/usr/include/machine/limits.h" 1 3 4





# 1 "/usr/include/i386/limits.h" 1 3 4
# 40 "/usr/include/i386/limits.h" 3 4
# 1 "/usr/include/i386/_limits.h" 1 3 4
# 41 "/usr/include/i386/limits.h" 2 3 4
# 7 "/usr/include/machine/limits.h" 2 3 4
# 65 "/usr/include/limits.h" 2 3 4
# 1 "/usr/include/sys/syslimits.h" 1 3 4
# 66 "/usr/include/limits.h" 2 3 4
# 16 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/limits.h" 2 3 4
# 12 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 25 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h"
# 1 "/usr/include/stdio.h" 1 3 4
# 65 "/usr/include/stdio.h" 3 4
# 1 "/usr/include/Availability.h" 1 3 4
# 141 "/usr/include/Availability.h" 3 4
# 1 "/usr/include/AvailabilityInternal.h" 1 3 4
# 142 "/usr/include/Availability.h" 2 3 4
# 66 "/usr/include/stdio.h" 2 3 4

# 1 "/usr/include/_types.h" 1 3 4
# 27 "/usr/include/_types.h" 3 4
# 1 "/usr/include/sys/_types.h" 1 3 4
# 33 "/usr/include/sys/_types.h" 3 4
# 1 "/usr/include/machine/_types.h" 1 3 4
# 32 "/usr/include/machine/_types.h" 3 4
# 1 "/usr/include/i386/_types.h" 1 3 4
# 37 "/usr/include/i386/_types.h" 3 4
typedef signed char __int8_t;



typedef unsigned char __uint8_t;
typedef short __int16_t;
typedef unsigned short __uint16_t;
typedef int __int32_t;
typedef unsigned int __uint32_t;
typedef long long __int64_t;
typedef unsigned long long __uint64_t;

typedef long __darwin_intptr_t;
typedef unsigned int __darwin_natural_t;
# 70 "/usr/include/i386/_types.h" 3 4
typedef int __darwin_ct_rune_t;





typedef union {
 char __mbstate8[128];
 long long _mbstateL;
} __mbstate_t;

typedef __mbstate_t __darwin_mbstate_t;


typedef long int __darwin_ptrdiff_t;





typedef long unsigned int __darwin_size_t;





typedef __builtin_va_list __darwin_va_list;





typedef int __darwin_wchar_t;




typedef __darwin_wchar_t __darwin_rune_t;


typedef int __darwin_wint_t;




typedef unsigned long __darwin_clock_t;
typedef __uint32_t __darwin_socklen_t;
typedef long __darwin_ssize_t;
typedef long __darwin_time_t;
# 33 "/usr/include/machine/_types.h" 2 3 4
# 34 "/usr/include/sys/_types.h" 2 3 4
# 58 "/usr/include/sys/_types.h" 3 4
struct __darwin_pthread_handler_rec
{
 void (*__routine)(void *);
 void *__arg;
 struct __darwin_pthread_handler_rec *__next;
};
struct _opaque_pthread_attr_t { long __sig; char __opaque[56]; };
struct _opaque_pthread_cond_t { long __sig; char __opaque[40]; };
struct _opaque_pthread_condattr_t { long __sig; char __opaque[8]; };
struct _opaque_pthread_mutex_t { long __sig; char __opaque[56]; };
struct _opaque_pthread_mutexattr_t { long __sig; char __opaque[8]; };
struct _opaque_pthread_once_t { long __sig; char __opaque[8]; };
struct _opaque_pthread_rwlock_t { long __sig; char __opaque[192]; };
struct _opaque_pthread_rwlockattr_t { long __sig; char __opaque[16]; };
struct _opaque_pthread_t { long __sig; struct __darwin_pthread_handler_rec *__cleanup_stack; char __opaque[1168]; };
# 94 "/usr/include/sys/_types.h" 3 4
typedef __int64_t __darwin_blkcnt_t;
typedef __int32_t __darwin_blksize_t;
typedef __int32_t __darwin_dev_t;
typedef unsigned int __darwin_fsblkcnt_t;
typedef unsigned int __darwin_fsfilcnt_t;
typedef __uint32_t __darwin_gid_t;
typedef __uint32_t __darwin_id_t;
typedef __uint64_t __darwin_ino64_t;

typedef __darwin_ino64_t __darwin_ino_t;



typedef __darwin_natural_t __darwin_mach_port_name_t;
typedef __darwin_mach_port_name_t __darwin_mach_port_t;
typedef __uint16_t __darwin_mode_t;
typedef __int64_t __darwin_off_t;
typedef __int32_t __darwin_pid_t;
typedef struct _opaque_pthread_attr_t
   __darwin_pthread_attr_t;
typedef struct _opaque_pthread_cond_t
   __darwin_pthread_cond_t;
typedef struct _opaque_pthread_condattr_t
   __darwin_pthread_condattr_t;
typedef unsigned long __darwin_pthread_key_t;
typedef struct _opaque_pthread_mutex_t
   __darwin_pthread_mutex_t;
typedef struct _opaque_pthread_mutexattr_t
   __darwin_pthread_mutexattr_t;
typedef struct _opaque_pthread_once_t
   __darwin_pthread_once_t;
typedef struct _opaque_pthread_rwlock_t
   __darwin_pthread_rwlock_t;
typedef struct _opaque_pthread_rwlockattr_t
   __darwin_pthread_rwlockattr_t;
typedef struct _opaque_pthread_t
   *__darwin_pthread_t;
typedef __uint32_t __darwin_sigset_t;
typedef __int32_t __darwin_suseconds_t;
typedef __uint32_t __darwin_uid_t;
typedef __uint32_t __darwin_useconds_t;
typedef unsigned char __darwin_uuid_t[16];
typedef char __darwin_uuid_string_t[37];
# 28 "/usr/include/_types.h" 2 3 4
# 39 "/usr/include/_types.h" 3 4
typedef int __darwin_nl_item;
typedef int __darwin_wctrans_t;

typedef __uint32_t __darwin_wctype_t;
# 68 "/usr/include/stdio.h" 2 3 4





typedef __darwin_va_list va_list;




typedef __darwin_size_t size_t;






typedef __darwin_off_t fpos_t;
# 96 "/usr/include/stdio.h" 3 4
struct __sbuf {
 unsigned char *_base;
 int _size;
};


struct __sFILEX;
# 130 "/usr/include/stdio.h" 3 4
typedef struct __sFILE {
 unsigned char *_p;
 int _r;
 int _w;
 short _flags;
 short _file;
 struct __sbuf _bf;
 int _lbfsize;


 void *_cookie;
 int (*_close)(void *);
 int (*_read) (void *, char *, int);
 fpos_t (*_seek) (void *, fpos_t, int);
 int (*_write)(void *, const char *, int);


 struct __sbuf _ub;
 struct __sFILEX *_extra;
 int _ur;


 unsigned char _ubuf[3];
 unsigned char _nbuf[1];


 struct __sbuf _lb;


 int _blksize;
 fpos_t _offset;
} FILE;


extern FILE *__stdinp;
extern FILE *__stdoutp;
extern FILE *__stderrp;

# 238 "/usr/include/stdio.h" 3 4

void clearerr(FILE *);
int fclose(FILE *);
int feof(FILE *);
int ferror(FILE *);
int fflush(FILE *);
int fgetc(FILE *);
int fgetpos(FILE * , fpos_t *);
char *fgets(char * , int, FILE *);

FILE *fopen(const char * , const char * ) __asm("_" "fopen" "$DARWIN_EXTSN");



int fprintf(FILE * , const char * , ...) __attribute__((__format__ (__printf__, 2, 3)));
int fputc(int, FILE *);
int fputs(const char * , FILE * ) __asm("_" "fputs" );
size_t fread(void * , size_t, size_t, FILE * );
FILE *freopen(const char * , const char * ,
                 FILE * ) __asm("_" "freopen" );
int fscanf(FILE * , const char * , ...) __attribute__((__format__ (__scanf__, 2, 3)));
int fseek(FILE *, long, int);
int fsetpos(FILE *, const fpos_t *);
long ftell(FILE *);
size_t fwrite(const void * , size_t, size_t, FILE * ) __asm("_" "fwrite" );
int getc(FILE *);
int getchar(void);
char *gets(char *);
void perror(const char *);
int printf(const char * , ...) __attribute__((__format__ (__printf__, 1, 2)));
int putc(int, FILE *);
int putchar(int);
int puts(const char *);
int remove(const char *);
int rename (const char *, const char *);
void rewind(FILE *);
int scanf(const char * , ...) __attribute__((__format__ (__scanf__, 1, 2)));
void setbuf(FILE * , char * );
int setvbuf(FILE * , char * , int, size_t);
int sprintf(char * , const char * , ...) __attribute__((__format__ (__printf__, 2, 3)));
int sscanf(const char * , const char * , ...) __attribute__((__format__ (__scanf__, 2, 3)));
FILE *tmpfile(void);
char *tmpnam(char *);
int ungetc(int, FILE *);
int vfprintf(FILE * , const char * , va_list) __attribute__((__format__ (__printf__, 2, 0)));
int vprintf(const char * , va_list) __attribute__((__format__ (__printf__, 1, 0)));
int vsprintf(char * , const char * , va_list) __attribute__((__format__ (__printf__, 2, 0)));

# 296 "/usr/include/stdio.h" 3 4




char *ctermid(char *);



FILE *fdopen(int, const char *) __asm("_" "fdopen" "$DARWIN_EXTSN");



int fileno(FILE *);

# 318 "/usr/include/stdio.h" 3 4

int pclose(FILE *);

FILE *popen(const char *, const char *) __asm("_" "popen" "$DARWIN_EXTSN");




# 340 "/usr/include/stdio.h" 3 4

int __srget(FILE *);
int __svfscanf(FILE *, const char *, va_list) __attribute__((__format__ (__scanf__, 2, 0)));
int __swbuf(int, FILE *);








static __inline int __sputc(int _c, FILE *_p) {
 if (--_p->_w >= 0 || (_p->_w >= _p->_lbfsize && (char)_c != '\n'))
  return (*_p->_p++ = _c);
 else
  return (__swbuf(_c, _p));
}
# 377 "/usr/include/stdio.h" 3 4

void flockfile(FILE *);
int ftrylockfile(FILE *);
void funlockfile(FILE *);
int getc_unlocked(FILE *);
int getchar_unlocked(void);
int putc_unlocked(int, FILE *);
int putchar_unlocked(int);



int getw(FILE *);
int putw(int, FILE *);


char *tempnam(const char *, const char *) __asm("_" "tempnam" );

# 414 "/usr/include/stdio.h" 3 4
typedef __darwin_off_t off_t;



int fseeko(FILE *, off_t, int);
off_t ftello(FILE *);





int snprintf(char * , size_t, const char * , ...) __attribute__((__format__ (__printf__, 3, 4)));
int vfscanf(FILE * , const char * , va_list) __attribute__((__format__ (__scanf__, 2, 0)));
int vscanf(const char * , va_list) __attribute__((__format__ (__scanf__, 1, 0)));
int vsnprintf(char * , size_t, const char * , va_list) __attribute__((__format__ (__printf__, 3, 0)));
int vsscanf(const char * , const char * , va_list) __attribute__((__format__ (__scanf__, 2, 0)));

# 442 "/usr/include/stdio.h" 3 4
typedef __darwin_ssize_t ssize_t;



int dprintf(int, const char * , ...) __attribute__((__format__ (__printf__, 2, 3))) __attribute__((visibility("default")));
int vdprintf(int, const char * , va_list) __attribute__((__format__ (__printf__, 2, 0))) __attribute__((visibility("default")));
ssize_t getdelim(char ** , size_t * , int, FILE * ) __attribute__((visibility("default")));
ssize_t getline(char ** , size_t * , FILE * ) __attribute__((visibility("default")));









extern const int sys_nerr;
extern const char *const sys_errlist[];

int asprintf(char **, const char *, ...) __attribute__((__format__ (__printf__, 2, 3)));
char *ctermid_r(char *);
char *fgetln(FILE *, size_t *);
const char *fmtcheck(const char *, const char *);
int fpurge(FILE *);
void setbuffer(FILE *, char *, int);
int setlinebuf(FILE *);
int vasprintf(char **, const char *, va_list) __attribute__((__format__ (__printf__, 2, 0)));
FILE *zopen(const char *, const char *, int);





FILE *funopen(const void *,
                 int (*)(void *, char *, int),
                 int (*)(void *, const char *, int),
                 fpos_t (*)(void *, fpos_t, int),
                 int (*)(void *));

# 499 "/usr/include/stdio.h" 3 4
# 1 "/usr/include/secure/_stdio.h" 1 3 4
# 31 "/usr/include/secure/_stdio.h" 3 4
# 1 "/usr/include/secure/_common.h" 1 3 4
# 32 "/usr/include/secure/_stdio.h" 2 3 4
# 45 "/usr/include/secure/_stdio.h" 3 4
extern int __sprintf_chk (char * , int, size_t,
     const char * , ...)
  ;




extern int __snprintf_chk (char * , size_t, int, size_t,
      const char * , ...)
  ;





extern int __vsprintf_chk (char * , int, size_t,
      const char * , va_list)
  ;




extern int __vsnprintf_chk (char * , size_t, int, size_t,
       const char * , va_list)
  ;
# 500 "/usr/include/stdio.h" 2 3 4
# 26 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2




# 1 "/usr/include/string.h" 1 3 4
# 79 "/usr/include/string.h" 3 4

void *memchr(const void *, int, size_t);
int memcmp(const void *, const void *, size_t);
void *memcpy(void *, const void *, size_t);
void *memmove(void *, const void *, size_t);
void *memset(void *, int, size_t);
char *strcat(char *, const char *);
char *strchr(const char *, int);
int strcmp(const char *, const char *);
int strcoll(const char *, const char *);
char *strcpy(char *, const char *);
size_t strcspn(const char *, const char *);
char *strerror(int) __asm("_" "strerror" );
size_t strlen(const char *);
char *strncat(char *, const char *, size_t);
int strncmp(const char *, const char *, size_t);
char *strncpy(char *, const char *, size_t);
char *strpbrk(const char *, const char *);
char *strrchr(const char *, int);
size_t strspn(const char *, const char *);
char *strstr(const char *, const char *);
char *strtok(char *, const char *);
size_t strxfrm(char *, const char *, size_t);

# 113 "/usr/include/string.h" 3 4

char *strtok_r(char *, const char *, char **);

# 125 "/usr/include/string.h" 3 4

int strerror_r(int, char *, size_t);
char *strdup(const char *);
void *memccpy(void *, const void *, int, size_t);

# 139 "/usr/include/string.h" 3 4

char *stpcpy(char *, const char *);
char *stpncpy(char *, const char *, size_t) __attribute__((visibility("default")));
char *strndup(const char *, size_t) __attribute__((visibility("default")));
size_t strnlen(const char *, size_t) __attribute__((visibility("default")));
char *strsignal(int sig);

# 158 "/usr/include/string.h" 3 4

void *memmem(const void *, size_t, const void *, size_t) __attribute__((visibility("default")));
void memset_pattern4(void *, const void *, size_t) __attribute__((visibility("default")));
void memset_pattern8(void *, const void *, size_t) __attribute__((visibility("default")));
void memset_pattern16(void *, const void *, size_t) __attribute__((visibility("default")));

char *strcasestr(const char *, const char *);
char *strnstr(const char *, const char *, size_t);
size_t strlcat(char *, const char *, size_t);
size_t strlcpy(char *, const char *, size_t);
void strmode(int, char *);
char *strsep(char **, const char *);


void swab(const void * , void * , ssize_t);







# 1 "/usr/include/strings.h" 1 3 4
# 71 "/usr/include/strings.h" 3 4



int bcmp(const void *, const void *, size_t) ;
void bcopy(const void *, void *, size_t) ;
void bzero(void *, size_t) ;
char *index(const char *, int) ;
char *rindex(const char *, int) ;


int ffs(int);
int strcasecmp(const char *, const char *);
int strncasecmp(const char *, const char *, size_t);





int ffsl(long) __attribute__((visibility("default")));
int fls(int) __attribute__((visibility("default")));
int flsl(long) __attribute__((visibility("default")));


# 1 "/usr/include/string.h" 1 3 4
# 95 "/usr/include/strings.h" 2 3 4
# 181 "/usr/include/string.h" 2 3 4
# 190 "/usr/include/string.h" 3 4
# 1 "/usr/include/secure/_string.h" 1 3 4
# 58 "/usr/include/secure/_string.h" 3 4
static __inline void *
__inline_memcpy_chk (void *__dest, const void *__src, size_t __len)
{
  return __builtin___memcpy_chk (__dest, __src, __len, __builtin_object_size (__dest, 0));
}






static __inline void *
__inline_memmove_chk (void *__dest, const void *__src, size_t __len)
{
  return __builtin___memmove_chk (__dest, __src, __len, __builtin_object_size (__dest, 0));
}






static __inline void *
__inline_memset_chk (void *__dest, int __val, size_t __len)
{
  return __builtin___memset_chk (__dest, __val, __len, __builtin_object_size (__dest, 0));
}






static __inline char *
__inline_strcpy_chk (char * __dest, const char * __src)
{
  return __builtin___strcpy_chk (__dest, __src, __builtin_object_size (__dest, 2 > 1));
}







static __inline char *
__inline_stpcpy_chk (char *__dest, const char *__src)
{
  return __builtin___stpcpy_chk (__dest, __src, __builtin_object_size (__dest, 2 > 1));
}






static __inline char *
__inline_stpncpy_chk (char * __dest, const char * __src,
        size_t __len)
{
  return __builtin___stpncpy_chk (__dest, __src, __len, __builtin_object_size (__dest, 2 > 1));
}







static __inline char *
__inline_strncpy_chk (char * __dest, const char * __src,
        size_t __len)
{
  return __builtin___strncpy_chk (__dest, __src, __len, __builtin_object_size (__dest, 2 > 1));
}






static __inline char *
__inline_strcat_chk (char * __dest, const char * __src)
{
  return __builtin___strcat_chk (__dest, __src, __builtin_object_size (__dest, 2 > 1));
}







static __inline char *
__inline_strncat_chk (char * __dest, const char * __src,
        size_t __len)
{
  return __builtin___strncat_chk (__dest, __src, __len, __builtin_object_size (__dest, 2 > 1));
}
# 191 "/usr/include/string.h" 2 3 4
# 31 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2

# 1 "/usr/include/errno.h" 1 3 4
# 23 "/usr/include/errno.h" 3 4
# 1 "/usr/include/sys/errno.h" 1 3 4
# 74 "/usr/include/sys/errno.h" 3 4

extern int * __error(void);


# 24 "/usr/include/errno.h" 2 3 4
# 33 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2

# 1 "/usr/include/stdlib.h" 1 3 4
# 65 "/usr/include/stdlib.h" 3 4
# 1 "/usr/include/sys/wait.h" 1 3 4
# 79 "/usr/include/sys/wait.h" 3 4
typedef enum {
 P_ALL,
 P_PID,
 P_PGID
} idtype_t;






typedef __darwin_pid_t pid_t;




typedef __darwin_id_t id_t;
# 116 "/usr/include/sys/wait.h" 3 4
# 1 "/usr/include/sys/signal.h" 1 3 4
# 73 "/usr/include/sys/signal.h" 3 4
# 1 "/usr/include/sys/appleapiopts.h" 1 3 4
# 74 "/usr/include/sys/signal.h" 2 3 4







# 1 "/usr/include/machine/signal.h" 1 3 4
# 32 "/usr/include/machine/signal.h" 3 4
# 1 "/usr/include/i386/signal.h" 1 3 4
# 39 "/usr/include/i386/signal.h" 3 4
typedef int sig_atomic_t;
# 55 "/usr/include/i386/signal.h" 3 4
# 1 "/usr/include/i386/_structs.h" 1 3 4
# 56 "/usr/include/i386/signal.h" 2 3 4
# 33 "/usr/include/machine/signal.h" 2 3 4
# 82 "/usr/include/sys/signal.h" 2 3 4
# 148 "/usr/include/sys/signal.h" 3 4
# 1 "/usr/include/sys/_structs.h" 1 3 4
# 57 "/usr/include/sys/_structs.h" 3 4
# 1 "/usr/include/machine/_structs.h" 1 3 4
# 29 "/usr/include/machine/_structs.h" 3 4
# 1 "/usr/include/i386/_structs.h" 1 3 4
# 38 "/usr/include/i386/_structs.h" 3 4
# 1 "/usr/include/mach/i386/_structs.h" 1 3 4
# 43 "/usr/include/mach/i386/_structs.h" 3 4
struct __darwin_i386_thread_state
{
    unsigned int __eax;
    unsigned int __ebx;
    unsigned int __ecx;
    unsigned int __edx;
    unsigned int __edi;
    unsigned int __esi;
    unsigned int __ebp;
    unsigned int __esp;
    unsigned int __ss;
    unsigned int __eflags;
    unsigned int __eip;
    unsigned int __cs;
    unsigned int __ds;
    unsigned int __es;
    unsigned int __fs;
    unsigned int __gs;
};
# 89 "/usr/include/mach/i386/_structs.h" 3 4
struct __darwin_fp_control
{
    unsigned short __invalid :1,
        __denorm :1,
    __zdiv :1,
    __ovrfl :1,
    __undfl :1,
    __precis :1,
      :2,
    __pc :2,





    __rc :2,






             :1,
      :3;
};
typedef struct __darwin_fp_control __darwin_fp_control_t;
# 147 "/usr/include/mach/i386/_structs.h" 3 4
struct __darwin_fp_status
{
    unsigned short __invalid :1,
        __denorm :1,
    __zdiv :1,
    __ovrfl :1,
    __undfl :1,
    __precis :1,
    __stkflt :1,
    __errsumm :1,
    __c0 :1,
    __c1 :1,
    __c2 :1,
    __tos :3,
    __c3 :1,
    __busy :1;
};
typedef struct __darwin_fp_status __darwin_fp_status_t;
# 191 "/usr/include/mach/i386/_structs.h" 3 4
struct __darwin_mmst_reg
{
 char __mmst_reg[10];
 char __mmst_rsrv[6];
};
# 210 "/usr/include/mach/i386/_structs.h" 3 4
struct __darwin_xmm_reg
{
 char __xmm_reg[16];
};
# 232 "/usr/include/mach/i386/_structs.h" 3 4
struct __darwin_i386_float_state
{
 int __fpu_reserved[2];
 struct __darwin_fp_control __fpu_fcw;
 struct __darwin_fp_status __fpu_fsw;
 __uint8_t __fpu_ftw;
 __uint8_t __fpu_rsrv1;
 __uint16_t __fpu_fop;
 __uint32_t __fpu_ip;
 __uint16_t __fpu_cs;
 __uint16_t __fpu_rsrv2;
 __uint32_t __fpu_dp;
 __uint16_t __fpu_ds;
 __uint16_t __fpu_rsrv3;
 __uint32_t __fpu_mxcsr;
 __uint32_t __fpu_mxcsrmask;
 struct __darwin_mmst_reg __fpu_stmm0;
 struct __darwin_mmst_reg __fpu_stmm1;
 struct __darwin_mmst_reg __fpu_stmm2;
 struct __darwin_mmst_reg __fpu_stmm3;
 struct __darwin_mmst_reg __fpu_stmm4;
 struct __darwin_mmst_reg __fpu_stmm5;
 struct __darwin_mmst_reg __fpu_stmm6;
 struct __darwin_mmst_reg __fpu_stmm7;
 struct __darwin_xmm_reg __fpu_xmm0;
 struct __darwin_xmm_reg __fpu_xmm1;
 struct __darwin_xmm_reg __fpu_xmm2;
 struct __darwin_xmm_reg __fpu_xmm3;
 struct __darwin_xmm_reg __fpu_xmm4;
 struct __darwin_xmm_reg __fpu_xmm5;
 struct __darwin_xmm_reg __fpu_xmm6;
 struct __darwin_xmm_reg __fpu_xmm7;
 char __fpu_rsrv4[14*16];
 int __fpu_reserved1;
};


struct __darwin_i386_avx_state
{
 int __fpu_reserved[2];
 struct __darwin_fp_control __fpu_fcw;
 struct __darwin_fp_status __fpu_fsw;
 __uint8_t __fpu_ftw;
 __uint8_t __fpu_rsrv1;
 __uint16_t __fpu_fop;
 __uint32_t __fpu_ip;
 __uint16_t __fpu_cs;
 __uint16_t __fpu_rsrv2;
 __uint32_t __fpu_dp;
 __uint16_t __fpu_ds;
 __uint16_t __fpu_rsrv3;
 __uint32_t __fpu_mxcsr;
 __uint32_t __fpu_mxcsrmask;
 struct __darwin_mmst_reg __fpu_stmm0;
 struct __darwin_mmst_reg __fpu_stmm1;
 struct __darwin_mmst_reg __fpu_stmm2;
 struct __darwin_mmst_reg __fpu_stmm3;
 struct __darwin_mmst_reg __fpu_stmm4;
 struct __darwin_mmst_reg __fpu_stmm5;
 struct __darwin_mmst_reg __fpu_stmm6;
 struct __darwin_mmst_reg __fpu_stmm7;
 struct __darwin_xmm_reg __fpu_xmm0;
 struct __darwin_xmm_reg __fpu_xmm1;
 struct __darwin_xmm_reg __fpu_xmm2;
 struct __darwin_xmm_reg __fpu_xmm3;
 struct __darwin_xmm_reg __fpu_xmm4;
 struct __darwin_xmm_reg __fpu_xmm5;
 struct __darwin_xmm_reg __fpu_xmm6;
 struct __darwin_xmm_reg __fpu_xmm7;
 char __fpu_rsrv4[14*16];
 int __fpu_reserved1;
 char __avx_reserved1[64];
 struct __darwin_xmm_reg __fpu_ymmh0;
 struct __darwin_xmm_reg __fpu_ymmh1;
 struct __darwin_xmm_reg __fpu_ymmh2;
 struct __darwin_xmm_reg __fpu_ymmh3;
 struct __darwin_xmm_reg __fpu_ymmh4;
 struct __darwin_xmm_reg __fpu_ymmh5;
 struct __darwin_xmm_reg __fpu_ymmh6;
 struct __darwin_xmm_reg __fpu_ymmh7;
};
# 402 "/usr/include/mach/i386/_structs.h" 3 4
struct __darwin_i386_exception_state
{
 __uint16_t __trapno;
 __uint16_t __cpu;
 __uint32_t __err;
 __uint32_t __faultvaddr;
};
# 422 "/usr/include/mach/i386/_structs.h" 3 4
struct __darwin_x86_debug_state32
{
 unsigned int __dr0;
 unsigned int __dr1;
 unsigned int __dr2;
 unsigned int __dr3;
 unsigned int __dr4;
 unsigned int __dr5;
 unsigned int __dr6;
 unsigned int __dr7;
};
# 454 "/usr/include/mach/i386/_structs.h" 3 4
struct __darwin_x86_thread_state64
{
 __uint64_t __rax;
 __uint64_t __rbx;
 __uint64_t __rcx;
 __uint64_t __rdx;
 __uint64_t __rdi;
 __uint64_t __rsi;
 __uint64_t __rbp;
 __uint64_t __rsp;
 __uint64_t __r8;
 __uint64_t __r9;
 __uint64_t __r10;
 __uint64_t __r11;
 __uint64_t __r12;
 __uint64_t __r13;
 __uint64_t __r14;
 __uint64_t __r15;
 __uint64_t __rip;
 __uint64_t __rflags;
 __uint64_t __cs;
 __uint64_t __fs;
 __uint64_t __gs;
};
# 509 "/usr/include/mach/i386/_structs.h" 3 4
struct __darwin_x86_float_state64
{
 int __fpu_reserved[2];
 struct __darwin_fp_control __fpu_fcw;
 struct __darwin_fp_status __fpu_fsw;
 __uint8_t __fpu_ftw;
 __uint8_t __fpu_rsrv1;
 __uint16_t __fpu_fop;


 __uint32_t __fpu_ip;
 __uint16_t __fpu_cs;

 __uint16_t __fpu_rsrv2;


 __uint32_t __fpu_dp;
 __uint16_t __fpu_ds;

 __uint16_t __fpu_rsrv3;
 __uint32_t __fpu_mxcsr;
 __uint32_t __fpu_mxcsrmask;
 struct __darwin_mmst_reg __fpu_stmm0;
 struct __darwin_mmst_reg __fpu_stmm1;
 struct __darwin_mmst_reg __fpu_stmm2;
 struct __darwin_mmst_reg __fpu_stmm3;
 struct __darwin_mmst_reg __fpu_stmm4;
 struct __darwin_mmst_reg __fpu_stmm5;
 struct __darwin_mmst_reg __fpu_stmm6;
 struct __darwin_mmst_reg __fpu_stmm7;
 struct __darwin_xmm_reg __fpu_xmm0;
 struct __darwin_xmm_reg __fpu_xmm1;
 struct __darwin_xmm_reg __fpu_xmm2;
 struct __darwin_xmm_reg __fpu_xmm3;
 struct __darwin_xmm_reg __fpu_xmm4;
 struct __darwin_xmm_reg __fpu_xmm5;
 struct __darwin_xmm_reg __fpu_xmm6;
 struct __darwin_xmm_reg __fpu_xmm7;
 struct __darwin_xmm_reg __fpu_xmm8;
 struct __darwin_xmm_reg __fpu_xmm9;
 struct __darwin_xmm_reg __fpu_xmm10;
 struct __darwin_xmm_reg __fpu_xmm11;
 struct __darwin_xmm_reg __fpu_xmm12;
 struct __darwin_xmm_reg __fpu_xmm13;
 struct __darwin_xmm_reg __fpu_xmm14;
 struct __darwin_xmm_reg __fpu_xmm15;
 char __fpu_rsrv4[6*16];
 int __fpu_reserved1;
};


struct __darwin_x86_avx_state64
{
 int __fpu_reserved[2];
 struct __darwin_fp_control __fpu_fcw;
 struct __darwin_fp_status __fpu_fsw;
 __uint8_t __fpu_ftw;
 __uint8_t __fpu_rsrv1;
 __uint16_t __fpu_fop;


 __uint32_t __fpu_ip;
 __uint16_t __fpu_cs;

 __uint16_t __fpu_rsrv2;


 __uint32_t __fpu_dp;
 __uint16_t __fpu_ds;

 __uint16_t __fpu_rsrv3;
 __uint32_t __fpu_mxcsr;
 __uint32_t __fpu_mxcsrmask;
 struct __darwin_mmst_reg __fpu_stmm0;
 struct __darwin_mmst_reg __fpu_stmm1;
 struct __darwin_mmst_reg __fpu_stmm2;
 struct __darwin_mmst_reg __fpu_stmm3;
 struct __darwin_mmst_reg __fpu_stmm4;
 struct __darwin_mmst_reg __fpu_stmm5;
 struct __darwin_mmst_reg __fpu_stmm6;
 struct __darwin_mmst_reg __fpu_stmm7;
 struct __darwin_xmm_reg __fpu_xmm0;
 struct __darwin_xmm_reg __fpu_xmm1;
 struct __darwin_xmm_reg __fpu_xmm2;
 struct __darwin_xmm_reg __fpu_xmm3;
 struct __darwin_xmm_reg __fpu_xmm4;
 struct __darwin_xmm_reg __fpu_xmm5;
 struct __darwin_xmm_reg __fpu_xmm6;
 struct __darwin_xmm_reg __fpu_xmm7;
 struct __darwin_xmm_reg __fpu_xmm8;
 struct __darwin_xmm_reg __fpu_xmm9;
 struct __darwin_xmm_reg __fpu_xmm10;
 struct __darwin_xmm_reg __fpu_xmm11;
 struct __darwin_xmm_reg __fpu_xmm12;
 struct __darwin_xmm_reg __fpu_xmm13;
 struct __darwin_xmm_reg __fpu_xmm14;
 struct __darwin_xmm_reg __fpu_xmm15;
 char __fpu_rsrv4[6*16];
 int __fpu_reserved1;
 char __avx_reserved1[64];
 struct __darwin_xmm_reg __fpu_ymmh0;
 struct __darwin_xmm_reg __fpu_ymmh1;
 struct __darwin_xmm_reg __fpu_ymmh2;
 struct __darwin_xmm_reg __fpu_ymmh3;
 struct __darwin_xmm_reg __fpu_ymmh4;
 struct __darwin_xmm_reg __fpu_ymmh5;
 struct __darwin_xmm_reg __fpu_ymmh6;
 struct __darwin_xmm_reg __fpu_ymmh7;
 struct __darwin_xmm_reg __fpu_ymmh8;
 struct __darwin_xmm_reg __fpu_ymmh9;
 struct __darwin_xmm_reg __fpu_ymmh10;
 struct __darwin_xmm_reg __fpu_ymmh11;
 struct __darwin_xmm_reg __fpu_ymmh12;
 struct __darwin_xmm_reg __fpu_ymmh13;
 struct __darwin_xmm_reg __fpu_ymmh14;
 struct __darwin_xmm_reg __fpu_ymmh15;
};
# 751 "/usr/include/mach/i386/_structs.h" 3 4
struct __darwin_x86_exception_state64
{
    __uint16_t __trapno;
    __uint16_t __cpu;
    __uint32_t __err;
    __uint64_t __faultvaddr;
};
# 771 "/usr/include/mach/i386/_structs.h" 3 4
struct __darwin_x86_debug_state64
{
 __uint64_t __dr0;
 __uint64_t __dr1;
 __uint64_t __dr2;
 __uint64_t __dr3;
 __uint64_t __dr4;
 __uint64_t __dr5;
 __uint64_t __dr6;
 __uint64_t __dr7;
};
# 39 "/usr/include/i386/_structs.h" 2 3 4
# 48 "/usr/include/i386/_structs.h" 3 4
struct __darwin_mcontext32
{
 struct __darwin_i386_exception_state __es;
 struct __darwin_i386_thread_state __ss;
 struct __darwin_i386_float_state __fs;
};


struct __darwin_mcontext_avx32
{
 struct __darwin_i386_exception_state __es;
 struct __darwin_i386_thread_state __ss;
 struct __darwin_i386_avx_state __fs;
};
# 86 "/usr/include/i386/_structs.h" 3 4
struct __darwin_mcontext64
{
 struct __darwin_x86_exception_state64 __es;
 struct __darwin_x86_thread_state64 __ss;
 struct __darwin_x86_float_state64 __fs;
};


struct __darwin_mcontext_avx64
{
 struct __darwin_x86_exception_state64 __es;
 struct __darwin_x86_thread_state64 __ss;
 struct __darwin_x86_avx_state64 __fs;
};
# 127 "/usr/include/i386/_structs.h" 3 4
typedef struct __darwin_mcontext64 *mcontext_t;
# 30 "/usr/include/machine/_structs.h" 2 3 4
# 58 "/usr/include/sys/_structs.h" 2 3 4
# 75 "/usr/include/sys/_structs.h" 3 4
struct __darwin_sigaltstack
{
 void *ss_sp;
 __darwin_size_t ss_size;
 int ss_flags;
};
# 128 "/usr/include/sys/_structs.h" 3 4
struct __darwin_ucontext
{
 int uc_onstack;
 __darwin_sigset_t uc_sigmask;
 struct __darwin_sigaltstack uc_stack;
 struct __darwin_ucontext *uc_link;
 __darwin_size_t uc_mcsize;
 struct __darwin_mcontext64 *uc_mcontext;



};
# 218 "/usr/include/sys/_structs.h" 3 4
typedef struct __darwin_sigaltstack stack_t;
# 227 "/usr/include/sys/_structs.h" 3 4
typedef struct __darwin_ucontext ucontext_t;
# 149 "/usr/include/sys/signal.h" 2 3 4
# 157 "/usr/include/sys/signal.h" 3 4
typedef __darwin_pthread_attr_t pthread_attr_t;




typedef __darwin_sigset_t sigset_t;
# 172 "/usr/include/sys/signal.h" 3 4
typedef __darwin_uid_t uid_t;


union sigval {

 int sival_int;
 void *sival_ptr;
};





struct sigevent {
 int sigev_notify;
 int sigev_signo;
 union sigval sigev_value;
 void (*sigev_notify_function)(union sigval);
 pthread_attr_t *sigev_notify_attributes;
};


typedef struct __siginfo {
 int si_signo;
 int si_errno;
 int si_code;
 pid_t si_pid;
 uid_t si_uid;
 int si_status;
 void *si_addr;
 union sigval si_value;
 long si_band;
 unsigned long __pad[7];
} siginfo_t;
# 286 "/usr/include/sys/signal.h" 3 4
union __sigaction_u {
 void (*__sa_handler)(int);
 void (*__sa_sigaction)(int, struct __siginfo *,
         void *);
};


struct __sigaction {
 union __sigaction_u __sigaction_u;
 void (*sa_tramp)(void *, int, int, siginfo_t *, void *);
 sigset_t sa_mask;
 int sa_flags;
};




struct sigaction {
 union __sigaction_u __sigaction_u;
 sigset_t sa_mask;
 int sa_flags;
};
# 348 "/usr/include/sys/signal.h" 3 4
typedef void (*sig_t)(int);
# 365 "/usr/include/sys/signal.h" 3 4
struct sigvec {
 void (*sv_handler)(int);
 int sv_mask;
 int sv_flags;
};
# 384 "/usr/include/sys/signal.h" 3 4
struct sigstack {
 char *ss_sp;
 int ss_onstack;
};
# 406 "/usr/include/sys/signal.h" 3 4

void (*signal(int, void (*)(int)))(int);

# 117 "/usr/include/sys/wait.h" 2 3 4
# 1 "/usr/include/sys/resource.h" 1 3 4
# 77 "/usr/include/sys/resource.h" 3 4
# 1 "/usr/include/sys/_structs.h" 1 3 4
# 100 "/usr/include/sys/_structs.h" 3 4
struct timeval
{
 __darwin_time_t tv_sec;
 __darwin_suseconds_t tv_usec;
};
# 78 "/usr/include/sys/resource.h" 2 3 4
# 89 "/usr/include/sys/resource.h" 3 4
typedef __uint64_t rlim_t;
# 151 "/usr/include/sys/resource.h" 3 4
struct rusage {
 struct timeval ru_utime;
 struct timeval ru_stime;
# 162 "/usr/include/sys/resource.h" 3 4
 long ru_maxrss;

 long ru_ixrss;
 long ru_idrss;
 long ru_isrss;
 long ru_minflt;
 long ru_majflt;
 long ru_nswap;
 long ru_inblock;
 long ru_oublock;
 long ru_msgsnd;
 long ru_msgrcv;
 long ru_nsignals;
 long ru_nvcsw;
 long ru_nivcsw;


};
# 222 "/usr/include/sys/resource.h" 3 4
struct rlimit {
 rlim_t rlim_cur;
 rlim_t rlim_max;
};
# 244 "/usr/include/sys/resource.h" 3 4

int getpriority(int, id_t);

int getiopolicy_np(int, int) __attribute__((visibility("default")));

int getrlimit(int, struct rlimit *) __asm("_" "getrlimit" );
int getrusage(int, struct rusage *);
int setpriority(int, id_t, int);

int setiopolicy_np(int, int, int) __attribute__((visibility("default")));

int setrlimit(int, const struct rlimit *) __asm("_" "setrlimit" );

# 118 "/usr/include/sys/wait.h" 2 3 4
# 193 "/usr/include/sys/wait.h" 3 4
# 1 "/usr/include/machine/endian.h" 1 3 4
# 35 "/usr/include/machine/endian.h" 3 4
# 1 "/usr/include/i386/endian.h" 1 3 4
# 99 "/usr/include/i386/endian.h" 3 4
# 1 "/usr/include/sys/_endian.h" 1 3 4
# 124 "/usr/include/sys/_endian.h" 3 4
# 1 "/usr/include/libkern/_OSByteOrder.h" 1 3 4
# 66 "/usr/include/libkern/_OSByteOrder.h" 3 4
# 1 "/usr/include/libkern/i386/_OSByteOrder.h" 1 3 4
# 44 "/usr/include/libkern/i386/_OSByteOrder.h" 3 4
static __inline__
__uint16_t
_OSSwapInt16(
    __uint16_t _data
)
{
    return ((_data << 8) | (_data >> 8));
}

static __inline__
__uint32_t
_OSSwapInt32(
    __uint32_t _data
)
{

    return __builtin_bswap32(_data);




}


static __inline__
__uint64_t
_OSSwapInt64(
    __uint64_t _data
)
{
    return __builtin_bswap64(_data);
}
# 67 "/usr/include/libkern/_OSByteOrder.h" 2 3 4
# 125 "/usr/include/sys/_endian.h" 2 3 4
# 100 "/usr/include/i386/endian.h" 2 3 4
# 36 "/usr/include/machine/endian.h" 2 3 4
# 194 "/usr/include/sys/wait.h" 2 3 4







union wait {
 int w_status;



 struct {

  unsigned int w_Termsig:7,
    w_Coredump:1,
    w_Retcode:8,
    w_Filler:16;







 } w_T;





 struct {

  unsigned int w_Stopval:8,
    w_Stopsig:8,
    w_Filler:16;






 } w_S;
};
# 254 "/usr/include/sys/wait.h" 3 4

pid_t wait(int *) __asm("_" "wait" );
pid_t waitpid(pid_t, int *, int) __asm("_" "waitpid" );

int waitid(idtype_t, id_t, siginfo_t *, int) __asm("_" "waitid" );


pid_t wait3(int *, int, struct rusage *);
pid_t wait4(pid_t, int *, int, struct rusage *);


# 66 "/usr/include/stdlib.h" 2 3 4

# 1 "/usr/include/alloca.h" 1 3 4
# 35 "/usr/include/alloca.h" 3 4

void *alloca(size_t);

# 68 "/usr/include/stdlib.h" 2 3 4
# 81 "/usr/include/stdlib.h" 3 4
typedef __darwin_ct_rune_t ct_rune_t;




typedef __darwin_rune_t rune_t;






typedef __darwin_wchar_t wchar_t;



typedef struct {
 int quot;
 int rem;
} div_t;

typedef struct {
 long quot;
 long rem;
} ldiv_t;


typedef struct {
 long long quot;
 long long rem;
} lldiv_t;
# 134 "/usr/include/stdlib.h" 3 4
extern int __mb_cur_max;
# 144 "/usr/include/stdlib.h" 3 4

void abort(void) __attribute__((__noreturn__));
int abs(int) __attribute__((__const__));
int atexit(void (*)(void));
double atof(const char *);
int atoi(const char *);
long atol(const char *);

long long
  atoll(const char *);

void *bsearch(const void *, const void *, size_t,
     size_t, int (*)(const void *, const void *));
void *calloc(size_t, size_t);
div_t div(int, int) __attribute__((__const__));
void exit(int) __attribute__((__noreturn__));
void free(void *);
char *getenv(const char *);
long labs(long) __attribute__((__const__));
ldiv_t ldiv(long, long) __attribute__((__const__));

long long
  llabs(long long);
lldiv_t lldiv(long long, long long);

void *malloc(size_t);
int mblen(const char *, size_t);
size_t mbstowcs(wchar_t * , const char * , size_t);
int mbtowc(wchar_t * , const char * , size_t);
int posix_memalign(void **, size_t, size_t) __attribute__((visibility("default")));
void qsort(void *, size_t, size_t,
     int (*)(const void *, const void *));
int rand(void);
void *realloc(void *, size_t);
void srand(unsigned);
double strtod(const char *, char **) __asm("_" "strtod" );
float strtof(const char *, char **) __asm("_" "strtof" );
long strtol(const char *, char **, int);
long double
  strtold(const char *, char **) ;

long long
  strtoll(const char *, char **, int);

unsigned long
  strtoul(const char *, char **, int);

unsigned long long
  strtoull(const char *, char **, int);

int system(const char *) __asm("_" "system" );
size_t wcstombs(char * , const wchar_t * , size_t);
int wctomb(char *, wchar_t);


void _Exit(int) __attribute__((__noreturn__));
long a64l(const char *);
double drand48(void);
char *ecvt(double, int, int *, int *);
double erand48(unsigned short[3]);
char *fcvt(double, int, int *, int *);
char *gcvt(double, int, char *);
int getsubopt(char **, char * const *, char **);
int grantpt(int);

char *initstate(unsigned, char *, size_t);



long jrand48(unsigned short[3]);
char *l64a(long);
void lcong48(unsigned short[7]);
long lrand48(void);
char *mktemp(char *);
int mkstemp(char *);
long mrand48(void);
long nrand48(unsigned short[3]);
int posix_openpt(int);
char *ptsname(int);
int putenv(char *) __asm("_" "putenv" );
long random(void);
int rand_r(unsigned *);

char *realpath(const char * , char * ) __asm("_" "realpath" "$DARWIN_EXTSN");



unsigned short
 *seed48(unsigned short[3]);
int setenv(const char *, const char *, int) __asm("_" "setenv" );

void setkey(const char *) __asm("_" "setkey" );



char *setstate(const char *);
void srand48(long);

void srandom(unsigned);



int unlockpt(int);

int unsetenv(const char *) __asm("_" "unsetenv" );






# 1 "/usr/include/machine/types.h" 1 3 4
# 35 "/usr/include/machine/types.h" 3 4
# 1 "/usr/include/i386/types.h" 1 3 4
# 70 "/usr/include/i386/types.h" 3 4
# 1 "/usr/include/i386/_types.h" 1 3 4
# 71 "/usr/include/i386/types.h" 2 3 4







typedef signed char int8_t;

typedef unsigned char u_int8_t;


typedef short int16_t;

typedef unsigned short u_int16_t;


typedef int int32_t;

typedef unsigned int u_int32_t;


typedef long long int64_t;

typedef unsigned long long u_int64_t;


typedef int64_t register_t;






typedef __darwin_intptr_t intptr_t;



typedef unsigned long uintptr_t;




typedef u_int64_t user_addr_t;
typedef u_int64_t user_size_t;
typedef int64_t user_ssize_t;
typedef int64_t user_long_t;
typedef u_int64_t user_ulong_t;
typedef int64_t user_time_t;
typedef int64_t user_off_t;







typedef u_int64_t syscall_arg_t;
# 36 "/usr/include/machine/types.h" 2 3 4
# 256 "/usr/include/stdlib.h" 2 3 4


typedef __darwin_dev_t dev_t;




typedef __darwin_mode_t mode_t;



u_int32_t
  arc4random(void);
void arc4random_addrandom(unsigned char * , int );
void arc4random_buf(void * , size_t ) __attribute__((visibility("default")));
void arc4random_stir(void);
u_int32_t
  arc4random_uniform(u_int32_t ) __attribute__((visibility("default")));

int atexit_b(void (^)(void)) __attribute__((visibility("default")));
void *bsearch_b(const void *, const void *, size_t,
     size_t, int (^)(const void *, const void *)) __attribute__((visibility("default")));



char *cgetcap(char *, const char *, int);
int cgetclose(void);
int cgetent(char **, char **, const char *);
int cgetfirst(char **, char **);
int cgetmatch(const char *, const char *);
int cgetnext(char **, char **);
int cgetnum(char *, const char *, long *);
int cgetset(const char *);
int cgetstr(char *, const char *, char **);
int cgetustr(char *, const char *, char **);

int daemon(int, int) __asm("_" "daemon" "$1050") __attribute__((deprecated,visibility("default")));
char *devname(dev_t, mode_t);
char *devname_r(dev_t, mode_t, char *buf, int len);
char *getbsize(int *, long *);
int getloadavg(double [], int);
const char
 *getprogname(void);

int heapsort(void *, size_t, size_t,
     int (*)(const void *, const void *));

int heapsort_b(void *, size_t, size_t,
     int (^)(const void *, const void *)) __attribute__((visibility("default")));

int mergesort(void *, size_t, size_t,
     int (*)(const void *, const void *));

int mergesort_b(void *, size_t, size_t,
     int (^)(const void *, const void *)) __attribute__((visibility("default")));

void psort(void *, size_t, size_t,
     int (*)(const void *, const void *)) __attribute__((visibility("default")));

void psort_b(void *, size_t, size_t,
     int (^)(const void *, const void *)) __attribute__((visibility("default")));

void psort_r(void *, size_t, size_t, void *,
     int (*)(void *, const void *, const void *)) __attribute__((visibility("default")));

void qsort_b(void *, size_t, size_t,
     int (^)(const void *, const void *)) __attribute__((visibility("default")));

void qsort_r(void *, size_t, size_t, void *,
     int (*)(void *, const void *, const void *));
int radixsort(const unsigned char **, int, const unsigned char *,
     unsigned);
void setprogname(const char *);
int sradixsort(const unsigned char **, int, const unsigned char *,
     unsigned);
void sranddev(void);
void srandomdev(void);
void *reallocf(void *, size_t);

long long
  strtoq(const char *, char **, int);
unsigned long long
  strtouq(const char *, char **, int);

extern char *suboptarg;
void *valloc(size_t);







# 35 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2

# 1 "/usr/include/unistd.h" 1 3 4
# 72 "/usr/include/unistd.h" 3 4
# 1 "/usr/include/sys/unistd.h" 1 3 4
# 138 "/usr/include/sys/unistd.h" 3 4
struct accessx_descriptor {
 unsigned int ad_name_offset;
 int ad_flags;
 int ad_pad[2];
};
# 73 "/usr/include/unistd.h" 2 3 4




typedef __darwin_gid_t gid_t;
# 114 "/usr/include/unistd.h" 3 4
typedef __darwin_useconds_t useconds_t;
# 468 "/usr/include/unistd.h" 3 4

void _exit(int) __attribute__((__noreturn__));
int access(const char *, int);
unsigned int
  alarm(unsigned int);
int chdir(const char *);
int chown(const char *, uid_t, gid_t);

int close(int) __asm("_" "close" );

int dup(int);
int dup2(int, int);
int execl(const char *, const char *, ...);
int execle(const char *, const char *, ...);
int execlp(const char *, const char *, ...);
int execv(const char *, char * const *);
int execve(const char *, char * const *, char * const *);
int execvp(const char *, char * const *);
pid_t fork(void);
long fpathconf(int, int);
char *getcwd(char *, size_t);
gid_t getegid(void);
uid_t geteuid(void);
gid_t getgid(void);

int getgroups(int, gid_t []) __asm("_" "getgroups" "$DARWIN_EXTSN");



char *getlogin(void);
pid_t getpgrp(void);
pid_t getpid(void);
pid_t getppid(void);
uid_t getuid(void);
int isatty(int);
int link(const char *, const char *);
off_t lseek(int, off_t, int);
long pathconf(const char *, int);

int pause(void) __asm("_" "pause" );

int pipe(int [2]);

ssize_t read(int, void *, size_t) __asm("_" "read" );

int rmdir(const char *);
int setgid(gid_t);
int setpgid(pid_t, pid_t);
pid_t setsid(void);
int setuid(uid_t);

unsigned int
  sleep(unsigned int) __asm("_" "sleep" );

long sysconf(int);
pid_t tcgetpgrp(int);
int tcsetpgrp(int, pid_t);
char *ttyname(int);


int ttyname_r(int, char *, size_t) __asm("_" "ttyname_r" );




int unlink(const char *);

ssize_t write(int, const void *, size_t) __asm("_" "write" );

# 545 "/usr/include/unistd.h" 3 4

size_t confstr(int, char *, size_t) __asm("_" "confstr" );

int getopt(int, char * const [], const char *) __asm("_" "getopt" );

extern char *optarg;
extern int optind, opterr, optopt;

# 570 "/usr/include/unistd.h" 3 4





void *brk(const void *);
int chroot(const char *) ;


char *crypt(const char *, const char *);






void encrypt(char *, int) __asm("_" "encrypt" );



int fchdir(int);
long gethostid(void);
pid_t getpgid(pid_t);
pid_t getsid(pid_t);



int getdtablesize(void) ;
int getpagesize(void) __attribute__((__const__)) ;
char *getpass(const char *) ;




char *getwd(char *) ;


int lchown(const char *, uid_t, gid_t) __asm("_" "lchown" );

int lockf(int, int, off_t) __asm("_" "lockf" );

int nice(int) __asm("_" "nice" );

ssize_t pread(int, void *, size_t, off_t) __asm("_" "pread" );

ssize_t pwrite(int, const void *, size_t, off_t) __asm("_" "pwrite" );





void *sbrk(int);



pid_t setpgrp(void) __asm("_" "setpgrp" );




int setregid(gid_t, gid_t) __asm("_" "setregid" );

int setreuid(uid_t, uid_t) __asm("_" "setreuid" );

void swab(const void * , void * , ssize_t);
void sync(void);
int truncate(const char *, off_t);
useconds_t ualarm(useconds_t, useconds_t);
int usleep(useconds_t) __asm("_" "usleep" );
pid_t vfork(void);


int fsync(int) __asm("_" "fsync" );

int ftruncate(int, off_t);
int getlogin_r(char *, size_t);

# 657 "/usr/include/unistd.h" 3 4

int fchown(int, uid_t, gid_t);
int gethostname(char *, size_t);
ssize_t readlink(const char * , char * , size_t);
int setegid(gid_t);
int seteuid(uid_t);
int symlink(const char *, const char *);








# 1 "/usr/include/sys/select.h" 1 3 4
# 78 "/usr/include/sys/select.h" 3 4
# 1 "/usr/include/sys/_structs.h" 1 3 4
# 88 "/usr/include/sys/_structs.h" 3 4
struct timespec
{
 __darwin_time_t tv_sec;
 long tv_nsec;
};
# 183 "/usr/include/sys/_structs.h" 3 4

typedef struct fd_set {
 __int32_t fds_bits[((((1024) % ((sizeof(__int32_t) * 8))) == 0) ? ((1024) / ((sizeof(__int32_t) * 8))) : (((1024) / ((sizeof(__int32_t) * 8))) + 1))];
} fd_set;



static __inline int
__darwin_fd_isset(int _n, const struct fd_set *_p)
{
 return (_p->fds_bits[_n/(sizeof(__int32_t) * 8)] & (1<<(_n % (sizeof(__int32_t) * 8))));
}
# 79 "/usr/include/sys/select.h" 2 3 4
# 87 "/usr/include/sys/select.h" 3 4
typedef __darwin_time_t time_t;




typedef __darwin_suseconds_t suseconds_t;
# 134 "/usr/include/sys/select.h" 3 4



int pselect(int, fd_set * , fd_set * ,
  fd_set * , const struct timespec * ,
  const sigset_t * )

  __asm("_" "pselect" "$DARWIN_EXTSN" )







  ;


# 1 "/usr/include/sys/_select.h" 1 3 4
# 39 "/usr/include/sys/_select.h" 3 4
int select(int, fd_set * , fd_set * ,
  fd_set * , struct timeval * )

  __asm("_" "select" "$DARWIN_EXTSN" )







  ;
# 153 "/usr/include/sys/select.h" 2 3 4


# 673 "/usr/include/unistd.h" 2 3 4
# 686 "/usr/include/unistd.h" 3 4
typedef __darwin_uuid_t uuid_t;



void _Exit(int) __attribute__((__noreturn__));
int accessx_np(const struct accessx_descriptor *, size_t, int *, uid_t);
int acct(const char *);
int add_profil(char *, size_t, unsigned long, unsigned int);
void endusershell(void);
int execvP(const char *, const char *, char * const *);
char *fflagstostr(unsigned long);
int getdomainname(char *, int);
int getgrouplist(const char *, int, int *, int *);
int gethostuuid(uuid_t, const struct timespec *) __attribute__((visibility("default")));
mode_t getmode(const void *, mode_t);
int getpeereid(int, uid_t *, gid_t *);
int getsgroups_np(int *, uuid_t);
char *getusershell(void);
int getwgroups_np(int *, uuid_t);
int initgroups(const char *, int);
int iruserok(unsigned long, int, const char *, const char *);
int iruserok_sa(const void *, int, int, const char *, const char *);
int issetugid(void);
char *mkdtemp(char *);
int mknod(const char *, mode_t, dev_t);
int mkstemp(char *);
int mkstemps(char *, int);
char *mktemp(char *);
int nfssvc(int, void *);
int profil(char *, size_t, unsigned long, unsigned int);
int pthread_setugid_np(uid_t, gid_t);
int pthread_getugid_np( uid_t *, gid_t *);
int rcmd(char **, int, const char *, const char *, const char *, int *);
int rcmd_af(char **, int, const char *, const char *, const char *, int *,
  int);
int reboot(int);
int revoke(const char *);
int rresvport(int *);
int rresvport_af(int *, int);
int ruserok(const char *, int, const char *, const char *);
int setdomainname(const char *, int);
int setgroups(int, const gid_t *);
void sethostid(long);
int sethostname(const char *, int);

void setkey(const char *) __asm("_" "setkey" );



int setlogin(const char *);
void *setmode(const char *) __asm("_" "setmode" );
int setrgid(gid_t);
int setruid(uid_t);
int setsgroups_np(int, const uuid_t);
void setusershell(void);
int setwgroups_np(int, const uuid_t);
int strtofflags(char **, unsigned long *, unsigned long *);
int swapon(const char *);
int syscall(int, ...);
int ttyslot(void);
int undelete(const char *);
int unwhiteout(const char *);
void *valloc(size_t);

extern char *suboptarg;
int getsubopt(char **, char * const *, char **);



int fgetattrlist(int,void*,void*,size_t,unsigned int) __attribute__((visibility("default")));
int fsetattrlist(int,void*,void*,size_t,unsigned int) __attribute__((visibility("default")));
int getattrlist(const char*,void*,void*,size_t,unsigned int) __asm("_" "getattrlist" );
int setattrlist(const char*,void*,void*,size_t,unsigned int) __asm("_" "setattrlist" );
int exchangedata(const char*,const char*,unsigned int);
int getdirentriesattr(int,void*,void*,size_t,unsigned int*,unsigned int*,unsigned int*,unsigned int);
# 772 "/usr/include/unistd.h" 3 4
struct fssearchblock;
struct searchstate;

int searchfs(const char *, struct fssearchblock *, unsigned long *, unsigned int, unsigned int, struct searchstate *);
int fsctl(const char *,unsigned long,void*,unsigned int);
int ffsctl(int,unsigned long,void*,unsigned int) __attribute__((visibility("default")));

extern int optreset;


# 37 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 48 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h"
# 1 "/usr/include/assert.h" 1 3 4
# 75 "/usr/include/assert.h" 3 4

void __assert_rtn(const char *, const char *, int, const char *) __attribute__((__noreturn__));




# 49 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2

# 1 "/Users/parrt/tmp/Python-3.3.1/Include/pyport.h" 1
# 9 "/Users/parrt/tmp/Python-3.3.1/Include/pyport.h"
# 1 "/usr/include/inttypes.h" 1 3 4
# 247 "/usr/include/inttypes.h" 3 4
# 1 "/usr/include/stdint.h" 1 3 4
# 40 "/usr/include/stdint.h" 3 4
typedef unsigned char uint8_t;




typedef unsigned short uint16_t;




typedef unsigned int uint32_t;




typedef unsigned long long uint64_t;



typedef int8_t int_least8_t;
typedef int16_t int_least16_t;
typedef int32_t int_least32_t;
typedef int64_t int_least64_t;
typedef uint8_t uint_least8_t;
typedef uint16_t uint_least16_t;
typedef uint32_t uint_least32_t;
typedef uint64_t uint_least64_t;



typedef int8_t int_fast8_t;
typedef int16_t int_fast16_t;
typedef int32_t int_fast32_t;
typedef int64_t int_fast64_t;
typedef uint8_t uint_fast8_t;
typedef uint16_t uint_fast16_t;
typedef uint32_t uint_fast32_t;
typedef uint64_t uint_fast64_t;
# 97 "/usr/include/stdint.h" 3 4
typedef long int intmax_t;
# 106 "/usr/include/stdint.h" 3 4
typedef long unsigned int uintmax_t;
# 248 "/usr/include/inttypes.h" 2 3 4
# 257 "/usr/include/inttypes.h" 3 4



  extern intmax_t imaxabs(intmax_t j);


  typedef struct {
        intmax_t quot;
        intmax_t rem;
  } imaxdiv_t;

  extern imaxdiv_t imaxdiv(intmax_t numer, intmax_t denom);


  extern intmax_t strtoimax(const char * nptr, char ** endptr, int base);
  extern uintmax_t strtoumax(const char * nptr, char ** endptr, int base);
# 282 "/usr/include/inttypes.h" 3 4
  extern intmax_t wcstoimax(const wchar_t * nptr, wchar_t ** endptr, int base);
  extern uintmax_t wcstoumax(const wchar_t * nptr, wchar_t ** endptr, int base);







# 10 "/Users/parrt/tmp/Python-3.3.1/Include/pyport.h" 2
# 170 "/Users/parrt/tmp/Python-3.3.1/Include/pyport.h"
typedef uintptr_t Py_uintptr_t;
typedef intptr_t Py_intptr_t;
# 194 "/Users/parrt/tmp/Python-3.3.1/Include/pyport.h"
typedef ssize_t Py_ssize_t;







typedef Py_ssize_t Py_hash_t;

typedef size_t Py_uhash_t;
# 340 "/Users/parrt/tmp/Python-3.3.1/Include/pyport.h"
# 1 "/usr/include/math.h" 1 3 4
# 28 "/usr/include/math.h" 3 4
# 1 "/usr/include/architecture/i386/math.h" 1 3 4
# 49 "/usr/include/architecture/i386/math.h" 3 4
 typedef float float_t;
 typedef double double_t;
# 108 "/usr/include/architecture/i386/math.h" 3 4
extern int __math_errhandling ( void );
# 128 "/usr/include/architecture/i386/math.h" 3 4
extern int __fpclassifyf(float );
extern int __fpclassifyd(double );
extern int __fpclassify (long double);
# 163 "/usr/include/architecture/i386/math.h" 3 4
 static __inline__ int __inline_isfinitef (float ) __attribute__ ((always_inline));
 static __inline__ int __inline_isfinited (double ) __attribute__ ((always_inline));
 static __inline__ int __inline_isfinite (long double) __attribute__ ((always_inline));
 static __inline__ int __inline_isinff (float ) __attribute__ ((always_inline));
 static __inline__ int __inline_isinfd (double ) __attribute__ ((always_inline));
 static __inline__ int __inline_isinf (long double) __attribute__ ((always_inline));
 static __inline__ int __inline_isnanf (float ) __attribute__ ((always_inline));
 static __inline__ int __inline_isnand (double ) __attribute__ ((always_inline));
 static __inline__ int __inline_isnan (long double) __attribute__ ((always_inline));
 static __inline__ int __inline_isnormalf (float ) __attribute__ ((always_inline));
 static __inline__ int __inline_isnormald (double ) __attribute__ ((always_inline));
 static __inline__ int __inline_isnormal (long double) __attribute__ ((always_inline));
 static __inline__ int __inline_signbitf (float ) __attribute__ ((always_inline));
 static __inline__ int __inline_signbitd (double ) __attribute__ ((always_inline));
 static __inline__ int __inline_signbit (long double) __attribute__ ((always_inline));

 static __inline__ int __inline_isinff( float __x ) { return __builtin_fabsf(__x) == __builtin_inff(); }
 static __inline__ int __inline_isinfd( double __x ) { return __builtin_fabs(__x) == __builtin_inf(); }
 static __inline__ int __inline_isinf( long double __x ) { return __builtin_fabsl(__x) == __builtin_infl(); }
 static __inline__ int __inline_isfinitef( float __x ) { return __x == __x && __builtin_fabsf(__x) != __builtin_inff(); }
 static __inline__ int __inline_isfinited( double __x ) { return __x == __x && __builtin_fabs(__x) != __builtin_inf(); }
 static __inline__ int __inline_isfinite( long double __x ) { return __x == __x && __builtin_fabsl(__x) != __builtin_infl(); }
 static __inline__ int __inline_isnanf( float __x ) { return __x != __x; }
 static __inline__ int __inline_isnand( double __x ) { return __x != __x; }
 static __inline__ int __inline_isnan( long double __x ) { return __x != __x; }
 static __inline__ int __inline_signbitf( float __x ) { union{ float __f; unsigned int __u; }__u; __u.__f = __x; return (int)(__u.__u >> 31); }
 static __inline__ int __inline_signbitd( double __x ) { union{ double __f; unsigned int __u[2]; }__u; __u.__f = __x; return (int)(__u.__u[1] >> 31); }
 static __inline__ int __inline_signbit( long double __x ){ union{ long double __ld; struct{ unsigned int __m[2]; short __sexp; }__p; }__u; __u.__ld = __x; return (int) (((unsigned short) __u.__p.__sexp) >> 15); }
 static __inline__ int __inline_isnormalf( float __x ) { float fabsf = __builtin_fabsf(__x); if( __x != __x ) return 0; return fabsf < __builtin_inff() && fabsf >= 1.17549435e-38F; }
 static __inline__ int __inline_isnormald( double __x ) { double fabsf = __builtin_fabs(__x); if( __x != __x ) return 0; return fabsf < __builtin_inf() && fabsf >= 2.2250738585072014e-308; }
 static __inline__ int __inline_isnormal( long double __x ) { long double fabsf = __builtin_fabsl(__x); if( __x != __x ) return 0; return fabsf < __builtin_infl() && fabsf >= 3.36210314311209350626e-4932L; }
# 253 "/usr/include/architecture/i386/math.h" 3 4
extern double acos( double );
extern float acosf( float );

extern double asin( double );
extern float asinf( float );

extern double atan( double );
extern float atanf( float );

extern double atan2( double, double );
extern float atan2f( float, float );

extern double cos( double );
extern float cosf( float );

extern double sin( double );
extern float sinf( float );

extern double tan( double );
extern float tanf( float );

extern double acosh( double );
extern float acoshf( float );

extern double asinh( double );
extern float asinhf( float );

extern double atanh( double );
extern float atanhf( float );

extern double cosh( double );
extern float coshf( float );

extern double sinh( double );
extern float sinhf( float );

extern double tanh( double );
extern float tanhf( float );

extern double exp ( double );
extern float expf ( float );

extern double exp2 ( double );
extern float exp2f ( float );

extern double expm1 ( double );
extern float expm1f ( float );

extern double log ( double );
extern float logf ( float );

extern double log10 ( double );
extern float log10f ( float );

extern double log2 ( double );
extern float log2f ( float );

extern double log1p ( double );
extern float log1pf ( float );

extern double logb ( double );
extern float logbf ( float );

extern double modf ( double, double * );
extern float modff ( float, float * );

extern double ldexp ( double, int );
extern float ldexpf ( float, int );

extern double frexp ( double, int * );
extern float frexpf ( float, int * );

extern int ilogb ( double );
extern int ilogbf ( float );

extern double scalbn ( double, int );
extern float scalbnf ( float, int );

extern double scalbln ( double, long int );
extern float scalblnf ( float, long int );

extern double fabs( double );
extern float fabsf( float );

extern double cbrt( double );
extern float cbrtf( float );

extern double hypot ( double, double );
extern float hypotf ( float, float );

extern double pow ( double, double );
extern float powf ( float, float );

extern double sqrt( double );
extern float sqrtf( float );

extern double erf( double );
extern float erff( float );

extern double erfc( double );
extern float erfcf( float );






extern double lgamma( double );
extern float lgammaf( float );

extern double tgamma( double );
extern float tgammaf( float );

extern double ceil ( double );
extern float ceilf ( float );

extern double floor ( double );
extern float floorf ( float );

extern double nearbyint ( double );
extern float nearbyintf ( float );

extern double rint ( double );
extern float rintf ( float );

extern long int lrint ( double );
extern long int lrintf ( float );

extern double round ( double );
extern float roundf ( float );

extern long int lround ( double );
extern long int lroundf ( float );



    extern long long int llrint ( double );
    extern long long int llrintf ( float );
    extern long long int llround ( double );
    extern long long int llroundf ( float );


extern double trunc ( double );
extern float truncf ( float );

extern double fmod ( double, double );
extern float fmodf ( float, float );

extern double remainder ( double, double );
extern float remainderf ( float, float );

extern double remquo ( double, double, int * );
extern float remquof ( float, float, int * );

extern double copysign ( double, double );
extern float copysignf ( float, float );

extern double nan( const char * );
extern float nanf( const char * );

extern double nextafter ( double, double );
extern float nextafterf ( float, float );

extern double fdim ( double, double );
extern float fdimf ( float, float );

extern double fmax ( double, double );
extern float fmaxf ( float, float );

extern double fmin ( double, double );
extern float fminf ( float, float );

extern double fma ( double, double, double );
extern float fmaf ( float, float, float );

extern long double acosl(long double);
extern long double asinl(long double);
extern long double atanl(long double);
extern long double atan2l(long double, long double);
extern long double cosl(long double);
extern long double sinl(long double);
extern long double tanl(long double);
extern long double acoshl(long double);
extern long double asinhl(long double);
extern long double atanhl(long double);
extern long double coshl(long double);
extern long double sinhl(long double);
extern long double tanhl(long double);
extern long double expl(long double);
extern long double exp2l(long double);
extern long double expm1l(long double);
extern long double logl(long double);
extern long double log10l(long double);
extern long double log2l(long double);
extern long double log1pl(long double);
extern long double logbl(long double);
extern long double modfl(long double, long double *);
extern long double ldexpl(long double, int);
extern long double frexpl(long double, int *);
extern int ilogbl(long double);
extern long double scalbnl(long double, int);
extern long double scalblnl(long double, long int);
extern long double fabsl(long double);
extern long double cbrtl(long double);
extern long double hypotl(long double, long double);
extern long double powl(long double, long double);
extern long double sqrtl(long double);
extern long double erfl(long double);
extern long double erfcl(long double);






extern long double lgammal(long double);

extern long double tgammal(long double);
extern long double ceill(long double);
extern long double floorl(long double);
extern long double nearbyintl(long double);
extern long double rintl(long double);
extern long int lrintl(long double);
extern long double roundl(long double);
extern long int lroundl(long double);



    extern long long int llrintl(long double);
    extern long long int llroundl(long double);


extern long double truncl(long double);
extern long double fmodl(long double, long double);
extern long double remainderl(long double, long double);
extern long double remquol(long double, long double, int *);
extern long double copysignl(long double, long double);
extern long double nanl(const char *);
extern long double nextafterl(long double, long double);
extern double nexttoward(double, long double);
extern float nexttowardf(float, long double);
extern long double nexttowardl(long double, long double);
extern long double fdiml(long double, long double);
extern long double fmaxl(long double, long double);
extern long double fminl(long double, long double);
extern long double fmal(long double, long double, long double);
# 507 "/usr/include/architecture/i386/math.h" 3 4
extern double __inf( void );
extern float __inff( void );
extern long double __infl( void );
extern float __nan( void );


extern double j0 ( double );

extern double j1 ( double );

extern double jn ( int, double );

extern double y0 ( double );

extern double y1 ( double );

extern double yn ( int, double );

extern double scalb ( double, double );
# 543 "/usr/include/architecture/i386/math.h" 3 4
extern int signgam;
# 558 "/usr/include/architecture/i386/math.h" 3 4
extern long int rinttol ( double );


extern long int roundtol ( double );
# 570 "/usr/include/architecture/i386/math.h" 3 4
struct exception {
 int type;
 char *name;
 double arg1;
 double arg2;
 double retval;
};
# 601 "/usr/include/architecture/i386/math.h" 3 4
extern int finite ( double );


extern double gamma ( double );




extern int matherr ( struct exception * );





extern double significand ( double );






extern double drem ( double, double );







# 1 "/usr/include/AvailabilityMacros.h" 1 3 4
# 631 "/usr/include/architecture/i386/math.h" 2 3 4

 extern float lgammaf_r ( float, int * ) ;
 extern double lgamma_r ( double, int * ) ;
 extern long double lgammal_r ( long double, int * ) ;
# 29 "/usr/include/math.h" 2 3 4
# 341 "/Users/parrt/tmp/Python-3.3.1/Include/pyport.h" 2






# 1 "/usr/include/sys/time.h" 1 3 4
# 78 "/usr/include/sys/time.h" 3 4
# 1 "/usr/include/sys/_structs.h" 1 3 4
# 79 "/usr/include/sys/time.h" 2 3 4
# 94 "/usr/include/sys/time.h" 3 4
struct itimerval {
 struct timeval it_interval;
 struct timeval it_value;
};
# 144 "/usr/include/sys/time.h" 3 4
struct timezone {
 int tz_minuteswest;
 int tz_dsttime;
};
# 187 "/usr/include/sys/time.h" 3 4
struct clockinfo {
 int hz;
 int tick;
 int tickadj;
 int stathz;
 int profhz;
};




# 1 "/usr/include/time.h" 1 3 4
# 69 "/usr/include/time.h" 3 4
# 1 "/usr/include/_structs.h" 1 3 4
# 24 "/usr/include/_structs.h" 3 4
# 1 "/usr/include/sys/_structs.h" 1 3 4
# 25 "/usr/include/_structs.h" 2 3 4
# 70 "/usr/include/time.h" 2 3 4







typedef __darwin_clock_t clock_t;
# 90 "/usr/include/time.h" 3 4
struct tm {
 int tm_sec;
 int tm_min;
 int tm_hour;
 int tm_mday;
 int tm_mon;
 int tm_year;
 int tm_wday;
 int tm_yday;
 int tm_isdst;
 long tm_gmtoff;
 char *tm_zone;
};
# 113 "/usr/include/time.h" 3 4
extern char *tzname[];


extern int getdate_err;

extern long timezone __asm("_" "timezone" );

extern int daylight;


char *asctime(const struct tm *);
clock_t clock(void) __asm("_" "clock" );
char *ctime(const time_t *);
double difftime(time_t, time_t);
struct tm *getdate(const char *);
struct tm *gmtime(const time_t *);
struct tm *localtime(const time_t *);
time_t mktime(struct tm *) __asm("_" "mktime" );
size_t strftime(char * , size_t, const char * , const struct tm * ) __asm("_" "strftime" );
char *strptime(const char * , const char * , struct tm * ) __asm("_" "strptime" );
time_t time(time_t *);


void tzset(void);



char *asctime_r(const struct tm * , char * );
char *ctime_r(const time_t *, char *);
struct tm *gmtime_r(const time_t * , struct tm * );
struct tm *localtime_r(const time_t * , struct tm * );


time_t posix2time(time_t);



void tzsetwall(void);
time_t time2posix(time_t);
time_t timelocal(struct tm * const);
time_t timegm(struct tm * const);



int nanosleep(const struct timespec *, struct timespec *) __asm("_" "nanosleep" );


# 199 "/usr/include/sys/time.h" 2 3 4





int adjtime(const struct timeval *, struct timeval *);
int futimes(int, const struct timeval *);
int lutimes(const char *, const struct timeval *) __attribute__((visibility("default")));
int settimeofday(const struct timeval *, const struct timezone *);


int getitimer(int, struct itimerval *);
int gettimeofday(struct timeval * , void * );



int setitimer(int, const struct itimerval * ,
  struct itimerval * );
int utimes(const char *, const struct timeval *);


# 348 "/Users/parrt/tmp/Python-3.3.1/Include/pyport.h" 2
# 398 "/Users/parrt/tmp/Python-3.3.1/Include/pyport.h"
# 1 "/usr/include/sys/stat.h" 1 3 4
# 79 "/usr/include/sys/stat.h" 3 4
# 1 "/usr/include/sys/_structs.h" 1 3 4
# 80 "/usr/include/sys/stat.h" 2 3 4







typedef __darwin_blkcnt_t blkcnt_t;




typedef __darwin_blksize_t blksize_t;
# 102 "/usr/include/sys/stat.h" 3 4
typedef __darwin_ino_t ino_t;





typedef __darwin_ino64_t ino64_t;
# 119 "/usr/include/sys/stat.h" 3 4
typedef __uint16_t nlink_t;
# 153 "/usr/include/sys/stat.h" 3 4
struct ostat {
 __uint16_t st_dev;
 ino_t st_ino;
 mode_t st_mode;
 nlink_t st_nlink;
 __uint16_t st_uid;
 __uint16_t st_gid;
 __uint16_t st_rdev;
 __int32_t st_size;
 struct timespec st_atimespec;
 struct timespec st_mtimespec;
 struct timespec st_ctimespec;
 __int32_t st_blksize;
 __int32_t st_blocks;
 __uint32_t st_flags;
 __uint32_t st_gen;
};
# 225 "/usr/include/sys/stat.h" 3 4
struct stat { dev_t st_dev; mode_t st_mode; nlink_t st_nlink; __darwin_ino64_t st_ino; uid_t st_uid; gid_t st_gid; dev_t st_rdev; struct timespec st_atimespec; struct timespec st_mtimespec; struct timespec st_ctimespec; struct timespec st_birthtimespec; off_t st_size; blkcnt_t st_blocks; blksize_t st_blksize; __uint32_t st_flags; __uint32_t st_gen; __int32_t st_lspare; __int64_t st_qspare[2]; };
# 264 "/usr/include/sys/stat.h" 3 4
struct stat64 { dev_t st_dev; mode_t st_mode; nlink_t st_nlink; __darwin_ino64_t st_ino; uid_t st_uid; gid_t st_gid; dev_t st_rdev; struct timespec st_atimespec; struct timespec st_mtimespec; struct timespec st_ctimespec; struct timespec st_birthtimespec; off_t st_size; blkcnt_t st_blocks; blksize_t st_blksize; __uint32_t st_flags; __uint32_t st_gen; __int32_t st_lspare; __int64_t st_qspare[2]; };
# 428 "/usr/include/sys/stat.h" 3 4


int chmod(const char *, mode_t) __asm("_" "chmod" );
int fchmod(int, mode_t) __asm("_" "fchmod" );
int fstat(int, struct stat *) __asm("_" "fstat" "$INODE64");
int lstat(const char *, struct stat *) __asm("_" "lstat" "$INODE64");
int mkdir(const char *, mode_t);
int mkfifo(const char *, mode_t);
int stat(const char *, struct stat *) __asm("_" "stat" "$INODE64");
int mknod(const char *, mode_t, dev_t);
mode_t umask(mode_t);



struct _filesec;
typedef struct _filesec *filesec_t;


int chflags(const char *, __uint32_t);
int chmodx_np(const char *, filesec_t);
int fchflags(int, __uint32_t);
int fchmodx_np(int, filesec_t);
int fstatx_np(int, struct stat *, filesec_t) __asm("_" "fstatx_np" "$INODE64");
int lchflags(const char *, __uint32_t) __attribute__((visibility("default")));
int lchmod(const char *, mode_t) __attribute__((visibility("default")));
int lstatx_np(const char *, struct stat *, filesec_t) __asm("_" "lstatx_np" "$INODE64");
int mkdirx_np(const char *, filesec_t);
int mkfifox_np(const char *, filesec_t);
int statx_np(const char *, struct stat *, filesec_t) __asm("_" "statx_np" "$INODE64");
int umaskx_np(filesec_t) __attribute__((deprecated,visibility("default")));



int fstatx64_np(int, struct stat64 *, filesec_t) __attribute__((deprecated,visibility("default")));
int lstatx64_np(const char *, struct stat64 *, filesec_t) __attribute__((deprecated,visibility("default")));
int statx64_np(const char *, struct stat64 *, filesec_t) __attribute__((deprecated,visibility("default")));
int fstat64(int, struct stat64 *) __attribute__((deprecated,visibility("default")));
int lstat64(const char *, struct stat64 *) __attribute__((deprecated,visibility("default")));
int stat64(const char *, struct stat64 *) __attribute__((deprecated,visibility("default")));




# 399 "/Users/parrt/tmp/Python-3.3.1/Include/pyport.h" 2
# 673 "/Users/parrt/tmp/Python-3.3.1/Include/pyport.h"
# 1 "/usr/include/termios.h" 1 3 4
# 27 "/usr/include/termios.h" 3 4
# 1 "/usr/include/sys/termios.h" 1 3 4
# 265 "/usr/include/sys/termios.h" 3 4
typedef unsigned long tcflag_t;
typedef unsigned char cc_t;
typedef unsigned long speed_t;

struct termios {
 tcflag_t c_iflag;
 tcflag_t c_oflag;
 tcflag_t c_cflag;
 tcflag_t c_lflag;
 cc_t c_cc[20];
 speed_t c_ispeed;
 speed_t c_ospeed;
};
# 332 "/usr/include/sys/termios.h" 3 4

speed_t cfgetispeed(const struct termios *);
speed_t cfgetospeed(const struct termios *);
int cfsetispeed(struct termios *, speed_t);
int cfsetospeed(struct termios *, speed_t);
int tcgetattr(int, struct termios *);
int tcsetattr(int, int, const struct termios *);
int tcdrain(int) __asm("_" "tcdrain" );
int tcflow(int, int);
int tcflush(int, int);
int tcsendbreak(int, int);


void cfmakeraw(struct termios *);
int cfsetspeed(struct termios *, speed_t);


# 358 "/usr/include/sys/termios.h" 3 4
# 1 "/usr/include/sys/ttycom.h" 1 3 4
# 72 "/usr/include/sys/ttycom.h" 3 4
# 1 "/usr/include/sys/ioccom.h" 1 3 4
# 73 "/usr/include/sys/ttycom.h" 2 3 4
# 83 "/usr/include/sys/ttycom.h" 3 4
struct winsize {
 unsigned short ws_row;
 unsigned short ws_col;
 unsigned short ws_xpixel;
 unsigned short ws_ypixel;
};
# 359 "/usr/include/sys/termios.h" 2 3 4
# 367 "/usr/include/sys/termios.h" 3 4
# 1 "/usr/include/sys/ttydefaults.h" 1 3 4
# 368 "/usr/include/sys/termios.h" 2 3 4
# 28 "/usr/include/termios.h" 2 3 4








pid_t tcgetsid(int);

# 674 "/Users/parrt/tmp/Python-3.3.1/Include/pyport.h" 2
extern int openpty(int *, int *, char *, struct termios *, struct winsize *);
extern pid_t forkpty(int *, char *, struct termios *, struct winsize *);
# 700 "/Users/parrt/tmp/Python-3.3.1/Include/pyport.h"
# 1 "/usr/include/ctype.h" 1 3 4
# 69 "/usr/include/ctype.h" 3 4
# 1 "/usr/include/runetype.h" 1 3 4
# 70 "/usr/include/runetype.h" 3 4
typedef __darwin_wint_t wint_t;
# 81 "/usr/include/runetype.h" 3 4
typedef struct {
 __darwin_rune_t __min;
 __darwin_rune_t __max;
 __darwin_rune_t __map;
 __uint32_t *__types;
} _RuneEntry;

typedef struct {
 int __nranges;
 _RuneEntry *__ranges;
} _RuneRange;

typedef struct {
 char __name[14];
 __uint32_t __mask;
} _RuneCharClass;

typedef struct {
 char __magic[8];
 char __encoding[32];

 __darwin_rune_t (*__sgetrune)(const char *, __darwin_size_t, char const **);
 int (*__sputrune)(__darwin_rune_t, char *, __darwin_size_t, char **);
 __darwin_rune_t __invalid_rune;

 __uint32_t __runetype[(1 <<8 )];
 __darwin_rune_t __maplower[(1 <<8 )];
 __darwin_rune_t __mapupper[(1 <<8 )];






 _RuneRange __runetype_ext;
 _RuneRange __maplower_ext;
 _RuneRange __mapupper_ext;

 void *__variable;
 int __variable_len;




 int __ncharclasses;
 _RuneCharClass *__charclasses;
} _RuneLocale;




extern _RuneLocale _DefaultRuneLocale;
extern _RuneLocale *_CurrentRuneLocale;

# 70 "/usr/include/ctype.h" 2 3 4
# 145 "/usr/include/ctype.h" 3 4

unsigned long ___runetype(__darwin_ct_rune_t);
__darwin_ct_rune_t ___tolower(__darwin_ct_rune_t);
__darwin_ct_rune_t ___toupper(__darwin_ct_rune_t);


static __inline int
isascii(int _c)
{
 return ((_c & ~0x7F) == 0);
}
# 164 "/usr/include/ctype.h" 3 4

int __maskrune(__darwin_ct_rune_t, unsigned long);



static __inline int
__istype(__darwin_ct_rune_t _c, unsigned long _f)
{



 return (isascii(_c) ? !!(_DefaultRuneLocale.__runetype[_c] & _f)
  : !!__maskrune(_c, _f));

}

static __inline __darwin_ct_rune_t
__isctype(__darwin_ct_rune_t _c, unsigned long _f)
{



 return (_c < 0 || _c >= (1 <<8 )) ? 0 :
  !!(_DefaultRuneLocale.__runetype[_c] & _f);

}
# 204 "/usr/include/ctype.h" 3 4

__darwin_ct_rune_t __toupper(__darwin_ct_rune_t);
__darwin_ct_rune_t __tolower(__darwin_ct_rune_t);



static __inline int
__wcwidth(__darwin_ct_rune_t _c)
{
 unsigned int _x;

 if (_c == 0)
  return (0);
 _x = (unsigned int)__maskrune(_c, 0xe0000000L|0x00040000L);
 if ((_x & 0xe0000000L) != 0)
  return ((_x & 0xe0000000L) >> 30);
 return ((_x & 0x00040000L) != 0 ? 1 : -1);
}






static __inline int
isalnum(int _c)
{
 return (__istype(_c, 0x00000100L|0x00000400L));
}

static __inline int
isalpha(int _c)
{
 return (__istype(_c, 0x00000100L));
}

static __inline int
isblank(int _c)
{
 return (__istype(_c, 0x00020000L));
}

static __inline int
iscntrl(int _c)
{
 return (__istype(_c, 0x00000200L));
}


static __inline int
isdigit(int _c)
{
 return (__isctype(_c, 0x00000400L));
}

static __inline int
isgraph(int _c)
{
 return (__istype(_c, 0x00000800L));
}

static __inline int
islower(int _c)
{
 return (__istype(_c, 0x00001000L));
}

static __inline int
isprint(int _c)
{
 return (__istype(_c, 0x00040000L));
}

static __inline int
ispunct(int _c)
{
 return (__istype(_c, 0x00002000L));
}

static __inline int
isspace(int _c)
{
 return (__istype(_c, 0x00004000L));
}

static __inline int
isupper(int _c)
{
 return (__istype(_c, 0x00008000L));
}


static __inline int
isxdigit(int _c)
{
 return (__isctype(_c, 0x00010000L));
}

static __inline int
toascii(int _c)
{
 return (_c & 0x7F);
}

static __inline int
tolower(int _c)
{
        return (__tolower(_c));
}

static __inline int
toupper(int _c)
{
        return (__toupper(_c));
}


static __inline int
digittoint(int _c)
{
 return (__maskrune(_c, 0x0F));
}

static __inline int
ishexnumber(int _c)
{
 return (__istype(_c, 0x00010000L));
}

static __inline int
isideogram(int _c)
{
 return (__istype(_c, 0x00080000L));
}

static __inline int
isnumber(int _c)
{
 return (__istype(_c, 0x00000400L));
}

static __inline int
isphonogram(int _c)
{
 return (__istype(_c, 0x00200000L));
}

static __inline int
isrune(int _c)
{
 return (__istype(_c, 0xFFFFFFF0L));
}

static __inline int
isspecial(int _c)
{
 return (__istype(_c, 0x00100000L));
}
# 701 "/Users/parrt/tmp/Python-3.3.1/Include/pyport.h" 2
# 1 "/usr/include/wctype.h" 1 3 4
# 39 "/usr/include/wctype.h" 3 4
typedef __darwin_wctrans_t wctrans_t;
# 53 "/usr/include/wctype.h" 3 4
# 1 "/usr/include/_wctype.h" 1 3 4
# 52 "/usr/include/_wctype.h" 3 4
typedef __darwin_wctype_t wctype_t;
# 71 "/usr/include/_wctype.h" 3 4
static __inline int
iswalnum(wint_t _wc)
{
 return (__istype(_wc, 0x00000100L|0x00000400L));
}

static __inline int
iswalpha(wint_t _wc)
{
 return (__istype(_wc, 0x00000100L));
}

static __inline int
iswcntrl(wint_t _wc)
{
 return (__istype(_wc, 0x00000200L));
}

static __inline int
iswctype(wint_t _wc, wctype_t _charclass)
{
 return (__istype(_wc, _charclass));
}

static __inline int
iswdigit(wint_t _wc)
{
 return (__isctype(_wc, 0x00000400L));
}

static __inline int
iswgraph(wint_t _wc)
{
 return (__istype(_wc, 0x00000800L));
}

static __inline int
iswlower(wint_t _wc)
{
 return (__istype(_wc, 0x00001000L));
}

static __inline int
iswprint(wint_t _wc)
{
 return (__istype(_wc, 0x00040000L));
}

static __inline int
iswpunct(wint_t _wc)
{
 return (__istype(_wc, 0x00002000L));
}

static __inline int
iswspace(wint_t _wc)
{
 return (__istype(_wc, 0x00004000L));
}

static __inline int
iswupper(wint_t _wc)
{
 return (__istype(_wc, 0x00008000L));
}

static __inline int
iswxdigit(wint_t _wc)
{
 return (__isctype(_wc, 0x00010000L));
}

static __inline wint_t
towlower(wint_t _wc)
{
        return (__tolower(_wc));
}

static __inline wint_t
towupper(wint_t _wc)
{
        return (__toupper(_wc));
}
# 176 "/usr/include/_wctype.h" 3 4

wctype_t
 wctype(const char *);

# 54 "/usr/include/wctype.h" 2 3 4
# 62 "/usr/include/wctype.h" 3 4
static __inline int
iswblank(wint_t _wc)
{
 return (__istype(_wc, 0x00020000L));
}


static __inline int
iswascii(wint_t _wc)
{
 return ((_wc & ~0x7F) == 0);
}

static __inline int
iswhexnumber(wint_t _wc)
{
 return (__istype(_wc, 0x00010000L));
}

static __inline int
iswideogram(wint_t _wc)
{
 return (__istype(_wc, 0x00080000L));
}

static __inline int
iswnumber(wint_t _wc)
{
 return (__istype(_wc, 0x00000400L));
}

static __inline int
iswphonogram(wint_t _wc)
{
 return (__istype(_wc, 0x00200000L));
}

static __inline int
iswrune(wint_t _wc)
{
 return (__istype(_wc, 0xFFFFFFF0L));
}

static __inline int
iswspecial(wint_t _wc)
{
 return (__istype(_wc, 0x00100000L));
}
# 130 "/usr/include/wctype.h" 3 4


wint_t nextwctype(wint_t, wctype_t);

wint_t towctrans(wint_t, wctrans_t);
wctrans_t
 wctrans(const char *);

# 702 "/Users/parrt/tmp/Python-3.3.1/Include/pyport.h" 2
# 51 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/pymacro.h" 1
# 52 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2

# 1 "/Users/parrt/tmp/Python-3.3.1/Include/pyatomic.h" 1







# 1 "/Users/parrt/tmp/Python-3.3.1/Include/dynamic_annotations.h" 1
# 375 "/Users/parrt/tmp/Python-3.3.1/Include/dynamic_annotations.h"
void AnnotateRWLockCreate(const char *file, int line,
                          const volatile void *lock);
void AnnotateRWLockDestroy(const char *file, int line,
                           const volatile void *lock);
void AnnotateRWLockAcquired(const char *file, int line,
                            const volatile void *lock, long is_w);
void AnnotateRWLockReleased(const char *file, int line,
                            const volatile void *lock, long is_w);
void AnnotateBarrierInit(const char *file, int line,
                         const volatile void *barrier, long count,
                         long reinitialization_allowed);
void AnnotateBarrierWaitBefore(const char *file, int line,
                               const volatile void *barrier);
void AnnotateBarrierWaitAfter(const char *file, int line,
                              const volatile void *barrier);
void AnnotateBarrierDestroy(const char *file, int line,
                            const volatile void *barrier);
void AnnotateCondVarWait(const char *file, int line,
                         const volatile void *cv,
                         const volatile void *lock);
void AnnotateCondVarSignal(const char *file, int line,
                           const volatile void *cv);
void AnnotateCondVarSignalAll(const char *file, int line,
                              const volatile void *cv);
void AnnotatePublishMemoryRange(const char *file, int line,
                                const volatile void *address,
                                long size);
void AnnotateUnpublishMemoryRange(const char *file, int line,
                                  const volatile void *address,
                                  long size);
void AnnotatePCQCreate(const char *file, int line,
                       const volatile void *pcq);
void AnnotatePCQDestroy(const char *file, int line,
                        const volatile void *pcq);
void AnnotatePCQPut(const char *file, int line,
                    const volatile void *pcq);
void AnnotatePCQGet(const char *file, int line,
                    const volatile void *pcq);
void AnnotateNewMemory(const char *file, int line,
                       const volatile void *address,
                       long size);
void AnnotateExpectRace(const char *file, int line,
                        const volatile void *address,
                        const char *description);
void AnnotateBenignRace(const char *file, int line,
                        const volatile void *address,
                        const char *description);
void AnnotateBenignRaceSized(const char *file, int line,
                        const volatile void *address,
                        long size,
                        const char *description);
void AnnotateMutexIsUsedAsCondVar(const char *file, int line,
                                  const volatile void *mu);
void AnnotateTraceMemory(const char *file, int line,
                         const volatile void *arg);
void AnnotateThreadName(const char *file, int line,
                        const char *name);
void AnnotateIgnoreReadsBegin(const char *file, int line);
void AnnotateIgnoreReadsEnd(const char *file, int line);
void AnnotateIgnoreWritesBegin(const char *file, int line);
void AnnotateIgnoreWritesEnd(const char *file, int line);
void AnnotateEnableRaceDetection(const char *file, int line, int enable);
void AnnotateNoOp(const char *file, int line,
                  const volatile void *arg);
void AnnotateFlushState(const char *file, int line);
# 456 "/Users/parrt/tmp/Python-3.3.1/Include/dynamic_annotations.h"
int RunningOnValgrind(void);
# 9 "/Users/parrt/tmp/Python-3.3.1/Include/pyatomic.h" 2
# 23 "/Users/parrt/tmp/Python-3.3.1/Include/pyatomic.h"
typedef enum _Py_memory_order {
    _Py_memory_order_relaxed,
    _Py_memory_order_acquire,
    _Py_memory_order_release,
    _Py_memory_order_acq_rel,
    _Py_memory_order_seq_cst
} _Py_memory_order;

typedef struct _Py_atomic_address {
    void *_value;
} _Py_atomic_address;

typedef struct _Py_atomic_int {
    int _value;
} _Py_atomic_int;





static __inline__ void
_Py_atomic_signal_fence(_Py_memory_order order)
{
    if (order != _Py_memory_order_relaxed)
        __asm__ volatile("":::"memory");
}

static __inline__ void
_Py_atomic_thread_fence(_Py_memory_order order)
{
    if (order != _Py_memory_order_relaxed)
        __asm__ volatile("mfence":::"memory");
}


static __inline__ void
_Py_ANNOTATE_MEMORY_ORDER(const volatile void *address, _Py_memory_order order)
{
    (void)address;
    switch(order) {
    case _Py_memory_order_release:
    case _Py_memory_order_acq_rel:
    case _Py_memory_order_seq_cst:
        ;
        break;
    case _Py_memory_order_relaxed:
    case _Py_memory_order_acquire:
        break;
    }
    switch(order) {
    case _Py_memory_order_acquire:
    case _Py_memory_order_acq_rel:
    case _Py_memory_order_seq_cst:
        ;
        break;
    case _Py_memory_order_relaxed:
    case _Py_memory_order_release:
        break;
    }
}
# 54 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 64 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h"
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/pymath.h" 1
# 65 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/pytime.h" 1





# 1 "/Users/parrt/tmp/Python-3.3.1/Include/object.h" 1
# 105 "/Users/parrt/tmp/Python-3.3.1/Include/object.h"
typedef struct _object {
   
    Py_ssize_t ob_refcnt;
    struct _typeobject *ob_type;
} PyObject;

typedef struct {
    PyObject ob_base;
    Py_ssize_t ob_size;
} PyVarObject;
# 140 "/Users/parrt/tmp/Python-3.3.1/Include/object.h"
typedef struct _Py_Identifier {
    struct _Py_Identifier *next;
    const char* string;
    PyObject *object;
} _Py_Identifier;
# 164 "/Users/parrt/tmp/Python-3.3.1/Include/object.h"
typedef PyObject * (*unaryfunc)(PyObject *);
typedef PyObject * (*binaryfunc)(PyObject *, PyObject *);
typedef PyObject * (*ternaryfunc)(PyObject *, PyObject *, PyObject *);
typedef int (*inquiry)(PyObject *);
typedef Py_ssize_t (*lenfunc)(PyObject *);
typedef PyObject *(*ssizeargfunc)(PyObject *, Py_ssize_t);
typedef PyObject *(*ssizessizeargfunc)(PyObject *, Py_ssize_t, Py_ssize_t);
typedef int(*ssizeobjargproc)(PyObject *, Py_ssize_t, PyObject *);
typedef int(*ssizessizeobjargproc)(PyObject *, Py_ssize_t, Py_ssize_t, PyObject *);
typedef int(*objobjargproc)(PyObject *, PyObject *, PyObject *);



typedef struct bufferinfo {
    void *buf;
    PyObject *obj;
    Py_ssize_t len;
    Py_ssize_t itemsize;

    int readonly;
    int ndim;
    char *format;
    Py_ssize_t *shape;
    Py_ssize_t *strides;
    Py_ssize_t *suboffsets;
    void *internal;
} Py_buffer;

typedef int (*getbufferproc)(PyObject *, Py_buffer *, int);
typedef void (*releasebufferproc)(PyObject *, Py_buffer *);
# 230 "/Users/parrt/tmp/Python-3.3.1/Include/object.h"
typedef int (*objobjproc)(PyObject *, PyObject *);
typedef int (*visitproc)(PyObject *, void *);
typedef int (*traverseproc)(PyObject *, visitproc, void *);


typedef struct {




    binaryfunc nb_add;
    binaryfunc nb_subtract;
    binaryfunc nb_multiply;
    binaryfunc nb_remainder;
    binaryfunc nb_divmod;
    ternaryfunc nb_power;
    unaryfunc nb_negative;
    unaryfunc nb_positive;
    unaryfunc nb_absolute;
    inquiry nb_bool;
    unaryfunc nb_invert;
    binaryfunc nb_lshift;
    binaryfunc nb_rshift;
    binaryfunc nb_and;
    binaryfunc nb_xor;
    binaryfunc nb_or;
    unaryfunc nb_int;
    void *nb_reserved;
    unaryfunc nb_float;

    binaryfunc nb_inplace_add;
    binaryfunc nb_inplace_subtract;
    binaryfunc nb_inplace_multiply;
    binaryfunc nb_inplace_remainder;
    ternaryfunc nb_inplace_power;
    binaryfunc nb_inplace_lshift;
    binaryfunc nb_inplace_rshift;
    binaryfunc nb_inplace_and;
    binaryfunc nb_inplace_xor;
    binaryfunc nb_inplace_or;

    binaryfunc nb_floor_divide;
    binaryfunc nb_true_divide;
    binaryfunc nb_inplace_floor_divide;
    binaryfunc nb_inplace_true_divide;

    unaryfunc nb_index;
} PyNumberMethods;

typedef struct {
    lenfunc sq_length;
    binaryfunc sq_concat;
    ssizeargfunc sq_repeat;
    ssizeargfunc sq_item;
    void *was_sq_slice;
    ssizeobjargproc sq_ass_item;
    void *was_sq_ass_slice;
    objobjproc sq_contains;

    binaryfunc sq_inplace_concat;
    ssizeargfunc sq_inplace_repeat;
} PySequenceMethods;

typedef struct {
    lenfunc mp_length;
    binaryfunc mp_subscript;
    objobjargproc mp_ass_subscript;
} PyMappingMethods;


typedef struct {
     getbufferproc bf_getbuffer;
     releasebufferproc bf_releasebuffer;
} PyBufferProcs;


typedef void (*freefunc)(void *);
typedef void (*destructor)(PyObject *);





typedef int (*printfunc)(PyObject *, FILE *, int);

typedef PyObject *(*getattrfunc)(PyObject *, char *);
typedef PyObject *(*getattrofunc)(PyObject *, PyObject *);
typedef int (*setattrfunc)(PyObject *, char *, PyObject *);
typedef int (*setattrofunc)(PyObject *, PyObject *, PyObject *);
typedef PyObject *(*reprfunc)(PyObject *);
typedef Py_hash_t (*hashfunc)(PyObject *);
typedef PyObject *(*richcmpfunc) (PyObject *, PyObject *, int);
typedef PyObject *(*getiterfunc) (PyObject *);
typedef PyObject *(*iternextfunc) (PyObject *);
typedef PyObject *(*descrgetfunc) (PyObject *, PyObject *, PyObject *);
typedef int (*descrsetfunc) (PyObject *, PyObject *, PyObject *);
typedef int (*initproc)(PyObject *, PyObject *, PyObject *);
typedef PyObject *(*newfunc)(struct _typeobject *, PyObject *, PyObject *);
typedef PyObject *(*allocfunc)(struct _typeobject *, Py_ssize_t);




typedef struct _typeobject {
    PyVarObject ob_base;
    const char *tp_name;
    Py_ssize_t tp_basicsize, tp_itemsize;



    destructor tp_dealloc;
    printfunc tp_print;
    getattrfunc tp_getattr;
    setattrfunc tp_setattr;
    void *tp_reserved;
    reprfunc tp_repr;



    PyNumberMethods *tp_as_number;
    PySequenceMethods *tp_as_sequence;
    PyMappingMethods *tp_as_mapping;



    hashfunc tp_hash;
    ternaryfunc tp_call;
    reprfunc tp_str;
    getattrofunc tp_getattro;
    setattrofunc tp_setattro;


    PyBufferProcs *tp_as_buffer;


    long tp_flags;

    const char *tp_doc;



    traverseproc tp_traverse;


    inquiry tp_clear;



    richcmpfunc tp_richcompare;


    Py_ssize_t tp_weaklistoffset;


    getiterfunc tp_iter;
    iternextfunc tp_iternext;


    struct PyMethodDef *tp_methods;
    struct PyMemberDef *tp_members;
    struct PyGetSetDef *tp_getset;
    struct _typeobject *tp_base;
    PyObject *tp_dict;
    descrgetfunc tp_descr_get;
    descrsetfunc tp_descr_set;
    Py_ssize_t tp_dictoffset;
    initproc tp_init;
    allocfunc tp_alloc;
    newfunc tp_new;
    freefunc tp_free;
    inquiry tp_is_gc;
    PyObject *tp_bases;
    PyObject *tp_mro;
    PyObject *tp_cache;
    PyObject *tp_subclasses;
    PyObject *tp_weaklist;
    destructor tp_del;


    unsigned int tp_version_tag;
# 419 "/Users/parrt/tmp/Python-3.3.1/Include/object.h"
} PyTypeObject;


typedef struct{
    int slot;
    void *pfunc;
} PyType_Slot;

typedef struct{
    const char* name;
    int basicsize;
    int itemsize;
    int flags;
    PyType_Slot *slots;
} PyType_Spec;

PyObject* PyType_FromSpec(PyType_Spec*);

PyObject* PyType_FromSpecWithBases(PyType_Spec*, PyObject*);




typedef struct _heaptypeobject {


    PyTypeObject ht_type;
    PyNumberMethods as_number;
    PyMappingMethods as_mapping;
    PySequenceMethods as_sequence;




    PyBufferProcs as_buffer;
    PyObject *ht_name, *ht_slots, *ht_qualname;
    struct _dictkeysobject *ht_cached_keys;

} PyHeapTypeObject;







int PyType_IsSubtype(PyTypeObject *, PyTypeObject *);



extern PyTypeObject PyType_Type;
extern PyTypeObject PyBaseObject_Type;
extern PyTypeObject PySuper_Type;

long PyType_GetFlags(PyTypeObject*);





int PyType_Ready(PyTypeObject *);
PyObject * PyType_GenericAlloc(PyTypeObject *, Py_ssize_t);
PyObject * PyType_GenericNew(PyTypeObject *,
                                               PyObject *, PyObject *);

PyObject * _PyType_Lookup(PyTypeObject *, PyObject *);
PyObject * _PyObject_LookupSpecial(PyObject *, _Py_Identifier *);
PyTypeObject * _PyType_CalculateMetaclass(PyTypeObject *, PyObject *);

unsigned int PyType_ClearCache(void);
void PyType_Modified(PyTypeObject *);


struct _Py_Identifier;

int PyObject_Print(PyObject *, FILE *, int);
void _Py_BreakPoint(void);
void _PyObject_Dump(PyObject *);

PyObject * PyObject_Repr(PyObject *);
PyObject * PyObject_Str(PyObject *);
PyObject * PyObject_ASCII(PyObject *);
PyObject * PyObject_Bytes(PyObject *);
PyObject * PyObject_RichCompare(PyObject *, PyObject *, int);
int PyObject_RichCompareBool(PyObject *, PyObject *, int);
PyObject * PyObject_GetAttrString(PyObject *, const char *);
int PyObject_SetAttrString(PyObject *, const char *, PyObject *);
int PyObject_HasAttrString(PyObject *, const char *);
PyObject * PyObject_GetAttr(PyObject *, PyObject *);
int PyObject_SetAttr(PyObject *, PyObject *, PyObject *);
int PyObject_HasAttr(PyObject *, PyObject *);
int _PyObject_IsAbstract(PyObject *);
PyObject * _PyObject_GetAttrId(PyObject *, struct _Py_Identifier *);
int _PyObject_SetAttrId(PyObject *, struct _Py_Identifier *, PyObject *);
int _PyObject_HasAttrId(PyObject *, struct _Py_Identifier *);

PyObject ** _PyObject_GetDictPtr(PyObject *);

PyObject * PyObject_SelfIter(PyObject *);

PyObject * _PyObject_NextNotImplemented(PyObject *);

PyObject * PyObject_GenericGetAttr(PyObject *, PyObject *);
int PyObject_GenericSetAttr(PyObject *,
                                              PyObject *, PyObject *);
int PyObject_GenericSetDict(PyObject *, PyObject *, void *);
Py_hash_t PyObject_Hash(PyObject *);
Py_hash_t PyObject_HashNotImplemented(PyObject *);
int PyObject_IsTrue(PyObject *);
int PyObject_Not(PyObject *);
int PyCallable_Check(PyObject *);

void PyObject_ClearWeakRefs(PyObject *);



PyObject *
_PyObject_GenericGetAttrWithDict(PyObject *, PyObject *, PyObject *);
int
_PyObject_GenericSetAttrWithDict(PyObject *, PyObject *,
                                 PyObject *, PyObject *);



PyObject *
_PyObject_GetBuiltin(const char *name);







PyObject * PyObject_Dir(PyObject *);



int Py_ReprEnter(PyObject *);
void Py_ReprLeave(PyObject *);



Py_hash_t _Py_HashDouble(double);
Py_hash_t _Py_HashPointer(void*);
Py_hash_t _Py_HashBytes(unsigned char*, Py_ssize_t);


typedef struct {
    Py_hash_t prefix;
    Py_hash_t suffix;
} _Py_HashSecret_t;
extern _Py_HashSecret_t _Py_HashSecret;
# 830 "/Users/parrt/tmp/Python-3.3.1/Include/object.h"
void Py_IncRef(PyObject *);
void Py_DecRef(PyObject *);







extern PyObject _Py_NoneStruct;
# 849 "/Users/parrt/tmp/Python-3.3.1/Include/object.h"
extern PyObject _Py_NotImplementedStruct;
# 867 "/Users/parrt/tmp/Python-3.3.1/Include/object.h"
extern int _Py_SwappedOp[];
# 966 "/Users/parrt/tmp/Python-3.3.1/Include/object.h"
void _PyTrash_deposit_object(PyObject*);
void _PyTrash_destroy_chain(void);
extern int _PyTrash_delete_nesting;
extern PyObject * _PyTrash_delete_later;


void _PyTrash_thread_deposit_object(PyObject*);
void _PyTrash_thread_destroy_chain(void);
# 993 "/Users/parrt/tmp/Python-3.3.1/Include/object.h"
void
_PyDebugAllocatorStats(FILE *out, const char *block_name, int num_blocks,
                       size_t sizeof_block);
void
_PyObject_DebugTypeStats(FILE *out);
# 7 "/Users/parrt/tmp/Python-3.3.1/Include/pytime.h" 2
# 17 "/Users/parrt/tmp/Python-3.3.1/Include/pytime.h"
typedef struct timeval _PyTime_timeval;
# 26 "/Users/parrt/tmp/Python-3.3.1/Include/pytime.h"
typedef struct {
    const char *implementation;
    int monotonic;
    int adjustable;
    double resolution;
} _Py_clock_info_t;




void _PyTime_gettimeofday(_PyTime_timeval *tp);



void _PyTime_gettimeofday_info(
    _PyTime_timeval *tp,
    _Py_clock_info_t *info);
# 57 "/Users/parrt/tmp/Python-3.3.1/Include/pytime.h"
int _PyTime_ObjectToTime_t(
    PyObject *obj,
    time_t *sec);


PyObject * _PyLong_FromTime_t(
    time_t sec);


time_t _PyLong_AsTime_t(
    PyObject *obj);




int _PyTime_ObjectToTimeval(
    PyObject *obj,
    time_t *sec,
    long *usec);




int _PyTime_ObjectToTimespec(
    PyObject *obj,
    time_t *sec,
    long *nsec);



void _PyTime_Init(void);
# 66 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/pymem.h" 1
# 52 "/Users/parrt/tmp/Python-3.3.1/Include/pymem.h"
void * PyMem_Malloc(size_t);
void * PyMem_Realloc(void *, size_t);
void PyMem_Free(void *);
# 67 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2


# 1 "/Users/parrt/tmp/Python-3.3.1/Include/objimpl.h" 1
# 97 "/Users/parrt/tmp/Python-3.3.1/Include/objimpl.h"
void * PyObject_Malloc(size_t);
void * PyObject_Realloc(void *, size_t);
void PyObject_Free(void *);





void _PyObject_DebugMallocStats(FILE *out);
# 149 "/Users/parrt/tmp/Python-3.3.1/Include/objimpl.h"
PyObject * PyObject_Init(PyObject *, PyTypeObject *);
PyVarObject * PyObject_InitVar(PyVarObject *,
                                                 PyTypeObject *, Py_ssize_t);
PyObject * _PyObject_New(PyTypeObject *);
PyVarObject * _PyObject_NewVar(PyTypeObject *, Py_ssize_t);
# 231 "/Users/parrt/tmp/Python-3.3.1/Include/objimpl.h"
Py_ssize_t PyGC_Collect(void);
# 240 "/Users/parrt/tmp/Python-3.3.1/Include/objimpl.h"
PyVarObject * _PyObject_GC_Resize(PyVarObject *, Py_ssize_t);





typedef union _gc_head {
    struct {
        union _gc_head *gc_next;
        union _gc_head *gc_prev;
        Py_ssize_t gc_refs;
    } gc;
    long double dummy;
} PyGC_Head;

extern PyGC_Head *_PyGC_generation0;
# 300 "/Users/parrt/tmp/Python-3.3.1/Include/objimpl.h"
PyObject * _PyObject_GC_Malloc(size_t);
PyObject * _PyObject_GC_New(PyTypeObject *);
PyVarObject * _PyObject_GC_NewVar(PyTypeObject *, Py_ssize_t);
void PyObject_GC_Track(void *);
void PyObject_GC_UnTrack(void *);
void PyObject_GC_Del(void *);
# 70 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/typeslots.h" 1
# 71 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2

# 1 "/Users/parrt/tmp/Python-3.3.1/Include/pydebug.h" 1







extern int Py_DebugFlag;
extern int Py_VerboseFlag;
extern int Py_QuietFlag;
extern int Py_InteractiveFlag;
extern int Py_InspectFlag;
extern int Py_OptimizeFlag;
extern int Py_NoSiteFlag;
extern int Py_BytesWarningFlag;
extern int Py_UseClassExceptionsFlag;
extern int Py_FrozenFlag;
extern int Py_IgnoreEnvironmentFlag;
extern int Py_DontWriteBytecodeFlag;
extern int Py_NoUserSiteDirectory;
extern int Py_UnbufferedStdioFlag;
extern int Py_HashRandomizationFlag;
# 73 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2

# 1 "/Users/parrt/tmp/Python-3.3.1/Include/bytearrayobject.h" 1
# 9 "/Users/parrt/tmp/Python-3.3.1/Include/bytearrayobject.h"
# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stdarg.h" 1 3 4
# 43 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stdarg.h" 3 4
typedef __builtin_va_list __gnuc_va_list;
# 10 "/Users/parrt/tmp/Python-3.3.1/Include/bytearrayobject.h" 2
# 23 "/Users/parrt/tmp/Python-3.3.1/Include/bytearrayobject.h"
typedef struct {
    PyVarObject ob_base;

    int ob_exports;
    Py_ssize_t ob_alloc;
    char *ob_bytes;
} PyByteArrayObject;



extern PyTypeObject PyByteArray_Type;
extern PyTypeObject PyByteArrayIter_Type;






PyObject * PyByteArray_FromObject(PyObject *);
PyObject * PyByteArray_Concat(PyObject *, PyObject *);
PyObject * PyByteArray_FromStringAndSize(const char *, Py_ssize_t);
Py_ssize_t PyByteArray_Size(PyObject *);
char * PyByteArray_AsString(PyObject *);
int PyByteArray_Resize(PyObject *, Py_ssize_t);
# 55 "/Users/parrt/tmp/Python-3.3.1/Include/bytearrayobject.h"
extern char _PyByteArray_empty_string[];
# 75 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/bytesobject.h" 1
# 31 "/Users/parrt/tmp/Python-3.3.1/Include/bytesobject.h"
typedef struct {
    PyVarObject ob_base;
    Py_hash_t ob_shash;
    char ob_sval[1];






} PyBytesObject;


extern PyTypeObject PyBytes_Type;
extern PyTypeObject PyBytesIter_Type;





PyObject * PyBytes_FromStringAndSize(const char *, Py_ssize_t);
PyObject * PyBytes_FromString(const char *);
PyObject * PyBytes_FromObject(PyObject *);
PyObject * PyBytes_FromFormatV(const char*, va_list)
    __attribute__((format(printf, 1, 0)));
PyObject * PyBytes_FromFormat(const char*, ...)
    __attribute__((format(printf, 1, 2)));
Py_ssize_t PyBytes_Size(PyObject *);
char * PyBytes_AsString(PyObject *);
PyObject * PyBytes_Repr(PyObject *, int);
void PyBytes_Concat(PyObject **, PyObject *);
void PyBytes_ConcatAndDel(PyObject **, PyObject *);

int _PyBytes_Resize(PyObject **, Py_ssize_t);

PyObject * PyBytes_DecodeEscape(const char *, Py_ssize_t,
         const char *, Py_ssize_t,
         const char *);
# 80 "/Users/parrt/tmp/Python-3.3.1/Include/bytesobject.h"
PyObject * _PyBytes_Join(PyObject *sep, PyObject *x);







int PyBytes_AsStringAndSize(
    register PyObject *obj,
    register char **s,
    register Py_ssize_t *len


    );





Py_ssize_t _PyBytes_InsertThousandsGroupingLocale(char *buffer,
                                                   Py_ssize_t n_buffer,
                                                   char *digits,
                                                   Py_ssize_t n_digits,
                                                   Py_ssize_t min_width);




Py_ssize_t _PyBytes_InsertThousandsGrouping(char *buffer,
                                                   Py_ssize_t n_buffer,
                                                   char *digits,
                                                   Py_ssize_t n_digits,
                                                   Py_ssize_t min_width,
                                                   const char *grouping,
                                                   const char *thousands_sep);
# 76 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h" 1
# 93 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
typedef wchar_t Py_UNICODE;
# 115 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
# 1 "/usr/include/wchar.h" 1 3 4
# 85 "/usr/include/wchar.h" 3 4
typedef __darwin_mbstate_t mbstate_t;
# 120 "/usr/include/wchar.h" 3 4

wint_t btowc(int);
wint_t fgetwc(FILE *);
wchar_t *fgetws(wchar_t * , int, FILE * );
wint_t fputwc(wchar_t, FILE *);
int fputws(const wchar_t * , FILE * );
int fwide(FILE *, int);
int fwprintf(FILE * , const wchar_t * , ...) ;
int fwscanf(FILE * , const wchar_t * , ...) ;
wint_t getwc(FILE *);
wint_t getwchar(void);
size_t mbrlen(const char * , size_t, mbstate_t * );
size_t mbrtowc(wchar_t * , const char * , size_t,
     mbstate_t * );
int mbsinit(const mbstate_t *);
size_t mbsrtowcs(wchar_t * , const char ** , size_t,
     mbstate_t * );
wint_t putwc(wchar_t, FILE *);
wint_t putwchar(wchar_t);
int swprintf(wchar_t * , size_t, const wchar_t * ,
     ...) ;
int swscanf(const wchar_t * , const wchar_t * , ...) ;
wint_t ungetwc(wint_t, FILE *);
int vfwprintf(FILE * , const wchar_t * ,
     __darwin_va_list) ;
int vswprintf(wchar_t * , size_t, const wchar_t * ,
     __darwin_va_list) ;
int vwprintf(const wchar_t * , __darwin_va_list) ;
size_t wcrtomb(char * , wchar_t, mbstate_t * );
wchar_t *wcscat(wchar_t * , const wchar_t * );
wchar_t *wcschr(const wchar_t *, wchar_t);
int wcscmp(const wchar_t *, const wchar_t *);
int wcscoll(const wchar_t *, const wchar_t *);
wchar_t *wcscpy(wchar_t * , const wchar_t * );
size_t wcscspn(const wchar_t *, const wchar_t *);
size_t wcsftime(wchar_t * , size_t, const wchar_t * ,
     const struct tm * ) __asm("_" "wcsftime" );
size_t wcslen(const wchar_t *);
wchar_t *wcsncat(wchar_t * , const wchar_t * , size_t);
int wcsncmp(const wchar_t *, const wchar_t *, size_t);
wchar_t *wcsncpy(wchar_t * , const wchar_t * , size_t);
wchar_t *wcspbrk(const wchar_t *, const wchar_t *);
wchar_t *wcsrchr(const wchar_t *, wchar_t);
size_t wcsrtombs(char * , const wchar_t ** , size_t,
     mbstate_t * );
size_t wcsspn(const wchar_t *, const wchar_t *);
wchar_t *wcsstr(const wchar_t * , const wchar_t * );
size_t wcsxfrm(wchar_t * , const wchar_t * , size_t);
int wctob(wint_t);
double wcstod(const wchar_t * , wchar_t ** );
wchar_t *wcstok(wchar_t * , const wchar_t * ,
     wchar_t ** );
long wcstol(const wchar_t * , wchar_t ** , int);
unsigned long
  wcstoul(const wchar_t * , wchar_t ** , int);
wchar_t *wmemchr(const wchar_t *, wchar_t, size_t);
int wmemcmp(const wchar_t *, const wchar_t *, size_t);
wchar_t *wmemcpy(wchar_t * , const wchar_t * , size_t);
wchar_t *wmemmove(wchar_t *, const wchar_t *, size_t);
wchar_t *wmemset(wchar_t *, wchar_t, size_t);
int wprintf(const wchar_t * , ...) ;
int wscanf(const wchar_t * , ...) ;
int wcswidth(const wchar_t *, size_t);
int wcwidth(wchar_t);

# 194 "/usr/include/wchar.h" 3 4

int vfwscanf(FILE * , const wchar_t * ,
     __darwin_va_list) ;
int vswscanf(const wchar_t * , const wchar_t * ,
     __darwin_va_list) ;
int vwscanf(const wchar_t * , __darwin_va_list) ;
float wcstof(const wchar_t * , wchar_t ** );
long double
 wcstold(const wchar_t * , wchar_t ** ) ;

long long
 wcstoll(const wchar_t * , wchar_t ** , int);
unsigned long long
 wcstoull(const wchar_t * , wchar_t ** , int);


# 219 "/usr/include/wchar.h" 3 4

size_t mbsnrtowcs(wchar_t * , const char ** , size_t,
            size_t, mbstate_t * );
wchar_t *wcpcpy(wchar_t * , const wchar_t * ) __attribute__((visibility("default")));
wchar_t *wcpncpy(wchar_t * , const wchar_t * , size_t) __attribute__((visibility("default")));
wchar_t *wcsdup(const wchar_t *) __attribute__((visibility("default")));
int wcscasecmp(const wchar_t *, const wchar_t *) __attribute__((visibility("default")));
int wcsncasecmp(const wchar_t *, const wchar_t *, size_t n) __attribute__((visibility("default")));
size_t wcsnlen(const wchar_t *, size_t) __attribute__((visibility("default")));
size_t wcsnrtombs(char * , const wchar_t ** , size_t,
            size_t, mbstate_t * );









wchar_t *fgetwln(FILE * , size_t *) __attribute__((visibility("default")));
size_t wcslcat(wchar_t *, const wchar_t *, size_t);
size_t wcslcpy(wchar_t *, const wchar_t *, size_t);

# 116 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h" 2





typedef unsigned int Py_UCS4;







typedef unsigned short Py_UCS2;




typedef unsigned char Py_UCS1;
# 217 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
typedef struct {
# 291 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
    PyObject ob_base;
    Py_ssize_t length;
    Py_hash_t hash;
    struct {
# 303 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
        unsigned int interned:2;
# 331 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
        unsigned int kind:3;




        unsigned int compact:1;



        unsigned int ascii:1;




        unsigned int ready:1;
    } state;
    wchar_t *wstr;
} PyASCIIObject;




typedef struct {
    PyASCIIObject _base;
    Py_ssize_t utf8_length;

    char *utf8;
    Py_ssize_t wstr_length;

} PyCompactUnicodeObject;




typedef struct {
    PyCompactUnicodeObject _base;
    union {
        void *any;
        Py_UCS1 *latin1;
        Py_UCS2 *ucs2;
        Py_UCS4 *ucs4;
    } data;
} PyUnicodeObject;


extern PyTypeObject PyUnicode_Type;
extern PyTypeObject PyUnicodeIter_Type;
# 448 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
enum PyUnicode_Kind {



    PyUnicode_WCHAR_KIND = 0,

    PyUnicode_1BYTE_KIND = 1,
    PyUnicode_2BYTE_KIND = 2,
    PyUnicode_4BYTE_KIND = 4
};
# 599 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_New(
    Py_ssize_t size,
    Py_UCS4 maxchar
    );
# 613 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
int _PyUnicode_Ready(
    PyObject *unicode
    );




PyObject* _PyUnicode_Copy(
    PyObject *unicode
    );
# 644 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
Py_ssize_t PyUnicode_CopyCharacters(
    PyObject *to,
    Py_ssize_t to_start,
    PyObject *from,
    Py_ssize_t from_start,
    Py_ssize_t how_many
    );




void _PyUnicode_FastCopyCharacters(
    PyObject *to,
    Py_ssize_t to_start,
    PyObject *from,
    Py_ssize_t from_start,
    Py_ssize_t how_many
    );
# 673 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
Py_ssize_t PyUnicode_Fill(
    PyObject *unicode,
    Py_ssize_t start,
    Py_ssize_t length,
    Py_UCS4 fill_char
    );



void _PyUnicode_FastFill(
    PyObject *unicode,
    Py_ssize_t start,
    Py_ssize_t length,
    Py_UCS4 fill_char
    );
# 701 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_FromUnicode(
    const Py_UNICODE *u,
    Py_ssize_t size
    );



PyObject* PyUnicode_FromStringAndSize(
    const char *u,
    Py_ssize_t size
    );



PyObject* PyUnicode_FromString(
    const char *u
    );




PyObject* PyUnicode_FromKindAndData(
    int kind,
    const void *buffer,
    Py_ssize_t size);



PyObject* _PyUnicode_FromASCII(
    const char *buffer,
    Py_ssize_t size);


PyObject* PyUnicode_Substring(
    PyObject *str,
    Py_ssize_t start,
    Py_ssize_t end);




Py_UCS4 _PyUnicode_FindMaxChar (
    PyObject *unicode,
    Py_ssize_t start,
    Py_ssize_t end);







Py_UCS4* PyUnicode_AsUCS4(
    PyObject *unicode,
    Py_UCS4* buffer,
    Py_ssize_t buflen,
    int copy_null);




Py_UCS4* PyUnicode_AsUCS4Copy(PyObject *unicode);







Py_UNICODE * PyUnicode_AsUnicode(
    PyObject *unicode
    );
# 781 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
Py_UNICODE * PyUnicode_AsUnicodeAndSize(
    PyObject *unicode,
    Py_ssize_t *size
    );




Py_ssize_t PyUnicode_GetLength(
    PyObject *unicode
);




Py_ssize_t PyUnicode_GetSize(
    PyObject *unicode
    );



Py_UCS4 PyUnicode_ReadChar(
    PyObject *unicode,
    Py_ssize_t index
    );






int PyUnicode_WriteChar(
    PyObject *unicode,
    Py_ssize_t index,
    Py_UCS4 character
    );



Py_UNICODE PyUnicode_GetMax(void);
# 839 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
int PyUnicode_Resize(
    PyObject **unicode,
    Py_ssize_t length
    );
# 861 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_FromEncodedObject(
    register PyObject *obj,
    const char *encoding,
    const char *errors
    );
# 880 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_FromObject(
    register PyObject *obj
    );

PyObject * PyUnicode_FromFormatV(
    const char *format,
    va_list vargs
    );
PyObject * PyUnicode_FromFormat(
    const char *format,
    ...
    );


typedef struct {
    PyObject *buffer;
    void *data;
    enum PyUnicode_Kind kind;
    Py_UCS4 maxchar;
    Py_ssize_t size;
    Py_ssize_t pos;


    Py_ssize_t min_length;
    unsigned char overallocate;


    unsigned char readonly;
} _PyUnicodeWriter ;






void
_PyUnicodeWriter_Init(_PyUnicodeWriter *writer, Py_ssize_t min_length);
# 932 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
int
_PyUnicodeWriter_PrepareInternal(_PyUnicodeWriter *writer,
                                 Py_ssize_t length, Py_UCS4 maxchar);

int
_PyUnicodeWriter_WriteStr(_PyUnicodeWriter *writer, PyObject *str);

PyObject *
_PyUnicodeWriter_Finish(_PyUnicodeWriter *writer);

void
_PyUnicodeWriter_Dealloc(_PyUnicodeWriter *writer);





int _PyUnicode_FormatAdvancedWriter(
    _PyUnicodeWriter *writer,
    PyObject *obj,
    PyObject *format_spec,
    Py_ssize_t start,
    Py_ssize_t end);


void PyUnicode_InternInPlace(PyObject **);
void PyUnicode_InternImmortal(PyObject **);
PyObject * PyUnicode_InternFromString(
    const char *u
    );

void _Py_ReleaseInternedUnicodeStrings(void);
# 979 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_FromWideChar(
    register const wchar_t *w,
    Py_ssize_t size
    );
# 996 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
Py_ssize_t PyUnicode_AsWideChar(
    PyObject *unicode,
    register wchar_t *w,
    Py_ssize_t size
    );
# 1010 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
wchar_t* PyUnicode_AsWideCharString(
    PyObject *unicode,
    Py_ssize_t *size
    );


void* _PyUnicode_AsKind(PyObject *s, unsigned int kind);
# 1030 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_FromOrdinal(int ordinal);
# 1041 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
int PyUnicode_ClearFreeList(void);
# 1084 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
char * PyUnicode_AsUTF8AndSize(
    PyObject *unicode,
    Py_ssize_t *size);
# 1111 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
char * PyUnicode_AsUTF8(PyObject *unicode);





const char* PyUnicode_GetDefaultEncoding(void);






PyObject* PyUnicode_Decode(
    const char *s,
    Py_ssize_t size,
    const char *encoding,
    const char *errors
    );




PyObject* PyUnicode_AsDecodedObject(
    PyObject *unicode,
    const char *encoding,
    const char *errors
    );




PyObject* PyUnicode_AsDecodedUnicode(
    PyObject *unicode,
    const char *encoding,
    const char *errors
    );





PyObject* PyUnicode_Encode(
    const Py_UNICODE *s,
    Py_ssize_t size,
    const char *encoding,
    const char *errors
    );





PyObject* PyUnicode_AsEncodedObject(
    PyObject *unicode,
    const char *encoding,
    const char *errors
    );




PyObject* PyUnicode_AsEncodedString(
    PyObject *unicode,
    const char *encoding,
    const char *errors
    );




PyObject* PyUnicode_AsEncodedUnicode(
    PyObject *unicode,
    const char *encoding,
    const char *errors
    );



PyObject* PyUnicode_BuildEncodingMap(
    PyObject* string
   );



PyObject* PyUnicode_DecodeUTF7(
    const char *string,
    Py_ssize_t length,
    const char *errors
    );

PyObject* PyUnicode_DecodeUTF7Stateful(
    const char *string,
    Py_ssize_t length,
    const char *errors,
    Py_ssize_t *consumed
    );


PyObject* PyUnicode_EncodeUTF7(
    const Py_UNICODE *data,
    Py_ssize_t length,
    int base64SetO,
    int base64WhiteSpace,
    const char *errors
    );
PyObject* _PyUnicode_EncodeUTF7(
    PyObject *unicode,
    int base64SetO,
    int base64WhiteSpace,
    const char *errors
    );




PyObject* PyUnicode_DecodeUTF8(
    const char *string,
    Py_ssize_t length,
    const char *errors
    );

PyObject* PyUnicode_DecodeUTF8Stateful(
    const char *string,
    Py_ssize_t length,
    const char *errors,
    Py_ssize_t *consumed
    );

PyObject* PyUnicode_AsUTF8String(
    PyObject *unicode
    );


PyObject* _PyUnicode_AsUTF8String(
    PyObject *unicode,
    const char *errors);

PyObject* PyUnicode_EncodeUTF8(
    const Py_UNICODE *data,
    Py_ssize_t length,
    const char *errors
    );
# 1281 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_DecodeUTF32(
    const char *string,
    Py_ssize_t length,
    const char *errors,
    int *byteorder


    );

PyObject* PyUnicode_DecodeUTF32Stateful(
    const char *string,
    Py_ssize_t length,
    const char *errors,
    int *byteorder,


    Py_ssize_t *consumed
    );




PyObject* PyUnicode_AsUTF32String(
    PyObject *unicode
    );
# 1324 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_EncodeUTF32(
    const Py_UNICODE *data,
    Py_ssize_t length,
    const char *errors,
    int byteorder
    );
PyObject* _PyUnicode_EncodeUTF32(
    PyObject *object,
    const char *errors,
    int byteorder
    );
# 1362 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_DecodeUTF16(
    const char *string,
    Py_ssize_t length,
    const char *errors,
    int *byteorder


    );

PyObject* PyUnicode_DecodeUTF16Stateful(
    const char *string,
    Py_ssize_t length,
    const char *errors,
    int *byteorder,


    Py_ssize_t *consumed
    );




PyObject* PyUnicode_AsUTF16String(
    PyObject *unicode
    );
# 1409 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_EncodeUTF16(
    const Py_UNICODE *data,
    Py_ssize_t length,
    const char *errors,
    int byteorder
    );
PyObject* _PyUnicode_EncodeUTF16(
    PyObject* unicode,
    const char *errors,
    int byteorder
    );




PyObject* PyUnicode_DecodeUnicodeEscape(
    const char *string,
    Py_ssize_t length,
    const char *errors
    );

PyObject* PyUnicode_AsUnicodeEscapeString(
    PyObject *unicode
    );


PyObject* PyUnicode_EncodeUnicodeEscape(
    const Py_UNICODE *data,
    Py_ssize_t length
    );




PyObject* PyUnicode_DecodeRawUnicodeEscape(
    const char *string,
    Py_ssize_t length,
    const char *errors
    );

PyObject* PyUnicode_AsRawUnicodeEscapeString(
    PyObject *unicode
    );


PyObject* PyUnicode_EncodeRawUnicodeEscape(
    const Py_UNICODE *data,
    Py_ssize_t length
    );







PyObject *_PyUnicode_DecodeUnicodeInternal(
    const char *string,
    Py_ssize_t length,
    const char *errors
    );
# 1478 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_DecodeLatin1(
    const char *string,
    Py_ssize_t length,
    const char *errors
    );

PyObject* PyUnicode_AsLatin1String(
    PyObject *unicode
    );


PyObject* _PyUnicode_AsLatin1String(
    PyObject* unicode,
    const char* errors);

PyObject* PyUnicode_EncodeLatin1(
    const Py_UNICODE *data,
    Py_ssize_t length,
    const char *errors
    );
# 1506 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_DecodeASCII(
    const char *string,
    Py_ssize_t length,
    const char *errors
    );

PyObject* PyUnicode_AsASCIIString(
    PyObject *unicode
    );


PyObject* _PyUnicode_AsASCIIString(
    PyObject* unicode,
    const char* errors);

PyObject* PyUnicode_EncodeASCII(
    const Py_UNICODE *data,
    Py_ssize_t length,
    const char *errors
    );
# 1550 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_DecodeCharmap(
    const char *string,
    Py_ssize_t length,
    PyObject *mapping,

    const char *errors
    );

PyObject* PyUnicode_AsCharmapString(
    PyObject *unicode,
    PyObject *mapping

    );


PyObject* PyUnicode_EncodeCharmap(
    const Py_UNICODE *data,
    Py_ssize_t length,
    PyObject *mapping,

    const char *errors
    );
PyObject* _PyUnicode_EncodeCharmap(
    PyObject *unicode,
    PyObject *mapping,

    const char *errors
    );
# 1594 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject * PyUnicode_TranslateCharmap(
    const Py_UNICODE *data,
    Py_ssize_t length,
    PyObject *table,
    const char *errors
    );
# 1672 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
int PyUnicode_EncodeDecimal(
    Py_UNICODE *s,
    Py_ssize_t length,
    char *output,
    const char *errors
    );
# 1687 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_TransformDecimalToASCII(
    Py_UNICODE *s,
    Py_ssize_t length
    );
# 1699 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* _PyUnicode_TransformDecimalAndSpaceToASCII(
    PyObject *unicode
    );
# 1714 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_DecodeLocaleAndSize(
    const char *str,
    Py_ssize_t len,
    const char *errors);




PyObject* PyUnicode_DecodeLocale(
    const char *str,
    const char *errors);






PyObject* PyUnicode_EncodeLocale(
    PyObject *unicode,
    const char *errors
    );






int PyUnicode_FSConverter(PyObject*, void*);




int PyUnicode_FSDecoder(PyObject*, void*);
# 1757 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_DecodeFSDefault(
    const char *s
    );
# 1768 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_DecodeFSDefaultAndSize(
    const char *s,
    Py_ssize_t size
    );
# 1780 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_EncodeFSDefault(
    PyObject *unicode
    );
# 1792 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_Concat(
    PyObject *left,
    PyObject *right
    );




void PyUnicode_Append(
    PyObject **pleft,
    PyObject *right
    );




void PyUnicode_AppendAndDel(
    PyObject **pleft,
    PyObject *right
    );
# 1824 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_Split(
    PyObject *s,
    PyObject *sep,
    Py_ssize_t maxsplit
    );






PyObject* PyUnicode_Splitlines(
    PyObject *s,
    int keepends
    );



PyObject* PyUnicode_Partition(
    PyObject *s,
    PyObject *sep
    );




PyObject* PyUnicode_RPartition(
    PyObject *s,
    PyObject *sep
    );
# 1868 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* PyUnicode_RSplit(
    PyObject *s,
    PyObject *sep,
    Py_ssize_t maxsplit
    );
# 1886 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject * PyUnicode_Translate(
    PyObject *str,
    PyObject *table,
    const char *errors
    );




PyObject* PyUnicode_Join(
    PyObject *separator,
    PyObject *seq
    );




Py_ssize_t PyUnicode_Tailmatch(
    PyObject *str,
    PyObject *substr,
    Py_ssize_t start,
    Py_ssize_t end,
    int direction
    );





Py_ssize_t PyUnicode_Find(
    PyObject *str,
    PyObject *substr,
    Py_ssize_t start,
    Py_ssize_t end,
    int direction
    );


Py_ssize_t PyUnicode_FindChar(
    PyObject *str,
    Py_UCS4 ch,
    Py_ssize_t start,
    Py_ssize_t end,
    int direction
    );



Py_ssize_t PyUnicode_Count(
    PyObject *str,
    PyObject *substr,
    Py_ssize_t start,
    Py_ssize_t end
    );




PyObject * PyUnicode_Replace(
    PyObject *str,
    PyObject *substr,
    PyObject *replstr,
    Py_ssize_t maxcount

    );




int PyUnicode_Compare(
    PyObject *left,
    PyObject *right
    );

int PyUnicode_CompareWithASCIIString(
    PyObject *left,
    const char *right
    );
# 1981 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject * PyUnicode_RichCompare(
    PyObject *left,
    PyObject *right,
    int op
    );




PyObject * PyUnicode_Format(
    PyObject *format,
    PyObject *args
    );







int PyUnicode_Contains(
    PyObject *container,
    PyObject *element
    );




int _PyUnicode_HasNULChars(PyObject *);




int PyUnicode_IsIdentifier(PyObject *s);



PyObject * _PyUnicode_XStrip(
    PyObject *self,
    int striptype,
    PyObject *sepobj
    );






Py_ssize_t _PyUnicode_InsertThousandsGrouping(
    PyObject *unicode,
    Py_ssize_t index,
    Py_ssize_t n_buffer,
    void *digits,
    Py_ssize_t n_digits,
    Py_ssize_t min_width,
    const char *grouping,
    PyObject *thousands_sep,
    Py_UCS4 *maxchar);






extern const unsigned char _Py_ascii_whitespace[];
# 2054 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
int _PyUnicode_IsLowercase(
    Py_UCS4 ch
    );

int _PyUnicode_IsUppercase(
    Py_UCS4 ch
    );

int _PyUnicode_IsTitlecase(
    Py_UCS4 ch
    );

int _PyUnicode_IsXidStart(
    Py_UCS4 ch
    );

int _PyUnicode_IsXidContinue(
    Py_UCS4 ch
    );

int _PyUnicode_IsWhitespace(
    const Py_UCS4 ch
    );

int _PyUnicode_IsLinebreak(
    const Py_UCS4 ch
    );

Py_UCS4 _PyUnicode_ToLowercase(
    Py_UCS4 ch
    );

Py_UCS4 _PyUnicode_ToUppercase(
    Py_UCS4 ch
    );

Py_UCS4 _PyUnicode_ToTitlecase(
    Py_UCS4 ch
    );

int _PyUnicode_ToLowerFull(
    Py_UCS4 ch,
    Py_UCS4 *res
    );

int _PyUnicode_ToTitleFull(
    Py_UCS4 ch,
    Py_UCS4 *res
    );

int _PyUnicode_ToUpperFull(
    Py_UCS4 ch,
    Py_UCS4 *res
    );

int _PyUnicode_ToFoldedFull(
    Py_UCS4 ch,
    Py_UCS4 *res
    );

int _PyUnicode_IsCaseIgnorable(
    Py_UCS4 ch
    );

int _PyUnicode_IsCased(
    Py_UCS4 ch
    );

int _PyUnicode_ToDecimalDigit(
    Py_UCS4 ch
    );

int _PyUnicode_ToDigit(
    Py_UCS4 ch
    );

double _PyUnicode_ToNumeric(
    Py_UCS4 ch
    );

int _PyUnicode_IsDecimalDigit(
    Py_UCS4 ch
    );

int _PyUnicode_IsDigit(
    Py_UCS4 ch
    );

int _PyUnicode_IsNumeric(
    Py_UCS4 ch
    );

int _PyUnicode_IsPrintable(
    Py_UCS4 ch
    );

int _PyUnicode_IsAlpha(
    Py_UCS4 ch
    );

size_t Py_UNICODE_strlen(
    const Py_UNICODE *u
    );

Py_UNICODE* Py_UNICODE_strcpy(
    Py_UNICODE *s1,
    const Py_UNICODE *s2);

Py_UNICODE* Py_UNICODE_strcat(
    Py_UNICODE *s1, const Py_UNICODE *s2);

Py_UNICODE* Py_UNICODE_strncpy(
    Py_UNICODE *s1,
    const Py_UNICODE *s2,
    size_t n);

int Py_UNICODE_strcmp(
    const Py_UNICODE *s1,
    const Py_UNICODE *s2
    );

int Py_UNICODE_strncmp(
    const Py_UNICODE *s1,
    const Py_UNICODE *s2,
    size_t n
    );

Py_UNICODE* Py_UNICODE_strchr(
    const Py_UNICODE *s,
    Py_UNICODE c
    );

Py_UNICODE* Py_UNICODE_strrchr(
    const Py_UNICODE *s,
    Py_UNICODE c
    );





Py_UNICODE* PyUnicode_AsUnicodeCopy(
    PyObject *unicode
    );
# 2207 "/Users/parrt/tmp/Python-3.3.1/Include/unicodeobject.h"
PyObject* _PyUnicode_FromId(_Py_Identifier*);

void _PyUnicode_ClearStaticStrings(void);
# 77 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/longobject.h" 1
# 10 "/Users/parrt/tmp/Python-3.3.1/Include/longobject.h"
typedef struct _longobject PyLongObject;

extern PyTypeObject PyLong_Type;





PyObject * PyLong_FromLong(long);
PyObject * PyLong_FromUnsignedLong(unsigned long);
PyObject * PyLong_FromSize_t(size_t);
PyObject * PyLong_FromSsize_t(Py_ssize_t);
PyObject * PyLong_FromDouble(double);
long PyLong_AsLong(PyObject *);
long PyLong_AsLongAndOverflow(PyObject *, int *);
Py_ssize_t PyLong_AsSsize_t(PyObject *);
size_t PyLong_AsSize_t(PyObject *);
unsigned long PyLong_AsUnsignedLong(PyObject *);
unsigned long PyLong_AsUnsignedLongMask(PyObject *);

int _PyLong_AsInt(PyObject *);

PyObject * PyLong_GetInfo(void);
# 57 "/Users/parrt/tmp/Python-3.3.1/Include/longobject.h"
extern unsigned char _PyLong_DigitValue[256];
# 67 "/Users/parrt/tmp/Python-3.3.1/Include/longobject.h"
double _PyLong_Frexp(PyLongObject *a, Py_ssize_t *e);


double PyLong_AsDouble(PyObject *);
PyObject * PyLong_FromVoidPtr(void *);
void * PyLong_AsVoidPtr(PyObject *);


PyObject * PyLong_FromLongLong(long long);
PyObject * PyLong_FromUnsignedLongLong(unsigned long long);
long long PyLong_AsLongLong(PyObject *);
unsigned long long PyLong_AsUnsignedLongLong(PyObject *);
unsigned long long PyLong_AsUnsignedLongLongMask(PyObject *);
long long PyLong_AsLongLongAndOverflow(PyObject *, int *);


PyObject * PyLong_FromString(char *, char **, int);

PyObject * PyLong_FromUnicode(Py_UNICODE*, Py_ssize_t, int);
PyObject * PyLong_FromUnicodeObject(PyObject *u, int base);







int _PyLong_Sign(PyObject *v);
# 104 "/Users/parrt/tmp/Python-3.3.1/Include/longobject.h"
size_t _PyLong_NumBits(PyObject *v);







PyObject * _PyLong_DivmodNear(PyObject *, PyObject *);
# 127 "/Users/parrt/tmp/Python-3.3.1/Include/longobject.h"
PyObject * _PyLong_FromByteArray(
    const unsigned char* bytes, size_t n,
    int little_endian, int is_signed);
# 150 "/Users/parrt/tmp/Python-3.3.1/Include/longobject.h"
int _PyLong_AsByteArray(PyLongObject* v,
    unsigned char* bytes, size_t n,
    int little_endian, int is_signed);




PyObject * _PyLong_Format(PyObject *obj, int base);

int _PyLong_FormatWriter(
    _PyUnicodeWriter *writer,
    PyObject *obj,
    int base,
    int alternate);



int _PyLong_FormatAdvancedWriter(
    _PyUnicodeWriter *writer,
    PyObject *obj,
    PyObject *format_spec,
    Py_ssize_t start,
    Py_ssize_t end);





unsigned long PyOS_strtoul(char *, char **, int);
long PyOS_strtol(char *, char **, int);
# 78 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/longintrepr.h" 1
# 49 "/Users/parrt/tmp/Python-3.3.1/Include/longintrepr.h"
typedef uint32_t digit;
typedef int32_t sdigit;
typedef uint64_t twodigits;
typedef int64_t stwodigits;
# 89 "/Users/parrt/tmp/Python-3.3.1/Include/longintrepr.h"
struct _longobject {
 PyVarObject ob_base;
 digit ob_digit[1];
};

PyLongObject * _PyLong_New(Py_ssize_t);


PyObject * _PyLong_Copy(PyLongObject *src);
# 79 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/boolobject.h" 1
# 10 "/Users/parrt/tmp/Python-3.3.1/Include/boolobject.h"
extern PyTypeObject PyBool_Type;







extern struct _longobject _Py_FalseStruct, _Py_TrueStruct;
# 29 "/Users/parrt/tmp/Python-3.3.1/Include/boolobject.h"
PyObject * PyBool_FromLong(long);
# 80 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/floatobject.h" 1
# 15 "/Users/parrt/tmp/Python-3.3.1/Include/floatobject.h"
typedef struct {
    PyObject ob_base;
    double ob_fval;
} PyFloatObject;


extern PyTypeObject PyFloat_Type;
# 37 "/Users/parrt/tmp/Python-3.3.1/Include/floatobject.h"
double PyFloat_GetMax(void);
double PyFloat_GetMin(void);
PyObject * PyFloat_GetInfo(void);


PyObject * PyFloat_FromString(PyObject*);


PyObject * PyFloat_FromDouble(double);



double PyFloat_AsDouble(PyObject *);
# 87 "/Users/parrt/tmp/Python-3.3.1/Include/floatobject.h"
int _PyFloat_Pack4(double x, unsigned char *p, int le);
int _PyFloat_Pack8(double x, unsigned char *p, int le);




int _PyFloat_Repr(double x, char *p, size_t len);


int _PyFloat_Digits(char *buf, double v, int *signum);
void _PyFloat_DigitsInit(void);
# 107 "/Users/parrt/tmp/Python-3.3.1/Include/floatobject.h"
double _PyFloat_Unpack4(const unsigned char *p, int le);
double _PyFloat_Unpack8(const unsigned char *p, int le);


int PyFloat_ClearFreeList(void);

void _PyFloat_DebugMallocStats(FILE* out);



int _PyFloat_FormatAdvancedWriter(
    _PyUnicodeWriter *writer,
    PyObject *obj,
    PyObject *format_spec,
    Py_ssize_t start,
    Py_ssize_t end);
# 81 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/complexobject.h" 1
# 10 "/Users/parrt/tmp/Python-3.3.1/Include/complexobject.h"
typedef struct {
    double real;
    double imag;
} Py_complex;
# 25 "/Users/parrt/tmp/Python-3.3.1/Include/complexobject.h"
Py_complex _Py_c_sum(Py_complex, Py_complex);
Py_complex _Py_c_diff(Py_complex, Py_complex);
Py_complex _Py_c_neg(Py_complex);
Py_complex _Py_c_prod(Py_complex, Py_complex);
Py_complex _Py_c_quot(Py_complex, Py_complex);
Py_complex _Py_c_pow(Py_complex, Py_complex);
double _Py_c_abs(Py_complex);
# 41 "/Users/parrt/tmp/Python-3.3.1/Include/complexobject.h"
typedef struct {
    PyObject ob_base;
    Py_complex cval;
} PyComplexObject;


extern PyTypeObject PyComplex_Type;





PyObject * PyComplex_FromCComplex(Py_complex);

PyObject * PyComplex_FromDoubles(double real, double imag);

double PyComplex_RealAsDouble(PyObject *op);
double PyComplex_ImagAsDouble(PyObject *op);

Py_complex PyComplex_AsCComplex(PyObject *op);





int _PyComplex_FormatAdvancedWriter(
    _PyUnicodeWriter *writer,
    PyObject *obj,
    PyObject *format_spec,
    Py_ssize_t start,
    Py_ssize_t end);
# 82 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/rangeobject.h" 1
# 18 "/Users/parrt/tmp/Python-3.3.1/Include/rangeobject.h"
extern PyTypeObject PyRange_Type;
extern PyTypeObject PyRangeIter_Type;
extern PyTypeObject PyLongRangeIter_Type;
# 83 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/memoryobject.h" 1
# 10 "/Users/parrt/tmp/Python-3.3.1/Include/memoryobject.h"
extern PyTypeObject _PyManagedBuffer_Type;

extern PyTypeObject PyMemoryView_Type;
# 23 "/Users/parrt/tmp/Python-3.3.1/Include/memoryobject.h"
PyObject * PyMemoryView_FromObject(PyObject *base);
PyObject * PyMemoryView_FromMemory(char *mem, Py_ssize_t size,
                                               int flags);

PyObject * PyMemoryView_FromBuffer(Py_buffer *info);

PyObject * PyMemoryView_GetContiguous(PyObject *base,
                                                  int buffertype,
                                                  char order);
# 40 "/Users/parrt/tmp/Python-3.3.1/Include/memoryobject.h"
typedef struct {
    PyObject ob_base;
    int flags;
    Py_ssize_t exports;
    Py_buffer master;
} _PyManagedBufferObject;
# 58 "/Users/parrt/tmp/Python-3.3.1/Include/memoryobject.h"
typedef struct {
    PyVarObject ob_base;
    _PyManagedBufferObject *mbuf;
    Py_hash_t hash;
    int flags;
    Py_ssize_t exports;
    Py_buffer view;
    char format[3];
    PyObject *weakreflist;
    Py_ssize_t ob_array[1];
} PyMemoryViewObject;
# 84 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/tupleobject.h" 1
# 25 "/Users/parrt/tmp/Python-3.3.1/Include/tupleobject.h"
typedef struct {
    PyVarObject ob_base;
    PyObject *ob_item[1];





} PyTupleObject;


extern PyTypeObject PyTuple_Type;
extern PyTypeObject PyTupleIter_Type;





PyObject * PyTuple_New(Py_ssize_t size);
Py_ssize_t PyTuple_Size(PyObject *);
PyObject * PyTuple_GetItem(PyObject *, Py_ssize_t);
int PyTuple_SetItem(PyObject *, Py_ssize_t, PyObject *);
PyObject * PyTuple_GetSlice(PyObject *, Py_ssize_t, Py_ssize_t);

int _PyTuple_Resize(PyObject **, Py_ssize_t);

PyObject * PyTuple_Pack(Py_ssize_t, ...);

void _PyTuple_MaybeUntrack(PyObject *);
# 65 "/Users/parrt/tmp/Python-3.3.1/Include/tupleobject.h"
int PyTuple_ClearFreeList(void);

void _PyTuple_DebugMallocStats(FILE *out);
# 85 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/listobject.h" 1
# 23 "/Users/parrt/tmp/Python-3.3.1/Include/listobject.h"
typedef struct {
    PyVarObject ob_base;

    PyObject **ob_item;
# 39 "/Users/parrt/tmp/Python-3.3.1/Include/listobject.h"
    Py_ssize_t allocated;
} PyListObject;


extern PyTypeObject PyList_Type;
extern PyTypeObject PyListIter_Type;
extern PyTypeObject PyListRevIter_Type;
extern PyTypeObject PySortWrapper_Type;





PyObject * PyList_New(Py_ssize_t size);
Py_ssize_t PyList_Size(PyObject *);
PyObject * PyList_GetItem(PyObject *, Py_ssize_t);
int PyList_SetItem(PyObject *, Py_ssize_t, PyObject *);
int PyList_Insert(PyObject *, Py_ssize_t, PyObject *);
int PyList_Append(PyObject *, PyObject *);
PyObject * PyList_GetSlice(PyObject *, Py_ssize_t, Py_ssize_t);
int PyList_SetSlice(PyObject *, Py_ssize_t, Py_ssize_t, PyObject *);
int PyList_Sort(PyObject *);
int PyList_Reverse(PyObject *);
PyObject * PyList_AsTuple(PyObject *);

PyObject * _PyList_Extend(PyListObject *, PyObject *);

int PyList_ClearFreeList(void);
void _PyList_DebugMallocStats(FILE *out);
# 86 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/dictobject.h" 1
# 18 "/Users/parrt/tmp/Python-3.3.1/Include/dictobject.h"
typedef struct _dictkeysobject PyDictKeysObject;




typedef struct {
    PyObject ob_base;
    Py_ssize_t ma_used;
    PyDictKeysObject *ma_keys;
    PyObject **ma_values;
} PyDictObject;



extern PyTypeObject PyDict_Type;
extern PyTypeObject PyDictIterKey_Type;
extern PyTypeObject PyDictIterValue_Type;
extern PyTypeObject PyDictIterItem_Type;
extern PyTypeObject PyDictKeys_Type;
extern PyTypeObject PyDictItems_Type;
extern PyTypeObject PyDictValues_Type;
# 51 "/Users/parrt/tmp/Python-3.3.1/Include/dictobject.h"
PyObject * PyDict_New(void);
PyObject * PyDict_GetItem(PyObject *mp, PyObject *key);
PyObject * PyDict_GetItemWithError(PyObject *mp, PyObject *key);
PyObject * _PyDict_GetItemIdWithError(PyObject *dp,
                                                  struct _Py_Identifier *key);
int PyDict_SetItem(PyObject *mp, PyObject *key, PyObject *item);
int PyDict_DelItem(PyObject *mp, PyObject *key);
void PyDict_Clear(PyObject *mp);
int PyDict_Next(
    PyObject *mp, Py_ssize_t *pos, PyObject **key, PyObject **value);

PyDictKeysObject *_PyDict_NewKeysForClass(void);
PyObject * PyObject_GenericGetDict(PyObject *, void *);
int _PyDict_Next(
    PyObject *mp, Py_ssize_t *pos, PyObject **key, PyObject **value, Py_hash_t *hash);

PyObject * PyDict_Keys(PyObject *mp);
PyObject * PyDict_Values(PyObject *mp);
PyObject * PyDict_Items(PyObject *mp);
Py_ssize_t PyDict_Size(PyObject *mp);
PyObject * PyDict_Copy(PyObject *mp);
int PyDict_Contains(PyObject *mp, PyObject *key);

int _PyDict_Contains(PyObject *mp, PyObject *key, Py_hash_t hash);
PyObject * _PyDict_NewPresized(Py_ssize_t minused);
void _PyDict_MaybeUntrack(PyObject *mp);
int _PyDict_HasOnlyStringKeys(PyObject *mp);
Py_ssize_t _PyDict_KeysSize(PyDictKeysObject *keys);


int PyDict_ClearFreeList(void);



int PyDict_Update(PyObject *mp, PyObject *other);






int PyDict_Merge(PyObject *mp,
                                   PyObject *other,
                                   int override);






int PyDict_MergeFromSeq2(PyObject *d,
                                           PyObject *seq2,
                                           int override);

PyObject * PyDict_GetItemString(PyObject *dp, const char *key);
PyObject * _PyDict_GetItemId(PyObject *dp, struct _Py_Identifier *key);
int PyDict_SetItemString(PyObject *dp, const char *key, PyObject *item);
int _PyDict_SetItemId(PyObject *dp, struct _Py_Identifier *key, PyObject *item);
int PyDict_DelItemString(PyObject *dp, const char *key);


int _PyObjectDict_SetItem(PyTypeObject *tp, PyObject **dictptr, PyObject *name, PyObject *value);
PyObject *_PyDict_LoadGlobal(PyDictObject *, PyDictObject *, PyObject *);
void _PyDict_DebugMallocStats(FILE *out);
# 87 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/enumobject.h" 1
# 10 "/Users/parrt/tmp/Python-3.3.1/Include/enumobject.h"
extern PyTypeObject PyEnum_Type;
extern PyTypeObject PyReversed_Type;
# 88 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/setobject.h" 1
# 24 "/Users/parrt/tmp/Python-3.3.1/Include/setobject.h"
typedef struct {

    Py_hash_t hash;
    PyObject *key;
} setentry;






typedef struct _setobject PySetObject;
struct _setobject {
    PyObject ob_base;

    Py_ssize_t fill;
    Py_ssize_t used;





    Py_ssize_t mask;





    setentry *table;
    setentry *(*lookup)(PySetObject *so, PyObject *key, Py_hash_t hash);
    setentry smalltable[8];

    Py_hash_t hash;
    PyObject *weakreflist;
};


extern PyTypeObject PySet_Type;
extern PyTypeObject PyFrozenSet_Type;
extern PyTypeObject PySetIter_Type;
# 86 "/Users/parrt/tmp/Python-3.3.1/Include/setobject.h"
PyObject * PySet_New(PyObject *);
PyObject * PyFrozenSet_New(PyObject *);
Py_ssize_t PySet_Size(PyObject *anyset);



int PySet_Clear(PyObject *set);
int PySet_Contains(PyObject *anyset, PyObject *key);
int PySet_Discard(PyObject *set, PyObject *key);
int PySet_Add(PyObject *set, PyObject *key);

int _PySet_NextEntry(PyObject *set, Py_ssize_t *pos, PyObject **key, Py_hash_t *hash);

PyObject * PySet_Pop(PyObject *set);

int _PySet_Update(PyObject *set, PyObject *iterable);

int PySet_ClearFreeList(void);
void _PySet_DebugMallocStats(FILE *out);
# 89 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/methodobject.h" 1
# 14 "/Users/parrt/tmp/Python-3.3.1/Include/methodobject.h"
extern PyTypeObject PyCFunction_Type;



typedef PyObject *(*PyCFunction)(PyObject *, PyObject *);
typedef PyObject *(*PyCFunctionWithKeywords)(PyObject *, PyObject *,
                                             PyObject *);
typedef PyObject *(*PyNoArgsFunction)(PyObject *);

PyCFunction PyCFunction_GetFunction(PyObject *);
PyObject * PyCFunction_GetSelf(PyObject *);
int PyCFunction_GetFlags(PyObject *);
# 38 "/Users/parrt/tmp/Python-3.3.1/Include/methodobject.h"
PyObject * PyCFunction_Call(PyObject *, PyObject *, PyObject *);

struct PyMethodDef {
    const char *ml_name;
    PyCFunction ml_meth;
    int ml_flags;

    const char *ml_doc;
};
typedef struct PyMethodDef PyMethodDef;


PyObject * PyCFunction_NewEx(PyMethodDef *, PyObject *,
                                         PyObject *);
# 75 "/Users/parrt/tmp/Python-3.3.1/Include/methodobject.h"
typedef struct {
    PyObject ob_base;
    PyMethodDef *m_ml;
    PyObject *m_self;
    PyObject *m_module;
} PyCFunctionObject;


int PyCFunction_ClearFreeList(void);


void _PyCFunction_DebugMallocStats(FILE *out);
void _PyMethod_DebugMallocStats(FILE *out);
# 90 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/moduleobject.h" 1
# 10 "/Users/parrt/tmp/Python-3.3.1/Include/moduleobject.h"
extern PyTypeObject PyModule_Type;




PyObject * PyModule_NewObject(
    PyObject *name
    );
PyObject * PyModule_New(
    const char *name
    );
PyObject * PyModule_GetDict(PyObject *);
PyObject * PyModule_GetNameObject(PyObject *);
const char * PyModule_GetName(PyObject *);
const char * PyModule_GetFilename(PyObject *);
PyObject * PyModule_GetFilenameObject(PyObject *);

void _PyModule_Clear(PyObject *);

struct PyModuleDef* PyModule_GetDef(PyObject*);
void* PyModule_GetState(PyObject*);

typedef struct PyModuleDef_Base {
  PyObject ob_base;
  PyObject* (*m_init)(void);
  Py_ssize_t m_index;
  PyObject* m_copy;
} PyModuleDef_Base;
# 46 "/Users/parrt/tmp/Python-3.3.1/Include/moduleobject.h"
typedef struct PyModuleDef{
  PyModuleDef_Base m_base;
  const char* m_name;
  const char* m_doc;
  Py_ssize_t m_size;
  PyMethodDef *m_methods;
  inquiry m_reload;
  traverseproc m_traverse;
  inquiry m_clear;
  freefunc m_free;
}PyModuleDef;
# 91 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/funcobject.h" 1
# 21 "/Users/parrt/tmp/Python-3.3.1/Include/funcobject.h"
typedef struct {
    PyObject ob_base;
    PyObject *func_code;
    PyObject *func_globals;
    PyObject *func_defaults;
    PyObject *func_kwdefaults;
    PyObject *func_closure;
    PyObject *func_doc;
    PyObject *func_name;
    PyObject *func_dict;
    PyObject *func_weakreflist;
    PyObject *func_module;
    PyObject *func_annotations;
    PyObject *func_qualname;






} PyFunctionObject;

extern PyTypeObject PyFunction_Type;



PyObject * PyFunction_New(PyObject *, PyObject *);
PyObject * PyFunction_NewWithQualName(PyObject *, PyObject *, PyObject *);
PyObject * PyFunction_GetCode(PyObject *);
PyObject * PyFunction_GetGlobals(PyObject *);
PyObject * PyFunction_GetModule(PyObject *);
PyObject * PyFunction_GetDefaults(PyObject *);
int PyFunction_SetDefaults(PyObject *, PyObject *);
PyObject * PyFunction_GetKwDefaults(PyObject *);
int PyFunction_SetKwDefaults(PyObject *, PyObject *);
PyObject * PyFunction_GetClosure(PyObject *);
int PyFunction_SetClosure(PyObject *, PyObject *);
PyObject * PyFunction_GetAnnotations(PyObject *);
int PyFunction_SetAnnotations(PyObject *, PyObject *);
# 79 "/Users/parrt/tmp/Python-3.3.1/Include/funcobject.h"
extern PyTypeObject PyClassMethod_Type;
extern PyTypeObject PyStaticMethod_Type;

PyObject * PyClassMethod_New(PyObject *);
PyObject * PyStaticMethod_New(PyObject *);
# 92 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/classobject.h" 1
# 12 "/Users/parrt/tmp/Python-3.3.1/Include/classobject.h"
typedef struct {
    PyObject ob_base;
    PyObject *im_func;
    PyObject *im_self;
    PyObject *im_weakreflist;
} PyMethodObject;

extern PyTypeObject PyMethod_Type;



PyObject * PyMethod_New(PyObject *, PyObject *);

PyObject * PyMethod_Function(PyObject *);
PyObject * PyMethod_Self(PyObject *);
# 35 "/Users/parrt/tmp/Python-3.3.1/Include/classobject.h"
int PyMethod_ClearFreeList(void);

typedef struct {
 PyObject ob_base;
 PyObject *func;
} PyInstanceMethodObject;

extern PyTypeObject PyInstanceMethod_Type;



PyObject * PyInstanceMethod_New(PyObject *);
PyObject * PyInstanceMethod_Function(PyObject *);
# 93 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/fileobject.h" 1
# 11 "/Users/parrt/tmp/Python-3.3.1/Include/fileobject.h"
PyObject * PyFile_FromFd(int, char *, char *, int, char *, char *,
         char *, int);
PyObject * PyFile_GetLine(PyObject *, int);
int PyFile_WriteObject(PyObject *, PyObject *, int);
int PyFile_WriteString(const char *, PyObject *);
int PyObject_AsFileDescriptor(PyObject *);

char * Py_UniversalNewlineFgets(char *, int, FILE*, PyObject *);





extern const char * Py_FileSystemDefaultEncoding;
extern int Py_HasFileSystemDefaultEncoding;






PyObject * PyFile_NewStdPrinter(int);
extern PyTypeObject PyStdPrinter_Type;
# 94 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/pycapsule.h" 1
# 21 "/Users/parrt/tmp/Python-3.3.1/Include/pycapsule.h"
extern PyTypeObject PyCapsule_Type;

typedef void (*PyCapsule_Destructor)(PyObject *);




PyObject * PyCapsule_New(
    void *pointer,
    const char *name,
    PyCapsule_Destructor destructor);

void * PyCapsule_GetPointer(PyObject *capsule, const char *name);

PyCapsule_Destructor PyCapsule_GetDestructor(PyObject *capsule);

const char * PyCapsule_GetName(PyObject *capsule);

void * PyCapsule_GetContext(PyObject *capsule);

int PyCapsule_IsValid(PyObject *capsule, const char *name);

int PyCapsule_SetPointer(PyObject *capsule, void *pointer);

int PyCapsule_SetDestructor(PyObject *capsule, PyCapsule_Destructor destructor);

int PyCapsule_SetName(PyObject *capsule, const char *name);

int PyCapsule_SetContext(PyObject *capsule, void *context);

void * PyCapsule_Import(
    const char *name,
    int no_block);
# 95 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/traceback.h" 1







# 1 "/Users/parrt/tmp/Python-3.3.1/Include/pystate.h" 1
# 13 "/Users/parrt/tmp/Python-3.3.1/Include/pystate.h"
struct _ts;
struct _is;




typedef struct _is {

    struct _is *next;
    struct _ts *tstate_head;

    PyObject *modules;
    PyObject *modules_by_index;
    PyObject *sysdict;
    PyObject *builtins;
    PyObject *importlib;

    PyObject *codec_search_path;
    PyObject *codec_search_cache;
    PyObject *codec_error_registry;
    int codecs_initialized;
    int fscodec_initialized;



    int dlopenflags;





} PyInterpreterState;





struct _frame;



typedef int (*Py_tracefunc)(PyObject *, struct _frame *, int, PyObject *);
# 69 "/Users/parrt/tmp/Python-3.3.1/Include/pystate.h"
typedef struct _ts {


    struct _ts *next;
    PyInterpreterState *interp;

    struct _frame *frame;
    int recursion_depth;
    char overflowed;

    char recursion_critical;




    int tracing;
    int use_tracing;

    Py_tracefunc c_profilefunc;
    Py_tracefunc c_tracefunc;
    PyObject *c_profileobj;
    PyObject *c_traceobj;

    PyObject *curexc_type;
    PyObject *curexc_value;
    PyObject *curexc_traceback;

    PyObject *exc_type;
    PyObject *exc_value;
    PyObject *exc_traceback;

    PyObject *dict;
# 110 "/Users/parrt/tmp/Python-3.3.1/Include/pystate.h"
    int tick_counter;

    int gilstate_counter;

    PyObject *async_exc;
    long thread_id;

    int trash_delete_nesting;
    PyObject *trash_delete_later;



} PyThreadState;



PyInterpreterState * PyInterpreterState_New(void);
void PyInterpreterState_Clear(PyInterpreterState *);
void PyInterpreterState_Delete(PyInterpreterState *);
int _PyState_AddModule(PyObject*, struct PyModuleDef*);


int PyState_AddModule(PyObject*, struct PyModuleDef*);
int PyState_RemoveModule(struct PyModuleDef*);

PyObject* PyState_FindModule(struct PyModuleDef*);

PyThreadState * PyThreadState_New(PyInterpreterState *);
PyThreadState * _PyThreadState_Prealloc(PyInterpreterState *);
void _PyThreadState_Init(PyThreadState *);
void PyThreadState_Clear(PyThreadState *);
void PyThreadState_Delete(PyThreadState *);

void PyThreadState_DeleteCurrent(void);
void _PyGILState_Reinit(void);


PyThreadState * PyThreadState_Get(void);
PyThreadState * PyThreadState_Swap(PyThreadState *);
PyObject * PyThreadState_GetDict(void);
int PyThreadState_SetAsyncExc(long, PyObject *);







extern _Py_atomic_address _PyThreadState_Current;
# 168 "/Users/parrt/tmp/Python-3.3.1/Include/pystate.h"
typedef
    enum {PyGILState_LOCKED, PyGILState_UNLOCKED}
        PyGILState_STATE;
# 195 "/Users/parrt/tmp/Python-3.3.1/Include/pystate.h"
PyGILState_STATE PyGILState_Ensure(void);
# 205 "/Users/parrt/tmp/Python-3.3.1/Include/pystate.h"
void PyGILState_Release(PyGILState_STATE);







PyThreadState * PyGILState_GetThisThreadState(void);







PyObject * _PyThread_CurrentFrames(void);





PyInterpreterState * PyInterpreterState_Head(void);
PyInterpreterState * PyInterpreterState_Next(PyInterpreterState *);
PyThreadState * PyInterpreterState_ThreadHead(PyInterpreterState *);
PyThreadState * PyThreadState_Next(PyThreadState *);

typedef struct _frame *(*PyThreadFrameGetter)(PyThreadState *self_);




extern PyThreadFrameGetter _PyThreadState_GetFrame;
# 9 "/Users/parrt/tmp/Python-3.3.1/Include/traceback.h" 2

struct _frame;



typedef struct _traceback {
    PyObject ob_base;
    struct _traceback *tb_next;
    struct _frame *tb_frame;
    int tb_lasti;
    int tb_lineno;
} PyTracebackObject;


int PyTraceBack_Here(struct _frame *);
int PyTraceBack_Print(PyObject *, PyObject *);

int _Py_DisplaySourceLine(PyObject *, PyObject *, int, int);



extern PyTypeObject PyTraceBack_Type;
# 50 "/Users/parrt/tmp/Python-3.3.1/Include/traceback.h"
extern void _Py_DumpTraceback(
    int fd,
    PyThreadState *tstate);
# 64 "/Users/parrt/tmp/Python-3.3.1/Include/traceback.h"
extern const char* _Py_DumpTracebackThreads(
    int fd, PyInterpreterState *interp,
    PyThreadState *current_thread);
# 96 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/sliceobject.h" 1
# 9 "/Users/parrt/tmp/Python-3.3.1/Include/sliceobject.h"
extern PyObject _Py_EllipsisObject;
# 22 "/Users/parrt/tmp/Python-3.3.1/Include/sliceobject.h"
typedef struct {
    PyObject ob_base;
    PyObject *start, *stop, *step;
} PySliceObject;


extern PyTypeObject PySlice_Type;
extern PyTypeObject PyEllipsis_Type;



PyObject * PySlice_New(PyObject* start, PyObject* stop,
                                  PyObject* step);

PyObject * _PySlice_FromIndices(Py_ssize_t start, Py_ssize_t stop);

int PySlice_GetIndices(PyObject *r, Py_ssize_t length,
                                  Py_ssize_t *start, Py_ssize_t *stop, Py_ssize_t *step);
int PySlice_GetIndicesEx(PyObject *r, Py_ssize_t length,
        Py_ssize_t *start, Py_ssize_t *stop,
        Py_ssize_t *step, Py_ssize_t *slicelength);
# 97 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/cellobject.h" 1
# 9 "/Users/parrt/tmp/Python-3.3.1/Include/cellobject.h"
typedef struct {
 PyObject ob_base;
 PyObject *ob_ref;
} PyCellObject;

extern PyTypeObject PyCell_Type;



PyObject * PyCell_New(PyObject *);
PyObject * PyCell_Get(PyObject *);
int PyCell_Set(PyObject *, PyObject *);
# 98 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/iterobject.h" 1







extern PyTypeObject PySeqIter_Type;
extern PyTypeObject PyCallIter_Type;
extern PyTypeObject PyCmpWrapper_Type;



PyObject * PySeqIter_New(PyObject *);




PyObject * PyCallIter_New(PyObject *, PyObject *);
# 99 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/genobject.h" 1
# 11 "/Users/parrt/tmp/Python-3.3.1/Include/genobject.h"
struct _frame;

typedef struct {
    PyObject ob_base;



    struct _frame *gi_frame;


    char gi_running;


    PyObject *gi_code;


    PyObject *gi_weakreflist;
} PyGenObject;

extern PyTypeObject PyGen_Type;




PyObject * PyGen_New(struct _frame *);
int PyGen_NeedsFinalizing(PyGenObject *);
int _PyGen_FetchStopIterationValue(PyObject **);
PyObject *_PyGen_Send(PyGenObject *, PyObject *);
# 100 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/descrobject.h" 1







typedef PyObject *(*getter)(PyObject *, void *);
typedef int (*setter)(PyObject *, PyObject *, void *);

typedef struct PyGetSetDef {
    char *name;
    getter get;
    setter set;
    char *doc;
    void *closure;
} PyGetSetDef;


typedef PyObject *(*wrapperfunc)(PyObject *self, PyObject *args,
                                 void *wrapped);

typedef PyObject *(*wrapperfunc_kwds)(PyObject *self, PyObject *args,
                                      void *wrapped, PyObject *kwds);

struct wrapperbase {
    char *name;
    int offset;
    void *function;
    wrapperfunc wrapper;
    char *doc;
    int flags;
    PyObject *name_strobj;
};






typedef struct {
    PyObject ob_base;
    PyTypeObject *d_type;
    PyObject *d_name;
    PyObject *d_qualname;
} PyDescrObject;






typedef struct {
    PyDescrObject d_common;
    PyMethodDef *d_method;
} PyMethodDescrObject;

typedef struct {
    PyDescrObject d_common;
    struct PyMemberDef *d_member;
} PyMemberDescrObject;

typedef struct {
    PyDescrObject d_common;
    PyGetSetDef *d_getset;
} PyGetSetDescrObject;

typedef struct {
    PyDescrObject d_common;
    struct wrapperbase *d_base;
    void *d_wrapped;
} PyWrapperDescrObject;


extern PyTypeObject PyClassMethodDescr_Type;
extern PyTypeObject PyGetSetDescr_Type;
extern PyTypeObject PyMemberDescr_Type;
extern PyTypeObject PyMethodDescr_Type;
extern PyTypeObject PyWrapperDescr_Type;
extern PyTypeObject PyDictProxy_Type;
extern PyTypeObject _PyMethodWrapper_Type;

PyObject * PyDescr_NewMethod(PyTypeObject *, PyMethodDef *);
PyObject * PyDescr_NewClassMethod(PyTypeObject *, PyMethodDef *);
struct PyMemberDef;
PyObject * PyDescr_NewMember(PyTypeObject *,
                                               struct PyMemberDef *);
PyObject * PyDescr_NewGetSet(PyTypeObject *,
                                               struct PyGetSetDef *);

PyObject * PyDescr_NewWrapper(PyTypeObject *,
                                                struct wrapperbase *, void *);



PyObject * PyDictProxy_New(PyObject *);
PyObject * PyWrapper_New(PyObject *, PyObject *);


extern PyTypeObject PyProperty_Type;
# 101 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/warnings.h" 1







PyObject* _PyWarnings_Init(void);


int PyErr_WarnEx(
    PyObject *category,
    const char *message,
    Py_ssize_t stack_level);
int PyErr_WarnFormat(
    PyObject *category,
    Py_ssize_t stack_level,
    const char *format,
    ...);
int PyErr_WarnExplicit(
    PyObject *category,
    const char *message,
    const char *filename,
    int lineno,
    const char *module,
    PyObject *registry);
# 102 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/weakrefobject.h" 1
# 10 "/Users/parrt/tmp/Python-3.3.1/Include/weakrefobject.h"
typedef struct _PyWeakReference PyWeakReference;





struct _PyWeakReference {
    PyObject ob_base;





    PyObject *wr_object;


    PyObject *wr_callback;




    Py_hash_t hash;






    PyWeakReference *wr_prev;
    PyWeakReference *wr_next;
};


extern PyTypeObject _PyWeakref_RefType;
extern PyTypeObject _PyWeakref_ProxyType;
extern PyTypeObject _PyWeakref_CallableProxyType;
# 61 "/Users/parrt/tmp/Python-3.3.1/Include/weakrefobject.h"
PyObject * PyWeakref_NewRef(PyObject *ob,
                                              PyObject *callback);
PyObject * PyWeakref_NewProxy(PyObject *ob,
                                                PyObject *callback);
PyObject * PyWeakref_GetObject(PyObject *ref);


Py_ssize_t _PyWeakref_GetWeakrefCount(PyWeakReference *head);

void _PyWeakref_ClearRef(PyWeakReference *self);
# 103 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/structseq.h" 1
# 10 "/Users/parrt/tmp/Python-3.3.1/Include/structseq.h"
typedef struct PyStructSequence_Field {
    char *name;
    char *doc;
} PyStructSequence_Field;

typedef struct PyStructSequence_Desc {
    char *name;
    char *doc;
    struct PyStructSequence_Field *fields;
    int n_in_sequence;
} PyStructSequence_Desc;

extern char* PyStructSequence_UnnamedField;


void PyStructSequence_InitType(PyTypeObject *type,
                                           PyStructSequence_Desc *desc);

PyTypeObject* PyStructSequence_NewType(PyStructSequence_Desc *desc);

PyObject * PyStructSequence_New(PyTypeObject* type);


typedef PyTupleObject PyStructSequence;







void PyStructSequence_SetItem(PyObject*, Py_ssize_t, PyObject*);
PyObject* PyStructSequence_GetItem(PyObject*, Py_ssize_t);
# 104 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/namespaceobject.h" 1
# 10 "/Users/parrt/tmp/Python-3.3.1/Include/namespaceobject.h"
extern PyTypeObject _PyNamespace_Type;

PyObject * _PyNamespace_New(PyObject *kwds);
# 105 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2

# 1 "/Users/parrt/tmp/Python-3.3.1/Include/codecs.h" 1
# 26 "/Users/parrt/tmp/Python-3.3.1/Include/codecs.h"
int PyCodec_Register(
       PyObject *search_function
       );
# 49 "/Users/parrt/tmp/Python-3.3.1/Include/codecs.h"
PyObject * _PyCodec_Lookup(
       const char *encoding
       );
# 61 "/Users/parrt/tmp/Python-3.3.1/Include/codecs.h"
int PyCodec_KnownEncoding(
       const char *encoding
       );
# 75 "/Users/parrt/tmp/Python-3.3.1/Include/codecs.h"
PyObject * PyCodec_Encode(
       PyObject *object,
       const char *encoding,
       const char *errors
       );
# 91 "/Users/parrt/tmp/Python-3.3.1/Include/codecs.h"
PyObject * PyCodec_Decode(
       PyObject *object,
       const char *encoding,
       const char *errors
       );
# 107 "/Users/parrt/tmp/Python-3.3.1/Include/codecs.h"
PyObject * PyCodec_Encoder(
       const char *encoding
       );



PyObject * PyCodec_Decoder(
       const char *encoding
       );



PyObject * PyCodec_IncrementalEncoder(
       const char *encoding,
       const char *errors
       );



PyObject * PyCodec_IncrementalDecoder(
       const char *encoding,
       const char *errors
       );



PyObject * PyCodec_StreamReader(
       const char *encoding,
       PyObject *stream,
       const char *errors
       );



PyObject * PyCodec_StreamWriter(
       const char *encoding,
       PyObject *stream,
       const char *errors
       );
# 155 "/Users/parrt/tmp/Python-3.3.1/Include/codecs.h"
int PyCodec_RegisterError(const char *name, PyObject *error);




PyObject * PyCodec_LookupError(const char *name);


PyObject * PyCodec_StrictErrors(PyObject *exc);


PyObject * PyCodec_IgnoreErrors(PyObject *exc);


PyObject * PyCodec_ReplaceErrors(PyObject *exc);


PyObject * PyCodec_XMLCharRefReplaceErrors(PyObject *exc);


PyObject * PyCodec_BackslashReplaceErrors(PyObject *exc);

extern const char * Py_hexdigits;
# 107 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/pyerrors.h" 1
# 16 "/Users/parrt/tmp/Python-3.3.1/Include/pyerrors.h"
typedef struct {
    PyObject ob_base; PyObject *dict; PyObject *args; PyObject *traceback; PyObject *context; PyObject *cause; char suppress_context;
} PyBaseExceptionObject;

typedef struct {
    PyObject ob_base; PyObject *dict; PyObject *args; PyObject *traceback; PyObject *context; PyObject *cause; char suppress_context;
    PyObject *msg;
    PyObject *filename;
    PyObject *lineno;
    PyObject *offset;
    PyObject *text;
    PyObject *print_file_and_line;
} PySyntaxErrorObject;

typedef struct {
    PyObject ob_base; PyObject *dict; PyObject *args; PyObject *traceback; PyObject *context; PyObject *cause; char suppress_context;
    PyObject *msg;
    PyObject *name;
    PyObject *path;
} PyImportErrorObject;

typedef struct {
    PyObject ob_base; PyObject *dict; PyObject *args; PyObject *traceback; PyObject *context; PyObject *cause; char suppress_context;
    PyObject *encoding;
    PyObject *object;
    Py_ssize_t start;
    Py_ssize_t end;
    PyObject *reason;
} PyUnicodeErrorObject;

typedef struct {
    PyObject ob_base; PyObject *dict; PyObject *args; PyObject *traceback; PyObject *context; PyObject *cause; char suppress_context;
    PyObject *code;
} PySystemExitObject;

typedef struct {
    PyObject ob_base; PyObject *dict; PyObject *args; PyObject *traceback; PyObject *context; PyObject *cause; char suppress_context;
    PyObject *myerrno;
    PyObject *strerror;
    PyObject *filename;



    Py_ssize_t written;
} PyOSErrorObject;

typedef struct {
    PyObject ob_base; PyObject *dict; PyObject *args; PyObject *traceback; PyObject *context; PyObject *cause; char suppress_context;
    PyObject *value;
} PyStopIterationObject;


typedef PyOSErrorObject PyEnvironmentErrorObject;







void PyErr_SetNone(PyObject *);
void PyErr_SetObject(PyObject *, PyObject *);
void PyErr_SetString(
    PyObject *exception,
    const char *string
    );
PyObject * PyErr_Occurred(void);
void PyErr_Clear(void);
void PyErr_Fetch(PyObject **, PyObject **, PyObject **);
void PyErr_Restore(PyObject *, PyObject *, PyObject *);
void PyErr_GetExcInfo(PyObject **, PyObject **, PyObject **);
void PyErr_SetExcInfo(PyObject *, PyObject *, PyObject *);
# 98 "/Users/parrt/tmp/Python-3.3.1/Include/pyerrors.h"
void Py_FatalError(const char *message) ;
# 107 "/Users/parrt/tmp/Python-3.3.1/Include/pyerrors.h"
int PyErr_GivenExceptionMatches(PyObject *, PyObject *);
int PyErr_ExceptionMatches(PyObject *);
void PyErr_NormalizeException(PyObject**, PyObject**, PyObject**);


int PyException_SetTraceback(PyObject *, PyObject *);
PyObject * PyException_GetTraceback(PyObject *);


PyObject * PyException_GetCause(PyObject *);
void PyException_SetCause(PyObject *, PyObject *);


PyObject * PyException_GetContext(PyObject *);
void PyException_SetContext(PyObject *, PyObject *);
# 141 "/Users/parrt/tmp/Python-3.3.1/Include/pyerrors.h"
extern PyObject * PyExc_BaseException;
extern PyObject * PyExc_Exception;
extern PyObject * PyExc_StopIteration;
extern PyObject * PyExc_GeneratorExit;
extern PyObject * PyExc_ArithmeticError;
extern PyObject * PyExc_LookupError;

extern PyObject * PyExc_AssertionError;
extern PyObject * PyExc_AttributeError;
extern PyObject * PyExc_BufferError;
extern PyObject * PyExc_EOFError;
extern PyObject * PyExc_FloatingPointError;
extern PyObject * PyExc_OSError;
extern PyObject * PyExc_ImportError;
extern PyObject * PyExc_IndexError;
extern PyObject * PyExc_KeyError;
extern PyObject * PyExc_KeyboardInterrupt;
extern PyObject * PyExc_MemoryError;
extern PyObject * PyExc_NameError;
extern PyObject * PyExc_OverflowError;
extern PyObject * PyExc_RuntimeError;
extern PyObject * PyExc_NotImplementedError;
extern PyObject * PyExc_SyntaxError;
extern PyObject * PyExc_IndentationError;
extern PyObject * PyExc_TabError;
extern PyObject * PyExc_ReferenceError;
extern PyObject * PyExc_SystemError;
extern PyObject * PyExc_SystemExit;
extern PyObject * PyExc_TypeError;
extern PyObject * PyExc_UnboundLocalError;
extern PyObject * PyExc_UnicodeError;
extern PyObject * PyExc_UnicodeEncodeError;
extern PyObject * PyExc_UnicodeDecodeError;
extern PyObject * PyExc_UnicodeTranslateError;
extern PyObject * PyExc_ValueError;
extern PyObject * PyExc_ZeroDivisionError;

extern PyObject * PyExc_BlockingIOError;
extern PyObject * PyExc_BrokenPipeError;
extern PyObject * PyExc_ChildProcessError;
extern PyObject * PyExc_ConnectionError;
extern PyObject * PyExc_ConnectionAbortedError;
extern PyObject * PyExc_ConnectionRefusedError;
extern PyObject * PyExc_ConnectionResetError;
extern PyObject * PyExc_FileExistsError;
extern PyObject * PyExc_FileNotFoundError;
extern PyObject * PyExc_InterruptedError;
extern PyObject * PyExc_IsADirectoryError;
extern PyObject * PyExc_NotADirectoryError;
extern PyObject * PyExc_PermissionError;
extern PyObject * PyExc_ProcessLookupError;
extern PyObject * PyExc_TimeoutError;



extern PyObject * PyExc_EnvironmentError;
extern PyObject * PyExc_IOError;







extern PyObject * PyExc_RecursionErrorInst;


extern PyObject * PyExc_Warning;
extern PyObject * PyExc_UserWarning;
extern PyObject * PyExc_DeprecationWarning;
extern PyObject * PyExc_PendingDeprecationWarning;
extern PyObject * PyExc_SyntaxWarning;
extern PyObject * PyExc_RuntimeWarning;
extern PyObject * PyExc_FutureWarning;
extern PyObject * PyExc_ImportWarning;
extern PyObject * PyExc_UnicodeWarning;
extern PyObject * PyExc_BytesWarning;
extern PyObject * PyExc_ResourceWarning;




int PyErr_BadArgument(void);
PyObject * PyErr_NoMemory(void);
PyObject * PyErr_SetFromErrno(PyObject *);
PyObject * PyErr_SetFromErrnoWithFilenameObject(
    PyObject *, PyObject *);
PyObject * PyErr_SetFromErrnoWithFilename(
    PyObject *exc,
    const char *filename
    );





PyObject * PyErr_Format(
    PyObject *exception,
    const char *format,
    ...
    );
# 268 "/Users/parrt/tmp/Python-3.3.1/Include/pyerrors.h"
PyObject * PyErr_SetExcWithArgsKwargs(PyObject *, PyObject *,
    PyObject *);
PyObject * PyErr_SetImportError(PyObject *, PyObject *,
    PyObject *);


void PyErr_BadInternalCall(void);
void _PyErr_BadInternalCall(const char *filename, int lineno);





PyObject * PyErr_NewException(
    const char *name, PyObject *base, PyObject *dict);
PyObject * PyErr_NewExceptionWithDoc(
    const char *name, const char *doc, PyObject *base, PyObject *dict);
void PyErr_WriteUnraisable(PyObject *);


int PyErr_CheckSignals(void);
void PyErr_SetInterrupt(void);



int PySignal_SetWakeupFd(int fd);



void PyErr_SyntaxLocation(
    const char *filename,
    int lineno);
void PyErr_SyntaxLocationEx(
    const char *filename,
    int lineno,
    int col_offset);
PyObject * PyErr_ProgramText(
    const char *filename,
    int lineno);





PyObject * PyUnicodeDecodeError_Create(
    const char *encoding,
    const char *object,
    Py_ssize_t length,
    Py_ssize_t start,
    Py_ssize_t end,
    const char *reason
    );



PyObject * PyUnicodeEncodeError_Create(
    const char *encoding,
    const Py_UNICODE *object,
    Py_ssize_t length,
    Py_ssize_t start,
    Py_ssize_t end,
    const char *reason
    );




PyObject * PyUnicodeTranslateError_Create(
    const Py_UNICODE *object,
    Py_ssize_t length,
    Py_ssize_t start,
    Py_ssize_t end,
    const char *reason
    );
PyObject * _PyUnicodeTranslateError_Create(
    PyObject *object,
    Py_ssize_t start,
    Py_ssize_t end,
    const char *reason
    );



PyObject * PyUnicodeEncodeError_GetEncoding(PyObject *);
PyObject * PyUnicodeDecodeError_GetEncoding(PyObject *);


PyObject * PyUnicodeEncodeError_GetObject(PyObject *);
PyObject * PyUnicodeDecodeError_GetObject(PyObject *);
PyObject * PyUnicodeTranslateError_GetObject(PyObject *);



int PyUnicodeEncodeError_GetStart(PyObject *, Py_ssize_t *);
int PyUnicodeDecodeError_GetStart(PyObject *, Py_ssize_t *);
int PyUnicodeTranslateError_GetStart(PyObject *, Py_ssize_t *);



int PyUnicodeEncodeError_SetStart(PyObject *, Py_ssize_t);
int PyUnicodeDecodeError_SetStart(PyObject *, Py_ssize_t);
int PyUnicodeTranslateError_SetStart(PyObject *, Py_ssize_t);



int PyUnicodeEncodeError_GetEnd(PyObject *, Py_ssize_t *);
int PyUnicodeDecodeError_GetEnd(PyObject *, Py_ssize_t *);
int PyUnicodeTranslateError_GetEnd(PyObject *, Py_ssize_t *);



int PyUnicodeEncodeError_SetEnd(PyObject *, Py_ssize_t);
int PyUnicodeDecodeError_SetEnd(PyObject *, Py_ssize_t);
int PyUnicodeTranslateError_SetEnd(PyObject *, Py_ssize_t);


PyObject * PyUnicodeEncodeError_GetReason(PyObject *);
PyObject * PyUnicodeDecodeError_GetReason(PyObject *);
PyObject * PyUnicodeTranslateError_GetReason(PyObject *);



int PyUnicodeEncodeError_SetReason(
    PyObject *exc,
    const char *reason
    );
int PyUnicodeDecodeError_SetReason(
    PyObject *exc,
    const char *reason
    );
int PyUnicodeTranslateError_SetReason(
    PyObject *exc,
    const char *reason
    );
# 418 "/Users/parrt/tmp/Python-3.3.1/Include/pyerrors.h"
int PyOS_snprintf(char *str, size_t size, const char *format, ...)
                        __attribute__((format(printf, 3, 4)));
int PyOS_vsnprintf(char *str, size_t size, const char *format, va_list va)
                        __attribute__((format(printf, 3, 0)));
# 108 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2



# 1 "/Users/parrt/tmp/Python-3.3.1/Include/pyarena.h" 1
# 12 "/Users/parrt/tmp/Python-3.3.1/Include/pyarena.h"
  typedef struct _arena PyArena;
# 36 "/Users/parrt/tmp/Python-3.3.1/Include/pyarena.h"
  PyArena * PyArena_New(void);
  void PyArena_Free(PyArena *);
# 51 "/Users/parrt/tmp/Python-3.3.1/Include/pyarena.h"
  void * PyArena_Malloc(PyArena *, size_t size);





  int PyArena_AddPyObject(PyArena *, PyObject *);
# 112 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/modsupport.h" 1
# 23 "/Users/parrt/tmp/Python-3.3.1/Include/modsupport.h"
PyObject * _Py_VaBuildValue_SizeT(const char *, va_list);




int PyArg_Parse(PyObject *, const char *, ...);
int PyArg_ParseTuple(PyObject *, const char *, ...) ;
int PyArg_ParseTupleAndKeywords(PyObject *, PyObject *,
                                                  const char *, char **, ...);
int PyArg_ValidateKeywordArguments(PyObject *);
int PyArg_UnpackTuple(PyObject *, const char *, Py_ssize_t, Py_ssize_t, ...);
PyObject * Py_BuildValue(const char *, ...);
PyObject * _Py_BuildValue_SizeT(const char *, ...);


int _PyArg_NoKeywords(const char *funcname, PyObject *kw);

int PyArg_VaParse(PyObject *, const char *, va_list);
int PyArg_VaParseTupleAndKeywords(PyObject *, PyObject *,
                                                  const char *, char **, va_list);

PyObject * Py_VaBuildValue(const char *, va_list);

int PyModule_AddObject(PyObject *, const char *, PyObject *);
int PyModule_AddIntConstant(PyObject *, const char *, long);
int PyModule_AddStringConstant(PyObject *, const char *, const char *);
# 113 "/Users/parrt/tmp/Python-3.3.1/Include/modsupport.h"
PyObject * PyModule_Create2(struct PyModuleDef*,
                                     int apiver);
# 125 "/Users/parrt/tmp/Python-3.3.1/Include/modsupport.h"
extern char * _Py_PackageContext;
# 113 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/pythonrun.h" 1
# 20 "/Users/parrt/tmp/Python-3.3.1/Include/pythonrun.h"
typedef struct {
    int cf_flags;
} PyCompilerFlags;


void Py_SetProgramName(wchar_t *);
wchar_t * Py_GetProgramName(void);

void Py_SetPythonHome(wchar_t *);
wchar_t * Py_GetPythonHome(void);

void Py_Initialize(void);
void Py_InitializeEx(int);

void _Py_InitializeEx_Private(int, int);

void Py_Finalize(void);
int Py_IsInitialized(void);
PyThreadState * Py_NewInterpreter(void);
void Py_EndInterpreter(PyThreadState *);


int PyRun_SimpleStringFlags(const char *, PyCompilerFlags *);
int PyRun_AnyFileFlags(FILE *, const char *, PyCompilerFlags *);
int PyRun_AnyFileExFlags(
    FILE *fp,
    const char *filename,
    int closeit,
    PyCompilerFlags *flags);
int PyRun_SimpleFileExFlags(
    FILE *fp,
    const char *filename,
    int closeit,
    PyCompilerFlags *flags);
int PyRun_InteractiveOneFlags(
    FILE *fp,
    const char *filename,
    PyCompilerFlags *flags);
int PyRun_InteractiveLoopFlags(
    FILE *fp,
    const char *filename,
    PyCompilerFlags *flags);

struct _mod * PyParser_ASTFromString(
    const char *s,
    const char *filename,
    int start,
    PyCompilerFlags *flags,
    PyArena *arena);
struct _mod * PyParser_ASTFromFile(
    FILE *fp,
    const char *filename,
    const char* enc,
    int start,
    char *ps1,
    char *ps2,
    PyCompilerFlags *flags,
    int *errcode,
    PyArena *arena);
# 87 "/Users/parrt/tmp/Python-3.3.1/Include/pythonrun.h"
struct _node * PyParser_SimpleParseStringFlags(const char *, int,
                                                           int);
struct _node * PyParser_SimpleParseStringFlagsFilename(const char *,
                                                                   const char *,
                                                                   int, int);
struct _node * PyParser_SimpleParseFileFlags(FILE *, const char *,
                                                         int, int);


PyObject * PyRun_StringFlags(const char *, int, PyObject *,
                                         PyObject *, PyCompilerFlags *);

PyObject * PyRun_FileExFlags(
    FILE *fp,
    const char *filename,
    int start,
    PyObject *globals,
    PyObject *locals,
    int closeit,
    PyCompilerFlags *flags);







PyObject * Py_CompileStringExFlags(
    const char *str,
    const char *filename,
    int start,
    PyCompilerFlags *flags,
    int optimize);

struct symtable * Py_SymtableString(
    const char *str,
    const char *filename,
    int start);

void PyErr_Print(void);
void PyErr_PrintEx(int);
void PyErr_Display(PyObject *, PyObject *, PyObject *);





void _Py_PyAtExit(void (*func)(void));

int Py_AtExit(void (*func)(void));

void Py_Exit(int);



void _Py_RestoreSignals(void);

int Py_FdIsInteractive(FILE *, const char *);



int Py_Main(int argc, wchar_t **argv);
# 172 "/Users/parrt/tmp/Python-3.3.1/Include/pythonrun.h"
wchar_t * Py_GetProgramFullPath(void);
wchar_t * Py_GetPrefix(void);
wchar_t * Py_GetExecPrefix(void);
wchar_t * Py_GetPath(void);
void Py_SetPath(const wchar_t *);





const char * Py_GetVersion(void);
const char * Py_GetPlatform(void);
const char * Py_GetCopyright(void);
const char * Py_GetCompiler(void);
const char * Py_GetBuildInfo(void);

const char * _Py_hgidentifier(void);
const char * _Py_hgversion(void);




PyObject * _PyBuiltin_Init(void);
PyObject * _PySys_Init(void);
void _PyImport_Init(void);
void _PyExc_Init(PyObject * bltinmod);
void _PyImportHooks_Init(void);
int _PyFrame_Init(void);
void _PyFloat_Init(void);
int PyByteArray_Init(void);
void _PyRandom_Init(void);




void _PyExc_Fini(void);
void _PyImport_Fini(void);
void PyMethod_Fini(void);
void PyFrame_Fini(void);
void PyCFunction_Fini(void);
void PyDict_Fini(void);
void PyTuple_Fini(void);
void PyList_Fini(void);
void PySet_Fini(void);
void PyBytes_Fini(void);
void PyByteArray_Fini(void);
void PyFloat_Fini(void);
void PyOS_FiniInterrupts(void);
void _PyGC_Fini(void);
void PySlice_Fini(void);

extern PyThreadState * _Py_Finalizing;




char * PyOS_Readline(FILE *, FILE *, char *);

extern int (*PyOS_InputHook)(void);
extern char *(*PyOS_ReadlineFunctionPointer)(FILE *, FILE *, char *);

extern PyThreadState* _PyOS_ReadlineTState;
# 252 "/Users/parrt/tmp/Python-3.3.1/Include/pythonrun.h"
typedef void (*PyOS_sighandler_t)(int);
PyOS_sighandler_t PyOS_getsig(int);
PyOS_sighandler_t PyOS_setsig(int, PyOS_sighandler_t);


int _PyOS_URandom (void *buffer, Py_ssize_t size);
# 114 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/ceval.h" 1
# 10 "/Users/parrt/tmp/Python-3.3.1/Include/ceval.h"
PyObject * PyEval_CallObjectWithKeywords(
    PyObject *, PyObject *, PyObject *);





PyObject * PyEval_CallFunction(PyObject *obj,
                                           const char *format, ...);
PyObject * PyEval_CallMethod(PyObject *obj,
                                         const char *methodname,
                                         const char *format, ...);


void PyEval_SetProfile(Py_tracefunc, PyObject *);
void PyEval_SetTrace(Py_tracefunc, PyObject *);


struct _frame;

PyObject * PyEval_GetBuiltins(void);
PyObject * PyEval_GetGlobals(void);
PyObject * PyEval_GetLocals(void);
struct _frame * PyEval_GetFrame(void);





int PyEval_MergeCompilerFlags(PyCompilerFlags *cf);


int Py_AddPendingCall(int (*func)(void *), void *arg);
int Py_MakePendingCalls(void);
# 70 "/Users/parrt/tmp/Python-3.3.1/Include/ceval.h"
void Py_SetRecursionLimit(int);
int Py_GetRecursionLimit(void);
# 80 "/Users/parrt/tmp/Python-3.3.1/Include/ceval.h"
int _Py_CheckRecursiveCall(char *where);
extern int _Py_CheckRecursionLimit;
# 108 "/Users/parrt/tmp/Python-3.3.1/Include/ceval.h"
const char * PyEval_GetFuncName(PyObject *);
const char * PyEval_GetFuncDesc(PyObject *);

PyObject * PyEval_GetCallStats(PyObject *);
PyObject * PyEval_EvalFrame(struct _frame *);
PyObject * PyEval_EvalFrameEx(struct _frame *f, int exc);
# 160 "/Users/parrt/tmp/Python-3.3.1/Include/ceval.h"
PyThreadState * PyEval_SaveThread(void);
void PyEval_RestoreThread(PyThreadState *);



int PyEval_ThreadsInitialized(void);
void PyEval_InitThreads(void);
void _PyEval_FiniThreads(void);
void PyEval_AcquireLock(void);
void PyEval_ReleaseLock(void);
void PyEval_AcquireThread(PyThreadState *tstate);
void PyEval_ReleaseThread(PyThreadState *tstate);
void PyEval_ReInitThreads(void);


void _PyEval_SetSwitchInterval(unsigned long microseconds);
unsigned long _PyEval_GetSwitchInterval(void);
# 197 "/Users/parrt/tmp/Python-3.3.1/Include/ceval.h"
int _PyEval_SliceIndex(PyObject *, Py_ssize_t *);
void _PyEval_SignalAsyncExc(void);
# 115 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/sysmodule.h" 1
# 10 "/Users/parrt/tmp/Python-3.3.1/Include/sysmodule.h"
PyObject * PySys_GetObject(const char *);
int PySys_SetObject(const char *, PyObject *);
void PySys_SetArgv(int, wchar_t **);
void PySys_SetArgvEx(int, wchar_t **, int);
void PySys_SetPath(const wchar_t *);

void PySys_WriteStdout(const char *format, ...)
                 __attribute__((format(printf, 1, 2)));
void PySys_WriteStderr(const char *format, ...)
                 __attribute__((format(printf, 1, 2)));
void PySys_FormatStdout(const char *format, ...);
void PySys_FormatStderr(const char *format, ...);

void PySys_ResetWarnOptions(void);
void PySys_AddWarnOption(const wchar_t *);
void PySys_AddWarnOptionUnicode(PyObject *);
int PySys_HasWarnOptions(void);

void PySys_AddXOption(const wchar_t *);
PyObject * PySys_GetXOptions(void);
# 116 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/intrcheck.h" 1







int PyOS_InterruptOccurred(void);
void PyOS_InitInterrupts(void);
void PyOS_AfterFork(void);
int _PyOS_IsMainThread(void);
# 117 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/import.h" 1
# 10 "/Users/parrt/tmp/Python-3.3.1/Include/import.h"
void _PyImportZip_Init(void);

PyObject* PyInit_imp(void);
long PyImport_GetMagicNumber(void);
const char * PyImport_GetMagicTag(void);
PyObject * PyImport_ExecCodeModule(
    char *name,
    PyObject *co
    );
PyObject * PyImport_ExecCodeModuleEx(
    char *name,
    PyObject *co,
    char *pathname
    );
PyObject * PyImport_ExecCodeModuleWithPathnames(
    char *name,
    PyObject *co,
    char *pathname,
    char *cpathname
    );
PyObject * PyImport_ExecCodeModuleObject(
    PyObject *name,
    PyObject *co,
    PyObject *pathname,
    PyObject *cpathname
    );
PyObject * PyImport_GetModuleDict(void);
PyObject * PyImport_AddModuleObject(
    PyObject *name
    );
PyObject * PyImport_AddModule(
    const char *name
    );
PyObject * PyImport_ImportModule(
    const char *name
    );
PyObject * PyImport_ImportModuleNoBlock(
    const char *name
    );
PyObject * PyImport_ImportModuleLevel(
    const char *name,
    PyObject *globals,
    PyObject *locals,
    PyObject *fromlist,
    int level
    );
PyObject * PyImport_ImportModuleLevelObject(
    PyObject *name,
    PyObject *globals,
    PyObject *locals,
    PyObject *fromlist,
    int level
    );




PyObject * PyImport_GetImporter(PyObject *path);
PyObject * PyImport_Import(PyObject *name);
PyObject * PyImport_ReloadModule(PyObject *m);
void PyImport_Cleanup(void);
int PyImport_ImportFrozenModuleObject(
    PyObject *name
    );
int PyImport_ImportFrozenModule(
    char *name
    );



void _PyImport_AcquireLock(void);
int _PyImport_ReleaseLock(void);





void _PyImport_ReInitLock(void);

PyObject *_PyImport_FindBuiltin(
    const char *name
    );
PyObject *_PyImport_FindExtensionObject(PyObject *, PyObject *);
int _PyImport_FixupBuiltin(
    PyObject *mod,
    char *name
    );
int _PyImport_FixupExtensionObject(PyObject*, PyObject *, PyObject *);

struct _inittab {
    char *name;
    PyObject* (*initfunc)(void);
};
extern struct _inittab * PyImport_Inittab;
int PyImport_ExtendInittab(struct _inittab *newtab);


extern PyTypeObject PyNullImporter_Type;

int PyImport_AppendInittab(
    const char *name,
    PyObject* (*initfunc)(void)
    );


struct _frozen {
    char *name;
    unsigned char *code;
    int size;
};




extern struct _frozen * PyImport_FrozenModules;
# 118 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2

# 1 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h" 1
# 266 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * PyObject_Call(PyObject *callable_object,
                                          PyObject *args, PyObject *kw);







     PyObject * PyObject_CallObject(PyObject *callable_object,
                                                PyObject *args);
# 286 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * PyObject_CallFunction(PyObject *callable_object,
                                                  char *format, ...);
# 299 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * PyObject_CallMethod(PyObject *o, char *method,
                                                char *format, ...);
# 311 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * _PyObject_CallMethodId(PyObject *o, _Py_Identifier *method,
                                                  char *format, ...);






     PyObject * _PyObject_CallFunction_SizeT(PyObject *callable,
                                                         char *format, ...);
     PyObject * _PyObject_CallMethod_SizeT(PyObject *o,
                                                       char *name,
                                                       char *format, ...);
     PyObject * _PyObject_CallMethodId_SizeT(PyObject *o,
                                                       _Py_Identifier *name,
                                                       char *format, ...);

     PyObject * PyObject_CallFunctionObjArgs(PyObject *callable,
                                                         ...);
# 340 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * PyObject_CallMethodObjArgs(PyObject *o,
                                                       PyObject *method, ...);
     PyObject * _PyObject_CallMethodObjIdArgs(PyObject *o,
                                               struct _Py_Identifier *method,
                                               ...);
# 384 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * PyObject_Type(PyObject *o);







     Py_ssize_t PyObject_Size(PyObject *o);
# 403 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     Py_ssize_t PyObject_Length(PyObject *o);



     Py_ssize_t _PyObject_LengthHint(PyObject *o, Py_ssize_t);
# 416 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * PyObject_GetItem(PyObject *o, PyObject *key);







     int PyObject_SetItem(PyObject *o, PyObject *key, PyObject *v);







     int PyObject_DelItemString(PyObject *o, char *key);







     int PyObject_DelItem(PyObject *o, PyObject *key);
# 453 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     int PyObject_AsCharBuffer(PyObject *obj,
                                           const char **buffer,
                                           Py_ssize_t *buffer_len);
# 468 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     int PyObject_CheckReadBuffer(PyObject *obj);







     int PyObject_AsReadBuffer(PyObject *obj,
                                           const void **buffer,
                                           Py_ssize_t *buffer_len);
# 491 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     int PyObject_AsWriteBuffer(PyObject *obj,
                                            void **buffer,
                                            Py_ssize_t *buffer_len);
# 515 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     int PyObject_GetBuffer(PyObject *obj, Py_buffer *view,
                                        int flags);
# 525 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     void * PyBuffer_GetPointer(Py_buffer *view, Py_ssize_t *indices);





     int PyBuffer_SizeFromFormat(const char *);







     int PyBuffer_ToContiguous(void *buf, Py_buffer *view,
                                           Py_ssize_t len, char order);

     int PyBuffer_FromContiguous(Py_buffer *view, void *buf,
                                             Py_ssize_t len, char order);
# 562 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     int PyObject_CopyData(PyObject *dest, PyObject *src);




     int PyBuffer_IsContiguous(const Py_buffer *view, char fort);


     void PyBuffer_FillContiguousStrides(int ndims,
                                                    Py_ssize_t *shape,
                                                    Py_ssize_t *strides,
                                                    int itemsize,
                                                    char fort);







     int PyBuffer_FillInfo(Py_buffer *view, PyObject *o, void *buf,
                                       Py_ssize_t len, int readonly,
                                       int flags);







     void PyBuffer_Release(Py_buffer *view);





     PyObject * PyObject_Format(PyObject* obj,
                                            PyObject *format_spec);







     PyObject * PyObject_GetIter(PyObject *);
# 616 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * PyIter_Next(PyObject *);







     int PyNumber_Check(PyObject *o);
# 633 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * PyNumber_Add(PyObject *o1, PyObject *o2);






     PyObject * PyNumber_Subtract(PyObject *o1, PyObject *o2);







     PyObject * PyNumber_Multiply(PyObject *o1, PyObject *o2);







     PyObject * PyNumber_FloorDivide(PyObject *o1, PyObject *o2);







     PyObject * PyNumber_TrueDivide(PyObject *o1, PyObject *o2);







     PyObject * PyNumber_Remainder(PyObject *o1, PyObject *o2);







     PyObject * PyNumber_Divmod(PyObject *o1, PyObject *o2);







     PyObject * PyNumber_Power(PyObject *o1, PyObject *o2,
                                           PyObject *o3);







     PyObject * PyNumber_Negative(PyObject *o);






     PyObject * PyNumber_Positive(PyObject *o);






     PyObject * PyNumber_Absolute(PyObject *o);






     PyObject * PyNumber_Invert(PyObject *o);







     PyObject * PyNumber_Lshift(PyObject *o1, PyObject *o2);







     PyObject * PyNumber_Rshift(PyObject *o1, PyObject *o2);







     PyObject * PyNumber_And(PyObject *o1, PyObject *o2);
# 751 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * PyNumber_Xor(PyObject *o1, PyObject *o2);







     PyObject * PyNumber_Or(PyObject *o1, PyObject *o2);
# 771 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * PyNumber_Index(PyObject *o);






     Py_ssize_t PyNumber_AsSsize_t(PyObject *o, PyObject *exc);
# 788 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * PyNumber_Long(PyObject *o);







     PyObject * PyNumber_Float(PyObject *o);
# 806 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * PyNumber_InPlaceAdd(PyObject *o1, PyObject *o2);







     PyObject * PyNumber_InPlaceSubtract(PyObject *o1, PyObject *o2);







     PyObject * PyNumber_InPlaceMultiply(PyObject *o1, PyObject *o2);







     PyObject * PyNumber_InPlaceFloorDivide(PyObject *o1,
                                                        PyObject *o2);
# 840 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * PyNumber_InPlaceTrueDivide(PyObject *o1,
                                                       PyObject *o2);
# 850 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * PyNumber_InPlaceRemainder(PyObject *o1, PyObject *o2);







     PyObject * PyNumber_InPlacePower(PyObject *o1, PyObject *o2,
                                                  PyObject *o3);







     PyObject * PyNumber_InPlaceLshift(PyObject *o1, PyObject *o2);







     PyObject * PyNumber_InPlaceRshift(PyObject *o1, PyObject *o2);







     PyObject * PyNumber_InPlaceAnd(PyObject *o1, PyObject *o2);







     PyObject * PyNumber_InPlaceXor(PyObject *o1, PyObject *o2);







     PyObject * PyNumber_InPlaceOr(PyObject *o1, PyObject *o2);







     PyObject * PyNumber_ToBase(PyObject *n, int base);
# 918 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     int PySequence_Check(PyObject *o);
# 927 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     Py_ssize_t PySequence_Size(PyObject *o);







     Py_ssize_t PySequence_Length(PyObject *o);



     PyObject * PySequence_Concat(PyObject *o1, PyObject *o2);







     PyObject * PySequence_Repeat(PyObject *o, Py_ssize_t count);







     PyObject * PySequence_GetItem(PyObject *o, Py_ssize_t i);






     PyObject * PySequence_GetSlice(PyObject *o, Py_ssize_t i1, Py_ssize_t i2);







     int PySequence_SetItem(PyObject *o, Py_ssize_t i, PyObject *v);







     int PySequence_DelItem(PyObject *o, Py_ssize_t i);







     int PySequence_SetSlice(PyObject *o, Py_ssize_t i1, Py_ssize_t i2,
                                         PyObject *v);







     int PySequence_DelSlice(PyObject *o, Py_ssize_t i1, Py_ssize_t i2);







     PyObject * PySequence_Tuple(PyObject *o);







     PyObject * PySequence_List(PyObject *o);





     PyObject * PySequence_Fast(PyObject *o, const char* m);
# 1053 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     Py_ssize_t PySequence_Count(PyObject *o, PyObject *value);
# 1062 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     int PySequence_Contains(PyObject *seq, PyObject *ob);
# 1072 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     Py_ssize_t _PySequence_IterSearch(PyObject *seq,
                                        PyObject *obj, int operation);
# 1088 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     int PySequence_In(PyObject *o, PyObject *value);
# 1099 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     Py_ssize_t PySequence_Index(PyObject *o, PyObject *value);
# 1109 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * PySequence_InPlaceConcat(PyObject *o1, PyObject *o2);
# 1118 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * PySequence_InPlaceRepeat(PyObject *o, Py_ssize_t count);
# 1129 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     int PyMapping_Check(PyObject *o);
# 1138 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     Py_ssize_t PyMapping_Size(PyObject *o);
# 1148 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     Py_ssize_t PyMapping_Length(PyObject *o);
# 1172 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     int PyMapping_HasKeyString(PyObject *o, char *key);
# 1182 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     int PyMapping_HasKey(PyObject *o, PyObject *key);
# 1193 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * PyMapping_Keys(PyObject *o);






     PyObject * PyMapping_Values(PyObject *o);






     PyObject * PyMapping_Items(PyObject *o);
# 1216 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * PyMapping_GetItemString(PyObject *o, char *key);







     int PyMapping_SetItemString(PyObject *o, char *key,
                                            PyObject *value);
# 1234 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
int PyObject_IsInstance(PyObject *object, PyObject *typeorclass);


int PyObject_IsSubclass(PyObject *object, PyObject *typeorclass);




int _PyObject_RealIsInstance(PyObject *inst, PyObject *cls);

int _PyObject_RealIsSubclass(PyObject *derived, PyObject *cls);

char *const * _PySequence_BytesToCharpArray(PyObject* self);

void _Py_FreeCharPArray(char *const array[]);



void _Py_add_one_to_index_F(int nd, Py_ssize_t *index,
                                        const Py_ssize_t *shape);
void _Py_add_one_to_index_C(int nd, Py_ssize_t *index,
                                        const Py_ssize_t *shape);
# 120 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/bltinmodule.h" 1






extern PyTypeObject PyFilter_Type;
extern PyTypeObject PyMap_Type;
extern PyTypeObject PyZip_Type;
# 121 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2

# 1 "/Users/parrt/tmp/Python-3.3.1/Include/compile.h" 1




# 1 "/Users/parrt/tmp/Python-3.3.1/Include/code.h" 1
# 11 "/Users/parrt/tmp/Python-3.3.1/Include/code.h"
typedef struct {
    PyObject ob_base;
    int co_argcount;
    int co_kwonlyargcount;
    int co_nlocals;
    int co_stacksize;
    int co_flags;
    PyObject *co_code;
    PyObject *co_consts;
    PyObject *co_names;
    PyObject *co_varnames;
    PyObject *co_freevars;
    PyObject *co_cellvars;

    unsigned char *co_cell2arg;
    PyObject *co_filename;
    PyObject *co_name;
    int co_firstlineno;
    PyObject *co_lnotab;

    void *co_zombieframe;
    PyObject *co_weakreflist;
} PyCodeObject;
# 73 "/Users/parrt/tmp/Python-3.3.1/Include/code.h"
extern PyTypeObject PyCode_Type;





PyCodeObject * PyCode_New(
 int, int, int, int, int, PyObject *, PyObject *,
 PyObject *, PyObject *, PyObject *, PyObject *,
 PyObject *, PyObject *, int, PyObject *);



PyCodeObject *
PyCode_NewEmpty(const char *filename, const char *funcname, int firstlineno);




int PyCode_Addr2Line(PyCodeObject *, int);


typedef struct _addr_pair {
        int ap_lower;
        int ap_upper;
} PyAddrPair;





int _PyCode_CheckLineNumber(PyCodeObject* co,
                                        int lasti, PyAddrPair *bounds);


PyObject* PyCode_Optimize(PyObject *code, PyObject* consts,
                                      PyObject *names, PyObject *lineno_obj);
# 6 "/Users/parrt/tmp/Python-3.3.1/Include/compile.h" 2






struct _node;
PyCodeObject * PyNode_Compile(struct _node *, const char *);



typedef struct {
    int ff_features;
    int ff_lineno;
} PyFutureFeatures;
# 31 "/Users/parrt/tmp/Python-3.3.1/Include/compile.h"
struct _mod;

PyCodeObject * PyAST_CompileEx(
    struct _mod *mod,
    const char *filename,
    PyCompilerFlags *flags,
    int optimize,
    PyArena *arena);
PyFutureFeatures * PyFuture_FromAST(struct _mod *, const char *);


PyObject* _Py_Mangle(PyObject *p, PyObject *name);
# 123 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/eval.h" 1
# 10 "/Users/parrt/tmp/Python-3.3.1/Include/eval.h"
PyObject * PyEval_EvalCode(PyObject *, PyObject *, PyObject *);

PyObject * PyEval_EvalCodeEx(PyObject *co,
     PyObject *globals,
     PyObject *locals,
     PyObject **args, int argc,
     PyObject **kwds, int kwdc,
     PyObject **defs, int defc,
     PyObject *kwdefs, PyObject *closure);


PyObject * _PyEval_CallTracing(PyObject *func, PyObject *args);
# 124 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2

# 1 "/Users/parrt/tmp/Python-3.3.1/Include/pyctype.h" 1
# 13 "/Users/parrt/tmp/Python-3.3.1/Include/pyctype.h"
extern const unsigned int _Py_ctype_table[256];
# 26 "/Users/parrt/tmp/Python-3.3.1/Include/pyctype.h"
extern const unsigned char _Py_ctype_tolower[256];
extern const unsigned char _Py_ctype_toupper[256];
# 126 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/pystrtod.h" 1
# 9 "/Users/parrt/tmp/Python-3.3.1/Include/pystrtod.h"
double PyOS_string_to_double(const char *str,
                                         char **endptr,
                                         PyObject *overflow_exception);



char * PyOS_double_to_string(double val,
                                         char format_code,
                                         int precision,
                                         int flags,
                                         int *type);


double _Py_parse_inf_or_nan(const char *p, char **endptr);
# 127 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/pystrcmp.h" 1







int PyOS_mystrnicmp(const char *, const char *, Py_ssize_t);
int PyOS_mystricmp(const char *, const char *);
# 128 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/dtoa.h" 1






double _Py_dg_strtod(const char *str, char **ptr);
char * _Py_dg_dtoa(double d, int mode, int ndigits,
                        int *decpt, int *sign, char **rve);
void _Py_dg_freedtoa(char *s);
double _Py_dg_stdnan(int sign);
double _Py_dg_infinity(int sign);
# 129 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/fileutils.h" 1







PyObject * _Py_device_encoding(int);

wchar_t * _Py_char2wchar(
    const char *arg,
    size_t *size);

char* _Py_wchar2char(
    const wchar_t *text,
    size_t *error_pos);


int _Py_wstat(
    const wchar_t* path,
    struct stat *buf);



int _Py_stat(
    PyObject *path,
    struct stat *statbuf);


FILE * _Py_wfopen(
    const wchar_t *path,
    const wchar_t *mode);

FILE* _Py_fopen(
    PyObject *path,
    const char *mode);


int _Py_wreadlink(
    const wchar_t *path,
    wchar_t *buf,
    size_t bufsiz);



wchar_t* _Py_wrealpath(
    const wchar_t *path,
    wchar_t *resolved_path,
    size_t resolved_path_size);


wchar_t* _Py_wgetcwd(
    wchar_t *buf,
    size_t size);
# 130 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/pyfpe.h" 1
# 131 "/Users/parrt/tmp/Python-3.3.1/Include/Python.h" 2
# 2 "_pickle.c" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/structmember.h" 1
# 10 "/Users/parrt/tmp/Python-3.3.1/Include/structmember.h"
# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stddef.h" 1 3 4
# 152 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stddef.h" 3 4
typedef long int ptrdiff_t;
# 11 "/Users/parrt/tmp/Python-3.3.1/Include/structmember.h" 2







typedef struct PyMemberDef {
    char *name;
    int type;
    Py_ssize_t offset;
    int flags;
    char *doc;
} PyMemberDef;
# 69 "/Users/parrt/tmp/Python-3.3.1/Include/structmember.h"
PyObject * PyMember_GetOne(const char *, struct PyMemberDef *);
int PyMember_SetOne(char *, struct PyMemberDef *, PyObject *);
# 3 "_pickle.c" 2

static char pickle_module_doc[] = "Optimized C implementation for the Python pickle module.";



enum {
    HIGHEST_PROTOCOL = 3,
    DEFAULT_PROTOCOL = 3
};



enum opcode {
    MARK = '(',
    STOP = '.',
    POP = '0',
    POP_MARK = '1',
    DUP = '2',
    FLOAT = 'F',
    INT = 'I',
    BININT = 'J',
    BININT1 = 'K',
    LONG = 'L',
    BININT2 = 'M',
    NONE = 'N',
    PERSID = 'P',
    BINPERSID = 'Q',
    REDUCE = 'R',
    STRING = 'S',
    BINSTRING = 'T',
    SHORT_BINSTRING = 'U',
    UNICODE = 'V',
    BINUNICODE = 'X',
    APPEND = 'a',
    BUILD = 'b',
    GLOBAL = 'c',
    DICT = 'd',
    EMPTY_DICT = '}',
    APPENDS = 'e',
    GET = 'g',
    BINGET = 'h',
    INST = 'i',
    LONG_BINGET = 'j',
    LIST = 'l',
    EMPTY_LIST = ']',
    OBJ = 'o',
    PUT = 'p',
    BINPUT = 'q',
    LONG_BINPUT = 'r',
    SETITEM = 's',
    TUPLE = 't',
    EMPTY_TUPLE = ')',
    SETITEMS = 'u',
    BINFLOAT = 'G',


    PROTO = '\x80',
    NEWOBJ = '\x81',
    EXT1 = '\x82',
    EXT2 = '\x83',
    EXT4 = '\x84',
    TUPLE1 = '\x85',
    TUPLE2 = '\x86',
    TUPLE3 = '\x87',
    NEWTRUE = '\x88',
    NEWFALSE = '\x89',
    LONG1 = '\x8a',
    LONG4 = '\x8b',


    BINBYTES = 'B',
    SHORT_BINBYTES = 'C'
};
# 87 "_pickle.c"
enum {




    BATCHSIZE = 1000,



    FAST_NESTING_LIMIT = 50,


    WRITE_BUF_SIZE = 4096,



    MAX_WRITE_BUF_SIZE = 64 * 1024,


    PREFETCH = 8192 * 16
};



static PyObject *PickleError = ((void *)0);
static PyObject *PicklingError = ((void *)0);
static PyObject *UnpicklingError = ((void *)0);


static PyObject *dispatch_table = ((void *)0);


static PyObject *extension_registry = ((void *)0);

static PyObject *inverted_registry = ((void *)0);

static PyObject *extension_cache = ((void *)0);


static PyObject *name_mapping_2to3 = ((void *)0);

static PyObject *import_mapping_2to3 = ((void *)0);

static PyObject *name_mapping_3to2 = ((void *)0);
static PyObject *import_mapping_3to2 = ((void *)0);



static PyObject *empty_tuple = ((void *)0);

static PyObject *two_tuple = ((void *)0);

static int
stack_underflow(void)
{
    PyErr_SetString(UnpicklingError, "unpickling stack underflow");
    return -1;
}


typedef struct {
    PyVarObject ob_base;
    PyObject **data;
    Py_ssize_t allocated;
} Pdata;

static void
Pdata_dealloc(Pdata *self)
{
    Py_ssize_t i = (((PyVarObject*)(self))->ob_size);
    while (--i >= 0) {
        do { if ( --((PyObject*)(self->data[i]))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->data[i])))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->data[i])))); } while (0);
    }
    free(self->data);
    PyObject_Free(self);
}

static PyTypeObject Pdata_Type = {
    { { 1, ((void *)0) }, 0 },
    "_pickle.Pdata",
    sizeof(Pdata),
    0,
    (destructor)Pdata_dealloc,
};

static PyObject *
Pdata_New(void)
{
    Pdata *self;

    if (!(self = ( (Pdata *) _PyObject_New(&Pdata_Type) )))
        return ((void *)0);
    (((PyVarObject*)(self))->ob_size) = 0;
    self->allocated = 8;
    self->data = ((size_t)(self->allocated * sizeof(PyObject *)) > (size_t)((Py_ssize_t)(((size_t)-1)>>1)) ? ((void *)0) : malloc((self->allocated * sizeof(PyObject *)) ? (self->allocated * sizeof(PyObject *)) : 1));
    if (self->data)
        return (PyObject *)self;
    do { if ( --((PyObject*)(self))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self)))); } while (0);
    return PyErr_NoMemory();
}





static int
Pdata_clear(Pdata *self, Py_ssize_t clearto)
{
    Py_ssize_t i = (((PyVarObject*)(self))->ob_size);

    if (clearto < 0)
        return stack_underflow();
    if (clearto >= i)
        return 0;

    while (--i >= clearto) {
        do { if (self->data[i]) { PyObject *_py_tmp = (PyObject *)(self->data[i]); (self->data[i]) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    }
    (((PyVarObject*)(self))->ob_size) = clearto;
    return 0;
}

static int
Pdata_grow(Pdata *self)
{
    PyObject **data = self->data;
    Py_ssize_t allocated = self->allocated;
    Py_ssize_t new_allocated;

    new_allocated = (allocated >> 3) + 6;

    if (new_allocated > ((Py_ssize_t)(((size_t)-1)>>1)) - allocated)
        goto nomemory;
    new_allocated += allocated;
    if (new_allocated > (((Py_ssize_t)(((size_t)-1)>>1)) / sizeof(PyObject *)))
        goto nomemory;
    data = ((size_t)(new_allocated * sizeof(PyObject *)) > (size_t)((Py_ssize_t)(((size_t)-1)>>1)) ? ((void *)0) : realloc((data), (new_allocated * sizeof(PyObject *)) ? (new_allocated * sizeof(PyObject *)) : 1));
    if (data == ((void *)0))
        goto nomemory;

    self->data = data;
    self->allocated = new_allocated;
    return 0;

  nomemory:
    PyErr_NoMemory();
    return -1;
}





static PyObject *
Pdata_pop(Pdata *self)
{
    if ((((PyVarObject*)(self))->ob_size) == 0) {
        PyErr_SetString(UnpicklingError, "bad pickle data");
        return ((void *)0);
    }
    return self->data[--(((PyVarObject*)(self))->ob_size)];
}


static int
Pdata_push(Pdata *self, PyObject *obj)
{
    if ((((PyVarObject*)(self))->ob_size) == self->allocated && Pdata_grow(self) < 0) {
        return -1;
    }
    self->data[(((PyVarObject*)(self))->ob_size)++] = obj;
    return 0;
}
# 270 "_pickle.c"
static PyObject *
Pdata_poptuple(Pdata *self, Py_ssize_t start)
{
    PyObject *tuple;
    Py_ssize_t len, i, j;

    len = (((PyVarObject*)(self))->ob_size) - start;
    tuple = PyTuple_New(len);
    if (tuple == ((void *)0))
        return ((void *)0);
    for (i = start, j = 0; j < len; i++, j++)
        (((PyTupleObject *)(tuple))->ob_item[j] = self->data[i]);

    (((PyVarObject*)(self))->ob_size) = start;
    return tuple;
}

static PyObject *
Pdata_poplist(Pdata *self, Py_ssize_t start)
{
    PyObject *list;
    Py_ssize_t len, i, j;

    len = (((PyVarObject*)(self))->ob_size) - start;
    list = PyList_New(len);
    if (list == ((void *)0))
        return ((void *)0);
    for (i = start, j = 0; j < len; i++, j++)
        (((PyListObject *)(list))->ob_item[j] = (self->data[i]));

    (((PyVarObject*)(self))->ob_size) = start;
    return list;
}

typedef struct {
    PyObject *me_key;
    Py_ssize_t me_value;
} PyMemoEntry;

typedef struct {
    Py_ssize_t mt_mask;
    Py_ssize_t mt_used;
    Py_ssize_t mt_allocated;
    PyMemoEntry *mt_table;
} PyMemoTable;

typedef struct PicklerObject {
    PyObject ob_base;
    PyMemoTable *memo;


    PyObject *pers_func;
    PyObject *dispatch_table;
    PyObject *arg;

    PyObject *write;
    PyObject *output_buffer;

    Py_ssize_t output_len;
    Py_ssize_t max_output_len;
    int proto;
    int bin;
    Py_ssize_t buf_size;
    int fast;





    int fast_nesting;
    int fix_imports;

    PyObject *fast_memo;
} PicklerObject;

typedef struct UnpicklerObject {
    PyObject ob_base;
    Pdata *stack;



    PyObject **memo;
    Py_ssize_t memo_size;

    PyObject *arg;
    PyObject *pers_func;

    Py_buffer buffer;
    char *input_buffer;
    char *input_line;
    Py_ssize_t input_len;
    Py_ssize_t next_read_idx;
    Py_ssize_t prefetched_idx;
    PyObject *read;
    PyObject *readline;
    PyObject *peek;

    char *encoding;


    char *errors;


    Py_ssize_t *marks;

    Py_ssize_t num_marks;
    Py_ssize_t marks_size;
    int proto;
    int fix_imports;

} UnpicklerObject;


static int save(PicklerObject *, PyObject *, int);
static int save_reduce(PicklerObject *, PyObject *, PyObject *);
static PyTypeObject Pickler_Type;
static PyTypeObject Unpickler_Type;
# 399 "_pickle.c"
static PyMemoTable *
PyMemoTable_New(void)
{
    PyMemoTable *memo = ((size_t)(sizeof(PyMemoTable)) > (size_t)((Py_ssize_t)(((size_t)-1)>>1)) ? ((void *)0) : malloc((sizeof(PyMemoTable)) ? (sizeof(PyMemoTable)) : 1));
    if (memo == ((void *)0)) {
        PyErr_NoMemory();
        return ((void *)0);
    }

    memo->mt_used = 0;
    memo->mt_allocated = 8;
    memo->mt_mask = 8 - 1;
    memo->mt_table = ((size_t)(8 * sizeof(PyMemoEntry)) > (size_t)((Py_ssize_t)(((size_t)-1)>>1)) ? ((void *)0) : malloc((8 * sizeof(PyMemoEntry)) ? (8 * sizeof(PyMemoEntry)) : 1));
    if (memo->mt_table == ((void *)0)) {
        free(memo);
        PyErr_NoMemory();
        return ((void *)0);
    }
    ((__builtin_object_size (memo->mt_table, 0) != (size_t) -1) ? __builtin___memset_chk (memo->mt_table, 0, 8 * sizeof(PyMemoEntry), __builtin_object_size (memo->mt_table, 0)) : __inline_memset_chk (memo->mt_table, 0, 8 * sizeof(PyMemoEntry)));

    return memo;
}

static PyMemoTable *
PyMemoTable_Copy(PyMemoTable *self)
{
    Py_ssize_t i;
    PyMemoTable *new = PyMemoTable_New();
    if (new == ((void *)0))
        return ((void *)0);

    new->mt_used = self->mt_used;
    new->mt_allocated = self->mt_allocated;
    new->mt_mask = self->mt_mask;


    free(new->mt_table);
    new->mt_table = ((size_t)(self->mt_allocated * sizeof(PyMemoEntry)) > (size_t)((Py_ssize_t)(((size_t)-1)>>1)) ? ((void *)0) : malloc((self->mt_allocated * sizeof(PyMemoEntry)) ? (self->mt_allocated * sizeof(PyMemoEntry)) : 1));
    if (new->mt_table == ((void *)0)) {
        free(new);
        return ((void *)0);
    }
    for (i = 0; i < self->mt_allocated; i++) {
        do { if ((self->mt_table[i].me_key) == ((void *)0)) ; else ( ((PyObject*)(self->mt_table[i].me_key))->ob_refcnt++); } while (0);
    }
    ((__builtin_object_size (new->mt_table, 0) != (size_t) -1) ? __builtin___memcpy_chk (new->mt_table, self->mt_table, sizeof(PyMemoEntry) * self->mt_allocated, __builtin_object_size (new->mt_table, 0)) : __inline_memcpy_chk (new->mt_table, self->mt_table, sizeof(PyMemoEntry) * self->mt_allocated));


    return new;
}

static Py_ssize_t
PyMemoTable_Size(PyMemoTable *self)
{
    return self->mt_used;
}

static int
PyMemoTable_Clear(PyMemoTable *self)
{
    Py_ssize_t i = self->mt_allocated;

    while (--i >= 0) {
        do { if ((self->mt_table[i].me_key) == ((void *)0)) ; else do { if ( --((PyObject*)(self->mt_table[i].me_key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->mt_table[i].me_key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->mt_table[i].me_key)))); } while (0); } while (0);
    }
    self->mt_used = 0;
    ((__builtin_object_size (self->mt_table, 0) != (size_t) -1) ? __builtin___memset_chk (self->mt_table, 0, self->mt_allocated * sizeof(PyMemoEntry), __builtin_object_size (self->mt_table, 0)) : __inline_memset_chk (self->mt_table, 0, self->mt_allocated * sizeof(PyMemoEntry)));
    return 0;
}

static void
PyMemoTable_Del(PyMemoTable *self)
{
    if (self == ((void *)0))
        return;
    PyMemoTable_Clear(self);

    free(self->mt_table);
    free(self);
}



static PyMemoEntry *
_PyMemoTable_Lookup(PyMemoTable *self, PyObject *key)
{
    size_t i;
    size_t perturb;
    size_t mask = (size_t)self->mt_mask;
    PyMemoEntry *table = self->mt_table;
    PyMemoEntry *entry;
    Py_hash_t hash = (Py_hash_t)key >> 3;

    i = hash & mask;
    entry = &table[i];
    if (entry->me_key == ((void *)0) || entry->me_key == key)
        return entry;

    for (perturb = hash; ; perturb >>= 5) {
        i = (i << 2) + i + perturb + 1;
        entry = &table[i & mask];
        if (entry->me_key == ((void *)0) || entry->me_key == key)
            return entry;
    }
    (__builtin_expect(!(0), 0) ? __assert_rtn(__func__, "_pickle.c", 503, "0") : (void)0);
    return ((void *)0);
}


static int
_PyMemoTable_ResizeTable(PyMemoTable *self, Py_ssize_t min_size)
{
    PyMemoEntry *oldtable = ((void *)0);
    PyMemoEntry *oldentry, *newentry;
    Py_ssize_t new_size = 8;
    Py_ssize_t to_process;

    (__builtin_expect(!(min_size > 0), 0) ? __assert_rtn(__func__, "_pickle.c", 516, "min_size > 0") : (void)0);


    while (new_size < min_size && new_size > 0)
        new_size <<= 1;
    if (new_size <= 0) {
        PyErr_NoMemory();
        return -1;
    }

    (__builtin_expect(!((new_size & (new_size - 1)) == 0), 0) ? __assert_rtn(__func__, "_pickle.c", 526, "(new_size & (new_size - 1)) == 0") : (void)0);


    oldtable = self->mt_table;
    self->mt_table = ((size_t)(new_size * sizeof(PyMemoEntry)) > (size_t)((Py_ssize_t)(((size_t)-1)>>1)) ? ((void *)0) : malloc((new_size * sizeof(PyMemoEntry)) ? (new_size * sizeof(PyMemoEntry)) : 1));
    if (self->mt_table == ((void *)0)) {
        free(oldtable);
        PyErr_NoMemory();
        return -1;
    }
    self->mt_allocated = new_size;
    self->mt_mask = new_size - 1;
    ((__builtin_object_size (self->mt_table, 0) != (size_t) -1) ? __builtin___memset_chk (self->mt_table, 0, sizeof(PyMemoEntry) * new_size, __builtin_object_size (self->mt_table, 0)) : __inline_memset_chk (self->mt_table, 0, sizeof(PyMemoEntry) * new_size));


    to_process = self->mt_used;
    for (oldentry = oldtable; to_process > 0; oldentry++) {
        if (oldentry->me_key != ((void *)0)) {
            to_process--;



            newentry = _PyMemoTable_Lookup(self, oldentry->me_key);
            newentry->me_key = oldentry->me_key;
            newentry->me_value = oldentry->me_value;
        }
    }


    free(oldtable);
    return 0;
}


static Py_ssize_t *
PyMemoTable_Get(PyMemoTable *self, PyObject *key)
{
    PyMemoEntry *entry = _PyMemoTable_Lookup(self, key);
    if (entry->me_key == ((void *)0))
        return ((void *)0);
    return &entry->me_value;
}


static int
PyMemoTable_Set(PyMemoTable *self, PyObject *key, Py_ssize_t value)
{
    PyMemoEntry *entry;

    (__builtin_expect(!(key != ((void *)0)), 0) ? __assert_rtn(__func__, "_pickle.c", 575, "key != NULL") : (void)0);

    entry = _PyMemoTable_Lookup(self, key);
    if (entry->me_key != ((void *)0)) {
        entry->me_value = value;
        return 0;
    }
    ( ((PyObject*)(key))->ob_refcnt++);
    entry->me_key = key;
    entry->me_value = value;
    self->mt_used++;
# 597 "_pickle.c"
    if (!(self->mt_used * 3 >= (self->mt_mask + 1) * 2))
        return 0;
    return _PyMemoTable_ResizeTable(self,
        (self->mt_used > 50000 ? 2 : 4) * self->mt_used);
}
# 650 "_pickle.c"
static PyObject *
_Pickler_FastCall(PicklerObject *self, PyObject *func, PyObject *arg)
{
    PyObject *result = ((void *)0);

    do { if ((self)->arg || ((self)->arg=PyTuple_New(1))) { do { if (((((PyTupleObject *)((self)->arg))->ob_item[0])) == ((void *)0)) ; else do { if ( --((PyObject*)((((PyTupleObject *)((self)->arg))->ob_item[0])))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)((((PyTupleObject *)((self)->arg))->ob_item[0]))))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)((((PyTupleObject *)((self)->arg))->ob_item[0]))))); } while (0); } while (0); (((PyTupleObject *)((self)->arg))->ob_item[0] = (arg)); } else { do { if ( --((PyObject*)((arg)))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)((arg))))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)((arg))))); } while (0); } } while (0);
    if (self->arg) {
        result = PyObject_Call(func, self->arg, ((void *)0));
        do { if ((self)->arg->ob_refcnt > 1) do { if ((self)->arg) { PyObject *_py_tmp = (PyObject *)((self)->arg); ((self)->arg) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0); } while (0);
    }
    return result;
}

static int
_Pickler_ClearBuffer(PicklerObject *self)
{
    do { if (self->output_buffer) { PyObject *_py_tmp = (PyObject *)(self->output_buffer); (self->output_buffer) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    self->output_buffer =
        PyBytes_FromStringAndSize(((void *)0), self->max_output_len);
    if (self->output_buffer == ((void *)0))
        return -1;
    self->output_len = 0;
    return 0;
}

static PyObject *
_Pickler_GetString(PicklerObject *self)
{
    PyObject *output_buffer = self->output_buffer;

    (__builtin_expect(!(self->output_buffer != ((void *)0)), 0) ? __assert_rtn(__func__, "_pickle.c", 680, "self->output_buffer != NULL") : (void)0);
    self->output_buffer = ((void *)0);

    if (_PyBytes_Resize(&output_buffer, self->output_len) < 0)
        return ((void *)0);
    return output_buffer;
}

static int
_Pickler_FlushToFile(PicklerObject *self)
{
    PyObject *output, *result;

    (__builtin_expect(!(self->write != ((void *)0)), 0) ? __assert_rtn(__func__, "_pickle.c", 693, "self->write != NULL") : (void)0);

    output = _Pickler_GetString(self);
    if (output == ((void *)0))
        return -1;

    result = _Pickler_FastCall(self, self->write, output);
    do { if ((result) == ((void *)0)) ; else do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0); } while (0);
    return (result == ((void *)0)) ? -1 : 0;
}

static Py_ssize_t
_Pickler_Write(PicklerObject *self, const char *s, Py_ssize_t n)
{
    Py_ssize_t i, required;
    char *buffer;

    (__builtin_expect(!(s != ((void *)0)), 0) ? __assert_rtn(__func__, "_pickle.c", 710, "s != NULL") : (void)0);

    required = self->output_len + n;
    if (required > self->max_output_len) {
        if (self->write != ((void *)0) && required > MAX_WRITE_BUF_SIZE) {


            if (_Pickler_FlushToFile(self) < 0)
                return -1;
            if (_Pickler_ClearBuffer(self) < 0)
                return -1;
        }
        if (self->write != ((void *)0) && n > MAX_WRITE_BUF_SIZE) {

            PyObject *result;


            PyObject *output = PyBytes_FromStringAndSize(s, n);
            if (s == ((void *)0))
                return -1;
            result = _Pickler_FastCall(self, self->write, output);
            do { if ((result) == ((void *)0)) ; else do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0); } while (0);
            return (result == ((void *)0)) ? -1 : 0;
        }
        else {
            if (self->output_len >= ((Py_ssize_t)(((size_t)-1)>>1)) / 2 - n) {
                PyErr_NoMemory();
                return -1;
            }
            self->max_output_len = (self->output_len + n) / 2 * 3;
            if (_PyBytes_Resize(&self->output_buffer, self->max_output_len) < 0)
                return -1;
        }
    }
    buffer = ((__builtin_expect(!(((((((PyObject*)(self->output_buffer))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 744, "PyBytes_Check(self->output_buffer)") : (void)0), (((PyBytesObject *)(self->output_buffer))->ob_sval));
    if (n < 8) {

        for (i = 0; i < n; i++) {
            buffer[self->output_len + i] = s[i];
        }
    }
    else {
        ((__builtin_object_size (buffer + self->output_len, 0) != (size_t) -1) ? __builtin___memcpy_chk (buffer + self->output_len, s, n, __builtin_object_size (buffer + self->output_len, 0)) : __inline_memcpy_chk (buffer + self->output_len, s, n));
    }
    self->output_len += n;
    return n;
}

static PicklerObject *
_Pickler_New(void)
{
    PicklerObject *self;

    self = ( (PicklerObject *) _PyObject_GC_New(&Pickler_Type) );
    if (self == ((void *)0))
        return ((void *)0);

    self->pers_func = ((void *)0);
    self->dispatch_table = ((void *)0);
    self->arg = ((void *)0);
    self->write = ((void *)0);
    self->proto = 0;
    self->bin = 0;
    self->fast = 0;
    self->fast_nesting = 0;
    self->fix_imports = 0;
    self->fast_memo = ((void *)0);

    self->memo = PyMemoTable_New();
    if (self->memo == ((void *)0)) {
        do { if ( --((PyObject*)(self))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self)))); } while (0);
        return ((void *)0);
    }
    self->max_output_len = WRITE_BUF_SIZE;
    self->output_len = 0;
    self->output_buffer = PyBytes_FromStringAndSize(((void *)0),
                                                    self->max_output_len);
    if (self->output_buffer == ((void *)0)) {
        do { if ( --((PyObject*)(self))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self)))); } while (0);
        return ((void *)0);
    }
    return self;
}

static int
_Pickler_SetProtocol(PicklerObject *self, PyObject *proto_obj,
                     PyObject *fix_imports_obj)
{
    long proto = 0;
    int fix_imports;

    if (proto_obj == ((void *)0) || proto_obj == (&_Py_NoneStruct))
        proto = DEFAULT_PROTOCOL;
    else {
        proto = PyLong_AsLong(proto_obj);
        if (proto == -1 && PyErr_Occurred())
            return -1;
    }
    if (proto < 0)
        proto = HIGHEST_PROTOCOL;
    if (proto > HIGHEST_PROTOCOL) {
        PyErr_Format(PyExc_ValueError, "pickle protocol must be <= %d",
                     HIGHEST_PROTOCOL);
        return -1;
    }
    fix_imports = PyObject_IsTrue(fix_imports_obj);
    if (fix_imports == -1)
        return -1;

    self->proto = proto;
    self->bin = proto > 0;
    self->fix_imports = fix_imports && proto < 3;

    return 0;
}



static int
_Pickler_SetOutputStream(PicklerObject *self, PyObject *file)
{
    static _Py_Identifier PyId_write = { 0, "write", 0 };
    (__builtin_expect(!(file != ((void *)0)), 0) ? __assert_rtn(__func__, "_pickle.c", 832, "file != NULL") : (void)0);
    self->write = _PyObject_GetAttrId(file, &PyId_write);
    if (self->write == ((void *)0)) {
        if (PyErr_ExceptionMatches(PyExc_AttributeError))
            PyErr_SetString(PyExc_TypeError,
                            "file must have a 'write' attribute");
        return -1;
    }

    return 0;
}


static PyObject *
_Unpickler_FastCall(UnpicklerObject *self, PyObject *func, PyObject *arg)
{
    PyObject *result = ((void *)0);

    do { if ((self)->arg || ((self)->arg=PyTuple_New(1))) { do { if (((((PyTupleObject *)((self)->arg))->ob_item[0])) == ((void *)0)) ; else do { if ( --((PyObject*)((((PyTupleObject *)((self)->arg))->ob_item[0])))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)((((PyTupleObject *)((self)->arg))->ob_item[0]))))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)((((PyTupleObject *)((self)->arg))->ob_item[0]))))); } while (0); } while (0); (((PyTupleObject *)((self)->arg))->ob_item[0] = (arg)); } else { do { if ( --((PyObject*)((arg)))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)((arg))))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)((arg))))); } while (0); } } while (0);
    if (self->arg) {
        result = PyObject_Call(func, self->arg, ((void *)0));
        do { if ((self)->arg->ob_refcnt > 1) do { if ((self)->arg) { PyObject *_py_tmp = (PyObject *)((self)->arg); ((self)->arg) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0); } while (0);
    }
    return result;
}



static Py_ssize_t
_Unpickler_SetStringInput(UnpicklerObject *self, PyObject *input)
{
    if (self->buffer.buf != ((void *)0))
        PyBuffer_Release(&self->buffer);
    if (PyObject_GetBuffer(input, &self->buffer, (0x0008)) < 0)
        return -1;
    self->input_buffer = self->buffer.buf;
    self->input_len = self->buffer.len;
    self->next_read_idx = 0;
    self->prefetched_idx = self->input_len;
    return self->input_len;
}

static int
_Unpickler_SkipConsumed(UnpicklerObject *self)
{
    Py_ssize_t consumed = self->next_read_idx - self->prefetched_idx;

    if (consumed > 0) {
        PyObject *r;
        (__builtin_expect(!(self->peek), 0) ? __assert_rtn(__func__, "_pickle.c", 881, "self->peek") : (void)0);

        r = PyObject_CallFunction(self->read, "n", consumed);
        if (r == ((void *)0))
            return -1;
        do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0);
        self->prefetched_idx = self->next_read_idx;
    }
    return 0;
}

static const Py_ssize_t READ_WHOLE_LINE = -1;
# 908 "_pickle.c"
static Py_ssize_t
_Unpickler_ReadFromFile(UnpicklerObject *self, Py_ssize_t n)
{
    PyObject *data;
    Py_ssize_t read_size, prefetched_size = 0;

    (__builtin_expect(!(self->read != ((void *)0)), 0) ? __assert_rtn(__func__, "_pickle.c", 914, "self->read != NULL") : (void)0);

    if (_Unpickler_SkipConsumed(self) < 0)
        return -1;

    if (n == READ_WHOLE_LINE)
        data = PyObject_Call(self->readline, empty_tuple, ((void *)0));
    else {
        PyObject *len = PyLong_FromSsize_t(n);
        if (len == ((void *)0))
            return -1;
        data = _Unpickler_FastCall(self, self->read, len);
    }
    if (data == ((void *)0))
        return -1;


    if (self->peek) {
        PyObject *len, *prefetched;
        len = PyLong_FromSsize_t(PREFETCH);
        if (len == ((void *)0)) {
            do { if ( --((PyObject*)(data))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(data)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(data)))); } while (0);
            return -1;
        }
        prefetched = _Unpickler_FastCall(self, self->peek, len);
        if (prefetched == ((void *)0)) {
            if (PyErr_ExceptionMatches(PyExc_NotImplementedError)) {

                PyErr_Clear();
                do { if (self->peek) { PyObject *_py_tmp = (PyObject *)(self->peek); (self->peek) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
            }
            else {
                do { if ( --((PyObject*)(data))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(data)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(data)))); } while (0);
                return -1;
            }
        }
        else {
            (__builtin_expect(!(((((((PyObject*)(prefetched))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 951, "PyBytes_Check(prefetched)") : (void)0);
            prefetched_size = ((__builtin_expect(!(((((((PyObject*)(prefetched))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 952, "PyBytes_Check(prefetched)") : (void)0),(((PyVarObject*)(prefetched))->ob_size));
            PyBytes_ConcatAndDel(&data, prefetched);
            if (data == ((void *)0))
                return -1;
        }
    }

    read_size = _Unpickler_SetStringInput(self, data) - prefetched_size;
    do { if ( --((PyObject*)(data))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(data)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(data)))); } while (0);
    self->prefetched_idx = read_size;
    return read_size;
}
# 978 "_pickle.c"
static Py_ssize_t
_Unpickler_Read(UnpicklerObject *self, char **s, Py_ssize_t n)
{
    Py_ssize_t num_read;

    if (self->next_read_idx + n <= self->input_len) {
        *s = self->input_buffer + self->next_read_idx;
        self->next_read_idx += n;
        return n;
    }
    if (!self->read) {
        PyErr_Format(PyExc_EOFError, "Ran out of input");
        return -1;
    }
    num_read = _Unpickler_ReadFromFile(self, n);
    if (num_read < 0)
        return -1;
    if (num_read < n) {
        PyErr_Format(PyExc_EOFError, "Ran out of input");
        return -1;
    }
    *s = self->input_buffer;
    self->next_read_idx = n;
    return n;
}

static Py_ssize_t
_Unpickler_CopyLine(UnpicklerObject *self, char *line, Py_ssize_t len,
                    char **result)
{
    char *input_line = PyMem_Realloc(self->input_line, len + 1);
    if (input_line == ((void *)0))
        return -1;

    ((__builtin_object_size (input_line, 0) != (size_t) -1) ? __builtin___memcpy_chk (input_line, line, len, __builtin_object_size (input_line, 0)) : __inline_memcpy_chk (input_line, line, len));
    input_line[len] = '\0';
    self->input_line = input_line;
    *result = self->input_line;
    return len;
}





static Py_ssize_t
_Unpickler_Readline(UnpicklerObject *self, char **result)
{
    Py_ssize_t i, num_read;

    for (i = self->next_read_idx; i < self->input_len; i++) {
        if (self->input_buffer[i] == '\n') {
            char *line_start = self->input_buffer + self->next_read_idx;
            num_read = i - self->next_read_idx + 1;
            self->next_read_idx = i + 1;
            return _Unpickler_CopyLine(self, line_start, num_read, result);
        }
    }
    if (self->read) {
        num_read = _Unpickler_ReadFromFile(self, READ_WHOLE_LINE);
        if (num_read < 0)
            return -1;
        self->next_read_idx = num_read;
        return _Unpickler_CopyLine(self, self->input_buffer, num_read, result);
    }



    *result = self->input_buffer + self->next_read_idx;
    num_read = i - self->next_read_idx;
    self->next_read_idx = i;
    return num_read;
}



static int
_Unpickler_ResizeMemoList(UnpicklerObject *self, Py_ssize_t new_size)
{
    Py_ssize_t i;
    PyObject **memo;

    (__builtin_expect(!(new_size > self->memo_size), 0) ? __assert_rtn(__func__, "_pickle.c", 1060, "new_size > self->memo_size") : (void)0);

    memo = ((size_t)(new_size * sizeof(PyObject *)) > (size_t)((Py_ssize_t)(((size_t)-1)>>1)) ? ((void *)0) : realloc((self->memo), (new_size * sizeof(PyObject *)) ? (new_size * sizeof(PyObject *)) : 1));
    if (memo == ((void *)0)) {
        PyErr_NoMemory();
        return -1;
    }
    self->memo = memo;
    for (i = self->memo_size; i < new_size; i++)
        self->memo[i] = ((void *)0);
    self->memo_size = new_size;
    return 0;
}


static PyObject *
_Unpickler_MemoGet(UnpicklerObject *self, Py_ssize_t idx)
{
    if (idx < 0 || idx >= self->memo_size)
        return ((void *)0);

    return self->memo[idx];
}



static int
_Unpickler_MemoPut(UnpicklerObject *self, Py_ssize_t idx, PyObject *value)
{
    PyObject *old_item;

    if (idx >= self->memo_size) {
        if (_Unpickler_ResizeMemoList(self, idx * 2) < 0)
            return -1;
        (__builtin_expect(!(idx < self->memo_size), 0) ? __assert_rtn(__func__, "_pickle.c", 1094, "idx < self->memo_size") : (void)0);
    }
    ( ((PyObject*)(value))->ob_refcnt++);
    old_item = self->memo[idx];
    self->memo[idx] = value;
    do { if ((old_item) == ((void *)0)) ; else do { if ( --((PyObject*)(old_item))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(old_item)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(old_item)))); } while (0); } while (0);
    return 0;
}

static PyObject **
_Unpickler_NewMemo(Py_ssize_t new_size)
{
    PyObject **memo = ((size_t)(new_size * sizeof(PyObject *)) > (size_t)((Py_ssize_t)(((size_t)-1)>>1)) ? ((void *)0) : malloc((new_size * sizeof(PyObject *)) ? (new_size * sizeof(PyObject *)) : 1));
    if (memo == ((void *)0))
        return ((void *)0);
    ((__builtin_object_size (memo, 0) != (size_t) -1) ? __builtin___memset_chk (memo, 0, new_size * sizeof(PyObject *), __builtin_object_size (memo, 0)) : __inline_memset_chk (memo, 0, new_size * sizeof(PyObject *)));
    return memo;
}


static void
_Unpickler_MemoCleanup(UnpicklerObject *self)
{
    Py_ssize_t i;
    PyObject **memo = self->memo;

    if (self->memo == ((void *)0))
        return;
    self->memo = ((void *)0);
    i = self->memo_size;
    while (--i >= 0) {
        do { if ((memo[i]) == ((void *)0)) ; else do { if ( --((PyObject*)(memo[i]))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(memo[i])))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(memo[i])))); } while (0); } while (0);
    }
    free(memo);
}

static UnpicklerObject *
_Unpickler_New(void)
{
    UnpicklerObject *self;

    self = ( (UnpicklerObject *) _PyObject_GC_New(&Unpickler_Type) );
    if (self == ((void *)0))
        return ((void *)0);

    self->stack = (Pdata *)Pdata_New();
    if (self->stack == ((void *)0)) {
        do { if ( --((PyObject*)(self))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self)))); } while (0);
        return ((void *)0);
    }
    ((__builtin_object_size (&self->buffer, 0) != (size_t) -1) ? __builtin___memset_chk (&self->buffer, 0, sizeof(Py_buffer), __builtin_object_size (&self->buffer, 0)) : __inline_memset_chk (&self->buffer, 0, sizeof(Py_buffer)));

    self->memo_size = 32;
    self->memo = _Unpickler_NewMemo(self->memo_size);
    if (self->memo == ((void *)0)) {
        do { if ( --((PyObject*)(self))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self)))); } while (0);
        return ((void *)0);
    }

    self->arg = ((void *)0);
    self->pers_func = ((void *)0);
    self->input_buffer = ((void *)0);
    self->input_line = ((void *)0);
    self->input_len = 0;
    self->next_read_idx = 0;
    self->prefetched_idx = 0;
    self->read = ((void *)0);
    self->readline = ((void *)0);
    self->peek = ((void *)0);
    self->encoding = ((void *)0);
    self->errors = ((void *)0);
    self->marks = ((void *)0);
    self->num_marks = 0;
    self->marks_size = 0;
    self->proto = 0;
    self->fix_imports = 0;

    return self;
}



static int
_Unpickler_SetInputStream(UnpicklerObject *self, PyObject *file)
{
    static _Py_Identifier PyId_peek = { 0, "peek", 0 };
    static _Py_Identifier PyId_read = { 0, "read", 0 };
    static _Py_Identifier PyId_readline = { 0, "readline", 0 };

    self->peek = _PyObject_GetAttrId(file, &PyId_peek);
    if (self->peek == ((void *)0)) {
        if (PyErr_ExceptionMatches(PyExc_AttributeError))
            PyErr_Clear();
        else
            return -1;
    }
    self->read = _PyObject_GetAttrId(file, &PyId_read);
    self->readline = _PyObject_GetAttrId(file, &PyId_readline);
    if (self->readline == ((void *)0) || self->read == ((void *)0)) {
        if (PyErr_ExceptionMatches(PyExc_AttributeError))
            PyErr_SetString(PyExc_TypeError,
                            "file must have 'read' and 'readline' attributes");
        do { if (self->read) { PyObject *_py_tmp = (PyObject *)(self->read); (self->read) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
        do { if (self->readline) { PyObject *_py_tmp = (PyObject *)(self->readline); (self->readline) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
        do { if (self->peek) { PyObject *_py_tmp = (PyObject *)(self->peek); (self->peek) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
        return -1;
    }
    return 0;
}



static int
_Unpickler_SetInputEncoding(UnpicklerObject *self,
                            const char *encoding,
                            const char *errors)
{
    if (encoding == ((void *)0))
        encoding = "ASCII";
    if (errors == ((void *)0))
        errors = "strict";

    self->encoding = strdup(encoding);
    self->errors = strdup(errors);
    if (self->encoding == ((void *)0) || self->errors == ((void *)0)) {
        PyErr_NoMemory();
        return -1;
    }
    return 0;
}


static int
memo_get(PicklerObject *self, PyObject *key)
{
    Py_ssize_t *value;
    char pdata[30];
    Py_ssize_t len;

    value = PyMemoTable_Get(self->memo, key);
    if (value == ((void *)0)) {
        PyErr_SetObject(PyExc_KeyError, key);
        return -1;
    }

    if (!self->bin) {
        pdata[0] = GET;
        PyOS_snprintf(pdata + 1, sizeof(pdata) - 1,
                      "%" "l" "d\n", *value);
        len = strlen(pdata);
    }
    else {
        if (*value < 256) {
            pdata[0] = BINGET;
            pdata[1] = (unsigned char)(*value & 0xff);
            len = 2;
        }
        else if (*value <= 0xffffffffL) {
            pdata[0] = LONG_BINGET;
            pdata[1] = (unsigned char)(*value & 0xff);
            pdata[2] = (unsigned char)((*value >> 8) & 0xff);
            pdata[3] = (unsigned char)((*value >> 16) & 0xff);
            pdata[4] = (unsigned char)((*value >> 24) & 0xff);
            len = 5;
        }
        else {
            PyErr_SetString(PicklingError,
                            "memo id too large for LONG_BINGET");
            return -1;
        }
    }

    if (_Pickler_Write(self, pdata, len) < 0)
        return -1;

    return 0;
}



static int
memo_put(PicklerObject *self, PyObject *obj)
{
    Py_ssize_t x;
    char pdata[30];
    Py_ssize_t len;
    int status = 0;

    if (self->fast)
        return 0;

    x = PyMemoTable_Size(self->memo);
    if (PyMemoTable_Set(self->memo, obj, x) < 0)
        goto error;

    if (!self->bin) {
        pdata[0] = PUT;
        PyOS_snprintf(pdata + 1, sizeof(pdata) - 1,
                      "%" "l" "d\n", x);
        len = strlen(pdata);
    }
    else {
        if (x < 256) {
            pdata[0] = BINPUT;
            pdata[1] = (unsigned char)x;
            len = 2;
        }
        else if (x <= 0xffffffffL) {
            pdata[0] = LONG_BINPUT;
            pdata[1] = (unsigned char)(x & 0xff);
            pdata[2] = (unsigned char)((x >> 8) & 0xff);
            pdata[3] = (unsigned char)((x >> 16) & 0xff);
            pdata[4] = (unsigned char)((x >> 24) & 0xff);
            len = 5;
        }
        else {
            PyErr_SetString(PicklingError,
                            "memo id too large for LONG_BINPUT");
            return -1;
        }
    }

    if (_Pickler_Write(self, pdata, len) < 0)
        goto error;

    if (0) {
  error:
        status = -1;
    }

    return status;
}

static PyObject *
whichmodule(PyObject *global, PyObject *global_name)
{
    Py_ssize_t i, j;
    static PyObject *module_str = ((void *)0);
    static PyObject *main_str = ((void *)0);
    PyObject *module_name;
    PyObject *modules_dict;
    PyObject *module;
    PyObject *obj;

    if (module_str == ((void *)0)) {
        module_str = PyUnicode_InternFromString("__module__");
        if (module_str == ((void *)0))
            return ((void *)0);
        main_str = PyUnicode_InternFromString("__main__");
        if (main_str == ((void *)0))
            return ((void *)0);
    }

    module_name = PyObject_GetAttr(global, module_str);




    if (module_name == (&_Py_NoneStruct)) {
        do { if ( --((PyObject*)(module_name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(module_name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(module_name)))); } while (0);
        goto search;
    }

    if (module_name) {
        return module_name;
    }
    if (PyErr_ExceptionMatches(PyExc_AttributeError))
        PyErr_Clear();
    else
        return ((void *)0);

  search:
    modules_dict = PySys_GetObject("modules");
    if (modules_dict == ((void *)0))
        return ((void *)0);

    i = 0;
    module_name = ((void *)0);
    while ((j = PyDict_Next(modules_dict, &i, &module_name, &module))) {
        if (PyObject_RichCompareBool(module_name, main_str, 2) == 1)
            continue;

        obj = PyObject_GetAttr(module, global_name);
        if (obj == ((void *)0)) {
            if (PyErr_ExceptionMatches(PyExc_AttributeError))
                PyErr_Clear();
            else
                return ((void *)0);
            continue;
        }

        if (obj != global) {
            do { if ( --((PyObject*)(obj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(obj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(obj)))); } while (0);
            continue;
        }

        do { if ( --((PyObject*)(obj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(obj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(obj)))); } while (0);
        break;
    }


    if (!j) {
        module_name = main_str;
    }

    ( ((PyObject*)(module_name))->ob_refcnt++);
    return module_name;
}
# 1411 "_pickle.c"
static int
fast_save_enter(PicklerObject *self, PyObject *obj)
{

    if (++self->fast_nesting >= FAST_NESTING_LIMIT) {
        PyObject *key = ((void *)0);
        if (self->fast_memo == ((void *)0)) {
            self->fast_memo = PyDict_New();
            if (self->fast_memo == ((void *)0)) {
                self->fast_nesting = -1;
                return 0;
            }
        }
        key = PyLong_FromVoidPtr(obj);
        if (key == ((void *)0))
            return 0;
        if (PyDict_GetItem(self->fast_memo, key)) {
            do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
            PyErr_Format(PyExc_ValueError,
                         "fast mode: can't pickle cyclic objects "
                         "including object type %.200s at %p",
                         obj->ob_type->tp_name, obj);
            self->fast_nesting = -1;
            return 0;
        }
        if (PyDict_SetItem(self->fast_memo, key, (&_Py_NoneStruct)) < 0) {
            do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
            self->fast_nesting = -1;
            return 0;
        }
        do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
    }
    return 1;
}

static int
fast_save_leave(PicklerObject *self, PyObject *obj)
{
    if (self->fast_nesting-- >= FAST_NESTING_LIMIT) {
        PyObject *key = PyLong_FromVoidPtr(obj);
        if (key == ((void *)0))
            return 0;
        if (PyDict_DelItem(self->fast_memo, key) < 0) {
            do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
            return 0;
        }
        do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
    }
    return 1;
}

static int
save_none(PicklerObject *self, PyObject *obj)
{
    const char none_op = NONE;
    if (_Pickler_Write(self, &none_op, 1) < 0)
        return -1;

    return 0;
}

static int
save_bool(PicklerObject *self, PyObject *obj)
{
    static const char *buf[2] = { "I00\n", "I01\n" };
    const char len[2] = {sizeof("I00\n") - 1, sizeof("I01\n") - 1};
    int p = (obj == ((PyObject *) &_Py_TrueStruct));

    if (self->proto >= 2) {
        const char bool_op = p ? NEWTRUE : NEWFALSE;
        if (_Pickler_Write(self, &bool_op, 1) < 0)
            return -1;
    }
    else if (_Pickler_Write(self, buf[p], len[p]) < 0)
        return -1;

    return 0;
}

static int
save_int(PicklerObject *self, long x)
{
    char pdata[32];
    Py_ssize_t len = 0;

    if (!self->bin

        || x > 0x7fffffffL || x < -0x80000000L

        ) {



        pdata[0] = LONG;
        PyOS_snprintf(pdata + 1, sizeof(pdata) - 1, "%ldL\n", x);
        if (_Pickler_Write(self, pdata, strlen(pdata)) < 0)
            return -1;
    }
    else {

        pdata[1] = (unsigned char)(x & 0xff);
        pdata[2] = (unsigned char)((x >> 8) & 0xff);
        pdata[3] = (unsigned char)((x >> 16) & 0xff);
        pdata[4] = (unsigned char)((x >> 24) & 0xff);

        if ((pdata[4] == 0) && (pdata[3] == 0)) {
            if (pdata[2] == 0) {
                pdata[0] = BININT1;
                len = 2;
            }
            else {
                pdata[0] = BININT2;
                len = 3;
            }
        }
        else {
            pdata[0] = BININT;
            len = 5;
        }

        if (_Pickler_Write(self, pdata, len) < 0)
            return -1;
    }

    return 0;
}

static int
save_long(PicklerObject *self, PyObject *obj)
{
    PyObject *repr = ((void *)0);
    Py_ssize_t size;
    long val = PyLong_AsLong(obj);
    int status = 0;

    const char long_op = LONG;

    if (val == -1 && PyErr_Occurred()) {

        PyErr_Clear();
    }
    else

        if (val <= 0x7fffffffL && val >= -0x80000000L)

            return save_int(self, val);

    if (self->proto >= 2) {

        size_t nbits;
        size_t nbytes;
        unsigned char *pdata;
        char header[5];
        int i;
        int sign = _PyLong_Sign(obj);

        if (sign == 0) {
            header[0] = LONG1;
            header[1] = 0;
            if (_Pickler_Write(self, header, 2) < 0)
                goto error;
            return 0;
        }
        nbits = _PyLong_NumBits(obj);
        if (nbits == (size_t)-1 && PyErr_Occurred())
            goto error;
# 1591 "_pickle.c"
        nbytes = (nbits >> 3) + 1;
        if (nbytes > 0x7fffffffL) {
            PyErr_SetString(PyExc_OverflowError,
                            "long too large to pickle");
            goto error;
        }
        repr = PyBytes_FromStringAndSize(((void *)0), (Py_ssize_t)nbytes);
        if (repr == ((void *)0))
            goto error;
        pdata = (unsigned char *)((__builtin_expect(!(((((((PyObject*)(repr))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 1600, "PyBytes_Check(repr)") : (void)0), (((PyBytesObject *)(repr))->ob_sval));
        i = _PyLong_AsByteArray((PyLongObject *)obj,
                                pdata, nbytes,
                                1 , 1 );
        if (i < 0)
            goto error;




        if (sign < 0 &&
            nbytes > 1 &&
            pdata[nbytes - 1] == 0xff &&
            (pdata[nbytes - 2] & 0x80) != 0) {
            nbytes--;
        }

        if (nbytes < 256) {
            header[0] = LONG1;
            header[1] = (unsigned char)nbytes;
            size = 2;
        }
        else {
            header[0] = LONG4;
            size = (Py_ssize_t) nbytes;
            for (i = 1; i < 5; i++) {
                header[i] = (unsigned char)(size & 0xff);
                size >>= 8;
            }
            size = 5;
        }
        if (_Pickler_Write(self, header, size) < 0 ||
            _Pickler_Write(self, (char *)pdata, (int)nbytes) < 0)
            goto error;
    }
    else {
        char *string;





        repr = PyObject_Repr(obj);
        if (repr == ((void *)0))
            goto error;

        string = PyUnicode_AsUTF8AndSize(repr, &size);
        if (string == ((void *)0))
            goto error;

        if (_Pickler_Write(self, &long_op, 1) < 0 ||
            _Pickler_Write(self, string, size) < 0 ||
            _Pickler_Write(self, "L\n", 2) < 0)
            goto error;
    }

    if (0) {
  error:
      status = -1;
    }
    do { if ((repr) == ((void *)0)) ; else do { if ( --((PyObject*)(repr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(repr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(repr)))); } while (0); } while (0);

    return status;
}

static int
save_float(PicklerObject *self, PyObject *obj)
{
    double x = (((PyFloatObject *)((PyFloatObject *)obj))->ob_fval);

    if (self->bin) {
        char pdata[9];
        pdata[0] = BINFLOAT;
        if (_PyFloat_Pack8(x, (unsigned char *)&pdata[1], 0) < 0)
            return -1;
        if (_Pickler_Write(self, pdata, 9) < 0)
            return -1;
   }
    else {
        int result = -1;
        char *buf = ((void *)0);
        char op = FLOAT;

        if (_Pickler_Write(self, &op, 1) < 0)
            goto done;

        buf = PyOS_double_to_string(x, 'g', 17, 0, ((void *)0));
        if (!buf) {
            PyErr_NoMemory();
            goto done;
        }

        if (_Pickler_Write(self, buf, strlen(buf)) < 0)
            goto done;

        if (_Pickler_Write(self, "\n", 1) < 0)
            goto done;

        result = 0;
done:
        PyMem_Free(buf);
        return result;
    }

    return 0;
}

static int
save_bytes(PicklerObject *self, PyObject *obj)
{
    if (self->proto < 3) {
# 1722 "_pickle.c"
        static PyObject *codecs_encode = ((void *)0);
        PyObject *reduce_value = ((void *)0);
        int status;

        if (codecs_encode == ((void *)0)) {
            PyObject *codecs_module = PyImport_ImportModule("codecs");
            if (codecs_module == ((void *)0)) {
                return -1;
            }
            codecs_encode = PyObject_GetAttrString(codecs_module, "encode");
            do { if ( --((PyObject*)(codecs_module))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(codecs_module)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(codecs_module)))); } while (0);
            if (codecs_encode == ((void *)0)) {
                return -1;
            }
        }

        if (((__builtin_expect(!(((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 1738, "PyBytes_Check(obj)") : (void)0),(((PyVarObject*)(obj))->ob_size)) == 0) {
            reduce_value = Py_BuildValue("(O())", (PyObject*)&PyBytes_Type);
        }
        else {
            static PyObject *latin1 = ((void *)0);
            PyObject *unicode_str =
                PyUnicode_DecodeLatin1(((__builtin_expect(!(((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 1744, "PyBytes_Check(obj)") : (void)0), (((PyBytesObject *)(obj))->ob_sval)),
                                       ((__builtin_expect(!(((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 1745, "PyBytes_Check(obj)") : (void)0),(((PyVarObject*)(obj))->ob_size)),
                                       "strict");
            if (unicode_str == ((void *)0))
                return -1;
            if (latin1 == ((void *)0)) {
                latin1 = PyUnicode_InternFromString("latin1");
                if (latin1 == ((void *)0))
                    return -1;
            }
            reduce_value = Py_BuildValue("(O(OO))",
                                         codecs_encode, unicode_str, latin1);
            do { if ( --((PyObject*)(unicode_str))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(unicode_str)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(unicode_str)))); } while (0);
        }

        if (reduce_value == ((void *)0))
            return -1;


        status = save_reduce(self, reduce_value, obj);
        do { if ( --((PyObject*)(reduce_value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(reduce_value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(reduce_value)))); } while (0);
        return status;
    }
    else {
        Py_ssize_t size;
        char header[5];
        Py_ssize_t len;

        size = ((__builtin_expect(!(((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 1772, "PyBytes_Check(obj)") : (void)0),(((PyVarObject*)(obj))->ob_size));
        if (size < 0)
            return -1;

        if (size < 256) {
            header[0] = SHORT_BINBYTES;
            header[1] = (unsigned char)size;
            len = 2;
        }
        else if (size <= 0xffffffffL) {
            header[0] = BINBYTES;
            header[1] = (unsigned char)(size & 0xff);
            header[2] = (unsigned char)((size >> 8) & 0xff);
            header[3] = (unsigned char)((size >> 16) & 0xff);
            header[4] = (unsigned char)((size >> 24) & 0xff);
            len = 5;
        }
        else {
            PyErr_SetString(PyExc_OverflowError,
                            "cannot serialize a bytes object larger than 4 GiB");
            return -1;
        }

        if (_Pickler_Write(self, header, len) < 0)
            return -1;

        if (_Pickler_Write(self, ((__builtin_expect(!(((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 1798, "PyBytes_Check(obj)") : (void)0), (((PyBytesObject *)(obj))->ob_sval)), size) < 0)
            return -1;

        if (memo_put(self, obj) < 0)
            return -1;

        return 0;
    }
}



static PyObject *
raw_unicode_escape(PyObject *obj)
{
    PyObject *repr, *result;
    char *p;
    Py_ssize_t i, size, expandsize;
    void *data;
    unsigned int kind;

    if (((__builtin_expect(!(((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 1819, "PyUnicode_Check(obj)") : (void)0), ((((PyASCIIObject*)obj)->state.ready) ? 0 : _PyUnicode_Ready((PyObject *)(obj)))))
        return ((void *)0);

    size = ((__builtin_expect(!(((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 1822, "PyUnicode_Check(obj)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)obj)->state.ready)), 0) ? __assert_rtn(__func__, "_pickle.c", 1822, "PyUnicode_IS_READY(obj)") : (void)0), ((PyASCIIObject *)(obj))->length);
    data = ((__builtin_expect(!(((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 1823, "PyUnicode_Check(obj)") : (void)0), (((PyASCIIObject*)(obj))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 1823, "PyUnicode_Check(obj)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)obj)->state.ready)), 0) ? __assert_rtn(__func__, "_pickle.c", 1823, "PyUnicode_IS_READY(obj)") : (void)0), ((PyASCIIObject*)obj)->state.ascii) ? ((void*)((PyASCIIObject*)(obj) + 1)) : ((void*)((PyCompactUnicodeObject*)(obj) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)(obj))->data.any), 0) ? __assert_rtn(__func__, "_pickle.c", 1823, "((PyUnicodeObject*)(obj))->data.any") : (void)0), ((((PyUnicodeObject *)(obj))->data.any))));
    kind = ((__builtin_expect(!(((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 1824, "PyUnicode_Check(obj)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)obj)->state.ready)), 0) ? __assert_rtn(__func__, "_pickle.c", 1824, "PyUnicode_IS_READY(obj)") : (void)0), ((PyASCIIObject *)(obj))->state.kind);
    if (kind == PyUnicode_4BYTE_KIND)
        expandsize = 10;
    else
        expandsize = 6;

    if (size > ((Py_ssize_t)(((size_t)-1)>>1)) / expandsize)
        return PyErr_NoMemory();
    repr = PyByteArray_FromStringAndSize(((void *)0), expandsize * size);
    if (repr == ((void *)0))
        return ((void *)0);
    if (size == 0)
        goto done;

    p = ((__builtin_expect(!(((((PyObject*)(repr))->ob_type) == (&PyByteArray_Type) || PyType_IsSubtype((((PyObject*)(repr))->ob_type), (&PyByteArray_Type)))), 0) ? __assert_rtn(__func__, "_pickle.c", 1838, "PyByteArray_Check(repr)") : (void)0), (((PyVarObject*)(repr))->ob_size) ? ((PyByteArrayObject *)(repr))->ob_bytes : _PyByteArray_empty_string);
    for (i=0; i < size; i++) {
        Py_UCS4 ch = ((Py_UCS4) ((kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(data))[(i)] : ((kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(data))[(i)] : ((const Py_UCS4 *)(data))[(i)] ) ));

        if (ch >= 0x10000) {
            *p++ = '\\';
            *p++ = 'U';
            *p++ = Py_hexdigits[(ch >> 28) & 0xf];
            *p++ = Py_hexdigits[(ch >> 24) & 0xf];
            *p++ = Py_hexdigits[(ch >> 20) & 0xf];
            *p++ = Py_hexdigits[(ch >> 16) & 0xf];
            *p++ = Py_hexdigits[(ch >> 12) & 0xf];
            *p++ = Py_hexdigits[(ch >> 8) & 0xf];
            *p++ = Py_hexdigits[(ch >> 4) & 0xf];
            *p++ = Py_hexdigits[ch & 15];
        }

        else if (ch >= 256 || ch == '\\' || ch == '\n') {
            *p++ = '\\';
            *p++ = 'u';
            *p++ = Py_hexdigits[(ch >> 12) & 0xf];
            *p++ = Py_hexdigits[(ch >> 8) & 0xf];
            *p++ = Py_hexdigits[(ch >> 4) & 0xf];
            *p++ = Py_hexdigits[ch & 15];
        }

        else
            *p++ = (char) ch;
    }
    size = p - ((__builtin_expect(!(((((PyObject*)(repr))->ob_type) == (&PyByteArray_Type) || PyType_IsSubtype((((PyObject*)(repr))->ob_type), (&PyByteArray_Type)))), 0) ? __assert_rtn(__func__, "_pickle.c", 1867, "PyByteArray_Check(repr)") : (void)0), (((PyVarObject*)(repr))->ob_size) ? ((PyByteArrayObject *)(repr))->ob_bytes : _PyByteArray_empty_string);

done:
    result = PyBytes_FromStringAndSize(((__builtin_expect(!(((((PyObject*)(repr))->ob_type) == (&PyByteArray_Type) || PyType_IsSubtype((((PyObject*)(repr))->ob_type), (&PyByteArray_Type)))), 0) ? __assert_rtn(__func__, "_pickle.c", 1870, "PyByteArray_Check(repr)") : (void)0), (((PyVarObject*)(repr))->ob_size) ? ((PyByteArrayObject *)(repr))->ob_bytes : _PyByteArray_empty_string), size);
    do { if ( --((PyObject*)(repr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(repr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(repr)))); } while (0);
    return result;
}

static int
save_unicode(PicklerObject *self, PyObject *obj)
{
    Py_ssize_t size;
    PyObject *encoded = ((void *)0);

    if (self->bin) {
        char pdata[5];

        encoded = PyUnicode_AsEncodedString(obj, "utf-8", "surrogatepass");
        if (encoded == ((void *)0))
            goto error;

        size = ((__builtin_expect(!(((((((PyObject*)(encoded))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 1888, "PyBytes_Check(encoded)") : (void)0),(((PyVarObject*)(encoded))->ob_size));
        if (size > 0xffffffffL) {
            PyErr_SetString(PyExc_OverflowError,
                            "cannot serialize a string larger than 4 GiB");
            goto error;
        }

        pdata[0] = BINUNICODE;
        pdata[1] = (unsigned char)(size & 0xff);
        pdata[2] = (unsigned char)((size >> 8) & 0xff);
        pdata[3] = (unsigned char)((size >> 16) & 0xff);
        pdata[4] = (unsigned char)((size >> 24) & 0xff);

        if (_Pickler_Write(self, pdata, 5) < 0)
            goto error;

        if (_Pickler_Write(self, ((__builtin_expect(!(((((((PyObject*)(encoded))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 1904, "PyBytes_Check(encoded)") : (void)0), (((PyBytesObject *)(encoded))->ob_sval)), size) < 0)
            goto error;
    }
    else {
        const char unicode_op = UNICODE;

        encoded = raw_unicode_escape(obj);
        if (encoded == ((void *)0))
            goto error;

        if (_Pickler_Write(self, &unicode_op, 1) < 0)
            goto error;

        size = ((__builtin_expect(!(((((((PyObject*)(encoded))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 1917, "PyBytes_Check(encoded)") : (void)0),(((PyVarObject*)(encoded))->ob_size));
        if (_Pickler_Write(self, ((__builtin_expect(!(((((((PyObject*)(encoded))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 1918, "PyBytes_Check(encoded)") : (void)0), (((PyBytesObject *)(encoded))->ob_sval)), size) < 0)
            goto error;

        if (_Pickler_Write(self, "\n", 1) < 0)
            goto error;
    }
    if (memo_put(self, obj) < 0)
        goto error;

    do { if ( --((PyObject*)(encoded))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(encoded)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(encoded)))); } while (0);
    return 0;

  error:
    do { if ((encoded) == ((void *)0)) ; else do { if ( --((PyObject*)(encoded))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(encoded)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(encoded)))); } while (0); } while (0);
    return -1;
}


static int
store_tuple_elements(PicklerObject *self, PyObject *t, Py_ssize_t len)
{
    Py_ssize_t i;

    (__builtin_expect(!(PyTuple_Size(t) == len), 0) ? __assert_rtn(__func__, "_pickle.c", 1941, "PyTuple_Size(t) == len") : (void)0);

    for (i = 0; i < len; i++) {
        PyObject *element = (((PyTupleObject *)(t))->ob_item[i]);

        if (element == ((void *)0))
            return -1;
        if (save(self, element, 0) < 0)
            return -1;
    }

    return 0;
}







static int
save_tuple(PicklerObject *self, PyObject *obj)
{
    Py_ssize_t len, i;

    const char mark_op = MARK;
    const char tuple_op = TUPLE;
    const char pop_op = POP;
    const char pop_mark_op = POP_MARK;
    const char len2opcode[] = {EMPTY_TUPLE, TUPLE1, TUPLE2, TUPLE3};

    if ((len = PyTuple_Size(obj)) < 0)
        return -1;

    if (len == 0) {
        char pdata[2];

        if (self->proto) {
            pdata[0] = EMPTY_TUPLE;
            len = 1;
        }
        else {
            pdata[0] = MARK;
            pdata[1] = TUPLE;
            len = 2;
        }
        if (_Pickler_Write(self, pdata, len) < 0)
            return -1;
        return 0;
    }






    if (len <= 3 && self->proto >= 2) {

        if (store_tuple_elements(self, obj, len) < 0)
            return -1;

        if (PyMemoTable_Get(self->memo, obj)) {

            for (i = 0; i < len; i++)
                if (_Pickler_Write(self, &pop_op, 1) < 0)
                    return -1;

            if (memo_get(self, obj) < 0)
                return -1;

            return 0;
        }
        else {
            if (_Pickler_Write(self, len2opcode + len, 1) < 0)
                return -1;
        }
        goto memoize;
    }




    if (_Pickler_Write(self, &mark_op, 1) < 0)
        return -1;

    if (store_tuple_elements(self, obj, len) < 0)
        return -1;

    if (PyMemoTable_Get(self->memo, obj)) {

        if (self->bin) {
            if (_Pickler_Write(self, &pop_mark_op, 1) < 0)
                return -1;
        }
        else {



            for (i = 0; i <= len; i++)
                if (_Pickler_Write(self, &pop_op, 1) < 0)
                    return -1;
        }

        if (memo_get(self, obj) < 0)
            return -1;

        return 0;
    }
    else {
        if (_Pickler_Write(self, &tuple_op, 1) < 0)
            return -1;
    }

  memoize:
    if (memo_put(self, obj) < 0)
        return -1;

    return 0;
}







static int
batch_list(PicklerObject *self, PyObject *iter)
{
    PyObject *obj = ((void *)0);
    PyObject *firstitem = ((void *)0);
    int i, n;

    const char mark_op = MARK;
    const char append_op = APPEND;
    const char appends_op = APPENDS;

    (__builtin_expect(!(iter != ((void *)0)), 0) ? __assert_rtn(__func__, "_pickle.c", 2078, "iter != NULL") : (void)0);






    if (self->proto == 0) {

        for (;;) {
            obj = PyIter_Next(iter);
            if (obj == ((void *)0)) {
                if (PyErr_Occurred())
                    return -1;
                break;
            }
            i = save(self, obj, 0);
            do { if ( --((PyObject*)(obj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(obj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(obj)))); } while (0);
            if (i < 0)
                return -1;
            if (_Pickler_Write(self, &append_op, 1) < 0)
                return -1;
        }
        return 0;
    }


    do {

        firstitem = PyIter_Next(iter);
        if (firstitem == ((void *)0)) {
            if (PyErr_Occurred())
                goto error;


            break;
        }


        obj = PyIter_Next(iter);
        if (obj == ((void *)0)) {
            if (PyErr_Occurred())
                goto error;


            if (save(self, firstitem, 0) < 0)
                goto error;
            if (_Pickler_Write(self, &append_op, 1) < 0)
                goto error;
            do { if (firstitem) { PyObject *_py_tmp = (PyObject *)(firstitem); (firstitem) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
            break;
        }




        if (_Pickler_Write(self, &mark_op, 1) < 0)
            goto error;

        if (save(self, firstitem, 0) < 0)
            goto error;
        do { if (firstitem) { PyObject *_py_tmp = (PyObject *)(firstitem); (firstitem) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
        n = 1;


        while (obj) {
            if (save(self, obj, 0) < 0)
                goto error;
            do { if (obj) { PyObject *_py_tmp = (PyObject *)(obj); (obj) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
            n += 1;

            if (n == BATCHSIZE)
                break;

            obj = PyIter_Next(iter);
            if (obj == ((void *)0)) {
                if (PyErr_Occurred())
                    goto error;
                break;
            }
        }

        if (_Pickler_Write(self, &appends_op, 1) < 0)
            goto error;

    } while (n == BATCHSIZE);
    return 0;

  error:
    do { if ((firstitem) == ((void *)0)) ; else do { if ( --((PyObject*)(firstitem))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(firstitem)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(firstitem)))); } while (0); } while (0);
    do { if ((obj) == ((void *)0)) ; else do { if ( --((PyObject*)(obj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(obj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(obj)))); } while (0); } while (0);
    return -1;
}
# 2183 "_pickle.c"
static int
batch_list_exact(PicklerObject *self, PyObject *obj)
{
    PyObject *item = ((void *)0);
    Py_ssize_t this_batch, total;

    const char append_op = APPEND;
    const char appends_op = APPENDS;
    const char mark_op = MARK;

    (__builtin_expect(!(obj != ((void *)0)), 0) ? __assert_rtn(__func__, "_pickle.c", 2193, "obj != NULL") : (void)0);
    (__builtin_expect(!(self->proto > 0), 0) ? __assert_rtn(__func__, "_pickle.c", 2194, "self->proto > 0") : (void)0);
    (__builtin_expect(!(((((PyObject*)(obj))->ob_type) == &PyList_Type)), 0) ? __assert_rtn(__func__, "_pickle.c", 2195, "PyList_CheckExact(obj)") : (void)0);

    if ((((PyVarObject*)(obj))->ob_size) == 1) {
        item = (((PyListObject *)(obj))->ob_item[0]);
        if (save(self, item, 0) < 0)
            return -1;
        if (_Pickler_Write(self, &append_op, 1) < 0)
            return -1;
        return 0;
    }


    total = 0;
    do {
        this_batch = 0;
        if (_Pickler_Write(self, &mark_op, 1) < 0)
            return -1;
        while (total < (((PyVarObject*)(obj))->ob_size)) {
            item = (((PyListObject *)(obj))->ob_item[total]);
            if (save(self, item, 0) < 0)
                return -1;
            total++;
            if (++this_batch == BATCHSIZE)
                break;
        }
        if (_Pickler_Write(self, &appends_op, 1) < 0)
            return -1;

    } while (total < (((PyVarObject*)(obj))->ob_size));

    return 0;
}

static int
save_list(PicklerObject *self, PyObject *obj)
{
    char header[3];
    Py_ssize_t len;
    int status = 0;

    if (self->fast && !fast_save_enter(self, obj))
        goto error;


    if (self->bin) {
        header[0] = EMPTY_LIST;
        len = 1;
    }
    else {
        header[0] = MARK;
        header[1] = LIST;
        len = 2;
    }

    if (_Pickler_Write(self, header, len) < 0)
        goto error;


    if ((len = PyList_Size(obj)) < 0)
        goto error;

    if (memo_put(self, obj) < 0)
        goto error;

    if (len != 0) {

        if (((((PyObject*)(obj))->ob_type) == &PyList_Type) && self->proto > 0) {
            if (((++(((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->recursion_depth) > _Py_CheckRecursionLimit) && _Py_CheckRecursiveCall(" while pickling an object")))
                goto error;
            status = batch_list_exact(self, obj);
            do{ if((--(((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->recursion_depth) < ((_Py_CheckRecursionLimit > 100) ? (_Py_CheckRecursionLimit - 50) : (3 * (_Py_CheckRecursionLimit >> 2))))) ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->overflowed = 0; } while(0);
        } else {
            PyObject *iter = PyObject_GetIter(obj);
            if (iter == ((void *)0))
                goto error;

            if (((++(((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->recursion_depth) > _Py_CheckRecursionLimit) && _Py_CheckRecursiveCall(" while pickling an object"))) {
                do { if ( --((PyObject*)(iter))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(iter)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(iter)))); } while (0);
                goto error;
            }
            status = batch_list(self, iter);
            do{ if((--(((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->recursion_depth) < ((_Py_CheckRecursionLimit > 100) ? (_Py_CheckRecursionLimit - 50) : (3 * (_Py_CheckRecursionLimit >> 2))))) ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->overflowed = 0; } while(0);
            do { if ( --((PyObject*)(iter))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(iter)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(iter)))); } while (0);
        }
    }
    if (0) {
  error:
        status = -1;
    }

    if (self->fast && !fast_save_leave(self, obj))
        status = -1;

    return status;
}
# 2302 "_pickle.c"
static int
batch_dict(PicklerObject *self, PyObject *iter)
{
    PyObject *obj = ((void *)0);
    PyObject *firstitem = ((void *)0);
    int i, n;

    const char mark_op = MARK;
    const char setitem_op = SETITEM;
    const char setitems_op = SETITEMS;

    (__builtin_expect(!(iter != ((void *)0)), 0) ? __assert_rtn(__func__, "_pickle.c", 2313, "iter != NULL") : (void)0);

    if (self->proto == 0) {

        for (;;) {
            obj = PyIter_Next(iter);
            if (obj == ((void *)0)) {
                if (PyErr_Occurred())
                    return -1;
                break;
            }
            if (!((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<26))) != 0) || PyTuple_Size(obj) != 2) {
                PyErr_SetString(PyExc_TypeError, "dict items "
                                "iterator must return 2-tuples");
                return -1;
            }
            i = save(self, (((PyTupleObject *)(obj))->ob_item[0]), 0);
            if (i >= 0)
                i = save(self, (((PyTupleObject *)(obj))->ob_item[1]), 0);
            do { if ( --((PyObject*)(obj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(obj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(obj)))); } while (0);
            if (i < 0)
                return -1;
            if (_Pickler_Write(self, &setitem_op, 1) < 0)
                return -1;
        }
        return 0;
    }


    do {

        firstitem = PyIter_Next(iter);
        if (firstitem == ((void *)0)) {
            if (PyErr_Occurred())
                goto error;


            break;
        }
        if (!((((((PyObject*)(firstitem))->ob_type))->tp_flags & ((1L<<26))) != 0) || PyTuple_Size(firstitem) != 2) {
            PyErr_SetString(PyExc_TypeError, "dict items "
                                "iterator must return 2-tuples");
            goto error;
        }


        obj = PyIter_Next(iter);
        if (obj == ((void *)0)) {
            if (PyErr_Occurred())
                goto error;


            if (save(self, (((PyTupleObject *)(firstitem))->ob_item[0]), 0) < 0)
                goto error;
            if (save(self, (((PyTupleObject *)(firstitem))->ob_item[1]), 0) < 0)
                goto error;
            if (_Pickler_Write(self, &setitem_op, 1) < 0)
                goto error;
            do { if (firstitem) { PyObject *_py_tmp = (PyObject *)(firstitem); (firstitem) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
            break;
        }




        if (_Pickler_Write(self, &mark_op, 1) < 0)
            goto error;

        if (save(self, (((PyTupleObject *)(firstitem))->ob_item[0]), 0) < 0)
            goto error;
        if (save(self, (((PyTupleObject *)(firstitem))->ob_item[1]), 0) < 0)
            goto error;
        do { if (firstitem) { PyObject *_py_tmp = (PyObject *)(firstitem); (firstitem) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
        n = 1;


        while (obj) {
            if (!((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<26))) != 0) || PyTuple_Size(obj) != 2) {
                PyErr_SetString(PyExc_TypeError, "dict items "
                    "iterator must return 2-tuples");
                goto error;
            }
            if (save(self, (((PyTupleObject *)(obj))->ob_item[0]), 0) < 0 ||
                save(self, (((PyTupleObject *)(obj))->ob_item[1]), 0) < 0)
                goto error;
            do { if (obj) { PyObject *_py_tmp = (PyObject *)(obj); (obj) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
            n += 1;

            if (n == BATCHSIZE)
                break;

            obj = PyIter_Next(iter);
            if (obj == ((void *)0)) {
                if (PyErr_Occurred())
                    goto error;
                break;
            }
        }

        if (_Pickler_Write(self, &setitems_op, 1) < 0)
            goto error;

    } while (n == BATCHSIZE);
    return 0;

  error:
    do { if ((firstitem) == ((void *)0)) ; else do { if ( --((PyObject*)(firstitem))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(firstitem)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(firstitem)))); } while (0); } while (0);
    do { if ((obj) == ((void *)0)) ; else do { if ( --((PyObject*)(obj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(obj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(obj)))); } while (0); } while (0);
    return -1;
}
# 2433 "_pickle.c"
static int
batch_dict_exact(PicklerObject *self, PyObject *obj)
{
    PyObject *key = ((void *)0), *value = ((void *)0);
    int i;
    Py_ssize_t dict_size, ppos = 0;

    const char mark_op = MARK;
    const char setitem_op = SETITEM;
    const char setitems_op = SETITEMS;

    (__builtin_expect(!(obj != ((void *)0)), 0) ? __assert_rtn(__func__, "_pickle.c", 2444, "obj != NULL") : (void)0);
    (__builtin_expect(!(self->proto > 0), 0) ? __assert_rtn(__func__, "_pickle.c", 2445, "self->proto > 0") : (void)0);

    dict_size = PyDict_Size(obj);


    if (dict_size == 1) {
        PyDict_Next(obj, &ppos, &key, &value);
        if (save(self, key, 0) < 0)
            return -1;
        if (save(self, value, 0) < 0)
            return -1;
        if (_Pickler_Write(self, &setitem_op, 1) < 0)
            return -1;
        return 0;
    }


    do {
        i = 0;
        if (_Pickler_Write(self, &mark_op, 1) < 0)
            return -1;
        while (PyDict_Next(obj, &ppos, &key, &value)) {
            if (save(self, key, 0) < 0)
                return -1;
            if (save(self, value, 0) < 0)
                return -1;
            if (++i == BATCHSIZE)
                break;
        }
        if (_Pickler_Write(self, &setitems_op, 1) < 0)
            return -1;
        if (PyDict_Size(obj) != dict_size) {
            PyErr_Format(
                PyExc_RuntimeError,
                "dictionary changed size during iteration");
            return -1;
        }

    } while (i == BATCHSIZE);
    return 0;
}

static int
save_dict(PicklerObject *self, PyObject *obj)
{
    PyObject *items, *iter;
    char header[3];
    Py_ssize_t len;
    int status = 0;

    if (self->fast && !fast_save_enter(self, obj))
        goto error;


    if (self->bin) {
        header[0] = EMPTY_DICT;
        len = 1;
    }
    else {
        header[0] = MARK;
        header[1] = DICT;
        len = 2;
    }

    if (_Pickler_Write(self, header, len) < 0)
        goto error;


    if ((len = PyDict_Size(obj)) < 0)
        goto error;

    if (memo_put(self, obj) < 0)
        goto error;

    if (len != 0) {

        if (((((PyObject*)(obj))->ob_type) == &PyDict_Type) && self->proto > 0) {


            if (((++(((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->recursion_depth) > _Py_CheckRecursionLimit) && _Py_CheckRecursiveCall(" while pickling an object")))
                goto error;
            status = batch_dict_exact(self, obj);
            do{ if((--(((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->recursion_depth) < ((_Py_CheckRecursionLimit > 100) ? (_Py_CheckRecursionLimit - 50) : (3 * (_Py_CheckRecursionLimit >> 2))))) ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->overflowed = 0; } while(0);
        } else {
            static _Py_Identifier PyId_items = { 0, "items", 0 };

            items = _PyObject_CallMethodId(obj, &PyId_items, "()");
            if (items == ((void *)0))
                goto error;
            iter = PyObject_GetIter(items);
            do { if ( --((PyObject*)(items))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(items)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(items)))); } while (0);
            if (iter == ((void *)0))
                goto error;
            if (((++(((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->recursion_depth) > _Py_CheckRecursionLimit) && _Py_CheckRecursiveCall(" while pickling an object"))) {
                do { if ( --((PyObject*)(iter))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(iter)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(iter)))); } while (0);
                goto error;
            }
            status = batch_dict(self, iter);
            do{ if((--(((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->recursion_depth) < ((_Py_CheckRecursionLimit > 100) ? (_Py_CheckRecursionLimit - 50) : (3 * (_Py_CheckRecursionLimit >> 2))))) ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->overflowed = 0; } while(0);
            do { if ( --((PyObject*)(iter))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(iter)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(iter)))); } while (0);
        }
    }

    if (0) {
  error:
        status = -1;
    }

    if (self->fast && !fast_save_leave(self, obj))
        status = -1;

    return status;
}

static int
save_global(PicklerObject *self, PyObject *obj, PyObject *name)
{
    static PyObject *name_str = ((void *)0);
    PyObject *global_name = ((void *)0);
    PyObject *module_name = ((void *)0);
    PyObject *module = ((void *)0);
    PyObject *cls;
    int status = 0;

    const char global_op = GLOBAL;

    if (name_str == ((void *)0)) {
        name_str = PyUnicode_InternFromString("__name__");
        if (name_str == ((void *)0))
            goto error;
    }

    if (name) {
        global_name = name;
        ( ((PyObject*)(global_name))->ob_refcnt++);
    }
    else {
        global_name = PyObject_GetAttr(obj, name_str);
        if (global_name == ((void *)0))
            goto error;
    }

    module_name = whichmodule(obj, global_name);
    if (module_name == ((void *)0))
        goto error;
# 2599 "_pickle.c"
    module = PyImport_Import(module_name);
    if (module == ((void *)0)) {
        PyErr_Format(PicklingError,
                     "Can't pickle %R: import of module %R failed",
                     obj, module_name);
        goto error;
    }
    cls = PyObject_GetAttr(module, global_name);
    if (cls == ((void *)0)) {
        PyErr_Format(PicklingError,
                     "Can't pickle %R: attribute lookup %S.%S failed",
                     obj, module_name, global_name);
        goto error;
    }
    if (cls != obj) {
        do { if ( --((PyObject*)(cls))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(cls)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(cls)))); } while (0);
        PyErr_Format(PicklingError,
                     "Can't pickle %R: it's not the same object as %S.%S",
                     obj, module_name, global_name);
        goto error;
    }
    do { if ( --((PyObject*)(cls))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(cls)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(cls)))); } while (0);

    if (self->proto >= 2) {



        PyObject *code_obj;
        long code;
        char pdata[5];
        Py_ssize_t n;

        (((PyTupleObject *)(two_tuple))->ob_item[0] = module_name);
        (((PyTupleObject *)(two_tuple))->ob_item[1] = global_name);
        code_obj = PyDict_GetItem(extension_registry, two_tuple);


        if (code_obj == ((void *)0))
            goto gen_global;






        if (!((((((PyObject*)(code_obj))->ob_type))->tp_flags & ((1L<<24))) != 0)) {
            PyErr_Format(PicklingError,
                         "Can't pickle %R: extension code %R isn't an integer",
                         obj, code_obj);
            goto error;
        }
        code = PyLong_AsLong(code_obj);
        if (code <= 0 || code > 0x7fffffffL) {
            if (!PyErr_Occurred())
                PyErr_Format(PicklingError,
                             "Can't pickle %R: extension code %ld is out of range",
                             obj, code);
            goto error;
        }


        if (code <= 0xff) {
            pdata[0] = EXT1;
            pdata[1] = (unsigned char)code;
            n = 2;
        }
        else if (code <= 0xffff) {
            pdata[0] = EXT2;
            pdata[1] = (unsigned char)(code & 0xff);
            pdata[2] = (unsigned char)((code >> 8) & 0xff);
            n = 3;
        }
        else {
            pdata[0] = EXT4;
            pdata[1] = (unsigned char)(code & 0xff);
            pdata[2] = (unsigned char)((code >> 8) & 0xff);
            pdata[3] = (unsigned char)((code >> 16) & 0xff);
            pdata[4] = (unsigned char)((code >> 24) & 0xff);
            n = 5;
        }

        if (_Pickler_Write(self, pdata, n) < 0)
            goto error;
    }
    else {



        PyObject *encoded;
        PyObject *(*unicode_encoder)(PyObject *);

  gen_global:
        if (_Pickler_Write(self, &global_op, 1) < 0)
            goto error;





        if (self->proto >= 3) {
            unicode_encoder = PyUnicode_AsUTF8String;
        }
        else {
            unicode_encoder = PyUnicode_AsASCIIString;
        }



        if (self->fix_imports) {
            PyObject *key;
            PyObject *item;

            key = PyTuple_Pack(2, module_name, global_name);
            if (key == ((void *)0))
                goto error;
            item = PyDict_GetItemWithError(name_mapping_3to2, key);
            do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
            if (item) {
                if (!((((((PyObject*)(item))->ob_type))->tp_flags & ((1L<<26))) != 0) || (((PyVarObject*)(item))->ob_size) != 2) {
                    PyErr_Format(PyExc_RuntimeError,
                                 "_compat_pickle.REVERSE_NAME_MAPPING values "
                                 "should be 2-tuples, not %.200s",
                                 (((PyObject*)(item))->ob_type)->tp_name);
                    goto error;
                }
                do { if (module_name) { PyObject *_py_tmp = (PyObject *)(module_name); (module_name) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
                do { if (global_name) { PyObject *_py_tmp = (PyObject *)(global_name); (global_name) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
                module_name = (((PyTupleObject *)(item))->ob_item[0]);
                global_name = (((PyTupleObject *)(item))->ob_item[1]);
                if (!((((((PyObject*)(module_name))->ob_type))->tp_flags & ((1L<<28))) != 0) ||
                    !((((((PyObject*)(global_name))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
                    PyErr_Format(PyExc_RuntimeError,
                                 "_compat_pickle.REVERSE_NAME_MAPPING values "
                                 "should be pairs of str, not (%.200s, %.200s)",
                                 (((PyObject*)(module_name))->ob_type)->tp_name,
                                 (((PyObject*)(global_name))->ob_type)->tp_name);
                    goto error;
                }
                ( ((PyObject*)(module_name))->ob_refcnt++);
                ( ((PyObject*)(global_name))->ob_refcnt++);
            }
            else if (PyErr_Occurred()) {
                goto error;
            }

            item = PyDict_GetItemWithError(import_mapping_3to2, module_name);
            if (item) {
                if (!((((((PyObject*)(item))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
                    PyErr_Format(PyExc_RuntimeError,
                                 "_compat_pickle.REVERSE_IMPORT_MAPPING values "
                                 "should be strings, not %.200s",
                                 (((PyObject*)(item))->ob_type)->tp_name);
                    goto error;
                }
                do { if (module_name) { PyObject *_py_tmp = (PyObject *)(module_name); (module_name) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
                module_name = item;
                ( ((PyObject*)(module_name))->ob_refcnt++);
            }
            else if (PyErr_Occurred()) {
                goto error;
            }
        }


        encoded = unicode_encoder(module_name);
        if (encoded == ((void *)0)) {
            if (PyErr_ExceptionMatches(PyExc_UnicodeEncodeError))
                PyErr_Format(PicklingError,
                             "can't pickle module identifier '%S' using "
                             "pickle protocol %i", module_name, self->proto);
            goto error;
        }
        if (_Pickler_Write(self, ((__builtin_expect(!(((((((PyObject*)(encoded))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 2771, "PyBytes_Check(encoded)") : (void)0), (((PyBytesObject *)(encoded))->ob_sval)),
                          ((__builtin_expect(!(((((((PyObject*)(encoded))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 2772, "PyBytes_Check(encoded)") : (void)0),(((PyVarObject*)(encoded))->ob_size))) < 0) {
            do { if ( --((PyObject*)(encoded))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(encoded)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(encoded)))); } while (0);
            goto error;
        }
        do { if ( --((PyObject*)(encoded))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(encoded)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(encoded)))); } while (0);
        if(_Pickler_Write(self, "\n", 1) < 0)
            goto error;


        encoded = unicode_encoder(global_name);
        if (encoded == ((void *)0)) {
            if (PyErr_ExceptionMatches(PyExc_UnicodeEncodeError))
                PyErr_Format(PicklingError,
                             "can't pickle global identifier '%S' using "
                             "pickle protocol %i", global_name, self->proto);
            goto error;
        }
        if (_Pickler_Write(self, ((__builtin_expect(!(((((((PyObject*)(encoded))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 2789, "PyBytes_Check(encoded)") : (void)0), (((PyBytesObject *)(encoded))->ob_sval)),
                          ((__builtin_expect(!(((((((PyObject*)(encoded))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 2790, "PyBytes_Check(encoded)") : (void)0),(((PyVarObject*)(encoded))->ob_size))) < 0) {
            do { if ( --((PyObject*)(encoded))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(encoded)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(encoded)))); } while (0);
            goto error;
        }
        do { if ( --((PyObject*)(encoded))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(encoded)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(encoded)))); } while (0);
        if(_Pickler_Write(self, "\n", 1) < 0)
            goto error;


        if (memo_put(self, obj) < 0)
            goto error;
    }

    if (0) {
  error:
        status = -1;
    }
    do { if ((module_name) == ((void *)0)) ; else do { if ( --((PyObject*)(module_name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(module_name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(module_name)))); } while (0); } while (0);
    do { if ((global_name) == ((void *)0)) ; else do { if ( --((PyObject*)(global_name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(global_name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(global_name)))); } while (0); } while (0);
    do { if ((module) == ((void *)0)) ; else do { if ( --((PyObject*)(module))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(module)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(module)))); } while (0); } while (0);

    return status;
}

static int
save_ellipsis(PicklerObject *self, PyObject *obj)
{
    PyObject *str = PyUnicode_FromString("Ellipsis");
    int res;
    if (str == ((void *)0))
        return -1;
    res = save_global(self, (&_Py_EllipsisObject), str);
    do { if ( --((PyObject*)(str))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(str)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(str)))); } while (0);
    return res;
}

static int
save_notimplemented(PicklerObject *self, PyObject *obj)
{
    PyObject *str = PyUnicode_FromString("NotImplemented");
    int res;
    if (str == ((void *)0))
        return -1;
    res = save_global(self, (&_Py_NotImplementedStruct), str);
    do { if ( --((PyObject*)(str))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(str)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(str)))); } while (0);
    return res;
}

static int
save_pers(PicklerObject *self, PyObject *obj, PyObject *func)
{
    PyObject *pid = ((void *)0);
    int status = 0;

    const char persid_op = PERSID;
    const char binpersid_op = BINPERSID;

    ( ((PyObject*)(obj))->ob_refcnt++);
    pid = _Pickler_FastCall(self, func, obj);
    if (pid == ((void *)0))
        return -1;

    if (pid != (&_Py_NoneStruct)) {
        if (self->bin) {
            if (save(self, pid, 1) < 0 ||
                _Pickler_Write(self, &binpersid_op, 1) < 0)
                goto error;
        }
        else {
            PyObject *pid_str = ((void *)0);
            char *pid_ascii_bytes;
            Py_ssize_t size;

            pid_str = PyObject_Str(pid);
            if (pid_str == ((void *)0))
                goto error;




            pid_ascii_bytes = PyUnicode_AsUTF8AndSize(pid_str, &size);
            do { if ( --((PyObject*)(pid_str))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pid_str)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pid_str)))); } while (0);
            if (pid_ascii_bytes == ((void *)0))
                goto error;

            if (_Pickler_Write(self, &persid_op, 1) < 0 ||
                _Pickler_Write(self, pid_ascii_bytes, size) < 0 ||
                _Pickler_Write(self, "\n", 1) < 0)
                goto error;
        }
        status = 1;
    }

    if (0) {
  error:
        status = -1;
    }
    do { if ((pid) == ((void *)0)) ; else do { if ( --((PyObject*)(pid))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pid)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pid)))); } while (0); } while (0);

    return status;
}

static PyObject *
get_class(PyObject *obj)
{
    PyObject *cls;
    static PyObject *str_class;

    if (str_class == ((void *)0)) {
        str_class = PyUnicode_InternFromString("__class__");
        if (str_class == ((void *)0))
            return ((void *)0);
    }
    cls = PyObject_GetAttr(obj, str_class);
    if (cls == ((void *)0)) {
        if (PyErr_ExceptionMatches(PyExc_AttributeError)) {
            PyErr_Clear();
            cls = (PyObject *) (((PyObject*)(obj))->ob_type);
            ( ((PyObject*)(cls))->ob_refcnt++);
        }
    }
    return cls;
}




static int
save_reduce(PicklerObject *self, PyObject *args, PyObject *obj)
{
    PyObject *callable;
    PyObject *argtup;
    PyObject *state = ((void *)0);
    PyObject *listitems = (&_Py_NoneStruct);
    PyObject *dictitems = (&_Py_NoneStruct);
    Py_ssize_t size;

    int use_newobj = self->proto >= 2;

    const char reduce_op = REDUCE;
    const char build_op = BUILD;
    const char newobj_op = NEWOBJ;

    size = PyTuple_Size(args);
    if (size < 2 || size > 5) {
        PyErr_SetString(PicklingError, "tuple returned by "
                        "__reduce__ must contain 2 through 5 elements");
        return -1;
    }

    if (!PyArg_UnpackTuple(args, "save_reduce", 2, 5,
                           &callable, &argtup, &state, &listitems, &dictitems))
        return -1;

    if (!PyCallable_Check(callable)) {
        PyErr_SetString(PicklingError, "first item of the tuple "
                        "returned by __reduce__ must be callable");
        return -1;
    }
    if (!((((((PyObject*)(argtup))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
        PyErr_SetString(PicklingError, "second item of the tuple "
                        "returned by __reduce__ must be a tuple");
        return -1;
    }

    if (state == (&_Py_NoneStruct))
        state = ((void *)0);

    if (listitems == (&_Py_NoneStruct))
        listitems = ((void *)0);
    else if (!((listitems)->ob_type->tp_iternext != ((void *)0) && (listitems)->ob_type->tp_iternext != &_PyObject_NextNotImplemented)) {
        PyErr_Format(PicklingError, "Fourth element of tuple"
                     "returned by __reduce__ must be an iterator, not %s",
                     (((PyObject*)(listitems))->ob_type)->tp_name);
        return -1;
    }

    if (dictitems == (&_Py_NoneStruct))
        dictitems = ((void *)0);
    else if (!((dictitems)->ob_type->tp_iternext != ((void *)0) && (dictitems)->ob_type->tp_iternext != &_PyObject_NextNotImplemented)) {
        PyErr_Format(PicklingError, "Fifth element of tuple"
                     "returned by __reduce__ must be an iterator, not %s",
                     (((PyObject*)(dictitems))->ob_type)->tp_name);
        return -1;
    }



    if (use_newobj) {
        static PyObject *newobj_str = ((void *)0), *name_str = ((void *)0);
        PyObject *name;

        if (newobj_str == ((void *)0)) {
            newobj_str = PyUnicode_InternFromString("__newobj__");
            name_str = PyUnicode_InternFromString("__name__");
            if (newobj_str == ((void *)0) || name_str == ((void *)0))
                return -1;
        }

        name = PyObject_GetAttr(callable, name_str);
        if (name == ((void *)0)) {
            if (PyErr_ExceptionMatches(PyExc_AttributeError))
                PyErr_Clear();
            else
                return -1;
            use_newobj = 0;
        }
        else {
            use_newobj = ((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0) &&
                         PyUnicode_Compare(name, newobj_str) == 0;
            do { if ( --((PyObject*)(name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(name)))); } while (0);
        }
    }
    if (use_newobj) {
        PyObject *cls;
        PyObject *newargtup;
        PyObject *obj_class;
        int p;


        if ((((PyVarObject*)(argtup))->ob_size) < 1) {
            PyErr_SetString(PicklingError, "__newobj__ arglist is empty");
            return -1;
        }

        cls = (((PyTupleObject *)(argtup))->ob_item[0]);
        if (!((((((PyObject*)(cls))->ob_type))->tp_flags & ((1L<<31))) != 0)) {
            PyErr_SetString(PicklingError, "args[0] from "
                            "__newobj__ args is not a type");
            return -1;
        }

        if (obj != ((void *)0)) {
            obj_class = get_class(obj);
            p = obj_class != cls;
            do { if ( --((PyObject*)(obj_class))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(obj_class)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(obj_class)))); } while (0);
            if (p) {
                PyErr_SetString(PicklingError, "args[0] from "
                                "__newobj__ args has the wrong class");
                return -1;
            }
        }
# 3060 "_pickle.c"
        if (save(self, cls, 0) < 0)
            return -1;

        newargtup = PyTuple_GetSlice(argtup, 1, (((PyVarObject*)(argtup))->ob_size));
        if (newargtup == ((void *)0))
            return -1;

        p = save(self, newargtup, 0);
        do { if ( --((PyObject*)(newargtup))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(newargtup)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(newargtup)))); } while (0);
        if (p < 0)
            return -1;


        if (_Pickler_Write(self, &newobj_op, 1) < 0)
            return -1;
    }
    else {
        if (save(self, callable, 0) < 0 ||
            save(self, argtup, 0) < 0 ||
            _Pickler_Write(self, &reduce_op, 1) < 0)
            return -1;
    }





    if (obj && memo_put(self, obj) < 0)
        return -1;

    if (listitems && batch_list(self, listitems) < 0)
        return -1;

    if (dictitems && batch_dict(self, dictitems) < 0)
        return -1;

    if (state) {
        if (save(self, state, 0) < 0 ||
            _Pickler_Write(self, &build_op, 1) < 0)
            return -1;
    }

    return 0;
}

static int
save(PicklerObject *self, PyObject *obj, int pers_save)
{
    PyTypeObject *type;
    PyObject *reduce_func = ((void *)0);
    PyObject *reduce_value = ((void *)0);
    int status = 0;

    if (((++(((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->recursion_depth) > _Py_CheckRecursionLimit) && _Py_CheckRecursiveCall(" while pickling an object")))
        return -1;



    if (!pers_save && self->pers_func) {





        if ((status = save_pers(self, obj, self->pers_func)) != 0)
            goto done;
    }

    type = (((PyObject*)(obj))->ob_type);
# 3137 "_pickle.c"
    if (obj == (&_Py_NoneStruct)) {
        status = save_none(self, obj);
        goto done;
    }
    else if (obj == (&_Py_EllipsisObject)) {
        status = save_ellipsis(self, obj);
        goto done;
    }
    else if (obj == (&_Py_NotImplementedStruct)) {
        status = save_notimplemented(self, obj);
        goto done;
    }
    else if (obj == ((PyObject *) &_Py_FalseStruct) || obj == ((PyObject *) &_Py_TrueStruct)) {
        status = save_bool(self, obj);
        goto done;
    }
    else if (type == &PyLong_Type) {
        status = save_long(self, obj);
        goto done;
    }
    else if (type == &PyFloat_Type) {
        status = save_float(self, obj);
        goto done;
    }




    if (PyMemoTable_Get(self->memo, obj)) {
        if (memo_get(self, obj) < 0)
            goto error;
        goto done;
    }

    if (type == &PyBytes_Type) {
        status = save_bytes(self, obj);
        goto done;
    }
    else if (type == &PyUnicode_Type) {
        status = save_unicode(self, obj);
        goto done;
    }
    else if (type == &PyDict_Type) {
        status = save_dict(self, obj);
        goto done;
    }
    else if (type == &PyList_Type) {
        status = save_list(self, obj);
        goto done;
    }
    else if (type == &PyTuple_Type) {
        status = save_tuple(self, obj);
        goto done;
    }
    else if (type == &PyType_Type) {
        status = save_global(self, obj, ((void *)0));
        goto done;
    }
    else if (type == &PyFunction_Type) {
        status = save_global(self, obj, ((void *)0));
        if (status < 0 && PyErr_ExceptionMatches(PickleError)) {

            PyErr_Clear();
        }
        else {
            goto done;
        }
    }
    else if (type == &PyCFunction_Type) {
        status = save_global(self, obj, ((void *)0));
        goto done;
    }







    if (self->dispatch_table == ((void *)0)) {
        reduce_func = PyDict_GetItem(dispatch_table, (PyObject *)type);


        do { if ((reduce_func) == ((void *)0)) ; else ( ((PyObject*)(reduce_func))->ob_refcnt++); } while (0);
    } else {
        reduce_func = PyObject_GetItem(self->dispatch_table, (PyObject *)type);
        if (reduce_func == ((void *)0)) {
            if (PyErr_ExceptionMatches(PyExc_KeyError))
                PyErr_Clear();
            else
                goto error;
        }
    }
    if (reduce_func != ((void *)0)) {
        ( ((PyObject*)(obj))->ob_refcnt++);
        reduce_value = _Pickler_FastCall(self, reduce_func, obj);
    }
    else if (PyType_IsSubtype(type, &PyType_Type)) {
        status = save_global(self, obj, ((void *)0));
        goto done;
    }
    else {
        static PyObject *reduce_str = ((void *)0);
        static PyObject *reduce_ex_str = ((void *)0);


        if (reduce_str == ((void *)0)) {
            reduce_str = PyUnicode_InternFromString("__reduce__");
            if (reduce_str == ((void *)0))
                goto error;
            reduce_ex_str = PyUnicode_InternFromString("__reduce_ex__");
            if (reduce_ex_str == ((void *)0))
                goto error;
        }
# 3261 "_pickle.c"
        reduce_func = PyObject_GetAttr(obj, reduce_ex_str);
        if (reduce_func != ((void *)0)) {
            PyObject *proto;
            proto = PyLong_FromLong(self->proto);
            if (proto != ((void *)0)) {
                reduce_value = _Pickler_FastCall(self, reduce_func, proto);
            }
        }
        else {
            if (PyErr_ExceptionMatches(PyExc_AttributeError))
                PyErr_Clear();
            else
                goto error;

            reduce_func = PyObject_GetAttr(obj, reduce_str);
            if (reduce_func != ((void *)0)) {
                reduce_value = PyObject_Call(reduce_func, empty_tuple, ((void *)0));
            }
            else {
                PyErr_Format(PicklingError, "can't pickle '%.200s' object: %R",
                             type->tp_name, obj);
                goto error;
            }
        }
    }

    if (reduce_value == ((void *)0))
        goto error;

    if (((((((PyObject*)(reduce_value))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        status = save_global(self, obj, reduce_value);
        goto done;
    }

    if (!((((((PyObject*)(reduce_value))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
        PyErr_SetString(PicklingError,
                        "__reduce__ must return a string or tuple");
        goto error;
    }

    status = save_reduce(self, reduce_value, obj);

    if (0) {
  error:
        status = -1;
    }
  done:
    do{ if((--(((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->recursion_depth) < ((_Py_CheckRecursionLimit > 100) ? (_Py_CheckRecursionLimit - 50) : (3 * (_Py_CheckRecursionLimit >> 2))))) ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->overflowed = 0; } while(0);
    do { if ((reduce_func) == ((void *)0)) ; else do { if ( --((PyObject*)(reduce_func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(reduce_func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(reduce_func)))); } while (0); } while (0);
    do { if ((reduce_value) == ((void *)0)) ; else do { if ( --((PyObject*)(reduce_value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(reduce_value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(reduce_value)))); } while (0); } while (0);

    return status;
}

static int
dump(PicklerObject *self, PyObject *obj)
{
    const char stop_op = STOP;

    if (self->proto >= 2) {
        char header[2];

        header[0] = PROTO;
        (__builtin_expect(!(self->proto >= 0 && self->proto < 256), 0) ? __assert_rtn(__func__, "_pickle.c", 3324, "self->proto >= 0 && self->proto < 256") : (void)0);
        header[1] = (unsigned char)self->proto;
        if (_Pickler_Write(self, header, 2) < 0)
            return -1;
    }

    if (save(self, obj, 0) < 0 ||
        _Pickler_Write(self, &stop_op, 1) < 0)
        return -1;

    return 0;
}

static char Pickler_clear_memo_doc[] = "clear_memo() -> None. Clears the pickler's \"memo\"." "\n" "The memo is the data structure that remembers which objects the\n" "pickler has already seen, so that shared or recursive objects are\n" "pickled by reference and not by value.  This method is useful when\n" "re-using picklers.";







static PyObject *
Pickler_clear_memo(PicklerObject *self)
{
    if (self->memo)
        PyMemoTable_Clear(self->memo);

    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}

static char Pickler_dump_doc[] = "dump(obj) -> None. Write a pickled representation of obj to the open file.";


static PyObject *
Pickler_dump(PicklerObject *self, PyObject *args)
{
    PyObject *obj;




    if (self->write == ((void *)0)) {
        PyErr_Format(PicklingError,
                     "Pickler.__init__() was not called by %s.__init__()",
                     (((PyObject*)(self))->ob_type)->tp_name);
        return ((void *)0);
    }

    if (!PyArg_ParseTuple(args, "O:dump", &obj))
        return ((void *)0);

    if (_Pickler_ClearBuffer(self) < 0)
        return ((void *)0);

    if (dump(self, obj) < 0)
        return ((void *)0);

    if (_Pickler_FlushToFile(self) < 0)
        return ((void *)0);

    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}

static struct PyMethodDef Pickler_methods[] = {
    {"dump", (PyCFunction)Pickler_dump, 0x0001,
     Pickler_dump_doc},
    {"clear_memo", (PyCFunction)Pickler_clear_memo, 0x0004,
     Pickler_clear_memo_doc},
    {((void *)0), ((void *)0)}
};

static void
Pickler_dealloc(PicklerObject *self)
{
    PyObject_GC_UnTrack(self);

    do { if ((self->output_buffer) == ((void *)0)) ; else do { if ( --((PyObject*)(self->output_buffer))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->output_buffer)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->output_buffer)))); } while (0); } while (0);
    do { if ((self->write) == ((void *)0)) ; else do { if ( --((PyObject*)(self->write))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->write)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->write)))); } while (0); } while (0);
    do { if ((self->pers_func) == ((void *)0)) ; else do { if ( --((PyObject*)(self->pers_func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->pers_func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->pers_func)))); } while (0); } while (0);
    do { if ((self->dispatch_table) == ((void *)0)) ; else do { if ( --((PyObject*)(self->dispatch_table))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->dispatch_table)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->dispatch_table)))); } while (0); } while (0);
    do { if ((self->arg) == ((void *)0)) ; else do { if ( --((PyObject*)(self->arg))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->arg)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->arg)))); } while (0); } while (0);
    do { if ((self->fast_memo) == ((void *)0)) ; else do { if ( --((PyObject*)(self->fast_memo))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->fast_memo)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->fast_memo)))); } while (0); } while (0);

    PyMemoTable_Del(self->memo);

    (((PyObject*)(self))->ob_type)->tp_free((PyObject *)self);
}

static int
Pickler_traverse(PicklerObject *self, visitproc visit, void *arg)
{
    do { if (self->write) { int vret = visit((PyObject *)(self->write), arg); if (vret) return vret; } } while (0);
    do { if (self->pers_func) { int vret = visit((PyObject *)(self->pers_func), arg); if (vret) return vret; } } while (0);
    do { if (self->dispatch_table) { int vret = visit((PyObject *)(self->dispatch_table), arg); if (vret) return vret; } } while (0);
    do { if (self->arg) { int vret = visit((PyObject *)(self->arg), arg); if (vret) return vret; } } while (0);
    do { if (self->fast_memo) { int vret = visit((PyObject *)(self->fast_memo), arg); if (vret) return vret; } } while (0);
    return 0;
}

static int
Pickler_clear(PicklerObject *self)
{
    do { if (self->output_buffer) { PyObject *_py_tmp = (PyObject *)(self->output_buffer); (self->output_buffer) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (self->write) { PyObject *_py_tmp = (PyObject *)(self->write); (self->write) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (self->pers_func) { PyObject *_py_tmp = (PyObject *)(self->pers_func); (self->pers_func) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (self->dispatch_table) { PyObject *_py_tmp = (PyObject *)(self->dispatch_table); (self->dispatch_table) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (self->arg) { PyObject *_py_tmp = (PyObject *)(self->arg); (self->arg) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (self->fast_memo) { PyObject *_py_tmp = (PyObject *)(self->fast_memo); (self->fast_memo) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);

    if (self->memo != ((void *)0)) {
        PyMemoTable *memo = self->memo;
        self->memo = ((void *)0);
        PyMemoTable_Del(memo);
    }
    return 0;
}


static char Pickler_doc[] = "Pickler(file, protocol=None)" "\n" "This takes a binary file for writing a pickle data stream.\n" "\n" "The optional protocol argument tells the pickler to use the\n" "given protocol; supported protocols are 0, 1, 2, 3.  The default\n" "protocol is 3; a backward-incompatible protocol designed for\n" "Python 3.0.\n" "\n" "Specifying a negative protocol version selects the highest\n" "protocol version supported.  The higher the protocol used, the\n" "more recent the version of Python needed to read the pickle\n" "produced.\n" "\n" "The file argument must have a write() method that accepts a single\n" "bytes argument. It can thus be a file object opened for binary\n" "writing, a io.BytesIO instance, or any other custom object that\n" "meets this interface.\n" "\n" "If fix_imports is True and protocol is less than 3, pickle will try to\n" "map the new Python 3.x names to the old module names used in Python\n" "2.x, so that the pickle data stream is readable with Python 2.x.\n";
# 3466 "_pickle.c"
static int
Pickler_init(PicklerObject *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"file", "protocol", "fix_imports", 0};
    PyObject *file;
    PyObject *proto_obj = ((void *)0);
    PyObject *fix_imports = ((PyObject *) &_Py_TrueStruct);
    static _Py_Identifier PyId_persistent_id = { 0, "persistent_id", 0 };
    static _Py_Identifier PyId_dispatch_table = { 0, "dispatch_table", 0 };

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "O|OO:Pickler",
                                     kwlist, &file, &proto_obj, &fix_imports))
        return -1;


    if (self->write != ((void *)0))
        (void)Pickler_clear(self);

    if (_Pickler_SetProtocol(self, proto_obj, fix_imports) < 0)
        return -1;

    if (_Pickler_SetOutputStream(self, file) < 0)
        return -1;


    if (self->memo == ((void *)0)) {
        self->memo = PyMemoTable_New();
        if (self->memo == ((void *)0))
            return -1;
    }
    self->output_len = 0;
    if (self->output_buffer == ((void *)0)) {
        self->max_output_len = WRITE_BUF_SIZE;
        self->output_buffer = PyBytes_FromStringAndSize(((void *)0),
                                                        self->max_output_len);
        if (self->output_buffer == ((void *)0))
            return -1;
    }

    self->arg = ((void *)0);
    self->fast = 0;
    self->fast_nesting = 0;
    self->fast_memo = ((void *)0);
    self->pers_func = ((void *)0);
    if (_PyObject_HasAttrId((PyObject *)self, &PyId_persistent_id)) {
        self->pers_func = _PyObject_GetAttrId((PyObject *)self,
                                              &PyId_persistent_id);
        if (self->pers_func == ((void *)0))
            return -1;
    }
    self->dispatch_table = ((void *)0);
    if (_PyObject_HasAttrId((PyObject *)self, &PyId_dispatch_table)) {
        self->dispatch_table = _PyObject_GetAttrId((PyObject *)self,
                                                   &PyId_dispatch_table);
        if (self->dispatch_table == ((void *)0))
            return -1;
    }
    return 0;
}
# 3536 "_pickle.c"
typedef struct {
    PyObject ob_base;
    PicklerObject *pickler;
} PicklerMemoProxyObject;

static char pmp_clear_doc[] = "memo.clear() -> None.  Remove all items from memo.";


static PyObject *
pmp_clear(PicklerMemoProxyObject *self)
{
    if (self->pickler->memo)
        PyMemoTable_Clear(self->pickler->memo);
    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}

static char pmp_copy_doc[] = "memo.copy() -> new_memo.  Copy the memo to a new object.";


static PyObject *
pmp_copy(PicklerMemoProxyObject *self)
{
    Py_ssize_t i;
    PyMemoTable *memo;
    PyObject *new_memo = PyDict_New();
    if (new_memo == ((void *)0))
        return ((void *)0);

    memo = self->pickler->memo;
    for (i = 0; i < memo->mt_allocated; ++i) {
        PyMemoEntry entry = memo->mt_table[i];
        if (entry.me_key != ((void *)0)) {
            int status;
            PyObject *key, *value;

            key = PyLong_FromVoidPtr(entry.me_key);
            value = Py_BuildValue("nO", entry.me_value, entry.me_key);

            if (key == ((void *)0) || value == ((void *)0)) {
                do { if ((key) == ((void *)0)) ; else do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0); } while (0);
                do { if ((value) == ((void *)0)) ; else do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); } while (0);
                goto error;
            }
            status = PyDict_SetItem(new_memo, key, value);
            do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
            do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0);
            if (status < 0)
                goto error;
        }
    }
    return new_memo;

  error:
    do { if ((new_memo) == ((void *)0)) ; else do { if ( --((PyObject*)(new_memo))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(new_memo)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(new_memo)))); } while (0); } while (0);
    return ((void *)0);
}

static char pmp_reduce_doc[] = "memo.__reduce__(). Pickling support.";


static PyObject *
pmp_reduce(PicklerMemoProxyObject *self, PyObject *args)
{
    PyObject *reduce_value, *dict_args;
    PyObject *contents = pmp_copy(self);
    if (contents == ((void *)0))
        return ((void *)0);

    reduce_value = PyTuple_New(2);
    if (reduce_value == ((void *)0)) {
        do { if ( --((PyObject*)(contents))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(contents)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(contents)))); } while (0);
        return ((void *)0);
    }
    dict_args = PyTuple_New(1);
    if (dict_args == ((void *)0)) {
        do { if ( --((PyObject*)(contents))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(contents)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(contents)))); } while (0);
        do { if ( --((PyObject*)(reduce_value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(reduce_value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(reduce_value)))); } while (0);
        return ((void *)0);
    }
    (((PyTupleObject *)(dict_args))->ob_item[0] = contents);
    ( ((PyObject*)((PyObject *)&PyDict_Type))->ob_refcnt++);
    (((PyTupleObject *)(reduce_value))->ob_item[0] = (PyObject *)&PyDict_Type);
    (((PyTupleObject *)(reduce_value))->ob_item[1] = dict_args);
    return reduce_value;
}

static PyMethodDef picklerproxy_methods[] = {
    {"clear", (PyCFunction)pmp_clear, 0x0004, pmp_clear_doc},
    {"copy", (PyCFunction)pmp_copy, 0x0004, pmp_copy_doc},
    {"__reduce__", (PyCFunction)pmp_reduce, 0x0001, pmp_reduce_doc},
    {((void *)0), ((void *)0)}
};

static void
PicklerMemoProxy_dealloc(PicklerMemoProxyObject *self)
{
    PyObject_GC_UnTrack(self);
    do { if ((self->pickler) == ((void *)0)) ; else do { if ( --((PyObject*)(self->pickler))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->pickler)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->pickler)))); } while (0); } while (0);
    PyObject_GC_Del((PyObject *)self);
}

static int
PicklerMemoProxy_traverse(PicklerMemoProxyObject *self,
                          visitproc visit, void *arg)
{
    do { if (self->pickler) { int vret = visit((PyObject *)(self->pickler), arg); if (vret) return vret; } } while (0);
    return 0;
}

static int
PicklerMemoProxy_clear(PicklerMemoProxyObject *self)
{
    do { if (self->pickler) { PyObject *_py_tmp = (PyObject *)(self->pickler); (self->pickler) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    return 0;
}

static PyTypeObject PicklerMemoProxyType = {
    { { 1, ((void *)0) }, 0 },
    "_pickle.PicklerMemoProxy",
    sizeof(PicklerMemoProxyObject),
    0,
    (destructor)PicklerMemoProxy_dealloc,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    PyObject_HashNotImplemented,
    0,
    0,
    PyObject_GenericGetAttr,
    PyObject_GenericSetAttr,
    0,
    ( 0 | (1L<<18) | 0) | (1L<<10) | (1L<<14),
    0,
    (traverseproc)PicklerMemoProxy_traverse,
    (inquiry)PicklerMemoProxy_clear,
    0,
    0,
    0,
    0,
    picklerproxy_methods,
};

static PyObject *
PicklerMemoProxy_New(PicklerObject *pickler)
{
    PicklerMemoProxyObject *self;

    self = ( (PicklerMemoProxyObject *) _PyObject_GC_New(&PicklerMemoProxyType) );
    if (self == ((void *)0))
        return ((void *)0);
    ( ((PyObject*)(pickler))->ob_refcnt++);
    self->pickler = pickler;
    PyObject_GC_Track(self);
    return (PyObject *)self;
}



static PyObject *
Pickler_get_memo(PicklerObject *self)
{
    return PicklerMemoProxy_New(self);
}

static int
Pickler_set_memo(PicklerObject *self, PyObject *obj)
{
    PyMemoTable *new_memo = ((void *)0);

    if (obj == ((void *)0)) {
        PyErr_SetString(PyExc_TypeError,
                        "attribute deletion is not supported");
        return -1;
    }

    if ((((PyObject*)(obj))->ob_type) == &PicklerMemoProxyType) {
        PicklerObject *pickler =
            ((PicklerMemoProxyObject *)obj)->pickler;

        new_memo = PyMemoTable_Copy(pickler->memo);
        if (new_memo == ((void *)0))
            return -1;
    }
    else if (((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<29))) != 0)) {
        Py_ssize_t i = 0;
        PyObject *key, *value;

        new_memo = PyMemoTable_New();
        if (new_memo == ((void *)0))
            return -1;

        while (PyDict_Next(obj, &i, &key, &value)) {
            Py_ssize_t memo_id;
            PyObject *memo_obj;

            if (!((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<26))) != 0) || (((PyVarObject*)(value))->ob_size) != 2) {
                PyErr_SetString(PyExc_TypeError,
                                "'memo' values must be 2-item tuples");
                goto error;
            }
            memo_id = PyLong_AsSsize_t((((PyTupleObject *)(value))->ob_item[0]));
            if (memo_id == -1 && PyErr_Occurred())
                goto error;
            memo_obj = (((PyTupleObject *)(value))->ob_item[1]);
            if (PyMemoTable_Set(new_memo, memo_obj, memo_id) < 0)
                goto error;
        }
    }
    else {
        PyErr_Format(PyExc_TypeError,
                     "'memo' attribute must be an PicklerMemoProxy object"
                     "or dict, not %.200s", (((PyObject*)(obj))->ob_type)->tp_name);
        return -1;
    }

    PyMemoTable_Del(self->memo);
    self->memo = new_memo;

    return 0;

  error:
    if (new_memo)
        PyMemoTable_Del(new_memo);
    return -1;
}

static PyObject *
Pickler_get_persid(PicklerObject *self)
{
    if (self->pers_func == ((void *)0))
        PyErr_SetString(PyExc_AttributeError, "persistent_id");
    else
        ( ((PyObject*)(self->pers_func))->ob_refcnt++);
    return self->pers_func;
}

static int
Pickler_set_persid(PicklerObject *self, PyObject *value)
{
    PyObject *tmp;

    if (value == ((void *)0)) {
        PyErr_SetString(PyExc_TypeError,
                        "attribute deletion is not supported");
        return -1;
    }
    if (!PyCallable_Check(value)) {
        PyErr_SetString(PyExc_TypeError,
                        "persistent_id must be a callable taking one argument");
        return -1;
    }

    tmp = self->pers_func;
    ( ((PyObject*)(value))->ob_refcnt++);
    self->pers_func = value;
    do { if ((tmp) == ((void *)0)) ; else do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0); } while (0);

    return 0;
}

static PyMemberDef Pickler_members[] = {
    {"bin", 1, __builtin_offsetof (PicklerObject, bin)},
    {"fast", 1, __builtin_offsetof (PicklerObject, fast)},
    {"dispatch_table", 16, __builtin_offsetof (PicklerObject, dispatch_table)},
    {((void *)0)}
};

static PyGetSetDef Pickler_getsets[] = {
    {"memo", (getter)Pickler_get_memo,
                      (setter)Pickler_set_memo},
    {"persistent_id", (getter)Pickler_get_persid,
                      (setter)Pickler_set_persid},
    {((void *)0)}
};

static PyTypeObject Pickler_Type = {
    { { 1, ((void *)0) }, 0 },
    "_pickle.Pickler" ,
    sizeof(PicklerObject),
    0,
    (destructor)Pickler_dealloc,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    ( 0 | (1L<<18) | 0) | (1L<<10) | (1L<<14),
    Pickler_doc,
    (traverseproc)Pickler_traverse,
    (inquiry)Pickler_clear,
    0,
    0,
    0,
    0,
    Pickler_methods,
    Pickler_members,
    Pickler_getsets,
    0,
    0,
    0,
    0,
    0,
    (initproc)Pickler_init,
    PyType_GenericAlloc,
    PyType_GenericNew,
    PyObject_GC_Del,
    0,
};
# 3866 "_pickle.c"
static PyObject *
find_class(UnpicklerObject *self, PyObject *module_name, PyObject *global_name)
{
    static _Py_Identifier PyId_find_class = { 0, "find_class", 0 };

    return _PyObject_CallMethodId((PyObject *)self, &PyId_find_class, "OO",
                                  module_name, global_name);
}

static Py_ssize_t
marker(UnpicklerObject *self)
{
    if (self->num_marks < 1) {
        PyErr_SetString(UnpicklingError, "could not find MARK");
        return -1;
    }

    return self->marks[--self->num_marks];
}

static int
load_none(UnpicklerObject *self)
{
    do { ( ((PyObject*)(((&_Py_NoneStruct))))->ob_refcnt++); if (Pdata_push((self->stack), ((&_Py_NoneStruct))) < 0) return (-1); } while(0);
    return 0;
}

static int
bad_readline(void)
{
    PyErr_SetString(UnpicklingError, "pickle data was truncated");
    return -1;
}

static int
load_int(UnpicklerObject *self)
{
    PyObject *value;
    char *endptr, *s;
    Py_ssize_t len;
    long x;

    if ((len = _Unpickler_Readline(self, &s)) < 0)
        return -1;
    if (len < 2)
        return bad_readline();

    (*__error()) = 0;


    x = strtol(s, &endptr, 0);

    if ((*__error()) || (*endptr != '\n' && *endptr != '\0')) {


        (*__error()) = 0;

        value = PyLong_FromString(s, ((void *)0), 0);
        if (value == ((void *)0)) {
            PyErr_SetString(PyExc_ValueError,
                            "could not convert string to int");
            return -1;
        }
    }
    else {
        if (len == 3 && (x == 0 || x == 1)) {
            if ((value = PyBool_FromLong(x)) == ((void *)0))
                return -1;
        }
        else {
            if ((value = PyLong_FromLong(x)) == ((void *)0))
                return -1;
        }
    }

    do { if (Pdata_push((self->stack), (value)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_bool(UnpicklerObject *self, PyObject *boolean)
{
    (__builtin_expect(!(boolean == ((PyObject *) &_Py_TrueStruct) || boolean == ((PyObject *) &_Py_FalseStruct)), 0) ? __assert_rtn(__func__, "_pickle.c", 3948, "boolean == Py_True || boolean == Py_False") : (void)0);
    do { ( ((PyObject*)((boolean)))->ob_refcnt++); if (Pdata_push((self->stack), (boolean)) < 0) return (-1); } while(0);
    return 0;
}




static Py_ssize_t
calc_binsize(char *bytes, int size)
{
    unsigned char *s = (unsigned char *)bytes;
    size_t x = 0;

    (__builtin_expect(!(size == 4), 0) ? __assert_rtn(__func__, "_pickle.c", 3962, "size == 4") : (void)0);

    x = (size_t) s[0];
    x |= (size_t) s[1] << 8;
    x |= (size_t) s[2] << 16;
    x |= (size_t) s[3] << 24;

    if (x > ((Py_ssize_t)(((size_t)-1)>>1)))
        return -1;
    else
        return (Py_ssize_t) x;
}






static long
calc_binint(char *bytes, int size)
{
    unsigned char *s = (unsigned char *)bytes;
    int i = size;
    long x = 0;

    for (i = 0; i < size; i++) {
        x |= (long)s[i] << (i * 8);
    }





    if (8 > 4 && size == 4) {
        x |= -(x & (1L << 31));
    }

    return x;
}

static int
load_binintx(UnpicklerObject *self, char *s, int size)
{
    PyObject *value;
    long x;

    x = calc_binint(s, size);

    if ((value = PyLong_FromLong(x)) == ((void *)0))
        return -1;

    do { if (Pdata_push((self->stack), (value)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_binint(UnpicklerObject *self)
{
    char *s;

    if (_Unpickler_Read(self, &s, 4) < 0)
        return -1;

    return load_binintx(self, s, 4);
}

static int
load_binint1(UnpicklerObject *self)
{
    char *s;

    if (_Unpickler_Read(self, &s, 1) < 0)
        return -1;

    return load_binintx(self, s, 1);
}

static int
load_binint2(UnpicklerObject *self)
{
    char *s;

    if (_Unpickler_Read(self, &s, 2) < 0)
        return -1;

    return load_binintx(self, s, 2);
}

static int
load_long(UnpicklerObject *self)
{
    PyObject *value;
    char *s;
    Py_ssize_t len;

    if ((len = _Unpickler_Readline(self, &s)) < 0)
        return -1;
    if (len < 2)
        return bad_readline();





    if (s[len-2] == 'L')
        s[len-2] = '\0';

    value = PyLong_FromString(s, ((void *)0), 0);
    if (value == ((void *)0))
        return -1;

    do { if (Pdata_push((self->stack), (value)) < 0) return (-1); } while(0);
    return 0;
}




static int
load_counted_long(UnpicklerObject *self, int size)
{
    PyObject *value;
    char *nbytes;
    char *pdata;

    (__builtin_expect(!(size == 1 || size == 4), 0) ? __assert_rtn(__func__, "_pickle.c", 4087, "size == 1 || size == 4") : (void)0);
    if (_Unpickler_Read(self, &nbytes, size) < 0)
        return -1;

    size = calc_binint(nbytes, size);
    if (size < 0) {

        PyErr_SetString(UnpicklingError,
                        "LONG pickle has negative byte count");
        return -1;
    }

    if (size == 0)
        value = PyLong_FromLong(0L);
    else {

        if (_Unpickler_Read(self, &pdata, size) < 0)
            return -1;
        value = _PyLong_FromByteArray((unsigned char *)pdata, (size_t)size,
                                      1 , 1 );
    }
    if (value == ((void *)0))
        return -1;
    do { if (Pdata_push((self->stack), (value)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_float(UnpicklerObject *self)
{
    PyObject *value;
    char *endptr, *s;
    Py_ssize_t len;
    double d;

    if ((len = _Unpickler_Readline(self, &s)) < 0)
        return -1;
    if (len < 2)
        return bad_readline();

    (*__error()) = 0;
    d = PyOS_string_to_double(s, &endptr, PyExc_OverflowError);
    if (d == -1.0 && PyErr_Occurred())
        return -1;
    if ((endptr[0] != '\n') && (endptr[0] != '\0')) {
        PyErr_SetString(PyExc_ValueError, "could not convert string to float");
        return -1;
    }
    value = PyFloat_FromDouble(d);
    if (value == ((void *)0))
        return -1;

    do { if (Pdata_push((self->stack), (value)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_binfloat(UnpicklerObject *self)
{
    PyObject *value;
    double x;
    char *s;

    if (_Unpickler_Read(self, &s, 8) < 0)
        return -1;

    x = _PyFloat_Unpack8((unsigned char *)s, 0);
    if (x == -1.0 && PyErr_Occurred())
        return -1;

    if ((value = PyFloat_FromDouble(x)) == ((void *)0))
        return -1;

    do { if (Pdata_push((self->stack), (value)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_string(UnpicklerObject *self)
{
    PyObject *bytes;
    PyObject *str = ((void *)0);
    Py_ssize_t len;
    char *s, *p;

    if ((len = _Unpickler_Readline(self, &s)) < 0)
        return -1;
    if (len < 3)
        return bad_readline();
    if ((s = strdup(s)) == ((void *)0)) {
        PyErr_NoMemory();
        return -1;
    }


    while (s[len - 1] <= ' ')
        len--;
    if (s[0] == '"' && s[len - 1] == '"') {
        s[len - 1] = '\0';
        p = s + 1;
        len -= 2;
    }
    else if (s[0] == '\'' && s[len - 1] == '\'') {
        s[len - 1] = '\0';
        p = s + 1;
        len -= 2;
    }
    else {
        free(s);
        PyErr_SetString(PyExc_ValueError, "insecure string pickle");
        return -1;
    }



    bytes = PyBytes_DecodeEscape(p, len, ((void *)0), 0, ((void *)0));
    free(s);
    if (bytes == ((void *)0))
        return -1;
    str = PyUnicode_FromEncodedObject(bytes, self->encoding, self->errors);
    do { if ( --((PyObject*)(bytes))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(bytes)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(bytes)))); } while (0);
    if (str == ((void *)0))
        return -1;

    do { if (Pdata_push((self->stack), (str)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_binbytes(UnpicklerObject *self)
{
    PyObject *bytes;
    Py_ssize_t x;
    char *s;

    if (_Unpickler_Read(self, &s, 4) < 0)
        return -1;

    x = calc_binsize(s, 4);
    if (x < 0) {
        PyErr_Format(PyExc_OverflowError,
                     "BINBYTES exceeds system's maximum size of %zd bytes",
                     ((Py_ssize_t)(((size_t)-1)>>1))
                    );
        return -1;
    }

    if (_Unpickler_Read(self, &s, x) < 0)
        return -1;
    bytes = PyBytes_FromStringAndSize(s, x);
    if (bytes == ((void *)0))
        return -1;

    do { if (Pdata_push((self->stack), (bytes)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_short_binbytes(UnpicklerObject *self)
{
    PyObject *bytes;
    Py_ssize_t x;
    char *s;

    if (_Unpickler_Read(self, &s, 1) < 0)
        return -1;

    x = (unsigned char)s[0];

    if (_Unpickler_Read(self, &s, x) < 0)
        return -1;

    bytes = PyBytes_FromStringAndSize(s, x);
    if (bytes == ((void *)0))
        return -1;

    do { if (Pdata_push((self->stack), (bytes)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_binstring(UnpicklerObject *self)
{
    PyObject *str;
    Py_ssize_t x;
    char *s;

    if (_Unpickler_Read(self, &s, 4) < 0)
        return -1;

    x = calc_binint(s, 4);
    if (x < 0) {
        PyErr_SetString(UnpicklingError,
                        "BINSTRING pickle has negative byte count");
        return -1;
    }

    if (_Unpickler_Read(self, &s, x) < 0)
        return -1;


    str = PyUnicode_Decode(s, x, self->encoding, self->errors);
    if (str == ((void *)0))
        return -1;

    do { if (Pdata_push((self->stack), (str)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_short_binstring(UnpicklerObject *self)
{
    PyObject *str;
    Py_ssize_t x;
    char *s;

    if (_Unpickler_Read(self, &s, 1) < 0)
        return -1;

    x = (unsigned char)s[0];

    if (_Unpickler_Read(self, &s, x) < 0)
        return -1;


    str = PyUnicode_Decode(s, x, self->encoding, self->errors);
    if (str == ((void *)0))
        return -1;

    do { if (Pdata_push((self->stack), (str)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_unicode(UnpicklerObject *self)
{
    PyObject *str;
    Py_ssize_t len;
    char *s;

    if ((len = _Unpickler_Readline(self, &s)) < 0)
        return -1;
    if (len < 1)
        return bad_readline();

    str = PyUnicode_DecodeRawUnicodeEscape(s, len - 1, ((void *)0));
    if (str == ((void *)0))
        return -1;

    do { if (Pdata_push((self->stack), (str)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_binunicode(UnpicklerObject *self)
{
    PyObject *str;
    Py_ssize_t size;
    char *s;

    if (_Unpickler_Read(self, &s, 4) < 0)
        return -1;

    size = calc_binsize(s, 4);
    if (size < 0) {
        PyErr_Format(PyExc_OverflowError,
                     "BINUNICODE exceeds system's maximum size of %zd bytes",
                     ((Py_ssize_t)(((size_t)-1)>>1))
                    );
        return -1;
    }


    if (_Unpickler_Read(self, &s, size) < 0)
        return -1;

    str = PyUnicode_DecodeUTF8(s, size, "surrogatepass");
    if (str == ((void *)0))
        return -1;

    do { if (Pdata_push((self->stack), (str)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_tuple(UnpicklerObject *self)
{
    PyObject *tuple;
    Py_ssize_t i;

    if ((i = marker(self)) < 0)
        return -1;

    tuple = Pdata_poptuple(self->stack, i);
    if (tuple == ((void *)0))
        return -1;
    do { if (Pdata_push((self->stack), (tuple)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_counted_tuple(UnpicklerObject *self, int len)
{
    PyObject *tuple;

    tuple = PyTuple_New(len);
    if (tuple == ((void *)0))
        return -1;

    while (--len >= 0) {
        PyObject *item;

        do { (item) = Pdata_pop((self->stack)); } while (0);
        if (item == ((void *)0))
            return -1;
        (((PyTupleObject *)(tuple))->ob_item[len] = item);
    }
    do { if (Pdata_push((self->stack), (tuple)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_empty_list(UnpicklerObject *self)
{
    PyObject *list;

    if ((list = PyList_New(0)) == ((void *)0))
        return -1;
    do { if (Pdata_push((self->stack), (list)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_empty_dict(UnpicklerObject *self)
{
    PyObject *dict;

    if ((dict = PyDict_New()) == ((void *)0))
        return -1;
    do { if (Pdata_push((self->stack), (dict)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_list(UnpicklerObject *self)
{
    PyObject *list;
    Py_ssize_t i;

    if ((i = marker(self)) < 0)
        return -1;

    list = Pdata_poplist(self->stack, i);
    if (list == ((void *)0))
        return -1;
    do { if (Pdata_push((self->stack), (list)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_dict(UnpicklerObject *self)
{
    PyObject *dict, *key, *value;
    Py_ssize_t i, j, k;

    if ((i = marker(self)) < 0)
        return -1;
    j = (((PyVarObject*)(self->stack))->ob_size);

    if ((dict = PyDict_New()) == ((void *)0))
        return -1;

    for (k = i + 1; k < j; k += 2) {
        key = self->stack->data[k - 1];
        value = self->stack->data[k];
        if (PyDict_SetItem(dict, key, value) < 0) {
            do { if ( --((PyObject*)(dict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dict)))); } while (0);
            return -1;
        }
    }
    Pdata_clear(self->stack, i);
    do { if (Pdata_push((self->stack), (dict)) < 0) return (-1); } while(0);
    return 0;
}

static PyObject *
instantiate(PyObject *cls, PyObject *args)
{
    PyObject *result = ((void *)0);
    static _Py_Identifier PyId___getinitargs__ = { 0, "__getinitargs__", 0 };



    (__builtin_expect(!(((((((PyObject*)(args))->ob_type))->tp_flags & ((1L<<26))) != 0)), 0) ? __assert_rtn(__func__, "_pickle.c", 4480, "PyTuple_Check(args)") : (void)0);
    if ((((PyVarObject*)(args))->ob_size) > 0 || !((((((PyObject*)(cls))->ob_type))->tp_flags & ((1L<<31))) != 0) ||
        _PyObject_HasAttrId(cls, &PyId___getinitargs__)) {
        result = PyObject_CallObject(cls, args);
    }
    else {
        static _Py_Identifier PyId___new__ = { 0, "__new__", 0 };

        result = _PyObject_CallMethodId(cls, &PyId___new__, "O", cls);
    }
    return result;
}

static int
load_obj(UnpicklerObject *self)
{
    PyObject *cls, *args, *obj = ((void *)0);
    Py_ssize_t i;

    if ((i = marker(self)) < 0)
        return -1;

    args = Pdata_poptuple(self->stack, i + 1);
    if (args == ((void *)0))
        return -1;

    do { (cls) = Pdata_pop((self->stack)); } while (0);
    if (cls) {
        obj = instantiate(cls, args);
        do { if ( --((PyObject*)(cls))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(cls)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(cls)))); } while (0);
    }
    do { if ( --((PyObject*)(args))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(args)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(args)))); } while (0);
    if (obj == ((void *)0))
        return -1;

    do { if (Pdata_push((self->stack), (obj)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_inst(UnpicklerObject *self)
{
    PyObject *cls = ((void *)0);
    PyObject *args = ((void *)0);
    PyObject *obj = ((void *)0);
    PyObject *module_name;
    PyObject *class_name;
    Py_ssize_t len;
    Py_ssize_t i;
    char *s;

    if ((i = marker(self)) < 0)
        return -1;
    if ((len = _Unpickler_Readline(self, &s)) < 0)
        return -1;
    if (len < 2)
        return bad_readline();




    module_name = PyUnicode_DecodeASCII(s, len - 1, "strict");
    if (module_name == ((void *)0))
        return -1;

    if ((len = _Unpickler_Readline(self, &s)) >= 0) {
        if (len < 2)
            return bad_readline();
        class_name = PyUnicode_DecodeASCII(s, len - 1, "strict");
        if (class_name != ((void *)0)) {
            cls = find_class(self, module_name, class_name);
            do { if ( --((PyObject*)(class_name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(class_name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(class_name)))); } while (0);
        }
    }
    do { if ( --((PyObject*)(module_name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(module_name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(module_name)))); } while (0);

    if (cls == ((void *)0))
        return -1;

    if ((args = Pdata_poptuple(self->stack, i)) != ((void *)0)) {
        obj = instantiate(cls, args);
        do { if ( --((PyObject*)(args))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(args)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(args)))); } while (0);
    }
    do { if ( --((PyObject*)(cls))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(cls)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(cls)))); } while (0);

    if (obj == ((void *)0))
        return -1;

    do { if (Pdata_push((self->stack), (obj)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_newobj(UnpicklerObject *self)
{
    PyObject *args = ((void *)0);
    PyObject *clsraw = ((void *)0);
    PyTypeObject *cls;
    PyObject *obj;




    do { (args) = Pdata_pop((self->stack)); } while (0);
    if (args == ((void *)0))
        goto error;
    if (!((((((PyObject*)(args))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
        PyErr_SetString(UnpicklingError, "NEWOBJ expected an arg " "tuple.");
        goto error;
    }

    do { (clsraw) = Pdata_pop((self->stack)); } while (0);
    cls = (PyTypeObject *)clsraw;
    if (cls == ((void *)0))
        goto error;
    if (!((((((PyObject*)(cls))->ob_type))->tp_flags & ((1L<<31))) != 0)) {
        PyErr_SetString(UnpicklingError, "NEWOBJ class argument "
                        "isn't a type object");
        goto error;
    }
    if (cls->tp_new == ((void *)0)) {
        PyErr_SetString(UnpicklingError, "NEWOBJ class argument "
                        "has NULL tp_new");
        goto error;
    }


    obj = cls->tp_new(cls, args, ((void *)0));
    if (obj == ((void *)0))
        goto error;

    do { if ( --((PyObject*)(args))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(args)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(args)))); } while (0);
    do { if ( --((PyObject*)(clsraw))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(clsraw)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(clsraw)))); } while (0);
    do { if (Pdata_push((self->stack), (obj)) < 0) return (-1); } while(0);
    return 0;

  error:
    do { if ((args) == ((void *)0)) ; else do { if ( --((PyObject*)(args))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(args)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(args)))); } while (0); } while (0);
    do { if ((clsraw) == ((void *)0)) ; else do { if ( --((PyObject*)(clsraw))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(clsraw)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(clsraw)))); } while (0); } while (0);
    return -1;
}

static int
load_global(UnpicklerObject *self)
{
    PyObject *global = ((void *)0);
    PyObject *module_name;
    PyObject *global_name;
    Py_ssize_t len;
    char *s;

    if ((len = _Unpickler_Readline(self, &s)) < 0)
        return -1;
    if (len < 2)
        return bad_readline();
    module_name = PyUnicode_DecodeUTF8(s, len - 1, "strict");
    if (!module_name)
        return -1;

    if ((len = _Unpickler_Readline(self, &s)) >= 0) {
        if (len < 2) {
            do { if ( --((PyObject*)(module_name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(module_name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(module_name)))); } while (0);
            return bad_readline();
        }
        global_name = PyUnicode_DecodeUTF8(s, len - 1, "strict");
        if (global_name) {
            global = find_class(self, module_name, global_name);
            do { if ( --((PyObject*)(global_name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(global_name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(global_name)))); } while (0);
        }
    }
    do { if ( --((PyObject*)(module_name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(module_name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(module_name)))); } while (0);

    if (global == ((void *)0))
        return -1;
    do { if (Pdata_push((self->stack), (global)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_persid(UnpicklerObject *self)
{
    PyObject *pid;
    Py_ssize_t len;
    char *s;

    if (self->pers_func) {
        if ((len = _Unpickler_Readline(self, &s)) < 0)
            return -1;
        if (len < 2)
            return bad_readline();

        pid = PyBytes_FromStringAndSize(s, len - 1);
        if (pid == ((void *)0))
            return -1;



        pid = _Unpickler_FastCall(self, self->pers_func, pid);
        if (pid == ((void *)0))
            return -1;

        do { if (Pdata_push((self->stack), (pid)) < 0) return (-1); } while(0);
        return 0;
    }
    else {
        PyErr_SetString(UnpicklingError,
                        "A load persistent id instruction was encountered,\n"
                        "but no persistent_load function was specified.");
        return -1;
    }
}

static int
load_binpersid(UnpicklerObject *self)
{
    PyObject *pid;

    if (self->pers_func) {
        do { (pid) = Pdata_pop((self->stack)); } while (0);
        if (pid == ((void *)0))
            return -1;



        pid = _Unpickler_FastCall(self, self->pers_func, pid);
        if (pid == ((void *)0))
            return -1;

        do { if (Pdata_push((self->stack), (pid)) < 0) return (-1); } while(0);
        return 0;
    }
    else {
        PyErr_SetString(UnpicklingError,
                        "A load persistent id instruction was encountered,\n"
                        "but no persistent_load function was specified.");
        return -1;
    }
}

static int
load_pop(UnpicklerObject *self)
{
    Py_ssize_t len = (((PyVarObject*)(self->stack))->ob_size);
# 4731 "_pickle.c"
    if (self->num_marks > 0 && self->marks[self->num_marks - 1] == len) {
        self->num_marks--;
    } else if (len > 0) {
        len--;
        do { if ( --((PyObject*)(self->stack->data[len]))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->stack->data[len])))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->stack->data[len])))); } while (0);
        (((PyVarObject*)(self->stack))->ob_size) = len;
    } else {
        return stack_underflow();
    }
    return 0;
}

static int
load_pop_mark(UnpicklerObject *self)
{
    Py_ssize_t i;

    if ((i = marker(self)) < 0)
        return -1;

    Pdata_clear(self->stack, i);

    return 0;
}

static int
load_dup(UnpicklerObject *self)
{
    PyObject *last;
    Py_ssize_t len;

    if ((len = (((PyVarObject*)(self->stack))->ob_size)) <= 0)
        return stack_underflow();
    last = self->stack->data[len - 1];
    do { ( ((PyObject*)((last)))->ob_refcnt++); if (Pdata_push((self->stack), (last)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_get(UnpicklerObject *self)
{
    PyObject *key, *value;
    Py_ssize_t idx;
    Py_ssize_t len;
    char *s;

    if ((len = _Unpickler_Readline(self, &s)) < 0)
        return -1;
    if (len < 2)
        return bad_readline();

    key = PyLong_FromString(s, ((void *)0), 10);
    if (key == ((void *)0))
        return -1;
    idx = PyLong_AsSsize_t(key);
    if (idx == -1 && PyErr_Occurred()) {
        do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
        return -1;
    }

    value = _Unpickler_MemoGet(self, idx);
    if (value == ((void *)0)) {
        if (!PyErr_Occurred())
            PyErr_SetObject(PyExc_KeyError, key);
        do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
        return -1;
    }
    do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);

    do { ( ((PyObject*)((value)))->ob_refcnt++); if (Pdata_push((self->stack), (value)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_binget(UnpicklerObject *self)
{
    PyObject *value;
    Py_ssize_t idx;
    char *s;

    if (_Unpickler_Read(self, &s, 1) < 0)
        return -1;

    idx = ((unsigned char)((s[0]) & 0xff));

    value = _Unpickler_MemoGet(self, idx);
    if (value == ((void *)0)) {
        PyObject *key = PyLong_FromSsize_t(idx);
        if (!PyErr_Occurred())
            PyErr_SetObject(PyExc_KeyError, key);
        do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
        return -1;
    }

    do { ( ((PyObject*)((value)))->ob_refcnt++); if (Pdata_push((self->stack), (value)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_long_binget(UnpicklerObject *self)
{
    PyObject *value;
    Py_ssize_t idx;
    char *s;

    if (_Unpickler_Read(self, &s, 4) < 0)
        return -1;

    idx = calc_binsize(s, 4);

    value = _Unpickler_MemoGet(self, idx);
    if (value == ((void *)0)) {
        PyObject *key = PyLong_FromSsize_t(idx);
        if (!PyErr_Occurred())
            PyErr_SetObject(PyExc_KeyError, key);
        do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
        return -1;
    }

    do { ( ((PyObject*)((value)))->ob_refcnt++); if (Pdata_push((self->stack), (value)) < 0) return (-1); } while(0);
    return 0;
}




static int
load_extension(UnpicklerObject *self, int nbytes)
{
    char *codebytes;
    long code;
    PyObject *py_code;
    PyObject *obj;
    PyObject *pair;
    PyObject *module_name, *class_name;

    (__builtin_expect(!(nbytes == 1 || nbytes == 2 || nbytes == 4), 0) ? __assert_rtn(__func__, "_pickle.c", 4867, "nbytes == 1 || nbytes == 2 || nbytes == 4") : (void)0);
    if (_Unpickler_Read(self, &codebytes, nbytes) < 0)
        return -1;
    code = calc_binint(codebytes, nbytes);
    if (code <= 0) {

        PyErr_SetString(UnpicklingError, "EXT specifies code <= 0");
        return -1;
    }


    py_code = PyLong_FromLong(code);
    if (py_code == ((void *)0))
        return -1;
    obj = PyDict_GetItem(extension_cache, py_code);
    if (obj != ((void *)0)) {

        do { if ( --((PyObject*)(py_code))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(py_code)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(py_code)))); } while (0);
        do { ( ((PyObject*)((obj)))->ob_refcnt++); if (Pdata_push((self->stack), (obj)) < 0) return (-1); } while(0);
        return 0;
    }


    pair = PyDict_GetItem(inverted_registry, py_code);
    if (pair == ((void *)0)) {
        do { if ( --((PyObject*)(py_code))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(py_code)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(py_code)))); } while (0);
        PyErr_Format(PyExc_ValueError, "unregistered extension "
                     "code %ld", code);
        return -1;
    }



    if (!((((((PyObject*)(pair))->ob_type))->tp_flags & ((1L<<26))) != 0) || PyTuple_Size(pair) != 2 ||
        !((((((PyObject*)(module_name = (((PyTupleObject *)(pair))->ob_item[0])))->ob_type))->tp_flags & ((1L<<28))) != 0) ||
        !((((((PyObject*)(class_name = (((PyTupleObject *)(pair))->ob_item[1])))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        do { if ( --((PyObject*)(py_code))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(py_code)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(py_code)))); } while (0);
        PyErr_Format(PyExc_ValueError, "_inverted_registry[%ld] "
                     "isn't a 2-tuple of strings", code);
        return -1;
    }

    obj = find_class(self, module_name, class_name);
    if (obj == ((void *)0)) {
        do { if ( --((PyObject*)(py_code))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(py_code)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(py_code)))); } while (0);
        return -1;
    }

    code = PyDict_SetItem(extension_cache, py_code, obj);
    do { if ( --((PyObject*)(py_code))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(py_code)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(py_code)))); } while (0);
    if (code < 0) {
        do { if ( --((PyObject*)(obj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(obj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(obj)))); } while (0);
        return -1;
    }
    do { if (Pdata_push((self->stack), (obj)) < 0) return (-1); } while(0);
    return 0;
}

static int
load_put(UnpicklerObject *self)
{
    PyObject *key, *value;
    Py_ssize_t idx;
    Py_ssize_t len;
    char *s;

    if ((len = _Unpickler_Readline(self, &s)) < 0)
        return -1;
    if (len < 2)
        return bad_readline();
    if ((((PyVarObject*)(self->stack))->ob_size) <= 0)
        return stack_underflow();
    value = self->stack->data[(((PyVarObject*)(self->stack))->ob_size) - 1];

    key = PyLong_FromString(s, ((void *)0), 10);
    if (key == ((void *)0))
        return -1;
    idx = PyLong_AsSsize_t(key);
    do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
    if (idx < 0) {
        if (!PyErr_Occurred())
            PyErr_SetString(PyExc_ValueError,
                            "negative PUT argument");
        return -1;
    }

    return _Unpickler_MemoPut(self, idx, value);
}

static int
load_binput(UnpicklerObject *self)
{
    PyObject *value;
    Py_ssize_t idx;
    char *s;

    if (_Unpickler_Read(self, &s, 1) < 0)
        return -1;

    if ((((PyVarObject*)(self->stack))->ob_size) <= 0)
        return stack_underflow();
    value = self->stack->data[(((PyVarObject*)(self->stack))->ob_size) - 1];

    idx = ((unsigned char)((s[0]) & 0xff));

    return _Unpickler_MemoPut(self, idx, value);
}

static int
load_long_binput(UnpicklerObject *self)
{
    PyObject *value;
    Py_ssize_t idx;
    char *s;

    if (_Unpickler_Read(self, &s, 4) < 0)
        return -1;

    if ((((PyVarObject*)(self->stack))->ob_size) <= 0)
        return stack_underflow();
    value = self->stack->data[(((PyVarObject*)(self->stack))->ob_size) - 1];

    idx = calc_binsize(s, 4);
    if (idx < 0) {
        PyErr_SetString(PyExc_ValueError,
                        "negative LONG_BINPUT argument");
        return -1;
    }

    return _Unpickler_MemoPut(self, idx, value);
}

static int
do_append(UnpicklerObject *self, Py_ssize_t x)
{
    PyObject *value;
    PyObject *list;
    Py_ssize_t len, i;

    len = (((PyVarObject*)(self->stack))->ob_size);
    if (x > len || x <= 0)
        return stack_underflow();
    if (len == x)
        return 0;

    list = self->stack->data[x - 1];

    if (((((((PyObject*)(list))->ob_type))->tp_flags & ((1L<<25))) != 0)) {
        PyObject *slice;
        Py_ssize_t list_len;
        int ret;

        slice = Pdata_poplist(self->stack, x);
        if (!slice)
            return -1;
        list_len = (((PyVarObject*)(list))->ob_size);
        ret = PyList_SetSlice(list, list_len, list_len, slice);
        do { if ( --((PyObject*)(slice))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(slice)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(slice)))); } while (0);
        return ret;
    }
    else {
        PyObject *append_func;
        static _Py_Identifier PyId_append = { 0, "append", 0 };

        append_func = _PyObject_GetAttrId(list, &PyId_append);
        if (append_func == ((void *)0))
            return -1;
        for (i = x; i < len; i++) {
            PyObject *result;

            value = self->stack->data[i];
            result = _Unpickler_FastCall(self, append_func, value);
            if (result == ((void *)0)) {
                Pdata_clear(self->stack, i + 1);
                (((PyVarObject*)(self->stack))->ob_size) = x;
                return -1;
            }
            do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0);
        }
        (((PyVarObject*)(self->stack))->ob_size) = x;
    }

    return 0;
}

static int
load_append(UnpicklerObject *self)
{
    return do_append(self, (((PyVarObject*)(self->stack))->ob_size) - 1);
}

static int
load_appends(UnpicklerObject *self)
{
    return do_append(self, marker(self));
}

static int
do_setitems(UnpicklerObject *self, Py_ssize_t x)
{
    PyObject *value, *key;
    PyObject *dict;
    Py_ssize_t len, i;
    int status = 0;

    len = (((PyVarObject*)(self->stack))->ob_size);
    if (x > len || x <= 0)
        return stack_underflow();
    if (len == x)
        return 0;
    if ((len - x) % 2 != 0) {

        PyErr_SetString(UnpicklingError, "odd number of items for SETITEMS");
        return -1;
    }



    dict = self->stack->data[x - 1];

    for (i = x + 1; i < len; i += 2) {
        key = self->stack->data[i - 1];
        value = self->stack->data[i];
        if (PyObject_SetItem(dict, key, value) < 0) {
            status = -1;
            break;
        }
    }

    Pdata_clear(self->stack, x);
    return status;
}

static int
load_setitem(UnpicklerObject *self)
{
    return do_setitems(self, (((PyVarObject*)(self->stack))->ob_size) - 2);
}

static int
load_setitems(UnpicklerObject *self)
{
    return do_setitems(self, marker(self));
}

static int
load_build(UnpicklerObject *self)
{
    PyObject *state, *inst, *slotstate;
    PyObject *setstate;
    int status = 0;
    static _Py_Identifier PyId___setstate__ = { 0, "__setstate__", 0 };




    if ((((PyVarObject*)(self->stack))->ob_size) < 2)
        return stack_underflow();

    do { (state) = Pdata_pop((self->stack)); } while (0);
    if (state == ((void *)0))
        return -1;

    inst = self->stack->data[(((PyVarObject*)(self->stack))->ob_size) - 1];

    setstate = _PyObject_GetAttrId(inst, &PyId___setstate__);
    if (setstate == ((void *)0)) {
        if (PyErr_ExceptionMatches(PyExc_AttributeError))
            PyErr_Clear();
        else {
            do { if ( --((PyObject*)(state))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(state)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(state)))); } while (0);
            return -1;
        }
    }
    else {
        PyObject *result;




        result = _Unpickler_FastCall(self, setstate, state);
        do { if ( --((PyObject*)(setstate))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(setstate)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(setstate)))); } while (0);
        if (result == ((void *)0))
            return -1;
        do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0);
        return 0;
    }




    if (((((((PyObject*)(state))->ob_type))->tp_flags & ((1L<<26))) != 0) && (((PyVarObject*)(state))->ob_size) == 2) {
        PyObject *tmp = state;

        state = (((PyTupleObject *)(tmp))->ob_item[0]);
        slotstate = (((PyTupleObject *)(tmp))->ob_item[1]);
        ( ((PyObject*)(state))->ob_refcnt++);
        ( ((PyObject*)(slotstate))->ob_refcnt++);
        do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0);
    }
    else
        slotstate = ((void *)0);


    if (state != (&_Py_NoneStruct)) {
        PyObject *dict;
        PyObject *d_key, *d_value;
        Py_ssize_t i;
        static _Py_Identifier PyId___dict__ = { 0, "__dict__", 0 };

        if (!((((((PyObject*)(state))->ob_type))->tp_flags & ((1L<<29))) != 0)) {
            PyErr_SetString(UnpicklingError, "state is not a dictionary");
            goto error;
        }
        dict = _PyObject_GetAttrId(inst, &PyId___dict__);
        if (dict == ((void *)0))
            goto error;

        i = 0;
        while (PyDict_Next(state, &i, &d_key, &d_value)) {


            ( ((PyObject*)(d_key))->ob_refcnt++);
            if (((((PyObject*)(d_key))->ob_type) == &PyUnicode_Type))
                PyUnicode_InternInPlace(&d_key);
            if (PyObject_SetItem(dict, d_key, d_value) < 0) {
                do { if ( --((PyObject*)(d_key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(d_key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(d_key)))); } while (0);
                goto error;
            }
            do { if ( --((PyObject*)(d_key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(d_key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(d_key)))); } while (0);
        }
        do { if ( --((PyObject*)(dict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dict)))); } while (0);
    }


    if (slotstate != ((void *)0)) {
        PyObject *d_key, *d_value;
        Py_ssize_t i;

        if (!((((((PyObject*)(slotstate))->ob_type))->tp_flags & ((1L<<29))) != 0)) {
            PyErr_SetString(UnpicklingError,
                            "slot state is not a dictionary");
            goto error;
        }
        i = 0;
        while (PyDict_Next(slotstate, &i, &d_key, &d_value)) {
            if (PyObject_SetAttr(inst, d_key, d_value) < 0)
                goto error;
        }
    }

    if (0) {
  error:
        status = -1;
    }

    do { if ( --((PyObject*)(state))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(state)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(state)))); } while (0);
    do { if ((slotstate) == ((void *)0)) ; else do { if ( --((PyObject*)(slotstate))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(slotstate)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(slotstate)))); } while (0); } while (0);
    return status;
}

static int
load_mark(UnpicklerObject *self)
{






    if ((self->num_marks + 1) >= self->marks_size) {
        size_t alloc;
        Py_ssize_t *marks;


        alloc = ((size_t)self->num_marks << 1) + 20;
        if (alloc > (((Py_ssize_t)(((size_t)-1)>>1)) / sizeof(Py_ssize_t)) ||
            alloc <= ((size_t)self->num_marks + 1)) {
            PyErr_NoMemory();
            return -1;
        }

        if (self->marks == ((void *)0))
            marks = (Py_ssize_t *) PyMem_Malloc(alloc * sizeof(Py_ssize_t));
        else
            marks = (Py_ssize_t *) PyMem_Realloc(self->marks,
                                                 alloc * sizeof(Py_ssize_t));
        if (marks == ((void *)0)) {
            PyErr_NoMemory();
            return -1;
        }
        self->marks = marks;
        self->marks_size = (Py_ssize_t)alloc;
    }

    self->marks[self->num_marks++] = (((PyVarObject*)(self->stack))->ob_size);

    return 0;
}

static int
load_reduce(UnpicklerObject *self)
{
    PyObject *callable = ((void *)0);
    PyObject *argtup = ((void *)0);
    PyObject *obj = ((void *)0);

    do { (argtup) = Pdata_pop((self->stack)); } while (0);
    if (argtup == ((void *)0))
        return -1;
    do { (callable) = Pdata_pop((self->stack)); } while (0);
    if (callable) {
        obj = PyObject_CallObject(callable, argtup);
        do { if ( --((PyObject*)(callable))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(callable)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(callable)))); } while (0);
    }
    do { if ( --((PyObject*)(argtup))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(argtup)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(argtup)))); } while (0);

    if (obj == ((void *)0))
        return -1;

    do { if (Pdata_push((self->stack), (obj)) < 0) return (-1); } while(0);
    return 0;
}




static int
load_proto(UnpicklerObject *self)
{
    char *s;
    int i;

    if (_Unpickler_Read(self, &s, 1) < 0)
        return -1;

    i = (unsigned char)s[0];
    if (i <= HIGHEST_PROTOCOL) {
        self->proto = i;
        return 0;
    }

    PyErr_Format(PyExc_ValueError, "unsupported pickle protocol: %d", i);
    return -1;
}

static PyObject *
load(UnpicklerObject *self)
{
    PyObject *err;
    PyObject *value = ((void *)0);
    char *s;

    self->num_marks = 0;
    if ((((PyVarObject*)(self->stack))->ob_size))
        Pdata_clear(self->stack, 0);
# 5331 "_pickle.c"
    while (1) {
        if (_Unpickler_Read(self, &s, 1) < 0)
            break;

        switch ((enum opcode)s[0]) {
        case NONE: if (load_none(self) < 0) break; continue;
        case BININT: if (load_binint(self) < 0) break; continue;
        case BININT1: if (load_binint1(self) < 0) break; continue;
        case BININT2: if (load_binint2(self) < 0) break; continue;
        case INT: if (load_int(self) < 0) break; continue;
        case LONG: if (load_long(self) < 0) break; continue;
        case LONG1: if (load_counted_long(self, (1)) < 0) break; continue;
        case LONG4: if (load_counted_long(self, (4)) < 0) break; continue;
        case FLOAT: if (load_float(self) < 0) break; continue;
        case BINFLOAT: if (load_binfloat(self) < 0) break; continue;
        case BINBYTES: if (load_binbytes(self) < 0) break; continue;
        case SHORT_BINBYTES: if (load_short_binbytes(self) < 0) break; continue;
        case BINSTRING: if (load_binstring(self) < 0) break; continue;
        case SHORT_BINSTRING: if (load_short_binstring(self) < 0) break; continue;
        case STRING: if (load_string(self) < 0) break; continue;
        case UNICODE: if (load_unicode(self) < 0) break; continue;
        case BINUNICODE: if (load_binunicode(self) < 0) break; continue;
        case EMPTY_TUPLE: if (load_counted_tuple(self, (0)) < 0) break; continue;
        case TUPLE1: if (load_counted_tuple(self, (1)) < 0) break; continue;
        case TUPLE2: if (load_counted_tuple(self, (2)) < 0) break; continue;
        case TUPLE3: if (load_counted_tuple(self, (3)) < 0) break; continue;
        case TUPLE: if (load_tuple(self) < 0) break; continue;
        case EMPTY_LIST: if (load_empty_list(self) < 0) break; continue;
        case LIST: if (load_list(self) < 0) break; continue;
        case EMPTY_DICT: if (load_empty_dict(self) < 0) break; continue;
        case DICT: if (load_dict(self) < 0) break; continue;
        case OBJ: if (load_obj(self) < 0) break; continue;
        case INST: if (load_inst(self) < 0) break; continue;
        case NEWOBJ: if (load_newobj(self) < 0) break; continue;
        case GLOBAL: if (load_global(self) < 0) break; continue;
        case APPEND: if (load_append(self) < 0) break; continue;
        case APPENDS: if (load_appends(self) < 0) break; continue;
        case BUILD: if (load_build(self) < 0) break; continue;
        case DUP: if (load_dup(self) < 0) break; continue;
        case BINGET: if (load_binget(self) < 0) break; continue;
        case LONG_BINGET: if (load_long_binget(self) < 0) break; continue;
        case GET: if (load_get(self) < 0) break; continue;
        case MARK: if (load_mark(self) < 0) break; continue;
        case BINPUT: if (load_binput(self) < 0) break; continue;
        case LONG_BINPUT: if (load_long_binput(self) < 0) break; continue;
        case PUT: if (load_put(self) < 0) break; continue;
        case POP: if (load_pop(self) < 0) break; continue;
        case POP_MARK: if (load_pop_mark(self) < 0) break; continue;
        case SETITEM: if (load_setitem(self) < 0) break; continue;
        case SETITEMS: if (load_setitems(self) < 0) break; continue;
        case PERSID: if (load_persid(self) < 0) break; continue;
        case BINPERSID: if (load_binpersid(self) < 0) break; continue;
        case REDUCE: if (load_reduce(self) < 0) break; continue;
        case PROTO: if (load_proto(self) < 0) break; continue;
        case EXT1: if (load_extension(self, (1)) < 0) break; continue;
        case EXT2: if (load_extension(self, (2)) < 0) break; continue;
        case EXT4: if (load_extension(self, (4)) < 0) break; continue;
        case NEWTRUE: if (load_bool(self, (((PyObject *) &_Py_TrueStruct))) < 0) break; continue;
        case NEWFALSE: if (load_bool(self, (((PyObject *) &_Py_FalseStruct))) < 0) break; continue;

        case STOP:
            break;

        default:
            if (s[0] == '\0')
                PyErr_SetNone(PyExc_EOFError);
            else
                PyErr_Format(UnpicklingError,
                             "invalid load key, '%c'.", s[0]);
            return ((void *)0);
        }

        break;
    }

    if (_Unpickler_SkipConsumed(self) < 0)
        return ((void *)0);


    if ((err = PyErr_Occurred())) {
        if (err == PyExc_EOFError) {
            PyErr_SetNone(PyExc_EOFError);
        }
        return ((void *)0);
    }

    do { (value) = Pdata_pop((self->stack)); } while (0);
    return value;
}

static char Unpickler_load_doc[] = "load() -> object. Load a pickle." "\n" "Read a pickled object representation from the open file object given in\n" "the constructor, and return the reconstituted object hierarchy specified\n" "therein.\n";






static PyObject *
Unpickler_load(UnpicklerObject *self)
{




    if (self->read == ((void *)0)) {
        PyErr_Format(UnpicklingError,
                     "Unpickler.__init__() was not called by %s.__init__()",
                     (((PyObject*)(self))->ob_type)->tp_name);
        return ((void *)0);
    }

    return load(self);
}





static char Unpickler_find_class_doc[] = "find_class(module_name, global_name) -> object.\n" "\n" "Return an object from a specified module, importing the module if\n" "necessary.  Subclasses may override this method (e.g. to restrict\n" "unpickling of arbitrary classes and functions).\n" "\n" "This method is called whenever a class or a function object is\n" "needed.  Both arguments passed are str objects.\n";
# 5459 "_pickle.c"
static PyObject *
Unpickler_find_class(UnpicklerObject *self, PyObject *args)
{
    PyObject *global;
    PyObject *modules_dict;
    PyObject *module;
    PyObject *module_name, *global_name;

    if (!PyArg_UnpackTuple(args, "find_class", 2, 2,
                           &module_name, &global_name))
        return ((void *)0);




    if (self->proto < 3 && self->fix_imports) {
        PyObject *key;
        PyObject *item;



        key = PyTuple_Pack(2, module_name, global_name);
        if (key == ((void *)0))
            return ((void *)0);
        item = PyDict_GetItemWithError(name_mapping_2to3, key);
        do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
        if (item) {
            if (!((((((PyObject*)(item))->ob_type))->tp_flags & ((1L<<26))) != 0) || (((PyVarObject*)(item))->ob_size) != 2) {
                PyErr_Format(PyExc_RuntimeError,
                             "_compat_pickle.NAME_MAPPING values should be "
                             "2-tuples, not %.200s", (((PyObject*)(item))->ob_type)->tp_name);
                return ((void *)0);
            }
            module_name = (((PyTupleObject *)(item))->ob_item[0]);
            global_name = (((PyTupleObject *)(item))->ob_item[1]);
            if (!((((((PyObject*)(module_name))->ob_type))->tp_flags & ((1L<<28))) != 0) ||
                !((((((PyObject*)(global_name))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
                PyErr_Format(PyExc_RuntimeError,
                             "_compat_pickle.NAME_MAPPING values should be "
                             "pairs of str, not (%.200s, %.200s)",
                             (((PyObject*)(module_name))->ob_type)->tp_name,
                             (((PyObject*)(global_name))->ob_type)->tp_name);
                return ((void *)0);
            }
        }
        else if (PyErr_Occurred()) {
            return ((void *)0);
        }


        item = PyDict_GetItemWithError(import_mapping_2to3, module_name);
        if (item) {
            if (!((((((PyObject*)(item))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
                PyErr_Format(PyExc_RuntimeError,
                             "_compat_pickle.IMPORT_MAPPING values should be "
                             "strings, not %.200s", (((PyObject*)(item))->ob_type)->tp_name);
                return ((void *)0);
            }
            module_name = item;
        }
        else if (PyErr_Occurred()) {
            return ((void *)0);
        }
    }

    modules_dict = PySys_GetObject("modules");
    if (modules_dict == ((void *)0))
        return ((void *)0);

    module = PyDict_GetItemWithError(modules_dict, module_name);
    if (module == ((void *)0)) {
        if (PyErr_Occurred())
            return ((void *)0);
        module = PyImport_Import(module_name);
        if (module == ((void *)0))
            return ((void *)0);
        global = PyObject_GetAttr(module, global_name);
        do { if ( --((PyObject*)(module))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(module)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(module)))); } while (0);
    }
    else {
        global = PyObject_GetAttr(module, global_name);
    }
    return global;
}

static struct PyMethodDef Unpickler_methods[] = {
    {"load", (PyCFunction)Unpickler_load, 0x0004,
     Unpickler_load_doc},
    {"find_class", (PyCFunction)Unpickler_find_class, 0x0001,
     Unpickler_find_class_doc},
    {((void *)0), ((void *)0)}
};

static void
Unpickler_dealloc(UnpicklerObject *self)
{
    PyObject_GC_UnTrack((PyObject *)self);
    do { if ((self->readline) == ((void *)0)) ; else do { if ( --((PyObject*)(self->readline))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->readline)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->readline)))); } while (0); } while (0);
    do { if ((self->read) == ((void *)0)) ; else do { if ( --((PyObject*)(self->read))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->read)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->read)))); } while (0); } while (0);
    do { if ((self->peek) == ((void *)0)) ; else do { if ( --((PyObject*)(self->peek))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->peek)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->peek)))); } while (0); } while (0);
    do { if ((self->stack) == ((void *)0)) ; else do { if ( --((PyObject*)(self->stack))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->stack)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->stack)))); } while (0); } while (0);
    do { if ((self->pers_func) == ((void *)0)) ; else do { if ( --((PyObject*)(self->pers_func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->pers_func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->pers_func)))); } while (0); } while (0);
    do { if ((self->arg) == ((void *)0)) ; else do { if ( --((PyObject*)(self->arg))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->arg)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->arg)))); } while (0); } while (0);
    if (self->buffer.buf != ((void *)0)) {
        PyBuffer_Release(&self->buffer);
        self->buffer.buf = ((void *)0);
    }

    _Unpickler_MemoCleanup(self);
    PyMem_Free(self->marks);
    PyMem_Free(self->input_line);
    free(self->encoding);
    free(self->errors);

    (((PyObject*)(self))->ob_type)->tp_free((PyObject *)self);
}

static int
Unpickler_traverse(UnpicklerObject *self, visitproc visit, void *arg)
{
    do { if (self->readline) { int vret = visit((PyObject *)(self->readline), arg); if (vret) return vret; } } while (0);
    do { if (self->read) { int vret = visit((PyObject *)(self->read), arg); if (vret) return vret; } } while (0);
    do { if (self->peek) { int vret = visit((PyObject *)(self->peek), arg); if (vret) return vret; } } while (0);
    do { if (self->stack) { int vret = visit((PyObject *)(self->stack), arg); if (vret) return vret; } } while (0);
    do { if (self->pers_func) { int vret = visit((PyObject *)(self->pers_func), arg); if (vret) return vret; } } while (0);
    do { if (self->arg) { int vret = visit((PyObject *)(self->arg), arg); if (vret) return vret; } } while (0);
    return 0;
}

static int
Unpickler_clear(UnpicklerObject *self)
{
    do { if (self->readline) { PyObject *_py_tmp = (PyObject *)(self->readline); (self->readline) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (self->read) { PyObject *_py_tmp = (PyObject *)(self->read); (self->read) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (self->peek) { PyObject *_py_tmp = (PyObject *)(self->peek); (self->peek) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (self->stack) { PyObject *_py_tmp = (PyObject *)(self->stack); (self->stack) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (self->pers_func) { PyObject *_py_tmp = (PyObject *)(self->pers_func); (self->pers_func) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (self->arg) { PyObject *_py_tmp = (PyObject *)(self->arg); (self->arg) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    if (self->buffer.buf != ((void *)0)) {
        PyBuffer_Release(&self->buffer);
        self->buffer.buf = ((void *)0);
    }

    _Unpickler_MemoCleanup(self);
    PyMem_Free(self->marks);
    self->marks = ((void *)0);
    PyMem_Free(self->input_line);
    self->input_line = ((void *)0);
    free(self->encoding);
    self->encoding = ((void *)0);
    free(self->errors);
    self->errors = ((void *)0);

    return 0;
}

static char Unpickler_doc[] = "Unpickler(file, *, encoding='ASCII', errors='strict')" "\n" "This takes a binary file for reading a pickle data stream.\n" "\n" "The protocol version of the pickle is detected automatically, so no\n" "proto argument is needed.\n" "\n" "The file-like object must have two methods, a read() method\n" "that takes an integer argument, and a readline() method that\n" "requires no arguments.  Both methods should return bytes.\n" "Thus file-like object can be a binary file object opened for\n" "reading, a BytesIO object, or any other custom object that\n" "meets this interface.\n" "\n" "Optional keyword arguments are *fix_imports*, *encoding* and *errors*,\n" "which are used to control compatiblity support for pickle stream\n" "generated by Python 2.x.  If *fix_imports* is True, pickle will try to\n" "map the old Python 2.x names to the new names used in Python 3.x.  The\n" "*encoding* and *errors* tell pickle how to decode 8-bit string\n" "instances pickled by Python 2.x; these default to 'ASCII' and\n" "'strict', respectively.\n";
# 5638 "_pickle.c"
static int
Unpickler_init(UnpicklerObject *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"file", "fix_imports", "encoding", "errors", 0};
    PyObject *file;
    PyObject *fix_imports = ((PyObject *) &_Py_TrueStruct);
    char *encoding = ((void *)0);
    char *errors = ((void *)0);
    static _Py_Identifier PyId_persistent_load = { 0, "persistent_load", 0 };



    if ((((PyVarObject*)(args))->ob_size) != 1) {
        PyErr_Format(PyExc_TypeError,
                     "%s takes exactly one positional argument (%zd given)",
                     (((PyObject*)(self))->ob_type)->tp_name, (((PyVarObject*)(args))->ob_size));
        return -1;
    }







    if (!PyArg_ParseTupleAndKeywords(args, kwds, "O|Oss:Unpickler", kwlist,
                                     &file, &fix_imports, &encoding, &errors))
        return -1;


    if (self->read != ((void *)0))
        (void)Unpickler_clear(self);

    if (_Unpickler_SetInputStream(self, file) < 0)
        return -1;

    if (_Unpickler_SetInputEncoding(self, encoding, errors) < 0)
        return -1;

    self->fix_imports = PyObject_IsTrue(fix_imports);
    if (self->fix_imports == -1)
        return -1;

    if (_PyObject_HasAttrId((PyObject *)self, &PyId_persistent_load)) {
        self->pers_func = _PyObject_GetAttrId((PyObject *)self,
                                              &PyId_persistent_load);
        if (self->pers_func == ((void *)0))
            return -1;
    }
    else {
        self->pers_func = ((void *)0);
    }

    self->stack = (Pdata *)Pdata_New();
    if (self->stack == ((void *)0))
        return -1;

    self->memo_size = 32;
    self->memo = _Unpickler_NewMemo(self->memo_size);
    if (self->memo == ((void *)0))
        return -1;

    self->arg = ((void *)0);
    self->proto = 0;

    return 0;
}
# 5719 "_pickle.c"
typedef struct {
    PyObject ob_base;
    UnpicklerObject *unpickler;
} UnpicklerMemoProxyObject;

static char ump_clear_doc[] = "memo.clear() -> None.  Remove all items from memo.";


static PyObject *
ump_clear(UnpicklerMemoProxyObject *self)
{
    _Unpickler_MemoCleanup(self->unpickler);
    self->unpickler->memo = _Unpickler_NewMemo(self->unpickler->memo_size);
    if (self->unpickler->memo == ((void *)0))
        return ((void *)0);
    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}

static char ump_copy_doc[] = "memo.copy() -> new_memo.  Copy the memo to a new object.";


static PyObject *
ump_copy(UnpicklerMemoProxyObject *self)
{
    Py_ssize_t i;
    PyObject *new_memo = PyDict_New();
    if (new_memo == ((void *)0))
        return ((void *)0);

    for (i = 0; i < self->unpickler->memo_size; i++) {
        int status;
        PyObject *key, *value;

        value = self->unpickler->memo[i];
        if (value == ((void *)0))
            continue;

        key = PyLong_FromSsize_t(i);
        if (key == ((void *)0))
            goto error;
        status = PyDict_SetItem(new_memo, key, value);
        do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
        if (status < 0)
            goto error;
    }
    return new_memo;

error:
    do { if ( --((PyObject*)(new_memo))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(new_memo)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(new_memo)))); } while (0);
    return ((void *)0);
}

static char ump_reduce_doc[] = "memo.__reduce__(). Pickling support.";


static PyObject *
ump_reduce(UnpicklerMemoProxyObject *self, PyObject *args)
{
    PyObject *reduce_value;
    PyObject *constructor_args;
    PyObject *contents = ump_copy(self);
    if (contents == ((void *)0))
        return ((void *)0);

    reduce_value = PyTuple_New(2);
    if (reduce_value == ((void *)0)) {
        do { if ( --((PyObject*)(contents))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(contents)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(contents)))); } while (0);
        return ((void *)0);
    }
    constructor_args = PyTuple_New(1);
    if (constructor_args == ((void *)0)) {
        do { if ( --((PyObject*)(contents))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(contents)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(contents)))); } while (0);
        do { if ( --((PyObject*)(reduce_value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(reduce_value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(reduce_value)))); } while (0);
        return ((void *)0);
    }
    (((PyTupleObject *)(constructor_args))->ob_item[0] = contents);
    ( ((PyObject*)((PyObject *)&PyDict_Type))->ob_refcnt++);
    (((PyTupleObject *)(reduce_value))->ob_item[0] = (PyObject *)&PyDict_Type);
    (((PyTupleObject *)(reduce_value))->ob_item[1] = constructor_args);
    return reduce_value;
}

static PyMethodDef unpicklerproxy_methods[] = {
    {"clear", (PyCFunction)ump_clear, 0x0004, ump_clear_doc},
    {"copy", (PyCFunction)ump_copy, 0x0004, ump_copy_doc},
    {"__reduce__", (PyCFunction)ump_reduce, 0x0001, ump_reduce_doc},
    {((void *)0), ((void *)0)}
};

static void
UnpicklerMemoProxy_dealloc(UnpicklerMemoProxyObject *self)
{
    PyObject_GC_UnTrack(self);
    do { if ((self->unpickler) == ((void *)0)) ; else do { if ( --((PyObject*)(self->unpickler))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->unpickler)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->unpickler)))); } while (0); } while (0);
    PyObject_GC_Del((PyObject *)self);
}

static int
UnpicklerMemoProxy_traverse(UnpicklerMemoProxyObject *self,
                            visitproc visit, void *arg)
{
    do { if (self->unpickler) { int vret = visit((PyObject *)(self->unpickler), arg); if (vret) return vret; } } while (0);
    return 0;
}

static int
UnpicklerMemoProxy_clear(UnpicklerMemoProxyObject *self)
{
    do { if (self->unpickler) { PyObject *_py_tmp = (PyObject *)(self->unpickler); (self->unpickler) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    return 0;
}

static PyTypeObject UnpicklerMemoProxyType = {
    { { 1, ((void *)0) }, 0 },
    "_pickle.UnpicklerMemoProxy",
    sizeof(UnpicklerMemoProxyObject),
    0,
    (destructor)UnpicklerMemoProxy_dealloc,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    PyObject_HashNotImplemented,
    0,
    0,
    PyObject_GenericGetAttr,
    PyObject_GenericSetAttr,
    0,
    ( 0 | (1L<<18) | 0) | (1L<<10) | (1L<<14),
    0,
    (traverseproc)UnpicklerMemoProxy_traverse,
    (inquiry)UnpicklerMemoProxy_clear,
    0,
    0,
    0,
    0,
    unpicklerproxy_methods,
};

static PyObject *
UnpicklerMemoProxy_New(UnpicklerObject *unpickler)
{
    UnpicklerMemoProxyObject *self;

    self = ( (UnpicklerMemoProxyObject *) _PyObject_GC_New(&UnpicklerMemoProxyType) );

    if (self == ((void *)0))
        return ((void *)0);
    ( ((PyObject*)(unpickler))->ob_refcnt++);
    self->unpickler = unpickler;
    PyObject_GC_Track(self);
    return (PyObject *)self;
}




static PyObject *
Unpickler_get_memo(UnpicklerObject *self)
{
    return UnpicklerMemoProxy_New(self);
}

static int
Unpickler_set_memo(UnpicklerObject *self, PyObject *obj)
{
    PyObject **new_memo;
    Py_ssize_t new_memo_size = 0;
    Py_ssize_t i;

    if (obj == ((void *)0)) {
        PyErr_SetString(PyExc_TypeError,
                        "attribute deletion is not supported");
        return -1;
    }

    if ((((PyObject*)(obj))->ob_type) == &UnpicklerMemoProxyType) {
        UnpicklerObject *unpickler =
            ((UnpicklerMemoProxyObject *)obj)->unpickler;

        new_memo_size = unpickler->memo_size;
        new_memo = _Unpickler_NewMemo(new_memo_size);
        if (new_memo == ((void *)0))
            return -1;

        for (i = 0; i < new_memo_size; i++) {
            do { if ((unpickler->memo[i]) == ((void *)0)) ; else ( ((PyObject*)(unpickler->memo[i]))->ob_refcnt++); } while (0);
            new_memo[i] = unpickler->memo[i];
        }
    }
    else if (((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<29))) != 0)) {
        Py_ssize_t i = 0;
        PyObject *key, *value;

        new_memo_size = PyDict_Size(obj);
        new_memo = _Unpickler_NewMemo(new_memo_size);
        if (new_memo == ((void *)0))
            return -1;

        while (PyDict_Next(obj, &i, &key, &value)) {
            Py_ssize_t idx;
            if (!((((((PyObject*)(key))->ob_type))->tp_flags & ((1L<<24))) != 0)) {
                PyErr_SetString(PyExc_TypeError,
                                "memo key must be integers");
                goto error;
            }
            idx = PyLong_AsSsize_t(key);
            if (idx == -1 && PyErr_Occurred())
                goto error;
            if (_Unpickler_MemoPut(self, idx, value) < 0)
                goto error;
        }
    }
    else {
        PyErr_Format(PyExc_TypeError,
                     "'memo' attribute must be an UnpicklerMemoProxy object"
                     "or dict, not %.200s", (((PyObject*)(obj))->ob_type)->tp_name);
        return -1;
    }

    _Unpickler_MemoCleanup(self);
    self->memo_size = new_memo_size;
    self->memo = new_memo;

    return 0;

  error:
    if (new_memo_size) {
        i = new_memo_size;
        while (--i >= 0) {
            do { if ((new_memo[i]) == ((void *)0)) ; else do { if ( --((PyObject*)(new_memo[i]))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(new_memo[i])))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(new_memo[i])))); } while (0); } while (0);
        }
        free(new_memo);
    }
    return -1;
}

static PyObject *
Unpickler_get_persload(UnpicklerObject *self)
{
    if (self->pers_func == ((void *)0))
        PyErr_SetString(PyExc_AttributeError, "persistent_load");
    else
        ( ((PyObject*)(self->pers_func))->ob_refcnt++);
    return self->pers_func;
}

static int
Unpickler_set_persload(UnpicklerObject *self, PyObject *value)
{
    PyObject *tmp;

    if (value == ((void *)0)) {
        PyErr_SetString(PyExc_TypeError,
                        "attribute deletion is not supported");
        return -1;
    }
    if (!PyCallable_Check(value)) {
        PyErr_SetString(PyExc_TypeError,
                        "persistent_load must be a callable taking "
                        "one argument");
        return -1;
    }

    tmp = self->pers_func;
    ( ((PyObject*)(value))->ob_refcnt++);
    self->pers_func = value;
    do { if ((tmp) == ((void *)0)) ; else do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0); } while (0);

    return 0;
}

static PyGetSetDef Unpickler_getsets[] = {
    {"memo", (getter)Unpickler_get_memo, (setter)Unpickler_set_memo},
    {"persistent_load", (getter)Unpickler_get_persload,
                        (setter)Unpickler_set_persload},
    {((void *)0)}
};

static PyTypeObject Unpickler_Type = {
    { { 1, ((void *)0) }, 0 },
    "_pickle.Unpickler",
    sizeof(UnpicklerObject),
    0,
    (destructor)Unpickler_dealloc,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    ( 0 | (1L<<18) | 0) | (1L<<10) | (1L<<14),
    Unpickler_doc,
    (traverseproc)Unpickler_traverse,
    (inquiry)Unpickler_clear,
    0,
    0,
    0,
    0,
    Unpickler_methods,
    0,
    Unpickler_getsets,
    0,
    0,
    0,
    0,
    0,
    (initproc)Unpickler_init,
    PyType_GenericAlloc,
    PyType_GenericNew,
    PyObject_GC_Del,
    0,
};

static char pickle_dump_doc[] = "dump(obj, file, protocol=None, *, fix_imports=True) -> None\n" "\n" "Write a pickled representation of obj to the open file object file.  This\n" "is equivalent to ``Pickler(file, protocol).dump(obj)``, but may be more\n" "efficient.\n" "\n" "The optional protocol argument tells the pickler to use the given protocol;\n" "supported protocols are 0, 1, 2, 3.  The default protocol is 3; a\n" "backward-incompatible protocol designed for Python 3.0.\n" "\n" "Specifying a negative protocol version selects the highest protocol version\n" "supported.  The higher the protocol used, the more recent the version of\n" "Python needed to read the pickle produced.\n" "\n" "The file argument must have a write() method that accepts a single bytes\n" "argument.  It can thus be a file object opened for binary writing, a\n" "io.BytesIO instance, or any other custom object that meets this interface.\n" "\n" "If fix_imports is True and protocol is less than 3, pickle will try to\n" "map the new Python 3.x names to the old module names used in Python 2.x,\n" "so that the pickle data stream is readable with Python 2.x.\n";
# 6068 "_pickle.c"
static PyObject *
pickle_dump(PyObject *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"obj", "file", "protocol", "fix_imports", 0};
    PyObject *obj;
    PyObject *file;
    PyObject *proto = ((void *)0);
    PyObject *fix_imports = ((PyObject *) &_Py_TrueStruct);
    PicklerObject *pickler;


    if ((((PyVarObject*)(args))->ob_size) > 3) {
        PyErr_Format(PyExc_TypeError,
                     "pickle.dump() takes at most 3 positional "
                     "argument (%zd given)", (((PyVarObject*)(args))->ob_size));
        return ((void *)0);
    }

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "OO|OO:dump", kwlist,
                                     &obj, &file, &proto, &fix_imports))
        return ((void *)0);

    pickler = _Pickler_New();
    if (pickler == ((void *)0))
        return ((void *)0);

    if (_Pickler_SetProtocol(pickler, proto, fix_imports) < 0)
        goto error;

    if (_Pickler_SetOutputStream(pickler, file) < 0)
        goto error;

    if (dump(pickler, obj) < 0)
        goto error;

    if (_Pickler_FlushToFile(pickler) < 0)
        goto error;

    do { if ( --((PyObject*)(pickler))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pickler)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pickler)))); } while (0);
    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);

  error:
    do { if ((pickler) == ((void *)0)) ; else do { if ( --((PyObject*)(pickler))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pickler)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pickler)))); } while (0); } while (0);
    return ((void *)0);
}

static char pickle_dumps_doc[] = "dumps(obj, protocol=None, *, fix_imports=True) -> bytes\n" "\n" "Return the pickled representation of the object as a bytes\n" "object, instead of writing it to a file.\n" "\n" "The optional protocol argument tells the pickler to use the given protocol;\n" "supported protocols are 0, 1, 2, 3.  The default protocol is 3; a\n" "backward-incompatible protocol designed for Python 3.0.\n" "\n" "Specifying a negative protocol version selects the highest protocol version\n" "supported.  The higher the protocol used, the more recent the version of\n" "Python needed to read the pickle produced.\n" "\n" "If fix_imports is True and *protocol* is less than 3, pickle will try to\n" "map the new Python 3.x names to the old module names used in Python 2.x,\n" "so that the pickle data stream is readable with Python 2.x.\n";
# 6132 "_pickle.c"
static PyObject *
pickle_dumps(PyObject *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"obj", "protocol", "fix_imports", 0};
    PyObject *obj;
    PyObject *proto = ((void *)0);
    PyObject *result;
    PyObject *fix_imports = ((PyObject *) &_Py_TrueStruct);
    PicklerObject *pickler;


    if ((((PyVarObject*)(args))->ob_size) > 2) {
        PyErr_Format(PyExc_TypeError,
                     "pickle.dumps() takes at most 2 positional "
                     "argument (%zd given)", (((PyVarObject*)(args))->ob_size));
        return ((void *)0);
    }

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "O|OO:dumps", kwlist,
                                     &obj, &proto, &fix_imports))
        return ((void *)0);

    pickler = _Pickler_New();
    if (pickler == ((void *)0))
        return ((void *)0);

    if (_Pickler_SetProtocol(pickler, proto, fix_imports) < 0)
        goto error;

    if (dump(pickler, obj) < 0)
        goto error;

    result = _Pickler_GetString(pickler);
    do { if ( --((PyObject*)(pickler))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pickler)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pickler)))); } while (0);
    return result;

  error:
    do { if ((pickler) == ((void *)0)) ; else do { if ( --((PyObject*)(pickler))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pickler)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pickler)))); } while (0); } while (0);
    return ((void *)0);
}

static char pickle_load_doc[] = "load(file, *, fix_imports=True, encoding='ASCII', errors='strict') -> object\n" "\n" "Read a pickled object representation from the open file object file and\n" "return the reconstituted object hierarchy specified therein.  This is\n" "equivalent to ``Unpickler(file).load()``, but may be more efficient.\n" "\n" "The protocol version of the pickle is detected automatically, so no protocol\n" "argument is needed.  Bytes past the pickled object's representation are\n" "ignored.\n" "\n" "The argument file must have two methods, a read() method that takes an\n" "integer argument, and a readline() method that requires no arguments.  Both\n" "methods should return bytes.  Thus *file* can be a binary file object opened\n" "for reading, a BytesIO object, or any other custom object that meets this\n" "interface.\n" "\n" "Optional keyword arguments are fix_imports, encoding and errors,\n" "which are used to control compatiblity support for pickle stream generated\n" "by Python 2.x.  If fix_imports is True, pickle will try to map the old\n" "Python 2.x names to the new names used in Python 3.x.  The encoding and\n" "errors tell pickle how to decode 8-bit string instances pickled by Python\n" "2.x; these default to 'ASCII' and 'strict', respectively.\n";
# 6197 "_pickle.c"
static PyObject *
pickle_load(PyObject *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"file", "fix_imports", "encoding", "errors", 0};
    PyObject *file;
    PyObject *fix_imports = ((PyObject *) &_Py_TrueStruct);
    PyObject *result;
    char *encoding = ((void *)0);
    char *errors = ((void *)0);
    UnpicklerObject *unpickler;


    if ((((PyVarObject*)(args))->ob_size) != 1) {
        PyErr_Format(PyExc_TypeError,
                     "pickle.load() takes exactly one positional "
                     "argument (%zd given)", (((PyVarObject*)(args))->ob_size));
        return ((void *)0);
    }

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "O|Oss:load", kwlist,
                                     &file, &fix_imports, &encoding, &errors))
        return ((void *)0);

    unpickler = _Unpickler_New();
    if (unpickler == ((void *)0))
        return ((void *)0);

    if (_Unpickler_SetInputStream(unpickler, file) < 0)
        goto error;

    if (_Unpickler_SetInputEncoding(unpickler, encoding, errors) < 0)
        goto error;

    unpickler->fix_imports = PyObject_IsTrue(fix_imports);
    if (unpickler->fix_imports == -1)
        goto error;

    result = load(unpickler);
    do { if ( --((PyObject*)(unpickler))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(unpickler)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(unpickler)))); } while (0);
    return result;

  error:
    do { if ((unpickler) == ((void *)0)) ; else do { if ( --((PyObject*)(unpickler))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(unpickler)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(unpickler)))); } while (0); } while (0);
    return ((void *)0);
}

static char pickle_loads_doc[] = "loads(input, *, fix_imports=True, encoding='ASCII', errors='strict') -> object\n" "\n" "Read a pickled object hierarchy from a bytes object and return the\n" "reconstituted object hierarchy specified therein\n" "\n" "The protocol version of the pickle is detected automatically, so no protocol\n" "argument is needed.  Bytes past the pickled object's representation are\n" "ignored.\n" "\n" "Optional keyword arguments are fix_imports, encoding and errors, which\n" "are used to control compatiblity support for pickle stream generated\n" "by Python 2.x.  If fix_imports is True, pickle will try to map the old\n" "Python 2.x names to the new names used in Python 3.x.  The encoding and\n" "errors tell pickle how to decode 8-bit string instances pickled by Python\n" "2.x; these default to 'ASCII' and 'strict', respectively.\n";
# 6260 "_pickle.c"
static PyObject *
pickle_loads(PyObject *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"input", "fix_imports", "encoding", "errors", 0};
    PyObject *input;
    PyObject *fix_imports = ((PyObject *) &_Py_TrueStruct);
    PyObject *result;
    char *encoding = ((void *)0);
    char *errors = ((void *)0);
    UnpicklerObject *unpickler;


    if ((((PyVarObject*)(args))->ob_size) != 1) {
        PyErr_Format(PyExc_TypeError,
                     "pickle.loads() takes exactly one positional "
                     "argument (%zd given)", (((PyVarObject*)(args))->ob_size));
        return ((void *)0);
    }

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "O|Oss:loads", kwlist,
                                     &input, &fix_imports, &encoding, &errors))
        return ((void *)0);

    unpickler = _Unpickler_New();
    if (unpickler == ((void *)0))
        return ((void *)0);

    if (_Unpickler_SetStringInput(unpickler, input) < 0)
        goto error;

    if (_Unpickler_SetInputEncoding(unpickler, encoding, errors) < 0)
        goto error;

    unpickler->fix_imports = PyObject_IsTrue(fix_imports);
    if (unpickler->fix_imports == -1)
        goto error;

    result = load(unpickler);
    do { if ( --((PyObject*)(unpickler))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(unpickler)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(unpickler)))); } while (0);
    return result;

  error:
    do { if ((unpickler) == ((void *)0)) ; else do { if ( --((PyObject*)(unpickler))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(unpickler)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(unpickler)))); } while (0); } while (0);
    return ((void *)0);
}


static struct PyMethodDef pickle_methods[] = {
    {"dump", (PyCFunction)pickle_dump, 0x0001|0x0002,
     pickle_dump_doc},
    {"dumps", (PyCFunction)pickle_dumps, 0x0001|0x0002,
     pickle_dumps_doc},
    {"load", (PyCFunction)pickle_load, 0x0001|0x0002,
     pickle_load_doc},
    {"loads", (PyCFunction)pickle_loads, 0x0001|0x0002,
     pickle_loads_doc},
    {((void *)0), ((void *)0)}
};

static int
initmodule(void)
{
    PyObject *copyreg = ((void *)0);
    PyObject *compat_pickle = ((void *)0);





    copyreg = PyImport_ImportModule("copyreg");
    if (!copyreg)
        goto error;
    dispatch_table = PyObject_GetAttrString(copyreg, "dispatch_table");
    if (!dispatch_table)
        goto error;
    extension_registry = PyObject_GetAttrString(copyreg, "_extension_registry");

    if (!extension_registry)
        goto error;
    inverted_registry = PyObject_GetAttrString(copyreg, "_inverted_registry");
    if (!inverted_registry)
        goto error;
    extension_cache = PyObject_GetAttrString(copyreg, "_extension_cache");
    if (!extension_cache)
        goto error;
    do { if (copyreg) { PyObject *_py_tmp = (PyObject *)(copyreg); (copyreg) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);


    compat_pickle = PyImport_ImportModule("_compat_pickle");
    if (!compat_pickle)
        goto error;
    name_mapping_2to3 = PyObject_GetAttrString(compat_pickle, "NAME_MAPPING");
    if (!name_mapping_2to3)
        goto error;
    if (!((((PyObject*)(name_mapping_2to3))->ob_type) == &PyDict_Type)) {
        PyErr_Format(PyExc_RuntimeError,
                     "_compat_pickle.NAME_MAPPING should be a dict, not %.200s",
                     (((PyObject*)(name_mapping_2to3))->ob_type)->tp_name);
        goto error;
    }
    import_mapping_2to3 = PyObject_GetAttrString(compat_pickle,
                                                 "IMPORT_MAPPING");
    if (!import_mapping_2to3)
        goto error;
    if (!((((PyObject*)(import_mapping_2to3))->ob_type) == &PyDict_Type)) {
        PyErr_Format(PyExc_RuntimeError,
                     "_compat_pickle.IMPORT_MAPPING should be a dict, "
                     "not %.200s", (((PyObject*)(import_mapping_2to3))->ob_type)->tp_name);
        goto error;
    }

    name_mapping_3to2 = PyObject_GetAttrString(compat_pickle,
                                               "REVERSE_NAME_MAPPING");
    if (!name_mapping_3to2)
        goto error;
    if (!((((PyObject*)(name_mapping_3to2))->ob_type) == &PyDict_Type)) {
        PyErr_Format(PyExc_RuntimeError,
                     "_compat_pickle.REVERSE_NAME_MAPPING should be a dict, "
                     "not %.200s", (((PyObject*)(name_mapping_3to2))->ob_type)->tp_name);
        goto error;
    }
    import_mapping_3to2 = PyObject_GetAttrString(compat_pickle,
                                                 "REVERSE_IMPORT_MAPPING");
    if (!import_mapping_3to2)
        goto error;
    if (!((((PyObject*)(import_mapping_3to2))->ob_type) == &PyDict_Type)) {
        PyErr_Format(PyExc_RuntimeError,
                     "_compat_pickle.REVERSE_IMPORT_MAPPING should be a dict, "
                     "not %.200s", (((PyObject*)(import_mapping_3to2))->ob_type)->tp_name);
        goto error;
    }
    do { if (compat_pickle) { PyObject *_py_tmp = (PyObject *)(compat_pickle); (compat_pickle) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);

    empty_tuple = PyTuple_New(0);
    if (empty_tuple == ((void *)0))
        goto error;
    two_tuple = PyTuple_New(2);
    if (two_tuple == ((void *)0))
        goto error;




    PyObject_GC_UnTrack(two_tuple);

    return 0;

  error:
    do { if (copyreg) { PyObject *_py_tmp = (PyObject *)(copyreg); (copyreg) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (dispatch_table) { PyObject *_py_tmp = (PyObject *)(dispatch_table); (dispatch_table) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (extension_registry) { PyObject *_py_tmp = (PyObject *)(extension_registry); (extension_registry) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (inverted_registry) { PyObject *_py_tmp = (PyObject *)(inverted_registry); (inverted_registry) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (extension_cache) { PyObject *_py_tmp = (PyObject *)(extension_cache); (extension_cache) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (compat_pickle) { PyObject *_py_tmp = (PyObject *)(compat_pickle); (compat_pickle) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (name_mapping_2to3) { PyObject *_py_tmp = (PyObject *)(name_mapping_2to3); (name_mapping_2to3) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (import_mapping_2to3) { PyObject *_py_tmp = (PyObject *)(import_mapping_2to3); (import_mapping_2to3) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (name_mapping_3to2) { PyObject *_py_tmp = (PyObject *)(name_mapping_3to2); (name_mapping_3to2) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (import_mapping_3to2) { PyObject *_py_tmp = (PyObject *)(import_mapping_3to2); (import_mapping_3to2) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (empty_tuple) { PyObject *_py_tmp = (PyObject *)(empty_tuple); (empty_tuple) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (two_tuple) { PyObject *_py_tmp = (PyObject *)(two_tuple); (two_tuple) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    return -1;
}

static struct PyModuleDef _picklemodule = {
    { { 1, ((void *)0) }, ((void *)0), 0, ((void *)0), },
    "_pickle",
    pickle_module_doc,
    -1,
    pickle_methods,
    ((void *)0),
    ((void *)0),
    ((void *)0),
    ((void *)0)
};

PyObject*
PyInit__pickle(void)
{
    PyObject *m;

    if (PyType_Ready(&Unpickler_Type) < 0)
        return ((void *)0);
    if (PyType_Ready(&Pickler_Type) < 0)
        return ((void *)0);
    if (PyType_Ready(&Pdata_Type) < 0)
        return ((void *)0);
    if (PyType_Ready(&PicklerMemoProxyType) < 0)
        return ((void *)0);
    if (PyType_Ready(&UnpicklerMemoProxyType) < 0)
        return ((void *)0);


    m = PyModule_Create2(&_picklemodule, 1013);
    if (m == ((void *)0))
        return ((void *)0);

    ( ((PyObject*)(&Pickler_Type))->ob_refcnt++);
    if (PyModule_AddObject(m, "Pickler", (PyObject *)&Pickler_Type) < 0)
        return ((void *)0);
    ( ((PyObject*)(&Unpickler_Type))->ob_refcnt++);
    if (PyModule_AddObject(m, "Unpickler", (PyObject *)&Unpickler_Type) < 0)
        return ((void *)0);


    PickleError = PyErr_NewException("_pickle.PickleError", ((void *)0), ((void *)0));
    if (PickleError == ((void *)0))
        return ((void *)0);
    PicklingError = PyErr_NewException("_pickle.PicklingError", PickleError, ((void *)0));

    if (PicklingError == ((void *)0))
        return ((void *)0);
    UnpicklingError = PyErr_NewException("_pickle.UnpicklingError", PickleError, ((void *)0));

    if (UnpicklingError == ((void *)0))
        return ((void *)0);

    if (PyModule_AddObject(m, "PickleError", PickleError) < 0)
        return ((void *)0);
    if (PyModule_AddObject(m, "PicklingError", PicklingError) < 0)
        return ((void *)0);
    if (PyModule_AddObject(m, "UnpicklingError", UnpicklingError) < 0)
        return ((void *)0);

    if (initmodule() < 0)
        return ((void *)0);

    return m;
}
