# 1 "_cursesmodule.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "_cursesmodule.c"
# 99 "_cursesmodule.c"
char *PyCursesVersion = "2.2";





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
# 28 "/Users/parrt/tmp/Python-3.3.1/Include/modsupport.h"
int _PyArg_Parse_SizeT(PyObject *, const char *, ...);
int _PyArg_ParseTuple_SizeT(PyObject *, const char *, ...) ;
int _PyArg_ParseTupleAndKeywords_SizeT(PyObject *, PyObject *,
                                                  const char *, char **, ...);
int PyArg_ValidateKeywordArguments(PyObject *);
int PyArg_UnpackTuple(PyObject *, const char *, Py_ssize_t, Py_ssize_t, ...);
PyObject * _Py_BuildValue_SizeT(const char *, ...);
PyObject * _Py_BuildValue_SizeT(const char *, ...);


int _PyArg_NoKeywords(const char *funcname, PyObject *kw);

int _PyArg_VaParse_SizeT(PyObject *, const char *, va_list);
int _PyArg_VaParseTupleAndKeywords_SizeT(PyObject *, PyObject *,
                                                  const char *, char **, va_list);

PyObject * _Py_VaBuildValue_SizeT(const char *, va_list);

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
     PyObject * _PyObject_CallFunction_SizeT(PyObject *callable_object,
                                                  char *format, ...);
# 299 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * _PyObject_CallMethod_SizeT(PyObject *o, char *method,
                                                char *format, ...);
# 311 "/Users/parrt/tmp/Python-3.3.1/Include/abstract.h"
     PyObject * _PyObject_CallMethodId_SizeT(PyObject *o, _Py_Identifier *method,
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
# 106 "_cursesmodule.c" 2







# 1 "/Users/parrt/tmp/Python-3.3.1/Include/py_curses.h" 1
# 48 "/Users/parrt/tmp/Python-3.3.1/Include/py_curses.h"
# 1 "/usr/include/ncurses.h" 1 3 4
# 66 "/usr/include/ncurses.h" 3 4
# 1 "/usr/include/ncurses_dll.h" 1 3 4
# 67 "/usr/include/ncurses.h" 2 3 4
# 136 "/usr/include/ncurses.h" 3 4
typedef unsigned int chtype;
typedef unsigned long mmask_t;



# 1 "/usr/include/unctrl.h" 1 3 4
# 54 "/usr/include/unctrl.h" 3 4
# 1 "/usr/include/curses.h" 1 3 4
# 55 "/usr/include/unctrl.h" 2 3 4


 char * unctrl (chtype);
# 142 "/usr/include/ncurses.h" 2 3 4
# 165 "/usr/include/ncurses.h" 3 4
typedef unsigned char NCURSES_BOOL;
# 175 "/usr/include/ncurses.h" 3 4
# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stdbool.h" 1 3 4
# 176 "/usr/include/ncurses.h" 2 3 4
# 231 "/usr/include/ncurses.h" 3 4
extern chtype acs_map[];
# 321 "/usr/include/ncurses.h" 3 4
typedef struct screen SCREEN;
typedef struct _win_st WINDOW;

typedef chtype attr_t;
# 363 "/usr/include/ncurses.h" 3 4
struct ldat;

struct _win_st
{
 short _cury, _curx;


 short _maxy, _maxx;
 short _begy, _begx;

 short _flags;


 attr_t _attrs;
 chtype _bkgd;


 _Bool _notimeout;
 _Bool _clear;
 _Bool _leaveok;
 _Bool _scroll;
 _Bool _idlok;
 _Bool _idcok;
 _Bool _immed;
 _Bool _sync;
 _Bool _use_keypad;
 int _delay;

 struct ldat *_line;


 short _regtop;
 short _regbottom;


 int _parx;
 int _pary;
 WINDOW *_parent;


 struct pdat
 {
     short _pad_y, _pad_x;
     short _pad_top, _pad_left;
     short _pad_bottom, _pad_right;
 } _pad;

 short _yoffset;







};
# 520 "/usr/include/ncurses.h" 3 4
extern int addch (const chtype);
extern int addchnstr (const chtype *, int);
extern int addchstr (const chtype *);
extern int addnstr (const char *, int);
extern int addstr (const char *);
extern int attroff (int);
extern int attron (int);
extern int attrset (int);
extern int attr_get (attr_t *, short *, void *);
extern int attr_off (attr_t, void *);
extern int attr_on (attr_t, void *);
extern int attr_set (attr_t, short, void *);
extern int baudrate (void);
extern int beep (void);
extern int bkgd (chtype);
extern void bkgdset (chtype);
extern int border (chtype,chtype,chtype,chtype,chtype,chtype,chtype,chtype);
extern int box (WINDOW *, chtype, chtype);
extern _Bool can_change_color (void);
extern int cbreak (void);
extern int chgat (int, attr_t, short, const void *);
extern int clear (void);
extern int clearok (WINDOW *,_Bool);
extern int clrtobot (void);
extern int clrtoeol (void);
extern int color_content (short,short*,short*,short*);
extern int color_set (short,void*);
extern int COLOR_PAIR (int);
extern int copywin (const WINDOW*,WINDOW*,int,int,int,int,int,int,int);
extern int curs_set (int);
extern int def_prog_mode (void);
extern int def_shell_mode (void);
extern int delay_output (int);
extern int delch (void);
extern void delscreen (SCREEN *);
extern int delwin (WINDOW *);
extern int deleteln (void);
extern WINDOW * derwin (WINDOW *,int,int,int,int);
extern int doupdate (void);
extern WINDOW * dupwin (WINDOW *);
extern int echo (void);
extern int echochar (const chtype);
extern int erase (void);
extern int endwin (void);
extern char erasechar (void);
extern void filter (void);
extern int flash (void);
extern int flushinp (void);
extern chtype getbkgd (WINDOW *);
extern int getch (void);
extern int getnstr (char *, int);
extern int getstr (char *);
extern WINDOW * getwin (FILE *);
extern int halfdelay (int);
extern _Bool has_colors (void);
extern _Bool has_ic (void);
extern _Bool has_il (void);
extern int hline (chtype, int);
extern void idcok (WINDOW *, _Bool);
extern int idlok (WINDOW *, _Bool);
extern void immedok (WINDOW *, _Bool);
extern chtype inch (void);
extern int inchnstr (chtype *, int);
extern int inchstr (chtype *);
extern WINDOW * initscr (void);
extern int init_color (short,short,short,short);
extern int init_pair (short,short,short);
extern int innstr (char *, int);
extern int insch (chtype);
extern int insdelln (int);
extern int insertln (void);
extern int insnstr (const char *, int);
extern int insstr (const char *);
extern int instr (char *);
extern int intrflush (WINDOW *,_Bool);
extern _Bool isendwin (void);
extern _Bool is_linetouched (WINDOW *,int);
extern _Bool is_wintouched (WINDOW *);
extern char * keyname (int);
extern int keypad (WINDOW *,_Bool);
extern char killchar (void);
extern int leaveok (WINDOW *,_Bool);
extern char * longname (void);
extern int meta (WINDOW *,_Bool);
extern int move (int, int);
extern int mvaddch (int, int, const chtype);
extern int mvaddchnstr (int, int, const chtype *, int);
extern int mvaddchstr (int, int, const chtype *);
extern int mvaddnstr (int, int, const char *, int);
extern int mvaddstr (int, int, const char *);
extern int mvchgat (int, int, int, attr_t, short, const void *);
extern int mvcur (int,int,int,int);
extern int mvdelch (int, int);
extern int mvderwin (WINDOW *, int, int);
extern int mvgetch (int, int);
extern int mvgetnstr (int, int, char *, int);
extern int mvgetstr (int, int, char *);
extern int mvhline (int, int, chtype, int);
extern chtype mvinch (int, int);
extern int mvinchnstr (int, int, chtype *, int);
extern int mvinchstr (int, int, chtype *);
extern int mvinnstr (int, int, char *, int);
extern int mvinsch (int, int, chtype);
extern int mvinsnstr (int, int, const char *, int);
extern int mvinsstr (int, int, const char *);
extern int mvinstr (int, int, char *);
extern int mvprintw (int,int, const char *,...)
  ;
extern int mvscanw (int,int, char *,...)
  ;
extern int mvvline (int, int, chtype, int);
extern int mvwaddch (WINDOW *, int, int, const chtype);
extern int mvwaddchnstr (WINDOW *, int, int, const chtype *, int);
extern int mvwaddchstr (WINDOW *, int, int, const chtype *);
extern int mvwaddnstr (WINDOW *, int, int, const char *, int);
extern int mvwaddstr (WINDOW *, int, int, const char *);
extern int mvwchgat (WINDOW *, int, int, int, attr_t, short, const void *);
extern int mvwdelch (WINDOW *, int, int);
extern int mvwgetch (WINDOW *, int, int);
extern int mvwgetnstr (WINDOW *, int, int, char *, int);
extern int mvwgetstr (WINDOW *, int, int, char *);
extern int mvwhline (WINDOW *, int, int, chtype, int);
extern int mvwin (WINDOW *,int,int);
extern chtype mvwinch (WINDOW *, int, int);
extern int mvwinchnstr (WINDOW *, int, int, chtype *, int);
extern int mvwinchstr (WINDOW *, int, int, chtype *);
extern int mvwinnstr (WINDOW *, int, int, char *, int);
extern int mvwinsch (WINDOW *, int, int, chtype);
extern int mvwinsnstr (WINDOW *, int, int, const char *, int);
extern int mvwinsstr (WINDOW *, int, int, const char *);
extern int mvwinstr (WINDOW *, int, int, char *);
extern int mvwprintw (WINDOW*,int,int, const char *,...)
  ;
extern int mvwscanw (WINDOW *,int,int, char *,...)
  ;
extern int mvwvline (WINDOW *,int, int, chtype, int);
extern int napms (int);
extern WINDOW * newpad (int,int);
extern SCREEN * newterm ( char *,FILE *,FILE *);
extern WINDOW * newwin (int,int,int,int);
extern int nl (void);
extern int nocbreak (void);
extern int nodelay (WINDOW *,_Bool);
extern int noecho (void);
extern int nonl (void);
extern void noqiflush (void);
extern int noraw (void);
extern int notimeout (WINDOW *,_Bool);
extern int overlay (const WINDOW*,WINDOW *);
extern int overwrite (const WINDOW*,WINDOW *);
extern int pair_content (short,short*,short*);
extern int PAIR_NUMBER (int);
extern int pechochar (WINDOW *, const chtype);
extern int pnoutrefresh (WINDOW*,int,int,int,int,int,int);
extern int prefresh (WINDOW *,int,int,int,int,int,int);
extern int printw (const char *,...)
  ;
extern int putwin (WINDOW *, FILE *);
extern void qiflush (void);
extern int raw (void);
extern int redrawwin (WINDOW *);
extern int refresh (void);
extern int resetty (void);
extern int reset_prog_mode (void);
extern int reset_shell_mode (void);
extern int ripoffline (int, int (*)(WINDOW *, int));
extern int savetty (void);
extern int scanw ( char *,...)
  ;
extern int scr_dump (const char *);
extern int scr_init (const char *);
extern int scrl (int);
extern int scroll (WINDOW *);
extern int scrollok (WINDOW *,_Bool);
extern int scr_restore (const char *);
extern int scr_set (const char *);
extern int setscrreg (int,int);
extern SCREEN * set_term (SCREEN *);
extern int slk_attroff (const chtype);
extern int slk_attr_off (const attr_t, void *);
extern int slk_attron (const chtype);
extern int slk_attr_on (attr_t,void*);
extern int slk_attrset (const chtype);
extern attr_t slk_attr (void);
extern int slk_attr_set (const attr_t,short,void*);
extern int slk_clear (void);
extern int slk_color (short);
extern int slk_init (int);
extern char * slk_label (int);
extern int slk_noutrefresh (void);
extern int slk_refresh (void);
extern int slk_restore (void);
extern int slk_set (int,const char *,int);
extern int slk_touch (void);
extern int standout (void);
extern int standend (void);
extern int start_color (void);
extern WINDOW * subpad (WINDOW *, int, int, int, int);
extern WINDOW * subwin (WINDOW *, int, int, int, int);
extern int syncok (WINDOW *, _Bool);
extern chtype termattrs (void);
extern char * termname (void);
extern void timeout (int);
extern int touchline (WINDOW *, int, int);
extern int touchwin (WINDOW *);
extern int typeahead (int);
extern int ungetch (int);
extern int untouchwin (WINDOW *);
extern void use_env (_Bool);
extern int vidattr (chtype);
extern int vidputs (chtype, int (*)(int));
extern int vline (chtype, int);
extern int vwprintw (WINDOW *, const char *,va_list);
extern int vw_printw (WINDOW *, const char *,va_list);
extern int vwscanw (WINDOW *, char *,va_list);
extern int vw_scanw (WINDOW *, char *,va_list);
extern int waddch (WINDOW *, const chtype);
extern int waddchnstr (WINDOW *,const chtype *,int);
extern int waddchstr (WINDOW *,const chtype *);
extern int waddnstr (WINDOW *,const char *,int);
extern int waddstr (WINDOW *,const char *);
extern int wattron (WINDOW *, int);
extern int wattroff (WINDOW *, int);
extern int wattrset (WINDOW *, int);
extern int wattr_get (WINDOW *, attr_t *, short *, void *);
extern int wattr_on (WINDOW *, attr_t, void *);
extern int wattr_off (WINDOW *, attr_t, void *);
extern int wattr_set (WINDOW *, attr_t, short, void *);
extern int wbkgd (WINDOW *, chtype);
extern void wbkgdset (WINDOW *,chtype);
extern int wborder (WINDOW *,chtype,chtype,chtype,chtype,chtype,chtype,chtype,chtype);
extern int wchgat (WINDOW *, int, attr_t, short, const void *);
extern int wclear (WINDOW *);
extern int wclrtobot (WINDOW *);
extern int wclrtoeol (WINDOW *);
extern int wcolor_set (WINDOW*,short,void*);
extern void wcursyncup (WINDOW *);
extern int wdelch (WINDOW *);
extern int wdeleteln (WINDOW *);
extern int wechochar (WINDOW *, const chtype);
extern int werase (WINDOW *);
extern int wgetch (WINDOW *);
extern int wgetnstr (WINDOW *,char *,int);
extern int wgetstr (WINDOW *, char *);
extern int whline (WINDOW *, chtype, int);
extern chtype winch (WINDOW *);
extern int winchnstr (WINDOW *, chtype *, int);
extern int winchstr (WINDOW *, chtype *);
extern int winnstr (WINDOW *, char *, int);
extern int winsch (WINDOW *, chtype);
extern int winsdelln (WINDOW *,int);
extern int winsertln (WINDOW *);
extern int winsnstr (WINDOW *, const char *,int);
extern int winsstr (WINDOW *, const char *);
extern int winstr (WINDOW *, char *);
extern int wmove (WINDOW *,int,int);
extern int wnoutrefresh (WINDOW *);
extern int wprintw (WINDOW *, const char *,...)
  ;
extern int wredrawln (WINDOW *,int,int);
extern int wrefresh (WINDOW *);
extern int wscanw (WINDOW *, char *,...)
  ;
extern int wscrl (WINDOW *,int);
extern int wsetscrreg (WINDOW *,int,int);
extern int wstandout (WINDOW *);
extern int wstandend (WINDOW *);
extern void wsyncdown (WINDOW *);
extern void wsyncup (WINDOW *);
extern void wtimeout (WINDOW *,int);
extern int wtouchln (WINDOW *,int,int,int);
extern int wvline (WINDOW *,chtype,int);




extern int tigetflag ( char *);
extern int tigetnum ( char *);
extern char * tigetstr ( char *);
extern int putp (const char *);


extern char * tparm ( char *, ...);
# 811 "/usr/include/ncurses.h" 3 4
extern int getattrs (const WINDOW *);
extern int getcurx (const WINDOW *);
extern int getcury (const WINDOW *);
extern int getbegx (const WINDOW *);
extern int getbegy (const WINDOW *);
extern int getmaxx (const WINDOW *);
extern int getmaxy (const WINDOW *);
extern int getparx (const WINDOW *);
extern int getpary (const WINDOW *);
# 834 "/usr/include/ncurses.h" 3 4
typedef int (*NCURSES_WINDOW_CB)(WINDOW *, void *);
typedef int (*NCURSES_SCREEN_CB)(SCREEN *, void *);
extern _Bool is_term_resized (int, int);
extern char * keybound (int, int);
extern const char * curses_version (void);
extern int assume_default_colors (int, int);
extern int define_key (const char *, int);
extern int key_defined (const char *);
extern int keyok (int, _Bool);
extern int resize_term (int, int);
extern int resizeterm (int, int);
extern int set_escdelay (int);
extern int set_tabsize (int);
extern int use_default_colors (void);
extern int use_extended_names (_Bool);
extern int use_legacy_coding (int);
extern int use_screen (SCREEN *, NCURSES_SCREEN_CB, void *);
extern int use_window (WINDOW *, NCURSES_WINDOW_CB, void *);
extern int wresize (WINDOW *, int, int);
extern void nofilter(void);





extern WINDOW * wgetparent (const WINDOW *);
extern _Bool is_cleared (const WINDOW *);
extern _Bool is_idcok (const WINDOW *);
extern _Bool is_idlok (const WINDOW *);
extern _Bool is_immedok (const WINDOW *);
extern _Bool is_keypad (const WINDOW *);
extern _Bool is_leaveok (const WINDOW *);
extern _Bool is_nodelay (const WINDOW *);
extern _Bool is_notimeout (const WINDOW *);
extern _Bool is_scrollok (const WINDOW *);
extern _Bool is_syncok (const WINDOW *);
extern int wgetscrreg (const WINDOW *, int *, int *);
# 1202 "/usr/include/ncurses.h" 3 4
extern WINDOW * curscr;
extern WINDOW * newscr;
extern WINDOW * stdscr;
extern char ttytype[];
extern int COLORS;
extern int COLOR_PAIRS;
extern int COLS;
extern int ESCDELAY;
extern int LINES;
extern int TABSIZE;
# 1667 "/usr/include/ncurses.h" 3 4
typedef struct
{
    short id;
    int x, y, z;
    mmask_t bstate;
}
MEVENT;

extern int getmouse (MEVENT *);
extern int ungetmouse (MEVENT *);
extern mmask_t mousemask (mmask_t, mmask_t *);
extern _Bool wenclose (const WINDOW *, int, int);
extern int mouseinterval (int);
extern _Bool wmouse_trafo (const WINDOW*, int*, int*, _Bool);
extern _Bool mouse_trafo (int*, int*, _Bool);





extern int mcprint (char *, int);
extern int has_key (int);



extern void _tracef (const char *, ...) ;
extern void _tracedump (const char *, WINDOW *);
extern char * _traceattr (attr_t);
extern char * _traceattr2 (int, chtype);
extern char * _nc_tracebits (void);
extern char * _tracechar (int);
extern char * _tracechtype (chtype);
extern char * _tracechtype2 (int, chtype);
# 1709 "/usr/include/ncurses.h" 3 4
extern char * _tracemouse (const MEVENT *);
extern void trace (const unsigned int);
# 49 "/Users/parrt/tmp/Python-3.3.1/Include/py_curses.h" 2
# 76 "/Users/parrt/tmp/Python-3.3.1/Include/py_curses.h"
typedef struct {
 PyObject ob_base;
 WINDOW *win;
 char *encoding;
} PyCursesWindowObject;
# 106 "/Users/parrt/tmp/Python-3.3.1/Include/py_curses.h"
static char *catchall_ERR = "curses function returned ERR";
static char *catchall_NULL = "curses function returned NULL";
# 114 "_cursesmodule.c" 2





extern int setupterm(char *,int,int *);





# 1 "/usr/include/langinfo.h" 1 3 4
# 35 "/usr/include/langinfo.h" 3 4
typedef __darwin_nl_item nl_item;
# 116 "/usr/include/langinfo.h" 3 4

char *nl_langinfo(nl_item);

# 126 "_cursesmodule.c" 2
# 139 "_cursesmodule.c"
static PyObject *PyCursesError;


static int initialised_setupterm = 0;


static int initialised = 0;


static int initialisedcolors = 0;

static char *screen_encoding = ((void *)0);
# 183 "_cursesmodule.c"
static PyObject *
PyCursesCheckERR(int code, const char *fname)
{
    if (code != (-1)) {
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        return (&_Py_NoneStruct);
    } else {
        if (fname == ((void *)0)) {
            PyErr_SetString(PyCursesError, catchall_ERR);
        } else {
            PyErr_Format(PyCursesError, "%s() returned ERR", fname);
        }
        return ((void *)0);
    }
}
# 206 "_cursesmodule.c"
static int
PyCurses_ConvertToChtype(PyCursesWindowObject *win, PyObject *obj, chtype *ch)
{
    long value;
    if(((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<27))) != 0) && PyBytes_Size(obj) == 1) {
        value = (unsigned char)PyBytes_AsString(obj)[0];
    }
    else if (((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        if (PyUnicode_GetLength(obj) != 1) {
            PyErr_Format(PyExc_TypeError,
                         "expect bytes or str of length 1, or int, "
                         "got a str of length %zi",
                         ((__builtin_expect(!(((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 218, "PyUnicode_Check(obj)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)obj)->state.ready)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 218, "PyUnicode_IS_READY(obj)") : (void)0), ((PyASCIIObject *)(obj))->length));
            return 0;
        }
        value = ((__builtin_expect(!(((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 221, "PyUnicode_Check(obj)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)obj)->state.ready)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 221, "PyUnicode_IS_READY(obj)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((obj)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 221, "PyUnicode_Check((obj))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(obj))->state.ready)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 221, "PyUnicode_IS_READY((obj))") : (void)0), ((PyASCIIObject *)((obj)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((obj)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 221, "PyUnicode_Check((obj))") : (void)0), (((PyASCIIObject*)((obj)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((obj)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 221, "PyUnicode_Check((obj))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(obj))->state.ready)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 221, "PyUnicode_IS_READY((obj))") : (void)0), ((PyASCIIObject*)(obj))->state.ascii) ? ((void*)((PyASCIIObject*)((obj)) + 1)) : ((void*)((PyCompactUnicodeObject*)((obj)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((obj)))->data.any), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 221, "((PyUnicodeObject*)((obj)))->data.any") : (void)0), ((((PyUnicodeObject *)((obj)))->data.any))))))[(0)] : (((__builtin_expect(!(((((((PyObject*)((obj)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 221, "PyUnicode_Check((obj))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(obj))->state.ready)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 221, "PyUnicode_IS_READY((obj))") : (void)0), ((PyASCIIObject *)((obj)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((obj)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 221, "PyUnicode_Check((obj))") : (void)0), (((PyASCIIObject*)((obj)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((obj)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 221, "PyUnicode_Check((obj))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(obj))->state.ready)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 221, "PyUnicode_IS_READY((obj))") : (void)0), ((PyASCIIObject*)(obj))->state.ascii) ? ((void*)((PyASCIIObject*)((obj)) + 1)) : ((void*)((PyCompactUnicodeObject*)((obj)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((obj)))->data.any), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 221, "((PyUnicodeObject*)((obj)))->data.any") : (void)0), ((((PyUnicodeObject *)((obj)))->data.any))))))[(0)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((obj)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 221, "PyUnicode_Check((obj))") : (void)0), (((PyASCIIObject*)((obj)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((obj)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 221, "PyUnicode_Check((obj))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(obj))->state.ready)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 221, "PyUnicode_IS_READY((obj))") : (void)0), ((PyASCIIObject*)(obj))->state.ascii) ? ((void*)((PyASCIIObject*)((obj)) + 1)) : ((void*)((PyCompactUnicodeObject*)((obj)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((obj)))->data.any), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 221, "((PyUnicodeObject*)((obj)))->data.any") : (void)0), ((((PyUnicodeObject *)((obj)))->data.any))))))[(0)] ) ));
        if (128 < value) {
            PyObject *bytes;
            const char *encoding;
            if (win)
                encoding = win->encoding;
            else
                encoding = screen_encoding;
            bytes = PyUnicode_AsEncodedObject(obj, encoding, ((void *)0));
            if (bytes == ((void *)0))
                return 0;
            if (((__builtin_expect(!(((((((PyObject*)(bytes))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 232, "PyBytes_Check(bytes)") : (void)0),(((PyVarObject*)(bytes))->ob_size)) == 1)
                value = (unsigned char)((__builtin_expect(!(((((((PyObject*)(bytes))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 233, "PyBytes_Check(bytes)") : (void)0), (((PyBytesObject *)(bytes))->ob_sval))[0];
            else
                value = -1;
            do { if ( --((PyObject*)(bytes))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(bytes)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(bytes)))); } while (0);
            if (value < 0)
                goto overflow;
        }
    }
    else if (((((PyObject*)(obj))->ob_type) == &PyLong_Type)) {
        int long_overflow;
        value = PyLong_AsLongAndOverflow(obj, &long_overflow);
        if (long_overflow)
            goto overflow;
    }
    else {
        PyErr_Format(PyExc_TypeError,
                     "expect bytes or str of length 1, or int, got %s",
                     (((PyObject*)(obj))->ob_type)->tp_name);
        return 0;
    }
    *ch = (chtype)value;
    if ((long)*ch != value)
        goto overflow;
    return 1;

overflow:
    PyErr_SetString(PyExc_OverflowError,
                    "byte doesn't fit in chtype");
    return 0;
}
# 275 "_cursesmodule.c"
static int
PyCurses_ConvertToCchar_t(PyCursesWindowObject *win, PyObject *obj,
                          chtype *ch



                          )
{
    long value;




    if (((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
# 301 "_cursesmodule.c"
        return PyCurses_ConvertToChtype(win, obj, ch);

    }
    else if(((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<27))) != 0) && PyBytes_Size(obj) == 1) {
        value = (unsigned char)PyBytes_AsString(obj)[0];
    }
    else if (((((PyObject*)(obj))->ob_type) == &PyLong_Type)) {
        int overflow;
        value = PyLong_AsLongAndOverflow(obj, &overflow);
        if (overflow) {
            PyErr_SetString(PyExc_OverflowError,
                            "int doesn't fit in long");
            return 0;
        }
    }
    else {
        PyErr_Format(PyExc_TypeError,
                     "expect bytes or str of length 1, or int, got %s",
                     (((PyObject*)(obj))->ob_type)->tp_name);
        return 0;
    }

    *ch = (chtype)value;
    if ((long)*ch != value) {
        PyErr_Format(PyExc_OverflowError,
                     "byte doesn't fit in chtype");
        return 0;
    }
    return 1;
}







static int
PyCurses_ConvertToString(PyCursesWindowObject *win, PyObject *obj,
                         PyObject **bytes, wchar_t **wstr)
{
    if (((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<28))) != 0)) {







        (__builtin_expect(!(wstr == ((void *)0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 350, "wstr == NULL") : (void)0);
        *bytes = PyUnicode_AsEncodedObject(obj, win->encoding, ((void *)0));
        if (*bytes == ((void *)0))
            return 0;
        return 1;

    }
    else if (((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
        ( ((PyObject*)(obj))->ob_refcnt++);
        *bytes = obj;
        return 1;
    }

    PyErr_Format(PyExc_TypeError, "expect bytes or str, got %s",
                 (((PyObject*)(obj))->ob_type)->tp_name);
    return 0;
}




static int func_PyCursesSetupTermCalled(void)
{
    if (initialised_setupterm != 1) { PyErr_SetString(PyCursesError, "must call (at least) setupterm() first"); return 0; };
    return 1;
}

static int func_PyCursesInitialised(void)
{
    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };
    return 1;
}

static int func_PyCursesInitialisedColor(void)
{
    if (initialisedcolors != 1) { PyErr_SetString(PyCursesError, "must call start_color() first"); return 0; };
    return 1;
}







PyTypeObject PyCursesWindow_Type;
# 456 "_cursesmodule.c"
static PyObject *PyCursesWindow_untouchwin (PyCursesWindowObject *self, PyObject *args) { return PyCursesCheckERR(wtouchln((self->win), 0, ((self->win) ? ((self->win)->_maxy + 1) : (-1)), 0), "untouchwin"); }
static PyObject *PyCursesWindow_touchwin (PyCursesWindowObject *self, PyObject *args) { return PyCursesCheckERR(wtouchln((self->win), 0, ((self->win) ? ((self->win)->_maxy + 1) : (-1)), 1), "touchwin"); }
static PyObject *PyCursesWindow_redrawwin (PyCursesWindowObject *self, PyObject *args) { return PyCursesCheckERR(wredrawln(self->win, 0, (self->win)->_maxy+1), "redrawwin"); }
static PyObject *PyCursesWindow_winsertln (PyCursesWindowObject *self, PyObject *args) { return PyCursesCheckERR(winsdelln(self->win,1), "winsertln"); }
static PyObject *PyCursesWindow_werase (PyCursesWindowObject *self, PyObject *args) { return PyCursesCheckERR(werase(self->win), "werase"); }
static PyObject *PyCursesWindow_wdeleteln (PyCursesWindowObject *self, PyObject *args) { return PyCursesCheckERR(winsdelln(self->win,-1), "wdeleteln"); }

static PyObject * PyCursesWindow_is_wintouched (PyCursesWindowObject *self) { if (is_wintouched (self->win) == 0) { ( ((PyObject*)(((PyObject *) &_Py_FalseStruct)))->ob_refcnt++); return ((PyObject *) &_Py_FalseStruct); } else { ( ((PyObject*)(((PyObject *) &_Py_TrueStruct)))->ob_refcnt++); return ((PyObject *) &_Py_TrueStruct); } }

static PyObject * PyCursesWindow_wsyncup (PyCursesWindowObject *self) { wsyncup(self->win); ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++); return (&_Py_NoneStruct); }
static PyObject * PyCursesWindow_wsyncdown (PyCursesWindowObject *self) { wsyncdown(self->win); ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++); return (&_Py_NoneStruct); }
static PyObject * PyCursesWindow_wstandend (PyCursesWindowObject *self) { (((self->win)->_attrs = ((1U - 1U)))); ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++); return (&_Py_NoneStruct); }
static PyObject * PyCursesWindow_wstandout (PyCursesWindowObject *self) { (((self->win)->_attrs = (((1U) << ((8) + 8))))); ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++); return (&_Py_NoneStruct); }
static PyObject * PyCursesWindow_wcursyncup (PyCursesWindowObject *self) { wcursyncup(self->win); ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++); return (&_Py_NoneStruct); }
static PyObject * PyCursesWindow_wclrtoeol (PyCursesWindowObject *self) { wclrtoeol(self->win); ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++); return (&_Py_NoneStruct); }
static PyObject * PyCursesWindow_wclrtobot (PyCursesWindowObject *self) { wclrtobot(self->win); ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++); return (&_Py_NoneStruct); }
static PyObject * PyCursesWindow_wclear (PyCursesWindowObject *self) { wclear(self->win); ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++); return (&_Py_NoneStruct); }

static PyObject * PyCursesWindow_idcok (PyCursesWindowObject *self, PyObject *args) { int arg1; if (!_PyArg_ParseTuple_SizeT(args, "i;True(1) or False(0)", &arg1)) return ((void *)0); idcok(self->win,arg1); ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++); return (&_Py_NoneStruct); }
static PyObject * PyCursesWindow_immedok (PyCursesWindowObject *self, PyObject *args) { int arg1; if (!_PyArg_ParseTuple_SizeT(args, "i;True(1) or False(0)", &arg1)) return ((void *)0); immedok(self->win,arg1); ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++); return (&_Py_NoneStruct); }
static PyObject * PyCursesWindow_wtimeout (PyCursesWindowObject *self, PyObject *args) { int arg1; if (!_PyArg_ParseTuple_SizeT(args, "i;delay", &arg1)) return ((void *)0); wtimeout(self->win,arg1); ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++); return (&_Py_NoneStruct); }

static PyObject * PyCursesWindow_getyx (PyCursesWindowObject *self) { int arg1, arg2; (arg1 = ((self->win) ? (self->win)->_cury : (-1)), arg2 = ((self->win) ? (self->win)->_curx : (-1))); return _Py_BuildValue_SizeT("ii", arg1, arg2); }
static PyObject * PyCursesWindow_getbegyx (PyCursesWindowObject *self) { int arg1, arg2; (arg1 = ((self->win) ? (self->win)->_begy : (-1)), arg2 = ((self->win) ? (self->win)->_begx : (-1))); return _Py_BuildValue_SizeT("ii", arg1, arg2); }
static PyObject * PyCursesWindow_getmaxyx (PyCursesWindowObject *self) { int arg1, arg2; (arg1 = ((self->win) ? ((self->win)->_maxy + 1) : (-1)), arg2 = ((self->win) ? ((self->win)->_maxx + 1) : (-1))); return _Py_BuildValue_SizeT("ii", arg1, arg2); }
static PyObject * PyCursesWindow_getparyx (PyCursesWindowObject *self) { int arg1, arg2; (arg1 = ((self->win) ? (self->win)->_pary : (-1)), arg2 = ((self->win) ? (self->win)->_parx : (-1))); return _Py_BuildValue_SizeT("ii", arg1, arg2); }

static PyObject * PyCursesWindow_clearok (PyCursesWindowObject *self, PyObject *args) { int arg1; if (!_PyArg_ParseTuple_SizeT(args,"i;True(1) or False(0)", &arg1)) return ((void *)0); return PyCursesCheckERR(clearok(self->win, arg1), "clearok"); }
static PyObject * PyCursesWindow_idlok (PyCursesWindowObject *self, PyObject *args) { int arg1; if (!_PyArg_ParseTuple_SizeT(args,"i;True(1) or False(0)", &arg1)) return ((void *)0); return PyCursesCheckERR(idlok(self->win, arg1), "idlok"); }



static PyObject * PyCursesWindow_keypad (PyCursesWindowObject *self, PyObject *args) { int arg1; if (!_PyArg_ParseTuple_SizeT(args,"i;True(1) or False(0)", &arg1)) return ((void *)0); return PyCursesCheckERR(keypad(self->win, arg1), "keypad"); }

static PyObject * PyCursesWindow_leaveok (PyCursesWindowObject *self, PyObject *args) { int arg1; if (!_PyArg_ParseTuple_SizeT(args,"i;True(1) or False(0)", &arg1)) return ((void *)0); return PyCursesCheckERR(leaveok(self->win, arg1), "leaveok"); }



static PyObject * PyCursesWindow_nodelay (PyCursesWindowObject *self, PyObject *args) { int arg1; if (!_PyArg_ParseTuple_SizeT(args,"i;True(1) or False(0)", &arg1)) return ((void *)0); return PyCursesCheckERR(nodelay(self->win, arg1), "nodelay"); }

static PyObject * PyCursesWindow_notimeout (PyCursesWindowObject *self, PyObject *args) { int arg1; if (!_PyArg_ParseTuple_SizeT(args,"i;True(1) or False(0)", &arg1)) return ((void *)0); return PyCursesCheckERR(notimeout(self->win, arg1), "notimeout"); }
static PyObject * PyCursesWindow_scrollok (PyCursesWindowObject *self, PyObject *args) { int arg1; if (!_PyArg_ParseTuple_SizeT(args,"i;True(1) or False(0)", &arg1)) return ((void *)0); return PyCursesCheckERR(scrollok(self->win, arg1), "scrollok"); }
static PyObject * PyCursesWindow_winsdelln (PyCursesWindowObject *self, PyObject *args) { int arg1; if (!_PyArg_ParseTuple_SizeT(args,"i;nlines", &arg1)) return ((void *)0); return PyCursesCheckERR(winsdelln(self->win, arg1), "winsdelln"); }
static PyObject * PyCursesWindow_syncok (PyCursesWindowObject *self, PyObject *args) { int arg1; if (!_PyArg_ParseTuple_SizeT(args,"i;True(1) or False(0)", &arg1)) return ((void *)0); return PyCursesCheckERR(syncok(self->win, arg1), "syncok"); }

static PyObject * PyCursesWindow_mvwin (PyCursesWindowObject *self, PyObject *args) { int arg1, arg2; if (!_PyArg_ParseTuple_SizeT(args,"ii;y,x", &arg1, &arg2)) return ((void *)0); return PyCursesCheckERR(mvwin(self->win, arg1, arg2), "mvwin"); }
static PyObject * PyCursesWindow_mvderwin (PyCursesWindowObject *self, PyObject *args) { int arg1, arg2; if (!_PyArg_ParseTuple_SizeT(args,"ii;y,x", &arg1, &arg2)) return ((void *)0); return PyCursesCheckERR(mvderwin(self->win, arg1, arg2), "mvderwin"); }
static PyObject * PyCursesWindow_wmove (PyCursesWindowObject *self, PyObject *args) { int arg1, arg2; if (!_PyArg_ParseTuple_SizeT(args,"ii;y,x", &arg1, &arg2)) return ((void *)0); return PyCursesCheckERR(wmove(self->win, arg1, arg2), "wmove"); }

static PyObject * PyCursesWindow_wresize (PyCursesWindowObject *self, PyObject *args) { int arg1, arg2; if (!_PyArg_ParseTuple_SizeT(args,"ii;lines,columns", &arg1, &arg2)) return ((void *)0); return PyCursesCheckERR(wresize(self->win, arg1, arg2), "wresize"); }




static PyObject *
PyCursesWindow_New(WINDOW *win, const char *encoding)
{
    PyCursesWindowObject *wo;

    if (encoding == ((void *)0)) {
# 525 "_cursesmodule.c"
        const char *codeset = nl_langinfo(0);
        if (codeset != ((void *)0) && codeset[0] != 0)
            encoding = codeset;

        if (encoding == ((void *)0))
            encoding = "utf-8";
    }

    wo = ( (PyCursesWindowObject *) PyObject_Init( (PyObject *) PyObject_Malloc( ( (&PyCursesWindow_Type)->tp_basicsize ) ), (&PyCursesWindow_Type)) );
    if (wo == ((void *)0)) return ((void *)0);
    wo->win = win;
    wo->encoding = strdup(encoding);
    if (wo->encoding == ((void *)0)) {
        do { if ( --((PyObject*)(wo))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(wo)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(wo)))); } while (0);
        PyErr_NoMemory();
        return ((void *)0);
    }
    return (PyObject *)wo;
}

static void
PyCursesWindow_Dealloc(PyCursesWindowObject *wo)
{
    if (wo->win != stdscr) delwin(wo->win);
    if (wo->encoding != ((void *)0))
        free(wo->encoding);
    PyObject_Free(wo);
}



static PyObject *
PyCursesWindow_AddCh(PyCursesWindowObject *self, PyObject *args)
{
    int rtn, x, y, use_xy = 0;
    PyObject *chobj;
    int type;
    chtype ch;



    attr_t attr = (1U - 1U);
    long lattr;
    const char *funcname;

    switch (PyTuple_Size(args)) {
    case 1:
        if (!_PyArg_ParseTuple_SizeT(args, "O;ch or int", &chobj))
            return ((void *)0);
        break;
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args, "Ol;ch or int,attr", &chobj, &lattr))
            return ((void *)0);
        attr = lattr;
        break;
    case 3:
        if (!_PyArg_ParseTuple_SizeT(args,"iiO;y,x,ch or int", &y, &x, &chobj))
            return ((void *)0);
        use_xy = 1;
        break;
    case 4:
        if (!_PyArg_ParseTuple_SizeT(args,"iiOl;y,x,ch or int, attr",
                              &y, &x, &chobj, &lattr))
            return ((void *)0);
        attr = lattr;
        use_xy = 1;
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "addch requires 1 to 4 arguments");
        return ((void *)0);
    }
# 610 "_cursesmodule.c"
    type = PyCurses_ConvertToCchar_t(self, chobj, &ch);

    if (type == 1) {
        funcname = "addch";
        if (use_xy == 1)
            rtn = (wmove(self->win,y,x) == (-1) ? (-1) : waddch(self->win,ch | attr));
        else {
            rtn = waddch(self->win, ch | attr);
        }
    }
    else {
        return ((void *)0);
    }
    return PyCursesCheckERR(rtn, funcname);
}

static PyObject *
PyCursesWindow_AddStr(PyCursesWindowObject *self, PyObject *args)
{
    int rtn;
    int x, y;
    int strtype;
    PyObject *strobj, *bytesobj = ((void *)0);



    attr_t attr = (1U - 1U) , attr_old = (1U - 1U);
    long lattr;
    int use_xy = 0, use_attr = 0;
    const char *funcname;

    switch (PyTuple_Size(args)) {
    case 1:
        if (!_PyArg_ParseTuple_SizeT(args,"O;str", &strobj))
            return ((void *)0);
        break;
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args,"Ol;str,attr", &strobj, &lattr))
            return ((void *)0);
        attr = lattr;
        use_attr = 1;
        break;
    case 3:
        if (!_PyArg_ParseTuple_SizeT(args,"iiO;int,int,str", &y, &x, &strobj))
            return ((void *)0);
        use_xy = 1;
        break;
    case 4:
        if (!_PyArg_ParseTuple_SizeT(args,"iiOl;int,int,str,attr", &y, &x, &strobj, &lattr))
            return ((void *)0);
        attr = lattr;
        use_xy = use_attr = 1;
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "addstr requires 1 to 4 arguments");
        return ((void *)0);
    }



    strtype = PyCurses_ConvertToString(self, strobj, &bytesobj, ((void *)0));

    if (strtype == 0)
        return ((void *)0);
    if (use_attr == 1) {
        attr_old = ((self->win) ? (self->win)->_attrs : (1U - 1U));
        (void)((self->win)->_attrs = (attr));
    }
# 689 "_cursesmodule.c"
    {
        char *str = ((__builtin_expect(!(((((((PyObject*)(bytesobj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 690, "PyBytes_Check(bytesobj)") : (void)0), (((PyBytesObject *)(bytesobj))->ob_sval));
        funcname = "addstr";
        if (use_xy == 1)
            rtn = (wmove(self->win,y,x) == (-1) ? (-1) : waddnstr(self->win,str,-1));
        else
            rtn = waddnstr(self->win,str,-1);
        do { if ( --((PyObject*)(bytesobj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(bytesobj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(bytesobj)))); } while (0);
    }
    if (use_attr == 1)
        (void)((self->win)->_attrs = (attr_old));
    return PyCursesCheckERR(rtn, funcname);
}

static PyObject *
PyCursesWindow_AddNStr(PyCursesWindowObject *self, PyObject *args)
{
    int rtn, x, y, n;
    int strtype;
    PyObject *strobj, *bytesobj = ((void *)0);



    attr_t attr = (1U - 1U) , attr_old = (1U - 1U);
    long lattr;
    int use_xy = 0, use_attr = 0;
    const char *funcname;

    switch (PyTuple_Size(args)) {
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args,"Oi;str,n", &strobj, &n))
            return ((void *)0);
        break;
    case 3:
        if (!_PyArg_ParseTuple_SizeT(args,"Oil;str,n,attr", &strobj, &n, &lattr))
            return ((void *)0);
        attr = lattr;
        use_attr = 1;
        break;
    case 4:
        if (!_PyArg_ParseTuple_SizeT(args,"iiOi;y,x,str,n", &y, &x, &strobj, &n))
            return ((void *)0);
        use_xy = 1;
        break;
    case 5:
        if (!_PyArg_ParseTuple_SizeT(args,"iiOil;y,x,str,n,attr", &y, &x, &strobj, &n, &lattr))
            return ((void *)0);
        attr = lattr;
        use_xy = use_attr = 1;
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "addnstr requires 2 to 5 arguments");
        return ((void *)0);
    }



    strtype = PyCurses_ConvertToString(self, strobj, &bytesobj, ((void *)0));

    if (strtype == 0)
        return ((void *)0);

    if (use_attr == 1) {
        attr_old = ((self->win) ? (self->win)->_attrs : (1U - 1U));
        (void)((self->win)->_attrs = (attr));
    }
# 766 "_cursesmodule.c"
    {
        char *str = ((__builtin_expect(!(((((((PyObject*)(bytesobj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 767, "PyBytes_Check(bytesobj)") : (void)0), (((PyBytesObject *)(bytesobj))->ob_sval));
        funcname = "addnstr";
        if (use_xy == 1)
            rtn = (wmove(self->win,y,x) == (-1) ? (-1) : waddnstr(self->win,str,n));
        else
            rtn = waddnstr(self->win,str,n);
        do { if ( --((PyObject*)(bytesobj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(bytesobj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(bytesobj)))); } while (0);
    }
    if (use_attr == 1)
        (void)((self->win)->_attrs = (attr_old));
    return PyCursesCheckERR(rtn, funcname);
}

static PyObject *
PyCursesWindow_Bkgd(PyCursesWindowObject *self, PyObject *args)
{
    PyObject *temp;
    chtype bkgd;
    attr_t attr = (1U - 1U);
    long lattr;

    switch (PyTuple_Size(args)) {
    case 1:
        if (!_PyArg_ParseTuple_SizeT(args, "O;ch or int", &temp))
            return ((void *)0);
        break;
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args,"Ol;ch or int,attr", &temp, &lattr))
            return ((void *)0);
        attr = lattr;
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "bkgd requires 1 or 2 arguments");
        return ((void *)0);
    }

    if (!PyCurses_ConvertToChtype(self, temp, &bkgd))
        return ((void *)0);

    return PyCursesCheckERR(wbkgd(self->win, bkgd | attr), "bkgd");
}

static PyObject *
PyCursesWindow_AttrOff(PyCursesWindowObject *self, PyObject *args)
{
    long lattr;
    if (!_PyArg_ParseTuple_SizeT(args,"l;attr", &lattr))
        return ((void *)0);
    return PyCursesCheckERR(wattr_off(self->win, (attr_t)((attr_t)lattr), ((void *)0)), "attroff");
}

static PyObject *
PyCursesWindow_AttrOn(PyCursesWindowObject *self, PyObject *args)
{
    long lattr;
    if (!_PyArg_ParseTuple_SizeT(args,"l;attr", &lattr))
        return ((void *)0);
    return PyCursesCheckERR(wattr_on(self->win, (attr_t)((attr_t)lattr), ((void *)0)), "attron");
}

static PyObject *
PyCursesWindow_AttrSet(PyCursesWindowObject *self, PyObject *args)
{
    long lattr;
    if (!_PyArg_ParseTuple_SizeT(args,"l;attr", &lattr))
        return ((void *)0);
    return PyCursesCheckERR(((self->win)->_attrs = ((attr_t)lattr)), "attrset");
}

static PyObject *
PyCursesWindow_BkgdSet(PyCursesWindowObject *self, PyObject *args)
{
    PyObject *temp;
    chtype bkgd;
    attr_t attr = (1U - 1U);
    long lattr;

    switch (PyTuple_Size(args)) {
    case 1:
        if (!_PyArg_ParseTuple_SizeT(args, "O;ch or int", &temp))
            return ((void *)0);
        break;
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args,"Ol;ch or int,attr", &temp, &lattr))
            return ((void *)0);
        attr = lattr;
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "bkgdset requires 1 or 2 arguments");
        return ((void *)0);
    }

    if (!PyCurses_ConvertToChtype(self, temp, &bkgd))
        return ((void *)0);

    wbkgdset(self->win, bkgd | attr);
    return PyCursesCheckERR(0, "bkgdset");
}

static PyObject *
PyCursesWindow_Border(PyCursesWindowObject *self, PyObject *args)
{
    PyObject *temp[8];
    chtype ch[8];
    int i;


    for(i=0; i<8; i++) {
        temp[i] = ((void *)0);
        ch[i] = 0;
    }

    if (!_PyArg_ParseTuple_SizeT(args,"|OOOOOOOO;ls,rs,ts,bs,tl,tr,bl,br",
                          &temp[0], &temp[1], &temp[2], &temp[3],
                          &temp[4], &temp[5], &temp[6], &temp[7]))
        return ((void *)0);

    for(i=0; i<8; i++) {
        if (temp[i] != ((void *)0) && !PyCurses_ConvertToChtype(self, temp[i], &ch[i]))
            return ((void *)0);
    }

    wborder(self->win,
            ch[0], ch[1], ch[2], ch[3],
            ch[4], ch[5], ch[6], ch[7]);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static PyObject *
PyCursesWindow_Box(PyCursesWindowObject *self, PyObject *args)
{
    chtype ch1=0,ch2=0;
    switch(PyTuple_Size(args)){
    case 0: break;
    default:
        if (!_PyArg_ParseTuple_SizeT(args,"ll;vertint,horint", &ch1, &ch2))
            return ((void *)0);
    }
    wborder(self->win, ch1, ch1, ch2, ch2, 0, 0, 0, 0);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}
# 925 "_cursesmodule.c"
static PyObject *
PyCursesWindow_ChgAt(PyCursesWindowObject *self, PyObject *args)
{
    int rtn;
    int x, y;
    int num = -1;
    short color;
    attr_t attr = (1U - 1U);
    long lattr;
    int use_xy = 0;

    switch (PyTuple_Size(args)) {
    case 1:
        if (!_PyArg_ParseTuple_SizeT(args,"l;attr", &lattr))
            return ((void *)0);
        attr = lattr;
        break;
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args,"il;n,attr", &num, &lattr))
            return ((void *)0);
        attr = lattr;
        break;
    case 3:
        if (!_PyArg_ParseTuple_SizeT(args,"iil;int,int,attr", &y, &x, &lattr))
            return ((void *)0);
        attr = lattr;
        use_xy = 1;
        break;
    case 4:
        if (!_PyArg_ParseTuple_SizeT(args,"iiil;int,int,n,attr", &y, &x, &num, &lattr))
            return ((void *)0);
        attr = lattr;
        use_xy = 1;
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "chgat requires 1 to 4 arguments");
        return ((void *)0);
    }

    color = (short)((attr >> 8) & 0xff);
    attr = attr - (color << 8);

    if (use_xy == 1) {
        rtn = (wmove(self->win,y,x) == (-1) ? (-1) : wchgat(self->win,num,attr,color,((void *)0)));
        wtouchln((self->win), y, 1, 1);
    } else {
        (y = ((self->win) ? (self->win)->_cury : (-1)), x = ((self->win) ? (self->win)->_curx : (-1)));
        rtn = wchgat(self->win,num,attr,color,((void *)0));
        wtouchln((self->win), y, 1, 1);
    }
    return PyCursesCheckERR(rtn, "chgat");
}


static PyObject *
PyCursesWindow_DelCh(PyCursesWindowObject *self, PyObject *args)
{
    int rtn;
    int x, y;

    switch (PyTuple_Size(args)) {
    case 0:
        rtn = wdelch(self->win);
        break;
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args,"ii;y,x", &y, &x))
            return ((void *)0);
        rtn = (wmove(self->win,y,x) == (-1) ? (-1) : wdelch(self->win));
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "delch requires 0 or 2 arguments");
        return ((void *)0);
    }
    return PyCursesCheckERR(rtn, "[mv]wdelch");
}

static PyObject *
PyCursesWindow_DerWin(PyCursesWindowObject *self, PyObject *args)
{
    WINDOW *win;
    int nlines, ncols, begin_y, begin_x;

    nlines = 0;
    ncols = 0;
    switch (PyTuple_Size(args)) {
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args,"ii;begin_y,begin_x",&begin_y,&begin_x))
            return ((void *)0);
        break;
    case 4:
        if (!_PyArg_ParseTuple_SizeT(args, "iiii;nlines,ncols,begin_y,begin_x",
                              &nlines,&ncols,&begin_y,&begin_x))
            return ((void *)0);
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "derwin requires 2 or 4 arguments");
        return ((void *)0);
    }

    win = derwin(self->win,nlines,ncols,begin_y,begin_x);

    if (win == ((void *)0)) {
        PyErr_SetString(PyCursesError, catchall_NULL);
        return ((void *)0);
    }

    return (PyObject *)PyCursesWindow_New(win, ((void *)0));
}

static PyObject *
PyCursesWindow_EchoChar(PyCursesWindowObject *self, PyObject *args)
{
    PyObject *temp;
    chtype ch;
    attr_t attr = (1U - 1U);
    long lattr;

    switch (PyTuple_Size(args)) {
    case 1:
        if (!_PyArg_ParseTuple_SizeT(args,"O;ch or int", &temp))
            return ((void *)0);
        break;
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args,"Ol;ch or int,attr", &temp, &lattr))
            return ((void *)0);
        attr = lattr;
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "echochar requires 1 or 2 arguments");


        return ((void *)0);
    }

    if (!PyCurses_ConvertToChtype(self, temp, &ch))
        return ((void *)0);


    if (self->win->_flags & 0x10)
        return PyCursesCheckERR(pechochar(self->win, ch | attr),
                                "echochar");
    else

        return PyCursesCheckERR(wechochar(self->win, ch | attr),
                                "echochar");
}


static PyObject *
PyCursesWindow_Enclose(PyCursesWindowObject *self, PyObject *args)
{
    int x, y;
    if (!_PyArg_ParseTuple_SizeT(args,"ii;y,x", &y, &x))
        return ((void *)0);

    return PyLong_FromLong( wenclose(self->win,y,x) );
}


static PyObject *
PyCursesWindow_GetBkgd(PyCursesWindowObject *self)
{
    return PyLong_FromLong((long) ((self->win)->_bkgd));
}

static PyObject *
PyCursesWindow_GetCh(PyCursesWindowObject *self, PyObject *args)
{
    int x, y;
    int rtn;

    switch (PyTuple_Size(args)) {
    case 0:
        { PyThreadState *_save; _save = PyEval_SaveThread();
        rtn = wgetch(self->win);
        PyEval_RestoreThread(_save); }
        break;
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args,"ii;y,x",&y,&x))
            return ((void *)0);
        { PyThreadState *_save; _save = PyEval_SaveThread();
        rtn = (wmove(self->win,y,x) == (-1) ? (-1) : wgetch(self->win));
        PyEval_RestoreThread(_save); }
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "getch requires 0 or 2 arguments");
        return ((void *)0);
    }
    return PyLong_FromLong((long)rtn);
}

static PyObject *
PyCursesWindow_GetKey(PyCursesWindowObject *self, PyObject *args)
{
    int x, y;
    int rtn;

    switch (PyTuple_Size(args)) {
    case 0:
        { PyThreadState *_save; _save = PyEval_SaveThread();
        rtn = wgetch(self->win);
        PyEval_RestoreThread(_save); }
        break;
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args,"ii;y,x",&y,&x))
            return ((void *)0);
        { PyThreadState *_save; _save = PyEval_SaveThread();
        rtn = (wmove(self->win,y,x) == (-1) ? (-1) : wgetch(self->win));
        PyEval_RestoreThread(_save); }
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "getkey requires 0 or 2 arguments");
        return ((void *)0);
    }
    if (rtn == (-1)) {

        PyErr_CheckSignals();
        if (!PyErr_Occurred())
            PyErr_SetString(PyCursesError, "no input");
        return ((void *)0);
    } else if (rtn<=255) {
        return _Py_BuildValue_SizeT("C", rtn);
    } else {
        const char *knp;



        knp = keyname(rtn);

        return PyUnicode_FromString((knp == ((void *)0)) ? "" : knp);
    }
}
# 1198 "_cursesmodule.c"
static PyObject *
PyCursesWindow_GetStr(PyCursesWindowObject *self, PyObject *args)
{
    int x, y, n;
    char rtn[1024];
    int rtn2;

    switch (PyTuple_Size(args)) {
    case 0:
        { PyThreadState *_save; _save = PyEval_SaveThread();
        rtn2 = wgetnstr(self->win,rtn, 1023);
        PyEval_RestoreThread(_save); }
        break;
    case 1:
        if (!_PyArg_ParseTuple_SizeT(args,"i;n", &n))
            return ((void *)0);
        { PyThreadState *_save; _save = PyEval_SaveThread();
        rtn2 = wgetnstr(self->win,rtn,((n) < (1023) ? (n) : (1023)));
        PyEval_RestoreThread(_save); }
        break;
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args,"ii;y,x",&y,&x))
            return ((void *)0);
        { PyThreadState *_save; _save = PyEval_SaveThread();



        rtn2 = (wmove(self->win,y,x) == (-1) ? (-1) : wgetnstr(self->win,rtn,1023));

        PyEval_RestoreThread(_save); }
        break;
    case 3:
        if (!_PyArg_ParseTuple_SizeT(args,"iii;y,x,n", &y, &x, &n))
            return ((void *)0);






        { PyThreadState *_save; _save = PyEval_SaveThread();
        rtn2 = (wmove(self->win,y,x) == (-1) ? (-1) : wgetnstr(self->win,rtn,((n) < (1023) ? (n) : (1023))));
        PyEval_RestoreThread(_save); }

        break;
    default:
        PyErr_SetString(PyExc_TypeError, "getstr requires 0 to 3 arguments");
        return ((void *)0);
    }
    if (rtn2 == (-1))
        rtn[0] = 0;
    return PyBytes_FromString(rtn);
}

static PyObject *
PyCursesWindow_Hline(PyCursesWindowObject *self, PyObject *args)
{
    PyObject *temp;
    chtype ch;
    int n, x, y, code = (0);
    attr_t attr = (1U - 1U);
    long lattr;

    switch (PyTuple_Size(args)) {
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args, "Oi;ch or int,n", &temp, &n))
            return ((void *)0);
        break;
    case 3:
        if (!_PyArg_ParseTuple_SizeT(args, "Oil;ch or int,n,attr", &temp, &n, &lattr))
            return ((void *)0);
        attr = lattr;
        break;
    case 4:
        if (!_PyArg_ParseTuple_SizeT(args, "iiOi;y,x,ch or int,n", &y, &x, &temp, &n))
            return ((void *)0);
        code = wmove(self->win, y, x);
        break;
    case 5:
        if (!_PyArg_ParseTuple_SizeT(args, "iiOil; y,x,ch or int,n,attr",
                              &y, &x, &temp, &n, &lattr))
            return ((void *)0);
        attr = lattr;
        code = wmove(self->win, y, x);
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "hline requires 2 to 5 arguments");
        return ((void *)0);
    }

    if (code != (-1)) {
        if (!PyCurses_ConvertToChtype(self, temp, &ch))
            return ((void *)0);
        return PyCursesCheckERR(whline(self->win, ch | attr, n), "hline");
    } else
        return PyCursesCheckERR(code, "wmove");
}

static PyObject *
PyCursesWindow_InsCh(PyCursesWindowObject *self, PyObject *args)
{
    int rtn, x, y, use_xy = 0;
    PyObject *temp;
    chtype ch = 0;
    attr_t attr = (1U - 1U);
    long lattr;

    switch (PyTuple_Size(args)) {
    case 1:
        if (!_PyArg_ParseTuple_SizeT(args, "O;ch or int", &temp))
            return ((void *)0);
        break;
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args, "Ol;ch or int,attr", &temp, &lattr))
            return ((void *)0);
        attr = lattr;
        break;
    case 3:
        if (!_PyArg_ParseTuple_SizeT(args,"iiO;y,x,ch or int", &y, &x, &temp))
            return ((void *)0);
        use_xy = 1;
        break;
    case 4:
        if (!_PyArg_ParseTuple_SizeT(args,"iiOl;y,x,ch or int, attr", &y, &x, &temp, &lattr))
            return ((void *)0);
        attr = lattr;
        use_xy = 1;
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "insch requires 1 or 4 arguments");
        return ((void *)0);
    }

    if (!PyCurses_ConvertToChtype(self, temp, &ch))
        return ((void *)0);

    if (use_xy == 1)
        rtn = (wmove(self->win,y,x) == (-1) ? (-1) : winsch(self->win,ch | attr));
    else {
        rtn = winsch(self->win, ch | attr);
    }
    return PyCursesCheckERR(rtn, "insch");
}

static PyObject *
PyCursesWindow_InCh(PyCursesWindowObject *self, PyObject *args)
{
    int x, y, rtn;

    switch (PyTuple_Size(args)) {
    case 0:
        rtn = winch(self->win);
        break;
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args,"ii;y,x",&y,&x))
            return ((void *)0);
        rtn = (wmove(self->win,y,x) == (-1) ? (chtype)((-1)) : winch(self->win));
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "inch requires 0 or 2 arguments");
        return ((void *)0);
    }
    return PyLong_FromLong((long) rtn);
}

static PyObject *
PyCursesWindow_InStr(PyCursesWindowObject *self, PyObject *args)
{
    int x, y, n;
    char rtn[1024];
    int rtn2;

    switch (PyTuple_Size(args)) {
    case 0:
        rtn2 = winnstr(self->win,rtn, 1023);
        break;
    case 1:
        if (!_PyArg_ParseTuple_SizeT(args,"i;n", &n))
            return ((void *)0);
        rtn2 = winnstr(self->win,rtn,((n) < (1023) ? (n) : (1023)));
        break;
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args,"ii;y,x",&y,&x))
            return ((void *)0);
        rtn2 = (wmove(self->win,y,x) == (-1) ? (-1) : winnstr(self->win,rtn,1023));
        break;
    case 3:
        if (!_PyArg_ParseTuple_SizeT(args, "iii;y,x,n", &y, &x, &n))
            return ((void *)0);
        rtn2 = (wmove(self->win,y,x) == (-1) ? (-1) : winnstr(self->win,rtn,((n) < (1023) ? (n) : (1023))));
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "instr requires 0 or 3 arguments");
        return ((void *)0);
    }
    if (rtn2 == (-1))
        rtn[0] = 0;
    return PyBytes_FromString(rtn);
}

static PyObject *
PyCursesWindow_InsStr(PyCursesWindowObject *self, PyObject *args)
{
    int rtn;
    int x, y;
    int strtype;
    PyObject *strobj, *bytesobj = ((void *)0);



    attr_t attr = (1U - 1U) , attr_old = (1U - 1U);
    long lattr;
    int use_xy = 0, use_attr = 0;
    const char *funcname;

    switch (PyTuple_Size(args)) {
    case 1:
        if (!_PyArg_ParseTuple_SizeT(args,"O;str", &strobj))
            return ((void *)0);
        break;
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args,"Ol;str,attr", &strobj, &lattr))
            return ((void *)0);
        attr = lattr;
        use_attr = 1;
        break;
    case 3:
        if (!_PyArg_ParseTuple_SizeT(args,"iiO;y,x,str", &y, &x, &strobj))
            return ((void *)0);
        use_xy = 1;
        break;
    case 4:
        if (!_PyArg_ParseTuple_SizeT(args,"iiOl;y,x,str,attr", &y, &x, &strobj, &lattr))
            return ((void *)0);
        attr = lattr;
        use_xy = use_attr = 1;
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "insstr requires 1 to 4 arguments");
        return ((void *)0);
    }




    strtype = PyCurses_ConvertToString(self, strobj, &bytesobj, ((void *)0));

    if (strtype == 0)
        return ((void *)0);

    if (use_attr == 1) {
        attr_old = ((self->win) ? (self->win)->_attrs : (1U - 1U));
        (void)((self->win)->_attrs = (attr));
    }
# 1463 "_cursesmodule.c"
    {
        char *str = ((__builtin_expect(!(((((((PyObject*)(bytesobj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 1464, "PyBytes_Check(bytesobj)") : (void)0), (((PyBytesObject *)(bytesobj))->ob_sval));
        funcname = "insstr";
        if (use_xy == 1)
            rtn = (wmove(self->win,y,x) == (-1) ? (-1) : winsnstr(self->win, str, -1));
        else
            rtn = winsnstr(self->win, str, -1);
        do { if ( --((PyObject*)(bytesobj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(bytesobj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(bytesobj)))); } while (0);
    }
    if (use_attr == 1)
        (void)((self->win)->_attrs = (attr_old));
    return PyCursesCheckERR(rtn, funcname);
}

static PyObject *
PyCursesWindow_InsNStr(PyCursesWindowObject *self, PyObject *args)
{
    int rtn, x, y, n;
    int strtype;
    PyObject *strobj, *bytesobj = ((void *)0);



    attr_t attr = (1U - 1U) , attr_old = (1U - 1U);
    long lattr;
    int use_xy = 0, use_attr = 0;
    const char *funcname;

    switch (PyTuple_Size(args)) {
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args,"Oi;str,n", &strobj, &n))
            return ((void *)0);
        break;
    case 3:
        if (!_PyArg_ParseTuple_SizeT(args,"Oil;str,n,attr", &strobj, &n, &lattr))
            return ((void *)0);
        attr = lattr;
        use_attr = 1;
        break;
    case 4:
        if (!_PyArg_ParseTuple_SizeT(args,"iiOi;y,x,str,n", &y, &x, &strobj, &n))
            return ((void *)0);
        use_xy = 1;
        break;
    case 5:
        if (!_PyArg_ParseTuple_SizeT(args,"iiOil;y,x,str,n,attr", &y, &x, &strobj, &n, &lattr))
            return ((void *)0);
        attr = lattr;
        use_xy = use_attr = 1;
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "insnstr requires 2 to 5 arguments");
        return ((void *)0);
    }




    strtype = PyCurses_ConvertToString(self, strobj, &bytesobj, ((void *)0));

    if (strtype == 0)
        return ((void *)0);

    if (use_attr == 1) {
        attr_old = ((self->win) ? (self->win)->_attrs : (1U - 1U));
        (void)((self->win)->_attrs = (attr));
    }
# 1541 "_cursesmodule.c"
    {
        char *str = ((__builtin_expect(!(((((((PyObject*)(bytesobj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 1542, "PyBytes_Check(bytesobj)") : (void)0), (((PyBytesObject *)(bytesobj))->ob_sval));
        funcname = "insnstr";
        if (use_xy == 1)
            rtn = (wmove(self->win,y,x) == (-1) ? (-1) : winsnstr(self->win,str,n));
        else
            rtn = winsnstr(self->win,str,n);
        do { if ( --((PyObject*)(bytesobj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(bytesobj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(bytesobj)))); } while (0);
    }
    if (use_attr == 1)
        (void)((self->win)->_attrs = (attr_old));
    return PyCursesCheckERR(rtn, funcname);
}

static PyObject *
PyCursesWindow_Is_LineTouched(PyCursesWindowObject *self, PyObject *args)
{
    int line, erg;
    if (!_PyArg_ParseTuple_SizeT(args,"i;line", &line))
        return ((void *)0);
    erg = is_linetouched(self->win, line);
    if (erg == (-1)) {
        PyErr_SetString(PyExc_TypeError,
                        "is_linetouched: line number outside of boundaries");
        return ((void *)0);
    } else
        if (erg == 0) {
            ( ((PyObject*)(((PyObject *) &_Py_FalseStruct)))->ob_refcnt++);
            return ((PyObject *) &_Py_FalseStruct);
        } else {
            ( ((PyObject*)(((PyObject *) &_Py_TrueStruct)))->ob_refcnt++);
            return ((PyObject *) &_Py_TrueStruct);
        }
}

static PyObject *
PyCursesWindow_NoOutRefresh(PyCursesWindowObject *self, PyObject *args)
{
    int pminrow,pmincol,sminrow,smincol,smaxrow,smaxcol;
    int rtn;




        if (self->win->_flags & 0x10)

        {
            switch(PyTuple_Size(args)) {
            case 6:
                if (!_PyArg_ParseTuple_SizeT(args,
                                      "iiiiii;" "pminrow,pmincol,sminrow,smincol,smaxrow,smaxcol",

                                      &pminrow, &pmincol, &sminrow,
                                      &smincol, &smaxrow, &smaxcol))
                    return ((void *)0);
                { PyThreadState *_save; _save = PyEval_SaveThread();
                rtn = pnoutrefresh(self->win,
                                   pminrow, pmincol, sminrow,
                                   smincol, smaxrow, smaxcol);
                PyEval_RestoreThread(_save); }
                return PyCursesCheckERR(rtn, "pnoutrefresh");
            default:
                PyErr_SetString(PyCursesError,
                                "noutrefresh() called for a pad "
                                "requires 6 arguments");
                return ((void *)0);
            }
        } else {
            if (!_PyArg_ParseTuple_SizeT(args, ":noutrefresh"))
                return ((void *)0);

            { PyThreadState *_save; _save = PyEval_SaveThread();
            rtn = wnoutrefresh(self->win);
            PyEval_RestoreThread(_save); }
            return PyCursesCheckERR(rtn, "wnoutrefresh");
        }
}

static PyObject *
PyCursesWindow_Overlay(PyCursesWindowObject *self, PyObject *args)
{
    PyCursesWindowObject *temp;
    int use_copywin = 0;
    int sminrow, smincol, dminrow, dmincol, dmaxrow, dmaxcol;
    int rtn;

    switch (PyTuple_Size(args)) {
    case 1:
        if (!_PyArg_ParseTuple_SizeT(args, "O!;window object",
                              &PyCursesWindow_Type, &temp))
            return ((void *)0);
        break;
    case 7:
        if (!_PyArg_ParseTuple_SizeT(args, "O!iiiiii;window object, int, int, int, int, int, int",
                              &PyCursesWindow_Type, &temp, &sminrow, &smincol,
                              &dminrow, &dmincol, &dmaxrow, &dmaxcol))
            return ((void *)0);
        use_copywin = 1;
        break;
    default:
        PyErr_SetString(PyExc_TypeError,
                        "overlay requires one or seven arguments");
        return ((void *)0);
    }

    if (use_copywin == 1) {
        rtn = copywin(self->win, temp->win, sminrow, smincol,
                      dminrow, dmincol, dmaxrow, dmaxcol, 1);
        return PyCursesCheckERR(rtn, "copywin");
    }
    else {
        rtn = overlay(self->win, temp->win);
        return PyCursesCheckERR(rtn, "overlay");
    }
}

static PyObject *
PyCursesWindow_Overwrite(PyCursesWindowObject *self, PyObject *args)
{
    PyCursesWindowObject *temp;
    int use_copywin = 0;
    int sminrow, smincol, dminrow, dmincol, dmaxrow, dmaxcol;
    int rtn;

    switch (PyTuple_Size(args)) {
    case 1:
        if (!_PyArg_ParseTuple_SizeT(args, "O!;window object",
                              &PyCursesWindow_Type, &temp))
            return ((void *)0);
        break;
    case 7:
        if (!_PyArg_ParseTuple_SizeT(args, "O!iiiiii;window object, int, int, int, int, int, int",
                              &PyCursesWindow_Type, &temp, &sminrow, &smincol,
                              &dminrow, &dmincol, &dmaxrow, &dmaxcol))
            return ((void *)0);
        use_copywin = 1;
        break;
    default:
        PyErr_SetString(PyExc_TypeError,
                        "overwrite requires one or seven arguments");
        return ((void *)0);
    }

    if (use_copywin == 1) {
        rtn = copywin(self->win, temp->win, sminrow, smincol,
                      dminrow, dmincol, dmaxrow, dmaxcol, 0);
        return PyCursesCheckERR(rtn, "copywin");
    }
    else {
        rtn = overwrite(self->win, temp->win);
        return PyCursesCheckERR(rtn, "overwrite");
    }
}

static PyObject *
PyCursesWindow_PutWin(PyCursesWindowObject *self, PyObject *stream)
{


    char fn[100];
    int fd;
    FILE *fp;
    PyObject *res;

    ((__builtin_object_size (fn, 0) != (size_t) -1) ? __builtin___strcpy_chk (fn, "/tmp/py.curses.putwin.XXXXXX", __builtin_object_size (fn, 2 > 1)) : __inline_strcpy_chk (fn, "/tmp/py.curses.putwin.XXXXXX"));
    fd = mkstemp(fn);
    if (fd < 0)
        return PyErr_SetFromErrnoWithFilename(PyExc_IOError, fn);
    fp = fdopen(fd, "wb+");
    if (fp == ((void *)0)) {
        close(fd);
        remove(fn);
        return PyErr_SetFromErrnoWithFilename(PyExc_IOError, fn);
    }
    res = PyCursesCheckERR(putwin(self->win, fp), "putwin");
    if (res == ((void *)0)) {
        fclose(fp);
        remove(fn);
        return res;
    }
    fseek(fp, 0, 0);
    while (1) {
        char buf[1024];
        Py_ssize_t n = fread(buf, 1, 1024, fp);
        static _Py_Identifier PyId_write = { 0, "write", 0 };

        if (n <= 0)
            break;
        do { if ( --((PyObject*)(res))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(res)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(res)))); } while (0);
        res = _PyObject_CallMethodId_SizeT(stream, &PyId_write, "y#", buf, n);
        if (res == ((void *)0))
            break;
    }
    fclose(fp);
    remove(fn);
    return res;
}

static PyObject *
PyCursesWindow_RedrawLine(PyCursesWindowObject *self, PyObject *args)
{
    int beg, num;
    if (!_PyArg_ParseTuple_SizeT(args, "ii;beg,num", &beg, &num))
        return ((void *)0);
    return PyCursesCheckERR(wredrawln(self->win,beg,num), "redrawln");
}

static PyObject *
PyCursesWindow_Refresh(PyCursesWindowObject *self, PyObject *args)
{
    int pminrow,pmincol,sminrow,smincol,smaxrow,smaxcol;
    int rtn;




        if (self->win->_flags & 0x10)

        {
            switch(PyTuple_Size(args)) {
            case 6:
                if (!_PyArg_ParseTuple_SizeT(args,
                                      "iiiiii;" "pminrow,pmincol,sminrow,smincol,smaxrow,smaxcol",

                                      &pminrow, &pmincol, &sminrow,
                                      &smincol, &smaxrow, &smaxcol))
                    return ((void *)0);

                { PyThreadState *_save; _save = PyEval_SaveThread();
                rtn = prefresh(self->win,
                               pminrow, pmincol, sminrow,
                               smincol, smaxrow, smaxcol);
                PyEval_RestoreThread(_save); }
                return PyCursesCheckERR(rtn, "prefresh");
            default:
                PyErr_SetString(PyCursesError,
                                "refresh() for a pad requires 6 arguments");
                return ((void *)0);
            }
        } else {
            if (!_PyArg_ParseTuple_SizeT(args, ":refresh"))
                return ((void *)0);
            { PyThreadState *_save; _save = PyEval_SaveThread();
            rtn = wrefresh(self->win);
            PyEval_RestoreThread(_save); }
            return PyCursesCheckERR(rtn, "prefresh");
        }
}

static PyObject *
PyCursesWindow_SetScrollRegion(PyCursesWindowObject *self, PyObject *args)
{
    int x, y;
    if (!_PyArg_ParseTuple_SizeT(args,"ii;top, bottom",&y,&x))
        return ((void *)0);
    return PyCursesCheckERR(wsetscrreg(self->win,y,x), "wsetscrreg");
}

static PyObject *
PyCursesWindow_SubWin(PyCursesWindowObject *self, PyObject *args)
{
    WINDOW *win;
    int nlines, ncols, begin_y, begin_x;

    nlines = 0;
    ncols = 0;
    switch (PyTuple_Size(args)) {
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args,"ii;begin_y,begin_x",&begin_y,&begin_x))
            return ((void *)0);
        break;
    case 4:
        if (!_PyArg_ParseTuple_SizeT(args, "iiii;nlines,ncols,begin_y,begin_x",
                              &nlines,&ncols,&begin_y,&begin_x))
            return ((void *)0);
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "subwin requires 2 or 4 arguments");
        return ((void *)0);
    }



    if (self->win->_flags & 0x10)
        win = subpad(self->win, nlines, ncols, begin_y, begin_x);
    else

        win = subwin(self->win, nlines, ncols, begin_y, begin_x);

    if (win == ((void *)0)) {
        PyErr_SetString(PyCursesError, catchall_NULL);
        return ((void *)0);
    }

    return (PyObject *)PyCursesWindow_New(win, self->encoding);
}

static PyObject *
PyCursesWindow_Scroll(PyCursesWindowObject *self, PyObject *args)
{
    int nlines;
    switch(PyTuple_Size(args)) {
    case 0:
        return PyCursesCheckERR(wscrl(self->win,1), "scroll");
    case 1:
        if (!_PyArg_ParseTuple_SizeT(args, "i;nlines", &nlines))
            return ((void *)0);
        return PyCursesCheckERR(wscrl(self->win, nlines), "scroll");
    default:
        PyErr_SetString(PyExc_TypeError, "scroll requires 0 or 1 arguments");
        return ((void *)0);
    }
}

static PyObject *
PyCursesWindow_TouchLine(PyCursesWindowObject *self, PyObject *args)
{
    int st, cnt, val;
    switch (PyTuple_Size(args)) {
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args,"ii;start,count",&st,&cnt))
            return ((void *)0);
        return PyCursesCheckERR(wtouchln((self->win), st, cnt, 1), "touchline");
    case 3:
        if (!_PyArg_ParseTuple_SizeT(args, "iii;start,count,val", &st, &cnt, &val))
            return ((void *)0);
        return PyCursesCheckERR(wtouchln(self->win, st, cnt, val), "touchline");
    default:
        PyErr_SetString(PyExc_TypeError, "touchline requires 2 or 3 arguments");
        return ((void *)0);
    }
}

static PyObject *
PyCursesWindow_Vline(PyCursesWindowObject *self, PyObject *args)
{
    PyObject *temp;
    chtype ch;
    int n, x, y, code = (0);
    attr_t attr = (1U - 1U);
    long lattr;

    switch (PyTuple_Size(args)) {
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args, "Oi;ch or int,n", &temp, &n))
            return ((void *)0);
        break;
    case 3:
        if (!_PyArg_ParseTuple_SizeT(args, "Oil;ch or int,n,attr", &temp, &n, &lattr))
            return ((void *)0);
        attr = lattr;
        break;
    case 4:
        if (!_PyArg_ParseTuple_SizeT(args, "iiOi;y,x,ch or int,n", &y, &x, &temp, &n))
            return ((void *)0);
        code = wmove(self->win, y, x);
        break;
    case 5:
        if (!_PyArg_ParseTuple_SizeT(args, "iiOil; y,x,ch or int,n,attr",
                              &y, &x, &temp, &n, &lattr))
            return ((void *)0);
        attr = lattr;
        code = wmove(self->win, y, x);
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "vline requires 2 to 5 arguments");
        return ((void *)0);
    }

    if (code != (-1)) {
        if (!PyCurses_ConvertToChtype(self, temp, &ch))
            return ((void *)0);
        return PyCursesCheckERR(wvline(self->win, ch | attr, n), "vline");
    } else
        return PyCursesCheckERR(code, "wmove");
}

static PyObject *
PyCursesWindow_get_encoding(PyCursesWindowObject *self, void *closure)
{
    return PyUnicode_FromString(self->encoding);
}

static int
PyCursesWindow_set_encoding(PyCursesWindowObject *self, PyObject *value)
{
    PyObject *ascii;
    char *encoding;


    if (value == ((void *)0)) {
        PyErr_SetString(PyExc_TypeError,
                        "encoding may not be deleted");
        return -1;
    }

    if (!((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        PyErr_SetString(PyExc_TypeError,
                        "setting encoding to a non-string");
        return -1;
    }
    ascii = PyUnicode_AsASCIIString(value);
    if (ascii == ((void *)0))
        return -1;
    encoding = strdup(((__builtin_expect(!(((((((PyObject*)(ascii))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 1945, "PyBytes_Check(ascii)") : (void)0), (((PyBytesObject *)(ascii))->ob_sval)));
    do { if ( --((PyObject*)(ascii))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(ascii)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(ascii)))); } while (0);
    if (encoding == ((void *)0)) {
        PyErr_NoMemory();
        return -1;
    }
    free(self->encoding);
    self->encoding = encoding;
    return 0;
}


static PyMethodDef PyCursesWindow_Methods[] = {
    {"addch", (PyCFunction)PyCursesWindow_AddCh, 0x0001},
    {"addnstr", (PyCFunction)PyCursesWindow_AddNStr, 0x0001},
    {"addstr", (PyCFunction)PyCursesWindow_AddStr, 0x0001},
    {"attroff", (PyCFunction)PyCursesWindow_AttrOff, 0x0001},
    {"attron", (PyCFunction)PyCursesWindow_AttrOn, 0x0001},
    {"attrset", (PyCFunction)PyCursesWindow_AttrSet, 0x0001},
    {"bkgd", (PyCFunction)PyCursesWindow_Bkgd, 0x0001},
    {"chgat", (PyCFunction)PyCursesWindow_ChgAt, 0x0001},
    {"bkgdset", (PyCFunction)PyCursesWindow_BkgdSet, 0x0001},
    {"border", (PyCFunction)PyCursesWindow_Border, 0x0001},
    {"box", (PyCFunction)PyCursesWindow_Box, 0x0001},
    {"clear", (PyCFunction)PyCursesWindow_wclear, 0x0004},
    {"clearok", (PyCFunction)PyCursesWindow_clearok, 0x0001},
    {"clrtobot", (PyCFunction)PyCursesWindow_wclrtobot, 0x0004},
    {"clrtoeol", (PyCFunction)PyCursesWindow_wclrtoeol, 0x0004},
    {"cursyncup", (PyCFunction)PyCursesWindow_wcursyncup, 0x0004},
    {"delch", (PyCFunction)PyCursesWindow_DelCh, 0x0001},
    {"deleteln", (PyCFunction)PyCursesWindow_wdeleteln, 0x0004},
    {"derwin", (PyCFunction)PyCursesWindow_DerWin, 0x0001},
    {"echochar", (PyCFunction)PyCursesWindow_EchoChar, 0x0001},

    {"enclose", (PyCFunction)PyCursesWindow_Enclose, 0x0001},

    {"erase", (PyCFunction)PyCursesWindow_werase, 0x0004},
    {"getbegyx", (PyCFunction)PyCursesWindow_getbegyx, 0x0004},
    {"getbkgd", (PyCFunction)PyCursesWindow_GetBkgd, 0x0004},
    {"getch", (PyCFunction)PyCursesWindow_GetCh, 0x0001},
    {"getkey", (PyCFunction)PyCursesWindow_GetKey, 0x0001},



    {"getmaxyx", (PyCFunction)PyCursesWindow_getmaxyx, 0x0004},
    {"getparyx", (PyCFunction)PyCursesWindow_getparyx, 0x0004},
    {"getstr", (PyCFunction)PyCursesWindow_GetStr, 0x0001},
    {"getyx", (PyCFunction)PyCursesWindow_getyx, 0x0004},
    {"hline", (PyCFunction)PyCursesWindow_Hline, 0x0001},
    {"idcok", (PyCFunction)PyCursesWindow_idcok, 0x0001},
    {"idlok", (PyCFunction)PyCursesWindow_idlok, 0x0001},
    {"immedok", (PyCFunction)PyCursesWindow_immedok, 0x0001},
    {"inch", (PyCFunction)PyCursesWindow_InCh, 0x0001},
    {"insch", (PyCFunction)PyCursesWindow_InsCh, 0x0001},
    {"insdelln", (PyCFunction)PyCursesWindow_winsdelln, 0x0001},
    {"insertln", (PyCFunction)PyCursesWindow_winsertln, 0x0004},
    {"insnstr", (PyCFunction)PyCursesWindow_InsNStr, 0x0001},
    {"insstr", (PyCFunction)PyCursesWindow_InsStr, 0x0001},
    {"instr", (PyCFunction)PyCursesWindow_InStr, 0x0001},
    {"is_linetouched", (PyCFunction)PyCursesWindow_Is_LineTouched, 0x0001},
    {"is_wintouched", (PyCFunction)PyCursesWindow_is_wintouched, 0x0004},
    {"keypad", (PyCFunction)PyCursesWindow_keypad, 0x0001},
    {"leaveok", (PyCFunction)PyCursesWindow_leaveok, 0x0001},
    {"move", (PyCFunction)PyCursesWindow_wmove, 0x0001},
    {"mvderwin", (PyCFunction)PyCursesWindow_mvderwin, 0x0001},
    {"mvwin", (PyCFunction)PyCursesWindow_mvwin, 0x0001},
    {"nodelay", (PyCFunction)PyCursesWindow_nodelay, 0x0001},
    {"notimeout", (PyCFunction)PyCursesWindow_notimeout, 0x0001},
    {"noutrefresh", (PyCFunction)PyCursesWindow_NoOutRefresh, 0x0001},

    {"nooutrefresh", (PyCFunction)PyCursesWindow_NoOutRefresh, 0x0001},
    {"overlay", (PyCFunction)PyCursesWindow_Overlay, 0x0001},
    {"overwrite", (PyCFunction)PyCursesWindow_Overwrite,
     0x0001},
    {"putwin", (PyCFunction)PyCursesWindow_PutWin, 0x0008},
    {"redrawln", (PyCFunction)PyCursesWindow_RedrawLine, 0x0001},
    {"redrawwin", (PyCFunction)PyCursesWindow_redrawwin, 0x0004},
    {"refresh", (PyCFunction)PyCursesWindow_Refresh, 0x0001},

    {"resize", (PyCFunction)PyCursesWindow_wresize, 0x0001},

    {"scroll", (PyCFunction)PyCursesWindow_Scroll, 0x0001},
    {"scrollok", (PyCFunction)PyCursesWindow_scrollok, 0x0001},
    {"setscrreg", (PyCFunction)PyCursesWindow_SetScrollRegion, 0x0001},
    {"standend", (PyCFunction)PyCursesWindow_wstandend, 0x0004},
    {"standout", (PyCFunction)PyCursesWindow_wstandout, 0x0004},
    {"subpad", (PyCFunction)PyCursesWindow_SubWin, 0x0001},
    {"subwin", (PyCFunction)PyCursesWindow_SubWin, 0x0001},
    {"syncdown", (PyCFunction)PyCursesWindow_wsyncdown, 0x0004},
    {"syncok", (PyCFunction)PyCursesWindow_syncok, 0x0001},
    {"syncup", (PyCFunction)PyCursesWindow_wsyncup, 0x0004},
    {"timeout", (PyCFunction)PyCursesWindow_wtimeout, 0x0001},
    {"touchline", (PyCFunction)PyCursesWindow_TouchLine, 0x0001},
    {"touchwin", (PyCFunction)PyCursesWindow_touchwin, 0x0004},
    {"untouchwin", (PyCFunction)PyCursesWindow_untouchwin, 0x0004},
    {"vline", (PyCFunction)PyCursesWindow_Vline, 0x0001},
    {((void *)0), ((void *)0)}
};

static PyGetSetDef PyCursesWindow_getsets[] = {
    {"encoding",
     (getter)PyCursesWindow_get_encoding,
     (setter)PyCursesWindow_set_encoding,
     "the typecode character used to create the array"},
    {((void *)0), ((void *)0), ((void *)0), ((void *)0) }
};



PyTypeObject PyCursesWindow_Type = {
    { { 1, ((void *)0) }, 0 },
    "_curses.curses window",
    sizeof(PyCursesWindowObject),
    0,

    (destructor)PyCursesWindow_Dealloc,
    0,
    (getattrfunc)0,
    (setattrfunc)0,
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
    ( 0 | (1L<<18) | 0),
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    PyCursesWindow_Methods,
    0,
    PyCursesWindow_getsets,
};





static PyObject *PyCurses_beep (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } return PyCursesCheckERR(beep(), "beep"); }
static PyObject *PyCurses_def_prog_mode (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } return PyCursesCheckERR(def_prog_mode(), "def_prog_mode"); }
static PyObject *PyCurses_def_shell_mode (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } return PyCursesCheckERR(def_shell_mode(), "def_shell_mode"); }
static PyObject *PyCurses_doupdate (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } return PyCursesCheckERR(doupdate(), "doupdate"); }
static PyObject *PyCurses_endwin (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } return PyCursesCheckERR(endwin(), "endwin"); }
static PyObject *PyCurses_flash (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } return PyCursesCheckERR(flash(), "flash"); }
static PyObject *PyCurses_nocbreak (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } return PyCursesCheckERR(nocbreak(), "nocbreak"); }
static PyObject *PyCurses_noecho (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } return PyCursesCheckERR(noecho(), "noecho"); }
static PyObject *PyCurses_nonl (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } return PyCursesCheckERR(nonl(), "nonl"); }
static PyObject *PyCurses_noraw (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } return PyCursesCheckERR(noraw(), "noraw"); }
static PyObject *PyCurses_reset_prog_mode (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } return PyCursesCheckERR(reset_prog_mode(), "reset_prog_mode"); }
static PyObject *PyCurses_reset_shell_mode (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } return PyCursesCheckERR(reset_shell_mode(), "reset_shell_mode"); }
static PyObject *PyCurses_resetty (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } return PyCursesCheckERR(resetty(), "resetty"); }
static PyObject *PyCurses_savetty (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } return PyCursesCheckERR(savetty(), "savetty"); }

static PyObject *PyCurses_cbreak (PyObject *self, PyObject *args) { int flag = 0; if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } switch(PyTuple_Size(args)) { case 0: return PyCursesCheckERR(cbreak(), "cbreak"); case 1: if (!_PyArg_ParseTuple_SizeT(args, "i;True(1) or False(0)", &flag)) return ((void *)0); if (flag) return PyCursesCheckERR(cbreak(), "cbreak"); else return PyCursesCheckERR(nocbreak (), "cbreak"); default: PyErr_SetString(PyExc_TypeError, "cbreak" " requires 0 or 1 arguments"); return ((void *)0); } }
static PyObject *PyCurses_echo (PyObject *self, PyObject *args) { int flag = 0; if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } switch(PyTuple_Size(args)) { case 0: return PyCursesCheckERR(echo(), "echo"); case 1: if (!_PyArg_ParseTuple_SizeT(args, "i;True(1) or False(0)", &flag)) return ((void *)0); if (flag) return PyCursesCheckERR(echo(), "echo"); else return PyCursesCheckERR(noecho (), "echo"); default: PyErr_SetString(PyExc_TypeError, "echo" " requires 0 or 1 arguments"); return ((void *)0); } }
static PyObject *PyCurses_nl (PyObject *self, PyObject *args) { int flag = 0; if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } switch(PyTuple_Size(args)) { case 0: return PyCursesCheckERR(nl(), "nl"); case 1: if (!_PyArg_ParseTuple_SizeT(args, "i;True(1) or False(0)", &flag)) return ((void *)0); if (flag) return PyCursesCheckERR(nl(), "nl"); else return PyCursesCheckERR(nonl (), "nl"); default: PyErr_SetString(PyExc_TypeError, "nl" " requires 0 or 1 arguments"); return ((void *)0); } }
static PyObject *PyCurses_raw (PyObject *self, PyObject *args) { int flag = 0; if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } switch(PyTuple_Size(args)) { case 0: return PyCursesCheckERR(raw(), "raw"); case 1: if (!_PyArg_ParseTuple_SizeT(args, "i;True(1) or False(0)", &flag)) return ((void *)0); if (flag) return PyCursesCheckERR(raw(), "raw"); else return PyCursesCheckERR(noraw (), "raw"); default: PyErr_SetString(PyExc_TypeError, "raw" " requires 0 or 1 arguments"); return ((void *)0); } }

static PyObject *PyCurses_baudrate (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } return PyLong_FromLong((long) baudrate()); }
static PyObject *PyCurses_termattrs (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } return PyLong_FromLong((long) termattrs()); }

static PyObject *PyCurses_termname (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } return PyBytes_FromString(termname()); }
static PyObject *PyCurses_longname (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } return PyBytes_FromString(longname()); }

static PyObject *PyCurses_can_change_color (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } if (can_change_color () == 0) { ( ((PyObject*)(((PyObject *) &_Py_FalseStruct)))->ob_refcnt++); return ((PyObject *) &_Py_FalseStruct); } ( ((PyObject*)(((PyObject *) &_Py_TrueStruct)))->ob_refcnt++); return ((PyObject *) &_Py_TrueStruct); }
static PyObject *PyCurses_has_colors (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } if (has_colors () == 0) { ( ((PyObject*)(((PyObject *) &_Py_FalseStruct)))->ob_refcnt++); return ((PyObject *) &_Py_FalseStruct); } ( ((PyObject*)(((PyObject *) &_Py_TrueStruct)))->ob_refcnt++); return ((PyObject *) &_Py_TrueStruct); }
static PyObject *PyCurses_has_ic (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } if (has_ic () == 0) { ( ((PyObject*)(((PyObject *) &_Py_FalseStruct)))->ob_refcnt++); return ((PyObject *) &_Py_FalseStruct); } ( ((PyObject*)(((PyObject *) &_Py_TrueStruct)))->ob_refcnt++); return ((PyObject *) &_Py_TrueStruct); }
static PyObject *PyCurses_has_il (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } if (has_il () == 0) { ( ((PyObject*)(((PyObject *) &_Py_FalseStruct)))->ob_refcnt++); return ((PyObject *) &_Py_FalseStruct); } ( ((PyObject*)(((PyObject *) &_Py_TrueStruct)))->ob_refcnt++); return ((PyObject *) &_Py_TrueStruct); }
static PyObject *PyCurses_isendwin (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } if (isendwin () == 0) { ( ((PyObject*)(((PyObject *) &_Py_FalseStruct)))->ob_refcnt++); return ((PyObject *) &_Py_FalseStruct); } ( ((PyObject*)(((PyObject *) &_Py_TrueStruct)))->ob_refcnt++); return ((PyObject *) &_Py_TrueStruct); }
static PyObject *PyCurses_flushinp (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } flushinp(); ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++); return (&_Py_NoneStruct); }
static PyObject *PyCurses_noqiflush (PyObject *self) { if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; } noqiflush(); ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++); return (&_Py_NoneStruct); }

static PyObject *
PyCurses_filter(PyObject *self)
{


    filter();
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static PyObject *
PyCurses_Color_Content(PyObject *self, PyObject *args)
{
    short color,r,g,b;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };
    if (initialisedcolors != 1) { PyErr_SetString(PyCursesError, "must call start_color() first"); return 0; };

    if (!_PyArg_ParseTuple_SizeT(args, "h:color_content", &color)) return ((void *)0);

    if (color_content(color, &r, &g, &b) != (-1))
        return _Py_BuildValue_SizeT("(iii)", r, g, b);
    else {
        PyErr_SetString(PyCursesError,
                        "Argument 1 was out of range. Check value of COLORS.");
        return ((void *)0);
    }
}

static PyObject *
PyCurses_color_pair(PyObject *self, PyObject *args)
{
    int n;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };
    if (initialisedcolors != 1) { PyErr_SetString(PyCursesError, "must call start_color() first"); return 0; };

    if (!_PyArg_ParseTuple_SizeT(args, "i:color_pair", &n)) return ((void *)0);
    return PyLong_FromLong((long) (n << 8));
}

static PyObject *
PyCurses_Curs_Set(PyObject *self, PyObject *args)
{
    int vis,erg;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    if (!_PyArg_ParseTuple_SizeT(args, "i:curs_set", &vis)) return ((void *)0);

    erg = curs_set(vis);
    if (erg == (-1)) return PyCursesCheckERR(erg, "curs_set");

    return PyLong_FromLong((long) erg);
}

static PyObject *
PyCurses_Delay_Output(PyObject *self, PyObject *args)
{
    int ms;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    if (!_PyArg_ParseTuple_SizeT(args, "i:delay_output", &ms)) return ((void *)0);

    return PyCursesCheckERR(delay_output(ms), "delay_output");
}

static PyObject *
PyCurses_EraseChar(PyObject *self)
{
    char ch;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    ch = erasechar();

    return PyBytes_FromStringAndSize(&ch, 1);
}

static PyObject *
PyCurses_getsyx(PyObject *self)
{
    int x = 0;
    int y = 0;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    do { if (newscr) { if (((newscr)->_leaveok)) (y) = (x) = -1; else ((y) = ((newscr) ? (newscr)->_cury : (-1)), (x) = ((newscr) ? (newscr)->_curx : (-1))); } } while(0);

    return _Py_BuildValue_SizeT("(ii)", y, x);
}


static PyObject *
PyCurses_GetMouse(PyObject *self)
{
    int rtn;
    MEVENT event;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    rtn = getmouse( &event );
    if (rtn == (-1)) {
        PyErr_SetString(PyCursesError, "getmouse() returned ERR");
        return ((void *)0);
    }
    return _Py_BuildValue_SizeT("(hiiil)",
                         (short)event.id,
                         event.x, event.y, event.z,
                         (long) event.bstate);
}

static PyObject *
PyCurses_UngetMouse(PyObject *self, PyObject *args)
{
    MEVENT event;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };
    if (!_PyArg_ParseTuple_SizeT(args, "hiiil",
                          &event.id,
                          &event.x, &event.y, &event.z,
                          (int *) &event.bstate))
        return ((void *)0);

    return PyCursesCheckERR(ungetmouse(&event), "ungetmouse");
}


static PyObject *
PyCurses_GetWin(PyCursesWindowObject *self, PyObject *stream)
{
    char fn[100];
    int fd;
    FILE *fp;
    PyObject *data;
    size_t datalen;
    WINDOW *win;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };
    static _Py_Identifier PyId_read = { 0, "read", 0 };

    ((__builtin_object_size (fn, 0) != (size_t) -1) ? __builtin___strcpy_chk (fn, "/tmp/py.curses.getwin.XXXXXX", __builtin_object_size (fn, 2 > 1)) : __inline_strcpy_chk (fn, "/tmp/py.curses.getwin.XXXXXX"));
    fd = mkstemp(fn);
    if (fd < 0)
        return PyErr_SetFromErrnoWithFilename(PyExc_IOError, fn);
    fp = fdopen(fd, "wb+");
    if (fp == ((void *)0)) {
        close(fd);
        remove(fn);
        return PyErr_SetFromErrnoWithFilename(PyExc_IOError, fn);
    }
    data = _PyObject_CallMethodId_SizeT(stream, &PyId_read, "");
    if (data == ((void *)0)) {
        fclose(fp);
        remove(fn);
        return ((void *)0);
    }
    if (!((((((PyObject*)(data))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
        PyErr_Format(PyExc_TypeError,
                     "f.read() returned %.100s instead of bytes",
                     data->ob_type->tp_name);
        do { if ( --((PyObject*)(data))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(data)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(data)))); } while (0);
        fclose(fp);
        remove(fn);
        return ((void *)0);
    }
    datalen = ((__builtin_expect(!(((((((PyObject*)(data))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 2293, "PyBytes_Check(data)") : (void)0),(((PyVarObject*)(data))->ob_size));
    if (fwrite(((__builtin_expect(!(((((((PyObject*)(data))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_cursesmodule.c", 2294, "PyBytes_Check(data)") : (void)0), (((PyBytesObject *)(data))->ob_sval)), 1, datalen, fp) != datalen) {
        do { if ( --((PyObject*)(data))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(data)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(data)))); } while (0);
        fclose(fp);
        remove(fn);
        return PyErr_SetFromErrnoWithFilename(PyExc_IOError, fn);
    }
    do { if ( --((PyObject*)(data))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(data)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(data)))); } while (0);
    fseek(fp, 0, 0);
    win = getwin(fp);
    fclose(fp);
    remove(fn);
    if (win == ((void *)0)) {
        PyErr_SetString(PyCursesError, catchall_NULL);
        return ((void *)0);
    }
    return PyCursesWindow_New(win, ((void *)0));
}

static PyObject *
PyCurses_HalfDelay(PyObject *self, PyObject *args)
{
    unsigned char tenths;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    if (!_PyArg_ParseTuple_SizeT(args, "b:halfdelay", &tenths)) return ((void *)0);

    return PyCursesCheckERR(halfdelay(tenths), "halfdelay");
}



static PyObject * PyCurses_has_key(PyObject *self, PyObject *args)
{
    int ch;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    if (!_PyArg_ParseTuple_SizeT(args,"i",&ch)) return ((void *)0);

    if (has_key(ch) == 0) {
        ( ((PyObject*)(((PyObject *) &_Py_FalseStruct)))->ob_refcnt++);
        return ((PyObject *) &_Py_FalseStruct);
    }
    ( ((PyObject*)(((PyObject *) &_Py_TrueStruct)))->ob_refcnt++);
    return ((PyObject *) &_Py_TrueStruct);
}


static PyObject *
PyCurses_Init_Color(PyObject *self, PyObject *args)
{
    short color, r, g, b;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };
    if (initialisedcolors != 1) { PyErr_SetString(PyCursesError, "must call start_color() first"); return 0; };

    switch(PyTuple_Size(args)) {
    case 4:
        if (!_PyArg_ParseTuple_SizeT(args, "hhhh;color,r,g,b", &color, &r, &g, &b)) return ((void *)0);
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "init_color requires 4 arguments");
        return ((void *)0);
    }

    return PyCursesCheckERR(init_color(color, r, g, b), "init_color");
}

static PyObject *
PyCurses_Init_Pair(PyObject *self, PyObject *args)
{
    short pair, f, b;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };
    if (initialisedcolors != 1) { PyErr_SetString(PyCursesError, "must call start_color() first"); return 0; };

    if (PyTuple_Size(args) != 3) {
        PyErr_SetString(PyExc_TypeError, "init_pair requires 3 arguments");
        return ((void *)0);
    }

    if (!_PyArg_ParseTuple_SizeT(args, "hhh;pair, f, b", &pair, &f, &b)) return ((void *)0);

    return PyCursesCheckERR(init_pair(pair, f, b), "init_pair");
}

static PyObject *ModDict;

static PyObject *
PyCurses_InitScr(PyObject *self)
{
    WINDOW *win;
    PyCursesWindowObject *winobj;

    if (initialised == 1) {
        wrefresh(stdscr);
        return (PyObject *)PyCursesWindow_New(stdscr, ((void *)0));
    }

    win = initscr();

    if (win == ((void *)0)) {
        PyErr_SetString(PyCursesError, catchall_NULL);
        return ((void *)0);
    }

    initialised = initialised_setupterm = 1;
# 2414 "_cursesmodule.c"
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('l')])))); if (o && PyDict_SetItemString(ModDict, "ACS_ULCORNER", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('m')])))); if (o && PyDict_SetItemString(ModDict, "ACS_LLCORNER", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('k')])))); if (o && PyDict_SetItemString(ModDict, "ACS_URCORNER", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('j')])))); if (o && PyDict_SetItemString(ModDict, "ACS_LRCORNER", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('t')])))); if (o && PyDict_SetItemString(ModDict, "ACS_LTEE", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('u')])))); if (o && PyDict_SetItemString(ModDict, "ACS_RTEE", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('v')])))); if (o && PyDict_SetItemString(ModDict, "ACS_BTEE", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('w')])))); if (o && PyDict_SetItemString(ModDict, "ACS_TTEE", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('q')])))); if (o && PyDict_SetItemString(ModDict, "ACS_HLINE", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('x')])))); if (o && PyDict_SetItemString(ModDict, "ACS_VLINE", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('n')])))); if (o && PyDict_SetItemString(ModDict, "ACS_PLUS", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);





    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('o')])))); if (o && PyDict_SetItemString(ModDict, "ACS_S1", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('s')])))); if (o && PyDict_SetItemString(ModDict, "ACS_S9", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('`')])))); if (o && PyDict_SetItemString(ModDict, "ACS_DIAMOND", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('a')])))); if (o && PyDict_SetItemString(ModDict, "ACS_CKBOARD", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('f')])))); if (o && PyDict_SetItemString(ModDict, "ACS_DEGREE", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('g')])))); if (o && PyDict_SetItemString(ModDict, "ACS_PLMINUS", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('~')])))); if (o && PyDict_SetItemString(ModDict, "ACS_BULLET", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)(',')])))); if (o && PyDict_SetItemString(ModDict, "ACS_LARROW", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('+')])))); if (o && PyDict_SetItemString(ModDict, "ACS_RARROW", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('.')])))); if (o && PyDict_SetItemString(ModDict, "ACS_DARROW", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('-')])))); if (o && PyDict_SetItemString(ModDict, "ACS_UARROW", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('h')])))); if (o && PyDict_SetItemString(ModDict, "ACS_BOARD", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('i')])))); if (o && PyDict_SetItemString(ModDict, "ACS_LANTERN", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('0')])))); if (o && PyDict_SetItemString(ModDict, "ACS_BLOCK", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);

    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('l')])))); if (o && PyDict_SetItemString(ModDict, "ACS_BSSB", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('m')])))); if (o && PyDict_SetItemString(ModDict, "ACS_SSBB", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('k')])))); if (o && PyDict_SetItemString(ModDict, "ACS_BBSS", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('j')])))); if (o && PyDict_SetItemString(ModDict, "ACS_SBBS", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('u')])))); if (o && PyDict_SetItemString(ModDict, "ACS_SBSS", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('t')])))); if (o && PyDict_SetItemString(ModDict, "ACS_SSSB", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('v')])))); if (o && PyDict_SetItemString(ModDict, "ACS_SSBS", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('w')])))); if (o && PyDict_SetItemString(ModDict, "ACS_BSSS", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('q')])))); if (o && PyDict_SetItemString(ModDict, "ACS_BSBS", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('x')])))); if (o && PyDict_SetItemString(ModDict, "ACS_SBSB", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('n')])))); if (o && PyDict_SetItemString(ModDict, "ACS_SSSS", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);



    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('p')])))); if (o && PyDict_SetItemString(ModDict, "ACS_S3", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);


    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('r')])))); if (o && PyDict_SetItemString(ModDict, "ACS_S7", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);


    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('y')])))); if (o && PyDict_SetItemString(ModDict, "ACS_LEQUAL", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);


    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('z')])))); if (o && PyDict_SetItemString(ModDict, "ACS_GEQUAL", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);


    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('{')])))); if (o && PyDict_SetItemString(ModDict, "ACS_PI", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);


    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('|')])))); if (o && PyDict_SetItemString(ModDict, "ACS_NEQUAL", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);


    do { PyObject *o = PyLong_FromLong((long) (((acs_map[(unsigned char)('}')])))); if (o && PyDict_SetItemString(ModDict, "ACS_STERLING", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);


    do { PyObject *o = PyLong_FromLong((long) (LINES)); if (o && PyDict_SetItemString(ModDict, "LINES", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (COLS)); if (o && PyDict_SetItemString(ModDict, "COLS", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);

    winobj = (PyCursesWindowObject *)PyCursesWindow_New(win, ((void *)0));
    screen_encoding = winobj->encoding;
    return (PyObject *)winobj;
}

static PyObject *
PyCurses_setupterm(PyObject* self, PyObject *args, PyObject* keywds)
{
    int fd = -1;
    int err;
    char* termstr = ((void *)0);

    static char *kwlist[] = {"term", "fd", ((void *)0)};

    if (!_PyArg_ParseTupleAndKeywords_SizeT(
            args, keywds, "|zi:setupterm", kwlist, &termstr, &fd)) {
        return ((void *)0);
    }

    if (fd == -1) {
        PyObject* sys_stdout;

        sys_stdout = PySys_GetObject("stdout");

        if (sys_stdout == ((void *)0) || sys_stdout == (&_Py_NoneStruct)) {
            PyErr_SetString(
                PyCursesError,
                "lost sys.stdout");
            return ((void *)0);
        }

        fd = PyObject_AsFileDescriptor(sys_stdout);

        if (fd == -1) {
            return ((void *)0);
        }
    }

    if (!initialised_setupterm && setupterm(termstr,fd,&err) == (-1)) {
        char* s = "setupterm: unknown error";

        if (err == 0) {
            s = "setupterm: could not find terminal";
        } else if (err == -1) {
            s = "setupterm: could not find terminfo database";
        }

        PyErr_SetString(PyCursesError,s);
        return ((void *)0);
    }

    initialised_setupterm = 1;

    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static PyObject *
PyCurses_IntrFlush(PyObject *self, PyObject *args)
{
    int ch;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    switch(PyTuple_Size(args)) {
    case 1:
        if (!_PyArg_ParseTuple_SizeT(args,"i;True(1), False(0)",&ch)) return ((void *)0);
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "intrflush requires 1 argument");
        return ((void *)0);
    }

    return PyCursesCheckERR(intrflush(((void *)0),ch), "intrflush");
}


static PyObject *
PyCurses_Is_Term_Resized(PyObject *self, PyObject *args)
{
    int lines;
    int columns;
    int result;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    if (!_PyArg_ParseTuple_SizeT(args,"ii:is_term_resized", &lines, &columns))
        return ((void *)0);
    result = is_term_resized(lines, columns);
    if (result == 1) {
        ( ((PyObject*)(((PyObject *) &_Py_TrueStruct)))->ob_refcnt++);
        return ((PyObject *) &_Py_TrueStruct);
    } else {
        ( ((PyObject*)(((PyObject *) &_Py_FalseStruct)))->ob_refcnt++);
        return ((PyObject *) &_Py_FalseStruct);
    }
}



static PyObject *
PyCurses_KeyName(PyObject *self, PyObject *args)
{
    const char *knp;
    int ch;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    if (!_PyArg_ParseTuple_SizeT(args,"i",&ch)) return ((void *)0);

    if (ch < 0) {
        PyErr_SetString(PyExc_ValueError, "invalid key number");
        return ((void *)0);
    }
    knp = keyname(ch);

    return PyBytes_FromString((knp == ((void *)0)) ? "" : (char *)knp);
}


static PyObject *
PyCurses_KillChar(PyObject *self)
{
    char ch;

    ch = killchar();

    return PyBytes_FromStringAndSize(&ch, 1);
}

static PyObject *
PyCurses_Meta(PyObject *self, PyObject *args)
{
    int ch;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    switch(PyTuple_Size(args)) {
    case 1:
        if (!_PyArg_ParseTuple_SizeT(args,"i;True(1), False(0)",&ch)) return ((void *)0);
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "meta requires 1 argument");
        return ((void *)0);
    }

    return PyCursesCheckERR(meta(stdscr, ch), "meta");
}


static PyObject *
PyCurses_MouseInterval(PyObject *self, PyObject *args)
{
    int interval;
    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    if (!_PyArg_ParseTuple_SizeT(args,"i;interval",&interval))
        return ((void *)0);
    return PyCursesCheckERR(mouseinterval(interval), "mouseinterval");
}

static PyObject *
PyCurses_MouseMask(PyObject *self, PyObject *args)
{
    int newmask;
    mmask_t oldmask, availmask;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };
    if (!_PyArg_ParseTuple_SizeT(args,"i;mousemask",&newmask))
        return ((void *)0);
    availmask = mousemask(newmask, &oldmask);
    return _Py_BuildValue_SizeT("(ll)", (long)availmask, (long)oldmask);
}


static PyObject *
PyCurses_Napms(PyObject *self, PyObject *args)
{
    int ms;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };
    if (!_PyArg_ParseTuple_SizeT(args, "i;ms", &ms)) return ((void *)0);

    return _Py_BuildValue_SizeT("i", napms(ms));
}


static PyObject *
PyCurses_NewPad(PyObject *self, PyObject *args)
{
    WINDOW *win;
    int nlines, ncols;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    if (!_PyArg_ParseTuple_SizeT(args,"ii;nlines,ncols",&nlines,&ncols)) return ((void *)0);

    win = newpad(nlines, ncols);

    if (win == ((void *)0)) {
        PyErr_SetString(PyCursesError, catchall_NULL);
        return ((void *)0);
    }

    return (PyObject *)PyCursesWindow_New(win, ((void *)0));
}

static PyObject *
PyCurses_NewWindow(PyObject *self, PyObject *args)
{
    WINDOW *win;
    int nlines, ncols, begin_y=0, begin_x=0;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    switch (PyTuple_Size(args)) {
    case 2:
        if (!_PyArg_ParseTuple_SizeT(args,"ii;nlines,ncols",&nlines,&ncols))
            return ((void *)0);
        break;
    case 4:
        if (!_PyArg_ParseTuple_SizeT(args, "iiii;nlines,ncols,begin_y,begin_x",
                              &nlines,&ncols,&begin_y,&begin_x))
            return ((void *)0);
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "newwin requires 2 or 4 arguments");
        return ((void *)0);
    }

    win = newwin(nlines,ncols,begin_y,begin_x);
    if (win == ((void *)0)) {
        PyErr_SetString(PyCursesError, catchall_NULL);
        return ((void *)0);
    }

    return (PyObject *)PyCursesWindow_New(win, ((void *)0));
}

static PyObject *
PyCurses_Pair_Content(PyObject *self, PyObject *args)
{
    short pair,f,b;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };
    if (initialisedcolors != 1) { PyErr_SetString(PyCursesError, "must call start_color() first"); return 0; };

    switch(PyTuple_Size(args)) {
    case 1:
        if (!_PyArg_ParseTuple_SizeT(args, "h;pair", &pair)) return ((void *)0);
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "pair_content requires 1 argument");
        return ((void *)0);
    }

    if (pair_content(pair, &f, &b)==(-1)) {
        PyErr_SetString(PyCursesError,
                        "Argument 1 was out of range. (1..COLOR_PAIRS-1)");
        return ((void *)0);
    }

    return _Py_BuildValue_SizeT("(ii)", f, b);
}

static PyObject *
PyCurses_pair_number(PyObject *self, PyObject *args)
{
    int n;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };
    if (initialisedcolors != 1) { PyErr_SetString(PyCursesError, "must call start_color() first"); return 0; };

    switch(PyTuple_Size(args)) {
    case 1:
        if (!_PyArg_ParseTuple_SizeT(args, "i;pairvalue", &n)) return ((void *)0);
        break;
    default:
        PyErr_SetString(PyExc_TypeError,
                        "pair_number requires 1 argument");
        return ((void *)0);
    }

    return PyLong_FromLong((long) ((n & ((((1U) << 8) - 1U) << ((0) + 8))) >> 8));
}

static PyObject *
PyCurses_Putp(PyObject *self, PyObject *args)
{
    char *str;

    if (!_PyArg_ParseTuple_SizeT(args,"y;str", &str))
        return ((void *)0);
    return PyCursesCheckERR(putp(str), "putp");
}

static PyObject *
PyCurses_QiFlush(PyObject *self, PyObject *args)
{
    int flag = 0;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    switch(PyTuple_Size(args)) {
    case 0:
        qiflush();
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        return (&_Py_NoneStruct);
    case 1:
        if (!_PyArg_ParseTuple_SizeT(args, "i;True(1) or False(0)", &flag)) return ((void *)0);
        if (flag) qiflush();
        else noqiflush();
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        return (&_Py_NoneStruct);
    default:
        PyErr_SetString(PyExc_TypeError, "qiflush requires 0 or 1 arguments");
        return ((void *)0);
    }
}




static int
update_lines_cols(void)
{
    PyObject *o;
    PyObject *m = PyImport_ImportModuleNoBlock("curses");
    static _Py_Identifier PyId_LINES = { 0, "LINES", 0 };
    static _Py_Identifier PyId_COLS = { 0, "COLS", 0 };

    if (!m)
        return 0;

    o = PyLong_FromLong(LINES);
    if (!o) {
        do { if ( --((PyObject*)(m))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(m)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(m)))); } while (0);
        return 0;
    }
    if (_PyObject_SetAttrId(m, &PyId_LINES, o)) {
        do { if ( --((PyObject*)(m))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(m)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(m)))); } while (0);
        do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0);
        return 0;
    }

    if (PyDict_SetItem(ModDict, PyId_LINES.object, o)) {
        do { if ( --((PyObject*)(m))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(m)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(m)))); } while (0);
        do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0);
        return 0;
    }
    do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0);
    o = PyLong_FromLong(COLS);
    if (!o) {
        do { if ( --((PyObject*)(m))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(m)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(m)))); } while (0);
        return 0;
    }
    if (_PyObject_SetAttrId(m, &PyId_COLS, o)) {
        do { if ( --((PyObject*)(m))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(m)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(m)))); } while (0);
        do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0);
        return 0;
    }
    if (PyDict_SetItem(ModDict, PyId_COLS.object, o)) {
        do { if ( --((PyObject*)(m))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(m)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(m)))); } while (0);
        do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0);
        return 0;
    }
    do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0);
    do { if ( --((PyObject*)(m))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(m)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(m)))); } while (0);
    return 1;
}



static PyObject *
PyCurses_ResizeTerm(PyObject *self, PyObject *args)
{
    int lines;
    int columns;
    PyObject *result;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    if (!_PyArg_ParseTuple_SizeT(args,"ii:resizeterm", &lines, &columns))
        return ((void *)0);

    result = PyCursesCheckERR(resizeterm(lines, columns), "resizeterm");
    if (!result)
        return ((void *)0);
    if (!update_lines_cols())
        return ((void *)0);
    return result;
}




static PyObject *
PyCurses_Resize_Term(PyObject *self, PyObject *args)
{
    int lines;
    int columns;

    PyObject *result;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    if (!_PyArg_ParseTuple_SizeT(args,"ii:resize_term", &lines, &columns))
        return ((void *)0);

    result = PyCursesCheckERR(resize_term(lines, columns), "resize_term");
    if (!result)
        return ((void *)0);
    if (!update_lines_cols())
        return ((void *)0);
    return result;
}


static PyObject *
PyCurses_setsyx(PyObject *self, PyObject *args)
{
    int y,x;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    if (PyTuple_Size(args)!=2) {
        PyErr_SetString(PyExc_TypeError, "setsyx requires 2 arguments");
        return ((void *)0);
    }

    if (!_PyArg_ParseTuple_SizeT(args, "ii;y, x", &y, &x)) return ((void *)0);

    do { if (newscr) { if ((y) == -1 && (x) == -1) leaveok(newscr, 1); else { leaveok(newscr, 0); wmove(newscr, (y), (x)); } } } while(0);

    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static PyObject *
PyCurses_Start_Color(PyObject *self)
{
    int code;
    PyObject *c, *cp;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    code = start_color();
    if (code != (-1)) {
        initialisedcolors = 1;
        c = PyLong_FromLong((long) COLORS);
        PyDict_SetItemString(ModDict, "COLORS", c);
        do { if ( --((PyObject*)(c))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(c)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(c)))); } while (0);
        cp = PyLong_FromLong((long) COLOR_PAIRS);
        PyDict_SetItemString(ModDict, "COLOR_PAIRS", cp);
        do { if ( --((PyObject*)(cp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(cp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(cp)))); } while (0);
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        return (&_Py_NoneStruct);
    } else {
        PyErr_SetString(PyCursesError, "start_color() returned ERR");
        return ((void *)0);
    }
}

static PyObject *
PyCurses_tigetflag(PyObject *self, PyObject *args)
{
    char *capname;

    if (initialised_setupterm != 1) { PyErr_SetString(PyCursesError, "must call (at least) setupterm() first"); return 0; };

    if (!_PyArg_ParseTuple_SizeT(args, "s", &capname))
        return ((void *)0);

    return PyLong_FromLong( (long) tigetflag( capname ) );
}

static PyObject *
PyCurses_tigetnum(PyObject *self, PyObject *args)
{
    char *capname;

    if (initialised_setupterm != 1) { PyErr_SetString(PyCursesError, "must call (at least) setupterm() first"); return 0; };

    if (!_PyArg_ParseTuple_SizeT(args, "s", &capname))
        return ((void *)0);

    return PyLong_FromLong( (long) tigetnum( capname ) );
}

static PyObject *
PyCurses_tigetstr(PyObject *self, PyObject *args)
{
    char *capname;

    if (initialised_setupterm != 1) { PyErr_SetString(PyCursesError, "must call (at least) setupterm() first"); return 0; };

    if (!_PyArg_ParseTuple_SizeT(args, "s", &capname))
        return ((void *)0);

    capname = tigetstr( capname );
    if (capname == 0 || capname == (char*) -1) {
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        return (&_Py_NoneStruct);
    }
    return PyBytes_FromString( capname );
}

static PyObject *
PyCurses_tparm(PyObject *self, PyObject *args)
{
    char* fmt;
    char* result = ((void *)0);
    int i1=0,i2=0,i3=0,i4=0,i5=0,i6=0,i7=0,i8=0,i9=0;

    if (initialised_setupterm != 1) { PyErr_SetString(PyCursesError, "must call (at least) setupterm() first"); return 0; };

    if (!_PyArg_ParseTuple_SizeT(args, "y|iiiiiiiii:tparm",
                          &fmt, &i1, &i2, &i3, &i4,
                          &i5, &i6, &i7, &i8, &i9)) {
        return ((void *)0);
    }

    result = tparm(fmt,i1,i2,i3,i4,i5,i6,i7,i8,i9);
    if (!result) {
        PyErr_SetString(PyCursesError, "tparm() returned NULL");
        return ((void *)0);
    }

    return PyBytes_FromString(result);
}

static PyObject *
PyCurses_TypeAhead(PyObject *self, PyObject *args)
{
    int fd;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    if (!_PyArg_ParseTuple_SizeT(args,"i;fd",&fd)) return ((void *)0);

    return PyCursesCheckERR(typeahead( fd ), "typeahead");
}

static PyObject *
PyCurses_UnCtrl(PyObject *self, PyObject *args)
{
    PyObject *temp;
    chtype ch;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    if (!_PyArg_ParseTuple_SizeT(args,"O;ch or int",&temp)) return ((void *)0);

    if (!PyCurses_ConvertToChtype(((void *)0), temp, &ch))
        return ((void *)0);

    return PyBytes_FromString(unctrl(ch));
}

static PyObject *
PyCurses_UngetCh(PyObject *self, PyObject *args)
{
    PyObject *temp;
    chtype ch;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };

    if (!_PyArg_ParseTuple_SizeT(args,"O;ch or int",&temp))
        return ((void *)0);

    if (!PyCurses_ConvertToChtype(((void *)0), temp, &ch))
        return ((void *)0);

    return PyCursesCheckERR(ungetch(ch), "ungetch");
}
# 3124 "_cursesmodule.c"
static PyObject *
PyCurses_Use_Env(PyObject *self, PyObject *args)
{
    int flag;

    switch(PyTuple_Size(args)) {
    case 1:
        if (!_PyArg_ParseTuple_SizeT(args,"i;True(1), False(0)",&flag))
            return ((void *)0);
        break;
    default:
        PyErr_SetString(PyExc_TypeError, "use_env requires 1 argument");
        return ((void *)0);
    }
    use_env(flag);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}


static PyObject *
PyCurses_Use_Default_Colors(PyObject *self)
{
    int code;

    if (initialised != 1) { PyErr_SetString(PyCursesError, "must call initscr() first"); return 0; };
    if (initialisedcolors != 1) { PyErr_SetString(PyCursesError, "must call start_color() first"); return 0; };

    code = use_default_colors();
    if (code != (-1)) {
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        return (&_Py_NoneStruct);
    } else {
        PyErr_SetString(PyCursesError, "use_default_colors() returned ERR");
        return ((void *)0);
    }
}




static PyMethodDef PyCurses_methods[] = {
    {"baudrate", (PyCFunction)PyCurses_baudrate, 0x0004},
    {"beep", (PyCFunction)PyCurses_beep, 0x0004},
    {"can_change_color", (PyCFunction)PyCurses_can_change_color, 0x0004},
    {"cbreak", (PyCFunction)PyCurses_cbreak, 0x0001},
    {"color_content", (PyCFunction)PyCurses_Color_Content, 0x0001},
    {"color_pair", (PyCFunction)PyCurses_color_pair, 0x0001},
    {"curs_set", (PyCFunction)PyCurses_Curs_Set, 0x0001},
    {"def_prog_mode", (PyCFunction)PyCurses_def_prog_mode, 0x0004},
    {"def_shell_mode", (PyCFunction)PyCurses_def_shell_mode, 0x0004},
    {"delay_output", (PyCFunction)PyCurses_Delay_Output, 0x0001},
    {"doupdate", (PyCFunction)PyCurses_doupdate, 0x0004},
    {"echo", (PyCFunction)PyCurses_echo, 0x0001},
    {"endwin", (PyCFunction)PyCurses_endwin, 0x0004},
    {"erasechar", (PyCFunction)PyCurses_EraseChar, 0x0004},
    {"filter", (PyCFunction)PyCurses_filter, 0x0004},
    {"flash", (PyCFunction)PyCurses_flash, 0x0004},
    {"flushinp", (PyCFunction)PyCurses_flushinp, 0x0004},

    {"getmouse", (PyCFunction)PyCurses_GetMouse, 0x0004},
    {"ungetmouse", (PyCFunction)PyCurses_UngetMouse, 0x0001},

    {"getsyx", (PyCFunction)PyCurses_getsyx, 0x0004},
    {"getwin", (PyCFunction)PyCurses_GetWin, 0x0008},
    {"has_colors", (PyCFunction)PyCurses_has_colors, 0x0004},
    {"has_ic", (PyCFunction)PyCurses_has_ic, 0x0004},
    {"has_il", (PyCFunction)PyCurses_has_il, 0x0004},

    {"has_key", (PyCFunction)PyCurses_has_key, 0x0001},

    {"halfdelay", (PyCFunction)PyCurses_HalfDelay, 0x0001},
    {"init_color", (PyCFunction)PyCurses_Init_Color, 0x0001},
    {"init_pair", (PyCFunction)PyCurses_Init_Pair, 0x0001},
    {"initscr", (PyCFunction)PyCurses_InitScr, 0x0004},
    {"intrflush", (PyCFunction)PyCurses_IntrFlush, 0x0001},
    {"isendwin", (PyCFunction)PyCurses_isendwin, 0x0004},

    {"is_term_resized", (PyCFunction)PyCurses_Is_Term_Resized, 0x0001},


    {"keyname", (PyCFunction)PyCurses_KeyName, 0x0001},

    {"killchar", (PyCFunction)PyCurses_KillChar, 0x0004},
    {"longname", (PyCFunction)PyCurses_longname, 0x0004},
    {"meta", (PyCFunction)PyCurses_Meta, 0x0001},

    {"mouseinterval", (PyCFunction)PyCurses_MouseInterval, 0x0001},
    {"mousemask", (PyCFunction)PyCurses_MouseMask, 0x0001},

    {"napms", (PyCFunction)PyCurses_Napms, 0x0001},
    {"newpad", (PyCFunction)PyCurses_NewPad, 0x0001},
    {"newwin", (PyCFunction)PyCurses_NewWindow, 0x0001},
    {"nl", (PyCFunction)PyCurses_nl, 0x0001},
    {"nocbreak", (PyCFunction)PyCurses_nocbreak, 0x0004},
    {"noecho", (PyCFunction)PyCurses_noecho, 0x0004},
    {"nonl", (PyCFunction)PyCurses_nonl, 0x0004},
    {"noqiflush", (PyCFunction)PyCurses_noqiflush, 0x0004},
    {"noraw", (PyCFunction)PyCurses_noraw, 0x0004},
    {"pair_content", (PyCFunction)PyCurses_Pair_Content, 0x0001},
    {"pair_number", (PyCFunction)PyCurses_pair_number, 0x0001},
    {"putp", (PyCFunction)PyCurses_Putp, 0x0001},
    {"qiflush", (PyCFunction)PyCurses_QiFlush, 0x0001},
    {"raw", (PyCFunction)PyCurses_raw, 0x0001},
    {"reset_prog_mode", (PyCFunction)PyCurses_reset_prog_mode, 0x0004},
    {"reset_shell_mode", (PyCFunction)PyCurses_reset_shell_mode, 0x0004},
    {"resetty", (PyCFunction)PyCurses_resetty, 0x0004},

    {"resizeterm", (PyCFunction)PyCurses_ResizeTerm, 0x0001},


    {"resize_term", (PyCFunction)PyCurses_Resize_Term, 0x0001},

    {"savetty", (PyCFunction)PyCurses_savetty, 0x0004},
    {"setsyx", (PyCFunction)PyCurses_setsyx, 0x0001},
    {"setupterm", (PyCFunction)PyCurses_setupterm,
     0x0001|0x0002},
    {"start_color", (PyCFunction)PyCurses_Start_Color, 0x0004},
    {"termattrs", (PyCFunction)PyCurses_termattrs, 0x0004},
    {"termname", (PyCFunction)PyCurses_termname, 0x0004},
    {"tigetflag", (PyCFunction)PyCurses_tigetflag, 0x0001},
    {"tigetnum", (PyCFunction)PyCurses_tigetnum, 0x0001},
    {"tigetstr", (PyCFunction)PyCurses_tigetstr, 0x0001},
    {"tparm", (PyCFunction)PyCurses_tparm, 0x0001},
    {"typeahead", (PyCFunction)PyCurses_TypeAhead, 0x0001},
    {"unctrl", (PyCFunction)PyCurses_UnCtrl, 0x0001},
    {"ungetch", (PyCFunction)PyCurses_UngetCh, 0x0001},



    {"use_env", (PyCFunction)PyCurses_Use_Env, 0x0001},

    {"use_default_colors", (PyCFunction)PyCurses_Use_Default_Colors, 0x0004},

    {((void *)0), ((void *)0)}
};




static struct PyModuleDef _cursesmodule = {
    { { 1, ((void *)0) }, ((void *)0), 0, ((void *)0), },
    "_curses",
    ((void *)0),
    -1,
    PyCurses_methods,
    ((void *)0),
    ((void *)0),
    ((void *)0),
    ((void *)0)
};

PyObject*
PyInit__curses(void)
{
    PyObject *m, *d, *v, *c_api_object;
    static void *PyCurses_API[4];


    if (PyType_Ready(&PyCursesWindow_Type) < 0)
        return ((void *)0);


    PyCurses_API[0] = (void *)&PyCursesWindow_Type;
    PyCurses_API[1] = (void *)func_PyCursesSetupTermCalled;
    PyCurses_API[2] = (void *)func_PyCursesInitialised;
    PyCurses_API[3] = (void *)func_PyCursesInitialisedColor;


    m = PyModule_Create2(&_cursesmodule, 1013);
    if (m == ((void *)0))
        return ((void *)0);


    d = PyModule_GetDict(m);
    if (d == ((void *)0))
        return ((void *)0);
    ModDict = d;


    c_api_object = PyCapsule_New(PyCurses_API, "_curses._C_API", ((void *)0));
    PyDict_SetItemString(d, "_C_API", c_api_object);
    do { if ( --((PyObject*)(c_api_object))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(c_api_object)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(c_api_object)))); } while (0);


    PyCursesError = PyErr_NewException("_curses.error", ((void *)0), ((void *)0));
    PyDict_SetItemString(d, "error", PyCursesError);


    v = PyBytes_FromString(PyCursesVersion);
    PyDict_SetItemString(d, "version", v);
    PyDict_SetItemString(d, "__version__", v);
    do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);

    do { PyObject *o = PyLong_FromLong((long) ((-1))); if (o && PyDict_SetItemString(ModDict, "ERR", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) ((0))); if (o && PyDict_SetItemString(ModDict, "OK", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);



    do { PyObject *o = PyLong_FromLong((long) (((~(1U - 1U)) << ((0) + 8)))); if (o && PyDict_SetItemString(ModDict, "A_ATTRIBUTES", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) ((1U - 1U))); if (o && PyDict_SetItemString(ModDict, "A_NORMAL", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((1U) << ((8) + 8)))); if (o && PyDict_SetItemString(ModDict, "A_STANDOUT", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((1U) << ((9) + 8)))); if (o && PyDict_SetItemString(ModDict, "A_UNDERLINE", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((1U) << ((10) + 8)))); if (o && PyDict_SetItemString(ModDict, "A_REVERSE", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((1U) << ((11) + 8)))); if (o && PyDict_SetItemString(ModDict, "A_BLINK", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((1U) << ((12) + 8)))); if (o && PyDict_SetItemString(ModDict, "A_DIM", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((1U) << ((13) + 8)))); if (o && PyDict_SetItemString(ModDict, "A_BOLD", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((1U) << ((14) + 8)))); if (o && PyDict_SetItemString(ModDict, "A_ALTCHARSET", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);

    do { PyObject *o = PyLong_FromLong((long) (((1U) << ((15) + 8)))); if (o && PyDict_SetItemString(ModDict, "A_INVIS", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);

    do { PyObject *o = PyLong_FromLong((long) (((1U) << ((16) + 8)))); if (o && PyDict_SetItemString(ModDict, "A_PROTECT", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) ((((1U) << ((0) + 8)) - 1U))); if (o && PyDict_SetItemString(ModDict, "A_CHARTEXT", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((((1U) << 8) - 1U) << ((0) + 8)))); if (o && PyDict_SetItemString(ModDict, "A_COLOR", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);



    do { PyObject *o = PyLong_FromLong((long) (((1U) << ((17) + 8)))); if (o && PyDict_SetItemString(ModDict, "A_HORIZONTAL", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);


    do { PyObject *o = PyLong_FromLong((long) (((1U) << ((18) + 8)))); if (o && PyDict_SetItemString(ModDict, "A_LEFT", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);


    do { PyObject *o = PyLong_FromLong((long) (((1U) << ((19) + 8)))); if (o && PyDict_SetItemString(ModDict, "A_LOW", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);


    do { PyObject *o = PyLong_FromLong((long) (((1U) << ((20) + 8)))); if (o && PyDict_SetItemString(ModDict, "A_RIGHT", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);


    do { PyObject *o = PyLong_FromLong((long) (((1U) << ((21) + 8)))); if (o && PyDict_SetItemString(ModDict, "A_TOP", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);


    do { PyObject *o = PyLong_FromLong((long) (((1U) << ((22) + 8)))); if (o && PyDict_SetItemString(ModDict, "A_VERTICAL", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);


    do { PyObject *o = PyLong_FromLong((long) (0)); if (o && PyDict_SetItemString(ModDict, "COLOR_BLACK", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (1)); if (o && PyDict_SetItemString(ModDict, "COLOR_RED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (2)); if (o && PyDict_SetItemString(ModDict, "COLOR_GREEN", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (3)); if (o && PyDict_SetItemString(ModDict, "COLOR_YELLOW", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (4)); if (o && PyDict_SetItemString(ModDict, "COLOR_BLUE", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (5)); if (o && PyDict_SetItemString(ModDict, "COLOR_MAGENTA", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (6)); if (o && PyDict_SetItemString(ModDict, "COLOR_CYAN", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (7)); if (o && PyDict_SetItemString(ModDict, "COLOR_WHITE", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);



    do { PyObject *o = PyLong_FromLong((long) (((002L) << (((1) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON1_PRESSED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((001L) << (((1) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON1_RELEASED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((004L) << (((1) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON1_CLICKED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((010L) << (((1) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON1_DOUBLE_CLICKED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((020L) << (((1) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON1_TRIPLE_CLICKED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);

    do { PyObject *o = PyLong_FromLong((long) (((002L) << (((2) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON2_PRESSED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((001L) << (((2) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON2_RELEASED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((004L) << (((2) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON2_CLICKED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((010L) << (((2) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON2_DOUBLE_CLICKED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((020L) << (((2) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON2_TRIPLE_CLICKED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);

    do { PyObject *o = PyLong_FromLong((long) (((002L) << (((3) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON3_PRESSED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((001L) << (((3) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON3_RELEASED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((004L) << (((3) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON3_CLICKED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((010L) << (((3) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON3_DOUBLE_CLICKED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((020L) << (((3) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON3_TRIPLE_CLICKED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);

    do { PyObject *o = PyLong_FromLong((long) (((002L) << (((4) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON4_PRESSED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((001L) << (((4) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON4_RELEASED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((004L) << (((4) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON4_CLICKED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((010L) << (((4) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON4_DOUBLE_CLICKED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((020L) << (((4) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON4_TRIPLE_CLICKED", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);

    do { PyObject *o = PyLong_FromLong((long) (((0002L) << (((5) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON_SHIFT", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((0001L) << (((5) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON_CTRL", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((0004L) << (((5) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "BUTTON_ALT", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);

    do { PyObject *o = PyLong_FromLong((long) ((((0010L) << (((5) - 1) * 6)) - 1))); if (o && PyDict_SetItemString(ModDict, "ALL_MOUSE_EVENTS", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    do { PyObject *o = PyLong_FromLong((long) (((0010L) << (((5) - 1) * 6)))); if (o && PyDict_SetItemString(ModDict, "REPORT_MOUSE_POSITION", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);


    {
        int key;
        char *key_n;
        char *key_n2;

        for (key=0401;key < 0777; key++) {
            key_n = (char *)keyname(key);
            if (key_n == ((void *)0) || strcmp(key_n,"UNKNOWN KEY")==0)
                continue;
            if (strncmp(key_n,"KEY_F(",6)==0) {
                char *p1, *p2;
                key_n2 = malloc(strlen(key_n)+1);
                if (!key_n2) {
                    PyErr_NoMemory();
                    break;
                }
                p1 = key_n;
                p2 = key_n2;
                while (*p1) {
                    if (*p1 != '(' && *p1 != ')') {
                        *p2 = *p1;
                        p2++;
                    }
                    p1++;
                }
                *p2 = (char)0;
            } else
                key_n2 = key_n;
            do { PyObject *o = PyLong_FromLong((long) (key)); if (o && PyDict_SetItemString(ModDict, key_n2, o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
            if (key_n2 != key_n)
                free(key_n2);
        }

        do { PyObject *o = PyLong_FromLong((long) (0401)); if (o && PyDict_SetItemString(ModDict, "KEY_MIN", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
        do { PyObject *o = PyLong_FromLong((long) (0777)); if (o && PyDict_SetItemString(ModDict, "KEY_MAX", o) == 0) { do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } } while (0);
    }
    return m;
}
