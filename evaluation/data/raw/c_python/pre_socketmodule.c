# 1 "socketmodule.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "socketmodule.c"
# 92 "socketmodule.c"
#pragma weak inet_aton


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
# 96 "socketmodule.c" 2
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
# 97 "socketmodule.c" 2





static char sock_doc[] = "socket([family[, type[, proto]]]) -> socket object\n\nOpen a socket of the given type.  The family argument specifies the\naddress family; it defaults to AF_INET.  The type argument specifies\nwhether this is a stream (SOCK_STREAM, this is the default)\nor datagram (SOCK_DGRAM) socket.  The protocol argument defaults to 0,\nspecifying the default protocol.  Keyword arguments are accepted.\n\nA socket object represents one endpoint of a network connection.\n\nMethods of socket objects (keyword arguments not allowed):\n\n_accept() -- accept connection, returning new socket fd and client address\nbind(addr) -- bind the socket to a local address\nclose() -- close the socket\nconnect(addr) -- connect the socket to a remote address\nconnect_ex(addr) -- connect, return an error code instead of an exception\n_dup() -- return a new socket fd duplicated from fileno()\nfileno() -- return underlying file descriptor\ngetpeername() -- return remote address [*]\ngetsockname() -- return local address\ngetsockopt(level, optname[, buflen]) -- get socket options\ngettimeout() -- return timeout or None\nlisten(n) -- start listening for incoming connections\nrecv(buflen[, flags]) -- receive data\nrecv_into(buffer[, nbytes[, flags]]) -- receive data (into a buffer)\nrecvfrom(buflen[, flags]) -- receive data and sender\'s address\nrecvfrom_into(buffer[, nbytes, [, flags])\n  -- receive data and sender\'s address (into a buffer)\nsendall(data[, flags]) -- send all data\nsend(data[, flags]) -- send data, may not send all of it\nsendto(data[, flags], addr) -- send data to a given address\nsetblocking(0 | 1) -- set or clear the blocking I/O flag\nsetsockopt(level, optname, value) -- set socket options\nsettimeout(None | float) -- set or clear the timeout\nshutdown(how) -- shut down traffic in one or both directions\nif_nameindex() -- return all network interface indices and names\nif_nametoindex(name) -- return the corresponding interface index\nif_indextoname(index) -- return the corresponding interface name\n\n [*] not available on all platforms!";
# 186 "socketmodule.c"
# 1 "/usr/include/sys/param.h" 1 3 4
# 86 "/usr/include/sys/param.h" 3 4
# 1 "/usr/include/sys/types.h" 1 3 4
# 84 "/usr/include/sys/types.h" 3 4
typedef unsigned char u_char;
typedef unsigned short u_short;
typedef unsigned int u_int;

typedef unsigned long u_long;


typedef unsigned short ushort;
typedef unsigned int uint;


typedef u_int64_t u_quad_t;
typedef int64_t quad_t;
typedef quad_t * qaddr_t;

typedef char * caddr_t;
typedef int32_t daddr_t;






typedef u_int32_t fixpt_t;
# 126 "/usr/include/sys/types.h" 3 4
typedef __uint32_t in_addr_t;




typedef __uint16_t in_port_t;
# 148 "/usr/include/sys/types.h" 3 4
typedef __int32_t key_t;
# 176 "/usr/include/sys/types.h" 3 4
typedef int32_t segsz_t;
typedef int32_t swblk_t;
# 260 "/usr/include/sys/types.h" 3 4
# 1 "/usr/include/sys/_structs.h" 1 3 4
# 261 "/usr/include/sys/types.h" 2 3 4




typedef __int32_t fd_mask;
# 322 "/usr/include/sys/types.h" 3 4
typedef __darwin_pthread_cond_t pthread_cond_t;



typedef __darwin_pthread_condattr_t pthread_condattr_t;



typedef __darwin_pthread_mutex_t pthread_mutex_t;



typedef __darwin_pthread_mutexattr_t pthread_mutexattr_t;



typedef __darwin_pthread_once_t pthread_once_t;



typedef __darwin_pthread_rwlock_t pthread_rwlock_t;



typedef __darwin_pthread_rwlockattr_t pthread_rwlockattr_t;



typedef __darwin_pthread_t pthread_t;






typedef __darwin_pthread_key_t pthread_key_t;





typedef __darwin_fsblkcnt_t fsblkcnt_t;




typedef __darwin_fsfilcnt_t fsfilcnt_t;
# 87 "/usr/include/sys/param.h" 2 3 4
# 110 "/usr/include/sys/param.h" 3 4
# 1 "/usr/include/machine/param.h" 1 3 4
# 35 "/usr/include/machine/param.h" 3 4
# 1 "/usr/include/i386/param.h" 1 3 4
# 75 "/usr/include/i386/param.h" 3 4
# 1 "/usr/include/i386/_param.h" 1 3 4
# 76 "/usr/include/i386/param.h" 2 3 4
# 36 "/usr/include/machine/param.h" 2 3 4
# 111 "/usr/include/sys/param.h" 2 3 4


# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/limits.h" 1 3 4






# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/syslimits.h" 1 3 4
# 8 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/limits.h" 2 3 4
# 114 "/usr/include/sys/param.h" 2 3 4
# 187 "socketmodule.c" 2
# 206 "socketmodule.c"
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/pythread.h" 1




typedef void *PyThread_type_lock;
typedef void *PyThread_type_sema;







typedef enum PyLockStatus {
    PY_LOCK_FAILURE = 0,
    PY_LOCK_ACQUIRED = 1,
    PY_LOCK_INTR
} PyLockStatus;

void PyThread_init_thread(void);
long PyThread_start_new_thread(void (*)(void *), void *);
void PyThread_exit_thread(void);
long PyThread_get_thread_ident(void);

PyThread_type_lock PyThread_allocate_lock(void);
void PyThread_free_lock(PyThread_type_lock);
int PyThread_acquire_lock(PyThread_type_lock, int);
# 68 "/Users/parrt/tmp/Python-3.3.1/Include/pythread.h"
PyLockStatus PyThread_acquire_lock_timed(PyThread_type_lock,
                                                     long long microseconds,
                                                     int intr_flag);

void PyThread_release_lock(PyThread_type_lock);

size_t PyThread_get_stacksize(void);
int PyThread_set_stacksize(size_t);

PyObject* PyThread_GetInfo(void);


int PyThread_create_key(void);
void PyThread_delete_key(int);
int PyThread_set_key_value(int, void *);
void * PyThread_get_key_value(int);
void PyThread_delete_key_value(int key);


void PyThread_ReInitTLS(void);
# 207 "socketmodule.c" 2
# 222 "socketmodule.c"
# 1 "/usr/include/sys/ioctl.h" 1 3 4
# 79 "/usr/include/sys/ioctl.h" 3 4
struct ttysize {
 unsigned short ts_lines;
 unsigned short ts_cols;
 unsigned short ts_xxx;
 unsigned short ts_yyy;
};





# 1 "/usr/include/sys/filio.h" 1 3 4
# 91 "/usr/include/sys/ioctl.h" 2 3 4
# 1 "/usr/include/sys/sockio.h" 1 3 4
# 92 "/usr/include/sys/ioctl.h" 2 3 4





int ioctl(int, unsigned long, ...);

# 223 "socketmodule.c" 2
# 269 "socketmodule.c"
# 1 "/usr/include/sys/socket.h" 1 3 4
# 77 "/usr/include/sys/socket.h" 3 4
# 1 "/usr/include/machine/_param.h" 1 3 4
# 78 "/usr/include/sys/socket.h" 2 3 4
# 106 "/usr/include/sys/socket.h" 3 4
typedef __uint8_t sa_family_t;




typedef __darwin_socklen_t socklen_t;
# 131 "/usr/include/sys/socket.h" 3 4
struct iovec {
 void * iov_base;
 size_t iov_len;
};
# 219 "/usr/include/sys/socket.h" 3 4
struct linger {
 int l_onoff;
 int l_linger;
};
# 237 "/usr/include/sys/socket.h" 3 4
struct so_np_extensions {
 u_int32_t npx_flags;
 u_int32_t npx_mask;
};
# 322 "/usr/include/sys/socket.h" 3 4
struct sockaddr {
 __uint8_t sa_len;
 sa_family_t sa_family;
 char sa_data[14];
};
# 335 "/usr/include/sys/socket.h" 3 4
struct sockproto {
 __uint16_t sp_family;
 __uint16_t sp_protocol;
};
# 355 "/usr/include/sys/socket.h" 3 4
struct sockaddr_storage {
 __uint8_t ss_len;
 sa_family_t ss_family;
 char __ss_pad1[((sizeof(__int64_t)) - sizeof(__uint8_t) - sizeof(sa_family_t))];
 __int64_t __ss_align;
 char __ss_pad2[(128 - sizeof(__uint8_t) - sizeof(sa_family_t) - ((sizeof(__int64_t)) - sizeof(__uint8_t) - sizeof(sa_family_t)) - (sizeof(__int64_t)))];
};
# 462 "/usr/include/sys/socket.h" 3 4
struct msghdr {
 void *msg_name;
 socklen_t msg_namelen;
 struct iovec *msg_iov;
 int msg_iovlen;
 void *msg_control;
 socklen_t msg_controllen;
 int msg_flags;
};
# 502 "/usr/include/sys/socket.h" 3 4
struct cmsghdr {
 socklen_t cmsg_len;
 int cmsg_level;
 int cmsg_type;

};
# 592 "/usr/include/sys/socket.h" 3 4
struct sf_hdtr {
 struct iovec *headers;
 int hdr_cnt;
 struct iovec *trailers;
 int trl_cnt;
};





int accept(int, struct sockaddr * , socklen_t * )
  __asm("_" "accept" );
int bind(int, const struct sockaddr *, socklen_t) __asm("_" "bind" );
int connect(int, const struct sockaddr *, socklen_t) __asm("_" "connect" );
int getpeername(int, struct sockaddr * , socklen_t * )
  __asm("_" "getpeername" );
int getsockname(int, struct sockaddr * , socklen_t * )
  __asm("_" "getsockname" );
int getsockopt(int, int, int, void * , socklen_t * );
int listen(int, int) __asm("_" "listen" );
ssize_t recv(int, void *, size_t, int) __asm("_" "recv" );
ssize_t recvfrom(int, void *, size_t, int, struct sockaddr * ,
  socklen_t * ) __asm("_" "recvfrom" );
ssize_t recvmsg(int, struct msghdr *, int) __asm("_" "recvmsg" );
ssize_t send(int, const void *, size_t, int) __asm("_" "send" );
ssize_t sendmsg(int, const struct msghdr *, int) __asm("_" "sendmsg" );
ssize_t sendto(int, const void *, size_t,
  int, const struct sockaddr *, socklen_t) __asm("_" "sendto" );
int setsockopt(int, int, int, const void *, socklen_t);
int shutdown(int, int);
int sockatmark(int) __attribute__((visibility("default")));
int socket(int, int, int);
int socketpair(int, int, int, int *) __asm("_" "socketpair" );


int sendfile(int, int, off_t, off_t *, struct sf_hdtr *, int);



void pfctlinput(int, struct sockaddr *);


# 270 "socketmodule.c" 2



# 1 "/usr/include/net/if.h" 1 3 4
# 101 "/usr/include/net/if.h" 3 4
# 1 "/usr/include/net/if_var.h" 1 3 4
# 71 "/usr/include/net/if_var.h" 3 4
# 1 "/usr/include/sys/queue.h" 1 3 4
# 72 "/usr/include/net/if_var.h" 2 3 4
# 129 "/usr/include/net/if_var.h" 3 4
struct net_event_data {
 u_int32_t if_family;
 u_int32_t if_unit;
 char if_name[16];
};



# 1 "/usr/include/sys/_structs.h" 1 3 4
# 112 "/usr/include/sys/_structs.h" 3 4
struct timeval32
{
 __int32_t tv_sec;
 __int32_t tv_usec;
};
# 138 "/usr/include/net/if_var.h" 2 3 4





#pragma pack(4)





struct if_data {

 u_char ifi_type;
 u_char ifi_typelen;
 u_char ifi_physical;
 u_char ifi_addrlen;
 u_char ifi_hdrlen;
 u_char ifi_recvquota;
 u_char ifi_xmitquota;
 u_char ifi_unused1;
 u_int32_t ifi_mtu;
 u_int32_t ifi_metric;
 u_int32_t ifi_baudrate;

 u_int32_t ifi_ipackets;
 u_int32_t ifi_ierrors;
 u_int32_t ifi_opackets;
 u_int32_t ifi_oerrors;
 u_int32_t ifi_collisions;
 u_int32_t ifi_ibytes;
 u_int32_t ifi_obytes;
 u_int32_t ifi_imcasts;
 u_int32_t ifi_omcasts;
 u_int32_t ifi_iqdrops;
 u_int32_t ifi_noproto;
 u_int32_t ifi_recvtiming;
 u_int32_t ifi_xmittiming;
 struct timeval32 ifi_lastchange;
 u_int32_t ifi_unused2;
 u_int32_t ifi_hwassist;
 u_int32_t ifi_reserved1;
 u_int32_t ifi_reserved2;
};





struct if_data64 {

 u_char ifi_type;
 u_char ifi_typelen;
 u_char ifi_physical;
 u_char ifi_addrlen;
 u_char ifi_hdrlen;
 u_char ifi_recvquota;
 u_char ifi_xmitquota;
 u_char ifi_unused1;
 u_int32_t ifi_mtu;
 u_int32_t ifi_metric;
 u_int64_t ifi_baudrate;

 u_int64_t ifi_ipackets;
 u_int64_t ifi_ierrors;
 u_int64_t ifi_opackets;
 u_int64_t ifi_oerrors;
 u_int64_t ifi_collisions;
 u_int64_t ifi_ibytes;
 u_int64_t ifi_obytes;
 u_int64_t ifi_imcasts;
 u_int64_t ifi_omcasts;
 u_int64_t ifi_iqdrops;
 u_int64_t ifi_noproto;
 u_int32_t ifi_recvtiming;
 u_int32_t ifi_xmittiming;
 struct timeval32 ifi_lastchange;
};


#pragma pack()




struct ifqueue {
 void *ifq_head;
 void *ifq_tail;
 int ifq_len;
 int ifq_maxlen;
 int ifq_drops;
};
# 102 "/usr/include/net/if.h" 2 3 4
# 166 "/usr/include/net/if.h" 3 4
struct if_msghdr {
 unsigned short ifm_msglen;
 unsigned char ifm_version;
 unsigned char ifm_type;
 int ifm_addrs;
 int ifm_flags;
 unsigned short ifm_index;
 struct if_data ifm_data;
};





struct ifa_msghdr {
 unsigned short ifam_msglen;
 unsigned char ifam_version;
 unsigned char ifam_type;
 int ifam_addrs;
 int ifam_flags;
 unsigned short ifam_index;
 int ifam_metric;
};





struct ifma_msghdr {
 unsigned short ifmam_msglen;
 unsigned char ifmam_version;
 unsigned char ifmam_type;
 int ifmam_addrs;
 int ifmam_flags;
 unsigned short ifmam_index;
};





struct if_msghdr2 {
 u_short ifm_msglen;
 u_char ifm_version;
 u_char ifm_type;
 int ifm_addrs;
 int ifm_flags;
 u_short ifm_index;
 int ifm_snd_len;
 int ifm_snd_maxlen;
 int ifm_snd_drops;
 int ifm_timer;
 struct if_data64 ifm_data;
};





struct ifma_msghdr2 {
 u_short ifmam_msglen;
 u_char ifmam_version;
 u_char ifmam_type;
 int ifmam_addrs;
 int ifmam_flags;
 u_short ifmam_index;
 int32_t ifmam_refcount;
};






struct ifdevmtu {
 int ifdm_current;
 int ifdm_min;
 int ifdm_max;
};

#pragma pack(4)
# 273 "/usr/include/net/if.h" 3 4
struct ifkpi {
 unsigned int ifk_module_id;
 unsigned int ifk_type;
 union {
  void *ifk_ptr;
  int ifk_value;
 } ifk_data;
};





#pragma pack()







struct ifreq {



 char ifr_name[16];
 union {
  struct sockaddr ifru_addr;
  struct sockaddr ifru_dstaddr;
  struct sockaddr ifru_broadaddr;
  short ifru_flags;
  int ifru_metric;
  int ifru_mtu;
  int ifru_phys;
  int ifru_media;
  int ifru_intval;
  caddr_t ifru_data;
  struct ifdevmtu ifru_devmtu;
  struct ifkpi ifru_kpi;
  u_int32_t ifru_wake_flags;
  u_int32_t ifru_route_refcnt;
  int ifru_cap[2];
 } ifr_ifru;
# 337 "/usr/include/net/if.h" 3 4
};






struct ifaliasreq {
 char ifra_name[16];
 struct sockaddr ifra_addr;
 struct sockaddr ifra_broadaddr;
 struct sockaddr ifra_mask;
};

struct rslvmulti_req {
     struct sockaddr *sa;
     struct sockaddr **llsa;
};

#pragma pack(4)

struct ifmediareq {
 char ifm_name[16];
 int ifm_current;
 int ifm_mask;
 int ifm_status;
 int ifm_active;
 int ifm_count;
 int *ifm_ulist;
};

#pragma pack()



#pragma pack(4)
struct ifdrv {
 char ifd_name[16];
 unsigned long ifd_cmd;
 size_t ifd_len;
 void *ifd_data;
};
#pragma pack()
# 390 "/usr/include/net/if.h" 3 4
struct ifstat {
 char ifs_name[16];
 char ascii[800 + 1];
};







#pragma pack(4)
struct ifconf {
 int ifc_len;
 union {
  caddr_t ifcu_buf;
  struct ifreq *ifcu_req;
 } ifc_ifcu;
};
#pragma pack()







struct kev_dl_proto_data {
     struct net_event_data link_data;
     u_int32_t proto_family;
     u_int32_t proto_remaining_count;
};




struct if_laddrreq {
 char iflr_name[16];
 unsigned int flags;

 unsigned int prefixlen;
 struct sockaddr_storage addr;
 struct sockaddr_storage dstaddr;
};



struct if_nameindex {
 unsigned int if_index;
 char *if_name;
};


unsigned int if_nametoindex(const char *);
char *if_indextoname(unsigned int, char *);
struct if_nameindex *if_nameindex(void);
void if_freenameindex(struct if_nameindex *);

# 274 "socketmodule.c" 2




# 1 "socketmodule.h" 1
# 10 "socketmodule.h"
# 1 "/usr/include/netinet/in.h" 1 3 4
# 307 "/usr/include/netinet/in.h" 3 4
struct in_addr {
 in_addr_t s_addr;
};
# 380 "/usr/include/netinet/in.h" 3 4
struct sockaddr_in {
 __uint8_t sin_len;
 sa_family_t sin_family;
 in_port_t sin_port;
 struct in_addr sin_addr;
 char sin_zero[8];
};
# 398 "/usr/include/netinet/in.h" 3 4
struct ip_opts {
 struct in_addr ip_dst;
 char ip_opts[40];
};
# 506 "/usr/include/netinet/in.h" 3 4
struct ip_mreq {
 struct in_addr imr_multiaddr;
 struct in_addr imr_interface;
};






struct ip_mreqn {
 struct in_addr imr_multiaddr;
 struct in_addr imr_address;
 int imr_ifindex;
};

#pragma pack(4)



struct ip_mreq_source {
 struct in_addr imr_multiaddr;
 struct in_addr imr_sourceaddr;
 struct in_addr imr_interface;
};





struct group_req {
 uint32_t gr_interface;
 struct sockaddr_storage gr_group;
};

struct group_source_req {
 uint32_t gsr_interface;
 struct sockaddr_storage gsr_group;
 struct sockaddr_storage gsr_source;
};
# 554 "/usr/include/netinet/in.h" 3 4
struct __msfilterreq {
 uint32_t msfr_ifindex;
 uint32_t msfr_fmode;
 uint32_t msfr_nsrcs;
 uint32_t __msfr_align;
 struct sockaddr_storage msfr_group;
 struct sockaddr_storage *msfr_srcs;
};



#pragma pack()
struct sockaddr;






int setipv4sourcefilter(int, struct in_addr, struct in_addr, uint32_t,
     uint32_t, struct in_addr *) __attribute__((visibility("default")));
int getipv4sourcefilter(int, struct in_addr, struct in_addr, uint32_t *,
     uint32_t *, struct in_addr *) __attribute__((visibility("default")));
int setsourcefilter(int, uint32_t, struct sockaddr *, socklen_t,
     uint32_t, uint32_t, struct sockaddr_storage *) __attribute__((visibility("default")));
int getsourcefilter(int, uint32_t, struct sockaddr *, socklen_t,
     uint32_t *, uint32_t *, struct sockaddr_storage *) __attribute__((visibility("default")));
# 617 "/usr/include/netinet/in.h" 3 4
struct in_pktinfo {
 unsigned int ipi_ifindex;
 struct in_addr ipi_spec_dst;
 struct in_addr ipi_addr;
};
# 661 "/usr/include/netinet/in.h" 3 4
# 1 "/usr/include/netinet6/in6.h" 1 3 4
# 158 "/usr/include/netinet6/in6.h" 3 4
struct in6_addr {
 union {
  __uint8_t __u6_addr8[16];
  __uint16_t __u6_addr16[8];
  __uint32_t __u6_addr32[4];
 } __u6_addr;
};
# 176 "/usr/include/netinet6/in6.h" 3 4
struct sockaddr_in6 {
 __uint8_t sin6_len;
 sa_family_t sin6_family;
 in_port_t sin6_port;
 __uint32_t sin6_flowinfo;
 struct in6_addr sin6_addr;
 __uint32_t sin6_scope_id;
};
# 218 "/usr/include/netinet6/in6.h" 3 4
extern const struct in6_addr in6addr_any;
extern const struct in6_addr in6addr_loopback;

extern const struct in6_addr in6addr_nodelocal_allnodes;
extern const struct in6_addr in6addr_linklocal_allnodes;
extern const struct in6_addr in6addr_linklocal_allrouters;
extern const struct in6_addr in6addr_linklocal_allv2routers;
# 526 "/usr/include/netinet6/in6.h" 3 4
struct ipv6_mreq {
 struct in6_addr ipv6mr_multiaddr;
 unsigned int ipv6mr_interface;
};




struct in6_pktinfo {
 struct in6_addr ipi6_addr;
 unsigned int ipi6_ifindex;
};




struct ip6_mtuinfo {
 struct sockaddr_in6 ip6m_addr;
 uint32_t ip6m_mtu;
};
# 621 "/usr/include/netinet6/in6.h" 3 4

struct cmsghdr;

extern int inet6_option_space(int);
extern int inet6_option_init(void *, struct cmsghdr **, int);
extern int inet6_option_append(struct cmsghdr *, const __uint8_t *,
 int, int);
extern __uint8_t *inet6_option_alloc(struct cmsghdr *, int, int, int);
extern int inet6_option_next(const struct cmsghdr *, __uint8_t **);
extern int inet6_option_find(const struct cmsghdr *, __uint8_t **, int);

extern size_t inet6_rthdr_space(int, int);
extern struct cmsghdr *inet6_rthdr_init(void *, int);
extern int inet6_rthdr_add(struct cmsghdr *, const struct in6_addr *,
  unsigned int);
extern int inet6_rthdr_lasthop(struct cmsghdr *, unsigned int);



extern int inet6_rthdr_segments(const struct cmsghdr *);
extern struct in6_addr *inet6_rthdr_getaddr(struct cmsghdr *, int);
extern int inet6_rthdr_getflags(const struct cmsghdr *, int);

extern int inet6_opt_init(void *, socklen_t);
extern int inet6_opt_append(void *, socklen_t, int, __uint8_t,
     socklen_t, __uint8_t, void **);
extern int inet6_opt_finish(void *, socklen_t, int);
extern int inet6_opt_set_val(void *, int, void *, socklen_t);

extern int inet6_opt_next(void *, socklen_t, int, __uint8_t *,
          socklen_t *, void **);
extern int inet6_opt_find(void *, socklen_t, int, __uint8_t,
     socklen_t *, void **);
extern int inet6_opt_get_val(void *, int, void *, socklen_t);
extern socklen_t inet6_rth_space(int, int);
extern void *inet6_rth_init(void *, socklen_t, int, int);
extern int inet6_rth_add(void *, const struct in6_addr *);
extern int inet6_rth_reverse(const void *, void *);
extern int inet6_rth_segments(const void *);
extern struct in6_addr *inet6_rth_getaddr(const void *, int);
extern void addrsel_policy_init(void);

# 662 "/usr/include/netinet/in.h" 2 3 4





int bindresvport(int, struct sockaddr_in *);
struct sockaddr;
int bindresvport_sa(int, struct sockaddr *);

# 11 "socketmodule.h" 2

# 1 "/usr/include/netinet/tcp.h" 1 3 4
# 71 "/usr/include/netinet/tcp.h" 3 4
typedef __uint32_t tcp_seq;
typedef __uint32_t tcp_cc;
# 81 "/usr/include/netinet/tcp.h" 3 4
struct tcphdr {
 unsigned short th_sport;
 unsigned short th_dport;
 tcp_seq th_seq;
 tcp_seq th_ack;

 unsigned int th_x2:4,
   th_off:4;





 unsigned char th_flags;
# 105 "/usr/include/netinet/tcp.h" 3 4
 unsigned short th_win;
 unsigned short th_sum;
 unsigned short th_urp;
};
# 13 "socketmodule.h" 2
# 36 "socketmodule.h"
# 1 "/usr/include/sys/un.h" 1 3 4
# 79 "/usr/include/sys/un.h" 3 4
struct sockaddr_un {
 unsigned char sun_len;
 sa_family_t sun_family;
 char sun_path[104];
};
# 37 "socketmodule.h" 2
# 84 "socketmodule.h"
# 1 "/usr/include/sys/sys_domain.h" 1 3 4
# 47 "/usr/include/sys/sys_domain.h" 3 4
struct sockaddr_sys
{
 u_char ss_len;
 u_char ss_family;
 u_int16_t ss_sysaddr;
 u_int32_t ss_reserved[7];
};
# 85 "socketmodule.h" 2


# 1 "/usr/include/sys/kern_control.h" 1 3 4
# 72 "/usr/include/sys/kern_control.h" 3 4
struct ctl_event_data {
    u_int32_t ctl_id;
    u_int32_t ctl_unit;
};
# 114 "/usr/include/sys/kern_control.h" 3 4
struct ctl_info {
    u_int32_t ctl_id;
    char ctl_name[96];
};
# 137 "/usr/include/sys/kern_control.h" 3 4
struct sockaddr_ctl {
    u_char sc_len;
    u_char sc_family;
    u_int16_t ss_sysaddr;
    u_int32_t sc_id;
    u_int32_t sc_unit;
    u_int32_t sc_reserved[5];
};
# 88 "socketmodule.h" 2
# 110 "socketmodule.h"
typedef int SOCKET_T;
# 123 "socketmodule.h"
typedef union sock_addr {
    struct sockaddr_in in;
    struct sockaddr sa;

    struct sockaddr_un un;





    struct sockaddr_in6 in6;
    struct sockaddr_storage storage;
# 149 "socketmodule.h"
    struct sockaddr_ctl ctl;

} sock_addr_t;





typedef struct {
    PyObject ob_base;
    SOCKET_T sock_fd;
    int sock_family;
    int sock_type;
    int sock_proto;
    PyObject *(*errorhandler)(void);


    double sock_timeout;

} PySocketSockObject;
# 221 "socketmodule.h"
typedef struct {
    PyTypeObject *Sock_Type;
    PyObject *error;
    PyObject *timeout_error;
} PySocketModule_APIObject;
# 279 "socketmodule.c" 2






# 1 "/usr/include/netdb.h" 1 3 4
# 108 "/usr/include/netdb.h" 3 4
extern int h_errno;
# 119 "/usr/include/netdb.h" 3 4
struct hostent {
 char *h_name;
 char **h_aliases;
 int h_addrtype;
 int h_length;
 char **h_addr_list;



};





struct netent {
 char *n_name;
 char **n_aliases;
 int n_addrtype;
 uint32_t n_net;
};

struct servent {
 char *s_name;
 char **s_aliases;
 int s_port;
 char *s_proto;
};

struct protoent {
 char *p_name;
 char **p_aliases;
 int p_proto;
};

struct addrinfo {
 int ai_flags;
 int ai_family;
 int ai_socktype;
 int ai_protocol;
 socklen_t ai_addrlen;
 char *ai_canonname;
 struct sockaddr *ai_addr;
 struct addrinfo *ai_next;
};


struct rpcent {
        char *r_name;
        char **r_aliases;
        int r_number;
};
# 264 "/usr/include/netdb.h" 3 4


void endhostent(void);
void endnetent(void);
void endprotoent(void);
void endservent(void);

void freeaddrinfo(struct addrinfo *);
const char *gai_strerror(int);
int getaddrinfo(const char * , const char * ,
       const struct addrinfo * ,
       struct addrinfo ** );
struct hostent *gethostbyaddr(const void *, socklen_t, int);
struct hostent *gethostbyname(const char *);
struct hostent *gethostent(void);
int getnameinfo(const struct sockaddr * , socklen_t,
         char * , socklen_t, char * ,
         socklen_t, int);
struct netent *getnetbyaddr(uint32_t, int);
struct netent *getnetbyname(const char *);
struct netent *getnetent(void);
struct protoent *getprotobyname(const char *);
struct protoent *getprotobynumber(int);
struct protoent *getprotoent(void);
struct servent *getservbyname(const char *, const char *);
struct servent *getservbyport(int, const char *);
struct servent *getservent(void);
void sethostent(int);

void setnetent(int);
void setprotoent(int);
void setservent(int);


void freehostent(struct hostent *);
struct hostent *gethostbyname2(const char *, int);
struct hostent *getipnodebyaddr(const void *, size_t, int, int *);
struct hostent *getipnodebyname(const char *, int, int, int *);
struct rpcent *getrpcbyname(const char *name);

struct rpcent *getrpcbynumber(int number);



struct rpcent *getrpcent(void);
void setrpcent(int stayopen);
void endrpcent(void);
void herror(const char *);
const char *hstrerror(int);
int innetgr(const char *, const char *, const char *, const char *);
int getnetgrent(char **, char **, char **);
void endnetgrent(void);
void setnetgrent(const char *);



# 286 "socketmodule.c" 2







# 1 "/usr/include/arpa/inet.h" 1 3 4
# 95 "/usr/include/arpa/inet.h" 3 4


in_addr_t inet_addr(const char *);
char *inet_ntoa(struct in_addr);
const char *inet_ntop(int, const void *, char *, socklen_t);
int inet_pton(int, const char *, void *);

int ascii2addr(int, const char *, void *);
char *addr2ascii(int, const void *, int, char *);
int inet_aton(const char *, struct in_addr *);
in_addr_t inet_lnaof(struct in_addr);
struct in_addr inet_makeaddr(in_addr_t, in_addr_t);
in_addr_t inet_netof(struct in_addr);
in_addr_t inet_network(const char *);
char *inet_net_ntop(int, const void *, int, char *, __darwin_size_t);
int inet_net_pton(int, const char *, void *, __darwin_size_t);
char *inet_neta(in_addr_t, char *, __darwin_size_t);
unsigned int inet_nsap_addr(const char *, unsigned char *, int maxlen);
char *inet_nsap_ntoa(int, const unsigned char *, char *ascii);



# 294 "socketmodule.c" 2


# 1 "/usr/include/fcntl.h" 1 3 4
# 23 "/usr/include/fcntl.h" 3 4
# 1 "/usr/include/sys/fcntl.h" 1 3 4
# 339 "/usr/include/sys/fcntl.h" 3 4
struct flock {
 off_t l_start;
 off_t l_len;
 pid_t l_pid;
 short l_type;
 short l_whence;
};
# 355 "/usr/include/sys/fcntl.h" 3 4
struct radvisory {
       off_t ra_offset;
       int ra_count;
};
# 367 "/usr/include/sys/fcntl.h" 3 4
typedef struct fsignatures {
 off_t fs_file_start;
 void *fs_blob_start;
 size_t fs_blob_size;
} fsignatures_t;
# 381 "/usr/include/sys/fcntl.h" 3 4
typedef struct fstore {
 unsigned int fst_flags;
 int fst_posmode;
 off_t fst_offset;
 off_t fst_length;
 off_t fst_bytesalloc;
} fstore_t;



typedef struct fbootstraptransfer {
  off_t fbt_offset;
  size_t fbt_length;
  void *fbt_buffer;
} fbootstraptransfer_t;
# 419 "/usr/include/sys/fcntl.h" 3 4
#pragma pack(4)

struct log2phys {
 unsigned int l2p_flags;
 off_t l2p_contigbytes;


 off_t l2p_devoffset;


};

#pragma pack()
# 446 "/usr/include/sys/fcntl.h" 3 4
typedef enum {
 FILESEC_OWNER = 1,
 FILESEC_GROUP = 2,
 FILESEC_UUID = 3,
 FILESEC_MODE = 4,
 FILESEC_ACL = 5,
 FILESEC_GRPUUID = 6,


 FILESEC_ACL_RAW = 100,
 FILESEC_ACL_ALLOCSIZE = 101
} filesec_property_t;






int open(const char *, int, ...) __asm("_" "open" );
int creat(const char *, mode_t) __asm("_" "creat" );
int fcntl(int, int, ...) __asm("_" "fcntl" );


int openx_np(const char *, int, filesec_t);
int flock(int, int);
filesec_t filesec_init(void);
filesec_t filesec_dup(filesec_t);
void filesec_free(filesec_t);
int filesec_get_property(filesec_t, filesec_property_t, void *);
int filesec_query_property(filesec_t, filesec_property_t, int *);
int filesec_set_property(filesec_t, filesec_property_t, const void *);
int filesec_unset_property(filesec_t, filesec_property_t) __attribute__((visibility("default")));




# 23 "/usr/include/fcntl.h" 2 3 4
# 297 "socketmodule.c" 2
# 307 "socketmodule.c"
# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stddef.h" 1 3 4
# 308 "socketmodule.c" 2
# 328 "socketmodule.c"
# 1 "addrinfo.h" 1
# 173 "addrinfo.h"
extern void freehostent(struct hostent *);
# 329 "socketmodule.c" 2
# 467 "socketmodule.c"
static PyObject *socket_herror;
static PyObject *socket_gaierror;
static PyObject *socket_timeout;





static PyTypeObject sock_type;


# 1 "/usr/include/poll.h" 1 3 4
# 23 "/usr/include/poll.h" 3 4
# 1 "/usr/include/sys/poll.h" 1 3 4
# 96 "/usr/include/sys/poll.h" 3 4
struct pollfd
{
 int fd;
 short events;
 short revents;
};

typedef unsigned int nfds_t;










extern int poll (struct pollfd *, nfds_t, int) __asm("_" "poll" );


# 24 "/usr/include/poll.h" 2 3 4
# 479 "socketmodule.c" 2
# 504 "socketmodule.c"
static PyObject*
select_error(void)
{
    PyErr_SetString(PyExc_OSError, "unable to select on socket");
    return ((void *)0);
}
# 525 "socketmodule.c"
static PyObject *
set_error(void)
{
# 573 "socketmodule.c"
    return PyErr_SetFromErrno(PyExc_OSError);
}


static PyObject *
set_herror(int h_error)
{
    PyObject *v;


    v = Py_BuildValue("(is)", h_error, (char *)hstrerror(h_error));



    if (v != ((void *)0)) {
        PyErr_SetObject(socket_herror, v);
        do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
    }

    return ((void *)0);
}


static PyObject *
set_gaierror(int error)
{
    PyObject *v;



    if (error == 11)
        return set_error();



    v = Py_BuildValue("(is)", error, gai_strerror(error));



    if (v != ((void *)0)) {
        PyErr_SetObject(socket_gaierror, v);
        do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
    }

    return ((void *)0);
}
# 646 "socketmodule.c"
static int
internal_setblocking(PySocketSockObject *s, int block)
{

    int delay_flag;
# 659 "socketmodule.c"
    { PyThreadState *_save; _save = PyEval_SaveThread();
# 668 "socketmodule.c"
    delay_flag = fcntl(s->sock_fd, 3, 0);
    if (block)
        delay_flag &= (~0x0004);
    else
        delay_flag |= 0x0004;
    fcntl(s->sock_fd, 4, delay_flag);





    PyEval_RestoreThread(_save); }


    return 1;
}






static int
internal_select_ex(PySocketSockObject *s, int writing, double interval)
{
    int n;


    if (s->sock_timeout <= 0.0)
        return 0;


    if (s->sock_fd < 0)
        return 0;


    if (interval < 0.0)
        return 1;




    {
        struct pollfd pollfd;
        int timeout;

        pollfd.fd = s->sock_fd;
        pollfd.events = writing ? 0x0004 : 0x0001;


        timeout = (int)(interval * 1000 + 0.5);
        n = poll(&pollfd, 1, timeout);
    }
# 741 "socketmodule.c"
    if (n < 0)
        return -1;
    if (n == 0)
        return 1;
    return 0;
}

static int
internal_select(PySocketSockObject *s, int writing)
{
    return internal_select_ex(s, writing, s->sock_timeout);
}
# 797 "socketmodule.c"
static double defaulttimeout = -1.0;

static void
init_sockobject(PySocketSockObject *s,
                SOCKET_T fd, int family, int type, int proto)
{
    s->sock_fd = fd;
    s->sock_family = family;
    s->sock_type = type;
    s->sock_proto = proto;

    s->errorhandler = &set_error;





    {
        s->sock_timeout = defaulttimeout;
        if (defaulttimeout >= 0.0)
            internal_setblocking(s, 0);
    }

}







static PySocketSockObject *
new_sockobject(SOCKET_T fd, int family, int type, int proto)
{
    PySocketSockObject *s;
    s = (PySocketSockObject *)
        PyType_GenericNew(&sock_type, ((void *)0), ((void *)0));
    if (s != ((void *)0))
        init_sockobject(s, fd, family, type, proto);
    return s;
}





static PyThread_type_lock netdb_lock;
# 853 "socketmodule.c"
static int
setipaddr(char *name, struct sockaddr *addr_ret, size_t addr_ret_size, int af)
{
    struct addrinfo hints, *res;
    int error;
    int d1, d2, d3, d4;
    char ch;

    ((__builtin_object_size ((void *) addr_ret, 0) != (size_t) -1) ? __builtin___memset_chk ((void *) addr_ret, '\0', sizeof(*addr_ret), __builtin_object_size ((void *) addr_ret, 0)) : __inline_memset_chk ((void *) addr_ret, '\0', sizeof(*addr_ret)));
    if (name[0] == '\0') {
        int siz;
        ((__builtin_object_size (&hints, 0) != (size_t) -1) ? __builtin___memset_chk (&hints, 0, sizeof(hints), __builtin_object_size (&hints, 0)) : __inline_memset_chk (&hints, 0, sizeof(hints)));
        hints.ai_family = af;
        hints.ai_socktype = 2;
        hints.ai_flags = 0x00000001;
        { PyThreadState *_save; _save = PyEval_SaveThread();
        PyThread_acquire_lock(netdb_lock, 1);
        error = getaddrinfo(((void *)0), "0", &hints, &res);
        PyEval_RestoreThread(_save); }




        PyThread_release_lock(netdb_lock);
        if (error) {
            set_gaierror(error);
            return -1;
        }
        switch (res->ai_family) {
        case 2:
            siz = 4;
            break;

        case 30:
            siz = 16;
            break;

        default:
            freeaddrinfo(res);
            PyErr_SetString(PyExc_OSError,
                "unsupported address family");
            return -1;
        }
        if (res->ai_next) {
            freeaddrinfo(res);
            PyErr_SetString(PyExc_OSError,
                "wildcard resolved to multiple address");
            return -1;
        }
        if (res->ai_addrlen < addr_ret_size)
            addr_ret_size = res->ai_addrlen;
        ((__builtin_object_size (addr_ret, 0) != (size_t) -1) ? __builtin___memcpy_chk (addr_ret, res->ai_addr, addr_ret_size, __builtin_object_size (addr_ret, 0)) : __inline_memcpy_chk (addr_ret, res->ai_addr, addr_ret_size));
        freeaddrinfo(res);
        return siz;
    }
    if (name[0] == '<' && strcmp(name, "<broadcast>") == 0) {
        struct sockaddr_in *sin;
        if (af != 2 && af != 0) {
            PyErr_SetString(PyExc_OSError,
                "address family mismatched");
            return -1;
        }
        sin = (struct sockaddr_in *)addr_ret;
        ((__builtin_object_size ((void *) sin, 0) != (size_t) -1) ? __builtin___memset_chk ((void *) sin, '\0', sizeof(*sin), __builtin_object_size ((void *) sin, 0)) : __inline_memset_chk ((void *) sin, '\0', sizeof(*sin)));
        sin->sin_family = 2;

        sin->sin_len = sizeof(*sin);

        sin->sin_addr.s_addr = (u_int32_t)0xffffffff;
        return sizeof(sin->sin_addr);
    }
    if (sscanf(name, "%d.%d.%d.%d%c", &d1, &d2, &d3, &d4, &ch) == 4 &&
        0 <= d1 && d1 <= 255 && 0 <= d2 && d2 <= 255 &&
        0 <= d3 && d3 <= 255 && 0 <= d4 && d4 <= 255) {
        struct sockaddr_in *sin;
        sin = (struct sockaddr_in *)addr_ret;
        sin->sin_addr.s_addr = (__builtin_constant_p(((long) d1 << 24) | ((long) d2 << 16) | ((long) d3 << 8) | ((long) d4 << 0)) ? ((__uint32_t)((((__uint32_t)(((long) d1 << 24) | ((long) d2 << 16) | ((long) d3 << 8) | ((long) d4 << 0)) & 0xff000000) >> 24) | (((__uint32_t)(((long) d1 << 24) | ((long) d2 << 16) | ((long) d3 << 8) | ((long) d4 << 0)) & 0x00ff0000) >> 8) | (((__uint32_t)(((long) d1 << 24) | ((long) d2 << 16) | ((long) d3 << 8) | ((long) d4 << 0)) & 0x0000ff00) << 8) | (((__uint32_t)(((long) d1 << 24) | ((long) d2 << 16) | ((long) d3 << 8) | ((long) d4 << 0)) & 0x000000ff) << 24))) : _OSSwapInt32(((long) d1 << 24) | ((long) d2 << 16) | ((long) d3 << 8) | ((long) d4 << 0)));


        sin->sin_family = 2;

        sin->sin_len = sizeof(*sin);

        return 4;
    }
    ((__builtin_object_size (&hints, 0) != (size_t) -1) ? __builtin___memset_chk (&hints, 0, sizeof(hints), __builtin_object_size (&hints, 0)) : __inline_memset_chk (&hints, 0, sizeof(hints)));
    hints.ai_family = af;
    { PyThreadState *_save; _save = PyEval_SaveThread();
    PyThread_acquire_lock(netdb_lock, 1);
    error = getaddrinfo(name, ((void *)0), &hints, &res);
# 951 "socketmodule.c"
    PyEval_RestoreThread(_save); }
    PyThread_release_lock(netdb_lock);
    if (error) {
        set_gaierror(error);
        return -1;
    }
    if (res->ai_addrlen < addr_ret_size)
        addr_ret_size = res->ai_addrlen;
    ((__builtin_object_size ((char *) addr_ret, 0) != (size_t) -1) ? __builtin___memcpy_chk ((char *) addr_ret, res->ai_addr, addr_ret_size, __builtin_object_size ((char *) addr_ret, 0)) : __inline_memcpy_chk ((char *) addr_ret, res->ai_addr, addr_ret_size));
    freeaddrinfo(res);
    switch (addr_ret->sa_family) {
    case 2:
        return 4;

    case 30:
        return 16;

    default:
        PyErr_SetString(PyExc_OSError, "unknown address family");
        return -1;
    }
}






static PyObject *
makeipaddr(struct sockaddr *addr, int addrlen)
{
    char buf[1025];
    int error;

    error = getnameinfo(addr, addrlen, buf, sizeof(buf), ((void *)0), 0,
        0x00000002);
    if (error) {
        set_gaierror(error);
        return ((void *)0);
    }
    return PyUnicode_FromString(buf);
}
# 1046 "socketmodule.c"
static PyObject *
makesockaddr(SOCKET_T sockfd, struct sockaddr *addr, size_t addrlen, int proto)
{
    if (addrlen == 0) {

        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        return (&_Py_NoneStruct);
    }

    switch (addr->sa_family) {

    case 2:
    {
        struct sockaddr_in *a;
        PyObject *addrobj = makeipaddr(addr, sizeof(*a));
        PyObject *ret = ((void *)0);
        if (addrobj) {
            a = (struct sockaddr_in *)addr;
            ret = Py_BuildValue("Oi", addrobj, ((__uint16_t)(__builtin_constant_p(a->sin_port) ? ((__uint16_t)((((__uint16_t)(a->sin_port) & 0xff00) >> 8) | (((__uint16_t)(a->sin_port) & 0x00ff) << 8))) : _OSSwapInt16(a->sin_port))));
            do { if ( --((PyObject*)(addrobj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(addrobj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(addrobj)))); } while (0);
        }
        return ret;
    }


    case 1:
    {
        struct sockaddr_un *a = (struct sockaddr_un *) addr;







        {

            return PyUnicode_DecodeFSDefault(a->sun_path);
        }
    }
# 1097 "socketmodule.c"
    case 30:
    {
        struct sockaddr_in6 *a;
        PyObject *addrobj = makeipaddr(addr, sizeof(*a));
        PyObject *ret = ((void *)0);
        if (addrobj) {
            a = (struct sockaddr_in6 *)addr;
            ret = Py_BuildValue("OiII",
                                addrobj,
                                ((__uint16_t)(__builtin_constant_p(a->sin6_port) ? ((__uint16_t)((((__uint16_t)(a->sin6_port) & 0xff00) >> 8) | (((__uint16_t)(a->sin6_port) & 0x00ff) << 8))) : _OSSwapInt16(a->sin6_port))),
                                (__builtin_constant_p(a->sin6_flowinfo) ? ((__uint32_t)((((__uint32_t)(a->sin6_flowinfo) & 0xff000000) >> 24) | (((__uint32_t)(a->sin6_flowinfo) & 0x00ff0000) >> 8) | (((__uint32_t)(a->sin6_flowinfo) & 0x0000ff00) << 8) | (((__uint32_t)(a->sin6_flowinfo) & 0x000000ff) << 24))) : _OSSwapInt32(a->sin6_flowinfo)),
                                a->sin6_scope_id);
            do { if ( --((PyObject*)(addrobj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(addrobj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(addrobj)))); } while (0);
        }
        return ret;
    }
# 1249 "socketmodule.c"
    case 32:
        switch(proto) {

        case 2:
        {
            struct sockaddr_ctl *a = (struct sockaddr_ctl *)addr;
            return Py_BuildValue("(II)", a->sc_id, a->sc_unit);
        }

        default:
            PyErr_SetString(PyExc_ValueError,
                            "Invalid address type");
            return 0;
        }




    default:


        return Py_BuildValue("iy#",
                             addr->sa_family,
                             addr->sa_data,
                             sizeof(addr->sa_data));

    }
}







static int
getsockaddrarg(PySocketSockObject *s, PyObject *args,
               struct sockaddr *addr_ret, int *len_ret)
{
    switch (s->sock_family) {


    case 1:
    {
        struct sockaddr_un* addr;
        char *path;
        int len;
        int retval = 0;



        if (((((((PyObject*)(args))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
            if ((args = PyUnicode_EncodeFSDefault(args)) == ((void *)0))
                return 0;
        }
        else
            ( ((PyObject*)(args))->ob_refcnt++);
        if (!PyArg_Parse(args, "y#", &path, &len))
            goto unix_out;

        addr = (struct sockaddr_un*)addr_ret;
# 1321 "socketmodule.c"
        {

            if (len >= sizeof addr->sun_path) {
                PyErr_SetString(PyExc_OSError,
                                "AF_UNIX path too long");
                goto unix_out;
            }
            addr->sun_path[len] = 0;
        }
        addr->sun_family = s->sock_family;
        ((__builtin_object_size (addr->sun_path, 0) != (size_t) -1) ? __builtin___memcpy_chk (addr->sun_path, path, len, __builtin_object_size (addr->sun_path, 0)) : __inline_memcpy_chk (addr->sun_path, path, len));



        *len_ret = len + __builtin_offsetof (struct sockaddr_un, sun_path);

        retval = 1;
    unix_out:
        do { if ( --((PyObject*)(args))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(args)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(args)))); } while (0);
        return retval;
    }
# 1373 "socketmodule.c"
    case 2:
    {
        struct sockaddr_in* addr;
        char *host;
        int port, result;
        if (!((((((PyObject*)(args))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
            PyErr_Format(
                PyExc_TypeError,
                "getsockaddrarg: "
                "AF_INET address must be tuple, not %.500s",
                (((PyObject*)(args))->ob_type)->tp_name);
            return 0;
        }
        if (!PyArg_ParseTuple(args, "eti:getsockaddrarg",
                              "idna", &host, &port))
            return 0;
        addr=(struct sockaddr_in*)addr_ret;
        result = setipaddr(host, (struct sockaddr *)addr,
                           sizeof(*addr), 2);
        PyMem_Free(host);
        if (result < 0)
            return 0;
        if (port < 0 || port > 0xffff) {
            PyErr_SetString(
                PyExc_OverflowError,
                "getsockaddrarg: port must be 0-65535.");
            return 0;
        }
        addr->sin_family = 2;
        addr->sin_port = ((__uint16_t)(__builtin_constant_p((short)port) ? ((__uint16_t)((((__uint16_t)((short)port) & 0xff00) >> 8) | (((__uint16_t)((short)port) & 0x00ff) << 8))) : _OSSwapInt16((short)port)));
        *len_ret = sizeof *addr;
        return 1;
    }


    case 30:
    {
        struct sockaddr_in6* addr;
        char *host;
        int port, result;
        unsigned int flowinfo, scope_id;
        flowinfo = scope_id = 0;
        if (!((((((PyObject*)(args))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
            PyErr_Format(
                PyExc_TypeError,
                "getsockaddrarg: "
                "AF_INET6 address must be tuple, not %.500s",
                (((PyObject*)(args))->ob_type)->tp_name);
            return 0;
        }
        if (!PyArg_ParseTuple(args, "eti|II",
                              "idna", &host, &port, &flowinfo,
                              &scope_id)) {
            return 0;
        }
        addr = (struct sockaddr_in6*)addr_ret;
        result = setipaddr(host, (struct sockaddr *)addr,
                           sizeof(*addr), 30);
        PyMem_Free(host);
        if (result < 0)
            return 0;
        if (port < 0 || port > 0xffff) {
            PyErr_SetString(
                PyExc_OverflowError,
                "getsockaddrarg: port must be 0-65535.");
            return 0;
        }
        if (flowinfo > 0xfffff) {
            PyErr_SetString(
                PyExc_OverflowError,
                "getsockaddrarg: flowinfo must be 0-1048575.");
            return 0;
        }
        addr->sin6_family = s->sock_family;
        addr->sin6_port = ((__uint16_t)(__builtin_constant_p((short)port) ? ((__uint16_t)((((__uint16_t)((short)port) & 0xff00) >> 8) | (((__uint16_t)((short)port) & 0x00ff) << 8))) : _OSSwapInt16((short)port)));
        addr->sin6_flowinfo = (__builtin_constant_p(flowinfo) ? ((__uint32_t)((((__uint32_t)(flowinfo) & 0xff000000) >> 24) | (((__uint32_t)(flowinfo) & 0x00ff0000) >> 8) | (((__uint32_t)(flowinfo) & 0x0000ff00) << 8) | (((__uint32_t)(flowinfo) & 0x000000ff) << 24))) : _OSSwapInt32(flowinfo));
        addr->sin6_scope_id = scope_id;
        *len_ret = sizeof *addr;
        return 1;
    }
# 1706 "socketmodule.c"
    case 32:
        switch (s->sock_proto) {

        case 2:
        {
            struct sockaddr_ctl *addr;

            addr = (struct sockaddr_ctl *)addr_ret;
            addr->sc_family = 32;
            addr->ss_sysaddr = 2;

            if (((((((PyObject*)(args))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
                struct ctl_info info;
                PyObject *ctl_name;

                if (!PyArg_Parse(args, "O&",
                                PyUnicode_FSConverter, &ctl_name)) {
                    return 0;
                }

                if (((__builtin_expect(!(((((((PyObject*)(ctl_name))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "socketmodule.c", 1726, "PyBytes_Check(ctl_name)") : (void)0),(((PyVarObject*)(ctl_name))->ob_size)) > sizeof(info.ctl_name)) {
                    PyErr_SetString(PyExc_ValueError,
                                    "provided string is too long");
                    do { if ( --((PyObject*)(ctl_name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(ctl_name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(ctl_name)))); } while (0);
                    return 0;
                }
                ((__builtin_object_size (info.ctl_name, 0) != (size_t) -1) ? __builtin___strncpy_chk (info.ctl_name, ((__builtin_expect(!(((((((PyObject*)(ctl_name))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "socketmodule.c", 1733, "PyBytes_Check(ctl_name)") : (void)0), (((PyBytesObject *)(ctl_name))->ob_sval)), sizeof(info.ctl_name), __builtin_object_size (info.ctl_name, 2 > 1)) : __inline_strncpy_chk (info.ctl_name, ((__builtin_expect(!(((((((PyObject*)(ctl_name))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "socketmodule.c", 1733, "PyBytes_Check(ctl_name)") : (void)0), (((PyBytesObject *)(ctl_name))->ob_sval)), sizeof(info.ctl_name)));

                do { if ( --((PyObject*)(ctl_name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(ctl_name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(ctl_name)))); } while (0);

                if (ioctl(s->sock_fd, (((__uint32_t)0x80000000|(__uint32_t)0x40000000) | ((sizeof(struct ctl_info) & 0x1fff) << 16) | ((('N')) << 8) | ((3))), &info)) {
                    PyErr_SetString(PyExc_OSError,
                          "cannot find kernel control with provided name");
                    return 0;
                }

                addr->sc_id = info.ctl_id;
                addr->sc_unit = 0;
            } else if (!PyArg_ParseTuple(args, "II",
                                         &(addr->sc_id), &(addr->sc_unit))) {
                PyErr_SetString(PyExc_TypeError, "getsockaddrarg: "
                                "expected str or tuple of two ints");

                return 0;
            }

            *len_ret = sizeof(*addr);
            return 1;
        }

        default:
            PyErr_SetString(PyExc_OSError,
                            "getsockaddrarg: unsupported PF_SYSTEM protocol");
            return 0;
        }




    default:
        PyErr_SetString(PyExc_OSError, "getsockaddrarg: bad family");
        return 0;

    }
}






static int
getsockaddrlen(PySocketSockObject *s, socklen_t *len_ret)
{
    switch (s->sock_family) {


    case 1:
    {
        *len_ret = sizeof (struct sockaddr_un);
        return 1;
    }
# 1802 "socketmodule.c"
    case 2:
    {
        *len_ret = sizeof (struct sockaddr_in);
        return 1;
    }


    case 30:
    {
        *len_ret = sizeof (struct sockaddr_in6);
        return 1;
    }
# 1870 "socketmodule.c"
    case 32:
        switch(s->sock_proto) {

        case 2:
            *len_ret = sizeof (struct sockaddr_ctl);
            return 1;

        default:
            PyErr_SetString(PyExc_OSError, "getsockaddrlen: "
                            "unknown PF_SYSTEM protocol");
            return 0;
        }




    default:
        PyErr_SetString(PyExc_OSError, "getsockaddrlen: bad family");
        return 0;

    }
}
# 1905 "socketmodule.c"
static int
get_CMSG_LEN(size_t length, size_t *result)
{
    size_t tmp;

    if (length > (2147483647 - (((__darwin_size_t)((char *)(__darwin_size_t)(sizeof(struct cmsghdr)) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1)) + (0))))
        return 0;
    tmp = (((__darwin_size_t)((char *)(__darwin_size_t)(sizeof(struct cmsghdr)) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1)) + (length));
    if (tmp > 2147483647 || tmp < length)
        return 0;
    *result = tmp;
    return 1;
}




static int
get_CMSG_SPACE(size_t length, size_t *result)
{
    size_t tmp;



    if (length > (2147483647 - (((__darwin_size_t)((char *)(__darwin_size_t)(sizeof(struct cmsghdr)) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1)) + ((__darwin_size_t)((char *)(__darwin_size_t)(1) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1)))))
        return 0;
    tmp = (((__darwin_size_t)((char *)(__darwin_size_t)(sizeof(struct cmsghdr)) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1)) + ((__darwin_size_t)((char *)(__darwin_size_t)(length) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1)));
    if (tmp > 2147483647 || tmp < length)
        return 0;
    *result = tmp;
    return 1;
}





static int
cmsg_min_space(struct msghdr *msg, struct cmsghdr *cmsgh, size_t space)
{
    size_t cmsg_offset;
    static const size_t cmsg_len_end = (__builtin_offsetof (struct cmsghdr, cmsg_len) +
                                        sizeof(cmsgh->cmsg_len));


    if (cmsgh == ((void *)0) || msg->msg_control == ((void *)0) || msg->msg_controllen < 0)
        return 0;
    if (space < cmsg_len_end)
        space = cmsg_len_end;
    cmsg_offset = (char *)cmsgh - (char *)msg->msg_control;
    return (cmsg_offset <= (size_t)-1 - space &&
            cmsg_offset + space <= msg->msg_controllen);
}





static int
get_cmsg_data_space(struct msghdr *msg, struct cmsghdr *cmsgh, size_t *space)
{
    size_t data_offset;
    char *data_ptr;

    if ((data_ptr = (char *)((unsigned char *)(cmsgh) + ((__darwin_size_t)((char *)(__darwin_size_t)(sizeof(struct cmsghdr)) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1)))) == ((void *)0))
        return 0;
    data_offset = data_ptr - (char *)msg->msg_control;
    if (data_offset > msg->msg_controllen)
        return 0;
    *space = msg->msg_controllen - data_offset;
    return 1;
}
# 1985 "socketmodule.c"
static int
get_cmsg_data_len(struct msghdr *msg, struct cmsghdr *cmsgh, size_t *data_len)
{
    size_t space, cmsg_data_len;

    if (!cmsg_min_space(msg, cmsgh, (((__darwin_size_t)((char *)(__darwin_size_t)(sizeof(struct cmsghdr)) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1)) + (0))) ||
        cmsgh->cmsg_len < (((__darwin_size_t)((char *)(__darwin_size_t)(sizeof(struct cmsghdr)) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1)) + (0)))
        return -1;
    cmsg_data_len = cmsgh->cmsg_len - (((__darwin_size_t)((char *)(__darwin_size_t)(sizeof(struct cmsghdr)) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1)) + (0));
    if (!get_cmsg_data_space(msg, cmsgh, &space))
        return -1;
    if (space >= cmsg_data_len) {
        *data_len = cmsg_data_len;
        return 0;
    }
    *data_len = space;
    return 1;
}





static PyObject *
sock_accept(PySocketSockObject *s)
{
    sock_addr_t addrbuf;
    SOCKET_T newfd = (-1);
    socklen_t addrlen;
    PyObject *sock = ((void *)0);
    PyObject *addr = ((void *)0);
    PyObject *res = ((void *)0);
    int timeout;
    if (!getsockaddrlen(s, &addrlen))
        return ((void *)0);
    ((__builtin_object_size (&addrbuf, 0) != (size_t) -1) ? __builtin___memset_chk (&addrbuf, 0, addrlen, __builtin_object_size (&addrbuf, 0)) : __inline_memset_chk (&addrbuf, 0, addrlen));

    if (!1)
        return select_error();

    { _PyTime_timeval now, deadline = {0, 0}; double interval = s->sock_timeout; int has_timeout = s->sock_timeout > 0.0; if (has_timeout) { _PyTime_gettimeofday(&now); deadline = now; do { deadline.tv_usec += (long) (((long) s->sock_timeout - s->sock_timeout) * 1000000); deadline.tv_sec += (time_t) s->sock_timeout + (time_t) (deadline.tv_usec / 1000000); deadline.tv_usec %= 1000000; } while (0); } while (1) { (*__error()) = 0;
    { PyThreadState *_save; _save = PyEval_SaveThread();
    timeout = internal_select_ex(s, 0, interval);
    if (!timeout) {
        newfd = accept(s->sock_fd, (&((&addrbuf)->sa)), &addrlen);
    }
    PyEval_RestoreThread(_save); }

    if (timeout == 1) {
        PyErr_SetString(socket_timeout, "timed out");
        return ((void *)0);
    }
    if (!has_timeout || (!((*__error()) == 35) && !((*__error()) == 35))) break; _PyTime_gettimeofday(&now); interval = ((deadline.tv_sec - now.tv_sec) + (deadline.tv_usec - now.tv_usec) * 0.000001); } }

    if (newfd == (-1))
        return s->errorhandler();

    sock = PyLong_FromLong((SOCKET_T)(newfd));
    if (sock == ((void *)0)) {
        close(newfd);
        goto finally;
    }

    addr = makesockaddr(s->sock_fd, (&((&addrbuf)->sa)),
                        addrlen, s->sock_proto);
    if (addr == ((void *)0))
        goto finally;

    res = PyTuple_Pack(2, sock, addr);

finally:
    do { if ((sock) == ((void *)0)) ; else do { if ( --((PyObject*)(sock))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sock)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sock)))); } while (0); } while (0);
    do { if ((addr) == ((void *)0)) ; else do { if ( --((PyObject*)(addr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(addr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(addr)))); } while (0); } while (0);
    return res;
}

static char accept_doc[] = "_accept() -> (integer, address info)\n\nWait for an incoming connection.  Return a new socket file descriptor\nrepresenting the connection, and the address of the client.\nFor IP sockets, the address info is a pair (hostaddr, port).";
# 2073 "socketmodule.c"
static PyObject *
sock_setblocking(PySocketSockObject *s, PyObject *arg)
{
    long block;

    block = PyLong_AsLong(arg);
    if (block == -1 && PyErr_Occurred())
        return ((void *)0);

    s->sock_timeout = block ? -1.0 : 0.0;
    internal_setblocking(s, block);

    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static char setblocking_doc[] = "setblocking(flag)\n\nSet the socket to blocking (flag is true) or non-blocking (false).\nsetblocking(True) is equivalent to settimeout(None);\nsetblocking(False) is equivalent to settimeout(0.0).";
# 2102 "socketmodule.c"
static PyObject *
sock_settimeout(PySocketSockObject *s, PyObject *arg)
{
    double timeout;

    if (arg == (&_Py_NoneStruct))
        timeout = -1.0;
    else {
        timeout = PyFloat_AsDouble(arg);
        if (timeout < 0.0) {
            if (!PyErr_Occurred())
                PyErr_SetString(PyExc_ValueError,
                                "Timeout value out of range");
            return ((void *)0);
        }
    }

    s->sock_timeout = timeout;
    internal_setblocking(s, timeout < 0.0);

    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static char settimeout_doc[] = "settimeout(timeout)\n\nSet a timeout on socket operations.  'timeout' can be a float,\ngiving in seconds, or None.  Setting a timeout of None disables\nthe timeout feature and is equivalent to setblocking(1).\nSetting a timeout of zero is the same as setblocking(0).";
# 2136 "socketmodule.c"
static PyObject *
sock_gettimeout(PySocketSockObject *s)
{
    if (s->sock_timeout < 0.0) {
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        return (&_Py_NoneStruct);
    }
    else
        return PyFloat_FromDouble(s->sock_timeout);
}

static char gettimeout_doc[] = "gettimeout() -> timeout\n\nReturns the timeout in seconds (float) associated with socket \noperations. A timeout of None indicates that timeouts on socket \noperations are disabled.";
# 2159 "socketmodule.c"
static PyObject *
sock_setsockopt(PySocketSockObject *s, PyObject *args)
{
    int level;
    int optname;
    int res;
    char *buf;
    int buflen;
    int flag;

    if (PyArg_ParseTuple(args, "iii:setsockopt",
                         &level, &optname, &flag)) {
        buf = (char *) &flag;
        buflen = sizeof flag;
    }
    else {
        PyErr_Clear();
        if (!PyArg_ParseTuple(args, "iiy#:setsockopt",
                              &level, &optname, &buf, &buflen))
            return ((void *)0);
    }
    res = setsockopt(s->sock_fd, level, optname, (void *)buf, buflen);
    if (res < 0)
        return s->errorhandler();
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static char setsockopt_doc[] = "setsockopt(level, option, value)\n\nSet a socket option.  See the Unix manual for level and option.\nThe value argument can either be an integer or a string.";
# 2199 "socketmodule.c"
static PyObject *
sock_getsockopt(PySocketSockObject *s, PyObject *args)
{
    int level;
    int optname;
    int res;
    PyObject *buf;
    socklen_t buflen = 0;

    if (!PyArg_ParseTuple(args, "ii|i:getsockopt",
                          &level, &optname, &buflen))
        return ((void *)0);

    if (buflen == 0) {
        int flag = 0;
        socklen_t flagsize = sizeof flag;
        res = getsockopt(s->sock_fd, level, optname,
                         (void *)&flag, &flagsize);
        if (res < 0)
            return s->errorhandler();
        return PyLong_FromLong(flag);
    }





    if (buflen <= 0 || buflen > 1024) {

        PyErr_SetString(PyExc_OSError,
                        "getsockopt buflen out of range");
        return ((void *)0);
    }
    buf = PyBytes_FromStringAndSize((char *)((void *)0), buflen);
    if (buf == ((void *)0))
        return ((void *)0);
    res = getsockopt(s->sock_fd, level, optname,
                     (void *)((__builtin_expect(!(((((((PyObject*)(buf))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "socketmodule.c", 2236, "PyBytes_Check(buf)") : (void)0), (((PyBytesObject *)(buf))->ob_sval)), &buflen);
    if (res < 0) {
        do { if ( --((PyObject*)(buf))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(buf)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(buf)))); } while (0);
        return s->errorhandler();
    }
    _PyBytes_Resize(&buf, buflen);
    return buf;
}

static char getsockopt_doc[] = "getsockopt(level, option[, buffersize]) -> value\n\nGet a socket option.  See the Unix manual for level and option.\nIf a nonzero buffersize argument is given, the return value is a\nstring of that length; otherwise it is an integer.";
# 2255 "socketmodule.c"
static PyObject *
sock_bind(PySocketSockObject *s, PyObject *addro)
{
    sock_addr_t addrbuf;
    int addrlen;
    int res;

    if (!getsockaddrarg(s, addro, (&((&addrbuf)->sa)), &addrlen))
        return ((void *)0);
    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = bind(s->sock_fd, (&((&addrbuf)->sa)), addrlen);
    PyEval_RestoreThread(_save); }
    if (res < 0)
        return s->errorhandler();
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static char bind_doc[] = "bind(address)\n\nBind the socket to a local address.  For IP sockets, the address is a\npair (host, port); the host must refer to the local host. For raw packet\nsockets the address is a tuple (ifname, proto [,pkttype [,hatype]])";
# 2285 "socketmodule.c"
static PyObject *
sock_close(PySocketSockObject *s)
{
    SOCKET_T fd;

    if ((fd = s->sock_fd) != -1) {
        s->sock_fd = -1;
        { PyThreadState *_save; _save = PyEval_SaveThread();
        (void) close(fd);
        PyEval_RestoreThread(_save); }
    }
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static char close_doc[] = "close()\n\nClose the socket.  It cannot be used after this call.";




static PyObject *
sock_detach(PySocketSockObject *s)
{
    SOCKET_T fd = s->sock_fd;
    s->sock_fd = -1;
    return PyLong_FromLong((SOCKET_T)(fd));
}

static char detach_doc[] = "detach()\n\nClose the socket object without closing the underlying file descriptor.The object cannot be used after this call, but the file descriptorcan be reused for other purposes.  The file descriptor is returned.";






static int
internal_connect(PySocketSockObject *s, struct sockaddr *addr, int addrlen,
                 int *timeoutp)
{
    int res, timeout;

    timeout = 0;
    res = connect(s->sock_fd, addr, addrlen);
# 2378 "socketmodule.c"
    if (s->sock_timeout > 0.0) {
        if (res < 0 && (*__error()) == 36 && 1) {
            timeout = internal_select(s, 1);
            if (timeout == 0) {



                socklen_t res_size = sizeof res;
                (void)getsockopt(s->sock_fd, 0xffff,
                                 0x1007, &res, &res_size);
                if (res == 56)
                    res = 0;
                (*__error()) = res;
            }
            else if (timeout == -1) {
                res = (*__error());
            }
            else
                res = 35;
        }
    }

    if (res < 0)
        res = (*__error());


    *timeoutp = timeout;

    return res;
}



static PyObject *
sock_connect(PySocketSockObject *s, PyObject *addro)
{
    sock_addr_t addrbuf;
    int addrlen;
    int res;
    int timeout;

    if (!getsockaddrarg(s, addro, (&((&addrbuf)->sa)), &addrlen))
        return ((void *)0);

    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = internal_connect(s, (&((&addrbuf)->sa)), addrlen, &timeout);
    PyEval_RestoreThread(_save); }

    if (timeout == 1) {
        PyErr_SetString(socket_timeout, "timed out");
        return ((void *)0);
    }
    if (res != 0)
        return s->errorhandler();
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static char connect_doc[] = "connect(address)\n\nConnect the socket to a remote address.  For IP sockets, the address\nis a pair (host, port).";
# 2445 "socketmodule.c"
static PyObject *
sock_connect_ex(PySocketSockObject *s, PyObject *addro)
{
    sock_addr_t addrbuf;
    int addrlen;
    int res;
    int timeout;

    if (!getsockaddrarg(s, addro, (&((&addrbuf)->sa)), &addrlen))
        return ((void *)0);

    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = internal_connect(s, (&((&addrbuf)->sa)), addrlen, &timeout);
    PyEval_RestoreThread(_save); }




    if (res == 4 && PyErr_CheckSignals())
        return ((void *)0);


    return PyLong_FromLong((long) res);
}

static char connect_ex_doc[] = "connect_ex(address) -> errno\n\nThis is like connect(address), but returns an error code (the errno value)\ninstead of raising an exception when an error occurs.";
# 2479 "socketmodule.c"
static PyObject *
sock_fileno(PySocketSockObject *s)
{
    return PyLong_FromLong((SOCKET_T)(s->sock_fd));
}

static char fileno_doc[] = "fileno() -> integer\n\nReturn the integer file descriptor of the socket.";







static PyObject *
sock_getsockname(PySocketSockObject *s)
{
    sock_addr_t addrbuf;
    int res;
    socklen_t addrlen;

    if (!getsockaddrlen(s, &addrlen))
        return ((void *)0);
    ((__builtin_object_size (&addrbuf, 0) != (size_t) -1) ? __builtin___memset_chk (&addrbuf, 0, addrlen, __builtin_object_size (&addrbuf, 0)) : __inline_memset_chk (&addrbuf, 0, addrlen));
    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = getsockname(s->sock_fd, (&((&addrbuf)->sa)), &addrlen);
    PyEval_RestoreThread(_save); }
    if (res < 0)
        return s->errorhandler();
    return makesockaddr(s->sock_fd, (&((&addrbuf)->sa)), addrlen,
                        s->sock_proto);
}

static char getsockname_doc[] = "getsockname() -> address info\n\nReturn the address of the local endpoint.  For IP sockets, the address\ninfo is a pair (hostaddr, port).";
# 2522 "socketmodule.c"
static PyObject *
sock_getpeername(PySocketSockObject *s)
{
    sock_addr_t addrbuf;
    int res;
    socklen_t addrlen;

    if (!getsockaddrlen(s, &addrlen))
        return ((void *)0);
    ((__builtin_object_size (&addrbuf, 0) != (size_t) -1) ? __builtin___memset_chk (&addrbuf, 0, addrlen, __builtin_object_size (&addrbuf, 0)) : __inline_memset_chk (&addrbuf, 0, addrlen));
    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = getpeername(s->sock_fd, (&((&addrbuf)->sa)), &addrlen);
    PyEval_RestoreThread(_save); }
    if (res < 0)
        return s->errorhandler();
    return makesockaddr(s->sock_fd, (&((&addrbuf)->sa)), addrlen,
                        s->sock_proto);
}

static char getpeername_doc[] = "getpeername() -> address info\n\nReturn the address of the remote endpoint.  For IP sockets, the address\ninfo is a pair (hostaddr, port).";
# 2552 "socketmodule.c"
static PyObject *
sock_listen(PySocketSockObject *s, PyObject *arg)
{
    int backlog;
    int res;

    backlog = _PyLong_AsInt(arg);
    if (backlog == -1 && PyErr_Occurred())
        return ((void *)0);
    { PyThreadState *_save; _save = PyEval_SaveThread();


    if (backlog < 0)
        backlog = 0;
    res = listen(s->sock_fd, backlog);
    PyEval_RestoreThread(_save); }
    if (res < 0)
        return s->errorhandler();
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static char listen_doc[] = "listen(backlog)\n\nEnable a server to accept connections.  The backlog argument must be at\nleast 0 (if it is lower, it is set to 0); it specifies the number of\nunaccepted connections that the system will allow before refusing new\nconnections.";
# 2592 "socketmodule.c"
static Py_ssize_t
sock_recv_guts(PySocketSockObject *s, char* cbuf, Py_ssize_t len, int flags)
{
    Py_ssize_t outlen = -1;
    int timeout;





    if (!1) {
        select_error();
        return -1;
    }
    if (len == 0) {

        return 0;
    }


    { _PyTime_timeval now, deadline = {0, 0}; double interval = s->sock_timeout; int has_timeout = s->sock_timeout > 0.0; if (has_timeout) { _PyTime_gettimeofday(&now); deadline = now; do { deadline.tv_usec += (long) (((long) s->sock_timeout - s->sock_timeout) * 1000000); deadline.tv_sec += (time_t) s->sock_timeout + (time_t) (deadline.tv_usec / 1000000); deadline.tv_usec %= 1000000; } while (0); } while (1) { (*__error()) = 0;
    { PyThreadState *_save; _save = PyEval_SaveThread();
    timeout = internal_select_ex(s, 0, interval);
    if (!timeout)
        outlen = recv(s->sock_fd, cbuf, len, flags);
    PyEval_RestoreThread(_save); }

    if (timeout == 1) {
        PyErr_SetString(socket_timeout, "timed out");
        return -1;
    }
    if (!has_timeout || (!((*__error()) == 35) && !((*__error()) == 35))) break; _PyTime_gettimeofday(&now); interval = ((deadline.tv_sec - now.tv_sec) + (deadline.tv_usec - now.tv_usec) * 0.000001); } }
    if (outlen < 0) {


        s->errorhandler();
        return -1;
    }
# 2672 "socketmodule.c"
    return outlen;
}




static PyObject *
sock_recv(PySocketSockObject *s, PyObject *args)
{
    Py_ssize_t recvlen, outlen;
    int flags = 0;
    PyObject *buf;

    if (!PyArg_ParseTuple(args, "n|i:recv", &recvlen, &flags))
        return ((void *)0);

    if (recvlen < 0) {
        PyErr_SetString(PyExc_ValueError,
                        "negative buffersize in recv");
        return ((void *)0);
    }


    buf = PyBytes_FromStringAndSize((char *) 0, recvlen);
    if (buf == ((void *)0))
        return ((void *)0);


    outlen = sock_recv_guts(s, ((__builtin_expect(!(((((((PyObject*)(buf))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "socketmodule.c", 2700, "PyBytes_Check(buf)") : (void)0), (((PyBytesObject *)(buf))->ob_sval)), recvlen, flags);
    if (outlen < 0) {


        do { if ( --((PyObject*)(buf))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(buf)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(buf)))); } while (0);
        return ((void *)0);
    }
    if (outlen != recvlen) {


        _PyBytes_Resize(&buf, outlen);
    }

    return buf;
}

static char recv_doc[] = "recv(buffersize[, flags]) -> data\n\nReceive up to buffersize bytes from the socket.  For the optional flags\nargument, see the Unix manual.  When no data is available, block until\nat least one byte is available or until the remote end is closed.  When\nthe remote end is closed and all data is read, return the empty string.";
# 2727 "socketmodule.c"
static PyObject*
sock_recv_into(PySocketSockObject *s, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"buffer", "nbytes", "flags", 0};

    int flags = 0;
    Py_buffer pbuf;
    char *buf;
    Py_ssize_t buflen, readlen, recvlen = 0;


    if (!PyArg_ParseTupleAndKeywords(args, kwds, "w*|ni:recv_into", kwlist,
                                     &pbuf, &recvlen, &flags))
        return ((void *)0);
    buf = pbuf.buf;
    buflen = pbuf.len;

    if (recvlen < 0) {
        PyBuffer_Release(&pbuf);
        PyErr_SetString(PyExc_ValueError,
                        "negative buffersize in recv_into");
        return ((void *)0);
    }
    if (recvlen == 0) {

        recvlen = buflen;
    }


    if (buflen < recvlen) {
        PyBuffer_Release(&pbuf);
        PyErr_SetString(PyExc_ValueError,
                        "buffer too small for requested bytes");
        return ((void *)0);
    }


    readlen = sock_recv_guts(s, buf, recvlen, flags);
    if (readlen < 0) {

        PyBuffer_Release(&pbuf);
        return ((void *)0);
    }

    PyBuffer_Release(&pbuf);


    return PyLong_FromSsize_t(readlen);
}

static char recv_into_doc[] = "recv_into(buffer, [nbytes[, flags]]) -> nbytes_read\n\nA version of recv() that stores its data into a buffer rather than creating \na new string.  Receive up to buffersize bytes from the socket.  If buffersize \nis not specified (or 0), receive up to the size available in the given buffer.\n\nSee recv() for documentation about the flags.";
# 2798 "socketmodule.c"
static Py_ssize_t
sock_recvfrom_guts(PySocketSockObject *s, char* cbuf, Py_ssize_t len, int flags,
                   PyObject** addr)
{
    sock_addr_t addrbuf;
    int timeout;
    Py_ssize_t n = -1;
    socklen_t addrlen;

    *addr = ((void *)0);

    if (!getsockaddrlen(s, &addrlen))
        return -1;

    if (!1) {
        select_error();
        return -1;
    }

    { _PyTime_timeval now, deadline = {0, 0}; double interval = s->sock_timeout; int has_timeout = s->sock_timeout > 0.0; if (has_timeout) { _PyTime_gettimeofday(&now); deadline = now; do { deadline.tv_usec += (long) (((long) s->sock_timeout - s->sock_timeout) * 1000000); deadline.tv_sec += (time_t) s->sock_timeout + (time_t) (deadline.tv_usec / 1000000); deadline.tv_usec %= 1000000; } while (0); } while (1) { (*__error()) = 0;
    { PyThreadState *_save; _save = PyEval_SaveThread();
    ((__builtin_object_size (&addrbuf, 0) != (size_t) -1) ? __builtin___memset_chk (&addrbuf, 0, addrlen, __builtin_object_size (&addrbuf, 0)) : __inline_memset_chk (&addrbuf, 0, addrlen));
    timeout = internal_select_ex(s, 0, interval);
    if (!timeout) {





        n = recvfrom(s->sock_fd, cbuf, len, flags,
                     (void *) &addrbuf, &addrlen);





    }
    PyEval_RestoreThread(_save); }

    if (timeout == 1) {
        PyErr_SetString(socket_timeout, "timed out");
        return -1;
    }
    if (!has_timeout || (!((*__error()) == 35) && !((*__error()) == 35))) break; _PyTime_gettimeofday(&now); interval = ((deadline.tv_sec - now.tv_sec) + (deadline.tv_usec - now.tv_usec) * 0.000001); } }
    if (n < 0) {
        s->errorhandler();
        return -1;
    }

    if (!(*addr = makesockaddr(s->sock_fd, (&((&addrbuf)->sa)),
                               addrlen, s->sock_proto)))
        return -1;

    return n;
}



static PyObject *
sock_recvfrom(PySocketSockObject *s, PyObject *args)
{
    PyObject *buf = ((void *)0);
    PyObject *addr = ((void *)0);
    PyObject *ret = ((void *)0);
    int flags = 0;
    Py_ssize_t recvlen, outlen;

    if (!PyArg_ParseTuple(args, "n|i:recvfrom", &recvlen, &flags))
        return ((void *)0);

    if (recvlen < 0) {
        PyErr_SetString(PyExc_ValueError,
                        "negative buffersize in recvfrom");
        return ((void *)0);
    }

    buf = PyBytes_FromStringAndSize((char *) 0, recvlen);
    if (buf == ((void *)0))
        return ((void *)0);

    outlen = sock_recvfrom_guts(s, ((__builtin_expect(!(((((((PyObject*)(buf))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "socketmodule.c", 2878, "PyBytes_Check(buf)") : (void)0), (((PyBytesObject *)(buf))->ob_sval)),
                                recvlen, flags, &addr);
    if (outlen < 0) {
        goto finally;
    }

    if (outlen != recvlen) {


        if (_PyBytes_Resize(&buf, outlen) < 0)

            goto finally;
    }

    ret = PyTuple_Pack(2, buf, addr);

finally:
    do { if ((buf) == ((void *)0)) ; else do { if ( --((PyObject*)(buf))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(buf)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(buf)))); } while (0); } while (0);
    do { if ((addr) == ((void *)0)) ; else do { if ( --((PyObject*)(addr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(addr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(addr)))); } while (0); } while (0);
    return ret;
}

static char recvfrom_doc[] = "recvfrom(buffersize[, flags]) -> (data, address info)\n\nLike recv(buffersize, flags) but also return the sender's address info.";







static PyObject *
sock_recvfrom_into(PySocketSockObject *s, PyObject *args, PyObject* kwds)
{
    static char *kwlist[] = {"buffer", "nbytes", "flags", 0};

    int flags = 0;
    Py_buffer pbuf;
    char *buf;
    Py_ssize_t readlen, buflen, recvlen = 0;

    PyObject *addr = ((void *)0);

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "w*|ni:recvfrom_into",
                                     kwlist, &pbuf,
                                     &recvlen, &flags))
        return ((void *)0);
    buf = pbuf.buf;
    buflen = pbuf.len;
    (__builtin_expect(!(buf != 0 && buflen > 0), 0) ? __assert_rtn(__func__, "socketmodule.c", 2926, "buf != 0 && buflen > 0") : (void)0);

    if (recvlen < 0) {
        PyBuffer_Release(&pbuf);
        PyErr_SetString(PyExc_ValueError,
                        "negative buffersize in recvfrom_into");
        return ((void *)0);
    }
    if (recvlen == 0) {

        recvlen = buflen;
    }

    readlen = sock_recvfrom_guts(s, buf, recvlen, flags, &addr);
    if (readlen < 0) {
        PyBuffer_Release(&pbuf);

        do { if ((addr) == ((void *)0)) ; else do { if ( --((PyObject*)(addr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(addr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(addr)))); } while (0); } while (0);
        return ((void *)0);
    }

    PyBuffer_Release(&pbuf);


    return Py_BuildValue("nN", readlen, addr);
}

static char recvfrom_into_doc[] = "recvfrom_into(buffer[, nbytes[, flags]]) -> (nbytes, address info)\n\nLike recv_into(buffer[, nbytes[, flags]]) but also return the sender's address info.";
# 2972 "socketmodule.c"
static PyObject *
sock_recvmsg_guts(PySocketSockObject *s, struct iovec *iov, int iovlen,
                  int flags, Py_ssize_t controllen,
                  PyObject *(*makeval)(ssize_t, void *), void *makeval_data)
{
    ssize_t bytes_received = -1;
    int timeout;
    sock_addr_t addrbuf;
    socklen_t addrbuflen;
    struct msghdr msg = {0};
    PyObject *cmsg_list = ((void *)0), *retval = ((void *)0);
    void *controlbuf = ((void *)0);
    struct cmsghdr *cmsgh;
    size_t cmsgdatalen = 0;
    int cmsg_status;







    if (!getsockaddrlen(s, &addrbuflen))
        return ((void *)0);
    ((__builtin_object_size (&addrbuf, 0) != (size_t) -1) ? __builtin___memset_chk (&addrbuf, 0, addrbuflen, __builtin_object_size (&addrbuf, 0)) : __inline_memset_chk (&addrbuf, 0, addrbuflen));
    (&((&addrbuf)->sa))->sa_family = 0;

    if (controllen < 0 || controllen > 2147483647) {
        PyErr_SetString(PyExc_ValueError,
                        "invalid ancillary data buffer length");
        return ((void *)0);
    }
    if (controllen > 0 && (controlbuf = PyMem_Malloc(controllen)) == ((void *)0))
        return PyErr_NoMemory();


    if (!1) {
        select_error();
        goto finally;
    }

    { _PyTime_timeval now, deadline = {0, 0}; double interval = s->sock_timeout; int has_timeout = s->sock_timeout > 0.0; if (has_timeout) { _PyTime_gettimeofday(&now); deadline = now; do { deadline.tv_usec += (long) (((long) s->sock_timeout - s->sock_timeout) * 1000000); deadline.tv_sec += (time_t) s->sock_timeout + (time_t) (deadline.tv_usec / 1000000); deadline.tv_usec %= 1000000; } while (0); } while (1) { (*__error()) = 0;
    { PyThreadState *_save; _save = PyEval_SaveThread();;
    msg.msg_name = (&((&addrbuf)->sa));
    msg.msg_namelen = addrbuflen;
    msg.msg_iov = iov;
    msg.msg_iovlen = iovlen;
    msg.msg_control = controlbuf;
    msg.msg_controllen = controllen;
    timeout = internal_select_ex(s, 0, interval);
    if (!timeout)
        bytes_received = recvmsg(s->sock_fd, &msg, flags);
    PyEval_RestoreThread(_save); };
    if (timeout == 1) {
        PyErr_SetString(socket_timeout, "timed out");
        goto finally;
    }
    if (!has_timeout || (!((*__error()) == 35) && !((*__error()) == 35))) break; _PyTime_gettimeofday(&now); interval = ((deadline.tv_sec - now.tv_sec) + (deadline.tv_usec - now.tv_usec) * 0.000001); } }

    if (bytes_received < 0) {
        s->errorhandler();
        goto finally;
    }


    if ((cmsg_list = PyList_New(0)) == ((void *)0))
        goto err_closefds;


    for (cmsgh = ((msg.msg_controllen > 0) ? ((&msg)->msg_controllen >= sizeof(struct cmsghdr) ? (struct cmsghdr *)(&msg)->msg_control : (struct cmsghdr *)0L) : ((void *)0));
         cmsgh != ((void *)0); cmsgh = ((char *)(cmsgh) == (char *)0L ? ((&msg)->msg_controllen >= sizeof(struct cmsghdr) ? (struct cmsghdr *)(&msg)->msg_control : (struct cmsghdr *)0L) : ((((unsigned char *)(cmsgh) + ((__darwin_size_t)((char *)(__darwin_size_t)((__uint32_t)(cmsgh)->cmsg_len) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1)) + ((__darwin_size_t)((char *)(__darwin_size_t)(sizeof(struct cmsghdr)) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1))) > ((unsigned char *)(&msg)->msg_control + (&msg)->msg_controllen)) ? (struct cmsghdr *)0L : (struct cmsghdr *)(void *)((unsigned char *)(cmsgh) + ((__darwin_size_t)((char *)(__darwin_size_t)((__uint32_t)(cmsgh)->cmsg_len) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1)))))) {
        PyObject *bytes, *tuple;
        int tmp;

        cmsg_status = get_cmsg_data_len(&msg, cmsgh, &cmsgdatalen);
        if (cmsg_status != 0) {
            if (PyErr_WarnEx(PyExc_RuntimeWarning,
                             "received malformed or improperly-truncated "
                             "ancillary data", 1) == -1)
                goto err_closefds;
        }
        if (cmsg_status < 0)
            break;
        if (cmsgdatalen > ((Py_ssize_t)(((size_t)-1)>>1))) {
            PyErr_SetString(PyExc_OSError, "control message too long");
            goto err_closefds;
        }

        bytes = PyBytes_FromStringAndSize((char *)((unsigned char *)(cmsgh) + ((__darwin_size_t)((char *)(__darwin_size_t)(sizeof(struct cmsghdr)) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1))),
                                          cmsgdatalen);
        tuple = Py_BuildValue("iiN", (int)cmsgh->cmsg_level,
                              (int)cmsgh->cmsg_type, bytes);
        if (tuple == ((void *)0))
            goto err_closefds;
        tmp = PyList_Append(cmsg_list, tuple);
        do { if ( --((PyObject*)(tuple))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tuple)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tuple)))); } while (0);
        if (tmp != 0)
            goto err_closefds;

        if (cmsg_status != 0)
            break;
    }

    retval = Py_BuildValue("NOiN",
                           (*makeval)(bytes_received, makeval_data),
                           cmsg_list,
                           (int)msg.msg_flags,
                           makesockaddr(s->sock_fd, (&((&addrbuf)->sa)),
                                        ((msg.msg_namelen > addrbuflen) ?
                                         addrbuflen : msg.msg_namelen),
                                        s->sock_proto));
    if (retval == ((void *)0))
        goto err_closefds;

finally:
    do { if ((cmsg_list) == ((void *)0)) ; else do { if ( --((PyObject*)(cmsg_list))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(cmsg_list)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(cmsg_list)))); } while (0); } while (0);
    PyMem_Free(controlbuf);
    return retval;

err_closefds:


    for (cmsgh = ((msg.msg_controllen > 0) ? ((&msg)->msg_controllen >= sizeof(struct cmsghdr) ? (struct cmsghdr *)(&msg)->msg_control : (struct cmsghdr *)0L) : ((void *)0));
         cmsgh != ((void *)0); cmsgh = ((char *)(cmsgh) == (char *)0L ? ((&msg)->msg_controllen >= sizeof(struct cmsghdr) ? (struct cmsghdr *)(&msg)->msg_control : (struct cmsghdr *)0L) : ((((unsigned char *)(cmsgh) + ((__darwin_size_t)((char *)(__darwin_size_t)((__uint32_t)(cmsgh)->cmsg_len) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1)) + ((__darwin_size_t)((char *)(__darwin_size_t)(sizeof(struct cmsghdr)) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1))) > ((unsigned char *)(&msg)->msg_control + (&msg)->msg_controllen)) ? (struct cmsghdr *)0L : (struct cmsghdr *)(void *)((unsigned char *)(cmsgh) + ((__darwin_size_t)((char *)(__darwin_size_t)((__uint32_t)(cmsgh)->cmsg_len) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1)))))) {
        cmsg_status = get_cmsg_data_len(&msg, cmsgh, &cmsgdatalen);
        if (cmsg_status < 0)
            break;
        if (cmsgh->cmsg_level == 0xffff &&
            cmsgh->cmsg_type == 0x01) {
            size_t numfds;
            int *fdp;

            numfds = cmsgdatalen / sizeof(int);
            fdp = (int *)((unsigned char *)(cmsgh) + ((__darwin_size_t)((char *)(__darwin_size_t)(sizeof(struct cmsghdr)) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1)));
            while (numfds-- > 0)
                close(*fdp++);
        }
        if (cmsg_status != 0)
            break;
    }

    goto finally;
}


static PyObject *
makeval_recvmsg(ssize_t received, void *data)
{
    PyObject **buf = data;

    if (received < ((__builtin_expect(!(((((((PyObject*)(*buf))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "socketmodule.c", 3122, "PyBytes_Check(*buf)") : (void)0),(((PyVarObject*)(*buf))->ob_size)))
        _PyBytes_Resize(buf, received);
    do { if ((*buf) == ((void *)0)) ; else ( ((PyObject*)(*buf))->ob_refcnt++); } while (0);
    return *buf;
}



static PyObject *
sock_recvmsg(PySocketSockObject *s, PyObject *args)
{
    Py_ssize_t bufsize, ancbufsize = 0;
    int flags = 0;
    struct iovec iov;
    PyObject *buf = ((void *)0), *retval = ((void *)0);

    if (!PyArg_ParseTuple(args, "n|ni:recvmsg", &bufsize, &ancbufsize, &flags))
        return ((void *)0);

    if (bufsize < 0) {
        PyErr_SetString(PyExc_ValueError, "negative buffer size in recvmsg()");
        return ((void *)0);
    }
    if ((buf = PyBytes_FromStringAndSize(((void *)0), bufsize)) == ((void *)0))
        return ((void *)0);
    iov.iov_base = ((__builtin_expect(!(((((((PyObject*)(buf))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "socketmodule.c", 3147, "PyBytes_Check(buf)") : (void)0), (((PyBytesObject *)(buf))->ob_sval));
    iov.iov_len = bufsize;




    retval = sock_recvmsg_guts(s, &iov, 1, flags, ancbufsize,
                               &makeval_recvmsg, &buf);
    do { if ((buf) == ((void *)0)) ; else do { if ( --((PyObject*)(buf))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(buf)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(buf)))); } while (0); } while (0);
    return retval;
}

static char recvmsg_doc[] = "recvmsg(bufsize[, ancbufsize[, flags]]) -> (data, ancdata, msg_flags, address)\n\nReceive normal data (up to bufsize bytes) and ancillary data from the\nsocket.  The ancbufsize argument sets the size in bytes of the\ninternal buffer used to receive the ancillary data; it defaults to 0,\nmeaning that no ancillary data will be received.  Appropriate buffer\nsizes for ancillary data can be calculated using CMSG_SPACE() or\nCMSG_LEN(), and items which do not fit into the buffer might be\ntruncated or discarded.  The flags argument defaults to 0 and has the\nsame meaning as for recv().\n\nThe return value is a 4-tuple: (data, ancdata, msg_flags, address).\nThe data item is a bytes object holding the non-ancillary data\nreceived.  The ancdata item is a list of zero or more tuples\n(cmsg_level, cmsg_type, cmsg_data) representing the ancillary data\n(control messages) received: cmsg_level and cmsg_type are integers\nspecifying the protocol level and protocol-specific type respectively,\nand cmsg_data is a bytes object holding the associated data.  The\nmsg_flags item is the bitwise OR of various flags indicating\nconditions on the received message; see your system documentation for\ndetails.  If the receiving socket is unconnected, address is the\naddress of the sending socket, if available; otherwise, its value is\nunspecified.\n\nIf recvmsg() raises an exception after the system call returns, it\nwill first attempt to close any file descriptors received via the\nSCM_RIGHTS mechanism.";
# 3189 "socketmodule.c"
static PyObject *
makeval_recvmsg_into(ssize_t received, void *data)
{
    return PyLong_FromSsize_t(received);
}



static PyObject *
sock_recvmsg_into(PySocketSockObject *s, PyObject *args)
{
    Py_ssize_t ancbufsize = 0;
    int flags = 0;
    struct iovec *iovs = ((void *)0);
    Py_ssize_t i, nitems, nbufs = 0;
    Py_buffer *bufs = ((void *)0);
    PyObject *buffers_arg, *fast, *retval = ((void *)0);

    if (!PyArg_ParseTuple(args, "O|ni:recvmsg_into",
                          &buffers_arg, &ancbufsize, &flags))
        return ((void *)0);

    if ((fast = PySequence_Fast(buffers_arg,
                                "recvmsg_into() argument 1 must be an "
                                "iterable")) == ((void *)0))
        return ((void *)0);
    nitems = (((((((PyObject*)(fast))->ob_type))->tp_flags & ((1L<<25))) != 0) ? (((PyVarObject*)(fast))->ob_size) : (((PyVarObject*)(fast))->ob_size));
    if (nitems > 2147483647) {
        PyErr_SetString(PyExc_OSError, "recvmsg_into() argument 1 is too long");
        goto finally;
    }



    if (nitems > 0 && ((iovs = ( ((size_t)(nitems) > ((Py_ssize_t)(((size_t)-1)>>1)) / sizeof(struct iovec)) ? ((void *)0) : ( (struct iovec *) PyMem_Malloc((nitems) * sizeof(struct iovec)) ) )) == ((void *)0) ||
                       (bufs = ( ((size_t)(nitems) > ((Py_ssize_t)(((size_t)-1)>>1)) / sizeof(Py_buffer)) ? ((void *)0) : ( (Py_buffer *) PyMem_Malloc((nitems) * sizeof(Py_buffer)) ) )) == ((void *)0))) {
        PyErr_NoMemory();
        goto finally;
    }
    for (; nbufs < nitems; nbufs++) {
        if (!PyArg_Parse((((((((PyObject*)(fast))->ob_type))->tp_flags & ((1L<<25))) != 0) ? (((PyListObject *)(fast))->ob_item[nbufs]) : (((PyTupleObject *)(fast))->ob_item[nbufs])),
                         "w*;recvmsg_into() argument 1 must be an iterable "
                         "of single-segment read-write buffers",
                         &bufs[nbufs]))
            goto finally;
        iovs[nbufs].iov_base = bufs[nbufs].buf;
        iovs[nbufs].iov_len = bufs[nbufs].len;
    }

    retval = sock_recvmsg_guts(s, iovs, nitems, flags, ancbufsize,
                               &makeval_recvmsg_into, ((void *)0));
finally:
    for (i = 0; i < nbufs; i++)
        PyBuffer_Release(&bufs[i]);
    PyMem_Free(bufs);
    PyMem_Free(iovs);
    do { if ( --((PyObject*)(fast))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(fast)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(fast)))); } while (0);
    return retval;
}

static char recvmsg_into_doc[] = "recvmsg_into(buffers[, ancbufsize[, flags]]) -> (nbytes, ancdata, msg_flags, address)\n\nReceive normal data and ancillary data from the socket, scattering the\nnon-ancillary data into a series of buffers.  The buffers argument\nmust be an iterable of objects that export writable buffers\n(e.g. bytearray objects); these will be filled with successive chunks\nof the non-ancillary data until it has all been written or there are\nno more buffers.  The ancbufsize argument sets the size in bytes of\nthe internal buffer used to receive the ancillary data; it defaults to\n0, meaning that no ancillary data will be received.  Appropriate\nbuffer sizes for ancillary data can be calculated using CMSG_SPACE()\nor CMSG_LEN(), and items which do not fit into the buffer might be\ntruncated or discarded.  The flags argument defaults to 0 and has the\nsame meaning as for recv().\n\nThe return value is a 4-tuple: (nbytes, ancdata, msg_flags, address).\nThe nbytes item is the total number of bytes of non-ancillary data\nwritten into the buffers.  The ancdata item is a list of zero or more\ntuples (cmsg_level, cmsg_type, cmsg_data) representing the ancillary\ndata (control messages) received: cmsg_level and cmsg_type are\nintegers specifying the protocol level and protocol-specific type\nrespectively, and cmsg_data is a bytes object holding the associated\ndata.  The msg_flags item is the bitwise OR of various flags\nindicating conditions on the received message; see your system\ndocumentation for details.  If the receiving socket is unconnected,\naddress is the address of the sending socket, if available; otherwise,\nits value is unspecified.\n\nIf recvmsg_into() raises an exception after the system call returns,\nit will first attempt to close any file descriptors received via the\nSCM_RIGHTS mechanism.";
# 3286 "socketmodule.c"
static PyObject *
sock_send(PySocketSockObject *s, PyObject *args)
{
    char *buf;
    Py_ssize_t len, n = -1;
    int flags = 0, timeout;
    Py_buffer pbuf;

    if (!PyArg_ParseTuple(args, "y*|i:send", &pbuf, &flags))
        return ((void *)0);

    if (!1) {
        PyBuffer_Release(&pbuf);
        return select_error();
    }
    buf = pbuf.buf;
    len = pbuf.len;

    { _PyTime_timeval now, deadline = {0, 0}; double interval = s->sock_timeout; int has_timeout = s->sock_timeout > 0.0; if (has_timeout) { _PyTime_gettimeofday(&now); deadline = now; do { deadline.tv_usec += (long) (((long) s->sock_timeout - s->sock_timeout) * 1000000); deadline.tv_sec += (time_t) s->sock_timeout + (time_t) (deadline.tv_usec / 1000000); deadline.tv_usec %= 1000000; } while (0); } while (1) { (*__error()) = 0;
    { PyThreadState *_save; _save = PyEval_SaveThread();
    timeout = internal_select_ex(s, 1, interval);
    if (!timeout)



        n = send(s->sock_fd, buf, len, flags);

    PyEval_RestoreThread(_save); }
    if (timeout == 1) {
        PyBuffer_Release(&pbuf);
        PyErr_SetString(socket_timeout, "timed out");
        return ((void *)0);
    }
    if (!has_timeout || (!((*__error()) == 35) && !((*__error()) == 35))) break; _PyTime_gettimeofday(&now); interval = ((deadline.tv_sec - now.tv_sec) + (deadline.tv_usec - now.tv_usec) * 0.000001); } }

    PyBuffer_Release(&pbuf);
    if (n < 0)
        return s->errorhandler();
    return PyLong_FromSsize_t(n);
}

static char send_doc[] = "send(data[, flags]) -> count\n\nSend a data string to the socket.  For the optional flags\nargument, see the Unix manual.  Return the number of bytes\nsent; this may be less than len(data) if the network is busy.";
# 3337 "socketmodule.c"
static PyObject *
sock_sendall(PySocketSockObject *s, PyObject *args)
{
    char *buf;
    Py_ssize_t len, n = -1;
    int flags = 0, timeout, saved_errno;
    Py_buffer pbuf;

    if (!PyArg_ParseTuple(args, "y*|i:sendall", &pbuf, &flags))
        return ((void *)0);
    buf = pbuf.buf;
    len = pbuf.len;

    if (!1) {
        PyBuffer_Release(&pbuf);
        return select_error();
    }

    do {
        { PyThreadState *_save; _save = PyEval_SaveThread();
        timeout = internal_select(s, 1);
        n = -1;
        if (!timeout) {



            n = send(s->sock_fd, buf, len, flags);

        }
        PyEval_RestoreThread(_save); }
        if (timeout == 1) {
            PyBuffer_Release(&pbuf);
            PyErr_SetString(socket_timeout, "timed out");
            return ((void *)0);
        }

        saved_errno = (*__error());



        if (PyErr_CheckSignals()) {
            PyBuffer_Release(&pbuf);
            return ((void *)0);
        }
        if (n < 0) {

            if (saved_errno == 4)
                continue;
            else
                break;
        }
        buf += n;
        len -= n;
    } while (len > 0);
    PyBuffer_Release(&pbuf);

    if (n < 0)
        return s->errorhandler();

    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static char sendall_doc[] = "sendall(data[, flags])\n\nSend a data string to the socket.  For the optional flags\nargument, see the Unix manual.  This calls send() repeatedly\nuntil all data is sent.  If an error occurs, it's impossible\nto tell how much data has been sent.";
# 3411 "socketmodule.c"
static PyObject *
sock_sendto(PySocketSockObject *s, PyObject *args)
{
    Py_buffer pbuf;
    PyObject *addro;
    char *buf;
    Py_ssize_t len, arglen;
    sock_addr_t addrbuf;
    int addrlen, n = -1, flags, timeout;

    flags = 0;
    arglen = PyTuple_Size(args);
    switch (arglen) {
        case 2:
            PyArg_ParseTuple(args, "y*O:sendto", &pbuf, &addro);
            break;
        case 3:
            PyArg_ParseTuple(args, "y*iO:sendto",
                             &pbuf, &flags, &addro);
            break;
        default:
            PyErr_Format(PyExc_TypeError,
                         "sendto() takes 2 or 3 arguments (%d given)",
                         arglen);
            return ((void *)0);
    }
    if (PyErr_Occurred())
        return ((void *)0);

    buf = pbuf.buf;
    len = pbuf.len;

    if (!1) {
        PyBuffer_Release(&pbuf);
        return select_error();
    }

    if (!getsockaddrarg(s, addro, (&((&addrbuf)->sa)), &addrlen)) {
        PyBuffer_Release(&pbuf);
        return ((void *)0);
    }

    { _PyTime_timeval now, deadline = {0, 0}; double interval = s->sock_timeout; int has_timeout = s->sock_timeout > 0.0; if (has_timeout) { _PyTime_gettimeofday(&now); deadline = now; do { deadline.tv_usec += (long) (((long) s->sock_timeout - s->sock_timeout) * 1000000); deadline.tv_sec += (time_t) s->sock_timeout + (time_t) (deadline.tv_usec / 1000000); deadline.tv_usec %= 1000000; } while (0); } while (1) { (*__error()) = 0;
    { PyThreadState *_save; _save = PyEval_SaveThread();
    timeout = internal_select_ex(s, 1, interval);
    if (!timeout)
        n = sendto(s->sock_fd, buf, len, flags, (&((&addrbuf)->sa)), addrlen);
    PyEval_RestoreThread(_save); }

    if (timeout == 1) {
        PyBuffer_Release(&pbuf);
        PyErr_SetString(socket_timeout, "timed out");
        return ((void *)0);
    }
    if (!has_timeout || (!((*__error()) == 35) && !((*__error()) == 35))) break; _PyTime_gettimeofday(&now); interval = ((deadline.tv_sec - now.tv_sec) + (deadline.tv_usec - now.tv_usec) * 0.000001); } }
    PyBuffer_Release(&pbuf);
    if (n < 0)
        return s->errorhandler();
    return PyLong_FromSsize_t(n);
}

static char sendto_doc[] = "sendto(data[, flags], address) -> count\n\nLike send(data, flags) but allows specifying the destination address.\nFor IP sockets, the address is a pair (hostaddr, port).";
# 3484 "socketmodule.c"
static PyObject *
sock_sendmsg(PySocketSockObject *s, PyObject *args)
{
    Py_ssize_t i, ndataparts, ndatabufs = 0, ncmsgs, ncmsgbufs = 0;
    Py_buffer *databufs = ((void *)0);
    struct iovec *iovs = ((void *)0);
    sock_addr_t addrbuf;
    struct msghdr msg = {0};
    struct cmsginfo {
        int level;
        int type;
        Py_buffer data;
    } *cmsgs = ((void *)0);
    void *controlbuf = ((void *)0);
    size_t controllen, controllen_last;
    ssize_t bytes_sent = -1;
    int addrlen, timeout, flags = 0;
    PyObject *data_arg, *cmsg_arg = ((void *)0), *addr_arg = ((void *)0), *data_fast = ((void *)0),
        *cmsg_fast = ((void *)0), *retval = ((void *)0);

    if (!PyArg_ParseTuple(args, "O|OiO:sendmsg",
                          &data_arg, &cmsg_arg, &flags, &addr_arg))
        return ((void *)0);


    if (addr_arg != ((void *)0) && addr_arg != (&_Py_NoneStruct)) {
        if (!getsockaddrarg(s, addr_arg, (&((&addrbuf)->sa)), &addrlen))
            goto finally;
        msg.msg_name = &addrbuf;
        msg.msg_namelen = addrlen;
    }



    if ((data_fast = PySequence_Fast(data_arg,
                                     "sendmsg() argument 1 must be an "
                                     "iterable")) == ((void *)0))
        goto finally;
    ndataparts = (((((((PyObject*)(data_fast))->ob_type))->tp_flags & ((1L<<25))) != 0) ? (((PyVarObject*)(data_fast))->ob_size) : (((PyVarObject*)(data_fast))->ob_size));
    if (ndataparts > 2147483647) {
        PyErr_SetString(PyExc_OSError, "sendmsg() argument 1 is too long");
        goto finally;
    }
    msg.msg_iovlen = ndataparts;
    if (ndataparts > 0 &&
        ((msg.msg_iov = iovs = ( ((size_t)(ndataparts) > ((Py_ssize_t)(((size_t)-1)>>1)) / sizeof(struct iovec)) ? ((void *)0) : ( (struct iovec *) PyMem_Malloc((ndataparts) * sizeof(struct iovec)) ) )) == ((void *)0) ||
         (databufs = ( ((size_t)(ndataparts) > ((Py_ssize_t)(((size_t)-1)>>1)) / sizeof(Py_buffer)) ? ((void *)0) : ( (Py_buffer *) PyMem_Malloc((ndataparts) * sizeof(Py_buffer)) ) )) == ((void *)0))) {
        PyErr_NoMemory();
        goto finally;
    }
    for (; ndatabufs < ndataparts; ndatabufs++) {
        if (!PyArg_Parse((((((((PyObject*)(data_fast))->ob_type))->tp_flags & ((1L<<25))) != 0) ? (((PyListObject *)(data_fast))->ob_item[ndatabufs]) : (((PyTupleObject *)(data_fast))->ob_item[ndatabufs])),
                         "y*;sendmsg() argument 1 must be an iterable of "
                         "buffer-compatible objects",
                         &databufs[ndatabufs]))
            goto finally;
        iovs[ndatabufs].iov_base = databufs[ndatabufs].buf;
        iovs[ndatabufs].iov_len = databufs[ndatabufs].len;
    }

    if (cmsg_arg == ((void *)0))
        ncmsgs = 0;
    else {
        if ((cmsg_fast = PySequence_Fast(cmsg_arg,
                                         "sendmsg() argument 2 must be an "
                                         "iterable")) == ((void *)0))
            goto finally;
        ncmsgs = (((((((PyObject*)(cmsg_fast))->ob_type))->tp_flags & ((1L<<25))) != 0) ? (((PyVarObject*)(cmsg_fast))->ob_size) : (((PyVarObject*)(cmsg_fast))->ob_size));
    }
# 3564 "socketmodule.c"
    if (ncmsgs > 0 && (cmsgs = ( ((size_t)(ncmsgs) > ((Py_ssize_t)(((size_t)-1)>>1)) / sizeof(struct cmsginfo)) ? ((void *)0) : ( (struct cmsginfo *) PyMem_Malloc((ncmsgs) * sizeof(struct cmsginfo)) ) )) == ((void *)0)) {
        PyErr_NoMemory();
        goto finally;
    }
    controllen = controllen_last = 0;
    while (ncmsgbufs < ncmsgs) {
        size_t bufsize, space;

        if (!PyArg_Parse((((((((PyObject*)(cmsg_fast))->ob_type))->tp_flags & ((1L<<25))) != 0) ? (((PyListObject *)(cmsg_fast))->ob_item[ncmsgbufs]) : (((PyTupleObject *)(cmsg_fast))->ob_item[ncmsgbufs])),
                         "(iiy*):[sendmsg() ancillary data items]",
                         &cmsgs[ncmsgbufs].level,
                         &cmsgs[ncmsgbufs].type,
                         &cmsgs[ncmsgbufs].data))
            goto finally;
        bufsize = cmsgs[ncmsgbufs++].data.len;


        if (!get_CMSG_SPACE(bufsize, &space)) {



            PyErr_SetString(PyExc_OSError, "ancillary data item too large");
            goto finally;
        }
        controllen += space;
        if (controllen > 2147483647 || controllen < controllen_last) {
            PyErr_SetString(PyExc_OSError, "too much ancillary data");
            goto finally;
        }
        controllen_last = controllen;
    }


    if (ncmsgbufs > 0) {
        struct cmsghdr *cmsgh = ((void *)0);

        if ((msg.msg_control = controlbuf =
             PyMem_Malloc(controllen)) == ((void *)0)) {
            PyErr_NoMemory();
            goto finally;
        }
        msg.msg_controllen = controllen;







        ((__builtin_object_size (controlbuf, 0) != (size_t) -1) ? __builtin___memset_chk (controlbuf, 0, controllen, __builtin_object_size (controlbuf, 0)) : __inline_memset_chk (controlbuf, 0, controllen));

        for (i = 0; i < ncmsgbufs; i++) {
            size_t msg_len, data_len = cmsgs[i].data.len;
            int enough_space = 0;

            cmsgh = (i == 0) ? ((&msg)->msg_controllen >= sizeof(struct cmsghdr) ? (struct cmsghdr *)(&msg)->msg_control : (struct cmsghdr *)0L) : ((char *)(cmsgh) == (char *)0L ? ((&msg)->msg_controllen >= sizeof(struct cmsghdr) ? (struct cmsghdr *)(&msg)->msg_control : (struct cmsghdr *)0L) : ((((unsigned char *)(cmsgh) + ((__darwin_size_t)((char *)(__darwin_size_t)((__uint32_t)(cmsgh)->cmsg_len) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1)) + ((__darwin_size_t)((char *)(__darwin_size_t)(sizeof(struct cmsghdr)) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1))) > ((unsigned char *)(&msg)->msg_control + (&msg)->msg_controllen)) ? (struct cmsghdr *)0L : (struct cmsghdr *)(void *)((unsigned char *)(cmsgh) + ((__darwin_size_t)((char *)(__darwin_size_t)((__uint32_t)(cmsgh)->cmsg_len) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1)))));
            if (cmsgh == ((void *)0)) {
                PyErr_Format(PyExc_RuntimeError,
                             "unexpected NULL result from %s()",
                             (i == 0) ? "CMSG_FIRSTHDR" : "CMSG_NXTHDR");
                goto finally;
            }
            if (!get_CMSG_LEN(data_len, &msg_len)) {
                PyErr_SetString(PyExc_RuntimeError,
                                "item size out of range for CMSG_LEN()");
                goto finally;
            }
            if (cmsg_min_space(&msg, cmsgh, msg_len)) {
                size_t space;

                cmsgh->cmsg_len = msg_len;
                if (get_cmsg_data_space(&msg, cmsgh, &space))
                    enough_space = (space >= data_len);
            }
            if (!enough_space) {
                PyErr_SetString(PyExc_RuntimeError,
                                "ancillary data does not fit in calculated "
                                "space");
                goto finally;
            }
            cmsgh->cmsg_level = cmsgs[i].level;
            cmsgh->cmsg_type = cmsgs[i].type;
            ((__builtin_object_size (((unsigned char *)(cmsgh) + ((__darwin_size_t)((char *)(__darwin_size_t)(sizeof(struct cmsghdr)) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1))), 0) != (size_t) -1) ? __builtin___memcpy_chk (((unsigned char *)(cmsgh) + ((__darwin_size_t)((char *)(__darwin_size_t)(sizeof(struct cmsghdr)) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1))), cmsgs[i].data.buf, data_len, __builtin_object_size (((unsigned char *)(cmsgh) + ((__darwin_size_t)((char *)(__darwin_size_t)(sizeof(struct cmsghdr)) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1))), 0)) : __inline_memcpy_chk (((unsigned char *)(cmsgh) + ((__darwin_size_t)((char *)(__darwin_size_t)(sizeof(struct cmsghdr)) + (sizeof(__uint32_t) - 1)) &~ (sizeof(__uint32_t) - 1))), cmsgs[i].data.buf, data_len));
        }
    }


    if (!1) {
        select_error();
        goto finally;
    }

    { _PyTime_timeval now, deadline = {0, 0}; double interval = s->sock_timeout; int has_timeout = s->sock_timeout > 0.0; if (has_timeout) { _PyTime_gettimeofday(&now); deadline = now; do { deadline.tv_usec += (long) (((long) s->sock_timeout - s->sock_timeout) * 1000000); deadline.tv_sec += (time_t) s->sock_timeout + (time_t) (deadline.tv_usec / 1000000); deadline.tv_usec %= 1000000; } while (0); } while (1) { (*__error()) = 0;
    { PyThreadState *_save; _save = PyEval_SaveThread();;
    timeout = internal_select_ex(s, 1, interval);
    if (!timeout)
        bytes_sent = sendmsg(s->sock_fd, &msg, flags);
    PyEval_RestoreThread(_save); };
    if (timeout == 1) {
        PyErr_SetString(socket_timeout, "timed out");
        goto finally;
    }
    if (!has_timeout || (!((*__error()) == 35) && !((*__error()) == 35))) break; _PyTime_gettimeofday(&now); interval = ((deadline.tv_sec - now.tv_sec) + (deadline.tv_usec - now.tv_usec) * 0.000001); } }

    if (bytes_sent < 0) {
        s->errorhandler();
        goto finally;
    }
    retval = PyLong_FromSsize_t(bytes_sent);

finally:
    PyMem_Free(controlbuf);
    for (i = 0; i < ncmsgbufs; i++)
        PyBuffer_Release(&cmsgs[i].data);
    PyMem_Free(cmsgs);
    do { if ((cmsg_fast) == ((void *)0)) ; else do { if ( --((PyObject*)(cmsg_fast))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(cmsg_fast)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(cmsg_fast)))); } while (0); } while (0);
    for (i = 0; i < ndatabufs; i++)
        PyBuffer_Release(&databufs[i]);
    PyMem_Free(databufs);
    PyMem_Free(iovs);
    do { if ((data_fast) == ((void *)0)) ; else do { if ( --((PyObject*)(data_fast))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(data_fast)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(data_fast)))); } while (0); } while (0);
    return retval;
}

static char sendmsg_doc[] = "sendmsg(buffers[, ancdata[, flags[, address]]]) -> count\n\nSend normal and ancillary data to the socket, gathering the\nnon-ancillary data from a series of buffers and concatenating it into\na single message.  The buffers argument specifies the non-ancillary\ndata as an iterable of buffer-compatible objects (e.g. bytes objects).\nThe ancdata argument specifies the ancillary data (control messages)\nas an iterable of zero or more tuples (cmsg_level, cmsg_type,\ncmsg_data), where cmsg_level and cmsg_type are integers specifying the\nprotocol level and protocol-specific type respectively, and cmsg_data\nis a buffer-compatible object holding the associated data.  The flags\nargument defaults to 0 and has the same meaning as for send().  If\naddress is supplied and not None, it sets a destination address for\nthe message.  The return value is the number of bytes of non-ancillary\ndata sent.";
# 3709 "socketmodule.c"
static PyObject *
sock_shutdown(PySocketSockObject *s, PyObject *arg)
{
    int how;
    int res;

    how = _PyLong_AsInt(arg);
    if (how == -1 && PyErr_Occurred())
        return ((void *)0);
    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = shutdown(s->sock_fd, how);
    PyEval_RestoreThread(_save); }
    if (res < 0)
        return s->errorhandler();
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static char shutdown_doc[] = "shutdown(flag)\n\nShut down the reading side of the socket (flag == SHUT_RD), the writing side\nof the socket (flag == SHUT_WR), or both ends (flag == SHUT_RDWR).";
# 3808 "socketmodule.c"
static PyMethodDef sock_methods[] = {
    {"_accept", (PyCFunction)sock_accept, 0x0004,
                      accept_doc},
    {"bind", (PyCFunction)sock_bind, 0x0008,
                      bind_doc},
    {"close", (PyCFunction)sock_close, 0x0004,
                      close_doc},
    {"connect", (PyCFunction)sock_connect, 0x0008,
                      connect_doc},
    {"connect_ex", (PyCFunction)sock_connect_ex, 0x0008,
                      connect_ex_doc},
    {"detach", (PyCFunction)sock_detach, 0x0004,
                      detach_doc},
    {"fileno", (PyCFunction)sock_fileno, 0x0004,
                      fileno_doc},

    {"getpeername", (PyCFunction)sock_getpeername,
                      0x0004, getpeername_doc},

    {"getsockname", (PyCFunction)sock_getsockname,
                      0x0004, getsockname_doc},
    {"getsockopt", (PyCFunction)sock_getsockopt, 0x0001,
                      getsockopt_doc},
# 3839 "socketmodule.c"
    {"listen", (PyCFunction)sock_listen, 0x0008,
                      listen_doc},
    {"recv", (PyCFunction)sock_recv, 0x0001,
                      recv_doc},
    {"recv_into", (PyCFunction)sock_recv_into, 0x0001 | 0x0002,
                      recv_into_doc},
    {"recvfrom", (PyCFunction)sock_recvfrom, 0x0001,
                      recvfrom_doc},
    {"recvfrom_into", (PyCFunction)sock_recvfrom_into, 0x0001 | 0x0002,
                      recvfrom_into_doc},
    {"send", (PyCFunction)sock_send, 0x0001,
                      send_doc},
    {"sendall", (PyCFunction)sock_sendall, 0x0001,
                      sendall_doc},
    {"sendto", (PyCFunction)sock_sendto, 0x0001,
                      sendto_doc},
    {"setblocking", (PyCFunction)sock_setblocking, 0x0008,
                      setblocking_doc},
    {"settimeout", (PyCFunction)sock_settimeout, 0x0008,
                      settimeout_doc},
    {"gettimeout", (PyCFunction)sock_gettimeout, 0x0004,
                      gettimeout_doc},
    {"setsockopt", (PyCFunction)sock_setsockopt, 0x0001,
                      setsockopt_doc},
    {"shutdown", (PyCFunction)sock_shutdown, 0x0008,
                      shutdown_doc},

    {"recvmsg", (PyCFunction)sock_recvmsg, 0x0001,
                      recvmsg_doc},
    {"recvmsg_into", (PyCFunction)sock_recvmsg_into, 0x0001,
                      recvmsg_into_doc,},
    {"sendmsg", (PyCFunction)sock_sendmsg, 0x0001,
                      sendmsg_doc},

    {((void *)0), ((void *)0)}
};


static PyMemberDef sock_memberlist[] = {
       {"family", 1, __builtin_offsetof (PySocketSockObject, sock_family), 1, "the socket family"},
       {"type", 1, __builtin_offsetof (PySocketSockObject, sock_type), 1, "the socket type"},
       {"proto", 1, __builtin_offsetof (PySocketSockObject, sock_proto), 1, "the socket protocol"},
       {"timeout", 4, __builtin_offsetof (PySocketSockObject, sock_timeout), 1, "the socket timeout"},
       {0},
};




static void
sock_dealloc(PySocketSockObject *s)
{
    if (s->sock_fd != -1) {
        PyObject *exc, *val, *tb;
        Py_ssize_t old_refcount = (((PyObject*)(s))->ob_refcnt);
        ++(((PyObject*)(s))->ob_refcnt);
        PyErr_Fetch(&exc, &val, &tb);
        if (PyErr_WarnFormat(PyExc_ResourceWarning, 1,
                             "unclosed %R", s))

            if (PyErr_ExceptionMatches(PyExc_Warning))
                PyErr_WriteUnraisable((PyObject *) s);
        PyErr_Restore(exc, val, tb);
        (void) close(s->sock_fd);
        (((PyObject*)(s))->ob_refcnt) = old_refcount;
    }
    (((PyObject*)(s))->ob_type)->tp_free((PyObject *)s);
}


static PyObject *
sock_repr(PySocketSockObject *s)
{
# 3923 "socketmodule.c"
    return PyUnicode_FromFormat(
        "<socket object, fd=%ld, family=%d, type=%d, proto=%d>",
        (long)s->sock_fd, s->sock_family,
        s->sock_type,
        s->sock_proto);
}




static PyObject *
sock_new(PyTypeObject *type, PyObject *args, PyObject *kwds)
{
    PyObject *new;

    new = type->tp_alloc(type, 0);
    if (new != ((void *)0)) {
        ((PySocketSockObject *)new)->sock_fd = -1;
        ((PySocketSockObject *)new)->sock_timeout = -1.0;
        ((PySocketSockObject *)new)->errorhandler = &set_error;
    }
    return new;
}





static int
sock_initobj(PyObject *self, PyObject *args, PyObject *kwds)
{
    PySocketSockObject *s = (PySocketSockObject *)self;
    PyObject *fdobj = ((void *)0);
    SOCKET_T fd = (-1);
    int family = 2, type = 1, proto = 0;
    static char *keywords[] = {"family", "type", "proto", "fileno", 0};

    if (!PyArg_ParseTupleAndKeywords(args, kwds,
                                     "|iiiO:socket", keywords,
                                     &family, &type, &proto, &fdobj))
        return -1;

    if (fdobj != ((void *)0) && fdobj != (&_Py_NoneStruct)) {
# 3991 "socketmodule.c"
        {
            fd = (SOCKET_T)PyLong_AsLong(fdobj);
            if (fd == (SOCKET_T)(-1) && PyErr_Occurred())
                return -1;
            if (fd == (-1)) {
                PyErr_SetString(PyExc_ValueError,
                                "can't use invalid socket value");
                return -1;
            }
        }
    }
    else {
        { PyThreadState *_save; _save = PyEval_SaveThread();
        fd = socket(family, type, proto);
        PyEval_RestoreThread(_save); }

        if (fd == (-1)) {
            set_error();
            return -1;
        }
    }
    init_sockobject(s, fd, family, type, proto);

    return 0;

}




static PyTypeObject sock_type = {
    { { 1, 0 }, 0 },
    "_socket.socket",
    sizeof(PySocketSockObject),
    0,
    (destructor)sock_dealloc,
    0,
    0,
    0,
    0,
    (reprfunc)sock_repr,
    0,
    0,
    0,
    0,
    0,
    0,
    PyObject_GenericGetAttr,
    0,
    0,
    ( 0 | (1L<<18) | 0) | (1L<<10),
    sock_doc,
    0,
    0,
    0,
    0,
    0,
    0,
    sock_methods,
    sock_memberlist,
    0,
    0,
    0,
    0,
    0,
    0,
    sock_initobj,
    PyType_GenericAlloc,
    sock_new,
    PyObject_Free,
};





static PyObject *
socket_gethostname(PyObject *self, PyObject *unused)
{
# 4105 "socketmodule.c"
    char buf[1024];
    int res;
    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = gethostname(buf, (int) sizeof buf - 1);
    PyEval_RestoreThread(_save); }
    if (res < 0)
        return set_error();
    buf[sizeof buf - 1] = '\0';
    return PyUnicode_FromString(buf);

}

static char gethostname_doc[] = "gethostname() -> string\n\nReturn the current host name.";





static char sethostname_doc[] = "sethostname(name)\n\nSets the hostname to name.";



static PyObject *
socket_sethostname(PyObject *self, PyObject *args)
{
    PyObject *hnobj;
    Py_buffer buf;
    int res, flag = 0;

    if (!PyArg_ParseTuple(args, "S:sethostname", &hnobj)) {
        PyErr_Clear();
        if (!PyArg_ParseTuple(args, "O&:sethostname",
                PyUnicode_FSConverter, &hnobj))
            return ((void *)0);
        flag = 1;
    }
    res = PyObject_GetBuffer(hnobj, &buf, 0);
    if (!res) {
        res = sethostname(buf.buf, buf.len);
        PyBuffer_Release(&buf);
    }
    if (flag)
        do { if ( --((PyObject*)(hnobj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(hnobj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(hnobj)))); } while (0);
    if (res)
        return set_error();
    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}





static PyObject *
socket_gethostbyname(PyObject *self, PyObject *args)
{
    char *name;
    sock_addr_t addrbuf;
    PyObject *ret = ((void *)0);

    if (!PyArg_ParseTuple(args, "et:gethostbyname", "idna", &name))
        return ((void *)0);
    if (setipaddr(name, (&((&addrbuf)->sa)), sizeof(addrbuf), 2) < 0)
        goto finally;
    ret = makeipaddr((&((&addrbuf)->sa)), sizeof(struct sockaddr_in));
finally:
    PyMem_Free(name);
    return ret;
}

static char gethostbyname_doc[] = "gethostbyname(host) -> address\n\nReturn the IP address (a string of the form '255.255.255.255') for a host.";







static PyObject *
gethost_common(struct hostent *h, struct sockaddr *addr, int alen, int af)
{
    char **pch;
    PyObject *rtn_tuple = (PyObject *)((void *)0);
    PyObject *name_list = (PyObject *)((void *)0);
    PyObject *addr_list = (PyObject *)((void *)0);
    PyObject *tmp;

    if (h == ((void *)0)) {

        set_herror(h_errno);
        return ((void *)0);
    }

    if (h->h_addrtype != af) {

        (*__error()) = 47;
        PyErr_SetFromErrno(PyExc_OSError);
        return ((void *)0);
    }

    switch (af) {

    case 2:
        if (alen < sizeof(struct sockaddr_in))
            return ((void *)0);
        break;


    case 30:
        if (alen < sizeof(struct sockaddr_in6))
            return ((void *)0);
        break;


    }

    if ((name_list = PyList_New(0)) == ((void *)0))
        goto err;

    if ((addr_list = PyList_New(0)) == ((void *)0))
        goto err;


    if (h->h_aliases) {
        for (pch = h->h_aliases; *pch != ((void *)0); pch++) {
            int status;
            tmp = PyUnicode_FromString(*pch);
            if (tmp == ((void *)0))
                goto err;

            status = PyList_Append(name_list, tmp);
            do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0);

            if (status)
                goto err;
        }
    }

    for (pch = h->h_addr_list; *pch != ((void *)0); pch++) {
        int status;

        switch (af) {

        case 2:
            {
            struct sockaddr_in sin;
            ((__builtin_object_size (&sin, 0) != (size_t) -1) ? __builtin___memset_chk (&sin, 0, sizeof(sin), __builtin_object_size (&sin, 0)) : __inline_memset_chk (&sin, 0, sizeof(sin)));
            sin.sin_family = af;

            sin.sin_len = sizeof(sin);

            ((__builtin_object_size (&sin.sin_addr, 0) != (size_t) -1) ? __builtin___memcpy_chk (&sin.sin_addr, *pch, sizeof(sin.sin_addr), __builtin_object_size (&sin.sin_addr, 0)) : __inline_memcpy_chk (&sin.sin_addr, *pch, sizeof(sin.sin_addr)));
            tmp = makeipaddr((struct sockaddr *)&sin, sizeof(sin));

            if (pch == h->h_addr_list && alen >= sizeof(sin))
                ((__builtin_object_size ((char *) addr, 0) != (size_t) -1) ? __builtin___memcpy_chk ((char *) addr, &sin, sizeof(sin), __builtin_object_size ((char *) addr, 0)) : __inline_memcpy_chk ((char *) addr, &sin, sizeof(sin)));
            break;
            }


        case 30:
            {
            struct sockaddr_in6 sin6;
            ((__builtin_object_size (&sin6, 0) != (size_t) -1) ? __builtin___memset_chk (&sin6, 0, sizeof(sin6), __builtin_object_size (&sin6, 0)) : __inline_memset_chk (&sin6, 0, sizeof(sin6)));
            sin6.sin6_family = af;

            sin6.sin6_len = sizeof(sin6);

            ((__builtin_object_size (&sin6.sin6_addr, 0) != (size_t) -1) ? __builtin___memcpy_chk (&sin6.sin6_addr, *pch, sizeof(sin6.sin6_addr), __builtin_object_size (&sin6.sin6_addr, 0)) : __inline_memcpy_chk (&sin6.sin6_addr, *pch, sizeof(sin6.sin6_addr)));
            tmp = makeipaddr((struct sockaddr *)&sin6,
                sizeof(sin6));

            if (pch == h->h_addr_list && alen >= sizeof(sin6))
                ((__builtin_object_size ((char *) addr, 0) != (size_t) -1) ? __builtin___memcpy_chk ((char *) addr, &sin6, sizeof(sin6), __builtin_object_size ((char *) addr, 0)) : __inline_memcpy_chk ((char *) addr, &sin6, sizeof(sin6)));
            break;
            }


        default:
            PyErr_SetString(PyExc_OSError,
                            "unsupported address family");
            return ((void *)0);
        }

        if (tmp == ((void *)0))
            goto err;

        status = PyList_Append(addr_list, tmp);
        do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0);

        if (status)
            goto err;
    }

    rtn_tuple = Py_BuildValue("sOO", h->h_name, name_list, addr_list);

 err:
    do { if ((name_list) == ((void *)0)) ; else do { if ( --((PyObject*)(name_list))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(name_list)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(name_list)))); } while (0); } while (0);
    do { if ((addr_list) == ((void *)0)) ; else do { if ( --((PyObject*)(addr_list))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(addr_list)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(addr_list)))); } while (0); } while (0);
    return rtn_tuple;
}





static PyObject *
socket_gethostbyname_ex(PyObject *self, PyObject *args)
{
    char *name;
    struct hostent *h;
    sock_addr_t addr;
    struct sockaddr *sa;
    PyObject *ret = ((void *)0);
# 4332 "socketmodule.c"
    if (!PyArg_ParseTuple(args, "et:gethostbyname_ex", "idna", &name))
        return ((void *)0);
    if (setipaddr(name, (&((&addr)->sa)), sizeof(addr), 2) < 0)
        goto finally;
    { PyThreadState *_save; _save = PyEval_SaveThread();
# 4350 "socketmodule.c"
    PyThread_acquire_lock(netdb_lock, 1);

    h = gethostbyname(name);

    PyEval_RestoreThread(_save); }




    sa = (&((&addr)->sa));
    ret = gethost_common(h, (&((&addr)->sa)), sizeof(addr),
                         sa->sa_family);

    PyThread_release_lock(netdb_lock);

finally:
    PyMem_Free(name);
    return ret;
}

static char ghbn_ex_doc[] = "gethostbyname_ex(host) -> (name, aliaslist, addresslist)\n\nReturn the true host name, a list of aliases, and a list of IP addresses,\nfor a host.  The host argument is a string giving a host name or IP number.";
# 4380 "socketmodule.c"
static PyObject *
socket_gethostbyaddr(PyObject *self, PyObject *args)
{
    sock_addr_t addr;
    struct sockaddr *sa = (&((&addr)->sa));
    char *ip_num;
    struct hostent *h;
    PyObject *ret = ((void *)0);
# 4405 "socketmodule.c"
    char *ap;
    int al;
    int af;

    if (!PyArg_ParseTuple(args, "et:gethostbyaddr", "idna", &ip_num))
        return ((void *)0);
    af = 0;
    if (setipaddr(ip_num, sa, sizeof(addr), af) < 0)
        goto finally;
    af = sa->sa_family;
    ap = ((void *)0);

    switch (af) {
    case 2:
        ap = (char *)&((struct sockaddr_in *)sa)->sin_addr;
        al = sizeof(((struct sockaddr_in *)sa)->sin_addr);
        break;

    case 30:
        ap = (char *)&((struct sockaddr_in6 *)sa)->sin6_addr;
        al = sizeof(((struct sockaddr_in6 *)sa)->sin6_addr);
        break;

    default:
        PyErr_SetString(PyExc_OSError, "unsupported address family");
        goto finally;
    }
    { PyThreadState *_save; _save = PyEval_SaveThread();
# 4448 "socketmodule.c"
    PyThread_acquire_lock(netdb_lock, 1);

    h = gethostbyaddr(ap, al, af);

    PyEval_RestoreThread(_save); }
    ret = gethost_common(h, (&((&addr)->sa)), sizeof(addr), af);

    PyThread_release_lock(netdb_lock);

finally:
    PyMem_Free(ip_num);
    return ret;
}

static char gethostbyaddr_doc[] = "gethostbyaddr(host) -> (name, aliaslist, addresslist)\n\nReturn the true host name, a list of aliases, and a list of IP addresses,\nfor a host.  The host argument is a string giving a host name or IP number.";
# 4474 "socketmodule.c"
static PyObject *
socket_getservbyname(PyObject *self, PyObject *args)
{
    char *name, *proto=((void *)0);
    struct servent *sp;
    if (!PyArg_ParseTuple(args, "s|s:getservbyname", &name, &proto))
        return ((void *)0);
    { PyThreadState *_save; _save = PyEval_SaveThread();
    sp = getservbyname(name, proto);
    PyEval_RestoreThread(_save); }
    if (sp == ((void *)0)) {
        PyErr_SetString(PyExc_OSError, "service/proto not found");
        return ((void *)0);
    }
    return PyLong_FromLong((long) ((__uint16_t)(__builtin_constant_p(sp->s_port) ? ((__uint16_t)((((__uint16_t)(sp->s_port) & 0xff00) >> 8) | (((__uint16_t)(sp->s_port) & 0x00ff) << 8))) : _OSSwapInt16(sp->s_port))));
}

static char getservbyname_doc[] = "getservbyname(servicename[, protocolname]) -> integer\n\nReturn a port number from a service name and protocol name.\nThe optional protocol name, if given, should be 'tcp' or 'udp',\notherwise any protocol will match.";
# 4504 "socketmodule.c"
static PyObject *
socket_getservbyport(PyObject *self, PyObject *args)
{
    int port;
    char *proto=((void *)0);
    struct servent *sp;
    if (!PyArg_ParseTuple(args, "i|s:getservbyport", &port, &proto))
        return ((void *)0);
    if (port < 0 || port > 0xffff) {
        PyErr_SetString(
            PyExc_OverflowError,
            "getservbyport: port must be 0-65535.");
        return ((void *)0);
    }
    { PyThreadState *_save; _save = PyEval_SaveThread();
    sp = getservbyport(((__uint16_t)(__builtin_constant_p((short)port) ? ((__uint16_t)((((__uint16_t)((short)port) & 0xff00) >> 8) | (((__uint16_t)((short)port) & 0x00ff) << 8))) : _OSSwapInt16((short)port))), proto);
    PyEval_RestoreThread(_save); }
    if (sp == ((void *)0)) {
        PyErr_SetString(PyExc_OSError, "port/proto not found");
        return ((void *)0);
    }
    return PyUnicode_FromString(sp->s_name);
}

static char getservbyport_doc[] = "getservbyport(port[, protocolname]) -> string\n\nReturn the service name from a port number and protocol name.\nThe optional protocol name, if given, should be 'tcp' or 'udp',\notherwise any protocol will match.";
# 4540 "socketmodule.c"
static PyObject *
socket_getprotobyname(PyObject *self, PyObject *args)
{
    char *name;
    struct protoent *sp;
    if (!PyArg_ParseTuple(args, "s:getprotobyname", &name))
        return ((void *)0);
    { PyThreadState *_save; _save = PyEval_SaveThread();
    sp = getprotobyname(name);
    PyEval_RestoreThread(_save); }
    if (sp == ((void *)0)) {
        PyErr_SetString(PyExc_OSError, "protocol not found");
        return ((void *)0);
    }
    return PyLong_FromLong((long) sp->p_proto);
}

static char getprotobyname_doc[] = "getprotobyname(name) -> integer\n\nReturn the protocol number for the named protocol.  (Rarely used.)";
# 4566 "socketmodule.c"
static PyObject *
socket_dup(PyObject *self, PyObject *fdobj)
{
    SOCKET_T fd, newfd;
    PyObject *newfdobj;


    fd = (SOCKET_T)PyLong_AsLong(fdobj);
    if (fd == (SOCKET_T)(-1) && PyErr_Occurred())
        return ((void *)0);

    newfd = dup(fd);
    if (newfd == (-1))
        return set_error();

    newfdobj = PyLong_FromLong((SOCKET_T)(newfd));
    if (newfdobj == ((void *)0))
        close(newfd);
    return newfdobj;
}

static char dup_doc[] = "dup(integer) -> integer\n\nDuplicate an integer socket file descriptor.  This is like os.dup(), but for\nsockets; on some platforms os.dup() won't work for socket file descriptors.";
# 4601 "socketmodule.c"
static PyObject *
socket_socketpair(PyObject *self, PyObject *args)
{
    PySocketSockObject *s0 = ((void *)0), *s1 = ((void *)0);
    SOCKET_T sv[2];
    int family, type = 1, proto = 0;
    PyObject *res = ((void *)0);


    family = 1;



    if (!PyArg_ParseTuple(args, "|iii:socketpair",
                          &family, &type, &proto))
        return ((void *)0);

    if (socketpair(family, type, proto, sv) < 0)
        return set_error();
    s0 = new_sockobject(sv[0], family, type, proto);
    if (s0 == ((void *)0))
        goto finally;
    s1 = new_sockobject(sv[1], family, type, proto);
    if (s1 == ((void *)0))
        goto finally;
    res = PyTuple_Pack(2, s0, s1);

finally:
    if (res == ((void *)0)) {
        if (s0 == ((void *)0))
            close(sv[0]);
        if (s1 == ((void *)0))
            close(sv[1]);
    }
    do { if ((s0) == ((void *)0)) ; else do { if ( --((PyObject*)(s0))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(s0)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(s0)))); } while (0); } while (0);
    do { if ((s1) == ((void *)0)) ; else do { if ( --((PyObject*)(s1))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(s1)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(s1)))); } while (0); } while (0);
    return res;
}

static char socketpair_doc[] = "socketpair([family[, type[, proto]]]) -> (socket object, socket object)\n\nCreate a pair of socket objects from the sockets returned by the platform\nsocketpair() function.\nThe arguments are the same as for socket() except the default family is\nAF_UNIX if defined on the platform; otherwise, the default is AF_INET.";
# 4651 "socketmodule.c"
static PyObject *
socket_ntohs(PyObject *self, PyObject *args)
{
    int x1, x2;

    if (!PyArg_ParseTuple(args, "i:ntohs", &x1)) {
        return ((void *)0);
    }
    if (x1 < 0) {
        PyErr_SetString(PyExc_OverflowError,
            "can't convert negative number to unsigned long");
        return ((void *)0);
    }
    x2 = (unsigned int)((__uint16_t)(__builtin_constant_p((unsigned short)x1) ? ((__uint16_t)((((__uint16_t)((unsigned short)x1) & 0xff00) >> 8) | (((__uint16_t)((unsigned short)x1) & 0x00ff) << 8))) : _OSSwapInt16((unsigned short)x1)));
    return PyLong_FromLong(x2);
}

static char ntohs_doc[] = "ntohs(integer) -> integer\n\nConvert a 16-bit integer from network to host byte order.";





static PyObject *
socket_ntohl(PyObject *self, PyObject *arg)
{
    unsigned long x;

    if (((((((PyObject*)(arg))->ob_type))->tp_flags & ((1L<<24))) != 0)) {
        x = PyLong_AsUnsignedLong(arg);
        if (x == (unsigned long) -1 && PyErr_Occurred())
            return ((void *)0);

        {
            unsigned long y;

            y = x & 0xFFFFFFFFUL;
            if (y ^ x)
                return PyErr_Format(PyExc_OverflowError,
                            "long int larger than 32 bits");
            x = y;
        }

    }
    else
        return PyErr_Format(PyExc_TypeError,
                            "expected int/long, %s found",
                            (((PyObject*)(arg))->ob_type)->tp_name);
    if (x == (unsigned long) -1 && PyErr_Occurred())
        return ((void *)0);
    return PyLong_FromUnsignedLong((__builtin_constant_p(x) ? ((__uint32_t)((((__uint32_t)(x) & 0xff000000) >> 24) | (((__uint32_t)(x) & 0x00ff0000) >> 8) | (((__uint32_t)(x) & 0x0000ff00) << 8) | (((__uint32_t)(x) & 0x000000ff) << 24))) : _OSSwapInt32(x)));
}

static char ntohl_doc[] = "ntohl(integer) -> integer\n\nConvert a 32-bit integer from network to host byte order.";





static PyObject *
socket_htons(PyObject *self, PyObject *args)
{
    int x1, x2;

    if (!PyArg_ParseTuple(args, "i:htons", &x1)) {
        return ((void *)0);
    }
    if (x1 < 0) {
        PyErr_SetString(PyExc_OverflowError,
            "can't convert negative number to unsigned long");
        return ((void *)0);
    }
    x2 = (unsigned int)((__uint16_t)(__builtin_constant_p((unsigned short)x1) ? ((__uint16_t)((((__uint16_t)((unsigned short)x1) & 0xff00) >> 8) | (((__uint16_t)((unsigned short)x1) & 0x00ff) << 8))) : _OSSwapInt16((unsigned short)x1)));
    return PyLong_FromLong(x2);
}

static char htons_doc[] = "htons(integer) -> integer\n\nConvert a 16-bit integer from host to network byte order.";





static PyObject *
socket_htonl(PyObject *self, PyObject *arg)
{
    unsigned long x;

    if (((((((PyObject*)(arg))->ob_type))->tp_flags & ((1L<<24))) != 0)) {
        x = PyLong_AsUnsignedLong(arg);
        if (x == (unsigned long) -1 && PyErr_Occurred())
            return ((void *)0);

        {
            unsigned long y;

            y = x & 0xFFFFFFFFUL;
            if (y ^ x)
                return PyErr_Format(PyExc_OverflowError,
                            "long int larger than 32 bits");
            x = y;
        }

    }
    else
        return PyErr_Format(PyExc_TypeError,
                            "expected int/long, %s found",
                            (((PyObject*)(arg))->ob_type)->tp_name);
    return PyLong_FromUnsignedLong((__builtin_constant_p((unsigned long)x) ? ((__uint32_t)((((__uint32_t)((unsigned long)x) & 0xff000000) >> 24) | (((__uint32_t)((unsigned long)x) & 0x00ff0000) >> 8) | (((__uint32_t)((unsigned long)x) & 0x0000ff00) << 8) | (((__uint32_t)((unsigned long)x) & 0x000000ff) << 24))) : _OSSwapInt32((unsigned long)x)));
}

static char htonl_doc[] = "htonl(integer) -> integer\n\nConvert a 32-bit integer from host to network byte order.";






static char inet_aton_doc[] = "inet_aton(string) -> bytes giving packed 32-bit IP representation\n\nConvert an IP address in string format (123.45.67.89) to the 32-bit packed\nbinary format used in low-level network functions.";





static PyObject*
socket_inet_aton(PyObject *self, PyObject *args)
{




    struct in_addr buf;







    unsigned int packed_addr;

    char *ip_addr;

    if (!PyArg_ParseTuple(args, "s:inet_aton", &ip_addr))
        return ((void *)0);





    if (inet_aton != ((void *)0)) {

    if (inet_aton(ip_addr, &buf))
        return PyBytes_FromStringAndSize((char *)(&buf),
                                          sizeof(buf));

    PyErr_SetString(PyExc_OSError,
                    "illegal IP address string passed to inet_aton");
    return ((void *)0);


   } else {
# 4820 "socketmodule.c"
    if (strcmp(ip_addr, "255.255.255.255") == 0) {
        packed_addr = 0xFFFFFFFF;
    } else {

        packed_addr = inet_addr(ip_addr);

        if (packed_addr == 0xffffffff) {
            PyErr_SetString(PyExc_OSError,
                "illegal IP address string passed to inet_aton");
            return ((void *)0);
        }
    }
    return PyBytes_FromStringAndSize((char *) &packed_addr,
                                      sizeof(packed_addr));


   }



}

static char inet_ntoa_doc[] = "inet_ntoa(packed_ip) -> ip_address_string\n\nConvert an IP address from 32-bit packed binary format to string format";




static PyObject*
socket_inet_ntoa(PyObject *self, PyObject *args)
{
    char *packed_str;
    int addr_len;
    struct in_addr packed_addr;

    if (!PyArg_ParseTuple(args, "y#:inet_ntoa", &packed_str, &addr_len)) {
        return ((void *)0);
    }

    if (addr_len != sizeof(packed_addr)) {
        PyErr_SetString(PyExc_OSError,
            "packed IP wrong length for inet_ntoa");
        return ((void *)0);
    }

    ((__builtin_object_size (&packed_addr, 0) != (size_t) -1) ? __builtin___memcpy_chk (&packed_addr, packed_str, addr_len, __builtin_object_size (&packed_addr, 0)) : __inline_memcpy_chk (&packed_addr, packed_str, addr_len));

    return PyUnicode_FromString(inet_ntoa(packed_addr));
}



static char inet_pton_doc[] = "inet_pton(af, ip) -> packed IP address string\n\nConvert an IP address from string format to a packed string suitable\nfor use with low-level network functions.";





static PyObject *
socket_inet_pton(PyObject *self, PyObject *args)
{
    int af;
    char* ip;
    int retval;

    char packed[((sizeof(struct in_addr)) < (sizeof(struct in6_addr)) ? (sizeof(struct in6_addr)) : (sizeof(struct in_addr)))];



    if (!PyArg_ParseTuple(args, "is:inet_pton", &af, &ip)) {
        return ((void *)0);
    }
# 4900 "socketmodule.c"
    retval = inet_pton(af, ip, packed);
    if (retval < 0) {
        PyErr_SetFromErrno(PyExc_OSError);
        return ((void *)0);
    } else if (retval == 0) {
        PyErr_SetString(PyExc_OSError,
            "illegal IP address string passed to inet_pton");
        return ((void *)0);
    } else if (af == 2) {
        return PyBytes_FromStringAndSize(packed,
                                          sizeof(struct in_addr));

    } else if (af == 30) {
        return PyBytes_FromStringAndSize(packed,
                                          sizeof(struct in6_addr));

    } else {
        PyErr_SetString(PyExc_OSError, "unknown address family");
        return ((void *)0);
    }
}

static char inet_ntop_doc[] = "inet_ntop(af, packed_ip) -> string formatted IP address\n\nConvert a packed IP address of the given family to string format.";




static PyObject *
socket_inet_ntop(PyObject *self, PyObject *args)
{
    int af;
    char* packed;
    int len;
    const char* retval;

    char ip[((16) < (46) ? (46) : (16)) + 1];





    ((__builtin_object_size ((void *) &ip[0], 0) != (size_t) -1) ? __builtin___memset_chk ((void *) &ip[0], '\0', sizeof(ip), __builtin_object_size ((void *) &ip[0], 0)) : __inline_memset_chk ((void *) &ip[0], '\0', sizeof(ip)));

    if (!PyArg_ParseTuple(args, "iy#:inet_ntop", &af, &packed, &len)) {
        return ((void *)0);
    }

    if (af == 2) {
        if (len != sizeof(struct in_addr)) {
            PyErr_SetString(PyExc_ValueError,
                "invalid length of packed IP address string");
            return ((void *)0);
        }

    } else if (af == 30) {
        if (len != sizeof(struct in6_addr)) {
            PyErr_SetString(PyExc_ValueError,
                "invalid length of packed IP address string");
            return ((void *)0);
        }

    } else {
        PyErr_Format(PyExc_ValueError,
            "unknown address family %d", af);
        return ((void *)0);
    }

    retval = inet_ntop(af, packed, ip, sizeof(ip));
    if (!retval) {
        PyErr_SetFromErrno(PyExc_OSError);
        return ((void *)0);
    } else {
        return PyUnicode_FromString(retval);
    }


    PyErr_SetString(PyExc_RuntimeError, "invalid handling of inet_ntop");
    return ((void *)0);
}






static PyObject *
socket_getaddrinfo(PyObject *self, PyObject *args, PyObject* kwargs)
{
    static char* kwnames[] = {"host", "port", "family", "type", "proto",
                              "flags", 0};
    struct addrinfo hints, *res;
    struct addrinfo *res0 = ((void *)0);
    PyObject *hobj = ((void *)0);
    PyObject *pobj = (PyObject *)((void *)0);
    char pbuf[30];
    char *hptr, *pptr;
    int family, socktype, protocol, flags;
    int error;
    PyObject *all = (PyObject *)((void *)0);
    PyObject *idna = ((void *)0);

    family = socktype = protocol = flags = 0;
    family = 0;
    if (!PyArg_ParseTupleAndKeywords(args, kwargs, "OO|iiii:getaddrinfo",
                          kwnames, &hobj, &pobj, &family, &socktype,
                          &protocol, &flags)) {
        return ((void *)0);
    }
    if (hobj == (&_Py_NoneStruct)) {
        hptr = ((void *)0);
    } else if (((((((PyObject*)(hobj))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        static _Py_Identifier PyId_encode = { 0, "encode", 0 };

        idna = _PyObject_CallMethodId(hobj, &PyId_encode, "s", "idna");
        if (!idna)
            return ((void *)0);
        (__builtin_expect(!(((((((PyObject*)(idna))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "socketmodule.c", 5016, "PyBytes_Check(idna)") : (void)0);
        hptr = ((__builtin_expect(!(((((((PyObject*)(idna))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "socketmodule.c", 5017, "PyBytes_Check(idna)") : (void)0), (((PyBytesObject *)(idna))->ob_sval));
    } else if (((((((PyObject*)(hobj))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
        hptr = PyBytes_AsString(hobj);
    } else {
        PyErr_SetString(PyExc_TypeError,
                        "getaddrinfo() argument 1 must be string or None");
        return ((void *)0);
    }
    if (((((PyObject*)(pobj))->ob_type) == &PyLong_Type)) {
        long value = PyLong_AsLong(pobj);
        if (value == -1 && PyErr_Occurred())
            goto err;
        PyOS_snprintf(pbuf, sizeof(pbuf), "%ld", value);
        pptr = pbuf;
    } else if (((((((PyObject*)(pobj))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        pptr = PyUnicode_AsUTF8(pobj);
        if (pptr == ((void *)0))
            goto err;
    } else if (((((((PyObject*)(pobj))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
        pptr = ((__builtin_expect(!(((((((PyObject*)(pobj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "socketmodule.c", 5036, "PyBytes_Check(pobj)") : (void)0), (((PyBytesObject *)(pobj))->ob_sval));
    } else if (pobj == (&_Py_NoneStruct)) {
        pptr = (char *)((void *)0);
    } else {
        PyErr_SetString(PyExc_OSError, "Int or String expected");
        goto err;
    }
    ((__builtin_object_size (&hints, 0) != (size_t) -1) ? __builtin___memset_chk (&hints, 0, sizeof(hints), __builtin_object_size (&hints, 0)) : __inline_memset_chk (&hints, 0, sizeof(hints)));
    hints.ai_family = family;
    hints.ai_socktype = socktype;
    hints.ai_protocol = protocol;
    hints.ai_flags = flags;
    { PyThreadState *_save; _save = PyEval_SaveThread();
    PyThread_acquire_lock(netdb_lock, 1);
    error = getaddrinfo(hptr, pptr, &hints, &res0);
    PyEval_RestoreThread(_save); }
    PyThread_release_lock(netdb_lock);
    if (error) {
        set_gaierror(error);
        goto err;
    }

    if ((all = PyList_New(0)) == ((void *)0))
        goto err;
    for (res = res0; res; res = res->ai_next) {
        PyObject *single;
        PyObject *addr =
            makesockaddr(-1, res->ai_addr, res->ai_addrlen, protocol);
        if (addr == ((void *)0))
            goto err;
        single = Py_BuildValue("iiisO", res->ai_family,
            res->ai_socktype, res->ai_protocol,
            res->ai_canonname ? res->ai_canonname : "",
            addr);
        do { if ( --((PyObject*)(addr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(addr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(addr)))); } while (0);
        if (single == ((void *)0))
            goto err;

        if (PyList_Append(all, single))
            goto err;
        do { if ((single) == ((void *)0)) ; else do { if ( --((PyObject*)(single))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(single)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(single)))); } while (0); } while (0);
    }
    do { if ((idna) == ((void *)0)) ; else do { if ( --((PyObject*)(idna))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(idna)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(idna)))); } while (0); } while (0);
    if (res0)
        freeaddrinfo(res0);
    return all;
 err:
    do { if ((all) == ((void *)0)) ; else do { if ( --((PyObject*)(all))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(all)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(all)))); } while (0); } while (0);
    do { if ((idna) == ((void *)0)) ; else do { if ( --((PyObject*)(idna))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(idna)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(idna)))); } while (0); } while (0);
    if (res0)
        freeaddrinfo(res0);
    return (PyObject *)((void *)0);
}

static char getaddrinfo_doc[] = "getaddrinfo(host, port [, family, socktype, proto, flags])\n    -> list of (family, socktype, proto, canonname, sockaddr)\n\nResolve host and port into addrinfo struct.";
# 5099 "socketmodule.c"
static PyObject *
socket_getnameinfo(PyObject *self, PyObject *args)
{
    PyObject *sa = (PyObject *)((void *)0);
    int flags;
    char *hostp;
    int port;
    unsigned int flowinfo, scope_id;
    char hbuf[1025], pbuf[32];
    struct addrinfo hints, *res = ((void *)0);
    int error;
    PyObject *ret = (PyObject *)((void *)0);

    flags = flowinfo = scope_id = 0;
    if (!PyArg_ParseTuple(args, "Oi:getnameinfo", &sa, &flags))
        return ((void *)0);
    if (!((((((PyObject*)(sa))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
        PyErr_SetString(PyExc_TypeError,
                        "getnameinfo() argument 1 must be a tuple");
        return ((void *)0);
    }
    if (!PyArg_ParseTuple(sa, "si|II",
                          &hostp, &port, &flowinfo, &scope_id))
        return ((void *)0);
    if (flowinfo > 0xfffff) {
        PyErr_SetString(PyExc_OverflowError,
                        "getsockaddrarg: flowinfo must be 0-1048575.");
        return ((void *)0);
    }
    PyOS_snprintf(pbuf, sizeof(pbuf), "%d", port);
    ((__builtin_object_size (&hints, 0) != (size_t) -1) ? __builtin___memset_chk (&hints, 0, sizeof(hints), __builtin_object_size (&hints, 0)) : __inline_memset_chk (&hints, 0, sizeof(hints)));
    hints.ai_family = 0;
    hints.ai_socktype = 2;
    hints.ai_flags = 0x00000004;
    { PyThreadState *_save; _save = PyEval_SaveThread();
    PyThread_acquire_lock(netdb_lock, 1);
    error = getaddrinfo(hostp, pbuf, &hints, &res);
    PyEval_RestoreThread(_save); }
    PyThread_release_lock(netdb_lock);
    if (error) {
        set_gaierror(error);
        goto fail;
    }
    if (res->ai_next) {
        PyErr_SetString(PyExc_OSError,
            "sockaddr resolved to multiple addresses");
        goto fail;
    }
    switch (res->ai_family) {
    case 2:
        {
        if ((((PyVarObject*)(sa))->ob_size) != 2) {
            PyErr_SetString(PyExc_OSError,
                "IPv4 sockaddr must be 2 tuple");
            goto fail;
        }
        break;
        }

    case 30:
        {
        struct sockaddr_in6 *sin6;
        sin6 = (struct sockaddr_in6 *)res->ai_addr;
        sin6->sin6_flowinfo = (__builtin_constant_p(flowinfo) ? ((__uint32_t)((((__uint32_t)(flowinfo) & 0xff000000) >> 24) | (((__uint32_t)(flowinfo) & 0x00ff0000) >> 8) | (((__uint32_t)(flowinfo) & 0x0000ff00) << 8) | (((__uint32_t)(flowinfo) & 0x000000ff) << 24))) : _OSSwapInt32(flowinfo));
        sin6->sin6_scope_id = scope_id;
        break;
        }

    }
    error = getnameinfo(res->ai_addr, (socklen_t) res->ai_addrlen,
                    hbuf, sizeof(hbuf), pbuf, sizeof(pbuf), flags);
    if (error) {
        set_gaierror(error);
        goto fail;
    }
    ret = Py_BuildValue("ss", hbuf, pbuf);

fail:
    if (res)
        freeaddrinfo(res);
    return ret;
}

static char getnameinfo_doc[] = "getnameinfo(sockaddr, flags) --> (host, port)\n\nGet host and port for a sockaddr.";







static PyObject *
socket_getdefaulttimeout(PyObject *self)
{
    if (defaulttimeout < 0.0) {
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        return (&_Py_NoneStruct);
    }
    else
        return PyFloat_FromDouble(defaulttimeout);
}

static char getdefaulttimeout_doc[] = "getdefaulttimeout() -> timeout\n\nReturns the default timeout in seconds (float) for new socket objects.\nA value of None indicates that new socket objects have no timeout.\nWhen the socket module is first imported, the default is None.";






static PyObject *
socket_setdefaulttimeout(PyObject *self, PyObject *arg)
{
    double timeout;

    if (arg == (&_Py_NoneStruct))
        timeout = -1.0;
    else {
        timeout = PyFloat_AsDouble(arg);
        if (timeout < 0.0) {
            if (!PyErr_Occurred())
                PyErr_SetString(PyExc_ValueError,
                                "Timeout value out of range");
            return ((void *)0);
        }
    }

    defaulttimeout = timeout;

    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static char setdefaulttimeout_doc[] = "setdefaulttimeout(timeout)\n\nSet the default timeout in seconds (float) for new socket objects.\nA value of None indicates that new socket objects have no timeout.\nWhen the socket module is first imported, the default is None.";
# 5241 "socketmodule.c"
static PyObject *
socket_if_nameindex(PyObject *self, PyObject *arg)
{
    PyObject *list;
    int i;
    struct if_nameindex *ni;

    ni = if_nameindex();
    if (ni == ((void *)0)) {
        PyErr_SetFromErrno(PyExc_OSError);
        return ((void *)0);
    }

    list = PyList_New(0);
    if (list == ((void *)0)) {
        if_freenameindex(ni);
        return ((void *)0);
    }

    for (i = 0; ni[i].if_index != 0 && i < 2147483647; i++) {
        PyObject *ni_tuple = Py_BuildValue("IO&",
                ni[i].if_index, PyUnicode_DecodeFSDefault, ni[i].if_name);

        if (ni_tuple == ((void *)0) || PyList_Append(list, ni_tuple) == -1) {
            do { if ((ni_tuple) == ((void *)0)) ; else do { if ( --((PyObject*)(ni_tuple))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(ni_tuple)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(ni_tuple)))); } while (0); } while (0);
            do { if ( --((PyObject*)(list))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(list)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(list)))); } while (0);
            if_freenameindex(ni);
            return ((void *)0);
        }
        do { if ( --((PyObject*)(ni_tuple))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(ni_tuple)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(ni_tuple)))); } while (0);
    }

    if_freenameindex(ni);
    return list;
}

static char if_nameindex_doc[] = "if_nameindex()\n\nReturns a list of network interface information (index, name) tuples.";




static PyObject *
socket_if_nametoindex(PyObject *self, PyObject *args)
{
    PyObject *oname;
    unsigned long index;

    if (!PyArg_ParseTuple(args, "O&:if_nametoindex",
                          PyUnicode_FSConverter, &oname))
        return ((void *)0);

    index = if_nametoindex(((__builtin_expect(!(((((((PyObject*)(oname))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "socketmodule.c", 5292, "PyBytes_Check(oname)") : (void)0), (((PyBytesObject *)(oname))->ob_sval)));
    do { if ( --((PyObject*)(oname))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(oname)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(oname)))); } while (0);
    if (index == 0) {

        PyErr_SetString(PyExc_OSError, "no interface with this name");
        return ((void *)0);
    }

    return PyLong_FromUnsignedLong(index);
}

static char if_nametoindex_doc[] = "if_nametoindex(if_name)\n\nReturns the interface index corresponding to the interface name if_name.";




static PyObject *
socket_if_indextoname(PyObject *self, PyObject *arg)
{
    unsigned long index;
    char name[16 + 1];

    index = PyLong_AsUnsignedLong(arg);
    if (index == (unsigned long) -1)
        return ((void *)0);

    if (if_indextoname(index, name) == ((void *)0)) {
        PyErr_SetFromErrno(PyExc_OSError);
        return ((void *)0);
    }

    return PyUnicode_DecodeFSDefault(name);
}

static char if_indextoname_doc[] = "if_indextoname(if_index)\n\nReturns the interface name corresponding to the interface index if_index.";
# 5337 "socketmodule.c"
static PyObject *
socket_CMSG_LEN(PyObject *self, PyObject *args)
{
    Py_ssize_t length;
    size_t result;

    if (!PyArg_ParseTuple(args, "n:CMSG_LEN", &length))
        return ((void *)0);
    if (length < 0 || !get_CMSG_LEN(length, &result)) {
        PyErr_Format(PyExc_OverflowError, "CMSG_LEN() argument out of range");
        return ((void *)0);
    }
    return PyLong_FromSize_t(result);
}

static char CMSG_LEN_doc[] = "CMSG_LEN(length) -> control message length\n\nReturn the total length, without trailing padding, of an ancillary\ndata item with associated data of the given length.  This value can\noften be used as the buffer size for recvmsg() to receive a single\nitem of ancillary data, but RFC 3542 requires portable applications to\nuse CMSG_SPACE() and thus include space for padding, even when the\nitem will be the last in the buffer.  Raises OverflowError if length\nis outside the permissible range of values.";
# 5367 "socketmodule.c"
static PyObject *
socket_CMSG_SPACE(PyObject *self, PyObject *args)
{
    Py_ssize_t length;
    size_t result;

    if (!PyArg_ParseTuple(args, "n:CMSG_SPACE", &length))
        return ((void *)0);
    if (length < 0 || !get_CMSG_SPACE(length, &result)) {
        PyErr_SetString(PyExc_OverflowError,
                        "CMSG_SPACE() argument out of range");
        return ((void *)0);
    }
    return PyLong_FromSize_t(result);
}

static char CMSG_SPACE_doc[] = "CMSG_SPACE(length) -> buffer size\n\nReturn the buffer size needed for recvmsg() to receive an ancillary\ndata item with associated data of the given length, along with any\ntrailing padding.  The buffer space needed to receive multiple items\nis the sum of the CMSG_SPACE() values for their associated data\nlengths.  Raises OverflowError if length is outside the permissible\nrange of values.";
# 5398 "socketmodule.c"
static PyMethodDef socket_methods[] = {
    {"gethostbyname", socket_gethostbyname,
     0x0001, gethostbyname_doc},
    {"gethostbyname_ex", socket_gethostbyname_ex,
     0x0001, ghbn_ex_doc},
    {"gethostbyaddr", socket_gethostbyaddr,
     0x0001, gethostbyaddr_doc},
    {"gethostname", socket_gethostname,
     0x0004, gethostname_doc},

    {"sethostname", socket_sethostname,
     0x0001, sethostname_doc},

    {"getservbyname", socket_getservbyname,
     0x0001, getservbyname_doc},
    {"getservbyport", socket_getservbyport,
     0x0001, getservbyport_doc},
    {"getprotobyname", socket_getprotobyname,
     0x0001, getprotobyname_doc},

    {"dup", socket_dup,
     0x0008, dup_doc},


    {"socketpair", socket_socketpair,
     0x0001, socketpair_doc},

    {"ntohs", socket_ntohs,
     0x0001, ntohs_doc},
    {"ntohl", socket_ntohl,
     0x0008, ntohl_doc},
    {"htons", socket_htons,
     0x0001, htons_doc},
    {"htonl", socket_htonl,
     0x0008, htonl_doc},
    {"inet_aton", socket_inet_aton,
     0x0001, inet_aton_doc},
    {"inet_ntoa", socket_inet_ntoa,
     0x0001, inet_ntoa_doc},

    {"inet_pton", socket_inet_pton,
     0x0001, inet_pton_doc},
    {"inet_ntop", socket_inet_ntop,
     0x0001, inet_ntop_doc},

    {"getaddrinfo", (PyCFunction)socket_getaddrinfo,
     0x0001 | 0x0002, getaddrinfo_doc},
    {"getnameinfo", socket_getnameinfo,
     0x0001, getnameinfo_doc},
    {"getdefaulttimeout", (PyCFunction)socket_getdefaulttimeout,
     0x0004, getdefaulttimeout_doc},
    {"setdefaulttimeout", socket_setdefaulttimeout,
     0x0008, setdefaulttimeout_doc},

    {"if_nameindex", socket_if_nameindex,
     0x0004, if_nameindex_doc},
    {"if_nametoindex", socket_if_nametoindex,
     0x0001, if_nametoindex_doc},
    {"if_indextoname", socket_if_indextoname,
     0x0008, if_indextoname_doc},


    {"CMSG_LEN", socket_CMSG_LEN,
     0x0001, CMSG_LEN_doc},

    {"CMSG_SPACE", socket_CMSG_SPACE,
     0x0001, CMSG_SPACE_doc},


    {((void *)0), ((void *)0)}
};
# 5540 "socketmodule.c"
static int
os_init(void)
{
    return 1;
}





static
PySocketModule_APIObject PySocketModuleAPI =
{
    &sock_type,
    ((void *)0),
    ((void *)0)
};
# 5569 "socketmodule.c"
static char socket_doc[] = "Implementation module for socket operations.\n\nSee the socket module for documentation.";




static struct PyModuleDef socketmodule = {
    { { 1, ((void *)0) }, ((void *)0), 0, ((void *)0), },
    "_socket",
    socket_doc,
    -1,
    socket_methods,
    ((void *)0),
    ((void *)0),
    ((void *)0),
    ((void *)0)
};

PyObject*
PyInit__socket(void)
{
    PyObject *m, *has_ipv6;

    if (!os_init())
        return ((void *)0);

    (((PyObject*)(&sock_type))->ob_type) = &PyType_Type;
    m = PyModule_Create2(&socketmodule, 1013);
    if (m == ((void *)0))
        return ((void *)0);

    ( ((PyObject*)(PyExc_OSError))->ob_refcnt++);
    PySocketModuleAPI.error = PyExc_OSError;
    ( ((PyObject*)(PyExc_OSError))->ob_refcnt++);
    PyModule_AddObject(m, "error", PyExc_OSError);
    socket_herror = PyErr_NewException("socket.herror",
                                       PyExc_OSError, ((void *)0));
    if (socket_herror == ((void *)0))
        return ((void *)0);
    ( ((PyObject*)(socket_herror))->ob_refcnt++);
    PyModule_AddObject(m, "herror", socket_herror);
    socket_gaierror = PyErr_NewException("socket.gaierror", PyExc_OSError,
        ((void *)0));
    if (socket_gaierror == ((void *)0))
        return ((void *)0);
    ( ((PyObject*)(socket_gaierror))->ob_refcnt++);
    PyModule_AddObject(m, "gaierror", socket_gaierror);
    socket_timeout = PyErr_NewException("socket.timeout",
                                        PyExc_OSError, ((void *)0));
    if (socket_timeout == ((void *)0))
        return ((void *)0);
    PySocketModuleAPI.timeout_error = socket_timeout;
    ( ((PyObject*)(socket_timeout))->ob_refcnt++);
    PyModule_AddObject(m, "timeout", socket_timeout);
    ( ((PyObject*)((PyObject *)&sock_type))->ob_refcnt++);
    if (PyModule_AddObject(m, "SocketType",
                           (PyObject *)&sock_type) != 0)
        return ((void *)0);
    ( ((PyObject*)((PyObject *)&sock_type))->ob_refcnt++);
    if (PyModule_AddObject(m, "socket",
                           (PyObject *)&sock_type) != 0)
        return ((void *)0);


    has_ipv6 = ((PyObject *) &_Py_TrueStruct);



    ( ((PyObject*)(has_ipv6))->ob_refcnt++);
    PyModule_AddObject(m, "has_ipv6", has_ipv6);


    if (PyModule_AddObject(m, "CAPI",
           PyCapsule_New(&PySocketModuleAPI, "_socket" "." "CAPI", ((void *)0))
                             ) != 0)
        return ((void *)0);



    PyModule_AddIntConstant(m, "AF_UNSPEC", 0);

    PyModule_AddIntConstant(m, "AF_INET", 2);

    PyModule_AddIntConstant(m, "AF_INET6", 30);


    PyModule_AddIntConstant(m, "AF_UNIX", 1);






    PyModule_AddIntConstant(m, "AF_IPX", 23);



    PyModule_AddIntConstant(m, "AF_APPLETALK", 16);
# 5688 "socketmodule.c"
    PyModule_AddIntConstant(m, "AF_INET6", 30);







    PyModule_AddIntConstant(m, "AF_DECnet", 12);
# 5747 "socketmodule.c"
    PyModule_AddIntConstant(m, "AF_ROUTE", 17);
# 5763 "socketmodule.c"
    PyModule_AddIntConstant(m, "AF_SNA", 11);
# 5821 "socketmodule.c"
    PyModule_AddIntConstant(m, "PF_SYSTEM", 32);


    PyModule_AddIntConstant(m, "AF_SYSTEM", 32);
# 5900 "socketmodule.c"
    PyModule_AddIntConstant(m, "SOCK_STREAM", 1);
    PyModule_AddIntConstant(m, "SOCK_DGRAM", 2);

    PyModule_AddIntConstant(m, "SOCK_RAW", 3);
    PyModule_AddIntConstant(m, "SOCK_SEQPACKET", 5);

    PyModule_AddIntConstant(m, "SOCK_RDM", 4);
# 5916 "socketmodule.c"
    PyModule_AddIntConstant(m, "SO_DEBUG", 0x0001);


    PyModule_AddIntConstant(m, "SO_ACCEPTCONN", 0x0002);


    PyModule_AddIntConstant(m, "SO_REUSEADDR", 0x0004);






    PyModule_AddIntConstant(m, "SO_KEEPALIVE", 0x0008);


    PyModule_AddIntConstant(m, "SO_DONTROUTE", 0x0010);


    PyModule_AddIntConstant(m, "SO_BROADCAST", 0x0020);


    PyModule_AddIntConstant(m, "SO_USELOOPBACK", 0x0040);


    PyModule_AddIntConstant(m, "SO_LINGER", 0x0080);


    PyModule_AddIntConstant(m, "SO_OOBINLINE", 0x0100);


    PyModule_AddIntConstant(m, "SO_REUSEPORT", 0x0200);


    PyModule_AddIntConstant(m, "SO_SNDBUF", 0x1001);


    PyModule_AddIntConstant(m, "SO_RCVBUF", 0x1002);


    PyModule_AddIntConstant(m, "SO_SNDLOWAT", 0x1003);


    PyModule_AddIntConstant(m, "SO_RCVLOWAT", 0x1004);


    PyModule_AddIntConstant(m, "SO_SNDTIMEO", 0x1005);


    PyModule_AddIntConstant(m, "SO_RCVTIMEO", 0x1006);


    PyModule_AddIntConstant(m, "SO_ERROR", 0x1007);


    PyModule_AddIntConstant(m, "SO_TYPE", 0x1008);
# 5983 "socketmodule.c"
    PyModule_AddIntConstant(m, "LOCAL_PEERCRED", 0x001);







    PyModule_AddIntConstant(m, "SOMAXCONN", 128);






    PyModule_AddIntConstant(m, "SCM_RIGHTS", 0x01);





    PyModule_AddIntConstant(m, "SCM_CREDS", 0x03);




    PyModule_AddIntConstant(m, "MSG_OOB", 0x1);


    PyModule_AddIntConstant(m, "MSG_PEEK", 0x2);


    PyModule_AddIntConstant(m, "MSG_DONTROUTE", 0x4);


    PyModule_AddIntConstant(m, "MSG_DONTWAIT", 0x80);


    PyModule_AddIntConstant(m, "MSG_EOR", 0x8);


    PyModule_AddIntConstant(m, "MSG_TRUNC", 0x10);


    PyModule_AddIntConstant(m, "MSG_CTRUNC", 0x20);


    PyModule_AddIntConstant(m, "MSG_WAITALL", 0x40);
# 6057 "socketmodule.c"
    PyModule_AddIntConstant(m, "MSG_EOF", 0x100);
# 6068 "socketmodule.c"
    PyModule_AddIntConstant(m, "SOL_SOCKET", 0xffff);




    PyModule_AddIntConstant(m, "SOL_IP", 0);
# 6093 "socketmodule.c"
    PyModule_AddIntConstant(m, "SOL_TCP", 6);




    PyModule_AddIntConstant(m, "SOL_UDP", 17);
# 6144 "socketmodule.c"
    PyModule_AddIntConstant(m, "IPPROTO_IP", 0);




    PyModule_AddIntConstant(m, "IPPROTO_HOPOPTS", 0);


    PyModule_AddIntConstant(m, "IPPROTO_ICMP", 1);




    PyModule_AddIntConstant(m, "IPPROTO_IGMP", 2);


    PyModule_AddIntConstant(m, "IPPROTO_GGP", 3);


    PyModule_AddIntConstant(m, "IPPROTO_IPV4", 4);


    PyModule_AddIntConstant(m, "IPPROTO_IPV6", 41);


    PyModule_AddIntConstant(m, "IPPROTO_IPIP", 4);


    PyModule_AddIntConstant(m, "IPPROTO_TCP", 6);




    PyModule_AddIntConstant(m, "IPPROTO_EGP", 8);


    PyModule_AddIntConstant(m, "IPPROTO_PUP", 12);


    PyModule_AddIntConstant(m, "IPPROTO_UDP", 17);




    PyModule_AddIntConstant(m, "IPPROTO_IDP", 22);


    PyModule_AddIntConstant(m, "IPPROTO_HELLO", 63);


    PyModule_AddIntConstant(m, "IPPROTO_ND", 77);


    PyModule_AddIntConstant(m, "IPPROTO_TP", 29);


    PyModule_AddIntConstant(m, "IPPROTO_IPV6", 41);


    PyModule_AddIntConstant(m, "IPPROTO_ROUTING", 43);


    PyModule_AddIntConstant(m, "IPPROTO_FRAGMENT", 44);


    PyModule_AddIntConstant(m, "IPPROTO_RSVP", 46);


    PyModule_AddIntConstant(m, "IPPROTO_GRE", 47);


    PyModule_AddIntConstant(m, "IPPROTO_ESP", 50);


    PyModule_AddIntConstant(m, "IPPROTO_AH", 51);





    PyModule_AddIntConstant(m, "IPPROTO_ICMPV6", 58);


    PyModule_AddIntConstant(m, "IPPROTO_NONE", 59);


    PyModule_AddIntConstant(m, "IPPROTO_DSTOPTS", 60);


    PyModule_AddIntConstant(m, "IPPROTO_XTP", 36);


    PyModule_AddIntConstant(m, "IPPROTO_EON", 80);


    PyModule_AddIntConstant(m, "IPPROTO_PIM", 103);


    PyModule_AddIntConstant(m, "IPPROTO_IPCOMP", 108);





    PyModule_AddIntConstant(m, "IPPROTO_SCTP", 132);






    PyModule_AddIntConstant(m, "IPPROTO_RAW", 255);




    PyModule_AddIntConstant(m, "IPPROTO_MAX", 256);



    PyModule_AddIntConstant(m, "SYSPROTO_CONTROL", 2);




    PyModule_AddIntConstant(m, "IPPORT_RESERVED", 1024);




    PyModule_AddIntConstant(m, "IPPORT_USERRESERVED", 5000);






    PyModule_AddIntConstant(m, "INADDR_ANY", (u_int32_t)0x00000000);




    PyModule_AddIntConstant(m, "INADDR_BROADCAST", (u_int32_t)0xffffffff);




    PyModule_AddIntConstant(m, "INADDR_LOOPBACK", (u_int32_t)0x7f000001);




    PyModule_AddIntConstant(m, "INADDR_UNSPEC_GROUP", (u_int32_t)0xe0000000);




    PyModule_AddIntConstant(m, "INADDR_ALLHOSTS_GROUP",
                            (u_int32_t)0xe0000001);




    PyModule_AddIntConstant(m, "INADDR_MAX_LOCAL_GROUP",
                            (u_int32_t)0xe00000ff);




    PyModule_AddIntConstant(m, "INADDR_NONE", 0xffffffff);






    PyModule_AddIntConstant(m, "IP_OPTIONS", 1);


    PyModule_AddIntConstant(m, "IP_HDRINCL", 2);


    PyModule_AddIntConstant(m, "IP_TOS", 3);


    PyModule_AddIntConstant(m, "IP_TTL", 4);


    PyModule_AddIntConstant(m, "IP_RECVOPTS", 5);


    PyModule_AddIntConstant(m, "IP_RECVRETOPTS", 6);


    PyModule_AddIntConstant(m, "IP_RECVDSTADDR", 7);


    PyModule_AddIntConstant(m, "IP_RETOPTS", 8);


    PyModule_AddIntConstant(m, "IP_MULTICAST_IF", 9);


    PyModule_AddIntConstant(m, "IP_MULTICAST_TTL", 10);


    PyModule_AddIntConstant(m, "IP_MULTICAST_LOOP", 11);


    PyModule_AddIntConstant(m, "IP_ADD_MEMBERSHIP", 12);


    PyModule_AddIntConstant(m, "IP_DROP_MEMBERSHIP", 13);


    PyModule_AddIntConstant(m, "IP_DEFAULT_MULTICAST_TTL",
                            1);


    PyModule_AddIntConstant(m, "IP_DEFAULT_MULTICAST_LOOP",
                            1);


    PyModule_AddIntConstant(m, "IP_MAX_MEMBERSHIPS", 4095);







    PyModule_AddIntConstant(m, "IPV6_JOIN_GROUP", 12);


    PyModule_AddIntConstant(m, "IPV6_LEAVE_GROUP", 13);


    PyModule_AddIntConstant(m, "IPV6_MULTICAST_HOPS", 10);


    PyModule_AddIntConstant(m, "IPV6_MULTICAST_IF", 9);


    PyModule_AddIntConstant(m, "IPV6_MULTICAST_LOOP", 11);


    PyModule_AddIntConstant(m, "IPV6_UNICAST_HOPS", 4);



    PyModule_AddIntConstant(m, "IPV6_V6ONLY", 27);



    PyModule_AddIntConstant(m, "IPV6_CHECKSUM", 26);
# 6437 "socketmodule.c"
    PyModule_AddIntConstant(m, "IPV6_RECVTCLASS", 35);
# 6446 "socketmodule.c"
    PyModule_AddIntConstant(m, "IPV6_RTHDR_TYPE_0", 0);





    PyModule_AddIntConstant(m, "IPV6_TCLASS", 36);







    PyModule_AddIntConstant(m, "TCP_NODELAY", 0x01);


    PyModule_AddIntConstant(m, "TCP_MAXSEG", 0x02);
# 6542 "socketmodule.c"
    PyModule_AddIntConstant(m, "EAI_ADDRFAMILY", 1);


    PyModule_AddIntConstant(m, "EAI_AGAIN", 2);


    PyModule_AddIntConstant(m, "EAI_BADFLAGS", 3);


    PyModule_AddIntConstant(m, "EAI_FAIL", 4);


    PyModule_AddIntConstant(m, "EAI_FAMILY", 5);


    PyModule_AddIntConstant(m, "EAI_MEMORY", 6);


    PyModule_AddIntConstant(m, "EAI_NODATA", 7);


    PyModule_AddIntConstant(m, "EAI_NONAME", 8);


    PyModule_AddIntConstant(m, "EAI_OVERFLOW", 14);


    PyModule_AddIntConstant(m, "EAI_SERVICE", 9);


    PyModule_AddIntConstant(m, "EAI_SOCKTYPE", 10);


    PyModule_AddIntConstant(m, "EAI_SYSTEM", 11);


    PyModule_AddIntConstant(m, "EAI_BADHINTS", 12);


    PyModule_AddIntConstant(m, "EAI_PROTOCOL", 13);


    PyModule_AddIntConstant(m, "EAI_MAX", 15);


    PyModule_AddIntConstant(m, "AI_PASSIVE", 0x00000001);


    PyModule_AddIntConstant(m, "AI_CANONNAME", 0x00000002);


    PyModule_AddIntConstant(m, "AI_NUMERICHOST", 0x00000004);


    PyModule_AddIntConstant(m, "AI_NUMERICSERV", 0x00001000);


    PyModule_AddIntConstant(m, "AI_MASK", (0x00000001 | 0x00000002 | 0x00000004 | 0x00001000 | 0x00000400));


    PyModule_AddIntConstant(m, "AI_ALL", 0x00000100);


    PyModule_AddIntConstant(m, "AI_V4MAPPED_CFG", 0x00000200);


    PyModule_AddIntConstant(m, "AI_ADDRCONFIG", 0x00000400);


    PyModule_AddIntConstant(m, "AI_V4MAPPED", 0x00000800);


    PyModule_AddIntConstant(m, "AI_DEFAULT", (0x00000200 | 0x00000400));


    PyModule_AddIntConstant(m, "NI_MAXHOST", 1025);


    PyModule_AddIntConstant(m, "NI_MAXSERV", 32);


    PyModule_AddIntConstant(m, "NI_NOFQDN", 0x00000001);


    PyModule_AddIntConstant(m, "NI_NUMERICHOST", 0x00000002);


    PyModule_AddIntConstant(m, "NI_NAMEREQD", 0x00000004);


    PyModule_AddIntConstant(m, "NI_NUMERICSERV", 0x00000008);


    PyModule_AddIntConstant(m, "NI_DGRAM", 0x00000010);




    PyModule_AddIntConstant(m, "SHUT_RD", 0);






    PyModule_AddIntConstant(m, "SHUT_WR", 1);






    PyModule_AddIntConstant(m, "SHUT_RDWR", 2);
# 6687 "socketmodule.c"
    netdb_lock = PyThread_allocate_lock();

    return m;
}
