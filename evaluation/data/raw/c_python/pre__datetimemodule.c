# 1 "_datetimemodule.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "_datetimemodule.c"




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
# 6 "_datetimemodule.c" 2
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
# 7 "_datetimemodule.c" 2
# 16 "_datetimemodule.c"
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/datetime.h" 1
# 34 "/Users/parrt/tmp/Python-3.3.1/Include/datetime.h"
typedef struct
{
    PyObject ob_base;
    Py_hash_t hashcode;
    int days;
    int seconds;
    int microseconds;
} PyDateTime_Delta;

typedef struct
{
    PyObject ob_base;
} PyDateTime_TZInfo;
# 61 "/Users/parrt/tmp/Python-3.3.1/Include/datetime.h"
typedef struct
{
    PyObject ob_base; Py_hash_t hashcode; char hastzinfo;
} _PyDateTime_BaseTZInfo;
# 76 "/Users/parrt/tmp/Python-3.3.1/Include/datetime.h"
typedef struct
{
    PyObject ob_base; Py_hash_t hashcode; char hastzinfo; unsigned char data[6];
} _PyDateTime_BaseTime;

typedef struct
{
    PyObject ob_base; Py_hash_t hashcode; char hastzinfo; unsigned char data[6];
    PyObject *tzinfo;
} PyDateTime_Time;







typedef struct
{
    PyObject ob_base; Py_hash_t hashcode; char hastzinfo;
    unsigned char data[4];
} PyDateTime_Date;





typedef struct
{
    PyObject ob_base; Py_hash_t hashcode; char hastzinfo; unsigned char data[10];
} _PyDateTime_BaseDateTime;

typedef struct
{
    PyObject ob_base; Py_hash_t hashcode; char hastzinfo; unsigned char data[10];
    PyObject *tzinfo;
} PyDateTime_DateTime;
# 146 "/Users/parrt/tmp/Python-3.3.1/Include/datetime.h"
typedef struct {

    PyTypeObject *DateType;
    PyTypeObject *DateTimeType;
    PyTypeObject *TimeType;
    PyTypeObject *DeltaType;
    PyTypeObject *TZInfoType;


    PyObject *(*Date_FromDate)(int, int, int, PyTypeObject*);
    PyObject *(*DateTime_FromDateAndTime)(int, int, int, int, int, int, int,
        PyObject*, PyTypeObject*);
    PyObject *(*Time_FromTime)(int, int, int, int, PyObject*, PyTypeObject*);
    PyObject *(*Delta_FromDelta)(int, int, int, int, PyTypeObject*);


    PyObject *(*DateTime_FromTimestamp)(PyObject*, PyObject*, PyObject*);
    PyObject *(*Date_FromTimestamp)(PyObject*, PyObject*);

} PyDateTime_CAPI;
# 17 "_datetimemodule.c" 2
# 100 "_datetimemodule.c"
static PyTypeObject PyDateTime_DateType;
static PyTypeObject PyDateTime_DateTimeType;
static PyTypeObject PyDateTime_DeltaType;
static PyTypeObject PyDateTime_TimeType;
static PyTypeObject PyDateTime_TZInfoType;
static PyTypeObject PyDateTime_TimeZoneType;
# 127 "_datetimemodule.c"
static int
divmod(int x, int y, int *r)
{
    int quo;

    (__builtin_expect(!(y > 0), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 132, "y > 0") : (void)0);
    quo = x / y;
    *r = x - quo * y;
    if (*r < 0) {
        --quo;
        *r += y;
    }
    (__builtin_expect(!(0 <= *r && *r < y), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 139, "0 <= *r && *r < y") : (void)0);
    return quo;
}




static long
round_to_long(double x)
{
    if (x >= 0.0)
        x = floor(x + 0.5);
    else
        x = ceil(x - 0.5);
    return (long)x;
}




static PyObject *
divide_nearest(PyObject *m, PyObject *n)
{
    PyObject *result;
    PyObject *temp;

    temp = _PyLong_DivmodNear(m, n);
    if (temp == ((void *)0))
        return ((void *)0);
    result = (((PyTupleObject *)(temp))->ob_item[0]);
    ( ((PyObject*)(result))->ob_refcnt++);
    do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0);

    return result;
}
# 183 "_datetimemodule.c"
static int _days_in_month[] = {
    0,
    31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31
};

static int _days_before_month[] = {
    0,
    0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334
};


static int
is_leap(int year)
{





    const unsigned int ayear = (unsigned int)year;
    return ayear % 4 == 0 && (ayear % 100 != 0 || ayear % 400 == 0);
}


static int
days_in_month(int year, int month)
{
    (__builtin_expect(!(month >= 1), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 210, "month >= 1") : (void)0);
    (__builtin_expect(!(month <= 12), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 211, "month <= 12") : (void)0);
    if (month == 2 && is_leap(year))
        return 29;
    else
        return _days_in_month[month];
}


static int
days_before_month(int year, int month)
{
    int days;

    (__builtin_expect(!(month >= 1), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 224, "month >= 1") : (void)0);
    (__builtin_expect(!(month <= 12), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 225, "month <= 12") : (void)0);
    days = _days_before_month[month];
    if (month > 2 && is_leap(year))
        ++days;
    return days;
}




static int
days_before_year(int year)
{
    int y = year - 1;




    (__builtin_expect(!(year >= 1), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 243, "year >= 1") : (void)0);
    return y*365 + y/4 - y/100 + y/400;
}
# 255 "_datetimemodule.c"
static void
ord_to_ymd(int ordinal, int *year, int *month, int *day)
{
    int n, n1, n4, n100, n400, leapyear, preceding;
# 282 "_datetimemodule.c"
    (__builtin_expect(!(ordinal >= 1), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 282, "ordinal >= 1") : (void)0);
    --ordinal;
    n400 = ordinal / 146097;
    n = ordinal % 146097;
    *year = n400 * 400 + 1;
# 295 "_datetimemodule.c"
    n100 = n / 36524;
    n = n % 36524;


    n4 = n / 1461;
    n = n % 1461;





    n1 = n / 365;
    n = n % 365;

    *year += n100 * 100 + n4 * 4 + n1;
    if (n1 == 4 || n100 == 4) {
        (__builtin_expect(!(n == 0), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 311, "n == 0") : (void)0);
        *year -= 1;
        *month = 12;
        *day = 31;
        return;
    }





    leapyear = n1 == 3 && (n4 != 24 || n100 == 3);
    (__builtin_expect(!(leapyear == is_leap(*year)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 323, "leapyear == is_leap(*year)") : (void)0);
    *month = (n + 50) >> 5;
    preceding = (_days_before_month[*month] + (*month > 2 && leapyear));
    if (preceding > n) {

        *month -= 1;
        preceding -= days_in_month(*year, *month);
    }
    n -= preceding;
    (__builtin_expect(!(0 <= n), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 332, "0 <= n") : (void)0);
    (__builtin_expect(!(n < days_in_month(*year, *month)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 333, "n < days_in_month(*year, *month)") : (void)0);

    *day = n + 1;
}


static int
ymd_to_ord(int year, int month, int day)
{
    return days_before_year(year) + days_before_month(year, month) + day;
}


static int
weekday(int year, int month, int day)
{
    return (ymd_to_ord(year, month, day) + 6) % 7;
}




static int
iso_week1_monday(int year)
{
    int first_day = ymd_to_ord(year, 1, 1);

    int first_weekday = (first_day + 6) % 7;

    int week1_monday = first_day - first_weekday;

    if (first_weekday > 3)
        week1_monday += 7;
    return week1_monday;
}
# 376 "_datetimemodule.c"
static int
check_delta_day_range(int days)
{
    if (-999999999 <= days && days <= 999999999)
        return 0;
    PyErr_Format(PyExc_OverflowError,
                 "days=%d; must have magnitude <= %d",
                 days, 999999999);
    return -1;
}




static int
check_date_args(int year, int month, int day)
{

    if (year < 1 || year > 9999) {
        PyErr_SetString(PyExc_ValueError,
                        "year is out of range");
        return -1;
    }
    if (month < 1 || month > 12) {
        PyErr_SetString(PyExc_ValueError,
                        "month must be in 1..12");
        return -1;
    }
    if (day < 1 || day > days_in_month(year, month)) {
        PyErr_SetString(PyExc_ValueError,
                        "day is out of range for month");
        return -1;
    }
    return 0;
}




static int
check_time_args(int h, int m, int s, int us)
{
    if (h < 0 || h > 23) {
        PyErr_SetString(PyExc_ValueError,
                        "hour must be in 0..23");
        return -1;
    }
    if (m < 0 || m > 59) {
        PyErr_SetString(PyExc_ValueError,
                        "minute must be in 0..59");
        return -1;
    }
    if (s < 0 || s > 59) {
        PyErr_SetString(PyExc_ValueError,
                        "second must be in 0..59");
        return -1;
    }
    if (us < 0 || us > 999999) {
        PyErr_SetString(PyExc_ValueError,
                        "microsecond must be in 0..999999");
        return -1;
    }
    return 0;
}
# 451 "_datetimemodule.c"
static void
normalize_pair(int *hi, int *lo, int factor)
{
    (__builtin_expect(!(factor > 0), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 454, "factor > 0") : (void)0);
    (__builtin_expect(!(lo != hi), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 455, "lo != hi") : (void)0);
    if (*lo < 0 || *lo >= factor) {
        const int num_hi = divmod(*lo, factor, lo);
        const int new_hi = *hi + num_hi;
        (__builtin_expect(!(! ((((new_hi) ^ (*hi)) & ((new_hi) ^ (num_hi))) < 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 459, "! SIGNED_ADD_OVERFLOWED(new_hi, *hi, num_hi)") : (void)0);
        *hi = new_hi;
    }
    (__builtin_expect(!(0 <= *lo && *lo < factor), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 462, "0 <= *lo && *lo < factor") : (void)0);
}







static void
normalize_d_s_us(int *d, int *s, int *us)
{
    if (*us < 0 || *us >= 1000000) {
        normalize_pair(s, us, 1000000);




    }
    if (*s < 0 || *s >= 24*3600) {
        normalize_pair(d, s, 24*3600);




    }
    (__builtin_expect(!(0 <= *s && *s < 24*3600), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 488, "0 <= *s && *s < 24*3600") : (void)0);
    (__builtin_expect(!(0 <= *us && *us < 1000000), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 489, "0 <= *us && *us < 1000000") : (void)0);
}







static int
normalize_y_m_d(int *y, int *m, int *d)
{
    int dim;





    (__builtin_expect(!(1 <= *m && *m <= 12), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 507, "1 <= *m && *m <= 12") : (void)0);






    dim = days_in_month(*y, *m);
    if (*d < 1 || *d > dim) {




        if (*d == 0) {
            --*m;
            if (*m > 0)
                *d = days_in_month(*y, *m);
            else {
                --*y;
                *m = 12;
                *d = 31;
            }
        }
        else if (*d == dim + 1) {

            ++*m;
            *d = 1;
            if (*m > 12) {
                *m = 1;
                ++*y;
            }
        }
        else {
            int ordinal = ymd_to_ord(*y, *m, 1) +
                                      *d - 1;
            if (ordinal < 1 || ordinal > 3652059) {
                goto error;
            } else {
                ord_to_ymd(ordinal, y, m, d);
                return 0;
            }
        }
    }
    (__builtin_expect(!(*m > 0), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 550, "*m > 0") : (void)0);
    (__builtin_expect(!(*d > 0), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 551, "*d > 0") : (void)0);
    if (1 <= *y && *y <= 9999)
        return 0;
 error:
    PyErr_SetString(PyExc_OverflowError,
            "date value out of range");
    return -1;

}





static int
normalize_date(int *year, int *month, int *day)
{
    return normalize_y_m_d(year, month, day);
}




static int
normalize_datetime(int *year, int *month, int *day,
                   int *hour, int *minute, int *second,
                   int *microsecond)
{
    normalize_pair(second, microsecond, 1000000);
    normalize_pair(minute, second, 60);
    normalize_pair(hour, minute, 60);
    normalize_pair(day, hour, 24);
    return normalize_date(year, month, day);
}
# 607 "_datetimemodule.c"
static PyObject *
time_alloc(PyTypeObject *type, Py_ssize_t aware)
{
    PyObject *self;

    self = (PyObject *)
        PyObject_Malloc(aware ?
                        sizeof(PyDateTime_Time) :
                sizeof(_PyDateTime_BaseTime));
    if (self == ((void *)0))
        return (PyObject *)PyErr_NoMemory();
    ( (((PyObject*)(self))->ob_type) = (type), ( (((PyObject*)((PyObject *)(self)))->ob_refcnt) = 1), (self) );
    return self;
}

static PyObject *
datetime_alloc(PyTypeObject *type, Py_ssize_t aware)
{
    PyObject *self;

    self = (PyObject *)
        PyObject_Malloc(aware ?
                        sizeof(PyDateTime_DateTime) :
                sizeof(_PyDateTime_BaseDateTime));
    if (self == ((void *)0))
        return (PyObject *)PyErr_NoMemory();
    ( (((PyObject*)(self))->ob_type) = (type), ( (((PyObject*)((PyObject *)(self)))->ob_refcnt) = 1), (self) );
    return self;
}







static void
set_date_fields(PyDateTime_Date *self, int y, int m, int d)
{
    self->hashcode = -1;
    (((self)->data[0] = ((y) & 0xff00) >> 8), ((self)->data[1] = ((y) & 0x00ff)));
    ((((PyDateTime_Date*)self)->data[2]) = (m));
    ((((PyDateTime_Date*)self)->data[3]) = (d));
}






static PyObject *
new_date_ex(int year, int month, int day, PyTypeObject *type)
{
    PyDateTime_Date *self;

    self = (PyDateTime_Date *) (type->tp_alloc(type, 0));
    if (self != ((void *)0))
        set_date_fields(self, year, month, day);
    return (PyObject *) self;
}





static PyObject *
new_datetime_ex(int year, int month, int day, int hour, int minute,
             int second, int usecond, PyObject *tzinfo, PyTypeObject *type)
{
    PyDateTime_DateTime *self;
    char aware = tzinfo != (&_Py_NoneStruct);

    self = (PyDateTime_DateTime *) (type->tp_alloc(type, aware));
    if (self != ((void *)0)) {
        self->hastzinfo = aware;
        set_date_fields((PyDateTime_Date *)self, year, month, day);
        ((((PyDateTime_DateTime*)self)->data[4]) = (hour));
        ((((PyDateTime_DateTime*)self)->data[5]) = (minute));
        ((((PyDateTime_DateTime*)self)->data[6]) = (second));
        (((self)->data[7] = ((usecond) & 0xff0000) >> 16), ((self)->data[8] = ((usecond) & 0x00ff00) >> 8), ((self)->data[9] = ((usecond) & 0x0000ff)));
        if (aware) {
            ( ((PyObject*)(tzinfo))->ob_refcnt++);
            self->tzinfo = tzinfo;
        }
    }
    return (PyObject *)self;
}






static PyObject *
new_time_ex(int hour, int minute, int second, int usecond,
            PyObject *tzinfo, PyTypeObject *type)
{
    PyDateTime_Time *self;
    char aware = tzinfo != (&_Py_NoneStruct);

    self = (PyDateTime_Time *) (type->tp_alloc(type, aware));
    if (self != ((void *)0)) {
        self->hastzinfo = aware;
        self->hashcode = -1;
        ((((PyDateTime_Time*)self)->data[0]) = (hour));
        ((((PyDateTime_Time*)self)->data[1]) = (minute));
        ((((PyDateTime_Time*)self)->data[2]) = (second));
        (((self)->data[3] = ((usecond) & 0xff0000) >> 16), ((self)->data[4] = ((usecond) & 0x00ff00) >> 8), ((self)->data[5] = ((usecond) & 0x0000ff)));
        if (aware) {
            ( ((PyObject*)(tzinfo))->ob_refcnt++);
            self->tzinfo = tzinfo;
        }
    }
    return (PyObject *)self;
}
# 732 "_datetimemodule.c"
static PyObject *
new_delta_ex(int days, int seconds, int microseconds, int normalize,
             PyTypeObject *type)
{
    PyDateTime_Delta *self;

    if (normalize)
        normalize_d_s_us(&days, &seconds, &microseconds);
    (__builtin_expect(!(0 <= seconds && seconds < 24*3600), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 740, "0 <= seconds && seconds < 24*3600") : (void)0);
    (__builtin_expect(!(0 <= microseconds && microseconds < 1000000), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 741, "0 <= microseconds && microseconds < 1000000") : (void)0);

    if (check_delta_day_range(days) < 0)
        return ((void *)0);

    self = (PyDateTime_Delta *) (type->tp_alloc(type, 0));
    if (self != ((void *)0)) {
        self->hashcode = -1;
        ((self)->days = (days));
        ((self)->seconds = (seconds));
        ((self)->microseconds = (microseconds));
    }
    return (PyObject *) self;
}





typedef struct
{
    PyObject ob_base;
    PyObject *offset;
    PyObject *name;
} PyDateTime_TimeZone;


static PyObject *PyDateTime_TimeZone_UTC;

static PyObject *PyDateTime_Epoch;





static PyObject *
create_timezone(PyObject *offset, PyObject *name)
{
    PyDateTime_TimeZone *self;
    PyTypeObject *type = &PyDateTime_TimeZoneType;

    (__builtin_expect(!(offset != ((void *)0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 782, "offset != NULL") : (void)0);
    (__builtin_expect(!(((((PyObject*)(offset))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(offset))->ob_type), (&PyDateTime_DeltaType)))), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 783, "PyDelta_Check(offset)") : (void)0);
    (__builtin_expect(!(name == ((void *)0) || ((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 784, "name == NULL || PyUnicode_Check(name)") : (void)0);

    self = (PyDateTime_TimeZone *)(type->tp_alloc(type, 0));
    if (self == ((void *)0)) {
        return ((void *)0);
    }
    ( ((PyObject*)(offset))->ob_refcnt++);
    self->offset = offset;
    do { if ((name) == ((void *)0)) ; else ( ((PyObject*)(name))->ob_refcnt++); } while (0);
    self->name = name;
    return (PyObject *)self;
}

static int delta_bool(PyDateTime_Delta *self);

static PyObject *
new_timezone(PyObject *offset, PyObject *name)
{
    (__builtin_expect(!(offset != ((void *)0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 802, "offset != NULL") : (void)0);
    (__builtin_expect(!(((((PyObject*)(offset))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(offset))->ob_type), (&PyDateTime_DeltaType)))), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 803, "PyDelta_Check(offset)") : (void)0);
    (__builtin_expect(!(name == ((void *)0) || ((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 804, "name == NULL || PyUnicode_Check(name)") : (void)0);

    if (name == ((void *)0) && delta_bool((PyDateTime_Delta *)offset) == 0) {
        ( ((PyObject*)(PyDateTime_TimeZone_UTC))->ob_refcnt++);
        return PyDateTime_TimeZone_UTC;
    }
    if ((((PyDateTime_Delta *)(offset))->microseconds) != 0 || (((PyDateTime_Delta *)(offset))->seconds) % 60 != 0) {
        PyErr_Format(PyExc_ValueError, "offset must be a timedelta"
                     " representing a whole number of minutes,"
                     " not %R.", offset);
        return ((void *)0);
    }
    if (((((PyDateTime_Delta *)(offset))->days) == -1 && (((PyDateTime_Delta *)(offset))->seconds) == 0) ||
        (((PyDateTime_Delta *)(offset))->days) < -1 || (((PyDateTime_Delta *)(offset))->days) >= 1) {
        PyErr_Format(PyExc_ValueError, "offset must be a timedelta"
                     " strictly between -timedelta(hours=24) and"
                     " timedelta(hours=24),"
                     " not %R.", offset);
        return ((void *)0);
    }

    return create_timezone(offset, name);
}
# 835 "_datetimemodule.c"
static int
check_tzinfo_subclass(PyObject *p)
{
    if (p == (&_Py_NoneStruct) || ((((PyObject*)(p))->ob_type) == (&PyDateTime_TZInfoType) || PyType_IsSubtype((((PyObject*)(p))->ob_type), (&PyDateTime_TZInfoType))))
        return 0;
    PyErr_Format(PyExc_TypeError,
                 "tzinfo argument must be None or of a tzinfo subclass, "
                 "not type '%s'",
                 (((PyObject*)(p))->ob_type)->tp_name);
    return -1;
}





static PyObject *
get_tzinfo_member(PyObject *self)
{
    PyObject *tzinfo = ((void *)0);

    if (((((PyObject*)(self))->ob_type) == (&PyDateTime_DateTimeType) || PyType_IsSubtype((((PyObject*)(self))->ob_type), (&PyDateTime_DateTimeType))) && (((_PyDateTime_BaseTZInfo *)(self))->hastzinfo))
        tzinfo = ((PyDateTime_DateTime *)self)->tzinfo;
    else if (((((PyObject*)(self))->ob_type) == (&PyDateTime_TimeType) || PyType_IsSubtype((((PyObject*)(self))->ob_type), (&PyDateTime_TimeType))) && (((_PyDateTime_BaseTZInfo *)(self))->hastzinfo))
        tzinfo = ((PyDateTime_Time *)self)->tzinfo;

    return tzinfo;
}
# 871 "_datetimemodule.c"
static PyObject *
call_tzinfo_method(PyObject *tzinfo, char *name, PyObject *tzinfoarg)
{
    PyObject *offset;

    (__builtin_expect(!(tzinfo != ((void *)0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 876, "tzinfo != NULL") : (void)0);
    (__builtin_expect(!(((((PyObject*)(tzinfo))->ob_type) == (&PyDateTime_TZInfoType) || PyType_IsSubtype((((PyObject*)(tzinfo))->ob_type), (&PyDateTime_TZInfoType))) || tzinfo == (&_Py_NoneStruct)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 877, "PyTZInfo_Check(tzinfo) || tzinfo == Py_None") : (void)0);
    (__builtin_expect(!(tzinfoarg != ((void *)0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 878, "tzinfoarg != NULL") : (void)0);

    if (tzinfo == (&_Py_NoneStruct))
        return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
    offset = PyObject_CallMethod(tzinfo, name, "O", tzinfoarg);
    if (offset == (&_Py_NoneStruct) || offset == ((void *)0))
        return offset;
    if (((((PyObject*)(offset))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(offset))->ob_type), (&PyDateTime_DeltaType)))) {
        if ((((PyDateTime_Delta *)(offset))->microseconds) != 0 || (((PyDateTime_Delta *)(offset))->seconds) % 60 != 0) {
            do { if ( --((PyObject*)(offset))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset)))); } while (0);
            PyErr_Format(PyExc_ValueError, "offset must be a timedelta"
                         " representing a whole number of minutes");
            return ((void *)0);
        }
        if (((((PyDateTime_Delta *)(offset))->days) == -1 && (((PyDateTime_Delta *)(offset))->seconds) == 0) ||
            (((PyDateTime_Delta *)(offset))->days) < -1 || (((PyDateTime_Delta *)(offset))->days) >= 1) {
            do { if ( --((PyObject*)(offset))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset)))); } while (0);
            PyErr_Format(PyExc_ValueError, "offset must be a timedelta"
                         " strictly between -timedelta(hours=24) and"
                         " timedelta(hours=24).");
            return ((void *)0);
        }
    }
    else {
        do { if ( --((PyObject*)(offset))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset)))); } while (0);
        PyErr_Format(PyExc_TypeError,
                     "tzinfo.%s() must return None or "
                     "timedelta, not '%.200s'",
                     name, (((PyObject*)(offset))->ob_type)->tp_name);
        return ((void *)0);
    }

    return offset;
}
# 921 "_datetimemodule.c"
static PyObject *
call_utcoffset(PyObject *tzinfo, PyObject *tzinfoarg)
{
    return call_tzinfo_method(tzinfo, "utcoffset", tzinfoarg);
}
# 935 "_datetimemodule.c"
static PyObject *
call_dst(PyObject *tzinfo, PyObject *tzinfoarg)
{
    return call_tzinfo_method(tzinfo, "dst", tzinfoarg);
}







static PyObject *
call_tzname(PyObject *tzinfo, PyObject *tzinfoarg)
{
    PyObject *result;
    static _Py_Identifier PyId_tzname = { 0, "tzname", 0 };

    (__builtin_expect(!(tzinfo != ((void *)0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 953, "tzinfo != NULL") : (void)0);
    (__builtin_expect(!(check_tzinfo_subclass(tzinfo) >= 0), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 954, "check_tzinfo_subclass(tzinfo) >= 0") : (void)0);
    (__builtin_expect(!(tzinfoarg != ((void *)0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 955, "tzinfoarg != NULL") : (void)0);

    if (tzinfo == (&_Py_NoneStruct))
        return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);

    result = _PyObject_CallMethodId(tzinfo, &PyId_tzname, "O", tzinfoarg);

    if (result == ((void *)0) || result == (&_Py_NoneStruct))
        return result;

    if (!((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        PyErr_Format(PyExc_TypeError, "tzinfo.tzname() must "
                     "return None or a string, not '%s'",
                     (((PyObject*)(result))->ob_type)->tp_name);
        do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0);
        result = ((void *)0);
    }

    return result;
}






static PyObject *
append_keyword_tzinfo(PyObject *repr, PyObject *tzinfo)
{
    PyObject *temp;

    (__builtin_expect(!(((((((PyObject*)(repr))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 986, "PyUnicode_Check(repr)") : (void)0);
    (__builtin_expect(!(tzinfo), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 987, "tzinfo") : (void)0);
    if (tzinfo == (&_Py_NoneStruct))
        return repr;

    (__builtin_expect(!(((__builtin_expect(!(((((((PyObject*)(repr))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_Check(repr)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)repr)->state.ready)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_IS_READY(repr)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((repr)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_Check((repr))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(repr))->state.ready)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_IS_READY((repr))") : (void)0), ((PyASCIIObject *)((repr)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((repr)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_Check((repr))") : (void)0), (((PyASCIIObject*)((repr)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((repr)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_Check((repr))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(repr))->state.ready)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_IS_READY((repr))") : (void)0), ((PyASCIIObject*)(repr))->state.ascii) ? ((void*)((PyASCIIObject*)((repr)) + 1)) : ((void*)((PyCompactUnicodeObject*)((repr)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((repr)))->data.any), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "((PyUnicodeObject*)((repr)))->data.any") : (void)0), ((((PyUnicodeObject *)((repr)))->data.any))))))[(((__builtin_expect(!(((((((PyObject*)(repr))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_Check(repr)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)repr)->state.ready)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_IS_READY(repr)") : (void)0), ((PyASCIIObject *)(repr))->length)-1)] : (((__builtin_expect(!(((((((PyObject*)((repr)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_Check((repr))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(repr))->state.ready)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_IS_READY((repr))") : (void)0), ((PyASCIIObject *)((repr)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((repr)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_Check((repr))") : (void)0), (((PyASCIIObject*)((repr)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((repr)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_Check((repr))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(repr))->state.ready)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_IS_READY((repr))") : (void)0), ((PyASCIIObject*)(repr))->state.ascii) ? ((void*)((PyASCIIObject*)((repr)) + 1)) : ((void*)((PyCompactUnicodeObject*)((repr)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((repr)))->data.any), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "((PyUnicodeObject*)((repr)))->data.any") : (void)0), ((((PyUnicodeObject *)((repr)))->data.any))))))[(((__builtin_expect(!(((((((PyObject*)(repr))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_Check(repr)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)repr)->state.ready)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_IS_READY(repr)") : (void)0), ((PyASCIIObject *)(repr))->length)-1)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((repr)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_Check((repr))") : (void)0), (((PyASCIIObject*)((repr)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((repr)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_Check((repr))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(repr))->state.ready)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_IS_READY((repr))") : (void)0), ((PyASCIIObject*)(repr))->state.ascii) ? ((void*)((PyASCIIObject*)((repr)) + 1)) : ((void*)((PyCompactUnicodeObject*)((repr)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((repr)))->data.any), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "((PyUnicodeObject*)((repr)))->data.any") : (void)0), ((((PyUnicodeObject *)((repr)))->data.any))))))[(((__builtin_expect(!(((((((PyObject*)(repr))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_Check(repr)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)repr)->state.ready)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_IS_READY(repr)") : (void)0), ((PyASCIIObject *)(repr))->length)-1)] ) )) == ')'), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 991, "PyUnicode_READ_CHAR(repr, PyUnicode_GET_LENGTH(repr)-1) == ')'") : (void)0);
    temp = PyUnicode_Substring(repr, 0, ((__builtin_expect(!(((((((PyObject*)(repr))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 992, "PyUnicode_Check(repr)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)repr)->state.ready)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 992, "PyUnicode_IS_READY(repr)") : (void)0), ((PyASCIIObject *)(repr))->length) - 1);
    do { if ( --((PyObject*)(repr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(repr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(repr)))); } while (0);
    if (temp == ((void *)0))
        return ((void *)0);
    repr = PyUnicode_FromFormat("%U, tzinfo=%R)", temp, tzinfo);
    do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0);
    return repr;
}





static PyObject *
format_ctime(PyDateTime_Date *date, int hours, int minutes, int seconds)
{
    static const char *DayNames[] = {
        "Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"
    };
    static const char *MonthNames[] = {
        "Jan", "Feb", "Mar", "Apr", "May", "Jun",
        "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"
    };

    int wday = weekday(((((PyDateTime_Date*)date)->data[0] << 8) | ((PyDateTime_Date*)date)->data[1]), (((PyDateTime_Date*)date)->data[2]), (((PyDateTime_Date*)date)->data[3]));

    return PyUnicode_FromFormat("%s %s %2d %02d:%02d:%02d %04d",
                                DayNames[wday], MonthNames[(((PyDateTime_Date*)date)->data[2])-1],
                                (((PyDateTime_Date*)date)->data[3]), hours, minutes, seconds,
                                ((((PyDateTime_Date*)date)->data[0] << 8) | ((PyDateTime_Date*)date)->data[1]));
}

static PyObject *delta_negative(PyDateTime_Delta *self);
# 1036 "_datetimemodule.c"
static int
format_utcoffset(char *buf, size_t buflen, const char *sep,
                PyObject *tzinfo, PyObject *tzinfoarg)
{
    PyObject *offset;
    int hours, minutes, seconds;
    char sign;

    (__builtin_expect(!(buflen >= 1), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1044, "buflen >= 1") : (void)0);

    offset = call_utcoffset(tzinfo, tzinfoarg);
    if (offset == ((void *)0))
        return -1;
    if (offset == (&_Py_NoneStruct)) {
        do { if ( --((PyObject*)(offset))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset)))); } while (0);
        *buf = '\0';
        return 0;
    }

    if ((((PyDateTime_Delta *)(offset))->days) < 0) {
        PyObject *temp = offset;
        sign = '-';
        offset = delta_negative((PyDateTime_Delta *)offset);
        do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0);
        if (offset == ((void *)0))
            return -1;
    }
    else {
        sign = '+';
    }

    seconds = (((PyDateTime_Delta *)(offset))->seconds);
    do { if ( --((PyObject*)(offset))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset)))); } while (0);
    minutes = divmod(seconds, 60, &seconds);
    hours = divmod(minutes, 60, &minutes);
    (__builtin_expect(!(seconds == 0), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1071, "seconds == 0") : (void)0);

    PyOS_snprintf(buf, buflen, "%c%02d%s%02d", sign, hours, sep, minutes);

    return 0;
}

static PyObject *
make_Zreplacement(PyObject *object, PyObject *tzinfoarg)
{
    PyObject *temp;
    PyObject *tzinfo = get_tzinfo_member(object);
    PyObject *Zreplacement = PyUnicode_FromStringAndSize(((void *)0), 0);
    static _Py_Identifier PyId_replace = { 0, "replace", 0 };

    if (Zreplacement == ((void *)0))
        return ((void *)0);
    if (tzinfo == (&_Py_NoneStruct) || tzinfo == ((void *)0))
        return Zreplacement;

    (__builtin_expect(!(tzinfoarg != ((void *)0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1091, "tzinfoarg != NULL") : (void)0);
    temp = call_tzname(tzinfo, tzinfoarg);
    if (temp == ((void *)0))
        goto Error;
    if (temp == (&_Py_NoneStruct)) {
        do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0);
        return Zreplacement;
    }

    (__builtin_expect(!(((((((PyObject*)(temp))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1100, "PyUnicode_Check(temp)") : (void)0);




    do { if ( --((PyObject*)(Zreplacement))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(Zreplacement)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(Zreplacement)))); } while (0);
    Zreplacement = _PyObject_CallMethodId(temp, &PyId_replace, "ss", "%", "%%");
    do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0);
    if (Zreplacement == ((void *)0))
        return ((void *)0);
    if (!((((((PyObject*)(Zreplacement))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        PyErr_SetString(PyExc_TypeError,
                        "tzname.replace() did not return a string");
        goto Error;
    }
    return Zreplacement;

  Error:
    do { if ( --((PyObject*)(Zreplacement))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(Zreplacement)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(Zreplacement)))); } while (0);
    return ((void *)0);
}

static PyObject *
make_freplacement(PyObject *object)
{
    char freplacement[64];
    if (((((PyObject*)(object))->ob_type) == (&PyDateTime_TimeType) || PyType_IsSubtype((((PyObject*)(object))->ob_type), (&PyDateTime_TimeType))))
        __builtin___sprintf_chk (freplacement, 0, __builtin_object_size (freplacement, 2 > 1), "%06d", ((((PyDateTime_Time*)object)->data[3] << 16) | (((PyDateTime_Time*)object)->data[4] << 8) | ((PyDateTime_Time*)object)->data[5]));
    else if (((((PyObject*)(object))->ob_type) == (&PyDateTime_DateTimeType) || PyType_IsSubtype((((PyObject*)(object))->ob_type), (&PyDateTime_DateTimeType))))
        __builtin___sprintf_chk (freplacement, 0, __builtin_object_size (freplacement, 2 > 1), "%06d", ((((PyDateTime_DateTime*)object)->data[7] << 16) | (((PyDateTime_DateTime*)object)->data[8] << 8) | ((PyDateTime_DateTime*)object)->data[9]));
    else
        __builtin___sprintf_chk (freplacement, 0, __builtin_object_size (freplacement, 2 > 1), "%06d", 0);

    return PyBytes_FromStringAndSize(freplacement, strlen(freplacement));
}
# 1143 "_datetimemodule.c"
static PyObject *
wrap_strftime(PyObject *object, PyObject *format, PyObject *timetuple,
              PyObject *tzinfoarg)
{
    PyObject *result = ((void *)0);

    PyObject *zreplacement = ((void *)0);
    PyObject *Zreplacement = ((void *)0);
    PyObject *freplacement = ((void *)0);

    const char *pin;
    Py_ssize_t flen;
    char ch;

    PyObject *newfmt = ((void *)0);
    char *pnew;
    size_t totalnew;

    size_t usednew;

    const char *ptoappend;
    Py_ssize_t ntoappend;

    (__builtin_expect(!(object && format && timetuple), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1166, "object && format && timetuple") : (void)0);
    (__builtin_expect(!(((((((PyObject*)(format))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1167, "PyUnicode_Check(format)") : (void)0);

    pin = PyUnicode_AsUTF8AndSize(format, &flen);
    if (!pin)
        return ((void *)0);





    if (flen > 2147483647 - 1) {
        PyErr_NoMemory();
        goto Done;
    }

    totalnew = flen + 1;
    newfmt = PyBytes_FromStringAndSize(((void *)0), totalnew);
    if (newfmt == ((void *)0)) goto Done;
    pnew = PyBytes_AsString(newfmt);
    usednew = 0;

    while ((ch = *pin++) != '\0') {
        if (ch != '%') {
            ptoappend = pin - 1;
            ntoappend = 1;
        }
        else if ((ch = *pin++) == '\0') {

            PyErr_SetString(PyExc_ValueError, "strftime format "
                            "ends with raw %");
            goto Done;
        }

        else if (ch == 'z') {
            if (zreplacement == ((void *)0)) {

                char buf[100];
                PyObject *tzinfo = get_tzinfo_member(object);
                zreplacement = PyBytes_FromStringAndSize("", 0);
                if (zreplacement == ((void *)0)) goto Done;
                if (tzinfo != (&_Py_NoneStruct) && tzinfo != ((void *)0)) {
                    (__builtin_expect(!(tzinfoarg != ((void *)0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1208, "tzinfoarg != NULL") : (void)0);
                    if (format_utcoffset(buf,
                                         sizeof(buf),
                                         "",
                                         tzinfo,
                                         tzinfoarg) < 0)
                        goto Done;
                    do { if ( --((PyObject*)(zreplacement))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(zreplacement)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(zreplacement)))); } while (0);
                    zreplacement =
                      PyBytes_FromStringAndSize(buf,
                                               strlen(buf));
                    if (zreplacement == ((void *)0))
                        goto Done;
                }
            }
            (__builtin_expect(!(zreplacement != ((void *)0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1223, "zreplacement != NULL") : (void)0);
            ptoappend = ((__builtin_expect(!(((((((PyObject*)(zreplacement))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1224, "PyBytes_Check(zreplacement)") : (void)0), (((PyBytesObject *)(zreplacement))->ob_sval));
            ntoappend = ((__builtin_expect(!(((((((PyObject*)(zreplacement))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1225, "PyBytes_Check(zreplacement)") : (void)0),(((PyVarObject*)(zreplacement))->ob_size));
        }
        else if (ch == 'Z') {

            if (Zreplacement == ((void *)0)) {
                Zreplacement = make_Zreplacement(object,
                                                 tzinfoarg);
                if (Zreplacement == ((void *)0))
                    goto Done;
            }
            (__builtin_expect(!(Zreplacement != ((void *)0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1235, "Zreplacement != NULL") : (void)0);
            (__builtin_expect(!(((((((PyObject*)(Zreplacement))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1236, "PyUnicode_Check(Zreplacement)") : (void)0);
            ptoappend = PyUnicode_AsUTF8AndSize(Zreplacement,
                                                  &ntoappend);
            if (ptoappend == ((void *)0))
                goto Done;
        }
        else if (ch == 'f') {

            if (freplacement == ((void *)0)) {
                freplacement = make_freplacement(object);
                if (freplacement == ((void *)0))
                    goto Done;
            }
            (__builtin_expect(!(freplacement != ((void *)0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1249, "freplacement != NULL") : (void)0);
            (__builtin_expect(!(((((((PyObject*)(freplacement))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1250, "PyBytes_Check(freplacement)") : (void)0);
            ptoappend = ((__builtin_expect(!(((((((PyObject*)(freplacement))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1251, "PyBytes_Check(freplacement)") : (void)0), (((PyBytesObject *)(freplacement))->ob_sval));
            ntoappend = ((__builtin_expect(!(((((((PyObject*)(freplacement))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1252, "PyBytes_Check(freplacement)") : (void)0),(((PyVarObject*)(freplacement))->ob_size));
        }
        else {

            ptoappend = pin - 2;
            ntoappend = 2;
        }




        if (ntoappend == 0)
            continue;
        (__builtin_expect(!(ptoappend != ((void *)0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1265, "ptoappend != NULL") : (void)0);
        (__builtin_expect(!(ntoappend > 0), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1266, "ntoappend > 0") : (void)0);
        while (usednew + ntoappend > totalnew) {
            if (totalnew > (((Py_ssize_t)(((size_t)-1)>>1)) >> 1)) {
                PyErr_NoMemory();
                goto Done;
            }
            totalnew <<= 1;
            if (_PyBytes_Resize(&newfmt, totalnew) < 0)
                goto Done;
            pnew = PyBytes_AsString(newfmt) + usednew;
        }
        ((__builtin_object_size (pnew, 0) != (size_t) -1) ? __builtin___memcpy_chk (pnew, ptoappend, ntoappend, __builtin_object_size (pnew, 0)) : __inline_memcpy_chk (pnew, ptoappend, ntoappend));
        pnew += ntoappend;
        usednew += ntoappend;
        (__builtin_expect(!(usednew <= totalnew), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1280, "usednew <= totalnew") : (void)0);
    }

    if (_PyBytes_Resize(&newfmt, usednew) < 0)
        goto Done;
    {
        PyObject *format;
        PyObject *time = PyImport_ImportModuleNoBlock("time");

        if (time == ((void *)0))
            goto Done;
        format = PyUnicode_FromString(((__builtin_expect(!(((((((PyObject*)(newfmt))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1291, "PyBytes_Check(newfmt)") : (void)0), (((PyBytesObject *)(newfmt))->ob_sval)));
        if (format != ((void *)0)) {
            static _Py_Identifier PyId_strftime = { 0, "strftime", 0 };

            result = _PyObject_CallMethodId(time, &PyId_strftime, "OO",
                                            format, timetuple, ((void *)0));
            do { if ( --((PyObject*)(format))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(format)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(format)))); } while (0);
        }
        do { if ( --((PyObject*)(time))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(time)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(time)))); } while (0);
    }
 Done:
    do { if ((freplacement) == ((void *)0)) ; else do { if ( --((PyObject*)(freplacement))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(freplacement)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(freplacement)))); } while (0); } while (0);
    do { if ((zreplacement) == ((void *)0)) ; else do { if ( --((PyObject*)(zreplacement))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(zreplacement)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(zreplacement)))); } while (0); } while (0);
    do { if ((Zreplacement) == ((void *)0)) ; else do { if ( --((PyObject*)(Zreplacement))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(Zreplacement)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(Zreplacement)))); } while (0); } while (0);
    do { if ((newfmt) == ((void *)0)) ; else do { if ( --((PyObject*)(newfmt))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(newfmt)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(newfmt)))); } while (0); } while (0);
    return result;
}







static PyObject *
time_time(void)
{
    PyObject *result = ((void *)0);
    PyObject *time = PyImport_ImportModuleNoBlock("time");

    if (time != ((void *)0)) {
        static _Py_Identifier PyId_time = { 0, "time", 0 };

        result = _PyObject_CallMethodId(time, &PyId_time, "()");
        do { if ( --((PyObject*)(time))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(time)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(time)))); } while (0);
    }
    return result;
}




static PyObject *
build_struct_time(int y, int m, int d, int hh, int mm, int ss, int dstflag)
{
    PyObject *time;
    PyObject *result = ((void *)0);

    time = PyImport_ImportModuleNoBlock("time");
    if (time != ((void *)0)) {
        static _Py_Identifier PyId_struct_time = { 0, "struct_time", 0 };

        result = _PyObject_CallMethodId(time, &PyId_struct_time,
                                        "((iiiiiiiii))",
                                        y, m, d,
                                        hh, mm, ss,
                                        weekday(y, m, d),
                                        days_before_month(y, m) + d,
                                        dstflag);
        do { if ( --((PyObject*)(time))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(time)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(time)))); } while (0);
    }
    return result;
}
# 1363 "_datetimemodule.c"
static PyObject *
diff_to_bool(int diff, int op)
{
    PyObject *result;
    int istrue;

    switch (op) {
        case 2: istrue = diff == 0; break;
        case 3: istrue = diff != 0; break;
        case 1: istrue = diff <= 0; break;
        case 5: istrue = diff >= 0; break;
        case 0: istrue = diff < 0; break;
        case 4: istrue = diff > 0; break;
        default:
            (__builtin_expect(!(! "op unknown"), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1377, "! \"op unknown\"") : (void)0);
            istrue = 0;
    }
    result = istrue ? ((PyObject *) &_Py_TrueStruct) : ((PyObject *) &_Py_FalseStruct);
    ( ((PyObject*)(result))->ob_refcnt++);
    return result;
}


static PyObject *
cmperror(PyObject *a, PyObject *b)
{
    PyErr_Format(PyExc_TypeError,
                 "can't compare %s to %s",
                 (((PyObject*)(a))->ob_type)->tp_name, (((PyObject*)(b))->ob_type)->tp_name);
    return ((void *)0);
}






static PyObject *us_per_us = ((void *)0);
static PyObject *us_per_ms = ((void *)0);
static PyObject *us_per_second = ((void *)0);
static PyObject *us_per_minute = ((void *)0);
static PyObject *us_per_hour = ((void *)0);
static PyObject *us_per_day = ((void *)0);
static PyObject *us_per_week = ((void *)0);
static PyObject *seconds_per_day = ((void *)0);
# 1423 "_datetimemodule.c"
static PyObject *
delta_to_microseconds(PyDateTime_Delta *self)
{
    PyObject *x1 = ((void *)0);
    PyObject *x2 = ((void *)0);
    PyObject *x3 = ((void *)0);
    PyObject *result = ((void *)0);

    x1 = PyLong_FromLong((((PyDateTime_Delta *)(self))->days));
    if (x1 == ((void *)0))
        goto Done;
    x2 = PyNumber_Multiply(x1, seconds_per_day);
    if (x2 == ((void *)0))
        goto Done;
    do { if ( --((PyObject*)(x1))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x1)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x1)))); } while (0);
    x1 = ((void *)0);


    x1 = PyLong_FromLong((((PyDateTime_Delta *)(self))->seconds));
    if (x1 == ((void *)0))
        goto Done;
    x3 = PyNumber_Add(x1, x2);
    if (x3 == ((void *)0))
        goto Done;
    do { if ( --((PyObject*)(x1))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x1)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x1)))); } while (0);
    do { if ( --((PyObject*)(x2))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x2)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x2)))); } while (0);
               x2 = ((void *)0);


    x1 = PyNumber_Multiply(x3, us_per_second);
    if (x1 == ((void *)0))
        goto Done;
    do { if ( --((PyObject*)(x3))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x3)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x3)))); } while (0);
    x3 = ((void *)0);


    x2 = PyLong_FromLong((((PyDateTime_Delta *)(self))->microseconds));
    if (x2 == ((void *)0))
        goto Done;
    result = PyNumber_Add(x1, x2);

Done:
    do { if ((x1) == ((void *)0)) ; else do { if ( --((PyObject*)(x1))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x1)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x1)))); } while (0); } while (0);
    do { if ((x2) == ((void *)0)) ; else do { if ( --((PyObject*)(x2))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x2)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x2)))); } while (0); } while (0);
    do { if ((x3) == ((void *)0)) ; else do { if ( --((PyObject*)(x3))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x3)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x3)))); } while (0); } while (0);
    return result;
}



static PyObject *
microseconds_to_delta_ex(PyObject *pyus, PyTypeObject *type)
{
    int us;
    int s;
    int d;
    long temp;

    PyObject *tuple = ((void *)0);
    PyObject *num = ((void *)0);
    PyObject *result = ((void *)0);

    tuple = PyNumber_Divmod(pyus, us_per_second);
    if (tuple == ((void *)0))
        goto Done;

    num = PyTuple_GetItem(tuple, 1);
    if (num == ((void *)0))
        goto Done;
    temp = PyLong_AsLong(num);
    num = ((void *)0);
    if (temp == -1 && PyErr_Occurred())
        goto Done;
    (__builtin_expect(!(0 <= temp && temp < 1000000), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1496, "0 <= temp && temp < 1000000") : (void)0);
    us = (int)temp;
    if (us < 0) {

        (__builtin_expect(!(PyErr_Occurred()), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1500, "PyErr_Occurred()") : (void)0);
        goto Done;
    }

    num = PyTuple_GetItem(tuple, 0);
    if (num == ((void *)0))
        goto Done;
    ( ((PyObject*)(num))->ob_refcnt++);
    do { if ( --((PyObject*)(tuple))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tuple)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tuple)))); } while (0);

    tuple = PyNumber_Divmod(num, seconds_per_day);
    if (tuple == ((void *)0))
        goto Done;
    do { if ( --((PyObject*)(num))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(num)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(num)))); } while (0);

    num = PyTuple_GetItem(tuple, 1);
    if (num == ((void *)0))
        goto Done;
    temp = PyLong_AsLong(num);
    num = ((void *)0);
    if (temp == -1 && PyErr_Occurred())
        goto Done;
    (__builtin_expect(!(0 <= temp && temp < 24*3600), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1522, "0 <= temp && temp < 24*3600") : (void)0);
    s = (int)temp;

    if (s < 0) {

        (__builtin_expect(!(PyErr_Occurred()), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1527, "PyErr_Occurred()") : (void)0);
        goto Done;
    }

    num = PyTuple_GetItem(tuple, 0);
    if (num == ((void *)0))
        goto Done;
    ( ((PyObject*)(num))->ob_refcnt++);
    temp = PyLong_AsLong(num);
    if (temp == -1 && PyErr_Occurred())
        goto Done;
    d = (int)temp;
    if ((long)d != temp) {
        PyErr_SetString(PyExc_OverflowError, "normalized days too "
                        "large to fit in a C int");
        goto Done;
    }
    result = new_delta_ex(d, s, us, 0, type);

Done:
    do { if ((tuple) == ((void *)0)) ; else do { if ( --((PyObject*)(tuple))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tuple)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tuple)))); } while (0); } while (0);
    do { if ((num) == ((void *)0)) ; else do { if ( --((PyObject*)(num))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(num)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(num)))); } while (0); } while (0);
    return result;
}




static PyObject *
multiply_int_timedelta(PyObject *intobj, PyDateTime_Delta *delta)
{
    PyObject *pyus_in;
    PyObject *pyus_out;
    PyObject *result;

    pyus_in = delta_to_microseconds(delta);
    if (pyus_in == ((void *)0))
        return ((void *)0);

    pyus_out = PyNumber_Multiply(pyus_in, intobj);
    do { if ( --((PyObject*)(pyus_in))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_in)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_in)))); } while (0);
    if (pyus_out == ((void *)0))
        return ((void *)0);

    result = microseconds_to_delta_ex(pyus_out, &PyDateTime_DeltaType);
    do { if ( --((PyObject*)(pyus_out))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_out)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_out)))); } while (0);
    return result;
}

static PyObject *
multiply_float_timedelta(PyObject *floatobj, PyDateTime_Delta *delta)
{
    PyObject *result = ((void *)0);
    PyObject *pyus_in = ((void *)0), *temp, *pyus_out;
    PyObject *ratio = ((void *)0);
    static _Py_Identifier PyId_as_integer_ratio = { 0, "as_integer_ratio", 0 };

    pyus_in = delta_to_microseconds(delta);
    if (pyus_in == ((void *)0))
        return ((void *)0);
    ratio = _PyObject_CallMethodId(floatobj, &PyId_as_integer_ratio, ((void *)0));
    if (ratio == ((void *)0))
        goto error;
    temp = PyNumber_Multiply(pyus_in, (((PyTupleObject *)(ratio))->ob_item[0]));
    do { if ( --((PyObject*)(pyus_in))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_in)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_in)))); } while (0);
    pyus_in = ((void *)0);
    if (temp == ((void *)0))
        goto error;
    pyus_out = divide_nearest(temp, (((PyTupleObject *)(ratio))->ob_item[1]));
    do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0);
    if (pyus_out == ((void *)0))
        goto error;
    result = microseconds_to_delta_ex(pyus_out, &PyDateTime_DeltaType);
    do { if ( --((PyObject*)(pyus_out))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_out)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_out)))); } while (0);
 error:
    do { if ((pyus_in) == ((void *)0)) ; else do { if ( --((PyObject*)(pyus_in))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_in)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_in)))); } while (0); } while (0);
    do { if ((ratio) == ((void *)0)) ; else do { if ( --((PyObject*)(ratio))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(ratio)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(ratio)))); } while (0); } while (0);

    return result;
}

static PyObject *
divide_timedelta_int(PyDateTime_Delta *delta, PyObject *intobj)
{
    PyObject *pyus_in;
    PyObject *pyus_out;
    PyObject *result;

    pyus_in = delta_to_microseconds(delta);
    if (pyus_in == ((void *)0))
        return ((void *)0);

    pyus_out = PyNumber_FloorDivide(pyus_in, intobj);
    do { if ( --((PyObject*)(pyus_in))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_in)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_in)))); } while (0);
    if (pyus_out == ((void *)0))
        return ((void *)0);

    result = microseconds_to_delta_ex(pyus_out, &PyDateTime_DeltaType);
    do { if ( --((PyObject*)(pyus_out))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_out)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_out)))); } while (0);
    return result;
}

static PyObject *
divide_timedelta_timedelta(PyDateTime_Delta *left, PyDateTime_Delta *right)
{
    PyObject *pyus_left;
    PyObject *pyus_right;
    PyObject *result;

    pyus_left = delta_to_microseconds(left);
    if (pyus_left == ((void *)0))
        return ((void *)0);

    pyus_right = delta_to_microseconds(right);
    if (pyus_right == ((void *)0)) {
        do { if ( --((PyObject*)(pyus_left))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_left)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_left)))); } while (0);
        return ((void *)0);
    }

    result = PyNumber_FloorDivide(pyus_left, pyus_right);
    do { if ( --((PyObject*)(pyus_left))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_left)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_left)))); } while (0);
    do { if ( --((PyObject*)(pyus_right))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_right)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_right)))); } while (0);
    return result;
}

static PyObject *
truedivide_timedelta_timedelta(PyDateTime_Delta *left, PyDateTime_Delta *right)
{
    PyObject *pyus_left;
    PyObject *pyus_right;
    PyObject *result;

    pyus_left = delta_to_microseconds(left);
    if (pyus_left == ((void *)0))
        return ((void *)0);

    pyus_right = delta_to_microseconds(right);
    if (pyus_right == ((void *)0)) {
        do { if ( --((PyObject*)(pyus_left))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_left)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_left)))); } while (0);
        return ((void *)0);
    }

    result = PyNumber_TrueDivide(pyus_left, pyus_right);
    do { if ( --((PyObject*)(pyus_left))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_left)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_left)))); } while (0);
    do { if ( --((PyObject*)(pyus_right))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_right)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_right)))); } while (0);
    return result;
}

static PyObject *
truedivide_timedelta_float(PyDateTime_Delta *delta, PyObject *f)
{
    PyObject *result = ((void *)0);
    PyObject *pyus_in = ((void *)0), *temp, *pyus_out;
    PyObject *ratio = ((void *)0);
    static _Py_Identifier PyId_as_integer_ratio = { 0, "as_integer_ratio", 0 };

    pyus_in = delta_to_microseconds(delta);
    if (pyus_in == ((void *)0))
        return ((void *)0);
    ratio = _PyObject_CallMethodId(f, &PyId_as_integer_ratio, ((void *)0));
    if (ratio == ((void *)0))
        goto error;
    temp = PyNumber_Multiply(pyus_in, (((PyTupleObject *)(ratio))->ob_item[1]));
    do { if ( --((PyObject*)(pyus_in))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_in)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_in)))); } while (0);
    pyus_in = ((void *)0);
    if (temp == ((void *)0))
        goto error;
    pyus_out = divide_nearest(temp, (((PyTupleObject *)(ratio))->ob_item[0]));
    do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0);
    if (pyus_out == ((void *)0))
        goto error;
    result = microseconds_to_delta_ex(pyus_out, &PyDateTime_DeltaType);
    do { if ( --((PyObject*)(pyus_out))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_out)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_out)))); } while (0);
 error:
    do { if ((pyus_in) == ((void *)0)) ; else do { if ( --((PyObject*)(pyus_in))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_in)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_in)))); } while (0); } while (0);
    do { if ((ratio) == ((void *)0)) ; else do { if ( --((PyObject*)(ratio))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(ratio)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(ratio)))); } while (0); } while (0);

    return result;
}

static PyObject *
truedivide_timedelta_int(PyDateTime_Delta *delta, PyObject *i)
{
    PyObject *result;
    PyObject *pyus_in, *pyus_out;
    pyus_in = delta_to_microseconds(delta);
    if (pyus_in == ((void *)0))
        return ((void *)0);
    pyus_out = divide_nearest(pyus_in, i);
    do { if ( --((PyObject*)(pyus_in))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_in)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_in)))); } while (0);
    if (pyus_out == ((void *)0))
        return ((void *)0);
    result = microseconds_to_delta_ex(pyus_out, &PyDateTime_DeltaType);
    do { if ( --((PyObject*)(pyus_out))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_out)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_out)))); } while (0);

    return result;
}

static PyObject *
delta_add(PyObject *left, PyObject *right)
{
    PyObject *result = (&_Py_NotImplementedStruct);

    if (((((PyObject*)(left))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(left))->ob_type), (&PyDateTime_DeltaType))) && ((((PyObject*)(right))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(right))->ob_type), (&PyDateTime_DeltaType)))) {




        int days = (((PyDateTime_Delta *)(left))->days) + (((PyDateTime_Delta *)(right))->days);
        int seconds = (((PyDateTime_Delta *)(left))->seconds) + (((PyDateTime_Delta *)(right))->seconds);
        int microseconds = (((PyDateTime_Delta *)(left))->microseconds) +
                           (((PyDateTime_Delta *)(right))->microseconds);
        result = new_delta_ex(days, seconds, microseconds, 1, &PyDateTime_DeltaType);
    }

    if (result == (&_Py_NotImplementedStruct))
        ( ((PyObject*)(result))->ob_refcnt++);
    return result;
}

static PyObject *
delta_negative(PyDateTime_Delta *self)
{
    return new_delta_ex(-(((PyDateTime_Delta *)(self))->days), -(((PyDateTime_Delta *)(self))->seconds), -(((PyDateTime_Delta *)(self))->microseconds), 1, &PyDateTime_DeltaType);



}

static PyObject *
delta_positive(PyDateTime_Delta *self)
{



    return new_delta_ex((((PyDateTime_Delta *)(self))->days), (((PyDateTime_Delta *)(self))->seconds), (((PyDateTime_Delta *)(self))->microseconds), 0, &PyDateTime_DeltaType);



}

static PyObject *
delta_abs(PyDateTime_Delta *self)
{
    PyObject *result;

    (__builtin_expect(!((((PyDateTime_Delta *)(self))->microseconds) >= 0), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1773, "GET_TD_MICROSECONDS(self) >= 0") : (void)0);
    (__builtin_expect(!((((PyDateTime_Delta *)(self))->seconds) >= 0), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1774, "GET_TD_SECONDS(self) >= 0") : (void)0);

    if ((((PyDateTime_Delta *)(self))->days) < 0)
        result = delta_negative(self);
    else
        result = delta_positive(self);

    return result;
}

static PyObject *
delta_subtract(PyObject *left, PyObject *right)
{
    PyObject *result = (&_Py_NotImplementedStruct);

    if (((((PyObject*)(left))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(left))->ob_type), (&PyDateTime_DeltaType))) && ((((PyObject*)(right))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(right))->ob_type), (&PyDateTime_DeltaType)))) {




        int days = (((PyDateTime_Delta *)(left))->days) - (((PyDateTime_Delta *)(right))->days);
        int seconds = (((PyDateTime_Delta *)(left))->seconds) - (((PyDateTime_Delta *)(right))->seconds);
        int microseconds = (((PyDateTime_Delta *)(left))->microseconds) -
                           (((PyDateTime_Delta *)(right))->microseconds);
        result = new_delta_ex(days, seconds, microseconds, 1, &PyDateTime_DeltaType);
    }

    if (result == (&_Py_NotImplementedStruct))
        ( ((PyObject*)(result))->ob_refcnt++);
    return result;
}

static int
delta_cmp(PyObject *self, PyObject *other)
{
    int diff = (((PyDateTime_Delta *)(self))->days) - (((PyDateTime_Delta *)(other))->days);
    if (diff == 0) {
        diff = (((PyDateTime_Delta *)(self))->seconds) - (((PyDateTime_Delta *)(other))->seconds);
        if (diff == 0)
            diff = (((PyDateTime_Delta *)(self))->microseconds) -
                (((PyDateTime_Delta *)(other))->microseconds);
    }
    return diff;
}

static PyObject *
delta_richcompare(PyObject *self, PyObject *other, int op)
{
    if (((((PyObject*)(other))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(other))->ob_type), (&PyDateTime_DeltaType)))) {
        int diff = delta_cmp(self, other);
        return diff_to_bool(diff, op);
    }
    else {
        return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct);
    }
}

static PyObject *delta_getstate(PyDateTime_Delta *self);

static Py_hash_t
delta_hash(PyDateTime_Delta *self)
{
    if (self->hashcode == -1) {
        PyObject *temp = delta_getstate(self);
        if (temp != ((void *)0)) {
            self->hashcode = PyObject_Hash(temp);
            do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0);
        }
    }
    return self->hashcode;
}

static PyObject *
delta_multiply(PyObject *left, PyObject *right)
{
    PyObject *result = (&_Py_NotImplementedStruct);

    if (((((PyObject*)(left))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(left))->ob_type), (&PyDateTime_DeltaType)))) {

        if (((((((PyObject*)(right))->ob_type))->tp_flags & ((1L<<24))) != 0))
            result = multiply_int_timedelta(right,
                            (PyDateTime_Delta *) left);
        else if (((((PyObject*)(right))->ob_type) == (&PyFloat_Type) || PyType_IsSubtype((((PyObject*)(right))->ob_type), (&PyFloat_Type))))
            result = multiply_float_timedelta(right,
                            (PyDateTime_Delta *) left);
    }
    else if (((((((PyObject*)(left))->ob_type))->tp_flags & ((1L<<24))) != 0))
        result = multiply_int_timedelta(left,
                        (PyDateTime_Delta *) right);
    else if (((((PyObject*)(left))->ob_type) == (&PyFloat_Type) || PyType_IsSubtype((((PyObject*)(left))->ob_type), (&PyFloat_Type))))
        result = multiply_float_timedelta(left,
                        (PyDateTime_Delta *) right);

    if (result == (&_Py_NotImplementedStruct))
        ( ((PyObject*)(result))->ob_refcnt++);
    return result;
}

static PyObject *
delta_divide(PyObject *left, PyObject *right)
{
    PyObject *result = (&_Py_NotImplementedStruct);

    if (((((PyObject*)(left))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(left))->ob_type), (&PyDateTime_DeltaType)))) {

        if (((((((PyObject*)(right))->ob_type))->tp_flags & ((1L<<24))) != 0))
            result = divide_timedelta_int(
                            (PyDateTime_Delta *)left,
                            right);
        else if (((((PyObject*)(right))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(right))->ob_type), (&PyDateTime_DeltaType))))
            result = divide_timedelta_timedelta(
                            (PyDateTime_Delta *)left,
                            (PyDateTime_Delta *)right);
    }

    if (result == (&_Py_NotImplementedStruct))
        ( ((PyObject*)(result))->ob_refcnt++);
    return result;
}

static PyObject *
delta_truedivide(PyObject *left, PyObject *right)
{
    PyObject *result = (&_Py_NotImplementedStruct);

    if (((((PyObject*)(left))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(left))->ob_type), (&PyDateTime_DeltaType)))) {
        if (((((PyObject*)(right))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(right))->ob_type), (&PyDateTime_DeltaType))))
            result = truedivide_timedelta_timedelta(
                            (PyDateTime_Delta *)left,
                            (PyDateTime_Delta *)right);
        else if (((((PyObject*)(right))->ob_type) == (&PyFloat_Type) || PyType_IsSubtype((((PyObject*)(right))->ob_type), (&PyFloat_Type))))
            result = truedivide_timedelta_float(
                            (PyDateTime_Delta *)left, right);
        else if (((((((PyObject*)(right))->ob_type))->tp_flags & ((1L<<24))) != 0))
            result = truedivide_timedelta_int(
                            (PyDateTime_Delta *)left, right);
    }

    if (result == (&_Py_NotImplementedStruct))
        ( ((PyObject*)(result))->ob_refcnt++);
    return result;
}

static PyObject *
delta_remainder(PyObject *left, PyObject *right)
{
    PyObject *pyus_left;
    PyObject *pyus_right;
    PyObject *pyus_remainder;
    PyObject *remainder;

    if (!((((PyObject*)(left))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(left))->ob_type), (&PyDateTime_DeltaType))) || !((((PyObject*)(right))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(right))->ob_type), (&PyDateTime_DeltaType))))
        return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct);

    pyus_left = delta_to_microseconds((PyDateTime_Delta *)left);
    if (pyus_left == ((void *)0))
        return ((void *)0);

    pyus_right = delta_to_microseconds((PyDateTime_Delta *)right);
    if (pyus_right == ((void *)0)) {
        do { if ( --((PyObject*)(pyus_left))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_left)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_left)))); } while (0);
        return ((void *)0);
    }

    pyus_remainder = PyNumber_Remainder(pyus_left, pyus_right);
    do { if ( --((PyObject*)(pyus_left))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_left)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_left)))); } while (0);
    do { if ( --((PyObject*)(pyus_right))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_right)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_right)))); } while (0);
    if (pyus_remainder == ((void *)0))
        return ((void *)0);

    remainder = microseconds_to_delta_ex(pyus_remainder, &PyDateTime_DeltaType);
    do { if ( --((PyObject*)(pyus_remainder))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_remainder)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_remainder)))); } while (0);
    if (remainder == ((void *)0))
        return ((void *)0);

    return remainder;
}

static PyObject *
delta_divmod(PyObject *left, PyObject *right)
{
    PyObject *pyus_left;
    PyObject *pyus_right;
    PyObject *divmod;
    PyObject *delta;
    PyObject *result;

    if (!((((PyObject*)(left))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(left))->ob_type), (&PyDateTime_DeltaType))) || !((((PyObject*)(right))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(right))->ob_type), (&PyDateTime_DeltaType))))
        return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct);

    pyus_left = delta_to_microseconds((PyDateTime_Delta *)left);
    if (pyus_left == ((void *)0))
        return ((void *)0);

    pyus_right = delta_to_microseconds((PyDateTime_Delta *)right);
    if (pyus_right == ((void *)0)) {
        do { if ( --((PyObject*)(pyus_left))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_left)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_left)))); } while (0);
        return ((void *)0);
    }

    divmod = PyNumber_Divmod(pyus_left, pyus_right);
    do { if ( --((PyObject*)(pyus_left))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_left)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_left)))); } while (0);
    do { if ( --((PyObject*)(pyus_right))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pyus_right)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pyus_right)))); } while (0);
    if (divmod == ((void *)0))
        return ((void *)0);

    (__builtin_expect(!(PyTuple_Size(divmod) == 2), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 1980, "PyTuple_Size(divmod) == 2") : (void)0);
    delta = microseconds_to_delta_ex((((PyTupleObject *)(divmod))->ob_item[1]), &PyDateTime_DeltaType);
    if (delta == ((void *)0)) {
        do { if ( --((PyObject*)(divmod))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(divmod)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(divmod)))); } while (0);
        return ((void *)0);
    }
    result = PyTuple_Pack(2, (((PyTupleObject *)(divmod))->ob_item[0]), delta);
    do { if ( --((PyObject*)(delta))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(delta)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(delta)))); } while (0);
    do { if ( --((PyObject*)(divmod))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(divmod)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(divmod)))); } while (0);
    return result;
}
# 2001 "_datetimemodule.c"
static PyObject *
accum(const char* tag, PyObject *sofar, PyObject *num, PyObject *factor,
      double *leftover)
{
    PyObject *prod;
    PyObject *sum;

    (__builtin_expect(!(num != ((void *)0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 2008, "num != NULL") : (void)0);

    if (((((((PyObject*)(num))->ob_type))->tp_flags & ((1L<<24))) != 0)) {
        prod = PyNumber_Multiply(num, factor);
        if (prod == ((void *)0))
            return ((void *)0);
        sum = PyNumber_Add(sofar, prod);
        do { if ( --((PyObject*)(prod))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(prod)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(prod)))); } while (0);
        return sum;
    }

    if (((((PyObject*)(num))->ob_type) == (&PyFloat_Type) || PyType_IsSubtype((((PyObject*)(num))->ob_type), (&PyFloat_Type)))) {
        double dnum;
        double fracpart;
        double intpart;
        PyObject *x;
        PyObject *y;
# 2034 "_datetimemodule.c"
        dnum = PyFloat_AsDouble(num);
        if (dnum == -1.0 && PyErr_Occurred())
            return ((void *)0);
        fracpart = modf(dnum, &intpart);
        x = PyLong_FromDouble(intpart);
        if (x == ((void *)0))
            return ((void *)0);

        prod = PyNumber_Multiply(x, factor);
        do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);
        if (prod == ((void *)0))
            return ((void *)0);

        sum = PyNumber_Add(sofar, prod);
        do { if ( --((PyObject*)(prod))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(prod)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(prod)))); } while (0);
        if (sum == ((void *)0))
            return ((void *)0);

        if (fracpart == 0.0)
            return sum;




        (__builtin_expect(!(((((((PyObject*)(factor))->ob_type))->tp_flags & ((1L<<24))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 2058, "PyLong_Check(factor)") : (void)0);
        dnum = PyLong_AsDouble(factor);

        dnum *= fracpart;
        fracpart = modf(dnum, &intpart);
        x = PyLong_FromDouble(intpart);
        if (x == ((void *)0)) {
            do { if ( --((PyObject*)(sum))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sum)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sum)))); } while (0);
            return ((void *)0);
        }

        y = PyNumber_Add(sum, x);
        do { if ( --((PyObject*)(sum))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sum)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sum)))); } while (0);
        do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);
        *leftover += fracpart;
        return y;
    }

    PyErr_Format(PyExc_TypeError,
                 "unsupported type for timedelta %s component: %s",
                 tag, (((PyObject*)(num))->ob_type)->tp_name);
    return ((void *)0);
}

static PyObject *
delta_new(PyTypeObject *type, PyObject *args, PyObject *kw)
{
    PyObject *self = ((void *)0);


    PyObject *day = ((void *)0);
    PyObject *second = ((void *)0);
    PyObject *us = ((void *)0);
    PyObject *ms = ((void *)0);
    PyObject *minute = ((void *)0);
    PyObject *hour = ((void *)0);
    PyObject *week = ((void *)0);

    PyObject *x = ((void *)0);
    PyObject *y = ((void *)0);
    double leftover_us = 0.0;

    static char *keywords[] = {
        "days", "seconds", "microseconds", "milliseconds",
        "minutes", "hours", "weeks", ((void *)0)
    };

    if (PyArg_ParseTupleAndKeywords(args, kw, "|OOOOOOO:__new__",
                                    keywords,
                                    &day, &second, &us,
                                    &ms, &minute, &hour, &week) == 0)
        goto Done;

    x = PyLong_FromLong(0);
    if (x == ((void *)0))
        goto Done;







    if (us) {
        y = accum("microseconds", x, us, us_per_us, &leftover_us);
        do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0); x = y; if (x == ((void *)0)) goto Done;
    }
    if (ms) {
        y = accum("milliseconds", x, ms, us_per_ms, &leftover_us);
        do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0); x = y; if (x == ((void *)0)) goto Done;
    }
    if (second) {
        y = accum("seconds", x, second, us_per_second, &leftover_us);
        do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0); x = y; if (x == ((void *)0)) goto Done;
    }
    if (minute) {
        y = accum("minutes", x, minute, us_per_minute, &leftover_us);
        do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0); x = y; if (x == ((void *)0)) goto Done;
    }
    if (hour) {
        y = accum("hours", x, hour, us_per_hour, &leftover_us);
        do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0); x = y; if (x == ((void *)0)) goto Done;
    }
    if (day) {
        y = accum("days", x, day, us_per_day, &leftover_us);
        do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0); x = y; if (x == ((void *)0)) goto Done;
    }
    if (week) {
        y = accum("weeks", x, week, us_per_week, &leftover_us);
        do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0); x = y; if (x == ((void *)0)) goto Done;
    }
    if (leftover_us) {

        PyObject *temp = PyLong_FromLong(round_to_long(leftover_us));
        if (temp == ((void *)0)) {
            do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);
            goto Done;
        }
        y = PyNumber_Add(x, temp);
        do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0);
        do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0); x = y; if (x == ((void *)0)) goto Done;
    }

    self = microseconds_to_delta_ex(x, type);
    do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);
Done:
    return self;


}

static int
delta_bool(PyDateTime_Delta *self)
{
    return ((((PyDateTime_Delta *)(self))->days) != 0
        || (((PyDateTime_Delta *)(self))->seconds) != 0
        || (((PyDateTime_Delta *)(self))->microseconds) != 0);
}

static PyObject *
delta_repr(PyDateTime_Delta *self)
{
    if ((((PyDateTime_Delta *)(self))->microseconds) != 0)
        return PyUnicode_FromFormat("%s(%d, %d, %d)",
                                    (((PyObject*)(self))->ob_type)->tp_name,
                                    (((PyDateTime_Delta *)(self))->days),
                                    (((PyDateTime_Delta *)(self))->seconds),
                                    (((PyDateTime_Delta *)(self))->microseconds));
    if ((((PyDateTime_Delta *)(self))->seconds) != 0)
        return PyUnicode_FromFormat("%s(%d, %d)",
                                    (((PyObject*)(self))->ob_type)->tp_name,
                                    (((PyDateTime_Delta *)(self))->days),
                                    (((PyDateTime_Delta *)(self))->seconds));

    return PyUnicode_FromFormat("%s(%d)",
                                (((PyObject*)(self))->ob_type)->tp_name,
                                (((PyDateTime_Delta *)(self))->days));
}

static PyObject *
delta_str(PyDateTime_Delta *self)
{
    int us = (((PyDateTime_Delta *)(self))->microseconds);
    int seconds = (((PyDateTime_Delta *)(self))->seconds);
    int minutes = divmod(seconds, 60, &seconds);
    int hours = divmod(minutes, 60, &minutes);
    int days = (((PyDateTime_Delta *)(self))->days);

    if (days) {
        if (us)
            return PyUnicode_FromFormat("%d day%s, %d:%02d:%02d.%06d",
                                        days, (days == 1 || days == -1) ? "" : "s",
                                        hours, minutes, seconds, us);
        else
            return PyUnicode_FromFormat("%d day%s, %d:%02d:%02d",
                                        days, (days == 1 || days == -1) ? "" : "s",
                                        hours, minutes, seconds);
    } else {
        if (us)
            return PyUnicode_FromFormat("%d:%02d:%02d.%06d",
                                        hours, minutes, seconds, us);
        else
            return PyUnicode_FromFormat("%d:%02d:%02d",
                                        hours, minutes, seconds);
    }

}




static PyObject *
delta_getstate(PyDateTime_Delta *self)
{
    return Py_BuildValue("iii", (((PyDateTime_Delta *)(self))->days),
                                (((PyDateTime_Delta *)(self))->seconds),
                                (((PyDateTime_Delta *)(self))->microseconds));
}

static PyObject *
delta_total_seconds(PyObject *self)
{
    PyObject *total_seconds;
    PyObject *total_microseconds;
    PyObject *one_million;

    total_microseconds = delta_to_microseconds((PyDateTime_Delta *)self);
    if (total_microseconds == ((void *)0))
        return ((void *)0);

    one_million = PyLong_FromLong(1000000L);
    if (one_million == ((void *)0)) {
        do { if ( --((PyObject*)(total_microseconds))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(total_microseconds)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(total_microseconds)))); } while (0);
        return ((void *)0);
    }

    total_seconds = PyNumber_TrueDivide(total_microseconds, one_million);

    do { if ( --((PyObject*)(total_microseconds))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(total_microseconds)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(total_microseconds)))); } while (0);
    do { if ( --((PyObject*)(one_million))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(one_million)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(one_million)))); } while (0);
    return total_seconds;
}

static PyObject *
delta_reduce(PyDateTime_Delta* self)
{
    return Py_BuildValue("ON", (((PyObject*)(self))->ob_type), delta_getstate(self));
}



static PyMemberDef delta_members[] = {

    {"days", 1, __builtin_offsetof (PyDateTime_Delta, days), 1,
     "Number of days."},

    {"seconds", 1, __builtin_offsetof (PyDateTime_Delta, seconds), 1,
     "Number of seconds (>= 0 and less than 1 day)."},

    {"microseconds", 1, __builtin_offsetof (PyDateTime_Delta, microseconds), 1,
     "Number of microseconds (>= 0 and less than 1 second)."},
    {((void *)0)}
};

static PyMethodDef delta_methods[] = {
    {"total_seconds", (PyCFunction)delta_total_seconds, 0x0004,
     "Total seconds in the duration."},

    {"__reduce__", (PyCFunction)delta_reduce, 0x0004,
     "__reduce__() -> (cls, state)"},

    {((void *)0), ((void *)0)},
};

static char delta_doc[] =
"Difference between two datetime values.";

static PyNumberMethods delta_as_number = {
    delta_add,
    delta_subtract,
    delta_multiply,
    delta_remainder,
    delta_divmod,
    0,
    (unaryfunc)delta_negative,
    (unaryfunc)delta_positive,
    (unaryfunc)delta_abs,
    (inquiry)delta_bool,
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
    0,
    0,
    0,
    0,
    0,
    delta_divide,
    delta_truedivide,
    0,
    0,
};

static PyTypeObject PyDateTime_DeltaType = {
    { { 1, ((void *)0) }, 0 },
    "datetime.timedelta",
    sizeof(PyDateTime_Delta),
    0,
    0,
    0,
    0,
    0,
    0,
    (reprfunc)delta_repr,
    &delta_as_number,
    0,
    0,
    (hashfunc)delta_hash,
    0,
    (reprfunc)delta_str,
    PyObject_GenericGetAttr,
    0,
    0,
    ( 0 | (1L<<18) | 0) | (1L<<10),
    delta_doc,
    0,
    0,
    delta_richcompare,
    0,
    0,
    0,
    delta_methods,
    delta_members,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    delta_new,
    0,
};







static PyObject *
date_year(PyDateTime_Date *self, void *unused)
{
    return PyLong_FromLong(((((PyDateTime_Date*)self)->data[0] << 8) | ((PyDateTime_Date*)self)->data[1]));
}

static PyObject *
date_month(PyDateTime_Date *self, void *unused)
{
    return PyLong_FromLong((((PyDateTime_Date*)self)->data[2]));
}

static PyObject *
date_day(PyDateTime_Date *self, void *unused)
{
    return PyLong_FromLong((((PyDateTime_Date*)self)->data[3]));
}

static PyGetSetDef date_getset[] = {
    {"year", (getter)date_year},
    {"month", (getter)date_month},
    {"day", (getter)date_day},
    {((void *)0)}
};



static char *date_kws[] = {"year", "month", "day", ((void *)0)};

static PyObject *
date_new(PyTypeObject *type, PyObject *args, PyObject *kw)
{
    PyObject *self = ((void *)0);
    PyObject *state;
    int year;
    int month;
    int day;


    if ((((PyVarObject*)(args))->ob_size) == 1 &&
        ((((((PyObject*)(state = (((PyTupleObject *)(args))->ob_item[0])))->ob_type))->tp_flags & ((1L<<27))) != 0) &&
        ((__builtin_expect(!(((((((PyObject*)(state))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 2420, "PyBytes_Check(state)") : (void)0),(((PyVarObject*)(state))->ob_size)) == 4 &&
        ((unsigned int)(((__builtin_expect(!(((((((PyObject*)(state))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 2421, "PyBytes_Check(state)") : (void)0), (((PyBytesObject *)(state))->ob_sval))[2]) - 1 < 12))
    {
        PyDateTime_Date *me;

        me = (PyDateTime_Date *) (type->tp_alloc(type, 0));
        if (me != ((void *)0)) {
            char *pdata = ((__builtin_expect(!(((((((PyObject*)(state))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 2427, "PyBytes_Check(state)") : (void)0), (((PyBytesObject *)(state))->ob_sval));
            ((__builtin_object_size (me->data, 0) != (size_t) -1) ? __builtin___memcpy_chk (me->data, pdata, 4, __builtin_object_size (me->data, 0)) : __inline_memcpy_chk (me->data, pdata, 4));
            me->hashcode = -1;
        }
        return (PyObject *)me;
    }

    if (PyArg_ParseTupleAndKeywords(args, kw, "iii", date_kws,
                                    &year, &month, &day)) {
        if (check_date_args(year, month, day) < 0)
            return ((void *)0);
        self = new_date_ex(year, month, day, type);
    }
    return self;
}


static PyObject *
date_local_from_object(PyObject *cls, PyObject *obj)
{
    struct tm *tm;
    time_t t;

    if (_PyTime_ObjectToTime_t(obj, &t) == -1)
        return ((void *)0);

    tm = localtime(&t);
    if (tm == ((void *)0)) {


        if ((*__error()) == 0)
            (*__error()) = 22;

        PyErr_SetFromErrno(PyExc_OSError);
        return ((void *)0);
    }

    return PyObject_CallFunction(cls, "iii",
                                 tm->tm_year + 1900,
                                 tm->tm_mon + 1,
                                 tm->tm_mday);
}






static PyObject *
date_today(PyObject *cls, PyObject *dummy)
{
    PyObject *time;
    PyObject *result;
    static _Py_Identifier PyId_fromtimestamp = { 0, "fromtimestamp", 0 };

    time = time_time();
    if (time == ((void *)0))
        return ((void *)0);







    result = _PyObject_CallMethodId(cls, &PyId_fromtimestamp, "O", time);
    do { if ( --((PyObject*)(time))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(time)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(time)))); } while (0);
    return result;
}


static PyObject *
date_fromtimestamp(PyObject *cls, PyObject *args)
{
    PyObject *timestamp;
    PyObject *result = ((void *)0);

    if (PyArg_ParseTuple(args, "O:fromtimestamp", &timestamp))
        result = date_local_from_object(cls, timestamp);
    return result;
}




static PyObject *
date_fromordinal(PyObject *cls, PyObject *args)
{
    PyObject *result = ((void *)0);
    int ordinal;

    if (PyArg_ParseTuple(args, "i:fromordinal", &ordinal)) {
        int year;
        int month;
        int day;

        if (ordinal < 1)
            PyErr_SetString(PyExc_ValueError, "ordinal must be "
                                              ">= 1");
        else {
            ord_to_ymd(ordinal, &year, &month, &day);
            result = PyObject_CallFunction(cls, "iii",
                                           year, month, day);
        }
    }
    return result;
}
# 2542 "_datetimemodule.c"
static PyObject *
add_date_timedelta(PyDateTime_Date *date, PyDateTime_Delta *delta, int negate)
{
    PyObject *result = ((void *)0);
    int year = ((((PyDateTime_Date*)date)->data[0] << 8) | ((PyDateTime_Date*)date)->data[1]);
    int month = (((PyDateTime_Date*)date)->data[2]);
    int deltadays = (((PyDateTime_Delta *)(delta))->days);

    int day = (((PyDateTime_Date*)date)->data[3]) + (negate ? -deltadays : deltadays);

    if (normalize_date(&year, &month, &day) >= 0)
        result = new_date_ex(year, month, day, &PyDateTime_DateType);
    return result;
}

static PyObject *
date_add(PyObject *left, PyObject *right)
{
    if (((((PyObject*)(left))->ob_type) == (&PyDateTime_DateTimeType) || PyType_IsSubtype((((PyObject*)(left))->ob_type), (&PyDateTime_DateTimeType))) || ((((PyObject*)(right))->ob_type) == (&PyDateTime_DateTimeType) || PyType_IsSubtype((((PyObject*)(right))->ob_type), (&PyDateTime_DateTimeType))))
        return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct);

    if (((((PyObject*)(left))->ob_type) == (&PyDateTime_DateType) || PyType_IsSubtype((((PyObject*)(left))->ob_type), (&PyDateTime_DateType)))) {

        if (((((PyObject*)(right))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(right))->ob_type), (&PyDateTime_DeltaType))))

            return add_date_timedelta((PyDateTime_Date *) left,
                                      (PyDateTime_Delta *) right,
                                      0);
    }
    else {



        if (((((PyObject*)(left))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(left))->ob_type), (&PyDateTime_DeltaType))))

            return add_date_timedelta((PyDateTime_Date *) right,
                                      (PyDateTime_Delta *) left,
                                      0);
    }
    return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct);
}

static PyObject *
date_subtract(PyObject *left, PyObject *right)
{
    if (((((PyObject*)(left))->ob_type) == (&PyDateTime_DateTimeType) || PyType_IsSubtype((((PyObject*)(left))->ob_type), (&PyDateTime_DateTimeType))) || ((((PyObject*)(right))->ob_type) == (&PyDateTime_DateTimeType) || PyType_IsSubtype((((PyObject*)(right))->ob_type), (&PyDateTime_DateTimeType))))
        return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct);

    if (((((PyObject*)(left))->ob_type) == (&PyDateTime_DateType) || PyType_IsSubtype((((PyObject*)(left))->ob_type), (&PyDateTime_DateType)))) {
        if (((((PyObject*)(right))->ob_type) == (&PyDateTime_DateType) || PyType_IsSubtype((((PyObject*)(right))->ob_type), (&PyDateTime_DateType)))) {

            int left_ord = ymd_to_ord(((((PyDateTime_Date*)left)->data[0] << 8) | ((PyDateTime_Date*)left)->data[1]),
                                      (((PyDateTime_Date*)left)->data[2]),
                                      (((PyDateTime_Date*)left)->data[3]));
            int right_ord = ymd_to_ord(((((PyDateTime_Date*)right)->data[0] << 8) | ((PyDateTime_Date*)right)->data[1]),
                                       (((PyDateTime_Date*)right)->data[2]),
                                       (((PyDateTime_Date*)right)->data[3]));
            return new_delta_ex(left_ord - right_ord, 0, 0, 0, &PyDateTime_DeltaType);
        }
        if (((((PyObject*)(right))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(right))->ob_type), (&PyDateTime_DeltaType)))) {

            return add_date_timedelta((PyDateTime_Date *) left,
                                      (PyDateTime_Delta *) right,
                                      1);
        }
    }
    return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct);
}




static PyObject *
date_repr(PyDateTime_Date *self)
{
    return PyUnicode_FromFormat("%s(%d, %d, %d)",
                                (((PyObject*)(self))->ob_type)->tp_name,
                                ((((PyDateTime_Date*)self)->data[0] << 8) | ((PyDateTime_Date*)self)->data[1]), (((PyDateTime_Date*)self)->data[2]), (((PyDateTime_Date*)self)->data[3]));
}

static PyObject *
date_isoformat(PyDateTime_Date *self)
{
    return PyUnicode_FromFormat("%04d-%02d-%02d",
                                ((((PyDateTime_Date*)self)->data[0] << 8) | ((PyDateTime_Date*)self)->data[1]), (((PyDateTime_Date*)self)->data[2]), (((PyDateTime_Date*)self)->data[3]));
}


static PyObject *
date_str(PyDateTime_Date *self)
{
    static _Py_Identifier PyId_isoformat = { 0, "isoformat", 0 };

    return _PyObject_CallMethodId((PyObject *)self, &PyId_isoformat, "()");
}


static PyObject *
date_ctime(PyDateTime_Date *self)
{
    return format_ctime(self, 0, 0, 0);
}

static PyObject *
date_strftime(PyDateTime_Date *self, PyObject *args, PyObject *kw)
{



    PyObject *result;
    PyObject *tuple;
    PyObject *format;
    static _Py_Identifier PyId_timetuple = { 0, "timetuple", 0 };
    static char *keywords[] = {"format", ((void *)0)};

    if (! PyArg_ParseTupleAndKeywords(args, kw, "U:strftime", keywords,
                                      &format))
        return ((void *)0);

    tuple = _PyObject_CallMethodId((PyObject *)self, &PyId_timetuple, "()");
    if (tuple == ((void *)0))
        return ((void *)0);
    result = wrap_strftime((PyObject *)self, format, tuple,
                           (PyObject *)self);
    do { if ( --((PyObject*)(tuple))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tuple)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tuple)))); } while (0);
    return result;
}

static PyObject *
date_format(PyDateTime_Date *self, PyObject *args)
{
    PyObject *format;
    static _Py_Identifier PyId_strftime = { 0, "strftime", 0 };

    if (!PyArg_ParseTuple(args, "U:__format__", &format))
        return ((void *)0);


    if (PyUnicode_GetLength(format) == 0)
        return PyObject_Str((PyObject *)self);

    return _PyObject_CallMethodId((PyObject *)self, &PyId_strftime, "O", format);
}



static PyObject *
date_isoweekday(PyDateTime_Date *self)
{
    int dow = weekday(((((PyDateTime_Date*)self)->data[0] << 8) | ((PyDateTime_Date*)self)->data[1]), (((PyDateTime_Date*)self)->data[2]), (((PyDateTime_Date*)self)->data[3]));

    return PyLong_FromLong(dow + 1);
}

static PyObject *
date_isocalendar(PyDateTime_Date *self)
{
    int year = ((((PyDateTime_Date*)self)->data[0] << 8) | ((PyDateTime_Date*)self)->data[1]);
    int week1_monday = iso_week1_monday(year);
    int today = ymd_to_ord(year, (((PyDateTime_Date*)self)->data[2]), (((PyDateTime_Date*)self)->data[3]));
    int week;
    int day;

    week = divmod(today - week1_monday, 7, &day);
    if (week < 0) {
        --year;
        week1_monday = iso_week1_monday(year);
        week = divmod(today - week1_monday, 7, &day);
    }
    else if (week >= 52 && today >= iso_week1_monday(year + 1)) {
        ++year;
        week = 0;
    }
    return Py_BuildValue("iii", year, week + 1, day + 1);
}



static PyObject *
date_richcompare(PyObject *self, PyObject *other, int op)
{
    if (((((PyObject*)(other))->ob_type) == (&PyDateTime_DateType) || PyType_IsSubtype((((PyObject*)(other))->ob_type), (&PyDateTime_DateType)))) {
        int diff = memcmp(((PyDateTime_Date *)self)->data,
                          ((PyDateTime_Date *)other)->data,
                          4);
        return diff_to_bool(diff, op);
    }
    else
        return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct);
}

static PyObject *
date_timetuple(PyDateTime_Date *self)
{
    return build_struct_time(((((PyDateTime_Date*)self)->data[0] << 8) | ((PyDateTime_Date*)self)->data[1]),
                             (((PyDateTime_Date*)self)->data[2]),
                             (((PyDateTime_Date*)self)->data[3]),
                             0, 0, 0, -1);
}

static PyObject *
date_replace(PyDateTime_Date *self, PyObject *args, PyObject *kw)
{
    PyObject *clone;
    PyObject *tuple;
    int year = ((((PyDateTime_Date*)self)->data[0] << 8) | ((PyDateTime_Date*)self)->data[1]);
    int month = (((PyDateTime_Date*)self)->data[2]);
    int day = (((PyDateTime_Date*)self)->data[3]);

    if (! PyArg_ParseTupleAndKeywords(args, kw, "|iii:replace", date_kws,
                                      &year, &month, &day))
        return ((void *)0);
    tuple = Py_BuildValue("iii", year, month, day);
    if (tuple == ((void *)0))
        return ((void *)0);
    clone = date_new((((PyObject*)(self))->ob_type), tuple, ((void *)0));
    do { if ( --((PyObject*)(tuple))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tuple)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tuple)))); } while (0);
    return clone;
}

static Py_hash_t
generic_hash(unsigned char *data, int len)
{
    return _Py_HashBytes(data, len);
}


static PyObject *date_getstate(PyDateTime_Date *self);

static Py_hash_t
date_hash(PyDateTime_Date *self)
{
    if (self->hashcode == -1)
        self->hashcode = generic_hash(
            (unsigned char *)self->data, 4);

    return self->hashcode;
}

static PyObject *
date_toordinal(PyDateTime_Date *self)
{
    return PyLong_FromLong(ymd_to_ord(((((PyDateTime_Date*)self)->data[0] << 8) | ((PyDateTime_Date*)self)->data[1]), (((PyDateTime_Date*)self)->data[2]),
                                     (((PyDateTime_Date*)self)->data[3])));
}

static PyObject *
date_weekday(PyDateTime_Date *self)
{
    int dow = weekday(((((PyDateTime_Date*)self)->data[0] << 8) | ((PyDateTime_Date*)self)->data[1]), (((PyDateTime_Date*)self)->data[2]), (((PyDateTime_Date*)self)->data[3]));

    return PyLong_FromLong(dow);
}




static PyObject *
date_getstate(PyDateTime_Date *self)
{
    PyObject* field;
    field = PyBytes_FromStringAndSize((char*)self->data,
                                       4);
    return Py_BuildValue("(N)", field);
}

static PyObject *
date_reduce(PyDateTime_Date *self, PyObject *arg)
{
    return Py_BuildValue("(ON)", (((PyObject*)(self))->ob_type), date_getstate(self));
}

static PyMethodDef date_methods[] = {



    {"fromtimestamp", (PyCFunction)date_fromtimestamp, 0x0001 |
                                                       0x0010,
     "timestamp -> local date from a POSIX timestamp (like " "time.time())."},


    {"fromordinal", (PyCFunction)date_fromordinal, 0x0001 |
                                                    0x0010,
     "int -> date corresponding to a proleptic Gregorian " "ordinal."},


    {"today", (PyCFunction)date_today, 0x0004 | 0x0010,
     "Current date or datetime:  same as " "self.__class__.fromtimestamp(time.time())."},




    {"ctime", (PyCFunction)date_ctime, 0x0004,
     "Return ctime() style string."},

    {"strftime", (PyCFunction)date_strftime, 0x0001 | 0x0002,
     "format -> strftime() style string."},

    {"__format__", (PyCFunction)date_format, 0x0001,
     "Formats self with strftime."},

    {"timetuple", (PyCFunction)date_timetuple, 0x0004,
     "Return time tuple, compatible with time.localtime()."},

    {"isocalendar", (PyCFunction)date_isocalendar, 0x0004,
     "Return a 3-tuple containing ISO year, week number, and " "weekday."},


    {"isoformat", (PyCFunction)date_isoformat, 0x0004,
     "Return string in ISO 8601 format, YYYY-MM-DD."},

    {"isoweekday", (PyCFunction)date_isoweekday, 0x0004,
     "Return the day of the week represented by the date.\n" "Monday == 1 ... Sunday == 7"},


    {"toordinal", (PyCFunction)date_toordinal, 0x0004,
     "Return proleptic Gregorian ordinal.  January 1 of year " "1 is day 1."},


    {"weekday", (PyCFunction)date_weekday, 0x0004,
     "Return the day of the week represented by the date.\n" "Monday == 0 ... Sunday == 6"},


    {"replace", (PyCFunction)date_replace, 0x0001 | 0x0002,
     "Return date with new specified fields."},

    {"__reduce__", (PyCFunction)date_reduce, 0x0004,
     "__reduce__() -> (cls, state)"},

    {((void *)0), ((void *)0)}
};

static char date_doc[] =
"date(year, month, day) --> date object";

static PyNumberMethods date_as_number = {
    date_add,
    date_subtract,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
};

static PyTypeObject PyDateTime_DateType = {
    { { 1, ((void *)0) }, 0 },
    "datetime.date",
    sizeof(PyDateTime_Date),
    0,
    0,
    0,
    0,
    0,
    0,
    (reprfunc)date_repr,
    &date_as_number,
    0,
    0,
    (hashfunc)date_hash,
    0,
    (reprfunc)date_str,
    PyObject_GenericGetAttr,
    0,
    0,
    ( 0 | (1L<<18) | 0) | (1L<<10),
    date_doc,
    0,
    0,
    date_richcompare,
    0,
    0,
    0,
    date_methods,
    0,
    date_getset,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    date_new,
    0,
};
# 2949 "_datetimemodule.c"
static PyObject *
tzinfo_nogo(const char* methodname)
{
    PyErr_Format(PyExc_NotImplementedError,
                 "a tzinfo subclass must implement %s()",
                 methodname);
    return ((void *)0);
}



static PyObject *
tzinfo_tzname(PyDateTime_TZInfo *self, PyObject *dt)
{
    return tzinfo_nogo("tzname");
}

static PyObject *
tzinfo_utcoffset(PyDateTime_TZInfo *self, PyObject *dt)
{
    return tzinfo_nogo("utcoffset");
}

static PyObject *
tzinfo_dst(PyDateTime_TZInfo *self, PyObject *dt)
{
    return tzinfo_nogo("dst");
}


static PyObject *add_datetime_timedelta(PyDateTime_DateTime *date,
                                        PyDateTime_Delta *delta,
                                        int factor);
static PyObject *datetime_utcoffset(PyObject *self, PyObject *);
static PyObject *datetime_dst(PyObject *self, PyObject *);

static PyObject *
tzinfo_fromutc(PyDateTime_TZInfo *self, PyObject *dt)
{
    PyObject *result = ((void *)0);
    PyObject *off = ((void *)0), *dst = ((void *)0);
    PyDateTime_Delta *delta = ((void *)0);

    if (!((((PyObject*)(dt))->ob_type) == (&PyDateTime_DateTimeType) || PyType_IsSubtype((((PyObject*)(dt))->ob_type), (&PyDateTime_DateTimeType)))) {
        PyErr_SetString(PyExc_TypeError,
                        "fromutc: argument must be a datetime");
        return ((void *)0);
    }
    if (((((_PyDateTime_BaseTZInfo *)(dt))->hastzinfo) ? ((PyDateTime_DateTime *)(dt))->tzinfo : (&_Py_NoneStruct)) != (PyObject *)self) {
        PyErr_SetString(PyExc_ValueError, "fromutc: dt.tzinfo "
                        "is not self");
        return ((void *)0);
    }

    off = datetime_utcoffset(dt, ((void *)0));
    if (off == ((void *)0))
        return ((void *)0);
    if (off == (&_Py_NoneStruct)) {
        PyErr_SetString(PyExc_ValueError, "fromutc: non-None "
                        "utcoffset() result required");
        goto Fail;
    }

    dst = datetime_dst(dt, ((void *)0));
    if (dst == ((void *)0))
        goto Fail;
    if (dst == (&_Py_NoneStruct)) {
        PyErr_SetString(PyExc_ValueError, "fromutc: non-None "
                        "dst() result required");
        goto Fail;
    }

    delta = (PyDateTime_Delta *)delta_subtract(off, dst);
    if (delta == ((void *)0))
        goto Fail;
    result = add_datetime_timedelta((PyDateTime_DateTime *)dt, delta, 1);
    if (result == ((void *)0))
        goto Fail;

    do { if ( --((PyObject*)(dst))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dst)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dst)))); } while (0);
    dst = call_dst(((((_PyDateTime_BaseTZInfo *)(dt))->hastzinfo) ? ((PyDateTime_DateTime *)(dt))->tzinfo : (&_Py_NoneStruct)), result);
    if (dst == ((void *)0))
        goto Fail;
    if (dst == (&_Py_NoneStruct))
        goto Inconsistent;
    if (delta_bool(delta) != 0) {
        PyObject *temp = result;
        result = add_datetime_timedelta((PyDateTime_DateTime *)result,
                                        (PyDateTime_Delta *)dst, 1);
        do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0);
        if (result == ((void *)0))
            goto Fail;
    }
    do { if ( --((PyObject*)(delta))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(delta)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(delta)))); } while (0);
    do { if ( --((PyObject*)(dst))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dst)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dst)))); } while (0);
    do { if ( --((PyObject*)(off))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(off)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(off)))); } while (0);
    return result;

Inconsistent:
    PyErr_SetString(PyExc_ValueError, "fromutc: tz.dst() gave"
                    "inconsistent results; cannot convert");


Fail:
    do { if ((off) == ((void *)0)) ; else do { if ( --((PyObject*)(off))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(off)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(off)))); } while (0); } while (0);
    do { if ((dst) == ((void *)0)) ; else do { if ( --((PyObject*)(dst))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dst)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dst)))); } while (0); } while (0);
    do { if ((delta) == ((void *)0)) ; else do { if ( --((PyObject*)(delta))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(delta)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(delta)))); } while (0); } while (0);
    do { if ((result) == ((void *)0)) ; else do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0); } while (0);
    return ((void *)0);
}






static PyObject *
tzinfo_reduce(PyObject *self)
{
    PyObject *args, *state, *tmp;
    PyObject *getinitargs, *getstate;
    static _Py_Identifier PyId___getinitargs__ = { 0, "__getinitargs__", 0 };
    static _Py_Identifier PyId___getstate__ = { 0, "__getstate__", 0 };

    tmp = PyTuple_New(0);
    if (tmp == ((void *)0))
        return ((void *)0);

    getinitargs = _PyObject_GetAttrId(self, &PyId___getinitargs__);
    if (getinitargs != ((void *)0)) {
        args = PyObject_CallObject(getinitargs, tmp);
        do { if ( --((PyObject*)(getinitargs))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(getinitargs)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(getinitargs)))); } while (0);
        if (args == ((void *)0)) {
            do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0);
            return ((void *)0);
        }
    }
    else {
        PyErr_Clear();
        args = tmp;
        ( ((PyObject*)(args))->ob_refcnt++);
    }

    getstate = _PyObject_GetAttrId(self, &PyId___getstate__);
    if (getstate != ((void *)0)) {
        state = PyObject_CallObject(getstate, tmp);
        do { if ( --((PyObject*)(getstate))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(getstate)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(getstate)))); } while (0);
        if (state == ((void *)0)) {
            do { if ( --((PyObject*)(args))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(args)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(args)))); } while (0);
            do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0);
            return ((void *)0);
        }
    }
    else {
        PyObject **dictptr;
        PyErr_Clear();
        state = (&_Py_NoneStruct);
        dictptr = _PyObject_GetDictPtr(self);
        if (dictptr && *dictptr && PyDict_Size(*dictptr))
            state = *dictptr;
        ( ((PyObject*)(state))->ob_refcnt++);
    }

    do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0);

    if (state == (&_Py_NoneStruct)) {
        do { if ( --((PyObject*)(state))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(state)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(state)))); } while (0);
        return Py_BuildValue("(ON)", (((PyObject*)(self))->ob_type), args);
    }
    else
        return Py_BuildValue("(ONN)", (((PyObject*)(self))->ob_type), args, state);
}

static PyMethodDef tzinfo_methods[] = {

    {"tzname", (PyCFunction)tzinfo_tzname, 0x0008,
     "datetime -> string name of time zone."},

    {"utcoffset", (PyCFunction)tzinfo_utcoffset, 0x0008,
     "datetime -> timedelta showing offset from UTC, negative " "values indicating West of UTC"},


    {"dst", (PyCFunction)tzinfo_dst, 0x0008,
     "datetime -> DST offset in minutes east of UTC."},

    {"fromutc", (PyCFunction)tzinfo_fromutc, 0x0008,
     "datetime in UTC -> datetime in local time."},

    {"__reduce__", (PyCFunction)tzinfo_reduce, 0x0004,
     "-> (cls, state)"},

    {((void *)0), ((void *)0)}
};

static char tzinfo_doc[] =
"Abstract base class for time zone info objects.";

static PyTypeObject PyDateTime_TZInfoType = {
    { { 1, ((void *)0) }, 0 },
    "datetime.tzinfo",
    sizeof(PyDateTime_TZInfo),
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
    PyObject_GenericGetAttr,
    0,
    0,
    ( 0 | (1L<<18) | 0) | (1L<<10),
    tzinfo_doc,
    0,
    0,
    0,
    0,
    0,
    0,
    tzinfo_methods,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    PyType_GenericNew,
    0,
};

static char *timezone_kws[] = {"offset", "name", ((void *)0)};

static PyObject *
timezone_new(PyTypeObject *type, PyObject *args, PyObject *kw)
{
    PyObject *offset;
    PyObject *name = ((void *)0);
    if (PyArg_ParseTupleAndKeywords(args, kw, "O!|O!:timezone", timezone_kws,
                                    &PyDateTime_DeltaType, &offset,
                                    &PyUnicode_Type, &name))
        return new_timezone(offset, name);

    return ((void *)0);
}

static void
timezone_dealloc(PyDateTime_TimeZone *self)
{
    do { if (self->offset) { PyObject *_py_tmp = (PyObject *)(self->offset); (self->offset) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (self->name) { PyObject *_py_tmp = (PyObject *)(self->name); (self->name) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    (((PyObject*)(self))->ob_type)->tp_free((PyObject *)self);
}

static PyObject *
timezone_richcompare(PyDateTime_TimeZone *self,
                     PyDateTime_TimeZone *other, int op)
{
    if (op != 2 && op != 3)
        return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct);
    if ((((PyObject*)(other))->ob_type) != &PyDateTime_TimeZoneType) {
 if (op == 2)
     return ( ((PyObject*)(((PyObject *) &_Py_FalseStruct)))->ob_refcnt++), ((PyObject *) &_Py_FalseStruct);
 else
     return ( ((PyObject*)(((PyObject *) &_Py_TrueStruct)))->ob_refcnt++), ((PyObject *) &_Py_TrueStruct);
    }
    return delta_richcompare(self->offset, other->offset, op);
}

static Py_hash_t
timezone_hash(PyDateTime_TimeZone *self)
{
    return delta_hash((PyDateTime_Delta *)self->offset);
}





static int
_timezone_check_argument(PyObject *dt, const char *meth)
{
    if (dt == (&_Py_NoneStruct) || ((((PyObject*)(dt))->ob_type) == (&PyDateTime_DateTimeType) || PyType_IsSubtype((((PyObject*)(dt))->ob_type), (&PyDateTime_DateTimeType))))
        return 0;
    PyErr_Format(PyExc_TypeError, "%s(dt) argument must be a datetime instance"
                 " or None, not %.200s", meth, (((PyObject*)(dt))->ob_type)->tp_name);
    return -1;
}

static PyObject *
timezone_repr(PyDateTime_TimeZone *self)
{


    const char *type_name = (((PyObject*)(self))->ob_type)->tp_name;

    if (((PyObject *)self) == PyDateTime_TimeZone_UTC)
        return PyUnicode_FromFormat("%s.utc", type_name);

    if (self->name == ((void *)0))
        return PyUnicode_FromFormat("%s(%R)", type_name, self->offset);

    return PyUnicode_FromFormat("%s(%R, %R)", type_name, self->offset,
                                self->name);
}


static PyObject *
timezone_str(PyDateTime_TimeZone *self)
{
    int hours, minutes, seconds;
    PyObject *offset;
    char sign;

    if (self->name != ((void *)0)) {
        ( ((PyObject*)(self->name))->ob_refcnt++);
        return self->name;
    }

    if ((((PyDateTime_Delta *)(self->offset))->days) < 0) {
        sign = '-';
        offset = delta_negative((PyDateTime_Delta *)self->offset);
        if (offset == ((void *)0))
            return ((void *)0);
    }
    else {
        sign = '+';
        offset = self->offset;
        ( ((PyObject*)(offset))->ob_refcnt++);
    }

    seconds = (((PyDateTime_Delta *)(offset))->seconds);
    do { if ( --((PyObject*)(offset))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset)))); } while (0);
    minutes = divmod(seconds, 60, &seconds);
    hours = divmod(minutes, 60, &minutes);

    (__builtin_expect(!(seconds == 0), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 3293, "seconds == 0") : (void)0);
    return PyUnicode_FromFormat("UTC%c%02d:%02d", sign, hours, minutes);
}

static PyObject *
timezone_tzname(PyDateTime_TimeZone *self, PyObject *dt)
{
    if (_timezone_check_argument(dt, "tzname") == -1)
        return ((void *)0);

    return timezone_str(self);
}

static PyObject *
timezone_utcoffset(PyDateTime_TimeZone *self, PyObject *dt)
{
    if (_timezone_check_argument(dt, "utcoffset") == -1)
        return ((void *)0);

    ( ((PyObject*)(self->offset))->ob_refcnt++);
    return self->offset;
}

static PyObject *
timezone_dst(PyObject *self, PyObject *dt)
{
    if (_timezone_check_argument(dt, "dst") == -1)
        return ((void *)0);

    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}

static PyObject *
timezone_fromutc(PyDateTime_TimeZone *self, PyDateTime_DateTime *dt)
{
    if (!((((PyObject*)(dt))->ob_type) == (&PyDateTime_DateTimeType) || PyType_IsSubtype((((PyObject*)(dt))->ob_type), (&PyDateTime_DateTimeType)))) {
        PyErr_SetString(PyExc_TypeError,
                        "fromutc: argument must be a datetime");
        return ((void *)0);
    }
    if (!(((_PyDateTime_BaseTZInfo *)(dt))->hastzinfo) || dt->tzinfo != (PyObject *)self) {
        PyErr_SetString(PyExc_ValueError, "fromutc: dt.tzinfo "
                        "is not self");
        return ((void *)0);
    }

    return add_datetime_timedelta(dt, (PyDateTime_Delta *)self->offset, 1);
}

static PyObject *
timezone_getinitargs(PyDateTime_TimeZone *self)
{
    if (self->name == ((void *)0))
        return Py_BuildValue("(O)", self->offset);
    return Py_BuildValue("(OO)", self->offset, self->name);
}

static PyMethodDef timezone_methods[] = {
    {"tzname", (PyCFunction)timezone_tzname, 0x0008,
     "If name is specified when timezone is created, returns the name." "  Otherwise returns offset as 'UTC(+|-)HH:MM'."},


    {"utcoffset", (PyCFunction)timezone_utcoffset, 0x0008,
     "Return fixed offset."},

    {"dst", (PyCFunction)timezone_dst, 0x0008,
     "Return None."},

    {"fromutc", (PyCFunction)timezone_fromutc, 0x0008,
     "datetime in UTC -> datetime in local time."},

    {"__getinitargs__", (PyCFunction)timezone_getinitargs, 0x0004,
     "pickle support"},

    {((void *)0), ((void *)0)}
};

static char timezone_doc[] =
"Fixed offset from UTC implementation of tzinfo.";

static PyTypeObject PyDateTime_TimeZoneType = {
    { { 1, ((void *)0) }, 0 },
    "datetime.timezone",
    sizeof(PyDateTime_TimeZone),
    0,
    (destructor)timezone_dealloc,
    0,
    0,
    0,
    0,
    (reprfunc)timezone_repr,
    0,
    0,
    0,
    (hashfunc)timezone_hash,
    0,
    (reprfunc)timezone_str,
    0,
    0,
    0,
    ( 0 | (1L<<18) | 0),
    timezone_doc,
    0,
    0,
    (richcmpfunc)timezone_richcompare,
    0,
    0,
    0,
    timezone_methods,
    0,
    0,
    &PyDateTime_TZInfoType,
    0,
    0,
    0,
    0,
    0,
    0,
    timezone_new,
};
# 3421 "_datetimemodule.c"
static PyObject *
time_hour(PyDateTime_Time *self, void *unused)
{
    return PyLong_FromLong((((PyDateTime_Time*)self)->data[0]));
}

static PyObject *
time_minute(PyDateTime_Time *self, void *unused)
{
    return PyLong_FromLong((((PyDateTime_Time*)self)->data[1]));
}


static PyObject *
py_time_second(PyDateTime_Time *self, void *unused)
{
    return PyLong_FromLong((((PyDateTime_Time*)self)->data[2]));
}

static PyObject *
time_microsecond(PyDateTime_Time *self, void *unused)
{
    return PyLong_FromLong(((((PyDateTime_Time*)self)->data[3] << 16) | (((PyDateTime_Time*)self)->data[4] << 8) | ((PyDateTime_Time*)self)->data[5]));
}

static PyObject *
time_tzinfo(PyDateTime_Time *self, void *unused)
{
    PyObject *result = (((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) ? self->tzinfo : (&_Py_NoneStruct);
    ( ((PyObject*)(result))->ob_refcnt++);
    return result;
}

static PyGetSetDef time_getset[] = {
    {"hour", (getter)time_hour},
    {"minute", (getter)time_minute},
    {"second", (getter)py_time_second},
    {"microsecond", (getter)time_microsecond},
    {"tzinfo", (getter)time_tzinfo},
    {((void *)0)}
};





static char *time_kws[] = {"hour", "minute", "second", "microsecond",
                           "tzinfo", ((void *)0)};

static PyObject *
time_new(PyTypeObject *type, PyObject *args, PyObject *kw)
{
    PyObject *self = ((void *)0);
    PyObject *state;
    int hour = 0;
    int minute = 0;
    int second = 0;
    int usecond = 0;
    PyObject *tzinfo = (&_Py_NoneStruct);


    if ((((PyVarObject*)(args))->ob_size) >= 1 &&
        (((PyVarObject*)(args))->ob_size) <= 2 &&
        ((((((PyObject*)(state = (((PyTupleObject *)(args))->ob_item[0])))->ob_type))->tp_flags & ((1L<<27))) != 0) &&
        ((__builtin_expect(!(((((((PyObject*)(state))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 3485, "PyBytes_Check(state)") : (void)0),(((PyVarObject*)(state))->ob_size)) == 6 &&
        ((unsigned char) (((__builtin_expect(!(((((((PyObject*)(state))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 3486, "PyBytes_Check(state)") : (void)0), (((PyBytesObject *)(state))->ob_sval))[0])) < 24)
    {
        PyDateTime_Time *me;
        char aware;

        if ((((PyVarObject*)(args))->ob_size) == 2) {
            tzinfo = (((PyTupleObject *)(args))->ob_item[1]);
            if (check_tzinfo_subclass(tzinfo) < 0) {
                PyErr_SetString(PyExc_TypeError, "bad "
                    "tzinfo state arg");
                return ((void *)0);
            }
        }
        aware = (char)(tzinfo != (&_Py_NoneStruct));
        me = (PyDateTime_Time *) (type->tp_alloc(type, aware));
        if (me != ((void *)0)) {
            char *pdata = ((__builtin_expect(!(((((((PyObject*)(state))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 3502, "PyBytes_Check(state)") : (void)0), (((PyBytesObject *)(state))->ob_sval));

            ((__builtin_object_size (me->data, 0) != (size_t) -1) ? __builtin___memcpy_chk (me->data, pdata, 6, __builtin_object_size (me->data, 0)) : __inline_memcpy_chk (me->data, pdata, 6));
            me->hashcode = -1;
            me->hastzinfo = aware;
            if (aware) {
                ( ((PyObject*)(tzinfo))->ob_refcnt++);
                me->tzinfo = tzinfo;
            }
        }
        return (PyObject *)me;
    }

    if (PyArg_ParseTupleAndKeywords(args, kw, "|iiiiO", time_kws,
                                    &hour, &minute, &second, &usecond,
                                    &tzinfo)) {
        if (check_time_args(hour, minute, second, usecond) < 0)
            return ((void *)0);
        if (check_tzinfo_subclass(tzinfo) < 0)
            return ((void *)0);
        self = new_time_ex(hour, minute, second, usecond, tzinfo,
                           type);
    }
    return self;
}





static void
time_dealloc(PyDateTime_Time *self)
{
    if ((((_PyDateTime_BaseTZInfo *)(self))->hastzinfo)) {
        do { if ((self->tzinfo) == ((void *)0)) ; else do { if ( --((PyObject*)(self->tzinfo))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->tzinfo)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->tzinfo)))); } while (0); } while (0);
    }
    (((PyObject*)(self))->ob_type)->tp_free((PyObject *)self);
}






static PyObject *
time_utcoffset(PyObject *self, PyObject *unused) {
    return call_utcoffset(((((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) ? ((PyDateTime_Time *)(self))->tzinfo : (&_Py_NoneStruct)), (&_Py_NoneStruct));
}

static PyObject *
time_dst(PyObject *self, PyObject *unused) {
    return call_dst(((((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) ? ((PyDateTime_Time *)(self))->tzinfo : (&_Py_NoneStruct)), (&_Py_NoneStruct));
}

static PyObject *
time_tzname(PyDateTime_Time *self, PyObject *unused) {
    return call_tzname(((((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) ? ((PyDateTime_Time *)(self))->tzinfo : (&_Py_NoneStruct)), (&_Py_NoneStruct));
}





static PyObject *
time_repr(PyDateTime_Time *self)
{
    const char *type_name = (((PyObject*)(self))->ob_type)->tp_name;
    int h = (((PyDateTime_Time*)self)->data[0]);
    int m = (((PyDateTime_Time*)self)->data[1]);
    int s = (((PyDateTime_Time*)self)->data[2]);
    int us = ((((PyDateTime_Time*)self)->data[3] << 16) | (((PyDateTime_Time*)self)->data[4] << 8) | ((PyDateTime_Time*)self)->data[5]);
    PyObject *result = ((void *)0);

    if (us)
        result = PyUnicode_FromFormat("%s(%d, %d, %d, %d)",
                                      type_name, h, m, s, us);
    else if (s)
        result = PyUnicode_FromFormat("%s(%d, %d, %d)",
                                      type_name, h, m, s);
    else
        result = PyUnicode_FromFormat("%s(%d, %d)", type_name, h, m);
    if (result != ((void *)0) && (((_PyDateTime_BaseTZInfo *)(self))->hastzinfo))
        result = append_keyword_tzinfo(result, self->tzinfo);
    return result;
}

static PyObject *
time_str(PyDateTime_Time *self)
{
    static _Py_Identifier PyId_isoformat = { 0, "isoformat", 0 };

    return _PyObject_CallMethodId((PyObject *)self, &PyId_isoformat, "()");
}

static PyObject *
time_isoformat(PyDateTime_Time *self, PyObject *unused)
{
    char buf[100];
    PyObject *result;
    int us = ((((PyDateTime_Time*)self)->data[3] << 16) | (((PyDateTime_Time*)self)->data[4] << 8) | ((PyDateTime_Time*)self)->data[5]);

    if (us)
        result = PyUnicode_FromFormat("%02d:%02d:%02d.%06d",
                                      (((PyDateTime_Time*)self)->data[0]),
                                      (((PyDateTime_Time*)self)->data[1]),
                                      (((PyDateTime_Time*)self)->data[2]),
                                      us);
    else
        result = PyUnicode_FromFormat("%02d:%02d:%02d",
                                      (((PyDateTime_Time*)self)->data[0]),
                                      (((PyDateTime_Time*)self)->data[1]),
                                      (((PyDateTime_Time*)self)->data[2]));

    if (result == ((void *)0) || !(((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) || self->tzinfo == (&_Py_NoneStruct))
        return result;


    if (format_utcoffset(buf, sizeof(buf), ":", self->tzinfo,
                         (&_Py_NoneStruct)) < 0) {
        do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0);
        return ((void *)0);
    }
    PyUnicode_AppendAndDel(&result, PyUnicode_FromString(buf));
    return result;
}

static PyObject *
time_strftime(PyDateTime_Time *self, PyObject *args, PyObject *kw)
{
    PyObject *result;
    PyObject *tuple;
    PyObject *format;
    static char *keywords[] = {"format", ((void *)0)};

    if (! PyArg_ParseTupleAndKeywords(args, kw, "U:strftime", keywords,
                                      &format))
        return ((void *)0);





    tuple = Py_BuildValue("iiiiiiiii",
                          1900, 1, 1,
                  (((PyDateTime_Time*)self)->data[0]),
                  (((PyDateTime_Time*)self)->data[1]),
                  (((PyDateTime_Time*)self)->data[2]),
                  0, 1, -1);
    if (tuple == ((void *)0))
        return ((void *)0);
    (__builtin_expect(!(PyTuple_Size(tuple) == 9), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 3652, "PyTuple_Size(tuple) == 9") : (void)0);
    result = wrap_strftime((PyObject *)self, format, tuple,
                           (&_Py_NoneStruct));
    do { if ( --((PyObject*)(tuple))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tuple)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tuple)))); } while (0);
    return result;
}





static PyObject *
time_richcompare(PyObject *self, PyObject *other, int op)
{
    PyObject *result = ((void *)0);
    PyObject *offset1, *offset2;
    int diff;

    if (! ((((PyObject*)(other))->ob_type) == (&PyDateTime_TimeType) || PyType_IsSubtype((((PyObject*)(other))->ob_type), (&PyDateTime_TimeType))))
        return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct);

    if (((((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) ? ((PyDateTime_Time *)(self))->tzinfo : (&_Py_NoneStruct)) == ((((_PyDateTime_BaseTZInfo *)(other))->hastzinfo) ? ((PyDateTime_Time *)(other))->tzinfo : (&_Py_NoneStruct))) {
        diff = memcmp(((PyDateTime_Time *)self)->data,
                      ((PyDateTime_Time *)other)->data,
                      6);
        return diff_to_bool(diff, op);
    }
    offset1 = time_utcoffset(self, ((void *)0));
    if (offset1 == ((void *)0))
        return ((void *)0);
    offset2 = time_utcoffset(other, ((void *)0));
    if (offset2 == ((void *)0))
        goto done;




    if ((offset1 == offset2) ||
        (((((PyObject*)(offset1))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(offset1))->ob_type), (&PyDateTime_DeltaType))) && ((((PyObject*)(offset2))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(offset2))->ob_type), (&PyDateTime_DeltaType))) &&
         delta_cmp(offset1, offset2) == 0)) {
        diff = memcmp(((PyDateTime_Time *)self)->data,
                      ((PyDateTime_Time *)other)->data,
                      6);
        result = diff_to_bool(diff, op);
    }

    else if (offset1 != (&_Py_NoneStruct) && offset2 != (&_Py_NoneStruct)) {
        int offsecs1, offsecs2;
        (__builtin_expect(!(offset1 != offset2), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 3700, "offset1 != offset2") : (void)0);
        offsecs1 = (((PyDateTime_Time*)self)->data[0]) * 3600 +
                   (((PyDateTime_Time*)self)->data[1]) * 60 +
                   (((PyDateTime_Time*)self)->data[2]) -
                   (((PyDateTime_Delta *)(offset1))->days) * 86400 -
                   (((PyDateTime_Delta *)(offset1))->seconds);
        offsecs2 = (((PyDateTime_Time*)other)->data[0]) * 3600 +
                   (((PyDateTime_Time*)other)->data[1]) * 60 +
                   (((PyDateTime_Time*)other)->data[2]) -
                   (((PyDateTime_Delta *)(offset2))->days) * 86400 -
                   (((PyDateTime_Delta *)(offset2))->seconds);
        diff = offsecs1 - offsecs2;
        if (diff == 0)
            diff = ((((PyDateTime_Time*)self)->data[3] << 16) | (((PyDateTime_Time*)self)->data[4] << 8) | ((PyDateTime_Time*)self)->data[5]) -
                   ((((PyDateTime_Time*)other)->data[3] << 16) | (((PyDateTime_Time*)other)->data[4] << 8) | ((PyDateTime_Time*)other)->data[5]);
        result = diff_to_bool(diff, op);
    }
    else if (op == 2) {
        result = ((PyObject *) &_Py_FalseStruct);
        ( ((PyObject*)(result))->ob_refcnt++);
    }
    else if (op == 3) {
        result = ((PyObject *) &_Py_TrueStruct);
        ( ((PyObject*)(result))->ob_refcnt++);
    }
    else {
        PyErr_SetString(PyExc_TypeError,
                        "can't compare offset-naive and "
                        "offset-aware times");
    }
 done:
    do { if ( --((PyObject*)(offset1))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset1)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset1)))); } while (0);
    do { if ((offset2) == ((void *)0)) ; else do { if ( --((PyObject*)(offset2))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset2)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset2)))); } while (0); } while (0);
    return result;
}

static Py_hash_t
time_hash(PyDateTime_Time *self)
{
    if (self->hashcode == -1) {
        PyObject *offset;

        offset = time_utcoffset((PyObject *)self, ((void *)0));

        if (offset == ((void *)0))
            return -1;


        if (offset == (&_Py_NoneStruct))
            self->hashcode = generic_hash(
                (unsigned char *)self->data, 6);
        else {
            PyObject *temp1, *temp2;
            int seconds, microseconds;
            (__builtin_expect(!((((_PyDateTime_BaseTZInfo *)(self))->hastzinfo)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 3754, "HASTZINFO(self)") : (void)0);
            seconds = (((PyDateTime_Time*)self)->data[0]) * 3600 +
                      (((PyDateTime_Time*)self)->data[1]) * 60 +
                      (((PyDateTime_Time*)self)->data[2]);
            microseconds = ((((PyDateTime_Time*)self)->data[3] << 16) | (((PyDateTime_Time*)self)->data[4] << 8) | ((PyDateTime_Time*)self)->data[5]);
            temp1 = new_delta_ex(0, seconds, microseconds, 1, &PyDateTime_DeltaType);
            if (temp1 == ((void *)0)) {
                do { if ( --((PyObject*)(offset))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset)))); } while (0);
                return -1;
            }
            temp2 = delta_subtract(temp1, offset);
            do { if ( --((PyObject*)(temp1))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp1)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp1)))); } while (0);
            if (temp2 == ((void *)0)) {
                do { if ( --((PyObject*)(offset))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset)))); } while (0);
                return -1;
            }
            self->hashcode = PyObject_Hash(temp2);
            do { if ( --((PyObject*)(temp2))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp2)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp2)))); } while (0);
        }
        do { if ( --((PyObject*)(offset))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset)))); } while (0);
    }
    return self->hashcode;
}

static PyObject *
time_replace(PyDateTime_Time *self, PyObject *args, PyObject *kw)
{
    PyObject *clone;
    PyObject *tuple;
    int hh = (((PyDateTime_Time*)self)->data[0]);
    int mm = (((PyDateTime_Time*)self)->data[1]);
    int ss = (((PyDateTime_Time*)self)->data[2]);
    int us = ((((PyDateTime_Time*)self)->data[3] << 16) | (((PyDateTime_Time*)self)->data[4] << 8) | ((PyDateTime_Time*)self)->data[5]);
    PyObject *tzinfo = (((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) ? self->tzinfo : (&_Py_NoneStruct);

    if (! PyArg_ParseTupleAndKeywords(args, kw, "|iiiiO:replace",
                                      time_kws,
                                      &hh, &mm, &ss, &us, &tzinfo))
        return ((void *)0);
    tuple = Py_BuildValue("iiiiO", hh, mm, ss, us, tzinfo);
    if (tuple == ((void *)0))
        return ((void *)0);
    clone = time_new((((PyObject*)(self))->ob_type), tuple, ((void *)0));
    do { if ( --((PyObject*)(tuple))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tuple)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tuple)))); } while (0);
    return clone;
}

static int
time_bool(PyObject *self)
{
    PyObject *offset, *tzinfo;
    int offsecs = 0;

    if ((((PyDateTime_Time*)self)->data[2]) || ((((PyDateTime_Time*)self)->data[3] << 16) | (((PyDateTime_Time*)self)->data[4] << 8) | ((PyDateTime_Time*)self)->data[5])) {



        return 1;
    }
    tzinfo = ((((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) ? ((PyDateTime_Time *)(self))->tzinfo : (&_Py_NoneStruct));
    if (tzinfo != (&_Py_NoneStruct)) {
        offset = call_utcoffset(tzinfo, (&_Py_NoneStruct));
        if (offset == ((void *)0))
            return -1;
        offsecs = (((PyDateTime_Delta *)(offset))->days)*86400 + (((PyDateTime_Delta *)(offset))->seconds);
        do { if ( --((PyObject*)(offset))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset)))); } while (0);
    }
    return ((((PyDateTime_Time*)self)->data[1])*60 - offsecs + (((PyDateTime_Time*)self)->data[0])*3600) != 0;
}
# 3831 "_datetimemodule.c"
static PyObject *
time_getstate(PyDateTime_Time *self)
{
    PyObject *basestate;
    PyObject *result = ((void *)0);

    basestate = PyBytes_FromStringAndSize((char *)self->data,
                                            6);
    if (basestate != ((void *)0)) {
        if (! (((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) || self->tzinfo == (&_Py_NoneStruct))
            result = PyTuple_Pack(1, basestate);
        else
            result = PyTuple_Pack(2, basestate, self->tzinfo);
        do { if ( --((PyObject*)(basestate))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(basestate)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(basestate)))); } while (0);
    }
    return result;
}

static PyObject *
time_reduce(PyDateTime_Time *self, PyObject *arg)
{
    return Py_BuildValue("(ON)", (((PyObject*)(self))->ob_type), time_getstate(self));
}

static PyMethodDef time_methods[] = {

    {"isoformat", (PyCFunction)time_isoformat, 0x0004,
     "Return string in ISO 8601 format, HH:MM:SS[.mmmmmm]" "[+HH:MM]."},


    {"strftime", (PyCFunction)time_strftime, 0x0001 | 0x0002,
     "format -> strftime() style string."},

    {"__format__", (PyCFunction)date_format, 0x0001,
     "Formats self with strftime."},

    {"utcoffset", (PyCFunction)time_utcoffset, 0x0004,
     "Return self.tzinfo.utcoffset(self)."},

    {"tzname", (PyCFunction)time_tzname, 0x0004,
     "Return self.tzinfo.tzname(self)."},

    {"dst", (PyCFunction)time_dst, 0x0004,
     "Return self.tzinfo.dst(self)."},

    {"replace", (PyCFunction)time_replace, 0x0001 | 0x0002,
     "Return time with new specified fields."},

    {"__reduce__", (PyCFunction)time_reduce, 0x0004,
     "__reduce__() -> (cls, state)"},

    {((void *)0), ((void *)0)}
};

static char time_doc[] =
"time([hour[, minute[, second[, microsecond[, tzinfo]]]]]) --> a time object\n\nAll arguments are optional. tzinfo may be None, or an instance of\na tzinfo subclass. The remaining arguments may be ints or longs.\n";




static PyNumberMethods time_as_number = {
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    (inquiry)time_bool,
};

static PyTypeObject PyDateTime_TimeType = {
    { { 1, ((void *)0) }, 0 },
    "datetime.time",
    sizeof(PyDateTime_Time),
    0,
    (destructor)time_dealloc,
    0,
    0,
    0,
    0,
    (reprfunc)time_repr,
    &time_as_number,
    0,
    0,
    (hashfunc)time_hash,
    0,
    (reprfunc)time_str,
    PyObject_GenericGetAttr,
    0,
    0,
    ( 0 | (1L<<18) | 0) | (1L<<10),
    time_doc,
    0,
    0,
    time_richcompare,
    0,
    0,
    0,
    time_methods,
    0,
    time_getset,
    0,
    0,
    0,
    0,
    0,
    0,
    time_alloc,
    time_new,
    0,
};
# 3954 "_datetimemodule.c"
static PyObject *
datetime_hour(PyDateTime_DateTime *self, void *unused)
{
    return PyLong_FromLong((((PyDateTime_DateTime*)self)->data[4]));
}

static PyObject *
datetime_minute(PyDateTime_DateTime *self, void *unused)
{
    return PyLong_FromLong((((PyDateTime_DateTime*)self)->data[5]));
}

static PyObject *
datetime_second(PyDateTime_DateTime *self, void *unused)
{
    return PyLong_FromLong((((PyDateTime_DateTime*)self)->data[6]));
}

static PyObject *
datetime_microsecond(PyDateTime_DateTime *self, void *unused)
{
    return PyLong_FromLong(((((PyDateTime_DateTime*)self)->data[7] << 16) | (((PyDateTime_DateTime*)self)->data[8] << 8) | ((PyDateTime_DateTime*)self)->data[9]));
}

static PyObject *
datetime_tzinfo(PyDateTime_DateTime *self, void *unused)
{
    PyObject *result = (((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) ? self->tzinfo : (&_Py_NoneStruct);
    ( ((PyObject*)(result))->ob_refcnt++);
    return result;
}

static PyGetSetDef datetime_getset[] = {
    {"hour", (getter)datetime_hour},
    {"minute", (getter)datetime_minute},
    {"second", (getter)datetime_second},
    {"microsecond", (getter)datetime_microsecond},
    {"tzinfo", (getter)datetime_tzinfo},
    {((void *)0)}
};





static char *datetime_kws[] = {
    "year", "month", "day", "hour", "minute", "second",
    "microsecond", "tzinfo", ((void *)0)
};

static PyObject *
datetime_new(PyTypeObject *type, PyObject *args, PyObject *kw)
{
    PyObject *self = ((void *)0);
    PyObject *state;
    int year;
    int month;
    int day;
    int hour = 0;
    int minute = 0;
    int second = 0;
    int usecond = 0;
    PyObject *tzinfo = (&_Py_NoneStruct);


    if ((((PyVarObject*)(args))->ob_size) >= 1 &&
        (((PyVarObject*)(args))->ob_size) <= 2 &&
        ((((((PyObject*)(state = (((PyTupleObject *)(args))->ob_item[0])))->ob_type))->tp_flags & ((1L<<27))) != 0) &&
        ((__builtin_expect(!(((((((PyObject*)(state))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 4022, "PyBytes_Check(state)") : (void)0),(((PyVarObject*)(state))->ob_size)) == 10 &&
        ((unsigned int)(((__builtin_expect(!(((((((PyObject*)(state))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 4023, "PyBytes_Check(state)") : (void)0), (((PyBytesObject *)(state))->ob_sval))[2]) - 1 < 12))
    {
        PyDateTime_DateTime *me;
        char aware;

        if ((((PyVarObject*)(args))->ob_size) == 2) {
            tzinfo = (((PyTupleObject *)(args))->ob_item[1]);
            if (check_tzinfo_subclass(tzinfo) < 0) {
                PyErr_SetString(PyExc_TypeError, "bad "
                    "tzinfo state arg");
                return ((void *)0);
            }
        }
        aware = (char)(tzinfo != (&_Py_NoneStruct));
        me = (PyDateTime_DateTime *) (type->tp_alloc(type , aware));
        if (me != ((void *)0)) {
            char *pdata = ((__builtin_expect(!(((((((PyObject*)(state))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 4039, "PyBytes_Check(state)") : (void)0), (((PyBytesObject *)(state))->ob_sval));

            ((__builtin_object_size (me->data, 0) != (size_t) -1) ? __builtin___memcpy_chk (me->data, pdata, 10, __builtin_object_size (me->data, 0)) : __inline_memcpy_chk (me->data, pdata, 10));
            me->hashcode = -1;
            me->hastzinfo = aware;
            if (aware) {
                ( ((PyObject*)(tzinfo))->ob_refcnt++);
                me->tzinfo = tzinfo;
            }
        }
        return (PyObject *)me;
    }

    if (PyArg_ParseTupleAndKeywords(args, kw, "iii|iiiiO", datetime_kws,
                                    &year, &month, &day, &hour, &minute,
                                    &second, &usecond, &tzinfo)) {
        if (check_date_args(year, month, day) < 0)
            return ((void *)0);
        if (check_time_args(hour, minute, second, usecond) < 0)
            return ((void *)0);
        if (check_tzinfo_subclass(tzinfo) < 0)
            return ((void *)0);
        self = new_datetime_ex(year, month, day,
                                hour, minute, second, usecond,
                                tzinfo, type);
    }
    return self;
}


typedef struct tm *(*TM_FUNC)(const time_t *timer);





static PyObject *
datetime_from_timet_and_us(PyObject *cls, TM_FUNC f, time_t timet, int us,
                           PyObject *tzinfo)
{
    struct tm *tm;

    tm = f(&timet);
    if (tm == ((void *)0)) {

        if ((*__error()) == 0)
            (*__error()) = 22;

        return PyErr_SetFromErrno(PyExc_OSError);
    }







    if (tm->tm_sec > 59)
        tm->tm_sec = 59;
    return PyObject_CallFunction(cls, "iiiiiiiO",
                                 tm->tm_year + 1900,
                                 tm->tm_mon + 1,
                                 tm->tm_mday,
                                 tm->tm_hour,
                                 tm->tm_min,
                                 tm->tm_sec,
                                 us,
                                 tzinfo);
}
# 4116 "_datetimemodule.c"
static PyObject *
datetime_from_timestamp(PyObject *cls, TM_FUNC f, PyObject *timestamp,
                        PyObject *tzinfo)
{
    time_t timet;
    long us;

    if (_PyTime_ObjectToTimeval(timestamp, &timet, &us) == -1)
        return ((void *)0);
    return datetime_from_timet_and_us(cls, f, timet, (int)us, tzinfo);
}





static PyObject *
datetime_best_possible(PyObject *cls, TM_FUNC f, PyObject *tzinfo)
{
    _PyTime_timeval t;
    _PyTime_gettimeofday(&t);
    return datetime_from_timet_and_us(cls, f, t.tv_sec, (int)t.tv_usec,
                                      tzinfo);
}




static PyObject *
datetime_now(PyObject *cls, PyObject *args, PyObject *kw)
{
    PyObject *self;
    PyObject *tzinfo = (&_Py_NoneStruct);
    static char *keywords[] = {"tz", ((void *)0)};

    if (! PyArg_ParseTupleAndKeywords(args, kw, "|O:now", keywords,
                                      &tzinfo))
        return ((void *)0);
    if (check_tzinfo_subclass(tzinfo) < 0)
        return ((void *)0);

    self = datetime_best_possible(cls,
                                  tzinfo == (&_Py_NoneStruct) ? localtime : gmtime,
                                  tzinfo);
    if (self != ((void *)0) && tzinfo != (&_Py_NoneStruct)) {

        PyObject *temp = self;
        static _Py_Identifier PyId_fromutc = { 0, "fromutc", 0 };

        self = _PyObject_CallMethodId(tzinfo, &PyId_fromutc, "O", self);
        do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0);
    }
    return self;
}




static PyObject *
datetime_utcnow(PyObject *cls, PyObject *dummy)
{
    return datetime_best_possible(cls, gmtime, (&_Py_NoneStruct));
}


static PyObject *
datetime_fromtimestamp(PyObject *cls, PyObject *args, PyObject *kw)
{
    PyObject *self;
    PyObject *timestamp;
    PyObject *tzinfo = (&_Py_NoneStruct);
    static char *keywords[] = {"timestamp", "tz", ((void *)0)};

    if (! PyArg_ParseTupleAndKeywords(args, kw, "O|O:fromtimestamp",
                                      keywords, &timestamp, &tzinfo))
        return ((void *)0);
    if (check_tzinfo_subclass(tzinfo) < 0)
        return ((void *)0);

    self = datetime_from_timestamp(cls,
                                   tzinfo == (&_Py_NoneStruct) ? localtime : gmtime,
                                   timestamp,
                                   tzinfo);
    if (self != ((void *)0) && tzinfo != (&_Py_NoneStruct)) {

        PyObject *temp = self;
        static _Py_Identifier PyId_fromutc = { 0, "fromutc", 0 };

        self = _PyObject_CallMethodId(tzinfo, &PyId_fromutc, "O", self);
        do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0);
    }
    return self;
}


static PyObject *
datetime_utcfromtimestamp(PyObject *cls, PyObject *args)
{
    PyObject *timestamp;
    PyObject *result = ((void *)0);

    if (PyArg_ParseTuple(args, "O:utcfromtimestamp", &timestamp))
        result = datetime_from_timestamp(cls, gmtime, timestamp,
                                         (&_Py_NoneStruct));
    return result;
}


static PyObject *
datetime_strptime(PyObject *cls, PyObject *args)
{
    static PyObject *module = ((void *)0);
    PyObject *string, *format;
    static _Py_Identifier PyId__strptime_datetime = { 0, "_strptime_datetime", 0 };

    if (!PyArg_ParseTuple(args, "UU:strptime", &string, &format))
        return ((void *)0);

    if (module == ((void *)0)) {
        module = PyImport_ImportModuleNoBlock("_strptime");
        if (module == ((void *)0))
            return ((void *)0);
    }
    return _PyObject_CallMethodId(module, &PyId__strptime_datetime, "OOO",
                                 cls, string, format);
}


static PyObject *
datetime_combine(PyObject *cls, PyObject *args, PyObject *kw)
{
    static char *keywords[] = {"date", "time", ((void *)0)};
    PyObject *date;
    PyObject *time;
    PyObject *result = ((void *)0);

    if (PyArg_ParseTupleAndKeywords(args, kw, "O!O!:combine", keywords,
                                    &PyDateTime_DateType, &date,
                                    &PyDateTime_TimeType, &time)) {
        PyObject *tzinfo = (&_Py_NoneStruct);

        if ((((_PyDateTime_BaseTZInfo *)(time))->hastzinfo))
            tzinfo = ((PyDateTime_Time *)time)->tzinfo;
        result = PyObject_CallFunction(cls, "iiiiiiiO",
                                        ((((PyDateTime_Date*)date)->data[0] << 8) | ((PyDateTime_Date*)date)->data[1]),
                                        (((PyDateTime_Date*)date)->data[2]),
                                        (((PyDateTime_Date*)date)->data[3]),
                                        (((PyDateTime_Time*)time)->data[0]),
                                        (((PyDateTime_Time*)time)->data[1]),
                                        (((PyDateTime_Time*)time)->data[2]),
                                        ((((PyDateTime_Time*)time)->data[3] << 16) | (((PyDateTime_Time*)time)->data[4] << 8) | ((PyDateTime_Time*)time)->data[5]),
                                        tzinfo);
    }
    return result;
}





static void
datetime_dealloc(PyDateTime_DateTime *self)
{
    if ((((_PyDateTime_BaseTZInfo *)(self))->hastzinfo)) {
        do { if ((self->tzinfo) == ((void *)0)) ; else do { if ( --((PyObject*)(self->tzinfo))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->tzinfo)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->tzinfo)))); } while (0); } while (0);
    }
    (((PyObject*)(self))->ob_type)->tp_free((PyObject *)self);
}






static PyObject *
datetime_utcoffset(PyObject *self, PyObject *unused) {
    return call_utcoffset(((((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) ? ((PyDateTime_DateTime *)(self))->tzinfo : (&_Py_NoneStruct)), self);
}

static PyObject *
datetime_dst(PyObject *self, PyObject *unused) {
    return call_dst(((((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) ? ((PyDateTime_DateTime *)(self))->tzinfo : (&_Py_NoneStruct)), self);
}

static PyObject *
datetime_tzname(PyObject *self, PyObject *unused) {
    return call_tzname(((((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) ? ((PyDateTime_DateTime *)(self))->tzinfo : (&_Py_NoneStruct)), self);
}
# 4312 "_datetimemodule.c"
static PyObject *
add_datetime_timedelta(PyDateTime_DateTime *date, PyDateTime_Delta *delta,
                       int factor)
{



    int year = ((((PyDateTime_Date*)date)->data[0] << 8) | ((PyDateTime_Date*)date)->data[1]);
    int month = (((PyDateTime_Date*)date)->data[2]);
    int day = (((PyDateTime_Date*)date)->data[3]) + (((PyDateTime_Delta *)(delta))->days) * factor;
    int hour = (((PyDateTime_DateTime*)date)->data[4]);
    int minute = (((PyDateTime_DateTime*)date)->data[5]);
    int second = (((PyDateTime_DateTime*)date)->data[6]) + (((PyDateTime_Delta *)(delta))->seconds) * factor;
    int microsecond = ((((PyDateTime_DateTime*)date)->data[7] << 16) | (((PyDateTime_DateTime*)date)->data[8] << 8) | ((PyDateTime_DateTime*)date)->data[9]) +
                      (((PyDateTime_Delta *)(delta))->microseconds) * factor;

    (__builtin_expect(!(factor == 1 || factor == -1), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 4328, "factor == 1 || factor == -1") : (void)0);
    if (normalize_datetime(&year, &month, &day,
                           &hour, &minute, &second, &microsecond) < 0)
        return ((void *)0);
    else
        return new_datetime_ex(year, month, day, hour, minute, second, microsecond, (((_PyDateTime_BaseTZInfo *)(date))->hastzinfo) ? date->tzinfo : (&_Py_NoneStruct), &PyDateTime_DateTimeType);


}

static PyObject *
datetime_add(PyObject *left, PyObject *right)
{
    if (((((PyObject*)(left))->ob_type) == (&PyDateTime_DateTimeType) || PyType_IsSubtype((((PyObject*)(left))->ob_type), (&PyDateTime_DateTimeType)))) {

        if (((((PyObject*)(right))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(right))->ob_type), (&PyDateTime_DeltaType))))

            return add_datetime_timedelta(
                            (PyDateTime_DateTime *)left,
                            (PyDateTime_Delta *)right,
                            1);
    }
    else if (((((PyObject*)(left))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(left))->ob_type), (&PyDateTime_DeltaType)))) {

        return add_datetime_timedelta((PyDateTime_DateTime *) right,
                                      (PyDateTime_Delta *) left,
                                      1);
    }
    return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct);
}

static PyObject *
datetime_subtract(PyObject *left, PyObject *right)
{
    PyObject *result = (&_Py_NotImplementedStruct);

    if (((((PyObject*)(left))->ob_type) == (&PyDateTime_DateTimeType) || PyType_IsSubtype((((PyObject*)(left))->ob_type), (&PyDateTime_DateTimeType)))) {

        if (((((PyObject*)(right))->ob_type) == (&PyDateTime_DateTimeType) || PyType_IsSubtype((((PyObject*)(right))->ob_type), (&PyDateTime_DateTimeType)))) {

            PyObject *offset1, *offset2, *offdiff = ((void *)0);
            int delta_d, delta_s, delta_us;

            if (((((_PyDateTime_BaseTZInfo *)(left))->hastzinfo) ? ((PyDateTime_DateTime *)(left))->tzinfo : (&_Py_NoneStruct)) == ((((_PyDateTime_BaseTZInfo *)(right))->hastzinfo) ? ((PyDateTime_DateTime *)(right))->tzinfo : (&_Py_NoneStruct))) {
                offset2 = offset1 = (&_Py_NoneStruct);
                ( ((PyObject*)(offset1))->ob_refcnt++);
                ( ((PyObject*)(offset2))->ob_refcnt++);
            }
            else {
                offset1 = datetime_utcoffset(left, ((void *)0));
                if (offset1 == ((void *)0))
                    return ((void *)0);
                offset2 = datetime_utcoffset(right, ((void *)0));
                if (offset2 == ((void *)0)) {
                    do { if ( --((PyObject*)(offset1))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset1)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset1)))); } while (0);
                    return ((void *)0);
                }
                if ((offset1 != (&_Py_NoneStruct)) != (offset2 != (&_Py_NoneStruct))) {
                    PyErr_SetString(PyExc_TypeError,
                                    "can't subtract offset-naive and "
                                    "offset-aware datetimes");
                    do { if ( --((PyObject*)(offset1))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset1)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset1)))); } while (0);
                    do { if ( --((PyObject*)(offset2))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset2)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset2)))); } while (0);
                    return ((void *)0);
                }
            }
            if ((offset1 != offset2) &&
                delta_cmp(offset1, offset2) != 0) {
                offdiff = delta_subtract(offset1, offset2);
                if (offdiff == ((void *)0)) {
                    do { if ( --((PyObject*)(offset1))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset1)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset1)))); } while (0);
                    do { if ( --((PyObject*)(offset2))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset2)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset2)))); } while (0);
                    return ((void *)0);
                }
            }
            do { if ( --((PyObject*)(offset1))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset1)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset1)))); } while (0);
            do { if ( --((PyObject*)(offset2))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset2)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset2)))); } while (0);
            delta_d = ymd_to_ord(((((PyDateTime_Date*)left)->data[0] << 8) | ((PyDateTime_Date*)left)->data[1]),
                                 (((PyDateTime_Date*)left)->data[2]),
                                 (((PyDateTime_Date*)left)->data[3])) -
                      ymd_to_ord(((((PyDateTime_Date*)right)->data[0] << 8) | ((PyDateTime_Date*)right)->data[1]),
                                 (((PyDateTime_Date*)right)->data[2]),
                                 (((PyDateTime_Date*)right)->data[3]));




            delta_s = ((((PyDateTime_DateTime*)left)->data[4]) -
                       (((PyDateTime_DateTime*)right)->data[4])) * 3600 +
                      ((((PyDateTime_DateTime*)left)->data[5]) -
                       (((PyDateTime_DateTime*)right)->data[5])) * 60 +
                      ((((PyDateTime_DateTime*)left)->data[6]) -
                       (((PyDateTime_DateTime*)right)->data[6]));
            delta_us = ((((PyDateTime_DateTime*)left)->data[7] << 16) | (((PyDateTime_DateTime*)left)->data[8] << 8) | ((PyDateTime_DateTime*)left)->data[9]) -
                       ((((PyDateTime_DateTime*)right)->data[7] << 16) | (((PyDateTime_DateTime*)right)->data[8] << 8) | ((PyDateTime_DateTime*)right)->data[9]);
            result = new_delta_ex(delta_d, delta_s, delta_us, 1, &PyDateTime_DeltaType);
            if (offdiff != ((void *)0)) {
                PyObject *temp = result;
                result = delta_subtract(result, offdiff);
                do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0);
                do { if ( --((PyObject*)(offdiff))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offdiff)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offdiff)))); } while (0);
            }
        }
        else if (((((PyObject*)(right))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(right))->ob_type), (&PyDateTime_DeltaType)))) {

            result = add_datetime_timedelta(
                            (PyDateTime_DateTime *)left,
                            (PyDateTime_Delta *)right,
                            -1);
        }
    }

    if (result == (&_Py_NotImplementedStruct))
        ( ((PyObject*)(result))->ob_refcnt++);
    return result;
}



static PyObject *
datetime_repr(PyDateTime_DateTime *self)
{
    const char *type_name = (((PyObject*)(self))->ob_type)->tp_name;
    PyObject *baserepr;

    if (((((PyDateTime_DateTime*)self)->data[7] << 16) | (((PyDateTime_DateTime*)self)->data[8] << 8) | ((PyDateTime_DateTime*)self)->data[9])) {
        baserepr = PyUnicode_FromFormat(
                      "%s(%d, %d, %d, %d, %d, %d, %d)",
                      type_name,
                      ((((PyDateTime_Date*)self)->data[0] << 8) | ((PyDateTime_Date*)self)->data[1]), (((PyDateTime_Date*)self)->data[2]), (((PyDateTime_Date*)self)->data[3]),
                      (((PyDateTime_DateTime*)self)->data[4]), (((PyDateTime_DateTime*)self)->data[5]),
                      (((PyDateTime_DateTime*)self)->data[6]),
                      ((((PyDateTime_DateTime*)self)->data[7] << 16) | (((PyDateTime_DateTime*)self)->data[8] << 8) | ((PyDateTime_DateTime*)self)->data[9]));
    }
    else if ((((PyDateTime_DateTime*)self)->data[6])) {
        baserepr = PyUnicode_FromFormat(
                      "%s(%d, %d, %d, %d, %d, %d)",
                      type_name,
                      ((((PyDateTime_Date*)self)->data[0] << 8) | ((PyDateTime_Date*)self)->data[1]), (((PyDateTime_Date*)self)->data[2]), (((PyDateTime_Date*)self)->data[3]),
                      (((PyDateTime_DateTime*)self)->data[4]), (((PyDateTime_DateTime*)self)->data[5]),
                      (((PyDateTime_DateTime*)self)->data[6]));
    }
    else {
        baserepr = PyUnicode_FromFormat(
                      "%s(%d, %d, %d, %d, %d)",
                      type_name,
                      ((((PyDateTime_Date*)self)->data[0] << 8) | ((PyDateTime_Date*)self)->data[1]), (((PyDateTime_Date*)self)->data[2]), (((PyDateTime_Date*)self)->data[3]),
                      (((PyDateTime_DateTime*)self)->data[4]), (((PyDateTime_DateTime*)self)->data[5]));
    }
    if (baserepr == ((void *)0) || ! (((_PyDateTime_BaseTZInfo *)(self))->hastzinfo))
        return baserepr;
    return append_keyword_tzinfo(baserepr, self->tzinfo);
}

static PyObject *
datetime_str(PyDateTime_DateTime *self)
{
    static _Py_Identifier PyId_isoformat = { 0, "isoformat", 0 };

    return _PyObject_CallMethodId((PyObject *)self, &PyId_isoformat, "(s)", " ");
}

static PyObject *
datetime_isoformat(PyDateTime_DateTime *self, PyObject *args, PyObject *kw)
{
    int sep = 'T';
    static char *keywords[] = {"sep", ((void *)0)};
    char buffer[100];
    PyObject *result;
    int us = ((((PyDateTime_DateTime*)self)->data[7] << 16) | (((PyDateTime_DateTime*)self)->data[8] << 8) | ((PyDateTime_DateTime*)self)->data[9]);

    if (!PyArg_ParseTupleAndKeywords(args, kw, "|C:isoformat", keywords, &sep))
        return ((void *)0);
    if (us)
        result = PyUnicode_FromFormat("%04d-%02d-%02d%c%02d:%02d:%02d.%06d",
                                      ((((PyDateTime_Date*)self)->data[0] << 8) | ((PyDateTime_Date*)self)->data[1]), (((PyDateTime_Date*)self)->data[2]),
                                      (((PyDateTime_Date*)self)->data[3]), (int)sep,
                                      (((PyDateTime_DateTime*)self)->data[4]), (((PyDateTime_DateTime*)self)->data[5]),
                                      (((PyDateTime_DateTime*)self)->data[6]), us);
    else
        result = PyUnicode_FromFormat("%04d-%02d-%02d%c%02d:%02d:%02d",
                                      ((((PyDateTime_Date*)self)->data[0] << 8) | ((PyDateTime_Date*)self)->data[1]), (((PyDateTime_Date*)self)->data[2]),
                                      (((PyDateTime_Date*)self)->data[3]), (int)sep,
                                      (((PyDateTime_DateTime*)self)->data[4]), (((PyDateTime_DateTime*)self)->data[5]),
                                      (((PyDateTime_DateTime*)self)->data[6]));

    if (!result || !(((_PyDateTime_BaseTZInfo *)(self))->hastzinfo))
        return result;


    if (format_utcoffset(buffer, sizeof(buffer), ":", self->tzinfo,
                         (PyObject *)self) < 0) {
        do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0);
        return ((void *)0);
    }
    PyUnicode_AppendAndDel(&result, PyUnicode_FromString(buffer));
    return result;
}

static PyObject *
datetime_ctime(PyDateTime_DateTime *self)
{
    return format_ctime((PyDateTime_Date *)self,
                        (((PyDateTime_DateTime*)self)->data[4]),
                        (((PyDateTime_DateTime*)self)->data[5]),
                        (((PyDateTime_DateTime*)self)->data[6]));
}



static PyObject *
datetime_richcompare(PyObject *self, PyObject *other, int op)
{
    PyObject *result = ((void *)0);
    PyObject *offset1, *offset2;
    int diff;

    if (! ((((PyObject*)(other))->ob_type) == (&PyDateTime_DateTimeType) || PyType_IsSubtype((((PyObject*)(other))->ob_type), (&PyDateTime_DateTimeType)))) {
        if (((((PyObject*)(other))->ob_type) == (&PyDateTime_DateType) || PyType_IsSubtype((((PyObject*)(other))->ob_type), (&PyDateTime_DateType)))) {







            if (op == 2)
                return ( ((PyObject*)(((PyObject *) &_Py_FalseStruct)))->ob_refcnt++), ((PyObject *) &_Py_FalseStruct);
            if (op == 3)
                return ( ((PyObject*)(((PyObject *) &_Py_TrueStruct)))->ob_refcnt++), ((PyObject *) &_Py_TrueStruct);
            return cmperror(self, other);
        }
        return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct);
    }

    if (((((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) ? ((PyDateTime_DateTime *)(self))->tzinfo : (&_Py_NoneStruct)) == ((((_PyDateTime_BaseTZInfo *)(other))->hastzinfo) ? ((PyDateTime_DateTime *)(other))->tzinfo : (&_Py_NoneStruct))) {
        diff = memcmp(((PyDateTime_DateTime *)self)->data,
                      ((PyDateTime_DateTime *)other)->data,
                      10);
        return diff_to_bool(diff, op);
    }
    offset1 = datetime_utcoffset(self, ((void *)0));
    if (offset1 == ((void *)0))
        return ((void *)0);
    offset2 = datetime_utcoffset(other, ((void *)0));
    if (offset2 == ((void *)0))
        goto done;




    if ((offset1 == offset2) ||
        (((((PyObject*)(offset1))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(offset1))->ob_type), (&PyDateTime_DeltaType))) && ((((PyObject*)(offset2))->ob_type) == (&PyDateTime_DeltaType) || PyType_IsSubtype((((PyObject*)(offset2))->ob_type), (&PyDateTime_DeltaType))) &&
         delta_cmp(offset1, offset2) == 0)) {
        diff = memcmp(((PyDateTime_DateTime *)self)->data,
                      ((PyDateTime_DateTime *)other)->data,
                      10);
        result = diff_to_bool(diff, op);
    }
    else if (offset1 != (&_Py_NoneStruct) && offset2 != (&_Py_NoneStruct)) {
        PyDateTime_Delta *delta;

        (__builtin_expect(!(offset1 != offset2), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 4590, "offset1 != offset2") : (void)0);
        delta = (PyDateTime_Delta *)datetime_subtract((PyObject *)self,
                                                       other);
        if (delta == ((void *)0))
            goto done;
        diff = (((PyDateTime_Delta *)(delta))->days);
        if (diff == 0)
            diff = (((PyDateTime_Delta *)(delta))->seconds) |
                   (((PyDateTime_Delta *)(delta))->microseconds);
        do { if ( --((PyObject*)(delta))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(delta)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(delta)))); } while (0);
        result = diff_to_bool(diff, op);
    }
    else if (op == 2) {
        result = ((PyObject *) &_Py_FalseStruct);
        ( ((PyObject*)(result))->ob_refcnt++);
    }
    else if (op == 3) {
        result = ((PyObject *) &_Py_TrueStruct);
        ( ((PyObject*)(result))->ob_refcnt++);
    }
    else {
        PyErr_SetString(PyExc_TypeError,
                        "can't compare offset-naive and "
                        "offset-aware datetimes");
    }
 done:
    do { if ( --((PyObject*)(offset1))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset1)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset1)))); } while (0);
    do { if ((offset2) == ((void *)0)) ; else do { if ( --((PyObject*)(offset2))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset2)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset2)))); } while (0); } while (0);
    return result;
}

static Py_hash_t
datetime_hash(PyDateTime_DateTime *self)
{
    if (self->hashcode == -1) {
        PyObject *offset;

        offset = datetime_utcoffset((PyObject *)self, ((void *)0));

        if (offset == ((void *)0))
            return -1;


        if (offset == (&_Py_NoneStruct))
            self->hashcode = generic_hash(
                (unsigned char *)self->data, 10);
        else {
            PyObject *temp1, *temp2;
            int days, seconds;

            (__builtin_expect(!((((_PyDateTime_BaseTZInfo *)(self))->hastzinfo)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 4640, "HASTZINFO(self)") : (void)0);
            days = ymd_to_ord(((((PyDateTime_Date*)self)->data[0] << 8) | ((PyDateTime_Date*)self)->data[1]),
                              (((PyDateTime_Date*)self)->data[2]),
                              (((PyDateTime_Date*)self)->data[3]));
            seconds = (((PyDateTime_DateTime*)self)->data[4]) * 3600 +
                      (((PyDateTime_DateTime*)self)->data[5]) * 60 +
                      (((PyDateTime_DateTime*)self)->data[6]);
            temp1 = new_delta_ex(days, seconds, ((((PyDateTime_DateTime*)self)->data[7] << 16) | (((PyDateTime_DateTime*)self)->data[8] << 8) | ((PyDateTime_DateTime*)self)->data[9]), 1, &PyDateTime_DeltaType);


            if (temp1 == ((void *)0)) {
                do { if ( --((PyObject*)(offset))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset)))); } while (0);
                return -1;
            }
            temp2 = delta_subtract(temp1, offset);
            do { if ( --((PyObject*)(temp1))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp1)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp1)))); } while (0);
            if (temp2 == ((void *)0)) {
                do { if ( --((PyObject*)(offset))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset)))); } while (0);
                return -1;
            }
            self->hashcode = PyObject_Hash(temp2);
            do { if ( --((PyObject*)(temp2))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp2)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp2)))); } while (0);
        }
        do { if ( --((PyObject*)(offset))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset)))); } while (0);
    }
    return self->hashcode;
}

static PyObject *
datetime_replace(PyDateTime_DateTime *self, PyObject *args, PyObject *kw)
{
    PyObject *clone;
    PyObject *tuple;
    int y = ((((PyDateTime_Date*)self)->data[0] << 8) | ((PyDateTime_Date*)self)->data[1]);
    int m = (((PyDateTime_Date*)self)->data[2]);
    int d = (((PyDateTime_Date*)self)->data[3]);
    int hh = (((PyDateTime_DateTime*)self)->data[4]);
    int mm = (((PyDateTime_DateTime*)self)->data[5]);
    int ss = (((PyDateTime_DateTime*)self)->data[6]);
    int us = ((((PyDateTime_DateTime*)self)->data[7] << 16) | (((PyDateTime_DateTime*)self)->data[8] << 8) | ((PyDateTime_DateTime*)self)->data[9]);
    PyObject *tzinfo = (((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) ? self->tzinfo : (&_Py_NoneStruct);

    if (! PyArg_ParseTupleAndKeywords(args, kw, "|iiiiiiiO:replace",
                                      datetime_kws,
                                      &y, &m, &d, &hh, &mm, &ss, &us,
                                      &tzinfo))
        return ((void *)0);
    tuple = Py_BuildValue("iiiiiiiO", y, m, d, hh, mm, ss, us, tzinfo);
    if (tuple == ((void *)0))
        return ((void *)0);
    clone = datetime_new((((PyObject*)(self))->ob_type), tuple, ((void *)0));
    do { if ( --((PyObject*)(tuple))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tuple)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tuple)))); } while (0);
    return clone;
}

static PyObject *
local_timezone(PyDateTime_DateTime *utc_time)
{
    PyObject *result = ((void *)0);
    struct tm *timep;
    time_t timestamp;
    PyObject *delta;
    PyObject *one_second;
    PyObject *seconds;
    PyObject *nameo = ((void *)0);
    const char *zone = ((void *)0);

    delta = datetime_subtract((PyObject *)utc_time, PyDateTime_Epoch);
    if (delta == ((void *)0))
        return ((void *)0);
    one_second = new_delta_ex(0, 1, 0, 0, &PyDateTime_DeltaType);
    if (one_second == ((void *)0))
        goto error;
    seconds = divide_timedelta_timedelta((PyDateTime_Delta *)delta,
                                         (PyDateTime_Delta *)one_second);
    do { if ( --((PyObject*)(one_second))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(one_second)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(one_second)))); } while (0);
    if (seconds == ((void *)0))
        goto error;
    do { if ( --((PyObject*)(delta))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(delta)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(delta)))); } while (0);
    timestamp = PyLong_AsLong(seconds);
    do { if ( --((PyObject*)(seconds))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(seconds)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(seconds)))); } while (0);
    if (timestamp == -1 && PyErr_Occurred())
        return ((void *)0);
    timep = localtime(&timestamp);

    zone = timep->tm_zone;
    delta = new_delta_ex(0, timep->tm_gmtoff, 0, 1, &PyDateTime_DeltaType);
# 4746 "_datetimemodule.c"
    if (zone != ((void *)0)) {
        nameo = PyUnicode_DecodeLocale(zone, "surrogateescape");
        if (nameo == ((void *)0))
            goto error;
    }
    result = new_timezone(delta, nameo);
    do { if ( --((PyObject*)(nameo))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(nameo)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(nameo)))); } while (0);
  error:
    do { if ( --((PyObject*)(delta))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(delta)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(delta)))); } while (0);
    return result;
}

static PyDateTime_DateTime *
datetime_astimezone(PyDateTime_DateTime *self, PyObject *args, PyObject *kw)
{
    PyDateTime_DateTime *result;
    PyObject *offset;
    PyObject *temp;
    PyObject *tzinfo = (&_Py_NoneStruct);
    static _Py_Identifier PyId_fromutc = { 0, "fromutc", 0 };
    static char *keywords[] = {"tz", ((void *)0)};

    if (! PyArg_ParseTupleAndKeywords(args, kw, "|O:astimezone", keywords,
          &tzinfo))
        return ((void *)0);

    if (check_tzinfo_subclass(tzinfo) == -1)
        return ((void *)0);

    if (!(((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) || self->tzinfo == (&_Py_NoneStruct))
        goto NeedAware;


    if (self->tzinfo == tzinfo) {
        ( ((PyObject*)(self))->ob_refcnt++);
        return self;
    }


    offset = datetime_utcoffset((PyObject *)self, ((void *)0));
    if (offset == ((void *)0))
        return ((void *)0);
    if (offset == (&_Py_NoneStruct)) {
        do { if ( --((PyObject*)(offset))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset)))); } while (0);
      NeedAware:
        PyErr_SetString(PyExc_ValueError, "astimezone() cannot be applied to "
                        "a naive datetime");
        return ((void *)0);
    }


    result = (PyDateTime_DateTime *)add_datetime_timedelta(self,
                                       (PyDateTime_Delta *)offset, -1);
    do { if ( --((PyObject*)(offset))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset)))); } while (0);
    if (result == ((void *)0))
        return ((void *)0);


    temp = result->tzinfo;
    if (tzinfo == (&_Py_NoneStruct)) {
        tzinfo = local_timezone(result);
        if (tzinfo == ((void *)0)) {
            do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0);
            return ((void *)0);
        }
    }
    else
      ( ((PyObject*)(tzinfo))->ob_refcnt++);
    result->tzinfo = tzinfo;
    do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0);

    temp = (PyObject *)result;
    result = (PyDateTime_DateTime *)
        _PyObject_CallMethodId(tzinfo, &PyId_fromutc, "O", temp);
    do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0);

    return result;
}

static PyObject *
datetime_timetuple(PyDateTime_DateTime *self)
{
    int dstflag = -1;

    if ((((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) && self->tzinfo != (&_Py_NoneStruct)) {
        PyObject * dst;

        dst = call_dst(self->tzinfo, (PyObject *)self);
        if (dst == ((void *)0))
            return ((void *)0);

        if (dst != (&_Py_NoneStruct))
            dstflag = delta_bool((PyDateTime_Delta *)dst);
        do { if ( --((PyObject*)(dst))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dst)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dst)))); } while (0);
    }
    return build_struct_time(((((PyDateTime_Date*)self)->data[0] << 8) | ((PyDateTime_Date*)self)->data[1]),
                             (((PyDateTime_Date*)self)->data[2]),
                             (((PyDateTime_Date*)self)->data[3]),
                             (((PyDateTime_DateTime*)self)->data[4]),
                             (((PyDateTime_DateTime*)self)->data[5]),
                             (((PyDateTime_DateTime*)self)->data[6]),
                             dstflag);
}

static PyObject *
datetime_timestamp(PyDateTime_DateTime *self)
{
    PyObject *result;

    if ((((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) && self->tzinfo != (&_Py_NoneStruct)) {
        PyObject *delta;
        delta = datetime_subtract((PyObject *)self, PyDateTime_Epoch);
        if (delta == ((void *)0))
            return ((void *)0);
        result = delta_total_seconds(delta);
        do { if ( --((PyObject*)(delta))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(delta)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(delta)))); } while (0);
    }
    else {
        struct tm time;
        time_t timestamp;
        ((__builtin_object_size ((void *) &time, 0) != (size_t) -1) ? __builtin___memset_chk ((void *) &time, '\0', sizeof(struct tm), __builtin_object_size ((void *) &time, 0)) : __inline_memset_chk ((void *) &time, '\0', sizeof(struct tm)));
        time.tm_year = ((((PyDateTime_Date*)self)->data[0] << 8) | ((PyDateTime_Date*)self)->data[1]) - 1900;
        time.tm_mon = (((PyDateTime_Date*)self)->data[2]) - 1;
        time.tm_mday = (((PyDateTime_Date*)self)->data[3]);
        time.tm_hour = (((PyDateTime_DateTime*)self)->data[4]);
        time.tm_min = (((PyDateTime_DateTime*)self)->data[5]);
        time.tm_sec = (((PyDateTime_DateTime*)self)->data[6]);
        time.tm_wday = -1;
        time.tm_isdst = -1;
        timestamp = mktime(&time);


        if (timestamp == (time_t)(-1) && time.tm_wday == -1) {
            PyErr_SetString(PyExc_OverflowError,
                            "timestamp out of range");
            return ((void *)0);
        }
        result = PyFloat_FromDouble(timestamp + ((((PyDateTime_DateTime*)self)->data[7] << 16) | (((PyDateTime_DateTime*)self)->data[8] << 8) | ((PyDateTime_DateTime*)self)->data[9]) / 1e6);
    }
    return result;
}

static PyObject *
datetime_getdate(PyDateTime_DateTime *self)
{
    return new_date_ex(((((PyDateTime_Date*)self)->data[0] << 8) | ((PyDateTime_Date*)self)->data[1]), (((PyDateTime_Date*)self)->data[2]), (((PyDateTime_Date*)self)->data[3]), &PyDateTime_DateType);


}

static PyObject *
datetime_gettime(PyDateTime_DateTime *self)
{
    return new_time_ex((((PyDateTime_DateTime*)self)->data[4]), (((PyDateTime_DateTime*)self)->data[5]), (((PyDateTime_DateTime*)self)->data[6]), ((((PyDateTime_DateTime*)self)->data[7] << 16) | (((PyDateTime_DateTime*)self)->data[8] << 8) | ((PyDateTime_DateTime*)self)->data[9]), (&_Py_NoneStruct), &PyDateTime_TimeType);




}

static PyObject *
datetime_gettimetz(PyDateTime_DateTime *self)
{
    return new_time_ex((((PyDateTime_DateTime*)self)->data[4]), (((PyDateTime_DateTime*)self)->data[5]), (((PyDateTime_DateTime*)self)->data[6]), ((((PyDateTime_DateTime*)self)->data[7] << 16) | (((PyDateTime_DateTime*)self)->data[8] << 8) | ((PyDateTime_DateTime*)self)->data[9]), ((((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) ? ((PyDateTime_DateTime *)(self))->tzinfo : (&_Py_NoneStruct)), &PyDateTime_TimeType);




}

static PyObject *
datetime_utctimetuple(PyDateTime_DateTime *self)
{
    int y, m, d, hh, mm, ss;
    PyObject *tzinfo;
    PyDateTime_DateTime *utcself;

    tzinfo = ((((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) ? ((PyDateTime_DateTime *)(self))->tzinfo : (&_Py_NoneStruct));
    if (tzinfo == (&_Py_NoneStruct)) {
        utcself = self;
        ( ((PyObject*)(utcself))->ob_refcnt++);
    }
    else {
        PyObject *offset;
        offset = call_utcoffset(tzinfo, (PyObject *)self);
        if (offset == ((void *)0))
            return ((void *)0);
        if (offset == (&_Py_NoneStruct)) {
            do { if ( --((PyObject*)(offset))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset)))); } while (0);
            utcself = self;
            ( ((PyObject*)(utcself))->ob_refcnt++);
        }
        else {
            utcself = (PyDateTime_DateTime *)add_datetime_timedelta(self,
                                                (PyDateTime_Delta *)offset, -1);
            do { if ( --((PyObject*)(offset))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(offset)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(offset)))); } while (0);
            if (utcself == ((void *)0))
                return ((void *)0);
        }
    }
    y = ((((PyDateTime_Date*)utcself)->data[0] << 8) | ((PyDateTime_Date*)utcself)->data[1]);
    m = (((PyDateTime_Date*)utcself)->data[2]);
    d = (((PyDateTime_Date*)utcself)->data[3]);
    hh = (((PyDateTime_DateTime*)utcself)->data[4]);
    mm = (((PyDateTime_DateTime*)utcself)->data[5]);
    ss = (((PyDateTime_DateTime*)utcself)->data[6]);

    do { if ( --((PyObject*)(utcself))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(utcself)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(utcself)))); } while (0);
    return build_struct_time(y, m, d, hh, mm, ss, 0);
}
# 4964 "_datetimemodule.c"
static PyObject *
datetime_getstate(PyDateTime_DateTime *self)
{
    PyObject *basestate;
    PyObject *result = ((void *)0);

    basestate = PyBytes_FromStringAndSize((char *)self->data,
                                           10);
    if (basestate != ((void *)0)) {
        if (! (((_PyDateTime_BaseTZInfo *)(self))->hastzinfo) || self->tzinfo == (&_Py_NoneStruct))
            result = PyTuple_Pack(1, basestate);
        else
            result = PyTuple_Pack(2, basestate, self->tzinfo);
        do { if ( --((PyObject*)(basestate))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(basestate)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(basestate)))); } while (0);
    }
    return result;
}

static PyObject *
datetime_reduce(PyDateTime_DateTime *self, PyObject *arg)
{
    return Py_BuildValue("(ON)", (((PyObject*)(self))->ob_type), datetime_getstate(self));
}

static PyMethodDef datetime_methods[] = {



    {"now", (PyCFunction)datetime_now,
     0x0001 | 0x0002 | 0x0010,
     "[tz] -> new datetime with tz's local day and time."},

    {"utcnow", (PyCFunction)datetime_utcnow,
     0x0004 | 0x0010,
     "Return a new datetime representing UTC day and time."},

    {"fromtimestamp", (PyCFunction)datetime_fromtimestamp,
     0x0001 | 0x0002 | 0x0010,
     "timestamp[, tz] -> tz's local time from POSIX timestamp."},

    {"utcfromtimestamp", (PyCFunction)datetime_utcfromtimestamp,
     0x0001 | 0x0010,
     "timestamp -> UTC datetime from a POSIX timestamp " "(like time.time())."},


    {"strptime", (PyCFunction)datetime_strptime,
     0x0001 | 0x0010,
     "string, format -> new datetime parsed from a string " "(like time.strptime())."},


    {"combine", (PyCFunction)datetime_combine,
     0x0001 | 0x0002 | 0x0010,
     "date, time -> datetime with same date and time fields"},



    {"date", (PyCFunction)datetime_getdate, 0x0004,
     "Return date object with same year, month and day."},

    {"time", (PyCFunction)datetime_gettime, 0x0004,
     "Return time object with same time but with tzinfo=None."},

    {"timetz", (PyCFunction)datetime_gettimetz, 0x0004,
     "Return time object with same time and tzinfo."},

    {"ctime", (PyCFunction)datetime_ctime, 0x0004,
     "Return ctime() style string."},

    {"timetuple", (PyCFunction)datetime_timetuple, 0x0004,
     "Return time tuple, compatible with time.localtime()."},

    {"timestamp", (PyCFunction)datetime_timestamp, 0x0004,
     "Return POSIX timestamp as float."},

    {"utctimetuple", (PyCFunction)datetime_utctimetuple, 0x0004,
     "Return UTC time tuple, compatible with time.localtime()."},

    {"isoformat", (PyCFunction)datetime_isoformat, 0x0001 | 0x0002,
     "[sep] -> string in ISO 8601 format, " "YYYY-MM-DDTHH:MM:SS[.mmmmmm][+HH:MM].\n\n" "sep is used to separate the year from the time, and " "defaults to 'T'."},




    {"utcoffset", (PyCFunction)datetime_utcoffset, 0x0004,
     "Return self.tzinfo.utcoffset(self)."},

    {"tzname", (PyCFunction)datetime_tzname, 0x0004,
     "Return self.tzinfo.tzname(self)."},

    {"dst", (PyCFunction)datetime_dst, 0x0004,
     "Return self.tzinfo.dst(self)."},

    {"replace", (PyCFunction)datetime_replace, 0x0001 | 0x0002,
     "Return datetime with new specified fields."},

    {"astimezone", (PyCFunction)datetime_astimezone, 0x0001 | 0x0002,
     "tz -> convert to local time in new timezone tz\n"},

    {"__reduce__", (PyCFunction)datetime_reduce, 0x0004,
     "__reduce__() -> (cls, state)"},

    {((void *)0), ((void *)0)}
};

static char datetime_doc[] =
"datetime(year, month, day[, hour[, minute[, second[, microsecond[,tzinfo]]]]])\n\nThe year, month and day arguments are required. tzinfo may be None, or an\ninstance of a tzinfo subclass. The remaining arguments may be ints or longs.\n";




static PyNumberMethods datetime_as_number = {
    datetime_add,
    datetime_subtract,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
};

static PyTypeObject PyDateTime_DateTimeType = {
    { { 1, ((void *)0) }, 0 },
    "datetime.datetime",
    sizeof(PyDateTime_DateTime),
    0,
    (destructor)datetime_dealloc,
    0,
    0,
    0,
    0,
    (reprfunc)datetime_repr,
    &datetime_as_number,
    0,
    0,
    (hashfunc)datetime_hash,
    0,
    (reprfunc)datetime_str,
    PyObject_GenericGetAttr,
    0,
    0,
    ( 0 | (1L<<18) | 0) | (1L<<10),
    datetime_doc,
    0,
    0,
    datetime_richcompare,
    0,
    0,
    0,
    datetime_methods,
    0,
    datetime_getset,
    &PyDateTime_DateType,
    0,
    0,
    0,
    0,
    0,
    datetime_alloc,
    datetime_new,
    0,
};





static PyMethodDef module_methods[] = {
    {((void *)0), ((void *)0)}
};




static PyDateTime_CAPI CAPI = {
    &PyDateTime_DateType,
    &PyDateTime_DateTimeType,
    &PyDateTime_TimeType,
    &PyDateTime_DeltaType,
    &PyDateTime_TZInfoType,
    new_date_ex,
    new_datetime_ex,
    new_time_ex,
    new_delta_ex,
    datetime_fromtimestamp,
    date_fromtimestamp
};



static struct PyModuleDef datetimemodule = {
    { { 1, ((void *)0) }, ((void *)0), 0, ((void *)0), },
    "_datetime",
    "Fast implementation of the datetime type.",
    -1,
    module_methods,
    ((void *)0),
    ((void *)0),
    ((void *)0),
    ((void *)0)
};

PyObject*
PyInit__datetime(void)
{
    PyObject *m;
    PyObject *d;
    PyObject *x;
    PyObject *delta;

    m = PyModule_Create2(&datetimemodule, 1013);
    if (m == ((void *)0))
        return ((void *)0);

    if (PyType_Ready(&PyDateTime_DateType) < 0)
        return ((void *)0);
    if (PyType_Ready(&PyDateTime_DateTimeType) < 0)
        return ((void *)0);
    if (PyType_Ready(&PyDateTime_DeltaType) < 0)
        return ((void *)0);
    if (PyType_Ready(&PyDateTime_TimeType) < 0)
        return ((void *)0);
    if (PyType_Ready(&PyDateTime_TZInfoType) < 0)
        return ((void *)0);
    if (PyType_Ready(&PyDateTime_TimeZoneType) < 0)
        return ((void *)0);


    d = PyDateTime_DeltaType.tp_dict;

    x = new_delta_ex(0, 0, 1, 0, &PyDateTime_DeltaType);
    if (x == ((void *)0) || PyDict_SetItemString(d, "resolution", x) < 0)
        return ((void *)0);
    do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);

    x = new_delta_ex(-999999999, 0, 0, 0, &PyDateTime_DeltaType);
    if (x == ((void *)0) || PyDict_SetItemString(d, "min", x) < 0)
        return ((void *)0);
    do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);

    x = new_delta_ex(999999999, 24*3600-1, 1000000-1, 0, &PyDateTime_DeltaType);
    if (x == ((void *)0) || PyDict_SetItemString(d, "max", x) < 0)
        return ((void *)0);
    do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);


    d = PyDateTime_DateType.tp_dict;

    x = new_date_ex(1, 1, 1, &PyDateTime_DateType);
    if (x == ((void *)0) || PyDict_SetItemString(d, "min", x) < 0)
        return ((void *)0);
    do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);

    x = new_date_ex(9999, 12, 31, &PyDateTime_DateType);
    if (x == ((void *)0) || PyDict_SetItemString(d, "max", x) < 0)
        return ((void *)0);
    do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);

    x = new_delta_ex(1, 0, 0, 0, &PyDateTime_DeltaType);
    if (x == ((void *)0) || PyDict_SetItemString(d, "resolution", x) < 0)
        return ((void *)0);
    do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);


    d = PyDateTime_TimeType.tp_dict;

    x = new_time_ex(0, 0, 0, 0, (&_Py_NoneStruct), &PyDateTime_TimeType);
    if (x == ((void *)0) || PyDict_SetItemString(d, "min", x) < 0)
        return ((void *)0);
    do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);

    x = new_time_ex(23, 59, 59, 999999, (&_Py_NoneStruct), &PyDateTime_TimeType);
    if (x == ((void *)0) || PyDict_SetItemString(d, "max", x) < 0)
        return ((void *)0);
    do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);

    x = new_delta_ex(0, 0, 1, 0, &PyDateTime_DeltaType);
    if (x == ((void *)0) || PyDict_SetItemString(d, "resolution", x) < 0)
        return ((void *)0);
    do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);


    d = PyDateTime_DateTimeType.tp_dict;

    x = new_datetime_ex(1, 1, 1, 0, 0, 0, 0, (&_Py_NoneStruct), &PyDateTime_DateTimeType);
    if (x == ((void *)0) || PyDict_SetItemString(d, "min", x) < 0)
        return ((void *)0);
    do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);

    x = new_datetime_ex(9999, 12, 31, 23, 59, 59, 999999, (&_Py_NoneStruct), &PyDateTime_DateTimeType);
    if (x == ((void *)0) || PyDict_SetItemString(d, "max", x) < 0)
        return ((void *)0);
    do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);

    x = new_delta_ex(0, 0, 1, 0, &PyDateTime_DeltaType);
    if (x == ((void *)0) || PyDict_SetItemString(d, "resolution", x) < 0)
        return ((void *)0);
    do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);


    d = PyDateTime_TimeZoneType.tp_dict;

    delta = new_delta_ex(0, 0, 0, 0, &PyDateTime_DeltaType);
    if (delta == ((void *)0))
        return ((void *)0);
    x = create_timezone(delta, ((void *)0));
    do { if ( --((PyObject*)(delta))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(delta)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(delta)))); } while (0);
    if (x == ((void *)0) || PyDict_SetItemString(d, "utc", x) < 0)
        return ((void *)0);
    PyDateTime_TimeZone_UTC = x;

    delta = new_delta_ex(-1, 60, 0, 1, &PyDateTime_DeltaType);
    if (delta == ((void *)0))
        return ((void *)0);
    x = create_timezone(delta, ((void *)0));
    do { if ( --((PyObject*)(delta))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(delta)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(delta)))); } while (0);
    if (x == ((void *)0) || PyDict_SetItemString(d, "min", x) < 0)
        return ((void *)0);
    do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);

    delta = new_delta_ex(0, (23 * 60 + 59) * 60, 0, 0, &PyDateTime_DeltaType);
    if (delta == ((void *)0))
        return ((void *)0);
    x = create_timezone(delta, ((void *)0));
    do { if ( --((PyObject*)(delta))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(delta)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(delta)))); } while (0);
    if (x == ((void *)0) || PyDict_SetItemString(d, "max", x) < 0)
        return ((void *)0);
    do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);


    PyDateTime_Epoch = new_datetime_ex(1970, 1, 1, 0, 0, 0, 0, PyDateTime_TimeZone_UTC, &PyDateTime_DateTimeType);

    if (PyDateTime_Epoch == ((void *)0))
      return ((void *)0);


    PyModule_AddIntConstant(m, "MINYEAR", 1);
    PyModule_AddIntConstant(m, "MAXYEAR", 9999);

    ( ((PyObject*)(&PyDateTime_DateType))->ob_refcnt++);
    PyModule_AddObject(m, "date", (PyObject *) &PyDateTime_DateType);

    ( ((PyObject*)(&PyDateTime_DateTimeType))->ob_refcnt++);
    PyModule_AddObject(m, "datetime",
                       (PyObject *)&PyDateTime_DateTimeType);

    ( ((PyObject*)(&PyDateTime_TimeType))->ob_refcnt++);
    PyModule_AddObject(m, "time", (PyObject *) &PyDateTime_TimeType);

    ( ((PyObject*)(&PyDateTime_DeltaType))->ob_refcnt++);
    PyModule_AddObject(m, "timedelta", (PyObject *) &PyDateTime_DeltaType);

    ( ((PyObject*)(&PyDateTime_TZInfoType))->ob_refcnt++);
    PyModule_AddObject(m, "tzinfo", (PyObject *) &PyDateTime_TZInfoType);

    ( ((PyObject*)(&PyDateTime_TimeZoneType))->ob_refcnt++);
    PyModule_AddObject(m, "timezone", (PyObject *) &PyDateTime_TimeZoneType);

    x = PyCapsule_New(&CAPI, "datetime.datetime_CAPI", ((void *)0));
    if (x == ((void *)0))
        return ((void *)0);
    PyModule_AddObject(m, "datetime_CAPI", x);




    (__builtin_expect(!(1461 == 4 * 365 + 1), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 5332, "DI4Y == 4 * 365 + 1") : (void)0);
    (__builtin_expect(!(1461 == days_before_year(4+1)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 5333, "DI4Y == days_before_year(4+1)") : (void)0);




    (__builtin_expect(!(146097 == 4 * 36524 + 1), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 5338, "DI400Y == 4 * DI100Y + 1") : (void)0);
    (__builtin_expect(!(146097 == days_before_year(400+1)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 5339, "DI400Y == days_before_year(400+1)") : (void)0);




    (__builtin_expect(!(36524 == 25 * 1461 - 1), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 5344, "DI100Y == 25 * DI4Y - 1") : (void)0);
    (__builtin_expect(!(36524 == days_before_year(100+1)), 0) ? __assert_rtn(__func__, "_datetimemodule.c", 5345, "DI100Y == days_before_year(100+1)") : (void)0);

    us_per_us = PyLong_FromLong(1);
    us_per_ms = PyLong_FromLong(1000);
    us_per_second = PyLong_FromLong(1000000);
    us_per_minute = PyLong_FromLong(60000000);
    seconds_per_day = PyLong_FromLong(24 * 3600);
    if (us_per_us == ((void *)0) || us_per_ms == ((void *)0) || us_per_second == ((void *)0) ||
        us_per_minute == ((void *)0) || seconds_per_day == ((void *)0))
        return ((void *)0);




    us_per_hour = PyLong_FromDouble(3600000000.0);
    us_per_day = PyLong_FromDouble(86400000000.0);
    us_per_week = PyLong_FromDouble(604800000000.0);
    if (us_per_hour == ((void *)0) || us_per_day == ((void *)0) || us_per_week == ((void *)0))
        return ((void *)0);
    return m;
}
