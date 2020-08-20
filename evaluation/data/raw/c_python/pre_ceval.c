# 1 "ceval.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "ceval.c"
# 12 "ceval.c"
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
# 13 "ceval.c" 2

# 1 "/Users/parrt/tmp/Python-3.3.1/Include/code.h" 1
# 15 "ceval.c" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/frameobject.h" 1
# 11 "/Users/parrt/tmp/Python-3.3.1/Include/frameobject.h"
typedef struct {
    int b_type;
    int b_handler;
    int b_level;
} PyTryBlock;

typedef struct _frame {
    PyVarObject ob_base;
    struct _frame *f_back;
    PyCodeObject *f_code;
    PyObject *f_builtins;
    PyObject *f_globals;
    PyObject *f_locals;
    PyObject **f_valuestack;



    PyObject **f_stacktop;
    PyObject *f_trace;
# 38 "/Users/parrt/tmp/Python-3.3.1/Include/frameobject.h"
    PyObject *f_exc_type, *f_exc_value, *f_exc_traceback;

    PyThreadState *f_tstate;
    int f_lasti;





    int f_lineno;
    int f_iblock;
    PyTryBlock f_blockstack[20];
    PyObject *f_localsplus[1];
} PyFrameObject;




extern PyTypeObject PyFrame_Type;



PyFrameObject * PyFrame_New(PyThreadState *, PyCodeObject *,
                                       PyObject *, PyObject *);






void PyFrame_BlockSetup(PyFrameObject *, int, int, int);
PyTryBlock * PyFrame_BlockPop(PyFrameObject *);



PyObject ** PyFrame_ExtendStack(PyFrameObject *, int, int);



void PyFrame_LocalsToFast(PyFrameObject *, int);
void PyFrame_FastToLocals(PyFrameObject *);

int PyFrame_ClearFreeList(void);

void _PyFrame_DebugMallocStats(FILE *out);


int PyFrame_GetLineNumber(PyFrameObject *);
# 16 "ceval.c" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/opcode.h" 1
# 151 "/Users/parrt/tmp/Python-3.3.1/Include/opcode.h"
enum cmp_op {PyCmp_LT=0, PyCmp_LE=1, PyCmp_EQ=2, PyCmp_NE=3, PyCmp_GT=4, PyCmp_GE=5,
             PyCmp_IN, PyCmp_NOT_IN, PyCmp_IS, PyCmp_IS_NOT, PyCmp_EXC_MATCH, PyCmp_BAD};
# 17 "ceval.c" 2
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
# 18 "ceval.c" 2
# 104 "ceval.c"
typedef PyObject *(*callproc)(PyObject *, PyObject *, PyObject *);





static PyObject * call_function(PyObject ***, int);

static PyObject * fast_function(PyObject *, PyObject ***, int, int, int);
static PyObject * do_call(PyObject *, PyObject ***, int, int);
static PyObject * ext_do_call(PyObject *, PyObject ***, int, int, int);
static PyObject * update_keyword_args(PyObject *, int, PyObject ***,
                                      PyObject *);
static PyObject * update_star_args(int, int, PyObject *, PyObject ***);
static PyObject * load_args(PyObject ***, int);







static int call_trace(Py_tracefunc, PyObject *, PyFrameObject *,
                      int, PyObject *);
static int call_trace_protected(Py_tracefunc, PyObject *,
                                PyFrameObject *, int, PyObject *);
static void call_exc_trace(Py_tracefunc, PyObject *, PyFrameObject *);
static int maybe_call_line_trace(Py_tracefunc, PyObject *,
                                 PyFrameObject *, int *, int *, int *);

static PyObject * cmp_outcome(int, PyObject *, PyObject *);
static PyObject * import_from(PyObject *, PyObject *);
static int import_all_from(PyObject *, PyObject *);
static void format_exc_check_arg(PyObject *, const char *, PyObject *);
static void format_exc_unbound(PyCodeObject *co, int oparg);
static PyObject * unicode_concatenate(PyObject *, PyObject *,
                                      PyFrameObject *, unsigned char *);
static PyObject * special_lookup(PyObject *, _Py_Identifier *);
# 211 "ceval.c"
PyObject *
PyEval_GetCallStats(PyObject *self)
{
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}
# 278 "ceval.c"
# 1 "/usr/include/errno.h" 1 3 4
# 279 "ceval.c" 2

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
# 281 "ceval.c" 2

static PyThread_type_lock pending_lock = 0;
static long main_thread = 0;


static _Py_atomic_int eval_breaker = {0};

static _Py_atomic_int gil_drop_request = {0};

static _Py_atomic_int pendingcalls_to_do = {0};


static int pending_async_exc = 0;

# 1 "ceval_gil.h" 1





# 1 "/usr/include/errno.h" 1 3 4
# 7 "ceval_gil.h" 2






static unsigned long gil_interval = 5000;
# 62 "ceval_gil.h"
# 1 "condvar.h" 1
# 60 "condvar.h"
# 1 "/usr/include/pthread.h" 1 3 4
# 57 "/usr/include/pthread.h" 3 4
# 1 "/usr/include/pthread_impl.h" 1 3 4
# 58 "/usr/include/pthread.h" 2 3 4

# 1 "/usr/include/sched.h" 1 3 4
# 30 "/usr/include/sched.h" 3 4





struct sched_param { int sched_priority; char __opaque[4]; };


extern int sched_yield(void);
extern int sched_get_priority_min(int);
extern int sched_get_priority_max(int);

# 60 "/usr/include/pthread.h" 2 3 4
# 69 "/usr/include/pthread.h" 3 4
typedef __darwin_pthread_cond_t pthread_cond_t;




typedef __darwin_pthread_condattr_t pthread_condattr_t;




typedef __darwin_pthread_key_t pthread_key_t;




typedef __darwin_pthread_mutex_t pthread_mutex_t;




typedef __darwin_pthread_mutexattr_t pthread_mutexattr_t;




typedef __darwin_pthread_once_t pthread_once_t;




typedef __darwin_pthread_rwlock_t pthread_rwlock_t;




typedef __darwin_pthread_rwlockattr_t pthread_rwlockattr_t;




typedef __darwin_pthread_t pthread_t;






typedef __darwin_mach_port_t mach_port_t;
# 149 "/usr/include/pthread.h" 3 4

# 250 "/usr/include/pthread.h" 3 4
int pthread_atfork(void (*)(void), void (*)(void),
                      void (*)(void));
int pthread_attr_destroy(pthread_attr_t *);
int pthread_attr_getdetachstate(const pthread_attr_t *,
          int *);
int pthread_attr_getguardsize(const pthread_attr_t * ,
                                      size_t * );
int pthread_attr_getinheritsched(const pthread_attr_t * ,
           int * );
int pthread_attr_getschedparam(const pthread_attr_t * ,
                                     struct sched_param * );
int pthread_attr_getschedpolicy(const pthread_attr_t * ,
          int * );
int pthread_attr_getscope(const pthread_attr_t * , int * );
int pthread_attr_getstack(const pthread_attr_t * ,
                                      void ** , size_t * );
int pthread_attr_getstackaddr(const pthread_attr_t * ,
                                      void ** );
int pthread_attr_getstacksize(const pthread_attr_t * ,
                                      size_t * );
int pthread_attr_init(pthread_attr_t *);
int pthread_attr_setdetachstate(pthread_attr_t *,
          int );
int pthread_attr_setguardsize(pthread_attr_t *, size_t );
int pthread_attr_setinheritsched(pthread_attr_t *,
           int );
int pthread_attr_setschedparam(pthread_attr_t * ,
                                     const struct sched_param * );
int pthread_attr_setschedpolicy(pthread_attr_t *,
          int );
int pthread_attr_setscope(pthread_attr_t *, int);
int pthread_attr_setstack(pthread_attr_t *,
                                      void *, size_t );
int pthread_attr_setstackaddr(pthread_attr_t *,
                                      void *);
int pthread_attr_setstacksize(pthread_attr_t *, size_t );
int pthread_cancel(pthread_t ) __asm("_" "pthread_cancel" );

int pthread_cond_broadcast(pthread_cond_t *);
int pthread_cond_destroy(pthread_cond_t *);
int pthread_cond_init(pthread_cond_t * ,
                            const pthread_condattr_t * ) __asm("_" "pthread_cond_init" );
int pthread_cond_signal(pthread_cond_t *);
int pthread_cond_timedwait(pthread_cond_t * ,
     pthread_mutex_t * ,
     const struct timespec * ) __asm("_" "pthread_cond_timedwait" );
int pthread_cond_wait(pthread_cond_t * ,
       pthread_mutex_t * ) __asm("_" "pthread_cond_wait" );
int pthread_condattr_destroy(pthread_condattr_t *);
int pthread_condattr_init(pthread_condattr_t *);
int pthread_condattr_getpshared(const pthread_condattr_t * ,
   int * );
int pthread_condattr_setpshared(pthread_condattr_t *,
   int );
int pthread_create(pthread_t * ,
                         const pthread_attr_t * ,
                         void *(*)(void *),
                         void * );
int pthread_detach(pthread_t );
int pthread_equal(pthread_t ,
   pthread_t );
void pthread_exit(void *) __attribute__((__noreturn__));
int pthread_getconcurrency(void);
int pthread_getschedparam(pthread_t , int * , struct sched_param * );
void *pthread_getspecific(pthread_key_t );
int pthread_join(pthread_t , void **) __asm("_" "pthread_join" );
int pthread_key_create(pthread_key_t *, void (*)(void *));
int pthread_key_delete(pthread_key_t );
int pthread_mutex_destroy(pthread_mutex_t *);
int pthread_mutex_getprioceiling(const pthread_mutex_t * , int * );
int pthread_mutex_init(pthread_mutex_t * , const pthread_mutexattr_t * );
int pthread_mutex_lock(pthread_mutex_t *);
int pthread_mutex_setprioceiling(pthread_mutex_t * , int, int * );
int pthread_mutex_trylock(pthread_mutex_t *);
int pthread_mutex_unlock(pthread_mutex_t *);
int pthread_mutexattr_destroy(pthread_mutexattr_t *) __asm("_" "pthread_mutexattr_destroy" );
int pthread_mutexattr_getprioceiling(const pthread_mutexattr_t * , int * );
int pthread_mutexattr_getprotocol(const pthread_mutexattr_t * , int * );
int pthread_mutexattr_getpshared(const pthread_mutexattr_t * , int * );
int pthread_mutexattr_gettype(const pthread_mutexattr_t * , int * );
int pthread_mutexattr_init(pthread_mutexattr_t *);
int pthread_mutexattr_setprioceiling(pthread_mutexattr_t *, int);
int pthread_mutexattr_setprotocol(pthread_mutexattr_t *, int);
int pthread_mutexattr_setpshared(pthread_mutexattr_t *, int );
int pthread_mutexattr_settype(pthread_mutexattr_t *, int);
int pthread_once(pthread_once_t *, void (*)(void));
int pthread_rwlock_destroy(pthread_rwlock_t * ) __asm("_" "pthread_rwlock_destroy" );
int pthread_rwlock_init(pthread_rwlock_t * , const pthread_rwlockattr_t * ) __asm("_" "pthread_rwlock_init" );
int pthread_rwlock_rdlock(pthread_rwlock_t *) __asm("_" "pthread_rwlock_rdlock" );
int pthread_rwlock_tryrdlock(pthread_rwlock_t *) __asm("_" "pthread_rwlock_tryrdlock" );
int pthread_rwlock_trywrlock(pthread_rwlock_t *) __asm("_" "pthread_rwlock_trywrlock" );
int pthread_rwlock_wrlock(pthread_rwlock_t *) __asm("_" "pthread_rwlock_wrlock" );
int pthread_rwlock_unlock(pthread_rwlock_t *) __asm("_" "pthread_rwlock_unlock" );
int pthread_rwlockattr_destroy(pthread_rwlockattr_t *);
int pthread_rwlockattr_getpshared(const pthread_rwlockattr_t * ,
   int * );
int pthread_rwlockattr_init(pthread_rwlockattr_t *);
int pthread_rwlockattr_setpshared(pthread_rwlockattr_t *,
   int );
pthread_t pthread_self(void);

int pthread_setcancelstate(int , int *) __asm("_" "pthread_setcancelstate" );
int pthread_setcanceltype(int , int *) __asm("_" "pthread_setcanceltype" );
int pthread_setconcurrency(int);
int pthread_setschedparam(pthread_t ,
    int ,
                                const struct sched_param *);
int pthread_setspecific(pthread_key_t ,
         const void *);
void pthread_testcancel(void) __asm("_" "pthread_testcancel" );



int pthread_is_threaded_np(void);

int pthread_threadid_np(pthread_t,__uint64_t*) __attribute__((visibility("default")));

int pthread_rwlock_longrdlock_np(pthread_rwlock_t *) __attribute__((visibility("default")));
int pthread_rwlock_yieldwrlock_np(pthread_rwlock_t *) __attribute__((visibility("default")));
int pthread_rwlock_downgrade_np(pthread_rwlock_t *);
int pthread_rwlock_upgrade_np(pthread_rwlock_t *);
int pthread_rwlock_tryupgrade_np(pthread_rwlock_t *);
int pthread_rwlock_held_np(pthread_rwlock_t *);
int pthread_rwlock_rdheld_np(pthread_rwlock_t *);
int pthread_rwlock_wrheld_np(pthread_rwlock_t *);


int pthread_getname_np(pthread_t,char*,size_t) __attribute__((visibility("default")));
int pthread_setname_np(const char*) __attribute__((visibility("default")));

int pthread_main_np(void);


mach_port_t pthread_mach_thread_np(pthread_t);
size_t pthread_get_stacksize_np(pthread_t);
void * pthread_get_stackaddr_np(pthread_t);


int pthread_cond_signal_thread_np(pthread_cond_t *, pthread_t);


int pthread_cond_timedwait_relative_np(pthread_cond_t *,
     pthread_mutex_t *,
     const struct timespec *);


int pthread_create_suspended_np(pthread_t *,
                         const pthread_attr_t *,
                         void *(*)(void *),
                         void *);
int pthread_kill(pthread_t, int);

pthread_t pthread_from_mach_thread_np(mach_port_t) __attribute__((visibility("default")));

int pthread_sigmask(int, const sigset_t *, sigset_t *) __asm("_" "pthread_sigmask" );
void pthread_yield_np(void);


# 61 "condvar.h" 2
# 91 "condvar.h"
static inline int
PyCOND_TIMEDWAIT(pthread_cond_t *cond, pthread_mutex_t *mut, long us)
{
    int r;
    struct timespec ts;
    struct timeval deadline;

    gettimeofday(&deadline, (struct timezone *)((void *)0));
    do { deadline.tv_usec += (long) us; deadline.tv_sec += deadline.tv_usec / 1000000; deadline.tv_usec %= 1000000; } while (0);
    ts.tv_sec = deadline.tv_sec;
    ts.tv_nsec = deadline.tv_usec * 1000;

    r = pthread_cond_timedwait((cond), (mut), &ts);
    if (r == 60)
        return 1;
    else if (r)
        return -1;
    else
        return 0;
}
# 63 "ceval_gil.h" 2
# 109 "ceval_gil.h"
static _Py_atomic_int gil_locked = {-1};

static unsigned long gil_switch_number = 0;


static _Py_atomic_address gil_last_holder = {((void *)0)};




static pthread_cond_t gil_cond;
static pthread_mutex_t gil_mutex;




static pthread_cond_t switch_cond;
static pthread_mutex_t switch_mutex;



static int gil_created(void)
{
    return __extension__ ({ __typeof__(&gil_locked) atomic_val = &gil_locked; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_acquire; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }) >= 0;
}

static void create_gil(void)
{
    if (pthread_mutex_init((&(gil_mutex)), ((void *)0))) { Py_FatalError("PyMUTEX_INIT(" "gil_mutex" ") failed"); };;

    if (pthread_mutex_init((&(switch_mutex)), ((void *)0))) { Py_FatalError("PyMUTEX_INIT(" "switch_mutex" ") failed"); };;

    if (pthread_cond_init((&(gil_cond)), ((void *)0))) { Py_FatalError("PyCOND_INIT(" "gil_cond" ") failed"); };;

    if (pthread_cond_init((&(switch_cond)), ((void *)0))) { Py_FatalError("PyCOND_INIT(" "switch_cond" ") failed"); };;

    __extension__ ({ __typeof__(&gil_last_holder) atomic_val = &gil_last_holder; __typeof__(atomic_val->_value) new_val = ((void *)0); volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; });
    ;
    __extension__ ({ __typeof__(&gil_locked) atomic_val = &gil_locked; __typeof__(atomic_val->_value) new_val = 0; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_release; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; });
}

static void destroy_gil(void)
{



    if (pthread_cond_destroy(&(gil_cond))) { Py_FatalError("PyCOND_FINI(" "gil_cond" ") failed"); };;
    if (pthread_mutex_destroy(&(gil_mutex))) { Py_FatalError("PyMUTEX_FINI(" "gil_mutex" ") failed"); };;

    if (pthread_cond_destroy(&(switch_cond))) { Py_FatalError("PyCOND_FINI(" "switch_cond" ") failed"); };;
    if (pthread_mutex_destroy(&(switch_mutex))) { Py_FatalError("PyMUTEX_FINI(" "switch_mutex" ") failed"); };;

    __extension__ ({ __typeof__(&gil_locked) atomic_val = &gil_locked; __typeof__(atomic_val->_value) new_val = -1; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_release; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; });
    ;
}

static void recreate_gil(void)
{
    ;

    create_gil();
}

static void drop_gil(PyThreadState *tstate)
{
    if (!__extension__ ({ __typeof__(&gil_locked) atomic_val = &gil_locked; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))
        Py_FatalError("drop_gil: GIL is not locked");

    if (tstate != ((void *)0)) {



        __extension__ ({ __typeof__(&gil_last_holder) atomic_val = &gil_last_holder; __typeof__(atomic_val->_value) new_val = tstate; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; });
    }

    if (pthread_mutex_lock(&(gil_mutex))) { Py_FatalError("PyMUTEX_LOCK(" "gil_mutex" ") failed"); };;
    ;
    __extension__ ({ __typeof__(&gil_locked) atomic_val = &gil_locked; __typeof__(atomic_val->_value) new_val = 0; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; });
    if (pthread_cond_signal(&(gil_cond))) { Py_FatalError("PyCOND_SIGNAL(" "gil_cond" ") failed"); };;
    if (pthread_mutex_unlock(&(gil_mutex))) { Py_FatalError("PyMUTEX_UNLOCK(" "gil_mutex" ") failed"); };;


    if (__extension__ ({ __typeof__(&gil_drop_request) atomic_val = &gil_drop_request; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }) && tstate != ((void *)0)) {
        if (pthread_mutex_lock(&(switch_mutex))) { Py_FatalError("PyMUTEX_LOCK(" "switch_mutex" ") failed"); };;

        if (__extension__ ({ __typeof__(&gil_last_holder) atomic_val = &gil_last_holder; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }) == tstate) {
        do { __extension__ ({ __typeof__(&gil_drop_request) atomic_val = &gil_drop_request; __typeof__(atomic_val->_value) new_val = 0; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; }); __extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) new_val = __extension__ ({ __typeof__(&gil_drop_request) atomic_val = &gil_drop_request; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }) | __extension__ ({ __typeof__(&pendingcalls_to_do) atomic_val = &pendingcalls_to_do; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }) | pending_async_exc; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; }); } while (0);




            if (pthread_cond_wait((&(switch_cond)), (&(switch_mutex)))) { Py_FatalError("PyCOND_WAIT(" "switch_cond" ") failed"); };;
    }
        if (pthread_mutex_unlock(&(switch_mutex))) { Py_FatalError("PyMUTEX_UNLOCK(" "switch_mutex" ") failed"); };;
    }

}

static void take_gil(PyThreadState *tstate)
{
    int err;
    if (tstate == ((void *)0))
        Py_FatalError("take_gil: NULL tstate");

    err = (*__error());
    if (pthread_mutex_lock(&(gil_mutex))) { Py_FatalError("PyMUTEX_LOCK(" "gil_mutex" ") failed"); };;

    if (!__extension__ ({ __typeof__(&gil_locked) atomic_val = &gil_locked; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))
        goto _ready;

    while (__extension__ ({ __typeof__(&gil_locked) atomic_val = &gil_locked; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) {
        int timed_out = 0;
        unsigned long saved_switchnum;

        saved_switchnum = gil_switch_number;
        { int r = PyCOND_TIMEDWAIT(&(gil_cond), &(gil_mutex), ((gil_interval >= 1 ? gil_interval : 1))); if (r < 0) Py_FatalError("PyCOND_WAIT(" "gil_cond" ") failed"); if (r) timed_out = 1; else timed_out = 0; };


        if (timed_out &&
            __extension__ ({ __typeof__(&gil_locked) atomic_val = &gil_locked; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }) &&
            gil_switch_number == saved_switchnum) {
            do { __extension__ ({ __typeof__(&gil_drop_request) atomic_val = &gil_drop_request; __typeof__(atomic_val->_value) new_val = 1; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; }); __extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) new_val = 1; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; }); } while (0);
        }
    }
_ready:


    if (pthread_mutex_lock(&(switch_mutex))) { Py_FatalError("PyMUTEX_LOCK(" "switch_mutex" ") failed"); };;


    __extension__ ({ __typeof__(&gil_locked) atomic_val = &gil_locked; __typeof__(atomic_val->_value) new_val = 1; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; });
    ;

    if (tstate != __extension__ ({ __typeof__(&gil_last_holder) atomic_val = &gil_last_holder; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) {
        __extension__ ({ __typeof__(&gil_last_holder) atomic_val = &gil_last_holder; __typeof__(atomic_val->_value) new_val = tstate; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; });
        ++gil_switch_number;
    }


    if (pthread_cond_signal(&(switch_cond))) { Py_FatalError("PyCOND_SIGNAL(" "switch_cond" ") failed"); };;
    if (pthread_mutex_unlock(&(switch_mutex))) { Py_FatalError("PyMUTEX_UNLOCK(" "switch_mutex" ") failed"); };;

    if (__extension__ ({ __typeof__(&gil_drop_request) atomic_val = &gil_drop_request; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) {
        do { __extension__ ({ __typeof__(&gil_drop_request) atomic_val = &gil_drop_request; __typeof__(atomic_val->_value) new_val = 0; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; }); __extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) new_val = __extension__ ({ __typeof__(&gil_drop_request) atomic_val = &gil_drop_request; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }) | __extension__ ({ __typeof__(&pendingcalls_to_do) atomic_val = &pendingcalls_to_do; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }) | pending_async_exc; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; }); } while (0);
    }
    if (tstate->async_exc != ((void *)0)) {
        _PyEval_SignalAsyncExc();
    }

    if (pthread_mutex_unlock(&(gil_mutex))) { Py_FatalError("PyMUTEX_UNLOCK(" "gil_mutex" ") failed"); };;
    (*__error()) = err;
}

void _PyEval_SetSwitchInterval(unsigned long microseconds)
{
    gil_interval = microseconds;
}

unsigned long _PyEval_GetSwitchInterval()
{
    return gil_interval;
}
# 296 "ceval.c" 2

int
PyEval_ThreadsInitialized(void)
{
    return gil_created();
}

void
PyEval_InitThreads(void)
{
    if (gil_created())
        return;
    create_gil();
    take_gil(((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })));
    main_thread = PyThread_get_thread_ident();
    if (!pending_lock)
        pending_lock = PyThread_allocate_lock();
}

void
_PyEval_FiniThreads(void)
{
    if (!gil_created())
        return;
    destroy_gil();
    (__builtin_expect(!(!gil_created()), 0) ? __assert_rtn(__func__, "ceval.c", 321, "!gil_created()") : (void)0);
}

void
PyEval_AcquireLock(void)
{
    PyThreadState *tstate = ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }));
    if (tstate == ((void *)0))
        Py_FatalError("PyEval_AcquireLock: current thread state is NULL");
    take_gil(tstate);
}

void
PyEval_ReleaseLock(void)
{




    drop_gil((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }));

}

void
PyEval_AcquireThread(PyThreadState *tstate)
{
    if (tstate == ((void *)0))
        Py_FatalError("PyEval_AcquireThread: NULL new thread state");

    (__builtin_expect(!(gil_created()), 0) ? __assert_rtn(__func__, "ceval.c", 350, "gil_created()") : (void)0);
    take_gil(tstate);
    if (PyThreadState_Swap(tstate) != ((void *)0))
        Py_FatalError(
            "PyEval_AcquireThread: non-NULL old thread state");
}

void
PyEval_ReleaseThread(PyThreadState *tstate)
{
    if (tstate == ((void *)0))
        Py_FatalError("PyEval_ReleaseThread: NULL thread state");
    if (PyThreadState_Swap(((void *)0)) != tstate)
        Py_FatalError("PyEval_ReleaseThread: wrong thread state");
    drop_gil(tstate);
}






void
PyEval_ReInitThreads(void)
{
    static _Py_Identifier PyId__after_fork = { 0, "_after_fork", 0 };
    PyObject *threading, *result;
    PyThreadState *tstate = ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }));

    if (!gil_created())
        return;
    recreate_gil();
    pending_lock = PyThread_allocate_lock();
    take_gil(tstate);
    main_thread = PyThread_get_thread_ident();



    tstate = ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }));
    threading = PyMapping_GetItemString(tstate->interp->modules,
                                        "threading");
    if (threading == ((void *)0)) {

        PyErr_Clear();
        return;
    }
    result = _PyObject_CallMethodId(threading, &PyId__after_fork, ((void *)0));
    if (result == ((void *)0))
        PyErr_WriteUnraisable(threading);
    else
        do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0);
    do { if ( --((PyObject*)(threading))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(threading)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(threading)))); } while (0);
}
# 412 "ceval.c"
void
_PyEval_SignalAsyncExc(void)
{
    do { pending_async_exc = 1; __extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) new_val = 1; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; }); } while (0);
}





PyThreadState *
PyEval_SaveThread(void)
{
    PyThreadState *tstate = PyThreadState_Swap(((void *)0));
    if (tstate == ((void *)0))
        Py_FatalError("PyEval_SaveThread: NULL tstate");

    if (gil_created())
        drop_gil(tstate);

    return tstate;
}

void
PyEval_RestoreThread(PyThreadState *tstate)
{
    if (tstate == ((void *)0))
        Py_FatalError("PyEval_RestoreThread: NULL tstate");

    if (gil_created()) {
        int err = (*__error());
        take_gil(tstate);

        if (_Py_Finalizing && tstate != _Py_Finalizing) {
            drop_gil(tstate);
            PyThread_exit_thread();
            (__builtin_expect(!(0), 0) ? __assert_rtn(__func__, "ceval.c", 448, "0") : (void)0);
        }
        (*__error()) = err;
    }

    PyThreadState_Swap(tstate);
}
# 489 "ceval.c"
static struct {
    int (*func)(void *);
    void *arg;
} pendingcalls[32];
static int pendingfirst = 0;
static int pendinglast = 0;

int
Py_AddPendingCall(int (*func)(void *), void *arg)
{
    int i, j, result=0;
    PyThread_type_lock lock = pending_lock;
# 513 "ceval.c"
    if (lock != ((void *)0)) {
        for (i = 0; i<100; i++) {
            if (PyThread_acquire_lock(lock, 0))
                break;
        }
        if (i == 100)
            return -1;
    }

    i = pendinglast;
    j = (i + 1) % 32;
    if (j == pendingfirst) {
        result = -1;
    } else {
        pendingcalls[i].func = func;
        pendingcalls[i].arg = arg;
        pendinglast = j;
    }

    do { __extension__ ({ __typeof__(&pendingcalls_to_do) atomic_val = &pendingcalls_to_do; __typeof__(atomic_val->_value) new_val = 1; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; }); __extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) new_val = 1; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; }); } while (0);
    if (lock != ((void *)0))
        PyThread_release_lock(lock);
    return result;
}

int
Py_MakePendingCalls(void)
{
    static int busy = 0;
    int i;
    int r = 0;

    if (!pending_lock) {

        pending_lock = PyThread_allocate_lock();
        if (pending_lock == ((void *)0))
            return -1;
    }


    if (main_thread && PyThread_get_thread_ident() != main_thread)
        return 0;

    if (busy)
        return 0;
    busy = 1;

    for (i=0; i<32; i++) {
        int j;
        int (*func)(void *);
        void *arg = ((void *)0);


        PyThread_acquire_lock(pending_lock, 1);
        j = pendingfirst;
        if (j == pendinglast) {
            func = ((void *)0);
        } else {
            func = pendingcalls[j].func;
            arg = pendingcalls[j].arg;
            pendingfirst = (j + 1) % 32;
        }
        if (pendingfirst != pendinglast)
            do { __extension__ ({ __typeof__(&pendingcalls_to_do) atomic_val = &pendingcalls_to_do; __typeof__(atomic_val->_value) new_val = 1; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; }); __extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) new_val = 1; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; }); } while (0);
        else
            do { __extension__ ({ __typeof__(&pendingcalls_to_do) atomic_val = &pendingcalls_to_do; __typeof__(atomic_val->_value) new_val = 0; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; }); __extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) new_val = __extension__ ({ __typeof__(&gil_drop_request) atomic_val = &gil_drop_request; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }) | __extension__ ({ __typeof__(&pendingcalls_to_do) atomic_val = &pendingcalls_to_do; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }) | pending_async_exc; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; }); } while (0);
        PyThread_release_lock(pending_lock);

        if (func == ((void *)0))
            break;
        r = func(arg);
        if (r)
            break;
    }
    busy = 0;
    return r;
}
# 686 "ceval.c"
static int recursion_limit = 1000;
int _Py_CheckRecursionLimit = 1000;

int
Py_GetRecursionLimit(void)
{
    return recursion_limit;
}

void
Py_SetRecursionLimit(int new_limit)
{
    recursion_limit = new_limit;
    _Py_CheckRecursionLimit = recursion_limit;
}






int
_Py_CheckRecursiveCall(char *where)
{
    PyThreadState *tstate = ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }));
# 719 "ceval.c"
    _Py_CheckRecursionLimit = recursion_limit;
    if (tstate->recursion_critical)

        return 0;
    if (tstate->overflowed) {
        if (tstate->recursion_depth > recursion_limit + 50) {

            Py_FatalError("Cannot recover from stack overflow.");
        }
        return 0;
    }
    if (tstate->recursion_depth > recursion_limit) {
        --tstate->recursion_depth;
        tstate->overflowed = 1;
        PyErr_Format(PyExc_RuntimeError,
                     "maximum recursion depth exceeded%s",
                     where);
        return -1;
    }
    return 0;
}


enum why_code {
        WHY_NOT = 0x0001,
        WHY_EXCEPTION = 0x0002,
        WHY_RERAISE = 0x0004,
        WHY_RETURN = 0x0008,
        WHY_BREAK = 0x0010,
        WHY_CONTINUE = 0x0020,
        WHY_YIELD = 0x0040,
        WHY_SILENCED = 0x0080
};

static void save_exc_state(PyThreadState *, PyFrameObject *);
static void swap_exc_state(PyThreadState *, PyFrameObject *);
static void restore_and_clear_exc_state(PyThreadState *, PyFrameObject *);
static enum why_code do_raise(PyObject *, PyObject *);
static int unpack_iterable(PyObject *, int, int, PyObject **);






static int _Py_TracingPossible = 0;



PyObject *
PyEval_EvalCode(PyObject *co, PyObject *globals, PyObject *locals)
{
    return PyEval_EvalCodeEx(co,
                      globals, locals,
                      (PyObject **)((void *)0), 0,
                      (PyObject **)((void *)0), 0,
                      (PyObject **)((void *)0), 0,
                      ((void *)0), ((void *)0));
}




PyObject *
PyEval_EvalFrame(PyFrameObject *f) {



    return PyEval_EvalFrameEx(f, 0);
}

PyObject *
PyEval_EvalFrameEx(PyFrameObject *f, int throwflag)
{



    register PyObject **stack_pointer;
    register unsigned char *next_instr;
    register int opcode;
    register int oparg;
    register enum why_code why;
    register int err;
    register PyObject *x;
    register PyObject *v;
    register PyObject *w;
    register PyObject *u;
    register PyObject *t;
    register PyObject **fastlocals, **freevars;
    PyObject *retval = ((void *)0);
    PyThreadState *tstate = ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }));
    PyCodeObject *co;
# 819 "ceval.c"
    int instr_ub = -1, instr_lb = 0, instr_prev = -1;

    unsigned char *first_instr;
    PyObject *names;
    PyObject *consts;
# 887 "ceval.c"
# 1 "opcode_targets.h" 1
static void *opcode_targets[256] = {
    &&_unknown_opcode,
    &&TARGET_POP_TOP,
    &&TARGET_ROT_TWO,
    &&TARGET_ROT_THREE,
    &&TARGET_DUP_TOP,
    &&TARGET_DUP_TOP_TWO,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&TARGET_NOP,
    &&TARGET_UNARY_POSITIVE,
    &&TARGET_UNARY_NEGATIVE,
    &&TARGET_UNARY_NOT,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&TARGET_UNARY_INVERT,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&TARGET_BINARY_POWER,
    &&TARGET_BINARY_MULTIPLY,
    &&_unknown_opcode,
    &&TARGET_BINARY_MODULO,
    &&TARGET_BINARY_ADD,
    &&TARGET_BINARY_SUBTRACT,
    &&TARGET_BINARY_SUBSCR,
    &&TARGET_BINARY_FLOOR_DIVIDE,
    &&TARGET_BINARY_TRUE_DIVIDE,
    &&TARGET_INPLACE_FLOOR_DIVIDE,
    &&TARGET_INPLACE_TRUE_DIVIDE,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&TARGET_STORE_MAP,
    &&TARGET_INPLACE_ADD,
    &&TARGET_INPLACE_SUBTRACT,
    &&TARGET_INPLACE_MULTIPLY,
    &&_unknown_opcode,
    &&TARGET_INPLACE_MODULO,
    &&TARGET_STORE_SUBSCR,
    &&TARGET_DELETE_SUBSCR,
    &&TARGET_BINARY_LSHIFT,
    &&TARGET_BINARY_RSHIFT,
    &&TARGET_BINARY_AND,
    &&TARGET_BINARY_XOR,
    &&TARGET_BINARY_OR,
    &&TARGET_INPLACE_POWER,
    &&TARGET_GET_ITER,
    &&TARGET_STORE_LOCALS,
    &&TARGET_PRINT_EXPR,
    &&TARGET_LOAD_BUILD_CLASS,
    &&TARGET_YIELD_FROM,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&TARGET_INPLACE_LSHIFT,
    &&TARGET_INPLACE_RSHIFT,
    &&TARGET_INPLACE_AND,
    &&TARGET_INPLACE_XOR,
    &&TARGET_INPLACE_OR,
    &&TARGET_BREAK_LOOP,
    &&TARGET_WITH_CLEANUP,
    &&_unknown_opcode,
    &&TARGET_RETURN_VALUE,
    &&TARGET_IMPORT_STAR,
    &&_unknown_opcode,
    &&TARGET_YIELD_VALUE,
    &&TARGET_POP_BLOCK,
    &&TARGET_END_FINALLY,
    &&TARGET_POP_EXCEPT,
    &&TARGET_STORE_NAME,
    &&TARGET_DELETE_NAME,
    &&TARGET_UNPACK_SEQUENCE,
    &&TARGET_FOR_ITER,
    &&TARGET_UNPACK_EX,
    &&TARGET_STORE_ATTR,
    &&TARGET_DELETE_ATTR,
    &&TARGET_STORE_GLOBAL,
    &&TARGET_DELETE_GLOBAL,
    &&_unknown_opcode,
    &&TARGET_LOAD_CONST,
    &&TARGET_LOAD_NAME,
    &&TARGET_BUILD_TUPLE,
    &&TARGET_BUILD_LIST,
    &&TARGET_BUILD_SET,
    &&TARGET_BUILD_MAP,
    &&TARGET_LOAD_ATTR,
    &&TARGET_COMPARE_OP,
    &&TARGET_IMPORT_NAME,
    &&TARGET_IMPORT_FROM,
    &&TARGET_JUMP_FORWARD,
    &&TARGET_JUMP_IF_FALSE_OR_POP,
    &&TARGET_JUMP_IF_TRUE_OR_POP,
    &&TARGET_JUMP_ABSOLUTE,
    &&TARGET_POP_JUMP_IF_FALSE,
    &&TARGET_POP_JUMP_IF_TRUE,
    &&TARGET_LOAD_GLOBAL,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&TARGET_CONTINUE_LOOP,
    &&TARGET_SETUP_LOOP,
    &&TARGET_SETUP_EXCEPT,
    &&TARGET_SETUP_FINALLY,
    &&_unknown_opcode,
    &&TARGET_LOAD_FAST,
    &&TARGET_STORE_FAST,
    &&TARGET_DELETE_FAST,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&TARGET_RAISE_VARARGS,
    &&TARGET_CALL_FUNCTION,
    &&TARGET_MAKE_FUNCTION,
    &&TARGET_BUILD_SLICE,
    &&TARGET_MAKE_CLOSURE,
    &&TARGET_LOAD_CLOSURE,
    &&TARGET_LOAD_DEREF,
    &&TARGET_STORE_DEREF,
    &&TARGET_DELETE_DEREF,
    &&_unknown_opcode,
    &&TARGET_CALL_FUNCTION_VAR,
    &&TARGET_CALL_FUNCTION_KW,
    &&TARGET_CALL_FUNCTION_VAR_KW,
    &&TARGET_SETUP_WITH,
    &&TARGET_EXTENDED_ARG,
    &&TARGET_LIST_APPEND,
    &&TARGET_SET_ADD,
    &&TARGET_MAP_ADD,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode,
    &&_unknown_opcode
};
# 888 "ceval.c" 2
# 1124 "ceval.c"
    if (((++(((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->recursion_depth) > _Py_CheckRecursionLimit) && _Py_CheckRecursiveCall("")))
        return ((void *)0);

    tstate->frame = f;

    if (tstate->use_tracing) {
        if (tstate->c_tracefunc != ((void *)0)) {
# 1144 "ceval.c"
            if (call_trace_protected(tstate->c_tracefunc,
                                     tstate->c_traceobj,
                                     f, 0, (&_Py_NoneStruct))) {

                goto exit_eval_frame;
            }
        }
        if (tstate->c_profilefunc != ((void *)0)) {


            if (call_trace_protected(tstate->c_profilefunc,
                                     tstate->c_profileobj,
                                     f, 0, (&_Py_NoneStruct))) {

                goto exit_eval_frame;
            }
        }
    }

    co = f->f_code;
    names = co->co_names;
    consts = co->co_consts;
    fastlocals = f->f_localsplus;
    freevars = f->f_localsplus + co->co_nlocals;
    first_instr = (unsigned char*) ((__builtin_expect(!(((((((PyObject*)(co->co_code))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "ceval.c", 1168, "PyBytes_Check(co->co_code)") : (void)0), (((PyBytesObject *)(co->co_code))->ob_sval));
# 1188 "ceval.c"
    next_instr = first_instr + f->f_lasti + 1;
    stack_pointer = f->f_stacktop;
    (__builtin_expect(!(stack_pointer != ((void *)0)), 0) ? __assert_rtn(__func__, "ceval.c", 1190, "stack_pointer != NULL") : (void)0);
    f->f_stacktop = ((void *)0);

    if (co->co_flags & 0x0020 && !throwflag) {
        if (f->f_exc_type != ((void *)0) && f->f_exc_type != (&_Py_NoneStruct)) {



            swap_exc_state(tstate, f);
        }
        else
            save_exc_state(tstate, f);
    }





    why = WHY_NOT;
    err = 0;
    x = (&_Py_NoneStruct);
    w = ((void *)0);

    if (throwflag) {
        why = WHY_EXCEPTION;
        goto on_error;
    }

    for (;;) {
# 1236 "ceval.c"
        (__builtin_expect(!(stack_pointer >= f->f_valuestack), 0) ? __assert_rtn(__func__, "ceval.c", 1236, "stack_pointer >= f->f_valuestack") : (void)0);
        (__builtin_expect(!(((int)(stack_pointer - f->f_valuestack)) <= co->co_stacksize), 0) ? __assert_rtn(__func__, "ceval.c", 1237, "STACK_LEVEL() <= co->co_stacksize") : (void)0);
# 1247 "ceval.c"
        if (__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) {
            if (*next_instr == 122) {


                goto fast_next_opcode;
            }
            tstate->tick_counter++;



            if (__extension__ ({ __typeof__(&pendingcalls_to_do) atomic_val = &pendingcalls_to_do; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) {
                if (Py_MakePendingCalls() < 0) {
                    why = WHY_EXCEPTION;
                    goto on_error;
                }
            }

            if (__extension__ ({ __typeof__(&gil_drop_request) atomic_val = &gil_drop_request; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) {

                if (PyThreadState_Swap(((void *)0)) != tstate)
                    Py_FatalError("ceval: tstate mix-up");
                drop_gil(tstate);



                take_gil(tstate);
                if (PyThreadState_Swap(tstate) != ((void *)0))
                    Py_FatalError("ceval: orphan tstate");
            }


            if (tstate->async_exc != ((void *)0)) {
                x = tstate->async_exc;
                tstate->async_exc = ((void *)0);
                do { pending_async_exc = 0; __extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) new_val = __extension__ ({ __typeof__(&gil_drop_request) atomic_val = &gil_drop_request; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }) | __extension__ ({ __typeof__(&pendingcalls_to_do) atomic_val = &pendingcalls_to_do; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }) | pending_async_exc; volatile __typeof__(new_val) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: _Py_atomic_signal_fence(_Py_memory_order_release); case _Py_memory_order_relaxed: *volatile_data = new_val; break; case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: __asm__ volatile("xchg %0, %1" : "+r"(new_val) : "m"(atomic_val->_value) : "memory"); break; } ; }); } while (0);
                PyErr_SetNone(x);
                do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);
                why = WHY_EXCEPTION;
                goto on_error;
            }
        }

    fast_next_opcode:
        f->f_lasti = ((int)(next_instr - first_instr));



        if (_Py_TracingPossible &&
            tstate->c_tracefunc != ((void *)0) && !tstate->tracing) {


            f->f_stacktop = stack_pointer;

            err = maybe_call_line_trace(tstate->c_tracefunc,
                                        tstate->c_traceobj,
                                        f, &instr_lb, &instr_ub,
                                        &instr_prev);

            (next_instr = first_instr + (f->f_lasti));
            if (f->f_stacktop != ((void *)0)) {
                stack_pointer = f->f_stacktop;
                f->f_stacktop = ((void *)0);
            }
            if (err) {

                goto on_error;
            }
        }



        opcode = (*next_instr++);
        oparg = 0;

        if (((opcode) >= 90))
            oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]);
    dispatch_opcode:
# 1348 "ceval.c"
        ;

        switch (opcode) {






        TARGET_NOP: opcode = 9; if (((9) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 9:
            { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; };

        TARGET_LOAD_FAST: opcode = 124; if (((124) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 124:
            x = (fastlocals[oparg]);
            if (x != ((void *)0)) {
                ( ((PyObject*)(x))->ob_refcnt++);
                (*stack_pointer++ = (x));
                { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; };
            }
            format_exc_check_arg(PyExc_UnboundLocalError,
                "local variable '%.200s' referenced before assignment",
                PyTuple_GetItem(co->co_varnames, oparg));
            break;

        TARGET_LOAD_CONST: opcode = 100; if (((100) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 100:
            x = (((PyTupleObject *)((PyTupleObject *)(consts)))->ob_item[(oparg)]);
            ( ((PyObject*)(x))->ob_refcnt++);
            (*stack_pointer++ = (x));
            { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; };

        PRED_STORE_FAST:;
        TARGET_STORE_FAST: opcode = 125; if (((125) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 125:
            v = (*--stack_pointer);
            do { PyObject *tmp = (fastlocals[oparg]); (fastlocals[oparg]) = v; do { if ((tmp) == ((void *)0)) ; else do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0); } while (0); } while (0);
            { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; };

        TARGET_POP_TOP: opcode = 1; if (((1) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 1:
            v = (*--stack_pointer);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; };

        TARGET_ROT_TWO: opcode = 2; if (((2) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 2:
            v = (stack_pointer[-1]);
            w = (stack_pointer[-2]);
            (stack_pointer[-1] = (w));
            (stack_pointer[-2] = (v));
            { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; };

        TARGET_ROT_THREE: opcode = 3; if (((3) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 3:
            v = (stack_pointer[-1]);
            w = (stack_pointer[-2]);
            x = (stack_pointer[-3]);
            (stack_pointer[-1] = (w));
            (stack_pointer[-2] = (x));
            (stack_pointer[-3] = (v));
            { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; };

        TARGET_DUP_TOP: opcode = 4; if (((4) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 4:
            v = (stack_pointer[-1]);
            ( ((PyObject*)(v))->ob_refcnt++);
            (*stack_pointer++ = (v));
            { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; };

        TARGET_DUP_TOP_TWO: opcode = 5; if (((5) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 5:
            x = (stack_pointer[-1]);
            ( ((PyObject*)(x))->ob_refcnt++);
            w = (stack_pointer[-2]);
            ( ((PyObject*)(w))->ob_refcnt++);
            (stack_pointer += 2);
            (stack_pointer[-1] = (x));
            (stack_pointer[-2] = (w));
            { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; };

        TARGET_UNARY_POSITIVE: opcode = 10; if (((10) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 10:
            v = (stack_pointer[-1]);
            x = PyNumber_Positive(v);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_UNARY_NEGATIVE: opcode = 11; if (((11) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 11:
            v = (stack_pointer[-1]);
            x = PyNumber_Negative(v);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_UNARY_NOT: opcode = 12; if (((12) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 12:
            v = (stack_pointer[-1]);
            err = PyObject_IsTrue(v);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            if (err == 0) {
                ( ((PyObject*)(((PyObject *) &_Py_TrueStruct)))->ob_refcnt++);
                (stack_pointer[-1] = (((PyObject *) &_Py_TrueStruct)));
                { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            }
            else if (err > 0) {
                ( ((PyObject*)(((PyObject *) &_Py_FalseStruct)))->ob_refcnt++);
                (stack_pointer[-1] = (((PyObject *) &_Py_FalseStruct)));
                err = 0;
                { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            }
            (stack_pointer += -1);
            break;

        TARGET_UNARY_INVERT: opcode = 15; if (((15) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 15:
            v = (stack_pointer[-1]);
            x = PyNumber_Invert(v);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_BINARY_POWER: opcode = 19; if (((19) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 19:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_Power(v, w, (&_Py_NoneStruct));
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_BINARY_MULTIPLY: opcode = 20; if (((20) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 20:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_Multiply(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_BINARY_TRUE_DIVIDE: opcode = 27; if (((27) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 27:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_TrueDivide(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_BINARY_FLOOR_DIVIDE: opcode = 26; if (((26) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 26:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_FloorDivide(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_BINARY_MODULO: opcode = 22; if (((22) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 22:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            if (((((PyObject*)(v))->ob_type) == &PyUnicode_Type))
                x = PyUnicode_Format(v, w);
            else
                x = PyNumber_Remainder(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_BINARY_ADD: opcode = 23; if (((23) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 23:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            if (((((PyObject*)(v))->ob_type) == &PyUnicode_Type) &&
                     ((((PyObject*)(w))->ob_type) == &PyUnicode_Type)) {
                x = unicode_concatenate(v, w, f, next_instr);

                goto skip_decref_vx;
            }
            else {
                x = PyNumber_Add(v, w);
            }
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
          skip_decref_vx:
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_BINARY_SUBTRACT: opcode = 24; if (((24) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 24:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_Subtract(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_BINARY_SUBSCR: opcode = 25; if (((25) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 25:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyObject_GetItem(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_BINARY_LSHIFT: opcode = 62; if (((62) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 62:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_Lshift(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_BINARY_RSHIFT: opcode = 63; if (((63) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 63:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_Rshift(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_BINARY_AND: opcode = 64; if (((64) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 64:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_And(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_BINARY_XOR: opcode = 65; if (((65) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 65:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_Xor(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_BINARY_OR: opcode = 66; if (((66) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 66:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_Or(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_LIST_APPEND: opcode = 145; if (((145) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 145:
            w = (*--stack_pointer);
            v = (stack_pointer[-(oparg)]);
            err = PyList_Append(v, w);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            if (err == 0) {
                if (0) goto PRED_JUMP_ABSOLUTE;
                { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            }
            break;

        TARGET_SET_ADD: opcode = 146; if (((146) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 146:
            w = (*--stack_pointer);
            v = stack_pointer[-oparg];
            err = PySet_Add(v, w);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            if (err == 0) {
                if (0) goto PRED_JUMP_ABSOLUTE;
                { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            }
            break;

        TARGET_INPLACE_POWER: opcode = 67; if (((67) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 67:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_InPlacePower(v, w, (&_Py_NoneStruct));
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_INPLACE_MULTIPLY: opcode = 57; if (((57) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 57:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_InPlaceMultiply(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_INPLACE_TRUE_DIVIDE: opcode = 29; if (((29) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 29:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_InPlaceTrueDivide(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_INPLACE_FLOOR_DIVIDE: opcode = 28; if (((28) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 28:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_InPlaceFloorDivide(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_INPLACE_MODULO: opcode = 59; if (((59) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 59:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_InPlaceRemainder(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_INPLACE_ADD: opcode = 55; if (((55) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 55:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            if (((((PyObject*)(v))->ob_type) == &PyUnicode_Type) &&
                     ((((PyObject*)(w))->ob_type) == &PyUnicode_Type)) {
                x = unicode_concatenate(v, w, f, next_instr);

                goto skip_decref_v;
            }
            else {
                x = PyNumber_InPlaceAdd(v, w);
            }
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
          skip_decref_v:
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_INPLACE_SUBTRACT: opcode = 56; if (((56) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 56:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_InPlaceSubtract(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_INPLACE_LSHIFT: opcode = 75; if (((75) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 75:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_InPlaceLshift(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_INPLACE_RSHIFT: opcode = 76; if (((76) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 76:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_InPlaceRshift(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_INPLACE_AND: opcode = 77; if (((77) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 77:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_InPlaceAnd(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_INPLACE_XOR: opcode = 78; if (((78) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 78:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_InPlaceXor(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_INPLACE_OR: opcode = 79; if (((79) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 79:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = PyNumber_InPlaceOr(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_STORE_SUBSCR: opcode = 60; if (((60) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 60:
            w = (stack_pointer[-1]);
            v = (stack_pointer[-2]);
            u = (stack_pointer[-3]);
            (stack_pointer += -3);

            err = PyObject_SetItem(v, w, u);
            do { if ( --((PyObject*)(u))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(u)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(u)))); } while (0);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            if (err == 0) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_DELETE_SUBSCR: opcode = 61; if (((61) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 61:
            w = (stack_pointer[-1]);
            v = (stack_pointer[-2]);
            (stack_pointer += -2);

            err = PyObject_DelItem(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            if (err == 0) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_PRINT_EXPR: opcode = 70; if (((70) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 70:
            v = (*--stack_pointer);
            w = PySys_GetObject("displayhook");
            if (w == ((void *)0)) {
                PyErr_SetString(PyExc_RuntimeError,
                                "lost sys.displayhook");
                err = -1;
                x = ((void *)0);
            }
            if (err == 0) {
                x = PyTuple_Pack(1, v);
                if (x == ((void *)0))
                    err = -1;
            }
            if (err == 0) {
                w = PyEval_CallObjectWithKeywords(w, x, (PyObject *)((void *)0));
                do { if ((w) == ((void *)0)) ; else do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0); } while (0);
                if (w == ((void *)0))
                    err = -1;
            }
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ((x) == ((void *)0)) ; else do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0); } while (0);
            break;




        TARGET_RAISE_VARARGS: opcode = 130; if (((130) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 130:
            v = w = ((void *)0);
            switch (oparg) {
            case 2:
                v = (*--stack_pointer);
            case 1:
                w = (*--stack_pointer);
            case 0:
                why = do_raise(w, v);
                break;
            default:
                PyErr_SetString(PyExc_SystemError,
                           "bad RAISE_VARARGS oparg");
                why = WHY_EXCEPTION;
                break;
            }
            break;

        TARGET_STORE_LOCALS: opcode = 69; if (((69) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 69:
            x = (*--stack_pointer);
            v = f->f_locals;
            do { if ((v) == ((void *)0)) ; else do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0); } while (0);
            f->f_locals = x;
            { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };

        TARGET_RETURN_VALUE: opcode = 83; if (((83) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 83:
            retval = (*--stack_pointer);
            why = WHY_RETURN;
            goto fast_block_end;

        TARGET_YIELD_FROM: opcode = 72; if (((72) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 72:
            u = (*--stack_pointer);
            x = (stack_pointer[-1]);

            if (((((PyObject*)(x))->ob_type) == &PyGen_Type)) {
                retval = _PyGen_Send((PyGenObject *)x, u);
            } else {
                static _Py_Identifier PyId_send = { 0, "send", 0 };
                if (u == (&_Py_NoneStruct))
                    retval = (((PyObject*)(x))->ob_type)->tp_iternext(x);
                else
                    retval = _PyObject_CallMethodId(x, &PyId_send, "O", u);
            }
            do { if ( --((PyObject*)(u))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(u)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(u)))); } while (0);
            if (!retval) {
                PyObject *val;
                x = (*--stack_pointer);
                do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);
                err = _PyGen_FetchStopIterationValue(&val);
                if (err < 0) {
                    x = ((void *)0);
                    break;
                }
                x = val;
                (*stack_pointer++ = (x));
                continue;
            }

            f->f_stacktop = stack_pointer;
            why = WHY_YIELD;

            f->f_lasti--;
            goto fast_yield;

        TARGET_YIELD_VALUE: opcode = 86; if (((86) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 86:
            retval = (*--stack_pointer);
            f->f_stacktop = stack_pointer;
            why = WHY_YIELD;
            goto fast_yield;

        TARGET_POP_EXCEPT: opcode = 89; if (((89) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 89:
            {
                PyTryBlock *b = PyFrame_BlockPop(f);
                if (b->b_type != 257) {
                    PyErr_SetString(PyExc_SystemError,
                        "popped block is not an except handler");
                    why = WHY_EXCEPTION;
                    break;
                }
                { PyObject *type, *value, *traceback; (__builtin_expect(!(((int)(stack_pointer - f->f_valuestack)) >= (b)->b_level + 3), 0) ? __assert_rtn(__func__, "ceval.c", 1886, "STACK_LEVEL() >= (b)->b_level + 3") : (void)0); while (((int)(stack_pointer - f->f_valuestack)) > (b)->b_level + 3) { value = (*--stack_pointer); do { if ((value) == ((void *)0)) ; else do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); } while (0); } type = tstate->exc_type; value = tstate->exc_value; traceback = tstate->exc_traceback; tstate->exc_type = (*--stack_pointer); tstate->exc_value = (*--stack_pointer); tstate->exc_traceback = (*--stack_pointer); do { if ((type) == ((void *)0)) ; else do { if ( --((PyObject*)(type))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type)))); } while (0); } while (0); do { if ((value) == ((void *)0)) ; else do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); } while (0); do { if ((traceback) == ((void *)0)) ; else do { if ( --((PyObject*)(traceback))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(traceback)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(traceback)))); } while (0); } while (0); };
            }
            { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };

        TARGET_POP_BLOCK: opcode = 87; if (((87) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 87:
            {
                PyTryBlock *b = PyFrame_BlockPop(f);
                while (((int)(stack_pointer - f->f_valuestack)) > (b)->b_level) { PyObject *v = (*--stack_pointer); do { if ((v) == ((void *)0)) ; else do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0); } while (0); };
            }
            { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };

        PRED_END_FINALLY:;
        TARGET_END_FINALLY: opcode = 88; if (((88) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 88:
            v = (*--stack_pointer);
            if (((((((PyObject*)(v))->ob_type))->tp_flags & ((1L<<24))) != 0)) {
                why = (enum why_code) PyLong_AsLong(v);
                (__builtin_expect(!(why != WHY_YIELD), 0) ? __assert_rtn(__func__, "ceval.c", 1902, "why != WHY_YIELD") : (void)0);
                if (why == WHY_RETURN ||
                    why == WHY_CONTINUE)
                    retval = (*--stack_pointer);
                if (why == WHY_SILENCED) {




                    PyTryBlock *b = PyFrame_BlockPop(f);
                    (__builtin_expect(!(b->b_type == 257), 0) ? __assert_rtn(__func__, "ceval.c", 1912, "b->b_type == EXCEPT_HANDLER") : (void)0);
                    { PyObject *type, *value, *traceback; (__builtin_expect(!(((int)(stack_pointer - f->f_valuestack)) >= (b)->b_level + 3), 0) ? __assert_rtn(__func__, "ceval.c", 1913, "STACK_LEVEL() >= (b)->b_level + 3") : (void)0); while (((int)(stack_pointer - f->f_valuestack)) > (b)->b_level + 3) { value = (*--stack_pointer); do { if ((value) == ((void *)0)) ; else do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); } while (0); } type = tstate->exc_type; value = tstate->exc_value; traceback = tstate->exc_traceback; tstate->exc_type = (*--stack_pointer); tstate->exc_value = (*--stack_pointer); tstate->exc_traceback = (*--stack_pointer); do { if ((type) == ((void *)0)) ; else do { if ( --((PyObject*)(type))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type)))); } while (0); } while (0); do { if ((value) == ((void *)0)) ; else do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); } while (0); do { if ((traceback) == ((void *)0)) ; else do { if ( --((PyObject*)(traceback))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(traceback)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(traceback)))); } while (0); } while (0); };
                    why = WHY_NOT;
                }
            }
            else if ((((((((PyObject*)((v)))->ob_type))->tp_flags & ((1L<<31))) != 0) && ((((PyTypeObject*)(v))->tp_flags & ((1L<<30))) != 0))) {
                w = (*--stack_pointer);
                u = (*--stack_pointer);
                PyErr_Restore(v, w, u);
                why = WHY_RERAISE;
                break;
            }
            else if (v != (&_Py_NoneStruct)) {
                PyErr_SetString(PyExc_SystemError,
                    "'finally' pops bad exception");
                why = WHY_EXCEPTION;
            }
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            break;

        TARGET_LOAD_BUILD_CLASS: opcode = 71; if (((71) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 71:
        {
            static _Py_Identifier PyId___build_class__ = { 0, "__build_class__", 0 };

            if (((((PyObject*)(f->f_builtins))->ob_type) == &PyDict_Type)) {
                x = _PyDict_GetItemId(f->f_builtins, &PyId___build_class__);
                if (x == ((void *)0)) {
                    PyErr_SetString(PyExc_NameError,
                                    "__build_class__ not found");
                    break;
                }
                ( ((PyObject*)(x))->ob_refcnt++);
            }
            else {
                PyObject *build_class_str = _PyUnicode_FromId(&PyId___build_class__);
                if (build_class_str == ((void *)0))
                    break;
                x = PyObject_GetItem(f->f_builtins, build_class_str);
                if (x == ((void *)0)) {
                    if (PyErr_ExceptionMatches(PyExc_KeyError))
                        PyErr_SetString(PyExc_NameError,
                                        "__build_class__ not found");
                    break;
                }
            }
            (*stack_pointer++ = (x));
            break;
        }

        TARGET_STORE_NAME: opcode = 90; if (((90) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 90:
            w = (((PyTupleObject *)((PyTupleObject *)(names)))->ob_item[(oparg)]);
            v = (*--stack_pointer);
            if ((x = f->f_locals) != ((void *)0)) {
                if (((((PyObject*)(x))->ob_type) == &PyDict_Type))
                    err = PyDict_SetItem(x, w, v);
                else
                    err = PyObject_SetItem(x, w, v);
                do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
                if (err == 0) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
                break;
            }
            PyErr_Format(PyExc_SystemError,
                         "no locals found when storing %R", w);
            break;

        TARGET_DELETE_NAME: opcode = 91; if (((91) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 91:
            w = (((PyTupleObject *)((PyTupleObject *)(names)))->ob_item[(oparg)]);
            if ((x = f->f_locals) != ((void *)0)) {
                if ((err = PyObject_DelItem(x, w)) != 0)
                    format_exc_check_arg(PyExc_NameError,
                                         "name '%.200s' is not defined",
                                         w);
                break;
            }
            PyErr_Format(PyExc_SystemError,
                         "no locals when deleting %R", w);
            break;

        PRED_UNPACK_SEQUENCE:;
        TARGET_UNPACK_SEQUENCE: opcode = 92; if (((92) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 92:
            v = (*--stack_pointer);
            if (((((PyObject*)(v))->ob_type) == &PyTuple_Type) &&
                (((PyVarObject*)(v))->ob_size) == oparg) {
                PyObject **items = ((PyTupleObject *)v)->ob_item;

                while (oparg--) {
                    w = items[oparg];
                    ( ((PyObject*)(w))->ob_refcnt++);
                    (*stack_pointer++ = (w));
                }
                do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
                { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            } else if (((((PyObject*)(v))->ob_type) == &PyList_Type) &&
                       (((PyVarObject*)(v))->ob_size) == oparg) {
                PyObject **items = ((PyListObject *)v)->ob_item;

                while (oparg--) {
                    w = items[oparg];
                    ( ((PyObject*)(w))->ob_refcnt++);
                    (*stack_pointer++ = (w));
                }
            } else if (unpack_iterable(v, oparg, -1,
                                       stack_pointer + oparg)) {
                (stack_pointer += oparg);
            } else {

                why = WHY_EXCEPTION;
            }
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            break;

        TARGET_UNPACK_EX: opcode = 94; if (((94) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 94:
        {
            int totalargs = 1 + (oparg & 0xFF) + (oparg >> 8);
            v = (*--stack_pointer);

            if (unpack_iterable(v, oparg & 0xFF, oparg >> 8,
                                stack_pointer + totalargs)) {
                stack_pointer += totalargs;
            } else {
                why = WHY_EXCEPTION;
            }
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            break;
        }

        TARGET_STORE_ATTR: opcode = 95; if (((95) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 95:
            w = (((PyTupleObject *)((PyTupleObject *)(names)))->ob_item[(oparg)]);
            v = (stack_pointer[-1]);
            u = (stack_pointer[-2]);
            (stack_pointer += -2);
            err = PyObject_SetAttr(v, w, u);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(u))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(u)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(u)))); } while (0);
            if (err == 0) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_DELETE_ATTR: opcode = 96; if (((96) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 96:
            w = (((PyTupleObject *)((PyTupleObject *)(names)))->ob_item[(oparg)]);
            v = (*--stack_pointer);
            err = PyObject_SetAttr(v, w, (PyObject *)((void *)0));

            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            break;

        TARGET_STORE_GLOBAL: opcode = 97; if (((97) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 97:
            w = (((PyTupleObject *)((PyTupleObject *)(names)))->ob_item[(oparg)]);
            v = (*--stack_pointer);
            err = PyDict_SetItem(f->f_globals, w, v);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            if (err == 0) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_DELETE_GLOBAL: opcode = 98; if (((98) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 98:
            w = (((PyTupleObject *)((PyTupleObject *)(names)))->ob_item[(oparg)]);
            if ((err = PyDict_DelItem(f->f_globals, w)) != 0)
                format_exc_check_arg(
                    PyExc_NameError, "global name '%.200s' is not defined", w);
            break;

        TARGET_LOAD_NAME: opcode = 101; if (((101) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 101:
            w = (((PyTupleObject *)((PyTupleObject *)(names)))->ob_item[(oparg)]);
            if ((v = f->f_locals) == ((void *)0)) {
                PyErr_Format(PyExc_SystemError,
                             "no locals when loading %R", w);
                why = WHY_EXCEPTION;
                break;
            }
            if (((((PyObject*)(v))->ob_type) == &PyDict_Type)) {
                x = PyDict_GetItem(v, w);
                do { if ((x) == ((void *)0)) ; else ( ((PyObject*)(x))->ob_refcnt++); } while (0);
            }
            else {
                x = PyObject_GetItem(v, w);
                if (x == ((void *)0) && PyErr_Occurred()) {
                    if (!PyErr_ExceptionMatches(
                                    PyExc_KeyError))
                        break;
                    PyErr_Clear();
                }
            }
            if (x == ((void *)0)) {
                x = PyDict_GetItem(f->f_globals, w);
                do { if ((x) == ((void *)0)) ; else ( ((PyObject*)(x))->ob_refcnt++); } while (0);
                if (x == ((void *)0)) {
                    if (((((PyObject*)(f->f_builtins))->ob_type) == &PyDict_Type)) {
                        x = PyDict_GetItem(f->f_builtins, w);
                        if (x == ((void *)0)) {
                            format_exc_check_arg(
                                        PyExc_NameError,
                                        "name '%.200s' is not defined", w);
                            break;
                        }
                        ( ((PyObject*)(x))->ob_refcnt++);
                    }
                    else {
                        x = PyObject_GetItem(f->f_builtins, w);
                        if (x == ((void *)0)) {
                            if (PyErr_ExceptionMatches(PyExc_KeyError))
                                format_exc_check_arg(
                                            PyExc_NameError,
                                            "name '%.200s' is not defined", w);
                            break;
                        }
                    }
                }
            }
            (*stack_pointer++ = (x));
            { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };

        TARGET_LOAD_GLOBAL: opcode = 116; if (((116) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 116:
            w = (((PyTupleObject *)((PyTupleObject *)(names)))->ob_item[(oparg)]);
            if (((((PyObject*)(f->f_globals))->ob_type) == &PyDict_Type)
                && ((((PyObject*)(f->f_builtins))->ob_type) == &PyDict_Type)) {
                x = _PyDict_LoadGlobal((PyDictObject *)f->f_globals,
                                       (PyDictObject *)f->f_builtins,
                                       w);
                if (x == ((void *)0)) {
                    if (!PyErr_Occurred())
                        format_exc_check_arg(PyExc_NameError,
                                             "global name '%.200s' is not defined", w);
                    break;
                }
                ( ((PyObject*)(x))->ob_refcnt++);
            }
            else {

                x = PyObject_GetItem(f->f_globals, w);
                if (x == ((void *)0)) {
                    x = PyObject_GetItem(f->f_builtins, w);
                    if (x == ((void *)0)) {
                        if (PyErr_ExceptionMatches(PyExc_KeyError))
                            format_exc_check_arg(
                                        PyExc_NameError,
                                        "global name '%.200s' is not defined", w);
                        break;
                    }
                }
            }
            (*stack_pointer++ = (x));
            { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };

        TARGET_DELETE_FAST: opcode = 126; if (((126) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 126:
            x = (fastlocals[oparg]);
            if (x != ((void *)0)) {
                do { PyObject *tmp = (fastlocals[oparg]); (fastlocals[oparg]) = ((void *)0); do { if ((tmp) == ((void *)0)) ; else do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0); } while (0); } while (0);
                { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            }
            format_exc_check_arg(
                PyExc_UnboundLocalError,
                "local variable '%.200s' referenced before assignment",
                PyTuple_GetItem(co->co_varnames, oparg)
                );
            break;

        TARGET_DELETE_DEREF: opcode = 138; if (((138) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 138:
            x = freevars[oparg];
            if ((((PyCellObject *)(x))->ob_ref) != ((void *)0)) {
                PyCell_Set(x, ((void *)0));
                { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            }
            err = -1;
            format_exc_unbound(co, oparg);
            break;

        TARGET_LOAD_CLOSURE: opcode = 135; if (((135) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 135:
            x = freevars[oparg];
            ( ((PyObject*)(x))->ob_refcnt++);
            (*stack_pointer++ = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_LOAD_DEREF: opcode = 136; if (((136) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 136:
            x = freevars[oparg];
            w = PyCell_Get(x);
            if (w != ((void *)0)) {
                (*stack_pointer++ = (w));
                { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            }
            err = -1;
            format_exc_unbound(co, oparg);
            break;

        TARGET_STORE_DEREF: opcode = 137; if (((137) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 137:
            w = (*--stack_pointer);
            x = freevars[oparg];
            PyCell_Set(x, w);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };

        TARGET_BUILD_TUPLE: opcode = 102; if (((102) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 102:
            x = PyTuple_New(oparg);
            if (x != ((void *)0)) {
                for (; --oparg >= 0;) {
                    w = (*--stack_pointer);
                    (((PyTupleObject *)(x))->ob_item[oparg] = w);
                }
                (*stack_pointer++ = (x));
                { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            }
            break;

        TARGET_BUILD_LIST: opcode = 103; if (((103) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 103:
            x = PyList_New(oparg);
            if (x != ((void *)0)) {
                for (; --oparg >= 0;) {
                    w = (*--stack_pointer);
                    (((PyListObject *)(x))->ob_item[oparg] = (w));
                }
                (*stack_pointer++ = (x));
                { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            }
            break;

        TARGET_BUILD_SET: opcode = 104; if (((104) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 104:
            x = PySet_New(((void *)0));
            if (x != ((void *)0)) {
                for (; --oparg >= 0;) {
                    w = (*--stack_pointer);
                    if (err == 0)
                        err = PySet_Add(x, w);
                    do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
                }
                if (err != 0) {
                    do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);
                    break;
                }
                (*stack_pointer++ = (x));
                { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            }
            break;

        TARGET_BUILD_MAP: opcode = 105; if (((105) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 105:
            x = _PyDict_NewPresized((Py_ssize_t)oparg);
            (*stack_pointer++ = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_STORE_MAP: opcode = 54; if (((54) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 54:
            w = (stack_pointer[-1]);
            u = (stack_pointer[-2]);
            v = (stack_pointer[-3]);
            (stack_pointer += -2);
            (__builtin_expect(!(((((PyObject*)(v))->ob_type) == &PyDict_Type)), 0) ? __assert_rtn(__func__, "ceval.c", 2255, "PyDict_CheckExact(v)") : (void)0);
            err = PyDict_SetItem(v, w, u);
            do { if ( --((PyObject*)(u))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(u)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(u)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            if (err == 0) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_MAP_ADD: opcode = 147; if (((147) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 147:
            w = (stack_pointer[-1]);
            u = (stack_pointer[-2]);
            (stack_pointer += -2);
            v = stack_pointer[-oparg];
            (__builtin_expect(!(((((PyObject*)(v))->ob_type) == &PyDict_Type)), 0) ? __assert_rtn(__func__, "ceval.c", 2267, "PyDict_CheckExact(v)") : (void)0);
            err = PyDict_SetItem(v, w, u);
            do { if ( --((PyObject*)(u))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(u)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(u)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            if (err == 0) {
                if (0) goto PRED_JUMP_ABSOLUTE;
                { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            }
            break;

        TARGET_LOAD_ATTR: opcode = 106; if (((106) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 106:
            w = (((PyTupleObject *)((PyTupleObject *)(names)))->ob_item[(oparg)]);
            v = (stack_pointer[-1]);
            x = PyObject_GetAttr(v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_COMPARE_OP: opcode = 107; if (((107) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 107:
            w = (*--stack_pointer);
            v = (stack_pointer[-1]);
            x = cmp_outcome(oparg, v, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x == ((void *)0)) break;
            if (0) goto PRED_POP_JUMP_IF_FALSE;
            if (0) goto PRED_POP_JUMP_IF_TRUE;
            { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };

        TARGET_IMPORT_NAME: opcode = 108; if (((108) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 108:
        {
            static _Py_Identifier PyId___import__ = { 0, "__import__", 0 };
            w = (((PyTupleObject *)((PyTupleObject *)(names)))->ob_item[(oparg)]);
            x = _PyDict_GetItemId(f->f_builtins, &PyId___import__);
            if (x == ((void *)0)) {
                PyErr_SetString(PyExc_ImportError,
                                "__import__ not found");
                break;
            }
            ( ((PyObject*)(x))->ob_refcnt++);
            v = (*--stack_pointer);
            u = (stack_pointer[-1]);
            if (PyLong_AsLong(u) != -1 || PyErr_Occurred())
                w = PyTuple_Pack(5,
                            w,
                            f->f_globals,
                            f->f_locals == ((void *)0) ?
                                  (&_Py_NoneStruct) : f->f_locals,
                            v,
                            u);
            else
                w = PyTuple_Pack(4,
                            w,
                            f->f_globals,
                            f->f_locals == ((void *)0) ?
                                  (&_Py_NoneStruct) : f->f_locals,
                            v);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(u))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(u)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(u)))); } while (0);
            if (w == ((void *)0)) {
                u = (*--stack_pointer);
                do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);
                x = ((void *)0);
                break;
            }
            ;
            v = x;
            x = PyEval_CallObjectWithKeywords(v, w, (PyObject *)((void *)0));
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            ;
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;
        }

        TARGET_IMPORT_STAR: opcode = 84; if (((84) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 84:
            v = (*--stack_pointer);
            PyFrame_FastToLocals(f);
            if ((x = f->f_locals) == ((void *)0)) {
                PyErr_SetString(PyExc_SystemError,
                    "no locals found during 'import *'");
                break;
            }
            ;
            err = import_all_from(x, v);
            ;
            PyFrame_LocalsToFast(f, 0);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            if (err == 0) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_IMPORT_FROM: opcode = 109; if (((109) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 109:
            w = (((PyTupleObject *)((PyTupleObject *)(names)))->ob_item[(oparg)]);
            v = (stack_pointer[-1]);
            ;
            x = import_from(v, w);
            ;
            (*stack_pointer++ = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_JUMP_FORWARD: opcode = 110; if (((110) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 110:
            (next_instr += (oparg));
            { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; };

        PRED_POP_JUMP_IF_FALSE:;
        TARGET_POP_JUMP_IF_FALSE: opcode = 114; if (((114) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 114:
            w = (*--stack_pointer);
            if (w == ((PyObject *) &_Py_TrueStruct)) {
                do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
                { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; };
            }
            if (w == ((PyObject *) &_Py_FalseStruct)) {
                do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
                (next_instr = first_instr + (oparg));
                { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; };
            }
            err = PyObject_IsTrue(w);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            if (err > 0)
                err = 0;
            else if (err == 0)
                (next_instr = first_instr + (oparg));
            else
                break;
            { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };

        PRED_POP_JUMP_IF_TRUE:;
        TARGET_POP_JUMP_IF_TRUE: opcode = 115; if (((115) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 115:
            w = (*--stack_pointer);
            if (w == ((PyObject *) &_Py_FalseStruct)) {
                do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
                { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; };
            }
            if (w == ((PyObject *) &_Py_TrueStruct)) {
                do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
                (next_instr = first_instr + (oparg));
                { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; };
            }
            err = PyObject_IsTrue(w);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            if (err > 0) {
                err = 0;
                (next_instr = first_instr + (oparg));
            }
            else if (err == 0)
                ;
            else
                break;
            { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };

        TARGET_JUMP_IF_FALSE_OR_POP: opcode = 111; if (((111) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 111:
            w = (stack_pointer[-1]);
            if (w == ((PyObject *) &_Py_TrueStruct)) {
                (stack_pointer += -1);
                do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
                { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; };
            }
            if (w == ((PyObject *) &_Py_FalseStruct)) {
                (next_instr = first_instr + (oparg));
                { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; };
            }
            err = PyObject_IsTrue(w);
            if (err > 0) {
                (stack_pointer += -1);
                do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
                err = 0;
            }
            else if (err == 0)
                (next_instr = first_instr + (oparg));
            else
                break;
            { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };

        TARGET_JUMP_IF_TRUE_OR_POP: opcode = 112; if (((112) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 112:
            w = (stack_pointer[-1]);
            if (w == ((PyObject *) &_Py_FalseStruct)) {
                (stack_pointer += -1);
                do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
                { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; };
            }
            if (w == ((PyObject *) &_Py_TrueStruct)) {
                (next_instr = first_instr + (oparg));
                { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; };
            }
            err = PyObject_IsTrue(w);
            if (err > 0) {
                err = 0;
                (next_instr = first_instr + (oparg));
            }
            else if (err == 0) {
                (stack_pointer += -1);
                do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            }
            else
                break;
            { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };

        PRED_JUMP_ABSOLUTE:;
        TARGET_JUMP_ABSOLUTE: opcode = 113; if (((113) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 113:
            (next_instr = first_instr + (oparg));
# 2481 "ceval.c"
            { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };


        TARGET_GET_ITER: opcode = 68; if (((68) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 68:

            v = (stack_pointer[-1]);
            x = PyObject_GetIter(v);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            if (x != ((void *)0)) {
                (stack_pointer[-1] = (x));
                if (0) goto PRED_FOR_ITER;
                { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            }
            (stack_pointer += -1);
            break;

        PRED_FOR_ITER:;
        TARGET_FOR_ITER: opcode = 93; if (((93) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 93:

            v = (stack_pointer[-1]);
            x = (*v->ob_type->tp_iternext)(v);
            if (x != ((void *)0)) {
                (*stack_pointer++ = (x));
                if (0) goto PRED_STORE_FAST;
                if (0) goto PRED_UNPACK_SEQUENCE;
                { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            }
            if (PyErr_Occurred()) {
                if (!PyErr_ExceptionMatches(
                                PyExc_StopIteration))
                    break;
                PyErr_Clear();
            }

            x = v = (*--stack_pointer);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            (next_instr += (oparg));
            { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };

        TARGET_BREAK_LOOP: opcode = 80; if (((80) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 80:
            why = WHY_BREAK;
            goto fast_block_end;

        TARGET_CONTINUE_LOOP: opcode = 119; if (((119) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 119:
            retval = PyLong_FromLong(oparg);
            if (!retval) {
                x = ((void *)0);
                break;
            }
            why = WHY_CONTINUE;
            goto fast_block_end;

        TARGET_SETUP_LOOP: opcode = 120; if (((120) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 120: goto _setup_finally;
        TARGET_SETUP_EXCEPT: opcode = 121; if (((121) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 121: goto _setup_finally;
        TARGET_SETUP_FINALLY: opcode = 122; if (((122) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 122:
        _setup_finally:





            PyFrame_BlockSetup(f, opcode, ((int)(next_instr - first_instr)) + oparg,
                               ((int)(stack_pointer - f->f_valuestack)));
            { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };

        TARGET_SETUP_WITH: opcode = 143; if (((143) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 143:
        {
            static _Py_Identifier PyId___exit__ = { 0, "__exit__", 0 };
            static _Py_Identifier PyId___enter__ = { 0, "__enter__", 0 };
            w = (stack_pointer[-1]);
            x = special_lookup(w, &PyId___exit__);
            if (!x)
                break;
            (stack_pointer[-1] = (x));
            u = special_lookup(w, &PyId___enter__);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            if (!u) {
                x = ((void *)0);
                break;
            }
            x = PyObject_CallFunctionObjArgs(u, ((void *)0));
            do { if ( --((PyObject*)(u))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(u)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(u)))); } while (0);
            if (!x)
                break;


            PyFrame_BlockSetup(f, 122, ((int)(next_instr - first_instr)) + oparg,
                               ((int)(stack_pointer - f->f_valuestack)));

            (*stack_pointer++ = (x));
            { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
        }

        TARGET_WITH_CLEANUP: opcode = 81; if (((81) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 81:
        {
# 2601 "ceval.c"
            PyObject *exit_func;
            u = (stack_pointer[-1]);
            if (u == (&_Py_NoneStruct)) {
                (void)(*--stack_pointer);
                exit_func = (stack_pointer[-1]);
                (stack_pointer[-1] = (u));
                v = w = (&_Py_NoneStruct);
            }
            else if (((((((PyObject*)(u))->ob_type))->tp_flags & ((1L<<24))) != 0)) {
                (void)(*--stack_pointer);
                switch(PyLong_AsLong(u)) {
                case WHY_RETURN:
                case WHY_CONTINUE:

                    exit_func = (stack_pointer[-2]);
                    (stack_pointer[-2] = ((stack_pointer[-1])));
                    (stack_pointer[-1] = (u));
                    break;
                default:
                    exit_func = (stack_pointer[-1]);
                    (stack_pointer[-1] = (u));
                    break;
                }
                u = v = w = (&_Py_NoneStruct);
            }
            else {
                PyObject *tp, *exc, *tb;
                PyTryBlock *block;
                v = (stack_pointer[-2]);
                w = (stack_pointer[-3]);
                tp = (stack_pointer[-4]);
                exc = (stack_pointer[-(5)]);
                tb = (stack_pointer[-(6)]);
                exit_func = (stack_pointer[-(7)]);
                (stack_pointer[-(7)] = (tb));
                (stack_pointer[-(6)] = (exc));
                (stack_pointer[-(5)] = (tp));

                (stack_pointer[-4] = (((void *)0)));



                block = &f->f_blockstack[f->f_iblock - 1];
                (__builtin_expect(!(block->b_type == 257), 0) ? __assert_rtn(__func__, "ceval.c", 2644, "block->b_type == EXCEPT_HANDLER") : (void)0);
                block->b_level--;
            }

            x = PyObject_CallFunctionObjArgs(exit_func, u, v, w,
                                             ((void *)0));
            do { if ( --((PyObject*)(exit_func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(exit_func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(exit_func)))); } while (0);
            if (x == ((void *)0))
                break;

            if (u != (&_Py_NoneStruct))
                err = PyObject_IsTrue(x);
            else
                err = 0;
            do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);

            if (err < 0)
                break;
            else if (err > 0) {
                err = 0;

                (*stack_pointer++ = (PyLong_FromLong((long) WHY_SILENCED)));
            }
            if (0) goto PRED_END_FINALLY;
            break;
        }

        TARGET_CALL_FUNCTION: opcode = 131; if (((131) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 131:
        {
            PyObject **sp;
            ;
            sp = stack_pointer;



            x = call_function(&sp, oparg);

            stack_pointer = sp;
            (*stack_pointer++ = (x));
            if (x != ((void *)0))
                { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;
        }

        TARGET_CALL_FUNCTION_VAR: opcode = 140; if (((140) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 140: goto _call_function_var_kw;
        TARGET_CALL_FUNCTION_KW: opcode = 141; if (((141) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 141: goto _call_function_var_kw;
        TARGET_CALL_FUNCTION_VAR_KW: opcode = 142; if (((142) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 142:
        _call_function_var_kw:
        {
            int na = oparg & 0xff;
            int nk = (oparg>>8) & 0xff;
            int flags = (opcode - 131) & 3;
            int n = na + 2 * nk;
            PyObject **pfunc, *func, **sp;
            ;
            if (flags & 1)
                n++;
            if (flags & 2)
                n++;
            pfunc = stack_pointer - n - 1;
            func = *pfunc;

            if (((func)->ob_type == &PyMethod_Type)
                && (((PyMethodObject *)func) -> im_self) != ((void *)0)) {
                PyObject *self = (((PyMethodObject *)func) -> im_self);
                ( ((PyObject*)(self))->ob_refcnt++);
                func = (((PyMethodObject *)func) -> im_func);
                ( ((PyObject*)(func))->ob_refcnt++);
                do { if ( --((PyObject*)(*pfunc))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(*pfunc)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(*pfunc)))); } while (0);
                *pfunc = self;
                na++;

            } else
                ( ((PyObject*)(func))->ob_refcnt++);
            sp = stack_pointer;
            ;
            x = ext_do_call(func, &sp, flags, na, nk);
            ;
            stack_pointer = sp;
            do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0);

            while (stack_pointer > pfunc) {
                w = (*--stack_pointer);
                do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            }
            (*stack_pointer++ = (x));
            if (x != ((void *)0))
                { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;
        }

        TARGET_MAKE_CLOSURE: opcode = 134; if (((134) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 134: goto _make_function;
        TARGET_MAKE_FUNCTION: opcode = 132; if (((132) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 132:
        _make_function:
        {
            int posdefaults = oparg & 0xff;
            int kwdefaults = (oparg>>8) & 0xff;
            int num_annotations = (oparg >> 16) & 0x7fff;

            w = (*--stack_pointer);
            v = (*--stack_pointer);
            x = PyFunction_NewWithQualName(v, f->f_globals, w);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);

            if (x != ((void *)0) && opcode == 134) {
                v = (*--stack_pointer);
                if (PyFunction_SetClosure(x, v) != 0) {

                    why = WHY_EXCEPTION;
                }
                do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            }

            if (x != ((void *)0) && num_annotations > 0) {
                Py_ssize_t name_ix;
                u = (*--stack_pointer);
                v = PyDict_New();
                if (v == ((void *)0)) {
                    do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);
                    x = ((void *)0);
                    break;
                }
                name_ix = PyTuple_Size(u);
                (__builtin_expect(!(num_annotations == name_ix+1), 0) ? __assert_rtn(__func__, "ceval.c", 2768, "num_annotations == name_ix+1") : (void)0);
                while (name_ix > 0) {
                    --name_ix;
                    t = (((PyTupleObject *)(u))->ob_item[name_ix]);
                    w = (*--stack_pointer);

                    PyDict_SetItem(v, t, w);
                    do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
                }

                if (PyFunction_SetAnnotations(x, v) != 0) {


                    why = WHY_EXCEPTION;
                }
                do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
                do { if ( --((PyObject*)(u))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(u)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(u)))); } while (0);
            }


            if (x != ((void *)0) && posdefaults > 0) {
                v = PyTuple_New(posdefaults);
                if (v == ((void *)0)) {
                    do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);
                    x = ((void *)0);
                    break;
                }
                while (--posdefaults >= 0) {
                    w = (*--stack_pointer);
                    (((PyTupleObject *)(v))->ob_item[posdefaults] = w);
                }
                if (PyFunction_SetDefaults(x, v) != 0) {


                    why = WHY_EXCEPTION;
                }
                do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            }
            if (x != ((void *)0) && kwdefaults > 0) {
                v = PyDict_New();
                if (v == ((void *)0)) {
                    do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0);
                    x = ((void *)0);
                    break;
                }
                while (--kwdefaults >= 0) {
                    w = (*--stack_pointer);
                    u = (*--stack_pointer);

                    PyDict_SetItem(v, u, w);
                    do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
                    do { if ( --((PyObject*)(u))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(u)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(u)))); } while (0);
                }
                if (PyFunction_SetKwDefaults(x, v) != 0) {


                    why = WHY_EXCEPTION;
                }
                do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            }
            (*stack_pointer++ = (x));
            break;
        }

        TARGET_BUILD_SLICE: opcode = 133; if (((133) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 133:
            if (oparg == 3)
                w = (*--stack_pointer);
            else
                w = ((void *)0);
            v = (*--stack_pointer);
            u = (stack_pointer[-1]);
            x = PySlice_New(u, v, w);
            do { if ( --((PyObject*)(u))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(u)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(u)))); } while (0);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ((w) == ((void *)0)) ; else do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0); } while (0);
            (stack_pointer[-1] = (x));
            if (x != ((void *)0)) { if (!__extension__ ({ __typeof__(&eval_breaker) atomic_val = &eval_breaker; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })) { { if (!_Py_TracingPossible) { f->f_lasti = ((int)(next_instr - first_instr)); goto *opcode_targets[*next_instr++]; } goto fast_next_opcode; }; } continue; };
            break;

        TARGET_EXTENDED_ARG: opcode = 144; if (((144) >= 90)) oparg = (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]); case 144:
            opcode = (*next_instr++);
            oparg = oparg<<16 | (next_instr += 2, (next_instr[-1]<<8) + next_instr[-2]);
            goto dispatch_opcode;


        _unknown_opcode:

        default:
            fprintf(__stderrp,
                "XXX lineno: %d, opcode: %d\n",
                PyFrame_GetLineNumber(f),
                opcode);
            PyErr_SetString(PyExc_SystemError, "unknown opcode");
            why = WHY_EXCEPTION;
            break;





        }

        on_error:

        ;



        if (why == WHY_NOT) {
            if (err == 0 && x != ((void *)0)) {







                    ;
                    continue;



            }
            why = WHY_EXCEPTION;
            x = (&_Py_NoneStruct);
            err = 0;
        }



        if (why == WHY_EXCEPTION || why == WHY_RERAISE) {
            if (!PyErr_Occurred()) {
                PyErr_SetString(PyExc_SystemError,
                    "error return without exception set");
                why = WHY_EXCEPTION;
            }
        }
# 2919 "ceval.c"
        if (why == WHY_EXCEPTION) {
            PyTraceBack_Here(f);

            if (tstate->c_tracefunc != ((void *)0))
                call_exc_trace(tstate->c_tracefunc,
                               tstate->c_traceobj, f);
        }



        if (why == WHY_RERAISE)
            why = WHY_EXCEPTION;



fast_block_end:
        while (why != WHY_NOT && f->f_iblock > 0) {

            PyTryBlock *b = &f->f_blockstack[f->f_iblock - 1];

            (__builtin_expect(!(why != WHY_YIELD), 0) ? __assert_rtn(__func__, "ceval.c", 2939, "why != WHY_YIELD") : (void)0);
            if (b->b_type == 120 && why == WHY_CONTINUE) {
                why = WHY_NOT;
                (next_instr = first_instr + (PyLong_AsLong(retval)));
                do { if ( --((PyObject*)(retval))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(retval)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(retval)))); } while (0);
                break;
            }

            f->f_iblock--;

            if (b->b_type == 257) {
                { PyObject *type, *value, *traceback; (__builtin_expect(!(((int)(stack_pointer - f->f_valuestack)) >= (b)->b_level + 3), 0) ? __assert_rtn(__func__, "ceval.c", 2950, "STACK_LEVEL() >= (b)->b_level + 3") : (void)0); while (((int)(stack_pointer - f->f_valuestack)) > (b)->b_level + 3) { value = (*--stack_pointer); do { if ((value) == ((void *)0)) ; else do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); } while (0); } type = tstate->exc_type; value = tstate->exc_value; traceback = tstate->exc_traceback; tstate->exc_type = (*--stack_pointer); tstate->exc_value = (*--stack_pointer); tstate->exc_traceback = (*--stack_pointer); do { if ((type) == ((void *)0)) ; else do { if ( --((PyObject*)(type))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type)))); } while (0); } while (0); do { if ((value) == ((void *)0)) ; else do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); } while (0); do { if ((traceback) == ((void *)0)) ; else do { if ( --((PyObject*)(traceback))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(traceback)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(traceback)))); } while (0); } while (0); };
                continue;
            }
            while (((int)(stack_pointer - f->f_valuestack)) > (b)->b_level) { PyObject *v = (*--stack_pointer); do { if ((v) == ((void *)0)) ; else do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0); } while (0); };
            if (b->b_type == 120 && why == WHY_BREAK) {
                why = WHY_NOT;
                (next_instr = first_instr + (b->b_handler));
                break;
            }
            if (why == WHY_EXCEPTION && (b->b_type == 121
                || b->b_type == 122)) {
                PyObject *exc, *val, *tb;
                int handler = b->b_handler;

                PyFrame_BlockSetup(f, 257, -1, ((int)(stack_pointer - f->f_valuestack)));
                (*stack_pointer++ = (tstate->exc_traceback));
                (*stack_pointer++ = (tstate->exc_value));
                if (tstate->exc_type != ((void *)0)) {
                    (*stack_pointer++ = (tstate->exc_type));
                }
                else {
                    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
                    (*stack_pointer++ = ((&_Py_NoneStruct)));
                }
                PyErr_Fetch(&exc, &val, &tb);




                PyErr_NormalizeException(
                    &exc, &val, &tb);
                PyException_SetTraceback(val, tb);
                ( ((PyObject*)(exc))->ob_refcnt++);
                tstate->exc_type = exc;
                ( ((PyObject*)(val))->ob_refcnt++);
                tstate->exc_value = val;
                tstate->exc_traceback = tb;
                if (tb == ((void *)0))
                    tb = (&_Py_NoneStruct);
                ( ((PyObject*)(tb))->ob_refcnt++);
                (*stack_pointer++ = (tb));
                (*stack_pointer++ = (val));
                (*stack_pointer++ = (exc));
                why = WHY_NOT;
                (next_instr = first_instr + (handler));
                break;
            }
            if (b->b_type == 122) {
                if (why & (WHY_RETURN | WHY_CONTINUE))
                    (*stack_pointer++ = (retval));
                (*stack_pointer++ = (PyLong_FromLong((long)why)));
                why = WHY_NOT;
                (next_instr = first_instr + (b->b_handler));
                break;
            }
        }



        if (why != WHY_NOT)
            break;
        ;

    }

    (__builtin_expect(!(why != WHY_YIELD), 0) ? __assert_rtn(__func__, "ceval.c", 3015, "why != WHY_YIELD") : (void)0);

    while (!(((int)(stack_pointer - f->f_valuestack)) == 0)) {
        v = (*--stack_pointer);
        do { if ((v) == ((void *)0)) ; else do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0); } while (0);
    }

    if (why != WHY_RETURN)
        retval = ((void *)0);

fast_yield:
    if (co->co_flags & 0x0020 && (why == WHY_YIELD || why == WHY_RETURN)) {
# 3035 "ceval.c"
        int i;
        for (i = 0; i < f->f_iblock; i++)
            if (f->f_blockstack[i].b_type == 257)
                break;
        if (i == f->f_iblock)

            restore_and_clear_exc_state(tstate, f);
        else
            swap_exc_state(tstate, f);
    }

    if (tstate->use_tracing) {
        if (tstate->c_tracefunc) {
            if (why == WHY_RETURN || why == WHY_YIELD) {
                if (call_trace(tstate->c_tracefunc,
                               tstate->c_traceobj, f,
                               3, retval)) {
                    do { if ((retval) == ((void *)0)) ; else do { if ( --((PyObject*)(retval))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(retval)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(retval)))); } while (0); } while (0);
                    retval = ((void *)0);
                    why = WHY_EXCEPTION;
                }
            }
            else if (why == WHY_EXCEPTION) {
                call_trace_protected(tstate->c_tracefunc,
                                     tstate->c_traceobj, f,
                                     3, ((void *)0));
            }
        }
        if (tstate->c_profilefunc) {
            if (why == WHY_EXCEPTION)
                call_trace_protected(tstate->c_profilefunc,
                                     tstate->c_profileobj, f,
                                     3, ((void *)0));
            else if (call_trace(tstate->c_profilefunc,
                                tstate->c_profileobj, f,
                                3, retval)) {
                do { if ((retval) == ((void *)0)) ; else do { if ( --((PyObject*)(retval))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(retval)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(retval)))); } while (0); } while (0);
                retval = ((void *)0);

            }
        }
    }


exit_eval_frame:
    do{ if((--(((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->recursion_depth) < ((_Py_CheckRecursionLimit > 100) ? (_Py_CheckRecursionLimit - 50) : (3 * (_Py_CheckRecursionLimit >> 2))))) ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->overflowed = 0; } while(0);
    tstate->frame = f->f_back;

    return retval;
}

static void
format_missing(const char *kind, PyCodeObject *co, PyObject *names)
{
    int err;
    Py_ssize_t len = (((PyVarObject*)(names))->ob_size);
    PyObject *name_str, *comma, *tail, *tmp;

    (__builtin_expect(!(((((PyObject*)(names))->ob_type) == &PyList_Type)), 0) ? __assert_rtn(__func__, "ceval.c", 3093, "PyList_CheckExact(names)") : (void)0);
    (__builtin_expect(!(len >= 1), 0) ? __assert_rtn(__func__, "ceval.c", 3094, "len >= 1") : (void)0);

    switch (len) {
    case 1:
        name_str = (((PyListObject *)(names))->ob_item[0]);
        ( ((PyObject*)(name_str))->ob_refcnt++);
        break;
    case 2:
        name_str = PyUnicode_FromFormat("%U and %U",
                                        (((PyListObject *)(names))->ob_item[len - 2]),
                                        (((PyListObject *)(names))->ob_item[len - 1]));
        break;
    default:
        tail = PyUnicode_FromFormat(", %U, and %U",
                                    (((PyListObject *)(names))->ob_item[len - 2]),
                                    (((PyListObject *)(names))->ob_item[len - 1]));
        if (tail == ((void *)0))
            return;


        err = PyList_SetSlice(names, len - 2, len, ((void *)0));
        if (err == -1) {
            do { if ( --((PyObject*)(tail))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tail)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tail)))); } while (0);
            return;
        }

        comma = PyUnicode_FromString(", ");
        if (comma == ((void *)0)) {
            do { if ( --((PyObject*)(tail))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tail)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tail)))); } while (0);
            return;
        }
        tmp = PyUnicode_Join(comma, names);
        do { if ( --((PyObject*)(comma))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(comma)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(comma)))); } while (0);
        if (tmp == ((void *)0)) {
            do { if ( --((PyObject*)(tail))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tail)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tail)))); } while (0);
            return;
        }
        name_str = PyUnicode_Concat(tmp, tail);
        do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0);
        do { if ( --((PyObject*)(tail))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tail)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tail)))); } while (0);
        break;
    }
    if (name_str == ((void *)0))
        return;
    PyErr_Format(PyExc_TypeError,
                 "%U() missing %i required %s argument%s: %U",
                 co->co_name,
                 len,
                 kind,
                 len == 1 ? "" : "s",
                 name_str);
    do { if ( --((PyObject*)(name_str))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(name_str)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(name_str)))); } while (0);
}

static void
missing_arguments(PyCodeObject *co, int missing, int defcount,
                  PyObject **fastlocals)
{
    int i, j = 0;
    int start, end;
    int positional = defcount != -1;
    const char *kind = positional ? "positional" : "keyword-only";
    PyObject *missing_names;


    missing_names = PyList_New(missing);
    if (missing_names == ((void *)0))
        return;
    if (positional) {
        start = 0;
        end = co->co_argcount - defcount;
    }
    else {
        start = co->co_argcount;
        end = start + co->co_kwonlyargcount;
    }
    for (i = start; i < end; i++) {
        if ((fastlocals[i]) == ((void *)0)) {
            PyObject *raw = (((PyTupleObject *)(co->co_varnames))->ob_item[i]);
            PyObject *name = PyObject_Repr(raw);
            if (name == ((void *)0)) {
                do { if ( --((PyObject*)(missing_names))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(missing_names)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(missing_names)))); } while (0);
                return;
            }
            (((PyListObject *)(missing_names))->ob_item[j++] = (name));
        }
    }
    (__builtin_expect(!(j == missing), 0) ? __assert_rtn(__func__, "ceval.c", 3181, "j == missing") : (void)0);
    format_missing(kind, co, missing_names);
    do { if ( --((PyObject*)(missing_names))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(missing_names)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(missing_names)))); } while (0);
}

static void
too_many_positional(PyCodeObject *co, int given, int defcount, PyObject **fastlocals)
{
    int plural;
    int kwonly_given = 0;
    int i;
    PyObject *sig, *kwonly_sig;

    (__builtin_expect(!((co->co_flags & 0x0004) == 0), 0) ? __assert_rtn(__func__, "ceval.c", 3194, "(co->co_flags & CO_VARARGS) == 0") : (void)0);

    for (i = co->co_argcount; i < co->co_argcount + co->co_kwonlyargcount; i++)
        if ((fastlocals[i]) != ((void *)0))
            kwonly_given++;
    if (defcount) {
        int atleast = co->co_argcount - defcount;
        plural = 1;
        sig = PyUnicode_FromFormat("from %d to %d", atleast, co->co_argcount);
    }
    else {
        plural = co->co_argcount != 1;
        sig = PyUnicode_FromFormat("%d", co->co_argcount);
    }
    if (sig == ((void *)0))
        return;
    if (kwonly_given) {
        const char *format = " positional argument%s (and %d keyword-only argument%s)";
        kwonly_sig = PyUnicode_FromFormat(format, given != 1 ? "s" : "", kwonly_given,
                                              kwonly_given != 1 ? "s" : "");
        if (kwonly_sig == ((void *)0)) {
            do { if ( --((PyObject*)(sig))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sig)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sig)))); } while (0);
            return;
        }
    }
    else {

        kwonly_sig = PyUnicode_FromString("");
        (__builtin_expect(!(kwonly_sig != ((void *)0)), 0) ? __assert_rtn(__func__, "ceval.c", 3222, "kwonly_sig != NULL") : (void)0);
    }
    PyErr_Format(PyExc_TypeError,
                 "%U() takes %U positional argument%s but %d%U %s given",
                 co->co_name,
                 sig,
                 plural ? "s" : "",
                 given,
                 kwonly_sig,
                 given == 1 && !kwonly_given ? "was" : "were");
    do { if ( --((PyObject*)(sig))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sig)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sig)))); } while (0);
    do { if ( --((PyObject*)(kwonly_sig))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(kwonly_sig)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(kwonly_sig)))); } while (0);
}





PyObject *
PyEval_EvalCodeEx(PyObject *_co, PyObject *globals, PyObject *locals,
           PyObject **args, int argcount, PyObject **kws, int kwcount,
           PyObject **defs, int defcount, PyObject *kwdefs, PyObject *closure)
{
    PyCodeObject* co = (PyCodeObject*)_co;
    register PyFrameObject *f;
    register PyObject *retval = ((void *)0);
    register PyObject **fastlocals, **freevars;
    PyThreadState *tstate = ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }));
    PyObject *x, *u;
    int total_args = co->co_argcount + co->co_kwonlyargcount;
    int i;
    int n = argcount;
    PyObject *kwdict = ((void *)0);

    if (globals == ((void *)0)) {
        PyErr_SetString(PyExc_SystemError,
                        "PyEval_EvalCodeEx: NULL globals");
        return ((void *)0);
    }

    (__builtin_expect(!(tstate != ((void *)0)), 0) ? __assert_rtn(__func__, "ceval.c", 3262, "tstate != NULL") : (void)0);
    (__builtin_expect(!(globals != ((void *)0)), 0) ? __assert_rtn(__func__, "ceval.c", 3263, "globals != NULL") : (void)0);
    f = PyFrame_New(tstate, co, globals, locals);
    if (f == ((void *)0))
        return ((void *)0);

    fastlocals = f->f_localsplus;
    freevars = f->f_localsplus + co->co_nlocals;


    if (co->co_flags & 0x0008) {
        kwdict = PyDict_New();
        if (kwdict == ((void *)0))
            goto fail;
        i = total_args;
        if (co->co_flags & 0x0004)
            i++;
        do { PyObject *tmp = (fastlocals[i]); (fastlocals[i]) = kwdict; do { if ((tmp) == ((void *)0)) ; else do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0); } while (0); } while (0);
    }
    if (argcount > co->co_argcount)
        n = co->co_argcount;
    for (i = 0; i < n; i++) {
        x = args[i];
        ( ((PyObject*)(x))->ob_refcnt++);
        do { PyObject *tmp = (fastlocals[i]); (fastlocals[i]) = x; do { if ((tmp) == ((void *)0)) ; else do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0); } while (0); } while (0);
    }
    if (co->co_flags & 0x0004) {
        u = PyTuple_New(argcount - n);
        if (u == ((void *)0))
            goto fail;
        do { PyObject *tmp = (fastlocals[total_args]); (fastlocals[total_args]) = u; do { if ((tmp) == ((void *)0)) ; else do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0); } while (0); } while (0);
        for (i = n; i < argcount; i++) {
            x = args[i];
            ( ((PyObject*)(x))->ob_refcnt++);
            (((PyTupleObject *)(u))->ob_item[i-n] = x);
        }
    }
    for (i = 0; i < kwcount; i++) {
        PyObject **co_varnames;
        PyObject *keyword = kws[2*i];
        PyObject *value = kws[2*i + 1];
        int j;
        if (keyword == ((void *)0) || !((((((PyObject*)(keyword))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
            PyErr_Format(PyExc_TypeError,
                         "%U() keywords must be strings",
                         co->co_name);
            goto fail;
        }


        co_varnames = ((PyTupleObject *)(co->co_varnames))->ob_item;
        for (j = 0; j < total_args; j++) {
            PyObject *nm = co_varnames[j];
            if (nm == keyword)
                goto kw_found;
        }

        for (j = 0; j < total_args; j++) {
            PyObject *nm = co_varnames[j];
            int cmp = PyObject_RichCompareBool(
                keyword, nm, 2);
            if (cmp > 0)
                goto kw_found;
            else if (cmp < 0)
                goto fail;
        }
        if (j >= total_args && kwdict == ((void *)0)) {
            PyErr_Format(PyExc_TypeError,
                         "%U() got an unexpected "
                         "keyword argument '%S'",
                         co->co_name,
                         keyword);
            goto fail;
        }
        PyDict_SetItem(kwdict, keyword, value);
        continue;
      kw_found:
        if ((fastlocals[j]) != ((void *)0)) {
            PyErr_Format(PyExc_TypeError,
                         "%U() got multiple "
                         "values for argument '%S'",
                         co->co_name,
                         keyword);
            goto fail;
        }
        ( ((PyObject*)(value))->ob_refcnt++);
        do { PyObject *tmp = (fastlocals[j]); (fastlocals[j]) = value; do { if ((tmp) == ((void *)0)) ; else do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0); } while (0); } while (0);
    }
    if (argcount > co->co_argcount && !(co->co_flags & 0x0004)) {
        too_many_positional(co, argcount, defcount, fastlocals);
        goto fail;
    }
    if (argcount < co->co_argcount) {
        int m = co->co_argcount - defcount;
        int missing = 0;
        for (i = argcount; i < m; i++)
            if ((fastlocals[i]) == ((void *)0))
                missing++;
        if (missing) {
            missing_arguments(co, missing, defcount, fastlocals);
            goto fail;
        }
        if (n > m)
            i = n - m;
        else
            i = 0;
        for (; i < defcount; i++) {
            if ((fastlocals[m+i]) == ((void *)0)) {
                PyObject *def = defs[i];
                ( ((PyObject*)(def))->ob_refcnt++);
                do { PyObject *tmp = (fastlocals[m+i]); (fastlocals[m+i]) = def; do { if ((tmp) == ((void *)0)) ; else do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0); } while (0); } while (0);
            }
        }
    }
    if (co->co_kwonlyargcount > 0) {
        int missing = 0;
        for (i = co->co_argcount; i < total_args; i++) {
            PyObject *name;
            if ((fastlocals[i]) != ((void *)0))
                continue;
            name = (((PyTupleObject *)(co->co_varnames))->ob_item[i]);
            if (kwdefs != ((void *)0)) {
                PyObject *def = PyDict_GetItem(kwdefs, name);
                if (def) {
                    ( ((PyObject*)(def))->ob_refcnt++);
                    do { PyObject *tmp = (fastlocals[i]); (fastlocals[i]) = def; do { if ((tmp) == ((void *)0)) ; else do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0); } while (0); } while (0);
                    continue;
                }
            }
            missing++;
        }
        if (missing) {
            missing_arguments(co, missing, -1, fastlocals);
            goto fail;
        }
    }



    for (i = 0; i < (((PyVarObject*)(co->co_cellvars))->ob_size); ++i) {
        PyObject *c;
        int arg;

        if (co->co_cell2arg != ((void *)0) &&
            (arg = co->co_cell2arg[i]) != 255)
            c = PyCell_New((fastlocals[arg]));
        else
            c = PyCell_New(((void *)0));
        if (c == ((void *)0))
            goto fail;
        do { PyObject *tmp = (fastlocals[co->co_nlocals + i]); (fastlocals[co->co_nlocals + i]) = c; do { if ((tmp) == ((void *)0)) ; else do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0); } while (0); } while (0);
    }
    for (i = 0; i < (((PyVarObject*)(co->co_freevars))->ob_size); ++i) {
        PyObject *o = (((PyTupleObject *)(closure))->ob_item[i]);
        ( ((PyObject*)(o))->ob_refcnt++);
        freevars[(((PyVarObject*)(co->co_cellvars))->ob_size) + i] = o;
    }

    if (co->co_flags & 0x0020) {


        do { if ((f->f_back) == ((void *)0)) ; else do { if ( --((PyObject*)(f->f_back))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(f->f_back)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(f->f_back)))); } while (0); } while (0);
        f->f_back = ((void *)0);

        ;



        return PyGen_New(f);
    }

    retval = PyEval_EvalFrameEx(f,0);

fail:






    (__builtin_expect(!(tstate != ((void *)0)), 0) ? __assert_rtn(__func__, "ceval.c", 3442, "tstate != NULL") : (void)0);
    ++tstate->recursion_depth;
    do { if ( --((PyObject*)(f))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(f)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(f)))); } while (0);
    --tstate->recursion_depth;
    return retval;
}


static PyObject *
special_lookup(PyObject *o, _Py_Identifier *id)
{
    PyObject *res;
    res = _PyObject_LookupSpecial(o, id);
    if (res == ((void *)0) && !PyErr_Occurred()) {
        PyErr_SetObject(PyExc_AttributeError, id->object);
        return ((void *)0);
    }
    return res;
}




static void
save_exc_state(PyThreadState *tstate, PyFrameObject *f)
{
    PyObject *type, *value, *traceback;
    do { if ((tstate->exc_type) == ((void *)0)) ; else ( ((PyObject*)(tstate->exc_type))->ob_refcnt++); } while (0);
    do { if ((tstate->exc_value) == ((void *)0)) ; else ( ((PyObject*)(tstate->exc_value))->ob_refcnt++); } while (0);
    do { if ((tstate->exc_traceback) == ((void *)0)) ; else ( ((PyObject*)(tstate->exc_traceback))->ob_refcnt++); } while (0);
    type = f->f_exc_type;
    value = f->f_exc_value;
    traceback = f->f_exc_traceback;
    f->f_exc_type = tstate->exc_type;
    f->f_exc_value = tstate->exc_value;
    f->f_exc_traceback = tstate->exc_traceback;
    do { if ((type) == ((void *)0)) ; else do { if ( --((PyObject*)(type))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type)))); } while (0); } while (0);
    do { if ((value) == ((void *)0)) ; else do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); } while (0);
    do { if ((traceback) == ((void *)0)) ; else do { if ( --((PyObject*)(traceback))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(traceback)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(traceback)))); } while (0); } while (0);
}

static void
swap_exc_state(PyThreadState *tstate, PyFrameObject *f)
{
    PyObject *tmp;
    tmp = tstate->exc_type;
    tstate->exc_type = f->f_exc_type;
    f->f_exc_type = tmp;
    tmp = tstate->exc_value;
    tstate->exc_value = f->f_exc_value;
    f->f_exc_value = tmp;
    tmp = tstate->exc_traceback;
    tstate->exc_traceback = f->f_exc_traceback;
    f->f_exc_traceback = tmp;
}

static void
restore_and_clear_exc_state(PyThreadState *tstate, PyFrameObject *f)
{
    PyObject *type, *value, *tb;
    type = tstate->exc_type;
    value = tstate->exc_value;
    tb = tstate->exc_traceback;
    tstate->exc_type = f->f_exc_type;
    tstate->exc_value = f->f_exc_value;
    tstate->exc_traceback = f->f_exc_traceback;
    f->f_exc_type = ((void *)0);
    f->f_exc_value = ((void *)0);
    f->f_exc_traceback = ((void *)0);
    do { if ((type) == ((void *)0)) ; else do { if ( --((PyObject*)(type))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type)))); } while (0); } while (0);
    do { if ((value) == ((void *)0)) ; else do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); } while (0);
    do { if ((tb) == ((void *)0)) ; else do { if ( --((PyObject*)(tb))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tb)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tb)))); } while (0); } while (0);
}




static enum why_code
do_raise(PyObject *exc, PyObject *cause)
{
    PyObject *type = ((void *)0), *value = ((void *)0);

    if (exc == ((void *)0)) {

        PyThreadState *tstate = ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }));
        PyObject *tb;
        type = tstate->exc_type;
        value = tstate->exc_value;
        tb = tstate->exc_traceback;
        if (type == (&_Py_NoneStruct)) {
            PyErr_SetString(PyExc_RuntimeError,
                            "No active exception to reraise");
            return WHY_EXCEPTION;
            }
        do { if ((type) == ((void *)0)) ; else ( ((PyObject*)(type))->ob_refcnt++); } while (0);
        do { if ((value) == ((void *)0)) ; else ( ((PyObject*)(value))->ob_refcnt++); } while (0);
        do { if ((tb) == ((void *)0)) ; else ( ((PyObject*)(tb))->ob_refcnt++); } while (0);
        PyErr_Restore(type, value, tb);
        return WHY_RERAISE;
    }






    if ((((((((PyObject*)((exc)))->ob_type))->tp_flags & ((1L<<31))) != 0) && ((((PyTypeObject*)(exc))->tp_flags & ((1L<<30))) != 0))) {
        type = exc;
        value = PyObject_CallObject(exc, ((void *)0));
        if (value == ((void *)0))
            goto raise_error;
        if (!((((value)->ob_type)->tp_flags & ((1L<<30))) != 0)) {
            PyErr_Format(PyExc_TypeError,
                         "calling %R should have returned an instance of "
                         "BaseException, not %R",
                         type, (((PyObject*)(value))->ob_type));
            goto raise_error;
        }
    }
    else if (((((exc)->ob_type)->tp_flags & ((1L<<30))) != 0)) {
        value = exc;
        type = ((PyObject*)((exc)->ob_type));
        ( ((PyObject*)(type))->ob_refcnt++);
    }
    else {


        do { if ( --((PyObject*)(exc))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(exc)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(exc)))); } while (0);
        PyErr_SetString(PyExc_TypeError,
                        "exceptions must derive from BaseException");
        goto raise_error;
    }

    if (cause) {
        PyObject *fixed_cause;
        if ((((((((PyObject*)((cause)))->ob_type))->tp_flags & ((1L<<31))) != 0) && ((((PyTypeObject*)(cause))->tp_flags & ((1L<<30))) != 0))) {
            fixed_cause = PyObject_CallObject(cause, ((void *)0));
            if (fixed_cause == ((void *)0))
                goto raise_error;
            do { if ( --((PyObject*)(cause))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(cause)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(cause)))); } while (0);
        }
        else if (((((cause)->ob_type)->tp_flags & ((1L<<30))) != 0)) {
            fixed_cause = cause;
        }
        else if (cause == (&_Py_NoneStruct)) {
            do { if ( --((PyObject*)(cause))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(cause)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(cause)))); } while (0);
            fixed_cause = ((void *)0);
        }
        else {
            PyErr_SetString(PyExc_TypeError,
                            "exception causes must derive from "
                            "BaseException");
            goto raise_error;
        }
        PyException_SetCause(value, fixed_cause);
    }

    PyErr_SetObject(type, value);

    do { if ((value) == ((void *)0)) ; else do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); } while (0);
    do { if ((type) == ((void *)0)) ; else do { if ( --((PyObject*)(type))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type)))); } while (0); } while (0);
    return WHY_EXCEPTION;

raise_error:
    do { if ((value) == ((void *)0)) ; else do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); } while (0);
    do { if ((type) == ((void *)0)) ; else do { if ( --((PyObject*)(type))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type)))); } while (0); } while (0);
    do { if ((cause) == ((void *)0)) ; else do { if ( --((PyObject*)(cause))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(cause)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(cause)))); } while (0); } while (0);
    return WHY_EXCEPTION;
}
# 3619 "ceval.c"
static int
unpack_iterable(PyObject *v, int argcnt, int argcntafter, PyObject **sp)
{
    int i = 0, j = 0;
    Py_ssize_t ll = 0;
    PyObject *it;
    PyObject *w;
    PyObject *l = ((void *)0);

    (__builtin_expect(!(v != ((void *)0)), 0) ? __assert_rtn(__func__, "ceval.c", 3628, "v != NULL") : (void)0);

    it = PyObject_GetIter(v);
    if (it == ((void *)0))
        goto Error;

    for (; i < argcnt; i++) {
        w = PyIter_Next(it);
        if (w == ((void *)0)) {

            if (!PyErr_Occurred()) {
                PyErr_Format(PyExc_ValueError,
                    "need more than %d value%s to unpack",
                    i, i == 1 ? "" : "s");
            }
            goto Error;
        }
        *--sp = w;
    }

    if (argcntafter == -1) {

        w = PyIter_Next(it);
        if (w == ((void *)0)) {
            if (PyErr_Occurred())
                goto Error;
            do { if ( --((PyObject*)(it))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(it)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(it)))); } while (0);
            return 1;
        }
        do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
        PyErr_Format(PyExc_ValueError, "too many values to unpack "
                     "(expected %d)", argcnt);
        goto Error;
    }

    l = PySequence_List(it);
    if (l == ((void *)0))
        goto Error;
    *--sp = l;
    i++;

    ll = (((PyVarObject*)(l))->ob_size);
    if (ll < argcntafter) {
        PyErr_Format(PyExc_ValueError, "need more than %zd values to unpack",
                     argcnt + ll);
        goto Error;
    }


    for (j = argcntafter; j > 0; j--, i++) {
        *--sp = (((PyListObject *)(l))->ob_item[ll - j]);
    }

    (((PyVarObject*)(l))->ob_size) = ll - argcntafter;
    do { if ( --((PyObject*)(it))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(it)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(it)))); } while (0);
    return 1;

Error:
    for (; i > 0; i--, sp++)
        do { if ( --((PyObject*)(*sp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(*sp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(*sp)))); } while (0);
    do { if ((it) == ((void *)0)) ; else do { if ( --((PyObject*)(it))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(it)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(it)))); } while (0); } while (0);
    return 0;
}
# 3705 "ceval.c"
static void
call_exc_trace(Py_tracefunc func, PyObject *self, PyFrameObject *f)
{
    PyObject *type, *value, *traceback, *arg;
    int err;
    PyErr_Fetch(&type, &value, &traceback);
    if (value == ((void *)0)) {
        value = (&_Py_NoneStruct);
        ( ((PyObject*)(value))->ob_refcnt++);
    }
    arg = PyTuple_Pack(3, type, value, traceback);
    if (arg == ((void *)0)) {
        PyErr_Restore(type, value, traceback);
        return;
    }
    err = call_trace(func, self, f, 1, arg);
    do { if ( --((PyObject*)(arg))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(arg)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(arg)))); } while (0);
    if (err == 0)
        PyErr_Restore(type, value, traceback);
    else {
        do { if ((type) == ((void *)0)) ; else do { if ( --((PyObject*)(type))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type)))); } while (0); } while (0);
        do { if ((value) == ((void *)0)) ; else do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); } while (0);
        do { if ((traceback) == ((void *)0)) ; else do { if ( --((PyObject*)(traceback))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(traceback)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(traceback)))); } while (0); } while (0);
    }
}

static int
call_trace_protected(Py_tracefunc func, PyObject *obj, PyFrameObject *frame,
                     int what, PyObject *arg)
{
    PyObject *type, *value, *traceback;
    int err;
    PyErr_Fetch(&type, &value, &traceback);
    err = call_trace(func, obj, frame, what, arg);
    if (err == 0)
    {
        PyErr_Restore(type, value, traceback);
        return 0;
    }
    else {
        do { if ((type) == ((void *)0)) ; else do { if ( --((PyObject*)(type))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type)))); } while (0); } while (0);
        do { if ((value) == ((void *)0)) ; else do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); } while (0);
        do { if ((traceback) == ((void *)0)) ; else do { if ( --((PyObject*)(traceback))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(traceback)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(traceback)))); } while (0); } while (0);
        return -1;
    }
}

static int
call_trace(Py_tracefunc func, PyObject *obj, PyFrameObject *frame,
           int what, PyObject *arg)
{
    register PyThreadState *tstate = frame->f_tstate;
    int result;
    if (tstate->tracing)
        return 0;
    tstate->tracing++;
    tstate->use_tracing = 0;
    result = func(obj, frame, what, arg);
    tstate->use_tracing = ((tstate->c_tracefunc != ((void *)0))
                           || (tstate->c_profilefunc != ((void *)0)));
    tstate->tracing--;
    return result;
}

PyObject *
_PyEval_CallTracing(PyObject *func, PyObject *args)
{
    PyFrameObject *frame = PyEval_GetFrame();
    PyThreadState *tstate = frame->f_tstate;
    int save_tracing = tstate->tracing;
    int save_use_tracing = tstate->use_tracing;
    PyObject *result;

    tstate->tracing = 0;
    tstate->use_tracing = ((tstate->c_tracefunc != ((void *)0))
                           || (tstate->c_profilefunc != ((void *)0)));
    result = PyObject_Call(func, args, ((void *)0));
    tstate->tracing = save_tracing;
    tstate->use_tracing = save_use_tracing;
    return result;
}


static int
maybe_call_line_trace(Py_tracefunc func, PyObject *obj,
                      PyFrameObject *frame, int *instr_lb, int *instr_ub,
                      int *instr_prev)
{
    int result = 0;
    int line = frame->f_lineno;




    if (frame->f_lasti < *instr_lb || frame->f_lasti >= *instr_ub) {
        PyAddrPair bounds;
        line = _PyCode_CheckLineNumber(frame->f_code, frame->f_lasti,
                                       &bounds);
        *instr_lb = bounds.ap_lower;
        *instr_ub = bounds.ap_upper;
    }



    if (frame->f_lasti == *instr_lb || frame->f_lasti < *instr_prev) {
        frame->f_lineno = line;
        result = call_trace(func, obj, frame, 2, (&_Py_NoneStruct));
    }
    *instr_prev = frame->f_lasti;
    return result;
}

void
PyEval_SetProfile(Py_tracefunc func, PyObject *arg)
{
    PyThreadState *tstate = ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }));
    PyObject *temp = tstate->c_profileobj;
    do { if ((arg) == ((void *)0)) ; else ( ((PyObject*)(arg))->ob_refcnt++); } while (0);
    tstate->c_profilefunc = ((void *)0);
    tstate->c_profileobj = ((void *)0);

    tstate->use_tracing = tstate->c_tracefunc != ((void *)0);
    do { if ((temp) == ((void *)0)) ; else do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0); } while (0);
    tstate->c_profilefunc = func;
    tstate->c_profileobj = arg;

    tstate->use_tracing = (func != ((void *)0)) || (tstate->c_tracefunc != ((void *)0));
}

void
PyEval_SetTrace(Py_tracefunc func, PyObject *arg)
{
    PyThreadState *tstate = ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }));
    PyObject *temp = tstate->c_traceobj;
    _Py_TracingPossible += (func != ((void *)0)) - (tstate->c_tracefunc != ((void *)0));
    do { if ((arg) == ((void *)0)) ; else ( ((PyObject*)(arg))->ob_refcnt++); } while (0);
    tstate->c_tracefunc = ((void *)0);
    tstate->c_traceobj = ((void *)0);

    tstate->use_tracing = tstate->c_profilefunc != ((void *)0);
    do { if ((temp) == ((void *)0)) ; else do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0); } while (0);
    tstate->c_tracefunc = func;
    tstate->c_traceobj = arg;

    tstate->use_tracing = ((func != ((void *)0))
                           || (tstate->c_profilefunc != ((void *)0)));
}

PyObject *
PyEval_GetBuiltins(void)
{
    PyFrameObject *current_frame = PyEval_GetFrame();
    if (current_frame == ((void *)0))
        return ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->interp->builtins;
    else
        return current_frame->f_builtins;
}

PyObject *
PyEval_GetLocals(void)
{
    PyFrameObject *current_frame = PyEval_GetFrame();
    if (current_frame == ((void *)0))
        return ((void *)0);
    PyFrame_FastToLocals(current_frame);
    return current_frame->f_locals;
}

PyObject *
PyEval_GetGlobals(void)
{
    PyFrameObject *current_frame = PyEval_GetFrame();
    if (current_frame == ((void *)0))
        return ((void *)0);
    else
        return current_frame->f_globals;
}

PyFrameObject *
PyEval_GetFrame(void)
{
    PyThreadState *tstate = ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }));
    return _PyThreadState_GetFrame(tstate);
}

int
PyEval_MergeCompilerFlags(PyCompilerFlags *cf)
{
    PyFrameObject *current_frame = PyEval_GetFrame();
    int result = cf->cf_flags != 0;

    if (current_frame != ((void *)0)) {
        const int codeflags = current_frame->f_code->co_flags;
        const int compilerflags = codeflags & (0x2000 | 0x4000 | 0x8000 | 0x10000 | 0x20000 | 0x40000);
        if (compilerflags) {
            result = 1;
            cf->cf_flags |= compilerflags;
        }






    }
    return result;
}





PyObject *
PyEval_CallObjectWithKeywords(PyObject *func, PyObject *arg, PyObject *kw)
{
    PyObject *result;

    if (arg == ((void *)0)) {
        arg = PyTuple_New(0);
        if (arg == ((void *)0))
            return ((void *)0);
    }
    else if (!((((((PyObject*)(arg))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
        PyErr_SetString(PyExc_TypeError,
                        "argument list must be a tuple");
        return ((void *)0);
    }
    else
        ( ((PyObject*)(arg))->ob_refcnt++);

    if (kw != ((void *)0) && !((((((PyObject*)(kw))->ob_type))->tp_flags & ((1L<<29))) != 0)) {
        PyErr_SetString(PyExc_TypeError,
                        "keyword list must be a dictionary");
        do { if ( --((PyObject*)(arg))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(arg)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(arg)))); } while (0);
        return ((void *)0);
    }

    result = PyObject_Call(func, arg, kw);
    do { if ( --((PyObject*)(arg))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(arg)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(arg)))); } while (0);
    return result;
}

const char *
PyEval_GetFuncName(PyObject *func)
{
    if (((func)->ob_type == &PyMethod_Type))
        return PyEval_GetFuncName((((PyMethodObject *)func) -> im_func));
    else if (((((PyObject*)(func))->ob_type) == &PyFunction_Type))
        return PyUnicode_AsUTF8(((PyFunctionObject*)func)->func_name);
    else if (((((PyObject*)(func))->ob_type) == &PyCFunction_Type))
        return ((PyCFunctionObject*)func)->m_ml->ml_name;
    else
        return func->ob_type->tp_name;
}

const char *
PyEval_GetFuncDesc(PyObject *func)
{
    if (((func)->ob_type == &PyMethod_Type))
        return "()";
    else if (((((PyObject*)(func))->ob_type) == &PyFunction_Type))
        return "()";
    else if (((((PyObject*)(func))->ob_type) == &PyCFunction_Type))
        return "()";
    else
        return " object";
}

static void
err_args(PyObject *func, int flags, int nargs)
{
    if (flags & 0x0004)
        PyErr_Format(PyExc_TypeError,
                     "%.200s() takes no arguments (%d given)",
                     ((PyCFunctionObject *)func)->m_ml->ml_name,
                     nargs);
    else
        PyErr_Format(PyExc_TypeError,
                     "%.200s() takes exactly one argument (%d given)",
                     ((PyCFunctionObject *)func)->m_ml->ml_name,
                     nargs);
}
# 4020 "ceval.c"
static PyObject *
call_function(PyObject ***pp_stack, int oparg



                )
{
    int na = oparg & 0xff;
    int nk = (oparg>>8) & 0xff;
    int n = na + 2 * nk;
    PyObject **pfunc = (*pp_stack) - n - 1;
    PyObject *func = *pfunc;
    PyObject *x, *w;




    if (((((PyObject*)(func))->ob_type) == &PyCFunction_Type) && nk == 0) {
        int flags = (((PyCFunctionObject *)func) -> m_ml -> ml_flags);
        PyThreadState *tstate = ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }));

        ;
        if (flags & (0x0004 | 0x0008)) {
            PyCFunction meth = (((PyCFunctionObject *)func) -> m_ml -> ml_meth);
            PyObject *self = (((PyCFunctionObject *)func) -> m_ml -> ml_flags & 0x0020 ? ((void *)0) : ((PyCFunctionObject *)func) -> m_self);
            if (flags & 0x0004 && na == 0) {
                if (tstate->use_tracing && tstate->c_profilefunc) { if (call_trace(tstate->c_profilefunc, tstate->c_profileobj, tstate->frame, 4, func)) { x = ((void *)0); } else { x = (*meth)(self,((void *)0)); if (tstate->c_profilefunc != ((void *)0)) { if (x == ((void *)0)) { call_trace_protected(tstate->c_profilefunc, tstate->c_profileobj, tstate->frame, 5, func); } else { if (call_trace(tstate->c_profilefunc, tstate->c_profileobj, tstate->frame, 6, func)) { do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0); x = ((void *)0); } } } } } else { x = (*meth)(self,((void *)0)); };
            }
            else if (flags & 0x0008 && na == 1) {
                PyObject *arg = (*--(*pp_stack));
                if (tstate->use_tracing && tstate->c_profilefunc) { if (call_trace(tstate->c_profilefunc, tstate->c_profileobj, tstate->frame, 4, func)) { x = ((void *)0); } else { x = (*meth)(self,arg); if (tstate->c_profilefunc != ((void *)0)) { if (x == ((void *)0)) { call_trace_protected(tstate->c_profilefunc, tstate->c_profileobj, tstate->frame, 5, func); } else { if (call_trace(tstate->c_profilefunc, tstate->c_profileobj, tstate->frame, 6, func)) { do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0); x = ((void *)0); } } } } } else { x = (*meth)(self,arg); };
                do { if ( --((PyObject*)(arg))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(arg)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(arg)))); } while (0);
            }
            else {
                err_args(func, flags, na);
                x = ((void *)0);
            }
        }
        else {
            PyObject *callargs;
            callargs = load_args(pp_stack, na);
            ;
            if (tstate->use_tracing && tstate->c_profilefunc) { if (call_trace(tstate->c_profilefunc, tstate->c_profileobj, tstate->frame, 4, func)) { x = ((void *)0); } else { x = PyCFunction_Call(func,callargs,((void *)0)); if (tstate->c_profilefunc != ((void *)0)) { if (x == ((void *)0)) { call_trace_protected(tstate->c_profilefunc, tstate->c_profileobj, tstate->frame, 5, func); } else { if (call_trace(tstate->c_profilefunc, tstate->c_profileobj, tstate->frame, 6, func)) { do { if ( --((PyObject*)(x))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(x)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(x)))); } while (0); x = ((void *)0); } } } } } else { x = PyCFunction_Call(func,callargs,((void *)0)); };
            ;
            do { if ((callargs) == ((void *)0)) ; else do { if ( --((PyObject*)(callargs))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(callargs)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(callargs)))); } while (0); } while (0);
        }
    } else {
        if (((func)->ob_type == &PyMethod_Type) && (((PyMethodObject *)func) -> im_self) != ((void *)0)) {

            PyObject *self = (((PyMethodObject *)func) -> im_self);
            ;
            ;
            ( ((PyObject*)(self))->ob_refcnt++);
            func = (((PyMethodObject *)func) -> im_func);
            ( ((PyObject*)(func))->ob_refcnt++);
            do { if ( --((PyObject*)(*pfunc))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(*pfunc)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(*pfunc)))); } while (0);
            *pfunc = self;
            na++;
            n++;
        } else
            ( ((PyObject*)(func))->ob_refcnt++);
        ;
        if (((((PyObject*)(func))->ob_type) == &PyFunction_Type))
            x = fast_function(func, pp_stack, n, na, nk);
        else
            x = do_call(func, pp_stack, na, nk);
        ;
        do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0);
    }





    while ((*pp_stack) > pfunc) {
        w = (*--(*pp_stack));
        do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
        ;
    }
    return x;
}
# 4111 "ceval.c"
static PyObject *
fast_function(PyObject *func, PyObject ***pp_stack, int n, int na, int nk)
{
    PyCodeObject *co = (PyCodeObject *)(((PyFunctionObject *)func) -> func_code);
    PyObject *globals = (((PyFunctionObject *)func) -> func_globals);
    PyObject *argdefs = (((PyFunctionObject *)func) -> func_defaults);
    PyObject *kwdefs = (((PyFunctionObject *)func) -> func_kwdefaults);
    PyObject **d = ((void *)0);
    int nd = 0;

    ;
    ;
    if (argdefs == ((void *)0) && co->co_argcount == n &&
        co->co_kwonlyargcount == 0 && nk==0 &&
        co->co_flags == (0x0001 | 0x0002 | 0x0040)) {
        PyFrameObject *f;
        PyObject *retval = ((void *)0);
        PyThreadState *tstate = ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }));
        PyObject **fastlocals, **stack;
        int i;

        ;
        (__builtin_expect(!(globals != ((void *)0)), 0) ? __assert_rtn(__func__, "ceval.c", 4133, "globals != NULL") : (void)0);




        (__builtin_expect(!(tstate != ((void *)0)), 0) ? __assert_rtn(__func__, "ceval.c", 4138, "tstate != NULL") : (void)0);
        f = PyFrame_New(tstate, co, globals, ((void *)0));
        if (f == ((void *)0))
            return ((void *)0);

        fastlocals = f->f_localsplus;
        stack = (*pp_stack) - n;

        for (i = 0; i < n; i++) {
            ( ((PyObject*)(*stack))->ob_refcnt++);
            fastlocals[i] = *stack++;
        }
        retval = PyEval_EvalFrameEx(f,0);
        ++tstate->recursion_depth;
        do { if ( --((PyObject*)(f))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(f)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(f)))); } while (0);
        --tstate->recursion_depth;
        return retval;
    }
    if (argdefs != ((void *)0)) {
        d = &(((PyTupleObject *)(argdefs))->ob_item[0]);
        nd = (((PyVarObject*)(argdefs))->ob_size);
    }
    return PyEval_EvalCodeEx((PyObject*)co, globals,
                             (PyObject *)((void *)0), (*pp_stack)-n, na,
                             (*pp_stack)-2*nk, nk, d, nd, kwdefs,
                             (((PyFunctionObject *)func) -> func_closure));
}

static PyObject *
update_keyword_args(PyObject *orig_kwdict, int nk, PyObject ***pp_stack,
                    PyObject *func)
{
    PyObject *kwdict = ((void *)0);
    if (orig_kwdict == ((void *)0))
        kwdict = PyDict_New();
    else {
        kwdict = PyDict_Copy(orig_kwdict);
        do { if ( --((PyObject*)(orig_kwdict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(orig_kwdict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(orig_kwdict)))); } while (0);
    }
    if (kwdict == ((void *)0))
        return ((void *)0);
    while (--nk >= 0) {
        int err;
        PyObject *value = (*--(*pp_stack));
        PyObject *key = (*--(*pp_stack));
        if (PyDict_GetItem(kwdict, key) != ((void *)0)) {
            PyErr_Format(PyExc_TypeError,
                         "%.200s%s got multiple values "
                         "for keyword argument '%U'",
                         PyEval_GetFuncName(func),
                         PyEval_GetFuncDesc(func),
                         key);
            do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
            do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0);
            do { if ( --((PyObject*)(kwdict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(kwdict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(kwdict)))); } while (0);
            return ((void *)0);
        }
        err = PyDict_SetItem(kwdict, key, value);
        do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
        do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0);
        if (err) {
            do { if ( --((PyObject*)(kwdict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(kwdict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(kwdict)))); } while (0);
            return ((void *)0);
        }
    }
    return kwdict;
}

static PyObject *
update_star_args(int nstack, int nstar, PyObject *stararg,
                 PyObject ***pp_stack)
{
    PyObject *callargs, *w;

    callargs = PyTuple_New(nstack + nstar);
    if (callargs == ((void *)0)) {
        return ((void *)0);
    }
    if (nstar) {
        int i;
        for (i = 0; i < nstar; i++) {
            PyObject *a = (((PyTupleObject *)(stararg))->ob_item[i]);
            ( ((PyObject*)(a))->ob_refcnt++);
            (((PyTupleObject *)(callargs))->ob_item[nstack + i] = a);
        }
    }
    while (--nstack >= 0) {
        w = (*--(*pp_stack));
        (((PyTupleObject *)(callargs))->ob_item[nstack] = w);
    }
    return callargs;
}

static PyObject *
load_args(PyObject ***pp_stack, int na)
{
    PyObject *args = PyTuple_New(na);
    PyObject *w;

    if (args == ((void *)0))
        return ((void *)0);
    while (--na >= 0) {
        w = (*--(*pp_stack));
        (((PyTupleObject *)(args))->ob_item[na] = w);
    }
    return args;
}

static PyObject *
do_call(PyObject *func, PyObject ***pp_stack, int na, int nk)
{
    PyObject *callargs = ((void *)0);
    PyObject *kwdict = ((void *)0);
    PyObject *result = ((void *)0);

    if (nk > 0) {
        kwdict = update_keyword_args(((void *)0), nk, pp_stack, func);
        if (kwdict == ((void *)0))
            goto call_fail;
    }
    callargs = load_args(pp_stack, na);
    if (callargs == ((void *)0))
        goto call_fail;
# 4277 "ceval.c"
    if (((((PyObject*)(func))->ob_type) == &PyCFunction_Type)) {
        PyThreadState *tstate = ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }));
        if (tstate->use_tracing && tstate->c_profilefunc) { if (call_trace(tstate->c_profilefunc, tstate->c_profileobj, tstate->frame, 4, func)) { result = ((void *)0); } else { result = PyCFunction_Call(func, callargs, kwdict); if (tstate->c_profilefunc != ((void *)0)) { if (result == ((void *)0)) { call_trace_protected(tstate->c_profilefunc, tstate->c_profileobj, tstate->frame, 5, func); } else { if (call_trace(tstate->c_profilefunc, tstate->c_profileobj, tstate->frame, 6, func)) { do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0); result = ((void *)0); } } } } } else { result = PyCFunction_Call(func, callargs, kwdict); };
    }
    else
        result = PyObject_Call(func, callargs, kwdict);
call_fail:
    do { if ((callargs) == ((void *)0)) ; else do { if ( --((PyObject*)(callargs))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(callargs)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(callargs)))); } while (0); } while (0);
    do { if ((kwdict) == ((void *)0)) ; else do { if ( --((PyObject*)(kwdict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(kwdict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(kwdict)))); } while (0); } while (0);
    return result;
}

static PyObject *
ext_do_call(PyObject *func, PyObject ***pp_stack, int flags, int na, int nk)
{
    int nstar = 0;
    PyObject *callargs = ((void *)0);
    PyObject *stararg = ((void *)0);
    PyObject *kwdict = ((void *)0);
    PyObject *result = ((void *)0);

    if (flags & 2) {
        kwdict = (*--(*pp_stack));
        if (!((((((PyObject*)(kwdict))->ob_type))->tp_flags & ((1L<<29))) != 0)) {
            PyObject *d;
            d = PyDict_New();
            if (d == ((void *)0))
                goto ext_call_fail;
            if (PyDict_Update(d, kwdict) != 0) {
                do { if ( --((PyObject*)(d))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(d)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(d)))); } while (0);






                if (PyErr_ExceptionMatches(PyExc_AttributeError)) {
                    PyErr_Format(PyExc_TypeError,
                                 "%.200s%.200s argument after ** "
                                 "must be a mapping, not %.200s",
                                 PyEval_GetFuncName(func),
                                 PyEval_GetFuncDesc(func),
                                 kwdict->ob_type->tp_name);
                }
                goto ext_call_fail;
            }
            do { if ( --((PyObject*)(kwdict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(kwdict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(kwdict)))); } while (0);
            kwdict = d;
        }
    }
    if (flags & 1) {
        stararg = (*--(*pp_stack));
        if (!((((((PyObject*)(stararg))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
            PyObject *t = ((void *)0);
            t = PySequence_Tuple(stararg);
            if (t == ((void *)0)) {
                if (PyErr_ExceptionMatches(PyExc_TypeError)) {
                    PyErr_Format(PyExc_TypeError,
                                 "%.200s%.200s argument after * "
                                 "must be a sequence, not %.200s",
                                 PyEval_GetFuncName(func),
                                 PyEval_GetFuncDesc(func),
                                 stararg->ob_type->tp_name);
                }
                goto ext_call_fail;
            }
            do { if ( --((PyObject*)(stararg))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(stararg)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(stararg)))); } while (0);
            stararg = t;
        }
        nstar = (((PyVarObject*)(stararg))->ob_size);
    }
    if (nk > 0) {
        kwdict = update_keyword_args(kwdict, nk, pp_stack, func);
        if (kwdict == ((void *)0))
            goto ext_call_fail;
    }
    callargs = update_star_args(na, nstar, stararg, pp_stack);
    if (callargs == ((void *)0))
        goto ext_call_fail;
# 4372 "ceval.c"
    if (((((PyObject*)(func))->ob_type) == &PyCFunction_Type)) {
        PyThreadState *tstate = ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }));
        if (tstate->use_tracing && tstate->c_profilefunc) { if (call_trace(tstate->c_profilefunc, tstate->c_profileobj, tstate->frame, 4, func)) { result = ((void *)0); } else { result = PyCFunction_Call(func, callargs, kwdict); if (tstate->c_profilefunc != ((void *)0)) { if (result == ((void *)0)) { call_trace_protected(tstate->c_profilefunc, tstate->c_profileobj, tstate->frame, 5, func); } else { if (call_trace(tstate->c_profilefunc, tstate->c_profileobj, tstate->frame, 6, func)) { do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0); result = ((void *)0); } } } } } else { result = PyCFunction_Call(func, callargs, kwdict); };
    }
    else
        result = PyObject_Call(func, callargs, kwdict);
ext_call_fail:
    do { if ((callargs) == ((void *)0)) ; else do { if ( --((PyObject*)(callargs))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(callargs)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(callargs)))); } while (0); } while (0);
    do { if ((kwdict) == ((void *)0)) ; else do { if ( --((PyObject*)(kwdict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(kwdict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(kwdict)))); } while (0); } while (0);
    do { if ((stararg) == ((void *)0)) ; else do { if ( --((PyObject*)(stararg))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(stararg)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(stararg)))); } while (0); } while (0);
    return result;
}
# 4395 "ceval.c"
int
_PyEval_SliceIndex(PyObject *v, Py_ssize_t *pi)
{
    if (v != ((void *)0)) {
        Py_ssize_t x;
        if (((v)->ob_type->tp_as_number != ((void *)0) && (v)->ob_type->tp_as_number->nb_index != ((void *)0))) {
            x = PyNumber_AsSsize_t(v, ((void *)0));
            if (x == -1 && PyErr_Occurred())
                return 0;
        }
        else {
            PyErr_SetString(PyExc_TypeError,
                            "slice indices must be integers or "
                            "None or have an __index__ method");
            return 0;
        }
        *pi = x;
    }
    return 1;
}




static PyObject *
cmp_outcome(int op, register PyObject *v, register PyObject *w)
{
    int res = 0;
    switch (op) {
    case PyCmp_IS:
        res = (v == w);
        break;
    case PyCmp_IS_NOT:
        res = (v != w);
        break;
    case PyCmp_IN:
        res = PySequence_Contains(w, v);
        if (res < 0)
            return ((void *)0);
        break;
    case PyCmp_NOT_IN:
        res = PySequence_Contains(w, v);
        if (res < 0)
            return ((void *)0);
        res = !res;
        break;
    case PyCmp_EXC_MATCH:
        if (((((((PyObject*)(w))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
            Py_ssize_t i, length;
            length = PyTuple_Size(w);
            for (i = 0; i < length; i += 1) {
                PyObject *exc = (((PyTupleObject *)(w))->ob_item[i]);
                if (!(((((((PyObject*)((exc)))->ob_type))->tp_flags & ((1L<<31))) != 0) && ((((PyTypeObject*)(exc))->tp_flags & ((1L<<30))) != 0))) {
                    PyErr_SetString(PyExc_TypeError,
                                    "catching classes that do not inherit from " "BaseException is not allowed");
                    return ((void *)0);
                }
            }
        }
        else {
            if (!(((((((PyObject*)((w)))->ob_type))->tp_flags & ((1L<<31))) != 0) && ((((PyTypeObject*)(w))->tp_flags & ((1L<<30))) != 0))) {
                PyErr_SetString(PyExc_TypeError,
                                "catching classes that do not inherit from " "BaseException is not allowed");
                return ((void *)0);
            }
        }
        res = PyErr_GivenExceptionMatches(v, w);
        break;
    default:
        return PyObject_RichCompare(v, w, op);
    }
    v = res ? ((PyObject *) &_Py_TrueStruct) : ((PyObject *) &_Py_FalseStruct);
    ( ((PyObject*)(v))->ob_refcnt++);
    return v;
}

static PyObject *
import_from(PyObject *v, PyObject *name)
{
    PyObject *x;

    x = PyObject_GetAttr(v, name);
    if (x == ((void *)0) && PyErr_ExceptionMatches(PyExc_AttributeError)) {
        PyErr_Format(PyExc_ImportError, "cannot import name %S", name);
    }
    return x;
}

static int
import_all_from(PyObject *locals, PyObject *v)
{
    static _Py_Identifier PyId___all__ = { 0, "__all__", 0 };
    static _Py_Identifier PyId___dict__ = { 0, "__dict__", 0 };
    PyObject *all = _PyObject_GetAttrId(v, &PyId___all__);
    PyObject *dict, *name, *value;
    int skip_leading_underscores = 0;
    int pos, err;

    if (all == ((void *)0)) {
        if (!PyErr_ExceptionMatches(PyExc_AttributeError))
            return -1;
        PyErr_Clear();
        dict = _PyObject_GetAttrId(v, &PyId___dict__);
        if (dict == ((void *)0)) {
            if (!PyErr_ExceptionMatches(PyExc_AttributeError))
                return -1;
            PyErr_SetString(PyExc_ImportError,
            "from-import-* object has no __dict__ and no __all__");
            return -1;
        }
        all = PyMapping_Keys(dict);
        do { if ( --((PyObject*)(dict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dict)))); } while (0);
        if (all == ((void *)0))
            return -1;
        skip_leading_underscores = 1;
    }

    for (pos = 0, err = 0; ; pos++) {
        name = PySequence_GetItem(all, pos);
        if (name == ((void *)0)) {
            if (!PyErr_ExceptionMatches(PyExc_IndexError))
                err = -1;
            else
                PyErr_Clear();
            break;
        }
        if (skip_leading_underscores &&
            ((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0) &&
            ((__builtin_expect(!(((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "ceval.c", 4523, "PyUnicode_Check(name)") : (void)0), ((((PyASCIIObject*)name)->state.ready) ? 0 : _PyUnicode_Ready((PyObject *)(name)))) != -1 &&
            ((__builtin_expect(!(((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "ceval.c", 4524, "PyUnicode_Check(name)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)name)->state.ready)), 0) ? __assert_rtn(__func__, "ceval.c", 4524, "PyUnicode_IS_READY(name)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "ceval.c", 4524, "PyUnicode_Check((name))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(name))->state.ready)), 0) ? __assert_rtn(__func__, "ceval.c", 4524, "PyUnicode_IS_READY((name))") : (void)0), ((PyASCIIObject *)((name)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "ceval.c", 4524, "PyUnicode_Check((name))") : (void)0), (((PyASCIIObject*)((name)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "ceval.c", 4524, "PyUnicode_Check((name))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(name))->state.ready)), 0) ? __assert_rtn(__func__, "ceval.c", 4524, "PyUnicode_IS_READY((name))") : (void)0), ((PyASCIIObject*)(name))->state.ascii) ? ((void*)((PyASCIIObject*)((name)) + 1)) : ((void*)((PyCompactUnicodeObject*)((name)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((name)))->data.any), 0) ? __assert_rtn(__func__, "ceval.c", 4524, "((PyUnicodeObject*)((name)))->data.any") : (void)0), ((((PyUnicodeObject *)((name)))->data.any))))))[(0)] : (((__builtin_expect(!(((((((PyObject*)((name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "ceval.c", 4524, "PyUnicode_Check((name))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(name))->state.ready)), 0) ? __assert_rtn(__func__, "ceval.c", 4524, "PyUnicode_IS_READY((name))") : (void)0), ((PyASCIIObject *)((name)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "ceval.c", 4524, "PyUnicode_Check((name))") : (void)0), (((PyASCIIObject*)((name)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "ceval.c", 4524, "PyUnicode_Check((name))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(name))->state.ready)), 0) ? __assert_rtn(__func__, "ceval.c", 4524, "PyUnicode_IS_READY((name))") : (void)0), ((PyASCIIObject*)(name))->state.ascii) ? ((void*)((PyASCIIObject*)((name)) + 1)) : ((void*)((PyCompactUnicodeObject*)((name)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((name)))->data.any), 0) ? __assert_rtn(__func__, "ceval.c", 4524, "((PyUnicodeObject*)((name)))->data.any") : (void)0), ((((PyUnicodeObject *)((name)))->data.any))))))[(0)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "ceval.c", 4524, "PyUnicode_Check((name))") : (void)0), (((PyASCIIObject*)((name)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "ceval.c", 4524, "PyUnicode_Check((name))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(name))->state.ready)), 0) ? __assert_rtn(__func__, "ceval.c", 4524, "PyUnicode_IS_READY((name))") : (void)0), ((PyASCIIObject*)(name))->state.ascii) ? ((void*)((PyASCIIObject*)((name)) + 1)) : ((void*)((PyCompactUnicodeObject*)((name)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((name)))->data.any), 0) ? __assert_rtn(__func__, "ceval.c", 4524, "((PyUnicodeObject*)((name)))->data.any") : (void)0), ((((PyUnicodeObject *)((name)))->data.any))))))[(0)] ) )) == '_')
        {
            do { if ( --((PyObject*)(name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(name)))); } while (0);
            continue;
        }
        value = PyObject_GetAttr(v, name);
        if (value == ((void *)0))
            err = -1;
        else if (((((PyObject*)(locals))->ob_type) == &PyDict_Type))
            err = PyDict_SetItem(locals, name, value);
        else
            err = PyObject_SetItem(locals, name, value);
        do { if ( --((PyObject*)(name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(name)))); } while (0);
        do { if ((value) == ((void *)0)) ; else do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); } while (0);
        if (err != 0)
            break;
    }
    do { if ( --((PyObject*)(all))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(all)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(all)))); } while (0);
    return err;
}

static void
format_exc_check_arg(PyObject *exc, const char *format_str, PyObject *obj)
{
    const char *obj_str;

    if (!obj)
        return;

    obj_str = PyUnicode_AsUTF8(obj);
    if (!obj_str)
        return;

    PyErr_Format(exc, format_str, obj_str);
}

static void
format_exc_unbound(PyCodeObject *co, int oparg)
{
    PyObject *name;

    if (PyErr_Occurred())
        return;
    if (oparg < (((PyVarObject*)(co->co_cellvars))->ob_size)) {
        name = (((PyTupleObject *)(co->co_cellvars))->ob_item[oparg]);

        format_exc_check_arg(
            PyExc_UnboundLocalError,
            "local variable '%.200s' referenced before assignment",
            name);
    } else {
        name = (((PyTupleObject *)(co->co_freevars))->ob_item[oparg - (((PyVarObject*)(co->co_cellvars))->ob_size)]);

        format_exc_check_arg(PyExc_NameError,
                             "free variable '%.200s' referenced before assignment" " in enclosing scope", name);
    }
}

static PyObject *
unicode_concatenate(PyObject *v, PyObject *w,
                    PyFrameObject *f, unsigned char *next_instr)
{
    PyObject *res;
    if ((((PyObject*)(v))->ob_refcnt) == 2) {






        switch (*next_instr) {
        case 125:
        {
            int oparg = ((next_instr[2]<<8) + next_instr[1]);
            PyObject **fastlocals = f->f_localsplus;
            if ((fastlocals[oparg]) == v)
                do { PyObject *tmp = (fastlocals[oparg]); (fastlocals[oparg]) = ((void *)0); do { if ((tmp) == ((void *)0)) ; else do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0); } while (0); } while (0);
            break;
        }
        case 137:
        {
            PyObject **freevars = (f->f_localsplus +
                                   f->f_code->co_nlocals);
            PyObject *c = freevars[((next_instr[2]<<8) + next_instr[1])];
            if ((((PyCellObject *)(c))->ob_ref) == v)
                PyCell_Set(c, ((void *)0));
            break;
        }
        case 90:
        {
            PyObject *names = f->f_code->co_names;
            PyObject *name = (((PyTupleObject *)((PyTupleObject *)(names)))->ob_item[(((next_instr[2]<<8) + next_instr[1]))]);
            PyObject *locals = f->f_locals;
            if (((((PyObject*)(locals))->ob_type) == &PyDict_Type) &&
                PyDict_GetItem(locals, name) == v) {
                if (PyDict_DelItem(locals, name) != 0) {
                    PyErr_Clear();
                }
            }
            break;
        }
        }
    }
    res = v;
    PyUnicode_Append(&res, w);
    return res;
}
