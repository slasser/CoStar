# 1 "compile.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "compile.c"
# 24 "compile.c"
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
# 25 "compile.c" 2

# 1 "/Users/parrt/tmp/Python-3.3.1/Include/Python-ast.h" 1


# 1 "/Users/parrt/tmp/Python-3.3.1/Include/asdl.h" 1



typedef PyObject * identifier;
typedef PyObject * string;
typedef PyObject * bytes;
typedef PyObject * object;
# 17 "/Users/parrt/tmp/Python-3.3.1/Include/asdl.h"
typedef struct {
    Py_ssize_t size;
    void *elements[1];
} asdl_seq;

typedef struct {
    Py_ssize_t size;
    int elements[1];
} asdl_int_seq;

asdl_seq *asdl_seq_new(Py_ssize_t size, PyArena *arena);
asdl_int_seq *asdl_int_seq_new(Py_ssize_t size, PyArena *arena);
# 4 "/Users/parrt/tmp/Python-3.3.1/Include/Python-ast.h" 2

typedef struct _mod *mod_ty;

typedef struct _stmt *stmt_ty;

typedef struct _expr *expr_ty;

typedef enum _expr_context { Load=1, Store=2, Del=3, AugLoad=4, AugStore=5,
                             Param=6 } expr_context_ty;

typedef struct _slice *slice_ty;

typedef enum _boolop { And=1, Or=2 } boolop_ty;

typedef enum _operator { Add=1, Sub=2, Mult=3, Div=4, Mod=5, Pow=6, LShift=7,
                         RShift=8, BitOr=9, BitXor=10, BitAnd=11, FloorDiv=12 }
                         operator_ty;

typedef enum _unaryop { Invert=1, Not=2, UAdd=3, USub=4 } unaryop_ty;

typedef enum _cmpop { Eq=1, NotEq=2, Lt=3, LtE=4, Gt=5, GtE=6, Is=7, IsNot=8,
                      In=9, NotIn=10 } cmpop_ty;

typedef struct _comprehension *comprehension_ty;

typedef struct _excepthandler *excepthandler_ty;

typedef struct _arguments *arguments_ty;

typedef struct _arg *arg_ty;

typedef struct _keyword *keyword_ty;

typedef struct _alias *alias_ty;

typedef struct _withitem *withitem_ty;


enum _mod_kind {Module_kind=1, Interactive_kind=2, Expression_kind=3,
                 Suite_kind=4};
struct _mod {
        enum _mod_kind kind;
        union {
                struct {
                        asdl_seq *body;
                } Module;

                struct {
                        asdl_seq *body;
                } Interactive;

                struct {
                        expr_ty body;
                } Expression;

                struct {
                        asdl_seq *body;
                } Suite;

        } v;
};

enum _stmt_kind {FunctionDef_kind=1, ClassDef_kind=2, Return_kind=3,
                  Delete_kind=4, Assign_kind=5, AugAssign_kind=6, For_kind=7,
                  While_kind=8, If_kind=9, With_kind=10, Raise_kind=11,
                  Try_kind=12, Assert_kind=13, Import_kind=14,
                  ImportFrom_kind=15, Global_kind=16, Nonlocal_kind=17,
                  Expr_kind=18, Pass_kind=19, Break_kind=20, Continue_kind=21};
struct _stmt {
        enum _stmt_kind kind;
        union {
                struct {
                        identifier name;
                        arguments_ty args;
                        asdl_seq *body;
                        asdl_seq *decorator_list;
                        expr_ty returns;
                } FunctionDef;

                struct {
                        identifier name;
                        asdl_seq *bases;
                        asdl_seq *keywords;
                        expr_ty starargs;
                        expr_ty kwargs;
                        asdl_seq *body;
                        asdl_seq *decorator_list;
                } ClassDef;

                struct {
                        expr_ty value;
                } Return;

                struct {
                        asdl_seq *targets;
                } Delete;

                struct {
                        asdl_seq *targets;
                        expr_ty value;
                } Assign;

                struct {
                        expr_ty target;
                        operator_ty op;
                        expr_ty value;
                } AugAssign;

                struct {
                        expr_ty target;
                        expr_ty iter;
                        asdl_seq *body;
                        asdl_seq *orelse;
                } For;

                struct {
                        expr_ty test;
                        asdl_seq *body;
                        asdl_seq *orelse;
                } While;

                struct {
                        expr_ty test;
                        asdl_seq *body;
                        asdl_seq *orelse;
                } If;

                struct {
                        asdl_seq *items;
                        asdl_seq *body;
                } With;

                struct {
                        expr_ty exc;
                        expr_ty cause;
                } Raise;

                struct {
                        asdl_seq *body;
                        asdl_seq *handlers;
                        asdl_seq *orelse;
                        asdl_seq *finalbody;
                } Try;

                struct {
                        expr_ty test;
                        expr_ty msg;
                } Assert;

                struct {
                        asdl_seq *names;
                } Import;

                struct {
                        identifier module;
                        asdl_seq *names;
                        int level;
                } ImportFrom;

                struct {
                        asdl_seq *names;
                } Global;

                struct {
                        asdl_seq *names;
                } Nonlocal;

                struct {
                        expr_ty value;
                } Expr;

        } v;
        int lineno;
        int col_offset;
};

enum _expr_kind {BoolOp_kind=1, BinOp_kind=2, UnaryOp_kind=3, Lambda_kind=4,
                  IfExp_kind=5, Dict_kind=6, Set_kind=7, ListComp_kind=8,
                  SetComp_kind=9, DictComp_kind=10, GeneratorExp_kind=11,
                  Yield_kind=12, YieldFrom_kind=13, Compare_kind=14,
                  Call_kind=15, Num_kind=16, Str_kind=17, Bytes_kind=18,
                  Ellipsis_kind=19, Attribute_kind=20, Subscript_kind=21,
                  Starred_kind=22, Name_kind=23, List_kind=24, Tuple_kind=25};
struct _expr {
        enum _expr_kind kind;
        union {
                struct {
                        boolop_ty op;
                        asdl_seq *values;
                } BoolOp;

                struct {
                        expr_ty left;
                        operator_ty op;
                        expr_ty right;
                } BinOp;

                struct {
                        unaryop_ty op;
                        expr_ty operand;
                } UnaryOp;

                struct {
                        arguments_ty args;
                        expr_ty body;
                } Lambda;

                struct {
                        expr_ty test;
                        expr_ty body;
                        expr_ty orelse;
                } IfExp;

                struct {
                        asdl_seq *keys;
                        asdl_seq *values;
                } Dict;

                struct {
                        asdl_seq *elts;
                } Set;

                struct {
                        expr_ty elt;
                        asdl_seq *generators;
                } ListComp;

                struct {
                        expr_ty elt;
                        asdl_seq *generators;
                } SetComp;

                struct {
                        expr_ty key;
                        expr_ty value;
                        asdl_seq *generators;
                } DictComp;

                struct {
                        expr_ty elt;
                        asdl_seq *generators;
                } GeneratorExp;

                struct {
                        expr_ty value;
                } Yield;

                struct {
                        expr_ty value;
                } YieldFrom;

                struct {
                        expr_ty left;
                        asdl_int_seq *ops;
                        asdl_seq *comparators;
                } Compare;

                struct {
                        expr_ty func;
                        asdl_seq *args;
                        asdl_seq *keywords;
                        expr_ty starargs;
                        expr_ty kwargs;
                } Call;

                struct {
                        object n;
                } Num;

                struct {
                        string s;
                } Str;

                struct {
                        bytes s;
                } Bytes;

                struct {
                        expr_ty value;
                        identifier attr;
                        expr_context_ty ctx;
                } Attribute;

                struct {
                        expr_ty value;
                        slice_ty slice;
                        expr_context_ty ctx;
                } Subscript;

                struct {
                        expr_ty value;
                        expr_context_ty ctx;
                } Starred;

                struct {
                        identifier id;
                        expr_context_ty ctx;
                } Name;

                struct {
                        asdl_seq *elts;
                        expr_context_ty ctx;
                } List;

                struct {
                        asdl_seq *elts;
                        expr_context_ty ctx;
                } Tuple;

        } v;
        int lineno;
        int col_offset;
};

enum _slice_kind {Slice_kind=1, ExtSlice_kind=2, Index_kind=3};
struct _slice {
        enum _slice_kind kind;
        union {
                struct {
                        expr_ty lower;
                        expr_ty upper;
                        expr_ty step;
                } Slice;

                struct {
                        asdl_seq *dims;
                } ExtSlice;

                struct {
                        expr_ty value;
                } Index;

        } v;
};

struct _comprehension {
        expr_ty target;
        expr_ty iter;
        asdl_seq *ifs;
};

enum _excepthandler_kind {ExceptHandler_kind=1};
struct _excepthandler {
        enum _excepthandler_kind kind;
        union {
                struct {
                        expr_ty type;
                        identifier name;
                        asdl_seq *body;
                } ExceptHandler;

        } v;
        int lineno;
        int col_offset;
};

struct _arguments {
        asdl_seq *args;
        identifier vararg;
        expr_ty varargannotation;
        asdl_seq *kwonlyargs;
        identifier kwarg;
        expr_ty kwargannotation;
        asdl_seq *defaults;
        asdl_seq *kw_defaults;
};

struct _arg {
        identifier arg;
        expr_ty annotation;
};

struct _keyword {
        identifier arg;
        expr_ty value;
};

struct _alias {
        identifier name;
        identifier asname;
};

struct _withitem {
        expr_ty context_expr;
        expr_ty optional_vars;
};



mod_ty _Py_Module(asdl_seq * body, PyArena *arena);

mod_ty _Py_Interactive(asdl_seq * body, PyArena *arena);

mod_ty _Py_Expression(expr_ty body, PyArena *arena);

mod_ty _Py_Suite(asdl_seq * body, PyArena *arena);

stmt_ty _Py_FunctionDef(identifier name, arguments_ty args, asdl_seq * body,
                        asdl_seq * decorator_list, expr_ty returns, int lineno,
                        int col_offset, PyArena *arena);

stmt_ty _Py_ClassDef(identifier name, asdl_seq * bases, asdl_seq * keywords,
                     expr_ty starargs, expr_ty kwargs, asdl_seq * body,
                     asdl_seq * decorator_list, int lineno, int col_offset,
                     PyArena *arena);

stmt_ty _Py_Return(expr_ty value, int lineno, int col_offset, PyArena *arena);

stmt_ty _Py_Delete(asdl_seq * targets, int lineno, int col_offset, PyArena
                   *arena);

stmt_ty _Py_Assign(asdl_seq * targets, expr_ty value, int lineno, int
                   col_offset, PyArena *arena);

stmt_ty _Py_AugAssign(expr_ty target, operator_ty op, expr_ty value, int
                      lineno, int col_offset, PyArena *arena);

stmt_ty _Py_For(expr_ty target, expr_ty iter, asdl_seq * body, asdl_seq *
                orelse, int lineno, int col_offset, PyArena *arena);

stmt_ty _Py_While(expr_ty test, asdl_seq * body, asdl_seq * orelse, int lineno,
                  int col_offset, PyArena *arena);

stmt_ty _Py_If(expr_ty test, asdl_seq * body, asdl_seq * orelse, int lineno,
               int col_offset, PyArena *arena);

stmt_ty _Py_With(asdl_seq * items, asdl_seq * body, int lineno, int col_offset,
                 PyArena *arena);

stmt_ty _Py_Raise(expr_ty exc, expr_ty cause, int lineno, int col_offset,
                  PyArena *arena);

stmt_ty _Py_Try(asdl_seq * body, asdl_seq * handlers, asdl_seq * orelse,
                asdl_seq * finalbody, int lineno, int col_offset, PyArena
                *arena);

stmt_ty _Py_Assert(expr_ty test, expr_ty msg, int lineno, int col_offset,
                   PyArena *arena);

stmt_ty _Py_Import(asdl_seq * names, int lineno, int col_offset, PyArena
                   *arena);

stmt_ty _Py_ImportFrom(identifier module, asdl_seq * names, int level, int
                       lineno, int col_offset, PyArena *arena);

stmt_ty _Py_Global(asdl_seq * names, int lineno, int col_offset, PyArena
                   *arena);

stmt_ty _Py_Nonlocal(asdl_seq * names, int lineno, int col_offset, PyArena
                     *arena);

stmt_ty _Py_Expr(expr_ty value, int lineno, int col_offset, PyArena *arena);

stmt_ty _Py_Pass(int lineno, int col_offset, PyArena *arena);

stmt_ty _Py_Break(int lineno, int col_offset, PyArena *arena);

stmt_ty _Py_Continue(int lineno, int col_offset, PyArena *arena);

expr_ty _Py_BoolOp(boolop_ty op, asdl_seq * values, int lineno, int col_offset,
                   PyArena *arena);

expr_ty _Py_BinOp(expr_ty left, operator_ty op, expr_ty right, int lineno, int
                  col_offset, PyArena *arena);

expr_ty _Py_UnaryOp(unaryop_ty op, expr_ty operand, int lineno, int col_offset,
                    PyArena *arena);

expr_ty _Py_Lambda(arguments_ty args, expr_ty body, int lineno, int col_offset,
                   PyArena *arena);

expr_ty _Py_IfExp(expr_ty test, expr_ty body, expr_ty orelse, int lineno, int
                  col_offset, PyArena *arena);

expr_ty _Py_Dict(asdl_seq * keys, asdl_seq * values, int lineno, int
                 col_offset, PyArena *arena);

expr_ty _Py_Set(asdl_seq * elts, int lineno, int col_offset, PyArena *arena);

expr_ty _Py_ListComp(expr_ty elt, asdl_seq * generators, int lineno, int
                     col_offset, PyArena *arena);

expr_ty _Py_SetComp(expr_ty elt, asdl_seq * generators, int lineno, int
                    col_offset, PyArena *arena);

expr_ty _Py_DictComp(expr_ty key, expr_ty value, asdl_seq * generators, int
                     lineno, int col_offset, PyArena *arena);

expr_ty _Py_GeneratorExp(expr_ty elt, asdl_seq * generators, int lineno, int
                         col_offset, PyArena *arena);

expr_ty _Py_Yield(expr_ty value, int lineno, int col_offset, PyArena *arena);

expr_ty _Py_YieldFrom(expr_ty value, int lineno, int col_offset, PyArena
                      *arena);

expr_ty _Py_Compare(expr_ty left, asdl_int_seq * ops, asdl_seq * comparators,
                    int lineno, int col_offset, PyArena *arena);

expr_ty _Py_Call(expr_ty func, asdl_seq * args, asdl_seq * keywords, expr_ty
                 starargs, expr_ty kwargs, int lineno, int col_offset, PyArena
                 *arena);

expr_ty _Py_Num(object n, int lineno, int col_offset, PyArena *arena);

expr_ty _Py_Str(string s, int lineno, int col_offset, PyArena *arena);

expr_ty _Py_Bytes(bytes s, int lineno, int col_offset, PyArena *arena);

expr_ty _Py_Ellipsis(int lineno, int col_offset, PyArena *arena);

expr_ty _Py_Attribute(expr_ty value, identifier attr, expr_context_ty ctx, int
                      lineno, int col_offset, PyArena *arena);

expr_ty _Py_Subscript(expr_ty value, slice_ty slice, expr_context_ty ctx, int
                      lineno, int col_offset, PyArena *arena);

expr_ty _Py_Starred(expr_ty value, expr_context_ty ctx, int lineno, int
                    col_offset, PyArena *arena);

expr_ty _Py_Name(identifier id, expr_context_ty ctx, int lineno, int
                 col_offset, PyArena *arena);

expr_ty _Py_List(asdl_seq * elts, expr_context_ty ctx, int lineno, int
                 col_offset, PyArena *arena);

expr_ty _Py_Tuple(asdl_seq * elts, expr_context_ty ctx, int lineno, int
                  col_offset, PyArena *arena);

slice_ty _Py_Slice(expr_ty lower, expr_ty upper, expr_ty step, PyArena *arena);

slice_ty _Py_ExtSlice(asdl_seq * dims, PyArena *arena);

slice_ty _Py_Index(expr_ty value, PyArena *arena);

comprehension_ty _Py_comprehension(expr_ty target, expr_ty iter, asdl_seq *
                                   ifs, PyArena *arena);

excepthandler_ty _Py_ExceptHandler(expr_ty type, identifier name, asdl_seq *
                                   body, int lineno, int col_offset, PyArena
                                   *arena);

arguments_ty _Py_arguments(asdl_seq * args, identifier vararg, expr_ty
                           varargannotation, asdl_seq * kwonlyargs, identifier
                           kwarg, expr_ty kwargannotation, asdl_seq * defaults,
                           asdl_seq * kw_defaults, PyArena *arena);

arg_ty _Py_arg(identifier arg, expr_ty annotation, PyArena *arena);

keyword_ty _Py_keyword(identifier arg, expr_ty value, PyArena *arena);

alias_ty _Py_alias(identifier name, identifier asname, PyArena *arena);

withitem_ty _Py_withitem(expr_ty context_expr, expr_ty optional_vars, PyArena
                         *arena);

PyObject* PyAST_mod2obj(mod_ty t);
mod_ty PyAST_obj2mod(PyObject* ast, PyArena* arena, int mode);
int PyAST_Check(PyObject* obj);
# 27 "compile.c" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/node.h" 1
# 10 "/Users/parrt/tmp/Python-3.3.1/Include/node.h"
typedef struct _node {
    short n_type;
    char *n_str;
    int n_lineno;
    int n_col_offset;
    int n_nchildren;
    struct _node *n_child;
} node;

node * PyNode_New(int type);
int PyNode_AddChild(node *n, int type,
                                      char *str, int lineno, int col_offset);
void PyNode_Free(node *n);

Py_ssize_t _PyNode_SizeOf(node *n);
# 39 "/Users/parrt/tmp/Python-3.3.1/Include/node.h"
void PyNode_ListTree(node *);
# 28 "compile.c" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/ast.h" 1






int PyAST_Validate(mod_ty);
mod_ty PyAST_FromNode(
    const node *n,
    PyCompilerFlags *flags,
    const char *filename,
    PyArena *arena);
# 29 "compile.c" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/code.h" 1
# 30 "compile.c" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/symtable.h" 1
# 13 "/Users/parrt/tmp/Python-3.3.1/Include/symtable.h"
typedef enum _block_type { FunctionBlock, ClassBlock, ModuleBlock }
    _Py_block_ty;

struct _symtable_entry;

struct symtable {
    const char *st_filename;

    struct _symtable_entry *st_cur;
    struct _symtable_entry *st_top;
    PyObject *st_blocks;

    PyObject *st_stack;
    PyObject *st_global;
    int st_nblocks;


    PyObject *st_private;
    PyFutureFeatures *st_future;

    int recursion_depth;
    int recursion_limit;
};

typedef struct _symtable_entry {
    PyObject ob_base;
    PyObject *ste_id;
    PyObject *ste_symbols;
    PyObject *ste_name;
    PyObject *ste_varnames;
    PyObject *ste_children;
    _Py_block_ty ste_type;
    int ste_unoptimized;
    int ste_nested;
    unsigned ste_free : 1;
    unsigned ste_child_free : 1;

    unsigned ste_generator : 1;
    unsigned ste_varargs : 1;
    unsigned ste_varkeywords : 1;
    unsigned ste_returns_value : 1;

    int ste_lineno;
    int ste_col_offset;
    int ste_opt_lineno;
    int ste_opt_col_offset;
    int ste_tmpname;
    struct symtable *ste_table;
} PySTEntryObject;

extern PyTypeObject PySTEntry_Type;



int PyST_GetScope(PySTEntryObject *, PyObject *);

struct symtable * PySymtable_Build(
    mod_ty mod,
    const char *filename,
    PyFutureFeatures *future);
PySTEntryObject * PySymtable_Lookup(struct symtable *, void *);

void PySymtable_Free(struct symtable *);
# 31 "compile.c" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/opcode.h" 1
# 151 "/Users/parrt/tmp/Python-3.3.1/Include/opcode.h"
enum cmp_op {PyCmp_LT=0, PyCmp_LE=1, PyCmp_EQ=2, PyCmp_NE=3, PyCmp_GT=4, PyCmp_GE=5,
             PyCmp_IN, PyCmp_NOT_IN, PyCmp_IS, PyCmp_IS_NOT, PyCmp_EXC_MATCH, PyCmp_BAD};
# 32 "compile.c" 2

int Py_OptimizeFlag = 0;
# 45 "compile.c"
struct instr {
    unsigned i_jabs : 1;
    unsigned i_jrel : 1;
    unsigned i_hasarg : 1;
    unsigned char i_opcode;
    int i_oparg;
    struct basicblock_ *i_target;
    int i_lineno;
};

typedef struct basicblock_ {



    struct basicblock_ *b_list;

    int b_iused;

    int b_ialloc;

    struct instr *b_instr;


    struct basicblock_ *b_next;

    unsigned b_seen : 1;

    unsigned b_return : 1;

    int b_startdepth;

    int b_offset;
} basicblock;
# 86 "compile.c"
enum fblocktype { LOOP, EXCEPT, FINALLY_TRY, FINALLY_END };

struct fblockinfo {
    enum fblocktype fb_type;
    basicblock *fb_block;
};

enum {
    COMPILER_SCOPE_MODULE,
    COMPILER_SCOPE_CLASS,
    COMPILER_SCOPE_FUNCTION,
    COMPILER_SCOPE_COMPREHENSION,
};




struct compiler_unit {
    PySTEntryObject *u_ste;

    PyObject *u_name;
    PyObject *u_qualname;
    int u_scope_type;





    PyObject *u_consts;
    PyObject *u_names;
    PyObject *u_varnames;
    PyObject *u_cellvars;
    PyObject *u_freevars;

    PyObject *u_private;

    int u_argcount;
    int u_kwonlyargcount;


    basicblock *u_blocks;
    basicblock *u_curblock;

    int u_nfblocks;
    struct fblockinfo u_fblock[20];

    int u_firstlineno;
    int u_lineno;
    int u_col_offset;
    int u_lineno_set;

};
# 151 "compile.c"
struct compiler {
    const char *c_filename;
    PyObject *c_filename_obj;
    struct symtable *c_st;
    PyFutureFeatures *c_future;
    PyCompilerFlags *c_flags;

    int c_optimize;
    int c_interactive;
    int c_nestlevel;

    struct compiler_unit *u;
    PyObject *c_stack;
    PyArena *c_arena;
};

static int compiler_enter_scope(struct compiler *, identifier, int, void *, int);
static void compiler_free(struct compiler *);
static basicblock *compiler_new_block(struct compiler *);
static int compiler_next_instr(struct compiler *, basicblock *);
static int compiler_addop(struct compiler *, int);
static int compiler_addop_o(struct compiler *, int, PyObject *, PyObject *);
static int compiler_addop_i(struct compiler *, int, int);
static int compiler_addop_j(struct compiler *, int, basicblock *, int);
static basicblock *compiler_use_new_block(struct compiler *);
static int compiler_error(struct compiler *, const char *);
static int compiler_nameop(struct compiler *, identifier, expr_context_ty);

static PyCodeObject *compiler_mod(struct compiler *, mod_ty);
static int compiler_visit_stmt(struct compiler *, stmt_ty);
static int compiler_visit_keyword(struct compiler *, keyword_ty);
static int compiler_visit_expr(struct compiler *, expr_ty);
static int compiler_augassign(struct compiler *, stmt_ty);
static int compiler_visit_slice(struct compiler *, slice_ty,
                                expr_context_ty);

static int compiler_push_fblock(struct compiler *, enum fblocktype,
                                basicblock *);
static void compiler_pop_fblock(struct compiler *, enum fblocktype,
                                basicblock *);

static int compiler_in_loop(struct compiler *);

static int inplace_binop(struct compiler *, operator_ty);
static int expr_constant(struct compiler *, expr_ty);

static int compiler_with(struct compiler *, stmt_ty, int);
static int compiler_call_helper(struct compiler *c, int n,
                                asdl_seq *args,
                                asdl_seq *keywords,
                                expr_ty starargs,
                                expr_ty kwargs);
static int compiler_try_except(struct compiler *, stmt_ty);

static PyCodeObject *assemble(struct compiler *, int addNone);
static PyObject *__doc__;



PyObject *
_Py_Mangle(PyObject *privateobj, PyObject *ident)
{


    PyObject *result;
    size_t nlen, plen, ipriv;
    Py_UCS4 maxchar;
    if (privateobj == ((void *)0) || !((((((PyObject*)(privateobj))->ob_type))->tp_flags & ((1L<<28))) != 0) ||
        ((__builtin_expect(!(((((((PyObject*)(ident))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 219, "PyUnicode_Check(ident)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)ident)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 219, "PyUnicode_IS_READY(ident)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 219, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 219, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject *)((ident)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 219, "PyUnicode_Check((ident))") : (void)0), (((PyASCIIObject*)((ident)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 219, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 219, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject*)(ident))->state.ascii) ? ((void*)((PyASCIIObject*)((ident)) + 1)) : ((void*)((PyCompactUnicodeObject*)((ident)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((ident)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 219, "((PyUnicodeObject*)((ident)))->data.any") : (void)0), ((((PyUnicodeObject *)((ident)))->data.any))))))[(0)] : (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 219, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 219, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject *)((ident)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 219, "PyUnicode_Check((ident))") : (void)0), (((PyASCIIObject*)((ident)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 219, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 219, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject*)(ident))->state.ascii) ? ((void*)((PyASCIIObject*)((ident)) + 1)) : ((void*)((PyCompactUnicodeObject*)((ident)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((ident)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 219, "((PyUnicodeObject*)((ident)))->data.any") : (void)0), ((((PyUnicodeObject *)((ident)))->data.any))))))[(0)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 219, "PyUnicode_Check((ident))") : (void)0), (((PyASCIIObject*)((ident)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 219, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 219, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject*)(ident))->state.ascii) ? ((void*)((PyASCIIObject*)((ident)) + 1)) : ((void*)((PyCompactUnicodeObject*)((ident)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((ident)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 219, "((PyUnicodeObject*)((ident)))->data.any") : (void)0), ((((PyUnicodeObject *)((ident)))->data.any))))))[(0)] ) )) != '_' ||
        ((__builtin_expect(!(((((((PyObject*)(ident))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 220, "PyUnicode_Check(ident)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)ident)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 220, "PyUnicode_IS_READY(ident)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 220, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 220, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject *)((ident)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 220, "PyUnicode_Check((ident))") : (void)0), (((PyASCIIObject*)((ident)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 220, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 220, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject*)(ident))->state.ascii) ? ((void*)((PyASCIIObject*)((ident)) + 1)) : ((void*)((PyCompactUnicodeObject*)((ident)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((ident)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 220, "((PyUnicodeObject*)((ident)))->data.any") : (void)0), ((((PyUnicodeObject *)((ident)))->data.any))))))[(1)] : (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 220, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 220, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject *)((ident)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 220, "PyUnicode_Check((ident))") : (void)0), (((PyASCIIObject*)((ident)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 220, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 220, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject*)(ident))->state.ascii) ? ((void*)((PyASCIIObject*)((ident)) + 1)) : ((void*)((PyCompactUnicodeObject*)((ident)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((ident)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 220, "((PyUnicodeObject*)((ident)))->data.any") : (void)0), ((((PyUnicodeObject *)((ident)))->data.any))))))[(1)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 220, "PyUnicode_Check((ident))") : (void)0), (((PyASCIIObject*)((ident)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 220, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 220, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject*)(ident))->state.ascii) ? ((void*)((PyASCIIObject*)((ident)) + 1)) : ((void*)((PyCompactUnicodeObject*)((ident)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((ident)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 220, "((PyUnicodeObject*)((ident)))->data.any") : (void)0), ((((PyUnicodeObject *)((ident)))->data.any))))))[(1)] ) )) != '_') {
        ( ((PyObject*)(ident))->ob_refcnt++);
        return ident;
    }
    nlen = ((__builtin_expect(!(((((((PyObject*)(ident))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 224, "PyUnicode_Check(ident)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)ident)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 224, "PyUnicode_IS_READY(ident)") : (void)0), ((PyASCIIObject *)(ident))->length);
    plen = ((__builtin_expect(!(((((((PyObject*)(privateobj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 225, "PyUnicode_Check(privateobj)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)privateobj)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 225, "PyUnicode_IS_READY(privateobj)") : (void)0), ((PyASCIIObject *)(privateobj))->length);
# 235 "compile.c"
    if ((((__builtin_expect(!(((((((PyObject*)(ident))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 235, "PyUnicode_Check(ident)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)ident)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 235, "PyUnicode_IS_READY(ident)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 235, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 235, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject *)((ident)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 235, "PyUnicode_Check((ident))") : (void)0), (((PyASCIIObject*)((ident)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 235, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 235, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject*)(ident))->state.ascii) ? ((void*)((PyASCIIObject*)((ident)) + 1)) : ((void*)((PyCompactUnicodeObject*)((ident)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((ident)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 235, "((PyUnicodeObject*)((ident)))->data.any") : (void)0), ((((PyUnicodeObject *)((ident)))->data.any))))))[(nlen-1)] : (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 235, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 235, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject *)((ident)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 235, "PyUnicode_Check((ident))") : (void)0), (((PyASCIIObject*)((ident)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 235, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 235, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject*)(ident))->state.ascii) ? ((void*)((PyASCIIObject*)((ident)) + 1)) : ((void*)((PyCompactUnicodeObject*)((ident)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((ident)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 235, "((PyUnicodeObject*)((ident)))->data.any") : (void)0), ((((PyUnicodeObject *)((ident)))->data.any))))))[(nlen-1)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 235, "PyUnicode_Check((ident))") : (void)0), (((PyASCIIObject*)((ident)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 235, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 235, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject*)(ident))->state.ascii) ? ((void*)((PyASCIIObject*)((ident)) + 1)) : ((void*)((PyCompactUnicodeObject*)((ident)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((ident)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 235, "((PyUnicodeObject*)((ident)))->data.any") : (void)0), ((((PyUnicodeObject *)((ident)))->data.any))))))[(nlen-1)] ) )) == '_' &&
         ((__builtin_expect(!(((((((PyObject*)(ident))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 236, "PyUnicode_Check(ident)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)ident)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 236, "PyUnicode_IS_READY(ident)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 236, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 236, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject *)((ident)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 236, "PyUnicode_Check((ident))") : (void)0), (((PyASCIIObject*)((ident)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 236, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 236, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject*)(ident))->state.ascii) ? ((void*)((PyASCIIObject*)((ident)) + 1)) : ((void*)((PyCompactUnicodeObject*)((ident)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((ident)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 236, "((PyUnicodeObject*)((ident)))->data.any") : (void)0), ((((PyUnicodeObject *)((ident)))->data.any))))))[(nlen-2)] : (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 236, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 236, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject *)((ident)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 236, "PyUnicode_Check((ident))") : (void)0), (((PyASCIIObject*)((ident)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 236, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 236, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject*)(ident))->state.ascii) ? ((void*)((PyASCIIObject*)((ident)) + 1)) : ((void*)((PyCompactUnicodeObject*)((ident)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((ident)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 236, "((PyUnicodeObject*)((ident)))->data.any") : (void)0), ((((PyUnicodeObject *)((ident)))->data.any))))))[(nlen-2)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 236, "PyUnicode_Check((ident))") : (void)0), (((PyASCIIObject*)((ident)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((ident)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 236, "PyUnicode_Check((ident))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(ident))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 236, "PyUnicode_IS_READY((ident))") : (void)0), ((PyASCIIObject*)(ident))->state.ascii) ? ((void*)((PyASCIIObject*)((ident)) + 1)) : ((void*)((PyCompactUnicodeObject*)((ident)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((ident)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 236, "((PyUnicodeObject*)((ident)))->data.any") : (void)0), ((((PyUnicodeObject *)((ident)))->data.any))))))[(nlen-2)] ) )) == '_') ||
        PyUnicode_FindChar(ident, '.', 0, nlen, 1) != -1) {
        ( ((PyObject*)(ident))->ob_refcnt++);
        return ident;
    }

    ipriv = 0;
    while (((__builtin_expect(!(((((((PyObject*)(privateobj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 243, "PyUnicode_Check(privateobj)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)privateobj)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 243, "PyUnicode_IS_READY(privateobj)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((privateobj)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 243, "PyUnicode_Check((privateobj))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(privateobj))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 243, "PyUnicode_IS_READY((privateobj))") : (void)0), ((PyASCIIObject *)((privateobj)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((privateobj)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 243, "PyUnicode_Check((privateobj))") : (void)0), (((PyASCIIObject*)((privateobj)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((privateobj)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 243, "PyUnicode_Check((privateobj))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(privateobj))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 243, "PyUnicode_IS_READY((privateobj))") : (void)0), ((PyASCIIObject*)(privateobj))->state.ascii) ? ((void*)((PyASCIIObject*)((privateobj)) + 1)) : ((void*)((PyCompactUnicodeObject*)((privateobj)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((privateobj)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 243, "((PyUnicodeObject*)((privateobj)))->data.any") : (void)0), ((((PyUnicodeObject *)((privateobj)))->data.any))))))[(ipriv)] : (((__builtin_expect(!(((((((PyObject*)((privateobj)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 243, "PyUnicode_Check((privateobj))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(privateobj))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 243, "PyUnicode_IS_READY((privateobj))") : (void)0), ((PyASCIIObject *)((privateobj)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((privateobj)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 243, "PyUnicode_Check((privateobj))") : (void)0), (((PyASCIIObject*)((privateobj)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((privateobj)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 243, "PyUnicode_Check((privateobj))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(privateobj))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 243, "PyUnicode_IS_READY((privateobj))") : (void)0), ((PyASCIIObject*)(privateobj))->state.ascii) ? ((void*)((PyASCIIObject*)((privateobj)) + 1)) : ((void*)((PyCompactUnicodeObject*)((privateobj)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((privateobj)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 243, "((PyUnicodeObject*)((privateobj)))->data.any") : (void)0), ((((PyUnicodeObject *)((privateobj)))->data.any))))))[(ipriv)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((privateobj)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 243, "PyUnicode_Check((privateobj))") : (void)0), (((PyASCIIObject*)((privateobj)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((privateobj)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 243, "PyUnicode_Check((privateobj))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(privateobj))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 243, "PyUnicode_IS_READY((privateobj))") : (void)0), ((PyASCIIObject*)(privateobj))->state.ascii) ? ((void*)((PyASCIIObject*)((privateobj)) + 1)) : ((void*)((PyCompactUnicodeObject*)((privateobj)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((privateobj)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 243, "((PyUnicodeObject*)((privateobj)))->data.any") : (void)0), ((((PyUnicodeObject *)((privateobj)))->data.any))))))[(ipriv)] ) )) == '_')
        ipriv++;
    if (ipriv == plen) {
        ( ((PyObject*)(ident))->ob_refcnt++);
        return ident;
    }
    plen -= ipriv;

    (__builtin_expect(!(1 <= ((Py_ssize_t)(((size_t)-1)>>1)) - nlen), 0) ? __assert_rtn(__func__, "compile.c", 251, "1 <= PY_SSIZE_T_MAX - nlen") : (void)0);
    (__builtin_expect(!(1 + nlen <= ((Py_ssize_t)(((size_t)-1)>>1)) - plen), 0) ? __assert_rtn(__func__, "compile.c", 252, "1 + nlen <= PY_SSIZE_T_MAX - plen") : (void)0);

    maxchar = ((__builtin_expect(!((((PyASCIIObject*)ident)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 254, "PyUnicode_IS_READY(ident)") : (void)0), (((__builtin_expect(!(((((((PyObject*)(ident))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 254, "PyUnicode_Check(ident)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)ident)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 254, "PyUnicode_IS_READY(ident)") : (void)0), ((PyASCIIObject*)ident)->state.ascii) ? (0x7f) : (((__builtin_expect(!(((((((PyObject*)(ident))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 254, "PyUnicode_Check(ident)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)ident)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 254, "PyUnicode_IS_READY(ident)") : (void)0), ((PyASCIIObject *)(ident))->state.kind) == PyUnicode_1BYTE_KIND ? (0xffU) : (((__builtin_expect(!(((((((PyObject*)(ident))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 254, "PyUnicode_Check(ident)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)ident)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 254, "PyUnicode_IS_READY(ident)") : (void)0), ((PyASCIIObject *)(ident))->state.kind) == PyUnicode_2BYTE_KIND ? (0xffffU) : (0x10ffffU)))));
    if (((__builtin_expect(!((((PyASCIIObject*)privateobj)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 255, "PyUnicode_IS_READY(privateobj)") : (void)0), (((__builtin_expect(!(((((((PyObject*)(privateobj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 255, "PyUnicode_Check(privateobj)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)privateobj)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 255, "PyUnicode_IS_READY(privateobj)") : (void)0), ((PyASCIIObject*)privateobj)->state.ascii) ? (0x7f) : (((__builtin_expect(!(((((((PyObject*)(privateobj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 255, "PyUnicode_Check(privateobj)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)privateobj)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 255, "PyUnicode_IS_READY(privateobj)") : (void)0), ((PyASCIIObject *)(privateobj))->state.kind) == PyUnicode_1BYTE_KIND ? (0xffU) : (((__builtin_expect(!(((((((PyObject*)(privateobj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 255, "PyUnicode_Check(privateobj)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)privateobj)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 255, "PyUnicode_IS_READY(privateobj)") : (void)0), ((PyASCIIObject *)(privateobj))->state.kind) == PyUnicode_2BYTE_KIND ? (0xffffU) : (0x10ffffU))))) > maxchar)
        maxchar = ((__builtin_expect(!((((PyASCIIObject*)privateobj)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 256, "PyUnicode_IS_READY(privateobj)") : (void)0), (((__builtin_expect(!(((((((PyObject*)(privateobj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 256, "PyUnicode_Check(privateobj)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)privateobj)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 256, "PyUnicode_IS_READY(privateobj)") : (void)0), ((PyASCIIObject*)privateobj)->state.ascii) ? (0x7f) : (((__builtin_expect(!(((((((PyObject*)(privateobj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 256, "PyUnicode_Check(privateobj)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)privateobj)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 256, "PyUnicode_IS_READY(privateobj)") : (void)0), ((PyASCIIObject *)(privateobj))->state.kind) == PyUnicode_1BYTE_KIND ? (0xffU) : (((__builtin_expect(!(((((((PyObject*)(privateobj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 256, "PyUnicode_Check(privateobj)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)privateobj)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 256, "PyUnicode_IS_READY(privateobj)") : (void)0), ((PyASCIIObject *)(privateobj))->state.kind) == PyUnicode_2BYTE_KIND ? (0xffffU) : (0x10ffffU)))));

    result = PyUnicode_New(1 + nlen + plen, maxchar);
    if (!result)
        return 0;

    do { switch ((((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 262, "PyUnicode_Check(result)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)result)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 262, "PyUnicode_IS_READY(result)") : (void)0), ((PyASCIIObject *)(result))->state.kind))) { case PyUnicode_1BYTE_KIND: { ((Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 262, "PyUnicode_Check(result)") : (void)0), (((PyASCIIObject*)(result))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 262, "PyUnicode_Check(result)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)result)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 262, "PyUnicode_IS_READY(result)") : (void)0), ((PyASCIIObject*)result)->state.ascii) ? ((void*)((PyASCIIObject*)(result) + 1)) : ((void*)((PyCompactUnicodeObject*)(result) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)(result))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 262, "((PyUnicodeObject*)(result))->data.any") : (void)0), ((((PyUnicodeObject *)(result))->data.any))))))[(0)] = (Py_UCS1)('_'); break; } case PyUnicode_2BYTE_KIND: { ((Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 262, "PyUnicode_Check(result)") : (void)0), (((PyASCIIObject*)(result))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 262, "PyUnicode_Check(result)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)result)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 262, "PyUnicode_IS_READY(result)") : (void)0), ((PyASCIIObject*)result)->state.ascii) ? ((void*)((PyASCIIObject*)(result) + 1)) : ((void*)((PyCompactUnicodeObject*)(result) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)(result))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 262, "((PyUnicodeObject*)(result))->data.any") : (void)0), ((((PyUnicodeObject *)(result))->data.any))))))[(0)] = (Py_UCS2)('_'); break; } default: { (__builtin_expect(!((((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 262, "PyUnicode_Check(result)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)result)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 262, "PyUnicode_IS_READY(result)") : (void)0), ((PyASCIIObject *)(result))->state.kind)) == PyUnicode_4BYTE_KIND), 0) ? __assert_rtn(__func__, "compile.c", 262, "(((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, \"compile.c\", 262, \"PyUnicode_Check(result)\") : (void)0), (__builtin_expect(!((((PyASCIIObject*)result)->state.ready)), 0) ? __assert_rtn(__func__, \"compile.c\", 262, \"PyUnicode_IS_READY(result)\") : (void)0), ((PyASCIIObject *)(result))->state.kind)) == PyUnicode_4BYTE_KIND") : (void)0); ((Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 262, "PyUnicode_Check(result)") : (void)0), (((PyASCIIObject*)(result))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 262, "PyUnicode_Check(result)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)result)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 262, "PyUnicode_IS_READY(result)") : (void)0), ((PyASCIIObject*)result)->state.ascii) ? ((void*)((PyASCIIObject*)(result) + 1)) : ((void*)((PyCompactUnicodeObject*)(result) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)(result))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 262, "((PyUnicodeObject*)(result))->data.any") : (void)0), ((((PyUnicodeObject *)(result))->data.any))))))[(0)] = (Py_UCS4)('_'); } } } while (0);
    if (PyUnicode_CopyCharacters(result, 1, privateobj, ipriv, plen) < 0) {
        do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0);
        return ((void *)0);
    }
    if (PyUnicode_CopyCharacters(result, plen+1, ident, 0, nlen) < 0) {
        do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0);
        return ((void *)0);
    }
    (__builtin_expect(!(_PyUnicode_CheckConsistency(result, 1)), 0) ? __assert_rtn(__func__, "compile.c", 271, "_PyUnicode_CheckConsistency(result, 1)") : (void)0);
    return result;
}

static int
compiler_init(struct compiler *c)
{
    ((__builtin_object_size (c, 0) != (size_t) -1) ? __builtin___memset_chk (c, 0, sizeof(struct compiler), __builtin_object_size (c, 0)) : __inline_memset_chk (c, 0, sizeof(struct compiler)));

    c->c_stack = PyList_New(0);
    if (!c->c_stack)
        return 0;

    return 1;
}

PyCodeObject *
PyAST_CompileEx(mod_ty mod, const char *filename, PyCompilerFlags *flags,
                int optimize, PyArena *arena)
{
    struct compiler c;
    PyCodeObject *co = ((void *)0);
    PyCompilerFlags local_flags;
    int merged;

    if (!__doc__) {
        __doc__ = PyUnicode_InternFromString("__doc__");
        if (!__doc__)
            return ((void *)0);
    }

    if (!compiler_init(&c))
        return ((void *)0);
    c.c_filename = filename;
    c.c_filename_obj = PyUnicode_DecodeFSDefault(filename);
    if (!c.c_filename_obj)
        goto finally;
    c.c_arena = arena;
    c.c_future = PyFuture_FromAST(mod, filename);
    if (c.c_future == ((void *)0))
        goto finally;
    if (!flags) {
        local_flags.cf_flags = 0;
        flags = &local_flags;
    }
    merged = c.c_future->ff_features | flags->cf_flags;
    c.c_future->ff_features = merged;
    flags->cf_flags = merged;
    c.c_flags = flags;
    c.c_optimize = (optimize == -1) ? Py_OptimizeFlag : optimize;
    c.c_nestlevel = 0;

    c.c_st = PySymtable_Build(mod, filename, c.c_future);
    if (c.c_st == ((void *)0)) {
        if (!PyErr_Occurred())
            PyErr_SetString(PyExc_SystemError, "no symtable");
        goto finally;
    }

    co = compiler_mod(&c, mod);

 finally:
    compiler_free(&c);
    (__builtin_expect(!(co || PyErr_Occurred()), 0) ? __assert_rtn(__func__, "compile.c", 334, "co || PyErr_Occurred()") : (void)0);
    return co;
}

PyCodeObject *
PyNode_Compile(struct _node *n, const char *filename)
{
    PyCodeObject *co = ((void *)0);
    mod_ty mod;
    PyArena *arena = PyArena_New();
    if (!arena)
        return ((void *)0);
    mod = PyAST_FromNode(n, ((void *)0), filename, arena);
    if (mod)
        co = PyAST_CompileEx(mod, filename, ((void *)0), -1, arena);
    PyArena_Free(arena);
    return co;
}

static void
compiler_free(struct compiler *c)
{
    if (c->c_st)
        PySymtable_Free(c->c_st);
    if (c->c_future)
        PyObject_Free(c->c_future);
    if (c->c_filename_obj)
        do { if ( --((PyObject*)(c->c_filename_obj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(c->c_filename_obj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(c->c_filename_obj)))); } while (0);
    do { if ( --((PyObject*)(c->c_stack))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(c->c_stack)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(c->c_stack)))); } while (0);
}

static PyObject *
list2dict(PyObject *list)
{
    Py_ssize_t i, n;
    PyObject *v, *k;
    PyObject *dict = PyDict_New();
    if (!dict) return ((void *)0);

    n = PyList_Size(list);
    for (i = 0; i < n; i++) {
        v = PyLong_FromLong(i);
        if (!v) {
            do { if ( --((PyObject*)(dict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dict)))); } while (0);
            return ((void *)0);
        }
        k = (((PyListObject *)(list))->ob_item[i]);
        k = PyTuple_Pack(2, k, k->ob_type);
        if (k == ((void *)0) || PyDict_SetItem(dict, k, v) < 0) {
            do { if ((k) == ((void *)0)) ; else do { if ( --((PyObject*)(k))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(k)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(k)))); } while (0); } while (0);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if ( --((PyObject*)(dict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dict)))); } while (0);
            return ((void *)0);
        }
        do { if ( --((PyObject*)(k))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(k)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(k)))); } while (0);
        do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
    }
    return dict;
}
# 402 "compile.c"
static PyObject *
dictbytype(PyObject *src, int scope_type, int flag, int offset)
{
    Py_ssize_t i = offset, scope, num_keys, key_i;
    PyObject *k, *v, *dest = PyDict_New();
    PyObject *sorted_keys;

    (__builtin_expect(!(offset >= 0), 0) ? __assert_rtn(__func__, "compile.c", 409, "offset >= 0") : (void)0);
    if (dest == ((void *)0))
        return ((void *)0);






    sorted_keys = PyDict_Keys(src);
    if (sorted_keys == ((void *)0))
        return ((void *)0);
    if (PyList_Sort(sorted_keys) != 0) {
        do { if ( --((PyObject*)(sorted_keys))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sorted_keys)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sorted_keys)))); } while (0);
        return ((void *)0);
    }
    num_keys = (((PyVarObject*)(sorted_keys))->ob_size);

    for (key_i = 0; key_i < num_keys; key_i++) {

        long vi;
        k = (((PyListObject *)(sorted_keys))->ob_item[key_i]);
        v = PyDict_GetItem(src, k);
        (__builtin_expect(!(((((((PyObject*)(v))->ob_type))->tp_flags & ((1L<<24))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 432, "PyLong_Check(v)") : (void)0);
        vi = PyLong_AsLong(v);
        scope = (vi >> 11) & (1 | 2 | 2<<1 | 2<<2);

        if (scope == scope_type || vi & flag) {
            PyObject *tuple, *item = PyLong_FromLong(i);
            if (item == ((void *)0)) {
                do { if ( --((PyObject*)(sorted_keys))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sorted_keys)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sorted_keys)))); } while (0);
                do { if ( --((PyObject*)(dest))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dest)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dest)))); } while (0);
                return ((void *)0);
            }
            i++;
            tuple = PyTuple_Pack(2, k, k->ob_type);
            if (!tuple || PyDict_SetItem(dest, tuple, item) < 0) {
                do { if ( --((PyObject*)(sorted_keys))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sorted_keys)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sorted_keys)))); } while (0);
                do { if ( --((PyObject*)(item))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(item)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(item)))); } while (0);
                do { if ( --((PyObject*)(dest))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dest)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dest)))); } while (0);
                do { if ((tuple) == ((void *)0)) ; else do { if ( --((PyObject*)(tuple))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tuple)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tuple)))); } while (0); } while (0);
                return ((void *)0);
            }
            do { if ( --((PyObject*)(item))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(item)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(item)))); } while (0);
            do { if ( --((PyObject*)(tuple))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tuple)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tuple)))); } while (0);
        }
    }
    do { if ( --((PyObject*)(sorted_keys))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sorted_keys)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sorted_keys)))); } while (0);
    return dest;
}

static void
compiler_unit_check(struct compiler_unit *u)
{
    basicblock *block;
    for (block = u->u_blocks; block != ((void *)0); block = block->b_list) {
        (__builtin_expect(!((void *)block != (void *)0xcbcbcbcb), 0) ? __assert_rtn(__func__, "compile.c", 465, "(void *)block != (void *)0xcbcbcbcb") : (void)0);
        (__builtin_expect(!((void *)block != (void *)0xfbfbfbfb), 0) ? __assert_rtn(__func__, "compile.c", 466, "(void *)block != (void *)0xfbfbfbfb") : (void)0);
        (__builtin_expect(!((void *)block != (void *)0xdbdbdbdb), 0) ? __assert_rtn(__func__, "compile.c", 467, "(void *)block != (void *)0xdbdbdbdb") : (void)0);
        if (block->b_instr != ((void *)0)) {
            (__builtin_expect(!(block->b_ialloc > 0), 0) ? __assert_rtn(__func__, "compile.c", 469, "block->b_ialloc > 0") : (void)0);
            (__builtin_expect(!(block->b_iused > 0), 0) ? __assert_rtn(__func__, "compile.c", 470, "block->b_iused > 0") : (void)0);
            (__builtin_expect(!(block->b_ialloc >= block->b_iused), 0) ? __assert_rtn(__func__, "compile.c", 471, "block->b_ialloc >= block->b_iused") : (void)0);
        }
        else {
            (__builtin_expect(!(block->b_iused == 0), 0) ? __assert_rtn(__func__, "compile.c", 474, "block->b_iused == 0") : (void)0);
            (__builtin_expect(!(block->b_ialloc == 0), 0) ? __assert_rtn(__func__, "compile.c", 475, "block->b_ialloc == 0") : (void)0);
        }
    }
}

static void
compiler_unit_free(struct compiler_unit *u)
{
    basicblock *b, *next;

    compiler_unit_check(u);
    b = u->u_blocks;
    while (b != ((void *)0)) {
        if (b->b_instr)
            PyObject_Free((void *)b->b_instr);
        next = b->b_list;
        PyObject_Free((void *)b);
        b = next;
    }
    do { if (u->u_ste) { PyObject *_py_tmp = (PyObject *)(u->u_ste); (u->u_ste) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (u->u_name) { PyObject *_py_tmp = (PyObject *)(u->u_name); (u->u_name) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (u->u_qualname) { PyObject *_py_tmp = (PyObject *)(u->u_qualname); (u->u_qualname) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (u->u_consts) { PyObject *_py_tmp = (PyObject *)(u->u_consts); (u->u_consts) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (u->u_names) { PyObject *_py_tmp = (PyObject *)(u->u_names); (u->u_names) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (u->u_varnames) { PyObject *_py_tmp = (PyObject *)(u->u_varnames); (u->u_varnames) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (u->u_freevars) { PyObject *_py_tmp = (PyObject *)(u->u_freevars); (u->u_freevars) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (u->u_cellvars) { PyObject *_py_tmp = (PyObject *)(u->u_cellvars); (u->u_cellvars) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (u->u_private) { PyObject *_py_tmp = (PyObject *)(u->u_private); (u->u_private) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    PyObject_Free(u);
}

static int
compiler_enter_scope(struct compiler *c, identifier name,
                     int scope_type, void *key, int lineno)
{
    struct compiler_unit *u;

    u = (struct compiler_unit *)PyObject_Malloc(sizeof(
                                            struct compiler_unit));
    if (!u) {
        PyErr_NoMemory();
        return 0;
    }
    ((__builtin_object_size (u, 0) != (size_t) -1) ? __builtin___memset_chk (u, 0, sizeof(struct compiler_unit), __builtin_object_size (u, 0)) : __inline_memset_chk (u, 0, sizeof(struct compiler_unit)));
    u->u_scope_type = scope_type;
    u->u_argcount = 0;
    u->u_kwonlyargcount = 0;
    u->u_ste = PySymtable_Lookup(c->c_st, key);
    if (!u->u_ste) {
        compiler_unit_free(u);
        return 0;
    }
    ( ((PyObject*)(name))->ob_refcnt++);
    u->u_name = name;
    u->u_varnames = list2dict(u->u_ste->ste_varnames);
    u->u_cellvars = dictbytype(u->u_ste->ste_symbols, 5, 0, 0);
    if (!u->u_varnames || !u->u_cellvars) {
        compiler_unit_free(u);
        return 0;
    }

    u->u_freevars = dictbytype(u->u_ste->ste_symbols, 4, 2<<5,
                               PyDict_Size(u->u_cellvars));
    if (!u->u_freevars) {
        compiler_unit_free(u);
        return 0;
    }

    u->u_blocks = ((void *)0);
    u->u_nfblocks = 0;
    u->u_firstlineno = lineno;
    u->u_lineno = 0;
    u->u_col_offset = 0;
    u->u_lineno_set = 0;
    u->u_consts = PyDict_New();
    if (!u->u_consts) {
        compiler_unit_free(u);
        return 0;
    }
    u->u_names = PyDict_New();
    if (!u->u_names) {
        compiler_unit_free(u);
        return 0;
    }

    u->u_private = ((void *)0);


    if (c->u) {
        PyObject *capsule = PyCapsule_New(c->u, "compile.c compiler unit", ((void *)0));
        if (!capsule || PyList_Append(c->c_stack, capsule) < 0) {
            do { if ((capsule) == ((void *)0)) ; else do { if ( --((PyObject*)(capsule))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(capsule)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(capsule)))); } while (0); } while (0);
            compiler_unit_free(u);
            return 0;
        }
        do { if ( --((PyObject*)(capsule))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(capsule)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(capsule)))); } while (0);
        u->u_private = c->u->u_private;
        do { if ((u->u_private) == ((void *)0)) ; else ( ((PyObject*)(u->u_private))->ob_refcnt++); } while (0);
    }
    c->u = u;

    c->c_nestlevel++;
    if (compiler_use_new_block(c) == ((void *)0))
        return 0;

    return 1;
}

static void
compiler_exit_scope(struct compiler *c)
{
    int n;
    PyObject *capsule;

    c->c_nestlevel--;
    compiler_unit_free(c->u);

    n = (((PyVarObject*)(c->c_stack))->ob_size) - 1;
    if (n >= 0) {
        capsule = (((PyListObject *)(c->c_stack))->ob_item[n]);
        c->u = (struct compiler_unit *)PyCapsule_GetPointer(capsule, "compile.c compiler unit");
        (__builtin_expect(!(c->u), 0) ? __assert_rtn(__func__, "compile.c", 596, "c->u") : (void)0);

        if (PySequence_DelItem(c->c_stack, n) < 0)
            Py_FatalError("compiler_exit_scope()");
        compiler_unit_check(c->u);
    }
    else
        c->u = ((void *)0);

}

static PyObject *
compiler_scope_qualname(struct compiler *c)
{
    Py_ssize_t stack_size, i;
    static _Py_Identifier dot = { 0, ".", 0 };
    static _Py_Identifier locals = { 0, "<locals>", 0 };
    struct compiler_unit *u;
    PyObject *capsule, *name, *seq, *dot_str, *locals_str;

    u = c->u;
    if (u->u_qualname != ((void *)0)) {
        ( ((PyObject*)(u->u_qualname))->ob_refcnt++);
        return u->u_qualname;
    }

    seq = PyList_New(0);
    if (seq == ((void *)0))
        return ((void *)0);

    stack_size = (((PyVarObject*)(c->c_stack))->ob_size);
    for (i = 0; i < stack_size; i++) {
        capsule = (((PyListObject *)(c->c_stack))->ob_item[i]);
        u = (struct compiler_unit *)PyCapsule_GetPointer(capsule, "compile.c compiler unit");
        (__builtin_expect(!(u), 0) ? __assert_rtn(__func__, "compile.c", 630, "u") : (void)0);
        if (u->u_scope_type == COMPILER_SCOPE_MODULE)
            continue;
        if (PyList_Append(seq, u->u_name))
            goto _error;
        if (u->u_scope_type == COMPILER_SCOPE_FUNCTION) {
            locals_str = _PyUnicode_FromId(&locals);
            if (locals_str == ((void *)0))
                goto _error;
            if (PyList_Append(seq, locals_str))
                goto _error;
        }
    }
    u = c->u;
    if (PyList_Append(seq, u->u_name))
        goto _error;
    dot_str = _PyUnicode_FromId(&dot);
    if (dot_str == ((void *)0))
        goto _error;
    name = PyUnicode_Join(dot_str, seq);
    do { if ( --((PyObject*)(seq))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(seq)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(seq)))); } while (0);
    u->u_qualname = name;
    do { if ((name) == ((void *)0)) ; else ( ((PyObject*)(name))->ob_refcnt++); } while (0);
    return name;

_error:
    do { if ((seq) == ((void *)0)) ; else do { if ( --((PyObject*)(seq))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(seq)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(seq)))); } while (0); } while (0);
    return ((void *)0);
}





static basicblock *
compiler_new_block(struct compiler *c)
{
    basicblock *b;
    struct compiler_unit *u;

    u = c->u;
    b = (basicblock *)PyObject_Malloc(sizeof(basicblock));
    if (b == ((void *)0)) {
        PyErr_NoMemory();
        return ((void *)0);
    }
    ((__builtin_object_size ((void *)b, 0) != (size_t) -1) ? __builtin___memset_chk ((void *)b, 0, sizeof(basicblock), __builtin_object_size ((void *)b, 0)) : __inline_memset_chk ((void *)b, 0, sizeof(basicblock)));

    b->b_list = u->u_blocks;
    u->u_blocks = b;
    return b;
}

static basicblock *
compiler_use_new_block(struct compiler *c)
{
    basicblock *block = compiler_new_block(c);
    if (block == ((void *)0))
        return ((void *)0);
    c->u->u_curblock = block;
    return block;
}

static basicblock *
compiler_next_block(struct compiler *c)
{
    basicblock *block = compiler_new_block(c);
    if (block == ((void *)0))
        return ((void *)0);
    c->u->u_curblock->b_next = block;
    c->u->u_curblock = block;
    return block;
}

static basicblock *
compiler_use_next_block(struct compiler *c, basicblock *block)
{
    (__builtin_expect(!(block != ((void *)0)), 0) ? __assert_rtn(__func__, "compile.c", 707, "block != NULL") : (void)0);
    c->u->u_curblock->b_next = block;
    c->u->u_curblock = block;
    return block;
}






static int
compiler_next_instr(struct compiler *c, basicblock *b)
{
    (__builtin_expect(!(b != ((void *)0)), 0) ? __assert_rtn(__func__, "compile.c", 721, "b != NULL") : (void)0);
    if (b->b_instr == ((void *)0)) {
        b->b_instr = (struct instr *)PyObject_Malloc(
                         sizeof(struct instr) * 16);
        if (b->b_instr == ((void *)0)) {
            PyErr_NoMemory();
            return -1;
        }
        b->b_ialloc = 16;
        ((__builtin_object_size ((char *)b->b_instr, 0) != (size_t) -1) ? __builtin___memset_chk ((char *)b->b_instr, 0, sizeof(struct instr) * 16, __builtin_object_size ((char *)b->b_instr, 0)) : __inline_memset_chk ((char *)b->b_instr, 0, sizeof(struct instr) * 16));

    }
    else if (b->b_iused == b->b_ialloc) {
        struct instr *tmp;
        size_t oldsize, newsize;
        oldsize = b->b_ialloc * sizeof(struct instr);
        newsize = oldsize << 1;

        if (oldsize > (18446744073709551615ULL >> 1)) {
            PyErr_NoMemory();
            return -1;
        }

        if (newsize == 0) {
            PyErr_NoMemory();
            return -1;
        }
        b->b_ialloc <<= 1;
        tmp = (struct instr *)PyObject_Realloc(
                                        (void *)b->b_instr, newsize);
        if (tmp == ((void *)0)) {
            PyErr_NoMemory();
            return -1;
        }
        b->b_instr = tmp;
        ((__builtin_object_size ((char *)b->b_instr + oldsize, 0) != (size_t) -1) ? __builtin___memset_chk ((char *)b->b_instr + oldsize, 0, newsize - oldsize, __builtin_object_size ((char *)b->b_instr + oldsize, 0)) : __inline_memset_chk ((char *)b->b_instr + oldsize, 0, newsize - oldsize));
    }
    return b->b_iused++;
}
# 773 "compile.c"
static void
compiler_set_lineno(struct compiler *c, int off)
{
    basicblock *b;
    if (c->u->u_lineno_set)
        return;
    c->u->u_lineno_set = 1;
    b = c->u->u_curblock;
    b->b_instr[off].i_lineno = c->u->u_lineno;
}

static int
opcode_stack_effect(int opcode, int oparg)
{
    switch (opcode) {
        case 1:
            return -1;
        case 2:
        case 3:
            return 0;
        case 4:
            return 1;
        case 5:
            return 2;

        case 10:
        case 11:
        case 12:
        case 15:
            return 0;

        case 146:
        case 145:
            return -1;
        case 147:
            return -2;

        case 19:
        case 20:
        case 22:
        case 23:
        case 24:
        case 25:
        case 26:
        case 27:
            return -1;
        case 28:
        case 29:
            return -1;

        case 55:
        case 56:
        case 57:
        case 59:
            return -1;
        case 60:
            return -3;
        case 54:
            return -2;
        case 61:
            return -2;

        case 62:
        case 63:
        case 64:
        case 65:
        case 66:
            return -1;
        case 67:
            return -1;
        case 68:
            return 0;

        case 70:
            return -1;
        case 71:
            return 1;
        case 75:
        case 76:
        case 77:
        case 78:
        case 79:
            return -1;
        case 80:
            return 0;
        case 143:
            return 7;
        case 81:
            return -1;
        case 69:
            return -1;
        case 83:
            return -1;
        case 84:
            return -1;
        case 86:
            return 0;
        case 72:
            return -1;
        case 87:
            return 0;
        case 89:
            return 0;
        case 88:
            return -1;

        case 90:
            return -1;
        case 91:
            return 0;
        case 92:
            return oparg-1;
        case 94:
            return (oparg&0xFF) + (oparg>>8);
        case 93:
            return 1;

        case 95:
            return -2;
        case 96:
            return -1;
        case 97:
            return -1;
        case 98:
            return 0;
        case 100:
            return 1;
        case 101:
            return 1;
        case 102:
        case 103:
        case 104:
            return 1-oparg;
        case 105:
            return 1;
        case 106:
            return 0;
        case 107:
            return -1;
        case 108:
            return -1;
        case 109:
            return 1;

        case 110:
        case 112:
        case 111:
        case 113:
            return 0;

        case 114:
        case 115:
            return -1;

        case 116:
            return 1;

        case 119:
            return 0;
        case 120:
            return 0;
        case 121:
        case 122:
            return 6;


        case 124:
            return 1;
        case 125:
            return -1;
        case 126:
            return 0;

        case 130:
            return -oparg;

        case 131:
            return -(((oparg) % 256) + 2*(((oparg) / 256) % 256));
        case 140:
        case 141:
            return -(((oparg) % 256) + 2*(((oparg) / 256) % 256))-1;
        case 142:
            return -(((oparg) % 256) + 2*(((oparg) / 256) % 256))-2;
        case 132:
            return -1 -(((oparg) % 256) + 2*(((oparg) / 256) % 256)) - ((oparg >> 16) & 0xffff);
        case 134:
            return -2 - (((oparg) % 256) + 2*(((oparg) / 256) % 256)) - ((oparg >> 16) & 0xffff);

        case 133:
            if (oparg == 3)
                return -2;
            else
                return -1;

        case 135:
            return 1;
        case 136:
            return 1;
        case 137:
            return -1;
        case 138:
            return 0;
        default:
            fprintf(__stderrp, "opcode = %d\n", opcode);
            Py_FatalError("opcode_stack_effect()");

    }
    return 0;
}





static int
compiler_addop(struct compiler *c, int opcode)
{
    basicblock *b;
    struct instr *i;
    int off;
    off = compiler_next_instr(c, c->u->u_curblock);
    if (off < 0)
        return 0;
    b = c->u->u_curblock;
    i = &b->b_instr[off];
    i->i_opcode = opcode;
    i->i_hasarg = 0;
    if (opcode == 83)
        b->b_return = 1;
    compiler_set_lineno(c, off);
    return 1;
}

static int
compiler_add_o(struct compiler *c, PyObject *dict, PyObject *o)
{
    PyObject *t, *v;
    Py_ssize_t arg;
    double d;



    if (((((PyObject*)(o))->ob_type) == (&PyFloat_Type) || PyType_IsSubtype((((PyObject*)(o))->ob_type), (&PyFloat_Type)))) {
        d = (((PyFloatObject *)(o))->ob_fval);



        if (d == 0.0 && copysign(1.0, d) < 0.0)
            t = PyTuple_Pack(3, o, o->ob_type, (&_Py_NoneStruct));
        else
            t = PyTuple_Pack(2, o, o->ob_type);
    }
    else if (((((PyObject*)(o))->ob_type) == (&PyComplex_Type) || PyType_IsSubtype((((PyObject*)(o))->ob_type), (&PyComplex_Type)))) {
        Py_complex z;
        int real_negzero, imag_negzero;




        z = PyComplex_AsCComplex(o);
        real_negzero = z.real == 0.0 && copysign(1.0, z.real) < 0.0;
        imag_negzero = z.imag == 0.0 && copysign(1.0, z.imag) < 0.0;
        if (real_negzero && imag_negzero) {
            t = PyTuple_Pack(5, o, o->ob_type,
                             (&_Py_NoneStruct), (&_Py_NoneStruct), (&_Py_NoneStruct));
        }
        else if (imag_negzero) {
            t = PyTuple_Pack(4, o, o->ob_type, (&_Py_NoneStruct), (&_Py_NoneStruct));
        }
        else if (real_negzero) {
            t = PyTuple_Pack(3, o, o->ob_type, (&_Py_NoneStruct));
        }
        else {
            t = PyTuple_Pack(2, o, o->ob_type);
        }
    }
    else {
        t = PyTuple_Pack(2, o, o->ob_type);
    }
    if (t == ((void *)0))
        return -1;

    v = PyDict_GetItem(dict, t);
    if (!v) {
        if (PyErr_Occurred())
            return -1;
        arg = PyDict_Size(dict);
        v = PyLong_FromLong(arg);
        if (!v) {
            do { if ( --((PyObject*)(t))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(t)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(t)))); } while (0);
            return -1;
        }
        if (PyDict_SetItem(dict, t, v) < 0) {
            do { if ( --((PyObject*)(t))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(t)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(t)))); } while (0);
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            return -1;
        }
        do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
    }
    else
        arg = PyLong_AsLong(v);
    do { if ( --((PyObject*)(t))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(t)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(t)))); } while (0);
    return arg;
}

static int
compiler_addop_o(struct compiler *c, int opcode, PyObject *dict,
                     PyObject *o)
{
    int arg = compiler_add_o(c, dict, o);
    if (arg < 0)
        return 0;
    return compiler_addop_i(c, opcode, arg);
}

static int
compiler_addop_name(struct compiler *c, int opcode, PyObject *dict,
                    PyObject *o)
{
    int arg;
    PyObject *mangled = _Py_Mangle(c->u->u_private, o);
    if (!mangled)
        return 0;
    arg = compiler_add_o(c, dict, mangled);
    do { if ( --((PyObject*)(mangled))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(mangled)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(mangled)))); } while (0);
    if (arg < 0)
        return 0;
    return compiler_addop_i(c, opcode, arg);
}





static int
compiler_addop_i(struct compiler *c, int opcode, int oparg)
{
    struct instr *i;
    int off;
    off = compiler_next_instr(c, c->u->u_curblock);
    if (off < 0)
        return 0;
    i = &c->u->u_curblock->b_instr[off];
    i->i_opcode = opcode;
    i->i_oparg = oparg;
    i->i_hasarg = 1;
    compiler_set_lineno(c, off);
    return 1;
}

static int
compiler_addop_j(struct compiler *c, int opcode, basicblock *b, int absolute)
{
    struct instr *i;
    int off;

    (__builtin_expect(!(b != ((void *)0)), 0) ? __assert_rtn(__func__, "compile.c", 1129, "b != NULL") : (void)0);
    off = compiler_next_instr(c, c->u->u_curblock);
    if (off < 0)
        return 0;
    i = &c->u->u_curblock->b_instr[off];
    i->i_opcode = opcode;
    i->i_target = b;
    i->i_hasarg = 1;
    if (absolute)
        i->i_jabs = 1;
    else
        i->i_jrel = 1;
    compiler_set_lineno(c, off);
    return 1;
}
# 1246 "compile.c"
static int
compiler_isdocstring(stmt_ty s)
{
    if (s->kind != Expr_kind)
        return 0;
    return s->v.Expr.value->kind == Str_kind;
}



static int
compiler_body(struct compiler *c, asdl_seq *stmts)
{
    int i = 0;
    stmt_ty st;

    if (!((stmts) == ((void *)0) ? 0 : (stmts)->size))
        return 1;
    st = (stmt_ty)(stmts)->elements[(0)];
    if (compiler_isdocstring(st) && c->c_optimize < 2) {

        i = 1;
        { if (!compiler_visit_expr((c), (st->v.Expr.value))) return 0; };
        if (!compiler_nameop(c, __doc__, Store))
            return 0;
    }
    for (; i < ((stmts) == ((void *)0) ? 0 : (stmts)->size); i++)
        { if (!compiler_visit_stmt((c), ((stmt_ty)(stmts)->elements[(i)]))) return 0; };
    return 1;
}

static PyCodeObject *
compiler_mod(struct compiler *c, mod_ty mod)
{
    PyCodeObject *co;
    int addNone = 1;
    static PyObject *module;
    if (!module) {
        module = PyUnicode_InternFromString("<module>");
        if (!module)
            return ((void *)0);
    }

    if (!compiler_enter_scope(c, module, COMPILER_SCOPE_MODULE, mod, 0))
        return ((void *)0);
    switch (mod->kind) {
    case Module_kind:
        if (!compiler_body(c, mod->v.Module.body)) {
            compiler_exit_scope(c);
            return 0;
        }
        break;
    case Interactive_kind:
        c->c_interactive = 1;
        { int _i; asdl_seq *seq = (mod->v.Interactive.body); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { stmt_ty elt = (stmt_ty)(seq)->elements[(_i)]; if (!compiler_visit_stmt((c), elt)) { compiler_exit_scope(c); return 0; } } };

        break;
    case Expression_kind:
        { if (!compiler_visit_expr((c), (mod->v.Expression.body))) { compiler_exit_scope(c); return 0; } };
        addNone = 0;
        break;
    case Suite_kind:
        PyErr_SetString(PyExc_SystemError,
                        "suite should not be possible");
        return 0;
    default:
        PyErr_Format(PyExc_SystemError,
                     "module kind %d should not be possible",
                     mod->kind);
        return 0;
    }
    co = assemble(c, addNone);
    compiler_exit_scope(c);
    return co;
}






static int
get_ref_type(struct compiler *c, PyObject *name)
{
    int scope = PyST_GetScope(c->u->u_ste, name);
    if (scope == 0) {
        char buf[350];
        PyOS_snprintf(buf, sizeof(buf),
                      "unknown scope for %.100s in %.100s(%s) in %s\n"
                      "symbols: %s\nlocals: %s\nglobals: %s",
                      ((__builtin_expect(!(((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 1336, "PyBytes_Check(name)") : (void)0), (((PyBytesObject *)(name))->ob_sval)),
                      ((__builtin_expect(!(((((((PyObject*)(c->u->u_name))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 1337, "PyBytes_Check(c->u->u_name)") : (void)0), (((PyBytesObject *)(c->u->u_name))->ob_sval)),
                      PyUnicode_AsUTF8(PyObject_Repr(c->u->u_ste->ste_id)),
                      c->c_filename,
                      PyUnicode_AsUTF8(PyObject_Repr(c->u->u_ste->ste_symbols)),
                      PyUnicode_AsUTF8(PyObject_Repr(c->u->u_varnames)),
                      PyUnicode_AsUTF8(PyObject_Repr(c->u->u_names))
        );
        Py_FatalError(buf);
    }

    return scope;
}

static int
compiler_lookup_arg(PyObject *dict, PyObject *name)
{
    PyObject *k, *v;
    k = PyTuple_Pack(2, name, name->ob_type);
    if (k == ((void *)0))
        return -1;
    v = PyDict_GetItem(dict, k);
    do { if ( --((PyObject*)(k))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(k)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(k)))); } while (0);
    if (v == ((void *)0))
        return -1;
    return PyLong_AsLong(v);
}

static int
compiler_make_closure(struct compiler *c, PyCodeObject *co, int args, PyObject *qualname)
{
    int i, free = ((((PyVarObject*)((co)->co_freevars))->ob_size));
    if (qualname == ((void *)0))
        qualname = co->co_name;

    if (free == 0) {
        { if (!compiler_addop_o((c), (100), (c)->u->u_consts, ((PyObject*)co))) return 0; };
        { if (!compiler_addop_o((c), (100), (c)->u->u_consts, (qualname))) return 0; };
        { if (!compiler_addop_i((c), (132), (args))) return 0; };
        return 1;
    }
    for (i = 0; i < free; ++i) {



        PyObject *name = (((PyTupleObject *)(co->co_freevars))->ob_item[i]);
        int arg, reftype;







        reftype = get_ref_type(c, name);
        if (reftype == 5)
            arg = compiler_lookup_arg(c->u->u_cellvars, name);
        else
            arg = compiler_lookup_arg(c->u->u_freevars, name);
        if (arg == -1) {
            fprintf(__stderrp,
                "lookup %s in %s %d %d\n"
                "freevars of %s: %s\n",
                PyUnicode_AsUTF8(PyObject_Repr(name)),
                ((__builtin_expect(!(((((((PyObject*)(c->u->u_name))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 1400, "PyBytes_Check(c->u->u_name)") : (void)0), (((PyBytesObject *)(c->u->u_name))->ob_sval)),
                reftype, arg,
                PyUnicode_AsUTF8(co->co_name),
                PyUnicode_AsUTF8(PyObject_Repr(co->co_freevars)));
            Py_FatalError("compiler_make_closure()");
        }
        { if (!compiler_addop_i((c), (135), (arg))) return 0; };
    }
    { if (!compiler_addop_i((c), (102), (free))) return 0; };
    { if (!compiler_addop_o((c), (100), (c)->u->u_consts, ((PyObject*)co))) return 0; };
    { if (!compiler_addop_o((c), (100), (c)->u->u_consts, (qualname))) return 0; };
    { if (!compiler_addop_i((c), (134), (args))) return 0; };
    return 1;
}

static int
compiler_decorators(struct compiler *c, asdl_seq* decos)
{
    int i;

    if (!decos)
        return 1;

    for (i = 0; i < ((decos) == ((void *)0) ? 0 : (decos)->size); i++) {
        { if (!compiler_visit_expr((c), ((expr_ty)(decos)->elements[(i)]))) return 0; };
    }
    return 1;
}

static int
compiler_visit_kwonlydefaults(struct compiler *c, asdl_seq *kwonlyargs,
                              asdl_seq *kw_defaults)
{
    int i, default_count = 0;
    for (i = 0; i < ((kwonlyargs) == ((void *)0) ? 0 : (kwonlyargs)->size); i++) {
        arg_ty arg = (kwonlyargs)->elements[(i)];
        expr_ty default_ = (kw_defaults)->elements[(i)];
        if (default_) {
            PyObject *mangled = _Py_Mangle(c->u->u_private, arg->arg);
            if (!mangled)
                return -1;
            { if (!compiler_addop_o((c), (100), (c)->u->u_consts, (mangled))) return 0; };
            do { if ( --((PyObject*)(mangled))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(mangled)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(mangled)))); } while (0);
            if (!compiler_visit_expr(c, default_)) {
                return -1;
            }
            default_count++;
        }
    }
    return default_count;
}

static int
compiler_visit_argannotation(struct compiler *c, identifier id,
    expr_ty annotation, PyObject *names)
{
    if (annotation) {
        { if (!compiler_visit_expr((c), (annotation))) return 0; };
        if (PyList_Append(names, id))
            return -1;
    }
    return 0;
}

static int
compiler_visit_argannotations(struct compiler *c, asdl_seq* args,
                              PyObject *names)
{
    int i, error;
    for (i = 0; i < ((args) == ((void *)0) ? 0 : (args)->size); i++) {
        arg_ty arg = (arg_ty)(args)->elements[(i)];
        error = compiler_visit_argannotation(
                        c,
                        arg->arg,
                        arg->annotation,
                        names);
        if (error)
            return error;
    }
    return 0;
}

static int
compiler_visit_annotations(struct compiler *c, arguments_ty args,
                           expr_ty returns)
{






    static identifier return_str;
    PyObject *names;
    int len;
    names = PyList_New(0);
    if (!names)
        return -1;

    if (compiler_visit_argannotations(c, args->args, names))
        goto error;
    if (args->varargannotation &&
        compiler_visit_argannotation(c, args->vararg,
                                     args->varargannotation, names))
        goto error;
    if (compiler_visit_argannotations(c, args->kwonlyargs, names))
        goto error;
    if (args->kwargannotation &&
        compiler_visit_argannotation(c, args->kwarg,
                                     args->kwargannotation, names))
        goto error;

    if (!return_str) {
        return_str = PyUnicode_InternFromString("return");
        if (!return_str)
            goto error;
    }
    if (compiler_visit_argannotation(c, return_str, returns, names)) {
        goto error;
    }

    len = (((PyVarObject*)(names))->ob_size);
    if (len > 65534) {

        PyErr_SetString(PyExc_SyntaxError,
                        "too many annotations");
        goto error;
    }
    if (len) {

        PyObject *elt;
        int i;
        PyObject *s = PyTuple_New(len);
        if (!s)
            goto error;
        for (i = 0; i < len; i++) {
            elt = (((PyListObject *)(names))->ob_item[i]);
            ( ((PyObject*)(elt))->ob_refcnt++);
            (((PyTupleObject *)(s))->ob_item[i] = elt);
        }
        { if (!compiler_addop_o((c), (100), (c)->u->u_consts, (s))) return 0; };
        do { if ( --((PyObject*)(s))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(s)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(s)))); } while (0);
        len++;
    }
    do { if ( --((PyObject*)(names))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(names)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(names)))); } while (0);
    return len;

error:
    do { if ( --((PyObject*)(names))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(names)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(names)))); } while (0);
    return -1;
}

static int
compiler_function(struct compiler *c, stmt_ty s)
{
    PyCodeObject *co;
    PyObject *qualname, *first_const = (&_Py_NoneStruct);
    arguments_ty args = s->v.FunctionDef.args;
    expr_ty returns = s->v.FunctionDef.returns;
    asdl_seq* decos = s->v.FunctionDef.decorator_list;
    stmt_ty st;
    int i, n, docstring, kw_default_count = 0, arglength;
    int num_annotations;

    (__builtin_expect(!(s->kind == FunctionDef_kind), 0) ? __assert_rtn(__func__, "compile.c", 1564, "s->kind == FunctionDef_kind") : (void)0);

    if (!compiler_decorators(c, decos))
        return 0;
    if (args->kwonlyargs) {
        int res = compiler_visit_kwonlydefaults(c, args->kwonlyargs,
                                                args->kw_defaults);
        if (res < 0)
            return 0;
        kw_default_count = res;
    }
    if (args->defaults)
        { int _i; asdl_seq *seq = (args->defaults); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { expr_ty elt = (expr_ty)(seq)->elements[(_i)]; if (!compiler_visit_expr((c), elt)) return 0; } };
    num_annotations = compiler_visit_annotations(c, args, returns);
    if (num_annotations < 0)
        return 0;
    (__builtin_expect(!((num_annotations & 0xFFFF) == num_annotations), 0) ? __assert_rtn(__func__, "compile.c", 1580, "(num_annotations & 0xFFFF) == num_annotations") : (void)0);

    if (!compiler_enter_scope(c, s->v.FunctionDef.name,
                              COMPILER_SCOPE_FUNCTION, (void *)s,
                              s->lineno))
        return 0;

    st = (stmt_ty)(s->v.FunctionDef.body)->elements[(0)];
    docstring = compiler_isdocstring(st);
    if (docstring && c->c_optimize < 2)
        first_const = st->v.Expr.value->v.Str.s;
    if (compiler_add_o(c, c->u->u_consts, first_const) < 0) {
        compiler_exit_scope(c);
        return 0;
    }

    c->u->u_argcount = ((args->args) == ((void *)0) ? 0 : (args->args)->size);
    c->u->u_kwonlyargcount = ((args->kwonlyargs) == ((void *)0) ? 0 : (args->kwonlyargs)->size);
    n = ((s->v.FunctionDef.body) == ((void *)0) ? 0 : (s->v.FunctionDef.body)->size);

    for (i = docstring; i < n; i++) {
        st = (stmt_ty)(s->v.FunctionDef.body)->elements[(i)];
        { if (!compiler_visit_stmt((c), (st))) { compiler_exit_scope(c); return 0; } };
    }
    co = assemble(c, 1);
    qualname = compiler_scope_qualname(c);
    compiler_exit_scope(c);
    if (qualname == ((void *)0) || co == ((void *)0)) {
        do { if ((qualname) == ((void *)0)) ; else do { if ( --((PyObject*)(qualname))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(qualname)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(qualname)))); } while (0); } while (0);
        do { if ((co) == ((void *)0)) ; else do { if ( --((PyObject*)(co))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(co)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(co)))); } while (0); } while (0);
        return 0;
    }

    arglength = ((args->defaults) == ((void *)0) ? 0 : (args->defaults)->size);
    arglength |= kw_default_count << 8;
    arglength |= num_annotations << 16;
    compiler_make_closure(c, co, arglength, qualname);
    do { if ( --((PyObject*)(qualname))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(qualname)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(qualname)))); } while (0);
    do { if ( --((PyObject*)(co))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(co)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(co)))); } while (0);


    for (i = 0; i < ((decos) == ((void *)0) ? 0 : (decos)->size); i++) {
        { if (!compiler_addop_i((c), (131), (1))) return 0; };
    }

    return compiler_nameop(c, s->v.FunctionDef.name, Store);
}

static int
compiler_class(struct compiler *c, stmt_ty s)
{
    PyCodeObject *co;
    PyObject *str;
    int i;
    asdl_seq* decos = s->v.ClassDef.decorator_list;

    if (!compiler_decorators(c, decos))
        return 0;
# 1652 "compile.c"
    if (!compiler_enter_scope(c, s->v.ClassDef.name,
                              COMPILER_SCOPE_CLASS, (void *)s, s->lineno))
        return 0;

    {

        ( ((PyObject*)(s->v.ClassDef.name))->ob_refcnt++);
        do { if ((c->u->u_private) == ((void *)0)) ; else do { if ( --((PyObject*)(c->u->u_private))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(c->u->u_private)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(c->u->u_private)))); } while (0); } while (0);
        c->u->u_private = s->v.ClassDef.name;

        c->u->u_argcount = 1;

        { if (!compiler_addop_i((c), (124), (0))) return 0; };

        { if (!compiler_addop((c), (69))) { compiler_exit_scope(c); return 0; } };

        str = PyUnicode_InternFromString("__name__");
        if (!str || !compiler_nameop(c, str, Load)) {
            do { if ((str) == ((void *)0)) ; else do { if ( --((PyObject*)(str))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(str)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(str)))); } while (0); } while (0);
            compiler_exit_scope(c);
            return 0;
        }
        do { if ( --((PyObject*)(str))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(str)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(str)))); } while (0);

        str = PyUnicode_InternFromString("__module__");
        if (!str || !compiler_nameop(c, str, Store)) {
            do { if ((str) == ((void *)0)) ; else do { if ( --((PyObject*)(str))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(str)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(str)))); } while (0); } while (0);
            compiler_exit_scope(c);
            return 0;
        }
        do { if ( --((PyObject*)(str))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(str)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(str)))); } while (0);

        str = compiler_scope_qualname(c);
        if (!str) {
            compiler_exit_scope(c);
            return 0;
        }
        { if (!compiler_addop_o((c), (100), (c)->u->u_consts, (str))) return 0; };
        do { if ( --((PyObject*)(str))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(str)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(str)))); } while (0);
        str = PyUnicode_InternFromString("__qualname__");
        if (!str || !compiler_nameop(c, str, Store)) {
            do { if ((str) == ((void *)0)) ; else do { if ( --((PyObject*)(str))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(str)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(str)))); } while (0); } while (0);
            compiler_exit_scope(c);
            return 0;
        }
        do { if ( --((PyObject*)(str))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(str)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(str)))); } while (0);

        if (!compiler_body(c, s->v.ClassDef.body)) {
            compiler_exit_scope(c);
            return 0;
        }

        str = PyUnicode_InternFromString("__class__");
        if (str == ((void *)0)) {
            compiler_exit_scope(c);
            return 0;
        }
        i = compiler_lookup_arg(c->u->u_cellvars, str);
        do { if ( --((PyObject*)(str))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(str)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(str)))); } while (0);
        if (i == -1) {

            PyErr_Clear();

            { if (!compiler_addop_o((c), (100), (c)->u->u_consts, ((&_Py_NoneStruct)))) return 0; };
        }
        else {

            { if (!compiler_addop_i((c), (135), (i))) return 0; };
        }
        { if (!compiler_addop((c), (83))) { compiler_exit_scope(c); return 0; } };

        co = assemble(c, 1);
    }

    compiler_exit_scope(c);
    if (co == ((void *)0))
        return 0;


    { if (!compiler_addop((c), (71))) return 0; };


    compiler_make_closure(c, co, 0, ((void *)0));
    do { if ( --((PyObject*)(co))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(co)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(co)))); } while (0);


    { if (!compiler_addop_o((c), (100), (c)->u->u_consts, (s->v.ClassDef.name))) return 0; };


    if (!compiler_call_helper(c, 2,
                              s->v.ClassDef.bases,
                              s->v.ClassDef.keywords,
                              s->v.ClassDef.starargs,
                              s->v.ClassDef.kwargs))
        return 0;


    for (i = 0; i < ((decos) == ((void *)0) ? 0 : (decos)->size); i++) {
        { if (!compiler_addop_i((c), (131), (1))) return 0; };
    }


    if (!compiler_nameop(c, s->v.ClassDef.name, Store))
        return 0;
    return 1;
}

static int
compiler_ifexp(struct compiler *c, expr_ty e)
{
    basicblock *end, *next;

    (__builtin_expect(!(e->kind == IfExp_kind), 0) ? __assert_rtn(__func__, "compile.c", 1764, "e->kind == IfExp_kind") : (void)0);
    end = compiler_new_block(c);
    if (end == ((void *)0))
        return 0;
    next = compiler_new_block(c);
    if (next == ((void *)0))
        return 0;
    { if (!compiler_visit_expr((c), (e->v.IfExp.test))) return 0; };
    { if (!compiler_addop_j((c), (114), (next), 1)) return 0; };
    { if (!compiler_visit_expr((c), (e->v.IfExp.body))) return 0; };
    { if (!compiler_addop_j((c), (110), (end), 0)) return 0; };
    compiler_use_next_block(c, next);
    { if (!compiler_visit_expr((c), (e->v.IfExp.orelse))) return 0; };
    compiler_use_next_block(c, end);
    return 1;
}

static int
compiler_lambda(struct compiler *c, expr_ty e)
{
    PyCodeObject *co;
    PyObject *qualname;
    static identifier name;
    int kw_default_count = 0, arglength;
    arguments_ty args = e->v.Lambda.args;
    (__builtin_expect(!(e->kind == Lambda_kind), 0) ? __assert_rtn(__func__, "compile.c", 1789, "e->kind == Lambda_kind") : (void)0);

    if (!name) {
        name = PyUnicode_InternFromString("<lambda>");
        if (!name)
            return 0;
    }

    if (args->kwonlyargs) {
        int res = compiler_visit_kwonlydefaults(c, args->kwonlyargs,
                                                args->kw_defaults);
        if (res < 0) return 0;
        kw_default_count = res;
    }
    if (args->defaults)
        { int _i; asdl_seq *seq = (args->defaults); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { expr_ty elt = (expr_ty)(seq)->elements[(_i)]; if (!compiler_visit_expr((c), elt)) return 0; } };
    if (!compiler_enter_scope(c, name, COMPILER_SCOPE_FUNCTION,
                              (void *)e, e->lineno))
        return 0;



    if (compiler_add_o(c, c->u->u_consts, (&_Py_NoneStruct)) < 0)
        return 0;

    c->u->u_argcount = ((args->args) == ((void *)0) ? 0 : (args->args)->size);
    c->u->u_kwonlyargcount = ((args->kwonlyargs) == ((void *)0) ? 0 : (args->kwonlyargs)->size);
    { if (!compiler_visit_expr((c), (e->v.Lambda.body))) { compiler_exit_scope(c); return 0; } };
    if (c->u->u_ste->ste_generator) {
        { if (!compiler_addop((c), (1))) { compiler_exit_scope(c); return 0; } };
    }
    else {
        { if (!compiler_addop((c), (83))) { compiler_exit_scope(c); return 0; } };
    }
    co = assemble(c, 1);
    qualname = compiler_scope_qualname(c);
    compiler_exit_scope(c);
    if (qualname == ((void *)0) || co == ((void *)0))
        return 0;

    arglength = ((args->defaults) == ((void *)0) ? 0 : (args->defaults)->size);
    arglength |= kw_default_count << 8;
    compiler_make_closure(c, co, arglength, qualname);
    do { if ( --((PyObject*)(qualname))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(qualname)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(qualname)))); } while (0);
    do { if ( --((PyObject*)(co))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(co)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(co)))); } while (0);

    return 1;
}

static int
compiler_if(struct compiler *c, stmt_ty s)
{
    basicblock *end, *next;
    int constant;
    (__builtin_expect(!(s->kind == If_kind), 0) ? __assert_rtn(__func__, "compile.c", 1843, "s->kind == If_kind") : (void)0);
    end = compiler_new_block(c);
    if (end == ((void *)0))
        return 0;

    constant = expr_constant(c, s->v.If.test);



    if (constant == 0) {
        if (s->v.If.orelse)
            { int _i; asdl_seq *seq = (s->v.If.orelse); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { stmt_ty elt = (stmt_ty)(seq)->elements[(_i)]; if (!compiler_visit_stmt((c), elt)) return 0; } };
    } else if (constant == 1) {
        { int _i; asdl_seq *seq = (s->v.If.body); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { stmt_ty elt = (stmt_ty)(seq)->elements[(_i)]; if (!compiler_visit_stmt((c), elt)) return 0; } };
    } else {
        if (s->v.If.orelse) {
            next = compiler_new_block(c);
            if (next == ((void *)0))
                return 0;
        }
        else
            next = end;
        { if (!compiler_visit_expr((c), (s->v.If.test))) return 0; };
        { if (!compiler_addop_j((c), (114), (next), 1)) return 0; };
        { int _i; asdl_seq *seq = (s->v.If.body); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { stmt_ty elt = (stmt_ty)(seq)->elements[(_i)]; if (!compiler_visit_stmt((c), elt)) return 0; } };
        { if (!compiler_addop_j((c), (110), (end), 0)) return 0; };
        if (s->v.If.orelse) {
            compiler_use_next_block(c, next);
            { int _i; asdl_seq *seq = (s->v.If.orelse); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { stmt_ty elt = (stmt_ty)(seq)->elements[(_i)]; if (!compiler_visit_stmt((c), elt)) return 0; } };
        }
    }
    compiler_use_next_block(c, end);
    return 1;
}

static int
compiler_for(struct compiler *c, stmt_ty s)
{
    basicblock *start, *cleanup, *end;

    start = compiler_new_block(c);
    cleanup = compiler_new_block(c);
    end = compiler_new_block(c);
    if (start == ((void *)0) || end == ((void *)0) || cleanup == ((void *)0))
        return 0;
    { if (!compiler_addop_j((c), (120), (end), 0)) return 0; };
    if (!compiler_push_fblock(c, LOOP, start))
        return 0;
    { if (!compiler_visit_expr((c), (s->v.For.iter))) return 0; };
    { if (!compiler_addop((c), (68))) return 0; };
    compiler_use_next_block(c, start);
    { if (!compiler_addop_j((c), (93), (cleanup), 0)) return 0; };
    { if (!compiler_visit_expr((c), (s->v.For.target))) return 0; };
    { int _i; asdl_seq *seq = (s->v.For.body); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { stmt_ty elt = (stmt_ty)(seq)->elements[(_i)]; if (!compiler_visit_stmt((c), elt)) return 0; } };
    { if (!compiler_addop_j((c), (113), (start), 1)) return 0; };
    compiler_use_next_block(c, cleanup);
    { if (!compiler_addop((c), (87))) return 0; };
    compiler_pop_fblock(c, LOOP, start);
    { int _i; asdl_seq *seq = (s->v.For.orelse); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { stmt_ty elt = (stmt_ty)(seq)->elements[(_i)]; if (!compiler_visit_stmt((c), elt)) return 0; } };
    compiler_use_next_block(c, end);
    return 1;
}

static int
compiler_while(struct compiler *c, stmt_ty s)
{
    basicblock *loop, *orelse, *end, *anchor = ((void *)0);
    int constant = expr_constant(c, s->v.While.test);

    if (constant == 0) {
        if (s->v.While.orelse)
            { int _i; asdl_seq *seq = (s->v.While.orelse); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { stmt_ty elt = (stmt_ty)(seq)->elements[(_i)]; if (!compiler_visit_stmt((c), elt)) return 0; } };
        return 1;
    }
    loop = compiler_new_block(c);
    end = compiler_new_block(c);
    if (constant == -1) {
        anchor = compiler_new_block(c);
        if (anchor == ((void *)0))
            return 0;
    }
    if (loop == ((void *)0) || end == ((void *)0))
        return 0;
    if (s->v.While.orelse) {
        orelse = compiler_new_block(c);
        if (orelse == ((void *)0))
            return 0;
    }
    else
        orelse = ((void *)0);

    { if (!compiler_addop_j((c), (120), (end), 0)) return 0; };
    compiler_use_next_block(c, loop);
    if (!compiler_push_fblock(c, LOOP, loop))
        return 0;
    if (constant == -1) {
        { if (!compiler_visit_expr((c), (s->v.While.test))) return 0; };
        { if (!compiler_addop_j((c), (114), (anchor), 1)) return 0; };
    }
    { int _i; asdl_seq *seq = (s->v.While.body); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { stmt_ty elt = (stmt_ty)(seq)->elements[(_i)]; if (!compiler_visit_stmt((c), elt)) return 0; } };
    { if (!compiler_addop_j((c), (113), (loop), 1)) return 0; };





    if (constant == -1) {
        compiler_use_next_block(c, anchor);
        { if (!compiler_addop((c), (87))) return 0; };
    }
    compiler_pop_fblock(c, LOOP, loop);
    if (orelse != ((void *)0))
        { int _i; asdl_seq *seq = (s->v.While.orelse); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { stmt_ty elt = (stmt_ty)(seq)->elements[(_i)]; if (!compiler_visit_stmt((c), elt)) return 0; } };
    compiler_use_next_block(c, end);

    return 1;
}

static int
compiler_continue(struct compiler *c)
{
    static const char LOOP_ERROR_MSG[] = "'continue' not properly in loop";
    static const char IN_FINALLY_ERROR_MSG[] =
                    "'continue' not supported inside 'finally' clause";
    int i;

    if (!c->u->u_nfblocks)
        return compiler_error(c, LOOP_ERROR_MSG);
    i = c->u->u_nfblocks - 1;
    switch (c->u->u_fblock[i].fb_type) {
    case LOOP:
        { if (!compiler_addop_j((c), (113), (c->u->u_fblock[i].fb_block), 1)) return 0; };
        break;
    case EXCEPT:
    case FINALLY_TRY:
        while (--i >= 0 && c->u->u_fblock[i].fb_type != LOOP) {


            if (c->u->u_fblock[i].fb_type == FINALLY_END)
                return compiler_error(c, IN_FINALLY_ERROR_MSG);
        }
        if (i == -1)
            return compiler_error(c, LOOP_ERROR_MSG);
        { if (!compiler_addop_j((c), (119), (c->u->u_fblock[i].fb_block), 1)) return 0; };
        break;
    case FINALLY_END:
        return compiler_error(c, IN_FINALLY_ERROR_MSG);
    }

    return 1;
}
# 2028 "compile.c"
static int
compiler_try_finally(struct compiler *c, stmt_ty s)
{
    basicblock *body, *end;
    body = compiler_new_block(c);
    end = compiler_new_block(c);
    if (body == ((void *)0) || end == ((void *)0))
        return 0;

    { if (!compiler_addop_j((c), (122), (end), 0)) return 0; };
    compiler_use_next_block(c, body);
    if (!compiler_push_fblock(c, FINALLY_TRY, body))
        return 0;
    if (s->v.Try.handlers && ((s->v.Try.handlers) == ((void *)0) ? 0 : (s->v.Try.handlers)->size)) {
        if (!compiler_try_except(c, s))
            return 0;
    }
    else {
        { int _i; asdl_seq *seq = (s->v.Try.body); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { stmt_ty elt = (stmt_ty)(seq)->elements[(_i)]; if (!compiler_visit_stmt((c), elt)) return 0; } };
    }
    { if (!compiler_addop((c), (87))) return 0; };
    compiler_pop_fblock(c, FINALLY_TRY, body);

    { if (!compiler_addop_o((c), (100), (c)->u->u_consts, ((&_Py_NoneStruct)))) return 0; };
    compiler_use_next_block(c, end);
    if (!compiler_push_fblock(c, FINALLY_END, end))
        return 0;
    { int _i; asdl_seq *seq = (s->v.Try.finalbody); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { stmt_ty elt = (stmt_ty)(seq)->elements[(_i)]; if (!compiler_visit_stmt((c), elt)) return 0; } };
    { if (!compiler_addop((c), (88))) return 0; };
    compiler_pop_fblock(c, FINALLY_END, end);

    return 1;
}
# 2093 "compile.c"
static int
compiler_try_except(struct compiler *c, stmt_ty s)
{
    basicblock *body, *orelse, *except, *end;
    int i, n;

    body = compiler_new_block(c);
    except = compiler_new_block(c);
    orelse = compiler_new_block(c);
    end = compiler_new_block(c);
    if (body == ((void *)0) || except == ((void *)0) || orelse == ((void *)0) || end == ((void *)0))
        return 0;
    { if (!compiler_addop_j((c), (121), (except), 0)) return 0; };
    compiler_use_next_block(c, body);
    if (!compiler_push_fblock(c, EXCEPT, body))
        return 0;
    { int _i; asdl_seq *seq = (s->v.Try.body); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { stmt_ty elt = (stmt_ty)(seq)->elements[(_i)]; if (!compiler_visit_stmt((c), elt)) return 0; } };
    { if (!compiler_addop((c), (87))) return 0; };
    compiler_pop_fblock(c, EXCEPT, body);
    { if (!compiler_addop_j((c), (110), (orelse), 0)) return 0; };
    n = ((s->v.Try.handlers) == ((void *)0) ? 0 : (s->v.Try.handlers)->size);
    compiler_use_next_block(c, except);
    for (i = 0; i < n; i++) {
        excepthandler_ty handler = (excepthandler_ty)(s->v.Try.handlers)->elements[(i)];

        if (!handler->v.ExceptHandler.type && i < n-1)
            return compiler_error(c, "default 'except:' must be last");
        c->u->u_lineno_set = 0;
        c->u->u_lineno = handler->lineno;
        c->u->u_col_offset = handler->col_offset;
        except = compiler_new_block(c);
        if (except == ((void *)0))
            return 0;
        if (handler->v.ExceptHandler.type) {
            { if (!compiler_addop((c), (4))) return 0; };
            { if (!compiler_visit_expr((c), (handler->v.ExceptHandler.type))) return 0; };
            { if (!compiler_addop_i((c), (107), (PyCmp_EXC_MATCH))) return 0; };
            { if (!compiler_addop_j((c), (114), (except), 1)) return 0; };
        }
        { if (!compiler_addop((c), (1))) return 0; };
        if (handler->v.ExceptHandler.name) {
            basicblock *cleanup_end, *cleanup_body;

            cleanup_end = compiler_new_block(c);
            cleanup_body = compiler_new_block(c);
            if (!(cleanup_end || cleanup_body))
                return 0;

            compiler_nameop(c, handler->v.ExceptHandler.name, Store);
            { if (!compiler_addop((c), (1))) return 0; };
# 2156 "compile.c"
            { if (!compiler_addop_j((c), (122), (cleanup_end), 0)) return 0; };
            compiler_use_next_block(c, cleanup_body);
            if (!compiler_push_fblock(c, FINALLY_TRY, cleanup_body))
                return 0;


            { int _i; asdl_seq *seq = (handler->v.ExceptHandler.body); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { stmt_ty elt = (stmt_ty)(seq)->elements[(_i)]; if (!compiler_visit_stmt((c), elt)) return 0; } };
            { if (!compiler_addop((c), (87))) return 0; };
            { if (!compiler_addop((c), (89))) return 0; };
            compiler_pop_fblock(c, FINALLY_TRY, cleanup_body);


            { if (!compiler_addop_o((c), (100), (c)->u->u_consts, ((&_Py_NoneStruct)))) return 0; };
            compiler_use_next_block(c, cleanup_end);
            if (!compiler_push_fblock(c, FINALLY_END, cleanup_end))
                return 0;


            { if (!compiler_addop_o((c), (100), (c)->u->u_consts, ((&_Py_NoneStruct)))) return 0; };
            compiler_nameop(c, handler->v.ExceptHandler.name, Store);


            compiler_nameop(c, handler->v.ExceptHandler.name, Del);

            { if (!compiler_addop((c), (88))) return 0; };
            compiler_pop_fblock(c, FINALLY_END, cleanup_end);
        }
        else {
            basicblock *cleanup_body;

            cleanup_body = compiler_new_block(c);
            if (!cleanup_body)
                return 0;

            { if (!compiler_addop((c), (1))) return 0; };
            { if (!compiler_addop((c), (1))) return 0; };
            compiler_use_next_block(c, cleanup_body);
            if (!compiler_push_fblock(c, FINALLY_TRY, cleanup_body))
                return 0;
            { int _i; asdl_seq *seq = (handler->v.ExceptHandler.body); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { stmt_ty elt = (stmt_ty)(seq)->elements[(_i)]; if (!compiler_visit_stmt((c), elt)) return 0; } };
            { if (!compiler_addop((c), (89))) return 0; };
            compiler_pop_fblock(c, FINALLY_TRY, cleanup_body);
        }
        { if (!compiler_addop_j((c), (110), (end), 0)) return 0; };
        compiler_use_next_block(c, except);
    }
    { if (!compiler_addop((c), (88))) return 0; };
    compiler_use_next_block(c, orelse);
    { int _i; asdl_seq *seq = (s->v.Try.orelse); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { stmt_ty elt = (stmt_ty)(seq)->elements[(_i)]; if (!compiler_visit_stmt((c), elt)) return 0; } };
    compiler_use_next_block(c, end);
    return 1;
}

static int
compiler_try(struct compiler *c, stmt_ty s) {
    if (s->v.Try.finalbody && ((s->v.Try.finalbody) == ((void *)0) ? 0 : (s->v.Try.finalbody)->size))
        return compiler_try_finally(c, s);
    else
        return compiler_try_except(c, s);
}


static int
compiler_import_as(struct compiler *c, identifier name, identifier asname)
{






    Py_ssize_t dot = PyUnicode_FindChar(name, '.', 0,
                                        ((__builtin_expect(!(((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2228, "PyUnicode_Check(name)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)name)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 2228, "PyUnicode_IS_READY(name)") : (void)0), ((PyASCIIObject *)(name))->length), 1);
    if (dot == -2)
        return -1;
    if (dot != -1) {

        Py_ssize_t pos = dot + 1;
        while (dot != -1) {
            PyObject *attr;
            dot = PyUnicode_FindChar(name, '.', pos,
                                     ((__builtin_expect(!(((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2237, "PyUnicode_Check(name)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)name)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 2237, "PyUnicode_IS_READY(name)") : (void)0), ((PyASCIIObject *)(name))->length), 1);
            if (dot == -2)
                return -1;
            attr = PyUnicode_Substring(name, pos,
                                       (dot != -1) ? dot :
                                       ((__builtin_expect(!(((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2242, "PyUnicode_Check(name)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)name)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 2242, "PyUnicode_IS_READY(name)") : (void)0), ((PyASCIIObject *)(name))->length));
            if (!attr)
                return -1;
            { if (!compiler_addop_o((c), (106), (c)->u->u_names, (attr))) return 0; };
            do { if ( --((PyObject*)(attr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(attr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(attr)))); } while (0);
            pos = dot + 1;
        }
    }
    return compiler_nameop(c, asname, Store);
}

static int
compiler_import(struct compiler *c, stmt_ty s)
{







    int i, n = ((s->v.Import.names) == ((void *)0) ? 0 : (s->v.Import.names)->size);

    for (i = 0; i < n; i++) {
        alias_ty alias = (alias_ty)(s->v.Import.names)->elements[(i)];
        int r;
        PyObject *level;

        level = PyLong_FromLong(0);
        if (level == ((void *)0))
            return 0;

        { if (!compiler_addop_o((c), (100), (c)->u->u_consts, (level))) return 0; };
        do { if ( --((PyObject*)(level))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(level)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(level)))); } while (0);
        { if (!compiler_addop_o((c), (100), (c)->u->u_consts, ((&_Py_NoneStruct)))) return 0; };
        { if (!compiler_addop_name((c), (108), (c)->u->u_names, (alias->name))) return 0; };

        if (alias->asname) {
            r = compiler_import_as(c, alias->name, alias->asname);
            if (!r)
                return r;
        }
        else {
            identifier tmp = alias->name;
            Py_ssize_t dot = PyUnicode_FindChar(
                alias->name, '.', 0, ((__builtin_expect(!(((((((PyObject*)(alias->name))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2287, "PyUnicode_Check(alias->name)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)alias->name)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 2287, "PyUnicode_IS_READY(alias->name)") : (void)0), ((PyASCIIObject *)(alias->name))->length), 1);
            if (dot != -1)
                tmp = PyUnicode_Substring(alias->name, 0, dot);
            r = compiler_nameop(c, tmp, Store);
            if (dot != -1) {
                do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0);
            }
            if (!r)
                return r;
        }
    }
    return 1;
}

static int
compiler_from_import(struct compiler *c, stmt_ty s)
{
    int i, n = ((s->v.ImportFrom.names) == ((void *)0) ? 0 : (s->v.ImportFrom.names)->size);

    PyObject *names = PyTuple_New(n);
    PyObject *level;
    static PyObject *empty_string;

    if (!empty_string) {
        empty_string = PyUnicode_FromString("");
        if (!empty_string)
            return 0;
    }

    if (!names)
        return 0;

    level = PyLong_FromLong(s->v.ImportFrom.level);
    if (!level) {
        do { if ( --((PyObject*)(names))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(names)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(names)))); } while (0);
        return 0;
    }


    for (i = 0; i < n; i++) {
        alias_ty alias = (alias_ty)(s->v.ImportFrom.names)->elements[(i)];
        ( ((PyObject*)(alias->name))->ob_refcnt++);
        (((PyTupleObject *)(names))->ob_item[i] = alias->name);
    }

    if (s->lineno > c->c_future->ff_lineno && s->v.ImportFrom.module &&
        !PyUnicode_CompareWithASCIIString(s->v.ImportFrom.module, "__future__")) {
        do { if ( --((PyObject*)(level))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(level)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(level)))); } while (0);
        do { if ( --((PyObject*)(names))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(names)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(names)))); } while (0);
        return compiler_error(c, "from __future__ imports must occur "
                              "at the beginning of the file");
    }

    { if (!compiler_addop_o((c), (100), (c)->u->u_consts, (level))) return 0; };
    do { if ( --((PyObject*)(level))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(level)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(level)))); } while (0);
    { if (!compiler_addop_o((c), (100), (c)->u->u_consts, (names))) return 0; };
    do { if ( --((PyObject*)(names))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(names)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(names)))); } while (0);
    if (s->v.ImportFrom.module) {
        { if (!compiler_addop_name((c), (108), (c)->u->u_names, (s->v.ImportFrom.module))) return 0; };
    }
    else {
        { if (!compiler_addop_name((c), (108), (c)->u->u_names, (empty_string))) return 0; };
    }
    for (i = 0; i < n; i++) {
        alias_ty alias = (alias_ty)(s->v.ImportFrom.names)->elements[(i)];
        identifier store_name;

        if (i == 0 && ((__builtin_expect(!(((((((PyObject*)(alias->name))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2354, "PyUnicode_Check(alias->name)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)alias->name)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 2354, "PyUnicode_IS_READY(alias->name)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((alias->name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2354, "PyUnicode_Check((alias->name))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(alias->name))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 2354, "PyUnicode_IS_READY((alias->name))") : (void)0), ((PyASCIIObject *)((alias->name)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((alias->name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2354, "PyUnicode_Check((alias->name))") : (void)0), (((PyASCIIObject*)((alias->name)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((alias->name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2354, "PyUnicode_Check((alias->name))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(alias->name))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 2354, "PyUnicode_IS_READY((alias->name))") : (void)0), ((PyASCIIObject*)(alias->name))->state.ascii) ? ((void*)((PyASCIIObject*)((alias->name)) + 1)) : ((void*)((PyCompactUnicodeObject*)((alias->name)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((alias->name)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 2354, "((PyUnicodeObject*)((alias->name)))->data.any") : (void)0), ((((PyUnicodeObject *)((alias->name)))->data.any))))))[(0)] : (((__builtin_expect(!(((((((PyObject*)((alias->name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2354, "PyUnicode_Check((alias->name))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(alias->name))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 2354, "PyUnicode_IS_READY((alias->name))") : (void)0), ((PyASCIIObject *)((alias->name)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((alias->name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2354, "PyUnicode_Check((alias->name))") : (void)0), (((PyASCIIObject*)((alias->name)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((alias->name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2354, "PyUnicode_Check((alias->name))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(alias->name))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 2354, "PyUnicode_IS_READY((alias->name))") : (void)0), ((PyASCIIObject*)(alias->name))->state.ascii) ? ((void*)((PyASCIIObject*)((alias->name)) + 1)) : ((void*)((PyCompactUnicodeObject*)((alias->name)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((alias->name)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 2354, "((PyUnicodeObject*)((alias->name)))->data.any") : (void)0), ((((PyUnicodeObject *)((alias->name)))->data.any))))))[(0)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((alias->name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2354, "PyUnicode_Check((alias->name))") : (void)0), (((PyASCIIObject*)((alias->name)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((alias->name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2354, "PyUnicode_Check((alias->name))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(alias->name))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 2354, "PyUnicode_IS_READY((alias->name))") : (void)0), ((PyASCIIObject*)(alias->name))->state.ascii) ? ((void*)((PyASCIIObject*)((alias->name)) + 1)) : ((void*)((PyCompactUnicodeObject*)((alias->name)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((alias->name)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 2354, "((PyUnicodeObject*)((alias->name)))->data.any") : (void)0), ((((PyUnicodeObject *)((alias->name)))->data.any))))))[(0)] ) )) == '*') {
            (__builtin_expect(!(n == 1), 0) ? __assert_rtn(__func__, "compile.c", 2355, "n == 1") : (void)0);
            { if (!compiler_addop((c), (84))) return 0; };
            return 1;
        }

        { if (!compiler_addop_name((c), (109), (c)->u->u_names, (alias->name))) return 0; };
        store_name = alias->name;
        if (alias->asname)
            store_name = alias->asname;

        if (!compiler_nameop(c, store_name, Store)) {
            do { if ( --((PyObject*)(names))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(names)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(names)))); } while (0);
            return 0;
        }
    }

    { if (!compiler_addop((c), (1))) return 0; };
    return 1;
}

static int
compiler_assert(struct compiler *c, stmt_ty s)
{
    static PyObject *assertion_error = ((void *)0);
    basicblock *end;

    if (c->c_optimize)
        return 1;
    if (assertion_error == ((void *)0)) {
        assertion_error = PyUnicode_InternFromString("AssertionError");
        if (assertion_error == ((void *)0))
            return 0;
    }
    if (s->v.Assert.test->kind == Tuple_kind &&
        ((s->v.Assert.test->v.Tuple.elts) == ((void *)0) ? 0 : (s->v.Assert.test->v.Tuple.elts)->size) > 0) {
        const char* msg =
            "assertion is always true, perhaps remove parentheses?";
        if (PyErr_WarnExplicit(PyExc_SyntaxWarning, msg, c->c_filename,
                               c->u->u_lineno, ((void *)0), ((void *)0)) == -1)
            return 0;
    }
    { if (!compiler_visit_expr((c), (s->v.Assert.test))) return 0; };
    end = compiler_new_block(c);
    if (end == ((void *)0))
        return 0;
    { if (!compiler_addop_j((c), (115), (end), 1)) return 0; };
    { if (!compiler_addop_o((c), (116), (c)->u->u_names, (assertion_error))) return 0; };
    if (s->v.Assert.msg) {
        { if (!compiler_visit_expr((c), (s->v.Assert.msg))) return 0; };
        { if (!compiler_addop_i((c), (131), (1))) return 0; };
    }
    { if (!compiler_addop_i((c), (130), (1))) return 0; };
    compiler_use_next_block(c, end);
    return 1;
}

static int
compiler_visit_stmt(struct compiler *c, stmt_ty s)
{
    int i, n;


    c->u->u_lineno = s->lineno;
    c->u->u_col_offset = s->col_offset;
    c->u->u_lineno_set = 0;

    switch (s->kind) {
    case FunctionDef_kind:
        return compiler_function(c, s);
    case ClassDef_kind:
        return compiler_class(c, s);
    case Return_kind:
        if (c->u->u_ste->ste_type != FunctionBlock)
            return compiler_error(c, "'return' outside function");
        if (s->v.Return.value) {
            { if (!compiler_visit_expr((c), (s->v.Return.value))) return 0; };
        }
        else
            { if (!compiler_addop_o((c), (100), (c)->u->u_consts, ((&_Py_NoneStruct)))) return 0; };
        { if (!compiler_addop((c), (83))) return 0; };
        break;
    case Delete_kind:
        { int _i; asdl_seq *seq = (s->v.Delete.targets); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { expr_ty elt = (expr_ty)(seq)->elements[(_i)]; if (!compiler_visit_expr((c), elt)) return 0; } }
        break;
    case Assign_kind:
        n = ((s->v.Assign.targets) == ((void *)0) ? 0 : (s->v.Assign.targets)->size);
        { if (!compiler_visit_expr((c), (s->v.Assign.value))) return 0; };
        for (i = 0; i < n; i++) {
            if (i < n - 1)
                { if (!compiler_addop((c), (4))) return 0; };
            { if (!compiler_visit_expr((c), ((expr_ty)(s->v.Assign.targets)->elements[(i)]))) return 0; };

        }
        break;
    case AugAssign_kind:
        return compiler_augassign(c, s);
    case For_kind:
        return compiler_for(c, s);
    case While_kind:
        return compiler_while(c, s);
    case If_kind:
        return compiler_if(c, s);
    case Raise_kind:
        n = 0;
        if (s->v.Raise.exc) {
            { if (!compiler_visit_expr((c), (s->v.Raise.exc))) return 0; };
            n++;
        if (s->v.Raise.cause) {
        { if (!compiler_visit_expr((c), (s->v.Raise.cause))) return 0; };
        n++;
        }
        }
        { if (!compiler_addop_i((c), (130), (n))) return 0; };
        break;
    case Try_kind:
        return compiler_try(c, s);
    case Assert_kind:
        return compiler_assert(c, s);
    case Import_kind:
        return compiler_import(c, s);
    case ImportFrom_kind:
        return compiler_from_import(c, s);
    case Global_kind:
    case Nonlocal_kind:
        break;
    case Expr_kind:
        if (c->c_interactive && c->c_nestlevel <= 1) {
            { if (!compiler_visit_expr((c), (s->v.Expr.value))) return 0; };
            { if (!compiler_addop((c), (70))) return 0; };
        }
        else if (s->v.Expr.value->kind != Str_kind &&
                 s->v.Expr.value->kind != Num_kind) {
            { if (!compiler_visit_expr((c), (s->v.Expr.value))) return 0; };
            { if (!compiler_addop((c), (1))) return 0; };
        }
        break;
    case Pass_kind:
        break;
    case Break_kind:
        if (!compiler_in_loop(c))
            return compiler_error(c, "'break' outside loop");
        { if (!compiler_addop((c), (80))) return 0; };
        break;
    case Continue_kind:
        return compiler_continue(c);
    case With_kind:
        return compiler_with(c, s, 0);
    }
    return 1;
}

static int
unaryop(unaryop_ty op)
{
    switch (op) {
    case Invert:
        return 15;
    case Not:
        return 12;
    case UAdd:
        return 10;
    case USub:
        return 11;
    default:
        PyErr_Format(PyExc_SystemError,
            "unary op %d should not be possible", op);
        return 0;
    }
}

static int
binop(struct compiler *c, operator_ty op)
{
    switch (op) {
    case Add:
        return 23;
    case Sub:
        return 24;
    case Mult:
        return 20;
    case Div:
        return 27;
    case Mod:
        return 22;
    case Pow:
        return 19;
    case LShift:
        return 62;
    case RShift:
        return 63;
    case BitOr:
        return 66;
    case BitXor:
        return 65;
    case BitAnd:
        return 64;
    case FloorDiv:
        return 26;
    default:
        PyErr_Format(PyExc_SystemError,
            "binary op %d should not be possible", op);
        return 0;
    }
}

static int
cmpop(cmpop_ty op)
{
    switch (op) {
    case Eq:
        return PyCmp_EQ;
    case NotEq:
        return PyCmp_NE;
    case Lt:
        return PyCmp_LT;
    case LtE:
        return PyCmp_LE;
    case Gt:
        return PyCmp_GT;
    case GtE:
        return PyCmp_GE;
    case Is:
        return PyCmp_IS;
    case IsNot:
        return PyCmp_IS_NOT;
    case In:
        return PyCmp_IN;
    case NotIn:
        return PyCmp_NOT_IN;
    default:
        return PyCmp_BAD;
    }
}

static int
inplace_binop(struct compiler *c, operator_ty op)
{
    switch (op) {
    case Add:
        return 55;
    case Sub:
        return 56;
    case Mult:
        return 57;
    case Div:
        return 29;
    case Mod:
        return 59;
    case Pow:
        return 67;
    case LShift:
        return 75;
    case RShift:
        return 76;
    case BitOr:
        return 79;
    case BitXor:
        return 78;
    case BitAnd:
        return 77;
    case FloorDiv:
        return 28;
    default:
        PyErr_Format(PyExc_SystemError,
            "inplace binary op %d should not be possible", op);
        return 0;
    }
}

static int
compiler_nameop(struct compiler *c, identifier name, expr_context_ty ctx)
{
    int op, scope, arg;
    enum { OP_FAST, OP_GLOBAL, OP_DEREF, OP_NAME } optype;

    PyObject *dict = c->u->u_names;
    PyObject *mangled;


    mangled = _Py_Mangle(c->u->u_private, name);
    if (!mangled)
        return 0;

    op = 0;
    optype = OP_NAME;
    scope = PyST_GetScope(c->u->u_ste, mangled);
    switch (scope) {
    case 4:
        dict = c->u->u_freevars;
        optype = OP_DEREF;
        break;
    case 5:
        dict = c->u->u_cellvars;
        optype = OP_DEREF;
        break;
    case 1:
        if (c->u->u_ste->ste_type == FunctionBlock)
            optype = OP_FAST;
        break;
    case 3:
        if (c->u->u_ste->ste_type == FunctionBlock &&
            !c->u->u_ste->ste_unoptimized)
            optype = OP_GLOBAL;
        break;
    case 2:
        optype = OP_GLOBAL;
        break;
    default:

        break;
    }


    (__builtin_expect(!(scope || ((__builtin_expect(!(((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2668, "PyUnicode_Check(name)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)name)->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 2668, "PyUnicode_IS_READY(name)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2668, "PyUnicode_Check((name))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(name))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 2668, "PyUnicode_IS_READY((name))") : (void)0), ((PyASCIIObject *)((name)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2668, "PyUnicode_Check((name))") : (void)0), (((PyASCIIObject*)((name)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2668, "PyUnicode_Check((name))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(name))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 2668, "PyUnicode_IS_READY((name))") : (void)0), ((PyASCIIObject*)(name))->state.ascii) ? ((void*)((PyASCIIObject*)((name)) + 1)) : ((void*)((PyCompactUnicodeObject*)((name)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((name)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 2668, "((PyUnicodeObject*)((name)))->data.any") : (void)0), ((((PyUnicodeObject *)((name)))->data.any))))))[(0)] : (((__builtin_expect(!(((((((PyObject*)((name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2668, "PyUnicode_Check((name))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(name))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 2668, "PyUnicode_IS_READY((name))") : (void)0), ((PyASCIIObject *)((name)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2668, "PyUnicode_Check((name))") : (void)0), (((PyASCIIObject*)((name)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2668, "PyUnicode_Check((name))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(name))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 2668, "PyUnicode_IS_READY((name))") : (void)0), ((PyASCIIObject*)(name))->state.ascii) ? ((void*)((PyASCIIObject*)((name)) + 1)) : ((void*)((PyCompactUnicodeObject*)((name)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((name)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 2668, "((PyUnicodeObject*)((name)))->data.any") : (void)0), ((((PyUnicodeObject *)((name)))->data.any))))))[(0)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2668, "PyUnicode_Check((name))") : (void)0), (((PyASCIIObject*)((name)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((name)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 2668, "PyUnicode_Check((name))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(name))->state.ready)), 0) ? __assert_rtn(__func__, "compile.c", 2668, "PyUnicode_IS_READY((name))") : (void)0), ((PyASCIIObject*)(name))->state.ascii) ? ((void*)((PyASCIIObject*)((name)) + 1)) : ((void*)((PyCompactUnicodeObject*)((name)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((name)))->data.any), 0) ? __assert_rtn(__func__, "compile.c", 2668, "((PyUnicodeObject*)((name)))->data.any") : (void)0), ((((PyUnicodeObject *)((name)))->data.any))))))[(0)] ) )) == '_'), 0) ? __assert_rtn(__func__, "compile.c", 2668, "scope || PyUnicode_READ_CHAR(name, 0) == '_'") : (void)0);

    switch (optype) {
    case OP_DEREF:
        switch (ctx) {
        case Load: op = 136; break;
        case Store: op = 137; break;
        case AugLoad:
        case AugStore:
            break;
        case Del: op = 138; break;
        case Param:
        default:
            PyErr_SetString(PyExc_SystemError,
                            "param invalid for deref variable");
            return 0;
        }
        break;
    case OP_FAST:
        switch (ctx) {
        case Load: op = 124; break;
        case Store: op = 125; break;
        case Del: op = 126; break;
        case AugLoad:
        case AugStore:
            break;
        case Param:
        default:
            PyErr_SetString(PyExc_SystemError,
                            "param invalid for local variable");
            return 0;
        }
        { if (!compiler_addop_o((c), (op), (c)->u->u_varnames, (mangled))) return 0; };
        do { if ( --((PyObject*)(mangled))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(mangled)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(mangled)))); } while (0);
        return 1;
    case OP_GLOBAL:
        switch (ctx) {
        case Load: op = 116; break;
        case Store: op = 97; break;
        case Del: op = 98; break;
        case AugLoad:
        case AugStore:
            break;
        case Param:
        default:
            PyErr_SetString(PyExc_SystemError,
                            "param invalid for global variable");
            return 0;
        }
        break;
    case OP_NAME:
        switch (ctx) {
        case Load: op = 101; break;
        case Store: op = 90; break;
        case Del: op = 91; break;
        case AugLoad:
        case AugStore:
            break;
        case Param:
        default:
            PyErr_SetString(PyExc_SystemError,
                            "param invalid for name variable");
            return 0;
        }
        break;
    }

    (__builtin_expect(!(op), 0) ? __assert_rtn(__func__, "compile.c", 2735, "op") : (void)0);
    arg = compiler_add_o(c, dict, mangled);
    do { if ( --((PyObject*)(mangled))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(mangled)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(mangled)))); } while (0);
    if (arg < 0)
        return 0;
    return compiler_addop_i(c, op, arg);
}

static int
compiler_boolop(struct compiler *c, expr_ty e)
{
    basicblock *end;
    int jumpi, i, n;
    asdl_seq *s;

    (__builtin_expect(!(e->kind == BoolOp_kind), 0) ? __assert_rtn(__func__, "compile.c", 2750, "e->kind == BoolOp_kind") : (void)0);
    if (e->v.BoolOp.op == And)
        jumpi = 111;
    else
        jumpi = 112;
    end = compiler_new_block(c);
    if (end == ((void *)0))
        return 0;
    s = e->v.BoolOp.values;
    n = ((s) == ((void *)0) ? 0 : (s)->size) - 1;
    (__builtin_expect(!(n >= 0), 0) ? __assert_rtn(__func__, "compile.c", 2760, "n >= 0") : (void)0);
    for (i = 0; i < n; ++i) {
        { if (!compiler_visit_expr((c), ((expr_ty)(s)->elements[(i)]))) return 0; };
        { if (!compiler_addop_j((c), (jumpi), (end), 1)) return 0; };
    }
    { if (!compiler_visit_expr((c), ((expr_ty)(s)->elements[(n)]))) return 0; };
    compiler_use_next_block(c, end);
    return 1;
}

static int
compiler_list(struct compiler *c, expr_ty e)
{
    int n = ((e->v.List.elts) == ((void *)0) ? 0 : (e->v.List.elts)->size);
    if (e->v.List.ctx == Store) {
        int i, seen_star = 0;
        for (i = 0; i < n; i++) {
            expr_ty elt = (e->v.List.elts)->elements[(i)];
            if (elt->kind == Starred_kind && !seen_star) {
                if ((i >= (1 << 8)) ||
                    (n-i-1 >= (2147483647 >> 8)))
                    return compiler_error(c,
                        "too many expressions in "
                        "star-unpacking assignment");
                { if (!compiler_addop_i((c), (94), ((i + ((n-i-1) << 8))))) return 0; };
                seen_star = 1;
                (e->v.List.elts)->elements[i] = (elt->v.Starred.value);
            } else if (elt->kind == Starred_kind) {
                return compiler_error(c,
                    "two starred expressions in assignment");
            }
        }
        if (!seen_star) {
            { if (!compiler_addop_i((c), (92), (n))) return 0; };
        }
    }
    { int _i; asdl_seq *seq = (e->v.List.elts); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { expr_ty elt = (expr_ty)(seq)->elements[(_i)]; if (!compiler_visit_expr((c), elt)) return 0; } };
    if (e->v.List.ctx == Load) {
        { if (!compiler_addop_i((c), (103), (n))) return 0; };
    }
    return 1;
}

static int
compiler_tuple(struct compiler *c, expr_ty e)
{
    int n = ((e->v.Tuple.elts) == ((void *)0) ? 0 : (e->v.Tuple.elts)->size);
    if (e->v.Tuple.ctx == Store) {
        int i, seen_star = 0;
        for (i = 0; i < n; i++) {
            expr_ty elt = (e->v.Tuple.elts)->elements[(i)];
            if (elt->kind == Starred_kind && !seen_star) {
                if ((i >= (1 << 8)) ||
                    (n-i-1 >= (2147483647 >> 8)))
                    return compiler_error(c,
                        "too many expressions in "
                        "star-unpacking assignment");
                { if (!compiler_addop_i((c), (94), ((i + ((n-i-1) << 8))))) return 0; };
                seen_star = 1;
                (e->v.Tuple.elts)->elements[i] = (elt->v.Starred.value);
            } else if (elt->kind == Starred_kind) {
                return compiler_error(c,
                    "two starred expressions in assignment");
            }
        }
        if (!seen_star) {
            { if (!compiler_addop_i((c), (92), (n))) return 0; };
        }
    }
    { int _i; asdl_seq *seq = (e->v.Tuple.elts); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { expr_ty elt = (expr_ty)(seq)->elements[(_i)]; if (!compiler_visit_expr((c), elt)) return 0; } };
    if (e->v.Tuple.ctx == Load) {
        { if (!compiler_addop_i((c), (102), (n))) return 0; };
    }
    return 1;
}

static int
compiler_compare(struct compiler *c, expr_ty e)
{
    int i, n;
    basicblock *cleanup = ((void *)0);


    { if (!compiler_visit_expr((c), (e->v.Compare.left))) return 0; };
    n = ((e->v.Compare.ops) == ((void *)0) ? 0 : (e->v.Compare.ops)->size);
    (__builtin_expect(!(n > 0), 0) ? __assert_rtn(__func__, "compile.c", 2845, "n > 0") : (void)0);
    if (n > 1) {
        cleanup = compiler_new_block(c);
        if (cleanup == ((void *)0))
            return 0;
        { if (!compiler_visit_expr((c), ((expr_ty)(e->v.Compare.comparators)->elements[(0)]))) return 0; };

    }
    for (i = 1; i < n; i++) {
        { if (!compiler_addop((c), (4))) return 0; };
        { if (!compiler_addop((c), (3))) return 0; };
        { if (!compiler_addop_i((c), (107), (cmpop((cmpop_ty)((e->v.Compare.ops)->elements[(i - 1)]))))) return 0; };


        { if (!compiler_addop_j((c), (111), (cleanup), 1)) return 0; };
        { if (compiler_next_block((c)) == ((void *)0)) return 0; };
        if (i < (n - 1))
            { if (!compiler_visit_expr((c), ((expr_ty)(e->v.Compare.comparators)->elements[(i)]))) return 0; };

    }
    { if (!compiler_visit_expr((c), ((expr_ty)(e->v.Compare.comparators)->elements[(n - 1)]))) return 0; };
    { if (!compiler_addop_i((c), (107), (cmpop((cmpop_ty)((e->v.Compare.ops)->elements[(n - 1)]))))) return 0; };

    if (n > 1) {
        basicblock *end = compiler_new_block(c);
        if (end == ((void *)0))
            return 0;
        { if (!compiler_addop_j((c), (110), (end), 0)) return 0; };
        compiler_use_next_block(c, cleanup);
        { if (!compiler_addop((c), (2))) return 0; };
        { if (!compiler_addop((c), (1))) return 0; };
        compiler_use_next_block(c, end);
    }
    return 1;
}

static int
compiler_call(struct compiler *c, expr_ty e)
{
    { if (!compiler_visit_expr((c), (e->v.Call.func))) return 0; };
    return compiler_call_helper(c, 0,
                                e->v.Call.args,
                                e->v.Call.keywords,
                                e->v.Call.starargs,
                                e->v.Call.kwargs);
}


static int
compiler_call_helper(struct compiler *c,
                     int n,
             asdl_seq *args,
             asdl_seq *keywords,
             expr_ty starargs,
             expr_ty kwargs)
{
    int code = 0;

    n += ((args) == ((void *)0) ? 0 : (args)->size);
    { int _i; asdl_seq *seq = (args); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { expr_ty elt = (expr_ty)(seq)->elements[(_i)]; if (!compiler_visit_expr((c), elt)) return 0; } };
    if (keywords) {
        { int _i; asdl_seq *seq = (keywords); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { keyword_ty elt = (keyword_ty)(seq)->elements[(_i)]; if (!compiler_visit_keyword((c), elt)) return 0; } };
        n |= ((keywords) == ((void *)0) ? 0 : (keywords)->size) << 8;
    }
    if (starargs) {
        { if (!compiler_visit_expr((c), (starargs))) return 0; };
        code |= 1;
    }
    if (kwargs) {
        { if (!compiler_visit_expr((c), (kwargs))) return 0; };
        code |= 2;
    }
    switch (code) {
    case 0:
        { if (!compiler_addop_i((c), (131), (n))) return 0; };
        break;
    case 1:
        { if (!compiler_addop_i((c), (140), (n))) return 0; };
        break;
    case 2:
        { if (!compiler_addop_i((c), (141), (n))) return 0; };
        break;
    case 3:
        { if (!compiler_addop_i((c), (142), (n))) return 0; };
        break;
    }
    return 1;
}
# 2950 "compile.c"
static int
compiler_comprehension_generator(struct compiler *c,
                                 asdl_seq *generators, int gen_index,
                                 expr_ty elt, expr_ty val, int type)
{



    comprehension_ty gen;
    basicblock *start, *anchor, *skip, *if_cleanup;
    int i, n;

    start = compiler_new_block(c);
    skip = compiler_new_block(c);
    if_cleanup = compiler_new_block(c);
    anchor = compiler_new_block(c);

    if (start == ((void *)0) || skip == ((void *)0) || if_cleanup == ((void *)0) ||
        anchor == ((void *)0))
        return 0;

    gen = (comprehension_ty)(generators)->elements[(gen_index)];

    if (gen_index == 0) {

        c->u->u_argcount = 1;
        { if (!compiler_addop_i((c), (124), (0))) return 0; };
    }
    else {

        { if (!compiler_visit_expr((c), (gen->iter))) return 0; };
        { if (!compiler_addop((c), (68))) return 0; };
    }
    compiler_use_next_block(c, start);
    { if (!compiler_addop_j((c), (93), (anchor), 0)) return 0; };
    { if (compiler_next_block((c)) == ((void *)0)) return 0; };
    { if (!compiler_visit_expr((c), (gen->target))) return 0; };


    n = ((gen->ifs) == ((void *)0) ? 0 : (gen->ifs)->size);
    for (i = 0; i < n; i++) {
        expr_ty e = (expr_ty)(gen->ifs)->elements[(i)];
        { if (!compiler_visit_expr((c), (e))) return 0; };
        { if (!compiler_addop_j((c), (114), (if_cleanup), 1)) return 0; };
        { if (compiler_next_block((c)) == ((void *)0)) return 0; };
    }

    if (++gen_index < ((generators) == ((void *)0) ? 0 : (generators)->size))
        if (!compiler_comprehension_generator(c,
                                              generators, gen_index,
                                              elt, val, type))
        return 0;


    if (gen_index >= ((generators) == ((void *)0) ? 0 : (generators)->size)) {

        switch (type) {
        case 0:
            { if (!compiler_visit_expr((c), (elt))) return 0; };
            { if (!compiler_addop((c), (86))) return 0; };
            { if (!compiler_addop((c), (1))) return 0; };
            break;
        case 1:
            { if (!compiler_visit_expr((c), (elt))) return 0; };
            { if (!compiler_addop_i((c), (145), (gen_index + 1))) return 0; };
            break;
        case 2:
            { if (!compiler_visit_expr((c), (elt))) return 0; };
            { if (!compiler_addop_i((c), (146), (gen_index + 1))) return 0; };
            break;
        case 3:


            { if (!compiler_visit_expr((c), (val))) return 0; };
            { if (!compiler_visit_expr((c), (elt))) return 0; };
            { if (!compiler_addop_i((c), (147), (gen_index + 1))) return 0; };
            break;
        default:
            return 0;
        }

        compiler_use_next_block(c, skip);
    }
    compiler_use_next_block(c, if_cleanup);
    { if (!compiler_addop_j((c), (113), (start), 1)) return 0; };
    compiler_use_next_block(c, anchor);

    return 1;
}

static int
compiler_comprehension(struct compiler *c, expr_ty e, int type, identifier name,
                       asdl_seq *generators, expr_ty elt, expr_ty val)
{
    PyCodeObject *co = ((void *)0);
    expr_ty outermost_iter;
    PyObject *qualname = ((void *)0);

    outermost_iter = ((comprehension_ty)
                      (generators)->elements[(0)])->iter;

    if (!compiler_enter_scope(c, name, COMPILER_SCOPE_COMPREHENSION,
                              (void *)e, e->lineno))
        goto error;

    if (type != 0) {
        int op;
        switch (type) {
        case 1:
            op = 103;
            break;
        case 2:
            op = 104;
            break;
        case 3:
            op = 105;
            break;
        default:
            PyErr_Format(PyExc_SystemError,
                         "unknown comprehension type %d", type);
            goto error_in_scope;
        }

        { if (!compiler_addop_i((c), (op), (0))) return 0; };
    }

    if (!compiler_comprehension_generator(c, generators, 0, elt,
                                          val, type))
        goto error_in_scope;

    if (type != 0) {
        { if (!compiler_addop((c), (83))) return 0; };
    }

    co = assemble(c, 1);
    qualname = compiler_scope_qualname(c);
    compiler_exit_scope(c);
    if (qualname == ((void *)0) || co == ((void *)0))
        goto error;

    if (!compiler_make_closure(c, co, 0, qualname))
        goto error;
    do { if ( --((PyObject*)(qualname))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(qualname)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(qualname)))); } while (0);
    do { if ( --((PyObject*)(co))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(co)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(co)))); } while (0);

    { if (!compiler_visit_expr((c), (outermost_iter))) return 0; };
    { if (!compiler_addop((c), (68))) return 0; };
    { if (!compiler_addop_i((c), (131), (1))) return 0; };
    return 1;
error_in_scope:
    compiler_exit_scope(c);
error:
    do { if ((qualname) == ((void *)0)) ; else do { if ( --((PyObject*)(qualname))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(qualname)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(qualname)))); } while (0); } while (0);
    do { if ((co) == ((void *)0)) ; else do { if ( --((PyObject*)(co))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(co)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(co)))); } while (0); } while (0);
    return 0;
}

static int
compiler_genexp(struct compiler *c, expr_ty e)
{
    static identifier name;
    if (!name) {
        name = PyUnicode_FromString("<genexpr>");
        if (!name)
            return 0;
    }
    (__builtin_expect(!(e->kind == GeneratorExp_kind), 0) ? __assert_rtn(__func__, "compile.c", 3116, "e->kind == GeneratorExp_kind") : (void)0);
    return compiler_comprehension(c, e, 0, name,
                                  e->v.GeneratorExp.generators,
                                  e->v.GeneratorExp.elt, ((void *)0));
}

static int
compiler_listcomp(struct compiler *c, expr_ty e)
{
    static identifier name;
    if (!name) {
        name = PyUnicode_FromString("<listcomp>");
        if (!name)
            return 0;
    }
    (__builtin_expect(!(e->kind == ListComp_kind), 0) ? __assert_rtn(__func__, "compile.c", 3131, "e->kind == ListComp_kind") : (void)0);
    return compiler_comprehension(c, e, 1, name,
                                  e->v.ListComp.generators,
                                  e->v.ListComp.elt, ((void *)0));
}

static int
compiler_setcomp(struct compiler *c, expr_ty e)
{
    static identifier name;
    if (!name) {
        name = PyUnicode_FromString("<setcomp>");
        if (!name)
            return 0;
    }
    (__builtin_expect(!(e->kind == SetComp_kind), 0) ? __assert_rtn(__func__, "compile.c", 3146, "e->kind == SetComp_kind") : (void)0);
    return compiler_comprehension(c, e, 2, name,
                                  e->v.SetComp.generators,
                                  e->v.SetComp.elt, ((void *)0));
}


static int
compiler_dictcomp(struct compiler *c, expr_ty e)
{
    static identifier name;
    if (!name) {
        name = PyUnicode_FromString("<dictcomp>");
        if (!name)
            return 0;
    }
    (__builtin_expect(!(e->kind == DictComp_kind), 0) ? __assert_rtn(__func__, "compile.c", 3162, "e->kind == DictComp_kind") : (void)0);
    return compiler_comprehension(c, e, 3, name,
                                  e->v.DictComp.generators,
                                  e->v.DictComp.key, e->v.DictComp.value);
}


static int
compiler_visit_keyword(struct compiler *c, keyword_ty k)
{
    { if (!compiler_addop_o((c), (100), (c)->u->u_consts, (k->arg))) return 0; };
    { if (!compiler_visit_expr((c), (k->value))) return 0; };
    return 1;
}







static int
expr_constant(struct compiler *c, expr_ty e)
{
    char *id;
    switch (e->kind) {
    case Ellipsis_kind:
        return 1;
    case Num_kind:
        return PyObject_IsTrue(e->v.Num.n);
    case Str_kind:
        return PyObject_IsTrue(e->v.Str.s);
    case Name_kind:

        id = PyUnicode_AsUTF8(e->v.Name.id);
        if (strcmp(id, "True") == 0) return 1;
        if (strcmp(id, "False") == 0) return 0;
        if (strcmp(id, "None") == 0) return 0;
        if (strcmp(id, "__debug__") == 0)
            return ! c->c_optimize;

    default:
        return -1;
    }
}
# 3231 "compile.c"
static int
compiler_with(struct compiler *c, stmt_ty s, int pos)
{
    basicblock *block, *finally;
    withitem_ty item = (s->v.With.items)->elements[(pos)];

    (__builtin_expect(!(s->kind == With_kind), 0) ? __assert_rtn(__func__, "compile.c", 3237, "s->kind == With_kind") : (void)0);

    block = compiler_new_block(c);
    finally = compiler_new_block(c);
    if (!block || !finally)
        return 0;


    { if (!compiler_visit_expr((c), (item->context_expr))) return 0; };
    { if (!compiler_addop_j((c), (143), (finally), 0)) return 0; };


    compiler_use_next_block(c, block);
    if (!compiler_push_fblock(c, FINALLY_TRY, block)) {
        return 0;
    }

    if (item->optional_vars) {
        { if (!compiler_visit_expr((c), (item->optional_vars))) return 0; };
    }
    else {

        { if (!compiler_addop((c), (1))) return 0; };
    }

    pos++;
    if (pos == ((s->v.With.items) == ((void *)0) ? 0 : (s->v.With.items)->size))

        { int _i; asdl_seq *seq = (s->v.With.body); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { stmt_ty elt = (stmt_ty)(seq)->elements[(_i)]; if (!compiler_visit_stmt((c), elt)) return 0; } }
    else if (!compiler_with(c, s, pos))
            return 0;


    { if (!compiler_addop((c), (87))) return 0; };
    compiler_pop_fblock(c, FINALLY_TRY, block);

    { if (!compiler_addop_o((c), (100), (c)->u->u_consts, ((&_Py_NoneStruct)))) return 0; };
    compiler_use_next_block(c, finally);
    if (!compiler_push_fblock(c, FINALLY_END, finally))
        return 0;




    { if (!compiler_addop((c), (81))) return 0; };


    { if (!compiler_addop((c), (88))) return 0; };
    compiler_pop_fblock(c, FINALLY_END, finally);
    return 1;
}

static int
compiler_visit_expr(struct compiler *c, expr_ty e)
{
    int i, n;




    if (e->lineno > c->u->u_lineno) {
        c->u->u_lineno = e->lineno;
        c->u->u_lineno_set = 0;
    }

    c->u->u_col_offset = e->col_offset;
    switch (e->kind) {
    case BoolOp_kind:
        return compiler_boolop(c, e);
    case BinOp_kind:
        { if (!compiler_visit_expr((c), (e->v.BinOp.left))) return 0; };
        { if (!compiler_visit_expr((c), (e->v.BinOp.right))) return 0; };
        { if (!compiler_addop((c), (binop(c, e->v.BinOp.op)))) return 0; };
        break;
    case UnaryOp_kind:
        { if (!compiler_visit_expr((c), (e->v.UnaryOp.operand))) return 0; };
        { if (!compiler_addop((c), (unaryop(e->v.UnaryOp.op)))) return 0; };
        break;
    case Lambda_kind:
        return compiler_lambda(c, e);
    case IfExp_kind:
        return compiler_ifexp(c, e);
    case Dict_kind:
        n = ((e->v.Dict.values) == ((void *)0) ? 0 : (e->v.Dict.values)->size);
        { if (!compiler_addop_i((c), (105), ((n>0xFFFF ? 0xFFFF : n)))) return 0; };
        for (i = 0; i < n; i++) {
            { if (!compiler_visit_expr((c), ((expr_ty)(e->v.Dict.values)->elements[(i)]))) return 0; };

            { if (!compiler_visit_expr((c), ((expr_ty)(e->v.Dict.keys)->elements[(i)]))) return 0; };

            { if (!compiler_addop((c), (54))) return 0; };
        }
        break;
    case Set_kind:
        n = ((e->v.Set.elts) == ((void *)0) ? 0 : (e->v.Set.elts)->size);
        { int _i; asdl_seq *seq = (e->v.Set.elts); for (_i = 0; _i < ((seq) == ((void *)0) ? 0 : (seq)->size); _i++) { expr_ty elt = (expr_ty)(seq)->elements[(_i)]; if (!compiler_visit_expr((c), elt)) return 0; } };
        { if (!compiler_addop_i((c), (104), (n))) return 0; };
        break;
    case GeneratorExp_kind:
        return compiler_genexp(c, e);
    case ListComp_kind:
        return compiler_listcomp(c, e);
    case SetComp_kind:
        return compiler_setcomp(c, e);
    case DictComp_kind:
        return compiler_dictcomp(c, e);
    case Yield_kind:
        if (c->u->u_ste->ste_type != FunctionBlock)
            return compiler_error(c, "'yield' outside function");
        if (e->v.Yield.value) {
            { if (!compiler_visit_expr((c), (e->v.Yield.value))) return 0; };
        }
        else {
            { if (!compiler_addop_o((c), (100), (c)->u->u_consts, ((&_Py_NoneStruct)))) return 0; };
        }
        { if (!compiler_addop((c), (86))) return 0; };
        break;
    case YieldFrom_kind:
        if (c->u->u_ste->ste_type != FunctionBlock)
            return compiler_error(c, "'yield' outside function");
        { if (!compiler_visit_expr((c), (e->v.YieldFrom.value))) return 0; };
        { if (!compiler_addop((c), (68))) return 0; };
        { if (!compiler_addop_o((c), (100), (c)->u->u_consts, ((&_Py_NoneStruct)))) return 0; };
        { if (!compiler_addop((c), (72))) return 0; };
        break;
    case Compare_kind:
        return compiler_compare(c, e);
    case Call_kind:
        return compiler_call(c, e);
    case Num_kind:
        { if (!compiler_addop_o((c), (100), (c)->u->u_consts, (e->v.Num.n))) return 0; };
        break;
    case Str_kind:
        { if (!compiler_addop_o((c), (100), (c)->u->u_consts, (e->v.Str.s))) return 0; };
        break;
    case Bytes_kind:
        { if (!compiler_addop_o((c), (100), (c)->u->u_consts, (e->v.Bytes.s))) return 0; };
        break;
    case Ellipsis_kind:
        { if (!compiler_addop_o((c), (100), (c)->u->u_consts, ((&_Py_EllipsisObject)))) return 0; };
        break;

    case Attribute_kind:
        if (e->v.Attribute.ctx != AugStore)
            { if (!compiler_visit_expr((c), (e->v.Attribute.value))) return 0; };
        switch (e->v.Attribute.ctx) {
        case AugLoad:
            { if (!compiler_addop((c), (4))) return 0; };

        case Load:
            { if (!compiler_addop_name((c), (106), (c)->u->u_names, (e->v.Attribute.attr))) return 0; };
            break;
        case AugStore:
            { if (!compiler_addop((c), (2))) return 0; };

        case Store:
            { if (!compiler_addop_name((c), (95), (c)->u->u_names, (e->v.Attribute.attr))) return 0; };
            break;
        case Del:
            { if (!compiler_addop_name((c), (96), (c)->u->u_names, (e->v.Attribute.attr))) return 0; };
            break;
        case Param:
        default:
            PyErr_SetString(PyExc_SystemError,
                            "param invalid in attribute expression");
            return 0;
        }
        break;
    case Subscript_kind:
        switch (e->v.Subscript.ctx) {
        case AugLoad:
            { if (!compiler_visit_expr((c), (e->v.Subscript.value))) return 0; };
            { if (!compiler_visit_slice((c), (e->v.Subscript.slice), (AugLoad))) return 0; };
            break;
        case Load:
            { if (!compiler_visit_expr((c), (e->v.Subscript.value))) return 0; };
            { if (!compiler_visit_slice((c), (e->v.Subscript.slice), (Load))) return 0; };
            break;
        case AugStore:
            { if (!compiler_visit_slice((c), (e->v.Subscript.slice), (AugStore))) return 0; };
            break;
        case Store:
            { if (!compiler_visit_expr((c), (e->v.Subscript.value))) return 0; };
            { if (!compiler_visit_slice((c), (e->v.Subscript.slice), (Store))) return 0; };
            break;
        case Del:
            { if (!compiler_visit_expr((c), (e->v.Subscript.value))) return 0; };
            { if (!compiler_visit_slice((c), (e->v.Subscript.slice), (Del))) return 0; };
            break;
        case Param:
        default:
            PyErr_SetString(PyExc_SystemError,
                "param invalid in subscript expression");
            return 0;
        }
        break;
    case Starred_kind:
        switch (e->v.Starred.ctx) {
        case Store:


            return compiler_error(c,
                "starred assignment target must be in a list or tuple");
        default:
            return compiler_error(c,
                "can use starred expression only as assignment target");
        }
        break;
    case Name_kind:
        return compiler_nameop(c, e->v.Name.id, e->v.Name.ctx);

    case List_kind:
        return compiler_list(c, e);
    case Tuple_kind:
        return compiler_tuple(c, e);
    }
    return 1;
}

static int
compiler_augassign(struct compiler *c, stmt_ty s)
{
    expr_ty e = s->v.AugAssign.target;
    expr_ty auge;

    (__builtin_expect(!(s->kind == AugAssign_kind), 0) ? __assert_rtn(__func__, "compile.c", 3462, "s->kind == AugAssign_kind") : (void)0);

    switch (e->kind) {
    case Attribute_kind:
        auge = _Py_Attribute(e->v.Attribute.value, e->v.Attribute.attr, AugLoad, e->lineno, e->col_offset, c->c_arena);

        if (auge == ((void *)0))
            return 0;
        { if (!compiler_visit_expr((c), (auge))) return 0; };
        { if (!compiler_visit_expr((c), (s->v.AugAssign.value))) return 0; };
        { if (!compiler_addop((c), (inplace_binop(c, s->v.AugAssign.op)))) return 0; };
        auge->v.Attribute.ctx = AugStore;
        { if (!compiler_visit_expr((c), (auge))) return 0; };
        break;
    case Subscript_kind:
        auge = _Py_Subscript(e->v.Subscript.value, e->v.Subscript.slice, AugLoad, e->lineno, e->col_offset, c->c_arena);

        if (auge == ((void *)0))
            return 0;
        { if (!compiler_visit_expr((c), (auge))) return 0; };
        { if (!compiler_visit_expr((c), (s->v.AugAssign.value))) return 0; };
        { if (!compiler_addop((c), (inplace_binop(c, s->v.AugAssign.op)))) return 0; };
        auge->v.Subscript.ctx = AugStore;
        { if (!compiler_visit_expr((c), (auge))) return 0; };
        break;
    case Name_kind:
        if (!compiler_nameop(c, e->v.Name.id, Load))
            return 0;
        { if (!compiler_visit_expr((c), (s->v.AugAssign.value))) return 0; };
        { if (!compiler_addop((c), (inplace_binop(c, s->v.AugAssign.op)))) return 0; };
        return compiler_nameop(c, e->v.Name.id, Store);
    default:
        PyErr_Format(PyExc_SystemError,
            "invalid node type (%d) for augmented assignment",
            e->kind);
        return 0;
    }
    return 1;
}

static int
compiler_push_fblock(struct compiler *c, enum fblocktype t, basicblock *b)
{
    struct fblockinfo *f;
    if (c->u->u_nfblocks >= 20) {
        PyErr_SetString(PyExc_SystemError,
                        "too many statically nested blocks");
        return 0;
    }
    f = &c->u->u_fblock[c->u->u_nfblocks++];
    f->fb_type = t;
    f->fb_block = b;
    return 1;
}

static void
compiler_pop_fblock(struct compiler *c, enum fblocktype t, basicblock *b)
{
    struct compiler_unit *u = c->u;
    (__builtin_expect(!(u->u_nfblocks > 0), 0) ? __assert_rtn(__func__, "compile.c", 3521, "u->u_nfblocks > 0") : (void)0);
    u->u_nfblocks--;
    (__builtin_expect(!(u->u_fblock[u->u_nfblocks].fb_type == t), 0) ? __assert_rtn(__func__, "compile.c", 3523, "u->u_fblock[u->u_nfblocks].fb_type == t") : (void)0);
    (__builtin_expect(!(u->u_fblock[u->u_nfblocks].fb_block == b), 0) ? __assert_rtn(__func__, "compile.c", 3524, "u->u_fblock[u->u_nfblocks].fb_block == b") : (void)0);
}

static int
compiler_in_loop(struct compiler *c) {
    int i;
    struct compiler_unit *u = c->u;
    for (i = 0; i < u->u_nfblocks; ++i) {
        if (u->u_fblock[i].fb_type == LOOP)
            return 1;
    }
    return 0;
}




static int
compiler_error(struct compiler *c, const char *errstr)
{
    PyObject *loc;
    PyObject *u = ((void *)0), *v = ((void *)0);

    loc = PyErr_ProgramText(c->c_filename, c->u->u_lineno);
    if (!loc) {
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        loc = (&_Py_NoneStruct);
    }
    u = Py_BuildValue("(OiiO)", c->c_filename_obj, c->u->u_lineno,
                      c->u->u_col_offset, loc);
    if (!u)
        goto exit;
    v = Py_BuildValue("(zO)", errstr, u);
    if (!v)
        goto exit;
    PyErr_SetObject(PyExc_SyntaxError, v);
 exit:
    do { if ( --((PyObject*)(loc))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(loc)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(loc)))); } while (0);
    do { if ((u) == ((void *)0)) ; else do { if ( --((PyObject*)(u))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(u)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(u)))); } while (0); } while (0);
    do { if ((v) == ((void *)0)) ; else do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0); } while (0);
    return 0;
}

static int
compiler_handle_subscr(struct compiler *c, const char *kind,
                       expr_context_ty ctx)
{
    int op = 0;


    switch (ctx) {
        case AugLoad:
        case Load: op = 25; break;
        case AugStore:
        case Store: op = 60; break;
        case Del: op = 61; break;
        case Param:
            PyErr_Format(PyExc_SystemError,
                         "invalid %s kind %d in subscript\n",
                         kind, ctx);
            return 0;
    }
    if (ctx == AugLoad) {
        { if (!compiler_addop((c), (5))) return 0; };
    }
    else if (ctx == AugStore) {
        { if (!compiler_addop((c), (3))) return 0; };
    }
    { if (!compiler_addop((c), (op))) return 0; };
    return 1;
}

static int
compiler_slice(struct compiler *c, slice_ty s, expr_context_ty ctx)
{
    int n = 2;
    (__builtin_expect(!(s->kind == Slice_kind), 0) ? __assert_rtn(__func__, "compile.c", 3600, "s->kind == Slice_kind") : (void)0);


    if (s->v.Slice.lower) {
        { if (!compiler_visit_expr((c), (s->v.Slice.lower))) return 0; };
    }
    else {
        { if (!compiler_addop_o((c), (100), (c)->u->u_consts, ((&_Py_NoneStruct)))) return 0; };
    }

    if (s->v.Slice.upper) {
        { if (!compiler_visit_expr((c), (s->v.Slice.upper))) return 0; };
    }
    else {
        { if (!compiler_addop_o((c), (100), (c)->u->u_consts, ((&_Py_NoneStruct)))) return 0; };
    }

    if (s->v.Slice.step) {
        n++;
        { if (!compiler_visit_expr((c), (s->v.Slice.step))) return 0; };
    }
    { if (!compiler_addop_i((c), (133), (n))) return 0; };
    return 1;
}

static int
compiler_visit_nested_slice(struct compiler *c, slice_ty s,
                            expr_context_ty ctx)
{
    switch (s->kind) {
    case Slice_kind:
        return compiler_slice(c, s, ctx);
    case Index_kind:
        { if (!compiler_visit_expr((c), (s->v.Index.value))) return 0; };
        break;
    case ExtSlice_kind:
    default:
        PyErr_SetString(PyExc_SystemError,
                        "extended slice invalid in nested slice");
        return 0;
    }
    return 1;
}

static int
compiler_visit_slice(struct compiler *c, slice_ty s, expr_context_ty ctx)
{
    char * kindname = ((void *)0);
    switch (s->kind) {
    case Index_kind:
        kindname = "index";
        if (ctx != AugStore) {
            { if (!compiler_visit_expr((c), (s->v.Index.value))) return 0; };
        }
        break;
    case Slice_kind:
        kindname = "slice";
        if (ctx != AugStore) {
            if (!compiler_slice(c, s, ctx))
                return 0;
        }
        break;
    case ExtSlice_kind:
        kindname = "extended slice";
        if (ctx != AugStore) {
            int i, n = ((s->v.ExtSlice.dims) == ((void *)0) ? 0 : (s->v.ExtSlice.dims)->size);
            for (i = 0; i < n; i++) {
                slice_ty sub = (slice_ty)(s->v.ExtSlice.dims)->elements[(i)];

                if (!compiler_visit_nested_slice(c, sub, ctx))
                    return 0;
            }
            { if (!compiler_addop_i((c), (102), (n))) return 0; };
        }
        break;
    default:
        PyErr_Format(PyExc_SystemError,
                     "invalid subscript kind %d", s->kind);
        return 0;
    }
    return compiler_handle_subscr(c, kindname, ctx);
}
# 3691 "compile.c"
struct assembler {
    PyObject *a_bytecode;
    int a_offset;
    int a_nblocks;
    basicblock **a_postorder;
    PyObject *a_lnotab;
    int a_lnotab_off;
    int a_lineno;
    int a_lineno_off;
};

static void
dfs(struct compiler *c, basicblock *b, struct assembler *a)
{
    int i;
    struct instr *instr = ((void *)0);

    if (b->b_seen)
        return;
    b->b_seen = 1;
    if (b->b_next != ((void *)0))
        dfs(c, b->b_next, a);
    for (i = 0; i < b->b_iused; i++) {
        instr = &b->b_instr[i];
        if (instr->i_jrel || instr->i_jabs)
            dfs(c, instr->i_target, a);
    }
    a->a_postorder[a->a_nblocks++] = b;
}

static int
stackdepth_walk(struct compiler *c, basicblock *b, int depth, int maxdepth)
{
    int i, target_depth;
    struct instr *instr;
    if (b->b_seen || b->b_startdepth >= depth)
        return maxdepth;
    b->b_seen = 1;
    b->b_startdepth = depth;
    for (i = 0; i < b->b_iused; i++) {
        instr = &b->b_instr[i];
        depth += opcode_stack_effect(instr->i_opcode, instr->i_oparg);
        if (depth > maxdepth)
            maxdepth = depth;
        (__builtin_expect(!(depth >= 0), 0) ? __assert_rtn(__func__, "compile.c", 3735, "depth >= 0") : (void)0);
        if (instr->i_jrel || instr->i_jabs) {
            target_depth = depth;
            if (instr->i_opcode == 93) {
                target_depth = depth-2;
            } else if (instr->i_opcode == 122 ||
                       instr->i_opcode == 121) {
                target_depth = depth+3;
                if (target_depth > maxdepth)
                    maxdepth = target_depth;
            }
            maxdepth = stackdepth_walk(c, instr->i_target,
                                       target_depth, maxdepth);
            if (instr->i_opcode == 113 ||
                instr->i_opcode == 110) {
                goto out;
            }
        }
    }
    if (b->b_next)
        maxdepth = stackdepth_walk(c, b->b_next, depth, maxdepth);
out:
    b->b_seen = 0;
    return maxdepth;
}




static int
stackdepth(struct compiler *c)
{
    basicblock *b, *entryblock;
    entryblock = ((void *)0);
    for (b = c->u->u_blocks; b != ((void *)0); b = b->b_list) {
        b->b_seen = 0;
        b->b_startdepth = (-2147483647 - 1);
        entryblock = b;
    }
    if (!entryblock)
        return 0;
    return stackdepth_walk(c, entryblock, 0, 0);
}

static int
assemble_init(struct assembler *a, int nblocks, int firstlineno)
{
    ((__builtin_object_size (a, 0) != (size_t) -1) ? __builtin___memset_chk (a, 0, sizeof(struct assembler), __builtin_object_size (a, 0)) : __inline_memset_chk (a, 0, sizeof(struct assembler)));
    a->a_lineno = firstlineno;
    a->a_bytecode = PyBytes_FromStringAndSize(((void *)0), 128);
    if (!a->a_bytecode)
        return 0;
    a->a_lnotab = PyBytes_FromStringAndSize(((void *)0), 16);
    if (!a->a_lnotab)
        return 0;
    if (nblocks > 18446744073709551615ULL / sizeof(basicblock *)) {
        PyErr_NoMemory();
        return 0;
    }
    a->a_postorder = (basicblock **)PyObject_Malloc(
                                        sizeof(basicblock *) * nblocks);
    if (!a->a_postorder) {
        PyErr_NoMemory();
        return 0;
    }
    return 1;
}

static void
assemble_free(struct assembler *a)
{
    do { if ((a->a_bytecode) == ((void *)0)) ; else do { if ( --((PyObject*)(a->a_bytecode))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(a->a_bytecode)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(a->a_bytecode)))); } while (0); } while (0);
    do { if ((a->a_lnotab) == ((void *)0)) ; else do { if ( --((PyObject*)(a->a_lnotab))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(a->a_lnotab)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(a->a_lnotab)))); } while (0); } while (0);
    if (a->a_postorder)
        PyObject_Free(a->a_postorder);
}



static int
instrsize(struct instr *instr)
{
    if (!instr->i_hasarg)
        return 1;
    if (instr->i_oparg > 0xffff)
        return 6;
    return 3;
}

static int
blocksize(basicblock *b)
{
    int i;
    int size = 0;

    for (i = 0; i < b->b_iused; i++)
        size += instrsize(&b->b_instr[i]);
    return size;
}





static int
assemble_lnotab(struct assembler *a, struct instr *i)
{
    int d_bytecode, d_lineno;
    int len;
    unsigned char *lnotab;

    d_bytecode = a->a_offset - a->a_lineno_off;
    d_lineno = i->i_lineno - a->a_lineno;

    (__builtin_expect(!(d_bytecode >= 0), 0) ? __assert_rtn(__func__, "compile.c", 3849, "d_bytecode >= 0") : (void)0);
    (__builtin_expect(!(d_lineno >= 0), 0) ? __assert_rtn(__func__, "compile.c", 3850, "d_lineno >= 0") : (void)0);

    if(d_bytecode == 0 && d_lineno == 0)
        return 1;

    if (d_bytecode > 255) {
        int j, nbytes, ncodes = d_bytecode / 255;
        nbytes = a->a_lnotab_off + 2 * ncodes;
        len = ((__builtin_expect(!(((((((PyObject*)(a->a_lnotab))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 3858, "PyBytes_Check(a->a_lnotab)") : (void)0),(((PyVarObject*)(a->a_lnotab))->ob_size));
        if (nbytes >= len) {
            if ((len <= 2147483647 / 2) && (len * 2 < nbytes))
                len = nbytes;
            else if (len <= 2147483647 / 2)
                len *= 2;
            else {
                PyErr_NoMemory();
                return 0;
            }
            if (_PyBytes_Resize(&a->a_lnotab, len) < 0)
                return 0;
        }
        lnotab = (unsigned char *)
                   ((__builtin_expect(!(((((((PyObject*)(a->a_lnotab))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 3872, "PyBytes_Check(a->a_lnotab)") : (void)0), (((PyBytesObject *)(a->a_lnotab))->ob_sval)) + a->a_lnotab_off;
        for (j = 0; j < ncodes; j++) {
            *lnotab++ = 255;
            *lnotab++ = 0;
        }
        d_bytecode -= ncodes * 255;
        a->a_lnotab_off += ncodes * 2;
    }
    (__builtin_expect(!(d_bytecode <= 255), 0) ? __assert_rtn(__func__, "compile.c", 3880, "d_bytecode <= 255") : (void)0);
    if (d_lineno > 255) {
        int j, nbytes, ncodes = d_lineno / 255;
        nbytes = a->a_lnotab_off + 2 * ncodes;
        len = ((__builtin_expect(!(((((((PyObject*)(a->a_lnotab))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 3884, "PyBytes_Check(a->a_lnotab)") : (void)0),(((PyVarObject*)(a->a_lnotab))->ob_size));
        if (nbytes >= len) {
            if ((len <= 2147483647 / 2) && len * 2 < nbytes)
                len = nbytes;
            else if (len <= 2147483647 / 2)
                len *= 2;
            else {
                PyErr_NoMemory();
                return 0;
            }
            if (_PyBytes_Resize(&a->a_lnotab, len) < 0)
                return 0;
        }
        lnotab = (unsigned char *)
                   ((__builtin_expect(!(((((((PyObject*)(a->a_lnotab))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 3898, "PyBytes_Check(a->a_lnotab)") : (void)0), (((PyBytesObject *)(a->a_lnotab))->ob_sval)) + a->a_lnotab_off;
        *lnotab++ = d_bytecode;
        *lnotab++ = 255;
        d_bytecode = 0;
        for (j = 1; j < ncodes; j++) {
            *lnotab++ = 0;
            *lnotab++ = 255;
        }
        d_lineno -= ncodes * 255;
        a->a_lnotab_off += ncodes * 2;
    }

    len = ((__builtin_expect(!(((((((PyObject*)(a->a_lnotab))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 3910, "PyBytes_Check(a->a_lnotab)") : (void)0),(((PyVarObject*)(a->a_lnotab))->ob_size));
    if (a->a_lnotab_off + 2 >= len) {
        if (_PyBytes_Resize(&a->a_lnotab, len * 2) < 0)
            return 0;
    }
    lnotab = (unsigned char *)
                    ((__builtin_expect(!(((((((PyObject*)(a->a_lnotab))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 3916, "PyBytes_Check(a->a_lnotab)") : (void)0), (((PyBytesObject *)(a->a_lnotab))->ob_sval)) + a->a_lnotab_off;

    a->a_lnotab_off += 2;
    if (d_bytecode) {
        *lnotab++ = d_bytecode;
        *lnotab++ = d_lineno;
    }
    else {
        *lnotab++ = 0;
        *lnotab++ = d_lineno;
    }
    a->a_lineno = i->i_lineno;
    a->a_lineno_off = a->a_offset;
    return 1;
}






static int
assemble_emit(struct assembler *a, struct instr *i)
{
    int size, arg = 0, ext = 0;
    Py_ssize_t len = ((__builtin_expect(!(((((((PyObject*)(a->a_bytecode))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 3941, "PyBytes_Check(a->a_bytecode)") : (void)0),(((PyVarObject*)(a->a_bytecode))->ob_size));
    char *code;

    size = instrsize(i);
    if (i->i_hasarg) {
        arg = i->i_oparg;
        ext = arg >> 16;
    }
    if (i->i_lineno && !assemble_lnotab(a, i))
        return 0;
    if (a->a_offset + size >= len) {
        if (len > ((Py_ssize_t)(((size_t)-1)>>1)) / 2)
            return 0;
        if (_PyBytes_Resize(&a->a_bytecode, len * 2) < 0)
            return 0;
    }
    code = ((__builtin_expect(!(((((((PyObject*)(a->a_bytecode))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "compile.c", 3957, "PyBytes_Check(a->a_bytecode)") : (void)0), (((PyBytesObject *)(a->a_bytecode))->ob_sval)) + a->a_offset;
    a->a_offset += size;
    if (size == 6) {
        (__builtin_expect(!(i->i_hasarg), 0) ? __assert_rtn(__func__, "compile.c", 3960, "i->i_hasarg") : (void)0);
        *code++ = (char)144;
        *code++ = ext & 0xff;
        *code++ = ext >> 8;
        arg &= 0xffff;
    }
    *code++ = i->i_opcode;
    if (i->i_hasarg) {
        (__builtin_expect(!(size == 3 || size == 6), 0) ? __assert_rtn(__func__, "compile.c", 3968, "size == 3 || size == 6") : (void)0);
        *code++ = arg & 0xff;
        *code++ = arg >> 8;
    }
    return 1;
}

static void
assemble_jump_offsets(struct assembler *a, struct compiler *c)
{
    basicblock *b;
    int bsize, totsize, extended_arg_count = 0, last_extended_arg_count;
    int i;



    do {
        totsize = 0;
        for (i = a->a_nblocks - 1; i >= 0; i--) {
            b = a->a_postorder[i];
            bsize = blocksize(b);
            b->b_offset = totsize;
            totsize += bsize;
        }
        last_extended_arg_count = extended_arg_count;
        extended_arg_count = 0;
        for (b = c->u->u_blocks; b != ((void *)0); b = b->b_list) {
            bsize = b->b_offset;
            for (i = 0; i < b->b_iused; i++) {
                struct instr *instr = &b->b_instr[i];




                bsize += instrsize(instr);
                if (instr->i_jabs)
                    instr->i_oparg = instr->i_target->b_offset;
                else if (instr->i_jrel) {
                    int delta = instr->i_target->b_offset - bsize;
                    instr->i_oparg = delta;
                }
                else
                    continue;
                if (instr->i_oparg > 0xffff)
                    extended_arg_count++;
            }
        }
# 4030 "compile.c"
    } while (last_extended_arg_count != extended_arg_count);
}

static PyObject *
dict_keys_inorder(PyObject *dict, int offset)
{
    PyObject *tuple, *k, *v;
    Py_ssize_t i, pos = 0, size = PyDict_Size(dict);

    tuple = PyTuple_New(size);
    if (tuple == ((void *)0))
        return ((void *)0);
    while (PyDict_Next(dict, &pos, &k, &v)) {
        i = PyLong_AsLong(v);


        k = (((PyTupleObject *)(k))->ob_item[0]);
        ( ((PyObject*)(k))->ob_refcnt++);
        (__builtin_expect(!((i - offset) < size), 0) ? __assert_rtn(__func__, "compile.c", 4048, "(i - offset) < size") : (void)0);
        (__builtin_expect(!((i - offset) >= 0), 0) ? __assert_rtn(__func__, "compile.c", 4049, "(i - offset) >= 0") : (void)0);
        (((PyTupleObject *)(tuple))->ob_item[i - offset] = k);
    }
    return tuple;
}

static int
compute_code_flags(struct compiler *c)
{
    PySTEntryObject *ste = c->u->u_ste;
    int flags = 0, n;
    if (ste->ste_type != ModuleBlock)
        flags |= 0x0002;
    if (ste->ste_type == FunctionBlock) {
        if (!ste->ste_unoptimized)
            flags |= 0x0001;
        if (ste->ste_nested)
            flags |= 0x0010;
        if (ste->ste_generator)
            flags |= 0x0020;
        if (ste->ste_varargs)
            flags |= 0x0004;
        if (ste->ste_varkeywords)
            flags |= 0x0008;
    }


    flags |= (c->c_flags->cf_flags & (0x2000 | 0x4000 | 0x8000 | 0x10000 | 0x20000 | 0x40000));

    n = PyDict_Size(c->u->u_freevars);
    if (n < 0)
        return -1;
    if (n == 0) {
        n = PyDict_Size(c->u->u_cellvars);
        if (n < 0)
        return -1;
        if (n == 0) {
        flags |= 0x0040;
        }
    }

    return flags;
}

static PyCodeObject *
makecode(struct compiler *c, struct assembler *a)
{
    PyObject *tmp;
    PyCodeObject *co = ((void *)0);
    PyObject *consts = ((void *)0);
    PyObject *names = ((void *)0);
    PyObject *varnames = ((void *)0);
    PyObject *name = ((void *)0);
    PyObject *freevars = ((void *)0);
    PyObject *cellvars = ((void *)0);
    PyObject *bytecode = ((void *)0);
    int nlocals, flags;

    tmp = dict_keys_inorder(c->u->u_consts, 0);
    if (!tmp)
        goto error;
    consts = PySequence_List(tmp);
    do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0);

    names = dict_keys_inorder(c->u->u_names, 0);
    varnames = dict_keys_inorder(c->u->u_varnames, 0);
    if (!consts || !names || !varnames)
        goto error;

    cellvars = dict_keys_inorder(c->u->u_cellvars, 0);
    if (!cellvars)
        goto error;
    freevars = dict_keys_inorder(c->u->u_freevars, PyTuple_Size(cellvars));
    if (!freevars)
        goto error;
    nlocals = PyDict_Size(c->u->u_varnames);
    flags = compute_code_flags(c);
    if (flags < 0)
        goto error;

    bytecode = PyCode_Optimize(a->a_bytecode, consts, names, a->a_lnotab);
    if (!bytecode)
        goto error;

    tmp = PyList_AsTuple(consts);
    if (!tmp)
        goto error;
    do { if ( --((PyObject*)(consts))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(consts)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(consts)))); } while (0);
    consts = tmp;

    co = PyCode_New(c->u->u_argcount, c->u->u_kwonlyargcount,
                    nlocals, stackdepth(c), flags,
                    bytecode, consts, names, varnames,
                    freevars, cellvars,
                    c->c_filename_obj, c->u->u_name,
                    c->u->u_firstlineno,
                    a->a_lnotab);
 error:
    do { if ((consts) == ((void *)0)) ; else do { if ( --((PyObject*)(consts))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(consts)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(consts)))); } while (0); } while (0);
    do { if ((names) == ((void *)0)) ; else do { if ( --((PyObject*)(names))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(names)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(names)))); } while (0); } while (0);
    do { if ((varnames) == ((void *)0)) ; else do { if ( --((PyObject*)(varnames))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(varnames)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(varnames)))); } while (0); } while (0);
    do { if ((name) == ((void *)0)) ; else do { if ( --((PyObject*)(name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(name)))); } while (0); } while (0);
    do { if ((freevars) == ((void *)0)) ; else do { if ( --((PyObject*)(freevars))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(freevars)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(freevars)))); } while (0); } while (0);
    do { if ((cellvars) == ((void *)0)) ; else do { if ( --((PyObject*)(cellvars))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(cellvars)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(cellvars)))); } while (0); } while (0);
    do { if ((bytecode) == ((void *)0)) ; else do { if ( --((PyObject*)(bytecode))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(bytecode)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(bytecode)))); } while (0); } while (0);
    return co;
}
# 4192 "compile.c"
static PyCodeObject *
assemble(struct compiler *c, int addNone)
{
    basicblock *b, *entryblock;
    struct assembler a;
    int i, j, nblocks;
    PyCodeObject *co = ((void *)0);





    if (!c->u->u_curblock->b_return) {
        { if (compiler_next_block((c)) == ((void *)0)) return 0; };
        if (addNone)
            { if (!compiler_addop_o((c), (100), (c)->u->u_consts, ((&_Py_NoneStruct)))) return 0; };
        { if (!compiler_addop((c), (83))) return 0; };
    }

    nblocks = 0;
    entryblock = ((void *)0);
    for (b = c->u->u_blocks; b != ((void *)0); b = b->b_list) {
        nblocks++;
        entryblock = b;
    }


    if (!c->u->u_firstlineno) {
        if (entryblock && entryblock->b_instr)
            c->u->u_firstlineno = entryblock->b_instr->i_lineno;
        else
            c->u->u_firstlineno = 1;
    }
    if (!assemble_init(&a, nblocks, c->u->u_firstlineno))
        goto error;
    dfs(c, entryblock, &a);


    assemble_jump_offsets(&a, c);


    for (i = a.a_nblocks - 1; i >= 0; i--) {
        b = a.a_postorder[i];
        for (j = 0; j < b->b_iused; j++)
            if (!assemble_emit(&a, &b->b_instr[j]))
                goto error;
    }

    if (_PyBytes_Resize(&a.a_lnotab, a.a_lnotab_off) < 0)
        goto error;
    if (_PyBytes_Resize(&a.a_bytecode, a.a_offset) < 0)
        goto error;

    co = makecode(c, &a);
 error:
    assemble_free(&a);
    return co;
}


PyCodeObject *
PyAST_Compile(mod_ty mod, const char *filename, PyCompilerFlags *flags,
              PyArena *arena)
{
    return PyAST_CompileEx(mod, filename, flags, -1, arena);
}
