# 1 "ast.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "ast.c"





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
# 7 "ast.c" 2
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
# 8 "ast.c" 2
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
# 9 "ast.c" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/ast.h" 1






int PyAST_Validate(mod_ty);
mod_ty PyAST_FromNode(
    const node *n,
    PyCompilerFlags *flags,
    const char *filename,
    PyArena *arena);
# 10 "ast.c" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/token.h" 1
# 78 "/Users/parrt/tmp/Python-3.3.1/Include/token.h"
extern char * _PyParser_TokenNames[];
int PyToken_OneChar(int);
int PyToken_TwoChars(int, int);
int PyToken_ThreeChars(int, int, int);
# 11 "ast.c" 2

# 1 "/usr/include/assert.h" 1 3 4
# 75 "/usr/include/assert.h" 3 4

void __assert_rtn(const char *, const char *, int, const char *) __attribute__((__noreturn__));




# 13 "ast.c" 2

static int validate_stmts(asdl_seq *);
static int validate_exprs(asdl_seq *, expr_context_ty, int);
static int validate_nonempty_seq(asdl_seq *, const char *, const char *);
static int validate_stmt(stmt_ty);
static int validate_expr(expr_ty, expr_context_ty);

static int
validate_comprehension(asdl_seq *gens)
{
    int i;
    if (!((gens) == ((void *)0) ? 0 : (gens)->size)) {
        PyErr_SetString(PyExc_ValueError, "comprehension with no generators");
        return 0;
    }
    for (i = 0; i < ((gens) == ((void *)0) ? 0 : (gens)->size); i++) {
        comprehension_ty comp = (gens)->elements[(i)];
        if (!validate_expr(comp->target, Store) ||
            !validate_expr(comp->iter, Load) ||
            !validate_exprs(comp->ifs, Load, 0))
            return 0;
    }
    return 1;
}

static int
validate_slice(slice_ty slice)
{
    switch (slice->kind) {
    case Slice_kind:
        return (!slice->v.Slice.lower || validate_expr(slice->v.Slice.lower, Load)) &&
            (!slice->v.Slice.upper || validate_expr(slice->v.Slice.upper, Load)) &&
            (!slice->v.Slice.step || validate_expr(slice->v.Slice.step, Load));
    case ExtSlice_kind: {
        int i;
        if (!validate_nonempty_seq(slice->v.ExtSlice.dims, "dims", "ExtSlice"))
            return 0;
        for (i = 0; i < ((slice->v.ExtSlice.dims) == ((void *)0) ? 0 : (slice->v.ExtSlice.dims)->size); i++)
            if (!validate_slice((slice->v.ExtSlice.dims)->elements[(i)]))
                return 0;
        return 1;
    }
    case Index_kind:
        return validate_expr(slice->v.Index.value, Load);
    default:
        PyErr_SetString(PyExc_SystemError, "unknown slice node");
        return 0;
    }
}

static int
validate_keywords(asdl_seq *keywords)
{
    int i;
    for (i = 0; i < ((keywords) == ((void *)0) ? 0 : (keywords)->size); i++)
        if (!validate_expr(((keyword_ty)(keywords)->elements[(i)])->value, Load))
            return 0;
    return 1;
}

static int
validate_args(asdl_seq *args)
{
    int i;
    for (i = 0; i < ((args) == ((void *)0) ? 0 : (args)->size); i++) {
        arg_ty arg = (args)->elements[(i)];
        if (arg->annotation && !validate_expr(arg->annotation, Load))
            return 0;
    }
    return 1;
}

static const char *
expr_context_name(expr_context_ty ctx)
{
    switch (ctx) {
    case Load:
        return "Load";
    case Store:
        return "Store";
    case Del:
        return "Del";
    case AugLoad:
        return "AugLoad";
    case AugStore:
        return "AugStore";
    case Param:
        return "Param";
    default:
        (__builtin_expect(!(0), 0) ? __assert_rtn(__func__, "ast.c", 102, "0") : (void)0);
        return "(unknown)";
    }
}

static int
validate_arguments(arguments_ty args)
{
    if (!validate_args(args->args))
        return 0;
    if (args->varargannotation) {
        if (!args->vararg) {
            PyErr_SetString(PyExc_ValueError, "varargannotation but no vararg on arguments");
            return 0;
        }
        if (!validate_expr(args->varargannotation, Load))
            return 0;
    }
    if (!validate_args(args->kwonlyargs))
        return 0;
    if (args->kwargannotation) {
        if (!args->kwarg) {
            PyErr_SetString(PyExc_ValueError, "kwargannotation but no kwarg on arguments");
            return 0;
        }
        if (!validate_expr(args->kwargannotation, Load))
            return 0;
    }
    if (((args->defaults) == ((void *)0) ? 0 : (args->defaults)->size) > ((args->args) == ((void *)0) ? 0 : (args->args)->size)) {
        PyErr_SetString(PyExc_ValueError, "more positional defaults than args on arguments");
        return 0;
    }
    if (((args->kw_defaults) == ((void *)0) ? 0 : (args->kw_defaults)->size) != ((args->kwonlyargs) == ((void *)0) ? 0 : (args->kwonlyargs)->size)) {
        PyErr_SetString(PyExc_ValueError, "length of kwonlyargs is not the same as "
                        "kw_defaults on arguments");
        return 0;
    }
    return validate_exprs(args->defaults, Load, 0) && validate_exprs(args->kw_defaults, Load, 1);
}

static int
validate_expr(expr_ty exp, expr_context_ty ctx)
{
    int check_ctx = 1;
    expr_context_ty actual_ctx;


    switch (exp->kind) {
    case Attribute_kind:
        actual_ctx = exp->v.Attribute.ctx;
        break;
    case Subscript_kind:
        actual_ctx = exp->v.Subscript.ctx;
        break;
    case Starred_kind:
        actual_ctx = exp->v.Starred.ctx;
        break;
    case Name_kind:
        actual_ctx = exp->v.Name.ctx;
        break;
    case List_kind:
        actual_ctx = exp->v.List.ctx;
        break;
    case Tuple_kind:
        actual_ctx = exp->v.Tuple.ctx;
        break;
    default:
        if (ctx != Load) {
            PyErr_Format(PyExc_ValueError, "expression which can't be "
                         "assigned to in %s context", expr_context_name(ctx));
            return 0;
        }
        check_ctx = 0;
    }
    if (check_ctx && actual_ctx != ctx) {
        PyErr_Format(PyExc_ValueError, "expression must have %s context but has %s instead",
                     expr_context_name(ctx), expr_context_name(actual_ctx));
        return 0;
    }


    switch (exp->kind) {
    case BoolOp_kind:
        if (((exp->v.BoolOp.values) == ((void *)0) ? 0 : (exp->v.BoolOp.values)->size) < 2) {
            PyErr_SetString(PyExc_ValueError, "BoolOp with less than 2 values");
            return 0;
        }
        return validate_exprs(exp->v.BoolOp.values, Load, 0);
    case BinOp_kind:
        return validate_expr(exp->v.BinOp.left, Load) &&
            validate_expr(exp->v.BinOp.right, Load);
    case UnaryOp_kind:
        return validate_expr(exp->v.UnaryOp.operand, Load);
    case Lambda_kind:
        return validate_arguments(exp->v.Lambda.args) &&
            validate_expr(exp->v.Lambda.body, Load);
    case IfExp_kind:
        return validate_expr(exp->v.IfExp.test, Load) &&
            validate_expr(exp->v.IfExp.body, Load) &&
            validate_expr(exp->v.IfExp.orelse, Load);
    case Dict_kind:
        if (((exp->v.Dict.keys) == ((void *)0) ? 0 : (exp->v.Dict.keys)->size) != ((exp->v.Dict.values) == ((void *)0) ? 0 : (exp->v.Dict.values)->size)) {
            PyErr_SetString(PyExc_ValueError,
                            "Dict doesn't have the same number of keys as values");
            return 0;
        }
        return validate_exprs(exp->v.Dict.keys, Load, 0) &&
            validate_exprs(exp->v.Dict.values, Load, 0);
    case Set_kind:
        return validate_exprs(exp->v.Set.elts, Load, 0);




    case ListComp_kind: return validate_comprehension(exp->v.ListComp.generators) && validate_expr(exp->v.ListComp.elt, Load);
    case SetComp_kind: return validate_comprehension(exp->v.SetComp.generators) && validate_expr(exp->v.SetComp.elt, Load);
    case GeneratorExp_kind: return validate_comprehension(exp->v.GeneratorExp.generators) && validate_expr(exp->v.GeneratorExp.elt, Load);

    case DictComp_kind:
        return validate_comprehension(exp->v.DictComp.generators) &&
            validate_expr(exp->v.DictComp.key, Load) &&
            validate_expr(exp->v.DictComp.value, Load);
    case Yield_kind:
        return !exp->v.Yield.value || validate_expr(exp->v.Yield.value, Load);
    case YieldFrom_kind:
        return validate_expr(exp->v.YieldFrom.value, Load);
    case Compare_kind:
        if (!((exp->v.Compare.comparators) == ((void *)0) ? 0 : (exp->v.Compare.comparators)->size)) {
            PyErr_SetString(PyExc_ValueError, "Compare with no comparators");
            return 0;
        }
        if (((exp->v.Compare.comparators) == ((void *)0) ? 0 : (exp->v.Compare.comparators)->size) !=
            ((exp->v.Compare.ops) == ((void *)0) ? 0 : (exp->v.Compare.ops)->size)) {
            PyErr_SetString(PyExc_ValueError, "Compare has a different number "
                            "of comparators and operands");
            return 0;
        }
        return validate_exprs(exp->v.Compare.comparators, Load, 0) &&
            validate_expr(exp->v.Compare.left, Load);
    case Call_kind:
        return validate_expr(exp->v.Call.func, Load) &&
            validate_exprs(exp->v.Call.args, Load, 0) &&
            validate_keywords(exp->v.Call.keywords) &&
            (!exp->v.Call.starargs || validate_expr(exp->v.Call.starargs, Load)) &&
            (!exp->v.Call.kwargs || validate_expr(exp->v.Call.kwargs, Load));
    case Num_kind: {
        PyObject *n = exp->v.Num.n;
        if (!((((PyObject*)(n))->ob_type) == &PyLong_Type) && !((((PyObject*)(n))->ob_type) == &PyFloat_Type) &&
            !((((PyObject*)(n))->ob_type) == &PyComplex_Type)) {
            PyErr_SetString(PyExc_TypeError, "non-numeric type in Num");
            return 0;
        }
        return 1;
    }
    case Str_kind: {
        PyObject *s = exp->v.Str.s;
        if (!((((PyObject*)(s))->ob_type) == &PyUnicode_Type)) {
            PyErr_SetString(PyExc_TypeError, "non-string type in Str");
            return 0;
        }
        return 1;
    }
    case Bytes_kind: {
        PyObject *b = exp->v.Bytes.s;
        if (!((((PyObject*)(b))->ob_type) == &PyBytes_Type)) {
            PyErr_SetString(PyExc_TypeError, "non-bytes type in Bytes");
            return 0;
        }
        return 1;
    }
    case Attribute_kind:
        return validate_expr(exp->v.Attribute.value, Load);
    case Subscript_kind:
        return validate_slice(exp->v.Subscript.slice) &&
            validate_expr(exp->v.Subscript.value, Load);
    case Starred_kind:
        return validate_expr(exp->v.Starred.value, ctx);
    case List_kind:
        return validate_exprs(exp->v.List.elts, ctx, 0);
    case Tuple_kind:
        return validate_exprs(exp->v.Tuple.elts, ctx, 0);

    case Name_kind:
    case Ellipsis_kind:
        return 1;
    default:
        PyErr_SetString(PyExc_SystemError, "unexpected expression");
        return 0;
    }
}

static int
validate_nonempty_seq(asdl_seq *seq, const char *what, const char *owner)
{
    if (((seq) == ((void *)0) ? 0 : (seq)->size))
        return 1;
    PyErr_Format(PyExc_ValueError, "empty %s on %s", what, owner);
    return 0;
}

static int
validate_assignlist(asdl_seq *targets, expr_context_ty ctx)
{
    return validate_nonempty_seq(targets, "targets", ctx == Del ? "Delete" : "Assign") &&
        validate_exprs(targets, ctx, 0);
}

static int
validate_body(asdl_seq *body, const char *owner)
{
    return validate_nonempty_seq(body, "body", owner) && validate_stmts(body);
}

static int
validate_stmt(stmt_ty stmt)
{
    int i;
    switch (stmt->kind) {
    case FunctionDef_kind:
        return validate_body(stmt->v.FunctionDef.body, "FunctionDef") &&
            validate_arguments(stmt->v.FunctionDef.args) &&
            validate_exprs(stmt->v.FunctionDef.decorator_list, Load, 0) &&
            (!stmt->v.FunctionDef.returns ||
             validate_expr(stmt->v.FunctionDef.returns, Load));
    case ClassDef_kind:
        return validate_body(stmt->v.ClassDef.body, "ClassDef") &&
            validate_exprs(stmt->v.ClassDef.bases, Load, 0) &&
            validate_keywords(stmt->v.ClassDef.keywords) &&
            validate_exprs(stmt->v.ClassDef.decorator_list, Load, 0) &&
            (!stmt->v.ClassDef.starargs || validate_expr(stmt->v.ClassDef.starargs, Load)) &&
            (!stmt->v.ClassDef.kwargs || validate_expr(stmt->v.ClassDef.kwargs, Load));
    case Return_kind:
        return !stmt->v.Return.value || validate_expr(stmt->v.Return.value, Load);
    case Delete_kind:
        return validate_assignlist(stmt->v.Delete.targets, Del);
    case Assign_kind:
        return validate_assignlist(stmt->v.Assign.targets, Store) &&
            validate_expr(stmt->v.Assign.value, Load);
    case AugAssign_kind:
        return validate_expr(stmt->v.AugAssign.target, Store) &&
            validate_expr(stmt->v.AugAssign.value, Load);
    case For_kind:
        return validate_expr(stmt->v.For.target, Store) &&
            validate_expr(stmt->v.For.iter, Load) &&
            validate_body(stmt->v.For.body, "For") &&
            validate_stmts(stmt->v.For.orelse);
    case While_kind:
        return validate_expr(stmt->v.While.test, Load) &&
            validate_body(stmt->v.While.body, "While") &&
            validate_stmts(stmt->v.While.orelse);
    case If_kind:
        return validate_expr(stmt->v.If.test, Load) &&
            validate_body(stmt->v.If.body, "If") &&
            validate_stmts(stmt->v.If.orelse);
    case With_kind:
        if (!validate_nonempty_seq(stmt->v.With.items, "items", "With"))
            return 0;
        for (i = 0; i < ((stmt->v.With.items) == ((void *)0) ? 0 : (stmt->v.With.items)->size); i++) {
            withitem_ty item = (stmt->v.With.items)->elements[(i)];
            if (!validate_expr(item->context_expr, Load) ||
                (item->optional_vars && !validate_expr(item->optional_vars, Store)))
                return 0;
        }
        return validate_body(stmt->v.With.body, "With");
    case Raise_kind:
        if (stmt->v.Raise.exc) {
            return validate_expr(stmt->v.Raise.exc, Load) &&
                (!stmt->v.Raise.cause || validate_expr(stmt->v.Raise.cause, Load));
        }
        if (stmt->v.Raise.cause) {
            PyErr_SetString(PyExc_ValueError, "Raise with cause but no exception");
            return 0;
        }
        return 1;
    case Try_kind:
        if (!validate_body(stmt->v.Try.body, "Try"))
            return 0;
        if (!((stmt->v.Try.handlers) == ((void *)0) ? 0 : (stmt->v.Try.handlers)->size) &&
            !((stmt->v.Try.finalbody) == ((void *)0) ? 0 : (stmt->v.Try.finalbody)->size)) {
            PyErr_SetString(PyExc_ValueError, "Try has neither except handlers nor finalbody");
            return 0;
        }
        if (!((stmt->v.Try.handlers) == ((void *)0) ? 0 : (stmt->v.Try.handlers)->size) &&
            ((stmt->v.Try.orelse) == ((void *)0) ? 0 : (stmt->v.Try.orelse)->size)) {
            PyErr_SetString(PyExc_ValueError, "Try has orelse but no except handlers");
            return 0;
        }
        for (i = 0; i < ((stmt->v.Try.handlers) == ((void *)0) ? 0 : (stmt->v.Try.handlers)->size); i++) {
            excepthandler_ty handler = (stmt->v.Try.handlers)->elements[(i)];
            if ((handler->v.ExceptHandler.type &&
                 !validate_expr(handler->v.ExceptHandler.type, Load)) ||
                !validate_body(handler->v.ExceptHandler.body, "ExceptHandler"))
                return 0;
        }
        return (!((stmt->v.Try.finalbody) == ((void *)0) ? 0 : (stmt->v.Try.finalbody)->size) ||
                validate_stmts(stmt->v.Try.finalbody)) &&
            (!((stmt->v.Try.orelse) == ((void *)0) ? 0 : (stmt->v.Try.orelse)->size) ||
             validate_stmts(stmt->v.Try.orelse));
    case Assert_kind:
        return validate_expr(stmt->v.Assert.test, Load) &&
            (!stmt->v.Assert.msg || validate_expr(stmt->v.Assert.msg, Load));
    case Import_kind:
        return validate_nonempty_seq(stmt->v.Import.names, "names", "Import");
    case ImportFrom_kind:
        if (stmt->v.ImportFrom.level < -1) {
            PyErr_SetString(PyExc_ValueError, "ImportFrom level less than -1");
            return 0;
        }
        return validate_nonempty_seq(stmt->v.ImportFrom.names, "names", "ImportFrom");
    case Global_kind:
        return validate_nonempty_seq(stmt->v.Global.names, "names", "Global");
    case Nonlocal_kind:
        return validate_nonempty_seq(stmt->v.Nonlocal.names, "names", "Nonlocal");
    case Expr_kind:
        return validate_expr(stmt->v.Expr.value, Load);
    case Pass_kind:
    case Break_kind:
    case Continue_kind:
        return 1;
    default:
        PyErr_SetString(PyExc_SystemError, "unexpected statement");
        return 0;
    }
}

static int
validate_stmts(asdl_seq *seq)
{
    int i;
    for (i = 0; i < ((seq) == ((void *)0) ? 0 : (seq)->size); i++) {
        stmt_ty stmt = (seq)->elements[(i)];
        if (stmt) {
            if (!validate_stmt(stmt))
                return 0;
        }
        else {
            PyErr_SetString(PyExc_ValueError,
                            "None disallowed in statement list");
            return 0;
        }
    }
    return 1;
}

static int
validate_exprs(asdl_seq *exprs, expr_context_ty ctx, int null_ok)
{
    int i;
    for (i = 0; i < ((exprs) == ((void *)0) ? 0 : (exprs)->size); i++) {
        expr_ty expr = (exprs)->elements[(i)];
        if (expr) {
            if (!validate_expr(expr, ctx))
                return 0;
        }
        else if (!null_ok) {
            PyErr_SetString(PyExc_ValueError,
                            "None disallowed in expression list");
            return 0;
        }

    }
    return 1;
}

int
PyAST_Validate(mod_ty mod)
{
    int res = 0;

    switch (mod->kind) {
    case Module_kind:
        res = validate_stmts(mod->v.Module.body);
        break;
    case Interactive_kind:
        res = validate_stmts(mod->v.Interactive.body);
        break;
    case Expression_kind:
        res = validate_expr(mod->v.Expression.body, Load);
        break;
    case Suite_kind:
        PyErr_SetString(PyExc_ValueError, "Suite is not valid in the CPython compiler");
        break;
    default:
        PyErr_SetString(PyExc_SystemError, "impossible module node");
        res = 0;
        break;
    }
    return res;
}


# 1 "/Users/parrt/tmp/Python-3.3.1/Include/grammar.h" 1
# 10 "/Users/parrt/tmp/Python-3.3.1/Include/grammar.h"
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/bitset.h" 1
# 12 "/Users/parrt/tmp/Python-3.3.1/Include/bitset.h"
typedef char *bitset;

bitset newbitset(int nbits);
void delbitset(bitset bs);

int addbit(bitset bs, int ibit);
int samebitset(bitset bs1, bitset bs2, int nbits);
void mergebitset(bitset bs1, bitset bs2, int nbits);
# 11 "/Users/parrt/tmp/Python-3.3.1/Include/grammar.h" 2



typedef struct {
    int lb_type;
    char *lb_str;
} label;





typedef struct {
    int ll_nlabels;
    label *ll_label;
} labellist;



typedef struct {
    short a_lbl;
    short a_arrow;
} arc;



typedef struct {
    int s_narcs;
    arc *s_arc;


    int s_lower;
    int s_upper;
    int *s_accel;
    int s_accept;
} state;



typedef struct {
    int d_type;
    char *d_name;
    int d_initial;
    int d_nstates;
    state *d_state;
    bitset d_first;
} dfa;



typedef struct {
    int g_ndfas;
    dfa *g_dfa;
    labellist g_ll;
    int g_start;
    int g_accel;
} grammar;



grammar *newgrammar(int start);
dfa *adddfa(grammar *g, int type, char *name);
int addstate(dfa *d);
void addarc(dfa *d, int from, int to, int lbl);
dfa *PyGrammar_FindDFA(grammar *g, int type);

int addlabel(labellist *ll, int type, char *str);
int findlabel(labellist *ll, int type, char *str);
char *PyGrammar_LabelRepr(label *lb);
void translatelabels(grammar *g);

void addfirstsets(grammar *g);

void PyGrammar_AddAccelerators(grammar *g);
void PyGrammar_RemoveAccelerators(grammar *);

void printgrammar(grammar *g, FILE *fp);
void printnonterminals(grammar *g, FILE *fp);
# 494 "ast.c" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/parsetok.h" 1
# 10 "/Users/parrt/tmp/Python-3.3.1/Include/parsetok.h"
typedef struct {
    int error;


    PyObject *filename;

    int lineno;
    int offset;
    char *text;
    int token;
    int expected;
} perrdetail;
# 38 "/Users/parrt/tmp/Python-3.3.1/Include/parsetok.h"
node * PyParser_ParseString(const char *, grammar *, int,
                                              perrdetail *);
node * PyParser_ParseFile (FILE *, const char *, grammar *, int,
                                             char *, char *, perrdetail *);

node * PyParser_ParseStringFlags(const char *, grammar *, int,
                                              perrdetail *, int);
node * PyParser_ParseFileFlags(FILE *, const char *,
        const char*, grammar *,
       int, char *, char *,
       perrdetail *, int);
node * PyParser_ParseFileFlagsEx(
    FILE *fp,
    const char *filename,
    const char *enc,
    grammar *g,
    int start,
    char *ps1,
    char *ps2,
    perrdetail *err_ret,
    int *flags);

node * PyParser_ParseStringFlagsFilename(const char *,
           const char *,
           grammar *, int,
                                              perrdetail *, int);
node * PyParser_ParseStringFlagsFilenameEx(
    const char *s,
    const char *filename,
    grammar *g,
    int start,
    perrdetail *err_ret,
    int *flags);



void PyParser_SetError(perrdetail *);
void PyParser_ClearError(perrdetail *);
# 495 "ast.c" 2
# 1 "/Users/parrt/tmp/Python-3.3.1/Include/graminit.h" 1
# 496 "ast.c" 2


struct compiling {
    char *c_encoding;
    PyArena *c_arena;
    const char *c_filename;
    PyObject *c_normalize;
    PyObject *c_normalize_args;
};

static asdl_seq *seq_for_testlist(struct compiling *, const node *);
static expr_ty ast_for_expr(struct compiling *, const node *);
static stmt_ty ast_for_stmt(struct compiling *, const node *);
static asdl_seq *ast_for_suite(struct compiling *, const node *);
static asdl_seq *ast_for_exprlist(struct compiling *, const node *,
                                  expr_context_ty);
static expr_ty ast_for_testlist(struct compiling *, const node *);
static stmt_ty ast_for_classdef(struct compiling *, const node *, asdl_seq *);


static expr_ty ast_for_call(struct compiling *, const node *, expr_ty);

static PyObject *parsenumber(struct compiling *, const char *);
static PyObject *parsestr(struct compiling *, const node *n, int *bytesmode);
static PyObject *parsestrplus(struct compiling *, const node *n,
                              int *bytesmode);





static int
init_normalization(struct compiling *c)
{
    PyObject *m = PyImport_ImportModuleNoBlock("unicodedata");
    if (!m)
        return 0;
    c->c_normalize = PyObject_GetAttrString(m, "normalize");
    do { if ( --((PyObject*)(m))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(m)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(m)))); } while (0);
    if (!c->c_normalize)
        return 0;
    c->c_normalize_args = Py_BuildValue("(sN)", "NFKC", (&_Py_NoneStruct));
    (((PyTupleObject *)(c->c_normalize_args))->ob_item[1] = ((void *)0));
    if (!c->c_normalize_args) {
        do { if (c->c_normalize) { PyObject *_py_tmp = (PyObject *)(c->c_normalize); (c->c_normalize) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
        return 0;
    }
    return 1;
}

static identifier
new_identifier(const char *n, struct compiling *c)
{
    PyObject *id = PyUnicode_DecodeUTF8(n, strlen(n), ((void *)0));
    if (!id)
        return ((void *)0);

    (__builtin_expect(!((((PyASCIIObject*)id)->state.ready)), 0) ? __assert_rtn(__func__, "ast.c", 553, "PyUnicode_IS_READY(id)") : (void)0);


    if (!((__builtin_expect(!(((((((PyObject*)(id))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "ast.c", 556, "PyUnicode_Check(id)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)id)->state.ready)), 0) ? __assert_rtn(__func__, "ast.c", 556, "PyUnicode_IS_READY(id)") : (void)0), ((PyASCIIObject*)id)->state.ascii)) {
        PyObject *id2;
        if (!c->c_normalize && !init_normalization(c)) {
            do { if ( --((PyObject*)(id))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(id)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(id)))); } while (0);
            return ((void *)0);
        }
        (((PyTupleObject *)(c->c_normalize_args))->ob_item[1] = id);
        id2 = PyObject_Call(c->c_normalize, c->c_normalize_args, ((void *)0));
        do { if ( --((PyObject*)(id))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(id)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(id)))); } while (0);
        if (!id2)
            return ((void *)0);
        id = id2;
    }
    PyUnicode_InternInPlace(&id);
    PyArena_AddPyObject(c->c_arena, id);
    return id;
}



static int
ast_error(struct compiling *c, const node *n, const char *errmsg)
{
    PyObject *value, *errstr, *loc, *tmp;
    PyObject *filename_obj;

    loc = PyErr_ProgramText(c->c_filename, ((n)->n_lineno));
    if (!loc) {
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        loc = (&_Py_NoneStruct);
    }
    if (c->c_filename) {
        filename_obj = PyUnicode_DecodeFSDefault(c->c_filename);
        if (!filename_obj) {
            do { if ( --((PyObject*)(loc))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(loc)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(loc)))); } while (0);
            return 0;
        }
    } else {
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        filename_obj = (&_Py_NoneStruct);
    }
    tmp = Py_BuildValue("(NiiN)", filename_obj, ((n)->n_lineno), n->n_col_offset, loc);
    if (!tmp)
        return 0;
    errstr = PyUnicode_FromString(errmsg);
    if (!errstr) {
        do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0);
        return 0;
    }
    value = PyTuple_Pack(2, errstr, tmp);
    do { if ( --((PyObject*)(errstr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(errstr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(errstr)))); } while (0);
    do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0);
    if (value) {
        PyErr_SetObject(PyExc_SyntaxError, value);
        do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0);
    }
    return 0;
}
# 629 "ast.c"
static int
num_stmts(const node *n)
{
    int i, l;
    node *ch;

    switch (((n)->n_type)) {
        case 256:
            if ((((&(n)->n_child[0]))->n_type) == 4)
                return 0;
            else
                return num_stmts((&(n)->n_child[0]));
        case 257:
            l = 0;
            for (i = 0; i < ((n)->n_nchildren); i++) {
                ch = (&(n)->n_child[i]);
                if (((ch)->n_type) == 268)
                    l += num_stmts(ch);
            }
            return l;
        case 268:
            return num_stmts((&(n)->n_child[0]));
        case 293:
            return 1;
        case 269:
            return ((n)->n_nchildren) / 2;
        case 301:
            if (((n)->n_nchildren) == 1)
                return num_stmts((&(n)->n_child[0]));
            else {
                l = 0;
                for (i = 2; i < (((n)->n_nchildren) - 1); i++)
                    l += num_stmts((&(n)->n_child[i]));
                return l;
            }
        default: {
            char buf[128];

            __builtin___sprintf_chk (buf, 0, __builtin_object_size (buf, 2 > 1), "Non-statement found: %d %d", ((n)->n_type), ((n)->n_nchildren));

            Py_FatalError(buf);
        }
    }
    (__builtin_expect(!(0), 0) ? __assert_rtn(__func__, "ast.c", 672, "0") : (void)0);
    return 0;
}




mod_ty
PyAST_FromNode(const node *n, PyCompilerFlags *flags, const char *filename,
               PyArena *arena)
{
    int i, j, k, num;
    asdl_seq *stmts = ((void *)0);
    stmt_ty s;
    node *ch;
    struct compiling c;
    mod_ty res = ((void *)0);

    c.c_arena = arena;
    c.c_filename = filename;
    c.c_normalize = c.c_normalize_args = ((void *)0);
    if (flags && flags->cf_flags & 0x0100) {
        c.c_encoding = "utf-8";
        if (((n)->n_type) == 335) {




            n = (&(n)->n_child[0]);
        }
    } else if (((n)->n_type) == 335) {
        c.c_encoding = ((n)->n_str);
        n = (&(n)->n_child[0]);
    } else {

        c.c_encoding = "utf-8";
    }

    k = 0;
    switch (((n)->n_type)) {
        case 257:
            stmts = asdl_seq_new(num_stmts(n), arena);
            if (!stmts)
                goto out;
            for (i = 0; i < ((n)->n_nchildren) - 1; i++) {
                ch = (&(n)->n_child[i]);
                if (((ch)->n_type) == 4)
                    continue;
                (__builtin_expect(!(((ch)->n_type) == (268)), 0) ? __assert_rtn(__func__, "ast.c", 720, "TYPE(ch) == (268)") : (void)0);
                num = num_stmts(ch);
                if (num == 1) {
                    s = ast_for_stmt(&c, ch);
                    if (!s)
                        goto out;
                    (stmts)->elements[k++] = (s);
                }
                else {
                    ch = (&(ch)->n_child[0]);
                    (__builtin_expect(!(((ch)->n_type) == (269)), 0) ? __assert_rtn(__func__, "ast.c", 730, "TYPE(ch) == (269)") : (void)0);
                    for (j = 0; j < num; j++) {
                        s = ast_for_stmt(&c, (&(ch)->n_child[j * 2]));
                        if (!s)
                            goto out;
                        (stmts)->elements[k++] = (s);
                    }
                }
            }
            res = _Py_Module(stmts, arena);
            break;
        case 258: {
            expr_ty testlist_ast;


            testlist_ast = ast_for_testlist(&c, (&(n)->n_child[0]));
            if (!testlist_ast)
                goto out;
            res = _Py_Expression(testlist_ast, arena);
            break;
        }
        case 256:
            if ((((&(n)->n_child[0]))->n_type) == 4) {
                stmts = asdl_seq_new(1, arena);
                if (!stmts)
                    goto out;
                (stmts)->elements[0] = (_Py_Pass(n->n_lineno, n->n_col_offset, arena));

                if (!(stmts)->elements[(0)])
                    goto out;
                res = _Py_Interactive(stmts, arena);
            }
            else {
                n = (&(n)->n_child[0]);
                num = num_stmts(n);
                stmts = asdl_seq_new(num, arena);
                if (!stmts)
                    goto out;
                if (num == 1) {
                    s = ast_for_stmt(&c, n);
                    if (!s)
                        goto out;
                    (stmts)->elements[0] = (s);
                }
                else {

                    (__builtin_expect(!(((n)->n_type) == (269)), 0) ? __assert_rtn(__func__, "ast.c", 776, "TYPE(n) == (269)") : (void)0);
                    for (i = 0; i < ((n)->n_nchildren); i += 2) {
                        if ((((&(n)->n_child[i]))->n_type) == 4)
                            break;
                        s = ast_for_stmt(&c, (&(n)->n_child[i]));
                        if (!s)
                            goto out;
                        (stmts)->elements[i / 2] = (s);
                    }
                }

                res = _Py_Interactive(stmts, arena);
            }
            break;
        default:
            PyErr_Format(PyExc_SystemError,
                         "invalid node %d for PyAST_FromNode", ((n)->n_type));
            goto out;
    }
 out:
    if (c.c_normalize) {
        do { if ( --((PyObject*)(c.c_normalize))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(c.c_normalize)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(c.c_normalize)))); } while (0);
        (((PyTupleObject *)(c.c_normalize_args))->ob_item[1] = ((void *)0));
        do { if ( --((PyObject*)(c.c_normalize_args))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(c.c_normalize_args)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(c.c_normalize_args)))); } while (0);
    }
    return res;
}




static operator_ty
get_operator(const node *n)
{
    switch (((n)->n_type)) {
        case 18:
            return BitOr;
        case 32:
            return BitXor;
        case 19:
            return BitAnd;
        case 33:
            return LShift;
        case 34:
            return RShift;
        case 14:
            return Add;
        case 15:
            return Sub;
        case 16:
            return Mult;
        case 17:
            return Div;
        case 47:
            return FloorDiv;
        case 24:
            return Mod;
        default:
            return (operator_ty)0;
    }
}

static const char* FORBIDDEN[] = {
    "None",
    "True",
    "False",
    ((void *)0),
};

static int
forbidden_name(struct compiling *c, identifier name, const node *n, int full_checks)
{
    (__builtin_expect(!(((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "ast.c", 848, "PyUnicode_Check(name)") : (void)0);
    if (PyUnicode_CompareWithASCIIString(name, "__debug__") == 0) {
        ast_error(c, n, "assignment to keyword");
        return 1;
    }
    if (full_checks) {
        const char **p;
        for (p = FORBIDDEN; *p; p++) {
            if (PyUnicode_CompareWithASCIIString(name, *p) == 0) {
                ast_error(c, n, "assignment to keyword");
                return 1;
            }
        }
    }
    return 0;
}
# 872 "ast.c"
static int
set_context(struct compiling *c, expr_ty e, expr_context_ty ctx, const node *n)
{
    asdl_seq *s = ((void *)0);



    const char* expr_name = ((void *)0);
# 888 "ast.c"
    (__builtin_expect(!(ctx != AugStore && ctx != AugLoad), 0) ? __assert_rtn(__func__, "ast.c", 888, "ctx != AugStore && ctx != AugLoad") : (void)0);

    switch (e->kind) {
        case Attribute_kind:
            e->v.Attribute.ctx = ctx;
            if (ctx == Store && forbidden_name(c, e->v.Attribute.attr, n, 1))
                return 0;
            break;
        case Subscript_kind:
            e->v.Subscript.ctx = ctx;
            break;
        case Starred_kind:
            e->v.Starred.ctx = ctx;
            if (!set_context(c, e->v.Starred.value, ctx, n))
                return 0;
            break;
        case Name_kind:
            if (ctx == Store) {
                if (forbidden_name(c, e->v.Name.id, n, 1))
                    return 0;
            }
            e->v.Name.ctx = ctx;
            break;
        case List_kind:
            e->v.List.ctx = ctx;
            s = e->v.List.elts;
            break;
        case Tuple_kind:
            if (((e->v.Tuple.elts) == ((void *)0) ? 0 : (e->v.Tuple.elts)->size)) {
                e->v.Tuple.ctx = ctx;
                s = e->v.Tuple.elts;
            }
            else {
                expr_name = "()";
            }
            break;
        case Lambda_kind:
            expr_name = "lambda";
            break;
        case Call_kind:
            expr_name = "function call";
            break;
        case BoolOp_kind:
        case BinOp_kind:
        case UnaryOp_kind:
            expr_name = "operator";
            break;
        case GeneratorExp_kind:
            expr_name = "generator expression";
            break;
        case Yield_kind:
        case YieldFrom_kind:
            expr_name = "yield expression";
            break;
        case ListComp_kind:
            expr_name = "list comprehension";
            break;
        case SetComp_kind:
            expr_name = "set comprehension";
            break;
        case DictComp_kind:
            expr_name = "dict comprehension";
            break;
        case Dict_kind:
        case Set_kind:
        case Num_kind:
        case Str_kind:
        case Bytes_kind:
            expr_name = "literal";
            break;
        case Ellipsis_kind:
            expr_name = "Ellipsis";
            break;
        case Compare_kind:
            expr_name = "comparison";
            break;
        case IfExp_kind:
            expr_name = "conditional expression";
            break;
        default:
            PyErr_Format(PyExc_SystemError,
                         "unexpected expression in assignment %d (line %d)",
                         e->kind, e->lineno);
            return 0;
    }

    if (expr_name) {
        char buf[300];
        PyOS_snprintf(buf, sizeof(buf),
                      "can't %s %s",
                      ctx == Store ? "assign to" : "delete",
                      expr_name);
        return ast_error(c, n, buf);
    }




    if (s) {
        int i;

        for (i = 0; i < ((s) == ((void *)0) ? 0 : (s)->size); i++) {
            if (!set_context(c, (expr_ty)(s)->elements[(i)], ctx, n))
                return 0;
        }
    }
    return 1;
}

static operator_ty
ast_for_augassign(struct compiling *c, const node *n)
{
    (__builtin_expect(!(((n)->n_type) == (273)), 0) ? __assert_rtn(__func__, "ast.c", 1000, "TYPE(n) == (273)") : (void)0);
    n = (&(n)->n_child[0]);
    switch (((n)->n_str)[0]) {
        case '+':
            return Add;
        case '-':
            return Sub;
        case '/':
            if (((n)->n_str)[1] == '/')
                return FloorDiv;
            else
                return Div;
        case '%':
            return Mod;
        case '<':
            return LShift;
        case '>':
            return RShift;
        case '&':
            return BitAnd;
        case '^':
            return BitXor;
        case '|':
            return BitOr;
        case '*':
            if (((n)->n_str)[1] == '*')
                return Pow;
            else
                return Mult;
        default:
            PyErr_Format(PyExc_SystemError, "invalid augassign: %s", ((n)->n_str));
            return (operator_ty)0;
    }
}

static cmpop_ty
ast_for_comp_op(struct compiling *c, const node *n)
{



    (__builtin_expect(!(((n)->n_type) == (310)), 0) ? __assert_rtn(__func__, "ast.c", 1041, "TYPE(n) == (310)") : (void)0);
    if (((n)->n_nchildren) == 1) {
        n = (&(n)->n_child[0]);
        switch (((n)->n_type)) {
            case 20:
                return Lt;
            case 21:
                return Gt;
            case 27:
                return Eq;
            case 29:
                return LtE;
            case 30:
                return GtE;
            case 28:
                return NotEq;
            case 1:
                if (strcmp(((n)->n_str), "in") == 0)
                    return In;
                if (strcmp(((n)->n_str), "is") == 0)
                    return Is;
            default:
                PyErr_Format(PyExc_SystemError, "invalid comp_op: %s",
                             ((n)->n_str));
                return (cmpop_ty)0;
        }
    }
    else if (((n)->n_nchildren) == 2) {

        switch ((((&(n)->n_child[0]))->n_type)) {
            case 1:
                if (strcmp((((&(n)->n_child[1]))->n_str), "in") == 0)
                    return NotIn;
                if (strcmp((((&(n)->n_child[0]))->n_str), "is") == 0)
                    return IsNot;
            default:
                PyErr_Format(PyExc_SystemError, "invalid comp_op: %s %s",
                             (((&(n)->n_child[0]))->n_str), (((&(n)->n_child[1]))->n_str));
                return (cmpop_ty)0;
        }
    }
    PyErr_Format(PyExc_SystemError, "invalid comp_op: has %d children",
                 ((n)->n_nchildren));
    return (cmpop_ty)0;
}

static asdl_seq *
seq_for_testlist(struct compiling *c, const node *n)
{



    asdl_seq *seq;
    expr_ty expression;
    int i;
    (__builtin_expect(!(((n)->n_type) == 327 || ((n)->n_type) == 272 || ((n)->n_type) == 321), 0) ? __assert_rtn(__func__, "ast.c", 1096, "TYPE(n) == testlist || TYPE(n) == testlist_star_expr || TYPE(n) == testlist_comp") : (void)0);

    seq = asdl_seq_new((((n)->n_nchildren) + 1) / 2, c->c_arena);
    if (!seq)
        return ((void *)0);

    for (i = 0; i < ((n)->n_nchildren); i += 2) {
        const node *ch = (&(n)->n_child[i]);
        (__builtin_expect(!(((ch)->n_type) == 302 || ((ch)->n_type) == 303 || ((ch)->n_type) == 311), 0) ? __assert_rtn(__func__, "ast.c", 1104, "TYPE(ch) == test || TYPE(ch) == test_nocond || TYPE(ch) == star_expr") : (void)0);

        expression = ast_for_expr(c, ch);
        if (!expression)
            return ((void *)0);

        (__builtin_expect(!(i / 2 < seq->size), 0) ? __assert_rtn(__func__, "ast.c", 1110, "i / 2 < seq->size") : (void)0);
        (seq)->elements[i / 2] = (expression);
    }
    return seq;
}

static arg_ty
ast_for_arg(struct compiling *c, const node *n)
{
    identifier name;
    expr_ty annotation = ((void *)0);
    node *ch;

    (__builtin_expect(!(((n)->n_type) == 265 || ((n)->n_type) == 267), 0) ? __assert_rtn(__func__, "ast.c", 1123, "TYPE(n) == tfpdef || TYPE(n) == vfpdef") : (void)0);
    ch = (&(n)->n_child[0]);
    name = new_identifier(((ch)->n_str), c);
    if (!name)
        return ((void *)0);
    if (forbidden_name(c, name, ch, 0))
        return ((void *)0);

    if (((n)->n_nchildren) == 3 && (((&(n)->n_child[1]))->n_type) == 11) {
        annotation = ast_for_expr(c, (&(n)->n_child[2]));
        if (!annotation)
            return ((void *)0);
    }

    return _Py_arg(name, annotation, c->c_arena);
}







static int
handle_keywordonly_args(struct compiling *c, const node *n, int start,
                        asdl_seq *kwonlyargs, asdl_seq *kwdefaults)
{
    PyObject *argname;
    node *ch;
    expr_ty expression, annotation;
    arg_ty arg;
    int i = start;
    int j = 0;

    if (kwonlyargs == ((void *)0)) {
        ast_error(c, (&(n)->n_child[start]), "named arguments must follow bare *");
        return -1;
    }
    (__builtin_expect(!(kwdefaults != ((void *)0)), 0) ? __assert_rtn(__func__, "ast.c", 1161, "kwdefaults != NULL") : (void)0);
    while (i < ((n)->n_nchildren)) {
        ch = (&(n)->n_child[i]);
        switch (((ch)->n_type)) {
            case 267:
            case 265:
                if (i + 1 < ((n)->n_nchildren) && (((&(n)->n_child[i + 1]))->n_type) == 22) {
                    expression = ast_for_expr(c, (&(n)->n_child[i + 2]));
                    if (!expression)
                        goto error;
                    (kwdefaults)->elements[j] = (expression);
                    i += 2;
                }
                else {
                    (kwdefaults)->elements[j] = (((void *)0));
                }
                if (((ch)->n_nchildren) == 3) {

                    annotation = ast_for_expr(c, (&(ch)->n_child[2]));
                    if (!annotation)
                        goto error;
                }
                else {
                    annotation = ((void *)0);
                }
                ch = (&(ch)->n_child[0]);
                argname = new_identifier(((ch)->n_str), c);
                if (!argname)
                    goto error;
                if (forbidden_name(c, argname, ch, 0))
                    goto error;
                arg = _Py_arg(argname, annotation, c->c_arena);
                if (!arg)
                    goto error;
                (kwonlyargs)->elements[j++] = (arg);
                i += 2;
                break;
            case 35:
                return i;
            default:
                ast_error(c, ch, "unexpected node");
                goto error;
        }
    }
    return i;
 error:
    return -1;
}



static arguments_ty
ast_for_arguments(struct compiling *c, const node *n)
{
# 1230 "ast.c"
    int i, j, k, nposargs = 0, nkwonlyargs = 0;
    int nposdefaults = 0, found_default = 0;
    asdl_seq *posargs, *posdefaults, *kwonlyargs, *kwdefaults;
    identifier vararg = ((void *)0), kwarg = ((void *)0);
    arg_ty arg;
    expr_ty varargannotation = ((void *)0), kwargannotation = ((void *)0);
    node *ch;

    if (((n)->n_type) == 263) {
        if (((n)->n_nchildren) == 2)
            return _Py_arguments(((void *)0), ((void *)0), ((void *)0), ((void *)0), ((void *)0), ((void *)0), ((void *)0), ((void *)0), c->c_arena);

        n = (&(n)->n_child[1]);
    }
    (__builtin_expect(!(((n)->n_type) == 264 || ((n)->n_type) == 266), 0) ? __assert_rtn(__func__, "ast.c", 1244, "TYPE(n) == typedargslist || TYPE(n) == varargslist") : (void)0);





    for (i = 0; i < ((n)->n_nchildren); i++) {
        ch = (&(n)->n_child[i]);
        if (((ch)->n_type) == 16) {

            i++;
            if (i < ((n)->n_nchildren) &&
                ((((&(n)->n_child[i]))->n_type) == 265 ||
                 (((&(n)->n_child[i]))->n_type) == 267)) {
                i++;
            }
            break;
        }
        if (((ch)->n_type) == 35) break;
        if (((ch)->n_type) == 267 || ((ch)->n_type) == 265) nposargs++;
        if (((ch)->n_type) == 22) nposdefaults++;
    }


    for ( ; i < ((n)->n_nchildren); ++i) {
        ch = (&(n)->n_child[i]);
        if (((ch)->n_type) == 35) break;
        if (((ch)->n_type) == 265 || ((ch)->n_type) == 267) nkwonlyargs++;
    }
    posargs = (nposargs ? asdl_seq_new(nposargs, c->c_arena) : ((void *)0));
    if (!posargs && nposargs)
        return ((void *)0);
    kwonlyargs = (nkwonlyargs ?
                   asdl_seq_new(nkwonlyargs, c->c_arena) : ((void *)0));
    if (!kwonlyargs && nkwonlyargs)
        return ((void *)0);
    posdefaults = (nposdefaults ?
                    asdl_seq_new(nposdefaults, c->c_arena) : ((void *)0));
    if (!posdefaults && nposdefaults)
        return ((void *)0);



    kwdefaults = (nkwonlyargs ?
                   asdl_seq_new(nkwonlyargs, c->c_arena) : ((void *)0));
    if (!kwdefaults && nkwonlyargs)
        return ((void *)0);

    if (nposargs + nkwonlyargs > 255) {
        ast_error(c, n, "more than 255 arguments");
        return ((void *)0);
    }




    i = 0;
    j = 0;
    k = 0;
    while (i < ((n)->n_nchildren)) {
        ch = (&(n)->n_child[i]);
        switch (((ch)->n_type)) {
            case 265:
            case 267:



                if (i + 1 < ((n)->n_nchildren) && (((&(n)->n_child[i + 1]))->n_type) == 22) {
                    expr_ty expression = ast_for_expr(c, (&(n)->n_child[i + 2]));
                    if (!expression)
                        return ((void *)0);
                    (__builtin_expect(!(posdefaults != ((void *)0)), 0) ? __assert_rtn(__func__, "ast.c", 1315, "posdefaults != NULL") : (void)0);
                    (posdefaults)->elements[j++] = (expression);
                    i += 2;
                    found_default = 1;
                }
                else if (found_default) {
                    ast_error(c, n,
                             "non-default argument follows default argument");
                    return ((void *)0);
                }
                arg = ast_for_arg(c, ch);
                if (!arg)
                    return ((void *)0);
                (posargs)->elements[k++] = (arg);
                i += 2;
                break;
            case 16:
                if (i+1 >= ((n)->n_nchildren)) {
                    ast_error(c, (&(n)->n_child[i]),
                        "named arguments must follow bare *");
                    return ((void *)0);
                }
                ch = (&(n)->n_child[i+1]);
                if (((ch)->n_type) == 12) {
                    int res = 0;
                    i += 2;
                    res = handle_keywordonly_args(c, n, i,
                                                  kwonlyargs, kwdefaults);
                    if (res == -1) return ((void *)0);
                    i = res;
                }
                else {
                    vararg = new_identifier((((&(ch)->n_child[0]))->n_str), c);
                    if (!vararg)
                        return ((void *)0);
                    if (forbidden_name(c, vararg, (&(ch)->n_child[0]), 0))
                        return ((void *)0);
                    if (((ch)->n_nchildren) > 1) {

                        varargannotation = ast_for_expr(c, (&(ch)->n_child[2]));
                        if (!varargannotation)
                            return ((void *)0);
                    }
                    i += 3;
                    if (i < ((n)->n_nchildren) && ((((&(n)->n_child[i]))->n_type) == 265
                                    || (((&(n)->n_child[i]))->n_type) == 267)) {
                        int res = 0;
                        res = handle_keywordonly_args(c, n, i,
                                                      kwonlyargs, kwdefaults);
                        if (res == -1) return ((void *)0);
                        i = res;
                    }
                }
                break;
            case 35:
                ch = (&(n)->n_child[i+1]);
                (__builtin_expect(!(((ch)->n_type) == 265 || ((ch)->n_type) == 267), 0) ? __assert_rtn(__func__, "ast.c", 1371, "TYPE(ch) == tfpdef || TYPE(ch) == vfpdef") : (void)0);
                kwarg = new_identifier((((&(ch)->n_child[0]))->n_str), c);
                if (!kwarg)
                    return ((void *)0);
                if (((ch)->n_nchildren) > 1) {

                    kwargannotation = ast_for_expr(c, (&(ch)->n_child[2]));
                    if (!kwargannotation)
                        return ((void *)0);
                }
                if (forbidden_name(c, kwarg, (&(ch)->n_child[0]), 0))
                    return ((void *)0);
                i += 3;
                break;
            default:
                PyErr_Format(PyExc_SystemError,
                             "unexpected node in varargslist: %d @ %d",
                             ((ch)->n_type), i);
                return ((void *)0);
        }
    }
    return _Py_arguments(posargs, vararg, varargannotation, kwonlyargs, kwarg, kwargannotation, posdefaults, kwdefaults, c->c_arena);

}

static expr_ty
ast_for_dotted_name(struct compiling *c, const node *n)
{
    expr_ty e;
    identifier id;
    int lineno, col_offset;
    int i;

    (__builtin_expect(!(((n)->n_type) == (289)), 0) ? __assert_rtn(__func__, "ast.c", 1404, "TYPE(n) == (289)") : (void)0);

    lineno = ((n)->n_lineno);
    col_offset = n->n_col_offset;

    id = new_identifier((((&(n)->n_child[0]))->n_str), c);
    if (!id)
        return ((void *)0);
    e = _Py_Name(id, Load, lineno, col_offset, c->c_arena);
    if (!e)
        return ((void *)0);

    for (i = 2; i < ((n)->n_nchildren); i+=2) {
        id = new_identifier((((&(n)->n_child[i]))->n_str), c);
        if (!id)
            return ((void *)0);
        e = _Py_Attribute(e, id, Load, lineno, col_offset, c->c_arena);
        if (!e)
            return ((void *)0);
    }

    return e;
}

static expr_ty
ast_for_decorator(struct compiling *c, const node *n)
{

    expr_ty d = ((void *)0);
    expr_ty name_expr;

    (__builtin_expect(!(((n)->n_type) == (259)), 0) ? __assert_rtn(__func__, "ast.c", 1435, "TYPE(n) == (259)") : (void)0);
    (__builtin_expect(!((((&(n)->n_child[0]))->n_type) == (49)), 0) ? __assert_rtn(__func__, "ast.c", 1436, "TYPE((&(n)->n_child[0])) == (49)") : (void)0);
    (__builtin_expect(!(((((&(n)->n_child[((n)->n_nchildren) + -1])))->n_type) == (4)), 0) ? __assert_rtn(__func__, "ast.c", 1437, "TYPE(((&(n)->n_child[((n)->n_nchildren) + -1]))) == (4)") : (void)0);

    name_expr = ast_for_dotted_name(c, (&(n)->n_child[1]));
    if (!name_expr)
        return ((void *)0);

    if (((n)->n_nchildren) == 3) {
        d = name_expr;
        name_expr = ((void *)0);
    }
    else if (((n)->n_nchildren) == 5) {
        d = _Py_Call(name_expr, ((void *)0), ((void *)0), ((void *)0), ((void *)0), ((n)->n_lineno), n->n_col_offset, c->c_arena);

        if (!d)
            return ((void *)0);
        name_expr = ((void *)0);
    }
    else {
        d = ast_for_call(c, (&(n)->n_child[3]), name_expr);
        if (!d)
            return ((void *)0);
        name_expr = ((void *)0);
    }

    return d;
}

static asdl_seq*
ast_for_decorators(struct compiling *c, const node *n)
{
    asdl_seq* decorator_seq;
    expr_ty d;
    int i;

    (__builtin_expect(!(((n)->n_type) == (260)), 0) ? __assert_rtn(__func__, "ast.c", 1471, "TYPE(n) == (260)") : (void)0);
    decorator_seq = asdl_seq_new(((n)->n_nchildren), c->c_arena);
    if (!decorator_seq)
        return ((void *)0);

    for (i = 0; i < ((n)->n_nchildren); i++) {
        d = ast_for_decorator(c, (&(n)->n_child[i]));
        if (!d)
            return ((void *)0);
        (decorator_seq)->elements[i] = (d);
    }
    return decorator_seq;
}

static stmt_ty
ast_for_funcdef(struct compiling *c, const node *n, asdl_seq *decorator_seq)
{

    identifier name;
    arguments_ty args;
    asdl_seq *body;
    expr_ty returns = ((void *)0);
    int name_i = 1;

    (__builtin_expect(!(((n)->n_type) == (262)), 0) ? __assert_rtn(__func__, "ast.c", 1495, "TYPE(n) == (262)") : (void)0);

    name = new_identifier((((&(n)->n_child[name_i]))->n_str), c);
    if (!name)
        return ((void *)0);
    if (forbidden_name(c, name, (&(n)->n_child[name_i]), 0))
        return ((void *)0);
    args = ast_for_arguments(c, (&(n)->n_child[name_i + 1]));
    if (!args)
        return ((void *)0);
    if ((((&(n)->n_child[name_i+2]))->n_type) == 50) {
        returns = ast_for_expr(c, (&(n)->n_child[name_i + 3]));
        if (!returns)
            return ((void *)0);
        name_i += 2;
    }
    body = ast_for_suite(c, (&(n)->n_child[name_i + 3]));
    if (!body)
        return ((void *)0);

    return _Py_FunctionDef(name, args, body, decorator_seq, returns, ((n)->n_lineno), n->n_col_offset, c->c_arena);

}

static stmt_ty
ast_for_decorated(struct compiling *c, const node *n)
{

    stmt_ty thing = ((void *)0);
    asdl_seq *decorator_seq = ((void *)0);

    (__builtin_expect(!(((n)->n_type) == (261)), 0) ? __assert_rtn(__func__, "ast.c", 1526, "TYPE(n) == (261)") : (void)0);

    decorator_seq = ast_for_decorators(c, (&(n)->n_child[0]));
    if (!decorator_seq)
      return ((void *)0);

    (__builtin_expect(!((((&(n)->n_child[1]))->n_type) == 262 || (((&(n)->n_child[1]))->n_type) == 329), 0) ? __assert_rtn(__func__, "ast.c", 1533, "TYPE(CHILD(n, 1)) == funcdef || TYPE(CHILD(n, 1)) == classdef") : (void)0);


    if ((((&(n)->n_child[1]))->n_type) == 262) {
      thing = ast_for_funcdef(c, (&(n)->n_child[1]), decorator_seq);
    } else if ((((&(n)->n_child[1]))->n_type) == 329) {
      thing = ast_for_classdef(c, (&(n)->n_child[1]), decorator_seq);
    }


    if (thing) {
        thing->lineno = ((n)->n_lineno);
        thing->col_offset = n->n_col_offset;
    }
    return thing;
}

static expr_ty
ast_for_lambdef(struct compiling *c, const node *n)
{


    arguments_ty args;
    expr_ty expression;

    if (((n)->n_nchildren) == 3) {
        args = _Py_arguments(((void *)0), ((void *)0), ((void *)0), ((void *)0), ((void *)0), ((void *)0), ((void *)0), ((void *)0), c->c_arena);

        if (!args)
            return ((void *)0);
        expression = ast_for_expr(c, (&(n)->n_child[2]));
        if (!expression)
            return ((void *)0);
    }
    else {
        args = ast_for_arguments(c, (&(n)->n_child[1]));
        if (!args)
            return ((void *)0);
        expression = ast_for_expr(c, (&(n)->n_child[3]));
        if (!expression)
            return ((void *)0);
    }

    return _Py_Lambda(args, expression, ((n)->n_lineno), n->n_col_offset, c->c_arena);
}

static expr_ty
ast_for_ifexpr(struct compiling *c, const node *n)
{

    expr_ty expression, body, orelse;

    (__builtin_expect(!(((n)->n_nchildren) == 5), 0) ? __assert_rtn(__func__, "ast.c", 1584, "NCH(n) == 5") : (void)0);
    body = ast_for_expr(c, (&(n)->n_child[0]));
    if (!body)
        return ((void *)0);
    expression = ast_for_expr(c, (&(n)->n_child[2]));
    if (!expression)
        return ((void *)0);
    orelse = ast_for_expr(c, (&(n)->n_child[4]));
    if (!orelse)
        return ((void *)0);
    return _Py_IfExp(expression, body, orelse, ((n)->n_lineno), n->n_col_offset, c->c_arena);

}







static int
count_comp_fors(struct compiling *c, const node *n)
{
    int n_fors = 0;

  count_comp_for:
    n_fors++;
    (__builtin_expect(!(((n)->n_type) == (333)), 0) ? __assert_rtn(__func__, "ast.c", 1611, "TYPE(n) == (333)") : (void)0);
    if (((n)->n_nchildren) == 5)
        n = (&(n)->n_child[4]);
    else
        return n_fors;
  count_comp_iter:
    (__builtin_expect(!(((n)->n_type) == (332)), 0) ? __assert_rtn(__func__, "ast.c", 1617, "TYPE(n) == (332)") : (void)0);
    n = (&(n)->n_child[0]);
    if (((n)->n_type) == 333)
        goto count_comp_for;
    else if (((n)->n_type) == 334) {
        if (((n)->n_nchildren) == 3) {
            n = (&(n)->n_child[2]);
            goto count_comp_iter;
        }
        else
            return n_fors;
    }


    PyErr_SetString(PyExc_SystemError,
                    "logic error in count_comp_fors");
    return -1;
}






static int
count_comp_ifs(struct compiling *c, const node *n)
{
    int n_ifs = 0;

    while (1) {
        (__builtin_expect(!(((n)->n_type) == (332)), 0) ? __assert_rtn(__func__, "ast.c", 1647, "TYPE(n) == (332)") : (void)0);
        if ((((&(n)->n_child[0]))->n_type) == 333)
            return n_ifs;
        n = (&(n)->n_child[0]);
        (__builtin_expect(!(((n)->n_type) == (334)), 0) ? __assert_rtn(__func__, "ast.c", 1651, "TYPE(n) == (334)") : (void)0);
        n_ifs++;
        if (((n)->n_nchildren) == 2)
            return n_ifs;
        n = (&(n)->n_child[2]);
    }
}

static asdl_seq *
ast_for_comprehension(struct compiling *c, const node *n)
{
    int i, n_fors;
    asdl_seq *comps;

    n_fors = count_comp_fors(c, n);
    if (n_fors == -1)
        return ((void *)0);

    comps = asdl_seq_new(n_fors, c->c_arena);
    if (!comps)
        return ((void *)0);

    for (i = 0; i < n_fors; i++) {
        comprehension_ty comp;
        asdl_seq *t;
        expr_ty expression, first;
        node *for_ch;

        (__builtin_expect(!(((n)->n_type) == (333)), 0) ? __assert_rtn(__func__, "ast.c", 1679, "TYPE(n) == (333)") : (void)0);

        for_ch = (&(n)->n_child[1]);
        t = ast_for_exprlist(c, for_ch, Store);
        if (!t)
            return ((void *)0);
        expression = ast_for_expr(c, (&(n)->n_child[3]));
        if (!expression)
            return ((void *)0);



        first = (expr_ty)(t)->elements[(0)];
        if (((for_ch)->n_nchildren) == 1)
            comp = _Py_comprehension(first, expression, ((void *)0), c->c_arena);
        else
            comp = _Py_comprehension(_Py_Tuple(t, Store, first->lineno, first->col_offset, c->c_arena), expression, ((void *)0), c->c_arena);


        if (!comp)
            return ((void *)0);

        if (((n)->n_nchildren) == 5) {
            int j, n_ifs;
            asdl_seq *ifs;

            n = (&(n)->n_child[4]);
            n_ifs = count_comp_ifs(c, n);
            if (n_ifs == -1)
                return ((void *)0);

            ifs = asdl_seq_new(n_ifs, c->c_arena);
            if (!ifs)
                return ((void *)0);

            for (j = 0; j < n_ifs; j++) {
                (__builtin_expect(!(((n)->n_type) == (332)), 0) ? __assert_rtn(__func__, "ast.c", 1715, "TYPE(n) == (332)") : (void)0);
                n = (&(n)->n_child[0]);
                (__builtin_expect(!(((n)->n_type) == (334)), 0) ? __assert_rtn(__func__, "ast.c", 1717, "TYPE(n) == (334)") : (void)0);

                expression = ast_for_expr(c, (&(n)->n_child[1]));
                if (!expression)
                    return ((void *)0);
                (ifs)->elements[j] = (expression);
                if (((n)->n_nchildren) == 3)
                    n = (&(n)->n_child[2]);
            }

            if (((n)->n_type) == 332)
                n = (&(n)->n_child[0]);
            comp->ifs = ifs;
        }
        (comps)->elements[i] = (comp);
    }
    return comps;
}

static expr_ty
ast_for_itercomp(struct compiling *c, const node *n, int type)
{


    expr_ty elt;
    asdl_seq *comps;

    (__builtin_expect(!(((n)->n_nchildren) > 1), 0) ? __assert_rtn(__func__, "ast.c", 1744, "NCH(n) > 1") : (void)0);

    elt = ast_for_expr(c, (&(n)->n_child[0]));
    if (!elt)
        return ((void *)0);

    comps = ast_for_comprehension(c, (&(n)->n_child[1]));
    if (!comps)
        return ((void *)0);

    if (type == 0)
        return _Py_GeneratorExp(elt, comps, ((n)->n_lineno), n->n_col_offset, c->c_arena);
    else if (type == 1)
        return _Py_ListComp(elt, comps, ((n)->n_lineno), n->n_col_offset, c->c_arena);
    else if (type == 2)
        return _Py_SetComp(elt, comps, ((n)->n_lineno), n->n_col_offset, c->c_arena);
    else

        return ((void *)0);
}

static expr_ty
ast_for_dictcomp(struct compiling *c, const node *n)
{
    expr_ty key, value;
    asdl_seq *comps;

    (__builtin_expect(!(((n)->n_nchildren) > 3), 0) ? __assert_rtn(__func__, "ast.c", 1771, "NCH(n) > 3") : (void)0);
    (__builtin_expect(!((((&(n)->n_child[1]))->n_type) == (11)), 0) ? __assert_rtn(__func__, "ast.c", 1772, "TYPE((&(n)->n_child[1])) == (11)") : (void)0);

    key = ast_for_expr(c, (&(n)->n_child[0]));
    if (!key)
        return ((void *)0);
    value = ast_for_expr(c, (&(n)->n_child[2]));
    if (!value)
        return ((void *)0);

    comps = ast_for_comprehension(c, (&(n)->n_child[3]));
    if (!comps)
        return ((void *)0);

    return _Py_DictComp(key, value, comps, ((n)->n_lineno), n->n_col_offset, c->c_arena);
}

static expr_ty
ast_for_genexp(struct compiling *c, const node *n)
{
    (__builtin_expect(!(((n)->n_type) == (321) || ((n)->n_type) == (331)), 0) ? __assert_rtn(__func__, "ast.c", 1791, "TYPE(n) == (testlist_comp) || TYPE(n) == (argument)") : (void)0);
    return ast_for_itercomp(c, n, 0);
}

static expr_ty
ast_for_listcomp(struct compiling *c, const node *n)
{
    (__builtin_expect(!(((n)->n_type) == (321)), 0) ? __assert_rtn(__func__, "ast.c", 1798, "TYPE(n) == (testlist_comp)") : (void)0);
    return ast_for_itercomp(c, n, 1);
}

static expr_ty
ast_for_setcomp(struct compiling *c, const node *n)
{
    (__builtin_expect(!(((n)->n_type) == (328)), 0) ? __assert_rtn(__func__, "ast.c", 1805, "TYPE(n) == (dictorsetmaker)") : (void)0);
    return ast_for_itercomp(c, n, 2);
}


static expr_ty
ast_for_atom(struct compiling *c, const node *n)
{




    node *ch = (&(n)->n_child[0]);
    int bytesmode = 0;

    switch (((ch)->n_type)) {
    case 1: {


        PyObject *name = new_identifier(((ch)->n_str), c);
        if (!name)
            return ((void *)0);
        return _Py_Name(name, Load, ((n)->n_lineno), n->n_col_offset, c->c_arena);
    }
    case 3: {
        PyObject *str = parsestrplus(c, n, &bytesmode);
        if (!str) {
            const char *errtype = ((void *)0);
            if (PyErr_ExceptionMatches(PyExc_UnicodeError))
                errtype = "unicode error";
            else if (PyErr_ExceptionMatches(PyExc_ValueError))
                errtype = "value error";
            if (errtype) {
                char buf[128];
                PyObject *type, *value, *tback, *errstr;
                PyErr_Fetch(&type, &value, &tback);
                errstr = PyObject_Str(value);
                if (errstr) {
                    char *s = PyUnicode_AsUTF8(errstr);
                    PyOS_snprintf(buf, sizeof(buf), "(%s) %s", errtype, s);
                    do { if ( --((PyObject*)(errstr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(errstr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(errstr)))); } while (0);
                } else {
                    PyOS_snprintf(buf, sizeof(buf), "(%s) unknown error", errtype);
                }
                ast_error(c, n, buf);
                do { if ( --((PyObject*)(type))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type)))); } while (0);
                do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0);
                do { if ((tback) == ((void *)0)) ; else do { if ( --((PyObject*)(tback))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tback)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tback)))); } while (0); } while (0);
            }
            return ((void *)0);
        }
        PyArena_AddPyObject(c->c_arena, str);
        if (bytesmode)
            return _Py_Bytes(str, ((n)->n_lineno), n->n_col_offset, c->c_arena);
        else
            return _Py_Str(str, ((n)->n_lineno), n->n_col_offset, c->c_arena);
    }
    case 2: {
        PyObject *pynum = parsenumber(c, ((ch)->n_str));
        if (!pynum)
            return ((void *)0);

        PyArena_AddPyObject(c->c_arena, pynum);
        return _Py_Num(pynum, ((n)->n_lineno), n->n_col_offset, c->c_arena);
    }
    case 51:
        return _Py_Ellipsis(((n)->n_lineno), n->n_col_offset, c->c_arena);
    case 7:
        ch = (&(n)->n_child[1]);

        if (((ch)->n_type) == 8)
            return _Py_Tuple(((void *)0), Load, ((n)->n_lineno), n->n_col_offset, c->c_arena);

        if (((ch)->n_type) == 336)
            return ast_for_expr(c, ch);


        if ((((ch)->n_nchildren) > 1) && ((((&(ch)->n_child[1]))->n_type) == 333))
            return ast_for_genexp(c, ch);

        return ast_for_testlist(c, ch);
    case 9:
        ch = (&(n)->n_child[1]);

        if (((ch)->n_type) == 10)
            return _Py_List(((void *)0), Load, ((n)->n_lineno), n->n_col_offset, c->c_arena);

        (__builtin_expect(!(((ch)->n_type) == (321)), 0) ? __assert_rtn(__func__, "ast.c", 1892, "TYPE(ch) == (321)") : (void)0);
        if (((ch)->n_nchildren) == 1 || (((&(ch)->n_child[1]))->n_type) == 12) {
            asdl_seq *elts = seq_for_testlist(c, ch);
            if (!elts)
                return ((void *)0);

            return _Py_List(elts, Load, ((n)->n_lineno), n->n_col_offset, c->c_arena);
        }
        else
            return ast_for_listcomp(c, ch);
    case 25: {


        int i, size;
        asdl_seq *keys, *values;

        ch = (&(n)->n_child[1]);
        if (((ch)->n_type) == 26) {

            return _Py_Dict(((void *)0), ((void *)0), ((n)->n_lineno), n->n_col_offset, c->c_arena);
        } else if (((ch)->n_nchildren) == 1 || (((&(ch)->n_child[1]))->n_type) == 12) {

            asdl_seq *elts;
            size = (((ch)->n_nchildren) + 1) / 2;
            elts = asdl_seq_new(size, c->c_arena);
            if (!elts)
                return ((void *)0);
            for (i = 0; i < ((ch)->n_nchildren); i += 2) {
                expr_ty expression;
                expression = ast_for_expr(c, (&(ch)->n_child[i]));
                if (!expression)
                    return ((void *)0);
                (elts)->elements[i / 2] = (expression);
            }
            return _Py_Set(elts, ((n)->n_lineno), n->n_col_offset, c->c_arena);
        } else if ((((&(ch)->n_child[1]))->n_type) == 333) {

            return ast_for_setcomp(c, ch);
        } else if (((ch)->n_nchildren) > 3 && (((&(ch)->n_child[3]))->n_type) == 333) {
            return ast_for_dictcomp(c, ch);
        } else {

            size = (((ch)->n_nchildren) + 1) / 4;
            keys = asdl_seq_new(size, c->c_arena);
            if (!keys)
                return ((void *)0);

            values = asdl_seq_new(size, c->c_arena);
            if (!values)
                return ((void *)0);

            for (i = 0; i < ((ch)->n_nchildren); i += 4) {
                expr_ty expression;

                expression = ast_for_expr(c, (&(ch)->n_child[i]));
                if (!expression)
                    return ((void *)0);

                (keys)->elements[i / 4] = (expression);

                expression = ast_for_expr(c, (&(ch)->n_child[i + 2]));
                if (!expression)
                    return ((void *)0);

                (values)->elements[i / 4] = (expression);
            }
            return _Py_Dict(keys, values, ((n)->n_lineno), n->n_col_offset, c->c_arena);
        }
    }
    default:
        PyErr_Format(PyExc_SystemError, "unhandled atom %d", ((ch)->n_type));
        return ((void *)0);
    }
}

static slice_ty
ast_for_slice(struct compiling *c, const node *n)
{
    node *ch;
    expr_ty lower = ((void *)0), upper = ((void *)0), step = ((void *)0);

    (__builtin_expect(!(((n)->n_type) == (324)), 0) ? __assert_rtn(__func__, "ast.c", 1973, "TYPE(n) == (324)") : (void)0);





    ch = (&(n)->n_child[0]);
    if (((n)->n_nchildren) == 1 && ((ch)->n_type) == 302) {


        step = ast_for_expr(c, ch);
        if (!step)
            return ((void *)0);

        return _Py_Index(step, c->c_arena);
    }

    if (((ch)->n_type) == 302) {
        lower = ast_for_expr(c, ch);
        if (!lower)
            return ((void *)0);
    }


    if (((ch)->n_type) == 11) {
        if (((n)->n_nchildren) > 1) {
            node *n2 = (&(n)->n_child[1]);

            if (((n2)->n_type) == 302) {
                upper = ast_for_expr(c, n2);
                if (!upper)
                    return ((void *)0);
            }
        }
    } else if (((n)->n_nchildren) > 2) {
        node *n2 = (&(n)->n_child[2]);

        if (((n2)->n_type) == 302) {
            upper = ast_for_expr(c, n2);
            if (!upper)
                return ((void *)0);
        }
    }

    ch = (&(n)->n_child[((n)->n_nchildren) - 1]);
    if (((ch)->n_type) == 325) {
        if (((ch)->n_nchildren) != 1) {
            ch = (&(ch)->n_child[1]);
            if (((ch)->n_type) == 302) {
                step = ast_for_expr(c, ch);
                if (!step)
                    return ((void *)0);
            }
        }
    }

    return _Py_Slice(lower, upper, step, c->c_arena);
}

static expr_ty
ast_for_binop(struct compiling *c, const node *n)
{





    int i, nops;
    expr_ty expr1, expr2, result;
    operator_ty newoperator;

    expr1 = ast_for_expr(c, (&(n)->n_child[0]));
    if (!expr1)
        return ((void *)0);

    expr2 = ast_for_expr(c, (&(n)->n_child[2]));
    if (!expr2)
        return ((void *)0);

    newoperator = get_operator((&(n)->n_child[1]));
    if (!newoperator)
        return ((void *)0);

    result = _Py_BinOp(expr1, newoperator, expr2, ((n)->n_lineno), n->n_col_offset, c->c_arena);

    if (!result)
        return ((void *)0);

    nops = (((n)->n_nchildren) - 1) / 2;
    for (i = 1; i < nops; i++) {
        expr_ty tmp_result, tmp;
        const node* next_oper = (&(n)->n_child[i * 2 + 1]);

        newoperator = get_operator(next_oper);
        if (!newoperator)
            return ((void *)0);

        tmp = ast_for_expr(c, (&(n)->n_child[i * 2 + 2]));
        if (!tmp)
            return ((void *)0);

        tmp_result = _Py_BinOp(result, newoperator, tmp, ((next_oper)->n_lineno), next_oper->n_col_offset, c->c_arena);


        if (!tmp_result)
            return ((void *)0);
        result = tmp_result;
    }
    return result;
}

static expr_ty
ast_for_trailer(struct compiling *c, const node *n, expr_ty left_expr)
{




    (__builtin_expect(!(((n)->n_type) == (322)), 0) ? __assert_rtn(__func__, "ast.c", 2091, "TYPE(n) == (322)") : (void)0);
    if ((((&(n)->n_child[0]))->n_type) == 7) {
        if (((n)->n_nchildren) == 2)
            return _Py_Call(left_expr, ((void *)0), ((void *)0), ((void *)0), ((void *)0), ((n)->n_lineno), n->n_col_offset, c->c_arena);

        else
            return ast_for_call(c, (&(n)->n_child[1]), left_expr);
    }
    else if ((((&(n)->n_child[0]))->n_type) == 23 ) {
        PyObject *attr_id = new_identifier((((&(n)->n_child[1]))->n_str), c);
        if (!attr_id)
            return ((void *)0);
        return _Py_Attribute(left_expr, attr_id, Load, ((n)->n_lineno), n->n_col_offset, c->c_arena);

    }
    else {
        (__builtin_expect(!((((&(n)->n_child[0]))->n_type) == (9)), 0) ? __assert_rtn(__func__, "ast.c", 2107, "TYPE((&(n)->n_child[0])) == (9)") : (void)0);
        (__builtin_expect(!((((&(n)->n_child[2]))->n_type) == (10)), 0) ? __assert_rtn(__func__, "ast.c", 2108, "TYPE((&(n)->n_child[2])) == (10)") : (void)0);
        n = (&(n)->n_child[1]);
        if (((n)->n_nchildren) == 1) {
            slice_ty slc = ast_for_slice(c, (&(n)->n_child[0]));
            if (!slc)
                return ((void *)0);
            return _Py_Subscript(left_expr, slc, Load, ((n)->n_lineno), n->n_col_offset, c->c_arena);

        }
        else {




            int j;
            slice_ty slc;
            expr_ty e;
            int simple = 1;
            asdl_seq *slices, *elts;
            slices = asdl_seq_new((((n)->n_nchildren) + 1) / 2, c->c_arena);
            if (!slices)
                return ((void *)0);
            for (j = 0; j < ((n)->n_nchildren); j += 2) {
                slc = ast_for_slice(c, (&(n)->n_child[j]));
                if (!slc)
                    return ((void *)0);
                if (slc->kind != Index_kind)
                    simple = 0;
                (slices)->elements[j / 2] = (slc);
            }
            if (!simple) {
                return _Py_Subscript(left_expr, _Py_ExtSlice(slices, c->c_arena), Load, ((n)->n_lineno), n->n_col_offset, c->c_arena);

            }

            elts = asdl_seq_new(((slices) == ((void *)0) ? 0 : (slices)->size), c->c_arena);
            if (!elts)
                return ((void *)0);
            for (j = 0; j < ((slices) == ((void *)0) ? 0 : (slices)->size); ++j) {
                slc = (slice_ty)(slices)->elements[(j)];
                (__builtin_expect(!(slc->kind == Index_kind && slc->v.Index.value), 0) ? __assert_rtn(__func__, "ast.c", 2148, "slc->kind == Index_kind && slc->v.Index.value") : (void)0);
                (elts)->elements[j] = (slc->v.Index.value);
            }
            e = _Py_Tuple(elts, Load, ((n)->n_lineno), n->n_col_offset, c->c_arena);
            if (!e)
                return ((void *)0);
            return _Py_Subscript(left_expr, _Py_Index(e, c->c_arena), Load, ((n)->n_lineno), n->n_col_offset, c->c_arena);

        }
    }
}

static expr_ty
ast_for_factor(struct compiling *c, const node *n)
{
    expr_ty expression;

    expression = ast_for_expr(c, (&(n)->n_child[1]));
    if (!expression)
        return ((void *)0);

    switch ((((&(n)->n_child[0]))->n_type)) {
        case 14:
            return _Py_UnaryOp(UAdd, expression, ((n)->n_lineno), n->n_col_offset, c->c_arena);

        case 15:
            return _Py_UnaryOp(USub, expression, ((n)->n_lineno), n->n_col_offset, c->c_arena);

        case 31:
            return _Py_UnaryOp(Invert, expression, ((n)->n_lineno), n->n_col_offset, c->c_arena);

    }
    PyErr_Format(PyExc_SystemError, "unhandled factor: %d",
                 (((&(n)->n_child[0]))->n_type));
    return ((void *)0);
}

static expr_ty
ast_for_power(struct compiling *c, const node *n)
{


    int i;
    expr_ty e, tmp;
    (__builtin_expect(!(((n)->n_type) == (319)), 0) ? __assert_rtn(__func__, "ast.c", 2192, "TYPE(n) == (319)") : (void)0);
    e = ast_for_atom(c, (&(n)->n_child[0]));
    if (!e)
        return ((void *)0);
    if (((n)->n_nchildren) == 1)
        return e;
    for (i = 1; i < ((n)->n_nchildren); i++) {
        node *ch = (&(n)->n_child[i]);
        if (((ch)->n_type) != 322)
            break;
        tmp = ast_for_trailer(c, ch, e);
        if (!tmp)
            return ((void *)0);
        tmp->lineno = e->lineno;
        tmp->col_offset = e->col_offset;
        e = tmp;
    }
    if ((((&(n)->n_child[((n)->n_nchildren) - 1]))->n_type) == 318) {
        expr_ty f = ast_for_expr(c, (&(n)->n_child[((n)->n_nchildren) - 1]));
        if (!f)
            return ((void *)0);
        tmp = _Py_BinOp(e, Pow, f, ((n)->n_lineno), n->n_col_offset, c->c_arena);
        if (!tmp)
            return ((void *)0);
        e = tmp;
    }
    return e;
}

static expr_ty
ast_for_starred(struct compiling *c, const node *n)
{
    expr_ty tmp;
    (__builtin_expect(!(((n)->n_type) == (311)), 0) ? __assert_rtn(__func__, "ast.c", 2225, "TYPE(n) == (311)") : (void)0);

    tmp = ast_for_expr(c, (&(n)->n_child[1]));
    if (!tmp)
        return ((void *)0);


    return _Py_Starred(tmp, Load, ((n)->n_lineno), n->n_col_offset, c->c_arena);
}





static expr_ty
ast_for_expr(struct compiling *c, const node *n)
{
# 2259 "ast.c"
    asdl_seq *seq;
    int i;

 loop:
    switch (((n)->n_type)) {
        case 302:
        case 303:
            if ((((&(n)->n_child[0]))->n_type) == 304 ||
                (((&(n)->n_child[0]))->n_type) == 305)
                return ast_for_lambdef(c, (&(n)->n_child[0]));
            else if (((n)->n_nchildren) > 1)
                return ast_for_ifexpr(c, n);

        case 306:
        case 307:
            if (((n)->n_nchildren) == 1) {
                n = (&(n)->n_child[0]);
                goto loop;
            }
            seq = asdl_seq_new((((n)->n_nchildren) + 1) / 2, c->c_arena);
            if (!seq)
                return ((void *)0);
            for (i = 0; i < ((n)->n_nchildren); i += 2) {
                expr_ty e = ast_for_expr(c, (&(n)->n_child[i]));
                if (!e)
                    return ((void *)0);
                (seq)->elements[i / 2] = (e);
            }
            if (!strcmp((((&(n)->n_child[1]))->n_str), "and"))
                return _Py_BoolOp(And, seq, ((n)->n_lineno), n->n_col_offset, c->c_arena);

            (__builtin_expect(!(!strcmp((((&(n)->n_child[1]))->n_str), "or")), 0) ? __assert_rtn(__func__, "ast.c", 2290, "!strcmp(STR(CHILD(n, 1)), \"or\")") : (void)0);
            return _Py_BoolOp(Or, seq, ((n)->n_lineno), n->n_col_offset, c->c_arena);
        case 308:
            if (((n)->n_nchildren) == 1) {
                n = (&(n)->n_child[0]);
                goto loop;
            }
            else {
                expr_ty expression = ast_for_expr(c, (&(n)->n_child[1]));
                if (!expression)
                    return ((void *)0);

                return _Py_UnaryOp(Not, expression, ((n)->n_lineno), n->n_col_offset, c->c_arena);

            }
        case 309:
            if (((n)->n_nchildren) == 1) {
                n = (&(n)->n_child[0]);
                goto loop;
            }
            else {
                expr_ty expression;
                asdl_int_seq *ops;
                asdl_seq *cmps;
                ops = asdl_int_seq_new(((n)->n_nchildren) / 2, c->c_arena);
                if (!ops)
                    return ((void *)0);
                cmps = asdl_seq_new(((n)->n_nchildren) / 2, c->c_arena);
                if (!cmps) {
                    return ((void *)0);
                }
                for (i = 1; i < ((n)->n_nchildren); i += 2) {
                    cmpop_ty newoperator;

                    newoperator = ast_for_comp_op(c, (&(n)->n_child[i]));
                    if (!newoperator) {
                        return ((void *)0);
                    }

                    expression = ast_for_expr(c, (&(n)->n_child[i + 1]));
                    if (!expression) {
                        return ((void *)0);
                    }

                    (ops)->elements[i / 2] = (newoperator);
                    (cmps)->elements[i / 2] = (expression);
                }
                expression = ast_for_expr(c, (&(n)->n_child[0]));
                if (!expression) {
                    return ((void *)0);
                }

                return _Py_Compare(expression, ops, cmps, ((n)->n_lineno), n->n_col_offset, c->c_arena);

            }
            break;

        case 311:
            return ast_for_starred(c, n);




        case 312:
        case 313:
        case 314:
        case 315:
        case 316:
        case 317:
            if (((n)->n_nchildren) == 1) {
                n = (&(n)->n_child[0]);
                goto loop;
            }
            return ast_for_binop(c, n);
        case 336: {
            node *an = ((void *)0);
            node *en = ((void *)0);
            int is_from = 0;
            expr_ty exp = ((void *)0);
            if (((n)->n_nchildren) > 1)
                an = (&(n)->n_child[1]);
            if (an) {
                en = (&(an)->n_child[((an)->n_nchildren) - 1]);
                if (((an)->n_nchildren) == 2) {
                    is_from = 1;
                    exp = ast_for_expr(c, en);
                }
                else
                    exp = ast_for_testlist(c, en);
                if (!exp)
                    return ((void *)0);
            }
            if (is_from)
                return _Py_YieldFrom(exp, ((n)->n_lineno), n->n_col_offset, c->c_arena);
            return _Py_Yield(exp, ((n)->n_lineno), n->n_col_offset, c->c_arena);
        }
        case 318:
            if (((n)->n_nchildren) == 1) {
                n = (&(n)->n_child[0]);
                goto loop;
            }
            return ast_for_factor(c, n);
        case 319:
            return ast_for_power(c, n);
        default:
            PyErr_Format(PyExc_SystemError, "unhandled expr: %d", ((n)->n_type));
            return ((void *)0);
    }

    return ((void *)0);
}

static expr_ty
ast_for_call(struct compiling *c, const node *n, expr_ty func)
{






    int i, nargs, nkeywords, ngens;
    asdl_seq *args;
    asdl_seq *keywords;
    expr_ty vararg = ((void *)0), kwarg = ((void *)0);

    (__builtin_expect(!(((n)->n_type) == (330)), 0) ? __assert_rtn(__func__, "ast.c", 2416, "TYPE(n) == (330)") : (void)0);

    nargs = 0;
    nkeywords = 0;
    ngens = 0;
    for (i = 0; i < ((n)->n_nchildren); i++) {
        node *ch = (&(n)->n_child[i]);
        if (((ch)->n_type) == 331) {
            if (((ch)->n_nchildren) == 1)
                nargs++;
            else if ((((&(ch)->n_child[1]))->n_type) == 333)
                ngens++;
            else
                nkeywords++;
        }
    }
    if (ngens > 1 || (ngens && (nargs || nkeywords))) {
        ast_error(c, n, "Generator expression must be parenthesized "
                  "if not sole argument");
        return ((void *)0);
    }

    if (nargs + nkeywords + ngens > 255) {
        ast_error(c, n, "more than 255 arguments");
        return ((void *)0);
    }

    args = asdl_seq_new(nargs + ngens, c->c_arena);
    if (!args)
        return ((void *)0);
    keywords = asdl_seq_new(nkeywords, c->c_arena);
    if (!keywords)
        return ((void *)0);
    nargs = 0;
    nkeywords = 0;
    for (i = 0; i < ((n)->n_nchildren); i++) {
        node *ch = (&(n)->n_child[i]);
        if (((ch)->n_type) == 331) {
            expr_ty e;
            if (((ch)->n_nchildren) == 1) {
                if (nkeywords) {
                    ast_error(c, (&(ch)->n_child[0]),
                              "non-keyword arg after keyword arg");
                    return ((void *)0);
                }
                if (vararg) {
                    ast_error(c, (&(ch)->n_child[0]),
                              "only named arguments may follow *expression");
                    return ((void *)0);
                }
                e = ast_for_expr(c, (&(ch)->n_child[0]));
                if (!e)
                    return ((void *)0);
                (args)->elements[nargs++] = (e);
            }
            else if ((((&(ch)->n_child[1]))->n_type) == 333) {
                e = ast_for_genexp(c, ch);
                if (!e)
                    return ((void *)0);
                (args)->elements[nargs++] = (e);
            }
            else {
                keyword_ty kw;
                identifier key, tmp;
                int k;


                e = ast_for_expr(c, (&(ch)->n_child[0]));
                if (!e)
                    return ((void *)0);





                if (e->kind == Lambda_kind) {
                    ast_error(c, (&(ch)->n_child[0]), "lambda cannot contain assignment");
                    return ((void *)0);
                } else if (e->kind != Name_kind) {
                    ast_error(c, (&(ch)->n_child[0]), "keyword can't be an expression");
                    return ((void *)0);
                } else if (forbidden_name(c, e->v.Name.id, ch, 1)) {
                    return ((void *)0);
                }
                key = e->v.Name.id;
                for (k = 0; k < nkeywords; k++) {
                    tmp = ((keyword_ty)(keywords)->elements[(k)])->arg;
                    if (!PyUnicode_Compare(tmp, key)) {
                        ast_error(c, (&(ch)->n_child[0]), "keyword argument repeated");
                        return ((void *)0);
                    }
                }
                e = ast_for_expr(c, (&(ch)->n_child[2]));
                if (!e)
                    return ((void *)0);
                kw = _Py_keyword(key, e, c->c_arena);
                if (!kw)
                    return ((void *)0);
                (keywords)->elements[nkeywords++] = (kw);
            }
        }
        else if (((ch)->n_type) == 16) {
            vararg = ast_for_expr(c, (&(n)->n_child[i+1]));
            if (!vararg)
                return ((void *)0);
            i++;
        }
        else if (((ch)->n_type) == 35) {
            kwarg = ast_for_expr(c, (&(n)->n_child[i+1]));
            if (!kwarg)
                return ((void *)0);
            i++;
        }
    }

    return _Py_Call(func, args, keywords, vararg, kwarg, func->lineno, func->col_offset, c->c_arena);
}

static expr_ty
ast_for_testlist(struct compiling *c, const node* n)
{


    (__builtin_expect(!(((n)->n_nchildren) > 0), 0) ? __assert_rtn(__func__, "ast.c", 2539, "NCH(n) > 0") : (void)0);
    if (((n)->n_type) == 321) {
        if (((n)->n_nchildren) > 1)
            (__builtin_expect(!((((&(n)->n_child[1]))->n_type) != 333), 0) ? __assert_rtn(__func__, "ast.c", 2542, "TYPE(CHILD(n, 1)) != comp_for") : (void)0);
    }
    else {
        (__builtin_expect(!(((n)->n_type) == 327 || ((n)->n_type) == 272), 0) ? __assert_rtn(__func__, "ast.c", 2546, "TYPE(n) == testlist || TYPE(n) == testlist_star_expr") : (void)0);

    }
    if (((n)->n_nchildren) == 1)
        return ast_for_expr(c, (&(n)->n_child[0]));
    else {
        asdl_seq *tmp = seq_for_testlist(c, n);
        if (!tmp)
            return ((void *)0);
        return _Py_Tuple(tmp, Load, ((n)->n_lineno), n->n_col_offset, c->c_arena);
    }
}

static stmt_ty
ast_for_expr_stmt(struct compiling *c, const node *n)
{
    (__builtin_expect(!(((n)->n_type) == (271)), 0) ? __assert_rtn(__func__, "ast.c", 2561, "TYPE(n) == (271)") : (void)0);
# 2570 "ast.c"
    if (((n)->n_nchildren) == 1) {
        expr_ty e = ast_for_testlist(c, (&(n)->n_child[0]));
        if (!e)
            return ((void *)0);

        return _Py_Expr(e, ((n)->n_lineno), n->n_col_offset, c->c_arena);
    }
    else if ((((&(n)->n_child[1]))->n_type) == 273) {
        expr_ty expr1, expr2;
        operator_ty newoperator;
        node *ch = (&(n)->n_child[0]);

        expr1 = ast_for_testlist(c, ch);
        if (!expr1)
            return ((void *)0);
        if(!set_context(c, expr1, Store, ch))
            return ((void *)0);




        switch (expr1->kind) {
            case Name_kind:
            case Attribute_kind:
            case Subscript_kind:
                break;
            default:
                ast_error(c, ch, "illegal expression for augmented assignment");
                return ((void *)0);
        }

        ch = (&(n)->n_child[2]);
        if (((ch)->n_type) == 327)
            expr2 = ast_for_testlist(c, ch);
        else
            expr2 = ast_for_expr(c, ch);
        if (!expr2)
            return ((void *)0);

        newoperator = ast_for_augassign(c, (&(n)->n_child[1]));
        if (!newoperator)
            return ((void *)0);

        return _Py_AugAssign(expr1, newoperator, expr2, ((n)->n_lineno), n->n_col_offset, c->c_arena);
    }
    else {
        int i;
        asdl_seq *targets;
        node *value;
        expr_ty expression;


        (__builtin_expect(!((((&(n)->n_child[1]))->n_type) == (22)), 0) ? __assert_rtn(__func__, "ast.c", 2622, "TYPE((&(n)->n_child[1])) == (22)") : (void)0);
        targets = asdl_seq_new(((n)->n_nchildren) / 2, c->c_arena);
        if (!targets)
            return ((void *)0);
        for (i = 0; i < ((n)->n_nchildren) - 2; i += 2) {
            expr_ty e;
            node *ch = (&(n)->n_child[i]);
            if (((ch)->n_type) == 336) {
                ast_error(c, ch, "assignment to yield expression not possible");
                return ((void *)0);
            }
            e = ast_for_testlist(c, ch);
            if (!e)
              return ((void *)0);


            if (!set_context(c, e, Store, (&(n)->n_child[i])))
              return ((void *)0);

            (targets)->elements[i / 2] = (e);
        }
        value = (&(n)->n_child[((n)->n_nchildren) - 1]);
        if (((value)->n_type) == 272)
            expression = ast_for_testlist(c, value);
        else
            expression = ast_for_expr(c, value);
        if (!expression)
            return ((void *)0);
        return _Py_Assign(targets, expression, ((n)->n_lineno), n->n_col_offset, c->c_arena);
    }
}


static asdl_seq *
ast_for_exprlist(struct compiling *c, const node *n, expr_context_ty context)
{
    asdl_seq *seq;
    int i;
    expr_ty e;

    (__builtin_expect(!(((n)->n_type) == (326)), 0) ? __assert_rtn(__func__, "ast.c", 2662, "TYPE(n) == (326)") : (void)0);

    seq = asdl_seq_new((((n)->n_nchildren) + 1) / 2, c->c_arena);
    if (!seq)
        return ((void *)0);
    for (i = 0; i < ((n)->n_nchildren); i += 2) {
        e = ast_for_expr(c, (&(n)->n_child[i]));
        if (!e)
            return ((void *)0);
        (seq)->elements[i / 2] = (e);
        if (context && !set_context(c, e, context, (&(n)->n_child[i])))
            return ((void *)0);
    }
    return seq;
}

static stmt_ty
ast_for_del_stmt(struct compiling *c, const node *n)
{
    asdl_seq *expr_list;


    (__builtin_expect(!(((n)->n_type) == (274)), 0) ? __assert_rtn(__func__, "ast.c", 2684, "TYPE(n) == (274)") : (void)0);

    expr_list = ast_for_exprlist(c, (&(n)->n_child[1]), Del);
    if (!expr_list)
        return ((void *)0);
    return _Py_Delete(expr_list, ((n)->n_lineno), n->n_col_offset, c->c_arena);
}

static stmt_ty
ast_for_flow_stmt(struct compiling *c, const node *n)
{
# 2705 "ast.c"
    node *ch;

    (__builtin_expect(!(((n)->n_type) == (276)), 0) ? __assert_rtn(__func__, "ast.c", 2707, "TYPE(n) == (276)") : (void)0);
    ch = (&(n)->n_child[0]);
    switch (((ch)->n_type)) {
        case 277:
            return _Py_Break(((n)->n_lineno), n->n_col_offset, c->c_arena);
        case 278:
            return _Py_Continue(((n)->n_lineno), n->n_col_offset, c->c_arena);
        case 280: {
            expr_ty exp = ast_for_expr(c, (&(ch)->n_child[0]));
            if (!exp)
                return ((void *)0);
            return _Py_Expr(exp, ((n)->n_lineno), n->n_col_offset, c->c_arena);
        }
        case 279:
            if (((ch)->n_nchildren) == 1)
                return _Py_Return(((void *)0), ((n)->n_lineno), n->n_col_offset, c->c_arena);
            else {
                expr_ty expression = ast_for_testlist(c, (&(ch)->n_child[1]));
                if (!expression)
                    return ((void *)0);
                return _Py_Return(expression, ((n)->n_lineno), n->n_col_offset, c->c_arena);
            }
        case 281:
            if (((ch)->n_nchildren) == 1)
                return _Py_Raise(((void *)0), ((void *)0), ((n)->n_lineno), n->n_col_offset, c->c_arena);
            else if (((ch)->n_nchildren) >= 2) {
                expr_ty cause = ((void *)0);
                expr_ty expression = ast_for_expr(c, (&(ch)->n_child[1]));
                if (!expression)
                    return ((void *)0);
                if (((ch)->n_nchildren) == 4) {
                    cause = ast_for_expr(c, (&(ch)->n_child[3]));
                    if (!cause)
                        return ((void *)0);
                }
                return _Py_Raise(expression, cause, ((n)->n_lineno), n->n_col_offset, c->c_arena);
            }
        default:
            PyErr_Format(PyExc_SystemError,
                         "unexpected flow_stmt: %d", ((ch)->n_type));
            return ((void *)0);
    }

    PyErr_SetString(PyExc_SystemError, "unhandled flow statement");
    return ((void *)0);
}

static alias_ty
alias_for_import_name(struct compiling *c, const node *n, int store)
{





    identifier str, name;

 loop:
    switch (((n)->n_type)) {
        case 285: {
            node *name_node = (&(n)->n_child[0]);
            str = ((void *)0);
            name = new_identifier(((name_node)->n_str), c);
            if (!name)
                return ((void *)0);
            if (((n)->n_nchildren) == 3) {
                node *str_node = (&(n)->n_child[2]);
                str = new_identifier(((str_node)->n_str), c);
                if (!str)
                    return ((void *)0);
                if (store && forbidden_name(c, str, str_node, 0))
                    return ((void *)0);
            }
            else {
                if (forbidden_name(c, name, name_node, 0))
                    return ((void *)0);
            }
            return _Py_alias(name, str, c->c_arena);
        }
        case 286:
            if (((n)->n_nchildren) == 1) {
                n = (&(n)->n_child[0]);
                goto loop;
            }
            else {
                node *asname_node = (&(n)->n_child[2]);
                alias_ty a = alias_for_import_name(c, (&(n)->n_child[0]), 0);
                if (!a)
                    return ((void *)0);
                (__builtin_expect(!(!a->asname), 0) ? __assert_rtn(__func__, "ast.c", 2796, "!a->asname") : (void)0);
                a->asname = new_identifier(((asname_node)->n_str), c);
                if (!a->asname)
                    return ((void *)0);
                if (forbidden_name(c, a->asname, asname_node, 0))
                    return ((void *)0);
                return a;
            }
            break;
        case 289:
            if (((n)->n_nchildren) == 1) {
                node *name_node = (&(n)->n_child[0]);
                name = new_identifier(((name_node)->n_str), c);
                if (!name)
                    return ((void *)0);
                if (store && forbidden_name(c, name, name_node, 0))
                    return ((void *)0);
                return _Py_alias(name, ((void *)0), c->c_arena);
            }
            else {

                int i;
                size_t len;
                char *s;
                PyObject *uni;

                len = 0;
                for (i = 0; i < ((n)->n_nchildren); i += 2)

                    len += strlen((((&(n)->n_child[i]))->n_str)) + 1;
                len--;
                str = PyBytes_FromStringAndSize(((void *)0), len);
                if (!str)
                    return ((void *)0);
                s = ((__builtin_expect(!(((((((PyObject*)(str))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "ast.c", 2830, "PyBytes_Check(str)") : (void)0), (((PyBytesObject *)(str))->ob_sval));
                if (!s)
                    return ((void *)0);
                for (i = 0; i < ((n)->n_nchildren); i += 2) {
                    char *sch = (((&(n)->n_child[i]))->n_str);
                    ((__builtin_object_size (s, 0) != (size_t) -1) ? __builtin___strcpy_chk (s, (((&(n)->n_child[i]))->n_str), __builtin_object_size (s, 2 > 1)) : __inline_strcpy_chk (s, (((&(n)->n_child[i]))->n_str)));
                    s += strlen(sch);
                    *s++ = '.';
                }
                --s;
                *s = '\0';
                uni = PyUnicode_DecodeUTF8(((__builtin_expect(!(((((((PyObject*)(str))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "ast.c", 2841, "PyBytes_Check(str)") : (void)0), (((PyBytesObject *)(str))->ob_sval)),
                                           ((__builtin_expect(!(((((((PyObject*)(str))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "ast.c", 2842, "PyBytes_Check(str)") : (void)0),(((PyVarObject*)(str))->ob_size)),
                                           ((void *)0));
                do { if ( --((PyObject*)(str))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(str)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(str)))); } while (0);
                if (!uni)
                    return ((void *)0);
                str = uni;
                PyUnicode_InternInPlace(&str);
                PyArena_AddPyObject(c->c_arena, str);
                return _Py_alias(str, ((void *)0), c->c_arena);
            }
            break;
        case 16:
            str = PyUnicode_InternFromString("*");
            PyArena_AddPyObject(c->c_arena, str);
            return _Py_alias(str, ((void *)0), c->c_arena);
        default:
            PyErr_Format(PyExc_SystemError,
                         "unexpected import name: %d", ((n)->n_type));
            return ((void *)0);
    }

    PyErr_SetString(PyExc_SystemError, "unhandled import name condition");
    return ((void *)0);
}

static stmt_ty
ast_for_import_stmt(struct compiling *c, const node *n)
{






    int lineno;
    int col_offset;
    int i;
    asdl_seq *aliases;

    (__builtin_expect(!(((n)->n_type) == (282)), 0) ? __assert_rtn(__func__, "ast.c", 2881, "TYPE(n) == (282)") : (void)0);
    lineno = ((n)->n_lineno);
    col_offset = n->n_col_offset;
    n = (&(n)->n_child[0]);
    if (((n)->n_type) == 283) {
        n = (&(n)->n_child[1]);
        (__builtin_expect(!(((n)->n_type) == (288)), 0) ? __assert_rtn(__func__, "ast.c", 2887, "TYPE(n) == (288)") : (void)0);
        aliases = asdl_seq_new((((n)->n_nchildren) + 1) / 2, c->c_arena);
        if (!aliases)
                return ((void *)0);
        for (i = 0; i < ((n)->n_nchildren); i += 2) {
            alias_ty import_alias = alias_for_import_name(c, (&(n)->n_child[i]), 1);
            if (!import_alias)
                return ((void *)0);
            (aliases)->elements[i / 2] = (import_alias);
        }
        return _Py_Import(aliases, lineno, col_offset, c->c_arena);
    }
    else if (((n)->n_type) == 284) {
        int n_children;
        int idx, ndots = 0;
        alias_ty mod = ((void *)0);
        identifier modname = ((void *)0);



        for (idx = 1; idx < ((n)->n_nchildren); idx++) {
            if ((((&(n)->n_child[idx]))->n_type) == 289) {
                mod = alias_for_import_name(c, (&(n)->n_child[idx]), 0);
                if (!mod)
                    return ((void *)0);
                idx++;
                break;
            } else if ((((&(n)->n_child[idx]))->n_type) == 51) {

                ndots += 3;
                continue;
            } else if ((((&(n)->n_child[idx]))->n_type) != 23) {
                break;
            }
            ndots++;
        }
        idx++;
        switch ((((&(n)->n_child[idx]))->n_type)) {
        case 16:

            n = (&(n)->n_child[idx]);
            n_children = 1;
            break;
        case 7:

            n = (&(n)->n_child[idx + 1]);
            n_children = ((n)->n_nchildren);
            break;
        case 287:

            n = (&(n)->n_child[idx]);
            n_children = ((n)->n_nchildren);
            if (n_children % 2 == 0) {
                ast_error(c, n, "trailing comma not allowed without"
                             " surrounding parentheses");
                return ((void *)0);
            }
            break;
        default:
            ast_error(c, n, "Unexpected node-type in from-import");
            return ((void *)0);
        }

        aliases = asdl_seq_new((n_children + 1) / 2, c->c_arena);
        if (!aliases)
            return ((void *)0);


        if (((n)->n_type) == 16) {
            alias_ty import_alias = alias_for_import_name(c, n, 1);
            if (!import_alias)
                return ((void *)0);
                (aliases)->elements[0] = (import_alias);
        }
        else {
            for (i = 0; i < ((n)->n_nchildren); i += 2) {
                alias_ty import_alias = alias_for_import_name(c, (&(n)->n_child[i]), 1);
                if (!import_alias)
                    return ((void *)0);
                    (aliases)->elements[i / 2] = (import_alias);
            }
        }
        if (mod != ((void *)0))
            modname = mod->name;
        return _Py_ImportFrom(modname, aliases, ndots, lineno, col_offset, c->c_arena);

    }
    PyErr_Format(PyExc_SystemError,
                 "unknown import statement: starts with command '%s'",
                 (((&(n)->n_child[0]))->n_str));
    return ((void *)0);
}

static stmt_ty
ast_for_global_stmt(struct compiling *c, const node *n)
{

    identifier name;
    asdl_seq *s;
    int i;

    (__builtin_expect(!(((n)->n_type) == (290)), 0) ? __assert_rtn(__func__, "ast.c", 2988, "TYPE(n) == (290)") : (void)0);
    s = asdl_seq_new(((n)->n_nchildren) / 2, c->c_arena);
    if (!s)
        return ((void *)0);
    for (i = 1; i < ((n)->n_nchildren); i += 2) {
        name = new_identifier((((&(n)->n_child[i]))->n_str), c);
        if (!name)
            return ((void *)0);
        (s)->elements[i / 2] = (name);
    }
    return _Py_Global(s, ((n)->n_lineno), n->n_col_offset, c->c_arena);
}

static stmt_ty
ast_for_nonlocal_stmt(struct compiling *c, const node *n)
{

    identifier name;
    asdl_seq *s;
    int i;

    (__builtin_expect(!(((n)->n_type) == (291)), 0) ? __assert_rtn(__func__, "ast.c", 3009, "TYPE(n) == (291)") : (void)0);
    s = asdl_seq_new(((n)->n_nchildren) / 2, c->c_arena);
    if (!s)
        return ((void *)0);
    for (i = 1; i < ((n)->n_nchildren); i += 2) {
        name = new_identifier((((&(n)->n_child[i]))->n_str), c);
        if (!name)
            return ((void *)0);
        (s)->elements[i / 2] = (name);
    }
    return _Py_Nonlocal(s, ((n)->n_lineno), n->n_col_offset, c->c_arena);
}

static stmt_ty
ast_for_assert_stmt(struct compiling *c, const node *n)
{

    (__builtin_expect(!(((n)->n_type) == (292)), 0) ? __assert_rtn(__func__, "ast.c", 3026, "TYPE(n) == (292)") : (void)0);
    if (((n)->n_nchildren) == 2) {
        expr_ty expression = ast_for_expr(c, (&(n)->n_child[1]));
        if (!expression)
            return ((void *)0);
        return _Py_Assert(expression, ((void *)0), ((n)->n_lineno), n->n_col_offset, c->c_arena);
    }
    else if (((n)->n_nchildren) == 4) {
        expr_ty expr1, expr2;

        expr1 = ast_for_expr(c, (&(n)->n_child[1]));
        if (!expr1)
            return ((void *)0);
        expr2 = ast_for_expr(c, (&(n)->n_child[3]));
        if (!expr2)
            return ((void *)0);

        return _Py_Assert(expr1, expr2, ((n)->n_lineno), n->n_col_offset, c->c_arena);
    }
    PyErr_Format(PyExc_SystemError,
                 "improper number of parts to 'assert' statement: %d",
                 ((n)->n_nchildren));
    return ((void *)0);
}

static asdl_seq *
ast_for_suite(struct compiling *c, const node *n)
{

    asdl_seq *seq;
    stmt_ty s;
    int i, total, num, end, pos = 0;
    node *ch;

    (__builtin_expect(!(((n)->n_type) == (301)), 0) ? __assert_rtn(__func__, "ast.c", 3060, "TYPE(n) == (301)") : (void)0);

    total = num_stmts(n);
    seq = asdl_seq_new(total, c->c_arena);
    if (!seq)
        return ((void *)0);
    if ((((&(n)->n_child[0]))->n_type) == 269) {
        n = (&(n)->n_child[0]);



        end = ((n)->n_nchildren) - 1;
        if ((((&(n)->n_child[end - 1]))->n_type) == 13)
            end--;

        for (i = 0; i < end; i += 2) {
            ch = (&(n)->n_child[i]);
            s = ast_for_stmt(c, ch);
            if (!s)
                return ((void *)0);
            (seq)->elements[pos++] = (s);
        }
    }
    else {
        for (i = 2; i < (((n)->n_nchildren) - 1); i++) {
            ch = (&(n)->n_child[i]);
            (__builtin_expect(!(((ch)->n_type) == (268)), 0) ? __assert_rtn(__func__, "ast.c", 3086, "TYPE(ch) == (268)") : (void)0);
            num = num_stmts(ch);
            if (num == 1) {

                s = ast_for_stmt(c, ch);
                if (!s)
                    return ((void *)0);
                (seq)->elements[pos++] = (s);
            }
            else {
                int j;
                ch = (&(ch)->n_child[0]);
                (__builtin_expect(!(((ch)->n_type) == (269)), 0) ? __assert_rtn(__func__, "ast.c", 3098, "TYPE(ch) == (269)") : (void)0);
                for (j = 0; j < ((ch)->n_nchildren); j += 2) {

                    if ((((&(ch)->n_child[j]))->n_nchildren) == 0) {
                        (__builtin_expect(!((j + 1) == ((ch)->n_nchildren)), 0) ? __assert_rtn(__func__, "ast.c", 3102, "(j + 1) == NCH(ch)") : (void)0);
                        break;
                    }
                    s = ast_for_stmt(c, (&(ch)->n_child[j]));
                    if (!s)
                        return ((void *)0);
                    (seq)->elements[pos++] = (s);
                }
            }
        }
    }
    (__builtin_expect(!(pos == seq->size), 0) ? __assert_rtn(__func__, "ast.c", 3113, "pos == seq->size") : (void)0);
    return seq;
}

static stmt_ty
ast_for_if_stmt(struct compiling *c, const node *n)
{



    char *s;

    (__builtin_expect(!(((n)->n_type) == (294)), 0) ? __assert_rtn(__func__, "ast.c", 3125, "TYPE(n) == (294)") : (void)0);

    if (((n)->n_nchildren) == 4) {
        expr_ty expression;
        asdl_seq *suite_seq;

        expression = ast_for_expr(c, (&(n)->n_child[1]));
        if (!expression)
            return ((void *)0);
        suite_seq = ast_for_suite(c, (&(n)->n_child[3]));
        if (!suite_seq)
            return ((void *)0);

        return _Py_If(expression, suite_seq, ((void *)0), ((n)->n_lineno), n->n_col_offset, c->c_arena);

    }

    s = (((&(n)->n_child[4]))->n_str);




    if (s[2] == 's') {
        expr_ty expression;
        asdl_seq *seq1, *seq2;

        expression = ast_for_expr(c, (&(n)->n_child[1]));
        if (!expression)
            return ((void *)0);
        seq1 = ast_for_suite(c, (&(n)->n_child[3]));
        if (!seq1)
            return ((void *)0);
        seq2 = ast_for_suite(c, (&(n)->n_child[6]));
        if (!seq2)
            return ((void *)0);

        return _Py_If(expression, seq1, seq2, ((n)->n_lineno), n->n_col_offset, c->c_arena);

    }
    else if (s[2] == 'i') {
        int i, n_elif, has_else = 0;
        expr_ty expression;
        asdl_seq *suite_seq;
        asdl_seq *orelse = ((void *)0);
        n_elif = ((n)->n_nchildren) - 4;


        if ((((&(n)->n_child[(n_elif + 1)]))->n_type) == 1
            && (((&(n)->n_child[(n_elif + 1)]))->n_str)[2] == 's') {
            has_else = 1;
            n_elif -= 3;
        }
        n_elif /= 4;

        if (has_else) {
            asdl_seq *suite_seq2;

            orelse = asdl_seq_new(1, c->c_arena);
            if (!orelse)
                return ((void *)0);
            expression = ast_for_expr(c, (&(n)->n_child[((n)->n_nchildren) - 6]));
            if (!expression)
                return ((void *)0);
            suite_seq = ast_for_suite(c, (&(n)->n_child[((n)->n_nchildren) - 4]));
            if (!suite_seq)
                return ((void *)0);
            suite_seq2 = ast_for_suite(c, (&(n)->n_child[((n)->n_nchildren) - 1]));
            if (!suite_seq2)
                return ((void *)0);

            (orelse)->elements[0] = (_Py_If(expression, suite_seq, suite_seq2, (((&(n)->n_child[((n)->n_nchildren) - 6]))->n_lineno), (&(n)->n_child[((n)->n_nchildren) - 6])->n_col_offset, c->c_arena));





            n_elif--;
        }

        for (i = 0; i < n_elif; i++) {
            int off = 5 + (n_elif - i - 1) * 4;
            asdl_seq *newobj = asdl_seq_new(1, c->c_arena);
            if (!newobj)
                return ((void *)0);
            expression = ast_for_expr(c, (&(n)->n_child[off]));
            if (!expression)
                return ((void *)0);
            suite_seq = ast_for_suite(c, (&(n)->n_child[off + 2]));
            if (!suite_seq)
                return ((void *)0);

            (newobj)->elements[0] = (_Py_If(expression, suite_seq, orelse, (((&(n)->n_child[off]))->n_lineno), (&(n)->n_child[off])->n_col_offset, c->c_arena));



            orelse = newobj;
        }
        expression = ast_for_expr(c, (&(n)->n_child[1]));
        if (!expression)
            return ((void *)0);
        suite_seq = ast_for_suite(c, (&(n)->n_child[3]));
        if (!suite_seq)
            return ((void *)0);
        return _Py_If(expression, suite_seq, orelse, ((n)->n_lineno), n->n_col_offset, c->c_arena);

    }

    PyErr_Format(PyExc_SystemError,
                 "unexpected token in 'if' statement: %s", s);
    return ((void *)0);
}

static stmt_ty
ast_for_while_stmt(struct compiling *c, const node *n)
{

    (__builtin_expect(!(((n)->n_type) == (295)), 0) ? __assert_rtn(__func__, "ast.c", 3241, "TYPE(n) == (295)") : (void)0);

    if (((n)->n_nchildren) == 4) {
        expr_ty expression;
        asdl_seq *suite_seq;

        expression = ast_for_expr(c, (&(n)->n_child[1]));
        if (!expression)
            return ((void *)0);
        suite_seq = ast_for_suite(c, (&(n)->n_child[3]));
        if (!suite_seq)
            return ((void *)0);
        return _Py_While(expression, suite_seq, ((void *)0), ((n)->n_lineno), n->n_col_offset, c->c_arena);
    }
    else if (((n)->n_nchildren) == 7) {
        expr_ty expression;
        asdl_seq *seq1, *seq2;

        expression = ast_for_expr(c, (&(n)->n_child[1]));
        if (!expression)
            return ((void *)0);
        seq1 = ast_for_suite(c, (&(n)->n_child[3]));
        if (!seq1)
            return ((void *)0);
        seq2 = ast_for_suite(c, (&(n)->n_child[6]));
        if (!seq2)
            return ((void *)0);

        return _Py_While(expression, seq1, seq2, ((n)->n_lineno), n->n_col_offset, c->c_arena);
    }

    PyErr_Format(PyExc_SystemError,
                 "wrong number of tokens for 'while' statement: %d",
                 ((n)->n_nchildren));
    return ((void *)0);
}

static stmt_ty
ast_for_for_stmt(struct compiling *c, const node *n)
{
    asdl_seq *_target, *seq = ((void *)0), *suite_seq;
    expr_ty expression;
    expr_ty target, first;
    const node *node_target;

    (__builtin_expect(!(((n)->n_type) == (296)), 0) ? __assert_rtn(__func__, "ast.c", 3286, "TYPE(n) == (296)") : (void)0);

    if (((n)->n_nchildren) == 9) {
        seq = ast_for_suite(c, (&(n)->n_child[8]));
        if (!seq)
            return ((void *)0);
    }

    node_target = (&(n)->n_child[1]);
    _target = ast_for_exprlist(c, node_target, Store);
    if (!_target)
        return ((void *)0);


    first = (expr_ty)(_target)->elements[(0)];
    if (((node_target)->n_nchildren) == 1)
        target = first;
    else
        target = _Py_Tuple(_target, Store, first->lineno, first->col_offset, c->c_arena);

    expression = ast_for_testlist(c, (&(n)->n_child[3]));
    if (!expression)
        return ((void *)0);
    suite_seq = ast_for_suite(c, (&(n)->n_child[5]));
    if (!suite_seq)
        return ((void *)0);

    return _Py_For(target, expression, suite_seq, seq, ((n)->n_lineno), n->n_col_offset, c->c_arena);

}

static excepthandler_ty
ast_for_except_clause(struct compiling *c, const node *exc, node *body)
{

    (__builtin_expect(!(((exc)->n_type) == (300)), 0) ? __assert_rtn(__func__, "ast.c", 3321, "TYPE(exc) == (300)") : (void)0);
    (__builtin_expect(!(((body)->n_type) == (301)), 0) ? __assert_rtn(__func__, "ast.c", 3322, "TYPE(body) == (301)") : (void)0);

    if (((exc)->n_nchildren) == 1) {
        asdl_seq *suite_seq = ast_for_suite(c, body);
        if (!suite_seq)
            return ((void *)0);

        return _Py_ExceptHandler(((void *)0), ((void *)0), suite_seq, ((exc)->n_lineno), exc->n_col_offset, c->c_arena);

    }
    else if (((exc)->n_nchildren) == 2) {
        expr_ty expression;
        asdl_seq *suite_seq;

        expression = ast_for_expr(c, (&(exc)->n_child[1]));
        if (!expression)
            return ((void *)0);
        suite_seq = ast_for_suite(c, body);
        if (!suite_seq)
            return ((void *)0);

        return _Py_ExceptHandler(expression, ((void *)0), suite_seq, ((exc)->n_lineno), exc->n_col_offset, c->c_arena);

    }
    else if (((exc)->n_nchildren) == 4) {
        asdl_seq *suite_seq;
        expr_ty expression;
        identifier e = new_identifier((((&(exc)->n_child[3]))->n_str), c);
        if (!e)
            return ((void *)0);
        if (forbidden_name(c, e, (&(exc)->n_child[3]), 0))
            return ((void *)0);
        expression = ast_for_expr(c, (&(exc)->n_child[1]));
        if (!expression)
            return ((void *)0);
        suite_seq = ast_for_suite(c, body);
        if (!suite_seq)
            return ((void *)0);

        return _Py_ExceptHandler(expression, e, suite_seq, ((exc)->n_lineno), exc->n_col_offset, c->c_arena);

    }

    PyErr_Format(PyExc_SystemError,
                 "wrong number of children for 'except' clause: %d",
                 ((exc)->n_nchildren));
    return ((void *)0);
}

static stmt_ty
ast_for_try_stmt(struct compiling *c, const node *n)
{
    const int nch = ((n)->n_nchildren);
    int n_except = (nch - 3)/3;
    asdl_seq *body, *handlers = ((void *)0), *orelse = ((void *)0), *finally = ((void *)0);

    (__builtin_expect(!(((n)->n_type) == (297)), 0) ? __assert_rtn(__func__, "ast.c", 3378, "TYPE(n) == (297)") : (void)0);

    body = ast_for_suite(c, (&(n)->n_child[2]));
    if (body == ((void *)0))
        return ((void *)0);

    if ((((&(n)->n_child[nch - 3]))->n_type) == 1) {
        if (strcmp((((&(n)->n_child[nch - 3]))->n_str), "finally") == 0) {
            if (nch >= 9 && (((&(n)->n_child[nch - 6]))->n_type) == 1) {



                orelse = ast_for_suite(c, (&(n)->n_child[nch - 4]));
                if (orelse == ((void *)0))
                    return ((void *)0);
                n_except--;
            }

            finally = ast_for_suite(c, (&(n)->n_child[nch - 1]));
            if (finally == ((void *)0))
                return ((void *)0);
            n_except--;
        }
        else {


            orelse = ast_for_suite(c, (&(n)->n_child[nch - 1]));
            if (orelse == ((void *)0))
                return ((void *)0);
            n_except--;
        }
    }
    else if ((((&(n)->n_child[nch - 3]))->n_type) != 300) {
        ast_error(c, n, "malformed 'try' statement");
        return ((void *)0);
    }

    if (n_except > 0) {
        int i;

        handlers = asdl_seq_new(n_except, c->c_arena);
        if (handlers == ((void *)0))
            return ((void *)0);

        for (i = 0; i < n_except; i++) {
            excepthandler_ty e = ast_for_except_clause(c, (&(n)->n_child[3 + i * 3]),
                                                       (&(n)->n_child[5 + i * 3]));
            if (!e)
                return ((void *)0);
            (handlers)->elements[i] = (e);
        }
    }

    (__builtin_expect(!(finally != ((void *)0) || ((handlers) == ((void *)0) ? 0 : (handlers)->size)), 0) ? __assert_rtn(__func__, "ast.c", 3431, "finally != NULL || asdl_seq_LEN(handlers)") : (void)0);
    return _Py_Try(body, handlers, orelse, finally, ((n)->n_lineno), n->n_col_offset, c->c_arena);
}


static withitem_ty
ast_for_with_item(struct compiling *c, const node *n)
{
    expr_ty context_expr, optional_vars = ((void *)0);

    (__builtin_expect(!(((n)->n_type) == (299)), 0) ? __assert_rtn(__func__, "ast.c", 3441, "TYPE(n) == (299)") : (void)0);
    context_expr = ast_for_expr(c, (&(n)->n_child[0]));
    if (!context_expr)
        return ((void *)0);
    if (((n)->n_nchildren) == 3) {
        optional_vars = ast_for_expr(c, (&(n)->n_child[2]));

        if (!optional_vars) {
            return ((void *)0);
        }
        if (!set_context(c, optional_vars, Store, n)) {
            return ((void *)0);
        }
    }

    return _Py_withitem(context_expr, optional_vars, c->c_arena);
}


static stmt_ty
ast_for_with_stmt(struct compiling *c, const node *n)
{
    int i, n_items;
    asdl_seq *items, *body;

    (__builtin_expect(!(((n)->n_type) == (298)), 0) ? __assert_rtn(__func__, "ast.c", 3466, "TYPE(n) == (298)") : (void)0);

    n_items = (((n)->n_nchildren) - 2) / 2;
    items = asdl_seq_new(n_items, c->c_arena);
    if (!items)
        return ((void *)0);
    for (i = 1; i < ((n)->n_nchildren) - 2; i += 2) {
        withitem_ty item = ast_for_with_item(c, (&(n)->n_child[i]));
        if (!item)
            return ((void *)0);
        (items)->elements[(i - 1) / 2] = (item);
    }

    body = ast_for_suite(c, (&(n)->n_child[((n)->n_nchildren) - 1]));
    if (!body)
        return ((void *)0);

    return _Py_With(items, body, ((n)->n_lineno), n->n_col_offset, c->c_arena);
}

static stmt_ty
ast_for_classdef(struct compiling *c, const node *n, asdl_seq *decorator_seq)
{

    PyObject *classname;
    asdl_seq *s;
    expr_ty call;

    (__builtin_expect(!(((n)->n_type) == (329)), 0) ? __assert_rtn(__func__, "ast.c", 3494, "TYPE(n) == (329)") : (void)0);

    if (((n)->n_nchildren) == 4) {
        s = ast_for_suite(c, (&(n)->n_child[3]));
        if (!s)
            return ((void *)0);
        classname = new_identifier((((&(n)->n_child[1]))->n_str), c);
        if (!classname)
            return ((void *)0);
        if (forbidden_name(c, classname, (&(n)->n_child[3]), 0))
            return ((void *)0);
        return _Py_ClassDef(classname, ((void *)0), ((void *)0), ((void *)0), ((void *)0), s, decorator_seq, ((n)->n_lineno), n->n_col_offset, c->c_arena);

    }

    if ((((&(n)->n_child[3]))->n_type) == 8) {
        s = ast_for_suite(c, (&(n)->n_child[5]));
        if (!s)
            return ((void *)0);
        classname = new_identifier((((&(n)->n_child[1]))->n_str), c);
        if (!classname)
            return ((void *)0);
        if (forbidden_name(c, classname, (&(n)->n_child[3]), 0))
            return ((void *)0);
        return _Py_ClassDef(classname, ((void *)0), ((void *)0), ((void *)0), ((void *)0), s, decorator_seq, ((n)->n_lineno), n->n_col_offset, c->c_arena);

    }



    {
        PyObject *dummy_name;
        expr_ty dummy;
        dummy_name = new_identifier((((&(n)->n_child[1]))->n_str), c);
        if (!dummy_name)
            return ((void *)0);
        dummy = _Py_Name(dummy_name, Load, ((n)->n_lineno), n->n_col_offset, c->c_arena);
        call = ast_for_call(c, (&(n)->n_child[3]), dummy);
        if (!call)
            return ((void *)0);
    }
    s = ast_for_suite(c, (&(n)->n_child[6]));
    if (!s)
        return ((void *)0);
    classname = new_identifier((((&(n)->n_child[1]))->n_str), c);
    if (!classname)
        return ((void *)0);
    if (forbidden_name(c, classname, (&(n)->n_child[1]), 0))
        return ((void *)0);

    return _Py_ClassDef(classname, call->v.Call.args, call->v.Call.keywords, call->v.Call.starargs, call->v.Call.kwargs, s, decorator_seq, ((n)->n_lineno), n->n_col_offset, c->c_arena);


}

static stmt_ty
ast_for_stmt(struct compiling *c, const node *n)
{
    if (((n)->n_type) == 268) {
        (__builtin_expect(!(((n)->n_nchildren) == 1), 0) ? __assert_rtn(__func__, "ast.c", 3553, "NCH(n) == 1") : (void)0);
        n = (&(n)->n_child[0]);
    }
    if (((n)->n_type) == 269) {
        (__builtin_expect(!(num_stmts(n) == 1), 0) ? __assert_rtn(__func__, "ast.c", 3557, "num_stmts(n) == 1") : (void)0);
        n = (&(n)->n_child[0]);
    }
    if (((n)->n_type) == 270) {
        n = (&(n)->n_child[0]);



        switch (((n)->n_type)) {
            case 271:
                return ast_for_expr_stmt(c, n);
            case 274:
                return ast_for_del_stmt(c, n);
            case 275:
                return _Py_Pass(((n)->n_lineno), n->n_col_offset, c->c_arena);
            case 276:
                return ast_for_flow_stmt(c, n);
            case 282:
                return ast_for_import_stmt(c, n);
            case 290:
                return ast_for_global_stmt(c, n);
            case 291:
                return ast_for_nonlocal_stmt(c, n);
            case 292:
                return ast_for_assert_stmt(c, n);
            default:
                PyErr_Format(PyExc_SystemError,
                             "unhandled small_stmt: TYPE=%d NCH=%d\n",
                             ((n)->n_type), ((n)->n_nchildren));
                return ((void *)0);
        }
    }
    else {



        node *ch = (&(n)->n_child[0]);
        (__builtin_expect(!(((n)->n_type) == (293)), 0) ? __assert_rtn(__func__, "ast.c", 3594, "TYPE(n) == (293)") : (void)0);
        switch (((ch)->n_type)) {
            case 294:
                return ast_for_if_stmt(c, ch);
            case 295:
                return ast_for_while_stmt(c, ch);
            case 296:
                return ast_for_for_stmt(c, ch);
            case 297:
                return ast_for_try_stmt(c, ch);
            case 298:
                return ast_for_with_stmt(c, ch);
            case 262:
                return ast_for_funcdef(c, ch, ((void *)0));
            case 329:
                return ast_for_classdef(c, ch, ((void *)0));
            case 261:
                return ast_for_decorated(c, ch);
            default:
                PyErr_Format(PyExc_SystemError,
                             "unhandled small_stmt: TYPE=%d NCH=%d\n",
                             ((n)->n_type), ((n)->n_nchildren));
                return ((void *)0);
        }
    }
}

static PyObject *
parsenumber(struct compiling *c, const char *s)
{
    const char *end;
    long x;
    double dx;
    Py_complex compl;
    int imflag;

    (__builtin_expect(!(s != ((void *)0)), 0) ? __assert_rtn(__func__, "ast.c", 3630, "s != NULL") : (void)0);
    (*__error()) = 0;
    end = s + strlen(s) - 1;
    imflag = *end == 'j' || *end == 'J';
    if (s[0] == '0') {
        x = (long) PyOS_strtoul((char *)s, (char **)&end, 0);
        if (x < 0 && (*__error()) == 0) {
            return PyLong_FromString((char *)s,
                                     (char **)0,
                                     0);
        }
    }
    else
        x = PyOS_strtol((char *)s, (char **)&end, 0);
    if (*end == '\0') {
        if ((*__error()) != 0)
            return PyLong_FromString((char *)s, (char **)0, 0);
        return PyLong_FromLong(x);
    }

    if (imflag) {
        compl.real = 0.;
        compl.imag = PyOS_string_to_double(s, (char **)&end, ((void *)0));
        if (compl.imag == -1.0 && PyErr_Occurred())
            return ((void *)0);
        return PyComplex_FromCComplex(compl);
    }
    else
    {
        dx = PyOS_string_to_double(s, ((void *)0), ((void *)0));
        if (dx == -1.0 && PyErr_Occurred())
            return ((void *)0);
        return PyFloat_FromDouble(dx);
    }
}

static PyObject *
decode_utf8(struct compiling *c, const char **sPtr, const char *end)
{
    char *s, *t;
    t = s = (char *)*sPtr;

    while (s < end && (*s & 0x80)) s++;
    *sPtr = s;
    return PyUnicode_DecodeUTF8(t, s - t, ((void *)0));
}

static PyObject *
decode_unicode(struct compiling *c, const char *s, size_t len, int rawmode, const char *encoding)
{
    PyObject *v, *u;
    char *buf;
    char *p;
    const char *end;

    if (encoding == ((void *)0)) {
        u = ((void *)0);
    } else {

        if (len > 18446744073709551615ULL / 6)
            return ((void *)0);


        u = PyBytes_FromStringAndSize((char *)((void *)0), len * 6);
        if (u == ((void *)0))
            return ((void *)0);
        p = buf = PyBytes_AsString(u);
        end = s + len;
        while (s < end) {
            if (*s == '\\') {
                *p++ = *s++;
                if (*s & 0x80) {
                    ((__builtin_object_size (p, 0) != (size_t) -1) ? __builtin___strcpy_chk (p, "u005c", __builtin_object_size (p, 2 > 1)) : __inline_strcpy_chk (p, "u005c"));
                    p += 5;
                }
            }
            if (*s & 0x80) {
                PyObject *w;
                int kind;
                void *data;
                Py_ssize_t len, i;
                w = decode_utf8(c, &s, end);
                if (w == ((void *)0)) {
                    do { if ( --((PyObject*)(u))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(u)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(u)))); } while (0);
                    return ((void *)0);
                }
                kind = ((__builtin_expect(!(((((((PyObject*)(w))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "ast.c", 3716, "PyUnicode_Check(w)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)w)->state.ready)), 0) ? __assert_rtn(__func__, "ast.c", 3716, "PyUnicode_IS_READY(w)") : (void)0), ((PyASCIIObject *)(w))->state.kind);
                data = ((__builtin_expect(!(((((((PyObject*)(w))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "ast.c", 3717, "PyUnicode_Check(w)") : (void)0), (((PyASCIIObject*)(w))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)(w))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "ast.c", 3717, "PyUnicode_Check(w)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)w)->state.ready)), 0) ? __assert_rtn(__func__, "ast.c", 3717, "PyUnicode_IS_READY(w)") : (void)0), ((PyASCIIObject*)w)->state.ascii) ? ((void*)((PyASCIIObject*)(w) + 1)) : ((void*)((PyCompactUnicodeObject*)(w) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)(w))->data.any), 0) ? __assert_rtn(__func__, "ast.c", 3717, "((PyUnicodeObject*)(w))->data.any") : (void)0), ((((PyUnicodeObject *)(w))->data.any))));
                len = ((__builtin_expect(!(((((((PyObject*)(w))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "ast.c", 3718, "PyUnicode_Check(w)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)w)->state.ready)), 0) ? __assert_rtn(__func__, "ast.c", 3718, "PyUnicode_IS_READY(w)") : (void)0), ((PyASCIIObject *)(w))->length);
                for (i = 0; i < len; i++) {
                    Py_UCS4 chr = ((Py_UCS4) ((kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(data))[(i)] : ((kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(data))[(i)] : ((const Py_UCS4 *)(data))[(i)] ) ));
                    __builtin___sprintf_chk (p, 0, __builtin_object_size (p, 2 > 1), "\\U%08x", chr);
                    p += 10;
                }

                (__builtin_expect(!(p - buf <= (((PyVarObject*)(u))->ob_size)), 0) ? __assert_rtn(__func__, "ast.c", 3725, "p - buf <= Py_SIZE(u)") : (void)0);
                do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
            } else {
                *p++ = *s++;
            }
        }
        len = p - buf;
        s = buf;
    }
    if (rawmode)
        v = PyUnicode_DecodeRawUnicodeEscape(s, len, ((void *)0));
    else
        v = PyUnicode_DecodeUnicodeEscape(s, len, ((void *)0));
    do { if ((u) == ((void *)0)) ; else do { if ( --((PyObject*)(u))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(u)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(u)))); } while (0); } while (0);
    return v;
}





static PyObject *
parsestr(struct compiling *c, const node *n, int *bytesmode)
{
    size_t len;
    const char *s = ((n)->n_str);
    int quote = ((unsigned char)((*s) & 0xff));
    int rawmode = 0;
    int need_encoding;
    if ((_Py_ctype_table[((unsigned char)((quote) & 0xff))] & (0x01|0x02))) {
        while (!*bytesmode || !rawmode) {
            if (quote == 'b' || quote == 'B') {
                quote = *++s;
                *bytesmode = 1;
            }
            else if (quote == 'u' || quote == 'U') {
                quote = *++s;
            }
            else if (quote == 'r' || quote == 'R') {
                quote = *++s;
                rawmode = 1;
            }
            else {
                break;
            }
        }
    }
    if (quote != '\'' && quote != '\"') {
        _PyErr_BadInternalCall("ast.c", 3773);
        return ((void *)0);
    }
    s++;
    len = strlen(s);
    if (len > 2147483647) {
        PyErr_SetString(PyExc_OverflowError,
                        "string to parse is too long");
        return ((void *)0);
    }
    if (s[--len] != quote) {
        _PyErr_BadInternalCall("ast.c", 3784);
        return ((void *)0);
    }
    if (len >= 4 && s[0] == quote && s[1] == quote) {
        s += 2;
        len -= 2;
        if (s[--len] != quote || s[--len] != quote) {
            _PyErr_BadInternalCall("ast.c", 3791);
            return ((void *)0);
        }
    }
    if (!*bytesmode && !rawmode) {
        return decode_unicode(c, s, len, rawmode, c->c_encoding);
    }
    if (*bytesmode) {

        const char *ch;
        for (ch = s; *ch; ch++) {
            if (((unsigned char)((*ch) & 0xff)) >= 0x80) {
                ast_error(c, n, "bytes can only contain ASCII "
                          "literal characters.");
                return ((void *)0);
            }
        }
    }
    need_encoding = (!*bytesmode && c->c_encoding != ((void *)0) &&
                     strcmp(c->c_encoding, "utf-8") != 0);
    if (rawmode || strchr(s, '\\') == ((void *)0)) {
        if (need_encoding) {
            PyObject *v, *u = PyUnicode_DecodeUTF8(s, len, ((void *)0));
            if (u == ((void *)0) || !*bytesmode)
                return u;
            v = PyUnicode_AsEncodedString(u, c->c_encoding, ((void *)0));
            do { if ( --((PyObject*)(u))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(u)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(u)))); } while (0);
            return v;
        } else if (*bytesmode) {
            return PyBytes_FromStringAndSize(s, len);
        } else if (strcmp(c->c_encoding, "utf-8") == 0) {
            return PyUnicode_FromStringAndSize(s, len);
        } else {
            return PyUnicode_DecodeLatin1(s, len, ((void *)0));
        }
    }
    return PyBytes_DecodeEscape(s, len, ((void *)0), 1,
                                 need_encoding ? c->c_encoding : ((void *)0));
}





static PyObject *
parsestrplus(struct compiling *c, const node *n, int *bytesmode)
{
    PyObject *v;
    int i;
    (__builtin_expect(!((((&(n)->n_child[0]))->n_type) == (3)), 0) ? __assert_rtn(__func__, "ast.c", 3840, "TYPE((&(n)->n_child[0])) == (3)") : (void)0);
    v = parsestr(c, (&(n)->n_child[0]), bytesmode);
    if (v != ((void *)0)) {

        for (i = 1; i < ((n)->n_nchildren); i++) {
            PyObject *s;
            int subbm = 0;
            s = parsestr(c, (&(n)->n_child[i]), &subbm);
            if (s == ((void *)0))
                goto onError;
            if (*bytesmode != subbm) {
                ast_error(c, n, "cannot mix bytes and nonbytes literals");
                do { if ( --((PyObject*)(s))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(s)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(s)))); } while (0);
                goto onError;
            }
            if (((((((PyObject*)(v))->ob_type))->tp_flags & ((1L<<27))) != 0) && ((((((PyObject*)(s))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
                PyBytes_ConcatAndDel(&v, s);
                if (v == ((void *)0))
                    goto onError;
            }
            else {
                PyObject *temp = PyUnicode_Concat(v, s);
                do { if ( --((PyObject*)(s))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(s)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(s)))); } while (0);
                do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
                v = temp;
                if (v == ((void *)0))
                    goto onError;
            }
        }
    }
    return v;

  onError:
    do { if ((v) == ((void *)0)) ; else do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0); } while (0);
    return ((void *)0);
}
