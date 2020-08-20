# 1 "typeobject.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "typeobject.c"


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
# 4 "typeobject.c" 2
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
# 5 "typeobject.c" 2
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
# 6 "typeobject.c" 2
# 29 "typeobject.c"
struct method_cache_entry {
    unsigned int version;
    PyObject *name;
    PyObject *value;
};

static struct method_cache_entry method_cache[1 << 9];
static unsigned int next_version_tag = 0;

static _Py_Identifier PyId___class__ = { 0, "__class__", 0 };
static _Py_Identifier PyId___dict__ = { 0, "__dict__", 0 };
static _Py_Identifier PyId___doc__ = { 0, "__doc__", 0 };
static _Py_Identifier PyId___getitem__ = { 0, "__getitem__", 0 };
static _Py_Identifier PyId___getattribute__ = { 0, "__getattribute__", 0 };
static _Py_Identifier PyId___hash__ = { 0, "__hash__", 0 };
static _Py_Identifier PyId___module__ = { 0, "__module__", 0 };
static _Py_Identifier PyId___name__ = { 0, "__name__", 0 };
static _Py_Identifier PyId___new__ = { 0, "__new__", 0 };

static PyObject *
_PyType_LookupId(PyTypeObject *type, struct _Py_Identifier *name);

static PyObject *
slot_tp_new(PyTypeObject *type, PyObject *args, PyObject *kwds);

unsigned int
PyType_ClearCache(void)
{
    Py_ssize_t i;
    unsigned int cur_version_tag = next_version_tag - 1;

    for (i = 0; i < (1 << 9); i++) {
        method_cache[i].version = 0;
        do { if (method_cache[i].name) { PyObject *_py_tmp = (PyObject *)(method_cache[i].name); (method_cache[i].name) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
        method_cache[i].value = ((void *)0);
    }
    next_version_tag = 0;

    PyType_Modified(&PyBaseObject_Type);
    return cur_version_tag;
}

void
PyType_Modified(PyTypeObject *type)
{
# 93 "typeobject.c"
    PyObject *raw, *ref;
    Py_ssize_t i, n;

    if (!(((type)->tp_flags & ((1L<<19))) != 0))
        return;

    raw = type->tp_subclasses;
    if (raw != ((void *)0)) {
        n = (((PyVarObject*)(raw))->ob_size);
        for (i = 0; i < n; i++) {
            ref = (((PyListObject *)(raw))->ob_item[i]);
            ref = ((((PyObject*)(((PyWeakReference *)(ref))->wr_object))->ob_refcnt) > 0 ? ((PyWeakReference *)(ref))->wr_object : (&_Py_NoneStruct));
            if (ref != (&_Py_NoneStruct)) {
                PyType_Modified((PyTypeObject *)ref);
            }
        }
    }
    type->tp_flags &= ~(1L<<19);
}

static void
type_mro_modified(PyTypeObject *type, PyObject *bases) {
# 127 "typeobject.c"
    Py_ssize_t i, n;
    int clear = 0;

    if (!(((type)->tp_flags & ((1L<<18))) != 0))
        return;

    n = (((PyVarObject*)(bases))->ob_size);
    for (i = 0; i < n; i++) {
        PyObject *b = (((PyTupleObject *)(bases))->ob_item[i]);
        PyTypeObject *cls;

        (__builtin_expect(!(((((((PyObject*)(b))->ob_type))->tp_flags & ((1L<<31))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 138, "PyType_Check(b)") : (void)0);
        cls = (PyTypeObject *)b;

        if (!(((cls)->tp_flags & ((1L<<18))) != 0) ||
            !PyType_IsSubtype(type, cls)) {
            clear = 1;
            break;
        }
    }

    if (clear)
        type->tp_flags &= ~((1L<<18)|
                            (1L<<19));
}

static int
assign_version_tag(PyTypeObject *type)
{





    Py_ssize_t i, n;
    PyObject *bases;

    if ((((type)->tp_flags & ((1L<<19))) != 0))
        return 1;
    if (!(((type)->tp_flags & ((1L<<18))) != 0))
        return 0;
    if (!(((type)->tp_flags & ((1L<<12))) != 0))
        return 0;

    type->tp_version_tag = next_version_tag++;


    if (type->tp_version_tag == 0) {




        for (i = 0; i < (1 << 9); i++) {
            method_cache[i].value = ((void *)0);
            do { if ((method_cache[i].name) == ((void *)0)) ; else do { if ( --((PyObject*)(method_cache[i].name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(method_cache[i].name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(method_cache[i].name)))); } while (0); } while (0);
            method_cache[i].name = (&_Py_NoneStruct);
            ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        }

        PyType_Modified(&PyBaseObject_Type);
        return 1;
    }
    bases = type->tp_bases;
    n = (((PyVarObject*)(bases))->ob_size);
    for (i = 0; i < n; i++) {
        PyObject *b = (((PyTupleObject *)(bases))->ob_item[i]);
        (__builtin_expect(!(((((((PyObject*)(b))->ob_type))->tp_flags & ((1L<<31))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 193, "PyType_Check(b)") : (void)0);
        if (!assign_version_tag((PyTypeObject *)b))
            return 0;
    }
    type->tp_flags |= (1L<<19);
    return 1;
}


static PyMemberDef type_members[] = {
    {"__basicsize__", 19, __builtin_offsetof (PyTypeObject, tp_basicsize),1},
    {"__itemsize__", 19, __builtin_offsetof (PyTypeObject, tp_itemsize), 1},
    {"__flags__", 2, __builtin_offsetof (PyTypeObject, tp_flags), 1},
    {"__weakrefoffset__", 2,
     __builtin_offsetof (PyTypeObject, tp_weaklistoffset), 1},
    {"__base__", 6, __builtin_offsetof (PyTypeObject, tp_base), 1},
    {"__dictoffset__", 2,
     __builtin_offsetof (PyTypeObject, tp_dictoffset), 1},
    {"__mro__", 6, __builtin_offsetof (PyTypeObject, tp_mro), 1},
    {0}
};

static int
check_set_special_type_attr(PyTypeObject *type, PyObject *value, const char *name)
{
    if (!(type->tp_flags & (1L<<9))) {
        PyErr_Format(PyExc_TypeError,
                     "can't set %s.%s", type->tp_name, name);
        return 0;
    }
    if (!value) {
        PyErr_Format(PyExc_TypeError,
                     "can't delete %s.%s", type->tp_name, name);
        return 0;
    }
    return 1;
}

static PyObject *
type_name(PyTypeObject *type, void *context)
{
    const char *s;

    if (type->tp_flags & (1L<<9)) {
        PyHeapTypeObject* et = (PyHeapTypeObject*)type;

        ( ((PyObject*)(et->ht_name))->ob_refcnt++);
        return et->ht_name;
    }
    else {
        s = strrchr(type->tp_name, '.');
        if (s == ((void *)0))
            s = type->tp_name;
        else
            s++;
        return PyUnicode_FromString(s);
    }
}

static PyObject *
type_qualname(PyTypeObject *type, void *context)
{
    if (type->tp_flags & (1L<<9)) {
        PyHeapTypeObject* et = (PyHeapTypeObject*)type;
        ( ((PyObject*)(et->ht_qualname))->ob_refcnt++);
        return et->ht_qualname;
    }
    else {
        return type_name(type, context);
    }
}

static int
type_set_name(PyTypeObject *type, PyObject *value, void *context)
{
    PyHeapTypeObject* et;
    char *tp_name;
    PyObject *tmp;

    if (!check_set_special_type_attr(type, value, "__name__"))
        return -1;
    if (!((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        PyErr_Format(PyExc_TypeError,
                     "can only assign string to %s.__name__, not '%s'",
                     type->tp_name, (((PyObject*)(value))->ob_type)->tp_name);
        return -1;
    }


    tmp = PyUnicode_FromStringAndSize("\0", 1);
    if (tmp == ((void *)0))
        return -1;
    if (PyUnicode_Contains(value, tmp) != 0) {
        do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0);
        PyErr_Format(PyExc_ValueError,
                     "__name__ must not contain null bytes");
        return -1;
    }
    do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0);

    tp_name = PyUnicode_AsUTF8(value);
    if (tp_name == ((void *)0))
        return -1;

    et = (PyHeapTypeObject*)type;

    ( ((PyObject*)(value))->ob_refcnt++);

    do { if ( --((PyObject*)(et->ht_name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(et->ht_name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(et->ht_name)))); } while (0);
    et->ht_name = value;

    type->tp_name = tp_name;

    return 0;
}

static int
type_set_qualname(PyTypeObject *type, PyObject *value, void *context)
{
    PyHeapTypeObject* et;

    if (!check_set_special_type_attr(type, value, "__qualname__"))
        return -1;
    if (!((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        PyErr_Format(PyExc_TypeError,
                     "can only assign string to %s.__qualname__, not '%s'",
                     type->tp_name, (((PyObject*)(value))->ob_type)->tp_name);
        return -1;
    }

    et = (PyHeapTypeObject*)type;
    ( ((PyObject*)(value))->ob_refcnt++);
    do { if ( --((PyObject*)(et->ht_qualname))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(et->ht_qualname)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(et->ht_qualname)))); } while (0);
    et->ht_qualname = value;
    return 0;
}

static PyObject *
type_module(PyTypeObject *type, void *context)
{
    PyObject *mod;
    char *s;

    if (type->tp_flags & (1L<<9)) {
        mod = _PyDict_GetItemId(type->tp_dict, &PyId___module__);
        if (!mod) {
            PyErr_Format(PyExc_AttributeError, "__module__");
            return 0;
        }
        do { if ((mod) == ((void *)0)) ; else ( ((PyObject*)(mod))->ob_refcnt++); } while (0);
        return mod;
    }
    else {
        s = strrchr(type->tp_name, '.');
        if (s != ((void *)0))
            return PyUnicode_FromStringAndSize(
                type->tp_name, (Py_ssize_t)(s - type->tp_name));
        return PyUnicode_FromString("builtins");
    }
}

static int
type_set_module(PyTypeObject *type, PyObject *value, void *context)
{
    if (!check_set_special_type_attr(type, value, "__module__"))
        return -1;

    PyType_Modified(type);

    return _PyDict_SetItemId(type->tp_dict, &PyId___module__, value);
}

static PyObject *
type_abstractmethods(PyTypeObject *type, void *context)
{
    PyObject *mod = ((void *)0);


    if (type != &PyType_Type)
        mod = PyDict_GetItemString(type->tp_dict, "__abstractmethods__");
    if (!mod) {
        PyErr_SetString(PyExc_AttributeError, "__abstractmethods__");
        return ((void *)0);
    }
    do { if ((mod) == ((void *)0)) ; else ( ((PyObject*)(mod))->ob_refcnt++); } while (0);
    return mod;
}

static int
type_set_abstractmethods(PyTypeObject *type, PyObject *value, void *context)
{




    int abstract, res;
    if (value != ((void *)0)) {
        abstract = PyObject_IsTrue(value);
        if (abstract < 0)
            return -1;
        res = PyDict_SetItemString(type->tp_dict, "__abstractmethods__", value);
    }
    else {
        abstract = 0;
        res = PyDict_DelItemString(type->tp_dict, "__abstractmethods__");
        if (res && PyErr_ExceptionMatches(PyExc_KeyError)) {
            PyErr_SetString(PyExc_AttributeError, "__abstractmethods__");
            return -1;
        }
    }
    if (res == 0) {
        PyType_Modified(type);
        if (abstract)
            type->tp_flags |= (1L<<20);
        else
            type->tp_flags &= ~(1L<<20);
    }
    return res;
}

static PyObject *
type_get_bases(PyTypeObject *type, void *context)
{
    ( ((PyObject*)(type->tp_bases))->ob_refcnt++);
    return type->tp_bases;
}

static PyTypeObject *best_base(PyObject *);
static int mro_internal(PyTypeObject *);
static int compatible_for_assignment(PyTypeObject *, PyTypeObject *, char *);
static int add_subclass(PyTypeObject*, PyTypeObject*);
static void remove_subclass(PyTypeObject *, PyTypeObject *);
static void update_all_slots(PyTypeObject *);

typedef int (*update_callback)(PyTypeObject *, void *);
static int update_subclasses(PyTypeObject *type, PyObject *name,
                             update_callback callback, void *data);
static int recurse_down_subclasses(PyTypeObject *type, PyObject *name,
                                   update_callback callback, void *data);

static int
mro_subclasses(PyTypeObject *type, PyObject* temp)
{
    PyTypeObject *subclass;
    PyObject *ref, *subclasses, *old_mro;
    Py_ssize_t i, n;

    subclasses = type->tp_subclasses;
    if (subclasses == ((void *)0))
        return 0;
    (__builtin_expect(!(((((((PyObject*)(subclasses))->ob_type))->tp_flags & ((1L<<25))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 443, "PyList_Check(subclasses)") : (void)0);
    n = (((PyVarObject*)(subclasses))->ob_size);
    for (i = 0; i < n; i++) {
        ref = (((PyListObject *)(subclasses))->ob_item[i]);
        (__builtin_expect(!(((((PyObject*)(ref))->ob_type) == (&_PyWeakref_RefType) || PyType_IsSubtype((((PyObject*)(ref))->ob_type), (&_PyWeakref_RefType)))), 0) ? __assert_rtn(__func__, "typeobject.c", 447, "PyWeakref_CheckRef(ref)") : (void)0);
        subclass = (PyTypeObject *)((((PyObject*)(((PyWeakReference *)(ref))->wr_object))->ob_refcnt) > 0 ? ((PyWeakReference *)(ref))->wr_object : (&_Py_NoneStruct));
        (__builtin_expect(!(subclass != ((void *)0)), 0) ? __assert_rtn(__func__, "typeobject.c", 449, "subclass != NULL") : (void)0);
        if ((PyObject *)subclass == (&_Py_NoneStruct))
            continue;
        (__builtin_expect(!(((((((PyObject*)(subclass))->ob_type))->tp_flags & ((1L<<31))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 452, "PyType_Check(subclass)") : (void)0);
        old_mro = subclass->tp_mro;
        if (mro_internal(subclass) < 0) {
            subclass->tp_mro = old_mro;
            return -1;
        }
        else {
            PyObject* tuple;
            tuple = PyTuple_Pack(2, subclass, old_mro);
            do { if ( --((PyObject*)(old_mro))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(old_mro)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(old_mro)))); } while (0);
            if (!tuple)
                return -1;
            if (PyList_Append(temp, tuple) < 0)
                return -1;
            do { if ( --((PyObject*)(tuple))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tuple)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tuple)))); } while (0);
        }
        if (mro_subclasses(subclass, temp) < 0)
            return -1;
    }
    return 0;
}

static int
type_set_bases(PyTypeObject *type, PyObject *value, void *context)
{
    Py_ssize_t i;
    int r = 0;
    PyObject *ob, *temp;
    PyTypeObject *new_base, *old_base;
    PyObject *old_bases, *old_mro;

    if (!check_set_special_type_attr(type, value, "__bases__"))
        return -1;
    if (!((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
        PyErr_Format(PyExc_TypeError,
             "can only assign tuple to %s.__bases__, not %s",
                 type->tp_name, (((PyObject*)(value))->ob_type)->tp_name);
        return -1;
    }
    if ((((PyVarObject*)(value))->ob_size) == 0) {
        PyErr_Format(PyExc_TypeError,
             "can only assign non-empty tuple to %s.__bases__, not ()",
                 type->tp_name);
        return -1;
    }
    for (i = 0; i < (((PyVarObject*)(value))->ob_size); i++) {
        ob = (((PyTupleObject *)(value))->ob_item[i]);
        if (!((((((PyObject*)(ob))->ob_type))->tp_flags & ((1L<<31))) != 0)) {
            PyErr_Format(PyExc_TypeError,
                         "%s.__bases__ must be tuple of classes, not '%s'",
                         type->tp_name, (((PyObject*)(ob))->ob_type)->tp_name);
            return -1;
        }
        if (PyType_IsSubtype((PyTypeObject*)ob, type)) {
            PyErr_SetString(PyExc_TypeError,
                            "a __bases__ item causes an inheritance cycle");
            return -1;
        }
    }

    new_base = best_base(value);

    if (!new_base)
        return -1;

    if (!compatible_for_assignment(type->tp_base, new_base, "__bases__"))
        return -1;

    ( ((PyObject*)(new_base))->ob_refcnt++);
    ( ((PyObject*)(value))->ob_refcnt++);

    old_bases = type->tp_bases;
    old_base = type->tp_base;
    old_mro = type->tp_mro;

    type->tp_bases = value;
    type->tp_base = new_base;

    if (mro_internal(type) < 0) {
        goto bail;
    }

    temp = PyList_New(0);
    if (!temp)
        goto bail;

    r = mro_subclasses(type, temp);

    if (r < 0) {
        for (i = 0; i < PyList_Size(temp); i++) {
            PyTypeObject* cls;
            PyObject* mro;
            PyArg_UnpackTuple((((PyListObject *)(temp))->ob_item[i]),
                             "", 2, 2, &cls, &mro);
            ( ((PyObject*)(mro))->ob_refcnt++);
            ob = cls->tp_mro;
            cls->tp_mro = mro;
            do { if ( --((PyObject*)(ob))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(ob)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(ob)))); } while (0);
        }
        do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0);
        goto bail;
    }

    do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0);
# 565 "typeobject.c"
    for (i = (((PyVarObject*)(old_bases))->ob_size) - 1; i >= 0; i--) {
        ob = (((PyTupleObject *)(old_bases))->ob_item[i]);
        if (((((((PyObject*)(ob))->ob_type))->tp_flags & ((1L<<31))) != 0)) {
            remove_subclass(
                (PyTypeObject*)ob, type);
        }
    }

    for (i = (((PyVarObject*)(value))->ob_size) - 1; i >= 0; i--) {
        ob = (((PyTupleObject *)(value))->ob_item[i]);
        if (((((((PyObject*)(ob))->ob_type))->tp_flags & ((1L<<31))) != 0)) {
            if (add_subclass((PyTypeObject*)ob, type) < 0)
                r = -1;
        }
    }

    update_all_slots(type);

    do { if ( --((PyObject*)(old_bases))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(old_bases)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(old_bases)))); } while (0);
    do { if ( --((PyObject*)(old_base))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(old_base)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(old_base)))); } while (0);
    do { if ( --((PyObject*)(old_mro))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(old_mro)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(old_mro)))); } while (0);

    return r;

  bail:
    do { if ( --((PyObject*)(type->tp_bases))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type->tp_bases)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type->tp_bases)))); } while (0);
    do { if ( --((PyObject*)(type->tp_base))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type->tp_base)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type->tp_base)))); } while (0);
    if (type->tp_mro != old_mro) {
        do { if ( --((PyObject*)(type->tp_mro))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type->tp_mro)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type->tp_mro)))); } while (0);
    }

    type->tp_bases = old_bases;
    type->tp_base = old_base;
    type->tp_mro = old_mro;

    return -1;
}

static PyObject *
type_dict(PyTypeObject *type, void *context)
{
    if (type->tp_dict == ((void *)0)) {
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        return (&_Py_NoneStruct);
    }
    return PyDictProxy_New(type->tp_dict);
}

static PyObject *
type_get_doc(PyTypeObject *type, void *context)
{
    PyObject *result;
    if (!(type->tp_flags & (1L<<9)) && type->tp_doc != ((void *)0))
        return PyUnicode_FromString(type->tp_doc);
    result = _PyDict_GetItemId(type->tp_dict, &PyId___doc__);
    if (result == ((void *)0)) {
        result = (&_Py_NoneStruct);
        ( ((PyObject*)(result))->ob_refcnt++);
    }
    else if ((((PyObject*)(result))->ob_type)->tp_descr_get) {
        result = (((PyObject*)(result))->ob_type)->tp_descr_get(result, ((void *)0),
                                               (PyObject *)type);
    }
    else {
        ( ((PyObject*)(result))->ob_refcnt++);
    }
    return result;
}

static int
type_set_doc(PyTypeObject *type, PyObject *value, void *context)
{
    if (!check_set_special_type_attr(type, value, "__doc__"))
        return -1;
    PyType_Modified(type);
    return _PyDict_SetItemId(type->tp_dict, &PyId___doc__, value);
}

static PyObject *
type___instancecheck__(PyObject *type, PyObject *inst)
{
    switch (_PyObject_RealIsInstance(inst, type)) {
    case -1:
        return ((void *)0);
    case 0:
        return ( ((PyObject*)(((PyObject *) &_Py_FalseStruct)))->ob_refcnt++), ((PyObject *) &_Py_FalseStruct);
    default:
        return ( ((PyObject*)(((PyObject *) &_Py_TrueStruct)))->ob_refcnt++), ((PyObject *) &_Py_TrueStruct);
    }
}


static PyObject *
type___subclasscheck__(PyObject *type, PyObject *inst)
{
    switch (_PyObject_RealIsSubclass(inst, type)) {
    case -1:
        return ((void *)0);
    case 0:
        return ( ((PyObject*)(((PyObject *) &_Py_FalseStruct)))->ob_refcnt++), ((PyObject *) &_Py_FalseStruct);
    default:
        return ( ((PyObject*)(((PyObject *) &_Py_TrueStruct)))->ob_refcnt++), ((PyObject *) &_Py_TrueStruct);
    }
}


static PyGetSetDef type_getsets[] = {
    {"__name__", (getter)type_name, (setter)type_set_name, ((void *)0)},
    {"__qualname__", (getter)type_qualname, (setter)type_set_qualname, ((void *)0)},
    {"__bases__", (getter)type_get_bases, (setter)type_set_bases, ((void *)0)},
    {"__module__", (getter)type_module, (setter)type_set_module, ((void *)0)},
    {"__abstractmethods__", (getter)type_abstractmethods,
     (setter)type_set_abstractmethods, ((void *)0)},
    {"__dict__", (getter)type_dict, ((void *)0), ((void *)0)},
    {"__doc__", (getter)type_get_doc, (setter)type_set_doc, ((void *)0)},
    {0}
};

static PyObject *
type_repr(PyTypeObject *type)
{
    PyObject *mod, *name, *rtn;

    mod = type_module(type, ((void *)0));
    if (mod == ((void *)0))
        PyErr_Clear();
    else if (!((((((PyObject*)(mod))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        do { if ( --((PyObject*)(mod))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(mod)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(mod)))); } while (0);
        mod = ((void *)0);
    }
    name = type_qualname(type, ((void *)0));
    if (name == ((void *)0)) {
        do { if ((mod) == ((void *)0)) ; else do { if ( --((PyObject*)(mod))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(mod)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(mod)))); } while (0); } while (0);
        return ((void *)0);
    }

    if (mod != ((void *)0) && PyUnicode_CompareWithASCIIString(mod, "builtins"))
        rtn = PyUnicode_FromFormat("<class '%U.%U'>", mod, name);
    else
        rtn = PyUnicode_FromFormat("<class '%s'>", type->tp_name);

    do { if ((mod) == ((void *)0)) ; else do { if ( --((PyObject*)(mod))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(mod)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(mod)))); } while (0); } while (0);
    do { if ( --((PyObject*)(name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(name)))); } while (0);
    return rtn;
}

static PyObject *
type_call(PyTypeObject *type, PyObject *args, PyObject *kwds)
{
    PyObject *obj;

    if (type->tp_new == ((void *)0)) {
        PyErr_Format(PyExc_TypeError,
                     "cannot create '%.100s' instances",
                     type->tp_name);
        return ((void *)0);
    }

    obj = type->tp_new(type, args, kwds);
    if (obj != ((void *)0)) {


        if (type == &PyType_Type &&
            ((((((PyObject*)(args))->ob_type))->tp_flags & ((1L<<26))) != 0) && (((PyVarObject*)(args))->ob_size) == 1 &&
            (kwds == ((void *)0) ||
             (((((((PyObject*)(kwds))->ob_type))->tp_flags & ((1L<<29))) != 0) && PyDict_Size(kwds) == 0)))
            return obj;


        if (!PyType_IsSubtype((((PyObject*)(obj))->ob_type), type))
            return obj;
        type = (((PyObject*)(obj))->ob_type);
        if (type->tp_init != ((void *)0) &&
            type->tp_init(obj, args, kwds) < 0) {
            do { if ( --((PyObject*)(obj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(obj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(obj)))); } while (0);
            obj = ((void *)0);
        }
    }
    return obj;
}

PyObject *
PyType_GenericAlloc(PyTypeObject *type, Py_ssize_t nitems)
{
    PyObject *obj;
    const size_t size = (((size_t)((type)->tp_basicsize + (nitems+1)*(type)->tp_itemsize) + (size_t)((8) - 1)) & ~(size_t)((8) - 1));


    if (((((type))->tp_flags & ((1L<<14))) != 0))
        obj = _PyObject_GC_Malloc(size);
    else
        obj = (PyObject *)PyObject_Malloc(size);

    if (obj == ((void *)0))
        return PyErr_NoMemory();

    ((__builtin_object_size (obj, 0) != (size_t) -1) ? __builtin___memset_chk (obj, '\0', size, __builtin_object_size (obj, 0)) : __inline_memset_chk (obj, '\0', size));

    if (type->tp_flags & (1L<<9))
        ( ((PyObject*)(type))->ob_refcnt++);

    if (type->tp_itemsize == 0)
        ( (((PyObject*)(obj))->ob_type) = (type), ( (((PyObject*)((PyObject *)(obj)))->ob_refcnt) = 1), (obj) );
    else
        (void) ( (((PyVarObject*)((PyVarObject *)obj))->ob_size) = (nitems), ( (((PyObject*)(((PyVarObject *)obj)))->ob_type) = ((type)), ( (((PyObject*)((PyObject *)(((PyVarObject *)obj))))->ob_refcnt) = 1), (((PyVarObject *)obj)) ) );

    if (((((type))->tp_flags & ((1L<<14))) != 0))
        do { PyGC_Head *g = ((PyGC_Head *)(obj)-1); if (g->gc.gc_refs != (-2)) Py_FatalError("GC object already tracked"); g->gc.gc_refs = (-3); g->gc.gc_next = _PyGC_generation0; g->gc.gc_prev = _PyGC_generation0->gc.gc_prev; g->gc.gc_prev->gc.gc_next = g; _PyGC_generation0->gc.gc_prev = g; } while (0);;
    return obj;
}

PyObject *
PyType_GenericNew(PyTypeObject *type, PyObject *args, PyObject *kwds)
{
    return type->tp_alloc(type, 0);
}



static int
traverse_slots(PyTypeObject *type, PyObject *self, visitproc visit, void *arg)
{
    Py_ssize_t i, n;
    PyMemberDef *mp;

    n = (((PyVarObject*)(type))->ob_size);
    mp = ((PyMemberDef *)(((char *)(PyHeapTypeObject *)type) + (((PyObject*)((PyHeapTypeObject *)type))->ob_type)->tp_basicsize));
    for (i = 0; i < n; i++, mp++) {
        if (mp->type == 16) {
            char *addr = (char *)self + mp->offset;
            PyObject *obj = *(PyObject **)addr;
            if (obj != ((void *)0)) {
                int err = visit(obj, arg);
                if (err)
                    return err;
            }
        }
    }
    return 0;
}

static int
subtype_traverse(PyObject *self, visitproc visit, void *arg)
{
    PyTypeObject *type, *base;
    traverseproc basetraverse;



    type = (((PyObject*)(self))->ob_type);
    base = type;
    while ((basetraverse = base->tp_traverse) == subtype_traverse) {
        if ((((PyVarObject*)(base))->ob_size)) {
            int err = traverse_slots(base, self, visit, arg);
            if (err)
                return err;
        }
        base = base->tp_base;
        (__builtin_expect(!(base), 0) ? __assert_rtn(__func__, "typeobject.c", 823, "base") : (void)0);
    }

    if (type->tp_dictoffset != base->tp_dictoffset) {
        PyObject **dictptr = _PyObject_GetDictPtr(self);
        if (dictptr && *dictptr)
            do { if (*dictptr) { int vret = visit((PyObject *)(*dictptr), arg); if (vret) return vret; } } while (0);
    }

    if (type->tp_flags & (1L<<9))



        do { if (type) { int vret = visit((PyObject *)(type), arg); if (vret) return vret; } } while (0);

    if (basetraverse)
        return basetraverse(self, visit, arg);
    return 0;
}

static void
clear_slots(PyTypeObject *type, PyObject *self)
{
    Py_ssize_t i, n;
    PyMemberDef *mp;

    n = (((PyVarObject*)(type))->ob_size);
    mp = ((PyMemberDef *)(((char *)(PyHeapTypeObject *)type) + (((PyObject*)((PyHeapTypeObject *)type))->ob_type)->tp_basicsize));
    for (i = 0; i < n; i++, mp++) {
        if (mp->type == 16 && !(mp->flags & 1)) {
            char *addr = (char *)self + mp->offset;
            PyObject *obj = *(PyObject **)addr;
            if (obj != ((void *)0)) {
                *(PyObject **)addr = ((void *)0);
                do { if ( --((PyObject*)(obj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(obj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(obj)))); } while (0);
            }
        }
    }
}

static int
subtype_clear(PyObject *self)
{
    PyTypeObject *type, *base;
    inquiry baseclear;



    type = (((PyObject*)(self))->ob_type);
    base = type;
    while ((baseclear = base->tp_clear) == subtype_clear) {
        if ((((PyVarObject*)(base))->ob_size))
            clear_slots(base, self);
        base = base->tp_base;
        (__builtin_expect(!(base), 0) ? __assert_rtn(__func__, "typeobject.c", 877, "base") : (void)0);
    }



    if (type->tp_dictoffset != base->tp_dictoffset) {
        PyObject **dictptr = _PyObject_GetDictPtr(self);
        if (dictptr && *dictptr)
            do { if (*dictptr) { PyObject *_py_tmp = (PyObject *)(*dictptr); (*dictptr) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    }

    if (baseclear)
        return baseclear(self);
    return 0;
}

static void
subtype_dealloc(PyObject *self)
{
    PyTypeObject *type, *base;
    destructor basedealloc;
    PyThreadState *tstate = ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }));


    type = (((PyObject*)(self))->ob_type);
    (__builtin_expect(!(type->tp_flags & (1L<<9)), 0) ? __assert_rtn(__func__, "typeobject.c", 902, "type->tp_flags & Py_TPFLAGS_HEAPTYPE") : (void)0);



    if (!((((type))->tp_flags & ((1L<<14))) != 0)) {







        if (type->tp_del) {
            type->tp_del(self);
            if (self->ob_refcnt > 0)
                return;
        }


        base = type;
        while ((basedealloc = base->tp_dealloc) == subtype_dealloc) {
            (__builtin_expect(!((((PyVarObject*)(base))->ob_size) == 0), 0) ? __assert_rtn(__func__, "typeobject.c", 923, "Py_SIZE(base) == 0") : (void)0);
            base = base->tp_base;
            (__builtin_expect(!(base), 0) ? __assert_rtn(__func__, "typeobject.c", 925, "base") : (void)0);
        }


        type = (((PyObject*)(self))->ob_type);


        (__builtin_expect(!(basedealloc), 0) ? __assert_rtn(__func__, "typeobject.c", 932, "basedealloc") : (void)0);
        basedealloc(self);


        do { if ( --((PyObject*)(type))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type)))); } while (0);


        return;
    }





    PyObject_GC_UnTrack(self);
    ++_PyTrash_delete_nesting;
    ++ tstate->trash_delete_nesting;
    do { PyThreadState *_tstate = ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; })); if (_tstate->trash_delete_nesting < 50) { ++_tstate->trash_delete_nesting;;
    --_PyTrash_delete_nesting;
    -- tstate->trash_delete_nesting;







    base = type;
    while (( base->tp_dealloc) == subtype_dealloc) {
        base = base->tp_base;
        (__builtin_expect(!(base), 0) ? __assert_rtn(__func__, "typeobject.c", 962, "base") : (void)0);
    }





    if (type->tp_weaklistoffset && !base->tp_weaklistoffset)
        PyObject_ClearWeakRefs(self);


    if (type->tp_del) {
        do { PyGC_Head *g = ((PyGC_Head *)(self)-1); if (g->gc.gc_refs != (-2)) Py_FatalError("GC object already tracked"); g->gc.gc_refs = (-3); g->gc.gc_next = _PyGC_generation0; g->gc.gc_prev = _PyGC_generation0->gc.gc_prev; g->gc.gc_prev->gc.gc_next = g; _PyGC_generation0->gc.gc_prev = g; } while (0);;
        type->tp_del(self);
        if (self->ob_refcnt > 0)
            goto endlabel;
        else
            do { PyGC_Head *g = ((PyGC_Head *)(self)-1); (__builtin_expect(!(g->gc.gc_refs != (-2)), 0) ? __assert_rtn(__func__, "typeobject.c", 979, "g->gc.gc_refs != _PyGC_REFS_UNTRACKED") : (void)0); g->gc.gc_refs = (-2); g->gc.gc_prev->gc.gc_next = g->gc.gc_next; g->gc.gc_next->gc.gc_prev = g->gc.gc_prev; g->gc.gc_next = ((void *)0); } while (0);;




        if (type->tp_weaklistoffset && !base->tp_weaklistoffset) {

            PyWeakReference **list = (PyWeakReference **) ((PyObject **) (((char *) (self)) + (((PyObject*)(self))->ob_type)->tp_weaklistoffset));

            while (*list)
                _PyWeakref_ClearRef(*list);
        }
    }


    base = type;
    while ((basedealloc = base->tp_dealloc) == subtype_dealloc) {
        if ((((PyVarObject*)(base))->ob_size))
            clear_slots(base, self);
        base = base->tp_base;
        (__builtin_expect(!(base), 0) ? __assert_rtn(__func__, "typeobject.c", 999, "base") : (void)0);
    }


    if (type->tp_dictoffset && !base->tp_dictoffset) {
        PyObject **dictptr = _PyObject_GetDictPtr(self);
        if (dictptr != ((void *)0)) {
            PyObject *dict = *dictptr;
            if (dict != ((void *)0)) {
                do { if ( --((PyObject*)(dict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dict)))); } while (0);
                *dictptr = ((void *)0);
            }
        }
    }


    type = (((PyObject*)(self))->ob_type);




    if (((((base))->tp_flags & ((1L<<14))) != 0))
        do { PyGC_Head *g = ((PyGC_Head *)(self)-1); if (g->gc.gc_refs != (-2)) Py_FatalError("GC object already tracked"); g->gc.gc_refs = (-3); g->gc.gc_next = _PyGC_generation0; g->gc.gc_prev = _PyGC_generation0->gc.gc_prev; g->gc.gc_prev->gc.gc_next = g; _PyGC_generation0->gc.gc_prev = g; } while (0);;
    (__builtin_expect(!(basedealloc), 0) ? __assert_rtn(__func__, "typeobject.c", 1022, "basedealloc") : (void)0);
    basedealloc(self);


    do { if ( --((PyObject*)(type))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type)))); } while (0);

  endlabel:
    ++_PyTrash_delete_nesting;
    ++ tstate->trash_delete_nesting;
    --_tstate->trash_delete_nesting; if (_tstate->trash_delete_later && _tstate->trash_delete_nesting <= 0) _PyTrash_thread_destroy_chain(); } else _PyTrash_thread_deposit_object((PyObject*)self); } while (0);;
    --_PyTrash_delete_nesting;
    -- tstate->trash_delete_nesting;
# 1132 "typeobject.c"
}

static PyTypeObject *solid_base(PyTypeObject *type);



int
PyType_IsSubtype(PyTypeObject *a, PyTypeObject *b)
{
    PyObject *mro;

    mro = a->tp_mro;
    if (mro != ((void *)0)) {


        Py_ssize_t i, n;
        (__builtin_expect(!(((((((PyObject*)(mro))->ob_type))->tp_flags & ((1L<<26))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 1148, "PyTuple_Check(mro)") : (void)0);
        n = (((PyVarObject*)(mro))->ob_size);
        for (i = 0; i < n; i++) {
            if ((((PyTupleObject *)(mro))->ob_item[i]) == (PyObject *)b)
                return 1;
        }
        return 0;
    }
    else {

        do {
            if (a == b)
                return 1;
            a = a->tp_base;
        } while (a != ((void *)0));
        return b == &PyBaseObject_Type;
    }
}
# 1184 "typeobject.c"
static PyObject *
lookup_maybe(PyObject *self, _Py_Identifier *attrid)
{
    PyObject *res;

    res = _PyType_LookupId((((PyObject*)(self))->ob_type), attrid);
    if (res != ((void *)0)) {
        descrgetfunc f;
        if ((f = (((PyObject*)(res))->ob_type)->tp_descr_get) == ((void *)0))
            ( ((PyObject*)(res))->ob_refcnt++);
        else
            res = f(res, self, (PyObject *)((((PyObject*)(self))->ob_type)));
    }
    return res;
}

static PyObject *
lookup_method(PyObject *self, _Py_Identifier *attrid)
{
    PyObject *res = lookup_maybe(self, attrid);
    if (res == ((void *)0) && !PyErr_Occurred())
        PyErr_SetObject(PyExc_AttributeError, attrid->object);
    return res;
}

PyObject *
_PyObject_LookupSpecial(PyObject *self, _Py_Identifier *attrid)
{
    return lookup_maybe(self, attrid);
}





static PyObject *
call_method(PyObject *o, _Py_Identifier *nameid, char *format, ...)
{
    va_list va;
    PyObject *args, *func = 0, *retval;
    __builtin_va_start(va,format);

    func = lookup_maybe(o, nameid);
    if (func == ((void *)0)) {
        __builtin_va_end(va);
        if (!PyErr_Occurred())
            PyErr_SetObject(PyExc_AttributeError, nameid->object);
        return ((void *)0);
    }

    if (format && *format)
        args = Py_VaBuildValue(format, va);
    else
        args = PyTuple_New(0);

    __builtin_va_end(va);

    if (args == ((void *)0))
        return ((void *)0);

    (__builtin_expect(!(((((((PyObject*)(args))->ob_type))->tp_flags & ((1L<<26))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 1244, "PyTuple_Check(args)") : (void)0);
    retval = PyObject_Call(func, args, ((void *)0));

    do { if ( --((PyObject*)(args))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(args)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(args)))); } while (0);
    do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0);

    return retval;
}



static PyObject *
call_maybe(PyObject *o, _Py_Identifier *nameid, char *format, ...)
{
    va_list va;
    PyObject *args, *func = 0, *retval;
    __builtin_va_start(va,format);

    func = lookup_maybe(o, nameid);
    if (func == ((void *)0)) {
        __builtin_va_end(va);
        if (!PyErr_Occurred())
            return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct);
        return ((void *)0);
    }

    if (format && *format)
        args = Py_VaBuildValue(format, va);
    else
        args = PyTuple_New(0);

    __builtin_va_end(va);

    if (args == ((void *)0))
        return ((void *)0);

    (__builtin_expect(!(((((((PyObject*)(args))->ob_type))->tp_flags & ((1L<<26))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 1280, "PyTuple_Check(args)") : (void)0);
    retval = PyObject_Call(func, args, ((void *)0));

    do { if ( --((PyObject*)(args))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(args)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(args)))); } while (0);
    do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0);

    return retval;
}
# 1317 "typeobject.c"
static int
tail_contains(PyObject *list, int whence, PyObject *o) {
    Py_ssize_t j, size;
    size = (((PyVarObject*)(list))->ob_size);

    for (j = whence+1; j < size; j++) {
        if ((((PyListObject *)(list))->ob_item[j]) == o)
            return 1;
    }
    return 0;
}

static PyObject *
class_name(PyObject *cls)
{
    PyObject *name = _PyObject_GetAttrId(cls, &PyId___name__);
    if (name == ((void *)0)) {
        PyErr_Clear();
        do { if ((name) == ((void *)0)) ; else do { if ( --((PyObject*)(name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(name)))); } while (0); } while (0);
        name = PyObject_Repr(cls);
    }
    if (name == ((void *)0))
        return ((void *)0);
    if (!((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        do { if ( --((PyObject*)(name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(name)))); } while (0);
        return ((void *)0);
    }
    return name;
}

static int
check_duplicates(PyObject *list)
{
    Py_ssize_t i, j, n;



    n = (((PyVarObject*)(list))->ob_size);
    for (i = 0; i < n; i++) {
        PyObject *o = (((PyListObject *)(list))->ob_item[i]);
        for (j = i + 1; j < n; j++) {
            if ((((PyListObject *)(list))->ob_item[j]) == o) {
                o = class_name(o);
                if (o != ((void *)0)) {
                    PyErr_Format(PyExc_TypeError,
                                 "duplicate base class %U",
                                 o);
                    do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0);
                } else {
                    PyErr_SetString(PyExc_TypeError,
                                 "duplicate base class");
                }
                return -1;
            }
        }
    }
    return 0;
}
# 1385 "typeobject.c"
static void
set_mro_error(PyObject *to_merge, int *remain)
{
    Py_ssize_t i, n, off, to_merge_size;
    char buf[1000];
    PyObject *k, *v;
    PyObject *set = PyDict_New();
    if (!set) return;

    to_merge_size = (((PyVarObject*)(to_merge))->ob_size);
    for (i = 0; i < to_merge_size; i++) {
        PyObject *L = (((PyListObject *)(to_merge))->ob_item[i]);
        if (remain[i] < (((PyVarObject*)(L))->ob_size)) {
            PyObject *c = (((PyListObject *)(L))->ob_item[remain[i]]);
            if (PyDict_SetItem(set, c, (&_Py_NoneStruct)) < 0) {
                do { if ( --((PyObject*)(set))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(set)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(set)))); } while (0);
                return;
            }
        }
    }
    n = PyDict_Size(set);

    off = PyOS_snprintf(buf, sizeof(buf), "Cannot create a consistent method resolution\norder (MRO) for bases");

    i = 0;
    while (PyDict_Next(set, &i, &k, &v) && (size_t)off < sizeof(buf)) {
        PyObject *name = class_name(k);
        char *name_str;
        if (name != ((void *)0)) {
            name_str = PyUnicode_AsUTF8(name);
            if (name_str == ((void *)0))
                name_str = "?";
        } else
            name_str = "?";
        off += PyOS_snprintf(buf + off, sizeof(buf) - off, " %s", name_str);
        do { if ((name) == ((void *)0)) ; else do { if ( --((PyObject*)(name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(name)))); } while (0); } while (0);
        if (--n && (size_t)(off+1) < sizeof(buf)) {
            buf[off++] = ',';
            buf[off] = '\0';
        }
    }
    PyErr_SetString(PyExc_TypeError, buf);
    do { if ( --((PyObject*)(set))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(set)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(set)))); } while (0);
}

static int
pmerge(PyObject *acc, PyObject* to_merge) {
    Py_ssize_t i, j, to_merge_size, empty_cnt;
    int *remain;
    int ok;

    to_merge_size = (((PyVarObject*)(to_merge))->ob_size);





    remain = (int *)((size_t)(4*to_merge_size) > (size_t)((Py_ssize_t)(((size_t)-1)>>1)) ? ((void *)0) : malloc((4*to_merge_size) ? (4*to_merge_size) : 1));
    if (remain == ((void *)0))
        return -1;
    for (i = 0; i < to_merge_size; i++)
        remain[i] = 0;

  again:
    empty_cnt = 0;
    for (i = 0; i < to_merge_size; i++) {
        PyObject *candidate;

        PyObject *cur_list = (((PyListObject *)(to_merge))->ob_item[i]);

        if (remain[i] >= (((PyVarObject*)(cur_list))->ob_size)) {
            empty_cnt++;
            continue;
        }
# 1467 "typeobject.c"
        candidate = (((PyListObject *)(cur_list))->ob_item[remain[i]]);
        for (j = 0; j < to_merge_size; j++) {
            PyObject *j_lst = (((PyListObject *)(to_merge))->ob_item[j]);
            if (tail_contains(j_lst, remain[j], candidate)) {
                goto skip;
            }
        }
        ok = PyList_Append(acc, candidate);
        if (ok < 0) {
            PyMem_Free(remain);
            return -1;
        }
        for (j = 0; j < to_merge_size; j++) {
            PyObject *j_lst = (((PyListObject *)(to_merge))->ob_item[j]);
            if (remain[j] < (((PyVarObject*)(j_lst))->ob_size) &&
                (((PyListObject *)(j_lst))->ob_item[remain[j]]) == candidate) {
                remain[j]++;
            }
        }
        goto again;
      skip: ;
    }

    if (empty_cnt == to_merge_size) {
        free(remain);
        return 0;
    }
    set_mro_error(to_merge, remain);
    free(remain);
    return -1;
}

static PyObject *
mro_implementation(PyTypeObject *type)
{
    Py_ssize_t i, n;
    int ok;
    PyObject *bases, *result;
    PyObject *to_merge, *bases_aslist;

    if (type->tp_dict == ((void *)0)) {
        if (PyType_Ready(type) < 0)
            return ((void *)0);
    }
# 1521 "typeobject.c"
    bases = type->tp_bases;
    n = (((PyVarObject*)(bases))->ob_size);

    to_merge = PyList_New(n+1);
    if (to_merge == ((void *)0))
        return ((void *)0);

    for (i = 0; i < n; i++) {
        PyObject *base = (((PyTupleObject *)(bases))->ob_item[i]);
        PyObject *parentMRO;
        parentMRO = PySequence_List(((PyTypeObject*)base)->tp_mro);
        if (parentMRO == ((void *)0)) {
            do { if ( --((PyObject*)(to_merge))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(to_merge)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(to_merge)))); } while (0);
            return ((void *)0);
        }

        (((PyListObject *)(to_merge))->ob_item[i] = (parentMRO));
    }

    bases_aslist = PySequence_List(bases);
    if (bases_aslist == ((void *)0)) {
        do { if ( --((PyObject*)(to_merge))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(to_merge)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(to_merge)))); } while (0);
        return ((void *)0);
    }

    if (check_duplicates(bases_aslist) < 0) {
        do { if ( --((PyObject*)(to_merge))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(to_merge)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(to_merge)))); } while (0);
        do { if ( --((PyObject*)(bases_aslist))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(bases_aslist)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(bases_aslist)))); } while (0);
        return ((void *)0);
    }
    (((PyListObject *)(to_merge))->ob_item[n] = (bases_aslist));

    result = Py_BuildValue("[O]", (PyObject *)type);
    if (result == ((void *)0)) {
        do { if ( --((PyObject*)(to_merge))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(to_merge)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(to_merge)))); } while (0);
        return ((void *)0);
    }

    ok = pmerge(result, to_merge);
    do { if ( --((PyObject*)(to_merge))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(to_merge)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(to_merge)))); } while (0);
    if (ok < 0) {
        do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0);
        return ((void *)0);
    }

    return result;
}

static PyObject *
mro_external(PyObject *self)
{
    PyTypeObject *type = (PyTypeObject *)self;

    return mro_implementation(type);
}

static int
mro_internal(PyTypeObject *type)
{
    PyObject *mro, *result, *tuple;
    int checkit = 0;

    if ((((PyObject*)(type))->ob_type) == &PyType_Type) {
        result = mro_implementation(type);
    }
    else {
        static _Py_Identifier PyId_mro = { 0, "mro", 0 };
        checkit = 1;
        mro = lookup_method((PyObject *)type, &PyId_mro);
        if (mro == ((void *)0))
            return -1;
        result = PyObject_CallObject(mro, ((void *)0));
        do { if ( --((PyObject*)(mro))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(mro)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(mro)))); } while (0);
    }
    if (result == ((void *)0))
        return -1;
    tuple = PySequence_Tuple(result);
    do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0);
    if (tuple == ((void *)0))
        return -1;
    if (checkit) {
        Py_ssize_t i, len;
        PyObject *cls;
        PyTypeObject *solid;

        solid = solid_base(type);

        len = (((PyVarObject*)(tuple))->ob_size);

        for (i = 0; i < len; i++) {
            PyTypeObject *t;
            cls = (((PyTupleObject *)(tuple))->ob_item[i]);
            if (!((((((PyObject*)(cls))->ob_type))->tp_flags & ((1L<<31))) != 0)) {
                PyErr_Format(PyExc_TypeError,
                 "mro() returned a non-class ('%.500s')",
                                 (((PyObject*)(cls))->ob_type)->tp_name);
                do { if ( --((PyObject*)(tuple))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tuple)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tuple)))); } while (0);
                return -1;
            }
            t = (PyTypeObject*)cls;
            if (!PyType_IsSubtype(solid, solid_base(t))) {
                PyErr_Format(PyExc_TypeError,
             "mro() returned base with unsuitable layout ('%.500s')",
                                     t->tp_name);
                        do { if ( --((PyObject*)(tuple))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tuple)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tuple)))); } while (0);
                        return -1;
            }
        }
    }
    type->tp_mro = tuple;

    type_mro_modified(type, type->tp_mro);


    type_mro_modified(type, type->tp_bases);

    PyType_Modified(type);

    return 0;
}





static PyTypeObject *
best_base(PyObject *bases)
{
    Py_ssize_t i, n;
    PyTypeObject *base, *winner, *candidate, *base_i;
    PyObject *base_proto;

    (__builtin_expect(!(((((((PyObject*)(bases))->ob_type))->tp_flags & ((1L<<26))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 1653, "PyTuple_Check(bases)") : (void)0);
    n = (((PyVarObject*)(bases))->ob_size);
    (__builtin_expect(!(n > 0), 0) ? __assert_rtn(__func__, "typeobject.c", 1655, "n > 0") : (void)0);
    base = ((void *)0);
    winner = ((void *)0);
    for (i = 0; i < n; i++) {
        base_proto = (((PyTupleObject *)(bases))->ob_item[i]);
        if (!((((((PyObject*)(base_proto))->ob_type))->tp_flags & ((1L<<31))) != 0)) {
            PyErr_SetString(
                PyExc_TypeError,
                "bases must be types");
            return ((void *)0);
        }
        base_i = (PyTypeObject *)base_proto;
        if (base_i->tp_dict == ((void *)0)) {
            if (PyType_Ready(base_i) < 0)
                return ((void *)0);
        }
        candidate = solid_base(base_i);
        if (winner == ((void *)0)) {
            winner = candidate;
            base = base_i;
        }
        else if (PyType_IsSubtype(winner, candidate))
            ;
        else if (PyType_IsSubtype(candidate, winner)) {
            winner = candidate;
            base = base_i;
        }
        else {
            PyErr_SetString(
                PyExc_TypeError,
                "multiple bases have "
                "instance lay-out conflict");
            return ((void *)0);
        }
    }
    (__builtin_expect(!(base != ((void *)0)), 0) ? __assert_rtn(__func__, "typeobject.c", 1690, "base != NULL") : (void)0);

    return base;
}

static int
extra_ivars(PyTypeObject *type, PyTypeObject *base)
{
    size_t t_size = type->tp_basicsize;
    size_t b_size = base->tp_basicsize;

    (__builtin_expect(!(t_size >= b_size), 0) ? __assert_rtn(__func__, "typeobject.c", 1701, "t_size >= b_size") : (void)0);
    if (type->tp_itemsize || base->tp_itemsize) {

        return t_size != b_size ||
            type->tp_itemsize != base->tp_itemsize;
    }
    if (type->tp_weaklistoffset && base->tp_weaklistoffset == 0 &&
        type->tp_weaklistoffset + sizeof(PyObject *) == t_size &&
        type->tp_flags & (1L<<9))
        t_size -= sizeof(PyObject *);
    if (type->tp_dictoffset && base->tp_dictoffset == 0 &&
        type->tp_dictoffset + sizeof(PyObject *) == t_size &&
        type->tp_flags & (1L<<9))
        t_size -= sizeof(PyObject *);

    return t_size != b_size;
}

static PyTypeObject *
solid_base(PyTypeObject *type)
{
    PyTypeObject *base;

    if (type->tp_base)
        base = solid_base(type->tp_base);
    else
        base = &PyBaseObject_Type;
    if (extra_ivars(type, base))
        return type;
    else
        return base;
}

static void object_dealloc(PyObject *);
static int object_init(PyObject *, PyObject *, PyObject *);
static int update_slot(PyTypeObject *, PyObject *);
static void fixup_slot_dispatchers(PyTypeObject *);






static PyTypeObject *
get_builtin_base_with_dict(PyTypeObject *type)
{
    while (type->tp_base != ((void *)0)) {
        if (type->tp_dictoffset != 0 &&
            !(type->tp_flags & (1L<<9)))
            return type;
        type = type->tp_base;
    }
    return ((void *)0);
}

static PyObject *
get_dict_descriptor(PyTypeObject *type)
{
    PyObject *descr;

    descr = _PyType_LookupId(type, &PyId___dict__);
    if (descr == ((void *)0) || !((((PyObject*)(descr))->ob_type)->tp_descr_set != ((void *)0)))
        return ((void *)0);

    return descr;
}

static void
raise_dict_descr_error(PyObject *obj)
{
    PyErr_Format(PyExc_TypeError,
                 "this __dict__ descriptor does not support "
                 "'%.200s' objects", (((PyObject*)(obj))->ob_type)->tp_name);
}

static PyObject *
subtype_dict(PyObject *obj, void *context)
{
    PyTypeObject *base;

    base = get_builtin_base_with_dict((((PyObject*)(obj))->ob_type));
    if (base != ((void *)0)) {
        descrgetfunc func;
        PyObject *descr = get_dict_descriptor(base);
        if (descr == ((void *)0)) {
            raise_dict_descr_error(obj);
            return ((void *)0);
        }
        func = (((PyObject*)(descr))->ob_type)->tp_descr_get;
        if (func == ((void *)0)) {
            raise_dict_descr_error(obj);
            return ((void *)0);
        }
        return func(descr, obj, (PyObject *)((((PyObject*)(obj))->ob_type)));
    }
    return PyObject_GenericGetDict(obj, context);
}

static int
subtype_setdict(PyObject *obj, PyObject *value, void *context)
{
    PyObject *dict, **dictptr;
    PyTypeObject *base;

    base = get_builtin_base_with_dict((((PyObject*)(obj))->ob_type));
    if (base != ((void *)0)) {
        descrsetfunc func;
        PyObject *descr = get_dict_descriptor(base);
        if (descr == ((void *)0)) {
            raise_dict_descr_error(obj);
            return -1;
        }
        func = (((PyObject*)(descr))->ob_type)->tp_descr_set;
        if (func == ((void *)0)) {
            raise_dict_descr_error(obj);
            return -1;
        }
        return func(descr, obj, value);
    }

    dictptr = _PyObject_GetDictPtr(obj);
    if (dictptr == ((void *)0)) {
        PyErr_SetString(PyExc_AttributeError,
                        "This object has no __dict__");
        return -1;
    }
    if (value != ((void *)0) && !((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<29))) != 0)) {
        PyErr_Format(PyExc_TypeError,
                     "__dict__ must be set to a dictionary, "
                     "not a '%.200s'", (((PyObject*)(value))->ob_type)->tp_name);
        return -1;
    }
    dict = *dictptr;
    do { if ((value) == ((void *)0)) ; else ( ((PyObject*)(value))->ob_refcnt++); } while (0);
    *dictptr = value;
    do { if ((dict) == ((void *)0)) ; else do { if ( --((PyObject*)(dict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dict)))); } while (0); } while (0);
    return 0;
}

static PyObject *
subtype_getweakref(PyObject *obj, void *context)
{
    PyObject **weaklistptr;
    PyObject *result;

    if ((((PyObject*)(obj))->ob_type)->tp_weaklistoffset == 0) {
        PyErr_SetString(PyExc_AttributeError,
                        "This object has no __weakref__");
        return ((void *)0);
    }
    (__builtin_expect(!((((PyObject*)(obj))->ob_type)->tp_weaklistoffset > 0), 0) ? __assert_rtn(__func__, "typeobject.c", 1851, "Py_TYPE(obj)->tp_weaklistoffset > 0") : (void)0);
    (__builtin_expect(!((((PyObject*)(obj))->ob_type)->tp_weaklistoffset + sizeof(PyObject *) <= (size_t)((((PyObject*)(obj))->ob_type)->tp_basicsize)), 0) ? __assert_rtn(__func__, "typeobject.c", 1853, "Py_TYPE(obj)->tp_weaklistoffset + sizeof(PyObject *) <= (size_t)(Py_TYPE(obj)->tp_basicsize)") : (void)0);

    weaklistptr = (PyObject **)
        ((char *)obj + (((PyObject*)(obj))->ob_type)->tp_weaklistoffset);
    if (*weaklistptr == ((void *)0))
        result = (&_Py_NoneStruct);
    else
        result = *weaklistptr;
    ( ((PyObject*)(result))->ob_refcnt++);
    return result;
}



static PyGetSetDef subtype_getsets_full[] = {
    {"__dict__", subtype_dict, subtype_setdict,
     "dictionary for instance variables (if defined)"},
    {"__weakref__", subtype_getweakref, ((void *)0),
     "list of weak references to the object (if defined)"},
    {0}
};

static PyGetSetDef subtype_getsets_dict_only[] = {
    {"__dict__", subtype_dict, subtype_setdict,
     "dictionary for instance variables (if defined)"},
    {0}
};

static PyGetSetDef subtype_getsets_weakref_only[] = {
    {"__weakref__", subtype_getweakref, ((void *)0),
     "list of weak references to the object (if defined)"},
    {0}
};

static int
valid_identifier(PyObject *s)
{
    if (!((((((PyObject*)(s))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        PyErr_Format(PyExc_TypeError,
                     "__slots__ items must be strings, not '%.200s'",
                     (((PyObject*)(s))->ob_type)->tp_name);
        return 0;
    }
    if (!PyUnicode_IsIdentifier(s)) {
        PyErr_SetString(PyExc_TypeError,
                        "__slots__ must be identifiers");
        return 0;
    }
    return 1;
}


static int
object_init(PyObject *self, PyObject *args, PyObject *kwds);

static int
type_init(PyObject *cls, PyObject *args, PyObject *kwds)
{
    int res;

    (__builtin_expect(!(args != ((void *)0) && ((((((PyObject*)(args))->ob_type))->tp_flags & ((1L<<26))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 1912, "args != NULL && PyTuple_Check(args)") : (void)0);
    (__builtin_expect(!(kwds == ((void *)0) || ((((((PyObject*)(kwds))->ob_type))->tp_flags & ((1L<<29))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 1913, "kwds == NULL || PyDict_Check(kwds)") : (void)0);

    if (kwds != ((void *)0) && ((((((PyObject*)(kwds))->ob_type))->tp_flags & ((1L<<29))) != 0) && PyDict_Size(kwds) != 0) {
        PyErr_SetString(PyExc_TypeError,
                        "type.__init__() takes no keyword arguments");
        return -1;
    }

    if (args != ((void *)0) && ((((((PyObject*)(args))->ob_type))->tp_flags & ((1L<<26))) != 0) &&
        ((((PyVarObject*)(args))->ob_size) != 1 && (((PyVarObject*)(args))->ob_size) != 3)) {
        PyErr_SetString(PyExc_TypeError,
                        "type.__init__() takes 1 or 3 arguments");
        return -1;
    }



    args = PyTuple_GetSlice(args, 0, 0);
    res = object_init(cls, args, ((void *)0));
    do { if ( --((PyObject*)(args))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(args)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(args)))); } while (0);
    return res;
}

long
PyType_GetFlags(PyTypeObject *type)
{
    return type->tp_flags;
}


PyTypeObject *
_PyType_CalculateMetaclass(PyTypeObject *metatype, PyObject *bases)
{
    Py_ssize_t i, nbases;
    PyTypeObject *winner;
    PyObject *tmp;
    PyTypeObject *tmptype;






    nbases = (((PyVarObject*)(bases))->ob_size);
    winner = metatype;
    for (i = 0; i < nbases; i++) {
        tmp = (((PyTupleObject *)(bases))->ob_item[i]);
        tmptype = (((PyObject*)(tmp))->ob_type);
        if (PyType_IsSubtype(winner, tmptype))
            continue;
        if (PyType_IsSubtype(tmptype, winner)) {
            winner = tmptype;
            continue;
        }

        PyErr_SetString(PyExc_TypeError,
                        "metaclass conflict: "
                        "the metaclass of a derived class "
                        "must be a (non-strict) subclass "
                        "of the metaclasses of all its bases");
        return ((void *)0);
    }
    return winner;
}

static PyObject *
type_new(PyTypeObject *metatype, PyObject *args, PyObject *kwds)
{
    PyObject *name, *bases = ((void *)0), *orig_dict, *dict = ((void *)0);
    static char *kwlist[] = {"name", "bases", "dict", 0};
    PyObject *qualname, *slots = ((void *)0), *tmp, *newslots;
    PyTypeObject *type = ((void *)0), *base, *tmptype, *winner;
    PyHeapTypeObject *et;
    PyMemberDef *mp;
    Py_ssize_t i, nbases, nslots, slotoffset, add_dict, add_weak;
    int j, may_add_dict, may_add_weak;
    static _Py_Identifier PyId___qualname__ = { 0, "__qualname__", 0 };
    static _Py_Identifier PyId___slots__ = { 0, "__slots__", 0 };

    (__builtin_expect(!(args != ((void *)0) && ((((((PyObject*)(args))->ob_type))->tp_flags & ((1L<<26))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 1992, "args != NULL && PyTuple_Check(args)") : (void)0);
    (__builtin_expect(!(kwds == ((void *)0) || ((((((PyObject*)(kwds))->ob_type))->tp_flags & ((1L<<29))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 1993, "kwds == NULL || PyDict_Check(kwds)") : (void)0);


    {
        const Py_ssize_t nargs = (((PyVarObject*)(args))->ob_size);
        const Py_ssize_t nkwds = kwds == ((void *)0) ? 0 : PyDict_Size(kwds);

        if (((((PyObject*)(metatype))->ob_type) == &PyType_Type) && nargs == 1 && nkwds == 0) {
            PyObject *x = (((PyTupleObject *)(args))->ob_item[0]);
            ( ((PyObject*)((((PyObject*)(x))->ob_type)))->ob_refcnt++);
            return (PyObject *) (((PyObject*)(x))->ob_type);
        }




        if (nargs + nkwds != 3) {
            PyErr_SetString(PyExc_TypeError,
                            "type() takes 1 or 3 arguments");
            return ((void *)0);
        }
    }


    if (!PyArg_ParseTupleAndKeywords(args, kwds, "UO!O!:type", kwlist,
                                     &name,
                                     &PyTuple_Type, &bases,
                                     &PyDict_Type, &orig_dict))
        return ((void *)0);


    winner = _PyType_CalculateMetaclass(metatype, bases);
    if (winner == ((void *)0)) {
        return ((void *)0);
    }

    if (winner != metatype) {
        if (winner->tp_new != type_new)
            return winner->tp_new(winner, args, kwds);
        metatype = winner;
    }


    nbases = (((PyVarObject*)(bases))->ob_size);
    if (nbases == 0) {
        bases = PyTuple_Pack(1, &PyBaseObject_Type);
        if (bases == ((void *)0))
            goto error;
        nbases = 1;
    }
    else
        ( ((PyObject*)(bases))->ob_refcnt++);


    base = best_base(bases);
    if (base == ((void *)0)) {
        goto error;
    }
    if (!(((base)->tp_flags & ((1L<<10))) != 0)) {
        PyErr_Format(PyExc_TypeError,
                     "type '%.100s' is not an acceptable base type",
                     base->tp_name);
        goto error;
    }

    dict = PyDict_Copy(orig_dict);
    if (dict == ((void *)0))
        goto error;


    slots = _PyDict_GetItemId(dict, &PyId___slots__);
    nslots = 0;
    add_dict = 0;
    add_weak = 0;
    may_add_dict = base->tp_dictoffset == 0;
    may_add_weak = base->tp_weaklistoffset == 0 && base->tp_itemsize == 0;
    if (slots == ((void *)0)) {
        if (may_add_dict) {
            add_dict++;
        }
        if (may_add_weak) {
            add_weak++;
        }
    }
    else {



        if (((((((PyObject*)(slots))->ob_type))->tp_flags & ((1L<<28))) != 0))
            slots = PyTuple_Pack(1, slots);
        else
            slots = PySequence_Tuple(slots);
        if (slots == ((void *)0))
            goto error;
        (__builtin_expect(!(((((((PyObject*)(slots))->ob_type))->tp_flags & ((1L<<26))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 2087, "PyTuple_Check(slots)") : (void)0);


        nslots = (((PyVarObject*)(slots))->ob_size);
        if (nslots > 0 && base->tp_itemsize != 0) {
            PyErr_Format(PyExc_TypeError,
                         "nonempty __slots__ "
                         "not supported for subtype of '%s'",
                         base->tp_name);
            goto error;
        }


        for (i = 0; i < nslots; i++) {
            PyObject *tmp = (((PyTupleObject *)(slots))->ob_item[i]);
            if (!valid_identifier(tmp))
                goto error;
            (__builtin_expect(!(((((((PyObject*)(tmp))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 2104, "PyUnicode_Check(tmp)") : (void)0);
            if (PyUnicode_CompareWithASCIIString(tmp, "__dict__") == 0) {
                if (!may_add_dict || add_dict) {
                    PyErr_SetString(PyExc_TypeError,
                        "__dict__ slot disallowed: "
                        "we already got one");
                    goto error;
                }
                add_dict++;
            }
            if (PyUnicode_CompareWithASCIIString(tmp, "__weakref__") == 0) {
                if (!may_add_weak || add_weak) {
                    PyErr_SetString(PyExc_TypeError,
                        "__weakref__ slot disallowed: "
                        "either we already got one, "
                        "or __itemsize__ != 0");
                    goto error;
                }
                add_weak++;
            }
        }





        newslots = PyList_New(nslots - add_dict - add_weak);
        if (newslots == ((void *)0))
            goto error;
        for (i = j = 0; i < nslots; i++) {
            tmp = (((PyTupleObject *)(slots))->ob_item[i]);
            if ((add_dict &&
                 PyUnicode_CompareWithASCIIString(tmp, "__dict__") == 0) ||
                (add_weak &&
                 PyUnicode_CompareWithASCIIString(tmp, "__weakref__") == 0))
                continue;
            tmp =_Py_Mangle(name, tmp);
            if (!tmp) {
                do { if ( --((PyObject*)(newslots))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(newslots)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(newslots)))); } while (0);
                goto error;
            }
            (((PyListObject *)(newslots))->ob_item[j] = (tmp));
            if (PyDict_GetItem(dict, tmp)) {
                PyErr_Format(PyExc_ValueError,
                             "%R in __slots__ conflicts with class variable",
                             tmp);
                do { if ( --((PyObject*)(newslots))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(newslots)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(newslots)))); } while (0);
                goto error;
            }
            j++;
        }
        (__builtin_expect(!(j == nslots - add_dict - add_weak), 0) ? __assert_rtn(__func__, "typeobject.c", 2155, "j == nslots - add_dict - add_weak") : (void)0);
        nslots = j;
        do { if (slots) { PyObject *_py_tmp = (PyObject *)(slots); (slots) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
        if (PyList_Sort(newslots) == -1) {
            do { if ( --((PyObject*)(newslots))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(newslots)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(newslots)))); } while (0);
            goto error;
        }
        slots = PyList_AsTuple(newslots);
        do { if ( --((PyObject*)(newslots))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(newslots)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(newslots)))); } while (0);
        if (slots == ((void *)0))
            goto error;


        if (nbases > 1 &&
            ((may_add_dict && !add_dict) ||
             (may_add_weak && !add_weak))) {
            for (i = 0; i < nbases; i++) {
                tmp = (((PyTupleObject *)(bases))->ob_item[i]);
                if (tmp == (PyObject *)base)
                    continue;
                (__builtin_expect(!(((((((PyObject*)(tmp))->ob_type))->tp_flags & ((1L<<31))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 2175, "PyType_Check(tmp)") : (void)0);
                tmptype = (PyTypeObject *)tmp;
                if (may_add_dict && !add_dict &&
                    tmptype->tp_dictoffset != 0)
                    add_dict++;
                if (may_add_weak && !add_weak &&
                    tmptype->tp_weaklistoffset != 0)
                    add_weak++;
                if (may_add_dict && !add_dict)
                    continue;
                if (may_add_weak && !add_weak)
                    continue;

                break;
            }
        }
    }


    type = (PyTypeObject *)metatype->tp_alloc(metatype, nslots);
    if (type == ((void *)0))
        goto error;


    et = (PyHeapTypeObject *)type;
    ( ((PyObject*)(name))->ob_refcnt++);
    et->ht_name = name;
    et->ht_slots = slots;
    slots = ((void *)0);


    type->tp_flags = ( 0 | (1L<<18) | 0) | (1L<<9) |
        (1L<<10);
    if (base->tp_flags & (1L<<14))
        type->tp_flags |= (1L<<14);


    type->tp_as_number = &et->as_number;
    type->tp_as_sequence = &et->as_sequence;
    type->tp_as_mapping = &et->as_mapping;
    type->tp_as_buffer = &et->as_buffer;
    type->tp_name = PyUnicode_AsUTF8(name);
    if (!type->tp_name)
        goto error;


    type->tp_bases = bases;
    bases = ((void *)0);
    ( ((PyObject*)(base))->ob_refcnt++);
    type->tp_base = base;


    ( ((PyObject*)(dict))->ob_refcnt++);
    type->tp_dict = dict;


    if (_PyDict_GetItemId(dict, &PyId___module__) == ((void *)0)) {
        tmp = PyEval_GetGlobals();
        if (tmp != ((void *)0)) {
            tmp = _PyDict_GetItemId(tmp, &PyId___name__);
            if (tmp != ((void *)0)) {
                if (_PyDict_SetItemId(dict, &PyId___module__,
                                      tmp) < 0)
                    goto error;
            }
        }
    }




    qualname = _PyDict_GetItemId(dict, &PyId___qualname__);
    if (qualname != ((void *)0)) {
        if (!((((((PyObject*)(qualname))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
            PyErr_Format(PyExc_TypeError,
                         "type __qualname__ must be a str, not %s",
                         (((PyObject*)(qualname))->ob_type)->tp_name);
            goto error;
        }
    }
    et->ht_qualname = qualname ? qualname : et->ht_name;
    ( ((PyObject*)(et->ht_qualname))->ob_refcnt++);
    if (qualname != ((void *)0) && PyDict_DelItem(dict, PyId___qualname__.object) < 0)
        goto error;





    {
        PyObject *doc = _PyDict_GetItemId(dict, &PyId___doc__);
        if (doc != ((void *)0) && ((((((PyObject*)(doc))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
            Py_ssize_t len;
            char *doc_str;
            char *tp_doc;

            doc_str = PyUnicode_AsUTF8(doc);
            if (doc_str == ((void *)0))
                goto error;

            len = strlen(doc_str);
            tp_doc = (char *)PyObject_Malloc(len + 1);
            if (tp_doc == ((void *)0))
                goto error;
            ((__builtin_object_size (tp_doc, 0) != (size_t) -1) ? __builtin___memcpy_chk (tp_doc, doc_str, len + 1, __builtin_object_size (tp_doc, 0)) : __inline_memcpy_chk (tp_doc, doc_str, len + 1));
            type->tp_doc = tp_doc;
        }
    }



    tmp = _PyDict_GetItemId(dict, &PyId___new__);
    if (tmp != ((void *)0) && ((((PyObject*)(tmp))->ob_type) == &PyFunction_Type)) {
        tmp = PyStaticMethod_New(tmp);
        if (tmp == ((void *)0))
            goto error;
        if (_PyDict_SetItemId(dict, &PyId___new__, tmp) < 0)
            goto error;
        do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0);
    }


    mp = ((PyMemberDef *)(((char *)et) + (((PyObject*)(et))->ob_type)->tp_basicsize));
    slotoffset = base->tp_basicsize;
    if (et->ht_slots != ((void *)0)) {
        for (i = 0; i < nslots; i++, mp++) {
            mp->name = PyUnicode_AsUTF8(
                (((PyTupleObject *)(et->ht_slots))->ob_item[i]));
            if (mp->name == ((void *)0))
                goto error;
            mp->type = 16;
            mp->offset = slotoffset;


            (__builtin_expect(!(strcmp(mp->name, "__dict__") != 0), 0) ? __assert_rtn(__func__, "typeobject.c", 2309, "strcmp(mp->name, \"__dict__\") != 0") : (void)0);
            (__builtin_expect(!(strcmp(mp->name, "__weakref__") != 0), 0) ? __assert_rtn(__func__, "typeobject.c", 2310, "strcmp(mp->name, \"__weakref__\") != 0") : (void)0);

            slotoffset += sizeof(PyObject *);
        }
    }
    if (add_dict) {
        if (base->tp_itemsize)
            type->tp_dictoffset = -(long)sizeof(PyObject *);
        else
            type->tp_dictoffset = slotoffset;
        slotoffset += sizeof(PyObject *);
    }
    if (type->tp_dictoffset) {
        et->ht_cached_keys = _PyDict_NewKeysForClass();
    }
    if (add_weak) {
        (__builtin_expect(!(!base->tp_itemsize), 0) ? __assert_rtn(__func__, "typeobject.c", 2326, "!base->tp_itemsize") : (void)0);
        type->tp_weaklistoffset = slotoffset;
        slotoffset += sizeof(PyObject *);
    }
    type->tp_basicsize = slotoffset;
    type->tp_itemsize = base->tp_itemsize;
    type->tp_members = ((PyMemberDef *)(((char *)et) + (((PyObject*)(et))->ob_type)->tp_basicsize));

    if (type->tp_weaklistoffset && type->tp_dictoffset)
        type->tp_getset = subtype_getsets_full;
    else if (type->tp_weaklistoffset && !type->tp_dictoffset)
        type->tp_getset = subtype_getsets_weakref_only;
    else if (!type->tp_weaklistoffset && type->tp_dictoffset)
        type->tp_getset = subtype_getsets_dict_only;
    else
        type->tp_getset = ((void *)0);


    if (type->tp_dictoffset != 0 || nslots > 0) {
        if (base->tp_getattr == ((void *)0) && base->tp_getattro == ((void *)0))
            type->tp_getattro = PyObject_GenericGetAttr;
        if (base->tp_setattr == ((void *)0) && base->tp_setattro == ((void *)0))
            type->tp_setattro = PyObject_GenericSetAttr;
    }
    type->tp_dealloc = subtype_dealloc;


    if (!(type->tp_basicsize == sizeof(PyObject) &&
          type->tp_itemsize == 0))
        type->tp_flags |= (1L<<14);


    type->tp_alloc = PyType_GenericAlloc;
    if (type->tp_flags & (1L<<14)) {
        type->tp_free = PyObject_GC_Del;
        type->tp_traverse = subtype_traverse;
        type->tp_clear = subtype_clear;
    }
    else
        type->tp_free = PyObject_Free;


    if (PyType_Ready(type) < 0)
        goto error;


    fixup_slot_dispatchers(type);

    do { if ( --((PyObject*)(dict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dict)))); } while (0);
    return (PyObject *)type;

error:
    do { if ((dict) == ((void *)0)) ; else do { if ( --((PyObject*)(dict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dict)))); } while (0); } while (0);
    do { if ((bases) == ((void *)0)) ; else do { if ( --((PyObject*)(bases))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(bases)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(bases)))); } while (0); } while (0);
    do { if ((slots) == ((void *)0)) ; else do { if ( --((PyObject*)(slots))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(slots)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(slots)))); } while (0); } while (0);
    do { if ((type) == ((void *)0)) ; else do { if ( --((PyObject*)(type))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type)))); } while (0); } while (0);
    return ((void *)0);
}

static short slotoffsets[] = {
    -1,
# 1 "typeslots.inc" 1

0,
0,
__builtin_offsetof (PyHeapTypeObject, as_mapping.mp_ass_subscript),
__builtin_offsetof (PyHeapTypeObject, as_mapping.mp_length),
__builtin_offsetof (PyHeapTypeObject, as_mapping.mp_subscript),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_absolute),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_add),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_and),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_bool),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_divmod),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_float),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_floor_divide),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_index),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_add),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_and),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_floor_divide),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_lshift),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_multiply),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_or),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_power),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_remainder),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_rshift),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_subtract),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_true_divide),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_xor),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_int),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_invert),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_lshift),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_multiply),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_negative),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_or),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_positive),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_power),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_remainder),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_rshift),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_subtract),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_true_divide),
__builtin_offsetof (PyHeapTypeObject, as_number.nb_xor),
__builtin_offsetof (PyHeapTypeObject, as_sequence.sq_ass_item),
__builtin_offsetof (PyHeapTypeObject, as_sequence.sq_concat),
__builtin_offsetof (PyHeapTypeObject, as_sequence.sq_contains),
__builtin_offsetof (PyHeapTypeObject, as_sequence.sq_inplace_concat),
__builtin_offsetof (PyHeapTypeObject, as_sequence.sq_inplace_repeat),
__builtin_offsetof (PyHeapTypeObject, as_sequence.sq_item),
__builtin_offsetof (PyHeapTypeObject, as_sequence.sq_length),
__builtin_offsetof (PyHeapTypeObject, as_sequence.sq_repeat),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_alloc),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_base),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_bases),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_call),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_clear),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_dealloc),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_del),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_descr_get),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_descr_set),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_doc),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_getattr),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_getattro),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_hash),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_init),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_is_gc),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_iter),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_iternext),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_methods),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_new),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_repr),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_richcompare),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_setattr),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_setattro),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_str),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_traverse),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_members),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_getset),
__builtin_offsetof (PyHeapTypeObject, ht_type.tp_free),
# 2388 "typeobject.c" 2
};

PyObject *
PyType_FromSpecWithBases(PyType_Spec *spec, PyObject *bases)
{
    PyHeapTypeObject *res = (PyHeapTypeObject*)PyType_GenericAlloc(&PyType_Type, 0);
    PyTypeObject *type, *base;
    char *s;
    char *res_start = (char*)res;
    PyType_Slot *slot;


    s = strrchr(spec->name, '.');
    if (s == ((void *)0))
        s = (char*)spec->name;
    else
        s++;

    if (res == ((void *)0))
        return ((void *)0);
    type = &res->ht_type;

    type->tp_flags = spec->flags | (1L<<9);
    res->ht_name = PyUnicode_FromString(s);
    if (!res->ht_name)
        goto fail;
    res->ht_qualname = res->ht_name;
    ( ((PyObject*)(res->ht_qualname))->ob_refcnt++);
    type->tp_name = spec->name;
    if (!type->tp_name)
        goto fail;


    if (!bases) {
        base = &PyBaseObject_Type;

        for (slot = spec->slots; slot->slot; slot++) {
            if (slot->slot == 48)
                base = slot->pfunc;
            else if (slot->slot == 49) {
                bases = slot->pfunc;
                ( ((PyObject*)(bases))->ob_refcnt++);
            }
        }
        if (!bases)
            bases = PyTuple_Pack(1, base);
        if (!bases)
            goto fail;
    }
    else
        ( ((PyObject*)(bases))->ob_refcnt++);


    base = best_base(bases);
    if (base == ((void *)0)) {
        goto fail;
    }
    if (!(((base)->tp_flags & ((1L<<10))) != 0)) {
        PyErr_Format(PyExc_TypeError,
                     "type '%.100s' is not an acceptable base type",
                     base->tp_name);
        goto fail;
    }


    type->tp_as_number = &res->as_number;
    type->tp_as_sequence = &res->as_sequence;
    type->tp_as_mapping = &res->as_mapping;
    type->tp_as_buffer = &res->as_buffer;

    type->tp_bases = bases;
    bases = ((void *)0);
    ( ((PyObject*)(base))->ob_refcnt++);
    type->tp_base = base;

    type->tp_basicsize = spec->basicsize;
    type->tp_itemsize = spec->itemsize;

    for (slot = spec->slots; slot->slot; slot++) {
        if (slot->slot >= (sizeof(slotoffsets) / sizeof((slotoffsets)[0]) + (sizeof(char [1 - 2*!(!__builtin_types_compatible_p(typeof(slotoffsets), typeof(&(slotoffsets)[0])))]) - 1))) {
            PyErr_SetString(PyExc_RuntimeError, "invalid slot offset");
            goto fail;
        }
        if (slot->slot == 48 || slot->slot == 49)

            continue;
        *(void**)(res_start + slotoffsets[slot->slot]) = slot->pfunc;



        if (slot->slot == 56) {
            size_t len = strlen(slot->pfunc)+1;
            char *tp_doc = PyObject_Malloc(len);
            if (tp_doc == ((void *)0))
                goto fail;
            ((__builtin_object_size (tp_doc, 0) != (size_t) -1) ? __builtin___memcpy_chk (tp_doc, slot->pfunc, len, __builtin_object_size (tp_doc, 0)) : __inline_memcpy_chk (tp_doc, slot->pfunc, len));
            type->tp_doc = tp_doc;
        }
    }
    if (type->tp_dictoffset) {
        res->ht_cached_keys = _PyDict_NewKeysForClass();
    }
    if (type->tp_dealloc == ((void *)0)) {



        type->tp_dealloc = subtype_dealloc;
    }

    if (PyType_Ready(type) < 0)
        goto fail;


    s = strrchr(spec->name, '.');
    if (s != ((void *)0))
        _PyDict_SetItemId(type->tp_dict, &PyId___module__,
            PyUnicode_FromStringAndSize(
                spec->name, (Py_ssize_t)(s - spec->name)));

    return (PyObject*)res;

 fail:
    do { if ( --((PyObject*)(res))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(res)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(res)))); } while (0);
    return ((void *)0);
}

PyObject *
PyType_FromSpec(PyType_Spec *spec)
{
    return PyType_FromSpecWithBases(spec, ((void *)0));
}




PyObject *
_PyType_Lookup(PyTypeObject *type, PyObject *name)
{
    Py_ssize_t i, n;
    PyObject *mro, *res, *base, *dict;
    unsigned int h;

    if (((((PyObject*)(name))->ob_type) == &PyUnicode_Type) && ((__builtin_expect(!(((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 2530, "PyUnicode_Check(name)") : (void)0), ((((PyASCIIObject*)name)->state.ready) ? 0 : _PyUnicode_Ready((PyObject *)(name)))) != -1 && ((__builtin_expect(!(((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 2530, "PyUnicode_Check(name)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)name)->state.ready)), 0) ? __assert_rtn(__func__, "typeobject.c", 2530, "PyUnicode_IS_READY(name)") : (void)0), ((PyASCIIObject *)(name))->length) <= 100 &&
        (((type)->tp_flags & ((1L<<19))) != 0)) {

        h = (((unsigned int)((type)->tp_version_tag) * (unsigned int)(((PyASCIIObject *)(name))->hash)) >> (8*sizeof(unsigned int) - 9));
        if (method_cache[h].version == type->tp_version_tag &&
            method_cache[h].name == name)
            return method_cache[h].value;
    }


    mro = type->tp_mro;




    if (mro == ((void *)0))
        return ((void *)0);

    res = ((void *)0);


    ( ((PyObject*)(mro))->ob_refcnt++);
    (__builtin_expect(!(((((((PyObject*)(mro))->ob_type))->tp_flags & ((1L<<26))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 2552, "PyTuple_Check(mro)") : (void)0);
    n = (((PyVarObject*)(mro))->ob_size);
    for (i = 0; i < n; i++) {
        base = (((PyTupleObject *)(mro))->ob_item[i]);
        (__builtin_expect(!(((((((PyObject*)(base))->ob_type))->tp_flags & ((1L<<31))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 2556, "PyType_Check(base)") : (void)0);
        dict = ((PyTypeObject *)base)->tp_dict;
        (__builtin_expect(!(dict && ((((((PyObject*)(dict))->ob_type))->tp_flags & ((1L<<29))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 2558, "dict && PyDict_Check(dict)") : (void)0);
        res = PyDict_GetItem(dict, name);
        if (res != ((void *)0))
            break;
    }
    do { if ( --((PyObject*)(mro))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(mro)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(mro)))); } while (0);

    if (((((PyObject*)(name))->ob_type) == &PyUnicode_Type) && ((__builtin_expect(!(((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 2565, "PyUnicode_Check(name)") : (void)0), ((((PyASCIIObject*)name)->state.ready) ? 0 : _PyUnicode_Ready((PyObject *)(name)))) != -1 && ((__builtin_expect(!(((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 2565, "PyUnicode_Check(name)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)name)->state.ready)), 0) ? __assert_rtn(__func__, "typeobject.c", 2565, "PyUnicode_IS_READY(name)") : (void)0), ((PyASCIIObject *)(name))->length) <= 100 && assign_version_tag(type)) {
        h = (((unsigned int)((type)->tp_version_tag) * (unsigned int)(((PyASCIIObject *)(name))->hash)) >> (8*sizeof(unsigned int) - 9));
        method_cache[h].version = type->tp_version_tag;
        method_cache[h].value = res;
        ( ((PyObject*)(name))->ob_refcnt++);
        do { if ( --((PyObject*)(method_cache[h].name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(method_cache[h].name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(method_cache[h].name)))); } while (0);
        method_cache[h].name = name;
    }
    return res;
}

static PyObject *
_PyType_LookupId(PyTypeObject *type, struct _Py_Identifier *name)
{
    PyObject *oname;
    oname = _PyUnicode_FromId(name);
    if (oname == ((void *)0))
        return ((void *)0);
    return _PyType_Lookup(type, oname);
}



static PyObject *
type_getattro(PyTypeObject *type, PyObject *name)
{
    PyTypeObject *metatype = (((PyObject*)(type))->ob_type);
    PyObject *meta_attribute, *attribute;
    descrgetfunc meta_get;

    if (!((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        PyErr_Format(PyExc_TypeError,
                     "attribute name must be string, not '%.200s'",
                     name->ob_type->tp_name);
        return ((void *)0);
    }


    if (type->tp_dict == ((void *)0)) {
        if (PyType_Ready(type) < 0)
            return ((void *)0);
    }


    meta_get = ((void *)0);


    meta_attribute = _PyType_Lookup(metatype, name);

    if (meta_attribute != ((void *)0)) {
        meta_get = (((PyObject*)(meta_attribute))->ob_type)->tp_descr_get;

        if (meta_get != ((void *)0) && ((((PyObject*)(meta_attribute))->ob_type)->tp_descr_set != ((void *)0))) {




            return meta_get(meta_attribute, (PyObject *)type,
                            (PyObject *)metatype);
        }
        ( ((PyObject*)(meta_attribute))->ob_refcnt++);
    }



    attribute = _PyType_Lookup(type, name);
    if (attribute != ((void *)0)) {

        descrgetfunc local_get = (((PyObject*)(attribute))->ob_type)->tp_descr_get;

        do { if ((meta_attribute) == ((void *)0)) ; else do { if ( --((PyObject*)(meta_attribute))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(meta_attribute)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(meta_attribute)))); } while (0); } while (0);

        if (local_get != ((void *)0)) {


            return local_get(attribute, (PyObject *)((void *)0),
                             (PyObject *)type);
        }

        ( ((PyObject*)(attribute))->ob_refcnt++);
        return attribute;
    }



    if (meta_get != ((void *)0)) {
        PyObject *res;
        res = meta_get(meta_attribute, (PyObject *)type,
                       (PyObject *)metatype);
        do { if ( --((PyObject*)(meta_attribute))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(meta_attribute)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(meta_attribute)))); } while (0);
        return res;
    }


    if (meta_attribute != ((void *)0)) {
        return meta_attribute;
    }


    PyErr_Format(PyExc_AttributeError,
                 "type object '%.50s' has no attribute '%U'",
                 type->tp_name, name);
    return ((void *)0);
}

static int
type_setattro(PyTypeObject *type, PyObject *name, PyObject *value)
{
    if (!(type->tp_flags & (1L<<9))) {
        PyErr_Format(
            PyExc_TypeError,
            "can't set attributes of built-in/extension type '%s'",
            type->tp_name);
        return -1;
    }
    if (PyObject_GenericSetAttr((PyObject *)type, name, value) < 0)
        return -1;
    return update_slot(type, name);
}

extern void
_PyDictKeys_DecRef(PyDictKeysObject *keys);

static void
type_dealloc(PyTypeObject *type)
{
    PyHeapTypeObject *et;


    (__builtin_expect(!(type->tp_flags & (1L<<9)), 0) ? __assert_rtn(__func__, "typeobject.c", 2694, "type->tp_flags & Py_TPFLAGS_HEAPTYPE") : (void)0);
    do { PyGC_Head *g = ((PyGC_Head *)(type)-1); (__builtin_expect(!(g->gc.gc_refs != (-2)), 0) ? __assert_rtn(__func__, "typeobject.c", 2695, "g->gc.gc_refs != _PyGC_REFS_UNTRACKED") : (void)0); g->gc.gc_refs = (-2); g->gc.gc_prev->gc.gc_next = g->gc.gc_next; g->gc.gc_next->gc.gc_prev = g->gc.gc_prev; g->gc.gc_next = ((void *)0); } while (0);;
    PyObject_ClearWeakRefs((PyObject *)type);
    et = (PyHeapTypeObject *)type;
    do { if ((type->tp_base) == ((void *)0)) ; else do { if ( --((PyObject*)(type->tp_base))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type->tp_base)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type->tp_base)))); } while (0); } while (0);
    do { if ((type->tp_dict) == ((void *)0)) ; else do { if ( --((PyObject*)(type->tp_dict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type->tp_dict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type->tp_dict)))); } while (0); } while (0);
    do { if ((type->tp_bases) == ((void *)0)) ; else do { if ( --((PyObject*)(type->tp_bases))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type->tp_bases)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type->tp_bases)))); } while (0); } while (0);
    do { if ((type->tp_mro) == ((void *)0)) ; else do { if ( --((PyObject*)(type->tp_mro))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type->tp_mro)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type->tp_mro)))); } while (0); } while (0);
    do { if ((type->tp_cache) == ((void *)0)) ; else do { if ( --((PyObject*)(type->tp_cache))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type->tp_cache)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type->tp_cache)))); } while (0); } while (0);
    do { if ((type->tp_subclasses) == ((void *)0)) ; else do { if ( --((PyObject*)(type->tp_subclasses))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(type->tp_subclasses)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(type->tp_subclasses)))); } while (0); } while (0);



    PyObject_Free((char *)type->tp_doc);
    do { if ((et->ht_name) == ((void *)0)) ; else do { if ( --((PyObject*)(et->ht_name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(et->ht_name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(et->ht_name)))); } while (0); } while (0);
    do { if ((et->ht_qualname) == ((void *)0)) ; else do { if ( --((PyObject*)(et->ht_qualname))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(et->ht_qualname)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(et->ht_qualname)))); } while (0); } while (0);
    do { if ((et->ht_slots) == ((void *)0)) ; else do { if ( --((PyObject*)(et->ht_slots))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(et->ht_slots)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(et->ht_slots)))); } while (0); } while (0);
    if (et->ht_cached_keys)
        _PyDictKeys_DecRef(et->ht_cached_keys);
    (((PyObject*)(type))->ob_type)->tp_free((PyObject *)type);
}

static PyObject *
type_subclasses(PyTypeObject *type, PyObject *args_ignored)
{
    PyObject *list, *raw, *ref;
    Py_ssize_t i, n;

    list = PyList_New(0);
    if (list == ((void *)0))
        return ((void *)0);
    raw = type->tp_subclasses;
    if (raw == ((void *)0))
        return list;
    (__builtin_expect(!(((((((PyObject*)(raw))->ob_type))->tp_flags & ((1L<<25))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 2728, "PyList_Check(raw)") : (void)0);
    n = (((PyVarObject*)(raw))->ob_size);
    for (i = 0; i < n; i++) {
        ref = (((PyListObject *)(raw))->ob_item[i]);
        (__builtin_expect(!(((((PyObject*)(ref))->ob_type) == (&_PyWeakref_RefType) || PyType_IsSubtype((((PyObject*)(ref))->ob_type), (&_PyWeakref_RefType)))), 0) ? __assert_rtn(__func__, "typeobject.c", 2732, "PyWeakref_CheckRef(ref)") : (void)0);
        ref = ((((PyObject*)(((PyWeakReference *)(ref))->wr_object))->ob_refcnt) > 0 ? ((PyWeakReference *)(ref))->wr_object : (&_Py_NoneStruct));
        if (ref != (&_Py_NoneStruct)) {
            if (PyList_Append(list, ref) < 0) {
                do { if ( --((PyObject*)(list))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(list)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(list)))); } while (0);
                return ((void *)0);
            }
        }
    }
    return list;
}

static PyObject *
type_prepare(PyObject *self, PyObject *args, PyObject *kwds)
{
    return PyDict_New();
}
# 2758 "typeobject.c"
static int
merge_class_dict(PyObject *dict, PyObject *aclass)
{
    PyObject *classdict;
    PyObject *bases;
    static _Py_Identifier PyId___bases__ = { 0, "__bases__", 0 };

    (__builtin_expect(!(((((((PyObject*)(dict))->ob_type))->tp_flags & ((1L<<29))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 2765, "PyDict_Check(dict)") : (void)0);
    (__builtin_expect(!(aclass), 0) ? __assert_rtn(__func__, "typeobject.c", 2766, "aclass") : (void)0);


    classdict = _PyObject_GetAttrId(aclass, &PyId___dict__);
    if (classdict == ((void *)0))
        PyErr_Clear();
    else {
        int status = PyDict_Update(dict, classdict);
        do { if ( --((PyObject*)(classdict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(classdict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(classdict)))); } while (0);
        if (status < 0)
            return -1;
    }


    bases = _PyObject_GetAttrId(aclass, &PyId___bases__);
    if (bases == ((void *)0))
        PyErr_Clear();
    else {

        Py_ssize_t i, n;
        n = PySequence_Size(bases);
        if (n < 0)
            PyErr_Clear();
        else {
            for (i = 0; i < n; i++) {
                int status;
                PyObject *base = PySequence_GetItem(bases, i);
                if (base == ((void *)0)) {
                    do { if ( --((PyObject*)(bases))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(bases)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(bases)))); } while (0);
                    return -1;
                }
                status = merge_class_dict(dict, base);
                do { if ( --((PyObject*)(base))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(base)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(base)))); } while (0);
                if (status < 0) {
                    do { if ( --((PyObject*)(bases))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(bases)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(bases)))); } while (0);
                    return -1;
                }
            }
        }
        do { if ( --((PyObject*)(bases))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(bases)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(bases)))); } while (0);
    }
    return 0;
}





static PyObject *
type_dir(PyObject *self, PyObject *args)
{
    PyObject *result = ((void *)0);
    PyObject *dict = PyDict_New();

    if (dict != ((void *)0) && merge_class_dict(dict, self) == 0)
        result = PyDict_Keys(dict);

    do { if ((dict) == ((void *)0)) ; else do { if ( --((PyObject*)(dict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dict)))); } while (0); } while (0);
    return result;
}

static PyObject*
type_sizeof(PyObject *self, PyObject *args_unused)
{
    Py_ssize_t size;
    PyTypeObject *type = (PyTypeObject*)self;
    if (type->tp_flags & (1L<<9)) {
        PyHeapTypeObject* et = (PyHeapTypeObject*)type;
        size = sizeof(PyHeapTypeObject);
        if (et->ht_cached_keys)
            size += _PyDict_KeysSize(et->ht_cached_keys);
    }
    else
        size = sizeof(PyTypeObject);
    return PyLong_FromSsize_t(size);
}

static PyMethodDef type_methods[] = {
    {"mro", (PyCFunction)mro_external, 0x0004,
     "mro() -> list\nreturn a type's method resolution order"},
    {"__subclasses__", (PyCFunction)type_subclasses, 0x0004,
     "__subclasses__() -> list of immediate subclasses"},
    {"__prepare__", (PyCFunction)type_prepare,
     0x0001 | 0x0002 | 0x0010,
     "__prepare__() -> dict\n" "used to create the namespace for the class statement"},

    {"__instancecheck__", type___instancecheck__, 0x0008,
     "__instancecheck__() -> bool\ncheck if an object is an instance"},
    {"__subclasscheck__", type___subclasscheck__, 0x0008,
     "__subclasscheck__() -> bool\ncheck if a class is a subclass"},
    {"__dir__", type_dir, 0x0004,
     "__dir__() -> list\nspecialized __dir__ implementation for types"},
    {"__sizeof__", type_sizeof, 0x0004,
     "__sizeof__() -> int\nreturn memory consumption of the type object"},
    {0}
};

static char type_doc[] = "type(object) -> the object's type\n" "type(name, bases, dict) -> a new type";



static int
type_traverse(PyTypeObject *type, visitproc visit, void *arg)
{


    if (!(type->tp_flags & (1L<<9))) {
        char msg[200];
        __builtin___sprintf_chk (msg, 0, __builtin_object_size (msg, 2 > 1), "type_traverse() called for non-heap type '%.100s'", type->tp_name);

        Py_FatalError(msg);
    }

    do { if (type->tp_dict) { int vret = visit((PyObject *)(type->tp_dict), arg); if (vret) return vret; } } while (0);
    do { if (type->tp_cache) { int vret = visit((PyObject *)(type->tp_cache), arg); if (vret) return vret; } } while (0);
    do { if (type->tp_mro) { int vret = visit((PyObject *)(type->tp_mro), arg); if (vret) return vret; } } while (0);
    do { if (type->tp_bases) { int vret = visit((PyObject *)(type->tp_bases), arg); if (vret) return vret; } } while (0);
    do { if (type->tp_base) { int vret = visit((PyObject *)(type->tp_base), arg); if (vret) return vret; } } while (0);






    return 0;
}

static int
type_clear(PyTypeObject *type)
{
    PyDictKeysObject *cached_keys;


    (__builtin_expect(!(type->tp_flags & (1L<<9)), 0) ? __assert_rtn(__func__, "typeobject.c", 2899, "type->tp_flags & Py_TPFLAGS_HEAPTYPE") : (void)0);
# 2927 "typeobject.c"
    PyType_Modified(type);
    cached_keys = ((PyHeapTypeObject *)type)->ht_cached_keys;
    if (cached_keys != ((void *)0)) {
        ((PyHeapTypeObject *)type)->ht_cached_keys = ((void *)0);
        _PyDictKeys_DecRef(cached_keys);
    }
    if (type->tp_dict)
        PyDict_Clear(type->tp_dict);
    do { if (type->tp_mro) { PyObject *_py_tmp = (PyObject *)(type->tp_mro); (type->tp_mro) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);

    return 0;
}

static int
type_is_gc(PyTypeObject *type)
{
    return type->tp_flags & (1L<<9);
}

PyTypeObject PyType_Type = {
    { { 1, &PyType_Type }, 0 },
    "type",
    sizeof(PyHeapTypeObject),
    sizeof(PyMemberDef),
    (destructor)type_dealloc,
    0,
    0,
    0,
    0,
    (reprfunc)type_repr,
    0,
    0,
    0,
    0,
    (ternaryfunc)type_call,
    0,
    (getattrofunc)type_getattro,
    (setattrofunc)type_setattro,
    0,
    ( 0 | (1L<<18) | 0) | (1L<<14) |
        (1L<<10) | (1L<<31),
    type_doc,
    (traverseproc)type_traverse,
    (inquiry)type_clear,
    0,
    __builtin_offsetof (PyTypeObject, tp_weaklist),
    0,
    0,
    type_methods,
    type_members,
    type_getsets,
    0,
    0,
    0,
    0,
    __builtin_offsetof (PyTypeObject, tp_dict),
    type_init,
    0,
    type_new,
    PyObject_GC_Del,
    (inquiry)type_is_gc,
};
# 3034 "typeobject.c"
static PyObject *
object_new(PyTypeObject *type, PyObject *args, PyObject *kwds);

static int
excess_args(PyObject *args, PyObject *kwds)
{
    return (((PyVarObject*)(args))->ob_size) ||
        (kwds && ((((((PyObject*)(kwds))->ob_type))->tp_flags & ((1L<<29))) != 0) && PyDict_Size(kwds));
}

static int
object_init(PyObject *self, PyObject *args, PyObject *kwds)
{
    int err = 0;
    PyTypeObject *type = (((PyObject*)(self))->ob_type);
    if (excess_args(args, kwds) &&
        (type->tp_new == object_new || type->tp_init != object_init)) {
        PyErr_SetString(PyExc_TypeError, "object.__init__() takes no parameters");
        err = -1;
    }
    return err;
}

static PyObject *
object_new(PyTypeObject *type, PyObject *args, PyObject *kwds)
{
    if (excess_args(args, kwds) &&
        (type->tp_init == object_init || type->tp_new != object_new)) {
        PyErr_SetString(PyExc_TypeError, "object() takes no parameters");
        return ((void *)0);
    }

    if (type->tp_flags & (1L<<20)) {
        PyObject *abstract_methods = ((void *)0);
        PyObject *builtins;
        PyObject *sorted;
        PyObject *sorted_methods = ((void *)0);
        PyObject *joined = ((void *)0);
        PyObject *comma;
        static _Py_Identifier comma_id = { 0, ", ", 0 };
        static _Py_Identifier PyId_sorted = { 0, "sorted", 0 };



        abstract_methods = type_abstractmethods(type, ((void *)0));
        if (abstract_methods == ((void *)0))
            goto error;
        builtins = PyEval_GetBuiltins();
        if (builtins == ((void *)0))
            goto error;
        sorted = _PyDict_GetItemId(builtins, &PyId_sorted);
        if (sorted == ((void *)0))
            goto error;
        sorted_methods = PyObject_CallFunctionObjArgs(sorted,
                                                      abstract_methods,
                                                      ((void *)0));
        if (sorted_methods == ((void *)0))
            goto error;
        comma = _PyUnicode_FromId(&comma_id);
        if (comma == ((void *)0))
            goto error;
        joined = PyUnicode_Join(comma, sorted_methods);
        if (joined == ((void *)0))
            goto error;

        PyErr_Format(PyExc_TypeError,
                     "Can't instantiate abstract class %s "
                     "with abstract methods %U",
                     type->tp_name,
                     joined);
    error:
        do { if ((joined) == ((void *)0)) ; else do { if ( --((PyObject*)(joined))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(joined)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(joined)))); } while (0); } while (0);
        do { if ((sorted_methods) == ((void *)0)) ; else do { if ( --((PyObject*)(sorted_methods))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sorted_methods)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sorted_methods)))); } while (0); } while (0);
        do { if ((abstract_methods) == ((void *)0)) ; else do { if ( --((PyObject*)(abstract_methods))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(abstract_methods)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(abstract_methods)))); } while (0); } while (0);
        return ((void *)0);
    }
    return type->tp_alloc(type, 0);
}

static void
object_dealloc(PyObject *self)
{
    (((PyObject*)(self))->ob_type)->tp_free(self);
}

static PyObject *
object_repr(PyObject *self)
{
    PyTypeObject *type;
    PyObject *mod, *name, *rtn;

    type = (((PyObject*)(self))->ob_type);
    mod = type_module(type, ((void *)0));
    if (mod == ((void *)0))
        PyErr_Clear();
    else if (!((((((PyObject*)(mod))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        do { if ( --((PyObject*)(mod))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(mod)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(mod)))); } while (0);
        mod = ((void *)0);
    }
    name = type_qualname(type, ((void *)0));
    if (name == ((void *)0)) {
        do { if ((mod) == ((void *)0)) ; else do { if ( --((PyObject*)(mod))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(mod)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(mod)))); } while (0); } while (0);
        return ((void *)0);
    }
    if (mod != ((void *)0) && PyUnicode_CompareWithASCIIString(mod, "builtins"))
        rtn = PyUnicode_FromFormat("<%U.%U object at %p>", mod, name, self);
    else
        rtn = PyUnicode_FromFormat("<%s object at %p>",
                                  type->tp_name, self);
    do { if ((mod) == ((void *)0)) ; else do { if ( --((PyObject*)(mod))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(mod)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(mod)))); } while (0); } while (0);
    do { if ( --((PyObject*)(name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(name)))); } while (0);
    return rtn;
}

static PyObject *
object_str(PyObject *self)
{
    unaryfunc f;

    f = (((PyObject*)(self))->ob_type)->tp_repr;
    if (f == ((void *)0))
        f = object_repr;
    return f(self);
}

static PyObject *
object_richcompare(PyObject *self, PyObject *other, int op)
{
    PyObject *res;

    switch (op) {

    case 2:



        res = (self == other) ? ((PyObject *) &_Py_TrueStruct) : (&_Py_NotImplementedStruct);
        ( ((PyObject*)(res))->ob_refcnt++);
        break;

    case 3:


        res = PyObject_RichCompare(self, other, 2);
        if (res != ((void *)0) && res != (&_Py_NotImplementedStruct)) {
            int ok = PyObject_IsTrue(res);
            do { if ( --((PyObject*)(res))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(res)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(res)))); } while (0);
            if (ok < 0)
                res = ((void *)0);
            else {
                if (ok)
                    res = ((PyObject *) &_Py_FalseStruct);
                else
                    res = ((PyObject *) &_Py_TrueStruct);
                ( ((PyObject*)(res))->ob_refcnt++);
            }
        }
        break;

    default:
        res = (&_Py_NotImplementedStruct);
        ( ((PyObject*)(res))->ob_refcnt++);
        break;
    }

    return res;
}

static PyObject *
object_get_class(PyObject *self, void *closure)
{
    ( ((PyObject*)((((PyObject*)(self))->ob_type)))->ob_refcnt++);
    return (PyObject *)((((PyObject*)(self))->ob_type));
}

static int
equiv_structs(PyTypeObject *a, PyTypeObject *b)
{
    return a == b ||
           (a != ((void *)0) &&
        b != ((void *)0) &&
        a->tp_basicsize == b->tp_basicsize &&
        a->tp_itemsize == b->tp_itemsize &&
        a->tp_dictoffset == b->tp_dictoffset &&
        a->tp_weaklistoffset == b->tp_weaklistoffset &&
        ((a->tp_flags & (1L<<14)) ==
         (b->tp_flags & (1L<<14))));
}

static int
same_slots_added(PyTypeObject *a, PyTypeObject *b)
{
    PyTypeObject *base = a->tp_base;
    Py_ssize_t size;
    PyObject *slots_a, *slots_b;

    (__builtin_expect(!(base == b->tp_base), 0) ? __assert_rtn(__func__, "typeobject.c", 3230, "base == b->tp_base") : (void)0);
    size = base->tp_basicsize;
    if (a->tp_dictoffset == size && b->tp_dictoffset == size)
        size += sizeof(PyObject *);
    if (a->tp_weaklistoffset == size && b->tp_weaklistoffset == size)
        size += sizeof(PyObject *);


    slots_a = ((PyHeapTypeObject *)a)->ht_slots;
    slots_b = ((PyHeapTypeObject *)b)->ht_slots;
    if (slots_a && slots_b) {
        if (PyObject_RichCompareBool(slots_a, slots_b, 2) != 1)
            return 0;
        size += sizeof(PyObject *) * (((PyVarObject*)(slots_a))->ob_size);
    }
    return size == a->tp_basicsize && size == b->tp_basicsize;
}

static int
compatible_for_assignment(PyTypeObject* oldto, PyTypeObject* newto, char* attr)
{
    PyTypeObject *newbase, *oldbase;

    if (newto->tp_dealloc != oldto->tp_dealloc ||
        newto->tp_free != oldto->tp_free)
    {
        PyErr_Format(PyExc_TypeError,
                     "%s assignment: "
                     "'%s' deallocator differs from '%s'",
                     attr,
                     newto->tp_name,
                     oldto->tp_name);
        return 0;
    }
    newbase = newto;
    oldbase = oldto;
    while (equiv_structs(newbase, newbase->tp_base))
        newbase = newbase->tp_base;
    while (equiv_structs(oldbase, oldbase->tp_base))
        oldbase = oldbase->tp_base;
    if (newbase != oldbase &&
        (newbase->tp_base != oldbase->tp_base ||
         !same_slots_added(newbase, oldbase))) {
        PyErr_Format(PyExc_TypeError,
                     "%s assignment: "
                     "'%s' object layout differs from '%s'",
                     attr,
                     newto->tp_name,
                     oldto->tp_name);
        return 0;
    }

    return 1;
}

static int
object_set_class(PyObject *self, PyObject *value, void *closure)
{
    PyTypeObject *oldto = (((PyObject*)(self))->ob_type);
    PyTypeObject *newto;

    if (value == ((void *)0)) {
        PyErr_SetString(PyExc_TypeError,
                        "can't delete __class__ attribute");
        return -1;
    }
    if (!((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<31))) != 0)) {
        PyErr_Format(PyExc_TypeError,
          "__class__ must be set to a class, not '%s' object",
          (((PyObject*)(value))->ob_type)->tp_name);
        return -1;
    }
    newto = (PyTypeObject *)value;
    if (!(newto->tp_flags & (1L<<9)) ||
        !(oldto->tp_flags & (1L<<9)))
    {
        PyErr_Format(PyExc_TypeError,
                     "__class__ assignment: only for heap types");
        return -1;
    }
    if (compatible_for_assignment(newto, oldto, "__class__")) {
        ( ((PyObject*)(newto))->ob_refcnt++);
        (((PyObject*)(self))->ob_type) = newto;
        do { if ( --((PyObject*)(oldto))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(oldto)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(oldto)))); } while (0);
        return 0;
    }
    else {
        return -1;
    }
}

static PyGetSetDef object_getsets[] = {
    {"__class__", object_get_class, object_set_class,
     "the object's class"},
    {0}
};
# 3335 "typeobject.c"
static PyObject *
import_copyreg(void)
{
    static PyObject *copyreg_str;
    static PyObject *mod_copyreg = ((void *)0);

    if (!copyreg_str) {
        copyreg_str = PyUnicode_InternFromString("copyreg");
        if (copyreg_str == ((void *)0))
            return ((void *)0);
    }
    if (!mod_copyreg) {
        mod_copyreg = PyImport_Import(copyreg_str);
    }

    do { if ((mod_copyreg) == ((void *)0)) ; else ( ((PyObject*)(mod_copyreg))->ob_refcnt++); } while (0);
    return mod_copyreg;
}

static PyObject *
slotnames(PyObject *cls)
{
    PyObject *clsdict;
    PyObject *copyreg;
    PyObject *slotnames;
    static _Py_Identifier PyId___slotnames__ = { 0, "__slotnames__", 0 };
    static _Py_Identifier PyId__slotnames = { 0, "_slotnames", 0 };

    clsdict = ((PyTypeObject *)cls)->tp_dict;
    slotnames = _PyDict_GetItemId(clsdict, &PyId___slotnames__);
    if (slotnames != ((void *)0) && ((((((PyObject*)(slotnames))->ob_type))->tp_flags & ((1L<<25))) != 0)) {
        ( ((PyObject*)(slotnames))->ob_refcnt++);
        return slotnames;
    }

    copyreg = import_copyreg();
    if (copyreg == ((void *)0))
        return ((void *)0);

    slotnames = _PyObject_CallMethodId(copyreg, &PyId__slotnames, "O", cls);
    do { if ( --((PyObject*)(copyreg))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(copyreg)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(copyreg)))); } while (0);
    if (slotnames != ((void *)0) &&
        slotnames != (&_Py_NoneStruct) &&
        !((((((PyObject*)(slotnames))->ob_type))->tp_flags & ((1L<<25))) != 0))
    {
        PyErr_SetString(PyExc_TypeError,
            "copyreg._slotnames didn't return a list or None");
        do { if ( --((PyObject*)(slotnames))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(slotnames)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(slotnames)))); } while (0);
        slotnames = ((void *)0);
    }

    return slotnames;
}

static PyObject *
reduce_2(PyObject *obj)
{
    PyObject *cls, *getnewargs;
    PyObject *args = ((void *)0), *args2 = ((void *)0);
    PyObject *getstate = ((void *)0), *state = ((void *)0), *names = ((void *)0);
    PyObject *slots = ((void *)0), *listitems = ((void *)0), *dictitems = ((void *)0);
    PyObject *copyreg = ((void *)0), *newobj = ((void *)0), *res = ((void *)0);
    Py_ssize_t i, n;
    static _Py_Identifier PyId___getnewargs__ = { 0, "__getnewargs__", 0 };
    static _Py_Identifier PyId___getstate__ = { 0, "__getstate__", 0 };
    static _Py_Identifier PyId___newobj__ = { 0, "__newobj__", 0 };

    cls = (PyObject *) (((PyObject*)(obj))->ob_type);

    getnewargs = _PyObject_GetAttrId(obj, &PyId___getnewargs__);
    if (getnewargs != ((void *)0)) {
        args = PyObject_CallObject(getnewargs, ((void *)0));
        do { if ( --((PyObject*)(getnewargs))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(getnewargs)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(getnewargs)))); } while (0);
        if (args != ((void *)0) && !((((((PyObject*)(args))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
            PyErr_Format(PyExc_TypeError,
                "__getnewargs__ should return a tuple, "
                "not '%.200s'", (((PyObject*)(args))->ob_type)->tp_name);
            goto end;
        }
    }
    else {
        PyErr_Clear();
        args = PyTuple_New(0);
    }
    if (args == ((void *)0))
        goto end;

    getstate = _PyObject_GetAttrId(obj, &PyId___getstate__);
    if (getstate != ((void *)0)) {
        state = PyObject_CallObject(getstate, ((void *)0));
        do { if ( --((PyObject*)(getstate))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(getstate)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(getstate)))); } while (0);
        if (state == ((void *)0))
            goto end;
    }
    else {
        PyObject **dict;
        PyErr_Clear();
        dict = _PyObject_GetDictPtr(obj);
        if (dict && *dict)
            state = *dict;
        else
            state = (&_Py_NoneStruct);
        ( ((PyObject*)(state))->ob_refcnt++);
        names = slotnames(cls);
        if (names == ((void *)0))
            goto end;
        if (names != (&_Py_NoneStruct) && (((PyVarObject*)(names))->ob_size) > 0) {
            (__builtin_expect(!(((((((PyObject*)(names))->ob_type))->tp_flags & ((1L<<25))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 3442, "PyList_Check(names)") : (void)0);
            slots = PyDict_New();
            if (slots == ((void *)0))
                goto end;
            n = 0;



            for (i = 0; i < (((PyVarObject*)(names))->ob_size); i++) {
                PyObject *name, *value;
                name = (((PyListObject *)(names))->ob_item[i]);
                value = PyObject_GetAttr(obj, name);
                if (value == ((void *)0))
                    PyErr_Clear();
                else {
                    int err = PyDict_SetItem(slots, name,
                                             value);
                    do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0);
                    if (err)
                        goto end;
                    n++;
                }
            }
            if (n) {
                state = Py_BuildValue("(NO)", state, slots);
                if (state == ((void *)0))
                    goto end;
            }
        }
    }

    if (!((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<25))) != 0)) {
        listitems = (&_Py_NoneStruct);
        ( ((PyObject*)(listitems))->ob_refcnt++);
    }
    else {
        listitems = PyObject_GetIter(obj);
        if (listitems == ((void *)0))
            goto end;
    }

    if (!((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<29))) != 0)) {
        dictitems = (&_Py_NoneStruct);
        ( ((PyObject*)(dictitems))->ob_refcnt++);
    }
    else {
        static _Py_Identifier PyId_items = { 0, "items", 0 };
        PyObject *items = _PyObject_CallMethodId(obj, &PyId_items, "");
        if (items == ((void *)0))
            goto end;
        dictitems = PyObject_GetIter(items);
        do { if ( --((PyObject*)(items))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(items)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(items)))); } while (0);
        if (dictitems == ((void *)0))
            goto end;
    }

    copyreg = import_copyreg();
    if (copyreg == ((void *)0))
        goto end;
    newobj = _PyObject_GetAttrId(copyreg, &PyId___newobj__);
    if (newobj == ((void *)0))
        goto end;

    n = (((PyVarObject*)(args))->ob_size);
    args2 = PyTuple_New(n+1);
    if (args2 == ((void *)0))
        goto end;
    ( ((PyObject*)(cls))->ob_refcnt++);
    (((PyTupleObject *)(args2))->ob_item[0] = cls);
    for (i = 0; i < n; i++) {
        PyObject *v = (((PyTupleObject *)(args))->ob_item[i]);
        ( ((PyObject*)(v))->ob_refcnt++);
        (((PyTupleObject *)(args2))->ob_item[i+1] = v);
    }

    res = PyTuple_Pack(5, newobj, args2, state, listitems, dictitems);

  end:
    do { if ((args) == ((void *)0)) ; else do { if ( --((PyObject*)(args))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(args)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(args)))); } while (0); } while (0);
    do { if ((args2) == ((void *)0)) ; else do { if ( --((PyObject*)(args2))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(args2)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(args2)))); } while (0); } while (0);
    do { if ((slots) == ((void *)0)) ; else do { if ( --((PyObject*)(slots))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(slots)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(slots)))); } while (0); } while (0);
    do { if ((state) == ((void *)0)) ; else do { if ( --((PyObject*)(state))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(state)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(state)))); } while (0); } while (0);
    do { if ((names) == ((void *)0)) ; else do { if ( --((PyObject*)(names))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(names)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(names)))); } while (0); } while (0);
    do { if ((listitems) == ((void *)0)) ; else do { if ( --((PyObject*)(listitems))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(listitems)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(listitems)))); } while (0); } while (0);
    do { if ((dictitems) == ((void *)0)) ; else do { if ( --((PyObject*)(dictitems))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dictitems)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dictitems)))); } while (0); } while (0);
    do { if ((copyreg) == ((void *)0)) ; else do { if ( --((PyObject*)(copyreg))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(copyreg)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(copyreg)))); } while (0); } while (0);
    do { if ((newobj) == ((void *)0)) ; else do { if ( --((PyObject*)(newobj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(newobj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(newobj)))); } while (0); } while (0);
    return res;
}
# 3547 "typeobject.c"
static PyObject *
_common_reduce(PyObject *self, int proto)
{
    PyObject *copyreg, *res;

    if (proto >= 2)
        return reduce_2(self);

    copyreg = import_copyreg();
    if (!copyreg)
        return ((void *)0);

    res = PyEval_CallMethod(copyreg, "_reduce_ex", "(Oi)", self, proto);
    do { if ( --((PyObject*)(copyreg))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(copyreg)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(copyreg)))); } while (0);

    return res;
}

static PyObject *
object_reduce(PyObject *self, PyObject *args)
{
    int proto = 0;

    if (!PyArg_ParseTuple(args, "|i:__reduce__", &proto))
        return ((void *)0);

    return _common_reduce(self, proto);
}

static PyObject *
object_reduce_ex(PyObject *self, PyObject *args)
{
    static PyObject *objreduce;
    PyObject *reduce, *res;
    int proto = 0;
    static _Py_Identifier PyId___reduce__ = { 0, "__reduce__", 0 };

    if (!PyArg_ParseTuple(args, "|i:__reduce_ex__", &proto))
        return ((void *)0);

    if (objreduce == ((void *)0)) {
        objreduce = _PyDict_GetItemId(PyBaseObject_Type.tp_dict,
                                      &PyId___reduce__);
        if (objreduce == ((void *)0))
            return ((void *)0);
    }

    reduce = _PyObject_GetAttrId(self, &PyId___reduce__);
    if (reduce == ((void *)0))
        PyErr_Clear();
    else {
        PyObject *cls, *clsreduce;
        int override;

        cls = (PyObject *) (((PyObject*)(self))->ob_type);
        clsreduce = _PyObject_GetAttrId(cls, &PyId___reduce__);
        if (clsreduce == ((void *)0)) {
            do { if ( --((PyObject*)(reduce))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(reduce)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(reduce)))); } while (0);
            return ((void *)0);
        }
        override = (clsreduce != objreduce);
        do { if ( --((PyObject*)(clsreduce))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(clsreduce)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(clsreduce)))); } while (0);
        if (override) {
            res = PyObject_CallObject(reduce, ((void *)0));
            do { if ( --((PyObject*)(reduce))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(reduce)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(reduce)))); } while (0);
            return res;
        }
        else
            do { if ( --((PyObject*)(reduce))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(reduce)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(reduce)))); } while (0);
    }

    return _common_reduce(self, proto);
}

static PyObject *
object_subclasshook(PyObject *cls, PyObject *args)
{
    return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct);
}

static char object_subclasshook_doc[] = "Abstract classes can override this to customize issubclass().\n" "\n" "This is invoked early on by abc.ABCMeta.__subclasscheck__().\n" "It should return True, False or NotImplemented.  If it returns\n" "NotImplemented, the normal algorithm is used.  Otherwise, it\n" "overrides the normal algorithm (and the outcome is cached).\n";
# 3642 "typeobject.c"
static PyObject *
object_format(PyObject *self, PyObject *args)
{
    PyObject *format_spec;
    PyObject *self_as_str = ((void *)0);
    PyObject *result = ((void *)0);

    if (!PyArg_ParseTuple(args, "U:__format__", &format_spec))
        return ((void *)0);

    self_as_str = PyObject_Str(self);
    if (self_as_str != ((void *)0)) {


        if (((__builtin_expect(!(((((((PyObject*)(format_spec))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 3656, "PyUnicode_Check(format_spec)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)format_spec)->state.ready)), 0) ? __assert_rtn(__func__, "typeobject.c", 3656, "PyUnicode_IS_READY(format_spec)") : (void)0), ((PyASCIIObject *)(format_spec))->length) > 0) {
            if (PyErr_WarnEx(PyExc_DeprecationWarning,
                             "object.__format__ with a non-empty format "
                             "string is deprecated", 1) < 0) {
              goto done;
            }





        }

        result = PyObject_Format(self_as_str, format_spec);
    }

done:
    do { if ((self_as_str) == ((void *)0)) ; else do { if ( --((PyObject*)(self_as_str))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self_as_str)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self_as_str)))); } while (0); } while (0);

    return result;
}

static PyObject *
object_sizeof(PyObject *self, PyObject *args)
{
    Py_ssize_t res, isize;

    res = 0;
    isize = self->ob_type->tp_itemsize;
    if (isize > 0)
        res = (((PyVarObject*)(self->ob_type))->ob_size) * isize;
    res += self->ob_type->tp_basicsize;

    return PyLong_FromSsize_t(res);
}




static PyObject *
object_dir(PyObject *self, PyObject *args)
{
    PyObject *result = ((void *)0);
    PyObject *dict = ((void *)0);
    PyObject *itsclass = ((void *)0);


    dict = _PyObject_GetAttrId(self, &PyId___dict__);
    if (dict == ((void *)0)) {
        PyErr_Clear();
        dict = PyDict_New();
    }
    else if (!((((((PyObject*)(dict))->ob_type))->tp_flags & ((1L<<29))) != 0)) {
        do { if ( --((PyObject*)(dict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dict)))); } while (0);
        dict = PyDict_New();
    }
    else {

        PyObject *temp = PyDict_Copy(dict);
        do { if ( --((PyObject*)(dict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dict)))); } while (0);
        dict = temp;
    }

    if (dict == ((void *)0))
        goto error;


    itsclass = _PyObject_GetAttrId(self, &PyId___class__);
    if (itsclass == ((void *)0))


        PyErr_Clear();
    else if (merge_class_dict(dict, itsclass) != 0)
        goto error;

    result = PyDict_Keys(dict);

error:
    do { if ((itsclass) == ((void *)0)) ; else do { if ( --((PyObject*)(itsclass))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(itsclass)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(itsclass)))); } while (0); } while (0);
    do { if ((dict) == ((void *)0)) ; else do { if ( --((PyObject*)(dict))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dict)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dict)))); } while (0); } while (0);
    return result;
}

static PyMethodDef object_methods[] = {
    {"__reduce_ex__", object_reduce_ex, 0x0001,
     "helper for pickle"},
    {"__reduce__", object_reduce, 0x0001,
     "helper for pickle"},
    {"__subclasshook__", object_subclasshook, 0x0010 | 0x0001,
     object_subclasshook_doc},
    {"__format__", object_format, 0x0001,
     "default object formatter"},
    {"__sizeof__", object_sizeof, 0x0004,
     "__sizeof__() -> int\nsize of object in memory, in bytes"},
    {"__dir__", object_dir, 0x0004,
     "__dir__() -> list\ndefault dir() implementation"},
    {0}
};


PyTypeObject PyBaseObject_Type = {
    { { 1, &PyType_Type }, 0 },
    "object",
    sizeof(PyObject),
    0,
    object_dealloc,
    0,
    0,
    0,
    0,
    object_repr,
    0,
    0,
    0,
    (hashfunc)_Py_HashPointer,
    0,
    object_str,
    PyObject_GenericGetAttr,
    PyObject_GenericSetAttr,
    0,
    ( 0 | (1L<<18) | 0) | (1L<<10),
    "The most base type",
    0,
    0,
    object_richcompare,
    0,
    0,
    0,
    object_methods,
    0,
    object_getsets,
    0,
    0,
    0,
    0,
    0,
    object_init,
    PyType_GenericAlloc,
    object_new,
    PyObject_Free,
};




static int
add_methods(PyTypeObject *type, PyMethodDef *meth)
{
    PyObject *dict = type->tp_dict;

    for (; meth->ml_name != ((void *)0); meth++) {
        PyObject *descr;
        int err;
        if (PyDict_GetItemString(dict, meth->ml_name) &&
            !(meth->ml_flags & 0x0040))
                continue;
        if (meth->ml_flags & 0x0010) {
            if (meth->ml_flags & 0x0020) {
                PyErr_SetString(PyExc_ValueError,
                     "method cannot be both class and static");
                return -1;
            }
            descr = PyDescr_NewClassMethod(type, meth);
        }
        else if (meth->ml_flags & 0x0020) {
            PyObject *cfunc = PyCFunction_NewEx((meth), ((PyObject*)type), ((void *)0));
            if (cfunc == ((void *)0))
                return -1;
            descr = PyStaticMethod_New(cfunc);
            do { if ( --((PyObject*)(cfunc))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(cfunc)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(cfunc)))); } while (0);
        }
        else {
            descr = PyDescr_NewMethod(type, meth);
        }
        if (descr == ((void *)0))
            return -1;
        err = PyDict_SetItemString(dict, meth->ml_name, descr);
        do { if ( --((PyObject*)(descr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(descr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(descr)))); } while (0);
        if (err < 0)
            return -1;
    }
    return 0;
}

static int
add_members(PyTypeObject *type, PyMemberDef *memb)
{
    PyObject *dict = type->tp_dict;

    for (; memb->name != ((void *)0); memb++) {
        PyObject *descr;
        if (PyDict_GetItemString(dict, memb->name))
            continue;
        descr = PyDescr_NewMember(type, memb);
        if (descr == ((void *)0))
            return -1;
        if (PyDict_SetItemString(dict, memb->name, descr) < 0)
            return -1;
        do { if ( --((PyObject*)(descr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(descr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(descr)))); } while (0);
    }
    return 0;
}

static int
add_getset(PyTypeObject *type, PyGetSetDef *gsp)
{
    PyObject *dict = type->tp_dict;

    for (; gsp->name != ((void *)0); gsp++) {
        PyObject *descr;
        if (PyDict_GetItemString(dict, gsp->name))
            continue;
        descr = PyDescr_NewGetSet(type, gsp);

        if (descr == ((void *)0))
            return -1;
        if (PyDict_SetItemString(dict, gsp->name, descr) < 0)
            return -1;
        do { if ( --((PyObject*)(descr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(descr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(descr)))); } while (0);
    }
    return 0;
}

static void
inherit_special(PyTypeObject *type, PyTypeObject *base)
{


    if (!(type->tp_flags & (1L<<14)) &&
        (base->tp_flags & (1L<<14)) &&
        (!type->tp_traverse && !type->tp_clear)) {
        type->tp_flags |= (1L<<14);
        if (type->tp_traverse == ((void *)0))
            type->tp_traverse = base->tp_traverse;
        if (type->tp_clear == ((void *)0))
            type->tp_clear = base->tp_clear;
    }
    {
# 3904 "typeobject.c"
        if (base != &PyBaseObject_Type ||
            (type->tp_flags & (1L<<9))) {
            if (type->tp_new == ((void *)0))
                type->tp_new = base->tp_new;
        }
    }
    if (type->tp_basicsize == 0)
        type->tp_basicsize = base->tp_basicsize;







    if (type->tp_itemsize == 0) type->tp_itemsize = base->tp_itemsize;
    if (type->tp_weaklistoffset == 0) type->tp_weaklistoffset = base->tp_weaklistoffset;
    if (type->tp_dictoffset == 0) type->tp_dictoffset = base->tp_dictoffset;


    if (PyType_IsSubtype(base, (PyTypeObject*)PyExc_BaseException))
        type->tp_flags |= (1L<<30);
    else if (PyType_IsSubtype(base, &PyType_Type))
        type->tp_flags |= (1L<<31);
    else if (PyType_IsSubtype(base, &PyLong_Type))
        type->tp_flags |= (1L<<24);
    else if (PyType_IsSubtype(base, &PyBytes_Type))
        type->tp_flags |= (1L<<27);
    else if (PyType_IsSubtype(base, &PyUnicode_Type))
        type->tp_flags |= (1L<<28);
    else if (PyType_IsSubtype(base, &PyTuple_Type))
        type->tp_flags |= (1L<<26);
    else if (PyType_IsSubtype(base, &PyList_Type))
        type->tp_flags |= (1L<<25);
    else if (PyType_IsSubtype(base, &PyDict_Type))
        type->tp_flags |= (1L<<29);
}

static int
overrides_hash(PyTypeObject *type)
{
    PyObject *dict = type->tp_dict;
    static _Py_Identifier PyId___eq__ = { 0, "__eq__", 0 };

    (__builtin_expect(!(dict != ((void *)0)), 0) ? __assert_rtn(__func__, "typeobject.c", 3948, "dict != NULL") : (void)0);
    if (_PyDict_GetItemId(dict, &PyId___eq__) != ((void *)0))
        return 1;
    if (_PyDict_GetItemId(dict, &PyId___hash__) != ((void *)0))
        return 1;
    return 0;
}

static void
inherit_slots(PyTypeObject *type, PyTypeObject *base)
{
    PyTypeObject *basebase;
# 3983 "typeobject.c"
    if (type->tp_as_number != ((void *)0) && base->tp_as_number != ((void *)0)) {
        basebase = base->tp_base;
        if (basebase->tp_as_number == ((void *)0))
            basebase = ((void *)0);
        if (!type->tp_as_number->nb_add && (base->tp_as_number->nb_add != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_add != basebase->tp_as_number->nb_add))) type->tp_as_number->nb_add = base->tp_as_number->nb_add;
        if (!type->tp_as_number->nb_subtract && (base->tp_as_number->nb_subtract != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_subtract != basebase->tp_as_number->nb_subtract))) type->tp_as_number->nb_subtract = base->tp_as_number->nb_subtract;
        if (!type->tp_as_number->nb_multiply && (base->tp_as_number->nb_multiply != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_multiply != basebase->tp_as_number->nb_multiply))) type->tp_as_number->nb_multiply = base->tp_as_number->nb_multiply;
        if (!type->tp_as_number->nb_remainder && (base->tp_as_number->nb_remainder != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_remainder != basebase->tp_as_number->nb_remainder))) type->tp_as_number->nb_remainder = base->tp_as_number->nb_remainder;
        if (!type->tp_as_number->nb_divmod && (base->tp_as_number->nb_divmod != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_divmod != basebase->tp_as_number->nb_divmod))) type->tp_as_number->nb_divmod = base->tp_as_number->nb_divmod;
        if (!type->tp_as_number->nb_power && (base->tp_as_number->nb_power != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_power != basebase->tp_as_number->nb_power))) type->tp_as_number->nb_power = base->tp_as_number->nb_power;
        if (!type->tp_as_number->nb_negative && (base->tp_as_number->nb_negative != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_negative != basebase->tp_as_number->nb_negative))) type->tp_as_number->nb_negative = base->tp_as_number->nb_negative;
        if (!type->tp_as_number->nb_positive && (base->tp_as_number->nb_positive != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_positive != basebase->tp_as_number->nb_positive))) type->tp_as_number->nb_positive = base->tp_as_number->nb_positive;
        if (!type->tp_as_number->nb_absolute && (base->tp_as_number->nb_absolute != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_absolute != basebase->tp_as_number->nb_absolute))) type->tp_as_number->nb_absolute = base->tp_as_number->nb_absolute;
        if (!type->tp_as_number->nb_bool && (base->tp_as_number->nb_bool != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_bool != basebase->tp_as_number->nb_bool))) type->tp_as_number->nb_bool = base->tp_as_number->nb_bool;
        if (!type->tp_as_number->nb_invert && (base->tp_as_number->nb_invert != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_invert != basebase->tp_as_number->nb_invert))) type->tp_as_number->nb_invert = base->tp_as_number->nb_invert;
        if (!type->tp_as_number->nb_lshift && (base->tp_as_number->nb_lshift != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_lshift != basebase->tp_as_number->nb_lshift))) type->tp_as_number->nb_lshift = base->tp_as_number->nb_lshift;
        if (!type->tp_as_number->nb_rshift && (base->tp_as_number->nb_rshift != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_rshift != basebase->tp_as_number->nb_rshift))) type->tp_as_number->nb_rshift = base->tp_as_number->nb_rshift;
        if (!type->tp_as_number->nb_and && (base->tp_as_number->nb_and != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_and != basebase->tp_as_number->nb_and))) type->tp_as_number->nb_and = base->tp_as_number->nb_and;
        if (!type->tp_as_number->nb_xor && (base->tp_as_number->nb_xor != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_xor != basebase->tp_as_number->nb_xor))) type->tp_as_number->nb_xor = base->tp_as_number->nb_xor;
        if (!type->tp_as_number->nb_or && (base->tp_as_number->nb_or != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_or != basebase->tp_as_number->nb_or))) type->tp_as_number->nb_or = base->tp_as_number->nb_or;
        if (!type->tp_as_number->nb_int && (base->tp_as_number->nb_int != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_int != basebase->tp_as_number->nb_int))) type->tp_as_number->nb_int = base->tp_as_number->nb_int;
        if (!type->tp_as_number->nb_float && (base->tp_as_number->nb_float != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_float != basebase->tp_as_number->nb_float))) type->tp_as_number->nb_float = base->tp_as_number->nb_float;
        if (!type->tp_as_number->nb_inplace_add && (base->tp_as_number->nb_inplace_add != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_inplace_add != basebase->tp_as_number->nb_inplace_add))) type->tp_as_number->nb_inplace_add = base->tp_as_number->nb_inplace_add;
        if (!type->tp_as_number->nb_inplace_subtract && (base->tp_as_number->nb_inplace_subtract != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_inplace_subtract != basebase->tp_as_number->nb_inplace_subtract))) type->tp_as_number->nb_inplace_subtract = base->tp_as_number->nb_inplace_subtract;
        if (!type->tp_as_number->nb_inplace_multiply && (base->tp_as_number->nb_inplace_multiply != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_inplace_multiply != basebase->tp_as_number->nb_inplace_multiply))) type->tp_as_number->nb_inplace_multiply = base->tp_as_number->nb_inplace_multiply;
        if (!type->tp_as_number->nb_inplace_remainder && (base->tp_as_number->nb_inplace_remainder != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_inplace_remainder != basebase->tp_as_number->nb_inplace_remainder))) type->tp_as_number->nb_inplace_remainder = base->tp_as_number->nb_inplace_remainder;
        if (!type->tp_as_number->nb_inplace_power && (base->tp_as_number->nb_inplace_power != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_inplace_power != basebase->tp_as_number->nb_inplace_power))) type->tp_as_number->nb_inplace_power = base->tp_as_number->nb_inplace_power;
        if (!type->tp_as_number->nb_inplace_lshift && (base->tp_as_number->nb_inplace_lshift != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_inplace_lshift != basebase->tp_as_number->nb_inplace_lshift))) type->tp_as_number->nb_inplace_lshift = base->tp_as_number->nb_inplace_lshift;
        if (!type->tp_as_number->nb_inplace_rshift && (base->tp_as_number->nb_inplace_rshift != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_inplace_rshift != basebase->tp_as_number->nb_inplace_rshift))) type->tp_as_number->nb_inplace_rshift = base->tp_as_number->nb_inplace_rshift;
        if (!type->tp_as_number->nb_inplace_and && (base->tp_as_number->nb_inplace_and != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_inplace_and != basebase->tp_as_number->nb_inplace_and))) type->tp_as_number->nb_inplace_and = base->tp_as_number->nb_inplace_and;
        if (!type->tp_as_number->nb_inplace_xor && (base->tp_as_number->nb_inplace_xor != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_inplace_xor != basebase->tp_as_number->nb_inplace_xor))) type->tp_as_number->nb_inplace_xor = base->tp_as_number->nb_inplace_xor;
        if (!type->tp_as_number->nb_inplace_or && (base->tp_as_number->nb_inplace_or != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_inplace_or != basebase->tp_as_number->nb_inplace_or))) type->tp_as_number->nb_inplace_or = base->tp_as_number->nb_inplace_or;
        if (!type->tp_as_number->nb_true_divide && (base->tp_as_number->nb_true_divide != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_true_divide != basebase->tp_as_number->nb_true_divide))) type->tp_as_number->nb_true_divide = base->tp_as_number->nb_true_divide;
        if (!type->tp_as_number->nb_floor_divide && (base->tp_as_number->nb_floor_divide != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_floor_divide != basebase->tp_as_number->nb_floor_divide))) type->tp_as_number->nb_floor_divide = base->tp_as_number->nb_floor_divide;
        if (!type->tp_as_number->nb_inplace_true_divide && (base->tp_as_number->nb_inplace_true_divide != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_inplace_true_divide != basebase->tp_as_number->nb_inplace_true_divide))) type->tp_as_number->nb_inplace_true_divide = base->tp_as_number->nb_inplace_true_divide;
        if (!type->tp_as_number->nb_inplace_floor_divide && (base->tp_as_number->nb_inplace_floor_divide != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_inplace_floor_divide != basebase->tp_as_number->nb_inplace_floor_divide))) type->tp_as_number->nb_inplace_floor_divide = base->tp_as_number->nb_inplace_floor_divide;
        if (!type->tp_as_number->nb_index && (base->tp_as_number->nb_index != 0 && (basebase == ((void *)0) || base->tp_as_number->nb_index != basebase->tp_as_number->nb_index))) type->tp_as_number->nb_index = base->tp_as_number->nb_index;
    }

    if (type->tp_as_sequence != ((void *)0) && base->tp_as_sequence != ((void *)0)) {
        basebase = base->tp_base;
        if (basebase->tp_as_sequence == ((void *)0))
            basebase = ((void *)0);
        if (!type->tp_as_sequence->sq_length && (base->tp_as_sequence->sq_length != 0 && (basebase == ((void *)0) || base->tp_as_sequence->sq_length != basebase->tp_as_sequence->sq_length))) type->tp_as_sequence->sq_length = base->tp_as_sequence->sq_length;
        if (!type->tp_as_sequence->sq_concat && (base->tp_as_sequence->sq_concat != 0 && (basebase == ((void *)0) || base->tp_as_sequence->sq_concat != basebase->tp_as_sequence->sq_concat))) type->tp_as_sequence->sq_concat = base->tp_as_sequence->sq_concat;
        if (!type->tp_as_sequence->sq_repeat && (base->tp_as_sequence->sq_repeat != 0 && (basebase == ((void *)0) || base->tp_as_sequence->sq_repeat != basebase->tp_as_sequence->sq_repeat))) type->tp_as_sequence->sq_repeat = base->tp_as_sequence->sq_repeat;
        if (!type->tp_as_sequence->sq_item && (base->tp_as_sequence->sq_item != 0 && (basebase == ((void *)0) || base->tp_as_sequence->sq_item != basebase->tp_as_sequence->sq_item))) type->tp_as_sequence->sq_item = base->tp_as_sequence->sq_item;
        if (!type->tp_as_sequence->sq_ass_item && (base->tp_as_sequence->sq_ass_item != 0 && (basebase == ((void *)0) || base->tp_as_sequence->sq_ass_item != basebase->tp_as_sequence->sq_ass_item))) type->tp_as_sequence->sq_ass_item = base->tp_as_sequence->sq_ass_item;
        if (!type->tp_as_sequence->sq_contains && (base->tp_as_sequence->sq_contains != 0 && (basebase == ((void *)0) || base->tp_as_sequence->sq_contains != basebase->tp_as_sequence->sq_contains))) type->tp_as_sequence->sq_contains = base->tp_as_sequence->sq_contains;
        if (!type->tp_as_sequence->sq_inplace_concat && (base->tp_as_sequence->sq_inplace_concat != 0 && (basebase == ((void *)0) || base->tp_as_sequence->sq_inplace_concat != basebase->tp_as_sequence->sq_inplace_concat))) type->tp_as_sequence->sq_inplace_concat = base->tp_as_sequence->sq_inplace_concat;
        if (!type->tp_as_sequence->sq_inplace_repeat && (base->tp_as_sequence->sq_inplace_repeat != 0 && (basebase == ((void *)0) || base->tp_as_sequence->sq_inplace_repeat != basebase->tp_as_sequence->sq_inplace_repeat))) type->tp_as_sequence->sq_inplace_repeat = base->tp_as_sequence->sq_inplace_repeat;
    }

    if (type->tp_as_mapping != ((void *)0) && base->tp_as_mapping != ((void *)0)) {
        basebase = base->tp_base;
        if (basebase->tp_as_mapping == ((void *)0))
            basebase = ((void *)0);
        if (!type->tp_as_mapping->mp_length && (base->tp_as_mapping->mp_length != 0 && (basebase == ((void *)0) || base->tp_as_mapping->mp_length != basebase->tp_as_mapping->mp_length))) type->tp_as_mapping->mp_length = base->tp_as_mapping->mp_length;
        if (!type->tp_as_mapping->mp_subscript && (base->tp_as_mapping->mp_subscript != 0 && (basebase == ((void *)0) || base->tp_as_mapping->mp_subscript != basebase->tp_as_mapping->mp_subscript))) type->tp_as_mapping->mp_subscript = base->tp_as_mapping->mp_subscript;
        if (!type->tp_as_mapping->mp_ass_subscript && (base->tp_as_mapping->mp_ass_subscript != 0 && (basebase == ((void *)0) || base->tp_as_mapping->mp_ass_subscript != basebase->tp_as_mapping->mp_ass_subscript))) type->tp_as_mapping->mp_ass_subscript = base->tp_as_mapping->mp_ass_subscript;
    }

    if (type->tp_as_buffer != ((void *)0) && base->tp_as_buffer != ((void *)0)) {
        basebase = base->tp_base;
        if (basebase->tp_as_buffer == ((void *)0))
            basebase = ((void *)0);
        if (!type->tp_as_buffer->bf_getbuffer && (base->tp_as_buffer->bf_getbuffer != 0 && (basebase == ((void *)0) || base->tp_as_buffer->bf_getbuffer != basebase->tp_as_buffer->bf_getbuffer))) type->tp_as_buffer->bf_getbuffer = base->tp_as_buffer->bf_getbuffer;
        if (!type->tp_as_buffer->bf_releasebuffer && (base->tp_as_buffer->bf_releasebuffer != 0 && (basebase == ((void *)0) || base->tp_as_buffer->bf_releasebuffer != basebase->tp_as_buffer->bf_releasebuffer))) type->tp_as_buffer->bf_releasebuffer = base->tp_as_buffer->bf_releasebuffer;
    }

    basebase = base->tp_base;

    if (!type->tp_dealloc && (base->tp_dealloc != 0 && (basebase == ((void *)0) || base->tp_dealloc != basebase->tp_dealloc))) type->tp_dealloc = base->tp_dealloc;
    if (type->tp_getattr == ((void *)0) && type->tp_getattro == ((void *)0)) {
        type->tp_getattr = base->tp_getattr;
        type->tp_getattro = base->tp_getattro;
    }
    if (type->tp_setattr == ((void *)0) && type->tp_setattro == ((void *)0)) {
        type->tp_setattr = base->tp_setattr;
        type->tp_setattro = base->tp_setattro;
    }

    if (!type->tp_repr && (base->tp_repr != 0 && (basebase == ((void *)0) || base->tp_repr != basebase->tp_repr))) type->tp_repr = base->tp_repr;

    if (!type->tp_call && (base->tp_call != 0 && (basebase == ((void *)0) || base->tp_call != basebase->tp_call))) type->tp_call = base->tp_call;
    if (!type->tp_str && (base->tp_str != 0 && (basebase == ((void *)0) || base->tp_str != basebase->tp_str))) type->tp_str = base->tp_str;
    {


        if (type->tp_richcompare == ((void *)0) &&
            type->tp_hash == ((void *)0) &&
            !overrides_hash(type))
        {
            type->tp_richcompare = base->tp_richcompare;
            type->tp_hash = base->tp_hash;
        }
    }
    {
        if (!type->tp_iter && (base->tp_iter != 0 && (basebase == ((void *)0) || base->tp_iter != basebase->tp_iter))) type->tp_iter = base->tp_iter;
        if (!type->tp_iternext && (base->tp_iternext != 0 && (basebase == ((void *)0) || base->tp_iternext != basebase->tp_iternext))) type->tp_iternext = base->tp_iternext;
    }
    {
        if (!type->tp_descr_get && (base->tp_descr_get != 0 && (basebase == ((void *)0) || base->tp_descr_get != basebase->tp_descr_get))) type->tp_descr_get = base->tp_descr_get;
        if (!type->tp_descr_set && (base->tp_descr_set != 0 && (basebase == ((void *)0) || base->tp_descr_set != basebase->tp_descr_set))) type->tp_descr_set = base->tp_descr_set;
        if (!type->tp_dictoffset && (base->tp_dictoffset != 0 && (basebase == ((void *)0) || base->tp_dictoffset != basebase->tp_dictoffset))) type->tp_dictoffset = base->tp_dictoffset;
        if (!type->tp_init && (base->tp_init != 0 && (basebase == ((void *)0) || base->tp_init != basebase->tp_init))) type->tp_init = base->tp_init;
        if (!type->tp_alloc && (base->tp_alloc != 0 && (basebase == ((void *)0) || base->tp_alloc != basebase->tp_alloc))) type->tp_alloc = base->tp_alloc;
        if (!type->tp_is_gc && (base->tp_is_gc != 0 && (basebase == ((void *)0) || base->tp_is_gc != basebase->tp_is_gc))) type->tp_is_gc = base->tp_is_gc;
        if ((type->tp_flags & (1L<<14)) ==
            (base->tp_flags & (1L<<14))) {

            if (!type->tp_free && (base->tp_free != 0 && (basebase == ((void *)0) || base->tp_free != basebase->tp_free))) type->tp_free = base->tp_free;
        }
        else if ((type->tp_flags & (1L<<14)) &&
                 type->tp_free == ((void *)0) &&
                 base->tp_free == PyObject_Free) {





            type->tp_free = PyObject_GC_Del;
        }



    }
}

static int add_operators(PyTypeObject *);

int
PyType_Ready(PyTypeObject *type)
{
    PyObject *dict, *bases;
    PyTypeObject *base;
    Py_ssize_t i, n;

    if (type->tp_flags & (1L<<12)) {
        (__builtin_expect(!(type->tp_dict != ((void *)0)), 0) ? __assert_rtn(__func__, "typeobject.c", 4122, "type->tp_dict != NULL") : (void)0);
        return 0;
    }
    (__builtin_expect(!((type->tp_flags & (1L<<13)) == 0), 0) ? __assert_rtn(__func__, "typeobject.c", 4125, "(type->tp_flags & Py_TPFLAGS_READYING) == 0") : (void)0);

    type->tp_flags |= (1L<<13);
# 4139 "typeobject.c"
    base = type->tp_base;
    if (base == ((void *)0) && type != &PyBaseObject_Type) {
        base = type->tp_base = &PyBaseObject_Type;
        ( ((PyObject*)(base))->ob_refcnt++);
    }






    if (base != ((void *)0) && base->tp_dict == ((void *)0)) {
        if (PyType_Ready(base) < 0)
            goto error;
    }
# 4162 "typeobject.c"
    if ((((PyObject*)(type))->ob_type) == ((void *)0) && base != ((void *)0))
        (((PyObject*)(type))->ob_type) = (((PyObject*)(base))->ob_type);


    bases = type->tp_bases;
    if (bases == ((void *)0)) {
        if (base == ((void *)0))
            bases = PyTuple_New(0);
        else
            bases = PyTuple_Pack(1, base);
        if (bases == ((void *)0))
            goto error;
        type->tp_bases = bases;
    }


    dict = type->tp_dict;
    if (dict == ((void *)0)) {
        dict = PyDict_New();
        if (dict == ((void *)0))
            goto error;
        type->tp_dict = dict;
    }


    if (add_operators(type) < 0)
        goto error;
    if (type->tp_methods != ((void *)0)) {
        if (add_methods(type, type->tp_methods) < 0)
            goto error;
    }
    if (type->tp_members != ((void *)0)) {
        if (add_members(type, type->tp_members) < 0)
            goto error;
    }
    if (type->tp_getset != ((void *)0)) {
        if (add_getset(type, type->tp_getset) < 0)
            goto error;
    }


    if (mro_internal(type) < 0) {
        goto error;
    }


    if (type->tp_base != ((void *)0))
        inherit_special(type, type->tp_base);


    bases = type->tp_mro;
    (__builtin_expect(!(bases != ((void *)0)), 0) ? __assert_rtn(__func__, "typeobject.c", 4213, "bases != NULL") : (void)0);
    (__builtin_expect(!(((((((PyObject*)(bases))->ob_type))->tp_flags & ((1L<<26))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 4214, "PyTuple_Check(bases)") : (void)0);
    n = (((PyVarObject*)(bases))->ob_size);
    for (i = 1; i < n; i++) {
        PyObject *b = (((PyTupleObject *)(bases))->ob_item[i]);
        if (((((((PyObject*)(b))->ob_type))->tp_flags & ((1L<<31))) != 0))
            inherit_slots(type, (PyTypeObject *)b);
    }


    if (((((type))->tp_flags & ((1L<<14))) != 0) && (type->tp_flags & (1L<<10)) &&
        (type->tp_free == ((void *)0) || type->tp_free == PyObject_Free)) {



        PyErr_Format(PyExc_TypeError, "type '%.100s' participates in "
                     "gc and is a base type but has inappropriate "
                     "tp_free slot",
                     type->tp_name);
        goto error;
    }




    if (_PyDict_GetItemId(type->tp_dict, &PyId___doc__) == ((void *)0)) {
        if (type->tp_doc != ((void *)0)) {
            PyObject *doc = PyUnicode_FromString(type->tp_doc);
            if (doc == ((void *)0))
                goto error;
            _PyDict_SetItemId(type->tp_dict, &PyId___doc__, doc);
            do { if ( --((PyObject*)(doc))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(doc)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(doc)))); } while (0);
        } else {
            _PyDict_SetItemId(type->tp_dict,
                              &PyId___doc__, (&_Py_NoneStruct));
        }
    }







    if (type->tp_hash == ((void *)0)) {
        if (_PyDict_GetItemId(type->tp_dict, &PyId___hash__) == ((void *)0)) {
            if (_PyDict_SetItemId(type->tp_dict, &PyId___hash__, (&_Py_NoneStruct)) < 0)
                goto error;
            type->tp_hash = PyObject_HashNotImplemented;
        }
    }


    base = type->tp_base;
    if (base != ((void *)0)) {
        if (type->tp_as_number == ((void *)0))
            type->tp_as_number = base->tp_as_number;
        if (type->tp_as_sequence == ((void *)0))
            type->tp_as_sequence = base->tp_as_sequence;
        if (type->tp_as_mapping == ((void *)0))
            type->tp_as_mapping = base->tp_as_mapping;
        if (type->tp_as_buffer == ((void *)0))
            type->tp_as_buffer = base->tp_as_buffer;
    }


    bases = type->tp_bases;
    n = (((PyVarObject*)(bases))->ob_size);
    for (i = 0; i < n; i++) {
        PyObject *b = (((PyTupleObject *)(bases))->ob_item[i]);
        if (((((((PyObject*)(b))->ob_type))->tp_flags & ((1L<<31))) != 0) &&
            add_subclass((PyTypeObject *)b, type) < 0)
            goto error;
    }



    if (type->tp_reserved && !type->tp_richcompare) {
        int error;
        error = PyErr_WarnFormat(PyExc_DeprecationWarning, 1,
            "Type %.100s defines tp_reserved (formerly tp_compare) "
            "but not tp_richcompare. Comparisons may not behave as intended.",
            type->tp_name);
        if (error == -1)
            goto error;
    }


    (__builtin_expect(!(type->tp_dict != ((void *)0)), 0) ? __assert_rtn(__func__, "typeobject.c", 4301, "type->tp_dict != NULL") : (void)0);
    type->tp_flags =
        (type->tp_flags & ~(1L<<13)) | (1L<<12);
    return 0;

  error:
    type->tp_flags &= ~(1L<<13);
    return -1;
}

static int
add_subclass(PyTypeObject *base, PyTypeObject *type)
{
    Py_ssize_t i;
    int result;
    PyObject *list, *ref, *newobj;

    list = base->tp_subclasses;
    if (list == ((void *)0)) {
        base->tp_subclasses = list = PyList_New(0);
        if (list == ((void *)0))
            return -1;
    }
    (__builtin_expect(!(((((((PyObject*)(list))->ob_type))->tp_flags & ((1L<<25))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 4324, "PyList_Check(list)") : (void)0);
    newobj = PyWeakref_NewRef((PyObject *)type, ((void *)0));
    i = (((PyVarObject*)(list))->ob_size);
    while (--i >= 0) {
        ref = (((PyListObject *)(list))->ob_item[i]);
        (__builtin_expect(!(((((PyObject*)(ref))->ob_type) == (&_PyWeakref_RefType) || PyType_IsSubtype((((PyObject*)(ref))->ob_type), (&_PyWeakref_RefType)))), 0) ? __assert_rtn(__func__, "typeobject.c", 4329, "PyWeakref_CheckRef(ref)") : (void)0);
        if (((((PyObject*)(((PyWeakReference *)(ref))->wr_object))->ob_refcnt) > 0 ? ((PyWeakReference *)(ref))->wr_object : (&_Py_NoneStruct)) == (&_Py_NoneStruct))
            return PyList_SetItem(list, i, newobj);
    }
    result = PyList_Append(list, newobj);
    do { if ( --((PyObject*)(newobj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(newobj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(newobj)))); } while (0);
    return result;
}

static void
remove_subclass(PyTypeObject *base, PyTypeObject *type)
{
    Py_ssize_t i;
    PyObject *list, *ref;

    list = base->tp_subclasses;
    if (list == ((void *)0)) {
        return;
    }
    (__builtin_expect(!(((((((PyObject*)(list))->ob_type))->tp_flags & ((1L<<25))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 4348, "PyList_Check(list)") : (void)0);
    i = (((PyVarObject*)(list))->ob_size);
    while (--i >= 0) {
        ref = (((PyListObject *)(list))->ob_item[i]);
        (__builtin_expect(!(((((PyObject*)(ref))->ob_type) == (&_PyWeakref_RefType) || PyType_IsSubtype((((PyObject*)(ref))->ob_type), (&_PyWeakref_RefType)))), 0) ? __assert_rtn(__func__, "typeobject.c", 4352, "PyWeakref_CheckRef(ref)") : (void)0);
        if (((((PyObject*)(((PyWeakReference *)(ref))->wr_object))->ob_refcnt) > 0 ? ((PyWeakReference *)(ref))->wr_object : (&_Py_NoneStruct)) == (PyObject*)type) {

            PySequence_DelItem(list, i);
            return;
        }
    }
}

static int
check_num_args(PyObject *ob, int n)
{
    if (!((((PyObject*)(ob))->ob_type) == &PyTuple_Type)) {
        PyErr_SetString(PyExc_SystemError,
            "PyArg_UnpackTuple() argument list is not a tuple");
        return 0;
    }
    if (n == (((PyVarObject*)(ob))->ob_size))
        return 1;
    PyErr_Format(
        PyExc_TypeError,
        "expected %d arguments, got %zd", n, (((PyVarObject*)(ob))->ob_size));
    return 0;
}
# 4385 "typeobject.c"
static PyObject *
wrap_lenfunc(PyObject *self, PyObject *args, void *wrapped)
{
    lenfunc func = (lenfunc)wrapped;
    Py_ssize_t res;

    if (!check_num_args(args, 0))
        return ((void *)0);
    res = (*func)(self);
    if (res == -1 && PyErr_Occurred())
        return ((void *)0);
    return PyLong_FromLong((long)res);
}

static PyObject *
wrap_inquirypred(PyObject *self, PyObject *args, void *wrapped)
{
    inquiry func = (inquiry)wrapped;
    int res;

    if (!check_num_args(args, 0))
        return ((void *)0);
    res = (*func)(self);
    if (res == -1 && PyErr_Occurred())
        return ((void *)0);
    return PyBool_FromLong((long)res);
}

static PyObject *
wrap_binaryfunc(PyObject *self, PyObject *args, void *wrapped)
{
    binaryfunc func = (binaryfunc)wrapped;
    PyObject *other;

    if (!check_num_args(args, 1))
        return ((void *)0);
    other = (((PyTupleObject *)(args))->ob_item[0]);
    return (*func)(self, other);
}

static PyObject *
wrap_binaryfunc_l(PyObject *self, PyObject *args, void *wrapped)
{
    binaryfunc func = (binaryfunc)wrapped;
    PyObject *other;

    if (!check_num_args(args, 1))
        return ((void *)0);
    other = (((PyTupleObject *)(args))->ob_item[0]);
    return (*func)(self, other);
}

static PyObject *
wrap_binaryfunc_r(PyObject *self, PyObject *args, void *wrapped)
{
    binaryfunc func = (binaryfunc)wrapped;
    PyObject *other;

    if (!check_num_args(args, 1))
        return ((void *)0);
    other = (((PyTupleObject *)(args))->ob_item[0]);
    return (*func)(other, self);
}

static PyObject *
wrap_ternaryfunc(PyObject *self, PyObject *args, void *wrapped)
{
    ternaryfunc func = (ternaryfunc)wrapped;
    PyObject *other;
    PyObject *third = (&_Py_NoneStruct);



    if (!PyArg_UnpackTuple(args, "", 1, 2, &other, &third))
        return ((void *)0);
    return (*func)(self, other, third);
}

static PyObject *
wrap_ternaryfunc_r(PyObject *self, PyObject *args, void *wrapped)
{
    ternaryfunc func = (ternaryfunc)wrapped;
    PyObject *other;
    PyObject *third = (&_Py_NoneStruct);



    if (!PyArg_UnpackTuple(args, "", 1, 2, &other, &third))
        return ((void *)0);
    return (*func)(other, self, third);
}

static PyObject *
wrap_unaryfunc(PyObject *self, PyObject *args, void *wrapped)
{
    unaryfunc func = (unaryfunc)wrapped;

    if (!check_num_args(args, 0))
        return ((void *)0);
    return (*func)(self);
}

static PyObject *
wrap_indexargfunc(PyObject *self, PyObject *args, void *wrapped)
{
    ssizeargfunc func = (ssizeargfunc)wrapped;
    PyObject* o;
    Py_ssize_t i;

    if (!PyArg_UnpackTuple(args, "", 1, 1, &o))
        return ((void *)0);
    i = PyNumber_AsSsize_t(o, PyExc_OverflowError);
    if (i == -1 && PyErr_Occurred())
        return ((void *)0);
    return (*func)(self, i);
}

static Py_ssize_t
getindex(PyObject *self, PyObject *arg)
{
    Py_ssize_t i;

    i = PyNumber_AsSsize_t(arg, PyExc_OverflowError);
    if (i == -1 && PyErr_Occurred())
        return -1;
    if (i < 0) {
        PySequenceMethods *sq = (((PyObject*)(self))->ob_type)->tp_as_sequence;
        if (sq && sq->sq_length) {
            Py_ssize_t n = (*sq->sq_length)(self);
            if (n < 0)
                return -1;
            i += n;
        }
    }
    return i;
}

static PyObject *
wrap_sq_item(PyObject *self, PyObject *args, void *wrapped)
{
    ssizeargfunc func = (ssizeargfunc)wrapped;
    PyObject *arg;
    Py_ssize_t i;

    if ((((PyVarObject*)(args))->ob_size) == 1) {
        arg = (((PyTupleObject *)(args))->ob_item[0]);
        i = getindex(self, arg);
        if (i == -1 && PyErr_Occurred())
            return ((void *)0);
        return (*func)(self, i);
    }
    check_num_args(args, 1);
    (__builtin_expect(!(PyErr_Occurred()), 0) ? __assert_rtn(__func__, "typeobject.c", 4537, "PyErr_Occurred()") : (void)0);
    return ((void *)0);
}

static PyObject *
wrap_sq_setitem(PyObject *self, PyObject *args, void *wrapped)
{
    ssizeobjargproc func = (ssizeobjargproc)wrapped;
    Py_ssize_t i;
    int res;
    PyObject *arg, *value;

    if (!PyArg_UnpackTuple(args, "", 2, 2, &arg, &value))
        return ((void *)0);
    i = getindex(self, arg);
    if (i == -1 && PyErr_Occurred())
        return ((void *)0);
    res = (*func)(self, i, value);
    if (res == -1 && PyErr_Occurred())
        return ((void *)0);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static PyObject *
wrap_sq_delitem(PyObject *self, PyObject *args, void *wrapped)
{
    ssizeobjargproc func = (ssizeobjargproc)wrapped;
    Py_ssize_t i;
    int res;
    PyObject *arg;

    if (!check_num_args(args, 1))
        return ((void *)0);
    arg = (((PyTupleObject *)(args))->ob_item[0]);
    i = getindex(self, arg);
    if (i == -1 && PyErr_Occurred())
        return ((void *)0);
    res = (*func)(self, i, ((void *)0));
    if (res == -1 && PyErr_Occurred())
        return ((void *)0);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}


static PyObject *
wrap_objobjproc(PyObject *self, PyObject *args, void *wrapped)
{
    objobjproc func = (objobjproc)wrapped;
    int res;
    PyObject *value;

    if (!check_num_args(args, 1))
        return ((void *)0);
    value = (((PyTupleObject *)(args))->ob_item[0]);
    res = (*func)(self, value);
    if (res == -1 && PyErr_Occurred())
        return ((void *)0);
    else
        return PyBool_FromLong(res);
}

static PyObject *
wrap_objobjargproc(PyObject *self, PyObject *args, void *wrapped)
{
    objobjargproc func = (objobjargproc)wrapped;
    int res;
    PyObject *key, *value;

    if (!PyArg_UnpackTuple(args, "", 2, 2, &key, &value))
        return ((void *)0);
    res = (*func)(self, key, value);
    if (res == -1 && PyErr_Occurred())
        return ((void *)0);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static PyObject *
wrap_delitem(PyObject *self, PyObject *args, void *wrapped)
{
    objobjargproc func = (objobjargproc)wrapped;
    int res;
    PyObject *key;

    if (!check_num_args(args, 1))
        return ((void *)0);
    key = (((PyTupleObject *)(args))->ob_item[0]);
    res = (*func)(self, key, ((void *)0));
    if (res == -1 && PyErr_Occurred())
        return ((void *)0);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}



static int
hackcheck(PyObject *self, setattrofunc func, char *what)
{
    PyTypeObject *type = (((PyObject*)(self))->ob_type);
    while (type && type->tp_flags & (1L<<9))
        type = type->tp_base;


    if (type && type->tp_setattro != func) {
        PyErr_Format(PyExc_TypeError,
                     "can't apply this %s to %s object",
                     what,
                     type->tp_name);
        return 0;
    }
    return 1;
}

static PyObject *
wrap_setattr(PyObject *self, PyObject *args, void *wrapped)
{
    setattrofunc func = (setattrofunc)wrapped;
    int res;
    PyObject *name, *value;

    if (!PyArg_UnpackTuple(args, "", 2, 2, &name, &value))
        return ((void *)0);
    if (!hackcheck(self, func, "__setattr__"))
        return ((void *)0);
    res = (*func)(self, name, value);
    if (res < 0)
        return ((void *)0);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static PyObject *
wrap_delattr(PyObject *self, PyObject *args, void *wrapped)
{
    setattrofunc func = (setattrofunc)wrapped;
    int res;
    PyObject *name;

    if (!check_num_args(args, 1))
        return ((void *)0);
    name = (((PyTupleObject *)(args))->ob_item[0]);
    if (!hackcheck(self, func, "__delattr__"))
        return ((void *)0);
    res = (*func)(self, name, ((void *)0));
    if (res < 0)
        return ((void *)0);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static PyObject *
wrap_hashfunc(PyObject *self, PyObject *args, void *wrapped)
{
    hashfunc func = (hashfunc)wrapped;
    Py_hash_t res;

    if (!check_num_args(args, 0))
        return ((void *)0);
    res = (*func)(self);
    if (res == -1 && PyErr_Occurred())
        return ((void *)0);
    return PyLong_FromSsize_t(res);
}

static PyObject *
wrap_call(PyObject *self, PyObject *args, void *wrapped, PyObject *kwds)
{
    ternaryfunc func = (ternaryfunc)wrapped;

    return (*func)(self, args, kwds);
}

static PyObject *
wrap_richcmpfunc(PyObject *self, PyObject *args, void *wrapped, int op)
{
    richcmpfunc func = (richcmpfunc)wrapped;
    PyObject *other;

    if (!check_num_args(args, 1))
        return ((void *)0);
    other = (((PyTupleObject *)(args))->ob_item[0]);
    return (*func)(self, other, op);
}
# 4732 "typeobject.c"
static PyObject * richcmp_lt(PyObject *self, PyObject *args, void *wrapped) { return wrap_richcmpfunc(self, args, wrapped, 0); }
static PyObject * richcmp_le(PyObject *self, PyObject *args, void *wrapped) { return wrap_richcmpfunc(self, args, wrapped, 1); }
static PyObject * richcmp_eq(PyObject *self, PyObject *args, void *wrapped) { return wrap_richcmpfunc(self, args, wrapped, 2); }
static PyObject * richcmp_ne(PyObject *self, PyObject *args, void *wrapped) { return wrap_richcmpfunc(self, args, wrapped, 3); }
static PyObject * richcmp_gt(PyObject *self, PyObject *args, void *wrapped) { return wrap_richcmpfunc(self, args, wrapped, 4); }
static PyObject * richcmp_ge(PyObject *self, PyObject *args, void *wrapped) { return wrap_richcmpfunc(self, args, wrapped, 5); }

static PyObject *
wrap_next(PyObject *self, PyObject *args, void *wrapped)
{
    unaryfunc func = (unaryfunc)wrapped;
    PyObject *res;

    if (!check_num_args(args, 0))
        return ((void *)0);
    res = (*func)(self);
    if (res == ((void *)0) && !PyErr_Occurred())
        PyErr_SetNone(PyExc_StopIteration);
    return res;
}

static PyObject *
wrap_descr_get(PyObject *self, PyObject *args, void *wrapped)
{
    descrgetfunc func = (descrgetfunc)wrapped;
    PyObject *obj;
    PyObject *type = ((void *)0);

    if (!PyArg_UnpackTuple(args, "", 1, 2, &obj, &type))
        return ((void *)0);
    if (obj == (&_Py_NoneStruct))
        obj = ((void *)0);
    if (type == (&_Py_NoneStruct))
        type = ((void *)0);
    if (type == ((void *)0) &&obj == ((void *)0)) {
        PyErr_SetString(PyExc_TypeError,
                        "__get__(None, None) is invalid");
        return ((void *)0);
    }
    return (*func)(self, obj, type);
}

static PyObject *
wrap_descr_set(PyObject *self, PyObject *args, void *wrapped)
{
    descrsetfunc func = (descrsetfunc)wrapped;
    PyObject *obj, *value;
    int ret;

    if (!PyArg_UnpackTuple(args, "", 2, 2, &obj, &value))
        return ((void *)0);
    ret = (*func)(self, obj, value);
    if (ret < 0)
        return ((void *)0);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static PyObject *
wrap_descr_delete(PyObject *self, PyObject *args, void *wrapped)
{
    descrsetfunc func = (descrsetfunc)wrapped;
    PyObject *obj;
    int ret;

    if (!check_num_args(args, 1))
        return ((void *)0);
    obj = (((PyTupleObject *)(args))->ob_item[0]);
    ret = (*func)(self, obj, ((void *)0));
    if (ret < 0)
        return ((void *)0);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static PyObject *
wrap_init(PyObject *self, PyObject *args, void *wrapped, PyObject *kwds)
{
    initproc func = (initproc)wrapped;

    if (func(self, args, kwds) < 0)
        return ((void *)0);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static PyObject *
tp_new_wrapper(PyObject *self, PyObject *args, PyObject *kwds)
{
    PyTypeObject *type, *subtype, *staticbase;
    PyObject *arg0, *res;

    if (self == ((void *)0) || !((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<31))) != 0))
        Py_FatalError("__new__() called with non-type 'self'");
    type = (PyTypeObject *)self;
    if (!((((((PyObject*)(args))->ob_type))->tp_flags & ((1L<<26))) != 0) || (((PyVarObject*)(args))->ob_size) < 1) {
        PyErr_Format(PyExc_TypeError,
                     "%s.__new__(): not enough arguments",
                     type->tp_name);
        return ((void *)0);
    }
    arg0 = (((PyTupleObject *)(args))->ob_item[0]);
    if (!((((((PyObject*)(arg0))->ob_type))->tp_flags & ((1L<<31))) != 0)) {
        PyErr_Format(PyExc_TypeError,
                     "%s.__new__(X): X is not a type object (%s)",
                     type->tp_name,
                     (((PyObject*)(arg0))->ob_type)->tp_name);
        return ((void *)0);
    }
    subtype = (PyTypeObject *)arg0;
    if (!PyType_IsSubtype(subtype, type)) {
        PyErr_Format(PyExc_TypeError,
                     "%s.__new__(%s): %s is not a subtype of %s",
                     type->tp_name,
                     subtype->tp_name,
                     subtype->tp_name,
                     type->tp_name);
        return ((void *)0);
    }




    staticbase = subtype;
    while (staticbase && (staticbase->tp_new == slot_tp_new))
        staticbase = staticbase->tp_base;


    if (staticbase && staticbase->tp_new != type->tp_new) {
        PyErr_Format(PyExc_TypeError,
                     "%s.__new__(%s) is not safe, use %s.__new__()",
                     type->tp_name,
                     subtype->tp_name,
                     staticbase == ((void *)0) ? "?" : staticbase->tp_name);
        return ((void *)0);
    }

    args = PyTuple_GetSlice(args, 1, (((PyVarObject*)(args))->ob_size));
    if (args == ((void *)0))
        return ((void *)0);
    res = type->tp_new(subtype, args, kwds);
    do { if ( --((PyObject*)(args))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(args)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(args)))); } while (0);
    return res;
}

static struct PyMethodDef tp_new_methoddef[] = {
    {"__new__", (PyCFunction)tp_new_wrapper, 0x0001|0x0002,
     "T.__new__(S, ...) -> " "a new object with type S, a subtype of T"},

    {0}
};

static int
add_tp_new_wrapper(PyTypeObject *type)
{
    PyObject *func;

    if (_PyDict_GetItemId(type->tp_dict, &PyId___new__) != ((void *)0))
        return 0;
    func = PyCFunction_NewEx((tp_new_methoddef), ((PyObject *)type), ((void *)0));
    if (func == ((void *)0))
        return -1;
    if (_PyDict_SetItemId(type->tp_dict, &PyId___new__, func)) {
        do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0);
        return -1;
    }
    do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0);
    return 0;
}
# 4923 "typeobject.c"
static int
method_is_overloaded(PyObject *left, PyObject *right, struct _Py_Identifier *name)
{
    PyObject *a, *b;
    int ok;

    b = _PyObject_GetAttrId((PyObject *)((((PyObject*)(right))->ob_type)), name);
    if (b == ((void *)0)) {
        PyErr_Clear();

        return 0;
    }

    a = _PyObject_GetAttrId((PyObject *)((((PyObject*)(left))->ob_type)), name);
    if (a == ((void *)0)) {
        PyErr_Clear();
        do { if ( --((PyObject*)(b))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(b)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(b)))); } while (0);

        return 1;
    }

    ok = PyObject_RichCompareBool(a, b, 3);
    do { if ( --((PyObject*)(a))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(a)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(a)))); } while (0);
    do { if ( --((PyObject*)(b))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(b)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(b)))); } while (0);
    if (ok < 0) {
        PyErr_Clear();
        return 0;
    }

    return ok;
}
# 5000 "typeobject.c"
static Py_ssize_t
slot_sq_length(PyObject *self)
{
    static _Py_Identifier PyId___len__ = { 0, "__len__", 0 };
    PyObject *res = call_method(self, &PyId___len__, "()");
    Py_ssize_t len;

    if (res == ((void *)0))
        return -1;
    len = PyNumber_AsSsize_t(res, PyExc_OverflowError);
    do { if ( --((PyObject*)(res))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(res)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(res)))); } while (0);
    if (len < 0) {
        if (!PyErr_Occurred())
            PyErr_SetString(PyExc_ValueError,
                            "__len__() should return >= 0");
        return -1;
    }
    return len;
}



static PyObject *
slot_sq_item(PyObject *self, Py_ssize_t i)
{
    PyObject *func, *args = ((void *)0), *ival = ((void *)0), *retval = ((void *)0);
    descrgetfunc f;

    func = _PyType_LookupId((((PyObject*)(self))->ob_type), &PyId___getitem__);
    if (func != ((void *)0)) {
        if ((f = (((PyObject*)(func))->ob_type)->tp_descr_get) == ((void *)0))
            ( ((PyObject*)(func))->ob_refcnt++);
        else {
            func = f(func, self, (PyObject *)((((PyObject*)(self))->ob_type)));
            if (func == ((void *)0)) {
                return ((void *)0);
            }
        }
        ival = PyLong_FromSsize_t(i);
        if (ival != ((void *)0)) {
            args = PyTuple_New(1);
            if (args != ((void *)0)) {
                (((PyTupleObject *)(args))->ob_item[0] = ival);
                retval = PyObject_Call(func, args, ((void *)0));
                do { if ((args) == ((void *)0)) ; else do { if ( --((PyObject*)(args))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(args)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(args)))); } while (0); } while (0);
                do { if ((func) == ((void *)0)) ; else do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0); } while (0);
                return retval;
            }
        }
    }
    else {
        PyObject *getitem_str = _PyUnicode_FromId(&PyId___getitem__);
        PyErr_SetObject(PyExc_AttributeError, getitem_str);
    }
    do { if ((args) == ((void *)0)) ; else do { if ( --((PyObject*)(args))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(args)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(args)))); } while (0); } while (0);
    do { if ((ival) == ((void *)0)) ; else do { if ( --((PyObject*)(ival))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(ival)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(ival)))); } while (0); } while (0);
    do { if ((func) == ((void *)0)) ; else do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0); } while (0);
    return ((void *)0);
}

static int
slot_sq_ass_item(PyObject *self, Py_ssize_t index, PyObject *value)
{
    PyObject *res;
    static _Py_Identifier PyId___delitem__ = { 0, "__delitem__", 0 };
    static _Py_Identifier PyId___setitem__ = { 0, "__setitem__", 0 };

    if (value == ((void *)0))
        res = call_method(self, &PyId___delitem__, "(n)", index);
    else
        res = call_method(self, &PyId___setitem__, "(nO)", index, value);
    if (res == ((void *)0))
        return -1;
    do { if ( --((PyObject*)(res))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(res)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(res)))); } while (0);
    return 0;
}

static int
slot_sq_contains(PyObject *self, PyObject *value)
{
    PyObject *func, *res, *args;
    int result = -1;
    static _Py_Identifier PyId___contains__ = { 0, "__contains__", 0 };

    func = lookup_maybe(self, &PyId___contains__);
    if (func != ((void *)0)) {
        args = PyTuple_Pack(1, value);
        if (args == ((void *)0))
            res = ((void *)0);
        else {
            res = PyObject_Call(func, args, ((void *)0));
            do { if ( --((PyObject*)(args))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(args)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(args)))); } while (0);
        }
        do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0);
        if (res != ((void *)0)) {
            result = PyObject_IsTrue(res);
            do { if ( --((PyObject*)(res))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(res)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(res)))); } while (0);
        }
    }
    else if (! PyErr_Occurred()) {

        result = (int)_PySequence_IterSearch(self, value,
                                         3);
    }
    return result;
}



static PyObject * slot_mp_subscript(PyObject *self, PyObject * arg1) { static _Py_Identifier id = { 0, "__getitem__", 0 }; return call_method(self, &id, "(" "O" ")", arg1); }

static int
slot_mp_ass_subscript(PyObject *self, PyObject *key, PyObject *value)
{
    PyObject *res;
    static _Py_Identifier PyId___delitem__ = { 0, "__delitem__", 0 };
    static _Py_Identifier PyId___setitem__ = { 0, "__setitem__", 0 };

    if (value == ((void *)0))
        res = call_method(self, &PyId___delitem__, "(O)", key);
    else
        res = call_method(self, &PyId___setitem__, "(OO)", key, value);

    if (res == ((void *)0))
        return -1;
    do { if ( --((PyObject*)(res))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(res)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(res)))); } while (0);
    return 0;
}

static PyObject * slot_nb_add(PyObject *self, PyObject *other) { static _Py_Identifier op_id = { 0, "__add__", 0 }; static _Py_Identifier rop_id = { 0, "__radd__", 0 }; int do_other = (((PyObject*)(self))->ob_type) != (((PyObject*)(other))->ob_type) && (((PyObject*)(other))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(other))->ob_type)->tp_as_number->nb_add == slot_nb_add; if ((((PyObject*)(self))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(self))->ob_type)->tp_as_number->nb_add == slot_nb_add) { PyObject *r; if (do_other && PyType_IsSubtype((((PyObject*)(other))->ob_type), (((PyObject*)(self))->ob_type)) && method_is_overloaded(self, other, &rop_id)) { r = call_maybe(other, &rop_id, "(O)", self); if (r != (&_Py_NotImplementedStruct)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); do_other = 0; } r = call_maybe(self, &op_id, "(O)", other); if (r != (&_Py_NotImplementedStruct) || (((PyObject*)(other))->ob_type) == (((PyObject*)(self))->ob_type)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); } if (do_other) { return call_maybe(other, &rop_id, "(O)", self); } return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct); }
static PyObject * slot_nb_subtract(PyObject *self, PyObject *other) { static _Py_Identifier op_id = { 0, "__sub__", 0 }; static _Py_Identifier rop_id = { 0, "__rsub__", 0 }; int do_other = (((PyObject*)(self))->ob_type) != (((PyObject*)(other))->ob_type) && (((PyObject*)(other))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(other))->ob_type)->tp_as_number->nb_subtract == slot_nb_subtract; if ((((PyObject*)(self))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(self))->ob_type)->tp_as_number->nb_subtract == slot_nb_subtract) { PyObject *r; if (do_other && PyType_IsSubtype((((PyObject*)(other))->ob_type), (((PyObject*)(self))->ob_type)) && method_is_overloaded(self, other, &rop_id)) { r = call_maybe(other, &rop_id, "(O)", self); if (r != (&_Py_NotImplementedStruct)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); do_other = 0; } r = call_maybe(self, &op_id, "(O)", other); if (r != (&_Py_NotImplementedStruct) || (((PyObject*)(other))->ob_type) == (((PyObject*)(self))->ob_type)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); } if (do_other) { return call_maybe(other, &rop_id, "(O)", self); } return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct); }
static PyObject * slot_nb_multiply(PyObject *self, PyObject *other) { static _Py_Identifier op_id = { 0, "__mul__", 0 }; static _Py_Identifier rop_id = { 0, "__rmul__", 0 }; int do_other = (((PyObject*)(self))->ob_type) != (((PyObject*)(other))->ob_type) && (((PyObject*)(other))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(other))->ob_type)->tp_as_number->nb_multiply == slot_nb_multiply; if ((((PyObject*)(self))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(self))->ob_type)->tp_as_number->nb_multiply == slot_nb_multiply) { PyObject *r; if (do_other && PyType_IsSubtype((((PyObject*)(other))->ob_type), (((PyObject*)(self))->ob_type)) && method_is_overloaded(self, other, &rop_id)) { r = call_maybe(other, &rop_id, "(O)", self); if (r != (&_Py_NotImplementedStruct)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); do_other = 0; } r = call_maybe(self, &op_id, "(O)", other); if (r != (&_Py_NotImplementedStruct) || (((PyObject*)(other))->ob_type) == (((PyObject*)(self))->ob_type)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); } if (do_other) { return call_maybe(other, &rop_id, "(O)", self); } return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct); }
static PyObject * slot_nb_remainder(PyObject *self, PyObject *other) { static _Py_Identifier op_id = { 0, "__mod__", 0 }; static _Py_Identifier rop_id = { 0, "__rmod__", 0 }; int do_other = (((PyObject*)(self))->ob_type) != (((PyObject*)(other))->ob_type) && (((PyObject*)(other))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(other))->ob_type)->tp_as_number->nb_remainder == slot_nb_remainder; if ((((PyObject*)(self))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(self))->ob_type)->tp_as_number->nb_remainder == slot_nb_remainder) { PyObject *r; if (do_other && PyType_IsSubtype((((PyObject*)(other))->ob_type), (((PyObject*)(self))->ob_type)) && method_is_overloaded(self, other, &rop_id)) { r = call_maybe(other, &rop_id, "(O)", self); if (r != (&_Py_NotImplementedStruct)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); do_other = 0; } r = call_maybe(self, &op_id, "(O)", other); if (r != (&_Py_NotImplementedStruct) || (((PyObject*)(other))->ob_type) == (((PyObject*)(self))->ob_type)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); } if (do_other) { return call_maybe(other, &rop_id, "(O)", self); } return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct); }
static PyObject * slot_nb_divmod(PyObject *self, PyObject *other) { static _Py_Identifier op_id = { 0, "__divmod__", 0 }; static _Py_Identifier rop_id = { 0, "__rdivmod__", 0 }; int do_other = (((PyObject*)(self))->ob_type) != (((PyObject*)(other))->ob_type) && (((PyObject*)(other))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(other))->ob_type)->tp_as_number->nb_divmod == slot_nb_divmod; if ((((PyObject*)(self))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(self))->ob_type)->tp_as_number->nb_divmod == slot_nb_divmod) { PyObject *r; if (do_other && PyType_IsSubtype((((PyObject*)(other))->ob_type), (((PyObject*)(self))->ob_type)) && method_is_overloaded(self, other, &rop_id)) { r = call_maybe(other, &rop_id, "(O)", self); if (r != (&_Py_NotImplementedStruct)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); do_other = 0; } r = call_maybe(self, &op_id, "(O)", other); if (r != (&_Py_NotImplementedStruct) || (((PyObject*)(other))->ob_type) == (((PyObject*)(self))->ob_type)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); } if (do_other) { return call_maybe(other, &rop_id, "(O)", self); } return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct); }

static PyObject *slot_nb_power(PyObject *, PyObject *, PyObject *);

static PyObject * slot_nb_power_binary(PyObject *self, PyObject *other) { static _Py_Identifier op_id = { 0, "__pow__", 0 }; static _Py_Identifier rop_id = { 0, "__rpow__", 0 }; int do_other = (((PyObject*)(self))->ob_type) != (((PyObject*)(other))->ob_type) && (((PyObject*)(other))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(other))->ob_type)->tp_as_number->nb_power == slot_nb_power; if ((((PyObject*)(self))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(self))->ob_type)->tp_as_number->nb_power == slot_nb_power) { PyObject *r; if (do_other && PyType_IsSubtype((((PyObject*)(other))->ob_type), (((PyObject*)(self))->ob_type)) && method_is_overloaded(self, other, &rop_id)) { r = call_maybe(other, &rop_id, "(O)", self); if (r != (&_Py_NotImplementedStruct)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); do_other = 0; } r = call_maybe(self, &op_id, "(O)", other); if (r != (&_Py_NotImplementedStruct) || (((PyObject*)(other))->ob_type) == (((PyObject*)(self))->ob_type)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); } if (do_other) { return call_maybe(other, &rop_id, "(O)", self); } return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct); }


static PyObject *
slot_nb_power(PyObject *self, PyObject *other, PyObject *modulus)
{
    static _Py_Identifier PyId___pow__ = { 0, "__pow__", 0 };

    if (modulus == (&_Py_NoneStruct))
        return slot_nb_power_binary(self, other);



    if ((((PyObject*)(self))->ob_type)->tp_as_number != ((void *)0) &&
        (((PyObject*)(self))->ob_type)->tp_as_number->nb_power == slot_nb_power) {
        return call_method(self, &PyId___pow__, "(OO)", other, modulus);
    }
    return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct);
}

static PyObject * slot_nb_negative(PyObject *self) { static _Py_Identifier id = { 0, "__neg__", 0 }; return call_method(self, &id, "()"); }
static PyObject * slot_nb_positive(PyObject *self) { static _Py_Identifier id = { 0, "__pos__", 0 }; return call_method(self, &id, "()"); }
static PyObject * slot_nb_absolute(PyObject *self) { static _Py_Identifier id = { 0, "__abs__", 0 }; return call_method(self, &id, "()"); }

static int
slot_nb_bool(PyObject *self)
{
    PyObject *func, *args;
    int result = -1;
    int using_len = 0;
    static _Py_Identifier PyId___len__ = { 0, "__len__", 0 };
    static _Py_Identifier PyId___bool__ = { 0, "__bool__", 0 };

    func = lookup_maybe(self, &PyId___bool__);
    if (func == ((void *)0)) {
        if (PyErr_Occurred())
            return -1;
        func = lookup_maybe(self, &PyId___len__);
        if (func == ((void *)0))
            return PyErr_Occurred() ? -1 : 1;
        using_len = 1;
    }
    args = PyTuple_New(0);
    if (args != ((void *)0)) {
        PyObject *temp = PyObject_Call(func, args, ((void *)0));
        do { if ( --((PyObject*)(args))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(args)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(args)))); } while (0);
        if (temp != ((void *)0)) {
            if (using_len) {

                result = PyObject_IsTrue(temp);
            }
            else if (((((PyObject*)(temp))->ob_type) == &PyBool_Type)) {
                result = PyObject_IsTrue(temp);
            }
            else {
                PyErr_Format(PyExc_TypeError,
                             "__bool__ should return "
                             "bool, returned %s",
                             (((PyObject*)(temp))->ob_type)->tp_name);
                result = -1;
            }
            do { if ( --((PyObject*)(temp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(temp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(temp)))); } while (0);
        }
    }
    do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0);
    return result;
}


static PyObject *
slot_nb_index(PyObject *self)
{
    static _Py_Identifier PyId___index__ = { 0, "__index__", 0 };
    return call_method(self, &PyId___index__, "()");
}


static PyObject * slot_nb_invert(PyObject *self) { static _Py_Identifier id = { 0, "__invert__", 0 }; return call_method(self, &id, "()"); }
static PyObject * slot_nb_lshift(PyObject *self, PyObject *other) { static _Py_Identifier op_id = { 0, "__lshift__", 0 }; static _Py_Identifier rop_id = { 0, "__rlshift__", 0 }; int do_other = (((PyObject*)(self))->ob_type) != (((PyObject*)(other))->ob_type) && (((PyObject*)(other))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(other))->ob_type)->tp_as_number->nb_lshift == slot_nb_lshift; if ((((PyObject*)(self))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(self))->ob_type)->tp_as_number->nb_lshift == slot_nb_lshift) { PyObject *r; if (do_other && PyType_IsSubtype((((PyObject*)(other))->ob_type), (((PyObject*)(self))->ob_type)) && method_is_overloaded(self, other, &rop_id)) { r = call_maybe(other, &rop_id, "(O)", self); if (r != (&_Py_NotImplementedStruct)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); do_other = 0; } r = call_maybe(self, &op_id, "(O)", other); if (r != (&_Py_NotImplementedStruct) || (((PyObject*)(other))->ob_type) == (((PyObject*)(self))->ob_type)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); } if (do_other) { return call_maybe(other, &rop_id, "(O)", self); } return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct); }
static PyObject * slot_nb_rshift(PyObject *self, PyObject *other) { static _Py_Identifier op_id = { 0, "__rshift__", 0 }; static _Py_Identifier rop_id = { 0, "__rrshift__", 0 }; int do_other = (((PyObject*)(self))->ob_type) != (((PyObject*)(other))->ob_type) && (((PyObject*)(other))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(other))->ob_type)->tp_as_number->nb_rshift == slot_nb_rshift; if ((((PyObject*)(self))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(self))->ob_type)->tp_as_number->nb_rshift == slot_nb_rshift) { PyObject *r; if (do_other && PyType_IsSubtype((((PyObject*)(other))->ob_type), (((PyObject*)(self))->ob_type)) && method_is_overloaded(self, other, &rop_id)) { r = call_maybe(other, &rop_id, "(O)", self); if (r != (&_Py_NotImplementedStruct)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); do_other = 0; } r = call_maybe(self, &op_id, "(O)", other); if (r != (&_Py_NotImplementedStruct) || (((PyObject*)(other))->ob_type) == (((PyObject*)(self))->ob_type)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); } if (do_other) { return call_maybe(other, &rop_id, "(O)", self); } return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct); }
static PyObject * slot_nb_and(PyObject *self, PyObject *other) { static _Py_Identifier op_id = { 0, "__and__", 0 }; static _Py_Identifier rop_id = { 0, "__rand__", 0 }; int do_other = (((PyObject*)(self))->ob_type) != (((PyObject*)(other))->ob_type) && (((PyObject*)(other))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(other))->ob_type)->tp_as_number->nb_and == slot_nb_and; if ((((PyObject*)(self))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(self))->ob_type)->tp_as_number->nb_and == slot_nb_and) { PyObject *r; if (do_other && PyType_IsSubtype((((PyObject*)(other))->ob_type), (((PyObject*)(self))->ob_type)) && method_is_overloaded(self, other, &rop_id)) { r = call_maybe(other, &rop_id, "(O)", self); if (r != (&_Py_NotImplementedStruct)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); do_other = 0; } r = call_maybe(self, &op_id, "(O)", other); if (r != (&_Py_NotImplementedStruct) || (((PyObject*)(other))->ob_type) == (((PyObject*)(self))->ob_type)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); } if (do_other) { return call_maybe(other, &rop_id, "(O)", self); } return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct); }
static PyObject * slot_nb_xor(PyObject *self, PyObject *other) { static _Py_Identifier op_id = { 0, "__xor__", 0 }; static _Py_Identifier rop_id = { 0, "__rxor__", 0 }; int do_other = (((PyObject*)(self))->ob_type) != (((PyObject*)(other))->ob_type) && (((PyObject*)(other))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(other))->ob_type)->tp_as_number->nb_xor == slot_nb_xor; if ((((PyObject*)(self))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(self))->ob_type)->tp_as_number->nb_xor == slot_nb_xor) { PyObject *r; if (do_other && PyType_IsSubtype((((PyObject*)(other))->ob_type), (((PyObject*)(self))->ob_type)) && method_is_overloaded(self, other, &rop_id)) { r = call_maybe(other, &rop_id, "(O)", self); if (r != (&_Py_NotImplementedStruct)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); do_other = 0; } r = call_maybe(self, &op_id, "(O)", other); if (r != (&_Py_NotImplementedStruct) || (((PyObject*)(other))->ob_type) == (((PyObject*)(self))->ob_type)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); } if (do_other) { return call_maybe(other, &rop_id, "(O)", self); } return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct); }
static PyObject * slot_nb_or(PyObject *self, PyObject *other) { static _Py_Identifier op_id = { 0, "__or__", 0 }; static _Py_Identifier rop_id = { 0, "__ror__", 0 }; int do_other = (((PyObject*)(self))->ob_type) != (((PyObject*)(other))->ob_type) && (((PyObject*)(other))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(other))->ob_type)->tp_as_number->nb_or == slot_nb_or; if ((((PyObject*)(self))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(self))->ob_type)->tp_as_number->nb_or == slot_nb_or) { PyObject *r; if (do_other && PyType_IsSubtype((((PyObject*)(other))->ob_type), (((PyObject*)(self))->ob_type)) && method_is_overloaded(self, other, &rop_id)) { r = call_maybe(other, &rop_id, "(O)", self); if (r != (&_Py_NotImplementedStruct)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); do_other = 0; } r = call_maybe(self, &op_id, "(O)", other); if (r != (&_Py_NotImplementedStruct) || (((PyObject*)(other))->ob_type) == (((PyObject*)(self))->ob_type)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); } if (do_other) { return call_maybe(other, &rop_id, "(O)", self); } return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct); }

static PyObject * slot_nb_int(PyObject *self) { static _Py_Identifier id = { 0, "__int__", 0 }; return call_method(self, &id, "()"); }
static PyObject * slot_nb_float(PyObject *self) { static _Py_Identifier id = { 0, "__float__", 0 }; return call_method(self, &id, "()"); }
static PyObject * slot_nb_inplace_add(PyObject *self, PyObject * arg1) { static _Py_Identifier id = { 0, "__iadd__", 0 }; return call_method(self, &id, "(" "O" ")", arg1); }
static PyObject * slot_nb_inplace_subtract(PyObject *self, PyObject * arg1) { static _Py_Identifier id = { 0, "__isub__", 0 }; return call_method(self, &id, "(" "O" ")", arg1); }
static PyObject * slot_nb_inplace_multiply(PyObject *self, PyObject * arg1) { static _Py_Identifier id = { 0, "__imul__", 0 }; return call_method(self, &id, "(" "O" ")", arg1); }
static PyObject * slot_nb_inplace_remainder(PyObject *self, PyObject * arg1) { static _Py_Identifier id = { 0, "__imod__", 0 }; return call_method(self, &id, "(" "O" ")", arg1); }

static PyObject *
slot_nb_inplace_power(PyObject *self, PyObject * arg1, PyObject *arg2)
{
    static _Py_Identifier PyId___ipow__ = { 0, "__ipow__", 0 };
    return call_method(self, &PyId___ipow__, "(" "O" ")", arg1);
}
static PyObject * slot_nb_inplace_lshift(PyObject *self, PyObject * arg1) { static _Py_Identifier id = { 0, "__ilshift__", 0 }; return call_method(self, &id, "(" "O" ")", arg1); }
static PyObject * slot_nb_inplace_rshift(PyObject *self, PyObject * arg1) { static _Py_Identifier id = { 0, "__irshift__", 0 }; return call_method(self, &id, "(" "O" ")", arg1); }
static PyObject * slot_nb_inplace_and(PyObject *self, PyObject * arg1) { static _Py_Identifier id = { 0, "__iand__", 0 }; return call_method(self, &id, "(" "O" ")", arg1); }
static PyObject * slot_nb_inplace_xor(PyObject *self, PyObject * arg1) { static _Py_Identifier id = { 0, "__ixor__", 0 }; return call_method(self, &id, "(" "O" ")", arg1); }
static PyObject * slot_nb_inplace_or(PyObject *self, PyObject * arg1) { static _Py_Identifier id = { 0, "__ior__", 0 }; return call_method(self, &id, "(" "O" ")", arg1); }
static PyObject * slot_nb_floor_divide(PyObject *self, PyObject *other) { static _Py_Identifier op_id = { 0, "__floordiv__", 0 }; static _Py_Identifier rop_id = { 0, "__rfloordiv__", 0 }; int do_other = (((PyObject*)(self))->ob_type) != (((PyObject*)(other))->ob_type) && (((PyObject*)(other))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(other))->ob_type)->tp_as_number->nb_floor_divide == slot_nb_floor_divide; if ((((PyObject*)(self))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(self))->ob_type)->tp_as_number->nb_floor_divide == slot_nb_floor_divide) { PyObject *r; if (do_other && PyType_IsSubtype((((PyObject*)(other))->ob_type), (((PyObject*)(self))->ob_type)) && method_is_overloaded(self, other, &rop_id)) { r = call_maybe(other, &rop_id, "(O)", self); if (r != (&_Py_NotImplementedStruct)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); do_other = 0; } r = call_maybe(self, &op_id, "(O)", other); if (r != (&_Py_NotImplementedStruct) || (((PyObject*)(other))->ob_type) == (((PyObject*)(self))->ob_type)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); } if (do_other) { return call_maybe(other, &rop_id, "(O)", self); } return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct); }

static PyObject * slot_nb_true_divide(PyObject *self, PyObject *other) { static _Py_Identifier op_id = { 0, "__truediv__", 0 }; static _Py_Identifier rop_id = { 0, "__rtruediv__", 0 }; int do_other = (((PyObject*)(self))->ob_type) != (((PyObject*)(other))->ob_type) && (((PyObject*)(other))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(other))->ob_type)->tp_as_number->nb_true_divide == slot_nb_true_divide; if ((((PyObject*)(self))->ob_type)->tp_as_number != ((void *)0) && (((PyObject*)(self))->ob_type)->tp_as_number->nb_true_divide == slot_nb_true_divide) { PyObject *r; if (do_other && PyType_IsSubtype((((PyObject*)(other))->ob_type), (((PyObject*)(self))->ob_type)) && method_is_overloaded(self, other, &rop_id)) { r = call_maybe(other, &rop_id, "(O)", self); if (r != (&_Py_NotImplementedStruct)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); do_other = 0; } r = call_maybe(self, &op_id, "(O)", other); if (r != (&_Py_NotImplementedStruct) || (((PyObject*)(other))->ob_type) == (((PyObject*)(self))->ob_type)) return r; do { if ( --((PyObject*)(r))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(r)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(r)))); } while (0); } if (do_other) { return call_maybe(other, &rop_id, "(O)", self); } return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct); }
static PyObject * slot_nb_inplace_floor_divide(PyObject *self, PyObject * arg1) { static _Py_Identifier id = { 0, "__ifloordiv__", 0 }; return call_method(self, &id, "(" "O" ")", arg1); }
static PyObject * slot_nb_inplace_true_divide(PyObject *self, PyObject * arg1) { static _Py_Identifier id = { 0, "__itruediv__", 0 }; return call_method(self, &id, "(" "O" ")", arg1); }

static PyObject *
slot_tp_repr(PyObject *self)
{
    PyObject *func, *res;
    static _Py_Identifier PyId___repr__ = { 0, "__repr__", 0 };

    func = lookup_method(self, &PyId___repr__);
    if (func != ((void *)0)) {
        res = PyEval_CallObjectWithKeywords(func, ((void *)0), (PyObject *)((void *)0));
        do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0);
        return res;
    }
    PyErr_Clear();
    return PyUnicode_FromFormat("<%s object at %p>",
                               (((PyObject*)(self))->ob_type)->tp_name, self);
}

static PyObject *
slot_tp_str(PyObject *self)
{
    PyObject *func, *res;
    static _Py_Identifier PyId___str__ = { 0, "__str__", 0 };

    func = lookup_method(self, &PyId___str__);
    if (func != ((void *)0)) {
        res = PyEval_CallObjectWithKeywords(func, ((void *)0), (PyObject *)((void *)0));
        do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0);
        return res;
    }
    else {

        PyErr_Clear();
        res = slot_tp_repr(self);
        if (!res)
            return ((void *)0);



        (__builtin_expect(!(0), 0) ? __assert_rtn(__func__, "typeobject.c", 5283, "0") : (void)0);
        return res;





    }
}

static Py_hash_t
slot_tp_hash(PyObject *self)
{
    PyObject *func, *res;
    Py_ssize_t h;

    func = lookup_method(self, &PyId___hash__);

    if (func == (&_Py_NoneStruct)) {
        do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0);
        func = ((void *)0);
    }

    if (func == ((void *)0)) {
        return PyObject_HashNotImplemented(self);
    }

    res = PyEval_CallObjectWithKeywords(func, ((void *)0), (PyObject *)((void *)0));
    do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0);
    if (res == ((void *)0))
        return -1;

    if (!((((((PyObject*)(res))->ob_type))->tp_flags & ((1L<<24))) != 0)) {
        PyErr_SetString(PyExc_TypeError,
                        "__hash__ method should return an integer");
        return -1;
    }





    h = PyLong_AsSsize_t(res);
    if (h == -1 && PyErr_Occurred()) {



        PyErr_Clear();
        h = PyLong_Type.tp_hash(res);
    }

    if (h == -1)
        h = -2;
    do { if ( --((PyObject*)(res))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(res)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(res)))); } while (0);
    return h;
}

static PyObject *
slot_tp_call(PyObject *self, PyObject *args, PyObject *kwds)
{
    static _Py_Identifier PyId___call__ = { 0, "__call__", 0 };
    PyObject *meth = lookup_method(self, &PyId___call__);
    PyObject *res;

    if (meth == ((void *)0))
        return ((void *)0);

    res = PyObject_Call(meth, args, kwds);

    do { if ( --((PyObject*)(meth))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(meth)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(meth)))); } while (0);
    return res;
}
# 5367 "typeobject.c"
static PyObject *
slot_tp_getattro(PyObject *self, PyObject *name)
{
    return call_method(self, &PyId___getattribute__, "(O)", name);
}

static PyObject *
call_attribute(PyObject *self, PyObject *attr, PyObject *name)
{
    PyObject *res, *descr = ((void *)0);
    descrgetfunc f = (((PyObject*)(attr))->ob_type)->tp_descr_get;

    if (f != ((void *)0)) {
        descr = f(attr, self, (PyObject *)((((PyObject*)(self))->ob_type)));
        if (descr == ((void *)0))
            return ((void *)0);
        else
            attr = descr;
    }
    res = PyObject_CallFunctionObjArgs(attr, name, ((void *)0));
    do { if ((descr) == ((void *)0)) ; else do { if ( --((PyObject*)(descr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(descr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(descr)))); } while (0); } while (0);
    return res;
}

static PyObject *
slot_tp_getattr_hook(PyObject *self, PyObject *name)
{
    PyTypeObject *tp = (((PyObject*)(self))->ob_type);
    PyObject *getattr, *getattribute, *res;
    static _Py_Identifier PyId___getattr__ = { 0, "__getattr__", 0 };






    getattr = _PyType_LookupId(tp, &PyId___getattr__);
    if (getattr == ((void *)0)) {

        tp->tp_getattro = slot_tp_getattro;
        return slot_tp_getattro(self, name);
    }
    ( ((PyObject*)(getattr))->ob_refcnt++);





    getattribute = _PyType_LookupId(tp, &PyId___getattribute__);
    if (getattribute == ((void *)0) ||
        ((((PyObject*)(getattribute))->ob_type) == &PyWrapperDescr_Type &&
         ((PyWrapperDescrObject *)getattribute)->d_wrapped ==
         (void *)PyObject_GenericGetAttr))
        res = PyObject_GenericGetAttr(self, name);
    else {
        ( ((PyObject*)(getattribute))->ob_refcnt++);
        res = call_attribute(self, getattribute, name);
        do { if ( --((PyObject*)(getattribute))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(getattribute)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(getattribute)))); } while (0);
    }
    if (res == ((void *)0) && PyErr_ExceptionMatches(PyExc_AttributeError)) {
        PyErr_Clear();
        res = call_attribute(self, getattr, name);
    }
    do { if ( --((PyObject*)(getattr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(getattr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(getattr)))); } while (0);
    return res;
}

static int
slot_tp_setattro(PyObject *self, PyObject *name, PyObject *value)
{
    PyObject *res;
    static _Py_Identifier PyId___delattr__ = { 0, "__delattr__", 0 };
    static _Py_Identifier PyId___setattr__ = { 0, "__setattr__", 0 };

    if (value == ((void *)0))
        res = call_method(self, &PyId___delattr__, "(O)", name);
    else
        res = call_method(self, &PyId___setattr__, "(OO)", name, value);
    if (res == ((void *)0))
        return -1;
    do { if ( --((PyObject*)(res))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(res)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(res)))); } while (0);
    return 0;
}

static _Py_Identifier name_op[] = {
    {0, "__lt__", 0},
    {0, "__le__", 0},
    {0, "__eq__", 0},
    {0, "__ne__", 0},
    {0, "__gt__", 0},
    {0, "__ge__", 0}
};

static PyObject *
slot_tp_richcompare(PyObject *self, PyObject *other, int op)
{
    PyObject *func, *args, *res;

    func = lookup_method(self, &name_op[op]);
    if (func == ((void *)0)) {
        PyErr_Clear();
        return ( ((PyObject*)((&_Py_NotImplementedStruct)))->ob_refcnt++), (&_Py_NotImplementedStruct);
    }
    args = PyTuple_Pack(1, other);
    if (args == ((void *)0))
        res = ((void *)0);
    else {
        res = PyObject_Call(func, args, ((void *)0));
        do { if ( --((PyObject*)(args))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(args)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(args)))); } while (0);
    }
    do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0);
    return res;
}

static PyObject *
slot_tp_iter(PyObject *self)
{
    PyObject *func, *res;
    static _Py_Identifier PyId___iter__ = { 0, "__iter__", 0 };

    func = lookup_method(self, &PyId___iter__);
    if (func != ((void *)0)) {
        PyObject *args;
        args = res = PyTuple_New(0);
        if (args != ((void *)0)) {
            res = PyObject_Call(func, args, ((void *)0));
            do { if ( --((PyObject*)(args))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(args)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(args)))); } while (0);
        }
        do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0);
        return res;
    }
    PyErr_Clear();
    func = lookup_method(self, &PyId___getitem__);
    if (func == ((void *)0)) {
        PyErr_Format(PyExc_TypeError,
                     "'%.200s' object is not iterable",
                     (((PyObject*)(self))->ob_type)->tp_name);
        return ((void *)0);
    }
    do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0);
    return PySeqIter_New(self);
}

static PyObject *
slot_tp_iternext(PyObject *self)
{
    static _Py_Identifier PyId___next__ = { 0, "__next__", 0 };
    return call_method(self, &PyId___next__, "()");
}

static PyObject *
slot_tp_descr_get(PyObject *self, PyObject *obj, PyObject *type)
{
    PyTypeObject *tp = (((PyObject*)(self))->ob_type);
    PyObject *get;
    static _Py_Identifier PyId___get__ = { 0, "__get__", 0 };

    get = _PyType_LookupId(tp, &PyId___get__);
    if (get == ((void *)0)) {

        if (tp->tp_descr_get == slot_tp_descr_get)
            tp->tp_descr_get = ((void *)0);
        ( ((PyObject*)(self))->ob_refcnt++);
        return self;
    }
    if (obj == ((void *)0))
        obj = (&_Py_NoneStruct);
    if (type == ((void *)0))
        type = (&_Py_NoneStruct);
    return PyObject_CallFunctionObjArgs(get, self, obj, type, ((void *)0));
}

static int
slot_tp_descr_set(PyObject *self, PyObject *target, PyObject *value)
{
    PyObject *res;
    static _Py_Identifier PyId___delete__ = { 0, "__delete__", 0 };
    static _Py_Identifier PyId___set__ = { 0, "__set__", 0 };

    if (value == ((void *)0))
        res = call_method(self, &PyId___delete__, "(O)", target);
    else
        res = call_method(self, &PyId___set__, "(OO)", target, value);
    if (res == ((void *)0))
        return -1;
    do { if ( --((PyObject*)(res))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(res)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(res)))); } while (0);
    return 0;
}

static int
slot_tp_init(PyObject *self, PyObject *args, PyObject *kwds)
{
    static _Py_Identifier PyId___init__ = { 0, "__init__", 0 };
    PyObject *meth = lookup_method(self, &PyId___init__);
    PyObject *res;

    if (meth == ((void *)0))
        return -1;
    res = PyObject_Call(meth, args, kwds);
    do { if ( --((PyObject*)(meth))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(meth)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(meth)))); } while (0);
    if (res == ((void *)0))
        return -1;
    if (res != (&_Py_NoneStruct)) {
        PyErr_Format(PyExc_TypeError,
                     "__init__() should return None, not '%.200s'",
                     (((PyObject*)(res))->ob_type)->tp_name);
        do { if ( --((PyObject*)(res))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(res)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(res)))); } while (0);
        return -1;
    }
    do { if ( --((PyObject*)(res))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(res)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(res)))); } while (0);
    return 0;
}

static PyObject *
slot_tp_new(PyTypeObject *type, PyObject *args, PyObject *kwds)
{
    PyObject *func;
    PyObject *newargs, *x;
    Py_ssize_t i, n;
    static _Py_Identifier PyId___new__ = { 0, "__new__", 0 };

    func = _PyObject_GetAttrId((PyObject *)type, &PyId___new__);
    if (func == ((void *)0))
        return ((void *)0);
    (__builtin_expect(!(((((((PyObject*)(args))->ob_type))->tp_flags & ((1L<<26))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 5591, "PyTuple_Check(args)") : (void)0);
    n = (((PyVarObject*)(args))->ob_size);
    newargs = PyTuple_New(n+1);
    if (newargs == ((void *)0))
        return ((void *)0);
    ( ((PyObject*)(type))->ob_refcnt++);
    (((PyTupleObject *)(newargs))->ob_item[0] = (PyObject *)type);
    for (i = 0; i < n; i++) {
        x = (((PyTupleObject *)(args))->ob_item[i]);
        ( ((PyObject*)(x))->ob_refcnt++);
        (((PyTupleObject *)(newargs))->ob_item[i+1] = x);
    }
    x = PyObject_Call(func, newargs, kwds);
    do { if ( --((PyObject*)(newargs))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(newargs)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(newargs)))); } while (0);
    do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0);
    return x;
}

static void
slot_tp_del(PyObject *self)
{
    static _Py_Identifier PyId___del__ = { 0, "__del__", 0 };
    PyObject *del, *res;
    PyObject *error_type, *error_value, *error_traceback;


    (__builtin_expect(!(self->ob_refcnt == 0), 0) ? __assert_rtn(__func__, "typeobject.c", 5617, "self->ob_refcnt == 0") : (void)0);
    self->ob_refcnt = 1;


    PyErr_Fetch(&error_type, &error_value, &error_traceback);


    del = lookup_maybe(self, &PyId___del__);
    if (del != ((void *)0)) {
        res = PyEval_CallObjectWithKeywords(del, ((void *)0), (PyObject *)((void *)0));
        if (res == ((void *)0))
            PyErr_WriteUnraisable(del);
        else
            do { if ( --((PyObject*)(res))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(res)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(res)))); } while (0);
        do { if ( --((PyObject*)(del))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(del)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(del)))); } while (0);
    }


    PyErr_Restore(error_type, error_value, error_traceback);




    (__builtin_expect(!(self->ob_refcnt > 0), 0) ? __assert_rtn(__func__, "typeobject.c", 5640, "self->ob_refcnt > 0") : (void)0);
    if (--self->ob_refcnt == 0)
        return;




    {
        Py_ssize_t refcnt = self->ob_refcnt;
        ( (((PyObject*)(self))->ob_refcnt) = 1);
        self->ob_refcnt = refcnt;
    }
    (__builtin_expect(!(!(((((((PyObject*)(self))->ob_type)))->tp_flags & ((1L<<14))) != 0) || ((PyGC_Head *)(self)-1)->gc.gc_refs != (-2)), 0) ? __assert_rtn(__func__, "typeobject.c", 5653, "!PyType_IS_GC(Py_TYPE(self)) || _Py_AS_GC(self)->gc.gc_refs != _PyGC_REFS_UNTRACKED") : (void)0);



    ;
# 5667 "typeobject.c"
}
# 5680 "typeobject.c"
typedef struct wrapperbase slotdef;
# 5727 "typeobject.c"
static slotdef slotdefs[] = {
    {"__len__", __builtin_offsetof (PyHeapTypeObject, as_sequence.sq_length), (void *)(slot_sq_length), wrap_lenfunc, "x.__len__() <==> len(x)"},






    {"__add__", __builtin_offsetof (PyHeapTypeObject, as_sequence.sq_concat), (void *)(((void *)0)), wrap_binaryfunc, "x.__add__(y) <==> x+y"},

    {"__mul__", __builtin_offsetof (PyHeapTypeObject, as_sequence.sq_repeat), (void *)(((void *)0)), wrap_indexargfunc, "x.__mul__(n) <==> x*n"},

    {"__rmul__", __builtin_offsetof (PyHeapTypeObject, as_sequence.sq_repeat), (void *)(((void *)0)), wrap_indexargfunc, "x.__rmul__(n) <==> n*x"},

    {"__getitem__", __builtin_offsetof (PyHeapTypeObject, as_sequence.sq_item), (void *)(slot_sq_item), wrap_sq_item, "x.__getitem__(y) <==> x[y]"},

    {"__setitem__", __builtin_offsetof (PyHeapTypeObject, as_sequence.sq_ass_item), (void *)(slot_sq_ass_item), wrap_sq_setitem, "x.__setitem__(i, y) <==> x[i]=y"},

    {"__delitem__", __builtin_offsetof (PyHeapTypeObject, as_sequence.sq_ass_item), (void *)(slot_sq_ass_item), wrap_sq_delitem, "x.__delitem__(y) <==> del x[y]"},

    {"__contains__", __builtin_offsetof (PyHeapTypeObject, as_sequence.sq_contains), (void *)(slot_sq_contains), wrap_objobjproc, "x.__contains__(y) <==> y in x"},

    {"__iadd__", __builtin_offsetof (PyHeapTypeObject, as_sequence.sq_inplace_concat), (void *)(((void *)0)), wrap_binaryfunc, "x.__iadd__(y) <==> x+=y"},

    {"__imul__", __builtin_offsetof (PyHeapTypeObject, as_sequence.sq_inplace_repeat), (void *)(((void *)0)), wrap_indexargfunc, "x.__imul__(y) <==> x*=y"},


    {"__len__", __builtin_offsetof (PyHeapTypeObject, as_mapping.mp_length), (void *)(slot_sq_length), wrap_lenfunc, "x.__len__() <==> len(x)"},

    {"__getitem__", __builtin_offsetof (PyHeapTypeObject, as_mapping.mp_subscript), (void *)(slot_mp_subscript), wrap_binaryfunc, "x.__getitem__(y) <==> x[y]"},


    {"__setitem__", __builtin_offsetof (PyHeapTypeObject, as_mapping.mp_ass_subscript), (void *)(slot_mp_ass_subscript), wrap_objobjargproc, "x.__setitem__(i, y) <==> x[i]=y"},


    {"__delitem__", __builtin_offsetof (PyHeapTypeObject, as_mapping.mp_ass_subscript), (void *)(slot_mp_ass_subscript), wrap_delitem, "x.__delitem__(y) <==> del x[y]"},



    {"__add__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_add), (void *)(slot_nb_add), wrap_binaryfunc_l, "x." "__add__" "(y) <==> x" "+" "y"},

    {"__radd__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_add), (void *)(slot_nb_add), wrap_binaryfunc_r, "x." "__radd__" "(y) <==> y" "+" "x"},

    {"__sub__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_subtract), (void *)(slot_nb_subtract), wrap_binaryfunc_l, "x." "__sub__" "(y) <==> x" "-" "y"},

    {"__rsub__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_subtract), (void *)(slot_nb_subtract), wrap_binaryfunc_r, "x." "__rsub__" "(y) <==> y" "-" "x"},

    {"__mul__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_multiply), (void *)(slot_nb_multiply), wrap_binaryfunc_l, "x." "__mul__" "(y) <==> x" "*" "y"},

    {"__rmul__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_multiply), (void *)(slot_nb_multiply), wrap_binaryfunc_r, "x." "__rmul__" "(y) <==> y" "*" "x"},

    {"__mod__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_remainder), (void *)(slot_nb_remainder), wrap_binaryfunc_l, "x." "__mod__" "(y) <==> x" "%" "y"},

    {"__rmod__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_remainder), (void *)(slot_nb_remainder), wrap_binaryfunc_r, "x." "__rmod__" "(y) <==> y" "%" "x"},

    {"__divmod__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_divmod), (void *)(slot_nb_divmod), wrap_binaryfunc_l, "x." "__divmod__" "(y) <==> " "divmod(x, y)"},

    {"__rdivmod__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_divmod), (void *)(slot_nb_divmod), wrap_binaryfunc_r, "x." "__rdivmod__" "(y) <==> " "divmod(y, x)"},

    {"__pow__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_power), (void *)(slot_nb_power), wrap_ternaryfunc, "x.__pow__(y[, z]) <==> pow(x, y[, z])"},

    {"__rpow__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_power), (void *)(slot_nb_power), wrap_ternaryfunc_r, "y.__rpow__(x[, z]) <==> pow(x, y[, z])"},

    {"__neg__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_negative), (void *)(slot_nb_negative), wrap_unaryfunc, "x." "__neg__" "() <==> " "-x"},
    {"__pos__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_positive), (void *)(slot_nb_positive), wrap_unaryfunc, "x." "__pos__" "() <==> " "+x"},
    {"__abs__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_absolute), (void *)(slot_nb_absolute), wrap_unaryfunc, "x." "__abs__" "() <==> " "abs(x)"},

    {"__bool__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_bool), (void *)(slot_nb_bool), wrap_inquirypred, "x." "__bool__" "() <==> " "x != 0"},

    {"__invert__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_invert), (void *)(slot_nb_invert), wrap_unaryfunc, "x." "__invert__" "() <==> " "~x"},
    {"__lshift__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_lshift), (void *)(slot_nb_lshift), wrap_binaryfunc_l, "x." "__lshift__" "(y) <==> x" "<<" "y"},
    {"__rlshift__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_lshift), (void *)(slot_nb_lshift), wrap_binaryfunc_r, "x." "__rlshift__" "(y) <==> y" "<<" "x"},
    {"__rshift__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_rshift), (void *)(slot_nb_rshift), wrap_binaryfunc_l, "x." "__rshift__" "(y) <==> x" ">>" "y"},
    {"__rrshift__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_rshift), (void *)(slot_nb_rshift), wrap_binaryfunc_r, "x." "__rrshift__" "(y) <==> y" ">>" "x"},
    {"__and__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_and), (void *)(slot_nb_and), wrap_binaryfunc_l, "x." "__and__" "(y) <==> x" "&" "y"},
    {"__rand__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_and), (void *)(slot_nb_and), wrap_binaryfunc_r, "x." "__rand__" "(y) <==> y" "&" "x"},
    {"__xor__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_xor), (void *)(slot_nb_xor), wrap_binaryfunc_l, "x." "__xor__" "(y) <==> x" "^" "y"},
    {"__rxor__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_xor), (void *)(slot_nb_xor), wrap_binaryfunc_r, "x." "__rxor__" "(y) <==> y" "^" "x"},
    {"__or__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_or), (void *)(slot_nb_or), wrap_binaryfunc_l, "x." "__or__" "(y) <==> x" "|" "y"},
    {"__ror__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_or), (void *)(slot_nb_or), wrap_binaryfunc_r, "x." "__ror__" "(y) <==> y" "|" "x"},
    {"__int__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_int), (void *)(slot_nb_int), wrap_unaryfunc, "x." "__int__" "() <==> " "int(x)"},

    {"__float__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_float), (void *)(slot_nb_float), wrap_unaryfunc, "x." "__float__" "() <==> " "float(x)"},

    {"__index__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_index), (void *)(slot_nb_index), wrap_unaryfunc, "x[y:z] <==> x[y.__index__():z.__index__()]"},

    {"__iadd__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_add), (void *)(slot_nb_inplace_add), wrap_binaryfunc, "x." "__iadd__" "(y) <==> x" "+=" "y"},

    {"__isub__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_subtract), (void *)(slot_nb_inplace_subtract), wrap_binaryfunc, "x." "__isub__" "(y) <==> x" "-=" "y"},

    {"__imul__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_multiply), (void *)(slot_nb_inplace_multiply), wrap_binaryfunc, "x." "__imul__" "(y) <==> x" "*=" "y"},

    {"__imod__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_remainder), (void *)(slot_nb_inplace_remainder), wrap_binaryfunc, "x." "__imod__" "(y) <==> x" "%=" "y"},

    {"__ipow__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_power), (void *)(slot_nb_inplace_power), wrap_binaryfunc, "x." "__ipow__" "(y) <==> x" "**=" "y"},

    {"__ilshift__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_lshift), (void *)(slot_nb_inplace_lshift), wrap_binaryfunc, "x." "__ilshift__" "(y) <==> x" "<<=" "y"},

    {"__irshift__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_rshift), (void *)(slot_nb_inplace_rshift), wrap_binaryfunc, "x." "__irshift__" "(y) <==> x" ">>=" "y"},

    {"__iand__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_and), (void *)(slot_nb_inplace_and), wrap_binaryfunc, "x." "__iand__" "(y) <==> x" "&=" "y"},

    {"__ixor__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_xor), (void *)(slot_nb_inplace_xor), wrap_binaryfunc, "x." "__ixor__" "(y) <==> x" "^=" "y"},

    {"__ior__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_or), (void *)(slot_nb_inplace_or), wrap_binaryfunc, "x." "__ior__" "(y) <==> x" "|=" "y"},

    {"__floordiv__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_floor_divide), (void *)(slot_nb_floor_divide), wrap_binaryfunc_l, "x." "__floordiv__" "(y) <==> x" "//" "y"},
    {"__rfloordiv__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_floor_divide), (void *)(slot_nb_floor_divide), wrap_binaryfunc_r, "x." "__rfloordiv__" "(y) <==> y" "//" "x"},
    {"__truediv__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_true_divide), (void *)(slot_nb_true_divide), wrap_binaryfunc_l, "x." "__truediv__" "(y) <==> x" "/" "y"},
    {"__rtruediv__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_true_divide), (void *)(slot_nb_true_divide), wrap_binaryfunc_r, "x." "__rtruediv__" "(y) <==> y" "/" "x"},
    {"__ifloordiv__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_floor_divide), (void *)(slot_nb_inplace_floor_divide), wrap_binaryfunc, "x." "__ifloordiv__" "(y) <==> x" "//" "y"},

    {"__itruediv__", __builtin_offsetof (PyHeapTypeObject, as_number.nb_inplace_true_divide), (void *)(slot_nb_inplace_true_divide), wrap_binaryfunc, "x." "__itruediv__" "(y) <==> x" "/" "y"},


    {"__str__", __builtin_offsetof (PyTypeObject, tp_str), (void *)(slot_tp_str), wrap_unaryfunc, "x.__str__() <==> str(x)"},

    {"__repr__", __builtin_offsetof (PyTypeObject, tp_repr), (void *)(slot_tp_repr), wrap_unaryfunc, "x.__repr__() <==> repr(x)"},

    {"__hash__", __builtin_offsetof (PyTypeObject, tp_hash), (void *)(slot_tp_hash), wrap_hashfunc, "x.__hash__() <==> hash(x)"},

    {"__call__", __builtin_offsetof (PyTypeObject, tp_call), (void *)(slot_tp_call), (wrapperfunc)wrap_call, "x.__call__(...) <==> x(...)", 1},

    {"__getattribute__", __builtin_offsetof (PyTypeObject, tp_getattro), (void *)(slot_tp_getattr_hook), wrap_binaryfunc, "x.__getattribute__('name') <==> x.name"},

    {"__getattribute__", __builtin_offsetof (PyTypeObject, tp_getattr), (void *)(((void *)0)), ((void *)0), ""},
    {"__getattr__", __builtin_offsetof (PyTypeObject, tp_getattro), (void *)(slot_tp_getattr_hook), ((void *)0), ""},
    {"__getattr__", __builtin_offsetof (PyTypeObject, tp_getattr), (void *)(((void *)0)), ((void *)0), ""},
    {"__setattr__", __builtin_offsetof (PyTypeObject, tp_setattro), (void *)(slot_tp_setattro), wrap_setattr, "x.__setattr__('name', value) <==> x.name = value"},

    {"__setattr__", __builtin_offsetof (PyTypeObject, tp_setattr), (void *)(((void *)0)), ((void *)0), ""},
    {"__delattr__", __builtin_offsetof (PyTypeObject, tp_setattro), (void *)(slot_tp_setattro), wrap_delattr, "x.__delattr__('name') <==> del x.name"},

    {"__delattr__", __builtin_offsetof (PyTypeObject, tp_setattr), (void *)(((void *)0)), ((void *)0), ""},
    {"__lt__", __builtin_offsetof (PyTypeObject, tp_richcompare), (void *)(slot_tp_richcompare), richcmp_lt, "x.__lt__(y) <==> x<y"},

    {"__le__", __builtin_offsetof (PyTypeObject, tp_richcompare), (void *)(slot_tp_richcompare), richcmp_le, "x.__le__(y) <==> x<=y"},

    {"__eq__", __builtin_offsetof (PyTypeObject, tp_richcompare), (void *)(slot_tp_richcompare), richcmp_eq, "x.__eq__(y) <==> x==y"},

    {"__ne__", __builtin_offsetof (PyTypeObject, tp_richcompare), (void *)(slot_tp_richcompare), richcmp_ne, "x.__ne__(y) <==> x!=y"},

    {"__gt__", __builtin_offsetof (PyTypeObject, tp_richcompare), (void *)(slot_tp_richcompare), richcmp_gt, "x.__gt__(y) <==> x>y"},

    {"__ge__", __builtin_offsetof (PyTypeObject, tp_richcompare), (void *)(slot_tp_richcompare), richcmp_ge, "x.__ge__(y) <==> x>=y"},

    {"__iter__", __builtin_offsetof (PyTypeObject, tp_iter), (void *)(slot_tp_iter), wrap_unaryfunc, "x.__iter__() <==> iter(x)"},

    {"__next__", __builtin_offsetof (PyTypeObject, tp_iternext), (void *)(slot_tp_iternext), wrap_next, "x.__next__() <==> next(x)"},

    {"__get__", __builtin_offsetof (PyTypeObject, tp_descr_get), (void *)(slot_tp_descr_get), wrap_descr_get, "descr.__get__(obj[, type]) -> value"},

    {"__set__", __builtin_offsetof (PyTypeObject, tp_descr_set), (void *)(slot_tp_descr_set), wrap_descr_set, "descr.__set__(obj, value)"},

    {"__delete__", __builtin_offsetof (PyTypeObject, tp_descr_set), (void *)(slot_tp_descr_set), wrap_descr_delete, "descr.__delete__(obj)"},

    {"__init__", __builtin_offsetof (PyTypeObject, tp_init), (void *)(slot_tp_init), (wrapperfunc)wrap_init, "x.__init__(...) initializes x; " "see help(type(x)) for signature", 1},



    {"__new__", __builtin_offsetof (PyTypeObject, tp_new), (void *)(slot_tp_new), ((void *)0), ""},
    {"__del__", __builtin_offsetof (PyTypeObject, tp_del), (void *)(slot_tp_del), ((void *)0), ""},
    {((void *)0)}
};






static void **
slotptr(PyTypeObject *type, int ioffset)
{
    char *ptr;
    long offset = ioffset;


    (__builtin_expect(!(offset >= 0), 0) ? __assert_rtn(__func__, "typeobject.c", 5904, "offset >= 0") : (void)0);
    (__builtin_expect(!((size_t)offset < __builtin_offsetof (PyHeapTypeObject, as_buffer)), 0) ? __assert_rtn(__func__, "typeobject.c", 5905, "(size_t)offset < offsetof(PyHeapTypeObject, as_buffer)") : (void)0);
    if ((size_t)offset >= __builtin_offsetof (PyHeapTypeObject, as_sequence)) {
        ptr = (char *)type->tp_as_sequence;
        offset -= __builtin_offsetof (PyHeapTypeObject, as_sequence);
    }
    else if ((size_t)offset >= __builtin_offsetof (PyHeapTypeObject, as_mapping)) {
        ptr = (char *)type->tp_as_mapping;
        offset -= __builtin_offsetof (PyHeapTypeObject, as_mapping);
    }
    else if ((size_t)offset >= __builtin_offsetof (PyHeapTypeObject, as_number)) {
        ptr = (char *)type->tp_as_number;
        offset -= __builtin_offsetof (PyHeapTypeObject, as_number);
    }
    else {
        ptr = (char *)type;
    }
    if (ptr != ((void *)0))
        ptr += offset;
    return (void **)ptr;
}
# 5934 "typeobject.c"
static void **
resolve_slotdups(PyTypeObject *type, PyObject *name)
{



    static PyObject *pname;
    static slotdef *ptrs[10];
    slotdef *p, **pp;
    void **res, **ptr;

    if (pname != name) {

        pname = name;
        pp = ptrs;
        for (p = slotdefs; p->name_strobj; p++) {
            if (p->name_strobj == name)
                *pp++ = p;
        }
        *pp = ((void *)0);
    }



    res = ((void *)0);
    for (pp = ptrs; *pp; pp++) {
        ptr = slotptr(type, (*pp)->offset);
        if (ptr == ((void *)0) || *ptr == ((void *)0))
            continue;
        if (res != ((void *)0))
            return ((void *)0);
        res = ptr;
    }
    return res;
}







static slotdef *
update_one_slot(PyTypeObject *type, slotdef *p)
{
    PyObject *descr;
    PyWrapperDescrObject *d;
    void *generic = ((void *)0), *specific = ((void *)0);
    int use_generic = 0;
    int offset = p->offset;
    void **ptr = slotptr(type, offset);

    if (ptr == ((void *)0)) {
        do {
            ++p;
        } while (p->offset == offset);
        return p;
    }
    do {
        descr = _PyType_Lookup(type, p->name_strobj);
        if (descr == ((void *)0)) {
            if (ptr == (void**)&type->tp_iternext) {
                specific = (void *)_PyObject_NextNotImplemented;
            }
            continue;
        }
        if ((((PyObject*)(descr))->ob_type) == &PyWrapperDescr_Type &&
            ((PyWrapperDescrObject *)descr)->d_base->name_strobj == p->name_strobj) {
            void **tptr = resolve_slotdups(type, p->name_strobj);
            if (tptr == ((void *)0) || tptr == ptr)
                generic = p->function;
            d = (PyWrapperDescrObject *)descr;
            if (d->d_base->wrapper == p->wrapper &&
                PyType_IsSubtype(type, (((PyDescrObject *)(d))->d_type)))
            {
                if (specific == ((void *)0) ||
                    specific == d->d_wrapped)
                    specific = d->d_wrapped;
                else
                    use_generic = 1;
            }
        }
        else if ((((PyObject*)(descr))->ob_type) == &PyCFunction_Type &&
                 (((PyCFunctionObject *)descr) -> m_ml -> ml_meth) ==
                 (PyCFunction)tp_new_wrapper &&
                 ptr == (void**)&type->tp_new)
        {
# 6032 "typeobject.c"
            specific = (void *)type->tp_new;




        }
        else if (descr == (&_Py_NoneStruct) &&
                 ptr == (void**)&type->tp_hash) {



            specific = (void *)PyObject_HashNotImplemented;
        }
        else {
            use_generic = 1;
            generic = p->function;
        }
    } while ((++p)->offset == offset);
    if (specific && !use_generic)
        *ptr = specific;
    else
        *ptr = generic;
    return p;
}



static int
update_slots_callback(PyTypeObject *type, void *data)
{
    slotdef **pp = (slotdef **)data;

    for (; *pp; pp++)
        update_one_slot(type, *pp);
    return 0;
}



static int
slotdef_cmp(const void *aa, const void *bb)
{
    const slotdef *a = (const slotdef *)aa, *b = (const slotdef *)bb;
    int c = a->offset - b->offset;
    if (c != 0)
        return c;
    else


        return (a > b) ? 1 : (a < b) ? -1 : 0;
}



static void
init_slotdefs(void)
{
    slotdef *p;
    static int initialized = 0;

    if (initialized)
        return;
    for (p = slotdefs; p->name; p++) {
        p->name_strobj = PyUnicode_InternFromString(p->name);
        if (!p->name_strobj)
            Py_FatalError("Out of memory interning slotdef names");
    }
    qsort((void *)slotdefs, (size_t)(p-slotdefs), sizeof(slotdef),
          slotdef_cmp);
    initialized = 1;
}


static int
update_slot(PyTypeObject *type, PyObject *name)
{
    slotdef *ptrs[10];
    slotdef *p;
    slotdef **pp;
    int offset;






    PyType_Modified(type);

    init_slotdefs();
    pp = ptrs;
    for (p = slotdefs; p->name; p++) {

        if (p->name_strobj == name)
            *pp++ = p;
    }
    *pp = ((void *)0);
    for (pp = ptrs; *pp; pp++) {
        p = *pp;
        offset = p->offset;
        while (p > slotdefs && (p-1)->offset == offset)
            --p;
        *pp = p;
    }
    if (ptrs[0] == ((void *)0))
        return 0;
    return update_subclasses(type, name,
                             update_slots_callback, (void *)ptrs);
}




static void
fixup_slot_dispatchers(PyTypeObject *type)
{
    slotdef *p;

    init_slotdefs();
    for (p = slotdefs; p->name; )
        p = update_one_slot(type, p);
}

static void
update_all_slots(PyTypeObject* type)
{
    slotdef *p;

    init_slotdefs();
    for (p = slotdefs; p->name; p++) {

        update_slot(type, p->name_strobj);
    }
}





static int
update_subclasses(PyTypeObject *type, PyObject *name,
                  update_callback callback, void *data)
{
    if (callback(type, data) < 0)
        return -1;
    return recurse_down_subclasses(type, name, callback, data);
}

static int
recurse_down_subclasses(PyTypeObject *type, PyObject *name,
                        update_callback callback, void *data)
{
    PyTypeObject *subclass;
    PyObject *ref, *subclasses, *dict;
    Py_ssize_t i, n;

    subclasses = type->tp_subclasses;
    if (subclasses == ((void *)0))
        return 0;
    (__builtin_expect(!(((((((PyObject*)(subclasses))->ob_type))->tp_flags & ((1L<<25))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 6190, "PyList_Check(subclasses)") : (void)0);
    n = (((PyVarObject*)(subclasses))->ob_size);
    for (i = 0; i < n; i++) {
        ref = (((PyListObject *)(subclasses))->ob_item[i]);
        (__builtin_expect(!(((((PyObject*)(ref))->ob_type) == (&_PyWeakref_RefType) || PyType_IsSubtype((((PyObject*)(ref))->ob_type), (&_PyWeakref_RefType)))), 0) ? __assert_rtn(__func__, "typeobject.c", 6194, "PyWeakref_CheckRef(ref)") : (void)0);
        subclass = (PyTypeObject *)((((PyObject*)(((PyWeakReference *)(ref))->wr_object))->ob_refcnt) > 0 ? ((PyWeakReference *)(ref))->wr_object : (&_Py_NoneStruct));
        (__builtin_expect(!(subclass != ((void *)0)), 0) ? __assert_rtn(__func__, "typeobject.c", 6196, "subclass != NULL") : (void)0);
        if ((PyObject *)subclass == (&_Py_NoneStruct))
            continue;
        (__builtin_expect(!(((((((PyObject*)(subclass))->ob_type))->tp_flags & ((1L<<31))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 6199, "PyType_Check(subclass)") : (void)0);

        dict = subclass->tp_dict;
        if (dict != ((void *)0) && ((((((PyObject*)(dict))->ob_type))->tp_flags & ((1L<<29))) != 0) &&
            PyDict_GetItem(dict, name) != ((void *)0))
            continue;
        if (update_subclasses(subclass, name, callback, data) < 0)
            return -1;
    }
    return 0;
}
# 6241 "typeobject.c"
static int
add_operators(PyTypeObject *type)
{
    PyObject *dict = type->tp_dict;
    slotdef *p;
    PyObject *descr;
    void **ptr;

    init_slotdefs();
    for (p = slotdefs; p->name; p++) {
        if (p->wrapper == ((void *)0))
            continue;
        ptr = slotptr(type, p->offset);
        if (!ptr || !*ptr)
            continue;
        if (PyDict_GetItem(dict, p->name_strobj))
            continue;
        if (*ptr == (void *)PyObject_HashNotImplemented) {



            if (PyDict_SetItem(dict, p->name_strobj, (&_Py_NoneStruct)) < 0)
                return -1;
        }
        else {
            descr = PyDescr_NewWrapper(type, p, *ptr);
            if (descr == ((void *)0))
                return -1;
            if (PyDict_SetItem(dict, p->name_strobj, descr) < 0)
                return -1;
            do { if ( --((PyObject*)(descr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(descr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(descr)))); } while (0);
        }
    }
    if (type->tp_new != ((void *)0)) {
        if (add_tp_new_wrapper(type) < 0)
            return -1;
    }
    return 0;
}




typedef struct {
    PyObject ob_base;
    PyTypeObject *type;
    PyObject *obj;
    PyTypeObject *obj_type;
} superobject;

static PyMemberDef super_members[] = {
    {"__thisclass__", 6, __builtin_offsetof (superobject, type), 1,
     "the class invoking super()"},
    {"__self__", 6, __builtin_offsetof (superobject, obj), 1,
     "the instance invoking super(); may be None"},
    {"__self_class__", 6, __builtin_offsetof (superobject, obj_type), 1,
     "the type of the instance invoking super(); may be None"},
    {0}
};

static void
super_dealloc(PyObject *self)
{
    superobject *su = (superobject *)self;

    do { PyGC_Head *g = ((PyGC_Head *)(self)-1); (__builtin_expect(!(g->gc.gc_refs != (-2)), 0) ? __assert_rtn(__func__, "typeobject.c", 6306, "g->gc.gc_refs != _PyGC_REFS_UNTRACKED") : (void)0); g->gc.gc_refs = (-2); g->gc.gc_prev->gc.gc_next = g->gc.gc_next; g->gc.gc_next->gc.gc_prev = g->gc.gc_prev; g->gc.gc_next = ((void *)0); } while (0);;
    do { if ((su->obj) == ((void *)0)) ; else do { if ( --((PyObject*)(su->obj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(su->obj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(su->obj)))); } while (0); } while (0);
    do { if ((su->type) == ((void *)0)) ; else do { if ( --((PyObject*)(su->type))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(su->type)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(su->type)))); } while (0); } while (0);
    do { if ((su->obj_type) == ((void *)0)) ; else do { if ( --((PyObject*)(su->obj_type))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(su->obj_type)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(su->obj_type)))); } while (0); } while (0);
    (((PyObject*)(self))->ob_type)->tp_free(self);
}

static PyObject *
super_repr(PyObject *self)
{
    superobject *su = (superobject *)self;

    if (su->obj_type)
        return PyUnicode_FromFormat(
            "<super: <class '%s'>, <%s object>>",
            su->type ? su->type->tp_name : "NULL",
            su->obj_type->tp_name);
    else
        return PyUnicode_FromFormat(
            "<super: <class '%s'>, NULL>",
            su->type ? su->type->tp_name : "NULL");
}

static PyObject *
super_getattro(PyObject *self, PyObject *name)
{
    superobject *su = (superobject *)self;
    int skip = su->obj_type == ((void *)0);

    if (!skip) {


        skip = (((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0) &&
            ((__builtin_expect(!(((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 6339, "PyUnicode_Check(name)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)name)->state.ready)), 0) ? __assert_rtn(__func__, "typeobject.c", 6339, "PyUnicode_IS_READY(name)") : (void)0), ((PyASCIIObject *)(name))->length) == 9 &&
            PyUnicode_CompareWithASCIIString(name, "__class__") == 0);
    }

    if (!skip) {
        PyObject *mro, *res, *tmp, *dict;
        PyTypeObject *starttype;
        descrgetfunc f;
        Py_ssize_t i, n;

        starttype = su->obj_type;
        mro = starttype->tp_mro;

        if (mro == ((void *)0))
            n = 0;
        else {
            (__builtin_expect(!(((((((PyObject*)(mro))->ob_type))->tp_flags & ((1L<<26))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 6355, "PyTuple_Check(mro)") : (void)0);
            n = (((PyVarObject*)(mro))->ob_size);
        }
        for (i = 0; i < n; i++) {
            if ((PyObject *)(su->type) == (((PyTupleObject *)(mro))->ob_item[i]))
                break;
        }
        i++;
        res = ((void *)0);


        ( ((PyObject*)(mro))->ob_refcnt++);
        for (; i < n; i++) {
            tmp = (((PyTupleObject *)(mro))->ob_item[i]);
            if (((((((PyObject*)(tmp))->ob_type))->tp_flags & ((1L<<31))) != 0))
                dict = ((PyTypeObject *)tmp)->tp_dict;
            else
                continue;
            res = PyDict_GetItem(dict, name);
            if (res != ((void *)0)) {
                ( ((PyObject*)(res))->ob_refcnt++);
                f = (((PyObject*)(res))->ob_type)->tp_descr_get;
                if (f != ((void *)0)) {
                    tmp = f(res,




                        (su->obj == (PyObject *)
                                    su->obj_type
                            ? (PyObject *)((void *)0)
                            : su->obj),
                        (PyObject *)starttype);
                    do { if ( --((PyObject*)(res))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(res)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(res)))); } while (0);
                    res = tmp;
                }
                do { if ( --((PyObject*)(mro))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(mro)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(mro)))); } while (0);
                return res;
            }
        }
        do { if ( --((PyObject*)(mro))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(mro)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(mro)))); } while (0);
    }
    return PyObject_GenericGetAttr(self, name);
}

static PyTypeObject *
supercheck(PyTypeObject *type, PyObject *obj)
{
# 6419 "typeobject.c"
    if (((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<31))) != 0) && PyType_IsSubtype((PyTypeObject *)obj, type)) {
        ( ((PyObject*)(obj))->ob_refcnt++);
        return (PyTypeObject *)obj;
    }


    if (PyType_IsSubtype((((PyObject*)(obj))->ob_type), type)) {
        ( ((PyObject*)((((PyObject*)(obj))->ob_type)))->ob_refcnt++);
        return (((PyObject*)(obj))->ob_type);
    }
    else {

        PyObject *class_attr;

        class_attr = _PyObject_GetAttrId(obj, &PyId___class__);
        if (class_attr != ((void *)0) &&
            ((((((PyObject*)(class_attr))->ob_type))->tp_flags & ((1L<<31))) != 0) &&
            (PyTypeObject *)class_attr != (((PyObject*)(obj))->ob_type))
        {
            int ok = PyType_IsSubtype(
                (PyTypeObject *)class_attr, type);
            if (ok)
                return (PyTypeObject *)class_attr;
        }

        if (class_attr == ((void *)0))
            PyErr_Clear();
        else
            do { if ( --((PyObject*)(class_attr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(class_attr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(class_attr)))); } while (0);
    }

    PyErr_SetString(PyExc_TypeError,
                    "super(type, obj): "
                    "obj must be an instance or subtype of type");
    return ((void *)0);
}

static PyObject *
super_descr_get(PyObject *self, PyObject *obj, PyObject *type)
{
    superobject *su = (superobject *)self;
    superobject *newobj;

    if (obj == ((void *)0) || obj == (&_Py_NoneStruct) || su->obj != ((void *)0)) {

        ( ((PyObject*)(self))->ob_refcnt++);
        return self;
    }
    if ((((PyObject*)(su))->ob_type) != &PySuper_Type)


        return PyObject_CallFunctionObjArgs((PyObject *)(((PyObject*)(su))->ob_type),
                                            su->type, obj, ((void *)0));
    else {

        PyTypeObject *obj_type = supercheck(su->type, obj);
        if (obj_type == ((void *)0))
            return ((void *)0);
        newobj = (superobject *)PySuper_Type.tp_new(&PySuper_Type,
                                                 ((void *)0), ((void *)0));
        if (newobj == ((void *)0))
            return ((void *)0);
        ( ((PyObject*)(su->type))->ob_refcnt++);
        ( ((PyObject*)(obj))->ob_refcnt++);
        newobj->type = su->type;
        newobj->obj = obj;
        newobj->obj_type = obj_type;
        return (PyObject *)newobj;
    }
}

static int
super_init(PyObject *self, PyObject *args, PyObject *kwds)
{
    superobject *su = (superobject *)self;
    PyTypeObject *type = ((void *)0);
    PyObject *obj = ((void *)0);
    PyTypeObject *obj_type = ((void *)0);

    if (!_PyArg_NoKeywords("super", kwds))
        return -1;
    if (!PyArg_ParseTuple(args, "|O!O:super", &PyType_Type, &type, &obj))
        return -1;

    if (type == ((void *)0)) {


        PyFrameObject *f = ((PyThreadState*)__extension__ ({ __typeof__(&_PyThreadState_Current) atomic_val = &_PyThreadState_Current; __typeof__(atomic_val->_value) result; volatile __typeof__(result) *volatile_data = &atomic_val->_value; _Py_memory_order order = _Py_memory_order_relaxed; _Py_ANNOTATE_MEMORY_ORDER(atomic_val, order); ; switch(order) { case _Py_memory_order_release: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_thread_fence(_Py_memory_order_release); break; default: break; } result = *volatile_data; switch(order) { case _Py_memory_order_acquire: case _Py_memory_order_acq_rel: case _Py_memory_order_seq_cst: _Py_atomic_signal_fence(_Py_memory_order_acquire); break; default: break; } ; result; }))->frame;
        PyCodeObject *co = f->f_code;
        Py_ssize_t i, n;
        if (co == ((void *)0)) {
            PyErr_SetString(PyExc_RuntimeError,
                            "super(): no code object");
            return -1;
        }
        if (co->co_argcount == 0) {
            PyErr_SetString(PyExc_RuntimeError,
                            "super(): no arguments");
            return -1;
        }
        obj = f->f_localsplus[0];
        if (obj == ((void *)0)) {
            PyErr_SetString(PyExc_RuntimeError,
                            "super(): arg[0] deleted");
            return -1;
        }
        if (co->co_freevars == ((void *)0))
            n = 0;
        else {
            (__builtin_expect(!(((((((PyObject*)(co->co_freevars))->ob_type))->tp_flags & ((1L<<26))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 6528, "PyTuple_Check(co->co_freevars)") : (void)0);
            n = (((PyVarObject*)(co->co_freevars))->ob_size);
        }
        for (i = 0; i < n; i++) {
            PyObject *name = (((PyTupleObject *)(co->co_freevars))->ob_item[i]);
            (__builtin_expect(!(((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "typeobject.c", 6533, "PyUnicode_Check(name)") : (void)0);
            if (!PyUnicode_CompareWithASCIIString(name,
                                                  "__class__")) {
                Py_ssize_t index = co->co_nlocals +
                    (((PyVarObject*)(co->co_cellvars))->ob_size) + i;
                PyObject *cell = f->f_localsplus[index];
                if (cell == ((void *)0) || !((((PyObject*)(cell))->ob_type) == &PyCell_Type)) {
                    PyErr_SetString(PyExc_RuntimeError,
                      "super(): bad __class__ cell");
                    return -1;
                }
                type = (PyTypeObject *) (((PyCellObject *)(cell))->ob_ref);
                if (type == ((void *)0)) {
                    PyErr_SetString(PyExc_RuntimeError,
                      "super(): empty __class__ cell");
                    return -1;
                }
                if (!((((((PyObject*)(type))->ob_type))->tp_flags & ((1L<<31))) != 0)) {
                    PyErr_Format(PyExc_RuntimeError,
                      "super(): __class__ is not a type (%s)",
                      (((PyObject*)(type))->ob_type)->tp_name);
                    return -1;
                }
                break;
            }
        }
        if (type == ((void *)0)) {
            PyErr_SetString(PyExc_RuntimeError,
                            "super(): __class__ cell not found");
            return -1;
        }
    }

    if (obj == (&_Py_NoneStruct))
        obj = ((void *)0);
    if (obj != ((void *)0)) {
        obj_type = supercheck(type, obj);
        if (obj_type == ((void *)0))
            return -1;
        ( ((PyObject*)(obj))->ob_refcnt++);
    }
    ( ((PyObject*)(type))->ob_refcnt++);
    su->type = type;
    su->obj = obj;
    su->obj_type = obj_type;
    return 0;
}

static char super_doc[] = "super() -> same as super(__class__, <first argument>)\n" "super(type) -> unbound super object\n" "super(type, obj) -> bound super object; requires isinstance(obj, type)\n" "super(type, type2) -> bound super object; requires issubclass(type2, type)\n" "Typical use to call a cooperative superclass method:\n" "class C(B):\n" "    def meth(self, arg):\n" "        super().meth(arg)\n" "This works for class methods too:\n" "class C(B):\n" "    @classmethod\n" "    def cmeth(cls, arg):\n" "        super().cmeth(arg)\n";
# 6596 "typeobject.c"
static int
super_traverse(PyObject *self, visitproc visit, void *arg)
{
    superobject *su = (superobject *)self;

    do { if (su->obj) { int vret = visit((PyObject *)(su->obj), arg); if (vret) return vret; } } while (0);
    do { if (su->type) { int vret = visit((PyObject *)(su->type), arg); if (vret) return vret; } } while (0);
    do { if (su->obj_type) { int vret = visit((PyObject *)(su->obj_type), arg); if (vret) return vret; } } while (0);

    return 0;
}

PyTypeObject PySuper_Type = {
    { { 1, &PyType_Type }, 0 },
    "super",
    sizeof(superobject),
    0,

    super_dealloc,
    0,
    0,
    0,
    0,
    super_repr,
    0,
    0,
    0,
    0,
    0,
    0,
    super_getattro,
    0,
    0,
    ( 0 | (1L<<18) | 0) | (1L<<14) |
        (1L<<10),
    super_doc,
    super_traverse,
    0,
    0,
    0,
    0,
    0,
    0,
    super_members,
    0,
    0,
    0,
    super_descr_get,
    0,
    0,
    super_init,
    PyType_GenericAlloc,
    PyType_GenericNew,
    PyObject_GC_Del,
};
