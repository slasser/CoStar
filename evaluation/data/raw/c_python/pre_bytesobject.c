# 1 "bytesobject.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "bytesobject.c"




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
# 6 "bytesobject.c" 2

# 1 "/Users/parrt/tmp/Python-3.3.1/Include/bytes_methods.h" 1
# 9 "/Users/parrt/tmp/Python-3.3.1/Include/bytes_methods.h"
extern PyObject* _Py_bytes_isspace(const char *cptr, Py_ssize_t len);
extern PyObject* _Py_bytes_isalpha(const char *cptr, Py_ssize_t len);
extern PyObject* _Py_bytes_isalnum(const char *cptr, Py_ssize_t len);
extern PyObject* _Py_bytes_isdigit(const char *cptr, Py_ssize_t len);
extern PyObject* _Py_bytes_islower(const char *cptr, Py_ssize_t len);
extern PyObject* _Py_bytes_isupper(const char *cptr, Py_ssize_t len);
extern PyObject* _Py_bytes_istitle(const char *cptr, Py_ssize_t len);


extern void _Py_bytes_lower(char *result, const char *cptr, Py_ssize_t len);
extern void _Py_bytes_upper(char *result, const char *cptr, Py_ssize_t len);
extern void _Py_bytes_title(char *result, char *s, Py_ssize_t len);
extern void _Py_bytes_capitalize(char *result, char *s, Py_ssize_t len);
extern void _Py_bytes_swapcase(char *result, char *s, Py_ssize_t len);


extern PyObject* _Py_bytes_maketrans(PyObject *args);


extern const char _Py_isspace__doc__[];
extern const char _Py_isalpha__doc__[];
extern const char _Py_isalnum__doc__[];
extern const char _Py_isdigit__doc__[];
extern const char _Py_islower__doc__[];
extern const char _Py_isupper__doc__[];
extern const char _Py_istitle__doc__[];
extern const char _Py_lower__doc__[];
extern const char _Py_upper__doc__[];
extern const char _Py_title__doc__[];
extern const char _Py_capitalize__doc__[];
extern const char _Py_swapcase__doc__[];
extern const char _Py_maketrans__doc__[];
# 8 "bytesobject.c" 2
# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stddef.h" 1 3 4
# 152 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stddef.h" 3 4
typedef long int ptrdiff_t;
# 9 "bytesobject.c" 2

static Py_ssize_t
_getbuffer(PyObject *obj, Py_buffer *view)
{
    PyBufferProcs *buffer = (((PyObject*)(obj))->ob_type)->tp_as_buffer;

    if (buffer == ((void *)0) || buffer->bf_getbuffer == ((void *)0))
    {
        PyErr_Format(PyExc_TypeError,
                     "Type %.100s doesn't support the buffer API",
                     (((PyObject*)(obj))->ob_type)->tp_name);
        return -1;
    }

    if (buffer->bf_getbuffer(obj, view, 0) < 0)
        return -1;
    return view->len;
}





static PyBytesObject *characters[(127 * 2 + 1) + 1];
static PyBytesObject *nullstring;
# 65 "bytesobject.c"
PyObject *
PyBytes_FromStringAndSize(const char *str, Py_ssize_t size)
{
    register PyBytesObject *op;
    if (size < 0) {
        PyErr_SetString(PyExc_SystemError,
            "Negative size passed to PyBytes_FromStringAndSize");
        return ((void *)0);
    }
    if (size == 0 && (op = nullstring) != ((void *)0)) {



        ( ((PyObject*)(op))->ob_refcnt++);
        return (PyObject *)op;
    }
    if (size == 1 && str != ((void *)0) &&
        (op = characters[*str & (127 * 2 + 1)]) != ((void *)0))
    {



        ( ((PyObject*)(op))->ob_refcnt++);
        return (PyObject *)op;
    }

    if (size > ((Py_ssize_t)(((size_t)-1)>>1)) - (__builtin_offsetof (PyBytesObject, ob_sval) + 1)) {
        PyErr_SetString(PyExc_OverflowError,
                        "byte string is too large");
        return ((void *)0);
    }


    op = (PyBytesObject *)PyObject_Malloc((__builtin_offsetof (PyBytesObject, ob_sval) + 1) + size);
    if (op == ((void *)0))
        return PyErr_NoMemory();
    ( (((PyVarObject*)(op))->ob_size) = (size), ( (((PyObject*)((op)))->ob_type) = ((&PyBytes_Type)), ( (((PyObject*)((PyObject *)((op))))->ob_refcnt) = 1), ((op)) ) );
    op->ob_shash = -1;
    if (str != ((void *)0))
        ((__builtin_object_size (op->ob_sval, 0) != (size_t) -1) ? __builtin___memcpy_chk (op->ob_sval, str, size, __builtin_object_size (op->ob_sval, 0)) : __inline_memcpy_chk (op->ob_sval, str, size));
    op->ob_sval[size] = '\0';

    if (size == 0) {
        nullstring = op;
        ( ((PyObject*)(op))->ob_refcnt++);
    } else if (size == 1 && str != ((void *)0)) {
        characters[*str & (127 * 2 + 1)] = op;
        ( ((PyObject*)(op))->ob_refcnt++);
    }
    return (PyObject *) op;
}

PyObject *
PyBytes_FromString(const char *str)
{
    register size_t size;
    register PyBytesObject *op;

    (__builtin_expect(!(str != ((void *)0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 123, "str != NULL") : (void)0);
    size = strlen(str);
    if (size > ((Py_ssize_t)(((size_t)-1)>>1)) - (__builtin_offsetof (PyBytesObject, ob_sval) + 1)) {
        PyErr_SetString(PyExc_OverflowError,
            "byte string is too long");
        return ((void *)0);
    }
    if (size == 0 && (op = nullstring) != ((void *)0)) {



        ( ((PyObject*)(op))->ob_refcnt++);
        return (PyObject *)op;
    }
    if (size == 1 && (op = characters[*str & (127 * 2 + 1)]) != ((void *)0)) {



        ( ((PyObject*)(op))->ob_refcnt++);
        return (PyObject *)op;
    }


    op = (PyBytesObject *)PyObject_Malloc((__builtin_offsetof (PyBytesObject, ob_sval) + 1) + size);
    if (op == ((void *)0))
        return PyErr_NoMemory();
    ( (((PyVarObject*)(op))->ob_size) = (size), ( (((PyObject*)((op)))->ob_type) = ((&PyBytes_Type)), ( (((PyObject*)((PyObject *)((op))))->ob_refcnt) = 1), ((op)) ) );
    op->ob_shash = -1;
    ((__builtin_object_size (op->ob_sval, 0) != (size_t) -1) ? __builtin___memcpy_chk (op->ob_sval, str, size+1, __builtin_object_size (op->ob_sval, 0)) : __inline_memcpy_chk (op->ob_sval, str, size+1));

    if (size == 0) {
        nullstring = op;
        ( ((PyObject*)(op))->ob_refcnt++);
    } else if (size == 1) {
        characters[*str & (127 * 2 + 1)] = op;
        ( ((PyObject*)(op))->ob_refcnt++);
    }
    return (PyObject *) op;
}

PyObject *
PyBytes_FromFormatV(const char *format, va_list vargs)
{
    va_list count;
    Py_ssize_t n = 0;
    const char* f;
    char *s;
    PyObject* string;

    ((__builtin_object_size ((count), 0) != (size_t) -1) ? __builtin___memcpy_chk ((count), (vargs), sizeof(va_list), __builtin_object_size ((count), 0)) : __inline_memcpy_chk ((count), (vargs), sizeof(va_list)));

    for (f = format; *f; f++) {
        if (*f == '%') {
            const char* p = f;
            while (*++f && *f != '%' && !(_Py_ctype_table[((unsigned char)((*f) & 0xff))] & (0x01|0x02)))
                ;




            if ((*f == 'l' || *f == 'z') &&
                            (f[1] == 'd' || f[1] == 'u'))
                ++f;

            switch (*f) {
            case 'c':
                (void)__builtin_va_arg(count,int);

            case '%':
                n++;
                break;
            case 'd': case 'u': case 'i': case 'x':
                (void) __builtin_va_arg(count,int);



                n += 20;
                break;
            case 's':
                s = __builtin_va_arg(count,char*);
                n += strlen(s);
                break;
            case 'p':
                (void) __builtin_va_arg(count,int);





                n += 19;
                break;
            default:






                n += strlen(p);
                goto expand;
            }
        } else
            n++;
    }
 expand:



    string = PyBytes_FromStringAndSize(((void *)0), n);
    if (!string)
        return ((void *)0);

    s = PyBytes_AsString(string);

    for (f = format; *f; f++) {
        if (*f == '%') {
            const char* p = f++;
            Py_ssize_t i;
            int longflag = 0;
            int size_tflag = 0;


            n = 0;
            while ((_Py_ctype_table[((unsigned char)((*f) & 0xff))] & 0x04))
                n = (n*10) + *f++ - '0';
            if (*f == '.') {
                f++;
                n = 0;
                while ((_Py_ctype_table[((unsigned char)((*f) & 0xff))] & 0x04))
                    n = (n*10) + *f++ - '0';
            }
            while (*f && *f != '%' && !(_Py_ctype_table[((unsigned char)((*f) & 0xff))] & (0x01|0x02)))
                f++;


            if (*f == 'l' && (f[1] == 'd' || f[1] == 'u')) {
                longflag = 1;
                ++f;
            }

            if (*f == 'z' && (f[1] == 'd' || f[1] == 'u')) {
                size_tflag = 1;
                ++f;
            }

            switch (*f) {
            case 'c':
                *s++ = __builtin_va_arg(vargs,int);
                break;
            case 'd':
                if (longflag)
                    __builtin___sprintf_chk (s, 0, __builtin_object_size (s, 2 > 1), "%ld", __builtin_va_arg(vargs,long));
                else if (size_tflag)
                    __builtin___sprintf_chk (s, 0, __builtin_object_size (s, 2 > 1), "%" "l" "d", __builtin_va_arg(vargs,Py_ssize_t));

                else
                    __builtin___sprintf_chk (s, 0, __builtin_object_size (s, 2 > 1), "%d", __builtin_va_arg(vargs,int));
                s += strlen(s);
                break;
            case 'u':
                if (longflag)
                    __builtin___sprintf_chk (s, 0, __builtin_object_size (s, 2 > 1), "%lu", __builtin_va_arg(vargs,unsigned long));

                else if (size_tflag)
                    __builtin___sprintf_chk (s, 0, __builtin_object_size (s, 2 > 1), "%" "l" "u", __builtin_va_arg(vargs,size_t));

                else
                    __builtin___sprintf_chk (s, 0, __builtin_object_size (s, 2 > 1), "%u", __builtin_va_arg(vargs,unsigned int));

                s += strlen(s);
                break;
            case 'i':
                __builtin___sprintf_chk (s, 0, __builtin_object_size (s, 2 > 1), "%i", __builtin_va_arg(vargs,int));
                s += strlen(s);
                break;
            case 'x':
                __builtin___sprintf_chk (s, 0, __builtin_object_size (s, 2 > 1), "%x", __builtin_va_arg(vargs,int));
                s += strlen(s);
                break;
            case 's':
                p = __builtin_va_arg(vargs,char*);
                i = strlen(p);
                if (n > 0 && i > n)
                    i = n;
                ((__builtin_object_size (s, 0) != (size_t) -1) ? __builtin___memcpy_chk (s, p, i, __builtin_object_size (s, 0)) : __inline_memcpy_chk (s, p, i));
                s += i;
                break;
            case 'p':
                __builtin___sprintf_chk (s, 0, __builtin_object_size (s, 2 > 1), "%p", __builtin_va_arg(vargs,void*));

                if (s[1] == 'X')
                    s[1] = 'x';
                else if (s[1] != 'x') {
                    ((__builtin_object_size (s+2, 0) != (size_t) -1) ? __builtin___memmove_chk (s+2, s, strlen(s)+1, __builtin_object_size (s+2, 0)) : __inline_memmove_chk (s+2, s, strlen(s)+1));
                    s[0] = '0';
                    s[1] = 'x';
                }
                s += strlen(s);
                break;
            case '%':
                *s++ = '%';
                break;
            default:
                ((__builtin_object_size (s, 0) != (size_t) -1) ? __builtin___strcpy_chk (s, p, __builtin_object_size (s, 2 > 1)) : __inline_strcpy_chk (s, p));
                s += strlen(s);
                goto end;
            }
        } else
            *s++ = *f;
    }

 end:
    _PyBytes_Resize(&string, s - ((__builtin_expect(!(((((((PyObject*)(string))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 335, "PyBytes_Check(string)") : (void)0), (((PyBytesObject *)(string))->ob_sval)));
    return string;
}

PyObject *
PyBytes_FromFormat(const char *format, ...)
{
    PyObject* ret;
    va_list vargs;


    __builtin_va_start(vargs,format);



    ret = PyBytes_FromFormatV(format, vargs);
    __builtin_va_end(vargs);
    return ret;
}

static void
bytes_dealloc(PyObject *op)
{
    (((PyObject*)(op))->ob_type)->tp_free(op);
}






PyObject *PyBytes_DecodeEscape(const char *s,
                                Py_ssize_t len,
                                const char *errors,
                                Py_ssize_t unicode,
                                const char *recode_encoding)
{
    int c;
    char *p, *buf;
    const char *end;
    PyObject *v;
    Py_ssize_t newlen = recode_encoding ? 4*len:len;
    v = PyBytes_FromStringAndSize((char *)((void *)0), newlen);
    if (v == ((void *)0))
        return ((void *)0);
    p = buf = PyBytes_AsString(v);
    end = s + len;
    while (s < end) {
        if (*s != '\\') {
          non_esc:
            if (recode_encoding && (*s & 0x80)) {
                PyObject *u, *w;
                char *r;
                const char* t;
                Py_ssize_t rn;
                t = s;

                while (t < end && (*t & 0x80)) t++;
                u = PyUnicode_DecodeUTF8(s, t - s, errors);
                if(!u) goto failed;


                w = PyUnicode_AsEncodedString(
                    u, recode_encoding, errors);
                do { if ( --((PyObject*)(u))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(u)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(u)))); } while (0);
                if (!w) goto failed;


                (__builtin_expect(!(((((((PyObject*)(w))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 403, "PyBytes_Check(w)") : (void)0);
                r = ((__builtin_expect(!(((((((PyObject*)(w))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 404, "PyBytes_Check(w)") : (void)0), (((PyBytesObject *)(w))->ob_sval));
                rn = ((__builtin_expect(!(((((((PyObject*)(w))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 405, "PyBytes_Check(w)") : (void)0),(((PyVarObject*)(w))->ob_size));
                ((__builtin_object_size (p, 0) != (size_t) -1) ? __builtin___memcpy_chk (p, r, rn, __builtin_object_size (p, 0)) : __inline_memcpy_chk (p, r, rn));
                p += rn;
                do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0);
                s = t;
            } else {
                *p++ = *s++;
            }
            continue;
        }
        s++;
        if (s==end) {
            PyErr_SetString(PyExc_ValueError,
                            "Trailing \\ in string");
            goto failed;
        }
        switch (*s++) {

        case '\n': break;
        case '\\': *p++ = '\\'; break;
        case '\'': *p++ = '\''; break;
        case '\"': *p++ = '\"'; break;
        case 'b': *p++ = '\b'; break;
        case 'f': *p++ = '\014'; break;
        case 't': *p++ = '\t'; break;
        case 'n': *p++ = '\n'; break;
        case 'r': *p++ = '\r'; break;
        case 'v': *p++ = '\013'; break;
        case 'a': *p++ = '\007'; break;
        case '0': case '1': case '2': case '3':
        case '4': case '5': case '6': case '7':
            c = s[-1] - '0';
            if (s < end && '0' <= *s && *s <= '7') {
                c = (c<<3) + *s++ - '0';
                if (s < end && '0' <= *s && *s <= '7')
                    c = (c<<3) + *s++ - '0';
            }
            *p++ = c;
            break;
        case 'x':
            if (s+1 < end && (_Py_ctype_table[((unsigned char)((s[0]) & 0xff))] & 0x10) && (_Py_ctype_table[((unsigned char)((s[1]) & 0xff))] & 0x10)) {
                unsigned int x = 0;
                c = ((unsigned char)((*s) & 0xff));
                s++;
                if ((_Py_ctype_table[((unsigned char)((c) & 0xff))] & 0x04))
                    x = c - '0';
                else if ((_Py_ctype_table[((unsigned char)((c) & 0xff))] & 0x01))
                    x = 10 + c - 'a';
                else
                    x = 10 + c - 'A';
                x = x << 4;
                c = ((unsigned char)((*s) & 0xff));
                s++;
                if ((_Py_ctype_table[((unsigned char)((c) & 0xff))] & 0x04))
                    x += c - '0';
                else if ((_Py_ctype_table[((unsigned char)((c) & 0xff))] & 0x01))
                    x += 10 + c - 'a';
                else
                    x += 10 + c - 'A';
                *p++ = x;
                break;
            }
            if (!errors || strcmp(errors, "strict") == 0) {
                PyErr_Format(PyExc_ValueError,
                             "invalid \\x escape at position %d",
                             s - 2 - (end - len));
                goto failed;
            }
            if (strcmp(errors, "replace") == 0) {
                *p++ = '?';
            } else if (strcmp(errors, "ignore") == 0)
                                ;
            else {
                PyErr_Format(PyExc_ValueError,
                             "decoding error; unknown "
                             "error handling code: %.400s",
                             errors);
                goto failed;
            }

            if (s < end && (_Py_ctype_table[((unsigned char)((s[0]) & 0xff))] & 0x10))
                s++;
            break;
        default:
            *p++ = '\\';
            s--;
            goto non_esc;

        }
    }
    if (p-buf < newlen)
        _PyBytes_Resize(&v, p - buf);
    return v;
  failed:
    do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
    return ((void *)0);
}




Py_ssize_t
PyBytes_Size(register PyObject *op)
{
    if (!((((((PyObject*)(op))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
        PyErr_Format(PyExc_TypeError,
             "expected bytes, %.200s found", (((PyObject*)(op))->ob_type)->tp_name);
        return -1;
    }
    return (((PyVarObject*)(op))->ob_size);
}

char *
PyBytes_AsString(register PyObject *op)
{
    if (!((((((PyObject*)(op))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
        PyErr_Format(PyExc_TypeError,
             "expected bytes, %.200s found", (((PyObject*)(op))->ob_type)->tp_name);
        return ((void *)0);
    }
    return ((PyBytesObject *)op)->ob_sval;
}

int
PyBytes_AsStringAndSize(register PyObject *obj,
                         register char **s,
                         register Py_ssize_t *len)
{
    if (s == ((void *)0)) {
        _PyErr_BadInternalCall("bytesobject.c", 534);
        return -1;
    }

    if (!((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
        PyErr_Format(PyExc_TypeError,
             "expected bytes, %.200s found", (((PyObject*)(obj))->ob_type)->tp_name);
        return -1;
    }

    *s = ((__builtin_expect(!(((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 544, "PyBytes_Check(obj)") : (void)0), (((PyBytesObject *)(obj))->ob_sval));
    if (len != ((void *)0))
        *len = ((__builtin_expect(!(((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 546, "PyBytes_Check(obj)") : (void)0),(((PyVarObject*)(obj))->ob_size));
    else if (strlen(*s) != (size_t)((__builtin_expect(!(((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 547, "PyBytes_Check(obj)") : (void)0),(((PyVarObject*)(obj))->ob_size))) {
        PyErr_SetString(PyExc_TypeError,
                        "expected bytes with no null");
        return -1;
    }
    return 0;
}




# 1 "stringlib/stringdefs.h" 1
# 559 "bytesobject.c" 2

# 1 "stringlib/fastsearch.h" 1
# 36 "stringlib/fastsearch.h"
static inline Py_ssize_t
stringlib_fastsearch_memchr_1char(const char* s, Py_ssize_t n,
                                   char ch, unsigned char needle,
                                   Py_ssize_t maxcount, int mode)
{
    if (mode == 1) {
        const char *ptr = s;
        const char *e = s + n;
        while (ptr < e) {
            void *candidate = memchr((const void *) ptr, needle, (e - ptr) * sizeof(char));
            if (candidate == ((void *)0))
                return -1;
            ptr = (const char *) ((void *)((Py_uintptr_t)(candidate) & ~(Py_uintptr_t)((sizeof(char)) - 1)));
            if (sizeof(char) == 1 || *ptr == ch)
                return (ptr - s);

            ptr++;
        }
        return -1;
    }
# 75 "stringlib/fastsearch.h"
    else {
        (__builtin_expect(!(0), 0) ? __assert_rtn(__func__, "stringlib/fastsearch.h", 76, "0") : (void)0);
        return 0;
    }


}

static inline Py_ssize_t
fastsearch(const char* s, Py_ssize_t n,
           const char* p, Py_ssize_t m,
           Py_ssize_t maxcount, int mode)
{
    unsigned long mask;
    Py_ssize_t skip, count = 0;
    Py_ssize_t i, j, mlast, w;

    w = n - m;

    if (w < 0 || (mode == 0 && maxcount == 0))
        return -1;


    if (m <= 1) {
        if (m <= 0)
            return -1;

        if (n > 10 && (mode == 1



                    )) {


            unsigned char needle;
            needle = p[0] & 0xff;






                return stringlib_fastsearch_memchr_1char
                       (s, n, p[0], needle, maxcount, mode);
        }
        if (mode == 0) {
            for (i = 0; i < n; i++)
                if (s[i] == p[0]) {
                    count++;
                    if (count == maxcount)
                        return maxcount;
                }
            return count;
        } else if (mode == 1) {
            for (i = 0; i < n; i++)
                if (s[i] == p[0])
                    return i;
        } else {
            for (i = n - 1; i > -1; i--)
                if (s[i] == p[0])
                    return i;
        }
        return -1;
    }

    mlast = m - 1;
    skip = mlast - 1;
    mask = 0;

    if (mode != 2) {




        for (i = 0; i < mlast; i++) {
            ((mask |= (1UL << ((p[i]) & (64 -1)))));
            if (p[i] == p[mlast])
                skip = mlast - i - 1;
        }

        ((mask |= (1UL << ((p[mlast]) & (64 -1)))));

        for (i = 0; i <= w; i++) {

            if (s[i+m-1] == p[m-1]) {

                for (j = 0; j < mlast; j++)
                    if (s[i+j] != p[j])
                        break;
                if (j == mlast) {

                    if (mode != 0)
                        return i;
                    count++;
                    if (count == maxcount)
                        return maxcount;
                    i = i + mlast;
                    continue;
                }

                if (!((mask & (1UL << ((s[i+m]) & (64 -1))))))
                    i = i + m;
                else
                    i = i + skip;
            } else {

                if (!((mask & (1UL << ((s[i+m]) & (64 -1))))))
                    i = i + m;
            }
        }
    } else {




        ((mask |= (1UL << ((p[0]) & (64 -1)))));

        for (i = mlast; i > 0; i--) {
            ((mask |= (1UL << ((p[i]) & (64 -1)))));
            if (p[i] == p[0])
                skip = i - 1;
        }

        for (i = w; i >= 0; i--) {
            if (s[i] == p[0]) {

                for (j = mlast; j > 0; j--)
                    if (s[i+j] != p[j])
                        break;
                if (j == 0)

                    return i;

                if (i > 0 && !((mask & (1UL << ((s[i-1]) & (64 -1))))))
                    i = i - m;
                else
                    i = i - skip;
            } else {

                if (i > 0 && !((mask & (1UL << ((s[i-1]) & (64 -1))))))
                    i = i - m;
            }
        }
    }

    if (mode != 0)
        return -1;
    return count;
}
# 561 "bytesobject.c" 2
# 1 "stringlib/count.h" 1






static inline Py_ssize_t
stringlib_count(const char* str, Py_ssize_t str_len,
                const char* sub, Py_ssize_t sub_len,
                Py_ssize_t maxcount)
{
    Py_ssize_t count;

    if (str_len < 0)
        return 0;
    if (sub_len == 0)
        return (str_len < maxcount) ? str_len + 1 : maxcount;

    count = fastsearch(str, str_len, sub, sub_len, maxcount, 0);

    if (count < 0)
        return 0;

    return count;
}
# 562 "bytesobject.c" 2
# 1 "stringlib/find.h" 1






static inline Py_ssize_t
stringlib_find(const char* str, Py_ssize_t str_len,
               const char* sub, Py_ssize_t sub_len,
               Py_ssize_t offset)
{
    Py_ssize_t pos;

    if (str_len < 0)
        return -1;
    if (sub_len == 0)
        return offset;

    pos = fastsearch(str, str_len, sub, sub_len, -1, 1);

    if (pos >= 0)
        pos += offset;

    return pos;
}

static inline Py_ssize_t
stringlib_rfind(const char* str, Py_ssize_t str_len,
                const char* sub, Py_ssize_t sub_len,
                Py_ssize_t offset)
{
    Py_ssize_t pos;

    if (str_len < 0)
        return -1;
    if (sub_len == 0)
        return str_len + offset;

    pos = fastsearch(str, str_len, sub, sub_len, -1, 2);

    if (pos >= 0)
        pos += offset;

    return pos;
}
# 62 "stringlib/find.h"
static inline Py_ssize_t
stringlib_find_slice(const char* str, Py_ssize_t str_len,
                     const char* sub, Py_ssize_t sub_len,
                     Py_ssize_t start, Py_ssize_t end)
{
    if (end > str_len) end = str_len; else if (end < 0) { end += str_len; if (end < 0) end = 0; } if (start < 0) { start += str_len; if (start < 0) start = 0; };
    return stringlib_find(str + start, end - start, sub, sub_len, start);
}

static inline Py_ssize_t
stringlib_rfind_slice(const char* str, Py_ssize_t str_len,
                      const char* sub, Py_ssize_t sub_len,
                      Py_ssize_t start, Py_ssize_t end)
{
    if (end > str_len) end = str_len; else if (end < 0) { end += str_len; if (end < 0) end = 0; } if (start < 0) { start += str_len; if (start < 0) start = 0; };
    return stringlib_rfind(str + start, end - start, sub, sub_len, start);
}
# 104 "stringlib/find.h"
static inline int
stringlib_parse_args_finds(const char * function_name, PyObject *args,
                           PyObject **subobj,
                           Py_ssize_t *start, Py_ssize_t *end)
{
    PyObject *tmp_subobj;
    Py_ssize_t tmp_start = 0;
    Py_ssize_t tmp_end = ((Py_ssize_t)(((size_t)-1)>>1));
    PyObject *obj_start=(&_Py_NoneStruct), *obj_end=(&_Py_NoneStruct);
    char format[50] = "O|OO:";
    size_t len = strlen(format);

    ((__builtin_object_size (format + len, 0) != (size_t) -1) ? __builtin___strncpy_chk (format + len, function_name, 50 - len - 1, __builtin_object_size (format + len, 2 > 1)) : __inline_strncpy_chk (format + len, function_name, 50 - len - 1));
    format[50 - 1] = '\0';

    if (!_PyArg_ParseTuple_SizeT(args, format, &tmp_subobj, &obj_start, &obj_end))
        return 0;




    if (obj_start != (&_Py_NoneStruct))
        if (!_PyEval_SliceIndex(obj_start, &tmp_start))
            return 0;
    if (obj_end != (&_Py_NoneStruct))
        if (!_PyEval_SliceIndex(obj_end, &tmp_end))
            return 0;

    *start = tmp_start;
    *end = tmp_end;
    *subobj = tmp_subobj;
    return 1;
}
# 182 "stringlib/find.h"
static inline int
stringlib_parse_args_finds_byte(const char *function_name, PyObject *args,
                                 PyObject **subobj, char *byte,
                                 Py_ssize_t *start, Py_ssize_t *end)
{
    PyObject *tmp_subobj;
    Py_ssize_t ival;
    PyObject *err;

    if(!stringlib_parse_args_finds(function_name, args, &tmp_subobj,
                                    start, end))
        return 0;

    if (!PyNumber_Check(tmp_subobj)) {
        *subobj = tmp_subobj;
        return 1;
    }

    ival = PyNumber_AsSsize_t(tmp_subobj, PyExc_OverflowError);
    if (ival == -1) {
        err = PyErr_Occurred();
        if (err && !PyErr_GivenExceptionMatches(err, PyExc_OverflowError)) {
            PyErr_Clear();
            *subobj = tmp_subobj;
            return 1;
        }
    }

    if (ival < 0 || ival > 255) {
        PyErr_SetString(PyExc_ValueError, "byte must be in range(0, 256)");
        return 0;
    }

    *subobj = ((void *)0);
    *byte = (char)ival;
    return 1;
}
# 563 "bytesobject.c" 2
# 1 "stringlib/partition.h" 1






static inline PyObject*
stringlib_partition(PyObject* str_obj,
                    const char* str, Py_ssize_t str_len,
                    PyObject* sep_obj,
                    const char* sep, Py_ssize_t sep_len)
{
    PyObject* out;
    Py_ssize_t pos;

    if (sep_len == 0) {
        PyErr_SetString(PyExc_ValueError, "empty separator");
        return ((void *)0);
    }

    out = PyTuple_New(3);
    if (!out)
        return ((void *)0);

    pos = fastsearch(str, str_len, sep, sep_len, -1, 1);

    if (pos < 0) {





        ( ((PyObject*)(str_obj))->ob_refcnt++);
        (((PyTupleObject *)(out))->ob_item[0] = (PyObject*) str_obj);
        ( ((PyObject*)(nullstring))->ob_refcnt++);
        (((PyTupleObject *)(out))->ob_item[1] = (PyObject*) nullstring);
        ( ((PyObject*)(nullstring))->ob_refcnt++);
        (((PyTupleObject *)(out))->ob_item[2] = (PyObject*) nullstring);

        return out;
    }

    (((PyTupleObject *)(out))->ob_item[0] = PyBytes_FromStringAndSize(str, pos));
    ( ((PyObject*)(sep_obj))->ob_refcnt++);
    (((PyTupleObject *)(out))->ob_item[1] = sep_obj);
    pos += sep_len;
    (((PyTupleObject *)(out))->ob_item[2] = PyBytes_FromStringAndSize(str + pos, str_len - pos));

    if (PyErr_Occurred()) {
        do { if ( --((PyObject*)(out))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(out)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(out)))); } while (0);
        return ((void *)0);
    }

    return out;
}

static inline PyObject*
stringlib_rpartition(PyObject* str_obj,
                     const char* str, Py_ssize_t str_len,
                     PyObject* sep_obj,
                     const char* sep, Py_ssize_t sep_len)
{
    PyObject* out;
    Py_ssize_t pos;

    if (sep_len == 0) {
        PyErr_SetString(PyExc_ValueError, "empty separator");
        return ((void *)0);
    }

    out = PyTuple_New(3);
    if (!out)
        return ((void *)0);

    pos = fastsearch(str, str_len, sep, sep_len, -1, 2);

    if (pos < 0) {





        ( ((PyObject*)(nullstring))->ob_refcnt++);
        (((PyTupleObject *)(out))->ob_item[0] = (PyObject*) nullstring);
        ( ((PyObject*)(nullstring))->ob_refcnt++);
        (((PyTupleObject *)(out))->ob_item[1] = (PyObject*) nullstring);
        ( ((PyObject*)(str_obj))->ob_refcnt++);
        (((PyTupleObject *)(out))->ob_item[2] = (PyObject*) str_obj);

        return out;
    }

    (((PyTupleObject *)(out))->ob_item[0] = PyBytes_FromStringAndSize(str, pos));
    ( ((PyObject*)(sep_obj))->ob_refcnt++);
    (((PyTupleObject *)(out))->ob_item[1] = sep_obj);
    pos += sep_len;
    (((PyTupleObject *)(out))->ob_item[2] = PyBytes_FromStringAndSize(str + pos, str_len - pos));

    if (PyErr_Occurred()) {
        do { if ( --((PyObject*)(out))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(out)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(out)))); } while (0);
        return ((void *)0);
    }

    return out;
}
# 564 "bytesobject.c" 2
# 1 "stringlib/split.h" 1
# 53 "stringlib/split.h"
static inline PyObject *
stringlib_split_whitespace(PyObject* str_obj,
                           const char* str, Py_ssize_t str_len,
                           Py_ssize_t maxcount)
{
    Py_ssize_t i, j, count=0;
    PyObject *list = PyList_New((maxcount >= 12 ? 12 : maxcount+1));
    PyObject *sub;

    if (list == ((void *)0))
        return ((void *)0);

    i = j = 0;
    while (maxcount-- > 0) {
        while (i < str_len && (_Py_ctype_table[((unsigned char)((str[i]) & 0xff))] & 0x08))
            i++;
        if (i == str_len) break;
        j = i; i++;
        while (i < str_len && !(_Py_ctype_table[((unsigned char)((str[i]) & 0xff))] & 0x08))
            i++;

        if (j == 0 && i == str_len && ((((PyObject*)(str_obj))->ob_type) == &PyBytes_Type)) {

            ( ((PyObject*)(str_obj))->ob_refcnt++);
            (((PyListObject *)(list))->ob_item[0] = ((PyObject *)str_obj));
            count++;
            break;
        }

        { sub = PyBytes_FromStringAndSize((str) + (j), (i) - (j)); if (sub == ((void *)0)) goto onError; if (count < 12) { (((PyListObject *)(list))->ob_item[count] = (sub)); } else { if (PyList_Append(list, sub)) { do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); goto onError; } else do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); } count++; };
    }

    if (i < str_len) {


        while (i < str_len && (_Py_ctype_table[((unsigned char)((str[i]) & 0xff))] & 0x08))
            i++;
        if (i != str_len)
            { sub = PyBytes_FromStringAndSize((str) + (i), (str_len) - (i)); if (sub == ((void *)0)) goto onError; if (count < 12) { (((PyListObject *)(list))->ob_item[count] = (sub)); } else { if (PyList_Append(list, sub)) { do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); goto onError; } else do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); } count++; };
    }
    (((PyVarObject*)(list))->ob_size) = count;
    return list;

  onError:
    do { if ( --((PyObject*)(list))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(list)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(list)))); } while (0);
    return ((void *)0);
}

static inline PyObject *
stringlib_split_char(PyObject* str_obj,
                     const char* str, Py_ssize_t str_len,
                     const char ch,
                     Py_ssize_t maxcount)
{
    Py_ssize_t i, j, count=0;
    PyObject *list = PyList_New((maxcount >= 12 ? 12 : maxcount+1));
    PyObject *sub;

    if (list == ((void *)0))
        return ((void *)0);

    i = j = 0;
    while ((j < str_len) && (maxcount-- > 0)) {
        for(; j < str_len; j++) {

            if (str[j] == ch) {
                { sub = PyBytes_FromStringAndSize((str) + (i), (j) - (i)); if (sub == ((void *)0)) goto onError; if (count < 12) { (((PyListObject *)(list))->ob_item[count] = (sub)); } else { if (PyList_Append(list, sub)) { do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); goto onError; } else do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); } count++; };
                i = j = j + 1;
                break;
            }
        }
    }

    if (count == 0 && ((((PyObject*)(str_obj))->ob_type) == &PyBytes_Type)) {

        ( ((PyObject*)(str_obj))->ob_refcnt++);
        (((PyListObject *)(list))->ob_item[0] = ((PyObject *)str_obj));
        count++;
    } else

    if (i <= str_len) {
        { sub = PyBytes_FromStringAndSize((str) + (i), (str_len) - (i)); if (sub == ((void *)0)) goto onError; if (count < 12) { (((PyListObject *)(list))->ob_item[count] = (sub)); } else { if (PyList_Append(list, sub)) { do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); goto onError; } else do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); } count++; };
    }
    (((PyVarObject*)(list))->ob_size) = count;
    return list;

  onError:
    do { if ( --((PyObject*)(list))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(list)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(list)))); } while (0);
    return ((void *)0);
}

static inline PyObject *
stringlib_split(PyObject* str_obj,
                const char* str, Py_ssize_t str_len,
                const char* sep, Py_ssize_t sep_len,
                Py_ssize_t maxcount)
{
    Py_ssize_t i, j, pos, count=0;
    PyObject *list, *sub;

    if (sep_len == 0) {
        PyErr_SetString(PyExc_ValueError, "empty separator");
        return ((void *)0);
    }
    else if (sep_len == 1)
        return stringlib_split_char(str_obj, str, str_len, sep[0], maxcount);

    list = PyList_New((maxcount >= 12 ? 12 : maxcount+1));
    if (list == ((void *)0))
        return ((void *)0);

    i = j = 0;
    while (maxcount-- > 0) {
        pos = fastsearch(str+i, str_len-i, sep, sep_len, -1, 1);
        if (pos < 0)
            break;
        j = i + pos;
        { sub = PyBytes_FromStringAndSize((str) + (i), (j) - (i)); if (sub == ((void *)0)) goto onError; if (count < 12) { (((PyListObject *)(list))->ob_item[count] = (sub)); } else { if (PyList_Append(list, sub)) { do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); goto onError; } else do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); } count++; };
        i = j + sep_len;
    }

    if (count == 0 && ((((PyObject*)(str_obj))->ob_type) == &PyBytes_Type)) {

        ( ((PyObject*)(str_obj))->ob_refcnt++);
        (((PyListObject *)(list))->ob_item[0] = ((PyObject *)str_obj));
        count++;
    } else

    {
        { sub = PyBytes_FromStringAndSize((str) + (i), (str_len) - (i)); if (sub == ((void *)0)) goto onError; if (count < 12) { (((PyListObject *)(list))->ob_item[count] = (sub)); } else { if (PyList_Append(list, sub)) { do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); goto onError; } else do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); } count++; };
    }
    (((PyVarObject*)(list))->ob_size) = count;
    return list;

  onError:
    do { if ( --((PyObject*)(list))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(list)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(list)))); } while (0);
    return ((void *)0);
}

static inline PyObject *
stringlib_rsplit_whitespace(PyObject* str_obj,
                            const char* str, Py_ssize_t str_len,
                            Py_ssize_t maxcount)
{
    Py_ssize_t i, j, count=0;
    PyObject *list = PyList_New((maxcount >= 12 ? 12 : maxcount+1));
    PyObject *sub;

    if (list == ((void *)0))
        return ((void *)0);

    i = j = str_len - 1;
    while (maxcount-- > 0) {
        while (i >= 0 && (_Py_ctype_table[((unsigned char)((str[i]) & 0xff))] & 0x08))
            i--;
        if (i < 0) break;
        j = i; i--;
        while (i >= 0 && !(_Py_ctype_table[((unsigned char)((str[i]) & 0xff))] & 0x08))
            i--;

        if (j == str_len - 1 && i < 0 && ((((PyObject*)(str_obj))->ob_type) == &PyBytes_Type)) {

            ( ((PyObject*)(str_obj))->ob_refcnt++);
            (((PyListObject *)(list))->ob_item[0] = ((PyObject *)str_obj));
            count++;
            break;
        }

        { sub = PyBytes_FromStringAndSize((str) + (i + 1), (j + 1) - (i + 1)); if (sub == ((void *)0)) goto onError; if (count < 12) { (((PyListObject *)(list))->ob_item[count] = (sub)); } else { if (PyList_Append(list, sub)) { do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); goto onError; } else do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); } count++; };
    }

    if (i >= 0) {


        while (i >= 0 && (_Py_ctype_table[((unsigned char)((str[i]) & 0xff))] & 0x08))
            i--;
        if (i >= 0)
            { sub = PyBytes_FromStringAndSize((str) + (0), (i + 1) - (0)); if (sub == ((void *)0)) goto onError; if (count < 12) { (((PyListObject *)(list))->ob_item[count] = (sub)); } else { if (PyList_Append(list, sub)) { do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); goto onError; } else do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); } count++; };
    }
    (((PyVarObject*)(list))->ob_size) = count;
    if (PyList_Reverse(list) < 0)
        goto onError;
    return list;

  onError:
    do { if ( --((PyObject*)(list))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(list)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(list)))); } while (0);
    return ((void *)0);
}

static inline PyObject *
stringlib_rsplit_char(PyObject* str_obj,
                      const char* str, Py_ssize_t str_len,
                      const char ch,
                      Py_ssize_t maxcount)
{
    Py_ssize_t i, j, count=0;
    PyObject *list = PyList_New((maxcount >= 12 ? 12 : maxcount+1));
    PyObject *sub;

    if (list == ((void *)0))
        return ((void *)0);

    i = j = str_len - 1;
    while ((i >= 0) && (maxcount-- > 0)) {
        for(; i >= 0; i--) {
            if (str[i] == ch) {
                { sub = PyBytes_FromStringAndSize((str) + (i + 1), (j + 1) - (i + 1)); if (sub == ((void *)0)) goto onError; if (count < 12) { (((PyListObject *)(list))->ob_item[count] = (sub)); } else { if (PyList_Append(list, sub)) { do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); goto onError; } else do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); } count++; };
                j = i = i - 1;
                break;
            }
        }
    }

    if (count == 0 && ((((PyObject*)(str_obj))->ob_type) == &PyBytes_Type)) {

        ( ((PyObject*)(str_obj))->ob_refcnt++);
        (((PyListObject *)(list))->ob_item[0] = ((PyObject *)str_obj));
        count++;
    } else

    if (j >= -1) {
        { sub = PyBytes_FromStringAndSize((str) + (0), (j + 1) - (0)); if (sub == ((void *)0)) goto onError; if (count < 12) { (((PyListObject *)(list))->ob_item[count] = (sub)); } else { if (PyList_Append(list, sub)) { do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); goto onError; } else do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); } count++; };
    }
    (((PyVarObject*)(list))->ob_size) = count;
    if (PyList_Reverse(list) < 0)
        goto onError;
    return list;

  onError:
    do { if ( --((PyObject*)(list))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(list)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(list)))); } while (0);
    return ((void *)0);
}

static inline PyObject *
stringlib_rsplit(PyObject* str_obj,
                 const char* str, Py_ssize_t str_len,
                 const char* sep, Py_ssize_t sep_len,
                 Py_ssize_t maxcount)
{
    Py_ssize_t j, pos, count=0;
    PyObject *list, *sub;

    if (sep_len == 0) {
        PyErr_SetString(PyExc_ValueError, "empty separator");
        return ((void *)0);
    }
    else if (sep_len == 1)
        return stringlib_rsplit_char(str_obj, str, str_len, sep[0], maxcount);

    list = PyList_New((maxcount >= 12 ? 12 : maxcount+1));
    if (list == ((void *)0))
        return ((void *)0);

    j = str_len;
    while (maxcount-- > 0) {
        pos = fastsearch(str, j, sep, sep_len, -1, 2);
        if (pos < 0)
            break;
        { sub = PyBytes_FromStringAndSize((str) + (pos + sep_len), (j) - (pos + sep_len)); if (sub == ((void *)0)) goto onError; if (count < 12) { (((PyListObject *)(list))->ob_item[count] = (sub)); } else { if (PyList_Append(list, sub)) { do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); goto onError; } else do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); } count++; };
        j = pos;
    }

    if (count == 0 && ((((PyObject*)(str_obj))->ob_type) == &PyBytes_Type)) {

        ( ((PyObject*)(str_obj))->ob_refcnt++);
        (((PyListObject *)(list))->ob_item[0] = ((PyObject *)str_obj));
        count++;
    } else

    {
        { sub = PyBytes_FromStringAndSize((str) + (0), (j) - (0)); if (sub == ((void *)0)) goto onError; if (count < 12) { (((PyListObject *)(list))->ob_item[count] = (sub)); } else { if (PyList_Append(list, sub)) { do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); goto onError; } else do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); } count++; };
    }
    (((PyVarObject*)(list))->ob_size) = count;
    if (PyList_Reverse(list) < 0)
        goto onError;
    return list;

  onError:
    do { if ( --((PyObject*)(list))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(list)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(list)))); } while (0);
    return ((void *)0);
}

static inline PyObject *
stringlib_splitlines(PyObject* str_obj,
                     const char* str, Py_ssize_t str_len,
                     int keepends)
{
# 348 "stringlib/split.h"
    register Py_ssize_t i;
    register Py_ssize_t j;
    PyObject *list = PyList_New(0);
    PyObject *sub;

    if (list == ((void *)0))
        return ((void *)0);

    for (i = j = 0; i < str_len; ) {
        Py_ssize_t eol;


        while (i < str_len && !((str[i] == '\n') || (str[i] == '\r')))
            i++;


        eol = i;
        if (i < str_len) {
            if (str[i] == '\r' && i + 1 < str_len && str[i+1] == '\n')
                i += 2;
            else
                i++;
            if (keepends)
                eol = i;
        }

        if (j == 0 && eol == str_len && ((((PyObject*)(str_obj))->ob_type) == &PyBytes_Type)) {

            if (PyList_Append(list, str_obj))
                goto onError;
            break;
        }

        sub = PyBytes_FromStringAndSize((str) + (j), (eol) - (j)); if (sub == ((void *)0)) goto onError; if (PyList_Append(list, sub)) { do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0); goto onError; } else do { if ( --((PyObject*)(sub))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sub)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sub)))); } while (0);;
        j = i;
    }
    return list;

  onError:
    do { if ( --((PyObject*)(list))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(list)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(list)))); } while (0);
    return ((void *)0);
}
# 565 "bytesobject.c" 2
# 1 "stringlib/ctype.h" 1



# 1 "/Users/parrt/tmp/Python-3.3.1/Include/bytes_methods.h" 1
# 5 "stringlib/ctype.h" 2

static PyObject*
stringlib_isspace(PyObject *self)
{
    return _Py_bytes_isspace(((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 9, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 9, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)));
}

static PyObject*
stringlib_isalpha(PyObject *self)
{
    return _Py_bytes_isalpha(((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 15, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 15, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)));
}

static PyObject*
stringlib_isalnum(PyObject *self)
{
    return _Py_bytes_isalnum(((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 21, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 21, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)));
}

static PyObject*
stringlib_isdigit(PyObject *self)
{
    return _Py_bytes_isdigit(((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 27, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 27, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)));
}

static PyObject*
stringlib_islower(PyObject *self)
{
    return _Py_bytes_islower(((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 33, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 33, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)));
}

static PyObject*
stringlib_isupper(PyObject *self)
{
    return _Py_bytes_isupper(((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 39, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 39, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)));
}

static PyObject*
stringlib_istitle(PyObject *self)
{
    return _Py_bytes_istitle(((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 45, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 45, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)));
}




static PyObject*
stringlib_lower(PyObject *self)
{
    PyObject* newobj;
    newobj = PyBytes_FromStringAndSize(((void *)0), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 55, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)));
    if (!newobj)
            return ((void *)0);
    _Py_bytes_lower(((__builtin_expect(!(((((((PyObject*)(newobj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 58, "PyBytes_Check(newobj)") : (void)0), (((PyBytesObject *)(newobj))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 58, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)),
                 ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 59, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)));
    return newobj;
}

static PyObject*
stringlib_upper(PyObject *self)
{
    PyObject* newobj;
    newobj = PyBytes_FromStringAndSize(((void *)0), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 67, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)));
    if (!newobj)
            return ((void *)0);
    _Py_bytes_upper(((__builtin_expect(!(((((((PyObject*)(newobj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 70, "PyBytes_Check(newobj)") : (void)0), (((PyBytesObject *)(newobj))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 70, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)),
                 ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 71, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)));
    return newobj;
}

static PyObject*
stringlib_title(PyObject *self)
{
    PyObject* newobj;
    newobj = PyBytes_FromStringAndSize(((void *)0), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 79, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)));
    if (!newobj)
            return ((void *)0);
    _Py_bytes_title(((__builtin_expect(!(((((((PyObject*)(newobj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 82, "PyBytes_Check(newobj)") : (void)0), (((PyBytesObject *)(newobj))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 82, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)),
                 ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 83, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)));
    return newobj;
}

static PyObject*
stringlib_capitalize(PyObject *self)
{
    PyObject* newobj;
    newobj = PyBytes_FromStringAndSize(((void *)0), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 91, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)));
    if (!newobj)
            return ((void *)0);
    _Py_bytes_capitalize(((__builtin_expect(!(((((((PyObject*)(newobj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 94, "PyBytes_Check(newobj)") : (void)0), (((PyBytesObject *)(newobj))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 94, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)),
                      ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 95, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)));
    return newobj;
}

static PyObject*
stringlib_swapcase(PyObject *self)
{
    PyObject* newobj;
    newobj = PyBytes_FromStringAndSize(((void *)0), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 103, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)));
    if (!newobj)
            return ((void *)0);
    _Py_bytes_swapcase(((__builtin_expect(!(((((((PyObject*)(newobj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 106, "PyBytes_Check(newobj)") : (void)0), (((PyBytesObject *)(newobj))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 106, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)),
                    ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/ctype.h", 107, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)));
    return newobj;
}
# 566 "bytesobject.c" 2

# 1 "stringlib/transmogrify.h" 1






static char expandtabs__doc__[] = "B.expandtabs([tabsize]) -> copy of B\n\nReturn a copy of B where all tab characters are expanded using spaces.\nIf tabsize is not given, a tab size of 8 characters is assumed.";





static PyObject*
stringlib_expandtabs(PyObject *self, PyObject *args)
{
    const char *e, *p;
    char *q;
    size_t i, j;
    PyObject *u;
    int tabsize = 8;

    if (!_PyArg_ParseTuple_SizeT(args, "|i:expandtabs", &tabsize))
        return ((void *)0);


    i = j = 0;
    e = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 27, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)) + ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 27, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size));
    for (p = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 28, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)); p < e; p++)
        if (*p == '\t') {
            if (tabsize > 0) {
                j += tabsize - (j % tabsize);
                if (j > ((Py_ssize_t)(((size_t)-1)>>1))) {
                    PyErr_SetString(PyExc_OverflowError,
                                    "result is too long");
                    return ((void *)0);
                }
            }
        }
        else {
            j++;
            if (*p == '\n' || *p == '\r') {
                i += j;
                j = 0;
                if (i > ((Py_ssize_t)(((size_t)-1)>>1))) {
                    PyErr_SetString(PyExc_OverflowError,
                                    "result is too long");
                    return ((void *)0);
                }
            }
        }

    if ((i + j) > ((Py_ssize_t)(((size_t)-1)>>1))) {
        PyErr_SetString(PyExc_OverflowError, "result is too long");
        return ((void *)0);
    }


    u = PyBytes_FromStringAndSize(((void *)0), i + j);
    if (!u)
        return ((void *)0);

    j = 0;
    q = ((__builtin_expect(!(((((((PyObject*)(u))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 63, "PyBytes_Check(u)") : (void)0), (((PyBytesObject *)(u))->ob_sval));

    for (p = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 65, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)); p < e; p++)
        if (*p == '\t') {
            if (tabsize > 0) {
                i = tabsize - (j % tabsize);
                j += i;
                while (i--)
                    *q++ = ' ';
            }
        }
        else {
            j++;
            *q++ = *p;
            if (*p == '\n' || *p == '\r')
                j = 0;
        }

    return u;
}

static inline PyObject *
pad(PyObject *self, Py_ssize_t left, Py_ssize_t right, char fill)
{
    PyObject *u;

    if (left < 0)
        left = 0;
    if (right < 0)
        right = 0;

    if (left == 0 && right == 0 && ((((PyObject*)(self))->ob_type) == &PyBytes_Type)) {





        ( ((PyObject*)(self))->ob_refcnt++);
        return (PyObject *)self;

    }

    u = PyBytes_FromStringAndSize(((void *)0),
       left + ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 106, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)) + right);
    if (u) {
        if (left)
            ((__builtin_object_size (((__builtin_expect(!(((((((PyObject*)(u))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 109, "PyBytes_Check(u)") : (void)0), (((PyBytesObject *)(u))->ob_sval)), 0) != (size_t) -1) ? __builtin___memset_chk (((__builtin_expect(!(((((((PyObject*)(u))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 109, "PyBytes_Check(u)") : (void)0), (((PyBytesObject *)(u))->ob_sval)), fill, left, __builtin_object_size (((__builtin_expect(!(((((((PyObject*)(u))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 109, "PyBytes_Check(u)") : (void)0), (((PyBytesObject *)(u))->ob_sval)), 0)) : __inline_memset_chk (((__builtin_expect(!(((((((PyObject*)(u))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 109, "PyBytes_Check(u)") : (void)0), (((PyBytesObject *)(u))->ob_sval)), fill, left));
        ((__builtin_object_size (((__builtin_expect(!(((((((PyObject*)(u))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 112, "PyBytes_Check(u)") : (void)0), (((PyBytesObject *)(u))->ob_sval)) + left, 0) != (size_t) -1) ? __builtin___memcpy_chk (((__builtin_expect(!(((((((PyObject*)(u))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 112, "PyBytes_Check(u)") : (void)0), (((PyBytesObject *)(u))->ob_sval)) + left, ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 112, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 112, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)), __builtin_object_size (((__builtin_expect(!(((((((PyObject*)(u))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 112, "PyBytes_Check(u)") : (void)0), (((PyBytesObject *)(u))->ob_sval)) + left, 0)) : __inline_memcpy_chk (((__builtin_expect(!(((((((PyObject*)(u))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 112, "PyBytes_Check(u)") : (void)0), (((PyBytesObject *)(u))->ob_sval)) + left, ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 112, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 112, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size))));


        if (right)
            ((__builtin_object_size (((__builtin_expect(!(((((((PyObject*)(u))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 115, "PyBytes_Check(u)") : (void)0), (((PyBytesObject *)(u))->ob_sval)) + left + ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 115, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)), 0) != (size_t) -1) ? __builtin___memset_chk (((__builtin_expect(!(((((((PyObject*)(u))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 115, "PyBytes_Check(u)") : (void)0), (((PyBytesObject *)(u))->ob_sval)) + left + ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 115, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)), fill, right, __builtin_object_size (((__builtin_expect(!(((((((PyObject*)(u))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 115, "PyBytes_Check(u)") : (void)0), (((PyBytesObject *)(u))->ob_sval)) + left + ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 115, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)), 0)) : __inline_memset_chk (((__builtin_expect(!(((((((PyObject*)(u))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 115, "PyBytes_Check(u)") : (void)0), (((PyBytesObject *)(u))->ob_sval)) + left + ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 115, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)), fill, right));

    }

    return u;
}

static char ljust__doc__[] = "B.ljust(width[, fillchar]) -> copy of B\n" "\n" "Return B left justified in a string of length width. Padding is\n" "done using the specified fill character (default is a space).";





static PyObject *
stringlib_ljust(PyObject *self, PyObject *args)
{
    Py_ssize_t width;
    char fillchar = ' ';

    if (!_PyArg_ParseTuple_SizeT(args, "n|c:ljust", &width, &fillchar))
        return ((void *)0);

    if (((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 136, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)) >= width && ((((PyObject*)(self))->ob_type) == &PyBytes_Type)) {





        ( ((PyObject*)(self))->ob_refcnt++);
        return (PyObject*) self;

    }

    return pad(self, 0, width - ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 147, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)), fillchar);
}


static char rjust__doc__[] = "B.rjust(width[, fillchar]) -> copy of B\n" "\n" "Return B right justified in a string of length width. Padding is\n" "done using the specified fill character (default is a space)";





static PyObject *
stringlib_rjust(PyObject *self, PyObject *args)
{
    Py_ssize_t width;
    char fillchar = ' ';

    if (!_PyArg_ParseTuple_SizeT(args, "n|c:rjust", &width, &fillchar))
        return ((void *)0);

    if (((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 166, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)) >= width && ((((PyObject*)(self))->ob_type) == &PyBytes_Type)) {





        ( ((PyObject*)(self))->ob_refcnt++);
        return (PyObject*) self;

    }

    return pad(self, width - ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 177, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)), 0, fillchar);
}


static char center__doc__[] = "B.center(width[, fillchar]) -> copy of B\n" "\n" "Return B centered in a string of length width.  Padding is\n" "done using the specified fill character (default is a space).";





static PyObject *
stringlib_center(PyObject *self, PyObject *args)
{
    Py_ssize_t marg, left;
    Py_ssize_t width;
    char fillchar = ' ';

    if (!_PyArg_ParseTuple_SizeT(args, "n|c:center", &width, &fillchar))
        return ((void *)0);

    if (((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 197, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)) >= width && ((((PyObject*)(self))->ob_type) == &PyBytes_Type)) {





        ( ((PyObject*)(self))->ob_refcnt++);
        return (PyObject*) self;

    }

    marg = width - ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 208, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size));
    left = marg / 2 + (marg & width & 1);

    return pad(self, left, marg - left, fillchar);
}

static char zfill__doc__[] = "B.zfill(width) -> copy of B\n" "\n" "Pad a numeric string B with zeros on the left, to fill a field\n" "of the specified width.  B is never truncated.";





static PyObject *
stringlib_zfill(PyObject *self, PyObject *args)
{
    Py_ssize_t fill;
    PyObject *s;
    char *p;
    Py_ssize_t width;

    if (!_PyArg_ParseTuple_SizeT(args, "n:zfill", &width))
        return ((void *)0);

    if (((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 231, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)) >= width) {
        if (((((PyObject*)(self))->ob_type) == &PyBytes_Type)) {





            ( ((PyObject*)(self))->ob_refcnt++);
            return (PyObject*) self;

        }
        else
            return PyBytes_FromStringAndSize(
                ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 244, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)),
                ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 245, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size))
            );
    }

    fill = width - ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 249, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size));

    s = pad(self, fill, 0, '0');

    if (s == ((void *)0))
        return ((void *)0);

    p = ((__builtin_expect(!(((((((PyObject*)(s))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "stringlib/transmogrify.h", 256, "PyBytes_Check(s)") : (void)0), (((PyBytesObject *)(s))->ob_sval));
    if (p[fill] == '+' || p[fill] == '-') {

        p[0] = p[fill];
        p[fill] = '0';
    }

    return (PyObject*) s;
}
# 568 "bytesobject.c" 2

PyObject *
PyBytes_Repr(PyObject *obj, int smartquotes)
{
    register PyBytesObject* op = (PyBytesObject*) obj;
    Py_ssize_t i, length = (((PyVarObject*)(op))->ob_size);
    size_t newsize, squotes, dquotes;
    PyObject *v;
    unsigned char quote, *s, *p;


    squotes = dquotes = 0;
    newsize = 3;
    s = (unsigned char*)op->ob_sval;
    for (i = 0; i < length; i++) {
        switch(s[i]) {
        case '\'': squotes++; newsize++; break;
        case '"': dquotes++; newsize++; break;
        case '\\': case '\t': case '\n': case '\r':
            newsize += 2; break;
        default:
            if (s[i] < ' ' || s[i] >= 0x7f)
                newsize += 4;
            else
                newsize++;
        }
    }
    quote = '\'';
    if (smartquotes && squotes && !dquotes)
        quote = '"';
    if (squotes && quote == '\'')
        newsize += squotes;

    if (newsize > (((Py_ssize_t)(((size_t)-1)>>1)) - sizeof(PyUnicodeObject) - 1)) {
        PyErr_SetString(PyExc_OverflowError,
            "bytes object is too large to make repr");
        return ((void *)0);
    }

    v = PyUnicode_New(newsize, 127);
    if (v == ((void *)0)) {
        return ((void *)0);
    }
    p = ((Py_UCS1*)((__builtin_expect(!(((((((PyObject*)(v))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 611, "PyUnicode_Check(v)") : (void)0), (((PyASCIIObject*)(v))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)(v))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 611, "PyUnicode_Check(v)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)v)->state.ready)), 0) ? __assert_rtn(__func__, "bytesobject.c", 611, "PyUnicode_IS_READY(v)") : (void)0), ((PyASCIIObject*)v)->state.ascii) ? ((void*)((PyASCIIObject*)(v) + 1)) : ((void*)((PyCompactUnicodeObject*)(v) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)(v))->data.any), 0) ? __assert_rtn(__func__, "bytesobject.c", 611, "((PyUnicodeObject*)(v))->data.any") : (void)0), ((((PyUnicodeObject *)(v))->data.any)))));

    *p++ = 'b', *p++ = quote;
    for (i = 0; i < length; i++) {
        unsigned char c = op->ob_sval[i];
        if (c == quote || c == '\\')
            *p++ = '\\', *p++ = c;
        else if (c == '\t')
            *p++ = '\\', *p++ = 't';
        else if (c == '\n')
            *p++ = '\\', *p++ = 'n';
        else if (c == '\r')
            *p++ = '\\', *p++ = 'r';
        else if (c < ' ' || c >= 0x7f) {
            *p++ = '\\';
            *p++ = 'x';
            *p++ = Py_hexdigits[(c & 0xf0) >> 4];
            *p++ = Py_hexdigits[c & 0xf];
        }
        else
            *p++ = c;
    }
    *p++ = quote;
    (__builtin_expect(!(_PyUnicode_CheckConsistency(v, 1)), 0) ? __assert_rtn(__func__, "bytesobject.c", 634, "_PyUnicode_CheckConsistency(v, 1)") : (void)0);
    return v;
}

static PyObject *
bytes_repr(PyObject *op)
{
    return PyBytes_Repr(op, 1);
}

static PyObject *
bytes_str(PyObject *op)
{
    if (Py_BytesWarningFlag) {
        if (PyErr_WarnEx(PyExc_BytesWarning,
                         "str() on a bytes instance", 1))
            return ((void *)0);
    }
    return bytes_repr(op);
}

static Py_ssize_t
bytes_length(PyBytesObject *a)
{
    return (((PyVarObject*)(a))->ob_size);
}


static PyObject *
bytes_concat(PyObject *a, PyObject *b)
{
    Py_ssize_t size;
    Py_buffer va, vb;
    PyObject *result = ((void *)0);

    va.len = -1;
    vb.len = -1;
    if (_getbuffer(a, &va) < 0 ||
        _getbuffer(b, &vb) < 0) {
        PyErr_Format(PyExc_TypeError, "can't concat %.100s to %.100s",
                     (((PyObject*)(a))->ob_type)->tp_name, (((PyObject*)(b))->ob_type)->tp_name);
        goto done;
    }


    if (va.len == 0 && ((((PyObject*)(b))->ob_type) == &PyBytes_Type)) {
        result = b;
        ( ((PyObject*)(result))->ob_refcnt++);
        goto done;
    }
    if (vb.len == 0 && ((((PyObject*)(a))->ob_type) == &PyBytes_Type)) {
        result = a;
        ( ((PyObject*)(result))->ob_refcnt++);
        goto done;
    }

    size = va.len + vb.len;
    if (size < 0) {
        PyErr_NoMemory();
        goto done;
    }

    result = PyBytes_FromStringAndSize(((void *)0), size);
    if (result != ((void *)0)) {
        ((__builtin_object_size (((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 698, "PyBytes_Check(result)") : (void)0), (((PyBytesObject *)(result))->ob_sval)), 0) != (size_t) -1) ? __builtin___memcpy_chk (((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 698, "PyBytes_Check(result)") : (void)0), (((PyBytesObject *)(result))->ob_sval)), va.buf, va.len, __builtin_object_size (((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 698, "PyBytes_Check(result)") : (void)0), (((PyBytesObject *)(result))->ob_sval)), 0)) : __inline_memcpy_chk (((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 698, "PyBytes_Check(result)") : (void)0), (((PyBytesObject *)(result))->ob_sval)), va.buf, va.len));
        ((__builtin_object_size (((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 699, "PyBytes_Check(result)") : (void)0), (((PyBytesObject *)(result))->ob_sval)) + va.len, 0) != (size_t) -1) ? __builtin___memcpy_chk (((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 699, "PyBytes_Check(result)") : (void)0), (((PyBytesObject *)(result))->ob_sval)) + va.len, vb.buf, vb.len, __builtin_object_size (((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 699, "PyBytes_Check(result)") : (void)0), (((PyBytesObject *)(result))->ob_sval)) + va.len, 0)) : __inline_memcpy_chk (((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 699, "PyBytes_Check(result)") : (void)0), (((PyBytesObject *)(result))->ob_sval)) + va.len, vb.buf, vb.len));
    }

  done:
    if (va.len != -1)
        PyBuffer_Release(&va);
    if (vb.len != -1)
        PyBuffer_Release(&vb);
    return result;
}

static PyObject *
bytes_repeat(register PyBytesObject *a, register Py_ssize_t n)
{
    register Py_ssize_t i;
    register Py_ssize_t j;
    register Py_ssize_t size;
    register PyBytesObject *op;
    size_t nbytes;
    if (n < 0)
        n = 0;



    if (n > 0 && (((PyVarObject*)(a))->ob_size) > ((Py_ssize_t)(((size_t)-1)>>1)) / n) {
        PyErr_SetString(PyExc_OverflowError,
            "repeated bytes are too long");
        return ((void *)0);
    }
    size = (((PyVarObject*)(a))->ob_size) * n;
    if (size == (((PyVarObject*)(a))->ob_size) && ((((PyObject*)(a))->ob_type) == &PyBytes_Type)) {
        ( ((PyObject*)(a))->ob_refcnt++);
        return (PyObject *)a;
    }
    nbytes = (size_t)size;
    if (nbytes + (__builtin_offsetof (PyBytesObject, ob_sval) + 1) <= nbytes) {
        PyErr_SetString(PyExc_OverflowError,
            "repeated bytes are too long");
        return ((void *)0);
    }
    op = (PyBytesObject *)PyObject_Malloc((__builtin_offsetof (PyBytesObject, ob_sval) + 1) + nbytes);
    if (op == ((void *)0))
        return PyErr_NoMemory();
    ( (((PyVarObject*)(op))->ob_size) = (size), ( (((PyObject*)((op)))->ob_type) = ((&PyBytes_Type)), ( (((PyObject*)((PyObject *)((op))))->ob_refcnt) = 1), ((op)) ) );
    op->ob_shash = -1;
    op->ob_sval[size] = '\0';
    if ((((PyVarObject*)(a))->ob_size) == 1 && n > 0) {
        ((__builtin_object_size (op->ob_sval, 0) != (size_t) -1) ? __builtin___memset_chk (op->ob_sval, a->ob_sval[0], n, __builtin_object_size (op->ob_sval, 0)) : __inline_memset_chk (op->ob_sval, a->ob_sval[0], n));
        return (PyObject *) op;
    }
    i = 0;
    if (i < size) {
        ((__builtin_object_size (op->ob_sval, 0) != (size_t) -1) ? __builtin___memcpy_chk (op->ob_sval, a->ob_sval, (((PyVarObject*)(a))->ob_size), __builtin_object_size (op->ob_sval, 0)) : __inline_memcpy_chk (op->ob_sval, a->ob_sval, (((PyVarObject*)(a))->ob_size)));
        i = (((PyVarObject*)(a))->ob_size);
    }
    while (i < size) {
        j = (i <= size-i) ? i : size-i;
        ((__builtin_object_size (op->ob_sval+i, 0) != (size_t) -1) ? __builtin___memcpy_chk (op->ob_sval+i, op->ob_sval, j, __builtin_object_size (op->ob_sval+i, 0)) : __inline_memcpy_chk (op->ob_sval+i, op->ob_sval, j));
        i += j;
    }
    return (PyObject *) op;
}

static int
bytes_contains(PyObject *self, PyObject *arg)
{
    Py_ssize_t ival = PyNumber_AsSsize_t(arg, PyExc_ValueError);
    if (ival == -1 && PyErr_Occurred()) {
        Py_buffer varg;
        Py_ssize_t pos;
        PyErr_Clear();
        if (_getbuffer(arg, &varg) < 0)
            return -1;
        pos = stringlib_find(((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 772, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)), (((PyVarObject*)(self))->ob_size),
                             varg.buf, varg.len, 0);
        PyBuffer_Release(&varg);
        return pos >= 0;
    }
    if (ival < 0 || ival >= 256) {
        PyErr_SetString(PyExc_ValueError, "byte must be in range(0, 256)");
        return -1;
    }

    return memchr(((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 782, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)), (int) ival, (((PyVarObject*)(self))->ob_size)) != ((void *)0);
}

static PyObject *
bytes_item(PyBytesObject *a, register Py_ssize_t i)
{
    if (i < 0 || i >= (((PyVarObject*)(a))->ob_size)) {
        PyErr_SetString(PyExc_IndexError, "index out of range");
        return ((void *)0);
    }
    return PyLong_FromLong((unsigned char)a->ob_sval[i]);
}

static PyObject*
bytes_richcompare(PyBytesObject *a, PyBytesObject *b, int op)
{
    int c;
    Py_ssize_t len_a, len_b;
    Py_ssize_t min_len;
    PyObject *result;


    if (!(((((((PyObject*)(a))->ob_type))->tp_flags & ((1L<<27))) != 0) && ((((((PyObject*)(b))->ob_type))->tp_flags & ((1L<<27))) != 0))) {
        if (Py_BytesWarningFlag && (op == 2 || op == 3) &&
            (PyObject_IsInstance((PyObject*)a,
                                 (PyObject*)&PyUnicode_Type) ||
            PyObject_IsInstance((PyObject*)b,
                                 (PyObject*)&PyUnicode_Type))) {
            if (PyErr_WarnEx(PyExc_BytesWarning,
                        "Comparison between bytes and string", 1))
                return ((void *)0);
        }
        result = (&_Py_NotImplementedStruct);
        goto out;
    }
    if (a == b) {
        switch (op) {
        case 2:case 1:case 5:
            result = ((PyObject *) &_Py_TrueStruct);
            goto out;
        case 3:case 0:case 4:
            result = ((PyObject *) &_Py_FalseStruct);
            goto out;
        }
    }
    if (op == 2) {


        if ((((PyVarObject*)(a))->ob_size) == (((PyVarObject*)(b))->ob_size)
            && (a->ob_sval[0] == b->ob_sval[0]
            && memcmp(a->ob_sval, b->ob_sval, (((PyVarObject*)(a))->ob_size)) == 0)) {
            result = ((PyObject *) &_Py_TrueStruct);
        } else {
            result = ((PyObject *) &_Py_FalseStruct);
        }
        goto out;
    }
    len_a = (((PyVarObject*)(a))->ob_size); len_b = (((PyVarObject*)(b))->ob_size);
    min_len = (len_a < len_b) ? len_a : len_b;
    if (min_len > 0) {
        c = ((unsigned char)((*a->ob_sval) & 0xff)) - ((unsigned char)((*b->ob_sval) & 0xff));
        if (c==0)
            c = memcmp(a->ob_sval, b->ob_sval, min_len);
    } else
        c = 0;
    if (c == 0)
        c = (len_a < len_b) ? -1 : (len_a > len_b) ? 1 : 0;
    switch (op) {
    case 0: c = c < 0; break;
    case 1: c = c <= 0; break;
    case 2: (__builtin_expect(!(0), 0) ? __assert_rtn(__func__, "bytesobject.c", 852, "0") : (void)0); break;
    case 3: c = c != 0; break;
    case 4: c = c > 0; break;
    case 5: c = c >= 0; break;
    default:
        result = (&_Py_NotImplementedStruct);
        goto out;
    }
    result = c ? ((PyObject *) &_Py_TrueStruct) : ((PyObject *) &_Py_FalseStruct);
  out:
    ( ((PyObject*)(result))->ob_refcnt++);
    return result;
}

static Py_hash_t
bytes_hash(PyBytesObject *a)
{
    if (a->ob_shash == -1) {

        a->ob_shash = _Py_HashBytes((unsigned char *) a->ob_sval, (((PyVarObject*)(a))->ob_size));
    }
    return a->ob_shash;
}

static PyObject*
bytes_subscript(PyBytesObject* self, PyObject* item)
{
    if (((item)->ob_type->tp_as_number != ((void *)0) && (item)->ob_type->tp_as_number->nb_index != ((void *)0))) {
        Py_ssize_t i = PyNumber_AsSsize_t(item, PyExc_IndexError);
        if (i == -1 && PyErr_Occurred())
            return ((void *)0);
        if (i < 0)
            i += ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 884, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size));
        if (i < 0 || i >= ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 885, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size))) {
            PyErr_SetString(PyExc_IndexError,
                            "index out of range");
            return ((void *)0);
        }
        return PyLong_FromLong((unsigned char)self->ob_sval[i]);
    }
    else if (((((PyObject*)(item))->ob_type) == &PySlice_Type)) {
        Py_ssize_t start, stop, step, slicelength, cur, i;
        char* source_buf;
        char* result_buf;
        PyObject* result;

        if (PySlice_GetIndicesEx(item,
                         ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 899, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)),
                         &start, &stop, &step, &slicelength) < 0) {
            return ((void *)0);
        }

        if (slicelength <= 0) {
            return PyBytes_FromStringAndSize("", 0);
        }
        else if (start == 0 && step == 1 &&
                 slicelength == ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 908, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)) &&
                 ((((PyObject*)(self))->ob_type) == &PyBytes_Type)) {
            ( ((PyObject*)(self))->ob_refcnt++);
            return (PyObject *)self;
        }
        else if (step == 1) {
            return PyBytes_FromStringAndSize(
                ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 915, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)) + start,
                slicelength);
        }
        else {
            source_buf = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 919, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval));
            result = PyBytes_FromStringAndSize(((void *)0), slicelength);
            if (result == ((void *)0))
                return ((void *)0);

            result_buf = ((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 924, "PyBytes_Check(result)") : (void)0), (((PyBytesObject *)(result))->ob_sval));
            for (cur = start, i = 0; i < slicelength;
                 cur += step, i++) {
                result_buf[i] = source_buf[cur];
            }

            return result;
        }
    }
    else {
        PyErr_Format(PyExc_TypeError,
                     "byte indices must be integers, not %.200s",
                     (((PyObject*)(item))->ob_type)->tp_name);
        return ((void *)0);
    }
}

static int
bytes_buffer_getbuffer(PyBytesObject *self, Py_buffer *view, int flags)
{
    return PyBuffer_FillInfo(view, (PyObject*)self, (void *)self->ob_sval, (((PyVarObject*)(self))->ob_size),
                             1, flags);
}

static PySequenceMethods bytes_as_sequence = {
    (lenfunc)bytes_length,
    (binaryfunc)bytes_concat,
    (ssizeargfunc)bytes_repeat,
    (ssizeargfunc)bytes_item,
    0,
    0,
    0,
    (objobjproc)bytes_contains
};

static PyMappingMethods bytes_as_mapping = {
    (lenfunc)bytes_length,
    (binaryfunc)bytes_subscript,
    0,
};

static PyBufferProcs bytes_as_buffer = {
    (getbufferproc)bytes_buffer_getbuffer,
    ((void *)0),
};







static const char *stripformat[] = {"|O:lstrip", "|O:rstrip", "|O:strip"};



static char split__doc__[] = "B.split(sep=None, maxsplit=-1) -> list of bytes\n\nReturn a list of the sections in B, using sep as the delimiter.\nIf sep is not specified or is None, B is split on ASCII whitespace\ncharacters (space, tab, return, newline, formfeed, vertical tab).\nIf maxsplit is given, at most maxsplit splits are done.";







static PyObject *
bytes_split(PyBytesObject *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"sep", "maxsplit", 0};
    Py_ssize_t len = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 992, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)), n;
    Py_ssize_t maxsplit = -1;
    const char *s = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 994, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)), *sub;
    Py_buffer vsub;
    PyObject *list, *subobj = (&_Py_NoneStruct);

    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwds, "|On:split",
                                     kwlist, &subobj, &maxsplit))
        return ((void *)0);
    if (maxsplit < 0)
        maxsplit = ((Py_ssize_t)(((size_t)-1)>>1));
    if (subobj == (&_Py_NoneStruct))
        return stringlib_split_whitespace((PyObject*) self, s, len, maxsplit);
    if (_getbuffer(subobj, &vsub) < 0)
        return ((void *)0);
    sub = vsub.buf;
    n = vsub.len;

    list = stringlib_split((PyObject*) self, s, len, sub, n, maxsplit);
    PyBuffer_Release(&vsub);
    return list;
}

static char partition__doc__[] = "B.partition(sep) -> (head, sep, tail)\n\nSearch for the separator sep in B, and return the part before it,\nthe separator itself, and the part after it.  If the separator is not\nfound, returns B and two empty bytes objects.";






static PyObject *
bytes_partition(PyBytesObject *self, PyObject *sep_obj)
{
    const char *sep;
    Py_ssize_t sep_len;

    if (((((((PyObject*)(sep_obj))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
        sep = ((__builtin_expect(!(((((((PyObject*)(sep_obj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1029, "PyBytes_Check(sep_obj)") : (void)0), (((PyBytesObject *)(sep_obj))->ob_sval));
        sep_len = ((__builtin_expect(!(((((((PyObject*)(sep_obj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1030, "PyBytes_Check(sep_obj)") : (void)0),(((PyVarObject*)(sep_obj))->ob_size));
    }
    else if (PyObject_AsCharBuffer(sep_obj, &sep, &sep_len))
        return ((void *)0);

    return stringlib_partition(
        (PyObject*) self,
        ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1037, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1037, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)),
        sep_obj, sep, sep_len
        );
}

static char rpartition__doc__[] = "B.rpartition(sep) -> (head, sep, tail)\n\nSearch for the separator sep in B, starting at the end of B,\nand return the part before it, the separator itself, and the\npart after it.  If the separator is not found, returns two empty\nbytes objects and B.";







static PyObject *
bytes_rpartition(PyBytesObject *self, PyObject *sep_obj)
{
    const char *sep;
    Py_ssize_t sep_len;

    if (((((((PyObject*)(sep_obj))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
        sep = ((__builtin_expect(!(((((((PyObject*)(sep_obj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1057, "PyBytes_Check(sep_obj)") : (void)0), (((PyBytesObject *)(sep_obj))->ob_sval));
        sep_len = ((__builtin_expect(!(((((((PyObject*)(sep_obj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1058, "PyBytes_Check(sep_obj)") : (void)0),(((PyVarObject*)(sep_obj))->ob_size));
    }
    else if (PyObject_AsCharBuffer(sep_obj, &sep, &sep_len))
        return ((void *)0);

    return stringlib_rpartition(
        (PyObject*) self,
        ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1065, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1065, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)),
        sep_obj, sep, sep_len
        );
}

static char rsplit__doc__[] = "B.rsplit(sep=None, maxsplit=-1) -> list of bytes\n\nReturn a list of the sections in B, using sep as the delimiter,\nstarting at the end of B and working to the front.\nIf sep is not given, B is split on ASCII whitespace characters\n(space, tab, return, newline, formfeed, vertical tab).\nIf maxsplit is given, at most maxsplit splits are done.";
# 1080 "bytesobject.c"
static PyObject *
bytes_rsplit(PyBytesObject *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"sep", "maxsplit", 0};
    Py_ssize_t len = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1084, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)), n;
    Py_ssize_t maxsplit = -1;
    const char *s = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1086, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)), *sub;
    Py_buffer vsub;
    PyObject *list, *subobj = (&_Py_NoneStruct);

    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwds, "|On:rsplit",
                                     kwlist, &subobj, &maxsplit))
        return ((void *)0);
    if (maxsplit < 0)
        maxsplit = ((Py_ssize_t)(((size_t)-1)>>1));
    if (subobj == (&_Py_NoneStruct))
        return stringlib_rsplit_whitespace((PyObject*) self, s, len, maxsplit);
    if (_getbuffer(subobj, &vsub) < 0)
        return ((void *)0);
    sub = vsub.buf;
    n = vsub.len;

    list = stringlib_rsplit((PyObject*) self, s, len, sub, n, maxsplit);
    PyBuffer_Release(&vsub);
    return list;
}


static char join__doc__[] = "B.join(iterable_of_bytes) -> bytes\n\nConcatenate any number of bytes objects, with B in between each pair.\nExample: b'.'.join([b'ab', b'pq', b'rs']) -> b'ab.pq.rs'.";





static PyObject *
bytes_join(PyObject *self, PyObject *orig)
{
    char *sep = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1117, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval));
    const Py_ssize_t seplen = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1118, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size));
    PyObject *res = ((void *)0);
    char *p;
    Py_ssize_t seqlen = 0;
    size_t sz = 0;
    Py_ssize_t i;
    PyObject *seq, *item;

    seq = PySequence_Fast(orig, "");
    if (seq == ((void *)0)) {
        return ((void *)0);
    }

    seqlen = PySequence_Size(seq);
    if (seqlen == 0) {
        do { if ( --((PyObject*)(seq))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(seq)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(seq)))); } while (0);
        return PyBytes_FromString("");
    }
    if (seqlen == 1) {
        item = (((((((PyObject*)(seq))->ob_type))->tp_flags & ((1L<<25))) != 0) ? (((PyListObject *)(seq))->ob_item[0]) : (((PyTupleObject *)(seq))->ob_item[0]));
        if (((((PyObject*)(item))->ob_type) == &PyBytes_Type)) {
            ( ((PyObject*)(item))->ob_refcnt++);
            do { if ( --((PyObject*)(seq))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(seq)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(seq)))); } while (0);
            return item;
        }
    }







    for (i = 0; i < seqlen; i++) {
        const size_t old_sz = sz;
        item = (((((((PyObject*)(seq))->ob_type))->tp_flags & ((1L<<25))) != 0) ? (((PyListObject *)(seq))->ob_item[i]) : (((PyTupleObject *)(seq))->ob_item[i]));
        if (!((((((PyObject*)(item))->ob_type))->tp_flags & ((1L<<27))) != 0) && !((((PyObject*)(item))->ob_type) == (&PyByteArray_Type) || PyType_IsSubtype((((PyObject*)(item))->ob_type), (&PyByteArray_Type)))) {
            PyErr_Format(PyExc_TypeError,
                         "sequence item %zd: expected bytes,"
                         " %.80s found",
                         i, (((PyObject*)(item))->ob_type)->tp_name);
            do { if ( --((PyObject*)(seq))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(seq)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(seq)))); } while (0);
            return ((void *)0);
        }
        sz += (((PyVarObject*)(item))->ob_size);
        if (i != 0)
            sz += seplen;
        if (sz < old_sz || sz > ((Py_ssize_t)(((size_t)-1)>>1))) {
            PyErr_SetString(PyExc_OverflowError,
                "join() result is too long for bytes");
            do { if ( --((PyObject*)(seq))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(seq)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(seq)))); } while (0);
            return ((void *)0);
        }
    }


    res = PyBytes_FromStringAndSize((char*)((void *)0), sz);
    if (res == ((void *)0)) {
        do { if ( --((PyObject*)(seq))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(seq)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(seq)))); } while (0);
        return ((void *)0);
    }




    p = ((__builtin_expect(!(((((((PyObject*)(res))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1183, "PyBytes_Check(res)") : (void)0), (((PyBytesObject *)(res))->ob_sval));
    for (i = 0; i < seqlen; ++i) {
        size_t n;
        char *q;
        if (i) {
            ((__builtin_object_size (p, 0) != (size_t) -1) ? __builtin___memcpy_chk (p, sep, seplen, __builtin_object_size (p, 0)) : __inline_memcpy_chk (p, sep, seplen));
            p += seplen;
        }
        item = (((((((PyObject*)(seq))->ob_type))->tp_flags & ((1L<<25))) != 0) ? (((PyListObject *)(seq))->ob_item[i]) : (((PyTupleObject *)(seq))->ob_item[i]));
        n = (((PyVarObject*)(item))->ob_size);
        if (((((((PyObject*)(item))->ob_type))->tp_flags & ((1L<<27))) != 0))
            q = ((__builtin_expect(!(((((((PyObject*)(item))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1194, "PyBytes_Check(item)") : (void)0), (((PyBytesObject *)(item))->ob_sval));
        else
            q = ((__builtin_expect(!(((((PyObject*)(item))->ob_type) == (&PyByteArray_Type) || PyType_IsSubtype((((PyObject*)(item))->ob_type), (&PyByteArray_Type)))), 0) ? __assert_rtn(__func__, "bytesobject.c", 1196, "PyByteArray_Check(item)") : (void)0), (((PyVarObject*)(item))->ob_size) ? ((PyByteArrayObject *)(item))->ob_bytes : _PyByteArray_empty_string);
        ((__builtin_object_size (p, 0) != (size_t) -1) ? __builtin___memcpy_chk (p, q, n, __builtin_object_size (p, 0)) : __inline_memcpy_chk (p, q, n));
        p += n;
    }

    do { if ( --((PyObject*)(seq))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(seq)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(seq)))); } while (0);
    return res;
}

PyObject *
_PyBytes_Join(PyObject *sep, PyObject *x)
{
    (__builtin_expect(!(sep != ((void *)0) && ((((((PyObject*)(sep))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1208, "sep != NULL && PyBytes_Check(sep)") : (void)0);
    (__builtin_expect(!(x != ((void *)0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1209, "x != NULL") : (void)0);
    return bytes_join(sep, x);
}
# 1228 "bytesobject.c"
static inline Py_ssize_t
bytes_find_internal(PyBytesObject *self, PyObject *args, int dir)
{
    PyObject *subobj;
    char byte;
    Py_buffer subbuf;
    const char *sub;
    Py_ssize_t sub_len;
    Py_ssize_t start=0, end=((Py_ssize_t)(((size_t)-1)>>1));
    Py_ssize_t res;

    if (!stringlib_parse_args_finds_byte("find/rfind/index/rindex",
                                         args, &subobj, &byte, &start, &end))
        return -2;

    if (subobj) {
        if (_getbuffer(subobj, &subbuf) < 0)
            return -2;

        sub = subbuf.buf;
        sub_len = subbuf.len;
    }
    else {
        sub = &byte;
        sub_len = 1;
    }

    if (dir > 0)
        res = stringlib_find_slice(
            ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1257, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1257, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)),
            sub, sub_len, start, end);
    else
        res = stringlib_rfind_slice(
            ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1261, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1261, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)),
            sub, sub_len, start, end);

    if (subobj)
        PyBuffer_Release(&subbuf);

    return res;
}


static char find__doc__[] = "B.find(sub[, start[, end]]) -> int\n\nReturn the lowest index in B where substring sub is found,\nsuch that sub is contained within B[start:end].  Optional\narguments start and end are interpreted as in slice notation.\n\nReturn -1 on failure.";
# 1280 "bytesobject.c"
static PyObject *
bytes_find(PyBytesObject *self, PyObject *args)
{
    Py_ssize_t result = bytes_find_internal(self, args, +1);
    if (result == -2)
        return ((void *)0);
    return PyLong_FromSsize_t(result);
}


static char index__doc__[] = "B.index(sub[, start[, end]]) -> int\n\nLike B.find() but raise ValueError when the substring is not found.";




static PyObject *
bytes_index(PyBytesObject *self, PyObject *args)
{
    Py_ssize_t result = bytes_find_internal(self, args, +1);
    if (result == -2)
        return ((void *)0);
    if (result == -1) {
        PyErr_SetString(PyExc_ValueError,
                        "substring not found");
        return ((void *)0);
    }
    return PyLong_FromSsize_t(result);
}


static char rfind__doc__[] = "B.rfind(sub[, start[, end]]) -> int\n\nReturn the highest index in B where substring sub is found,\nsuch that sub is contained within B[start:end].  Optional\narguments start and end are interpreted as in slice notation.\n\nReturn -1 on failure.";
# 1319 "bytesobject.c"
static PyObject *
bytes_rfind(PyBytesObject *self, PyObject *args)
{
    Py_ssize_t result = bytes_find_internal(self, args, -1);
    if (result == -2)
        return ((void *)0);
    return PyLong_FromSsize_t(result);
}


static char rindex__doc__[] = "B.rindex(sub[, start[, end]]) -> int\n\nLike B.rfind() but raise ValueError when the substring is not found.";




static PyObject *
bytes_rindex(PyBytesObject *self, PyObject *args)
{
    Py_ssize_t result = bytes_find_internal(self, args, -1);
    if (result == -2)
        return ((void *)0);
    if (result == -1) {
        PyErr_SetString(PyExc_ValueError,
                        "substring not found");
        return ((void *)0);
    }
    return PyLong_FromSsize_t(result);
}


static inline PyObject *
do_xstrip(PyBytesObject *self, int striptype, PyObject *sepobj)
{
    Py_buffer vsep;
    char *s = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1353, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval));
    Py_ssize_t len = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1354, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size));
    char *sep;
    Py_ssize_t seplen;
    Py_ssize_t i, j;

    if (_getbuffer(sepobj, &vsep) < 0)
        return ((void *)0);
    sep = vsep.buf;
    seplen = vsep.len;

    i = 0;
    if (striptype != 1) {
        while (i < len && memchr(sep, ((unsigned char)((s[i]) & 0xff)), seplen)) {
            i++;
        }
    }

    j = len;
    if (striptype != 0) {
        do {
            j--;
        } while (j >= i && memchr(sep, ((unsigned char)((s[j]) & 0xff)), seplen));
        j++;
    }

    PyBuffer_Release(&vsep);

    if (i == 0 && j == len && ((((PyObject*)(self))->ob_type) == &PyBytes_Type)) {
        ( ((PyObject*)(self))->ob_refcnt++);
        return (PyObject*)self;
    }
    else
        return PyBytes_FromStringAndSize(s+i, j-i);
}


static inline PyObject *
do_strip(PyBytesObject *self, int striptype)
{
    char *s = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1393, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval));
    Py_ssize_t len = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1394, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)), i, j;

    i = 0;
    if (striptype != 1) {
        while (i < len && (_Py_ctype_table[((unsigned char)((s[i]) & 0xff))] & 0x08)) {
            i++;
        }
    }

    j = len;
    if (striptype != 0) {
        do {
            j--;
        } while (j >= i && (_Py_ctype_table[((unsigned char)((s[j]) & 0xff))] & 0x08));
        j++;
    }

    if (i == 0 && j == len && ((((PyObject*)(self))->ob_type) == &PyBytes_Type)) {
        ( ((PyObject*)(self))->ob_refcnt++);
        return (PyObject*)self;
    }
    else
        return PyBytes_FromStringAndSize(s+i, j-i);
}


static inline PyObject *
do_argstrip(PyBytesObject *self, int striptype, PyObject *args)
{
    PyObject *sep = ((void *)0);

    if (!_PyArg_ParseTuple_SizeT(args, (char *)stripformat[striptype], &sep))
        return ((void *)0);

    if (sep != ((void *)0) && sep != (&_Py_NoneStruct)) {
        return do_xstrip(self, striptype, sep);
    }
    return do_strip(self, striptype);
}


static char strip__doc__[] = "B.strip([bytes]) -> bytes\n\nStrip leading and trailing bytes contained in the argument.\nIf the argument is omitted, strip leading and trailing ASCII whitespace.";




static PyObject *
bytes_strip(PyBytesObject *self, PyObject *args)
{
    if ((((PyVarObject*)(args))->ob_size) == 0)
        return do_strip(self, 2);
    else
        return do_argstrip(self, 2, args);
}


static char lstrip__doc__[] = "B.lstrip([bytes]) -> bytes\n\nStrip leading bytes contained in the argument.\nIf the argument is omitted, strip leading ASCII whitespace.";




static PyObject *
bytes_lstrip(PyBytesObject *self, PyObject *args)
{
    if ((((PyVarObject*)(args))->ob_size) == 0)
        return do_strip(self, 0);
    else
        return do_argstrip(self, 0, args);
}


static char rstrip__doc__[] = "B.rstrip([bytes]) -> bytes\n\nStrip trailing bytes contained in the argument.\nIf the argument is omitted, strip trailing ASCII whitespace.";




static PyObject *
bytes_rstrip(PyBytesObject *self, PyObject *args)
{
    if ((((PyVarObject*)(args))->ob_size) == 0)
        return do_strip(self, 1);
    else
        return do_argstrip(self, 1, args);
}


static char count__doc__[] = "B.count(sub[, start[, end]]) -> int\n\nReturn the number of non-overlapping occurrences of substring sub in\nstring B[start:end].  Optional arguments start and end are interpreted\nas in slice notation.";






static PyObject *
bytes_count(PyBytesObject *self, PyObject *args)
{
    PyObject *sub_obj;
    const char *str = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1491, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)), *sub;
    Py_ssize_t sub_len;
    char byte;
    Py_ssize_t start = 0, end = ((Py_ssize_t)(((size_t)-1)>>1));

    Py_buffer vsub;
    PyObject *count_obj;

    if (!stringlib_parse_args_finds_byte("count", args, &sub_obj, &byte,
                                         &start, &end))
        return ((void *)0);

    if (sub_obj) {
        if (_getbuffer(sub_obj, &vsub) < 0)
            return ((void *)0);

        sub = vsub.buf;
        sub_len = vsub.len;
    }
    else {
        sub = &byte;
        sub_len = 1;
    }

    if (end > ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1515, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size))) end = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1515, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)); else if (end < 0) { end += ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1515, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)); if (end < 0) end = 0; } if (start < 0) { start += ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1515, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)); if (start < 0) start = 0; };

    count_obj = PyLong_FromSsize_t(
        stringlib_count(str + start, end - start, sub, sub_len, ((Py_ssize_t)(((size_t)-1)>>1)))
        );

    if (sub_obj)
        PyBuffer_Release(&vsub);

    return count_obj;
}


static char translate__doc__[] = "B.translate(table[, deletechars]) -> bytes\n\nReturn a copy of B, where all characters occurring in the\noptional argument deletechars are removed, and the remaining\ncharacters have been mapped through the given translation\ntable, which must be a bytes object of length 256.";







static PyObject *
bytes_translate(PyBytesObject *self, PyObject *args)
{
    register char *input, *output;
    const char *table;
    register Py_ssize_t i, c, changed = 0;
    PyObject *input_obj = (PyObject*)self;
    const char *output_start, *del_table=((void *)0);
    Py_ssize_t inlen, tablen, dellen = 0;
    PyObject *result;
    int trans_table[256];
    PyObject *tableobj, *delobj = ((void *)0);

    if (!PyArg_UnpackTuple(args, "translate", 1, 2,
                          &tableobj, &delobj))
        return ((void *)0);

    if (((((((PyObject*)(tableobj))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
        table = ((__builtin_expect(!(((((((PyObject*)(tableobj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1554, "PyBytes_Check(tableobj)") : (void)0), (((PyBytesObject *)(tableobj))->ob_sval));
        tablen = ((__builtin_expect(!(((((((PyObject*)(tableobj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1555, "PyBytes_Check(tableobj)") : (void)0),(((PyVarObject*)(tableobj))->ob_size));
    }
    else if (tableobj == (&_Py_NoneStruct)) {
        table = ((void *)0);
        tablen = 256;
    }
    else if (PyObject_AsCharBuffer(tableobj, &table, &tablen))
        return ((void *)0);

    if (tablen != 256) {
        PyErr_SetString(PyExc_ValueError,
          "translation table must be 256 characters long");
        return ((void *)0);
    }

    if (delobj != ((void *)0)) {
        if (((((((PyObject*)(delobj))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
            del_table = ((__builtin_expect(!(((((((PyObject*)(delobj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1572, "PyBytes_Check(delobj)") : (void)0), (((PyBytesObject *)(delobj))->ob_sval));
            dellen = ((__builtin_expect(!(((((((PyObject*)(delobj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1573, "PyBytes_Check(delobj)") : (void)0),(((PyVarObject*)(delobj))->ob_size));
        }
        else if (PyObject_AsCharBuffer(delobj, &del_table, &dellen))
            return ((void *)0);
    }
    else {
        del_table = ((void *)0);
        dellen = 0;
    }

    inlen = ((__builtin_expect(!(((((((PyObject*)(input_obj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1583, "PyBytes_Check(input_obj)") : (void)0),(((PyVarObject*)(input_obj))->ob_size));
    result = PyBytes_FromStringAndSize((char *)((void *)0), inlen);
    if (result == ((void *)0))
        return ((void *)0);
    output_start = output = PyBytes_AsString(result);
    input = ((__builtin_expect(!(((((((PyObject*)(input_obj))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1588, "PyBytes_Check(input_obj)") : (void)0), (((PyBytesObject *)(input_obj))->ob_sval));

    if (dellen == 0 && table != ((void *)0)) {

        for (i = inlen; --i >= 0; ) {
            c = ((unsigned char)((*input++) & 0xff));
            if (((unsigned char)(((*output++ = table[c])) & 0xff)) != c)
                changed = 1;
        }
        if (changed || !((((PyObject*)(input_obj))->ob_type) == &PyBytes_Type))
            return result;
        do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0);
        ( ((PyObject*)(input_obj))->ob_refcnt++);
        return input_obj;
    }

    if (table == ((void *)0)) {
        for (i = 0; i < 256; i++)
            trans_table[i] = ((unsigned char)((i) & 0xff));
    } else {
        for (i = 0; i < 256; i++)
            trans_table[i] = ((unsigned char)((table[i]) & 0xff));
    }

    for (i = 0; i < dellen; i++)
        trans_table[(int) ((unsigned char)((del_table[i]) & 0xff))] = -1;

    for (i = inlen; --i >= 0; ) {
        c = ((unsigned char)((*input++) & 0xff));
        if (trans_table[c] != -1)
            if (((unsigned char)((*output++ = (char)trans_table[c]) & 0xff)) == c)
                continue;
        changed = 1;
    }
    if (!changed && ((((PyObject*)(input_obj))->ob_type) == &PyBytes_Type)) {
        do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0);
        ( ((PyObject*)(input_obj))->ob_refcnt++);
        return input_obj;
    }

    if (inlen > 0)
        _PyBytes_Resize(&result, output - output_start);
    return result;
}


static PyObject *
bytes_maketrans(PyObject *null, PyObject *args)
{
    return _Py_bytes_maketrans(args);
}
# 1647 "bytesobject.c"
static PyBytesObject *
return_self(PyBytesObject *self)
{
    if (((((PyObject*)(self))->ob_type) == &PyBytes_Type)) {
        ( ((PyObject*)(self))->ob_refcnt++);
        return self;
    }
    return (PyBytesObject *)PyBytes_FromStringAndSize(
        ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1655, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)),
        ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1656, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)));
}

static inline Py_ssize_t
countchar(const char *target, Py_ssize_t target_len, char c, Py_ssize_t maxcount)
{
    Py_ssize_t count=0;
    const char *start=target;
    const char *end=target+target_len;

    while ( (start=((char *)memchr((const void *)(start), c, end-start))) != ((void *)0) ) {
        count++;
        if (count >= maxcount)
            break;
        start += 1;
    }
    return count;
}





static PyBytesObject *
replace_interleave(PyBytesObject *self,
                   const char *to_s, Py_ssize_t to_len,
                   Py_ssize_t maxcount)
{
    char *self_s, *result_s;
    Py_ssize_t self_len, result_len;
    Py_ssize_t count, i;
    PyBytesObject *result;

    self_len = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1689, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size));



    if (maxcount <= self_len)
        count = maxcount;
    else

        count = self_len + 1;



    (__builtin_expect(!(count > 0), 0) ? __assert_rtn(__func__, "bytesobject.c", 1701, "count > 0") : (void)0);
    if (to_len > (((Py_ssize_t)(((size_t)-1)>>1)) - self_len) / count) {
        PyErr_SetString(PyExc_OverflowError,
                        "replacement bytes are too long");
        return ((void *)0);
    }
    result_len = count * to_len + self_len;

    if (! (result = (PyBytesObject *)
                     PyBytes_FromStringAndSize(((void *)0), result_len)) )
        return ((void *)0);

    self_s = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1713, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval));
    result_s = ((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1714, "PyBytes_Check(result)") : (void)0), (((PyBytesObject *)(result))->ob_sval));




    ((__builtin_object_size (result_s, 0) != (size_t) -1) ? __builtin___memcpy_chk (result_s, to_s, to_len, __builtin_object_size (result_s, 0)) : __inline_memcpy_chk (result_s, to_s, to_len));
    result_s += to_len;
    count -= 1;

    for (i=0; i<count; i++) {
        *result_s++ = *self_s++;
        ((__builtin_object_size (result_s, 0) != (size_t) -1) ? __builtin___memcpy_chk (result_s, to_s, to_len, __builtin_object_size (result_s, 0)) : __inline_memcpy_chk (result_s, to_s, to_len));
        result_s += to_len;
    }


    ((__builtin_object_size (result_s, 0) != (size_t) -1) ? __builtin___memcpy_chk (result_s, self_s, self_len-i, __builtin_object_size (result_s, 0)) : __inline_memcpy_chk (result_s, self_s, self_len-i));

    return result;
}



static PyBytesObject *
replace_delete_single_character(PyBytesObject *self,
                                char from_c, Py_ssize_t maxcount)
{
    char *self_s, *result_s;
    char *start, *next, *end;
    Py_ssize_t self_len, result_len;
    Py_ssize_t count;
    PyBytesObject *result;

    self_len = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1747, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size));
    self_s = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1748, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval));

    count = countchar(self_s, self_len, from_c, maxcount);
    if (count == 0) {
        return return_self(self);
    }

    result_len = self_len - count;
    (__builtin_expect(!(result_len>=0), 0) ? __assert_rtn(__func__, "bytesobject.c", 1756, "result_len>=0") : (void)0);

    if ( (result = (PyBytesObject *)
                    PyBytes_FromStringAndSize(((void *)0), result_len)) == ((void *)0))
        return ((void *)0);
    result_s = ((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1761, "PyBytes_Check(result)") : (void)0), (((PyBytesObject *)(result))->ob_sval));

    start = self_s;
    end = self_s + self_len;
    while (count-- > 0) {
        next = ((char *)memchr((const void *)(start), from_c, end-start));
        if (next == ((void *)0))
            break;
        ((__builtin_object_size (result_s, 0) != (size_t) -1) ? __builtin___memcpy_chk (result_s, start, next-start, __builtin_object_size (result_s, 0)) : __inline_memcpy_chk (result_s, start, next-start));
        result_s += (next-start);
        start = next+1;
    }
    ((__builtin_object_size (result_s, 0) != (size_t) -1) ? __builtin___memcpy_chk (result_s, start, end-start, __builtin_object_size (result_s, 0)) : __inline_memcpy_chk (result_s, start, end-start));

    return result;
}



static PyBytesObject *
replace_delete_substring(PyBytesObject *self,
                         const char *from_s, Py_ssize_t from_len,
                         Py_ssize_t maxcount) {
    char *self_s, *result_s;
    char *start, *next, *end;
    Py_ssize_t self_len, result_len;
    Py_ssize_t count, offset;
    PyBytesObject *result;

    self_len = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1790, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size));
    self_s = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1791, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval));

    count = stringlib_count(self_s, self_len,
                            from_s, from_len,
                            maxcount);

    if (count == 0) {

        return return_self(self);
    }

    result_len = self_len - (count * from_len);
    (__builtin_expect(!(result_len>=0), 0) ? __assert_rtn(__func__, "bytesobject.c", 1803, "result_len>=0") : (void)0);

    if ( (result = (PyBytesObject *)
          PyBytes_FromStringAndSize(((void *)0), result_len)) == ((void *)0) )
        return ((void *)0);

    result_s = ((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1809, "PyBytes_Check(result)") : (void)0), (((PyBytesObject *)(result))->ob_sval));

    start = self_s;
    end = self_s + self_len;
    while (count-- > 0) {
        offset = stringlib_find(start, end-start,
                                from_s, from_len,
                                0);
        if (offset == -1)
            break;
        next = start + offset;

        ((__builtin_object_size (result_s, 0) != (size_t) -1) ? __builtin___memcpy_chk (result_s, start, next-start, __builtin_object_size (result_s, 0)) : __inline_memcpy_chk (result_s, start, next-start));

        result_s += (next-start);
        start = next+from_len;
    }
    ((__builtin_object_size (result_s, 0) != (size_t) -1) ? __builtin___memcpy_chk (result_s, start, end-start, __builtin_object_size (result_s, 0)) : __inline_memcpy_chk (result_s, start, end-start));
    return result;
}


static PyBytesObject *
replace_single_character_in_place(PyBytesObject *self,
                                  char from_c, char to_c,
                                  Py_ssize_t maxcount)
{
    char *self_s, *result_s, *start, *end, *next;
    Py_ssize_t self_len;
    PyBytesObject *result;


    self_s = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1841, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval));
    self_len = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1842, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size));

    next = ((char *)memchr((const void *)(self_s), from_c, self_len));

    if (next == ((void *)0)) {

        return return_self(self);
    }


    result = (PyBytesObject *) PyBytes_FromStringAndSize(((void *)0), self_len);
    if (result == ((void *)0))
        return ((void *)0);
    result_s = ((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1855, "PyBytes_Check(result)") : (void)0), (((PyBytesObject *)(result))->ob_sval));
    ((__builtin_object_size (result_s, 0) != (size_t) -1) ? __builtin___memcpy_chk (result_s, self_s, self_len, __builtin_object_size (result_s, 0)) : __inline_memcpy_chk (result_s, self_s, self_len));


    start = result_s + (next-self_s);
    *start = to_c;
    start++;
    end = result_s + self_len;

    while (--maxcount > 0) {
        next = ((char *)memchr((const void *)(start), from_c, end-start));
        if (next == ((void *)0))
            break;
        *next = to_c;
        start = next+1;
    }

    return result;
}


static PyBytesObject *
replace_substring_in_place(PyBytesObject *self,
                           const char *from_s, Py_ssize_t from_len,
                           const char *to_s, Py_ssize_t to_len,
                           Py_ssize_t maxcount)
{
    char *result_s, *start, *end;
    char *self_s;
    Py_ssize_t self_len, offset;
    PyBytesObject *result;



    self_s = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1889, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval));
    self_len = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1890, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size));

    offset = stringlib_find(self_s, self_len,
                            from_s, from_len,
                            0);
    if (offset == -1) {

        return return_self(self);
    }


    result = (PyBytesObject *) PyBytes_FromStringAndSize(((void *)0), self_len);
    if (result == ((void *)0))
        return ((void *)0);
    result_s = ((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1904, "PyBytes_Check(result)") : (void)0), (((PyBytesObject *)(result))->ob_sval));
    ((__builtin_object_size (result_s, 0) != (size_t) -1) ? __builtin___memcpy_chk (result_s, self_s, self_len, __builtin_object_size (result_s, 0)) : __inline_memcpy_chk (result_s, self_s, self_len));


    start = result_s + offset;
    ((__builtin_object_size (start, 0) != (size_t) -1) ? __builtin___memcpy_chk (start, to_s, from_len, __builtin_object_size (start, 0)) : __inline_memcpy_chk (start, to_s, from_len));
    start += from_len;
    end = result_s + self_len;

    while ( --maxcount > 0) {
        offset = stringlib_find(start, end-start,
                                from_s, from_len,
                                0);
        if (offset==-1)
            break;
        ((__builtin_object_size (start+offset, 0) != (size_t) -1) ? __builtin___memcpy_chk (start+offset, to_s, from_len, __builtin_object_size (start+offset, 0)) : __inline_memcpy_chk (start+offset, to_s, from_len));
        start += offset+from_len;
    }

    return result;
}


static PyBytesObject *
replace_single_character(PyBytesObject *self,
                         char from_c,
                         const char *to_s, Py_ssize_t to_len,
                         Py_ssize_t maxcount)
{
    char *self_s, *result_s;
    char *start, *next, *end;
    Py_ssize_t self_len, result_len;
    Py_ssize_t count;
    PyBytesObject *result;

    self_s = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1939, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval));
    self_len = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1940, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size));

    count = countchar(self_s, self_len, from_c, maxcount);
    if (count == 0) {

        return return_self(self);
    }



    (__builtin_expect(!(count > 0), 0) ? __assert_rtn(__func__, "bytesobject.c", 1950, "count > 0") : (void)0);
    if (to_len - 1 > (((Py_ssize_t)(((size_t)-1)>>1)) - self_len) / count) {
        PyErr_SetString(PyExc_OverflowError,
                        "replacement bytes are too long");
        return ((void *)0);
    }
    result_len = self_len + count * (to_len - 1);

    if ( (result = (PyBytesObject *)
          PyBytes_FromStringAndSize(((void *)0), result_len)) == ((void *)0))
        return ((void *)0);
    result_s = ((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 1961, "PyBytes_Check(result)") : (void)0), (((PyBytesObject *)(result))->ob_sval));

    start = self_s;
    end = self_s + self_len;
    while (count-- > 0) {
        next = ((char *)memchr((const void *)(start), from_c, end-start));
        if (next == ((void *)0))
            break;

        if (next == start) {

            ((__builtin_object_size (result_s, 0) != (size_t) -1) ? __builtin___memcpy_chk (result_s, to_s, to_len, __builtin_object_size (result_s, 0)) : __inline_memcpy_chk (result_s, to_s, to_len));
            result_s += to_len;
            start += 1;
        } else {

            ((__builtin_object_size (result_s, 0) != (size_t) -1) ? __builtin___memcpy_chk (result_s, start, next-start, __builtin_object_size (result_s, 0)) : __inline_memcpy_chk (result_s, start, next-start));
            result_s += (next-start);
            ((__builtin_object_size (result_s, 0) != (size_t) -1) ? __builtin___memcpy_chk (result_s, to_s, to_len, __builtin_object_size (result_s, 0)) : __inline_memcpy_chk (result_s, to_s, to_len));
            result_s += to_len;
            start = next+1;
        }
    }

    ((__builtin_object_size (result_s, 0) != (size_t) -1) ? __builtin___memcpy_chk (result_s, start, end-start, __builtin_object_size (result_s, 0)) : __inline_memcpy_chk (result_s, start, end-start));

    return result;
}


static PyBytesObject *
replace_substring(PyBytesObject *self,
                  const char *from_s, Py_ssize_t from_len,
                  const char *to_s, Py_ssize_t to_len,
                  Py_ssize_t maxcount) {
    char *self_s, *result_s;
    char *start, *next, *end;
    Py_ssize_t self_len, result_len;
    Py_ssize_t count, offset;
    PyBytesObject *result;

    self_s = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2002, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval));
    self_len = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2003, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size));

    count = stringlib_count(self_s, self_len,
                            from_s, from_len,
                            maxcount);

    if (count == 0) {

        return return_self(self);
    }



    (__builtin_expect(!(count > 0), 0) ? __assert_rtn(__func__, "bytesobject.c", 2016, "count > 0") : (void)0);
    if (to_len - from_len > (((Py_ssize_t)(((size_t)-1)>>1)) - self_len) / count) {
        PyErr_SetString(PyExc_OverflowError,
                        "replacement bytes are too long");
        return ((void *)0);
    }
    result_len = self_len + count * (to_len-from_len);

    if ( (result = (PyBytesObject *)
          PyBytes_FromStringAndSize(((void *)0), result_len)) == ((void *)0))
        return ((void *)0);
    result_s = ((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2027, "PyBytes_Check(result)") : (void)0), (((PyBytesObject *)(result))->ob_sval));

    start = self_s;
    end = self_s + self_len;
    while (count-- > 0) {
        offset = stringlib_find(start, end-start,
                                from_s, from_len,
                                0);
        if (offset == -1)
            break;
        next = start+offset;
        if (next == start) {

            ((__builtin_object_size (result_s, 0) != (size_t) -1) ? __builtin___memcpy_chk (result_s, to_s, to_len, __builtin_object_size (result_s, 0)) : __inline_memcpy_chk (result_s, to_s, to_len));
            result_s += to_len;
            start += from_len;
        } else {

            ((__builtin_object_size (result_s, 0) != (size_t) -1) ? __builtin___memcpy_chk (result_s, start, next-start, __builtin_object_size (result_s, 0)) : __inline_memcpy_chk (result_s, start, next-start));
            result_s += (next-start);
            ((__builtin_object_size (result_s, 0) != (size_t) -1) ? __builtin___memcpy_chk (result_s, to_s, to_len, __builtin_object_size (result_s, 0)) : __inline_memcpy_chk (result_s, to_s, to_len));
            result_s += to_len;
            start = next+from_len;
        }
    }

    ((__builtin_object_size (result_s, 0) != (size_t) -1) ? __builtin___memcpy_chk (result_s, start, end-start, __builtin_object_size (result_s, 0)) : __inline_memcpy_chk (result_s, start, end-start));

    return result;
}


static PyBytesObject *
replace(PyBytesObject *self,
    const char *from_s, Py_ssize_t from_len,
    const char *to_s, Py_ssize_t to_len,
    Py_ssize_t maxcount)
{
    if (maxcount < 0) {
        maxcount = ((Py_ssize_t)(((size_t)-1)>>1));
    } else if (maxcount == 0 || ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2067, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)) == 0) {

        return return_self(self);
    }

    if (maxcount == 0 ||
        (from_len == 0 && to_len == 0)) {

        return return_self(self);
    }



    if (from_len == 0) {



        return replace_interleave(self, to_s, to_len, maxcount);
    }




    if (((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2090, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)) == 0) {
        return return_self(self);
    }

    if (to_len == 0) {

        if (from_len == 1) {
            return replace_delete_single_character(
                self, from_s[0], maxcount);
        } else {
            return replace_delete_substring(self, from_s,
                                            from_len, maxcount);
        }
    }



    if (from_len == to_len) {
        if (from_len == 1) {
            return replace_single_character_in_place(
                self,
                from_s[0],
                to_s[0],
                maxcount);
        } else {
            return replace_substring_in_place(
                self, from_s, from_len, to_s, to_len,
                maxcount);
        }
    }


    if (from_len == 1) {
        return replace_single_character(self, from_s[0],
                                        to_s, to_len, maxcount);
    } else {

        return replace_substring(self, from_s, from_len, to_s, to_len,
                                 maxcount);
    }
}

static char replace__doc__[] = "B.replace(old, new[, count]) -> bytes\n\nReturn a copy of B with all occurrences of subsection\nold replaced by new.  If the optional argument count is\ngiven, only first count occurances are replaced.";






static PyObject *
bytes_replace(PyBytesObject *self, PyObject *args)
{
    Py_ssize_t count = -1;
    PyObject *from, *to;
    const char *from_s, *to_s;
    Py_ssize_t from_len, to_len;

    if (!_PyArg_ParseTuple_SizeT(args, "OO|n:replace", &from, &to, &count))
        return ((void *)0);

    if (((((((PyObject*)(from))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
        from_s = ((__builtin_expect(!(((((((PyObject*)(from))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2151, "PyBytes_Check(from)") : (void)0), (((PyBytesObject *)(from))->ob_sval));
        from_len = ((__builtin_expect(!(((((((PyObject*)(from))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2152, "PyBytes_Check(from)") : (void)0),(((PyVarObject*)(from))->ob_size));
    }
    else if (PyObject_AsCharBuffer(from, &from_s, &from_len))
        return ((void *)0);

    if (((((((PyObject*)(to))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
        to_s = ((__builtin_expect(!(((((((PyObject*)(to))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2158, "PyBytes_Check(to)") : (void)0), (((PyBytesObject *)(to))->ob_sval));
        to_len = ((__builtin_expect(!(((((((PyObject*)(to))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2159, "PyBytes_Check(to)") : (void)0),(((PyVarObject*)(to))->ob_size));
    }
    else if (PyObject_AsCharBuffer(to, &to_s, &to_len))
        return ((void *)0);

    return (PyObject *)replace((PyBytesObject *) self,
                               from_s, from_len,
                               to_s, to_len, count);
}







static int
_bytes_tailmatch(PyBytesObject *self, PyObject *substr, Py_ssize_t start,
                  Py_ssize_t end, int direction)
{
    Py_ssize_t len = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2179, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size));
    Py_ssize_t slen;
    const char* sub;
    const char* str;

    if (((((((PyObject*)(substr))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
        sub = ((__builtin_expect(!(((((((PyObject*)(substr))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2185, "PyBytes_Check(substr)") : (void)0), (((PyBytesObject *)(substr))->ob_sval));
        slen = ((__builtin_expect(!(((((((PyObject*)(substr))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2186, "PyBytes_Check(substr)") : (void)0),(((PyVarObject*)(substr))->ob_size));
    }
    else if (PyObject_AsCharBuffer(substr, &sub, &slen))
        return -1;
    str = ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2190, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval));

    if (end > len) end = len; else if (end < 0) { end += len; if (end < 0) end = 0; } if (start < 0) { start += len; if (start < 0) start = 0; };

    if (direction < 0) {

        if (start+slen > len)
            return 0;
    } else {

        if (end-start < slen || start > len)
            return 0;

        if (end-slen > start)
            start = end - slen;
    }
    if (end-start >= slen)
        return ! memcmp(str+start, sub, slen);
    return 0;
}


static char startswith__doc__[] = "B.startswith(prefix[, start[, end]]) -> bool\n\nReturn True if B starts with the specified prefix, False otherwise.\nWith optional start, test B beginning at that position.\nWith optional end, stop comparing B at that position.\nprefix can also be a tuple of bytes to try.";







static PyObject *
bytes_startswith(PyBytesObject *self, PyObject *args)
{
    Py_ssize_t start = 0;
    Py_ssize_t end = ((Py_ssize_t)(((size_t)-1)>>1));
    PyObject *subobj;
    int result;

    if (!stringlib_parse_args_finds("startswith", args, &subobj, &start, &end))
        return ((void *)0);
    if (((((((PyObject*)(subobj))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
        Py_ssize_t i;
        for (i = 0; i < (((PyVarObject*)(subobj))->ob_size); i++) {
            result = _bytes_tailmatch(self,
                            (((PyTupleObject *)(subobj))->ob_item[i]),
                            start, end, -1);
            if (result == -1)
                return ((void *)0);
            else if (result) {
                return ( ((PyObject*)(((PyObject *) &_Py_TrueStruct)))->ob_refcnt++), ((PyObject *) &_Py_TrueStruct);
            }
        }
        return ( ((PyObject*)(((PyObject *) &_Py_FalseStruct)))->ob_refcnt++), ((PyObject *) &_Py_FalseStruct);
    }
    result = _bytes_tailmatch(self, subobj, start, end, -1);
    if (result == -1) {
        if (PyErr_ExceptionMatches(PyExc_TypeError))
            PyErr_Format(PyExc_TypeError, "startswith first arg must be bytes "
                         "or a tuple of bytes, not %s", (((PyObject*)(subobj))->ob_type)->tp_name);
        return ((void *)0);
    }
    else
        return PyBool_FromLong(result);
}


static char endswith__doc__[] = "B.endswith(suffix[, start[, end]]) -> bool\n\nReturn True if B ends with the specified suffix, False otherwise.\nWith optional start, test B beginning at that position.\nWith optional end, stop comparing B at that position.\nsuffix can also be a tuple of bytes to try.";







static PyObject *
bytes_endswith(PyBytesObject *self, PyObject *args)
{
    Py_ssize_t start = 0;
    Py_ssize_t end = ((Py_ssize_t)(((size_t)-1)>>1));
    PyObject *subobj;
    int result;

    if (!stringlib_parse_args_finds("endswith", args, &subobj, &start, &end))
        return ((void *)0);
    if (((((((PyObject*)(subobj))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
        Py_ssize_t i;
        for (i = 0; i < (((PyVarObject*)(subobj))->ob_size); i++) {
            result = _bytes_tailmatch(self,
                            (((PyTupleObject *)(subobj))->ob_item[i]),
                            start, end, +1);
            if (result == -1)
                return ((void *)0);
            else if (result) {
                return ( ((PyObject*)(((PyObject *) &_Py_TrueStruct)))->ob_refcnt++), ((PyObject *) &_Py_TrueStruct);
            }
        }
        return ( ((PyObject*)(((PyObject *) &_Py_FalseStruct)))->ob_refcnt++), ((PyObject *) &_Py_FalseStruct);
    }
    result = _bytes_tailmatch(self, subobj, start, end, +1);
    if (result == -1) {
        if (PyErr_ExceptionMatches(PyExc_TypeError))
            PyErr_Format(PyExc_TypeError, "endswith first arg must be bytes or "
                         "a tuple of bytes, not %s", (((PyObject*)(subobj))->ob_type)->tp_name);
        return ((void *)0);
    }
    else
        return PyBool_FromLong(result);
}


static char decode__doc__[] = "B.decode(encoding='utf-8', errors='strict') -> str\n\nDecode B using the codec registered for encoding. Default encoding\nis 'utf-8'. errors may be given to set a different error\nhandling scheme.  Default is 'strict' meaning that encoding errors raise\na UnicodeDecodeError.  Other possible values are 'ignore' and 'replace'\nas well as any other name registerd with codecs.register_error that is\nable to handle UnicodeDecodeErrors.";
# 2310 "bytesobject.c"
static PyObject *
bytes_decode(PyObject *self, PyObject *args, PyObject *kwargs)
{
    const char *encoding = ((void *)0);
    const char *errors = ((void *)0);
    static char *kwlist[] = {"encoding", "errors", 0};

    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "|ss:decode", kwlist, &encoding, &errors))
        return ((void *)0);
    if (encoding == ((void *)0))
        encoding = PyUnicode_GetDefaultEncoding();
    return PyUnicode_FromEncodedObject(self, encoding, errors);
}


static char splitlines__doc__[] = "B.splitlines([keepends]) -> list of lines\n\nReturn a list of the lines in B, breaking at line boundaries.\nLine breaks are not included in the resulting list unless keepends\nis given and true.";






static PyObject*
bytes_splitlines(PyObject *self, PyObject *args, PyObject *kwds)
{
    static char *kwlist[] = {"keepends", 0};
    int keepends = 0;

    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwds, "|i:splitlines",
                                     kwlist, &keepends))
        return ((void *)0);

    return stringlib_splitlines(
        (PyObject*) self, ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2343, "PyBytes_Check(self)") : (void)0), (((PyBytesObject *)(self))->ob_sval)),
        ((__builtin_expect(!(((((((PyObject*)(self))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2344, "PyBytes_Check(self)") : (void)0),(((PyVarObject*)(self))->ob_size)), keepends
        );
}


static char fromhex_doc[] = "bytes.fromhex(string) -> bytes\n\nCreate a bytes object from a string of hexadecimal numbers.\nSpaces between two numbers are accepted.\nExample: bytes.fromhex('B9 01EF') -> b'\\xb9\\x01\\xef'.";






static int
hex_digit_to_int(Py_UCS4 c)
{
    if (c >= 128)
        return -1;
    if ((_Py_ctype_table[((unsigned char)((c) & 0xff))] & 0x04))
        return c - '0';
    else {
        if ((_Py_ctype_table[((unsigned char)((c) & 0xff))] & 0x02))
            c = (_Py_ctype_tolower[((unsigned char)((c) & 0xff))]);
        if (c >= 'a' && c <= 'f')
            return c - 'a' + 10;
    }
    return -1;
}

static PyObject *
bytes_fromhex(PyObject *cls, PyObject *args)
{
    PyObject *newstring, *hexobj;
    char *buf;
    Py_ssize_t hexlen, byteslen, i, j;
    int top, bot;
    void *data;
    unsigned int kind;

    if (!_PyArg_ParseTuple_SizeT(args, "U:fromhex", &hexobj))
        return ((void *)0);
    (__builtin_expect(!(((((((PyObject*)(hexobj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2384, "PyUnicode_Check(hexobj)") : (void)0);
    if (((__builtin_expect(!(((((((PyObject*)(hexobj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2385, "PyUnicode_Check(hexobj)") : (void)0), ((((PyASCIIObject*)hexobj)->state.ready) ? 0 : _PyUnicode_Ready((PyObject *)(hexobj)))))
        return ((void *)0);
    kind = ((__builtin_expect(!(((((((PyObject*)(hexobj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2387, "PyUnicode_Check(hexobj)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)hexobj)->state.ready)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2387, "PyUnicode_IS_READY(hexobj)") : (void)0), ((PyASCIIObject *)(hexobj))->state.kind);
    data = ((__builtin_expect(!(((((((PyObject*)(hexobj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2388, "PyUnicode_Check(hexobj)") : (void)0), (((PyASCIIObject*)(hexobj))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)(hexobj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2388, "PyUnicode_Check(hexobj)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)hexobj)->state.ready)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2388, "PyUnicode_IS_READY(hexobj)") : (void)0), ((PyASCIIObject*)hexobj)->state.ascii) ? ((void*)((PyASCIIObject*)(hexobj) + 1)) : ((void*)((PyCompactUnicodeObject*)(hexobj) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)(hexobj))->data.any), 0) ? __assert_rtn(__func__, "bytesobject.c", 2388, "((PyUnicodeObject*)(hexobj))->data.any") : (void)0), ((((PyUnicodeObject *)(hexobj))->data.any))));
    hexlen = ((__builtin_expect(!(((((((PyObject*)(hexobj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2389, "PyUnicode_Check(hexobj)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)hexobj)->state.ready)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2389, "PyUnicode_IS_READY(hexobj)") : (void)0), ((PyASCIIObject *)(hexobj))->length);

    byteslen = hexlen/2;
    newstring = PyBytes_FromStringAndSize(((void *)0), byteslen);
    if (!newstring)
        return ((void *)0);
    buf = ((__builtin_expect(!(((((((PyObject*)(newstring))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2395, "PyBytes_Check(newstring)") : (void)0), (((PyBytesObject *)(newstring))->ob_sval));
    for (i = j = 0; i < hexlen; i += 2) {

        while (((Py_UCS4) ((kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(data))[(i)] : ((kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(data))[(i)] : ((const Py_UCS4 *)(data))[(i)] ) )) == ' ')
            i++;
        if (i >= hexlen)
            break;
        top = hex_digit_to_int(((Py_UCS4) ((kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(data))[(i)] : ((kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(data))[(i)] : ((const Py_UCS4 *)(data))[(i)] ) )));
        bot = hex_digit_to_int(((Py_UCS4) ((kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(data))[(i+1)] : ((kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(data))[(i+1)] : ((const Py_UCS4 *)(data))[(i+1)] ) )));
        if (top == -1 || bot == -1) {
            PyErr_Format(PyExc_ValueError,
                         "non-hexadecimal number found in "
                         "fromhex() arg at position %zd", i);
            goto error;
        }
        buf[j++] = (top << 4) + bot;
    }
    if (j != byteslen && _PyBytes_Resize(&newstring, j) < 0)
        goto error;
    return newstring;

  error:
    do { if ((newstring) == ((void *)0)) ; else do { if ( --((PyObject*)(newstring))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(newstring)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(newstring)))); } while (0); } while (0);
    return ((void *)0);
}

static char sizeof__doc__[] = "B.__sizeof__() -> size of B in memory, in bytes";


static PyObject *
bytes_sizeof(PyBytesObject *v)
{
    Py_ssize_t res;
    res = (__builtin_offsetof (PyBytesObject, ob_sval) + 1) + (((PyVarObject*)(v))->ob_size) * (((PyObject*)(v))->ob_type)->tp_itemsize;
    return PyLong_FromSsize_t(res);
}


static PyObject *
bytes_getnewargs(PyBytesObject *v)
{
    return _Py_BuildValue_SizeT("(y#)", v->ob_sval, (((PyVarObject*)(v))->ob_size));
}


static PyMethodDef
bytes_methods[] = {
    {"__getnewargs__", (PyCFunction)bytes_getnewargs, 0x0004},
    {"capitalize", (PyCFunction)stringlib_capitalize, 0x0004,
     _Py_capitalize__doc__},
    {"center", (PyCFunction)stringlib_center, 0x0001, center__doc__},
    {"count", (PyCFunction)bytes_count, 0x0001, count__doc__},
    {"decode", (PyCFunction)bytes_decode, 0x0001 | 0x0002, decode__doc__},
    {"endswith", (PyCFunction)bytes_endswith, 0x0001,
     endswith__doc__},
    {"expandtabs", (PyCFunction)stringlib_expandtabs, 0x0001,
     expandtabs__doc__},
    {"find", (PyCFunction)bytes_find, 0x0001, find__doc__},
    {"fromhex", (PyCFunction)bytes_fromhex, 0x0001|0x0010,
     fromhex_doc},
    {"index", (PyCFunction)bytes_index, 0x0001, index__doc__},
    {"isalnum", (PyCFunction)stringlib_isalnum, 0x0004,
     _Py_isalnum__doc__},
    {"isalpha", (PyCFunction)stringlib_isalpha, 0x0004,
     _Py_isalpha__doc__},
    {"isdigit", (PyCFunction)stringlib_isdigit, 0x0004,
     _Py_isdigit__doc__},
    {"islower", (PyCFunction)stringlib_islower, 0x0004,
     _Py_islower__doc__},
    {"isspace", (PyCFunction)stringlib_isspace, 0x0004,
     _Py_isspace__doc__},
    {"istitle", (PyCFunction)stringlib_istitle, 0x0004,
     _Py_istitle__doc__},
    {"isupper", (PyCFunction)stringlib_isupper, 0x0004,
     _Py_isupper__doc__},
    {"join", (PyCFunction)bytes_join, 0x0008, join__doc__},
    {"ljust", (PyCFunction)stringlib_ljust, 0x0001, ljust__doc__},
    {"lower", (PyCFunction)stringlib_lower, 0x0004, _Py_lower__doc__},
    {"lstrip", (PyCFunction)bytes_lstrip, 0x0001, lstrip__doc__},
    {"maketrans", (PyCFunction)bytes_maketrans, 0x0001|0x0020,
     _Py_maketrans__doc__},
    {"partition", (PyCFunction)bytes_partition, 0x0008, partition__doc__},
    {"replace", (PyCFunction)bytes_replace, 0x0001, replace__doc__},
    {"rfind", (PyCFunction)bytes_rfind, 0x0001, rfind__doc__},
    {"rindex", (PyCFunction)bytes_rindex, 0x0001, rindex__doc__},
    {"rjust", (PyCFunction)stringlib_rjust, 0x0001, rjust__doc__},
    {"rpartition", (PyCFunction)bytes_rpartition, 0x0008,
     rpartition__doc__},
    {"rsplit", (PyCFunction)bytes_rsplit, 0x0001 | 0x0002, rsplit__doc__},
    {"rstrip", (PyCFunction)bytes_rstrip, 0x0001, rstrip__doc__},
    {"split", (PyCFunction)bytes_split, 0x0001 | 0x0002, split__doc__},
    {"splitlines", (PyCFunction)bytes_splitlines, 0x0001 | 0x0002,
     splitlines__doc__},
    {"startswith", (PyCFunction)bytes_startswith, 0x0001,
     startswith__doc__},
    {"strip", (PyCFunction)bytes_strip, 0x0001, strip__doc__},
    {"swapcase", (PyCFunction)stringlib_swapcase, 0x0004,
     _Py_swapcase__doc__},
    {"title", (PyCFunction)stringlib_title, 0x0004, _Py_title__doc__},
    {"translate", (PyCFunction)bytes_translate, 0x0001,
     translate__doc__},
    {"upper", (PyCFunction)stringlib_upper, 0x0004, _Py_upper__doc__},
    {"zfill", (PyCFunction)stringlib_zfill, 0x0001, zfill__doc__},
    {"__sizeof__", (PyCFunction)bytes_sizeof, 0x0004,
     sizeof__doc__},
    {((void *)0), ((void *)0)}
};

static PyObject *
str_subtype_new(PyTypeObject *type, PyObject *args, PyObject *kwds);

static PyObject *
bytes_new(PyTypeObject *type, PyObject *args, PyObject *kwds)
{
    PyObject *x = ((void *)0);
    const char *encoding = ((void *)0);
    const char *errors = ((void *)0);
    PyObject *new = ((void *)0);
    PyObject *func;
    Py_ssize_t size;
    static char *kwlist[] = {"source", "encoding", "errors", 0};
    static _Py_Identifier PyId___bytes__ = { 0, "__bytes__", 0 };

    if (type != &PyBytes_Type)
        return str_subtype_new(type, args, kwds);
    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwds, "|Oss:bytes", kwlist, &x,
                                     &encoding, &errors))
        return ((void *)0);
    if (x == ((void *)0)) {
        if (encoding != ((void *)0) || errors != ((void *)0)) {
            PyErr_SetString(PyExc_TypeError,
                            "encoding or errors without sequence "
                            "argument");
            return ((void *)0);
        }
        return PyBytes_FromString("");
    }

    if (((((((PyObject*)(x))->ob_type))->tp_flags & ((1L<<28))) != 0)) {

        if (encoding == ((void *)0)) {
            PyErr_SetString(PyExc_TypeError,
                            "string argument without an encoding");
            return ((void *)0);
        }
        new = PyUnicode_AsEncodedString(x, encoding, errors);
        if (new == ((void *)0))
            return ((void *)0);
        (__builtin_expect(!(((((((PyObject*)(new))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2543, "PyBytes_Check(new)") : (void)0);
        return new;
    }




    func = _PyObject_LookupSpecial(x, &PyId___bytes__);
    if (func != ((void *)0)) {
        new = PyObject_CallFunctionObjArgs(func, ((void *)0));
        do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0);
        if (new == ((void *)0))
            return ((void *)0);
        if (!((((((PyObject*)(new))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
            PyErr_Format(PyExc_TypeError,
                         "__bytes__ returned non-bytes (type %.200s)",
                         (((PyObject*)(new))->ob_type)->tp_name);
            do { if ( --((PyObject*)(new))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(new)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(new)))); } while (0);
            return ((void *)0);
        }
        return new;
    }
    else if (PyErr_Occurred())
        return ((void *)0);


    size = PyNumber_AsSsize_t(x, PyExc_OverflowError);
    if (size == -1 && PyErr_Occurred()) {
        if (PyErr_ExceptionMatches(PyExc_OverflowError))
            return ((void *)0);
        PyErr_Clear();
    }
    else if (size < 0) {
        PyErr_SetString(PyExc_ValueError, "negative count");
        return ((void *)0);
    }
    else {
        new = PyBytes_FromStringAndSize(((void *)0), size);
        if (new == ((void *)0))
            return ((void *)0);
        if (size > 0)
            ((__builtin_object_size (((PyBytesObject*)new)->ob_sval, 0) != (size_t) -1) ? __builtin___memset_chk (((PyBytesObject*)new)->ob_sval, 0, size, __builtin_object_size (((PyBytesObject*)new)->ob_sval, 0)) : __inline_memset_chk (((PyBytesObject*)new)->ob_sval, 0, size));
        return new;
    }


    if (encoding != ((void *)0) || errors != ((void *)0)) {
        PyErr_SetString(PyExc_TypeError,
            "encoding or errors without a string argument");
        return ((void *)0);
    }

    return PyBytes_FromObject(x);
}

PyObject *
PyBytes_FromObject(PyObject *x)
{
    PyObject *new, *it;
    Py_ssize_t i, size;

    if (x == ((void *)0)) {
        _PyErr_BadInternalCall("bytesobject.c", 2605);
        return ((void *)0);
    }

    if (((((PyObject*)(x))->ob_type) == &PyBytes_Type)) {
        ( ((PyObject*)(x))->ob_refcnt++);
        return x;
    }


    if ((((x)->ob_type->tp_as_buffer != ((void *)0)) && ((x)->ob_type->tp_as_buffer->bf_getbuffer != ((void *)0)))) {
        Py_buffer view;
        if (PyObject_GetBuffer(x, &view, ((0x0100 | (0x0010 | 0x0008)) | 0x0004)) < 0)
            return ((void *)0);
        new = PyBytes_FromStringAndSize(((void *)0), view.len);
        if (!new)
            goto fail;
        if (PyBuffer_ToContiguous(((PyBytesObject *)new)->ob_sval,
                                  &view, view.len, 'C') < 0)
            goto fail;
        PyBuffer_Release(&view);
        return new;
      fail:
        do { if ((new) == ((void *)0)) ; else do { if ( --((PyObject*)(new))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(new)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(new)))); } while (0); } while (0);
        PyBuffer_Release(&view);
        return ((void *)0);
    }
    if (((((((PyObject*)(x))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        PyErr_SetString(PyExc_TypeError,
                        "cannot convert unicode object to bytes");
        return ((void *)0);
    }

    if (((((PyObject*)(x))->ob_type) == &PyList_Type)) {
        new = PyBytes_FromStringAndSize(((void *)0), (((PyVarObject*)(x))->ob_size));
        if (new == ((void *)0))
            return ((void *)0);
        for (i = 0; i < (((PyVarObject*)(x))->ob_size); i++) {
            Py_ssize_t value = PyNumber_AsSsize_t(
                (((PyListObject *)(x))->ob_item[i]), PyExc_ValueError);
            if (value == -1 && PyErr_Occurred()) {
                do { if ( --((PyObject*)(new))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(new)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(new)))); } while (0);
                return ((void *)0);
            }
            if (value < 0 || value >= 256) {
                PyErr_SetString(PyExc_ValueError,
                                "bytes must be in range(0, 256)");
                do { if ( --((PyObject*)(new))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(new)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(new)))); } while (0);
                return ((void *)0);
            }
            ((PyBytesObject *)new)->ob_sval[i] = (char) value;
        }
        return new;
    }
    if (((((PyObject*)(x))->ob_type) == &PyTuple_Type)) {
        new = PyBytes_FromStringAndSize(((void *)0), (((PyVarObject*)(x))->ob_size));
        if (new == ((void *)0))
            return ((void *)0);
        for (i = 0; i < (((PyVarObject*)(x))->ob_size); i++) {
            Py_ssize_t value = PyNumber_AsSsize_t(
                (((PyTupleObject *)(x))->ob_item[i]), PyExc_ValueError);
            if (value == -1 && PyErr_Occurred()) {
                do { if ( --((PyObject*)(new))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(new)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(new)))); } while (0);
                return ((void *)0);
            }
            if (value < 0 || value >= 256) {
                PyErr_SetString(PyExc_ValueError,
                                "bytes must be in range(0, 256)");
                do { if ( --((PyObject*)(new))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(new)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(new)))); } while (0);
                return ((void *)0);
            }
            ((PyBytesObject *)new)->ob_sval[i] = (char) value;
        }
        return new;
    }


    size = _PyObject_LengthHint(x, 64);
    if (size == -1 && PyErr_Occurred())
        return ((void *)0);




    size += 1;
    new = PyBytes_FromStringAndSize(((void *)0), size);
    if (new == ((void *)0))
        return ((void *)0);


    it = PyObject_GetIter(x);
    if (it == ((void *)0))
        goto error;


    for (i = 0; ; i++) {
        PyObject *item;
        Py_ssize_t value;


        item = PyIter_Next(it);
        if (item == ((void *)0)) {
            if (PyErr_Occurred())
                goto error;
            break;
        }


        value = PyNumber_AsSsize_t(item, PyExc_ValueError);
        do { if ( --((PyObject*)(item))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(item)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(item)))); } while (0);
        if (value == -1 && PyErr_Occurred())
            goto error;


        if (value < 0 || value >= 256) {
            PyErr_SetString(PyExc_ValueError,
                            "bytes must be in range(0, 256)");
            goto error;
        }


        if (i >= size) {
            size = 2 * size + 1;
            if (_PyBytes_Resize(&new, size) < 0)
                goto error;
        }
        ((PyBytesObject *)new)->ob_sval[i] = (char) value;
    }
    _PyBytes_Resize(&new, i);


    do { if ( --((PyObject*)(it))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(it)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(it)))); } while (0);
    return new;

  error:

    do { if ((it) == ((void *)0)) ; else do { if ( --((PyObject*)(it))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(it)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(it)))); } while (0); } while (0);
    do { if ( --((PyObject*)(new))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(new)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(new)))); } while (0);
    return ((void *)0);
}

static PyObject *
str_subtype_new(PyTypeObject *type, PyObject *args, PyObject *kwds)
{
    PyObject *tmp, *pnew;
    Py_ssize_t n;

    (__builtin_expect(!(PyType_IsSubtype(type, &PyBytes_Type)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2752, "PyType_IsSubtype(type, &PyBytes_Type)") : (void)0);
    tmp = bytes_new(&PyBytes_Type, args, kwds);
    if (tmp == ((void *)0))
        return ((void *)0);
    (__builtin_expect(!(((((PyObject*)(tmp))->ob_type) == &PyBytes_Type)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2756, "PyBytes_CheckExact(tmp)") : (void)0);
    n = ((__builtin_expect(!(((((((PyObject*)(tmp))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2757, "PyBytes_Check(tmp)") : (void)0),(((PyVarObject*)(tmp))->ob_size));
    pnew = type->tp_alloc(type, n);
    if (pnew != ((void *)0)) {
        ((__builtin_object_size (((__builtin_expect(!(((((((PyObject*)(pnew))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2761, "PyBytes_Check(pnew)") : (void)0), (((PyBytesObject *)(pnew))->ob_sval)), 0) != (size_t) -1) ? __builtin___memcpy_chk (((__builtin_expect(!(((((((PyObject*)(pnew))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2761, "PyBytes_Check(pnew)") : (void)0), (((PyBytesObject *)(pnew))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(tmp))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2761, "PyBytes_Check(tmp)") : (void)0), (((PyBytesObject *)(tmp))->ob_sval)), n+1, __builtin_object_size (((__builtin_expect(!(((((((PyObject*)(pnew))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2761, "PyBytes_Check(pnew)") : (void)0), (((PyBytesObject *)(pnew))->ob_sval)), 0)) : __inline_memcpy_chk (((__builtin_expect(!(((((((PyObject*)(pnew))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2761, "PyBytes_Check(pnew)") : (void)0), (((PyBytesObject *)(pnew))->ob_sval)), ((__builtin_expect(!(((((((PyObject*)(tmp))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2761, "PyBytes_Check(tmp)") : (void)0), (((PyBytesObject *)(tmp))->ob_sval)), n+1));

        ((PyBytesObject *)pnew)->ob_shash =
            ((PyBytesObject *)tmp)->ob_shash;
    }
    do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0);
    return pnew;
}

static char bytes_doc[] = "bytes(iterable_of_ints) -> bytes\nbytes(string, encoding[, errors]) -> bytes\nbytes(bytes_or_buffer) -> immutable copy of bytes_or_buffer\nbytes(int) -> bytes object of size given by the parameter initialized with null bytes\nbytes() -> empty bytes object\n\nConstruct an immutable array of bytes from:\n  - an iterable yielding integers in range(256)\n  - a text string encoded using the specified encoding\n  - any object implementing the buffer API.\n  - an integer";
# 2782 "bytesobject.c"
static PyObject *bytes_iter(PyObject *seq);

PyTypeObject PyBytes_Type = {
    { { 1, &PyType_Type }, 0 },
    "bytes",
    (__builtin_offsetof (PyBytesObject, ob_sval) + 1),
    sizeof(char),
    bytes_dealloc,
    0,
    0,
    0,
    0,
    (reprfunc)bytes_repr,
    0,
    &bytes_as_sequence,
    &bytes_as_mapping,
    (hashfunc)bytes_hash,
    0,
    bytes_str,
    PyObject_GenericGetAttr,
    0,
    &bytes_as_buffer,
    ( 0 | (1L<<18) | 0) | (1L<<10) |
        (1L<<27),
    bytes_doc,
    0,
    0,
    (richcmpfunc)bytes_richcompare,
    0,
    bytes_iter,
    0,
    bytes_methods,
    0,
    0,
    &PyBaseObject_Type,
    0,
    0,
    0,
    0,
    0,
    0,
    bytes_new,
    PyObject_Free,
};

void
PyBytes_Concat(register PyObject **pv, register PyObject *w)
{
    register PyObject *v;
    (__builtin_expect(!(pv != ((void *)0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2831, "pv != NULL") : (void)0);
    if (*pv == ((void *)0))
        return;
    if (w == ((void *)0)) {
        do { if (*pv) { PyObject *_py_tmp = (PyObject *)(*pv); (*pv) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
        return;
    }
    v = bytes_concat(*pv, w);
    do { if ( --((PyObject*)(*pv))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(*pv)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(*pv)))); } while (0);
    *pv = v;
}

void
PyBytes_ConcatAndDel(register PyObject **pv, register PyObject *w)
{
    PyBytes_Concat(pv, w);
    do { if ((w) == ((void *)0)) ; else do { if ( --((PyObject*)(w))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(w)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(w)))); } while (0); } while (0);
}
# 2865 "bytesobject.c"
int
_PyBytes_Resize(PyObject **pv, Py_ssize_t newsize)
{
    register PyObject *v;
    register PyBytesObject *sv;
    v = *pv;
    if (!((((((PyObject*)(v))->ob_type))->tp_flags & ((1L<<27))) != 0) || (((PyObject*)(v))->ob_refcnt) != 1 || newsize < 0) {
        *pv = 0;
        do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
        _PyErr_BadInternalCall("bytesobject.c", 2874);
        return -1;
    }

    ;
    ;
    *pv = (PyObject *)
        PyObject_Realloc((char *)v, (__builtin_offsetof (PyBytesObject, ob_sval) + 1) + newsize);
    if (*pv == ((void *)0)) {
        PyObject_Free(v);
        PyErr_NoMemory();
        return -1;
    }
    ( (((PyObject*)(*pv))->ob_refcnt) = 1);
    sv = (PyBytesObject *) *pv;
    (((PyVarObject*)(sv))->ob_size) = newsize;
    sv->ob_sval[newsize] = '\0';
    sv->ob_shash = -1;
    return 0;
}

void
PyBytes_Fini(void)
{
    int i;
    for (i = 0; i < (127 * 2 + 1) + 1; i++)
        do { if (characters[i]) { PyObject *_py_tmp = (PyObject *)(characters[i]); (characters[i]) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (nullstring) { PyObject *_py_tmp = (PyObject *)(nullstring); (nullstring) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
}



typedef struct {
    PyObject ob_base;
    Py_ssize_t it_index;
    PyBytesObject *it_seq;
} striterobject;

static void
striter_dealloc(striterobject *it)
{
    do { PyGC_Head *g = ((PyGC_Head *)(it)-1); (__builtin_expect(!(g->gc.gc_refs != (-2)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2915, "g->gc.gc_refs != _PyGC_REFS_UNTRACKED") : (void)0); g->gc.gc_refs = (-2); g->gc.gc_prev->gc.gc_next = g->gc.gc_next; g->gc.gc_next->gc.gc_prev = g->gc.gc_prev; g->gc.gc_next = ((void *)0); } while (0);;
    do { if ((it->it_seq) == ((void *)0)) ; else do { if ( --((PyObject*)(it->it_seq))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(it->it_seq)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(it->it_seq)))); } while (0); } while (0);
    PyObject_GC_Del(it);
}

static int
striter_traverse(striterobject *it, visitproc visit, void *arg)
{
    do { if (it->it_seq) { int vret = visit((PyObject *)(it->it_seq), arg); if (vret) return vret; } } while (0);
    return 0;
}

static PyObject *
striter_next(striterobject *it)
{
    PyBytesObject *seq;
    PyObject *item;

    (__builtin_expect(!(it != ((void *)0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2933, "it != NULL") : (void)0);
    seq = it->it_seq;
    if (seq == ((void *)0))
        return ((void *)0);
    (__builtin_expect(!(((((((PyObject*)(seq))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2937, "PyBytes_Check(seq)") : (void)0);

    if (it->it_index < ((__builtin_expect(!(((((((PyObject*)(seq))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2939, "PyBytes_Check(seq)") : (void)0),(((PyVarObject*)(seq))->ob_size))) {
        item = PyLong_FromLong(
            (unsigned char)seq->ob_sval[it->it_index]);
        if (item != ((void *)0))
            ++it->it_index;
        return item;
    }

    do { if ( --((PyObject*)(seq))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(seq)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(seq)))); } while (0);
    it->it_seq = ((void *)0);
    return ((void *)0);
}

static PyObject *
striter_len(striterobject *it)
{
    Py_ssize_t len = 0;
    if (it->it_seq)
        len = ((__builtin_expect(!(((((((PyObject*)(it->it_seq))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "bytesobject.c", 2957, "PyBytes_Check(it->it_seq)") : (void)0),(((PyVarObject*)(it->it_seq))->ob_size)) - it->it_index;
    return PyLong_FromSsize_t(len);
}

static char length_hint_doc[] = "Private method returning an estimate of len(list(it)).";


static PyObject *
striter_reduce(striterobject *it)
{
    if (it->it_seq != ((void *)0)) {
        return _Py_BuildValue_SizeT("N(O)n", _PyObject_GetBuiltin("iter"),
                             it->it_seq, it->it_index);
    } else {
        PyObject *u = PyUnicode_FromUnicode(((void *)0), 0);
        if (u == ((void *)0))
            return ((void *)0);
        return _Py_BuildValue_SizeT("N(N)", _PyObject_GetBuiltin("iter"), u);
    }
}

static char reduce_doc[] = "Return state information for pickling.";

static PyObject *
striter_setstate(striterobject *it, PyObject *state)
{
    Py_ssize_t index = PyLong_AsSsize_t(state);
    if (index == -1 && PyErr_Occurred())
        return ((void *)0);
    if (index < 0)
        index = 0;
    it->it_index = index;
    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}

static char setstate_doc[] = "Set state information for unpickling.";

static PyMethodDef striter_methods[] = {
    {"__length_hint__", (PyCFunction)striter_len, 0x0004,
     length_hint_doc},
    {"__reduce__", (PyCFunction)striter_reduce, 0x0004,
     reduce_doc},
    {"__setstate__", (PyCFunction)striter_setstate, 0x0008,
     setstate_doc},
    {((void *)0), ((void *)0)}
};

PyTypeObject PyBytesIter_Type = {
    { { 1, &PyType_Type }, 0 },
    "bytes_iterator",
    sizeof(striterobject),
    0,

    (destructor)striter_dealloc,
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
    ( 0 | (1L<<18) | 0) | (1L<<14),
    0,
    (traverseproc)striter_traverse,
    0,
    0,
    0,
    PyObject_SelfIter,
    (iternextfunc)striter_next,
    striter_methods,
    0,
};

static PyObject *
bytes_iter(PyObject *seq)
{
    striterobject *it;

    if (!((((((PyObject*)(seq))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
        _PyErr_BadInternalCall("bytesobject.c", 3043);
        return ((void *)0);
    }
    it = ( (striterobject *) _PyObject_GC_New(&PyBytesIter_Type) );
    if (it == ((void *)0))
        return ((void *)0);
    it->it_index = 0;
    ( ((PyObject*)(seq))->ob_refcnt++);
    it->it_seq = (PyBytesObject *)seq;
    do { PyGC_Head *g = ((PyGC_Head *)(it)-1); if (g->gc.gc_refs != (-2)) Py_FatalError("GC object already tracked"); g->gc.gc_refs = (-3); g->gc.gc_next = _PyGC_generation0; g->gc.gc_prev = _PyGC_generation0->gc.gc_prev; g->gc.gc_prev->gc.gc_next = g; _PyGC_generation0->gc.gc_prev = g; } while (0);;
    return (PyObject *)it;
}
