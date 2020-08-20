# 1 "_scproxy.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "_scproxy.c"




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
# 6 "_scproxy.c" 2
# 1 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SystemConfiguration.h" 1 3
# 29 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SystemConfiguration.h" 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 1 3
# 11 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 3
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
# 12 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3

# 1 "/usr/include/assert.h" 1 3 4
# 75 "/usr/include/assert.h" 3 4

void __assert_rtn(const char *, const char *, int, const char *) __attribute__((__noreturn__));




# 14 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3

# 1 "/usr/include/errno.h" 1 3 4
# 16 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/float.h" 1 3 4
# 17 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/limits.h" 1 3 4






# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/syslimits.h" 1 3 4
# 8 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/limits.h" 2 3 4
# 18 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/usr/include/locale.h" 1 3 4
# 40 "/usr/include/locale.h" 3 4
# 1 "/usr/include/_locale.h" 1 3 4
# 43 "/usr/include/_locale.h" 3 4
struct lconv {
 char *decimal_point;
 char *thousands_sep;
 char *grouping;
 char *int_curr_symbol;
 char *currency_symbol;
 char *mon_decimal_point;
 char *mon_thousands_sep;
 char *mon_grouping;
 char *positive_sign;
 char *negative_sign;
 char int_frac_digits;
 char frac_digits;
 char p_cs_precedes;
 char p_sep_by_space;
 char n_cs_precedes;
 char n_sep_by_space;
 char p_sign_posn;
 char n_sign_posn;
 char int_p_cs_precedes;
 char int_n_cs_precedes;
 char int_p_sep_by_space;
 char int_n_sep_by_space;
 char int_p_sign_posn;
 char int_n_sign_posn;
};






struct lconv *localeconv(void);

# 41 "/usr/include/locale.h" 2 3 4
# 52 "/usr/include/locale.h" 3 4

char *setlocale(int, const char *);

# 19 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3

# 1 "/usr/include/setjmp.h" 1 3 4
# 26 "/usr/include/setjmp.h" 3 4
# 1 "/usr/include/machine/setjmp.h" 1 3 4
# 35 "/usr/include/machine/setjmp.h" 3 4
# 1 "/usr/include/i386/setjmp.h" 1 3 4
# 47 "/usr/include/i386/setjmp.h" 3 4
typedef int jmp_buf[((9 * 2) + 3 + 16)];
typedef int sigjmp_buf[((9 * 2) + 3 + 16) + 1];
# 65 "/usr/include/i386/setjmp.h" 3 4

int setjmp(jmp_buf);
void longjmp(jmp_buf, int);


int _setjmp(jmp_buf);
void _longjmp(jmp_buf, int);
int sigsetjmp(sigjmp_buf, int);
void siglongjmp(sigjmp_buf, int);



void longjmperror(void);


# 36 "/usr/include/machine/setjmp.h" 2 3 4
# 27 "/usr/include/setjmp.h" 2 3 4
# 21 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/usr/include/signal.h" 1 3 4
# 71 "/usr/include/signal.h" 3 4
extern const char *const sys_signame[32];
extern const char *const sys_siglist[32];



int raise(int);




void (*bsd_signal(int, void (*)(int)))(int);
int kill(pid_t, int) __asm("_" "kill" );
int killpg(pid_t, int) __asm("_" "killpg" );
int pthread_kill(pthread_t, int);
int pthread_sigmask(int, const sigset_t *, sigset_t *) __asm("_" "pthread_sigmask" );
int sigaction(int, const struct sigaction * ,
     struct sigaction * );
int sigaddset(sigset_t *, int);
int sigaltstack(const stack_t * , stack_t * ) __asm("_" "sigaltstack" );
int sigdelset(sigset_t *, int);
int sigemptyset(sigset_t *);
int sigfillset(sigset_t *);
int sighold(int);
int sigignore(int);
int siginterrupt(int, int);
int sigismember(const sigset_t *, int);
int sigpause(int) __asm("_" "sigpause" );
int sigpending(sigset_t *);
int sigprocmask(int, const sigset_t * , sigset_t * );
int sigrelse(int);
void (*sigset(int, void (*)(int)))(int);
int sigsuspend(const sigset_t *) __asm("_" "sigsuspend" );
int sigwait(const sigset_t * , int * ) __asm("_" "sigwait" );

void psignal(unsigned int, const char *);
int sigblock(int);
int sigsetmask(int);
int sigvec(int, struct sigvec *, struct sigvec *);






static __inline int
__sigbits(int __signo)
{
    return __signo > 32 ? 0 : (1 << (__signo - 1));
}
# 22 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stddef.h" 1 3 4
# 152 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stddef.h" 3 4
typedef long int ptrdiff_t;
# 23 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 38 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBase.h" 1 3







# 1 "/usr/include/TargetConditionals.h" 1 3 4
# 9 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBase.h" 2 3
# 41 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBase.h" 3
# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stdbool.h" 1 3 4
# 42 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBase.h" 2 3



# 1 "/usr/include/Block.h" 1 3 4
# 31 "/usr/include/Block.h" 3 4
extern void *_Block_copy(const void *aBlock)
    __attribute__((visibility("default")));


extern void _Block_release(const void *aBlock)
    __attribute__((visibility("default")));



extern void _Block_object_assign(void *, const void *, const int)
    __attribute__((visibility("default")));


extern void _Block_object_dispose(const void *, const int)
    __attribute__((visibility("default")));


extern void * _NSConcreteGlobalBlock[32]
    __attribute__((visibility("default")));
extern void * _NSConcreteStackBlock[32]
    __attribute__((visibility("default")));
# 46 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBase.h" 2 3
# 108 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBase.h" 3
# 1 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 1 3
# 20 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
# 1 "/System/Library/Frameworks/CoreServices.framework/Frameworks/CarbonCore.framework/Headers/ConditionalMacros.h" 1 3
# 21 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 2 3
# 37 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
#pragma pack(push, 2)
# 85 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
typedef unsigned char UInt8;
typedef signed char SInt8;
typedef unsigned short UInt16;
typedef signed short SInt16;


typedef unsigned int UInt32;
typedef signed int SInt32;
# 112 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
struct wide {
  UInt32 lo;
  SInt32 hi;
};
typedef struct wide wide;
struct UnsignedWide {
  UInt32 lo;
  UInt32 hi;
};
typedef struct UnsignedWide UnsignedWide;
# 143 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
      typedef signed long long SInt64;
        typedef unsigned long long UInt64;
# 163 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
typedef SInt32 Fixed;
typedef Fixed * FixedPtr;
typedef SInt32 Fract;
typedef Fract * FractPtr;
typedef UInt32 UnsignedFixed;
typedef UnsignedFixed * UnsignedFixedPtr;
typedef short ShortFixed;
typedef ShortFixed * ShortFixedPtr;
# 190 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
typedef float Float32;
typedef double Float64;
struct Float80 {
    SInt16 exp;
    UInt16 man[4];
};
typedef struct Float80 Float80;

struct Float96 {
    SInt16 exp[2];
    UInt16 man[4];
};
typedef struct Float96 Float96;
struct Float32Point {
    Float32 x;
    Float32 y;
};
typedef struct Float32Point Float32Point;
# 218 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
typedef char * Ptr;
typedef Ptr * Handle;
typedef long Size;
# 248 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
typedef SInt16 OSErr;
typedef SInt32 OSStatus;
typedef void * LogicalAddress;
typedef const void * ConstLogicalAddress;
typedef void * PhysicalAddress;
typedef UInt8 * BytePtr;
typedef unsigned long ByteCount;
typedef unsigned long ByteOffset;
typedef SInt32 Duration;
typedef UnsignedWide AbsoluteTime;
typedef UInt32 OptionBits;
typedef unsigned long ItemCount;
typedef UInt32 PBVersion;
typedef SInt16 ScriptCode;
typedef SInt16 LangCode;
typedef SInt16 RegionCode;
typedef UInt32 FourCharCode;
typedef FourCharCode OSType;
typedef FourCharCode ResType;
typedef OSType * OSTypePtr;
typedef ResType * ResTypePtr;
# 279 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
typedef unsigned char Boolean;
# 292 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
typedef long ( * ProcPtr)();
typedef void ( * Register68kProcPtr)();




typedef ProcPtr UniversalProcPtr;


typedef ProcPtr * ProcHandle;
typedef UniversalProcPtr * UniversalProcHandle;
# 317 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
typedef void * PRefCon;

typedef void * URefCon;
typedef void * SRefCon;
# 347 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
enum {
  noErr = 0
};

enum {
  kNilOptions = 0
};


enum {
  kVariableLengthArray = 1
};

enum {
  kUnknownType = 0x3F3F3F3F
};
# 416 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
typedef UInt32 UnicodeScalarValue;
typedef UInt32 UTF32Char;
typedef UInt16 UniChar;
typedef UInt16 UTF16Char;
typedef UInt8 UTF8Char;
typedef UniChar * UniCharPtr;
typedef unsigned long UniCharCount;
typedef UniCharCount * UniCharCountPtr;
typedef unsigned char Str255[256];
typedef unsigned char Str63[64];
typedef unsigned char Str32[33];
typedef unsigned char Str31[32];
typedef unsigned char Str27[28];
typedef unsigned char Str15[16];
# 438 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
typedef unsigned char Str32Field[34];
# 448 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
typedef Str63 StrFileName;
typedef unsigned char * StringPtr;
typedef StringPtr * StringHandle;
typedef const unsigned char * ConstStringPtr;
typedef const unsigned char * ConstStr255Param;
typedef const unsigned char * ConstStr63Param;
typedef const unsigned char * ConstStr32Param;
typedef const unsigned char * ConstStr31Param;
typedef const unsigned char * ConstStr27Param;
typedef const unsigned char * ConstStr15Param;
typedef ConstStr63Param ConstStrFileNameParam;
# 475 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
struct ProcessSerialNumber {
  UInt32 highLongOfPSN;
  UInt32 lowLongOfPSN;
};
typedef struct ProcessSerialNumber ProcessSerialNumber;
typedef ProcessSerialNumber * ProcessSerialNumberPtr;
# 497 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
struct Point {
  short v;
  short h;
};
typedef struct Point Point;
typedef Point * PointPtr;
struct Rect {
  short top;
  short left;
  short bottom;
  short right;
};
typedef struct Rect Rect;
typedef Rect * RectPtr;
struct FixedPoint {
  Fixed x;
  Fixed y;
};
typedef struct FixedPoint FixedPoint;
struct FixedRect {
  Fixed left;
  Fixed top;
  Fixed right;
  Fixed bottom;
};
typedef struct FixedRect FixedRect;

typedef short CharParameter;
enum {
  normal = 0,
  bold = 1,
  italic = 2,
  underline = 4,
  outline = 8,
  shadow = 0x10,
  condense = 0x20,
  extend = 0x40
};

typedef unsigned char Style;
typedef short StyleParameter;
typedef Style StyleField;
# 553 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
typedef SInt32 TimeValue;
typedef SInt32 TimeScale;
typedef wide CompTimeValue;
typedef SInt64 TimeValue64;
typedef struct TimeBaseRecord* TimeBase;
struct TimeRecord {
  CompTimeValue value;
  TimeScale scale;
  TimeBase base;
};
typedef struct TimeRecord TimeRecord;
# 605 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
struct NumVersion {

  UInt8 nonRelRev;
  UInt8 stage;
  UInt8 minorAndBugRev;
  UInt8 majorRev;
};
typedef struct NumVersion NumVersion;


enum {

  developStage = 0x20,
  alphaStage = 0x40,
  betaStage = 0x60,
  finalStage = 0x80
};

union NumVersionVariant {

  NumVersion parts;
  UInt32 whole;
};
typedef union NumVersionVariant NumVersionVariant;
typedef NumVersionVariant * NumVersionVariantPtr;
typedef NumVersionVariantPtr * NumVersionVariantHandle;
struct VersRec {

  NumVersion numericVersion;
  short countryCode;
  Str255 shortVersion;
  Str255 reserved;
};
typedef struct VersRec VersRec;
typedef VersRec * VersRecPtr;
typedef VersRecPtr * VersRecHndl;





typedef UInt8 Byte;
typedef SInt8 SignedByte;
typedef wide * WidePtr;
typedef UnsignedWide * UnsignedWidePtr;
typedef Float80 extended80;
typedef Float96 extended96;
typedef SInt8 VHSelect;
# 666 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
extern void
Debugger(void) ;
# 678 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
extern void
DebugStr(ConstStr255Param debuggerMsg) ;
# 725 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
extern void
SysBreak(void) ;
# 737 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
extern void
SysBreakStr(ConstStr255Param debuggerMsg) ;
# 749 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
extern void
SysBreakFunc(ConstStr255Param debuggerMsg) ;
# 760 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/MacTypes.h" 3
#pragma pack(pop)
# 109 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBase.h" 2 3
# 183 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBase.h" 3

# 240 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBase.h" 3
extern double kCFCoreFoundationVersionNumber;
# 314 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBase.h" 3
typedef unsigned long CFTypeID;
typedef unsigned long CFOptionFlags;
typedef unsigned long CFHashCode;
typedef signed long CFIndex;


typedef const void * CFTypeRef;

typedef const struct __CFString * CFStringRef;
typedef struct __CFString * CFMutableStringRef;






typedef CFTypeRef CFPropertyListRef;


enum {
    kCFCompareLessThan = -1,
    kCFCompareEqualTo = 0,
    kCFCompareGreaterThan = 1
};
typedef CFIndex CFComparisonResult;


typedef CFComparisonResult (*CFComparatorFunction)(const void *val1, const void *val2, void *context);



enum {
    kCFNotFound = -1
};



typedef struct {
    CFIndex location;
    CFIndex length;
} CFRange;


static __inline__ __attribute__((always_inline)) CFRange CFRangeMake(CFIndex loc, CFIndex len) {
    CFRange range;
    range.location = loc;
    range.length = len;
    return range;
}





extern
CFRange __CFRangeMake(CFIndex loc, CFIndex len);




typedef const struct __CFNull * CFNullRef;

extern
CFTypeID CFNullGetTypeID(void);

extern
const CFNullRef kCFNull;
# 392 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBase.h" 3
typedef const struct __CFAllocator * CFAllocatorRef;


extern
const CFAllocatorRef kCFAllocatorDefault;


extern
const CFAllocatorRef kCFAllocatorSystemDefault;







extern
const CFAllocatorRef kCFAllocatorMalloc;





extern
const CFAllocatorRef kCFAllocatorMallocZone;





extern
const CFAllocatorRef kCFAllocatorNull;





extern
const CFAllocatorRef kCFAllocatorUseContext;

typedef const void * (*CFAllocatorRetainCallBack)(const void *info);
typedef void (*CFAllocatorReleaseCallBack)(const void *info);
typedef CFStringRef (*CFAllocatorCopyDescriptionCallBack)(const void *info);
typedef void * (*CFAllocatorAllocateCallBack)(CFIndex allocSize, CFOptionFlags hint, void *info);
typedef void * (*CFAllocatorReallocateCallBack)(void *ptr, CFIndex newsize, CFOptionFlags hint, void *info);
typedef void (*CFAllocatorDeallocateCallBack)(void *ptr, void *info);
typedef CFIndex (*CFAllocatorPreferredSizeCallBack)(CFIndex size, CFOptionFlags hint, void *info);
typedef struct {
    CFIndex version;
    void * info;
    CFAllocatorRetainCallBack retain;
    CFAllocatorReleaseCallBack release;
    CFAllocatorCopyDescriptionCallBack copyDescription;
    CFAllocatorAllocateCallBack allocate;
    CFAllocatorReallocateCallBack reallocate;
    CFAllocatorDeallocateCallBack deallocate;
    CFAllocatorPreferredSizeCallBack preferredSize;
} CFAllocatorContext;

extern
CFTypeID CFAllocatorGetTypeID(void);
# 477 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBase.h" 3
extern
void CFAllocatorSetDefault(CFAllocatorRef allocator);

extern
CFAllocatorRef CFAllocatorGetDefault(void);

extern
CFAllocatorRef CFAllocatorCreate(CFAllocatorRef allocator, CFAllocatorContext *context);

extern
void *CFAllocatorAllocate(CFAllocatorRef allocator, CFIndex size, CFOptionFlags hint);

extern
void *CFAllocatorReallocate(CFAllocatorRef allocator, void *ptr, CFIndex newsize, CFOptionFlags hint);

extern
void CFAllocatorDeallocate(CFAllocatorRef allocator, void *ptr);

extern
CFIndex CFAllocatorGetPreferredSizeForSize(CFAllocatorRef allocator, CFIndex size, CFOptionFlags hint);

extern
void CFAllocatorGetContext(CFAllocatorRef allocator, CFAllocatorContext *context);




extern
CFTypeID CFGetTypeID(CFTypeRef cf);

extern
CFStringRef CFCopyTypeIDDescription(CFTypeID type_id);

extern
CFTypeRef CFRetain(CFTypeRef cf);

extern
void CFRelease(CFTypeRef cf);

extern
CFIndex CFGetRetainCount(CFTypeRef cf);


extern
CFTypeRef CFMakeCollectable(CFTypeRef cf) ;

extern
Boolean CFEqual(CFTypeRef cf1, CFTypeRef cf2);

extern
CFHashCode CFHash(CFTypeRef cf);

extern
CFStringRef CFCopyDescription(CFTypeRef cf);

extern
CFAllocatorRef CFGetAllocator(CFTypeRef cf);


# 39 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 1 3
# 49 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3

# 73 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
typedef const void * (*CFArrayRetainCallBack)(CFAllocatorRef allocator, const void *value);
typedef void (*CFArrayReleaseCallBack)(CFAllocatorRef allocator, const void *value);
typedef CFStringRef (*CFArrayCopyDescriptionCallBack)(const void *value);
typedef Boolean (*CFArrayEqualCallBack)(const void *value1, const void *value2);
typedef struct {
    CFIndex version;
    CFArrayRetainCallBack retain;
    CFArrayReleaseCallBack release;
    CFArrayCopyDescriptionCallBack copyDescription;
    CFArrayEqualCallBack equal;
} CFArrayCallBacks;






extern
const CFArrayCallBacks kCFTypeArrayCallBacks;
# 101 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
typedef void (*CFArrayApplierFunction)(const void *value, void *context);





typedef const struct __CFArray * CFArrayRef;





typedef struct __CFArray * CFMutableArrayRef;





extern
CFTypeID CFArrayGetTypeID(void);
# 172 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
CFArrayRef CFArrayCreate(CFAllocatorRef allocator, const void **values, CFIndex numValues, const CFArrayCallBacks *callBacks);
# 193 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
CFArrayRef CFArrayCreateCopy(CFAllocatorRef allocator, CFArrayRef theArray);
# 237 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
CFMutableArrayRef CFArrayCreateMutable(CFAllocatorRef allocator, CFIndex capacity, const CFArrayCallBacks *callBacks);
# 267 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
CFMutableArrayRef CFArrayCreateMutableCopy(CFAllocatorRef allocator, CFIndex capacity, CFArrayRef theArray);
# 277 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
CFIndex CFArrayGetCount(CFArrayRef theArray);
# 300 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
CFIndex CFArrayGetCountOfValue(CFArrayRef theArray, CFRange range, const void *value);
# 323 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
Boolean CFArrayContainsValue(CFArrayRef theArray, CFRange range, const void *value);
# 337 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
const void *CFArrayGetValueAtIndex(CFArrayRef theArray, CFIndex idx);
# 358 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
void CFArrayGetValues(CFArrayRef theArray, CFRange range, const void **values);
# 385 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
void CFArrayApplyFunction(CFArrayRef theArray, CFRange range, CFArrayApplierFunction applier, void *context);
# 410 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
CFIndex CFArrayGetFirstIndexOfValue(CFArrayRef theArray, CFRange range, const void *value);
# 435 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
CFIndex CFArrayGetLastIndexOfValue(CFArrayRef theArray, CFRange range, const void *value);
# 474 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
CFIndex CFArrayBSearchValues(CFArrayRef theArray, CFRange range, const void *value, CFComparatorFunction comparator, void *context);
# 490 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
void CFArrayAppendValue(CFMutableArrayRef theArray, const void *value);
# 511 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
void CFArrayInsertValueAtIndex(CFMutableArrayRef theArray, CFIndex idx, const void *value);
# 532 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
void CFArraySetValueAtIndex(CFMutableArrayRef theArray, CFIndex idx, const void *value);
# 546 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
void CFArrayRemoveValueAtIndex(CFMutableArrayRef theArray, CFIndex idx);
# 556 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
void CFArrayRemoveAllValues(CFMutableArrayRef theArray);
# 590 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
void CFArrayReplaceValues(CFMutableArrayRef theArray, CFRange range, const void **newValues, CFIndex newCount);
# 608 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
void CFArrayExchangeValuesAtIndices(CFMutableArrayRef theArray, CFIndex idx1, CFIndex idx2);
# 638 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
void CFArraySortValues(CFMutableArrayRef theArray, CFRange range, CFComparatorFunction comparator, void *context);
# 665 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFArray.h" 3
extern
void CFArrayAppendArray(CFMutableArrayRef theArray, CFArrayRef otherArray, CFRange otherRange);


# 40 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBag.h" 1 3
# 10 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBag.h" 3


typedef const void * (*CFBagRetainCallBack)(CFAllocatorRef allocator, const void *value);
typedef void (*CFBagReleaseCallBack)(CFAllocatorRef allocator, const void *value);
typedef CFStringRef (*CFBagCopyDescriptionCallBack)(const void *value);
typedef Boolean (*CFBagEqualCallBack)(const void *value1, const void *value2);
typedef CFHashCode (*CFBagHashCallBack)(const void *value);
typedef struct {
    CFIndex version;
    CFBagRetainCallBack retain;
    CFBagReleaseCallBack release;
    CFBagCopyDescriptionCallBack copyDescription;
    CFBagEqualCallBack equal;
    CFBagHashCallBack hash;
} CFBagCallBacks;

extern
const CFBagCallBacks kCFTypeBagCallBacks;
extern
const CFBagCallBacks kCFCopyStringBagCallBacks;

typedef void (*CFBagApplierFunction)(const void *value, void *context);

typedef const struct __CFBag * CFBagRef;
typedef struct __CFBag * CFMutableBagRef;

extern
CFTypeID CFBagGetTypeID(void);

extern
CFBagRef CFBagCreate(CFAllocatorRef allocator, const void **values, CFIndex numValues, const CFBagCallBacks *callBacks);

extern
CFBagRef CFBagCreateCopy(CFAllocatorRef allocator, CFBagRef theBag);

extern
CFMutableBagRef CFBagCreateMutable(CFAllocatorRef allocator, CFIndex capacity, const CFBagCallBacks *callBacks);

extern
CFMutableBagRef CFBagCreateMutableCopy(CFAllocatorRef allocator, CFIndex capacity, CFBagRef theBag);

extern
CFIndex CFBagGetCount(CFBagRef theBag);

extern
CFIndex CFBagGetCountOfValue(CFBagRef theBag, const void *value);

extern
Boolean CFBagContainsValue(CFBagRef theBag, const void *value);

extern
const void *CFBagGetValue(CFBagRef theBag, const void *value);

extern
Boolean CFBagGetValueIfPresent(CFBagRef theBag, const void *candidate, const void **value);

extern
void CFBagGetValues(CFBagRef theBag, const void **values);

extern
void CFBagApplyFunction(CFBagRef theBag, CFBagApplierFunction applier, void *context);

extern
void CFBagAddValue(CFMutableBagRef theBag, const void *value);

extern
void CFBagReplaceValue(CFMutableBagRef theBag, const void *value);

extern
void CFBagSetValue(CFMutableBagRef theBag, const void *value);

extern
void CFBagRemoveValue(CFMutableBagRef theBag, const void *value);

extern
void CFBagRemoveAllValues(CFMutableBagRef theBag);


# 41 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBinaryHeap.h" 1 3
# 16 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBinaryHeap.h" 3


typedef struct {
    CFIndex version;
    void * info;
    const void *(*retain)(const void *info);
    void (*release)(const void *info);
    CFStringRef (*copyDescription)(const void *info);
} CFBinaryHeapCompareContext;
# 49 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBinaryHeap.h" 3
typedef struct {
    CFIndex version;
    const void *(*retain)(CFAllocatorRef allocator, const void *ptr);
    void (*release)(CFAllocatorRef allocator, const void *ptr);
    CFStringRef (*copyDescription)(const void *ptr);
    CFComparisonResult (*compare)(const void *ptr1, const void *ptr2, void *context);
} CFBinaryHeapCallBacks;







extern const CFBinaryHeapCallBacks kCFStringBinaryHeapCallBacks;
# 73 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBinaryHeap.h" 3
typedef void (*CFBinaryHeapApplierFunction)(const void *val, void *context);





typedef struct __CFBinaryHeap * CFBinaryHeapRef;





extern CFTypeID CFBinaryHeapGetTypeID(void);
# 129 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBinaryHeap.h" 3
extern CFBinaryHeapRef CFBinaryHeapCreate(CFAllocatorRef allocator, CFIndex capacity, const CFBinaryHeapCallBacks *callBacks, const CFBinaryHeapCompareContext *compareContext);
# 158 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBinaryHeap.h" 3
extern CFBinaryHeapRef CFBinaryHeapCreateCopy(CFAllocatorRef allocator, CFIndex capacity, CFBinaryHeapRef heap);
# 167 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBinaryHeap.h" 3
extern CFIndex CFBinaryHeapGetCount(CFBinaryHeapRef heap);
# 182 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBinaryHeap.h" 3
extern CFIndex CFBinaryHeapGetCountOfValue(CFBinaryHeapRef heap, const void *value);
# 197 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBinaryHeap.h" 3
extern Boolean CFBinaryHeapContainsValue(CFBinaryHeapRef heap, const void *value);
# 208 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBinaryHeap.h" 3
extern const void * CFBinaryHeapGetMinimum(CFBinaryHeapRef heap);
# 222 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBinaryHeap.h" 3
extern Boolean CFBinaryHeapGetMinimumIfPresent(CFBinaryHeapRef heap, const void **value);
# 234 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBinaryHeap.h" 3
extern void CFBinaryHeapGetValues(CFBinaryHeapRef heap, const void **values);
# 253 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBinaryHeap.h" 3
extern void CFBinaryHeapApplyFunction(CFBinaryHeapRef heap, CFBinaryHeapApplierFunction applier, void *context);
# 265 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBinaryHeap.h" 3
extern void CFBinaryHeapAddValue(CFBinaryHeapRef heap, const void *value);







extern void CFBinaryHeapRemoveMinimumValue(CFBinaryHeapRef heap);
# 282 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBinaryHeap.h" 3
extern void CFBinaryHeapRemoveAllValues(CFBinaryHeapRef heap);


# 42 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBitVector.h" 1 3
# 10 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBitVector.h" 3


typedef UInt32 CFBit;

typedef const struct __CFBitVector * CFBitVectorRef;
typedef struct __CFBitVector * CFMutableBitVectorRef;

extern CFTypeID CFBitVectorGetTypeID(void);

extern CFBitVectorRef CFBitVectorCreate(CFAllocatorRef allocator, const UInt8 *bytes, CFIndex numBits);
extern CFBitVectorRef CFBitVectorCreateCopy(CFAllocatorRef allocator, CFBitVectorRef bv);
extern CFMutableBitVectorRef CFBitVectorCreateMutable(CFAllocatorRef allocator, CFIndex capacity);
extern CFMutableBitVectorRef CFBitVectorCreateMutableCopy(CFAllocatorRef allocator, CFIndex capacity, CFBitVectorRef bv);

extern CFIndex CFBitVectorGetCount(CFBitVectorRef bv);
extern CFIndex CFBitVectorGetCountOfBit(CFBitVectorRef bv, CFRange range, CFBit value);
extern Boolean CFBitVectorContainsBit(CFBitVectorRef bv, CFRange range, CFBit value);
extern CFBit CFBitVectorGetBitAtIndex(CFBitVectorRef bv, CFIndex idx);
extern void CFBitVectorGetBits(CFBitVectorRef bv, CFRange range, UInt8 *bytes);
extern CFIndex CFBitVectorGetFirstIndexOfBit(CFBitVectorRef bv, CFRange range, CFBit value);
extern CFIndex CFBitVectorGetLastIndexOfBit(CFBitVectorRef bv, CFRange range, CFBit value);

extern void CFBitVectorSetCount(CFMutableBitVectorRef bv, CFIndex count);
extern void CFBitVectorFlipBitAtIndex(CFMutableBitVectorRef bv, CFIndex idx);
extern void CFBitVectorFlipBits(CFMutableBitVectorRef bv, CFRange range);
extern void CFBitVectorSetBitAtIndex(CFMutableBitVectorRef bv, CFIndex idx, CFBit value);
extern void CFBitVectorSetBits(CFMutableBitVectorRef bv, CFRange range, CFBit value);
extern void CFBitVectorSetAllBits(CFMutableBitVectorRef bv, CFBit value);


# 43 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFByteOrder.h" 1 3
# 10 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFByteOrder.h" 3
# 1 "/usr/include/libkern/OSByteOrder.h" 1 3 4
# 43 "/usr/include/libkern/OSByteOrder.h" 3 4
# 1 "/usr/include/libkern/i386/OSByteOrder.h" 1 3 4
# 41 "/usr/include/libkern/i386/OSByteOrder.h" 3 4
static __inline__
uint16_t
OSReadSwapInt16(
    const volatile void * base,
    uintptr_t byteOffset
)
{
    uint16_t result;

    result = *(volatile uint16_t *)((uintptr_t)base + byteOffset);
    return _OSSwapInt16(result);
}

static __inline__
uint32_t
OSReadSwapInt32(
    const volatile void * base,
    uintptr_t byteOffset
)
{
    uint32_t result;

    result = *(volatile uint32_t *)((uintptr_t)base + byteOffset);
    return _OSSwapInt32(result);
}

static __inline__
uint64_t
OSReadSwapInt64(
    const volatile void * base,
    uintptr_t byteOffset
)
{
    uint64_t result;

    result = *(volatile uint64_t *)((uintptr_t)base + byteOffset);
    return _OSSwapInt64(result);
}



static __inline__
void
OSWriteSwapInt16(
    volatile void * base,
    uintptr_t byteOffset,
    uint16_t data
)
{
    *(volatile uint16_t *)((uintptr_t)base + byteOffset) = _OSSwapInt16(data);
}

static __inline__
void
OSWriteSwapInt32(
    volatile void * base,
    uintptr_t byteOffset,
    uint32_t data
)
{
    *(volatile uint32_t *)((uintptr_t)base + byteOffset) = _OSSwapInt32(data);
}

static __inline__
void
OSWriteSwapInt64(
    volatile void * base,
    uintptr_t byteOffset,
    uint64_t data
)
{
    *(volatile uint64_t *)((uintptr_t)base + byteOffset) = _OSSwapInt64(data);
}
# 44 "/usr/include/libkern/OSByteOrder.h" 2 3 4
# 60 "/usr/include/libkern/OSByteOrder.h" 3 4
enum {
    OSUnknownByteOrder,
    OSLittleEndian,
    OSBigEndian
};

static __inline__
int32_t
OSHostByteOrder(void) {

    return OSLittleEndian;





}
# 89 "/usr/include/libkern/OSByteOrder.h" 3 4
static __inline__
uint16_t
_OSReadInt16(
    const volatile void * base,
    uintptr_t byteOffset
)
{
    return *(volatile uint16_t *)((uintptr_t)base + byteOffset);
}

static __inline__
uint32_t
_OSReadInt32(
    const volatile void * base,
    uintptr_t byteOffset
)
{
    return *(volatile uint32_t *)((uintptr_t)base + byteOffset);
}

static __inline__
uint64_t
_OSReadInt64(
    const volatile void * base,
    uintptr_t byteOffset
)
{
    return *(volatile uint64_t *)((uintptr_t)base + byteOffset);
}



static __inline__
void
_OSWriteInt16(
    volatile void * base,
    uintptr_t byteOffset,
    uint16_t data
)
{
    *(volatile uint16_t *)((uintptr_t)base + byteOffset) = data;
}

static __inline__
void
_OSWriteInt32(
    volatile void * base,
    uintptr_t byteOffset,
    uint32_t data
)
{
    *(volatile uint32_t *)((uintptr_t)base + byteOffset) = data;
}

static __inline__
void
_OSWriteInt64(
    volatile void * base,
    uintptr_t byteOffset,
    uint64_t data
)
{
    *(volatile uint64_t *)((uintptr_t)base + byteOffset) = data;
}
# 11 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFByteOrder.h" 2 3





enum __CFByteOrder {
    CFByteOrderUnknown,
    CFByteOrderLittleEndian,
    CFByteOrderBigEndian
};
typedef CFIndex CFByteOrder;

static __inline__ __attribute__((always_inline)) CFByteOrder CFByteOrderGetCurrent(void) {

    int32_t byteOrder = OSHostByteOrder();
    switch (byteOrder) {
    case OSLittleEndian: return CFByteOrderLittleEndian;
    case OSBigEndian: return CFByteOrderBigEndian;
    default: break;
    }
    return CFByteOrderUnknown;
# 41 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFByteOrder.h" 3
}

static __inline__ __attribute__((always_inline)) uint16_t CFSwapInt16(uint16_t arg) {

    return ((__uint16_t)(__builtin_constant_p(arg) ? ((__uint16_t)((((__uint16_t)(arg) & 0xff00) >> 8) | (((__uint16_t)(arg) & 0x00ff) << 8))) : _OSSwapInt16(arg)));





}

static __inline__ __attribute__((always_inline)) uint32_t CFSwapInt32(uint32_t arg) {

    return (__builtin_constant_p(arg) ? ((__uint32_t)((((__uint32_t)(arg) & 0xff000000) >> 24) | (((__uint32_t)(arg) & 0x00ff0000) >> 8) | (((__uint32_t)(arg) & 0x0000ff00) << 8) | (((__uint32_t)(arg) & 0x000000ff) << 24))) : _OSSwapInt32(arg));





}

static __inline__ __attribute__((always_inline)) uint64_t CFSwapInt64(uint64_t arg) {

    return (__builtin_constant_p(arg) ? ((__uint64_t)((((__uint64_t)(arg) & 0xff00000000000000ULL) >> 56) | (((__uint64_t)(arg) & 0x00ff000000000000ULL) >> 40) | (((__uint64_t)(arg) & 0x0000ff0000000000ULL) >> 24) | (((__uint64_t)(arg) & 0x000000ff00000000ULL) >> 8) | (((__uint64_t)(arg) & 0x00000000ff000000ULL) << 8) | (((__uint64_t)(arg) & 0x0000000000ff0000ULL) << 24) | (((__uint64_t)(arg) & 0x000000000000ff00ULL) << 40) | (((__uint64_t)(arg) & 0x00000000000000ffULL) << 56))) : _OSSwapInt64(arg));
# 76 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFByteOrder.h" 3
}

static __inline__ __attribute__((always_inline)) uint16_t CFSwapInt16BigToHost(uint16_t arg) {

    return ((__uint16_t)(__builtin_constant_p(arg) ? ((__uint16_t)((((__uint16_t)(arg) & 0xff00) >> 8) | (((__uint16_t)(arg) & 0x00ff) << 8))) : _OSSwapInt16(arg)));





}

static __inline__ __attribute__((always_inline)) uint32_t CFSwapInt32BigToHost(uint32_t arg) {

    return (__builtin_constant_p(arg) ? ((__uint32_t)((((__uint32_t)(arg) & 0xff000000) >> 24) | (((__uint32_t)(arg) & 0x00ff0000) >> 8) | (((__uint32_t)(arg) & 0x0000ff00) << 8) | (((__uint32_t)(arg) & 0x000000ff) << 24))) : _OSSwapInt32(arg));





}

static __inline__ __attribute__((always_inline)) uint64_t CFSwapInt64BigToHost(uint64_t arg) {

    return (__builtin_constant_p(arg) ? ((__uint64_t)((((__uint64_t)(arg) & 0xff00000000000000ULL) >> 56) | (((__uint64_t)(arg) & 0x00ff000000000000ULL) >> 40) | (((__uint64_t)(arg) & 0x0000ff0000000000ULL) >> 24) | (((__uint64_t)(arg) & 0x000000ff00000000ULL) >> 8) | (((__uint64_t)(arg) & 0x00000000ff000000ULL) << 8) | (((__uint64_t)(arg) & 0x0000000000ff0000ULL) << 24) | (((__uint64_t)(arg) & 0x000000000000ff00ULL) << 40) | (((__uint64_t)(arg) & 0x00000000000000ffULL) << 56))) : _OSSwapInt64(arg));





}

static __inline__ __attribute__((always_inline)) uint16_t CFSwapInt16HostToBig(uint16_t arg) {

    return ((__uint16_t)(__builtin_constant_p(arg) ? ((__uint16_t)((((__uint16_t)(arg) & 0xff00) >> 8) | (((__uint16_t)(arg) & 0x00ff) << 8))) : _OSSwapInt16(arg)));





}

static __inline__ __attribute__((always_inline)) uint32_t CFSwapInt32HostToBig(uint32_t arg) {

    return (__builtin_constant_p(arg) ? ((__uint32_t)((((__uint32_t)(arg) & 0xff000000) >> 24) | (((__uint32_t)(arg) & 0x00ff0000) >> 8) | (((__uint32_t)(arg) & 0x0000ff00) << 8) | (((__uint32_t)(arg) & 0x000000ff) << 24))) : _OSSwapInt32(arg));





}

static __inline__ __attribute__((always_inline)) uint64_t CFSwapInt64HostToBig(uint64_t arg) {

    return (__builtin_constant_p(arg) ? ((__uint64_t)((((__uint64_t)(arg) & 0xff00000000000000ULL) >> 56) | (((__uint64_t)(arg) & 0x00ff000000000000ULL) >> 40) | (((__uint64_t)(arg) & 0x0000ff0000000000ULL) >> 24) | (((__uint64_t)(arg) & 0x000000ff00000000ULL) >> 8) | (((__uint64_t)(arg) & 0x00000000ff000000ULL) << 8) | (((__uint64_t)(arg) & 0x0000000000ff0000ULL) << 24) | (((__uint64_t)(arg) & 0x000000000000ff00ULL) << 40) | (((__uint64_t)(arg) & 0x00000000000000ffULL) << 56))) : _OSSwapInt64(arg));





}

static __inline__ __attribute__((always_inline)) uint16_t CFSwapInt16LittleToHost(uint16_t arg) {

    return ((uint16_t)(arg));





}

static __inline__ __attribute__((always_inline)) uint32_t CFSwapInt32LittleToHost(uint32_t arg) {

    return ((uint32_t)(arg));





}

static __inline__ __attribute__((always_inline)) uint64_t CFSwapInt64LittleToHost(uint64_t arg) {

    return ((uint64_t)(arg));





}

static __inline__ __attribute__((always_inline)) uint16_t CFSwapInt16HostToLittle(uint16_t arg) {

    return ((uint16_t)(arg));





}

static __inline__ __attribute__((always_inline)) uint32_t CFSwapInt32HostToLittle(uint32_t arg) {

    return ((uint32_t)(arg));





}

static __inline__ __attribute__((always_inline)) uint64_t CFSwapInt64HostToLittle(uint64_t arg) {

    return ((uint64_t)(arg));





}

typedef struct {uint32_t v;} CFSwappedFloat32;
typedef struct {uint64_t v;} CFSwappedFloat64;

static __inline__ __attribute__((always_inline)) CFSwappedFloat32 CFConvertFloat32HostToSwapped(Float32 arg) {
    union CFSwap {
 Float32 v;
 CFSwappedFloat32 sv;
    } result;
    result.v = arg;

    result.sv.v = CFSwapInt32(result.sv.v);

    return result.sv;
}

static __inline__ __attribute__((always_inline)) Float32 CFConvertFloat32SwappedToHost(CFSwappedFloat32 arg) {
    union CFSwap {
 Float32 v;
 CFSwappedFloat32 sv;
    } result;
    result.sv = arg;

    result.sv.v = CFSwapInt32(result.sv.v);

    return result.v;
}

static __inline__ __attribute__((always_inline)) CFSwappedFloat64 CFConvertFloat64HostToSwapped(Float64 arg) {
    union CFSwap {
 Float64 v;
 CFSwappedFloat64 sv;
    } result;
    result.v = arg;

    result.sv.v = CFSwapInt64(result.sv.v);

    return result.sv;
}

static __inline__ __attribute__((always_inline)) Float64 CFConvertFloat64SwappedToHost(CFSwappedFloat64 arg) {
    union CFSwap {
 Float64 v;
 CFSwappedFloat64 sv;
    } result;
    result.sv = arg;

    result.sv.v = CFSwapInt64(result.sv.v);

    return result.v;
}

static __inline__ __attribute__((always_inline)) CFSwappedFloat32 CFConvertFloatHostToSwapped(float arg) {
    union CFSwap {
 float v;
 CFSwappedFloat32 sv;
    } result;
    result.v = arg;

    result.sv.v = CFSwapInt32(result.sv.v);

    return result.sv;
}

static __inline__ __attribute__((always_inline)) float CFConvertFloatSwappedToHost(CFSwappedFloat32 arg) {
    union CFSwap {
 float v;
 CFSwappedFloat32 sv;
    } result;
    result.sv = arg;

    result.sv.v = CFSwapInt32(result.sv.v);

    return result.v;
}

static __inline__ __attribute__((always_inline)) CFSwappedFloat64 CFConvertDoubleHostToSwapped(double arg) {
    union CFSwap {
 double v;
 CFSwappedFloat64 sv;
    } result;
    result.v = arg;

    result.sv.v = CFSwapInt64(result.sv.v);

    return result.sv;
}

static __inline__ __attribute__((always_inline)) double CFConvertDoubleSwappedToHost(CFSwappedFloat64 arg) {
    union CFSwap {
 double v;
 CFSwappedFloat64 sv;
    } result;
    result.sv = arg;

    result.sv.v = CFSwapInt64(result.sv.v);

    return result.v;
}


# 44 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCalendar.h" 1 3
# 9 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCalendar.h" 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFLocale.h" 1 3
# 10 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFLocale.h" 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 1 3
# 64 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3

# 91 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
typedef const void * (*CFDictionaryRetainCallBack)(CFAllocatorRef allocator, const void *value);
typedef void (*CFDictionaryReleaseCallBack)(CFAllocatorRef allocator, const void *value);
typedef CFStringRef (*CFDictionaryCopyDescriptionCallBack)(const void *value);
typedef Boolean (*CFDictionaryEqualCallBack)(const void *value1, const void *value2);
typedef CFHashCode (*CFDictionaryHashCallBack)(const void *value);
typedef struct {
    CFIndex version;
    CFDictionaryRetainCallBack retain;
    CFDictionaryReleaseCallBack release;
    CFDictionaryCopyDescriptionCallBack copyDescription;
    CFDictionaryEqualCallBack equal;
    CFDictionaryHashCallBack hash;
} CFDictionaryKeyCallBacks;







extern
const CFDictionaryKeyCallBacks kCFTypeDictionaryKeyCallBacks;
# 122 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
extern
const CFDictionaryKeyCallBacks kCFCopyStringDictionaryKeyCallBacks;
# 148 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
typedef struct {
    CFIndex version;
    CFDictionaryRetainCallBack retain;
    CFDictionaryReleaseCallBack release;
    CFDictionaryCopyDescriptionCallBack copyDescription;
    CFDictionaryEqualCallBack equal;
} CFDictionaryValueCallBacks;







extern
const CFDictionaryValueCallBacks kCFTypeDictionaryValueCallBacks;
# 174 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
typedef void (*CFDictionaryApplierFunction)(const void *key, const void *value, void *context);





typedef const struct __CFDictionary * CFDictionaryRef;





typedef struct __CFDictionary * CFMutableDictionaryRef;





extern
CFTypeID CFDictionaryGetTypeID(void);
# 277 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
extern
CFDictionaryRef CFDictionaryCreate(CFAllocatorRef allocator, const void **keys, const void **values, CFIndex numValues, const CFDictionaryKeyCallBacks *keyCallBacks, const CFDictionaryValueCallBacks *valueCallBacks);
# 301 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
extern
CFDictionaryRef CFDictionaryCreateCopy(CFAllocatorRef allocator, CFDictionaryRef theDict);
# 373 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
extern
CFMutableDictionaryRef CFDictionaryCreateMutable(CFAllocatorRef allocator, CFIndex capacity, const CFDictionaryKeyCallBacks *keyCallBacks, const CFDictionaryValueCallBacks *valueCallBacks);
# 406 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
extern
CFMutableDictionaryRef CFDictionaryCreateMutableCopy(CFAllocatorRef allocator, CFIndex capacity, CFDictionaryRef theDict);
# 416 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
extern
CFIndex CFDictionaryGetCount(CFDictionaryRef theDict);
# 435 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
extern
CFIndex CFDictionaryGetCountOfKey(CFDictionaryRef theDict, const void *key);
# 451 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
extern
CFIndex CFDictionaryGetCountOfValue(CFDictionaryRef theDict, const void *value);
# 469 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
extern
Boolean CFDictionaryContainsKey(CFDictionaryRef theDict, const void *key);
# 485 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
extern
Boolean CFDictionaryContainsValue(CFDictionaryRef theDict, const void *value);
# 507 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
extern
const void *CFDictionaryGetValue(CFDictionaryRef theDict, const void *key);
# 532 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
extern
Boolean CFDictionaryGetValueIfPresent(CFDictionaryRef theDict, const void *key, const void **value);
# 555 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
extern
void CFDictionaryGetKeysAndValues(CFDictionaryRef theDict, const void **keys, const void **values);
# 575 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
extern
void CFDictionaryApplyFunction(CFDictionaryRef theDict, CFDictionaryApplierFunction applier, void *context);
# 595 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
extern
void CFDictionaryAddValue(CFMutableDictionaryRef theDict, const void *key, const void *value);
# 618 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
extern
void CFDictionarySetValue(CFMutableDictionaryRef theDict, const void *key, const void *value);
# 637 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
extern
void CFDictionaryReplaceValue(CFMutableDictionaryRef theDict, const void *key, const void *value);
# 651 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
extern
void CFDictionaryRemoveValue(CFMutableDictionaryRef theDict, const void *key);
# 661 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDictionary.h" 3
extern
void CFDictionaryRemoveAllValues(CFMutableDictionaryRef theDict);


# 11 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFLocale.h" 2 3



typedef const struct __CFLocale *CFLocaleRef;

extern
CFTypeID CFLocaleGetTypeID(void);

extern
CFLocaleRef CFLocaleGetSystem(void);


extern
CFLocaleRef CFLocaleCopyCurrent(void);
# 34 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFLocale.h" 3
extern
CFArrayRef CFLocaleCopyAvailableLocaleIdentifiers(void);



extern
CFArrayRef CFLocaleCopyISOLanguageCodes(void);




extern
CFArrayRef CFLocaleCopyISOCountryCodes(void);




extern
CFArrayRef CFLocaleCopyISOCurrencyCodes(void);




extern
CFArrayRef CFLocaleCopyCommonISOCurrencyCodes(void) ;



extern
CFArrayRef CFLocaleCopyPreferredLanguages(void) ;


extern
CFStringRef CFLocaleCreateCanonicalLanguageIdentifierFromString(CFAllocatorRef allocator, CFStringRef localeIdentifier);



extern
CFStringRef CFLocaleCreateCanonicalLocaleIdentifierFromString(CFAllocatorRef allocator, CFStringRef localeIdentifier);



extern
CFStringRef CFLocaleCreateCanonicalLocaleIdentifierFromScriptManagerCodes(CFAllocatorRef allocator, LangCode lcode, RegionCode rcode);


extern
CFStringRef CFLocaleCreateLocaleIdentifierFromWindowsLocaleCode(CFAllocatorRef allocator, uint32_t lcid) ;


extern
uint32_t CFLocaleGetWindowsLocaleCodeFromLocaleIdentifier(CFStringRef localeIdentifier) ;


enum {
    kCFLocaleLanguageDirectionUnknown = 0,
    kCFLocaleLanguageDirectionLeftToRight = 1,
    kCFLocaleLanguageDirectionRightToLeft = 2,
    kCFLocaleLanguageDirectionTopToBottom = 3,
    kCFLocaleLanguageDirectionBottomToTop = 4
};
typedef CFIndex CFLocaleLanguageDirection;

extern
CFLocaleLanguageDirection CFLocaleGetLanguageCharacterDirection(CFStringRef isoLangCode) ;

extern
CFLocaleLanguageDirection CFLocaleGetLanguageLineDirection(CFStringRef isoLangCode) ;

extern
CFDictionaryRef CFLocaleCreateComponentsFromLocaleIdentifier(CFAllocatorRef allocator, CFStringRef localeID);
# 113 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFLocale.h" 3
extern
CFStringRef CFLocaleCreateLocaleIdentifierFromComponents(CFAllocatorRef allocator, CFDictionaryRef dictionary);






extern
CFLocaleRef CFLocaleCreate(CFAllocatorRef allocator, CFStringRef localeIdentifier);


extern
CFLocaleRef CFLocaleCreateCopy(CFAllocatorRef allocator, CFLocaleRef locale);




extern
CFStringRef CFLocaleGetIdentifier(CFLocaleRef locale);



extern
CFTypeRef CFLocaleGetValue(CFLocaleRef locale, CFStringRef key);



extern
CFStringRef CFLocaleCopyDisplayNameForPropertyValue(CFLocaleRef displayLocale, CFStringRef key, CFStringRef value);





extern const CFStringRef kCFLocaleCurrentLocaleDidChangeNotification ;



extern const CFStringRef kCFLocaleIdentifier;
extern const CFStringRef kCFLocaleLanguageCode;
extern const CFStringRef kCFLocaleCountryCode;
extern const CFStringRef kCFLocaleScriptCode;
extern const CFStringRef kCFLocaleVariantCode;

extern const CFStringRef kCFLocaleExemplarCharacterSet;
extern const CFStringRef kCFLocaleCalendarIdentifier;
extern const CFStringRef kCFLocaleCalendar;
extern const CFStringRef kCFLocaleCollationIdentifier;
extern const CFStringRef kCFLocaleUsesMetricSystem;
extern const CFStringRef kCFLocaleMeasurementSystem;
extern const CFStringRef kCFLocaleDecimalSeparator;
extern const CFStringRef kCFLocaleGroupingSeparator;
extern const CFStringRef kCFLocaleCurrencySymbol;
extern const CFStringRef kCFLocaleCurrencyCode;
extern const CFStringRef kCFLocaleCollatorIdentifier ;
extern const CFStringRef kCFLocaleQuotationBeginDelimiterKey ;
extern const CFStringRef kCFLocaleQuotationEndDelimiterKey ;
extern const CFStringRef kCFLocaleAlternateQuotationBeginDelimiterKey ;
extern const CFStringRef kCFLocaleAlternateQuotationEndDelimiterKey ;


extern const CFStringRef kCFGregorianCalendar;
extern const CFStringRef kCFBuddhistCalendar;
extern const CFStringRef kCFChineseCalendar;
extern const CFStringRef kCFHebrewCalendar;
extern const CFStringRef kCFIslamicCalendar;
extern const CFStringRef kCFIslamicCivilCalendar;
extern const CFStringRef kCFJapaneseCalendar;
extern const CFStringRef kCFRepublicOfChinaCalendar ;
extern const CFStringRef kCFPersianCalendar ;
extern const CFStringRef kCFIndianCalendar ;
extern const CFStringRef kCFISO8601Calendar ;


# 10 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCalendar.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDate.h" 1 3
# 10 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDate.h" 3


typedef double CFTimeInterval;
typedef CFTimeInterval CFAbsoluteTime;



extern
CFAbsoluteTime CFAbsoluteTimeGetCurrent(void);

extern
const CFTimeInterval kCFAbsoluteTimeIntervalSince1970;
extern
const CFTimeInterval kCFAbsoluteTimeIntervalSince1904;

typedef const struct __CFDate * CFDateRef;

extern
CFTypeID CFDateGetTypeID(void);

extern
CFDateRef CFDateCreate(CFAllocatorRef allocator, CFAbsoluteTime at);

extern
CFAbsoluteTime CFDateGetAbsoluteTime(CFDateRef theDate);

extern
CFTimeInterval CFDateGetTimeIntervalSinceDate(CFDateRef theDate, CFDateRef otherDate);

extern
CFComparisonResult CFDateCompare(CFDateRef theDate, CFDateRef otherDate, void *context);

typedef const struct __CFTimeZone * CFTimeZoneRef;

typedef struct {
    SInt32 year;
    SInt8 month;
    SInt8 day;
    SInt8 hour;
    SInt8 minute;
    double second;
} CFGregorianDate;

typedef struct {
    SInt32 years;
    SInt32 months;
    SInt32 days;
    SInt32 hours;
    SInt32 minutes;
    double seconds;
} CFGregorianUnits;

enum {
    kCFGregorianUnitsYears = (1UL << 0),
    kCFGregorianUnitsMonths = (1UL << 1),
    kCFGregorianUnitsDays = (1UL << 2),
    kCFGregorianUnitsHours = (1UL << 3),
    kCFGregorianUnitsMinutes = (1UL << 4),
    kCFGregorianUnitsSeconds = (1UL << 5),
    kCFGregorianAllUnits = 0x00FFFFFF
};
typedef CFOptionFlags CFGregorianUnitFlags;

extern
Boolean CFGregorianDateIsValid(CFGregorianDate gdate, CFOptionFlags unitFlags);

extern
CFAbsoluteTime CFGregorianDateGetAbsoluteTime(CFGregorianDate gdate, CFTimeZoneRef tz);

extern
CFGregorianDate CFAbsoluteTimeGetGregorianDate(CFAbsoluteTime at, CFTimeZoneRef tz);

extern
CFAbsoluteTime CFAbsoluteTimeAddGregorianUnits(CFAbsoluteTime at, CFTimeZoneRef tz, CFGregorianUnits units);

extern
CFGregorianUnits CFAbsoluteTimeGetDifferenceAsGregorianUnits(CFAbsoluteTime at1, CFAbsoluteTime at2, CFTimeZoneRef tz, CFOptionFlags unitFlags);

extern
SInt32 CFAbsoluteTimeGetDayOfWeek(CFAbsoluteTime at, CFTimeZoneRef tz);

extern
SInt32 CFAbsoluteTimeGetDayOfYear(CFAbsoluteTime at, CFTimeZoneRef tz);

extern
SInt32 CFAbsoluteTimeGetWeekOfYear(CFAbsoluteTime at, CFTimeZoneRef tz);


# 11 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCalendar.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTimeZone.h" 1 3
# 10 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTimeZone.h" 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFData.h" 1 3
# 10 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFData.h" 3


typedef const struct __CFData * CFDataRef;
typedef struct __CFData * CFMutableDataRef;

extern
CFTypeID CFDataGetTypeID(void);

extern
CFDataRef CFDataCreate(CFAllocatorRef allocator, const UInt8 *bytes, CFIndex length);

extern
CFDataRef CFDataCreateWithBytesNoCopy(CFAllocatorRef allocator, const UInt8 *bytes, CFIndex length, CFAllocatorRef bytesDeallocator);


extern
CFDataRef CFDataCreateCopy(CFAllocatorRef allocator, CFDataRef theData);

extern
CFMutableDataRef CFDataCreateMutable(CFAllocatorRef allocator, CFIndex capacity);

extern
CFMutableDataRef CFDataCreateMutableCopy(CFAllocatorRef allocator, CFIndex capacity, CFDataRef theData);

extern
CFIndex CFDataGetLength(CFDataRef theData);

extern
const UInt8 *CFDataGetBytePtr(CFDataRef theData);

extern
UInt8 *CFDataGetMutableBytePtr(CFMutableDataRef theData);

extern
void CFDataGetBytes(CFDataRef theData, CFRange range, UInt8 *buffer);

extern
void CFDataSetLength(CFMutableDataRef theData, CFIndex length);

extern
void CFDataIncreaseLength(CFMutableDataRef theData, CFIndex extraLength);

extern
void CFDataAppendBytes(CFMutableDataRef theData, const UInt8 *bytes, CFIndex length);

extern
void CFDataReplaceBytes(CFMutableDataRef theData, CFRange range, const UInt8 *newBytes, CFIndex newLength);

extern
void CFDataDeleteBytes(CFMutableDataRef theData, CFRange range);


enum {
    kCFDataSearchBackwards = 1UL << 0,
    kCFDataSearchAnchored = 1UL << 1
};

typedef CFOptionFlags CFDataSearchFlags;

extern
CFRange CFDataFind(CFDataRef theData, CFDataRef dataToFind, CFRange searchRange, CFDataSearchFlags compareOptions) ;


# 11 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTimeZone.h" 2 3


# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 1 3
# 12 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 1 3
# 37 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3






typedef const struct __CFCharacterSet * CFCharacterSetRef;





typedef struct __CFCharacterSet * CFMutableCharacterSetRef;






enum {
    kCFCharacterSetControl = 1,
    kCFCharacterSetWhitespace,
    kCFCharacterSetWhitespaceAndNewline,
    kCFCharacterSetDecimalDigit,
    kCFCharacterSetLetter,
    kCFCharacterSetLowercaseLetter,
    kCFCharacterSetUppercaseLetter,
    kCFCharacterSetNonBase,
    kCFCharacterSetDecomposable,
    kCFCharacterSetAlphaNumeric,
    kCFCharacterSetPunctuation,
    kCFCharacterSetCapitalizedLetter = 13,
    kCFCharacterSetSymbol = 14,

    kCFCharacterSetNewline = 15,

    kCFCharacterSetIllegal = 12
};
typedef CFIndex CFCharacterSetPredefinedSet;





extern
CFTypeID CFCharacterSetGetTypeID(void);
# 94 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern
CFCharacterSetRef CFCharacterSetGetPredefined(CFCharacterSetPredefinedSet theSetIdentifier);
# 113 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern
CFCharacterSetRef CFCharacterSetCreateWithCharactersInRange(CFAllocatorRef alloc, CFRange theRange);
# 130 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern
CFCharacterSetRef CFCharacterSetCreateWithCharactersInString(CFAllocatorRef alloc, CFStringRef theString);
# 158 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern
CFCharacterSetRef CFCharacterSetCreateWithBitmapRepresentation(CFAllocatorRef alloc, CFDataRef theData);
# 174 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern CFCharacterSetRef CFCharacterSetCreateInvertedSet(CFAllocatorRef alloc, CFCharacterSetRef theSet);
# 184 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern Boolean CFCharacterSetIsSupersetOfSet(CFCharacterSetRef theSet, CFCharacterSetRef theOtherset);
# 195 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern Boolean CFCharacterSetHasMemberInPlane(CFCharacterSetRef theSet, CFIndex thePlane);
# 207 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern
CFMutableCharacterSetRef CFCharacterSetCreateMutable(CFAllocatorRef alloc);
# 223 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern
CFCharacterSetRef CFCharacterSetCreateCopy(CFAllocatorRef alloc, CFCharacterSetRef theSet);
# 239 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern
CFMutableCharacterSetRef CFCharacterSetCreateMutableCopy(CFAllocatorRef alloc, CFCharacterSetRef theSet);
# 253 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern
Boolean CFCharacterSetIsCharacterMember(CFCharacterSetRef theSet, UniChar theChar);
# 265 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern Boolean CFCharacterSetIsLongCharacterMember(CFCharacterSetRef theSet, UTF32Char theChar);
# 283 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern
CFDataRef CFCharacterSetCreateBitmapRepresentation(CFAllocatorRef alloc, CFCharacterSetRef theSet);
# 298 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern
void CFCharacterSetAddCharactersInRange(CFMutableCharacterSetRef theSet, CFRange theRange);
# 313 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern
void CFCharacterSetRemoveCharactersInRange(CFMutableCharacterSetRef theSet, CFRange theRange);
# 326 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern
void CFCharacterSetAddCharactersInString(CFMutableCharacterSetRef theSet, CFStringRef theString);
# 339 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern
void CFCharacterSetRemoveCharactersInString(CFMutableCharacterSetRef theSet, CFStringRef theString);
# 353 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern
void CFCharacterSetUnion(CFMutableCharacterSetRef theSet, CFCharacterSetRef theOtherSet);
# 367 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern
void CFCharacterSetIntersect(CFMutableCharacterSetRef theSet, CFCharacterSetRef theOtherSet);
# 377 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCharacterSet.h" 3
extern
void CFCharacterSetInvert(CFMutableCharacterSetRef theSet);


# 13 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 2 3




# 92 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 3
typedef UInt32 CFStringEncoding;





enum {
    kCFStringEncodingMacRoman = 0,
    kCFStringEncodingWindowsLatin1 = 0x0500,
    kCFStringEncodingISOLatin1 = 0x0201,
    kCFStringEncodingNextStepLatin = 0x0B01,
    kCFStringEncodingASCII = 0x0600,
    kCFStringEncodingUnicode = 0x0100,
    kCFStringEncodingUTF8 = 0x08000100,
    kCFStringEncodingNonLossyASCII = 0x0BFF,

    kCFStringEncodingUTF16 = 0x0100,
    kCFStringEncodingUTF16BE = 0x10000100,
    kCFStringEncodingUTF16LE = 0x14000100,

    kCFStringEncodingUTF32 = 0x0c000100,
    kCFStringEncodingUTF32BE = 0x18000100,
    kCFStringEncodingUTF32LE = 0x1c000100
};
typedef CFStringEncoding CFStringBuiltInEncodings;



extern
CFTypeID CFStringGetTypeID(void);
# 168 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 3
extern
CFStringRef CFStringCreateWithPascalString(CFAllocatorRef alloc, ConstStr255Param pStr, CFStringEncoding encoding);

extern
CFStringRef CFStringCreateWithCString(CFAllocatorRef alloc, const char *cStr, CFStringEncoding encoding);



extern
CFStringRef CFStringCreateWithBytes(CFAllocatorRef alloc, const UInt8 *bytes, CFIndex numBytes, CFStringEncoding encoding, Boolean isExternalRepresentation);

extern
CFStringRef CFStringCreateWithCharacters(CFAllocatorRef alloc, const UniChar *chars, CFIndex numChars);
# 199 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 3
extern
CFStringRef CFStringCreateWithPascalStringNoCopy(CFAllocatorRef alloc, ConstStr255Param pStr, CFStringEncoding encoding, CFAllocatorRef contentsDeallocator);

extern
CFStringRef CFStringCreateWithCStringNoCopy(CFAllocatorRef alloc, const char *cStr, CFStringEncoding encoding, CFAllocatorRef contentsDeallocator);



extern
CFStringRef CFStringCreateWithBytesNoCopy(CFAllocatorRef alloc, const UInt8 *bytes, CFIndex numBytes, CFStringEncoding encoding, Boolean isExternalRepresentation, CFAllocatorRef contentsDeallocator);

extern
CFStringRef CFStringCreateWithCharactersNoCopy(CFAllocatorRef alloc, const UniChar *chars, CFIndex numChars, CFAllocatorRef contentsDeallocator);



extern
CFStringRef CFStringCreateWithSubstring(CFAllocatorRef alloc, CFStringRef str, CFRange range);

extern
CFStringRef CFStringCreateCopy(CFAllocatorRef alloc, CFStringRef theString);



extern
CFStringRef CFStringCreateWithFormat(CFAllocatorRef alloc, CFDictionaryRef formatOptions, CFStringRef format, ...) __attribute__((format(CFString, 3, 4)));

extern
CFStringRef CFStringCreateWithFormatAndArguments(CFAllocatorRef alloc, CFDictionaryRef formatOptions, CFStringRef format, va_list arguments) __attribute__((format(CFString, 3, 0)));



extern
CFMutableStringRef CFStringCreateMutable(CFAllocatorRef alloc, CFIndex maxLength);

extern
CFMutableStringRef CFStringCreateMutableCopy(CFAllocatorRef alloc, CFIndex maxLength, CFStringRef theString);







extern
CFMutableStringRef CFStringCreateMutableWithExternalCharactersNoCopy(CFAllocatorRef alloc, UniChar *chars, CFIndex numChars, CFIndex capacity, CFAllocatorRef externalCharactersAllocator);





extern
CFIndex CFStringGetLength(CFStringRef theString);






extern
UniChar CFStringGetCharacterAtIndex(CFStringRef theString, CFIndex idx);

extern
void CFStringGetCharacters(CFStringRef theString, CFRange range, UniChar *buffer);
# 275 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 3
extern
Boolean CFStringGetPascalString(CFStringRef theString, StringPtr buffer, CFIndex bufferSize, CFStringEncoding encoding);

extern
Boolean CFStringGetCString(CFStringRef theString, char *buffer, CFIndex bufferSize, CFStringEncoding encoding);






extern
ConstStringPtr CFStringGetPascalStringPtr(CFStringRef theString, CFStringEncoding encoding);

extern
const char *CFStringGetCStringPtr(CFStringRef theString, CFStringEncoding encoding);

extern
const UniChar *CFStringGetCharactersPtr(CFStringRef theString);
# 311 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 3
extern
CFIndex CFStringGetBytes(CFStringRef theString, CFRange range, CFStringEncoding encoding, UInt8 lossByte, Boolean isExternalRepresentation, UInt8 *buffer, CFIndex maxBufLen, CFIndex *usedBufLen);







extern
CFStringRef CFStringCreateFromExternalRepresentation(CFAllocatorRef alloc, CFDataRef data, CFStringEncoding encoding);

extern
CFDataRef CFStringCreateExternalRepresentation(CFAllocatorRef alloc, CFStringRef theString, CFStringEncoding encoding, UInt8 lossByte);



extern
CFStringEncoding CFStringGetSmallestEncoding(CFStringRef theString);

extern
CFStringEncoding CFStringGetFastestEncoding(CFStringRef theString);



extern
CFStringEncoding CFStringGetSystemEncoding(void);

extern
CFIndex CFStringGetMaximumSizeForEncoding(CFIndex length, CFStringEncoding encoding);






extern
Boolean CFStringGetFileSystemRepresentation(CFStringRef string, char *buffer, CFIndex maxBufLen);



extern
CFIndex CFStringGetMaximumSizeOfFileSystemRepresentation(CFStringRef string);



extern
CFStringRef CFStringCreateWithFileSystemRepresentation(CFAllocatorRef alloc, const char *buffer);






enum {
    kCFCompareCaseInsensitive = 1,
    kCFCompareBackwards = 4,
    kCFCompareAnchored = 8,
    kCFCompareNonliteral = 16,
    kCFCompareLocalized = 32,
    kCFCompareNumerically = 64

    ,
    kCFCompareDiacriticInsensitive = 128,
    kCFCompareWidthInsensitive = 256,
    kCFCompareForcedOrdering = 512

};
typedef CFOptionFlags CFStringCompareFlags;






extern
CFComparisonResult CFStringCompareWithOptionsAndLocale(CFStringRef theString1, CFStringRef theString2, CFRange rangeToCompare, CFStringCompareFlags compareOptions, CFLocaleRef locale) ;



extern
CFComparisonResult CFStringCompareWithOptions(CFStringRef theString1, CFStringRef theString2, CFRange rangeToCompare, CFStringCompareFlags compareOptions);





extern
CFComparisonResult CFStringCompare(CFStringRef theString1, CFStringRef theString2, CFStringCompareFlags compareOptions);






extern
Boolean CFStringFindWithOptionsAndLocale(CFStringRef theString, CFStringRef stringToFind, CFRange rangeToSearch, CFStringCompareFlags searchOptions, CFLocaleRef locale, CFRange *result) ;



extern
Boolean CFStringFindWithOptions(CFStringRef theString, CFStringRef stringToFind, CFRange rangeToSearch, CFStringCompareFlags searchOptions, CFRange *result);
# 422 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 3
extern
CFArrayRef CFStringCreateArrayWithFindResults(CFAllocatorRef alloc, CFStringRef theString, CFStringRef stringToFind, CFRange rangeToSearch, CFStringCompareFlags compareOptions);



extern
CFRange CFStringFind(CFStringRef theString, CFStringRef stringToFind, CFStringCompareFlags compareOptions);

extern
Boolean CFStringHasPrefix(CFStringRef theString, CFStringRef prefix);

extern
Boolean CFStringHasSuffix(CFStringRef theString, CFStringRef suffix);
# 449 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 3
extern CFRange CFStringGetRangeOfComposedCharactersAtIndex(CFStringRef theString, CFIndex theIndex);
# 480 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 3
extern Boolean CFStringFindCharacterFromSet(CFStringRef theString, CFCharacterSetRef theSet, CFRange rangeToSearch, CFStringCompareFlags searchOptions, CFRange *result);
# 491 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 3
extern
void CFStringGetLineBounds(CFStringRef theString, CFRange range, CFIndex *lineBeginIndex, CFIndex *lineEndIndex, CFIndex *contentsEndIndex);



extern
void CFStringGetParagraphBounds(CFStringRef string, CFRange range, CFIndex *parBeginIndex, CFIndex *parEndIndex, CFIndex *contentsEndIndex) ;
# 524 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 3
extern
CFIndex CFStringGetHyphenationLocationBeforeIndex(CFStringRef string, CFIndex location, CFRange limitRange, CFOptionFlags options, CFLocaleRef locale, UTF32Char *character) ;

extern
Boolean CFStringIsHyphenationAvailableForLocale(CFLocaleRef locale) ;



extern
CFStringRef CFStringCreateByCombiningStrings(CFAllocatorRef alloc, CFArrayRef theArray, CFStringRef separatorString);

extern
CFArrayRef CFStringCreateArrayBySeparatingStrings(CFAllocatorRef alloc, CFStringRef theString, CFStringRef separatorString);




extern
SInt32 CFStringGetIntValue(CFStringRef str);

extern
double CFStringGetDoubleValue(CFStringRef str);
# 555 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 3
extern
void CFStringAppend(CFMutableStringRef theString, CFStringRef appendedString);

extern
void CFStringAppendCharacters(CFMutableStringRef theString, const UniChar *chars, CFIndex numChars);

extern
void CFStringAppendPascalString(CFMutableStringRef theString, ConstStr255Param pStr, CFStringEncoding encoding);

extern
void CFStringAppendCString(CFMutableStringRef theString, const char *cStr, CFStringEncoding encoding);

extern
void CFStringAppendFormat(CFMutableStringRef theString, CFDictionaryRef formatOptions, CFStringRef format, ...) __attribute__((format(CFString, 3, 4)));

extern
void CFStringAppendFormatAndArguments(CFMutableStringRef theString, CFDictionaryRef formatOptions, CFStringRef format, va_list arguments) __attribute__((format(CFString, 3, 0)));

extern
void CFStringInsert(CFMutableStringRef str, CFIndex idx, CFStringRef insertedStr);

extern
void CFStringDelete(CFMutableStringRef theString, CFRange range);

extern
void CFStringReplace(CFMutableStringRef theString, CFRange range, CFStringRef replacement);

extern
void CFStringReplaceAll(CFMutableStringRef theString, CFStringRef replacement);
# 593 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 3
extern
CFIndex CFStringFindAndReplace(CFMutableStringRef theString, CFStringRef stringToFind, CFStringRef replacementString, CFRange rangeToSearch, CFStringCompareFlags compareOptions);
# 604 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 3
extern
void CFStringSetExternalCharactersNoCopy(CFMutableStringRef theString, UniChar *chars, CFIndex length, CFIndex capacity);
# 618 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 3
extern
void CFStringPad(CFMutableStringRef theString, CFStringRef padString, CFIndex length, CFIndex indexIntoPad);

extern
void CFStringTrim(CFMutableStringRef theString, CFStringRef trimString);

extern
void CFStringTrimWhitespace(CFMutableStringRef theString);

extern
void CFStringLowercase(CFMutableStringRef theString, CFLocaleRef locale);

extern
void CFStringUppercase(CFMutableStringRef theString, CFLocaleRef locale);

extern
void CFStringCapitalize(CFMutableStringRef theString, CFLocaleRef locale);







enum {
 kCFStringNormalizationFormD = 0,
 kCFStringNormalizationFormKD,
 kCFStringNormalizationFormC,
 kCFStringNormalizationFormKC
};
typedef CFIndex CFStringNormalizationForm;
# 661 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 3
extern void CFStringNormalize(CFMutableStringRef theString, CFStringNormalizationForm theForm);
# 688 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 3
extern
void CFStringFold(CFMutableStringRef theString, CFOptionFlags theFlags, CFLocaleRef theLocale) ;





extern
Boolean CFStringTransform(CFMutableStringRef string, CFRange *range, CFStringRef transform, Boolean reverse);



extern const CFStringRef kCFStringTransformStripCombiningMarks;
extern const CFStringRef kCFStringTransformToLatin;
extern const CFStringRef kCFStringTransformFullwidthHalfwidth;
extern const CFStringRef kCFStringTransformLatinKatakana;
extern const CFStringRef kCFStringTransformLatinHiragana;
extern const CFStringRef kCFStringTransformHiraganaKatakana;
extern const CFStringRef kCFStringTransformMandarinLatin;
extern const CFStringRef kCFStringTransformLatinHangul;
extern const CFStringRef kCFStringTransformLatinArabic;
extern const CFStringRef kCFStringTransformLatinHebrew;
extern const CFStringRef kCFStringTransformLatinThai;
extern const CFStringRef kCFStringTransformLatinCyrillic;
extern const CFStringRef kCFStringTransformLatinGreek;
extern const CFStringRef kCFStringTransformToXMLHex;
extern const CFStringRef kCFStringTransformToUnicodeName;
extern const CFStringRef kCFStringTransformStripDiacritics ;






extern
Boolean CFStringIsEncodingAvailable(CFStringEncoding encoding);



extern
const CFStringEncoding *CFStringGetListOfAvailableEncodings(void);



extern
CFStringRef CFStringGetNameOfEncoding(CFStringEncoding encoding);



extern
unsigned long CFStringConvertEncodingToNSStringEncoding(CFStringEncoding encoding);

extern
CFStringEncoding CFStringConvertNSStringEncodingToEncoding(unsigned long encoding);



extern
UInt32 CFStringConvertEncodingToWindowsCodepage(CFStringEncoding encoding);

extern
CFStringEncoding CFStringConvertWindowsCodepageToEncoding(UInt32 codepage);



extern
CFStringEncoding CFStringConvertIANACharSetNameToEncoding(CFStringRef theString);

extern
CFStringRef CFStringConvertEncodingToIANACharSetName(CFStringEncoding encoding);





extern
CFStringEncoding CFStringGetMostCompatibleMacStringEncoding(CFStringEncoding encoding);
# 778 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 3
typedef struct {
    UniChar buffer[64];
    CFStringRef theString;
    const UniChar *directBuffer;
    CFRange rangeToBuffer;
    CFIndex bufferedRangeStart;
    CFIndex bufferedRangeEnd;
} CFStringInlineBuffer;


static __inline__ __attribute__((always_inline)) void CFStringInitInlineBuffer(CFStringRef str, CFStringInlineBuffer *buf, CFRange range) {
    buf->theString = str;
    buf->rangeToBuffer = range;
    buf->directBuffer = CFStringGetCharactersPtr(str);
    buf->bufferedRangeStart = buf->bufferedRangeEnd = 0;
}

static __inline__ __attribute__((always_inline)) UniChar CFStringGetCharacterFromInlineBuffer(CFStringInlineBuffer *buf, CFIndex idx) {
    if (buf->directBuffer) {
 if (idx < 0 || idx >= buf->rangeToBuffer.length) return 0;
        return buf->directBuffer[idx + buf->rangeToBuffer.location];
    }
    if (idx >= buf->bufferedRangeEnd || idx < buf->bufferedRangeStart) {
 if (idx < 0 || idx >= buf->rangeToBuffer.length) return 0;
 if ((buf->bufferedRangeStart = idx - 4) < 0) buf->bufferedRangeStart = 0;
 buf->bufferedRangeEnd = buf->bufferedRangeStart + 64;
 if (buf->bufferedRangeEnd > buf->rangeToBuffer.length) buf->bufferedRangeEnd = buf->rangeToBuffer.length;
 CFStringGetCharacters(buf->theString, CFRangeMake(buf->rangeToBuffer.location + buf->bufferedRangeStart, buf->bufferedRangeEnd - buf->bufferedRangeStart), buf->buffer);
    }
    return buf->buffer[idx - buf->bufferedRangeStart];
}
# 825 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFString.h" 3
static __inline__ __attribute__((always_inline)) Boolean CFStringIsSurrogateHighCharacter(UniChar character) {
    return ((character >= 0xD800UL) && (character <= 0xDBFFUL) ? 1 : 0);
}

static __inline__ __attribute__((always_inline)) Boolean CFStringIsSurrogateLowCharacter(UniChar character) {
    return ((character >= 0xDC00UL) && (character <= 0xDFFFUL) ? 1 : 0);
}

static __inline__ __attribute__((always_inline)) UTF32Char CFStringGetLongCharacterForSurrogatePair(UniChar surrogateHigh, UniChar surrogateLow) {
    return (UTF32Char)(((surrogateHigh - 0xD800UL) << 10) + (surrogateLow - 0xDC00UL) + 0x0010000UL);
}


static __inline__ __attribute__((always_inline)) Boolean CFStringGetSurrogatePairForLongCharacter(UTF32Char character, UniChar *surrogates) {
    if ((character > 0xFFFFUL) && (character < 0x110000UL)) {
        character -= 0x10000;
        if (((void *)0) != surrogates) {
            surrogates[0] = (UniChar)((character >> 10) + 0xD800UL);
            surrogates[1] = (UniChar)((character & 0x3FF) + 0xDC00UL);
        }
        return 1;
    } else {
        if (((void *)0) != surrogates) *surrogates = (UniChar)character;
        return 0;
    }
}







extern
void CFShow(CFTypeRef obj);

extern
void CFShowStr(CFStringRef str);


extern
CFStringRef __CFStringMakeConstantString(const char *cStr);


# 14 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTimeZone.h" 2 3



extern
CFTypeID CFTimeZoneGetTypeID(void);

extern
CFTimeZoneRef CFTimeZoneCopySystem(void);

extern
void CFTimeZoneResetSystem(void);

extern
CFTimeZoneRef CFTimeZoneCopyDefault(void);

extern
void CFTimeZoneSetDefault(CFTimeZoneRef tz);

extern
CFArrayRef CFTimeZoneCopyKnownNames(void);

extern
CFDictionaryRef CFTimeZoneCopyAbbreviationDictionary(void);

extern
void CFTimeZoneSetAbbreviationDictionary(CFDictionaryRef dict);

extern
CFTimeZoneRef CFTimeZoneCreate(CFAllocatorRef allocator, CFStringRef name, CFDataRef data);

extern
CFTimeZoneRef CFTimeZoneCreateWithTimeIntervalFromGMT(CFAllocatorRef allocator, CFTimeInterval ti);

extern
CFTimeZoneRef CFTimeZoneCreateWithName(CFAllocatorRef allocator, CFStringRef name, Boolean tryAbbrev);

extern
CFStringRef CFTimeZoneGetName(CFTimeZoneRef tz);

extern
CFDataRef CFTimeZoneGetData(CFTimeZoneRef tz);

extern
CFTimeInterval CFTimeZoneGetSecondsFromGMT(CFTimeZoneRef tz, CFAbsoluteTime at);

extern
CFStringRef CFTimeZoneCopyAbbreviation(CFTimeZoneRef tz, CFAbsoluteTime at);

extern
Boolean CFTimeZoneIsDaylightSavingTime(CFTimeZoneRef tz, CFAbsoluteTime at);

extern
CFTimeInterval CFTimeZoneGetDaylightSavingTimeOffset(CFTimeZoneRef tz, CFAbsoluteTime at) ;

extern
CFAbsoluteTime CFTimeZoneGetNextDaylightSavingTimeTransition(CFTimeZoneRef tz, CFAbsoluteTime at) ;


enum {
 kCFTimeZoneNameStyleStandard,
 kCFTimeZoneNameStyleShortStandard,
 kCFTimeZoneNameStyleDaylightSaving,
 kCFTimeZoneNameStyleShortDaylightSaving,
 kCFTimeZoneNameStyleGeneric,
 kCFTimeZoneNameStyleShortGeneric
};

typedef CFIndex CFTimeZoneNameStyle;

extern
CFStringRef CFTimeZoneCopyLocalizedName(CFTimeZoneRef tz, CFTimeZoneNameStyle style, CFLocaleRef locale) ;

extern
const CFStringRef kCFTimeZoneSystemTimeZoneDidChangeNotification ;


# 12 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFCalendar.h" 2 3



typedef struct __CFCalendar * CFCalendarRef;

extern
CFTypeID CFCalendarGetTypeID(void);

extern
CFCalendarRef CFCalendarCopyCurrent(void);

extern
CFCalendarRef CFCalendarCreateWithIdentifier(CFAllocatorRef allocator, CFStringRef identifier);



extern
CFStringRef CFCalendarGetIdentifier(CFCalendarRef calendar);


extern
CFLocaleRef CFCalendarCopyLocale(CFCalendarRef calendar);

extern
void CFCalendarSetLocale(CFCalendarRef calendar, CFLocaleRef locale);

extern
CFTimeZoneRef CFCalendarCopyTimeZone(CFCalendarRef calendar);

extern
void CFCalendarSetTimeZone(CFCalendarRef calendar, CFTimeZoneRef tz);

extern
CFIndex CFCalendarGetFirstWeekday(CFCalendarRef calendar);

extern
void CFCalendarSetFirstWeekday(CFCalendarRef calendar, CFIndex wkdy);

extern
CFIndex CFCalendarGetMinimumDaysInFirstWeek(CFCalendarRef calendar);

extern
void CFCalendarSetMinimumDaysInFirstWeek(CFCalendarRef calendar, CFIndex mwd);


enum {
 kCFCalendarUnitEra = (1UL << 1),
 kCFCalendarUnitYear = (1UL << 2),
 kCFCalendarUnitMonth = (1UL << 3),
 kCFCalendarUnitDay = (1UL << 4),
 kCFCalendarUnitHour = (1UL << 5),
 kCFCalendarUnitMinute = (1UL << 6),
 kCFCalendarUnitSecond = (1UL << 7),
 kCFCalendarUnitWeek = (1UL << 8) ,
 kCFCalendarUnitWeekday = (1UL << 9),
 kCFCalendarUnitWeekdayOrdinal = (1UL << 10),

 kCFCalendarUnitQuarter = (1UL << 11),


 kCFCalendarUnitWeekOfMonth = (1UL << 12),
 kCFCalendarUnitWeekOfYear = (1UL << 13),
 kCFCalendarUnitYearForWeekOfYear = (1UL << 14),

};
typedef CFOptionFlags CFCalendarUnit;

extern
CFRange CFCalendarGetMinimumRangeOfUnit(CFCalendarRef calendar, CFCalendarUnit unit);

extern
CFRange CFCalendarGetMaximumRangeOfUnit(CFCalendarRef calendar, CFCalendarUnit unit);

extern
CFRange CFCalendarGetRangeOfUnit(CFCalendarRef calendar, CFCalendarUnit smallerUnit, CFCalendarUnit biggerUnit, CFAbsoluteTime at);

extern
CFIndex CFCalendarGetOrdinalityOfUnit(CFCalendarRef calendar, CFCalendarUnit smallerUnit, CFCalendarUnit biggerUnit, CFAbsoluteTime at);

extern
Boolean CFCalendarGetTimeRangeOfUnit(CFCalendarRef calendar, CFCalendarUnit unit, CFAbsoluteTime at, CFAbsoluteTime *startp, CFTimeInterval *tip) ;

extern
Boolean CFCalendarComposeAbsoluteTime(CFCalendarRef calendar, CFAbsoluteTime *at, const char *componentDesc, ...);

extern
Boolean CFCalendarDecomposeAbsoluteTime(CFCalendarRef calendar, CFAbsoluteTime at, const char *componentDesc, ...);


enum {
    kCFCalendarComponentsWrap = (1UL << 0)
};

extern
Boolean CFCalendarAddComponents(CFCalendarRef calendar, CFAbsoluteTime *at, CFOptionFlags options, const char *componentDesc, ...);

extern
Boolean CFCalendarGetComponentDifference(CFCalendarRef calendar, CFAbsoluteTime startingAT, CFAbsoluteTime resultAT, CFOptionFlags options, const char *componentDesc, ...);



# 45 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3



# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDateFormatter.h" 1 3
# 12 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDateFormatter.h" 3


typedef struct __CFDateFormatter *CFDateFormatterRef;



extern
CFStringRef CFDateFormatterCreateDateFormatFromTemplate(CFAllocatorRef allocator, CFStringRef tmplate, CFOptionFlags options, CFLocaleRef locale) ;


extern
CFTypeID CFDateFormatterGetTypeID(void);

enum {
 kCFDateFormatterNoStyle = 0,
 kCFDateFormatterShortStyle = 1,
 kCFDateFormatterMediumStyle = 2,
 kCFDateFormatterLongStyle = 3,
 kCFDateFormatterFullStyle = 4
};
typedef CFIndex CFDateFormatterStyle;
# 46 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDateFormatter.h" 3
extern
CFDateFormatterRef CFDateFormatterCreate(CFAllocatorRef allocator, CFLocaleRef locale, CFDateFormatterStyle dateStyle, CFDateFormatterStyle timeStyle);



extern
CFLocaleRef CFDateFormatterGetLocale(CFDateFormatterRef formatter);

extern
CFDateFormatterStyle CFDateFormatterGetDateStyle(CFDateFormatterRef formatter);

extern
CFDateFormatterStyle CFDateFormatterGetTimeStyle(CFDateFormatterRef formatter);


extern
CFStringRef CFDateFormatterGetFormat(CFDateFormatterRef formatter);

extern
void CFDateFormatterSetFormat(CFDateFormatterRef formatter, CFStringRef formatString);







extern
CFStringRef CFDateFormatterCreateStringWithDate(CFAllocatorRef allocator, CFDateFormatterRef formatter, CFDateRef date);

extern
CFStringRef CFDateFormatterCreateStringWithAbsoluteTime(CFAllocatorRef allocator, CFDateFormatterRef formatter, CFAbsoluteTime at);




extern
CFDateRef CFDateFormatterCreateDateFromString(CFAllocatorRef allocator, CFDateFormatterRef formatter, CFStringRef string, CFRange *rangep);

extern
Boolean CFDateFormatterGetAbsoluteTimeFromString(CFDateFormatterRef formatter, CFStringRef string, CFRange *rangep, CFAbsoluteTime *atp);
# 96 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDateFormatter.h" 3
extern
void CFDateFormatterSetProperty(CFDateFormatterRef formatter, CFStringRef key, CFTypeRef value);

extern
CFTypeRef CFDateFormatterCopyProperty(CFDateFormatterRef formatter, CFStringRef key);



extern const CFStringRef kCFDateFormatterIsLenient;
extern const CFStringRef kCFDateFormatterTimeZone;
extern const CFStringRef kCFDateFormatterCalendarName;
extern const CFStringRef kCFDateFormatterDefaultFormat;
extern const CFStringRef kCFDateFormatterTwoDigitStartDate;
extern const CFStringRef kCFDateFormatterDefaultDate;
extern const CFStringRef kCFDateFormatterCalendar;
extern const CFStringRef kCFDateFormatterEraSymbols;
extern const CFStringRef kCFDateFormatterMonthSymbols;
extern const CFStringRef kCFDateFormatterShortMonthSymbols;
extern const CFStringRef kCFDateFormatterWeekdaySymbols;
extern const CFStringRef kCFDateFormatterShortWeekdaySymbols;
extern const CFStringRef kCFDateFormatterAMSymbol;
extern const CFStringRef kCFDateFormatterPMSymbol;
extern const CFStringRef kCFDateFormatterLongEraSymbols ;
extern const CFStringRef kCFDateFormatterVeryShortMonthSymbols ;
extern const CFStringRef kCFDateFormatterStandaloneMonthSymbols ;
extern const CFStringRef kCFDateFormatterShortStandaloneMonthSymbols ;
extern const CFStringRef kCFDateFormatterVeryShortStandaloneMonthSymbols ;
extern const CFStringRef kCFDateFormatterVeryShortWeekdaySymbols ;
extern const CFStringRef kCFDateFormatterStandaloneWeekdaySymbols ;
extern const CFStringRef kCFDateFormatterShortStandaloneWeekdaySymbols ;
extern const CFStringRef kCFDateFormatterVeryShortStandaloneWeekdaySymbols ;
extern const CFStringRef kCFDateFormatterQuarterSymbols ;
extern const CFStringRef kCFDateFormatterShortQuarterSymbols ;
extern const CFStringRef kCFDateFormatterStandaloneQuarterSymbols ;
extern const CFStringRef kCFDateFormatterShortStandaloneQuarterSymbols ;
extern const CFStringRef kCFDateFormatterGregorianStartDate ;
extern const CFStringRef kCFDateFormatterDoesRelativeDateFormattingKey ;
# 147 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFDateFormatter.h" 3

# 49 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3

# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFError.h" 1 3
# 36 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFError.h" 3






typedef struct __CFError * CFErrorRef;





extern
CFTypeID CFErrorGetTypeID(void) ;



extern const CFStringRef kCFErrorDomainPOSIX ;
extern const CFStringRef kCFErrorDomainOSStatus ;
extern const CFStringRef kCFErrorDomainMach ;
extern const CFStringRef kCFErrorDomainCocoa ;


extern const CFStringRef kCFErrorLocalizedDescriptionKey ;
extern const CFStringRef kCFErrorLocalizedFailureReasonKey ;
extern const CFStringRef kCFErrorLocalizedRecoverySuggestionKey ;


extern const CFStringRef kCFErrorDescriptionKey ;


extern const CFStringRef kCFErrorUnderlyingErrorKey ;
extern const CFStringRef kCFErrorURLKey ;
extern const CFStringRef kCFErrorFilePathKey ;
# 83 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFError.h" 3
extern
CFErrorRef CFErrorCreate(CFAllocatorRef allocator, CFStringRef domain, CFIndex code, CFDictionaryRef userInfo) ;
# 98 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFError.h" 3
extern
CFErrorRef CFErrorCreateWithUserInfoKeysAndValues(CFAllocatorRef allocator, CFStringRef domain, CFIndex code, const void *const *userInfoKeys, const void *const *userInfoValues, CFIndex numUserInfoValues) ;







extern
CFStringRef CFErrorGetDomain(CFErrorRef err) ;







extern
CFIndex CFErrorGetCode(CFErrorRef err) ;
# 126 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFError.h" 3
extern
CFDictionaryRef CFErrorCopyUserInfo(CFErrorRef err) ;
# 140 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFError.h" 3
extern
CFStringRef CFErrorCopyDescription(CFErrorRef err) ;
# 152 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFError.h" 3
extern
CFStringRef CFErrorCopyFailureReason(CFErrorRef err) ;
# 164 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFError.h" 3
extern
CFStringRef CFErrorCopyRecoverySuggestion(CFErrorRef err) ;




# 51 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3

# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFNumber.h" 1 3
# 10 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFNumber.h" 3


typedef const struct __CFBoolean * CFBooleanRef;

extern
const CFBooleanRef kCFBooleanTrue;
extern
const CFBooleanRef kCFBooleanFalse;

extern
CFTypeID CFBooleanGetTypeID(void);

extern
Boolean CFBooleanGetValue(CFBooleanRef boolean);

enum {

    kCFNumberSInt8Type = 1,
    kCFNumberSInt16Type = 2,
    kCFNumberSInt32Type = 3,
    kCFNumberSInt64Type = 4,
    kCFNumberFloat32Type = 5,
    kCFNumberFloat64Type = 6,

    kCFNumberCharType = 7,
    kCFNumberShortType = 8,
    kCFNumberIntType = 9,
    kCFNumberLongType = 10,
    kCFNumberLongLongType = 11,
    kCFNumberFloatType = 12,
    kCFNumberDoubleType = 13,

    kCFNumberCFIndexType = 14,

    kCFNumberNSIntegerType = 15,
    kCFNumberCGFloatType = 16,
    kCFNumberMaxType = 16



};
typedef CFIndex CFNumberType;

typedef const struct __CFNumber * CFNumberRef;

extern
const CFNumberRef kCFNumberPositiveInfinity;
extern
const CFNumberRef kCFNumberNegativeInfinity;
extern
const CFNumberRef kCFNumberNaN;

extern
CFTypeID CFNumberGetTypeID(void);
# 72 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFNumber.h" 3
extern
CFNumberRef CFNumberCreate(CFAllocatorRef allocator, CFNumberType theType, const void *valuePtr);





extern
CFNumberType CFNumberGetType(CFNumberRef number);




extern
CFIndex CFNumberGetByteSize(CFNumberRef number);





extern
Boolean CFNumberIsFloatType(CFNumberRef number);
# 103 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFNumber.h" 3
extern
Boolean CFNumberGetValue(CFNumberRef number, CFNumberType theType, void *valuePtr);
# 121 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFNumber.h" 3
extern
CFComparisonResult CFNumberCompare(CFNumberRef number, CFNumberRef otherNumber, void *context);


# 53 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFNumberFormatter.h" 1 3
# 12 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFNumberFormatter.h" 3


typedef struct __CFNumberFormatter *CFNumberFormatterRef;



extern
CFTypeID CFNumberFormatterGetTypeID(void);

enum {
 kCFNumberFormatterNoStyle = 0,
 kCFNumberFormatterDecimalStyle = 1,
 kCFNumberFormatterCurrencyStyle = 2,
 kCFNumberFormatterPercentStyle = 3,
 kCFNumberFormatterScientificStyle = 4,
 kCFNumberFormatterSpellOutStyle = 5
};
typedef CFIndex CFNumberFormatterStyle;


extern
CFNumberFormatterRef CFNumberFormatterCreate(CFAllocatorRef allocator, CFLocaleRef locale, CFNumberFormatterStyle style);



extern
CFLocaleRef CFNumberFormatterGetLocale(CFNumberFormatterRef formatter);

extern
CFNumberFormatterStyle CFNumberFormatterGetStyle(CFNumberFormatterRef formatter);


extern
CFStringRef CFNumberFormatterGetFormat(CFNumberFormatterRef formatter);

extern
void CFNumberFormatterSetFormat(CFNumberFormatterRef formatter, CFStringRef formatString);
# 57 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFNumberFormatter.h" 3
extern
CFStringRef CFNumberFormatterCreateStringWithNumber(CFAllocatorRef allocator, CFNumberFormatterRef formatter, CFNumberRef number);

extern
CFStringRef CFNumberFormatterCreateStringWithValue(CFAllocatorRef allocator, CFNumberFormatterRef formatter, CFNumberType numberType, const void *valuePtr);




enum {
    kCFNumberFormatterParseIntegersOnly = 1
};
typedef CFOptionFlags CFNumberFormatterOptionFlags;

extern
CFNumberRef CFNumberFormatterCreateNumberFromString(CFAllocatorRef allocator, CFNumberFormatterRef formatter, CFStringRef string, CFRange *rangep, CFOptionFlags options);

extern
Boolean CFNumberFormatterGetValueFromString(CFNumberFormatterRef formatter, CFStringRef string, CFRange *rangep, CFNumberType numberType, void *valuePtr);
# 87 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFNumberFormatter.h" 3
extern
void CFNumberFormatterSetProperty(CFNumberFormatterRef formatter, CFStringRef key, CFTypeRef value);

extern
CFTypeRef CFNumberFormatterCopyProperty(CFNumberFormatterRef formatter, CFStringRef key);



extern const CFStringRef kCFNumberFormatterCurrencyCode;
extern const CFStringRef kCFNumberFormatterDecimalSeparator;
extern const CFStringRef kCFNumberFormatterCurrencyDecimalSeparator;
extern const CFStringRef kCFNumberFormatterAlwaysShowDecimalSeparator;
extern const CFStringRef kCFNumberFormatterGroupingSeparator;
extern const CFStringRef kCFNumberFormatterUseGroupingSeparator;
extern const CFStringRef kCFNumberFormatterPercentSymbol;
extern const CFStringRef kCFNumberFormatterZeroSymbol;
extern const CFStringRef kCFNumberFormatterNaNSymbol;
extern const CFStringRef kCFNumberFormatterInfinitySymbol;
extern const CFStringRef kCFNumberFormatterMinusSign;
extern const CFStringRef kCFNumberFormatterPlusSign;
extern const CFStringRef kCFNumberFormatterCurrencySymbol;
extern const CFStringRef kCFNumberFormatterExponentSymbol;
extern const CFStringRef kCFNumberFormatterMinIntegerDigits;
extern const CFStringRef kCFNumberFormatterMaxIntegerDigits;
extern const CFStringRef kCFNumberFormatterMinFractionDigits;
extern const CFStringRef kCFNumberFormatterMaxFractionDigits;
extern const CFStringRef kCFNumberFormatterGroupingSize;
extern const CFStringRef kCFNumberFormatterSecondaryGroupingSize;
extern const CFStringRef kCFNumberFormatterRoundingMode;
extern const CFStringRef kCFNumberFormatterRoundingIncrement;
extern const CFStringRef kCFNumberFormatterFormatWidth;
extern const CFStringRef kCFNumberFormatterPaddingPosition;
extern const CFStringRef kCFNumberFormatterPaddingCharacter;
extern const CFStringRef kCFNumberFormatterDefaultFormat;
extern const CFStringRef kCFNumberFormatterMultiplier;
extern const CFStringRef kCFNumberFormatterPositivePrefix;
extern const CFStringRef kCFNumberFormatterPositiveSuffix;
extern const CFStringRef kCFNumberFormatterNegativePrefix;
extern const CFStringRef kCFNumberFormatterNegativeSuffix;
extern const CFStringRef kCFNumberFormatterPerMillSymbol;
extern const CFStringRef kCFNumberFormatterInternationalCurrencySymbol;
extern const CFStringRef kCFNumberFormatterCurrencyGroupingSeparator ;
extern const CFStringRef kCFNumberFormatterIsLenient ;
extern const CFStringRef kCFNumberFormatterUseSignificantDigits ;
extern const CFStringRef kCFNumberFormatterMinSignificantDigits ;
extern const CFStringRef kCFNumberFormatterMaxSignificantDigits ;

enum {
    kCFNumberFormatterRoundCeiling = 0,
    kCFNumberFormatterRoundFloor = 1,
    kCFNumberFormatterRoundDown = 2,
    kCFNumberFormatterRoundUp = 3,
    kCFNumberFormatterRoundHalfEven = 4,
    kCFNumberFormatterRoundHalfDown = 5,
    kCFNumberFormatterRoundHalfUp = 6
};
typedef CFIndex CFNumberFormatterRoundingMode;

enum {
    kCFNumberFormatterPadBeforePrefix = 0,
    kCFNumberFormatterPadAfterPrefix = 1,
    kCFNumberFormatterPadBeforeSuffix = 2,
    kCFNumberFormatterPadAfterSuffix = 3
};
typedef CFIndex CFNumberFormatterPadPosition;


extern
Boolean CFNumberFormatterGetDecimalInfoForCurrencyCode(CFStringRef currencyCode, int32_t *defaultFractionDigits, double *roundingIncrement);







# 54 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFPreferences.h" 1 3
# 12 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFPreferences.h" 3


extern
const CFStringRef kCFPreferencesAnyApplication;
extern
const CFStringRef kCFPreferencesCurrentApplication;
extern
const CFStringRef kCFPreferencesAnyHost;
extern
const CFStringRef kCFPreferencesCurrentHost;
extern
const CFStringRef kCFPreferencesAnyUser;
extern
const CFStringRef kCFPreferencesCurrentUser;
# 41 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFPreferences.h" 3
extern
CFPropertyListRef CFPreferencesCopyAppValue(CFStringRef key, CFStringRef applicationID);




extern
Boolean CFPreferencesGetAppBooleanValue(CFStringRef key, CFStringRef applicationID, Boolean *keyExistsAndHasValidFormat);




extern
CFIndex CFPreferencesGetAppIntegerValue(CFStringRef key, CFStringRef applicationID, Boolean *keyExistsAndHasValidFormat);




extern
void CFPreferencesSetAppValue(CFStringRef key, CFPropertyListRef value, CFStringRef applicationID);





extern
void CFPreferencesAddSuitePreferencesToApp(CFStringRef applicationID, CFStringRef suiteID);

extern
void CFPreferencesRemoveSuitePreferencesFromApp(CFStringRef applicationID, CFStringRef suiteID);



extern
Boolean CFPreferencesAppSynchronize(CFStringRef applicationID);





extern
CFPropertyListRef CFPreferencesCopyValue(CFStringRef key, CFStringRef applicationID, CFStringRef userName, CFStringRef hostName);





extern
CFDictionaryRef CFPreferencesCopyMultiple(CFArrayRef keysToFetch, CFStringRef applicationID, CFStringRef userName, CFStringRef hostName);



extern
void CFPreferencesSetValue(CFStringRef key, CFPropertyListRef value, CFStringRef applicationID, CFStringRef userName, CFStringRef hostName);



extern
void CFPreferencesSetMultiple(CFDictionaryRef keysToSet, CFArrayRef keysToRemove, CFStringRef applicationID, CFStringRef userName, CFStringRef hostName);

extern
Boolean CFPreferencesSynchronize(CFStringRef applicationID, CFStringRef userName, CFStringRef hostName);





extern
CFArrayRef CFPreferencesCopyApplicationList(CFStringRef userName, CFStringRef hostName);




extern
CFArrayRef CFPreferencesCopyKeyList(CFStringRef applicationID, CFStringRef userName, CFStringRef hostName);







extern
Boolean CFPreferencesAppValueIsForced(CFStringRef key, CFStringRef applicationID);




# 55 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFPropertyList.h" 1 3
# 13 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFPropertyList.h" 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStream.h" 1 3
# 11 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStream.h" 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 1 3
# 14 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3


enum {
    kCFURLPOSIXPathStyle = 0,
    kCFURLHFSPathStyle,
    kCFURLWindowsPathStyle
};
typedef CFIndex CFURLPathStyle;

typedef const struct __CFURL * CFURLRef;
# 39 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
CFTypeID CFURLGetTypeID(void);



extern
CFURLRef CFURLCreateWithBytes(CFAllocatorRef allocator, const UInt8 *URLBytes, CFIndex length, CFStringEncoding encoding, CFURLRef baseURL);





extern
CFDataRef CFURLCreateData(CFAllocatorRef allocator, CFURLRef url, CFStringEncoding encoding, Boolean escapeWhitespace);


extern
CFURLRef CFURLCreateWithString(CFAllocatorRef allocator, CFStringRef URLString, CFURLRef baseURL);
# 69 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
CFURLRef CFURLCreateAbsoluteURLWithBytes(CFAllocatorRef alloc, const UInt8 *relativeURLBytes, CFIndex length, CFStringEncoding encoding, CFURLRef baseURL, Boolean useCompatibilityMode);







extern
CFURLRef CFURLCreateWithFileSystemPath(CFAllocatorRef allocator, CFStringRef filePath, CFURLPathStyle pathStyle, Boolean isDirectory);

extern
CFURLRef CFURLCreateFromFileSystemRepresentation(CFAllocatorRef allocator, const UInt8 *buffer, CFIndex bufLen, Boolean isDirectory);







extern
CFURLRef CFURLCreateWithFileSystemPathRelativeToBase(CFAllocatorRef allocator, CFStringRef filePath, CFURLPathStyle pathStyle, Boolean isDirectory, CFURLRef baseURL);

extern
CFURLRef CFURLCreateFromFileSystemRepresentationRelativeToBase(CFAllocatorRef allocator, const UInt8 *buffer, CFIndex bufLen, Boolean isDirectory, CFURLRef baseURL);
# 103 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
Boolean CFURLGetFileSystemRepresentation(CFURLRef url, Boolean resolveAgainstBase, UInt8 *buffer, CFIndex maxBufLen);


extern
CFURLRef CFURLCopyAbsoluteURL(CFURLRef relativeURL);


extern
CFStringRef CFURLGetString(CFURLRef anURL);


extern
CFURLRef CFURLGetBaseURL(CFURLRef anURL);
# 178 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
Boolean CFURLCanBeDecomposed(CFURLRef anURL);



extern
CFStringRef CFURLCopyScheme(CFURLRef anURL);


extern
CFStringRef CFURLCopyNetLocation(CFURLRef anURL);
# 201 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
CFStringRef CFURLCopyPath(CFURLRef anURL);

extern
CFStringRef CFURLCopyStrictPath(CFURLRef anURL, Boolean *isAbsolute);

extern
CFStringRef CFURLCopyFileSystemPath(CFURLRef anURL, CFURLPathStyle pathStyle);



extern
Boolean CFURLHasDirectoryPath(CFURLRef anURL);



extern
CFStringRef CFURLCopyResourceSpecifier(CFURLRef anURL);

extern
CFStringRef CFURLCopyHostName(CFURLRef anURL);

extern
SInt32 CFURLGetPortNumber(CFURLRef anURL);

extern
CFStringRef CFURLCopyUserName(CFURLRef anURL);

extern
CFStringRef CFURLCopyPassword(CFURLRef anURL);






extern
CFStringRef CFURLCopyParameterString(CFURLRef anURL, CFStringRef charactersToLeaveEscaped);

extern
CFStringRef CFURLCopyQueryString(CFURLRef anURL, CFStringRef charactersToLeaveEscaped);

extern
CFStringRef CFURLCopyFragment(CFURLRef anURL, CFStringRef charactersToLeaveEscaped);

extern
CFStringRef CFURLCopyLastPathComponent(CFURLRef url);

extern
CFStringRef CFURLCopyPathExtension(CFURLRef url);





extern
CFURLRef CFURLCreateCopyAppendingPathComponent(CFAllocatorRef allocator, CFURLRef url, CFStringRef pathComponent, Boolean isDirectory);

extern
CFURLRef CFURLCreateCopyDeletingLastPathComponent(CFAllocatorRef allocator, CFURLRef url);

extern
CFURLRef CFURLCreateCopyAppendingPathExtension(CFAllocatorRef allocator, CFURLRef url, CFStringRef extension);

extern
CFURLRef CFURLCreateCopyDeletingPathExtension(CFAllocatorRef allocator, CFURLRef url);







extern
CFIndex CFURLGetBytes(CFURLRef url, UInt8 *buffer, CFIndex bufferLength);

enum {
 kCFURLComponentScheme = 1,
 kCFURLComponentNetLocation = 2,
 kCFURLComponentPath = 3,
 kCFURLComponentResourceSpecifier = 4,

 kCFURLComponentUser = 5,
 kCFURLComponentPassword = 6,
 kCFURLComponentUserInfo = 7,
 kCFURLComponentHost = 8,
 kCFURLComponentPort = 9,
 kCFURLComponentParameterString = 10,
 kCFURLComponentQuery = 11,
 kCFURLComponentFragment = 12
};
typedef CFIndex CFURLComponentType;
# 357 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
CFRange CFURLGetByteRangeForComponent(CFURLRef url, CFURLComponentType component, CFRange *rangeIncludingSeparators);
# 367 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
CFStringRef CFURLCreateStringByReplacingPercentEscapes(CFAllocatorRef allocator, CFStringRef originalString, CFStringRef charactersToLeaveEscaped);


extern
CFStringRef CFURLCreateStringByReplacingPercentEscapesUsingEncoding(CFAllocatorRef allocator, CFStringRef origString, CFStringRef charsToLeaveEscaped, CFStringEncoding encoding);
# 387 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
CFStringRef CFURLCreateStringByAddingPercentEscapes(CFAllocatorRef allocator, CFStringRef originalString, CFStringRef charactersToLeaveUnescaped, CFStringRef legalURLCharactersToBeEscaped, CFStringEncoding encoding);
# 398 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
CFURLRef CFURLCreateFileReferenceURL(CFAllocatorRef allocator, CFURLRef url, CFErrorRef *error) ;







extern
CFURLRef CFURLCreateFilePathURL(CFAllocatorRef allocator, CFURLRef url, CFErrorRef *error) ;






struct FSRef;

extern
CFURLRef CFURLCreateFromFSRef(CFAllocatorRef allocator, const struct FSRef *fsRef);

extern
Boolean CFURLGetFSRef(CFURLRef url, struct FSRef *fsRef);
# 449 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
Boolean CFURLCopyResourcePropertyForKey(CFURLRef url, CFStringRef key, void *propertyValueTypeRefPtr, CFErrorRef *error) ;
# 460 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
CFDictionaryRef CFURLCopyResourcePropertiesForKeys(CFURLRef url, CFArrayRef keys, CFErrorRef *error) ;
# 471 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
Boolean CFURLSetResourcePropertyForKey(CFURLRef url, CFStringRef key, CFTypeRef propertyValue, CFErrorRef *error) ;
# 483 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
Boolean CFURLSetResourcePropertiesForKeys(CFURLRef url, CFDictionaryRef keyedPropertyValues, CFErrorRef *error) ;


extern
const CFStringRef kCFURLKeysOfUnsetValuesKey ;




extern
void CFURLClearResourcePropertyCacheForKey(CFURLRef url, CFStringRef key) ;



extern
void CFURLClearResourcePropertyCache(CFURLRef url) ;







extern
void CFURLSetTemporaryResourcePropertyForKey(CFURLRef url, CFStringRef key, CFTypeRef propertyValue) ;
# 520 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
Boolean CFURLResourceIsReachable(CFURLRef url, CFErrorRef *error) ;




extern
const CFStringRef kCFURLNameKey ;


extern
const CFStringRef kCFURLLocalizedNameKey ;


extern
const CFStringRef kCFURLIsRegularFileKey ;


extern
const CFStringRef kCFURLIsDirectoryKey ;


extern
const CFStringRef kCFURLIsSymbolicLinkKey ;


extern
const CFStringRef kCFURLIsVolumeKey ;


extern
const CFStringRef kCFURLIsPackageKey ;


extern
const CFStringRef kCFURLIsSystemImmutableKey ;


extern
const CFStringRef kCFURLIsUserImmutableKey ;


extern
const CFStringRef kCFURLIsHiddenKey ;


extern
const CFStringRef kCFURLHasHiddenExtensionKey ;


extern
const CFStringRef kCFURLCreationDateKey ;


extern
const CFStringRef kCFURLContentAccessDateKey ;


extern
const CFStringRef kCFURLContentModificationDateKey ;


extern
const CFStringRef kCFURLAttributeModificationDateKey ;


extern
const CFStringRef kCFURLLinkCountKey ;


extern
const CFStringRef kCFURLParentDirectoryURLKey ;


extern
const CFStringRef kCFURLVolumeURLKey ;


extern
const CFStringRef kCFURLTypeIdentifierKey ;


extern
const CFStringRef kCFURLLocalizedTypeDescriptionKey ;


extern
const CFStringRef kCFURLLabelNumberKey ;


extern
const CFStringRef kCFURLLabelColorKey ;


extern
const CFStringRef kCFURLLocalizedLabelKey ;


extern
const CFStringRef kCFURLEffectiveIconKey ;


extern
const CFStringRef kCFURLCustomIconKey ;


extern
const CFStringRef kCFURLFileResourceIdentifierKey ;


extern
const CFStringRef kCFURLVolumeIdentifierKey ;


extern
const CFStringRef kCFURLPreferredIOBlockSizeKey ;


extern
const CFStringRef kCFURLIsReadableKey ;


extern
const CFStringRef kCFURLIsWritableKey ;


extern
const CFStringRef kCFURLIsExecutableKey ;


extern
const CFStringRef kCFURLFileSecurityKey ;


extern
const CFStringRef kCFURLFileResourceTypeKey ;



extern
const CFStringRef kCFURLFileResourceTypeNamedPipe ;
extern
const CFStringRef kCFURLFileResourceTypeCharacterSpecial ;
extern
const CFStringRef kCFURLFileResourceTypeDirectory ;
extern
const CFStringRef kCFURLFileResourceTypeBlockSpecial ;
extern
const CFStringRef kCFURLFileResourceTypeRegular ;
extern
const CFStringRef kCFURLFileResourceTypeSymbolicLink ;
extern
const CFStringRef kCFURLFileResourceTypeSocket ;
extern
const CFStringRef kCFURLFileResourceTypeUnknown ;



extern
const CFStringRef kCFURLFileSizeKey ;


extern
const CFStringRef kCFURLFileAllocatedSizeKey ;


extern
const CFStringRef kCFURLTotalFileSizeKey ;


extern
const CFStringRef kCFURLTotalFileAllocatedSizeKey ;


extern
const CFStringRef kCFURLIsAliasFileKey ;


extern
const CFStringRef kCFURLIsMountTriggerKey ;







extern
const CFStringRef kCFURLVolumeLocalizedFormatDescriptionKey ;


extern
const CFStringRef kCFURLVolumeTotalCapacityKey ;


extern
const CFStringRef kCFURLVolumeAvailableCapacityKey ;


extern
const CFStringRef kCFURLVolumeResourceCountKey ;


extern
const CFStringRef kCFURLVolumeSupportsPersistentIDsKey ;


extern
const CFStringRef kCFURLVolumeSupportsSymbolicLinksKey ;


extern
const CFStringRef kCFURLVolumeSupportsHardLinksKey ;


extern
const CFStringRef kCFURLVolumeSupportsJournalingKey ;


extern
const CFStringRef kCFURLVolumeIsJournalingKey ;


extern
const CFStringRef kCFURLVolumeSupportsSparseFilesKey ;


extern
const CFStringRef kCFURLVolumeSupportsZeroRunsKey ;


extern
const CFStringRef kCFURLVolumeSupportsCaseSensitiveNamesKey ;


extern
const CFStringRef kCFURLVolumeSupportsCasePreservedNamesKey ;


extern
const CFStringRef kCFURLVolumeSupportsRootDirectoryDatesKey ;


extern
const CFStringRef kCFURLVolumeSupportsVolumeSizesKey ;


extern
const CFStringRef kCFURLVolumeSupportsRenamingKey ;


extern
const CFStringRef kCFURLVolumeSupportsAdvisoryFileLockingKey ;


extern
const CFStringRef kCFURLVolumeSupportsExtendedSecurityKey ;


extern
const CFStringRef kCFURLVolumeIsBrowsableKey ;


extern
const CFStringRef kCFURLVolumeMaximumFileSizeKey ;


extern
const CFStringRef kCFURLVolumeIsEjectableKey ;


extern
const CFStringRef kCFURLVolumeIsRemovableKey ;


extern
const CFStringRef kCFURLVolumeIsInternalKey ;


extern
const CFStringRef kCFURLVolumeIsAutomountedKey ;


extern
const CFStringRef kCFURLVolumeIsLocalKey ;


extern
const CFStringRef kCFURLVolumeIsReadOnlyKey ;


extern
const CFStringRef kCFURLVolumeCreationDateKey ;


extern
const CFStringRef kCFURLVolumeURLForRemountingKey ;


extern
const CFStringRef kCFURLVolumeUUIDStringKey ;


extern
const CFStringRef kCFURLVolumeNameKey ;


extern
const CFStringRef kCFURLVolumeLocalizedNameKey ;




extern
const CFStringRef kCFURLIsUbiquitousItemKey ;


extern
const CFStringRef kCFURLUbiquitousItemHasUnresolvedConflictsKey ;


extern
const CFStringRef kCFURLUbiquitousItemIsDownloadedKey ;


extern
const CFStringRef kCFURLUbiquitousItemIsDownloadingKey ;


extern
const CFStringRef kCFURLUbiquitousItemIsUploadedKey ;


extern
const CFStringRef kCFURLUbiquitousItemIsUploadingKey ;


extern
const CFStringRef kCFURLUbiquitousItemPercentDownloadedKey ;


extern
const CFStringRef kCFURLUbiquitousItemPercentUploadedKey ;


enum {
    kCFURLBookmarkCreationPreferFileIDResolutionMask = ( 1UL << 8 ),
    kCFURLBookmarkCreationMinimalBookmarkMask = ( 1UL << 9 ),
    kCFURLBookmarkCreationSuitableForBookmarkFile = ( 1UL << 10 ),
};
typedef CFOptionFlags CFURLBookmarkCreationOptions;

enum {
    kCFBookmarkResolutionWithoutUIMask = ( 1UL << 8 ),
    kCFBookmarkResolutionWithoutMountingMask = ( 1UL << 9 ),
};
typedef CFOptionFlags CFURLBookmarkResolutionOptions;

typedef CFOptionFlags CFURLBookmarkFileCreationOptions;
# 890 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
CFDataRef CFURLCreateBookmarkData ( CFAllocatorRef allocator, CFURLRef url, CFURLBookmarkCreationOptions options, CFArrayRef resourcePropertiesToInclude, CFURLRef relativeToURL, CFErrorRef* error ) ;
# 909 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
CFURLRef CFURLCreateByResolvingBookmarkData ( CFAllocatorRef allocator, CFDataRef bookmark, CFURLBookmarkResolutionOptions options, CFURLRef relativeToURL, CFArrayRef resourcePropertiesToInclude, Boolean* isStale, CFErrorRef* error ) ;
# 919 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
CFDictionaryRef CFURLCreateResourcePropertiesForKeysFromBookmarkData ( CFAllocatorRef allocator, CFArrayRef resourcePropertiesToReturn, CFDataRef bookmark ) ;
# 929 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
CFTypeRef CFURLCreateResourcePropertyForKeyFromBookmarkData( CFAllocatorRef allocator, CFStringRef resourcePropertyKey, CFDataRef bookmark ) ;
# 942 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
CFDataRef CFURLCreateBookmarkDataFromFile(CFAllocatorRef allocator, CFURLRef fileURL, CFErrorRef *errorRef ) ;
# 956 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
Boolean CFURLWriteBookmarkDataToFile( CFDataRef bookmarkRef, CFURLRef fileURL, CFURLBookmarkFileCreationOptions options, CFErrorRef *errorRef ) ;
# 967 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURL.h" 3
extern
CFDataRef CFURLCreateBookmarkDataFromAliasRecord ( CFAllocatorRef allocatorRef, CFDataRef aliasRecordDataRef ) ;




# 12 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStream.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFRunLoop.h" 1 3
# 13 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFRunLoop.h" 3
# 1 "/usr/include/mach/port.h" 1 3 4
# 91 "/usr/include/mach/port.h" 3 4
# 1 "/usr/include/mach/boolean.h" 1 3 4
# 73 "/usr/include/mach/boolean.h" 3 4
# 1 "/usr/include/mach/machine/boolean.h" 1 3 4
# 33 "/usr/include/mach/machine/boolean.h" 3 4
# 1 "/usr/include/mach/i386/boolean.h" 1 3 4
# 69 "/usr/include/mach/i386/boolean.h" 3 4
typedef unsigned int boolean_t;
# 34 "/usr/include/mach/machine/boolean.h" 2 3 4
# 74 "/usr/include/mach/boolean.h" 2 3 4
# 92 "/usr/include/mach/port.h" 2 3 4
# 1 "/usr/include/mach/machine/vm_types.h" 1 3 4
# 33 "/usr/include/mach/machine/vm_types.h" 3 4
# 1 "/usr/include/mach/i386/vm_types.h" 1 3 4
# 73 "/usr/include/mach/i386/vm_types.h" 3 4
# 1 "/usr/include/mach/i386/vm_param.h" 1 3 4
# 74 "/usr/include/mach/i386/vm_types.h" 2 3 4
# 93 "/usr/include/mach/i386/vm_types.h" 3 4
typedef __darwin_natural_t natural_t;
typedef int integer_t;






typedef uintptr_t vm_offset_t;
# 112 "/usr/include/mach/i386/vm_types.h" 3 4
typedef uintptr_t vm_size_t;
# 124 "/usr/include/mach/i386/vm_types.h" 3 4
typedef uint64_t mach_vm_address_t;
typedef uint64_t mach_vm_offset_t;
typedef uint64_t mach_vm_size_t;

typedef uint64_t vm_map_offset_t;
typedef uint64_t vm_map_address_t;
typedef uint64_t vm_map_size_t;
# 34 "/usr/include/mach/machine/vm_types.h" 2 3 4
# 93 "/usr/include/mach/port.h" 2 3 4
# 106 "/usr/include/mach/port.h" 3 4
typedef natural_t mach_port_name_t;
typedef mach_port_name_t *mach_port_name_array_t;
# 128 "/usr/include/mach/port.h" 3 4
typedef mach_port_name_t mach_port_t;



typedef mach_port_t *mach_port_array_t;
# 190 "/usr/include/mach/port.h" 3 4
typedef natural_t mach_port_right_t;
# 200 "/usr/include/mach/port.h" 3 4
typedef natural_t mach_port_type_t;
typedef mach_port_type_t *mach_port_type_array_t;
# 235 "/usr/include/mach/port.h" 3 4
typedef natural_t mach_port_urefs_t;
typedef integer_t mach_port_delta_t;



typedef natural_t mach_port_seqno_t;
typedef natural_t mach_port_mscount_t;
typedef natural_t mach_port_msgcount_t;
typedef natural_t mach_port_rights_t;






typedef unsigned int mach_port_srights_t;

typedef struct mach_port_status {
 mach_port_rights_t mps_pset;
 mach_port_seqno_t mps_seqno;
 mach_port_mscount_t mps_mscount;
 mach_port_msgcount_t mps_qlimit;
 mach_port_msgcount_t mps_msgcount;
 mach_port_rights_t mps_sorights;
 boolean_t mps_srights;
 boolean_t mps_pdrequest;
 boolean_t mps_nsrequest;
 natural_t mps_flags;
} mach_port_status_t;
# 275 "/usr/include/mach/port.h" 3 4
typedef struct mach_port_limits {
 mach_port_msgcount_t mpl_qlimit;
} mach_port_limits_t;

typedef integer_t *mach_port_info_t;


typedef int mach_port_flavor_t;
# 297 "/usr/include/mach/port.h" 3 4
typedef struct mach_port_qos {
 unsigned int name:1;
 unsigned int prealloc:1;
 boolean_t pad1:30;
 natural_t len;
} mach_port_qos_t;
# 14 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFRunLoop.h" 2 3




typedef struct __CFRunLoop * CFRunLoopRef;

typedef struct __CFRunLoopSource * CFRunLoopSourceRef;

typedef struct __CFRunLoopObserver * CFRunLoopObserverRef;

typedef struct __CFRunLoopTimer * CFRunLoopTimerRef;


enum {
    kCFRunLoopRunFinished = 1,
    kCFRunLoopRunStopped = 2,
    kCFRunLoopRunTimedOut = 3,
    kCFRunLoopRunHandledSource = 4
};


enum {
    kCFRunLoopEntry = (1UL << 0),
    kCFRunLoopBeforeTimers = (1UL << 1),
    kCFRunLoopBeforeSources = (1UL << 2),
    kCFRunLoopBeforeWaiting = (1UL << 5),
    kCFRunLoopAfterWaiting = (1UL << 6),
    kCFRunLoopExit = (1UL << 7),
    kCFRunLoopAllActivities = 0x0FFFFFFFU
};
typedef CFOptionFlags CFRunLoopActivity;

extern const CFStringRef kCFRunLoopDefaultMode;
extern const CFStringRef kCFRunLoopCommonModes;

extern CFTypeID CFRunLoopGetTypeID(void);

extern CFRunLoopRef CFRunLoopGetCurrent(void);
extern CFRunLoopRef CFRunLoopGetMain(void);

extern CFStringRef CFRunLoopCopyCurrentMode(CFRunLoopRef rl);

extern CFArrayRef CFRunLoopCopyAllModes(CFRunLoopRef rl);

extern void CFRunLoopAddCommonMode(CFRunLoopRef rl, CFStringRef mode);

extern CFAbsoluteTime CFRunLoopGetNextTimerFireDate(CFRunLoopRef rl, CFStringRef mode);

extern void CFRunLoopRun(void);
extern SInt32 CFRunLoopRunInMode(CFStringRef mode, CFTimeInterval seconds, Boolean returnAfterSourceHandled);
extern Boolean CFRunLoopIsWaiting(CFRunLoopRef rl);
extern void CFRunLoopWakeUp(CFRunLoopRef rl);
extern void CFRunLoopStop(CFRunLoopRef rl);


extern void CFRunLoopPerformBlock(CFRunLoopRef rl, CFTypeRef mode, void (^block)(void)) ;


extern Boolean CFRunLoopContainsSource(CFRunLoopRef rl, CFRunLoopSourceRef source, CFStringRef mode);
extern void CFRunLoopAddSource(CFRunLoopRef rl, CFRunLoopSourceRef source, CFStringRef mode);
extern void CFRunLoopRemoveSource(CFRunLoopRef rl, CFRunLoopSourceRef source, CFStringRef mode);

extern Boolean CFRunLoopContainsObserver(CFRunLoopRef rl, CFRunLoopObserverRef observer, CFStringRef mode);
extern void CFRunLoopAddObserver(CFRunLoopRef rl, CFRunLoopObserverRef observer, CFStringRef mode);
extern void CFRunLoopRemoveObserver(CFRunLoopRef rl, CFRunLoopObserverRef observer, CFStringRef mode);

extern Boolean CFRunLoopContainsTimer(CFRunLoopRef rl, CFRunLoopTimerRef timer, CFStringRef mode);
extern void CFRunLoopAddTimer(CFRunLoopRef rl, CFRunLoopTimerRef timer, CFStringRef mode);
extern void CFRunLoopRemoveTimer(CFRunLoopRef rl, CFRunLoopTimerRef timer, CFStringRef mode);

typedef struct {
    CFIndex version;
    void * info;
    const void *(*retain)(const void *info);
    void (*release)(const void *info);
    CFStringRef (*copyDescription)(const void *info);
    Boolean (*equal)(const void *info1, const void *info2);
    CFHashCode (*hash)(const void *info);
    void (*schedule)(void *info, CFRunLoopRef rl, CFStringRef mode);
    void (*cancel)(void *info, CFRunLoopRef rl, CFStringRef mode);
    void (*perform)(void *info);
} CFRunLoopSourceContext;

typedef struct {
    CFIndex version;
    void * info;
    const void *(*retain)(const void *info);
    void (*release)(const void *info);
    CFStringRef (*copyDescription)(const void *info);
    Boolean (*equal)(const void *info1, const void *info2);
    CFHashCode (*hash)(const void *info);

    mach_port_t (*getPort)(void *info);
    void * (*perform)(void *msg, CFIndex size, CFAllocatorRef allocator, void *info);




} CFRunLoopSourceContext1;

extern CFTypeID CFRunLoopSourceGetTypeID(void);

extern CFRunLoopSourceRef CFRunLoopSourceCreate(CFAllocatorRef allocator, CFIndex order, CFRunLoopSourceContext *context);

extern CFIndex CFRunLoopSourceGetOrder(CFRunLoopSourceRef source);
extern void CFRunLoopSourceInvalidate(CFRunLoopSourceRef source);
extern Boolean CFRunLoopSourceIsValid(CFRunLoopSourceRef source);
extern void CFRunLoopSourceGetContext(CFRunLoopSourceRef source, CFRunLoopSourceContext *context);
extern void CFRunLoopSourceSignal(CFRunLoopSourceRef source);

typedef struct {
    CFIndex version;
    void * info;
    const void *(*retain)(const void *info);
    void (*release)(const void *info);
    CFStringRef (*copyDescription)(const void *info);
} CFRunLoopObserverContext;

typedef void (*CFRunLoopObserverCallBack)(CFRunLoopObserverRef observer, CFRunLoopActivity activity, void *info);

extern CFTypeID CFRunLoopObserverGetTypeID(void);

extern CFRunLoopObserverRef CFRunLoopObserverCreate(CFAllocatorRef allocator, CFOptionFlags activities, Boolean repeats, CFIndex order, CFRunLoopObserverCallBack callout, CFRunLoopObserverContext *context);

extern CFRunLoopObserverRef CFRunLoopObserverCreateWithHandler(CFAllocatorRef allocator, CFOptionFlags activities, Boolean repeats, CFIndex order, void (^block) (CFRunLoopObserverRef observer, CFRunLoopActivity activity)) ;


extern CFOptionFlags CFRunLoopObserverGetActivities(CFRunLoopObserverRef observer);
extern Boolean CFRunLoopObserverDoesRepeat(CFRunLoopObserverRef observer);
extern CFIndex CFRunLoopObserverGetOrder(CFRunLoopObserverRef observer);
extern void CFRunLoopObserverInvalidate(CFRunLoopObserverRef observer);
extern Boolean CFRunLoopObserverIsValid(CFRunLoopObserverRef observer);
extern void CFRunLoopObserverGetContext(CFRunLoopObserverRef observer, CFRunLoopObserverContext *context);

typedef struct {
    CFIndex version;
    void * info;
    const void *(*retain)(const void *info);
    void (*release)(const void *info);
    CFStringRef (*copyDescription)(const void *info);
} CFRunLoopTimerContext;

typedef void (*CFRunLoopTimerCallBack)(CFRunLoopTimerRef timer, void *info);

extern CFTypeID CFRunLoopTimerGetTypeID(void);

extern CFRunLoopTimerRef CFRunLoopTimerCreate(CFAllocatorRef allocator, CFAbsoluteTime fireDate, CFTimeInterval interval, CFOptionFlags flags, CFIndex order, CFRunLoopTimerCallBack callout, CFRunLoopTimerContext *context);

extern CFRunLoopTimerRef CFRunLoopTimerCreateWithHandler(CFAllocatorRef allocator, CFAbsoluteTime fireDate, CFTimeInterval interval, CFOptionFlags flags, CFIndex order, void (^block) (CFRunLoopTimerRef timer)) ;


extern CFAbsoluteTime CFRunLoopTimerGetNextFireDate(CFRunLoopTimerRef timer);
extern void CFRunLoopTimerSetNextFireDate(CFRunLoopTimerRef timer, CFAbsoluteTime fireDate);
extern CFTimeInterval CFRunLoopTimerGetInterval(CFRunLoopTimerRef timer);
extern Boolean CFRunLoopTimerDoesRepeat(CFRunLoopTimerRef timer);
extern CFIndex CFRunLoopTimerGetOrder(CFRunLoopTimerRef timer);
extern void CFRunLoopTimerInvalidate(CFRunLoopTimerRef timer);
extern Boolean CFRunLoopTimerIsValid(CFRunLoopTimerRef timer);
extern void CFRunLoopTimerGetContext(CFRunLoopTimerRef timer, CFRunLoopTimerContext *context);


# 13 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStream.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSocket.h" 1 3
# 11 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSocket.h" 3


typedef struct __CFSocket * CFSocketRef;
# 93 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSocket.h" 3
enum {
    kCFSocketSuccess = 0,
    kCFSocketError = -1,
    kCFSocketTimeout = -2
};
typedef CFIndex CFSocketError;

typedef struct {
    SInt32 protocolFamily;
    SInt32 socketType;
    SInt32 protocol;
    CFDataRef address;
} CFSocketSignature;


enum {
    kCFSocketNoCallBack = 0,
    kCFSocketReadCallBack = 1,
    kCFSocketAcceptCallBack = 2,
    kCFSocketDataCallBack = 3,
    kCFSocketConnectCallBack = 4,
    kCFSocketWriteCallBack = 8
};
typedef CFOptionFlags CFSocketCallBackType;


enum {
    kCFSocketAutomaticallyReenableReadCallBack = 1,
    kCFSocketAutomaticallyReenableAcceptCallBack = 2,
    kCFSocketAutomaticallyReenableDataCallBack = 3,
    kCFSocketAutomaticallyReenableWriteCallBack = 8,

    kCFSocketLeaveErrors = 64,

    kCFSocketCloseOnInvalidate = 128
};

typedef void (*CFSocketCallBack)(CFSocketRef s, CFSocketCallBackType type, CFDataRef address, const void *data, void *info);


typedef struct {
    CFIndex version;
    void * info;
    const void *(*retain)(const void *info);
    void (*release)(const void *info);
    CFStringRef (*copyDescription)(const void *info);
} CFSocketContext;




typedef int CFSocketNativeHandle;


extern CFTypeID CFSocketGetTypeID(void);

extern CFSocketRef CFSocketCreate(CFAllocatorRef allocator, SInt32 protocolFamily, SInt32 socketType, SInt32 protocol, CFOptionFlags callBackTypes, CFSocketCallBack callout, const CFSocketContext *context);
extern CFSocketRef CFSocketCreateWithNative(CFAllocatorRef allocator, CFSocketNativeHandle sock, CFOptionFlags callBackTypes, CFSocketCallBack callout, const CFSocketContext *context);
extern CFSocketRef CFSocketCreateWithSocketSignature(CFAllocatorRef allocator, const CFSocketSignature *signature, CFOptionFlags callBackTypes, CFSocketCallBack callout, const CFSocketContext *context);
extern CFSocketRef CFSocketCreateConnectedToSocketSignature(CFAllocatorRef allocator, const CFSocketSignature *signature, CFOptionFlags callBackTypes, CFSocketCallBack callout, const CFSocketContext *context, CFTimeInterval timeout);


extern CFSocketError CFSocketSetAddress(CFSocketRef s, CFDataRef address);
extern CFSocketError CFSocketConnectToAddress(CFSocketRef s, CFDataRef address, CFTimeInterval timeout);
extern void CFSocketInvalidate(CFSocketRef s);

extern Boolean CFSocketIsValid(CFSocketRef s);
extern CFDataRef CFSocketCopyAddress(CFSocketRef s);
extern CFDataRef CFSocketCopyPeerAddress(CFSocketRef s);
extern void CFSocketGetContext(CFSocketRef s, CFSocketContext *context);
extern CFSocketNativeHandle CFSocketGetNative(CFSocketRef s);

extern CFRunLoopSourceRef CFSocketCreateRunLoopSource(CFAllocatorRef allocator, CFSocketRef s, CFIndex order);

extern CFOptionFlags CFSocketGetSocketFlags(CFSocketRef s);
extern void CFSocketSetSocketFlags(CFSocketRef s, CFOptionFlags flags);
extern void CFSocketDisableCallBacks(CFSocketRef s, CFOptionFlags callBackTypes);
extern void CFSocketEnableCallBacks(CFSocketRef s, CFOptionFlags callBackTypes);



extern CFSocketError CFSocketSendData(CFSocketRef s, CFDataRef address, CFDataRef data, CFTimeInterval timeout);
# 193 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSocket.h" 3
extern CFSocketError CFSocketRegisterValue(const CFSocketSignature *nameServerSignature, CFTimeInterval timeout, CFStringRef name, CFPropertyListRef value);
extern CFSocketError CFSocketCopyRegisteredValue(const CFSocketSignature *nameServerSignature, CFTimeInterval timeout, CFStringRef name, CFPropertyListRef *value, CFDataRef *nameServerAddress);

extern CFSocketError CFSocketRegisterSocketSignature(const CFSocketSignature *nameServerSignature, CFTimeInterval timeout, CFStringRef name, const CFSocketSignature *signature);
extern CFSocketError CFSocketCopyRegisteredSocketSignature(const CFSocketSignature *nameServerSignature, CFTimeInterval timeout, CFStringRef name, CFSocketSignature *signature, CFDataRef *nameServerAddress);

extern CFSocketError CFSocketUnregister(const CFSocketSignature *nameServerSignature, CFTimeInterval timeout, CFStringRef name);

extern void CFSocketSetDefaultNameRegistryPortNumber(UInt16 port);
extern UInt16 CFSocketGetDefaultNameRegistryPortNumber(void);


extern const CFStringRef kCFSocketCommandKey;
extern const CFStringRef kCFSocketNameKey;
extern const CFStringRef kCFSocketValueKey;
extern const CFStringRef kCFSocketResultKey;
extern const CFStringRef kCFSocketErrorKey;
extern const CFStringRef kCFSocketRegisterCommand;
extern const CFStringRef kCFSocketRetrieveCommand;


# 14 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStream.h" 2 3




enum {
    kCFStreamStatusNotOpen = 0,
    kCFStreamStatusOpening,
    kCFStreamStatusOpen,
    kCFStreamStatusReading,
    kCFStreamStatusWriting,
    kCFStreamStatusAtEnd,
    kCFStreamStatusClosed,
    kCFStreamStatusError
};
typedef CFIndex CFStreamStatus;

enum {
    kCFStreamEventNone = 0,
    kCFStreamEventOpenCompleted = 1,
    kCFStreamEventHasBytesAvailable = 2,
    kCFStreamEventCanAcceptBytes = 4,
    kCFStreamEventErrorOccurred = 8,
    kCFStreamEventEndEncountered = 16
};
typedef CFOptionFlags CFStreamEventType;

typedef struct {
    CFIndex version;
    void *info;
    void *(*retain)(void *info);
    void (*release)(void *info);
    CFStringRef (*copyDescription)(void *info);
} CFStreamClientContext;

typedef struct __CFReadStream * CFReadStreamRef;
typedef struct __CFWriteStream * CFWriteStreamRef;

typedef void (*CFReadStreamClientCallBack)(CFReadStreamRef stream, CFStreamEventType type, void *clientCallBackInfo);
typedef void (*CFWriteStreamClientCallBack)(CFWriteStreamRef stream, CFStreamEventType type, void *clientCallBackInfo);

extern
CFTypeID CFReadStreamGetTypeID(void);
extern
CFTypeID CFWriteStreamGetTypeID(void);




extern
const CFStringRef kCFStreamPropertyDataWritten;


extern
CFReadStreamRef CFReadStreamCreateWithBytesNoCopy(CFAllocatorRef alloc, const UInt8 *bytes, CFIndex length, CFAllocatorRef bytesDeallocator);


extern
CFWriteStreamRef CFWriteStreamCreateWithBuffer(CFAllocatorRef alloc, UInt8 *buffer, CFIndex bufferCapacity);


extern
CFWriteStreamRef CFWriteStreamCreateWithAllocatedBuffers(CFAllocatorRef alloc, CFAllocatorRef bufferAllocator);


extern
CFReadStreamRef CFReadStreamCreateWithFile(CFAllocatorRef alloc, CFURLRef fileURL);
extern
CFWriteStreamRef CFWriteStreamCreateWithFile(CFAllocatorRef alloc, CFURLRef fileURL);
extern
void CFStreamCreateBoundPair(CFAllocatorRef alloc, CFReadStreamRef *readStream, CFWriteStreamRef *writeStream, CFIndex transferBufferSize);


extern
const CFStringRef kCFStreamPropertyAppendToFile;

extern
const CFStringRef kCFStreamPropertyFileCurrentOffset;





extern
const CFStringRef kCFStreamPropertySocketNativeHandle;


extern
const CFStringRef kCFStreamPropertySocketRemoteHostName;


extern
const CFStringRef kCFStreamPropertySocketRemotePortNumber;


extern
void CFStreamCreatePairWithSocket(CFAllocatorRef alloc, CFSocketNativeHandle sock, CFReadStreamRef *readStream, CFWriteStreamRef *writeStream);
extern
void CFStreamCreatePairWithSocketToHost(CFAllocatorRef alloc, CFStringRef host, UInt32 port, CFReadStreamRef *readStream, CFWriteStreamRef *writeStream);
extern
void CFStreamCreatePairWithPeerSocketSignature(CFAllocatorRef alloc, const CFSocketSignature *signature, CFReadStreamRef *readStream, CFWriteStreamRef *writeStream);



extern
CFStreamStatus CFReadStreamGetStatus(CFReadStreamRef stream);
extern
CFStreamStatus CFWriteStreamGetStatus(CFWriteStreamRef stream);


extern
CFErrorRef CFReadStreamCopyError(CFReadStreamRef stream) ;
extern
CFErrorRef CFWriteStreamCopyError(CFWriteStreamRef stream) ;






extern
Boolean CFReadStreamOpen(CFReadStreamRef stream);
extern
Boolean CFWriteStreamOpen(CFWriteStreamRef stream);




extern
void CFReadStreamClose(CFReadStreamRef stream);
extern
void CFWriteStreamClose(CFWriteStreamRef stream);



extern
Boolean CFReadStreamHasBytesAvailable(CFReadStreamRef stream);
# 158 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStream.h" 3
extern
CFIndex CFReadStreamRead(CFReadStreamRef stream, UInt8 *buffer, CFIndex bufferLength);
# 170 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStream.h" 3
extern
const UInt8 *CFReadStreamGetBuffer(CFReadStreamRef stream, CFIndex maxBytesToRead, CFIndex *numBytesRead);



extern
Boolean CFWriteStreamCanAcceptBytes(CFWriteStreamRef stream);






extern
CFIndex CFWriteStreamWrite(CFWriteStreamRef stream, const UInt8 *buffer, CFIndex bufferLength);
# 194 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStream.h" 3
extern
CFTypeRef CFReadStreamCopyProperty(CFReadStreamRef stream, CFStringRef propertyName);
extern
CFTypeRef CFWriteStreamCopyProperty(CFWriteStreamRef stream, CFStringRef propertyName);



extern
Boolean CFReadStreamSetProperty(CFReadStreamRef stream, CFStringRef propertyName, CFTypeRef propertyValue);
extern
Boolean CFWriteStreamSetProperty(CFWriteStreamRef stream, CFStringRef propertyName, CFTypeRef propertyValue);
# 223 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStream.h" 3
extern
Boolean CFReadStreamSetClient(CFReadStreamRef stream, CFOptionFlags streamEvents, CFReadStreamClientCallBack clientCB, CFStreamClientContext *clientContext);
extern
Boolean CFWriteStreamSetClient(CFWriteStreamRef stream, CFOptionFlags streamEvents, CFWriteStreamClientCallBack clientCB, CFStreamClientContext *clientContext);

extern
void CFReadStreamScheduleWithRunLoop(CFReadStreamRef stream, CFRunLoopRef runLoop, CFStringRef runLoopMode);
extern
void CFWriteStreamScheduleWithRunLoop(CFWriteStreamRef stream, CFRunLoopRef runLoop, CFStringRef runLoopMode);

extern
void CFReadStreamUnscheduleFromRunLoop(CFReadStreamRef stream, CFRunLoopRef runLoop, CFStringRef runLoopMode);
extern
void CFWriteStreamUnscheduleFromRunLoop(CFWriteStreamRef stream, CFRunLoopRef runLoop, CFStringRef runLoopMode);



enum {
    kCFStreamErrorDomainCustom = -1,
    kCFStreamErrorDomainPOSIX = 1,
    kCFStreamErrorDomainMacOSStatus
};
typedef CFIndex CFStreamErrorDomain;

typedef struct {
    CFIndex domain;
    SInt32 error;
} CFStreamError;
extern
CFStreamError CFReadStreamGetError(CFReadStreamRef stream);
extern
CFStreamError CFWriteStreamGetError(CFWriteStreamRef stream);



# 14 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFPropertyList.h" 2 3




enum {
    kCFPropertyListImmutable = 0,
    kCFPropertyListMutableContainers,
    kCFPropertyListMutableContainersAndLeaves
};
typedef CFOptionFlags CFPropertyListMutabilityOptions;
# 35 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFPropertyList.h" 3
extern
CFPropertyListRef CFPropertyListCreateFromXMLData(CFAllocatorRef allocator, CFDataRef xmlData, CFOptionFlags mutabilityOption, CFStringRef *errorString);
# 50 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFPropertyList.h" 3
extern
CFDataRef CFPropertyListCreateXMLData(CFAllocatorRef allocator, CFPropertyListRef propertyList);







extern
CFPropertyListRef CFPropertyListCreateDeepCopy(CFAllocatorRef allocator, CFPropertyListRef propertyList, CFOptionFlags mutabilityOption);

enum {
    kCFPropertyListOpenStepFormat = 1,
    kCFPropertyListXMLFormat_v1_0 = 100,
    kCFPropertyListBinaryFormat_v1_0 = 200
};
typedef CFIndex CFPropertyListFormat;






extern
Boolean CFPropertyListIsValid(CFPropertyListRef plist, CFPropertyListFormat format);
# 89 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFPropertyList.h" 3
extern
CFIndex CFPropertyListWriteToStream(CFPropertyListRef propertyList, CFWriteStreamRef stream, CFPropertyListFormat format, CFStringRef *errorString);
# 104 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFPropertyList.h" 3
extern
CFPropertyListRef CFPropertyListCreateFromStream(CFAllocatorRef allocator, CFReadStreamRef stream, CFIndex streamLength, CFOptionFlags mutabilityOption, CFPropertyListFormat *format, CFStringRef *errorString);




enum {
    kCFPropertyListReadCorruptError = 3840,
    kCFPropertyListReadUnknownVersionError = 3841,
    kCFPropertyListReadStreamError = 3842,
    kCFPropertyListWriteStreamError = 3851,
};




extern
CFPropertyListRef CFPropertyListCreateWithData(CFAllocatorRef allocator, CFDataRef data, CFOptionFlags options, CFPropertyListFormat *format, CFErrorRef *error) ;





extern
CFPropertyListRef CFPropertyListCreateWithStream(CFAllocatorRef allocator, CFReadStreamRef stream, CFIndex streamLength, CFOptionFlags options, CFPropertyListFormat *format, CFErrorRef *error) ;



extern
CFIndex CFPropertyListWrite(CFPropertyListRef propertyList, CFWriteStreamRef stream, CFPropertyListFormat format, CFOptionFlags options, CFErrorRef *error) ;





extern
CFDataRef CFPropertyListCreateData(CFAllocatorRef allocator, CFPropertyListRef propertyList, CFPropertyListFormat format, CFOptionFlags options, CFErrorRef *error) ;



# 56 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 1 3
# 14 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3

# 25 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
typedef const void * (*CFSetRetainCallBack)(CFAllocatorRef allocator, const void *value);







typedef void (*CFSetReleaseCallBack)(CFAllocatorRef allocator, const void *value);







typedef CFStringRef (*CFSetCopyDescriptionCallBack)(const void *value);
# 50 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
typedef Boolean (*CFSetEqualCallBack)(const void *value1, const void *value2);







typedef CFHashCode (*CFSetHashCallBack)(const void *value);
# 84 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
typedef struct {
    CFIndex version;
    CFSetRetainCallBack retain;
    CFSetReleaseCallBack release;
    CFSetCopyDescriptionCallBack copyDescription;
    CFSetEqualCallBack equal;
    CFSetHashCallBack hash;
} CFSetCallBacks;






extern
const CFSetCallBacks kCFTypeSetCallBacks;







extern
const CFSetCallBacks kCFCopyStringSetCallBacks;
# 118 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
typedef void (*CFSetApplierFunction)(const void *value, void *context);





typedef const struct __CFSet * CFSetRef;





typedef struct __CFSet * CFMutableSetRef;





extern
CFTypeID CFSetGetTypeID(void);
# 185 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
extern
CFSetRef CFSetCreate(CFAllocatorRef allocator, const void **values, CFIndex numValues, const CFSetCallBacks *callBacks);
# 206 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
extern
CFSetRef CFSetCreateCopy(CFAllocatorRef allocator, CFSetRef theSet);
# 252 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
extern
CFMutableSetRef CFSetCreateMutable(CFAllocatorRef allocator, CFIndex capacity, const CFSetCallBacks *callBacks);
# 282 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
extern
CFMutableSetRef CFSetCreateMutableCopy(CFAllocatorRef allocator, CFIndex capacity, CFSetRef theSet);
# 292 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
extern
CFIndex CFSetGetCount(CFSetRef theSet);
# 310 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
extern
CFIndex CFSetGetCountOfValue(CFSetRef theSet, const void *value);
# 326 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
extern
Boolean CFSetContainsValue(CFSetRef theSet, const void *value);
# 341 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
extern
const void *CFSetGetValue(CFSetRef theSet, const void *value);
# 365 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
extern
Boolean CFSetGetValueIfPresent(CFSetRef theSet, const void *candidate, const void **value);
# 379 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
extern
void CFSetGetValues(CFSetRef theSet, const void **values);
# 399 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
extern
void CFSetApplyFunction(CFSetRef theSet, CFSetApplierFunction applier, void *context);
# 414 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
extern
void CFSetAddValue(CFMutableSetRef theSet, const void *value);
# 433 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
extern
void CFSetReplaceValue(CFMutableSetRef theSet, const void *value);
# 453 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
extern
void CFSetSetValue(CFMutableSetRef theSet, const void *value);
# 468 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
extern
void CFSetRemoveValue(CFMutableSetRef theSet, const void *value);
# 478 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFSet.h" 3
extern
void CFSetRemoveAllValues(CFMutableSetRef theSet);


# 57 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3

# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStringEncodingExt.h" 1 3
# 10 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStringEncodingExt.h" 3


enum {

    kCFStringEncodingMacJapanese = 1,
    kCFStringEncodingMacChineseTrad = 2,
    kCFStringEncodingMacKorean = 3,
    kCFStringEncodingMacArabic = 4,
    kCFStringEncodingMacHebrew = 5,
    kCFStringEncodingMacGreek = 6,
    kCFStringEncodingMacCyrillic = 7,
    kCFStringEncodingMacDevanagari = 9,
    kCFStringEncodingMacGurmukhi = 10,
    kCFStringEncodingMacGujarati = 11,
    kCFStringEncodingMacOriya = 12,
    kCFStringEncodingMacBengali = 13,
    kCFStringEncodingMacTamil = 14,
    kCFStringEncodingMacTelugu = 15,
    kCFStringEncodingMacKannada = 16,
    kCFStringEncodingMacMalayalam = 17,
    kCFStringEncodingMacSinhalese = 18,
    kCFStringEncodingMacBurmese = 19,
    kCFStringEncodingMacKhmer = 20,
    kCFStringEncodingMacThai = 21,
    kCFStringEncodingMacLaotian = 22,
    kCFStringEncodingMacGeorgian = 23,
    kCFStringEncodingMacArmenian = 24,
    kCFStringEncodingMacChineseSimp = 25,
    kCFStringEncodingMacTibetan = 26,
    kCFStringEncodingMacMongolian = 27,
    kCFStringEncodingMacEthiopic = 28,
    kCFStringEncodingMacCentralEurRoman = 29,
    kCFStringEncodingMacVietnamese = 30,
    kCFStringEncodingMacExtArabic = 31,

    kCFStringEncodingMacSymbol = 33,
    kCFStringEncodingMacDingbats = 34,
    kCFStringEncodingMacTurkish = 35,
    kCFStringEncodingMacCroatian = 36,
    kCFStringEncodingMacIcelandic = 37,
    kCFStringEncodingMacRomanian = 38,
    kCFStringEncodingMacCeltic = 39,
    kCFStringEncodingMacGaelic = 40,

    kCFStringEncodingMacFarsi = 0x8C,

    kCFStringEncodingMacUkrainian = 0x98,

    kCFStringEncodingMacInuit = 0xEC,
    kCFStringEncodingMacVT100 = 0xFC,

    kCFStringEncodingMacHFS = 0xFF,






    kCFStringEncodingISOLatin2 = 0x0202,
    kCFStringEncodingISOLatin3 = 0x0203,
    kCFStringEncodingISOLatin4 = 0x0204,
    kCFStringEncodingISOLatinCyrillic = 0x0205,
    kCFStringEncodingISOLatinArabic = 0x0206,
    kCFStringEncodingISOLatinGreek = 0x0207,
    kCFStringEncodingISOLatinHebrew = 0x0208,
    kCFStringEncodingISOLatin5 = 0x0209,
    kCFStringEncodingISOLatin6 = 0x020A,
    kCFStringEncodingISOLatinThai = 0x020B,
    kCFStringEncodingISOLatin7 = 0x020D,
    kCFStringEncodingISOLatin8 = 0x020E,
    kCFStringEncodingISOLatin9 = 0x020F,
    kCFStringEncodingISOLatin10 = 0x0210,


    kCFStringEncodingDOSLatinUS = 0x0400,
    kCFStringEncodingDOSGreek = 0x0405,
    kCFStringEncodingDOSBalticRim = 0x0406,
    kCFStringEncodingDOSLatin1 = 0x0410,
    kCFStringEncodingDOSGreek1 = 0x0411,
    kCFStringEncodingDOSLatin2 = 0x0412,
    kCFStringEncodingDOSCyrillic = 0x0413,
    kCFStringEncodingDOSTurkish = 0x0414,
    kCFStringEncodingDOSPortuguese = 0x0415,
    kCFStringEncodingDOSIcelandic = 0x0416,
    kCFStringEncodingDOSHebrew = 0x0417,
    kCFStringEncodingDOSCanadianFrench = 0x0418,
    kCFStringEncodingDOSArabic = 0x0419,
    kCFStringEncodingDOSNordic = 0x041A,
    kCFStringEncodingDOSRussian = 0x041B,
    kCFStringEncodingDOSGreek2 = 0x041C,
    kCFStringEncodingDOSThai = 0x041D,
    kCFStringEncodingDOSJapanese = 0x0420,
    kCFStringEncodingDOSChineseSimplif = 0x0421,
    kCFStringEncodingDOSKorean = 0x0422,
    kCFStringEncodingDOSChineseTrad = 0x0423,

    kCFStringEncodingWindowsLatin2 = 0x0501,
    kCFStringEncodingWindowsCyrillic = 0x0502,
    kCFStringEncodingWindowsGreek = 0x0503,
    kCFStringEncodingWindowsLatin5 = 0x0504,
    kCFStringEncodingWindowsHebrew = 0x0505,
    kCFStringEncodingWindowsArabic = 0x0506,
    kCFStringEncodingWindowsBalticRim = 0x0507,
    kCFStringEncodingWindowsVietnamese = 0x0508,
    kCFStringEncodingWindowsKoreanJohab = 0x0510,



    kCFStringEncodingANSEL = 0x0601,
    kCFStringEncodingJIS_X0201_76 = 0x0620,
    kCFStringEncodingJIS_X0208_83 = 0x0621,
    kCFStringEncodingJIS_X0208_90 = 0x0622,
    kCFStringEncodingJIS_X0212_90 = 0x0623,
    kCFStringEncodingJIS_C6226_78 = 0x0624,

    kCFStringEncodingShiftJIS_X0213 = 0x0628,

    kCFStringEncodingShiftJIS_X0213_MenKuTen = 0x0629,
    kCFStringEncodingGB_2312_80 = 0x0630,
    kCFStringEncodingGBK_95 = 0x0631,
    kCFStringEncodingGB_18030_2000 = 0x0632,
    kCFStringEncodingKSC_5601_87 = 0x0640,
    kCFStringEncodingKSC_5601_92_Johab = 0x0641,
    kCFStringEncodingCNS_11643_92_P1 = 0x0651,
    kCFStringEncodingCNS_11643_92_P2 = 0x0652,
    kCFStringEncodingCNS_11643_92_P3 = 0x0653,


    kCFStringEncodingISO_2022_JP = 0x0820,
    kCFStringEncodingISO_2022_JP_2 = 0x0821,
    kCFStringEncodingISO_2022_JP_1 = 0x0822,
    kCFStringEncodingISO_2022_JP_3 = 0x0823,
    kCFStringEncodingISO_2022_CN = 0x0830,
    kCFStringEncodingISO_2022_CN_EXT = 0x0831,
    kCFStringEncodingISO_2022_KR = 0x0840,


    kCFStringEncodingEUC_JP = 0x0920,
    kCFStringEncodingEUC_CN = 0x0930,
    kCFStringEncodingEUC_TW = 0x0931,
    kCFStringEncodingEUC_KR = 0x0940,


    kCFStringEncodingShiftJIS = 0x0A01,
    kCFStringEncodingKOI8_R = 0x0A02,
    kCFStringEncodingBig5 = 0x0A03,
    kCFStringEncodingMacRomanLatin1 = 0x0A04,
    kCFStringEncodingHZ_GB_2312 = 0x0A05,
    kCFStringEncodingBig5_HKSCS_1999 = 0x0A06,
    kCFStringEncodingVISCII = 0x0A07,
    kCFStringEncodingKOI8_U = 0x0A08,
    kCFStringEncodingBig5_E = 0x0A09,



    kCFStringEncodingNextStepJapanese = 0x0B02,


    kCFStringEncodingEBCDIC_US = 0x0C01,
    kCFStringEncodingEBCDIC_CP037 = 0x0C02,


    kCFStringEncodingUTF7 = 0x04000100,
    kCFStringEncodingUTF7_IMAP = 0x0A10,



    kCFStringEncodingShiftJIS_X0213_00 = 0x0628
};
typedef CFIndex CFStringEncodings;


# 59 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3

# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 1 3
# 15 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3

# 27 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3
typedef const void * (*CFTreeRetainCallBack)(const void *info);







typedef void (*CFTreeReleaseCallBack)(const void *info);
# 44 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3
typedef CFStringRef (*CFTreeCopyDescriptionCallBack)(const void *info);
# 63 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3
typedef struct {
    CFIndex version;
    void * info;
    CFTreeRetainCallBack retain;
    CFTreeReleaseCallBack release;
    CFTreeCopyDescriptionCallBack copyDescription;
} CFTreeContext;
# 79 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3
typedef void (*CFTreeApplierFunction)(const void *value, void *context);





typedef struct __CFTree * CFTreeRef;





extern
CFTypeID CFTreeGetTypeID(void);
# 111 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3
extern
CFTreeRef CFTreeCreate(CFAllocatorRef allocator, const CFTreeContext *context);
# 121 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3
extern
CFTreeRef CFTreeGetParent(CFTreeRef tree);
# 131 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3
extern
CFTreeRef CFTreeGetNextSibling(CFTreeRef tree);
# 141 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3
extern
CFTreeRef CFTreeGetFirstChild(CFTreeRef tree);
# 155 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3
extern
void CFTreeGetContext(CFTreeRef tree, CFTreeContext *context);
# 165 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3
extern
CFIndex CFTreeGetChildCount(CFTreeRef tree);
# 178 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3
extern
CFTreeRef CFTreeGetChildAtIndex(CFTreeRef tree, CFIndex idx);
# 191 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3
extern
void CFTreeGetChildren(CFTreeRef tree, CFTreeRef *children);
# 212 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3
extern
void CFTreeApplyFunctionToChildren(CFTreeRef tree, CFTreeApplierFunction applier, void *context);
# 222 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3
extern
CFTreeRef CFTreeFindRoot(CFTreeRef tree);
# 239 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3
extern
void CFTreeSetContext(CFTreeRef tree, const CFTreeContext *context);
# 252 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3
extern
void CFTreePrependChild(CFTreeRef tree, CFTreeRef newChild);
# 265 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3
extern
void CFTreeAppendChild(CFTreeRef tree, CFTreeRef newChild);
# 280 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3
extern
void CFTreeInsertSibling(CFTreeRef tree, CFTreeRef newSibling);







extern
void CFTreeRemove(CFTreeRef tree);







extern
void CFTreeRemoveAllChildren(CFTreeRef tree);
# 318 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFTree.h" 3
extern
void CFTreeSortChildren(CFTreeRef tree, CFComparatorFunction comparator, void *context);


# 61 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3

# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURLAccess.h" 1 3
# 16 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURLAccess.h" 3

# 42 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURLAccess.h" 3
extern
Boolean CFURLCreateDataAndPropertiesFromResource(CFAllocatorRef alloc, CFURLRef url, CFDataRef *resourceData, CFDictionaryRef *properties, CFArrayRef desiredProperties, SInt32 *errorCode) ;
# 53 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURLAccess.h" 3
extern
Boolean CFURLWriteDataAndPropertiesToResource(CFURLRef url, CFDataRef dataToWrite, CFDictionaryRef propertiesToWrite, SInt32 *errorCode) ;



extern
Boolean CFURLDestroyResource(CFURLRef url, SInt32 *errorCode) ;



extern
CFTypeRef CFURLCreatePropertyFromResource(CFAllocatorRef alloc, CFURLRef url, CFStringRef property, SInt32 *errorCode) ;



enum {
    kCFURLUnknownError = -10,
    kCFURLUnknownSchemeError = -11,
    kCFURLResourceNotFoundError = -12,
    kCFURLResourceAccessViolationError = -13,
    kCFURLRemoteHostUnavailableError = -14,
    kCFURLImproperArgumentsError = -15,
    kCFURLUnknownPropertyKeyError = -16,
    kCFURLPropertyKeyUnavailableError = -17,
    kCFURLTimeoutError = -18
};
typedef CFIndex CFURLError;



extern
const CFStringRef kCFURLFileExists ;
extern
const CFStringRef kCFURLFileDirectoryContents ;
extern
const CFStringRef kCFURLFileLength ;
extern
const CFStringRef kCFURLFileLastModificationTime ;
extern
const CFStringRef kCFURLFilePOSIXMode ;
extern
const CFStringRef kCFURLFileOwnerID ;
extern
const CFStringRef kCFURLHTTPStatusCode ;
extern
const CFStringRef kCFURLHTTPStatusLine ;
# 111 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURLAccess.h" 3

# 63 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFUUID.h" 1 3
# 11 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFUUID.h" 3


typedef const struct __CFUUID * CFUUIDRef;

typedef struct {
    UInt8 byte0;
    UInt8 byte1;
    UInt8 byte2;
    UInt8 byte3;
    UInt8 byte4;
    UInt8 byte5;
    UInt8 byte6;
    UInt8 byte7;
    UInt8 byte8;
    UInt8 byte9;
    UInt8 byte10;
    UInt8 byte11;
    UInt8 byte12;
    UInt8 byte13;
    UInt8 byte14;
    UInt8 byte15;
} CFUUIDBytes;






extern
CFTypeID CFUUIDGetTypeID(void);

extern
CFUUIDRef CFUUIDCreate(CFAllocatorRef alloc);


extern
CFUUIDRef CFUUIDCreateWithBytes(CFAllocatorRef alloc, UInt8 byte0, UInt8 byte1, UInt8 byte2, UInt8 byte3, UInt8 byte4, UInt8 byte5, UInt8 byte6, UInt8 byte7, UInt8 byte8, UInt8 byte9, UInt8 byte10, UInt8 byte11, UInt8 byte12, UInt8 byte13, UInt8 byte14, UInt8 byte15);


extern
CFUUIDRef CFUUIDCreateFromString(CFAllocatorRef alloc, CFStringRef uuidStr);


extern
CFStringRef CFUUIDCreateString(CFAllocatorRef alloc, CFUUIDRef uuid);


extern
CFUUIDRef CFUUIDGetConstantUUIDWithBytes(CFAllocatorRef alloc, UInt8 byte0, UInt8 byte1, UInt8 byte2, UInt8 byte3, UInt8 byte4, UInt8 byte5, UInt8 byte6, UInt8 byte7, UInt8 byte8, UInt8 byte9, UInt8 byte10, UInt8 byte11, UInt8 byte12, UInt8 byte13, UInt8 byte14, UInt8 byte15);


extern
CFUUIDBytes CFUUIDGetUUIDBytes(CFUUIDRef uuid);

extern
CFUUIDRef CFUUIDCreateFromUUIDBytes(CFAllocatorRef alloc, CFUUIDBytes bytes);


# 64 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3


# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBundle.h" 1 3
# 15 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBundle.h" 3


typedef struct __CFBundle *CFBundleRef;
typedef struct __CFBundle *CFPlugInRef;


extern
const CFStringRef kCFBundleInfoDictionaryVersionKey;

extern
const CFStringRef kCFBundleExecutableKey;

extern
const CFStringRef kCFBundleIdentifierKey;

extern
const CFStringRef kCFBundleVersionKey;



extern
const CFStringRef kCFBundleDevelopmentRegionKey;

extern
const CFStringRef kCFBundleNameKey;

extern
const CFStringRef kCFBundleLocalizationsKey;




extern
CFBundleRef CFBundleGetMainBundle(void);

extern
CFBundleRef CFBundleGetBundleWithIdentifier(CFStringRef bundleID);







extern
CFArrayRef CFBundleGetAllBundles(void);





extern
CFTypeID CFBundleGetTypeID(void);

extern
CFBundleRef CFBundleCreate(CFAllocatorRef allocator, CFURLRef bundleURL);


extern
CFArrayRef CFBundleCreateBundlesFromDirectory(CFAllocatorRef allocator, CFURLRef directoryURL, CFStringRef bundleType);





extern
CFURLRef CFBundleCopyBundleURL(CFBundleRef bundle);

extern
CFTypeRef CFBundleGetValueForInfoDictionaryKey(CFBundleRef bundle, CFStringRef key);



extern
CFDictionaryRef CFBundleGetInfoDictionary(CFBundleRef bundle);



extern
CFDictionaryRef CFBundleGetLocalInfoDictionary(CFBundleRef bundle);


extern
void CFBundleGetPackageInfo(CFBundleRef bundle, UInt32 *packageType, UInt32 *packageCreator);

extern
CFStringRef CFBundleGetIdentifier(CFBundleRef bundle);

extern
UInt32 CFBundleGetVersionNumber(CFBundleRef bundle);

extern
CFStringRef CFBundleGetDevelopmentRegion(CFBundleRef bundle);

extern
CFURLRef CFBundleCopySupportFilesDirectoryURL(CFBundleRef bundle);

extern
CFURLRef CFBundleCopyResourcesDirectoryURL(CFBundleRef bundle);

extern
CFURLRef CFBundleCopyPrivateFrameworksURL(CFBundleRef bundle);

extern
CFURLRef CFBundleCopySharedFrameworksURL(CFBundleRef bundle);

extern
CFURLRef CFBundleCopySharedSupportURL(CFBundleRef bundle);

extern
CFURLRef CFBundleCopyBuiltInPlugInsURL(CFBundleRef bundle);






extern
CFDictionaryRef CFBundleCopyInfoDictionaryInDirectory(CFURLRef bundleURL);

extern
Boolean CFBundleGetPackageInfoInDirectory(CFURLRef url, UInt32 *packageType, UInt32 *packageCreator);



extern
CFURLRef CFBundleCopyResourceURL(CFBundleRef bundle, CFStringRef resourceName, CFStringRef resourceType, CFStringRef subDirName);

extern
CFArrayRef CFBundleCopyResourceURLsOfType(CFBundleRef bundle, CFStringRef resourceType, CFStringRef subDirName);

extern
CFStringRef CFBundleCopyLocalizedString(CFBundleRef bundle, CFStringRef key, CFStringRef value, CFStringRef tableName) __attribute__((format_arg(2)));
# 164 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBundle.h" 3
extern
CFURLRef CFBundleCopyResourceURLInDirectory(CFURLRef bundleURL, CFStringRef resourceName, CFStringRef resourceType, CFStringRef subDirName);

extern
CFArrayRef CFBundleCopyResourceURLsOfTypeInDirectory(CFURLRef bundleURL, CFStringRef resourceType, CFStringRef subDirName);






extern
CFArrayRef CFBundleCopyBundleLocalizations(CFBundleRef bundle);


extern
CFArrayRef CFBundleCopyPreferredLocalizationsFromArray(CFArrayRef locArray);






extern
CFArrayRef CFBundleCopyLocalizationsForPreferences(CFArrayRef locArray, CFArrayRef prefArray);
# 198 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBundle.h" 3
extern
CFURLRef CFBundleCopyResourceURLForLocalization(CFBundleRef bundle, CFStringRef resourceName, CFStringRef resourceType, CFStringRef subDirName, CFStringRef localizationName);

extern
CFArrayRef CFBundleCopyResourceURLsOfTypeForLocalization(CFBundleRef bundle, CFStringRef resourceType, CFStringRef subDirName, CFStringRef localizationName);
# 212 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBundle.h" 3
extern
CFDictionaryRef CFBundleCopyInfoDictionaryForURL(CFURLRef url);





extern
CFArrayRef CFBundleCopyLocalizationsForURL(CFURLRef url);






extern
CFArrayRef CFBundleCopyExecutableArchitecturesForURL(CFURLRef url) ;
# 238 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBundle.h" 3
extern
CFURLRef CFBundleCopyExecutableURL(CFBundleRef bundle);


enum {
    kCFBundleExecutableArchitectureI386 = 0x00000007,
    kCFBundleExecutableArchitecturePPC = 0x00000012,
    kCFBundleExecutableArchitectureX86_64 = 0x01000007,
    kCFBundleExecutableArchitecturePPC64 = 0x01000012
};


extern
CFArrayRef CFBundleCopyExecutableArchitectures(CFBundleRef bundle) ;





extern
Boolean CFBundlePreflightExecutable(CFBundleRef bundle, CFErrorRef *error) ;






extern
Boolean CFBundleLoadExecutableAndReturnError(CFBundleRef bundle, CFErrorRef *error) ;





extern
Boolean CFBundleLoadExecutable(CFBundleRef bundle);

extern
Boolean CFBundleIsExecutableLoaded(CFBundleRef bundle);

extern
void CFBundleUnloadExecutable(CFBundleRef bundle);

extern
void *CFBundleGetFunctionPointerForName(CFBundleRef bundle, CFStringRef functionName);

extern
void CFBundleGetFunctionPointersForNames(CFBundleRef bundle, CFArrayRef functionNames, void *ftbl[]);

extern
void *CFBundleGetDataPointerForName(CFBundleRef bundle, CFStringRef symbolName);

extern
void CFBundleGetDataPointersForNames(CFBundleRef bundle, CFArrayRef symbolNames, void *stbl[]);

extern
CFURLRef CFBundleCopyAuxiliaryExecutableURL(CFBundleRef bundle, CFStringRef executableName);
# 305 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFBundle.h" 3
extern
CFPlugInRef CFBundleGetPlugIn(CFBundleRef bundle);




typedef int CFBundleRefNum;




extern
CFBundleRefNum CFBundleOpenBundleResourceMap(CFBundleRef bundle);






extern
SInt32 CFBundleOpenBundleResourceFiles(CFBundleRef bundle, CFBundleRefNum *refNum, CFBundleRefNum *localizedRefNum);



extern
void CFBundleCloseBundleResourceMap(CFBundleRef bundle, CFBundleRefNum refNum);


# 67 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFMessagePort.h" 1 3
# 11 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFMessagePort.h" 3
# 1 "/usr/include/dispatch/dispatch.h" 1 3 4
# 29 "/usr/include/dispatch/dispatch.h" 3 4
# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stddef.h" 1 3 4
# 30 "/usr/include/dispatch/dispatch.h" 2 3 4
# 47 "/usr/include/dispatch/dispatch.h" 3 4
# 1 "/usr/include/dispatch/base.h" 1 3 4
# 41 "/usr/include/dispatch/base.h" 3 4
typedef union {
 struct dispatch_object_s *_do;
 struct dispatch_continuation_s *_dc;
 struct dispatch_queue_s *_dq;
 struct dispatch_queue_attr_s *_dqa;
 struct dispatch_group_s *_dg;
 struct dispatch_source_s *_ds;
 struct dispatch_source_attr_s *_dsa;
 struct dispatch_semaphore_s *_dsema;
 struct dispatch_data_s *_ddata;
 struct dispatch_io_s *_dchannel;
 struct dispatch_operation_s *_doperation;
 struct dispatch_disk_s *_ddisk;
} dispatch_object_t __attribute__((transparent_union));


typedef void (*dispatch_function_t)(void *);
# 48 "/usr/include/dispatch/dispatch.h" 2 3 4
# 1 "/usr/include/dispatch/object.h" 1 3 4
# 29 "/usr/include/dispatch/object.h" 3 4

# 50 "/usr/include/dispatch/object.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(2))) __attribute__((__nothrow__)) __attribute__((__format__(printf,2,3)))
void
dispatch_debug(dispatch_object_t object, const char *message, ...);

__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(2))) __attribute__((__nothrow__)) __attribute__((__format__(printf,2,0)))
void
dispatch_debugv(dispatch_object_t object, const char *message, va_list ap);
# 74 "/usr/include/dispatch/object.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
void
dispatch_retain(dispatch_object_t object);
# 95 "/usr/include/dispatch/object.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
void
dispatch_release(dispatch_object_t object);
# 112 "/usr/include/dispatch/object.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__pure__)) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
void *
dispatch_get_context(dispatch_object_t object);
# 130 "/usr/include/dispatch/object.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nothrow__))
void
dispatch_set_context(dispatch_object_t object, void *context);
# 156 "/usr/include/dispatch/object.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nothrow__))
void
dispatch_set_finalizer_f(dispatch_object_t object,
 dispatch_function_t finalizer);
# 180 "/usr/include/dispatch/object.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
void
dispatch_suspend(dispatch_object_t object);
# 195 "/usr/include/dispatch/object.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
void
dispatch_resume(dispatch_object_t object);


# 49 "/usr/include/dispatch/dispatch.h" 2 3 4
# 1 "/usr/include/dispatch/time.h" 1 3 4
# 31 "/usr/include/dispatch/time.h" 3 4


struct timespec;
# 61 "/usr/include/dispatch/time.h" 3 4
typedef uint64_t dispatch_time_t;
# 86 "/usr/include/dispatch/time.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
dispatch_time_t
dispatch_time(dispatch_time_t when, int64_t delta);
# 110 "/usr/include/dispatch/time.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
dispatch_time_t
dispatch_walltime(const struct timespec *when, int64_t delta);


# 50 "/usr/include/dispatch/dispatch.h" 2 3 4
# 1 "/usr/include/dispatch/queue.h" 1 3 4
# 67 "/usr/include/dispatch/queue.h" 3 4
typedef struct dispatch_queue_s *dispatch_queue_t;







typedef struct dispatch_queue_attr_s *dispatch_queue_attr_t;
# 111 "/usr/include/dispatch/queue.h" 3 4
typedef void (^dispatch_block_t)(void);



# 145 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
void
dispatch_async(dispatch_queue_t queue, dispatch_block_t block);
# 175 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nonnull__(3))) __attribute__((__nothrow__))
void
dispatch_async_f(dispatch_queue_t queue,
 void *context,
 dispatch_function_t work);
# 213 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
void
dispatch_sync(dispatch_queue_t queue, dispatch_block_t block);
# 241 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nonnull__(3))) __attribute__((__nothrow__))
void
dispatch_sync_f(dispatch_queue_t queue,
 void *context,
 dispatch_function_t work);
# 274 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
void
dispatch_apply(size_t iterations, dispatch_queue_t queue, void (^block)(size_t));
# 306 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(2))) __attribute__((__nonnull__(4))) __attribute__((__nothrow__))
void
dispatch_apply_f(size_t iterations, dispatch_queue_t queue,
 void *context,
 void (*work)(void *, size_t));
# 335 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__pure__)) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
dispatch_queue_t
dispatch_get_current_queue(void);
# 355 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) struct dispatch_queue_s _dispatch_main_q;
# 392 "/usr/include/dispatch/queue.h" 3 4
typedef long dispatch_queue_priority_t;
# 415 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__const__)) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
dispatch_queue_t
dispatch_get_global_queue(dispatch_queue_priority_t priority, unsigned long flags);
# 432 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default")))
struct dispatch_queue_attr_s _dispatch_queue_attr_concurrent;
# 470 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__malloc__)) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
dispatch_queue_t
dispatch_queue_create(const char *label, dispatch_queue_attr_t attr);
# 488 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__pure__)) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
const char *
dispatch_queue_get_label(dispatch_queue_t queue);
# 540 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nothrow__))
void
dispatch_set_target_queue(dispatch_object_t object, dispatch_queue_t queue);
# 558 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nothrow__)) __attribute__((__noreturn__))
void
dispatch_main(void);
# 586 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(2))) __attribute__((__nonnull__(3))) __attribute__((__nothrow__))
void
dispatch_after(dispatch_time_t when,
 dispatch_queue_t queue,
 dispatch_block_t block);
# 619 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(2))) __attribute__((__nonnull__(4))) __attribute__((__nothrow__))
void
dispatch_after_f(dispatch_time_t when,
 dispatch_queue_t queue,
 void *context,
 dispatch_function_t work);
# 666 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
void
dispatch_barrier_async(dispatch_queue_t queue, dispatch_block_t block);
# 700 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nonnull__(3))) __attribute__((__nothrow__))
void
dispatch_barrier_async_f(dispatch_queue_t queue,
 void *context,
 dispatch_function_t work);
# 728 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
void
dispatch_barrier_sync(dispatch_queue_t queue, dispatch_block_t block);
# 759 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nonnull__(3))) __attribute__((__nothrow__))
void
dispatch_barrier_sync_f(dispatch_queue_t queue,
 void *context,
 dispatch_function_t work);
# 802 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nonnull__(2))) __attribute__((__nothrow__))
void
dispatch_queue_set_specific(dispatch_queue_t queue, const void *key,
 void *context, dispatch_function_t destructor);
# 831 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__pure__)) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
void *
dispatch_queue_get_specific(dispatch_queue_t queue, const void *key);
# 857 "/usr/include/dispatch/queue.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__pure__)) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
void *
dispatch_get_specific(const void *key);


# 51 "/usr/include/dispatch/dispatch.h" 2 3 4
# 1 "/usr/include/dispatch/source.h" 1 3 4
# 31 "/usr/include/dispatch/source.h" 3 4
# 1 "/usr/include/mach/message.h" 1 3 4
# 77 "/usr/include/mach/message.h" 3 4
# 1 "/usr/include/mach/kern_return.h" 1 3 4
# 70 "/usr/include/mach/kern_return.h" 3 4
# 1 "/usr/include/mach/machine/kern_return.h" 1 3 4
# 33 "/usr/include/mach/machine/kern_return.h" 3 4
# 1 "/usr/include/mach/i386/kern_return.h" 1 3 4
# 71 "/usr/include/mach/i386/kern_return.h" 3 4
typedef int kern_return_t;
# 34 "/usr/include/mach/machine/kern_return.h" 2 3 4
# 71 "/usr/include/mach/kern_return.h" 2 3 4
# 78 "/usr/include/mach/message.h" 2 3 4
# 89 "/usr/include/mach/message.h" 3 4
typedef natural_t mach_msg_timeout_t;
# 172 "/usr/include/mach/message.h" 3 4
typedef unsigned int mach_msg_bits_t;
typedef natural_t mach_msg_size_t;
typedef integer_t mach_msg_id_t;




typedef unsigned int mach_msg_type_name_t;
# 189 "/usr/include/mach/message.h" 3 4
typedef unsigned int mach_msg_copy_options_t;
# 211 "/usr/include/mach/message.h" 3 4
typedef unsigned int mach_msg_descriptor_type_t;






#pragma pack(4)

typedef struct
{
  natural_t pad1;
  mach_msg_size_t pad2;
  unsigned int pad3 : 24;
  mach_msg_descriptor_type_t type : 8;
} mach_msg_type_descriptor_t;

typedef struct
{
  mach_port_t name;


  mach_msg_size_t pad1;

  unsigned int pad2 : 16;
  mach_msg_type_name_t disposition : 8;
  mach_msg_descriptor_type_t type : 8;
} mach_msg_port_descriptor_t;

typedef struct
{
  uint32_t address;
  mach_msg_size_t size;
  boolean_t deallocate: 8;
  mach_msg_copy_options_t copy: 8;
  unsigned int pad1: 8;
  mach_msg_descriptor_type_t type: 8;
} mach_msg_ool_descriptor32_t;

typedef struct
{
  uint64_t address;
  boolean_t deallocate: 8;
  mach_msg_copy_options_t copy: 8;
  unsigned int pad1: 8;
  mach_msg_descriptor_type_t type: 8;
  mach_msg_size_t size;
} mach_msg_ool_descriptor64_t;

typedef struct
{
  void* address;



  boolean_t deallocate: 8;
  mach_msg_copy_options_t copy: 8;
  unsigned int pad1: 8;
  mach_msg_descriptor_type_t type: 8;

  mach_msg_size_t size;




} mach_msg_ool_descriptor_t;

typedef struct
{
  uint32_t address;
  mach_msg_size_t count;
  boolean_t deallocate: 8;
  mach_msg_copy_options_t copy: 8;
  mach_msg_type_name_t disposition : 8;
  mach_msg_descriptor_type_t type : 8;
} mach_msg_ool_ports_descriptor32_t;

typedef struct
{
  uint64_t address;
  boolean_t deallocate: 8;
  mach_msg_copy_options_t copy: 8;
  mach_msg_type_name_t disposition : 8;
  mach_msg_descriptor_type_t type : 8;
  mach_msg_size_t count;
} mach_msg_ool_ports_descriptor64_t;

typedef struct
{
  void* address;



  boolean_t deallocate: 8;
  mach_msg_copy_options_t copy: 8;
  mach_msg_type_name_t disposition : 8;
  mach_msg_descriptor_type_t type : 8;

  mach_msg_size_t count;




} mach_msg_ool_ports_descriptor_t;
# 330 "/usr/include/mach/message.h" 3 4
typedef union
{
  mach_msg_port_descriptor_t port;
  mach_msg_ool_descriptor_t out_of_line;
  mach_msg_ool_ports_descriptor_t ool_ports;
  mach_msg_type_descriptor_t type;
} mach_msg_descriptor_t;


typedef struct
{
        mach_msg_size_t msgh_descriptor_count;
} mach_msg_body_t;




typedef struct
{
  mach_msg_bits_t msgh_bits;
  mach_msg_size_t msgh_size;
  mach_port_t msgh_remote_port;
  mach_port_t msgh_local_port;
  mach_msg_size_t msgh_reserved;
  mach_msg_id_t msgh_id;
} mach_msg_header_t;



typedef struct
{
        mach_msg_header_t header;
        mach_msg_body_t body;
} mach_msg_base_t;

typedef unsigned int mach_msg_trailer_type_t;



typedef unsigned int mach_msg_trailer_size_t;

typedef struct
{
  mach_msg_trailer_type_t msgh_trailer_type;
  mach_msg_trailer_size_t msgh_trailer_size;
} mach_msg_trailer_t;

typedef struct
{
  mach_msg_trailer_type_t msgh_trailer_type;
  mach_msg_trailer_size_t msgh_trailer_size;
  mach_port_seqno_t msgh_seqno;
} mach_msg_seqno_trailer_t;

typedef struct
{
  unsigned int val[2];
} security_token_t;

typedef struct
{
  mach_msg_trailer_type_t msgh_trailer_type;
  mach_msg_trailer_size_t msgh_trailer_size;
  mach_port_seqno_t msgh_seqno;
  security_token_t msgh_sender;
} mach_msg_security_trailer_t;
# 406 "/usr/include/mach/message.h" 3 4
typedef struct
{
  unsigned int val[8];
} audit_token_t;

typedef struct
{
  mach_msg_trailer_type_t msgh_trailer_type;
  mach_msg_trailer_size_t msgh_trailer_size;
  mach_port_seqno_t msgh_seqno;
  security_token_t msgh_sender;
  audit_token_t msgh_audit;
} mach_msg_audit_trailer_t;

typedef struct
{
  mach_msg_trailer_type_t msgh_trailer_type;
  mach_msg_trailer_size_t msgh_trailer_size;
  mach_port_seqno_t msgh_seqno;
  security_token_t msgh_sender;
  audit_token_t msgh_audit;
  mach_vm_address_t msgh_context;
} mach_msg_context_trailer_t;


typedef struct
{
  mach_port_name_t sender;
} msg_labels_t;






typedef struct
{
  mach_msg_trailer_type_t msgh_trailer_type;
  mach_msg_trailer_size_t msgh_trailer_size;
  mach_port_seqno_t msgh_seqno;
  security_token_t msgh_sender;
  audit_token_t msgh_audit;
  mach_vm_address_t msgh_context;
  int msgh_ad;
  msg_labels_t msgh_labels;
} mach_msg_mac_trailer_t;
# 464 "/usr/include/mach/message.h" 3 4
typedef mach_msg_mac_trailer_t mach_msg_max_trailer_t;
# 474 "/usr/include/mach/message.h" 3 4
typedef mach_msg_security_trailer_t mach_msg_format_0_trailer_t;







extern security_token_t KERNEL_SECURITY_TOKEN;


extern audit_token_t KERNEL_AUDIT_TOKEN;

typedef integer_t mach_msg_options_t;

typedef struct
{
  mach_msg_header_t header;
} mach_msg_empty_send_t;

typedef struct
{
  mach_msg_header_t header;
  mach_msg_trailer_t trailer;
} mach_msg_empty_rcv_t;

typedef union
{
  mach_msg_empty_send_t send;
  mach_msg_empty_rcv_t rcv;
} mach_msg_empty_t;

#pragma pack()
# 527 "/usr/include/mach/message.h" 3 4
typedef natural_t mach_msg_type_size_t;
typedef natural_t mach_msg_type_number_t;
# 571 "/usr/include/mach/message.h" 3 4
typedef integer_t mach_msg_option_t;
# 648 "/usr/include/mach/message.h" 3 4
typedef kern_return_t mach_msg_return_t;
# 731 "/usr/include/mach/message.h" 3 4

# 750 "/usr/include/mach/message.h" 3 4
extern mach_msg_return_t mach_msg_overwrite(
     mach_msg_header_t *msg,
     mach_msg_option_t option,
     mach_msg_size_t send_size,
     mach_msg_size_t rcv_size,
     mach_port_name_t rcv_name,
     mach_msg_timeout_t timeout,
     mach_port_name_t notify,
     mach_msg_header_t *rcv_msg,
     mach_msg_size_t rcv_limit);
# 770 "/usr/include/mach/message.h" 3 4
extern mach_msg_return_t mach_msg(
     mach_msg_header_t *msg,
     mach_msg_option_t option,
     mach_msg_size_t send_size,
     mach_msg_size_t rcv_size,
     mach_port_name_t rcv_name,
     mach_msg_timeout_t timeout,
     mach_port_name_t notify);



# 32 "/usr/include/dispatch/source.h" 2 3 4
# 52 "/usr/include/dispatch/source.h" 3 4
typedef struct dispatch_source_s *dispatch_source_t;
# 65 "/usr/include/dispatch/source.h" 3 4
typedef const struct dispatch_source_type_s *dispatch_source_type_t;
# 75 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default")))
const struct dispatch_source_type_s _dispatch_source_type_data_add;
# 88 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default")))
const struct dispatch_source_type_s _dispatch_source_type_data_or;
# 100 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default")))
const struct dispatch_source_type_s _dispatch_source_type_mach_send;
# 111 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default")))
const struct dispatch_source_type_s _dispatch_source_type_mach_recv;
# 123 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default")))
const struct dispatch_source_type_s _dispatch_source_type_proc;
# 135 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default")))
const struct dispatch_source_type_s _dispatch_source_type_read;
# 146 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default")))
const struct dispatch_source_type_s _dispatch_source_type_signal;
# 158 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default")))
const struct dispatch_source_type_s _dispatch_source_type_timer;
# 170 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default")))
const struct dispatch_source_type_s _dispatch_source_type_vnode;
# 182 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default")))
const struct dispatch_source_type_s _dispatch_source_type_write;
# 195 "/usr/include/dispatch/source.h" 3 4
typedef unsigned long dispatch_source_mach_send_flags_t;
# 219 "/usr/include/dispatch/source.h" 3 4
typedef unsigned long dispatch_source_proc_flags_t;
# 255 "/usr/include/dispatch/source.h" 3 4
typedef unsigned long dispatch_source_vnode_flags_t;


# 290 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__malloc__)) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
dispatch_source_t
dispatch_source_create(dispatch_source_type_t type,
 uintptr_t handle,
 unsigned long mask,
 dispatch_queue_t queue);
# 312 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nothrow__))
void
dispatch_source_set_event_handler(dispatch_source_t source,
 dispatch_block_t handler);
# 335 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nothrow__))
void
dispatch_source_set_event_handler_f(dispatch_source_t source,
 dispatch_function_t handler);
# 369 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nothrow__))
void
dispatch_source_set_cancel_handler(dispatch_source_t source,
 dispatch_block_t cancel_handler);
# 394 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nothrow__))
void
dispatch_source_set_cancel_handler_f(dispatch_source_t source,
 dispatch_function_t cancel_handler);
# 422 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
void
dispatch_source_cancel(dispatch_source_t source);
# 440 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__warn_unused_result__)) __attribute__((__pure__)) __attribute__((__nothrow__))
long
dispatch_source_testcancel(dispatch_source_t source);
# 469 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__warn_unused_result__)) __attribute__((__pure__)) __attribute__((__nothrow__))
uintptr_t
dispatch_source_get_handle(dispatch_source_t source);
# 498 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__warn_unused_result__)) __attribute__((__pure__)) __attribute__((__nothrow__))
unsigned long
dispatch_source_get_mask(dispatch_source_t source);
# 534 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__warn_unused_result__)) __attribute__((__pure__)) __attribute__((__nothrow__))
unsigned long
dispatch_source_get_data(dispatch_source_t source);
# 555 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
void
dispatch_source_merge_data(dispatch_source_t source, unsigned long value);
# 592 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
void
dispatch_source_set_timer(dispatch_source_t source,
 dispatch_time_t start,
 uint64_t interval,
 uint64_t leeway);
# 622 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nothrow__))
void
dispatch_source_set_registration_handler(dispatch_source_t source,
 dispatch_block_t registration_handler);
# 647 "/usr/include/dispatch/source.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nothrow__))
void
dispatch_source_set_registration_handler_f(dispatch_source_t source,
 dispatch_function_t registration_handler);


# 52 "/usr/include/dispatch/dispatch.h" 2 3 4
# 1 "/usr/include/dispatch/group.h" 1 3 4
# 34 "/usr/include/dispatch/group.h" 3 4
typedef struct dispatch_group_s *dispatch_group_t;


# 52 "/usr/include/dispatch/group.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__malloc__)) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
dispatch_group_t
dispatch_group_create(void);
# 81 "/usr/include/dispatch/group.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
void
dispatch_group_async(dispatch_group_t group,
 dispatch_queue_t queue,
 dispatch_block_t block);
# 115 "/usr/include/dispatch/group.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nonnull__(2))) __attribute__((__nonnull__(4))) __attribute__((__nothrow__))
void
dispatch_group_async_f(dispatch_group_t group,
 dispatch_queue_t queue,
 void *context,
 dispatch_function_t work);
# 158 "/usr/include/dispatch/group.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
long
dispatch_group_wait(dispatch_group_t group, dispatch_time_t timeout);
# 194 "/usr/include/dispatch/group.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
void
dispatch_group_notify(dispatch_group_t group,
 dispatch_queue_t queue,
 dispatch_block_t block);
# 224 "/usr/include/dispatch/group.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nonnull__(2))) __attribute__((__nonnull__(4))) __attribute__((__nothrow__))
void
dispatch_group_notify_f(dispatch_group_t group,
 dispatch_queue_t queue,
 void *context,
 dispatch_function_t work);
# 247 "/usr/include/dispatch/group.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
void
dispatch_group_enter(dispatch_group_t group);
# 266 "/usr/include/dispatch/group.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
void
dispatch_group_leave(dispatch_group_t group);


# 53 "/usr/include/dispatch/dispatch.h" 2 3 4
# 1 "/usr/include/dispatch/semaphore.h" 1 3 4
# 35 "/usr/include/dispatch/semaphore.h" 3 4
typedef struct dispatch_semaphore_s *dispatch_semaphore_t;


# 58 "/usr/include/dispatch/semaphore.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__malloc__)) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
dispatch_semaphore_t
dispatch_semaphore_create(long value);
# 83 "/usr/include/dispatch/semaphore.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
long
dispatch_semaphore_wait(dispatch_semaphore_t dsema, dispatch_time_t timeout);
# 105 "/usr/include/dispatch/semaphore.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
long
dispatch_semaphore_signal(dispatch_semaphore_t dsema);


# 54 "/usr/include/dispatch/dispatch.h" 2 3 4
# 1 "/usr/include/dispatch/once.h" 1 3 4
# 29 "/usr/include/dispatch/once.h" 3 4

# 38 "/usr/include/dispatch/once.h" 3 4
typedef long dispatch_once_t;
# 58 "/usr/include/dispatch/once.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
void
dispatch_once(dispatch_once_t *predicate, dispatch_block_t block);

static __inline__ __attribute__((__always_inline__)) __attribute__((__nonnull__)) __attribute__((__nothrow__))
void
_dispatch_once(dispatch_once_t *predicate, dispatch_block_t block)
{
 if (__builtin_expect((*predicate), (~0l)) != ~0l) {
  dispatch_once(predicate, block);
 }
}




__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nonnull__(3))) __attribute__((__nothrow__))
void
dispatch_once_f(dispatch_once_t *predicate, void *context, dispatch_function_t function);

static __inline__ __attribute__((__always_inline__)) __attribute__((__nonnull__(1))) __attribute__((__nonnull__(3))) __attribute__((__nothrow__))
void
_dispatch_once_f(dispatch_once_t *predicate, void *context, dispatch_function_t function)
{
 if (__builtin_expect((*predicate), (~0l)) != ~0l) {
  dispatch_once_f(predicate, context, function);
 }
}




# 55 "/usr/include/dispatch/dispatch.h" 2 3 4
# 1 "/usr/include/dispatch/data.h" 1 3 4
# 29 "/usr/include/dispatch/data.h" 3 4

# 42 "/usr/include/dispatch/data.h" 3 4
typedef struct dispatch_data_s *dispatch_data_t;







__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) struct dispatch_data_s _dispatch_data_empty;
# 70 "/usr/include/dispatch/data.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) const dispatch_block_t _dispatch_data_destructor_free;
# 94 "/usr/include/dispatch/data.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__malloc__)) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
dispatch_data_t
dispatch_data_create(const void *buffer,
 size_t size,
 dispatch_queue_t queue,
 dispatch_block_t destructor);
# 110 "/usr/include/dispatch/data.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__pure__)) __attribute__((__nonnull__(1))) __attribute__((__nothrow__))
size_t
dispatch_data_get_size(dispatch_data_t data);
# 132 "/usr/include/dispatch/data.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
dispatch_data_t
dispatch_data_create_map(dispatch_data_t data,
 const void **buffer_ptr,
 size_t *size_ptr);
# 154 "/usr/include/dispatch/data.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
dispatch_data_t
dispatch_data_create_concat(dispatch_data_t data1, dispatch_data_t data2);
# 174 "/usr/include/dispatch/data.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
dispatch_data_t
dispatch_data_create_subrange(dispatch_data_t data,
 size_t offset,
 size_t length);
# 192 "/usr/include/dispatch/data.h" 3 4
typedef _Bool (^dispatch_data_applier_t)(dispatch_data_t region,
 size_t offset,
 const void *buffer,
 size_t size);
# 217 "/usr/include/dispatch/data.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
_Bool
dispatch_data_apply(dispatch_data_t data, dispatch_data_applier_t applier);
# 236 "/usr/include/dispatch/data.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nonnull__(3))) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
dispatch_data_t
dispatch_data_copy_region(dispatch_data_t data,
 size_t location,
 size_t *offset_ptr);




# 56 "/usr/include/dispatch/dispatch.h" 2 3 4
# 1 "/usr/include/dispatch/io.h" 1 3 4
# 29 "/usr/include/dispatch/io.h" 3 4

# 51 "/usr/include/dispatch/io.h" 3 4
typedef int dispatch_fd_t;
# 104 "/usr/include/dispatch/io.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(3))) __attribute__((__nonnull__(4))) __attribute__((__nothrow__))
void
dispatch_read(dispatch_fd_t fd,
 size_t length,
 dispatch_queue_t queue,
 void (^handler)(dispatch_data_t data, int error));
# 142 "/usr/include/dispatch/io.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(2))) __attribute__((__nonnull__(3))) __attribute__((__nonnull__(4))) __attribute__((__nothrow__))
void
dispatch_write(dispatch_fd_t fd,
 dispatch_data_t data,
 dispatch_queue_t queue,
 void (^handler)(dispatch_data_t data, int error));
# 160 "/usr/include/dispatch/io.h" 3 4
typedef struct dispatch_io_s *dispatch_io_t;
# 170 "/usr/include/dispatch/io.h" 3 4
typedef void (^dispatch_io_handler_t)(_Bool done, dispatch_data_t data, int error);
# 193 "/usr/include/dispatch/io.h" 3 4
typedef unsigned long dispatch_io_type_t;
# 220 "/usr/include/dispatch/io.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__malloc__)) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
dispatch_io_t
dispatch_io_create(dispatch_io_type_t type,
 dispatch_fd_t fd,
 dispatch_queue_t queue,
 void (^cleanup_handler)(int error));
# 255 "/usr/include/dispatch/io.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__malloc__)) __attribute__((__nonnull__(2))) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
dispatch_io_t
dispatch_io_create_with_path(dispatch_io_type_t type,
 const char *path, int oflag, mode_t mode,
 dispatch_queue_t queue,
 void (^cleanup_handler)(int error));
# 294 "/usr/include/dispatch/io.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(2))) __attribute__((__malloc__)) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
dispatch_io_t
dispatch_io_create_with_io(dispatch_io_type_t type,
 dispatch_io_t io,
 dispatch_queue_t queue,
 void (^cleanup_handler)(int error));
# 344 "/usr/include/dispatch/io.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nonnull__(4))) __attribute__((__nonnull__(5))) __attribute__((__nothrow__))
void
dispatch_io_read(dispatch_io_t channel,
 off_t offset,
 size_t length,
 dispatch_queue_t queue,
 dispatch_io_handler_t io_handler);
# 396 "/usr/include/dispatch/io.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nonnull__(3))) __attribute__((__nonnull__(4))) __attribute__((__nonnull__(5))) __attribute__((__nothrow__))
void
dispatch_io_write(dispatch_io_t channel,
 off_t offset,
 dispatch_data_t data,
 dispatch_queue_t queue,
 dispatch_io_handler_t io_handler);
# 414 "/usr/include/dispatch/io.h" 3 4
typedef unsigned long dispatch_io_close_flags_t;
# 433 "/usr/include/dispatch/io.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nothrow__))
void
dispatch_io_close(dispatch_io_t channel, dispatch_io_close_flags_t flags);
# 459 "/usr/include/dispatch/io.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__nothrow__))
void
dispatch_io_barrier(dispatch_io_t channel, dispatch_block_t barrier);
# 478 "/usr/include/dispatch/io.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__)) __attribute__((__warn_unused_result__)) __attribute__((__nothrow__))
dispatch_fd_t
dispatch_io_get_descriptor(dispatch_io_t channel);
# 499 "/usr/include/dispatch/io.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nothrow__))
void
dispatch_io_set_high_water(dispatch_io_t channel, size_t high_water);
# 530 "/usr/include/dispatch/io.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nothrow__))
void
dispatch_io_set_low_water(dispatch_io_t channel, size_t low_water);
# 545 "/usr/include/dispatch/io.h" 3 4
typedef unsigned long dispatch_io_interval_flags_t;
# 569 "/usr/include/dispatch/io.h" 3 4
__attribute__((visibility("default")))
extern __attribute__((visibility("default"))) __attribute__((__nonnull__(1))) __attribute__((__nothrow__))
void
dispatch_io_set_interval(dispatch_io_t channel,
 uint64_t interval,
 dispatch_io_interval_flags_t flags);




# 57 "/usr/include/dispatch/dispatch.h" 2 3 4
# 12 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFMessagePort.h" 2 3



typedef struct __CFMessagePort * CFMessagePortRef;

enum {
    kCFMessagePortSuccess = 0,
    kCFMessagePortSendTimeout = -1,
    kCFMessagePortReceiveTimeout = -2,
    kCFMessagePortIsInvalid = -3,
    kCFMessagePortTransportError = -4,
    kCFMessagePortBecameInvalidError = -5
};

typedef struct {
    CFIndex version;
    void * info;
    const void *(*retain)(const void *info);
    void (*release)(const void *info);
    CFStringRef (*copyDescription)(const void *info);
} CFMessagePortContext;

typedef CFDataRef (*CFMessagePortCallBack)(CFMessagePortRef local, SInt32 msgid, CFDataRef data, void *info);

typedef void (*CFMessagePortInvalidationCallBack)(CFMessagePortRef ms, void *info);

extern CFTypeID CFMessagePortGetTypeID(void);

extern CFMessagePortRef CFMessagePortCreateLocal(CFAllocatorRef allocator, CFStringRef name, CFMessagePortCallBack callout, CFMessagePortContext *context, Boolean *shouldFreeInfo);
extern CFMessagePortRef CFMessagePortCreateRemote(CFAllocatorRef allocator, CFStringRef name);

extern Boolean CFMessagePortIsRemote(CFMessagePortRef ms);
extern CFStringRef CFMessagePortGetName(CFMessagePortRef ms);
extern Boolean CFMessagePortSetName(CFMessagePortRef ms, CFStringRef newName);
extern void CFMessagePortGetContext(CFMessagePortRef ms, CFMessagePortContext *context);
extern void CFMessagePortInvalidate(CFMessagePortRef ms);
extern Boolean CFMessagePortIsValid(CFMessagePortRef ms);
extern CFMessagePortInvalidationCallBack CFMessagePortGetInvalidationCallBack(CFMessagePortRef ms);
extern void CFMessagePortSetInvalidationCallBack(CFMessagePortRef ms, CFMessagePortInvalidationCallBack callout);


extern SInt32 CFMessagePortSendRequest(CFMessagePortRef remote, SInt32 msgid, CFDataRef data, CFTimeInterval sendTimeout, CFTimeInterval rcvTimeout, CFStringRef replyMode, CFDataRef *returnData);

extern CFRunLoopSourceRef CFMessagePortCreateRunLoopSource(CFAllocatorRef allocator, CFMessagePortRef local, CFIndex order);

extern void CFMessagePortSetDispatchQueue(CFMessagePortRef ms, dispatch_queue_t queue) ;


# 68 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFPlugIn.h" 1 3
# 19 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFPlugIn.h" 3




extern
const CFStringRef kCFPlugInDynamicRegistrationKey;
extern
const CFStringRef kCFPlugInDynamicRegisterFunctionKey;
extern
const CFStringRef kCFPlugInUnloadFunctionKey;
extern
const CFStringRef kCFPlugInFactoriesKey;
extern
const CFStringRef kCFPlugInTypesKey;




typedef void (*CFPlugInDynamicRegisterFunction)(CFPlugInRef plugIn);
typedef void (*CFPlugInUnloadFunction)(CFPlugInRef plugIn);
typedef void *(*CFPlugInFactoryFunction)(CFAllocatorRef allocator, CFUUIDRef typeUUID);



extern
CFTypeID CFPlugInGetTypeID(void);

extern
CFPlugInRef CFPlugInCreate(CFAllocatorRef allocator, CFURLRef plugInURL);


extern
CFBundleRef CFPlugInGetBundle(CFPlugInRef plugIn);







extern
void CFPlugInSetLoadOnDemand(CFPlugInRef plugIn, Boolean flag);

extern
Boolean CFPlugInIsLoadOnDemand(CFPlugInRef plugIn);





extern
CFArrayRef CFPlugInFindFactoriesForPlugInType(CFUUIDRef typeUUID);


extern
CFArrayRef CFPlugInFindFactoriesForPlugInTypeInPlugIn(CFUUIDRef typeUUID, CFPlugInRef plugIn);


extern
void *CFPlugInInstanceCreate(CFAllocatorRef allocator, CFUUIDRef factoryUUID, CFUUIDRef typeUUID);






extern
Boolean CFPlugInRegisterFactoryFunction(CFUUIDRef factoryUUID, CFPlugInFactoryFunction func);

extern
Boolean CFPlugInRegisterFactoryFunctionByName(CFUUIDRef factoryUUID, CFPlugInRef plugIn, CFStringRef functionName);

extern
Boolean CFPlugInUnregisterFactory(CFUUIDRef factoryUUID);

extern
Boolean CFPlugInRegisterPlugInType(CFUUIDRef factoryUUID, CFUUIDRef typeUUID);

extern
Boolean CFPlugInUnregisterPlugInType(CFUUIDRef factoryUUID, CFUUIDRef typeUUID);





extern
void CFPlugInAddInstanceForFactory(CFUUIDRef factoryID);

extern
void CFPlugInRemoveInstanceForFactory(CFUUIDRef factoryID);




typedef struct __CFPlugInInstance *CFPlugInInstanceRef;

typedef Boolean (*CFPlugInInstanceGetInterfaceFunction)(CFPlugInInstanceRef instance, CFStringRef interfaceName, void **ftbl);
typedef void (*CFPlugInInstanceDeallocateInstanceDataFunction)(void *instanceData);

extern
Boolean CFPlugInInstanceGetInterfaceFunctionTable(CFPlugInInstanceRef instance, CFStringRef interfaceName, void **ftbl);
extern
CFStringRef CFPlugInInstanceGetFactoryName(CFPlugInInstanceRef instance);
extern
void *CFPlugInInstanceGetInstanceData(CFPlugInInstanceRef instance);
extern
CFTypeID CFPlugInInstanceGetTypeID(void);
extern
CFPlugInInstanceRef CFPlugInInstanceCreateWithInstanceDataSize(CFAllocatorRef allocator, CFIndex instanceDataSize, CFPlugInInstanceDeallocateInstanceDataFunction deallocateInstanceFunction, CFStringRef factoryName, CFPlugInInstanceGetInterfaceFunction getInterfaceFunction);


# 69 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3





# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFAttributedString.h" 1 3
# 20 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFAttributedString.h" 3





typedef const struct __CFAttributedString *CFAttributedStringRef;
typedef struct __CFAttributedString *CFMutableAttributedStringRef;




extern CFTypeID CFAttributedStringGetTypeID(void);
# 40 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFAttributedString.h" 3
extern CFAttributedStringRef CFAttributedStringCreate(CFAllocatorRef alloc, CFStringRef str, CFDictionaryRef attributes);




extern CFAttributedStringRef CFAttributedStringCreateWithSubstring(CFAllocatorRef alloc, CFAttributedStringRef aStr, CFRange range);




extern CFAttributedStringRef CFAttributedStringCreateCopy(CFAllocatorRef alloc, CFAttributedStringRef aStr);




extern CFStringRef CFAttributedStringGetString(CFAttributedStringRef aStr);




extern CFIndex CFAttributedStringGetLength(CFAttributedStringRef aStr);






extern CFDictionaryRef CFAttributedStringGetAttributes(CFAttributedStringRef aStr, CFIndex loc, CFRange *effectiveRange);




extern CFTypeRef CFAttributedStringGetAttribute(CFAttributedStringRef aStr, CFIndex loc, CFStringRef attrName, CFRange *effectiveRange);




extern CFDictionaryRef CFAttributedStringGetAttributesAndLongestEffectiveRange(CFAttributedStringRef aStr, CFIndex loc, CFRange inRange, CFRange *longestEffectiveRange);




extern CFTypeRef CFAttributedStringGetAttributeAndLongestEffectiveRange(CFAttributedStringRef aStr, CFIndex loc, CFStringRef attrName, CFRange inRange, CFRange *longestEffectiveRange);
# 91 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFAttributedString.h" 3
extern CFMutableAttributedStringRef CFAttributedStringCreateMutableCopy(CFAllocatorRef alloc, CFIndex maxLength, CFAttributedStringRef aStr);




extern CFMutableAttributedStringRef CFAttributedStringCreateMutable(CFAllocatorRef alloc, CFIndex maxLength);






extern void CFAttributedStringReplaceString(CFMutableAttributedStringRef aStr, CFRange range, CFStringRef replacement);






extern CFMutableStringRef CFAttributedStringGetMutableString(CFMutableAttributedStringRef aStr);




extern void CFAttributedStringSetAttributes(CFMutableAttributedStringRef aStr, CFRange range, CFDictionaryRef replacement, Boolean clearOtherAttributes);




extern void CFAttributedStringSetAttribute(CFMutableAttributedStringRef aStr, CFRange range, CFStringRef attrName, CFTypeRef value);




extern void CFAttributedStringRemoveAttribute(CFMutableAttributedStringRef aStr, CFRange range, CFStringRef attrName);




extern void CFAttributedStringReplaceAttributedString(CFMutableAttributedStringRef aStr, CFRange range, CFAttributedStringRef replacement);




extern void CFAttributedStringBeginEditing(CFMutableAttributedStringRef aStr);




extern void CFAttributedStringEndEditing(CFMutableAttributedStringRef aStr);



# 75 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFNotificationCenter.h" 1 3
# 11 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFNotificationCenter.h" 3


typedef struct __CFNotificationCenter * CFNotificationCenterRef;

typedef void (*CFNotificationCallback)(CFNotificationCenterRef center, void *observer, CFStringRef name, const void *object, CFDictionaryRef userInfo);

enum {
    CFNotificationSuspensionBehaviorDrop = 1,

    CFNotificationSuspensionBehaviorCoalesce = 2,

    CFNotificationSuspensionBehaviorHold = 3,

    CFNotificationSuspensionBehaviorDeliverImmediately = 4

};
typedef CFIndex CFNotificationSuspensionBehavior;

extern CFTypeID CFNotificationCenterGetTypeID(void);

extern CFNotificationCenterRef CFNotificationCenterGetLocalCenter(void);

extern CFNotificationCenterRef CFNotificationCenterGetDistributedCenter(void);


extern CFNotificationCenterRef CFNotificationCenterGetDarwinNotifyCenter(void);
# 54 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFNotificationCenter.h" 3
extern void CFNotificationCenterAddObserver(CFNotificationCenterRef center, const void *observer, CFNotificationCallback callBack, CFStringRef name, const void *object, CFNotificationSuspensionBehavior suspensionBehavior);

extern void CFNotificationCenterRemoveObserver(CFNotificationCenterRef center, const void *observer, CFStringRef name, const void *object);
extern void CFNotificationCenterRemoveEveryObserver(CFNotificationCenterRef center, const void *observer);

extern void CFNotificationCenterPostNotification(CFNotificationCenterRef center, CFStringRef name, const void *object, CFDictionaryRef userInfo, Boolean deliverImmediately);

enum {
    kCFNotificationDeliverImmediately = (1UL << 0),


    kCFNotificationPostToAllSessions = (1UL << 1)

};

extern void CFNotificationCenterPostNotificationWithOptions(CFNotificationCenterRef center, CFStringRef name, const void *object, CFDictionaryRef userInfo, CFOptionFlags options);



# 76 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURLEnumerator.h" 1 3
# 16 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURLEnumerator.h" 3



typedef const struct __CFURLEnumerator *CFURLEnumeratorRef;


extern
CFTypeID CFURLEnumeratorGetTypeID( void ) ;



enum {
    kCFURLEnumeratorDefaultBehavior = 0,
    kCFURLEnumeratorDescendRecursively = 1UL << 0,
    kCFURLEnumeratorSkipInvisibles = 1UL << 1,
    kCFURLEnumeratorGenerateFileReferenceURLs = 1UL << 2,
    kCFURLEnumeratorSkipPackageContents = 1UL << 3,
    kCFURLEnumeratorIncludeDirectoriesPreOrder = 1UL << 4,
    kCFURLEnumeratorIncludeDirectoriesPostOrder = 1UL << 5,

};
typedef CFOptionFlags CFURLEnumeratorOptions;







extern
CFURLEnumeratorRef CFURLEnumeratorCreateForDirectoryURL( CFAllocatorRef alloc, CFURLRef directoryURL, CFURLEnumeratorOptions option, CFArrayRef propertyKeys ) ;
# 55 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURLEnumerator.h" 3
extern
CFURLEnumeratorRef CFURLEnumeratorCreateForMountedVolumes( CFAllocatorRef alloc, CFURLEnumeratorOptions option, CFArrayRef propertyKeys ) ;



enum {
    kCFURLEnumeratorSuccess = 1,
    kCFURLEnumeratorEnd = 2,
    kCFURLEnumeratorError = 3,
    kCFURLEnumeratorDirectoryPostOrderSuccess = 4,
};
typedef CFIndex CFURLEnumeratorResult;





extern
CFURLEnumeratorResult CFURLEnumeratorGetNextURL( CFURLEnumeratorRef enumerator, CFURLRef *url, CFErrorRef *error ) ;
# 83 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFURLEnumerator.h" 3
extern
void CFURLEnumeratorSkipDescendents( CFURLEnumeratorRef enumerator ) ;




extern
CFIndex CFURLEnumeratorGetDescendentLevel( CFURLEnumeratorRef enumerator ) ;






extern
Boolean CFURLEnumeratorGetSourceDidChange( CFURLEnumeratorRef enumerator ) __attribute__((deprecated));



# 77 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3





# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFFileSecurity.h" 1 3
# 12 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFFileSecurity.h" 3
# 1 "/usr/include/sys/acl.h" 1 3 4
# 27 "/usr/include/sys/acl.h" 3 4
# 1 "/usr/include/sys/kauth.h" 1 3 4
# 55 "/usr/include/sys/kauth.h" 3 4
typedef struct {

 unsigned char g_guid[16];
} guid_t;




#pragma pack(1)
typedef struct {
 u_int8_t sid_kind;
 u_int8_t sid_authcount;
 u_int8_t sid_authority[6];

 u_int32_t sid_authorities[16];
} ntsid_t;
#pragma pack()
# 85 "/usr/include/sys/kauth.h" 3 4
struct kauth_identity_extlookup {
 u_int32_t el_seqno;
 u_int32_t el_result;





 u_int32_t el_flags;
# 114 "/usr/include/sys/kauth.h" 3 4
 __darwin_pid_t el_info_pid;
 u_int64_t el_extend;
 u_int32_t el_info_reserved_1;

 uid_t el_uid;
 guid_t el_uguid;
 u_int32_t el_uguid_valid;
 ntsid_t el_usid;
 u_int32_t el_usid_valid;
 gid_t el_gid;
 guid_t el_gguid;
 u_int32_t el_gguid_valid;
 ntsid_t el_gsid;
 u_int32_t el_gsid_valid;
 u_int32_t el_member_valid;
};
# 143 "/usr/include/sys/kauth.h" 3 4
typedef u_int32_t kauth_ace_rights_t;


struct kauth_ace {
 guid_t ace_applicable;
 u_int32_t ace_flags;
# 167 "/usr/include/sys/kauth.h" 3 4
 kauth_ace_rights_t ace_rights;






};



typedef struct kauth_ace *kauth_ace_t;




struct kauth_acl {
 u_int32_t acl_entrycount;
 u_int32_t acl_flags;

 struct kauth_ace acl_ace[1];
};
# 228 "/usr/include/sys/kauth.h" 3 4
typedef struct kauth_acl *kauth_acl_t;
# 238 "/usr/include/sys/kauth.h" 3 4
struct kauth_filesec {
 u_int32_t fsec_magic;

 guid_t fsec_owner;
 guid_t fsec_group;

 struct kauth_acl fsec_acl;
};
# 259 "/usr/include/sys/kauth.h" 3 4
typedef struct kauth_filesec *kauth_filesec_t;
# 28 "/usr/include/sys/acl.h" 2 3 4
# 67 "/usr/include/sys/acl.h" 3 4
typedef enum {
 ACL_READ_DATA = (1<<1),
 ACL_LIST_DIRECTORY = (1<<1),
 ACL_WRITE_DATA = (1<<2),
 ACL_ADD_FILE = (1<<2),
 ACL_EXECUTE = (1<<3),
 ACL_SEARCH = (1<<3),
 ACL_DELETE = (1<<4),
 ACL_APPEND_DATA = (1<<5),
 ACL_ADD_SUBDIRECTORY = (1<<5),
 ACL_DELETE_CHILD = (1<<6),
 ACL_READ_ATTRIBUTES = (1<<7),
 ACL_WRITE_ATTRIBUTES = (1<<8),
 ACL_READ_EXTATTRIBUTES = (1<<9),
 ACL_WRITE_EXTATTRIBUTES = (1<<10),
 ACL_READ_SECURITY = (1<<11),
 ACL_WRITE_SECURITY = (1<<12),
 ACL_CHANGE_OWNER = (1<<13),
} acl_perm_t;


typedef enum {
 ACL_UNDEFINED_TAG = 0,
 ACL_EXTENDED_ALLOW = 1,
 ACL_EXTENDED_DENY = 2
} acl_tag_t;


typedef enum {
 ACL_TYPE_EXTENDED = 0x00000100,

 ACL_TYPE_ACCESS = 0x00000000,
 ACL_TYPE_DEFAULT = 0x00000001,

 ACL_TYPE_AFS = 0x00000002,
 ACL_TYPE_CODA = 0x00000003,
 ACL_TYPE_NTFS = 0x00000004,
 ACL_TYPE_NWFS = 0x00000005
} acl_type_t;






typedef enum {
 ACL_FIRST_ENTRY = 0,
 ACL_NEXT_ENTRY = -1,
 ACL_LAST_ENTRY = -2
} acl_entry_id_t;


typedef enum {
 ACL_FLAG_DEFER_INHERIT = (1 << 0),
 ACL_FLAG_NO_INHERIT = (1<<17),
 ACL_ENTRY_INHERITED = (1<<4),
 ACL_ENTRY_FILE_INHERIT = (1<<5),
 ACL_ENTRY_DIRECTORY_INHERIT = (1<<6),
 ACL_ENTRY_LIMIT_INHERIT = (1<<7),
 ACL_ENTRY_ONLY_INHERIT = (1<<8)
} acl_flag_t;



struct _acl;
struct _acl_entry;
struct _acl_permset;
struct _acl_flagset;

typedef struct _acl *acl_t;
typedef struct _acl_entry *acl_entry_t;
typedef struct _acl_permset *acl_permset_t;
typedef struct _acl_flagset *acl_flagset_t;

typedef u_int64_t acl_permset_mask_t;



extern acl_t acl_dup(acl_t acl);
extern int acl_free(void *obj_p);
extern acl_t acl_init(int count);


extern int acl_copy_entry(acl_entry_t dest_d, acl_entry_t src_d);
extern int acl_create_entry(acl_t *acl_p, acl_entry_t *entry_p);
extern int acl_create_entry_np(acl_t *acl_p, acl_entry_t *entry_p, int entry_index);
extern int acl_delete_entry(acl_t acl, acl_entry_t entry_d);
extern int acl_get_entry(acl_t acl, int entry_id, acl_entry_t *entry_p);
extern int acl_valid(acl_t acl);
extern int acl_valid_fd_np(int fd, acl_type_t type, acl_t acl);
extern int acl_valid_file_np(const char *path, acl_type_t type, acl_t acl);
extern int acl_valid_link_np(const char *path, acl_type_t type, acl_t acl);


extern int acl_add_perm(acl_permset_t permset_d, acl_perm_t perm);
extern int acl_calc_mask(acl_t *acl_p);
extern int acl_clear_perms(acl_permset_t permset_d);
extern int acl_delete_perm(acl_permset_t permset_d, acl_perm_t perm);
extern int acl_get_perm_np(acl_permset_t permset_d, acl_perm_t perm);
extern int acl_get_permset(acl_entry_t entry_d, acl_permset_t *permset_p);
extern int acl_set_permset(acl_entry_t entry_d, acl_permset_t permset_d);


extern int acl_maximal_permset_mask_np(acl_permset_mask_t * mask_p) __attribute__((visibility("default")));
extern int acl_get_permset_mask_np(acl_entry_t entry_d, acl_permset_mask_t * mask_p) __attribute__((visibility("default")));
extern int acl_set_permset_mask_np(acl_entry_t entry_d, acl_permset_mask_t mask) __attribute__((visibility("default")));


extern int acl_add_flag_np(acl_flagset_t flagset_d, acl_flag_t flag);
extern int acl_clear_flags_np(acl_flagset_t flagset_d);
extern int acl_delete_flag_np(acl_flagset_t flagset_d, acl_flag_t flag);
extern int acl_get_flag_np(acl_flagset_t flagset_d, acl_flag_t flag);
extern int acl_get_flagset_np(void *obj_p, acl_flagset_t *flagset_p);
extern int acl_set_flagset_np(void *obj_p, acl_flagset_t flagset_d);


extern void *acl_get_qualifier(acl_entry_t entry_d);
extern int acl_get_tag_type(acl_entry_t entry_d, acl_tag_t *tag_type_p);
extern int acl_set_qualifier(acl_entry_t entry_d, const void *tag_qualifier_p);
extern int acl_set_tag_type(acl_entry_t entry_d, acl_tag_t tag_type);


extern int acl_delete_def_file(const char *path_p);
extern acl_t acl_get_fd(int fd);
extern acl_t acl_get_fd_np(int fd, acl_type_t type);
extern acl_t acl_get_file(const char *path_p, acl_type_t type);
extern acl_t acl_get_link_np(const char *path_p, acl_type_t type);
extern int acl_set_fd(int fd, acl_t acl);
extern int acl_set_fd_np(int fd, acl_t acl, acl_type_t acl_type);
extern int acl_set_file(const char *path_p, acl_type_t type, acl_t acl);
extern int acl_set_link_np(const char *path_p, acl_type_t type, acl_t acl);


extern ssize_t acl_copy_ext(void *buf_p, acl_t acl, ssize_t size);
extern ssize_t acl_copy_ext_native(void *buf_p, acl_t acl, ssize_t size);
extern acl_t acl_copy_int(const void *buf_p);
extern acl_t acl_copy_int_native(const void *buf_p);
extern acl_t acl_from_text(const char *buf_p);
extern ssize_t acl_size(acl_t acl);
extern char *acl_to_text(acl_t acl, ssize_t *len_p);

# 13 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFFileSecurity.h" 2 3








typedef struct __CFFileSecurity* CFFileSecurityRef;







extern
CFTypeID CFFileSecurityGetTypeID(void) ;
# 44 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFFileSecurity.h" 3
extern
CFFileSecurityRef CFFileSecurityCreate(CFAllocatorRef allocator) ;
# 61 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFFileSecurity.h" 3
extern
CFFileSecurityRef CFFileSecurityCreateCopy(CFAllocatorRef allocator, CFFileSecurityRef fileSec) ;
# 77 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFFileSecurity.h" 3
extern
Boolean CFFileSecurityCopyOwnerUUID(CFFileSecurityRef fileSec, CFUUIDRef *ownerUUID) ;
# 91 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFFileSecurity.h" 3
extern
Boolean CFFileSecuritySetOwnerUUID(CFFileSecurityRef fileSec, CFUUIDRef ownerUUID) ;
# 106 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFFileSecurity.h" 3
extern
Boolean CFFileSecurityCopyGroupUUID(CFFileSecurityRef fileSec, CFUUIDRef *groupUUID) ;
# 121 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFFileSecurity.h" 3
extern
Boolean CFFileSecuritySetGroupUUID(CFFileSecurityRef fileSec, CFUUIDRef groupUUID) ;
# 141 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFFileSecurity.h" 3
extern
Boolean CFFileSecurityCopyAccessControlList(CFFileSecurityRef fileSec, acl_t *accessControlList) ;
# 163 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFFileSecurity.h" 3
extern
Boolean CFFileSecuritySetAccessControlList(CFFileSecurityRef fileSec, acl_t accessControlList) ;
# 179 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFFileSecurity.h" 3
extern
Boolean CFFileSecurityGetOwner(CFFileSecurityRef fileSec, uid_t *owner) ;
# 194 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFFileSecurity.h" 3
extern
Boolean CFFileSecuritySetOwner(CFFileSecurityRef fileSec, uid_t owner) ;
# 210 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFFileSecurity.h" 3
extern
Boolean CFFileSecurityGetGroup(CFFileSecurityRef fileSec, gid_t *group) ;
# 225 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFFileSecurity.h" 3
extern
Boolean CFFileSecuritySetGroup(CFFileSecurityRef fileSec, gid_t group) ;
# 241 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFFileSecurity.h" 3
extern
Boolean CFFileSecurityGetMode(CFFileSecurityRef fileSec, mode_t *mode) ;
# 256 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFFileSecurity.h" 3
extern
Boolean CFFileSecuritySetMode(CFFileSecurityRef fileSec, mode_t mode) ;



# 83 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFMachPort.h" 1 3
# 11 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFMachPort.h" 3


typedef struct __CFMachPort * CFMachPortRef;

typedef struct {
    CFIndex version;
    void * info;
    const void *(*retain)(const void *info);
    void (*release)(const void *info);
    CFStringRef (*copyDescription)(const void *info);
} CFMachPortContext;

typedef void (*CFMachPortCallBack)(CFMachPortRef port, void *msg, CFIndex size, void *info);
typedef void (*CFMachPortInvalidationCallBack)(CFMachPortRef port, void *info);

extern CFTypeID CFMachPortGetTypeID(void);

extern CFMachPortRef CFMachPortCreate(CFAllocatorRef allocator, CFMachPortCallBack callout, CFMachPortContext *context, Boolean *shouldFreeInfo);
extern CFMachPortRef CFMachPortCreateWithPort(CFAllocatorRef allocator, mach_port_t portNum, CFMachPortCallBack callout, CFMachPortContext *context, Boolean *shouldFreeInfo);

extern mach_port_t CFMachPortGetPort(CFMachPortRef port);
extern void CFMachPortGetContext(CFMachPortRef port, CFMachPortContext *context);
extern void CFMachPortInvalidate(CFMachPortRef port);
extern Boolean CFMachPortIsValid(CFMachPortRef port);
extern CFMachPortInvalidationCallBack CFMachPortGetInvalidationCallBack(CFMachPortRef port);
extern void CFMachPortSetInvalidationCallBack(CFMachPortRef port, CFMachPortInvalidationCallBack callout);

extern CFRunLoopSourceRef CFMachPortCreateRunLoopSource(CFAllocatorRef allocator, CFMachPortRef port, CFIndex order);


# 84 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3

# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStringTokenizer.h" 1 3
# 29 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStringTokenizer.h" 3

# 51 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStringTokenizer.h" 3
extern
CFStringRef CFStringTokenizerCopyBestStringLanguage(CFStringRef string, CFRange range) ;







typedef struct __CFStringTokenizer * CFStringTokenizerRef;




enum {







    kCFStringTokenizerUnitWord = 0,
    kCFStringTokenizerUnitSentence = 1,
    kCFStringTokenizerUnitParagraph = 2,
    kCFStringTokenizerUnitLineBreak = 3,




    kCFStringTokenizerUnitWordBoundary = 4,
# 92 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStringTokenizer.h" 3
    kCFStringTokenizerAttributeLatinTranscription = 1UL << 16,


    kCFStringTokenizerAttributeLanguage = 1UL << 17
};






enum {

    kCFStringTokenizerTokenNone = 0,


    kCFStringTokenizerTokenNormal = 1UL << 0,





    kCFStringTokenizerTokenHasSubTokensMask = 1UL << 1,






    kCFStringTokenizerTokenHasDerivedSubTokensMask = 1UL << 2,

    kCFStringTokenizerTokenHasHasNumbersMask = 1UL << 3,
    kCFStringTokenizerTokenHasNonLettersMask = 1UL << 4,
    kCFStringTokenizerTokenIsCJWordMask = 1UL << 5
};
typedef CFOptionFlags CFStringTokenizerTokenType;






extern
CFTypeID CFStringTokenizerGetTypeID(void) ;
# 156 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStringTokenizer.h" 3
extern
CFStringTokenizerRef CFStringTokenizerCreate(CFAllocatorRef alloc, CFStringRef string, CFRange range, CFOptionFlags options, CFLocaleRef locale) ;
# 168 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStringTokenizer.h" 3
extern
void CFStringTokenizerSetString(CFStringTokenizerRef tokenizer, CFStringRef string, CFRange range) ;
# 186 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStringTokenizer.h" 3
extern
CFStringTokenizerTokenType CFStringTokenizerGoToTokenAtIndex(CFStringTokenizerRef tokenizer, CFIndex index) ;
# 210 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStringTokenizer.h" 3
extern
CFStringTokenizerTokenType CFStringTokenizerAdvanceToNextToken(CFStringTokenizerRef tokenizer) ;
# 220 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStringTokenizer.h" 3
extern
CFRange CFStringTokenizerGetCurrentTokenRange(CFStringTokenizerRef tokenizer) ;
# 234 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStringTokenizer.h" 3
extern
CFTypeRef CFStringTokenizerCopyCurrentTokenAttribute(CFStringTokenizerRef tokenizer, CFOptionFlags attribute) ;
# 261 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFStringTokenizer.h" 3
extern
CFIndex CFStringTokenizerGetCurrentSubTokens(CFStringTokenizerRef tokenizer, CFRange *ranges, CFIndex maxRangeLength, CFMutableArrayRef derivedSubTokens) ;


# 86 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFFileDescriptor.h" 1 3
# 11 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFFileDescriptor.h" 3


typedef int CFFileDescriptorNativeDescriptor;

typedef struct __CFFileDescriptor * CFFileDescriptorRef;


enum {
    kCFFileDescriptorReadCallBack = 1UL << 0,
    kCFFileDescriptorWriteCallBack = 1UL << 1
};

typedef void (*CFFileDescriptorCallBack)(CFFileDescriptorRef f, CFOptionFlags callBackTypes, void *info);

typedef struct {
    CFIndex version;
    void * info;
    void * (*retain)(void *info);
    void (*release)(void *info);
    CFStringRef (*copyDescription)(void *info);
} CFFileDescriptorContext;

extern CFTypeID CFFileDescriptorGetTypeID(void) ;

extern CFFileDescriptorRef CFFileDescriptorCreate(CFAllocatorRef allocator, CFFileDescriptorNativeDescriptor fd, Boolean closeOnInvalidate, CFFileDescriptorCallBack callout, const CFFileDescriptorContext *context) ;

extern CFFileDescriptorNativeDescriptor CFFileDescriptorGetNativeDescriptor(CFFileDescriptorRef f) ;

extern void CFFileDescriptorGetContext(CFFileDescriptorRef f, CFFileDescriptorContext *context) ;

extern void CFFileDescriptorEnableCallBacks(CFFileDescriptorRef f, CFOptionFlags callBackTypes) ;
extern void CFFileDescriptorDisableCallBacks(CFFileDescriptorRef f, CFOptionFlags callBackTypes) ;

extern void CFFileDescriptorInvalidate(CFFileDescriptorRef f) ;
extern Boolean CFFileDescriptorIsValid(CFFileDescriptorRef f) ;

extern CFRunLoopSourceRef CFFileDescriptorCreateRunLoopSource(CFAllocatorRef allocator, CFFileDescriptorRef f, CFIndex order) ;



# 87 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3




# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFUserNotification.h" 1 3
# 15 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFUserNotification.h" 3


typedef struct __CFUserNotification * CFUserNotificationRef;
# 63 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFUserNotification.h" 3
typedef void (*CFUserNotificationCallBack)(CFUserNotificationRef userNotification, CFOptionFlags responseFlags);

extern
CFTypeID CFUserNotificationGetTypeID(void);

extern
CFUserNotificationRef CFUserNotificationCreate(CFAllocatorRef allocator, CFTimeInterval timeout, CFOptionFlags flags, SInt32 *error, CFDictionaryRef dictionary);

extern
SInt32 CFUserNotificationReceiveResponse(CFUserNotificationRef userNotification, CFTimeInterval timeout, CFOptionFlags *responseFlags);

extern
CFStringRef CFUserNotificationGetResponseValue(CFUserNotificationRef userNotification, CFStringRef key, CFIndex idx);

extern
CFDictionaryRef CFUserNotificationGetResponseDictionary(CFUserNotificationRef userNotification);

extern
SInt32 CFUserNotificationUpdate(CFUserNotificationRef userNotification, CFTimeInterval timeout, CFOptionFlags flags, CFDictionaryRef dictionary);

extern
SInt32 CFUserNotificationCancel(CFUserNotificationRef userNotification);

extern
CFRunLoopSourceRef CFUserNotificationCreateRunLoopSource(CFAllocatorRef allocator, CFUserNotificationRef userNotification, CFUserNotificationCallBack callout, CFIndex order);




extern
SInt32 CFUserNotificationDisplayNotice(CFTimeInterval timeout, CFOptionFlags flags, CFURLRef iconURL, CFURLRef soundURL, CFURLRef localizationURL, CFStringRef alertHeader, CFStringRef alertMessage, CFStringRef defaultButtonTitle);

extern
SInt32 CFUserNotificationDisplayAlert(CFTimeInterval timeout, CFOptionFlags flags, CFURLRef iconURL, CFURLRef soundURL, CFURLRef localizationURL, CFStringRef alertHeader, CFStringRef alertMessage, CFStringRef defaultButtonTitle, CFStringRef alternateButtonTitle, CFStringRef otherButtonTitle, CFOptionFlags *responseFlags);




enum {
    kCFUserNotificationStopAlertLevel = 0,
    kCFUserNotificationNoteAlertLevel = 1,
    kCFUserNotificationCautionAlertLevel = 2,
    kCFUserNotificationPlainAlertLevel = 3
};

enum {
    kCFUserNotificationDefaultResponse = 0,
    kCFUserNotificationAlternateResponse = 1,
    kCFUserNotificationOtherResponse = 2,
    kCFUserNotificationCancelResponse = 3
};

enum {
    kCFUserNotificationNoDefaultButtonFlag = (1UL << 5),
    kCFUserNotificationUseRadioButtonsFlag = (1UL << 6)
};

static __inline__ __attribute__((always_inline)) CFOptionFlags CFUserNotificationCheckBoxChecked(CFIndex i) {return ((CFOptionFlags)(1UL << (8 + i)));}
static __inline__ __attribute__((always_inline)) CFOptionFlags CFUserNotificationSecureTextField(CFIndex i) {return ((CFOptionFlags)(1UL << (16 + i)));}
static __inline__ __attribute__((always_inline)) CFOptionFlags CFUserNotificationPopUpSelection(CFIndex n) {return ((CFOptionFlags)(n << 24));}




extern
const CFStringRef kCFUserNotificationIconURLKey;

extern
const CFStringRef kCFUserNotificationSoundURLKey;

extern
const CFStringRef kCFUserNotificationLocalizationURLKey;

extern
const CFStringRef kCFUserNotificationAlertHeaderKey;

extern
const CFStringRef kCFUserNotificationAlertMessageKey;

extern
const CFStringRef kCFUserNotificationDefaultButtonTitleKey;

extern
const CFStringRef kCFUserNotificationAlternateButtonTitleKey;

extern
const CFStringRef kCFUserNotificationOtherButtonTitleKey;

extern
const CFStringRef kCFUserNotificationProgressIndicatorValueKey;

extern
const CFStringRef kCFUserNotificationPopUpTitlesKey;

extern
const CFStringRef kCFUserNotificationTextFieldTitlesKey;

extern
const CFStringRef kCFUserNotificationCheckBoxTitlesKey;

extern
const CFStringRef kCFUserNotificationTextFieldValuesKey;

extern
const CFStringRef kCFUserNotificationPopUpSelectionKey ;
# 177 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFUserNotification.h" 3

# 92 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFXMLNode.h" 1 3
# 19 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFXMLNode.h" 3


enum {
 kCFXMLNodeCurrentVersion = 1
};

typedef const struct __CFXMLNode * CFXMLNodeRef;
typedef CFTreeRef CFXMLTreeRef;
# 49 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFXMLNode.h" 3
enum {
    kCFXMLNodeTypeDocument = 1,
    kCFXMLNodeTypeElement = 2,
    kCFXMLNodeTypeAttribute = 3,
    kCFXMLNodeTypeProcessingInstruction = 4,
    kCFXMLNodeTypeComment = 5,
    kCFXMLNodeTypeText = 6,
    kCFXMLNodeTypeCDATASection = 7,
    kCFXMLNodeTypeDocumentFragment = 8,
    kCFXMLNodeTypeEntity = 9,
    kCFXMLNodeTypeEntityReference = 10,
    kCFXMLNodeTypeDocumentType = 11,
    kCFXMLNodeTypeWhitespace = 12,
    kCFXMLNodeTypeNotation = 13,
    kCFXMLNodeTypeElementTypeDeclaration = 14,
    kCFXMLNodeTypeAttributeListDeclaration = 15
};
typedef CFIndex CFXMLNodeTypeCode;

typedef struct {
    CFDictionaryRef attributes;
    CFArrayRef attributeOrder;
    Boolean isEmpty;
    char _reserved[3];
} CFXMLElementInfo;

typedef struct {
    CFStringRef dataString;
} CFXMLProcessingInstructionInfo;

typedef struct {
    CFURLRef sourceURL;
    CFStringEncoding encoding;
} CFXMLDocumentInfo;

typedef struct {
    CFURLRef systemID;
    CFStringRef publicID;
} CFXMLExternalID;

typedef struct {
    CFXMLExternalID externalID;
} CFXMLDocumentTypeInfo;

typedef struct {
    CFXMLExternalID externalID;
} CFXMLNotationInfo;

typedef struct {

    CFStringRef contentDescription;
} CFXMLElementTypeDeclarationInfo;

typedef struct {

    CFStringRef attributeName;
    CFStringRef typeString;
    CFStringRef defaultString;
} CFXMLAttributeDeclarationInfo;

typedef struct {
    CFIndex numberOfAttributes;
    CFXMLAttributeDeclarationInfo *attributes;
} CFXMLAttributeListDeclarationInfo;

enum {
    kCFXMLEntityTypeParameter,
    kCFXMLEntityTypeParsedInternal,
    kCFXMLEntityTypeParsedExternal,
    kCFXMLEntityTypeUnparsed,
    kCFXMLEntityTypeCharacter
};
typedef CFIndex CFXMLEntityTypeCode;

typedef struct {
    CFXMLEntityTypeCode entityType;
    CFStringRef replacementText;
    CFXMLExternalID entityID;
    CFStringRef notationName;
} CFXMLEntityInfo;

typedef struct {
    CFXMLEntityTypeCode entityType;
} CFXMLEntityReferenceInfo;
# 154 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFXMLNode.h" 3
extern
CFTypeID CFXMLNodeGetTypeID(void);


extern
CFXMLNodeRef CFXMLNodeCreate(CFAllocatorRef alloc, CFXMLNodeTypeCode xmlType, CFStringRef dataString, const void *additionalInfoPtr, CFIndex version);


extern
CFXMLNodeRef CFXMLNodeCreateCopy(CFAllocatorRef alloc, CFXMLNodeRef origNode);

extern
CFXMLNodeTypeCode CFXMLNodeGetTypeCode(CFXMLNodeRef node);

extern
CFStringRef CFXMLNodeGetString(CFXMLNodeRef node);

extern
const void *CFXMLNodeGetInfoPtr(CFXMLNodeRef node);

extern
CFIndex CFXMLNodeGetVersion(CFXMLNodeRef node);




extern
CFXMLTreeRef CFXMLTreeCreateWithNode(CFAllocatorRef allocator, CFXMLNodeRef node);


extern
CFXMLNodeRef CFXMLTreeGetNode(CFXMLTreeRef xmlTree);


# 93 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 1 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFXMLParser.h" 1 3
# 21 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFXMLParser.h" 3


typedef struct __CFXMLParser * CFXMLParserRef;
# 55 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFXMLParser.h" 3
enum {
    kCFXMLParserValidateDocument = (1UL << 0),
    kCFXMLParserSkipMetaData = (1UL << 1),
    kCFXMLParserReplacePhysicalEntities = (1UL << 2),
    kCFXMLParserSkipWhitespace = (1UL << 3),
    kCFXMLParserResolveExternalEntities = (1UL << 4),
    kCFXMLParserAddImpliedAttributes = (1UL << 5),
    kCFXMLParserAllOptions = 0x00FFFFFF,
    kCFXMLParserNoOptions = 0
};
typedef CFOptionFlags CFXMLParserOptions;


enum {
    kCFXMLStatusParseNotBegun = -2,
    kCFXMLStatusParseInProgress = -1,
    kCFXMLStatusParseSuccessful = 0,
    kCFXMLErrorUnexpectedEOF = 1,
    kCFXMLErrorUnknownEncoding,
    kCFXMLErrorEncodingConversionFailure,
    kCFXMLErrorMalformedProcessingInstruction,
    kCFXMLErrorMalformedDTD,
    kCFXMLErrorMalformedName,
    kCFXMLErrorMalformedCDSect,
    kCFXMLErrorMalformedCloseTag,
    kCFXMLErrorMalformedStartTag,
    kCFXMLErrorMalformedDocument,
    kCFXMLErrorElementlessDocument,
    kCFXMLErrorMalformedComment,
    kCFXMLErrorMalformedCharacterReference,
    kCFXMLErrorMalformedParsedCharacterData,
    kCFXMLErrorNoData
};
typedef CFIndex CFXMLParserStatusCode;
# 132 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFXMLParser.h" 3
typedef void * (*CFXMLParserCreateXMLStructureCallBack)(CFXMLParserRef parser, CFXMLNodeRef nodeDesc, void *info);
typedef void (*CFXMLParserAddChildCallBack)(CFXMLParserRef parser, void *parent, void *child, void *info);
typedef void (*CFXMLParserEndXMLStructureCallBack)(CFXMLParserRef parser, void *xmlType, void *info);
typedef CFDataRef (*CFXMLParserResolveExternalEntityCallBack)(CFXMLParserRef parser, CFXMLExternalID *extID, void *info);
typedef Boolean (*CFXMLParserHandleErrorCallBack)(CFXMLParserRef parser, CFXMLParserStatusCode error, void *info);
typedef struct {
    CFIndex version;
    CFXMLParserCreateXMLStructureCallBack createXMLStructure;
    CFXMLParserAddChildCallBack addChild;
    CFXMLParserEndXMLStructureCallBack endXMLStructure;
    CFXMLParserResolveExternalEntityCallBack resolveExternalEntity;
    CFXMLParserHandleErrorCallBack handleError;
} CFXMLParserCallBacks;

typedef const void * (*CFXMLParserRetainCallBack)(const void *info);
typedef void (*CFXMLParserReleaseCallBack)(const void *info);
typedef CFStringRef (*CFXMLParserCopyDescriptionCallBack)(const void *info);
typedef struct {
    CFIndex version;
    void * info;
    CFXMLParserRetainCallBack retain;
    CFXMLParserReleaseCallBack release;
    CFXMLParserCopyDescriptionCallBack copyDescription;
} CFXMLParserContext;

extern
CFTypeID CFXMLParserGetTypeID(void);
# 167 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CFXMLParser.h" 3
extern
CFXMLParserRef CFXMLParserCreate(CFAllocatorRef allocator, CFDataRef xmlData, CFURLRef dataSource, CFOptionFlags parseOptions, CFIndex versionOfNodes, CFXMLParserCallBacks *callBacks, CFXMLParserContext *context);



extern
CFXMLParserRef CFXMLParserCreateWithDataFromURL(CFAllocatorRef allocator, CFURLRef dataSource, CFOptionFlags parseOptions, CFIndex versionOfNodes, CFXMLParserCallBacks *callBacks, CFXMLParserContext *context);

extern
void CFXMLParserGetContext(CFXMLParserRef parser, CFXMLParserContext *context);

extern
void CFXMLParserGetCallBacks(CFXMLParserRef parser, CFXMLParserCallBacks *callBacks);

extern
CFURLRef CFXMLParserGetSourceURL(CFXMLParserRef parser);


extern
CFIndex CFXMLParserGetLocation(CFXMLParserRef parser);


extern
CFIndex CFXMLParserGetLineNumber(CFXMLParserRef parser);


extern
void *CFXMLParserGetDocument(CFXMLParserRef parser);




extern
CFXMLParserStatusCode CFXMLParserGetStatusCode(CFXMLParserRef parser);

extern
CFStringRef CFXMLParserCopyErrorDescription(CFXMLParserRef parser);




extern
void CFXMLParserAbort(CFXMLParserRef parser, CFXMLParserStatusCode errorCode, CFStringRef errorDescription);






extern
Boolean CFXMLParserParse(CFXMLParserRef parser);







extern
CFXMLTreeRef CFXMLTreeCreateFromData(CFAllocatorRef allocator, CFDataRef xmlData, CFURLRef dataSource, CFOptionFlags parseOptions, CFIndex versionOfNodes);




extern
CFXMLTreeRef CFXMLTreeCreateFromDataWithError(CFAllocatorRef allocator, CFDataRef xmlData, CFURLRef dataSource, CFOptionFlags parseOptions, CFIndex versionOfNodes, CFDictionaryRef *errorDict);


extern
CFXMLTreeRef CFXMLTreeCreateWithDataFromURL(CFAllocatorRef allocator, CFURLRef dataSource, CFOptionFlags parseOptions, CFIndex versionOfNodes);






extern
CFDataRef CFXMLTreeCreateXMLData(CFAllocatorRef allocator, CFXMLTreeRef xmlTree);







extern
CFStringRef CFXMLCreateStringByEscapingEntities(CFAllocatorRef allocator, CFStringRef string, CFDictionaryRef entitiesDictionary);

extern
CFStringRef CFXMLCreateStringByUnescapingEntities(CFAllocatorRef allocator, CFStringRef string, CFDictionaryRef entitiesDictionary);


extern const CFStringRef kCFXMLTreeErrorDescription;


extern const CFStringRef kCFXMLTreeErrorLineNumber;


extern const CFStringRef kCFXMLTreeErrorLocation;


extern const CFStringRef kCFXMLTreeErrorStatusCode;



# 94 "/System/Library/Frameworks/CoreFoundation.framework/Headers/CoreFoundation.h" 2 3
# 30 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SystemConfiguration.h" 2 3
# 72 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SystemConfiguration.h" 3
enum {



 kSCStatusOK = 0,
 kSCStatusFailed = 1001,
 kSCStatusInvalidArgument = 1002,
 kSCStatusAccessError = 1003,



 kSCStatusNoKey = 1004,
 kSCStatusKeyExists = 1005,
 kSCStatusLocked = 1006,
 kSCStatusNeedLock = 1007,



 kSCStatusNoStoreSession = 2001,
 kSCStatusNoStoreServer = 2002,
 kSCStatusNotifierActive = 2003,



 kSCStatusNoPrefsSession = 3001,
 kSCStatusPrefsBusy = 3002,
 kSCStatusNoConfigFile = 3003,
 kSCStatusNoLink = 3004,
 kSCStatusStale = 3005,
 kSCStatusMaxLink = 3006,



 kSCStatusReachabilityUnknown = 4001,



 kSCStatusConnectionNoService = 5001,


};



# 1 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStore.h" 1 3
# 59 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStore.h" 3
typedef const struct __SCDynamicStore * SCDynamicStoreRef;
# 79 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStore.h" 3
typedef struct {
 CFIndex version;
 void * info;
 const void *(*retain)(const void *info);
 void (*release)(const void *info);
 CFStringRef (*copyDescription)(const void *info);
} SCDynamicStoreContext;
# 106 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStore.h" 3
typedef void (*SCDynamicStoreCallBack) (
     SCDynamicStoreRef store,
     CFArrayRef changedKeys,
     void *info
     );








CFTypeID
SCDynamicStoreGetTypeID (void) __attribute__((visibility("default")));
# 142 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStore.h" 3
SCDynamicStoreRef
SCDynamicStoreCreate (
     CFAllocatorRef allocator,
     CFStringRef name,
     SCDynamicStoreCallBack callout,
     SCDynamicStoreContext *context
     ) __attribute__((visibility("default")));
# 187 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStore.h" 3
SCDynamicStoreRef
SCDynamicStoreCreateWithOptions (
     CFAllocatorRef allocator,
     CFStringRef name,
     CFDictionaryRef storeOptions,
     SCDynamicStoreCallBack callout,
     SCDynamicStoreContext *context
     ) __attribute__((visibility("default")));

extern const CFStringRef kSCDynamicStoreUseSessionKeys __attribute__((visibility("default")));
# 221 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStore.h" 3
CFRunLoopSourceRef
SCDynamicStoreCreateRunLoopSource (
     CFAllocatorRef allocator,
     SCDynamicStoreRef store,
     CFIndex order
     ) __attribute__((visibility("default")));
# 238 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStore.h" 3
Boolean
SCDynamicStoreSetDispatchQueue (
     SCDynamicStoreRef store,
     dispatch_queue_t queue
     ) __attribute__((visibility("default")));
# 255 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStore.h" 3
CFArrayRef
SCDynamicStoreCopyKeyList (
     SCDynamicStoreRef store,
     CFStringRef pattern
     ) __attribute__((visibility("default")));
# 271 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStore.h" 3
Boolean
SCDynamicStoreAddValue (
     SCDynamicStoreRef store,
     CFStringRef key,
     CFPropertyListRef value
     ) __attribute__((visibility("default")));
# 290 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStore.h" 3
Boolean
SCDynamicStoreAddTemporaryValue (
     SCDynamicStoreRef store,
     CFStringRef key,
     CFPropertyListRef value
     ) __attribute__((visibility("default")));
# 306 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStore.h" 3
CFPropertyListRef
SCDynamicStoreCopyValue (
     SCDynamicStoreRef store,
     CFStringRef key
     ) __attribute__((visibility("default")));
# 325 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStore.h" 3
CFDictionaryRef
SCDynamicStoreCopyMultiple (
     SCDynamicStoreRef store,
     CFArrayRef keys,
     CFArrayRef patterns
     ) __attribute__((visibility("default")));
# 341 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStore.h" 3
Boolean
SCDynamicStoreSetValue (
     SCDynamicStoreRef store,
     CFStringRef key,
     CFPropertyListRef value
     ) __attribute__((visibility("default")));
# 357 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStore.h" 3
Boolean
SCDynamicStoreSetMultiple (
     SCDynamicStoreRef store,
     CFDictionaryRef keysToSet,
     CFArrayRef keysToRemove,
     CFArrayRef keysToNotify
     ) __attribute__((visibility("default")));
# 374 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStore.h" 3
Boolean
SCDynamicStoreRemoveValue (
     SCDynamicStoreRef store,
     CFStringRef key
     ) __attribute__((visibility("default")));
# 390 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStore.h" 3
Boolean
SCDynamicStoreNotifyValue (
     SCDynamicStoreRef store,
     CFStringRef key
     ) __attribute__((visibility("default")));
# 408 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStore.h" 3
Boolean
SCDynamicStoreSetNotificationKeys (
     SCDynamicStoreRef store,
     CFArrayRef keys,
     CFArrayRef patterns
     ) __attribute__((visibility("default")));
# 427 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStore.h" 3
CFArrayRef
SCDynamicStoreCopyNotifiedKeys (
     SCDynamicStoreRef store
     ) __attribute__((visibility("default")));


# 117 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SystemConfiguration.h" 2 3
# 1 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStoreKey.h" 1 3
# 42 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStoreKey.h" 3

# 60 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStoreKey.h" 3
CFStringRef
SCDynamicStoreKeyCreate (
      CFAllocatorRef allocator,
      CFStringRef fmt,
      ...
      ) __attribute__((visibility("default")));
# 85 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStoreKey.h" 3
CFStringRef
SCDynamicStoreKeyCreateNetworkGlobalEntity (
      CFAllocatorRef allocator,
      CFStringRef domain,
      CFStringRef entity
      ) __attribute__((visibility("default")));
# 108 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStoreKey.h" 3
CFStringRef
SCDynamicStoreKeyCreateNetworkInterface (
      CFAllocatorRef allocator,
      CFStringRef domain
      ) __attribute__((visibility("default")));
# 134 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStoreKey.h" 3
CFStringRef
SCDynamicStoreKeyCreateNetworkInterfaceEntity (
      CFAllocatorRef allocator,
      CFStringRef domain,
      CFStringRef ifname,
      CFStringRef entity
      ) __attribute__((visibility("default")));
# 163 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStoreKey.h" 3
CFStringRef
SCDynamicStoreKeyCreateNetworkServiceEntity (
      CFAllocatorRef allocator,
      CFStringRef domain,
      CFStringRef serviceID,
      CFStringRef entity
      ) __attribute__((visibility("default")));
# 184 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStoreKey.h" 3
CFStringRef
SCDynamicStoreKeyCreateComputerName (
      CFAllocatorRef allocator
      ) __attribute__((visibility("default")));
# 201 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStoreKey.h" 3
CFStringRef
SCDynamicStoreKeyCreateConsoleUser (
      CFAllocatorRef allocator
      ) __attribute__((visibility("default")));
# 219 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStoreKey.h" 3
CFStringRef
SCDynamicStoreKeyCreateHostNames (
      CFAllocatorRef allocator
      ) __attribute__((visibility("default")));
# 237 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStoreKey.h" 3
CFStringRef
SCDynamicStoreKeyCreateLocation (
      CFAllocatorRef allocator
      ) __attribute__((visibility("default")));
# 255 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStoreKey.h" 3
CFStringRef
SCDynamicStoreKeyCreateProxies (
      CFAllocatorRef allocator
      ) __attribute__((visibility("default")));


# 118 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SystemConfiguration.h" 2 3
# 1 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStoreCopySpecific.h" 1 3
# 43 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStoreCopySpecific.h" 3

# 58 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStoreCopySpecific.h" 3
CFStringRef
SCDynamicStoreCopyComputerName (
     SCDynamicStoreRef store,
     CFStringEncoding *nameEncoding
     ) __attribute__((visibility("default")));
# 86 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStoreCopySpecific.h" 3
CFStringRef
SCDynamicStoreCopyConsoleUser (
     SCDynamicStoreRef store,
     uid_t *uid,
     gid_t *gid
     ) __attribute__((visibility("default")));
# 103 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStoreCopySpecific.h" 3
CFStringRef
SCDynamicStoreCopyLocalHostName (
     SCDynamicStoreRef store
     ) __attribute__((visibility("default")));
# 119 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStoreCopySpecific.h" 3
CFStringRef
SCDynamicStoreCopyLocation (
     SCDynamicStoreRef store
     ) __attribute__((visibility("default")));
# 204 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCDynamicStoreCopySpecific.h" 3
CFDictionaryRef
SCDynamicStoreCopyProxies (
     SCDynamicStoreRef store
     ) __attribute__((visibility("default")));


# 119 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SystemConfiguration.h" 2 3


# 1 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 1 3
# 35 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 1 3
# 24 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/cssmconfig.h" 1 3
# 33 "/System/Library/Frameworks/Security.framework/Headers/cssmconfig.h" 3
# 1 "/System/Library/Frameworks/CoreServices.framework/Headers/../Frameworks/CarbonCore.framework/Headers/ConditionalMacros.h" 1 3
# 34 "/System/Library/Frameworks/Security.framework/Headers/cssmconfig.h" 2 3
# 49 "/System/Library/Frameworks/Security.framework/Headers/cssmconfig.h" 3
typedef int64_t sint64;



typedef uint64_t uint64;



typedef int32_t sint32;



typedef int16_t sint16;



typedef int8_t sint8;



typedef uint32_t uint32;



typedef uint16_t uint16;



typedef uint8_t uint8;



typedef intptr_t CSSM_INTPTR;
typedef size_t CSSM_SIZE;
# 25 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/cssmapple.h" 1 3
# 29 "/System/Library/Frameworks/Security.framework/Headers/cssmapple.h" 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/cssmerr.h" 1 3
# 43 "/System/Library/Frameworks/Security.framework/Headers/cssmerr.h" 3
enum {
 CSSM_BASE_ERROR = -0x7FFF0000
};

enum {
 CSSM_ERRORCODE_MODULE_EXTENT = 0x00000800,
 CSSM_ERRORCODE_CUSTOM_OFFSET = 0x00000400,
 CSSM_ERRORCODE_COMMON_EXTENT = 0x100
};
# 67 "/System/Library/Frameworks/Security.framework/Headers/cssmerr.h" 3
enum {
 CSSM_CSSM_BASE_ERROR = CSSM_BASE_ERROR,
 CSSM_CSSM_PRIVATE_ERROR = CSSM_BASE_ERROR + CSSM_ERRORCODE_CUSTOM_OFFSET,
 CSSM_CSP_BASE_ERROR = CSSM_CSSM_BASE_ERROR + CSSM_ERRORCODE_MODULE_EXTENT,
 CSSM_CSP_PRIVATE_ERROR = CSSM_CSP_BASE_ERROR + CSSM_ERRORCODE_CUSTOM_OFFSET,
 CSSM_DL_BASE_ERROR = CSSM_CSP_BASE_ERROR + CSSM_ERRORCODE_MODULE_EXTENT,
 CSSM_DL_PRIVATE_ERROR = CSSM_DL_BASE_ERROR + CSSM_ERRORCODE_CUSTOM_OFFSET,
 CSSM_CL_BASE_ERROR = CSSM_DL_BASE_ERROR + CSSM_ERRORCODE_MODULE_EXTENT,
 CSSM_CL_PRIVATE_ERROR = CSSM_CL_BASE_ERROR + CSSM_ERRORCODE_CUSTOM_OFFSET,
 CSSM_TP_BASE_ERROR = CSSM_CL_BASE_ERROR + CSSM_ERRORCODE_MODULE_EXTENT,
 CSSM_TP_PRIVATE_ERROR = CSSM_TP_BASE_ERROR + CSSM_ERRORCODE_CUSTOM_OFFSET ,
 CSSM_KR_BASE_ERROR = CSSM_TP_BASE_ERROR + CSSM_ERRORCODE_MODULE_EXTENT,
 CSSM_KR_PRIVATE_ERROR = CSSM_KR_BASE_ERROR + CSSM_ERRORCODE_CUSTOM_OFFSET,
 CSSM_AC_BASE_ERROR = CSSM_KR_BASE_ERROR + CSSM_ERRORCODE_MODULE_EXTENT,
 CSSM_AC_PRIVATE_ERROR = CSSM_AC_BASE_ERROR + CSSM_ERRORCODE_CUSTOM_OFFSET
};


enum {
 CSSM_MDS_BASE_ERROR = CSSM_CSP_BASE_ERROR + CSSM_ERRORCODE_MODULE_EXTENT,
 CSSM_MDS_PRIVATE_ERROR = CSSM_MDS_BASE_ERROR + CSSM_ERRORCODE_CUSTOM_OFFSET
};


enum {
 CSSMERR_CSSM_INVALID_ADDIN_HANDLE =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRORCODE_COMMON_EXTENT + 1,
 CSSMERR_CSSM_NOT_INITIALIZED =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRORCODE_COMMON_EXTENT + 2,
 CSSMERR_CSSM_INVALID_HANDLE_USAGE =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRORCODE_COMMON_EXTENT + 3,
 CSSMERR_CSSM_PVC_REFERENT_NOT_FOUND =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRORCODE_COMMON_EXTENT + 4,
 CSSMERR_CSSM_FUNCTION_INTEGRITY_FAIL =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRORCODE_COMMON_EXTENT + 5
};


enum {
 CSSM_ERRCODE_INTERNAL_ERROR = 0x0001,
 CSSM_ERRCODE_MEMORY_ERROR = 0x0002,
 CSSM_ERRCODE_MDS_ERROR = 0x0003,
 CSSM_ERRCODE_INVALID_POINTER = 0x0004,
 CSSM_ERRCODE_INVALID_INPUT_POINTER = 0x0005,
 CSSM_ERRCODE_INVALID_OUTPUT_POINTER = 0x0006,
 CSSM_ERRCODE_FUNCTION_NOT_IMPLEMENTED = 0x0007,
 CSSM_ERRCODE_SELF_CHECK_FAILED = 0x0008,
 CSSM_ERRCODE_OS_ACCESS_DENIED = 0x0009,
 CSSM_ERRCODE_FUNCTION_FAILED = 0x000A,
 CSSM_ERRCODE_MODULE_MANIFEST_VERIFY_FAILED = 0x000B,
 CSSM_ERRCODE_INVALID_GUID = 0x000C
};


enum {
 CSSM_ERRCODE_OPERATION_AUTH_DENIED = 0x0020,
 CSSM_ERRCODE_OBJECT_USE_AUTH_DENIED = 0x0021,
 CSSM_ERRCODE_OBJECT_MANIP_AUTH_DENIED = 0x0022,
 CSSM_ERRCODE_OBJECT_ACL_NOT_SUPPORTED = 0x0023,
 CSSM_ERRCODE_OBJECT_ACL_REQUIRED = 0x0024,
 CSSM_ERRCODE_INVALID_ACCESS_CREDENTIALS = 0x0025,
 CSSM_ERRCODE_INVALID_ACL_BASE_CERTS = 0x0026,
 CSSM_ERRCODE_ACL_BASE_CERTS_NOT_SUPPORTED = 0x0027,
 CSSM_ERRCODE_INVALID_SAMPLE_VALUE = 0x0028,
 CSSM_ERRCODE_SAMPLE_VALUE_NOT_SUPPORTED = 0x0029,
 CSSM_ERRCODE_INVALID_ACL_SUBJECT_VALUE = 0x002A,
 CSSM_ERRCODE_ACL_SUBJECT_TYPE_NOT_SUPPORTED = 0x002B,
 CSSM_ERRCODE_INVALID_ACL_CHALLENGE_CALLBACK = 0x002C,
 CSSM_ERRCODE_ACL_CHALLENGE_CALLBACK_FAILED = 0x002D,
 CSSM_ERRCODE_INVALID_ACL_ENTRY_TAG = 0x002E,
 CSSM_ERRCODE_ACL_ENTRY_TAG_NOT_FOUND = 0x002F,
 CSSM_ERRCODE_INVALID_ACL_EDIT_MODE = 0x0030,
 CSSM_ERRCODE_ACL_CHANGE_FAILED = 0x0031,
 CSSM_ERRCODE_INVALID_NEW_ACL_ENTRY = 0x0032,
 CSSM_ERRCODE_INVALID_NEW_ACL_OWNER = 0x0033,
 CSSM_ERRCODE_ACL_DELETE_FAILED = 0x0034,
 CSSM_ERRCODE_ACL_REPLACE_FAILED = 0x0035,
 CSSM_ERRCODE_ACL_ADD_FAILED = 0x0036
};


enum {
 CSSM_ERRCODE_INVALID_CONTEXT_HANDLE = 0x0040,
 CSSM_ERRCODE_INCOMPATIBLE_VERSION = 0x0041,
 CSSM_ERRCODE_INVALID_CERTGROUP_POINTER = 0x0042,
 CSSM_ERRCODE_INVALID_CERT_POINTER = 0x0043,
 CSSM_ERRCODE_INVALID_CRL_POINTER = 0x0044,
 CSSM_ERRCODE_INVALID_FIELD_POINTER = 0x0045,
 CSSM_ERRCODE_INVALID_DATA = 0x0046,
 CSSM_ERRCODE_CRL_ALREADY_SIGNED = 0x0047,
 CSSM_ERRCODE_INVALID_NUMBER_OF_FIELDS = 0x0048,
 CSSM_ERRCODE_VERIFICATION_FAILURE = 0x0049,
 CSSM_ERRCODE_INVALID_DB_HANDLE = 0x004A,
 CSSM_ERRCODE_PRIVILEGE_NOT_GRANTED = 0x004B,
 CSSM_ERRCODE_INVALID_DB_LIST = 0x004C,
 CSSM_ERRCODE_INVALID_DB_LIST_POINTER = 0x004D,
 CSSM_ERRCODE_UNKNOWN_FORMAT = 0x004E,
 CSSM_ERRCODE_UNKNOWN_TAG = 0x004F,
 CSSM_ERRCODE_INVALID_CSP_HANDLE = 0x0050,
 CSSM_ERRCODE_INVALID_DL_HANDLE = 0x0051,
 CSSM_ERRCODE_INVALID_CL_HANDLE = 0x0052,
 CSSM_ERRCODE_INVALID_TP_HANDLE = 0x0053,
 CSSM_ERRCODE_INVALID_KR_HANDLE = 0x0054,
 CSSM_ERRCODE_INVALID_AC_HANDLE = 0x0055,
 CSSM_ERRCODE_INVALID_PASSTHROUGH_ID = 0x0056,
 CSSM_ERRCODE_INVALID_NETWORK_ADDR = 0x0057,
 CSSM_ERRCODE_INVALID_CRYPTO_DATA = 0x0058
};


enum {
 CSSMERR_CSSM_INTERNAL_ERROR =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_INTERNAL_ERROR,
 CSSMERR_CSSM_MEMORY_ERROR =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_MEMORY_ERROR,
 CSSMERR_CSSM_MDS_ERROR =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_MDS_ERROR,
 CSSMERR_CSSM_INVALID_POINTER =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_INVALID_POINTER,
 CSSMERR_CSSM_INVALID_INPUT_POINTER =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_INVALID_INPUT_POINTER,
 CSSMERR_CSSM_INVALID_OUTPUT_POINTER =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_INVALID_OUTPUT_POINTER,
 CSSMERR_CSSM_FUNCTION_NOT_IMPLEMENTED =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_FUNCTION_NOT_IMPLEMENTED,
 CSSMERR_CSSM_SELF_CHECK_FAILED =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_SELF_CHECK_FAILED,
 CSSMERR_CSSM_OS_ACCESS_DENIED =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_OS_ACCESS_DENIED,
 CSSMERR_CSSM_FUNCTION_FAILED =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_FUNCTION_FAILED,
 CSSMERR_CSSM_MODULE_MANIFEST_VERIFY_FAILED =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_MODULE_MANIFEST_VERIFY_FAILED,
 CSSMERR_CSSM_INVALID_GUID =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_INVALID_GUID
};


enum {
 CSSMERR_CSSM_INVALID_CONTEXT_HANDLE =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_INVALID_CONTEXT_HANDLE,
 CSSMERR_CSSM_INCOMPATIBLE_VERSION =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_INCOMPATIBLE_VERSION,
 CSSMERR_CSSM_PRIVILEGE_NOT_GRANTED =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_PRIVILEGE_NOT_GRANTED
};


enum {
 CSSM_CSSM_BASE_CSSM_ERROR =
  CSSM_CSSM_BASE_ERROR + CSSM_ERRORCODE_COMMON_EXTENT + 0x10,
 CSSMERR_CSSM_SCOPE_NOT_SUPPORTED = CSSM_CSSM_BASE_CSSM_ERROR + 1,
 CSSMERR_CSSM_PVC_ALREADY_CONFIGURED = CSSM_CSSM_BASE_CSSM_ERROR + 2,
 CSSMERR_CSSM_INVALID_PVC = CSSM_CSSM_BASE_CSSM_ERROR + 3,
 CSSMERR_CSSM_EMM_LOAD_FAILED = CSSM_CSSM_BASE_CSSM_ERROR + 4,
 CSSMERR_CSSM_EMM_UNLOAD_FAILED = CSSM_CSSM_BASE_CSSM_ERROR + 5,
 CSSMERR_CSSM_ADDIN_LOAD_FAILED = CSSM_CSSM_BASE_CSSM_ERROR + 6,
 CSSMERR_CSSM_INVALID_KEY_HIERARCHY = CSSM_CSSM_BASE_CSSM_ERROR + 7,
 CSSMERR_CSSM_ADDIN_UNLOAD_FAILED = CSSM_CSSM_BASE_CSSM_ERROR + 8,
 CSSMERR_CSSM_LIB_REF_NOT_FOUND = CSSM_CSSM_BASE_CSSM_ERROR + 9,
 CSSMERR_CSSM_INVALID_ADDIN_FUNCTION_TABLE = CSSM_CSSM_BASE_CSSM_ERROR + 10,
 CSSMERR_CSSM_EMM_AUTHENTICATE_FAILED = CSSM_CSSM_BASE_CSSM_ERROR + 11,
 CSSMERR_CSSM_ADDIN_AUTHENTICATE_FAILED = CSSM_CSSM_BASE_CSSM_ERROR + 12,
 CSSMERR_CSSM_INVALID_SERVICE_MASK = CSSM_CSSM_BASE_CSSM_ERROR + 13,
 CSSMERR_CSSM_MODULE_NOT_LOADED = CSSM_CSSM_BASE_CSSM_ERROR + 14,
 CSSMERR_CSSM_INVALID_SUBSERVICEID = CSSM_CSSM_BASE_CSSM_ERROR + 15,
 CSSMERR_CSSM_BUFFER_TOO_SMALL = CSSM_CSSM_BASE_CSSM_ERROR + 16,
 CSSMERR_CSSM_INVALID_ATTRIBUTE = CSSM_CSSM_BASE_CSSM_ERROR + 17,
 CSSMERR_CSSM_ATTRIBUTE_NOT_IN_CONTEXT = CSSM_CSSM_BASE_CSSM_ERROR + 18,
 CSSMERR_CSSM_MODULE_MANAGER_INITIALIZE_FAIL = CSSM_CSSM_BASE_CSSM_ERROR + 19,
 CSSMERR_CSSM_MODULE_MANAGER_NOT_FOUND = CSSM_CSSM_BASE_CSSM_ERROR + 20,
 CSSMERR_CSSM_EVENT_NOTIFICATION_CALLBACK_NOT_FOUND = CSSM_CSSM_BASE_CSSM_ERROR + 21
};


enum {
 CSSMERR_CSP_INTERNAL_ERROR =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_INTERNAL_ERROR,
 CSSMERR_CSP_MEMORY_ERROR =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_MEMORY_ERROR,
 CSSMERR_CSP_MDS_ERROR =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_MDS_ERROR,
 CSSMERR_CSP_INVALID_POINTER =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_INVALID_POINTER,
 CSSMERR_CSP_INVALID_INPUT_POINTER =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_INVALID_INPUT_POINTER,
 CSSMERR_CSP_INVALID_OUTPUT_POINTER =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_INVALID_OUTPUT_POINTER,
 CSSMERR_CSP_FUNCTION_NOT_IMPLEMENTED =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_FUNCTION_NOT_IMPLEMENTED,
 CSSMERR_CSP_SELF_CHECK_FAILED =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_SELF_CHECK_FAILED,
 CSSMERR_CSP_OS_ACCESS_DENIED =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_OS_ACCESS_DENIED,
 CSSMERR_CSP_FUNCTION_FAILED =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_FUNCTION_FAILED
};


enum {
 CSSMERR_CSP_OPERATION_AUTH_DENIED =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_OPERATION_AUTH_DENIED,
 CSSMERR_CSP_OBJECT_USE_AUTH_DENIED =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_OBJECT_USE_AUTH_DENIED,
 CSSMERR_CSP_OBJECT_MANIP_AUTH_DENIED =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_OBJECT_MANIP_AUTH_DENIED,
 CSSMERR_CSP_OBJECT_ACL_NOT_SUPPORTED =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_OBJECT_ACL_NOT_SUPPORTED,
 CSSMERR_CSP_OBJECT_ACL_REQUIRED =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_OBJECT_ACL_REQUIRED,
 CSSMERR_CSP_INVALID_ACCESS_CREDENTIALS =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_INVALID_ACCESS_CREDENTIALS,
 CSSMERR_CSP_INVALID_ACL_BASE_CERTS =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_INVALID_ACL_BASE_CERTS,
 CSSMERR_CSP_ACL_BASE_CERTS_NOT_SUPPORTED =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_ACL_BASE_CERTS_NOT_SUPPORTED,
 CSSMERR_CSP_INVALID_SAMPLE_VALUE =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_INVALID_SAMPLE_VALUE,
 CSSMERR_CSP_SAMPLE_VALUE_NOT_SUPPORTED =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_SAMPLE_VALUE_NOT_SUPPORTED,
 CSSMERR_CSP_INVALID_ACL_SUBJECT_VALUE =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_INVALID_ACL_SUBJECT_VALUE,
 CSSMERR_CSP_ACL_SUBJECT_TYPE_NOT_SUPPORTED =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_ACL_SUBJECT_TYPE_NOT_SUPPORTED,
 CSSMERR_CSP_INVALID_ACL_CHALLENGE_CALLBACK =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_INVALID_ACL_CHALLENGE_CALLBACK,
 CSSMERR_CSP_ACL_CHALLENGE_CALLBACK_FAILED =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_ACL_CHALLENGE_CALLBACK_FAILED,
 CSSMERR_CSP_INVALID_ACL_ENTRY_TAG =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_INVALID_ACL_ENTRY_TAG,
 CSSMERR_CSP_ACL_ENTRY_TAG_NOT_FOUND =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_ACL_ENTRY_TAG_NOT_FOUND,
 CSSMERR_CSP_INVALID_ACL_EDIT_MODE =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_INVALID_ACL_EDIT_MODE,
 CSSMERR_CSP_ACL_CHANGE_FAILED =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_ACL_CHANGE_FAILED,
 CSSMERR_CSP_INVALID_NEW_ACL_ENTRY =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_INVALID_NEW_ACL_ENTRY,
 CSSMERR_CSP_INVALID_NEW_ACL_OWNER =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_INVALID_NEW_ACL_OWNER,
 CSSMERR_CSP_ACL_DELETE_FAILED =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_ACL_DELETE_FAILED,
 CSSMERR_CSP_ACL_REPLACE_FAILED =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_ACL_REPLACE_FAILED,
 CSSMERR_CSP_ACL_ADD_FAILED =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_ACL_ADD_FAILED
};


enum {
 CSSMERR_CSP_INVALID_CONTEXT_HANDLE =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_INVALID_CONTEXT_HANDLE,
 CSSMERR_CSP_PRIVILEGE_NOT_GRANTED =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_PRIVILEGE_NOT_GRANTED,
 CSSMERR_CSP_INVALID_DATA =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_INVALID_DATA,
 CSSMERR_CSP_INVALID_PASSTHROUGH_ID =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_INVALID_PASSTHROUGH_ID,
 CSSMERR_CSP_INVALID_CRYPTO_DATA =
  CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_INVALID_CRYPTO_DATA
};


enum {

 CSSM_CSP_BASE_CSP_ERROR =
  CSSM_CSP_BASE_ERROR + CSSM_ERRORCODE_COMMON_EXTENT,
 CSSMERR_CSP_INPUT_LENGTH_ERROR = CSSM_CSP_BASE_CSP_ERROR + 1,
 CSSMERR_CSP_OUTPUT_LENGTH_ERROR = CSSM_CSP_BASE_CSP_ERROR + 2,
 CSSMERR_CSP_PRIVILEGE_NOT_SUPPORTED = CSSM_CSP_BASE_CSP_ERROR + 3,
 CSSMERR_CSP_DEVICE_ERROR = CSSM_CSP_BASE_CSP_ERROR + 4,
 CSSMERR_CSP_DEVICE_MEMORY_ERROR = CSSM_CSP_BASE_CSP_ERROR + 5,
 CSSMERR_CSP_ATTACH_HANDLE_BUSY = CSSM_CSP_BASE_CSP_ERROR + 6,
 CSSMERR_CSP_NOT_LOGGED_IN = CSSM_CSP_BASE_CSP_ERROR + 7,
 CSSMERR_CSP_INVALID_KEY = CSSM_CSP_BASE_CSP_ERROR + 16,
 CSSMERR_CSP_INVALID_KEY_REFERENCE = CSSM_CSP_BASE_CSP_ERROR + 17,
 CSSMERR_CSP_INVALID_KEY_CLASS = CSSM_CSP_BASE_CSP_ERROR + 18,
 CSSMERR_CSP_ALGID_MISMATCH = CSSM_CSP_BASE_CSP_ERROR + 19,
 CSSMERR_CSP_KEY_USAGE_INCORRECT = CSSM_CSP_BASE_CSP_ERROR + 20,
 CSSMERR_CSP_KEY_BLOB_TYPE_INCORRECT = CSSM_CSP_BASE_CSP_ERROR + 21,
 CSSMERR_CSP_KEY_HEADER_INCONSISTENT = CSSM_CSP_BASE_CSP_ERROR + 22,
 CSSMERR_CSP_UNSUPPORTED_KEY_FORMAT = CSSM_CSP_BASE_CSP_ERROR + 23,
 CSSMERR_CSP_UNSUPPORTED_KEY_SIZE = CSSM_CSP_BASE_CSP_ERROR + 24,
 CSSMERR_CSP_INVALID_KEY_POINTER = CSSM_CSP_BASE_CSP_ERROR + 25,
 CSSMERR_CSP_INVALID_KEYUSAGE_MASK = CSSM_CSP_BASE_CSP_ERROR + 26,
 CSSMERR_CSP_UNSUPPORTED_KEYUSAGE_MASK = CSSM_CSP_BASE_CSP_ERROR + 27,
 CSSMERR_CSP_INVALID_KEYATTR_MASK = CSSM_CSP_BASE_CSP_ERROR + 28,
 CSSMERR_CSP_UNSUPPORTED_KEYATTR_MASK = CSSM_CSP_BASE_CSP_ERROR + 29,
 CSSMERR_CSP_INVALID_KEY_LABEL = CSSM_CSP_BASE_CSP_ERROR + 30,
 CSSMERR_CSP_UNSUPPORTED_KEY_LABEL = CSSM_CSP_BASE_CSP_ERROR + 31,
 CSSMERR_CSP_INVALID_KEY_FORMAT = CSSM_CSP_BASE_CSP_ERROR + 32,


 CSSMERR_CSP_INVALID_DATA_COUNT = CSSM_CSP_BASE_CSP_ERROR + 40,
 CSSMERR_CSP_VECTOR_OF_BUFS_UNSUPPORTED = CSSM_CSP_BASE_CSP_ERROR + 41,
 CSSMERR_CSP_INVALID_INPUT_VECTOR = CSSM_CSP_BASE_CSP_ERROR + 42,
 CSSMERR_CSP_INVALID_OUTPUT_VECTOR = CSSM_CSP_BASE_CSP_ERROR + 43,


 CSSMERR_CSP_INVALID_CONTEXT = CSSM_CSP_BASE_CSP_ERROR + 48,
 CSSMERR_CSP_INVALID_ALGORITHM = CSSM_CSP_BASE_CSP_ERROR + 49,
 CSSMERR_CSP_INVALID_ATTR_KEY = CSSM_CSP_BASE_CSP_ERROR + 54,
 CSSMERR_CSP_MISSING_ATTR_KEY = CSSM_CSP_BASE_CSP_ERROR + 55,
 CSSMERR_CSP_INVALID_ATTR_INIT_VECTOR = CSSM_CSP_BASE_CSP_ERROR + 56,
 CSSMERR_CSP_MISSING_ATTR_INIT_VECTOR = CSSM_CSP_BASE_CSP_ERROR + 57,
 CSSMERR_CSP_INVALID_ATTR_SALT = CSSM_CSP_BASE_CSP_ERROR + 58,
 CSSMERR_CSP_MISSING_ATTR_SALT = CSSM_CSP_BASE_CSP_ERROR + 59,
 CSSMERR_CSP_INVALID_ATTR_PADDING = CSSM_CSP_BASE_CSP_ERROR + 60,
 CSSMERR_CSP_MISSING_ATTR_PADDING = CSSM_CSP_BASE_CSP_ERROR + 61,
 CSSMERR_CSP_INVALID_ATTR_RANDOM = CSSM_CSP_BASE_CSP_ERROR + 62,
 CSSMERR_CSP_MISSING_ATTR_RANDOM = CSSM_CSP_BASE_CSP_ERROR + 63,
 CSSMERR_CSP_INVALID_ATTR_SEED = CSSM_CSP_BASE_CSP_ERROR + 64,
 CSSMERR_CSP_MISSING_ATTR_SEED = CSSM_CSP_BASE_CSP_ERROR + 65,
 CSSMERR_CSP_INVALID_ATTR_PASSPHRASE = CSSM_CSP_BASE_CSP_ERROR + 66,
 CSSMERR_CSP_MISSING_ATTR_PASSPHRASE = CSSM_CSP_BASE_CSP_ERROR + 67,
 CSSMERR_CSP_INVALID_ATTR_KEY_LENGTH = CSSM_CSP_BASE_CSP_ERROR + 68,
 CSSMERR_CSP_MISSING_ATTR_KEY_LENGTH = CSSM_CSP_BASE_CSP_ERROR + 69,
 CSSMERR_CSP_INVALID_ATTR_BLOCK_SIZE = CSSM_CSP_BASE_CSP_ERROR + 70,
 CSSMERR_CSP_MISSING_ATTR_BLOCK_SIZE = CSSM_CSP_BASE_CSP_ERROR + 71,
 CSSMERR_CSP_INVALID_ATTR_OUTPUT_SIZE = CSSM_CSP_BASE_CSP_ERROR + 100,
 CSSMERR_CSP_MISSING_ATTR_OUTPUT_SIZE = CSSM_CSP_BASE_CSP_ERROR + 101,
 CSSMERR_CSP_INVALID_ATTR_ROUNDS = CSSM_CSP_BASE_CSP_ERROR + 102,
 CSSMERR_CSP_MISSING_ATTR_ROUNDS = CSSM_CSP_BASE_CSP_ERROR + 103,
 CSSMERR_CSP_INVALID_ATTR_ALG_PARAMS = CSSM_CSP_BASE_CSP_ERROR + 104,
 CSSMERR_CSP_MISSING_ATTR_ALG_PARAMS = CSSM_CSP_BASE_CSP_ERROR + 105,
 CSSMERR_CSP_INVALID_ATTR_LABEL = CSSM_CSP_BASE_CSP_ERROR + 106,
 CSSMERR_CSP_MISSING_ATTR_LABEL = CSSM_CSP_BASE_CSP_ERROR + 107,
 CSSMERR_CSP_INVALID_ATTR_KEY_TYPE = CSSM_CSP_BASE_CSP_ERROR + 108,
 CSSMERR_CSP_MISSING_ATTR_KEY_TYPE = CSSM_CSP_BASE_CSP_ERROR + 109,
 CSSMERR_CSP_INVALID_ATTR_MODE = CSSM_CSP_BASE_CSP_ERROR + 110,
 CSSMERR_CSP_MISSING_ATTR_MODE = CSSM_CSP_BASE_CSP_ERROR + 111,
 CSSMERR_CSP_INVALID_ATTR_EFFECTIVE_BITS = CSSM_CSP_BASE_CSP_ERROR + 112,
 CSSMERR_CSP_MISSING_ATTR_EFFECTIVE_BITS = CSSM_CSP_BASE_CSP_ERROR + 113,
 CSSMERR_CSP_INVALID_ATTR_START_DATE = CSSM_CSP_BASE_CSP_ERROR + 114,
 CSSMERR_CSP_MISSING_ATTR_START_DATE = CSSM_CSP_BASE_CSP_ERROR + 115,
 CSSMERR_CSP_INVALID_ATTR_END_DATE = CSSM_CSP_BASE_CSP_ERROR + 116,
 CSSMERR_CSP_MISSING_ATTR_END_DATE = CSSM_CSP_BASE_CSP_ERROR + 117,
 CSSMERR_CSP_INVALID_ATTR_VERSION = CSSM_CSP_BASE_CSP_ERROR + 118,
 CSSMERR_CSP_MISSING_ATTR_VERSION = CSSM_CSP_BASE_CSP_ERROR + 119,
 CSSMERR_CSP_INVALID_ATTR_PRIME = CSSM_CSP_BASE_CSP_ERROR + 120,
 CSSMERR_CSP_MISSING_ATTR_PRIME = CSSM_CSP_BASE_CSP_ERROR + 121,
 CSSMERR_CSP_INVALID_ATTR_BASE = CSSM_CSP_BASE_CSP_ERROR + 122,
 CSSMERR_CSP_MISSING_ATTR_BASE = CSSM_CSP_BASE_CSP_ERROR + 123,
 CSSMERR_CSP_INVALID_ATTR_SUBPRIME = CSSM_CSP_BASE_CSP_ERROR + 124,
 CSSMERR_CSP_MISSING_ATTR_SUBPRIME = CSSM_CSP_BASE_CSP_ERROR + 125,
 CSSMERR_CSP_INVALID_ATTR_ITERATION_COUNT = CSSM_CSP_BASE_CSP_ERROR + 126,
 CSSMERR_CSP_MISSING_ATTR_ITERATION_COUNT = CSSM_CSP_BASE_CSP_ERROR + 127,
 CSSMERR_CSP_INVALID_ATTR_DL_DB_HANDLE = CSSM_CSP_BASE_CSP_ERROR + 128,
 CSSMERR_CSP_MISSING_ATTR_DL_DB_HANDLE = CSSM_CSP_BASE_CSP_ERROR + 129,
 CSSMERR_CSP_INVALID_ATTR_ACCESS_CREDENTIALS = CSSM_CSP_BASE_CSP_ERROR + 130,
 CSSMERR_CSP_MISSING_ATTR_ACCESS_CREDENTIALS = CSSM_CSP_BASE_CSP_ERROR + 131,
 CSSMERR_CSP_INVALID_ATTR_PUBLIC_KEY_FORMAT = CSSM_CSP_BASE_CSP_ERROR + 132,
 CSSMERR_CSP_MISSING_ATTR_PUBLIC_KEY_FORMAT = CSSM_CSP_BASE_CSP_ERROR + 133,
 CSSMERR_CSP_INVALID_ATTR_PRIVATE_KEY_FORMAT = CSSM_CSP_BASE_CSP_ERROR + 134,
 CSSMERR_CSP_MISSING_ATTR_PRIVATE_KEY_FORMAT = CSSM_CSP_BASE_CSP_ERROR + 135,
 CSSMERR_CSP_INVALID_ATTR_SYMMETRIC_KEY_FORMAT = CSSM_CSP_BASE_CSP_ERROR + 136,
 CSSMERR_CSP_MISSING_ATTR_SYMMETRIC_KEY_FORMAT = CSSM_CSP_BASE_CSP_ERROR + 137,
 CSSMERR_CSP_INVALID_ATTR_WRAPPED_KEY_FORMAT = CSSM_CSP_BASE_CSP_ERROR + 138,
 CSSMERR_CSP_MISSING_ATTR_WRAPPED_KEY_FORMAT = CSSM_CSP_BASE_CSP_ERROR + 139,


 CSSMERR_CSP_STAGED_OPERATION_IN_PROGRESS = CSSM_CSP_BASE_CSP_ERROR + 72,
 CSSMERR_CSP_STAGED_OPERATION_NOT_STARTED = CSSM_CSP_BASE_CSP_ERROR + 73,
 CSSMERR_CSP_VERIFY_FAILED = CSSM_CSP_BASE_CSP_ERROR + 74,
 CSSMERR_CSP_INVALID_SIGNATURE = CSSM_CSP_BASE_CSP_ERROR + 75,
 CSSMERR_CSP_QUERY_SIZE_UNKNOWN = CSSM_CSP_BASE_CSP_ERROR + 76,
 CSSMERR_CSP_BLOCK_SIZE_MISMATCH = CSSM_CSP_BASE_CSP_ERROR + 77,
 CSSMERR_CSP_PRIVATE_KEY_NOT_FOUND = CSSM_CSP_BASE_CSP_ERROR + 78,
 CSSMERR_CSP_PUBLIC_KEY_INCONSISTENT = CSSM_CSP_BASE_CSP_ERROR + 79,
 CSSMERR_CSP_DEVICE_VERIFY_FAILED = CSSM_CSP_BASE_CSP_ERROR + 80,
 CSSMERR_CSP_INVALID_LOGIN_NAME = CSSM_CSP_BASE_CSP_ERROR + 81,
 CSSMERR_CSP_ALREADY_LOGGED_IN = CSSM_CSP_BASE_CSP_ERROR + 82,
 CSSMERR_CSP_PRIVATE_KEY_ALREADY_EXISTS = CSSM_CSP_BASE_CSP_ERROR + 83,
 CSSMERR_CSP_KEY_LABEL_ALREADY_EXISTS = CSSM_CSP_BASE_CSP_ERROR + 84,
 CSSMERR_CSP_INVALID_DIGEST_ALGORITHM = CSSM_CSP_BASE_CSP_ERROR + 85,
 CSSMERR_CSP_CRYPTO_DATA_CALLBACK_FAILED = CSSM_CSP_BASE_CSP_ERROR + 86
};



enum {
 CSSMERR_TP_INTERNAL_ERROR =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INTERNAL_ERROR,
 CSSMERR_TP_MEMORY_ERROR =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_MEMORY_ERROR,
 CSSMERR_TP_MDS_ERROR =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_MDS_ERROR,
 CSSMERR_TP_INVALID_POINTER =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INVALID_POINTER,
 CSSMERR_TP_INVALID_INPUT_POINTER =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INVALID_INPUT_POINTER,
 CSSMERR_TP_INVALID_OUTPUT_POINTER =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INVALID_OUTPUT_POINTER,
 CSSMERR_TP_FUNCTION_NOT_IMPLEMENTED =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_FUNCTION_NOT_IMPLEMENTED,
 CSSMERR_TP_SELF_CHECK_FAILED =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_SELF_CHECK_FAILED,
 CSSMERR_TP_OS_ACCESS_DENIED =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_OS_ACCESS_DENIED,
 CSSMERR_TP_FUNCTION_FAILED =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_FUNCTION_FAILED,
 CSSMERR_TP_INVALID_CONTEXT_HANDLE =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INVALID_CONTEXT_HANDLE,
 CSSMERR_TP_INVALID_DATA =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INVALID_DATA,
 CSSMERR_TP_INVALID_DB_LIST =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INVALID_DB_LIST,
 CSSMERR_TP_INVALID_CERTGROUP_POINTER =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INVALID_CERTGROUP_POINTER,
 CSSMERR_TP_INVALID_CERT_POINTER =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INVALID_CERT_POINTER,
 CSSMERR_TP_INVALID_CRL_POINTER =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INVALID_CRL_POINTER,
 CSSMERR_TP_INVALID_FIELD_POINTER =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INVALID_FIELD_POINTER,
 CSSMERR_TP_INVALID_NETWORK_ADDR =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INVALID_NETWORK_ADDR,
 CSSMERR_TP_CRL_ALREADY_SIGNED =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_CRL_ALREADY_SIGNED,
 CSSMERR_TP_INVALID_NUMBER_OF_FIELDS =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INVALID_NUMBER_OF_FIELDS,
 CSSMERR_TP_VERIFICATION_FAILURE =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_VERIFICATION_FAILURE,
 CSSMERR_TP_INVALID_DB_HANDLE =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INVALID_DB_HANDLE,
 CSSMERR_TP_UNKNOWN_FORMAT =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_UNKNOWN_FORMAT,
 CSSMERR_TP_UNKNOWN_TAG =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_UNKNOWN_TAG,
 CSSMERR_TP_INVALID_PASSTHROUGH_ID =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INVALID_PASSTHROUGH_ID,
 CSSMERR_TP_INVALID_CSP_HANDLE =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INVALID_CSP_HANDLE,
 CSSMERR_TP_INVALID_DL_HANDLE =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INVALID_DL_HANDLE,
 CSSMERR_TP_INVALID_CL_HANDLE =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INVALID_CL_HANDLE,
 CSSMERR_TP_INVALID_DB_LIST_POINTER =
  CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INVALID_DB_LIST_POINTER
};


enum {
 CSSM_TP_BASE_TP_ERROR =
  CSSM_TP_BASE_ERROR + CSSM_ERRORCODE_COMMON_EXTENT,
 CSSMERR_TP_INVALID_CALLERAUTH_CONTEXT_POINTER = CSSM_TP_BASE_TP_ERROR + 1,
 CSSMERR_TP_INVALID_IDENTIFIER_POINTER = CSSM_TP_BASE_TP_ERROR + 2,
 CSSMERR_TP_INVALID_KEYCACHE_HANDLE = CSSM_TP_BASE_TP_ERROR + 3,
 CSSMERR_TP_INVALID_CERTGROUP = CSSM_TP_BASE_TP_ERROR + 4,
 CSSMERR_TP_INVALID_CRLGROUP = CSSM_TP_BASE_TP_ERROR + 5,
 CSSMERR_TP_INVALID_CRLGROUP_POINTER = CSSM_TP_BASE_TP_ERROR + 6,
 CSSMERR_TP_AUTHENTICATION_FAILED = CSSM_TP_BASE_TP_ERROR + 7,
 CSSMERR_TP_CERTGROUP_INCOMPLETE = CSSM_TP_BASE_TP_ERROR + 8,
 CSSMERR_TP_CERTIFICATE_CANT_OPERATE = CSSM_TP_BASE_TP_ERROR + 9,
 CSSMERR_TP_CERT_EXPIRED = CSSM_TP_BASE_TP_ERROR + 10,
 CSSMERR_TP_CERT_NOT_VALID_YET = CSSM_TP_BASE_TP_ERROR + 11,
 CSSMERR_TP_CERT_REVOKED = CSSM_TP_BASE_TP_ERROR + 12,
 CSSMERR_TP_CERT_SUSPENDED = CSSM_TP_BASE_TP_ERROR + 13,
 CSSMERR_TP_INSUFFICIENT_CREDENTIALS = CSSM_TP_BASE_TP_ERROR + 14,
 CSSMERR_TP_INVALID_ACTION = CSSM_TP_BASE_TP_ERROR + 15,
 CSSMERR_TP_INVALID_ACTION_DATA = CSSM_TP_BASE_TP_ERROR + 16,
 CSSMERR_TP_INVALID_ANCHOR_CERT = CSSM_TP_BASE_TP_ERROR + 18,
 CSSMERR_TP_INVALID_AUTHORITY = CSSM_TP_BASE_TP_ERROR + 19,
 CSSMERR_TP_VERIFY_ACTION_FAILED = CSSM_TP_BASE_TP_ERROR + 20,
 CSSMERR_TP_INVALID_CERTIFICATE = CSSM_TP_BASE_TP_ERROR + 21,
 CSSMERR_TP_INVALID_CERT_AUTHORITY = CSSM_TP_BASE_TP_ERROR + 22,
 CSSMERR_TP_INVALID_CRL_AUTHORITY = CSSM_TP_BASE_TP_ERROR + 23,
 CSSMERR_TP_INVALID_CRL_ENCODING = CSSM_TP_BASE_TP_ERROR + 24,
 CSSMERR_TP_INVALID_CRL_TYPE = CSSM_TP_BASE_TP_ERROR + 25,
 CSSMERR_TP_INVALID_CRL = CSSM_TP_BASE_TP_ERROR + 26,
 CSSMERR_TP_INVALID_FORM_TYPE = CSSM_TP_BASE_TP_ERROR + 27,
 CSSMERR_TP_INVALID_ID = CSSM_TP_BASE_TP_ERROR + 28,
 CSSMERR_TP_INVALID_IDENTIFIER = CSSM_TP_BASE_TP_ERROR + 29,
 CSSMERR_TP_INVALID_INDEX = CSSM_TP_BASE_TP_ERROR + 30,
 CSSMERR_TP_INVALID_NAME = CSSM_TP_BASE_TP_ERROR + 31,
 CSSMERR_TP_INVALID_POLICY_IDENTIFIERS = CSSM_TP_BASE_TP_ERROR + 32,
 CSSMERR_TP_INVALID_TIMESTRING = CSSM_TP_BASE_TP_ERROR + 33,
 CSSMERR_TP_INVALID_REASON = CSSM_TP_BASE_TP_ERROR + 34,
 CSSMERR_TP_INVALID_REQUEST_INPUTS = CSSM_TP_BASE_TP_ERROR + 35,
 CSSMERR_TP_INVALID_RESPONSE_VECTOR = CSSM_TP_BASE_TP_ERROR + 36,
 CSSMERR_TP_INVALID_SIGNATURE = CSSM_TP_BASE_TP_ERROR + 37,
 CSSMERR_TP_INVALID_STOP_ON_POLICY = CSSM_TP_BASE_TP_ERROR + 38,
 CSSMERR_TP_INVALID_CALLBACK = CSSM_TP_BASE_TP_ERROR + 39,
 CSSMERR_TP_INVALID_TUPLE = CSSM_TP_BASE_TP_ERROR + 40,
 CSSMERR_TP_NOT_SIGNER = CSSM_TP_BASE_TP_ERROR + 41,
 CSSMERR_TP_NOT_TRUSTED = CSSM_TP_BASE_TP_ERROR + 42,
 CSSMERR_TP_NO_DEFAULT_AUTHORITY = CSSM_TP_BASE_TP_ERROR + 43,
 CSSMERR_TP_REJECTED_FORM = CSSM_TP_BASE_TP_ERROR + 44,
 CSSMERR_TP_REQUEST_LOST = CSSM_TP_BASE_TP_ERROR + 45,
 CSSMERR_TP_REQUEST_REJECTED = CSSM_TP_BASE_TP_ERROR + 46,
 CSSMERR_TP_UNSUPPORTED_ADDR_TYPE = CSSM_TP_BASE_TP_ERROR + 47,
 CSSMERR_TP_UNSUPPORTED_SERVICE = CSSM_TP_BASE_TP_ERROR + 48,
 CSSMERR_TP_INVALID_TUPLEGROUP_POINTER = CSSM_TP_BASE_TP_ERROR + 49,
 CSSMERR_TP_INVALID_TUPLEGROUP = CSSM_TP_BASE_TP_ERROR + 50
};


enum {
 CSSMERR_AC_INTERNAL_ERROR =
  CSSM_AC_BASE_ERROR + CSSM_ERRCODE_INTERNAL_ERROR,
 CSSMERR_AC_MEMORY_ERROR =
  CSSM_AC_BASE_ERROR + CSSM_ERRCODE_MEMORY_ERROR,
 CSSMERR_AC_MDS_ERROR =
  CSSM_AC_BASE_ERROR + CSSM_ERRCODE_MDS_ERROR,
 CSSMERR_AC_INVALID_POINTER =
  CSSM_AC_BASE_ERROR + CSSM_ERRCODE_INVALID_POINTER,
 CSSMERR_AC_INVALID_INPUT_POINTER =
  CSSM_AC_BASE_ERROR + CSSM_ERRCODE_INVALID_INPUT_POINTER,
 CSSMERR_AC_INVALID_OUTPUT_POINTER =
  CSSM_AC_BASE_ERROR + CSSM_ERRCODE_INVALID_OUTPUT_POINTER,
 CSSMERR_AC_FUNCTION_NOT_IMPLEMENTED =
  CSSM_AC_BASE_ERROR + CSSM_ERRCODE_FUNCTION_NOT_IMPLEMENTED,
 CSSMERR_AC_SELF_CHECK_FAILED =
  CSSM_AC_BASE_ERROR + CSSM_ERRCODE_SELF_CHECK_FAILED,
 CSSMERR_AC_OS_ACCESS_DENIED =
  CSSM_AC_BASE_ERROR + CSSM_ERRCODE_OS_ACCESS_DENIED,
 CSSMERR_AC_FUNCTION_FAILED =
  CSSM_AC_BASE_ERROR + CSSM_ERRCODE_FUNCTION_FAILED,
 CSSMERR_AC_INVALID_CONTEXT_HANDLE =
  CSSM_AC_BASE_ERROR + CSSM_ERRCODE_INVALID_CONTEXT_HANDLE,
 CSSMERR_AC_INVALID_DATA =
  CSSM_AC_BASE_ERROR + CSSM_ERRCODE_INVALID_DATA,
 CSSMERR_AC_INVALID_DB_LIST =
  CSSM_AC_BASE_ERROR + CSSM_ERRCODE_INVALID_DB_LIST,
 CSSMERR_AC_INVALID_PASSTHROUGH_ID =
  CSSM_AC_BASE_ERROR + CSSM_ERRCODE_INVALID_PASSTHROUGH_ID,
 CSSMERR_AC_INVALID_DL_HANDLE =
  CSSM_AC_BASE_ERROR + CSSM_ERRCODE_INVALID_DL_HANDLE,
 CSSMERR_AC_INVALID_CL_HANDLE =
  CSSM_AC_BASE_ERROR + CSSM_ERRCODE_INVALID_CL_HANDLE,
 CSSMERR_AC_INVALID_TP_HANDLE =
  CSSM_AC_BASE_ERROR + CSSM_ERRCODE_INVALID_TP_HANDLE,
 CSSMERR_AC_INVALID_DB_HANDLE =
  CSSM_AC_BASE_ERROR + CSSM_ERRCODE_INVALID_DB_HANDLE,
 CSSMERR_AC_INVALID_DB_LIST_POINTER =
  CSSM_AC_BASE_ERROR + CSSM_ERRCODE_INVALID_DB_LIST_POINTER
};


enum {
 CSSM_AC_BASE_AC_ERROR =
  CSSM_AC_BASE_ERROR + CSSM_ERRORCODE_COMMON_EXTENT,
 CSSMERR_AC_INVALID_BASE_ACLS = CSSM_AC_BASE_AC_ERROR + 1,
 CSSMERR_AC_INVALID_TUPLE_CREDENTIALS = CSSM_AC_BASE_AC_ERROR + 2,
 CSSMERR_AC_INVALID_ENCODING = CSSM_AC_BASE_AC_ERROR + 3,
 CSSMERR_AC_INVALID_VALIDITY_PERIOD = CSSM_AC_BASE_AC_ERROR + 4,
 CSSMERR_AC_INVALID_REQUESTOR = CSSM_AC_BASE_AC_ERROR + 5,
 CSSMERR_AC_INVALID_REQUEST_DESCRIPTOR = CSSM_AC_BASE_AC_ERROR + 6
};


enum {
 CSSMERR_CL_INTERNAL_ERROR =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_INTERNAL_ERROR,
 CSSMERR_CL_MEMORY_ERROR =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_MEMORY_ERROR,
 CSSMERR_CL_MDS_ERROR =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_MDS_ERROR,
 CSSMERR_CL_INVALID_POINTER =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_INVALID_POINTER,
 CSSMERR_CL_INVALID_INPUT_POINTER =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_INVALID_INPUT_POINTER,
 CSSMERR_CL_INVALID_OUTPUT_POINTER =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_INVALID_OUTPUT_POINTER,
 CSSMERR_CL_FUNCTION_NOT_IMPLEMENTED =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_FUNCTION_NOT_IMPLEMENTED,
 CSSMERR_CL_SELF_CHECK_FAILED =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_SELF_CHECK_FAILED,
 CSSMERR_CL_OS_ACCESS_DENIED =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_OS_ACCESS_DENIED,
 CSSMERR_CL_FUNCTION_FAILED =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_FUNCTION_FAILED,
 CSSMERR_CL_INVALID_CONTEXT_HANDLE =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_INVALID_CONTEXT_HANDLE,
 CSSMERR_CL_INVALID_CERTGROUP_POINTER =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_INVALID_CERTGROUP_POINTER,
 CSSMERR_CL_INVALID_CERT_POINTER =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_INVALID_CERT_POINTER,
 CSSMERR_CL_INVALID_CRL_POINTER =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_INVALID_CRL_POINTER,
 CSSMERR_CL_INVALID_FIELD_POINTER =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_INVALID_FIELD_POINTER,
 CSSMERR_CL_INVALID_DATA =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_INVALID_DATA,
 CSSMERR_CL_CRL_ALREADY_SIGNED =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_CRL_ALREADY_SIGNED,
 CSSMERR_CL_INVALID_NUMBER_OF_FIELDS =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_INVALID_NUMBER_OF_FIELDS,
 CSSMERR_CL_VERIFICATION_FAILURE =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_VERIFICATION_FAILURE,
 CSSMERR_CL_UNKNOWN_FORMAT =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_UNKNOWN_FORMAT,
 CSSMERR_CL_UNKNOWN_TAG =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_UNKNOWN_TAG,
 CSSMERR_CL_INVALID_PASSTHROUGH_ID =
  CSSM_CL_BASE_ERROR + CSSM_ERRCODE_INVALID_PASSTHROUGH_ID
};


enum {
 CSSM_CL_BASE_CL_ERROR =
  CSSM_CL_BASE_ERROR + CSSM_ERRORCODE_COMMON_EXTENT,
 CSSMERR_CL_INVALID_BUNDLE_POINTER = CSSM_CL_BASE_CL_ERROR + 1,
 CSSMERR_CL_INVALID_CACHE_HANDLE = CSSM_CL_BASE_CL_ERROR + 2,
 CSSMERR_CL_INVALID_RESULTS_HANDLE = CSSM_CL_BASE_CL_ERROR + 3,
 CSSMERR_CL_INVALID_BUNDLE_INFO = CSSM_CL_BASE_CL_ERROR + 4,
 CSSMERR_CL_INVALID_CRL_INDEX = CSSM_CL_BASE_CL_ERROR + 5,
 CSSMERR_CL_INVALID_SCOPE = CSSM_CL_BASE_CL_ERROR + 6,
 CSSMERR_CL_NO_FIELD_VALUES = CSSM_CL_BASE_CL_ERROR + 7,
 CSSMERR_CL_SCOPE_NOT_SUPPORTED = CSSM_CL_BASE_CL_ERROR + 8
};


enum {
 CSSMERR_DL_INTERNAL_ERROR =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INTERNAL_ERROR,
 CSSMERR_DL_MEMORY_ERROR =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_MEMORY_ERROR,
 CSSMERR_DL_MDS_ERROR =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_MDS_ERROR,
 CSSMERR_DL_INVALID_POINTER =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INVALID_POINTER,
 CSSMERR_DL_INVALID_INPUT_POINTER =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INVALID_INPUT_POINTER,
 CSSMERR_DL_INVALID_OUTPUT_POINTER =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INVALID_OUTPUT_POINTER,
 CSSMERR_DL_FUNCTION_NOT_IMPLEMENTED =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_FUNCTION_NOT_IMPLEMENTED,
 CSSMERR_DL_SELF_CHECK_FAILED =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_SELF_CHECK_FAILED,
 CSSMERR_DL_OS_ACCESS_DENIED =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_OS_ACCESS_DENIED,
 CSSMERR_DL_FUNCTION_FAILED =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_FUNCTION_FAILED,
 CSSMERR_DL_INVALID_CSP_HANDLE =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INVALID_CSP_HANDLE,
 CSSMERR_DL_INVALID_DL_HANDLE =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INVALID_DL_HANDLE,
 CSSMERR_DL_INVALID_CL_HANDLE =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INVALID_CL_HANDLE,
 CSSMERR_DL_INVALID_DB_LIST_POINTER =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INVALID_DB_LIST_POINTER
};


enum {
 CSSMERR_DL_OPERATION_AUTH_DENIED =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_OPERATION_AUTH_DENIED,
 CSSMERR_DL_OBJECT_USE_AUTH_DENIED =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_OBJECT_USE_AUTH_DENIED,
 CSSMERR_DL_OBJECT_MANIP_AUTH_DENIED =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_OBJECT_MANIP_AUTH_DENIED,
 CSSMERR_DL_OBJECT_ACL_NOT_SUPPORTED =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_OBJECT_ACL_NOT_SUPPORTED,
 CSSMERR_DL_OBJECT_ACL_REQUIRED =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_OBJECT_ACL_REQUIRED,
 CSSMERR_DL_INVALID_ACCESS_CREDENTIALS =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INVALID_ACCESS_CREDENTIALS,
 CSSMERR_DL_INVALID_ACL_BASE_CERTS =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INVALID_ACL_BASE_CERTS,
 CSSMERR_DL_ACL_BASE_CERTS_NOT_SUPPORTED =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_ACL_BASE_CERTS_NOT_SUPPORTED,
 CSSMERR_DL_INVALID_SAMPLE_VALUE =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INVALID_SAMPLE_VALUE,
 CSSMERR_DL_SAMPLE_VALUE_NOT_SUPPORTED =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_SAMPLE_VALUE_NOT_SUPPORTED,
 CSSMERR_DL_INVALID_ACL_SUBJECT_VALUE =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INVALID_ACL_SUBJECT_VALUE,
 CSSMERR_DL_ACL_SUBJECT_TYPE_NOT_SUPPORTED =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_ACL_SUBJECT_TYPE_NOT_SUPPORTED,
 CSSMERR_DL_INVALID_ACL_CHALLENGE_CALLBACK =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INVALID_ACL_CHALLENGE_CALLBACK,
 CSSMERR_DL_ACL_CHALLENGE_CALLBACK_FAILED =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_ACL_CHALLENGE_CALLBACK_FAILED,
 CSSMERR_DL_INVALID_ACL_ENTRY_TAG =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INVALID_ACL_ENTRY_TAG,
 CSSMERR_DL_ACL_ENTRY_TAG_NOT_FOUND =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_ACL_ENTRY_TAG_NOT_FOUND,
 CSSMERR_DL_INVALID_ACL_EDIT_MODE =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INVALID_ACL_EDIT_MODE,
 CSSMERR_DL_ACL_CHANGE_FAILED =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_ACL_CHANGE_FAILED,
 CSSMERR_DL_INVALID_NEW_ACL_ENTRY =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INVALID_NEW_ACL_ENTRY,
 CSSMERR_DL_INVALID_NEW_ACL_OWNER =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INVALID_NEW_ACL_OWNER,
 CSSMERR_DL_ACL_DELETE_FAILED =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_ACL_DELETE_FAILED,
 CSSMERR_DL_ACL_REPLACE_FAILED =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_ACL_REPLACE_FAILED,
 CSSMERR_DL_ACL_ADD_FAILED =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_ACL_ADD_FAILED
};


enum {
 CSSMERR_DL_INVALID_DB_HANDLE =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INVALID_DB_HANDLE,
 CSSMERR_DL_INVALID_PASSTHROUGH_ID =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INVALID_PASSTHROUGH_ID,
 CSSMERR_DL_INVALID_NETWORK_ADDR =
  CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INVALID_NETWORK_ADDR
};


enum {
 CSSM_DL_BASE_DL_ERROR =
  CSSM_DL_BASE_ERROR + CSSM_ERRORCODE_COMMON_EXTENT,
 CSSMERR_DL_DATABASE_CORRUPT = CSSM_DL_BASE_DL_ERROR + 1,
 CSSMERR_DL_INVALID_RECORD_INDEX = CSSM_DL_BASE_DL_ERROR + 8,
 CSSMERR_DL_INVALID_RECORDTYPE = CSSM_DL_BASE_DL_ERROR + 9,
 CSSMERR_DL_INVALID_FIELD_NAME = CSSM_DL_BASE_DL_ERROR + 10,
 CSSMERR_DL_UNSUPPORTED_FIELD_FORMAT = CSSM_DL_BASE_DL_ERROR + 11,
 CSSMERR_DL_UNSUPPORTED_INDEX_INFO = CSSM_DL_BASE_DL_ERROR + 12,
 CSSMERR_DL_UNSUPPORTED_LOCALITY = CSSM_DL_BASE_DL_ERROR + 13,
 CSSMERR_DL_UNSUPPORTED_NUM_ATTRIBUTES = CSSM_DL_BASE_DL_ERROR + 14,
 CSSMERR_DL_UNSUPPORTED_NUM_INDEXES = CSSM_DL_BASE_DL_ERROR + 15,
 CSSMERR_DL_UNSUPPORTED_NUM_RECORDTYPES = CSSM_DL_BASE_DL_ERROR + 16,
 CSSMERR_DL_UNSUPPORTED_RECORDTYPE = CSSM_DL_BASE_DL_ERROR + 17,
 CSSMERR_DL_FIELD_SPECIFIED_MULTIPLE = CSSM_DL_BASE_DL_ERROR + 18,
 CSSMERR_DL_INCOMPATIBLE_FIELD_FORMAT = CSSM_DL_BASE_DL_ERROR + 19,
 CSSMERR_DL_INVALID_PARSING_MODULE = CSSM_DL_BASE_DL_ERROR + 20,
 CSSMERR_DL_INVALID_DB_NAME = CSSM_DL_BASE_DL_ERROR + 22,
 CSSMERR_DL_DATASTORE_DOESNOT_EXIST = CSSM_DL_BASE_DL_ERROR + 23,
 CSSMERR_DL_DATASTORE_ALREADY_EXISTS = CSSM_DL_BASE_DL_ERROR + 24,
 CSSMERR_DL_DB_LOCKED = CSSM_DL_BASE_DL_ERROR + 25,
 CSSMERR_DL_DATASTORE_IS_OPEN = CSSM_DL_BASE_DL_ERROR + 26,
 CSSMERR_DL_RECORD_NOT_FOUND = CSSM_DL_BASE_DL_ERROR + 27,
 CSSMERR_DL_MISSING_VALUE = CSSM_DL_BASE_DL_ERROR + 28,
 CSSMERR_DL_UNSUPPORTED_QUERY = CSSM_DL_BASE_DL_ERROR + 29,
 CSSMERR_DL_UNSUPPORTED_QUERY_LIMITS = CSSM_DL_BASE_DL_ERROR + 30,
 CSSMERR_DL_UNSUPPORTED_NUM_SELECTION_PREDS = CSSM_DL_BASE_DL_ERROR + 31,
 CSSMERR_DL_UNSUPPORTED_OPERATOR = CSSM_DL_BASE_DL_ERROR + 33,
 CSSMERR_DL_INVALID_RESULTS_HANDLE = CSSM_DL_BASE_DL_ERROR + 34,
 CSSMERR_DL_INVALID_DB_LOCATION = CSSM_DL_BASE_DL_ERROR + 35,
 CSSMERR_DL_INVALID_ACCESS_REQUEST = CSSM_DL_BASE_DL_ERROR + 36,
 CSSMERR_DL_INVALID_INDEX_INFO = CSSM_DL_BASE_DL_ERROR + 37,
 CSSMERR_DL_INVALID_SELECTION_TAG = CSSM_DL_BASE_DL_ERROR + 38,
 CSSMERR_DL_INVALID_NEW_OWNER = CSSM_DL_BASE_DL_ERROR + 39,
 CSSMERR_DL_INVALID_RECORD_UID = CSSM_DL_BASE_DL_ERROR + 40,
 CSSMERR_DL_INVALID_UNIQUE_INDEX_DATA = CSSM_DL_BASE_DL_ERROR + 41,
 CSSMERR_DL_INVALID_MODIFY_MODE = CSSM_DL_BASE_DL_ERROR + 42,
 CSSMERR_DL_INVALID_OPEN_PARAMETERS = CSSM_DL_BASE_DL_ERROR + 43,
 CSSMERR_DL_RECORD_MODIFIED = CSSM_DL_BASE_DL_ERROR + 44,
 CSSMERR_DL_ENDOFDATA = CSSM_DL_BASE_DL_ERROR + 45,
 CSSMERR_DL_INVALID_QUERY = CSSM_DL_BASE_DL_ERROR + 46,
 CSSMERR_DL_INVALID_VALUE = CSSM_DL_BASE_DL_ERROR + 47,
 CSSMERR_DL_MULTIPLE_VALUES_UNSUPPORTED = CSSM_DL_BASE_DL_ERROR + 48,
 CSSMERR_DL_STALE_UNIQUE_RECORD = CSSM_DL_BASE_DL_ERROR + 49
};
# 30 "/System/Library/Frameworks/Security.framework/Headers/cssmapple.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/cssmtype.h" 1 3
# 43 "/System/Library/Frameworks/Security.framework/Headers/cssmtype.h" 3
typedef CSSM_INTPTR CSSM_HANDLE, *CSSM_HANDLE_PTR;

typedef uint64 CSSM_LONG_HANDLE, *CSSM_LONG_HANDLE_PTR;

typedef CSSM_HANDLE CSSM_MODULE_HANDLE, *CSSM_MODULE_HANDLE_PTR;

typedef CSSM_LONG_HANDLE CSSM_CC_HANDLE;

typedef CSSM_MODULE_HANDLE CSSM_CSP_HANDLE;

typedef CSSM_MODULE_HANDLE CSSM_TP_HANDLE;

typedef CSSM_MODULE_HANDLE CSSM_AC_HANDLE;

typedef CSSM_MODULE_HANDLE CSSM_CL_HANDLE;

typedef CSSM_MODULE_HANDLE CSSM_DL_HANDLE;

typedef CSSM_MODULE_HANDLE CSSM_DB_HANDLE;



enum {
    CSSM_INVALID_HANDLE = 0
};




typedef sint32 CSSM_BOOL;
enum {
 CSSM_FALSE = 0,
 CSSM_TRUE = !CSSM_FALSE
};


typedef sint32 CSSM_RETURN;
enum {
 CSSM_OK = 0
};

enum {
 CSSM_MODULE_STRING_SIZE = 64
};
typedef char CSSM_STRING [CSSM_MODULE_STRING_SIZE + 4];

typedef struct cssm_data {
    CSSM_SIZE Length;
    uint8 *Data;
} CSSM_DATA __attribute__((deprecated)), *CSSM_DATA_PTR __attribute__((deprecated));

typedef struct cssm_guid {
    uint32 Data1;
    uint16 Data2;
    uint16 Data3;
    uint8 Data4[8];
} CSSM_GUID __attribute__((deprecated)), *CSSM_GUID_PTR __attribute__((deprecated));

typedef uint32 CSSM_BITMASK;
typedef CSSM_BITMASK CSSM_KEY_HIERARCHY;
enum {
 CSSM_KEY_HIERARCHY_NONE = 0,
 CSSM_KEY_HIERARCHY_INTEG = 1,
 CSSM_KEY_HIERARCHY_EXPORT = 2
};

typedef CSSM_BITMASK CSSM_PVC_MODE;
enum {
 CSSM_PVC_NONE = 0,
 CSSM_PVC_APP = 1,
 CSSM_PVC_SP = 2
};

typedef uint32 CSSM_PRIVILEGE_SCOPE;
enum {
 CSSM_PRIVILEGE_SCOPE_NONE = 0,
 CSSM_PRIVILEGE_SCOPE_PROCESS = 1,
 CSSM_PRIVILEGE_SCOPE_THREAD = 2
};

typedef struct cssm_version {
    uint32 Major;
    uint32 Minor;
} CSSM_VERSION __attribute__((deprecated)), *CSSM_VERSION_PTR __attribute__((deprecated));

typedef uint32 CSSM_SERVICE_MASK;
enum {
 CSSM_SERVICE_CSSM = 0x1,
 CSSM_SERVICE_CSP = 0x2,
 CSSM_SERVICE_DL = 0x4,
 CSSM_SERVICE_CL = 0x8,
 CSSM_SERVICE_TP = 0x10,
 CSSM_SERVICE_AC = 0x20,
 CSSM_SERVICE_KR = 0x40
};

typedef CSSM_SERVICE_MASK CSSM_SERVICE_TYPE;

typedef struct cssm_subservice_uid {
    CSSM_GUID Guid;
    CSSM_VERSION Version;
    uint32 SubserviceId;
    CSSM_SERVICE_TYPE SubserviceType;
} CSSM_SUBSERVICE_UID __attribute__((deprecated)), *CSSM_SUBSERVICE_UID_PTR __attribute__((deprecated));

typedef uint32 CSSM_MODULE_EVENT, *CSSM_MODULE_EVENT_PTR;
enum {
    CSSM_NOTIFY_INSERT = 1,
    CSSM_NOTIFY_REMOVE = 2,
    CSSM_NOTIFY_FAULT = 3
};

typedef CSSM_RETURN ( *CSSM_API_ModuleEventHandler)
    (const CSSM_GUID *ModuleGuid,
     void* AppNotifyCallbackCtx,
     uint32 SubserviceId,
     CSSM_SERVICE_TYPE ServiceType,
     CSSM_MODULE_EVENT EventType);

typedef uint32 CSSM_ATTACH_FLAGS;
enum {
 CSSM_ATTACH_READ_ONLY = 0x00000001
};



typedef uint64 CSSM_PRIVILEGE;
typedef CSSM_PRIVILEGE CSSM_USEE_TAG;
enum {
 CSSM_USEE_LAST = 0xFF,
 CSSM_USEE_NONE = 0,
 CSSM_USEE_DOMESTIC = 1,
 CSSM_USEE_FINANCIAL = 2,
 CSSM_USEE_KRLE = 3,
 CSSM_USEE_KRENT = 4,
 CSSM_USEE_SSL = 5,
 CSSM_USEE_AUTHENTICATION = 6,
 CSSM_USEE_KEYEXCH = 7,
 CSSM_USEE_MEDICAL = 8,
 CSSM_USEE_INSURANCE = 9,
 CSSM_USEE_WEAK = 10
};

typedef uint32 CSSM_NET_ADDRESS_TYPE;
enum {
    CSSM_ADDR_NONE = 0,
    CSSM_ADDR_CUSTOM = 1,
    CSSM_ADDR_URL = 2,
    CSSM_ADDR_SOCKADDR = 3,
    CSSM_ADDR_NAME = 4
};

typedef struct cssm_net_address {
    CSSM_NET_ADDRESS_TYPE AddressType;
    CSSM_DATA Address;
} CSSM_NET_ADDRESS __attribute__((deprecated)), *CSSM_NET_ADDRESS_PTR __attribute__((deprecated));

typedef uint32 CSSM_NET_PROTOCOL;
enum {
 CSSM_NET_PROTO_NONE = 0,
 CSSM_NET_PROTO_CUSTOM = 1,
 CSSM_NET_PROTO_UNSPECIFIED = 2,
 CSSM_NET_PROTO_LDAP = 3,
 CSSM_NET_PROTO_LDAPS = 4,
 CSSM_NET_PROTO_LDAPNS = 5,
 CSSM_NET_PROTO_X500DAP = 6,
 CSSM_NET_PROTO_FTP = 7,
 CSSM_NET_PROTO_FTPS = 8,
 CSSM_NET_PROTO_OCSP = 9,
 CSSM_NET_PROTO_CMP = 10,
 CSSM_NET_PROTO_CMPS = 11
};

typedef CSSM_RETURN ( *CSSM_CALLBACK)
    (CSSM_DATA_PTR OutData, void *CallerCtx);

typedef struct cssm_crypto_data {
    CSSM_DATA Param;
    CSSM_CALLBACK Callback;
    void *CallerCtx;
} CSSM_CRYPTO_DATA __attribute__((deprecated)), *CSSM_CRYPTO_DATA_PTR __attribute__((deprecated));

typedef sint32 CSSM_WORDID_TYPE;
enum {
 CSSM_WORDID__UNK_ = -1,
 CSSM_WORDID__NLU_ = 0,
 CSSM_WORDID__STAR_ = 1,
 CSSM_WORDID_A = 2,
 CSSM_WORDID_ACL = 3,
 CSSM_WORDID_ALPHA = 4,
 CSSM_WORDID_B = 5,
 CSSM_WORDID_BER = 6,
 CSSM_WORDID_BINARY = 7,
 CSSM_WORDID_BIOMETRIC = 8,
 CSSM_WORDID_C = 9,
 CSSM_WORDID_CANCELED = 10,
 CSSM_WORDID_CERT = 11,
 CSSM_WORDID_COMMENT = 12,
 CSSM_WORDID_CRL = 13,
 CSSM_WORDID_CUSTOM = 14,
 CSSM_WORDID_D = 15,
 CSSM_WORDID_DATE = 16,
 CSSM_WORDID_DB_DELETE = 17,
 CSSM_WORDID_DB_EXEC_STORED_QUERY = 18,
 CSSM_WORDID_DB_INSERT = 19,
 CSSM_WORDID_DB_MODIFY = 20,
 CSSM_WORDID_DB_READ = 21,
 CSSM_WORDID_DBS_CREATE = 22,
 CSSM_WORDID_DBS_DELETE = 23,
 CSSM_WORDID_DECRYPT = 24,
 CSSM_WORDID_DELETE = 25,
 CSSM_WORDID_DELTA_CRL = 26,
 CSSM_WORDID_DER = 27,
 CSSM_WORDID_DERIVE = 28,
 CSSM_WORDID_DISPLAY = 29,
 CSSM_WORDID_DO = 30,
 CSSM_WORDID_DSA = 31,
 CSSM_WORDID_DSA_SHA1 = 32,
 CSSM_WORDID_E = 33,
 CSSM_WORDID_ELGAMAL = 34,
 CSSM_WORDID_ENCRYPT = 35,
 CSSM_WORDID_ENTRY = 36,
 CSSM_WORDID_EXPORT_CLEAR = 37,
 CSSM_WORDID_EXPORT_WRAPPED = 38,
 CSSM_WORDID_G = 39,
 CSSM_WORDID_GE = 40,
 CSSM_WORDID_GENKEY = 41,
 CSSM_WORDID_HASH = 42,
 CSSM_WORDID_HASHED_PASSWORD = 43,
 CSSM_WORDID_HASHED_SUBJECT = 44,
 CSSM_WORDID_HAVAL = 45,
 CSSM_WORDID_IBCHASH = 46,
 CSSM_WORDID_IMPORT_CLEAR = 47,
 CSSM_WORDID_IMPORT_WRAPPED = 48,
 CSSM_WORDID_INTEL = 49,
 CSSM_WORDID_ISSUER = 50,
 CSSM_WORDID_ISSUER_INFO = 51,
 CSSM_WORDID_K_OF_N = 52,
 CSSM_WORDID_KEA = 53,
 CSSM_WORDID_KEYHOLDER = 54,
 CSSM_WORDID_L = 55,
 CSSM_WORDID_LE = 56,
 CSSM_WORDID_LOGIN = 57,
 CSSM_WORDID_LOGIN_NAME = 58,
 CSSM_WORDID_MAC = 59,
 CSSM_WORDID_MD2 = 60,
 CSSM_WORDID_MD2WITHRSA = 61,
 CSSM_WORDID_MD4 = 62,
 CSSM_WORDID_MD5 = 63,
 CSSM_WORDID_MD5WITHRSA = 64,
 CSSM_WORDID_N = 65,
 CSSM_WORDID_NAME = 66,
 CSSM_WORDID_NDR = 67,
 CSSM_WORDID_NHASH = 68,
 CSSM_WORDID_NOT_AFTER = 69,
 CSSM_WORDID_NOT_BEFORE = 70,
 CSSM_WORDID_NULL = 71,
 CSSM_WORDID_NUMERIC = 72,
 CSSM_WORDID_OBJECT_HASH = 73,
 CSSM_WORDID_ONE_TIME = 74,
 CSSM_WORDID_ONLINE = 75,
 CSSM_WORDID_OWNER = 76,
 CSSM_WORDID_P = 77,
 CSSM_WORDID_PAM_NAME = 78,
 CSSM_WORDID_PASSWORD = 79,
 CSSM_WORDID_PGP = 80,
 CSSM_WORDID_PREFIX = 81,
 CSSM_WORDID_PRIVATE_KEY = 82,
 CSSM_WORDID_PROMPTED_BIOMETRIC = 83,
 CSSM_WORDID_PROMPTED_PASSWORD = 84,
 CSSM_WORDID_PROPAGATE = 85,
 CSSM_WORDID_PROTECTED_BIOMETRIC = 86,
 CSSM_WORDID_PROTECTED_PASSWORD = 87,
 CSSM_WORDID_PROTECTED_PIN = 88,
 CSSM_WORDID_PUBLIC_KEY = 89,
 CSSM_WORDID_PUBLIC_KEY_FROM_CERT = 90,
 CSSM_WORDID_Q = 91,
 CSSM_WORDID_RANGE = 92,
 CSSM_WORDID_REVAL = 93,
 CSSM_WORDID_RIPEMAC = 94,
 CSSM_WORDID_RIPEMD = 95,
 CSSM_WORDID_RIPEMD160 = 96,
 CSSM_WORDID_RSA = 97,
 CSSM_WORDID_RSA_ISO9796 = 98,
 CSSM_WORDID_RSA_PKCS = 99,
 CSSM_WORDID_RSA_PKCS_MD5 = 100,
 CSSM_WORDID_RSA_PKCS_SHA1 = 101,
 CSSM_WORDID_RSA_PKCS1 = 102,
 CSSM_WORDID_RSA_PKCS1_MD5 = 103,
 CSSM_WORDID_RSA_PKCS1_SHA1 = 104,
 CSSM_WORDID_RSA_PKCS1_SIG = 105,
 CSSM_WORDID_RSA_RAW = 106,
 CSSM_WORDID_SDSIV1 = 107,
 CSSM_WORDID_SEQUENCE = 108,
 CSSM_WORDID_SET = 109,
 CSSM_WORDID_SEXPR = 110,
 CSSM_WORDID_SHA1 = 111,
 CSSM_WORDID_SHA1WITHDSA = 112,
 CSSM_WORDID_SHA1WITHECDSA = 113,
 CSSM_WORDID_SHA1WITHRSA = 114,
 CSSM_WORDID_SIGN = 115,
 CSSM_WORDID_SIGNATURE = 116,
 CSSM_WORDID_SIGNED_NONCE = 117,
 CSSM_WORDID_SIGNED_SECRET = 118,
 CSSM_WORDID_SPKI = 119,
 CSSM_WORDID_SUBJECT = 120,
 CSSM_WORDID_SUBJECT_INFO = 121,
 CSSM_WORDID_TAG = 122,
 CSSM_WORDID_THRESHOLD = 123,
 CSSM_WORDID_TIME = 124,
 CSSM_WORDID_URI = 125,
 CSSM_WORDID_VERSION = 126,
 CSSM_WORDID_X509_ATTRIBUTE = 127,
 CSSM_WORDID_X509V1 = 128,
 CSSM_WORDID_X509V2 = 129,
 CSSM_WORDID_X509V3 = 130,
 CSSM_WORDID_X9_ATTRIBUTE = 131,
 CSSM_WORDID_VENDOR_START = 0x00010000,
 CSSM_WORDID_VENDOR_END = 0x7FFF0000
};

typedef uint32 CSSM_LIST_ELEMENT_TYPE, *CSSM_LIST_ELEMENT_TYPE_PTR;
enum {
 CSSM_LIST_ELEMENT_DATUM = 0x00,
 CSSM_LIST_ELEMENT_SUBLIST = 0x01,
 CSSM_LIST_ELEMENT_WORDID = 0x02
};

typedef uint32 CSSM_LIST_TYPE, *CSSM_LIST_TYPE_PTR;
enum {
 CSSM_LIST_TYPE_UNKNOWN = 0,
 CSSM_LIST_TYPE_CUSTOM = 1,
 CSSM_LIST_TYPE_SEXPR = 2
};

typedef struct cssm_list_element *CSSM_LIST_ELEMENT_PTR;

typedef struct cssm_list {
    CSSM_LIST_TYPE ListType;
    CSSM_LIST_ELEMENT_PTR Head;
    CSSM_LIST_ELEMENT_PTR Tail;
} CSSM_LIST __attribute__((deprecated)), *CSSM_LIST_PTR __attribute__((deprecated));

typedef struct cssm_list_element {
    struct cssm_list_element *NextElement;
 CSSM_WORDID_TYPE WordID;

    CSSM_LIST_ELEMENT_TYPE ElementType;
    union {
        CSSM_LIST Sublist;
        CSSM_DATA Word;
    } Element;
} CSSM_LIST_ELEMENT;

typedef struct {
 CSSM_LIST Issuer;
 CSSM_LIST Subject;
 CSSM_BOOL Delegate;
 CSSM_LIST AuthorizationTag;
 CSSM_LIST ValidityPeriod;
} CSSM_TUPLE __attribute__((deprecated)), *CSSM_TUPLE_PTR __attribute__((deprecated));

typedef struct cssm_tuplegroup {
    uint32 NumberOfTuples;
    CSSM_TUPLE_PTR Tuples;
} CSSM_TUPLEGROUP __attribute__((deprecated)), *CSSM_TUPLEGROUP_PTR __attribute__((deprecated));

typedef CSSM_WORDID_TYPE CSSM_SAMPLE_TYPE;
enum {
 CSSM_SAMPLE_TYPE_PASSWORD = CSSM_WORDID_PASSWORD,
 CSSM_SAMPLE_TYPE_HASHED_PASSWORD = CSSM_WORDID_HASHED_PASSWORD,
 CSSM_SAMPLE_TYPE_PROTECTED_PASSWORD = CSSM_WORDID_PROTECTED_PASSWORD,
 CSSM_SAMPLE_TYPE_PROMPTED_PASSWORD = CSSM_WORDID_PROMPTED_PASSWORD,
 CSSM_SAMPLE_TYPE_SIGNED_NONCE = CSSM_WORDID_SIGNED_NONCE,
 CSSM_SAMPLE_TYPE_SIGNED_SECRET = CSSM_WORDID_SIGNED_SECRET,
 CSSM_SAMPLE_TYPE_BIOMETRIC = CSSM_WORDID_BIOMETRIC,
 CSSM_SAMPLE_TYPE_PROTECTED_BIOMETRIC = CSSM_WORDID_PROTECTED_BIOMETRIC,
 CSSM_SAMPLE_TYPE_PROMPTED_BIOMETRIC = CSSM_WORDID_PROMPTED_BIOMETRIC,
 CSSM_SAMPLE_TYPE_THRESHOLD = CSSM_WORDID_THRESHOLD
};

typedef struct cssm_sample {
    CSSM_LIST TypedSample;
    const CSSM_SUBSERVICE_UID *Verifier;
} CSSM_SAMPLE __attribute__((deprecated)), *CSSM_SAMPLE_PTR __attribute__((deprecated));

typedef struct cssm_samplegroup {
    uint32 NumberOfSamples;
    const CSSM_SAMPLE *Samples;
} CSSM_SAMPLEGROUP __attribute__((deprecated)), *CSSM_SAMPLEGROUP_PTR __attribute__((deprecated));

typedef void *( *CSSM_MALLOC)
    (CSSM_SIZE size,
     void *allocref);

typedef void ( *CSSM_FREE)
    (void *memblock,
     void *allocref);

typedef void *( *CSSM_REALLOC)
    (void *memblock,
     CSSM_SIZE size,
     void *allocref);

typedef void *( *CSSM_CALLOC)
    (uint32 num,
     CSSM_SIZE size,
     void *allocref);

typedef struct cssm_memory_funcs {
    CSSM_MALLOC malloc_func;
    CSSM_FREE free_func;
    CSSM_REALLOC realloc_func;
    CSSM_CALLOC calloc_func;
    void *AllocRef;
} CSSM_MEMORY_FUNCS __attribute__((deprecated)), *CSSM_MEMORY_FUNCS_PTR __attribute__((deprecated));

typedef CSSM_MEMORY_FUNCS CSSM_API_MEMORY_FUNCS;
typedef CSSM_API_MEMORY_FUNCS *CSSM_API_MEMORY_FUNCS_PTR;

typedef CSSM_RETURN ( * CSSM_CHALLENGE_CALLBACK)
    (const CSSM_LIST *Challenge,
     CSSM_SAMPLEGROUP_PTR Response,
     void *CallerCtx,
     const CSSM_MEMORY_FUNCS *MemFuncs);

typedef uint32 CSSM_CERT_TYPE, *CSSM_CERT_TYPE_PTR;
enum {
    CSSM_CERT_UNKNOWN = 0x00,
    CSSM_CERT_X_509v1 = 0x01,
    CSSM_CERT_X_509v2 = 0x02,
    CSSM_CERT_X_509v3 = 0x03,
    CSSM_CERT_PGP = 0x04,
    CSSM_CERT_SPKI = 0x05,
    CSSM_CERT_SDSIv1 = 0x06,
    CSSM_CERT_Intel = 0x08,
    CSSM_CERT_X_509_ATTRIBUTE = 0x09,
    CSSM_CERT_X9_ATTRIBUTE = 0x0A,
    CSSM_CERT_TUPLE = 0x0B,
    CSSM_CERT_ACL_ENTRY = 0x0C,
    CSSM_CERT_MULTIPLE = 0x7FFE,
    CSSM_CERT_LAST = 0x7FFF,



 CSSM_CL_CUSTOM_CERT_TYPE = 0x08000
};

typedef uint32 CSSM_CERT_ENCODING, *CSSM_CERT_ENCODING_PTR;
enum {
    CSSM_CERT_ENCODING_UNKNOWN = 0x00,
    CSSM_CERT_ENCODING_CUSTOM = 0x01,
    CSSM_CERT_ENCODING_BER = 0x02,
    CSSM_CERT_ENCODING_DER = 0x03,
    CSSM_CERT_ENCODING_NDR = 0x04,
    CSSM_CERT_ENCODING_SEXPR = 0x05,
    CSSM_CERT_ENCODING_PGP = 0x06,
    CSSM_CERT_ENCODING_MULTIPLE = 0x7FFE,
    CSSM_CERT_ENCODING_LAST = 0x7FFF,



 CSSM_CL_CUSTOM_CERT_ENCODING = 0x8000
};

typedef struct cssm_encoded_cert {
    CSSM_CERT_TYPE CertType;
    CSSM_CERT_ENCODING CertEncoding;
    CSSM_DATA CertBlob;
} CSSM_ENCODED_CERT __attribute__((deprecated)), *CSSM_ENCODED_CERT_PTR __attribute__((deprecated));

typedef uint32 CSSM_CERT_PARSE_FORMAT, *CSSM_CERT_PARSE_FORMAT_PTR;
enum {
 CSSM_CERT_PARSE_FORMAT_NONE = 0x00,
 CSSM_CERT_PARSE_FORMAT_CUSTOM = 0x01,
 CSSM_CERT_PARSE_FORMAT_SEXPR = 0x02,
 CSSM_CERT_PARSE_FORMAT_COMPLEX = 0x03,
 CSSM_CERT_PARSE_FORMAT_OID_NAMED = 0x04,
 CSSM_CERT_PARSE_FORMAT_TUPLE = 0x05,
 CSSM_CERT_PARSE_FORMAT_MULTIPLE = 0x7FFE,


 CSSM_CERT_PARSE_FORMAT_LAST = 0x7FFF,




 CSSM_CL_CUSTOM_CERT_PARSE_FORMAT = 0x8000
};

typedef struct cssm_parsed_cert {
    CSSM_CERT_TYPE CertType;
    CSSM_CERT_PARSE_FORMAT ParsedCertFormat;

    void *ParsedCert;
} CSSM_PARSED_CERT __attribute__((deprecated)), *CSSM_PARSED_CERT_PTR __attribute__((deprecated));

typedef struct cssm_cert_pair {
    CSSM_ENCODED_CERT EncodedCert;
    CSSM_PARSED_CERT ParsedCert;
} CSSM_CERT_PAIR __attribute__((deprecated)), *CSSM_CERT_PAIR_PTR __attribute__((deprecated));

typedef uint32 CSSM_CERTGROUP_TYPE, *CSSM_CERTGROUP_TYPE_PTR;
enum {
 CSSM_CERTGROUP_DATA = 0x00,
 CSSM_CERTGROUP_ENCODED_CERT = 0x01,
 CSSM_CERTGROUP_PARSED_CERT = 0x02,
 CSSM_CERTGROUP_CERT_PAIR = 0x03
};

typedef struct cssm_certgroup {
    CSSM_CERT_TYPE CertType;
    CSSM_CERT_ENCODING CertEncoding;
    uint32 NumCerts;
    union {
        CSSM_DATA_PTR CertList;
        CSSM_ENCODED_CERT_PTR EncodedCertList;

        CSSM_PARSED_CERT_PTR ParsedCertList;

        CSSM_CERT_PAIR_PTR PairCertList;

    } GroupList;
    CSSM_CERTGROUP_TYPE CertGroupType;

    void *Reserved;
} CSSM_CERTGROUP, *CSSM_CERTGROUP_PTR;

typedef struct cssm_base_certs {
    CSSM_TP_HANDLE TPHandle;
    CSSM_CL_HANDLE CLHandle;
    CSSM_CERTGROUP Certs;
} CSSM_BASE_CERTS __attribute__((deprecated)), *CSSM_BASE_CERTS_PTR __attribute__((deprecated));

typedef struct cssm_access_credentials {
    CSSM_STRING EntryTag;
    CSSM_BASE_CERTS BaseCerts;
    CSSM_SAMPLEGROUP Samples;
    CSSM_CHALLENGE_CALLBACK Callback;
    void *CallerCtx;
} CSSM_ACCESS_CREDENTIALS __attribute__((deprecated)), *CSSM_ACCESS_CREDENTIALS_PTR __attribute__((deprecated));

typedef sint32 CSSM_ACL_SUBJECT_TYPE;
enum {
 CSSM_ACL_SUBJECT_TYPE_ANY = CSSM_WORDID__STAR_,
 CSSM_ACL_SUBJECT_TYPE_THRESHOLD = CSSM_WORDID_THRESHOLD,
 CSSM_ACL_SUBJECT_TYPE_PASSWORD = CSSM_WORDID_PASSWORD,
 CSSM_ACL_SUBJECT_TYPE_PROTECTED_PASSWORD = CSSM_WORDID_PROTECTED_PASSWORD,
 CSSM_ACL_SUBJECT_TYPE_PROMPTED_PASSWORD = CSSM_WORDID_PROMPTED_PASSWORD,
 CSSM_ACL_SUBJECT_TYPE_PUBLIC_KEY = CSSM_WORDID_PUBLIC_KEY,
 CSSM_ACL_SUBJECT_TYPE_HASHED_SUBJECT = CSSM_WORDID_HASHED_SUBJECT,
 CSSM_ACL_SUBJECT_TYPE_BIOMETRIC = CSSM_WORDID_BIOMETRIC,
 CSSM_ACL_SUBJECT_TYPE_PROTECTED_BIOMETRIC = CSSM_WORDID_PROTECTED_BIOMETRIC,
 CSSM_ACL_SUBJECT_TYPE_PROMPTED_BIOMETRIC = CSSM_WORDID_PROMPTED_BIOMETRIC,
 CSSM_ACL_SUBJECT_TYPE_LOGIN_NAME = CSSM_WORDID_LOGIN_NAME,
 CSSM_ACL_SUBJECT_TYPE_EXT_PAM_NAME = CSSM_WORDID_PAM_NAME
};


typedef sint32 CSSM_ACL_AUTHORIZATION_TAG;
enum {


 CSSM_ACL_AUTHORIZATION_TAG_VENDOR_DEFINED_START = 0x00010000,


 CSSM_ACL_AUTHORIZATION_ANY = CSSM_WORDID__STAR_,

 CSSM_ACL_AUTHORIZATION_LOGIN = CSSM_WORDID_LOGIN,
 CSSM_ACL_AUTHORIZATION_GENKEY = CSSM_WORDID_GENKEY,
 CSSM_ACL_AUTHORIZATION_DELETE = CSSM_WORDID_DELETE,
 CSSM_ACL_AUTHORIZATION_EXPORT_WRAPPED = CSSM_WORDID_EXPORT_WRAPPED,
 CSSM_ACL_AUTHORIZATION_EXPORT_CLEAR = CSSM_WORDID_EXPORT_CLEAR,
 CSSM_ACL_AUTHORIZATION_IMPORT_WRAPPED = CSSM_WORDID_IMPORT_WRAPPED,
 CSSM_ACL_AUTHORIZATION_IMPORT_CLEAR = CSSM_WORDID_IMPORT_CLEAR,
 CSSM_ACL_AUTHORIZATION_SIGN = CSSM_WORDID_SIGN,
 CSSM_ACL_AUTHORIZATION_ENCRYPT = CSSM_WORDID_ENCRYPT,
 CSSM_ACL_AUTHORIZATION_DECRYPT = CSSM_WORDID_DECRYPT,
 CSSM_ACL_AUTHORIZATION_MAC = CSSM_WORDID_MAC,
 CSSM_ACL_AUTHORIZATION_DERIVE = CSSM_WORDID_DERIVE,

 CSSM_ACL_AUTHORIZATION_DBS_CREATE = CSSM_WORDID_DBS_CREATE,
 CSSM_ACL_AUTHORIZATION_DBS_DELETE = CSSM_WORDID_DBS_DELETE,
 CSSM_ACL_AUTHORIZATION_DB_READ = CSSM_WORDID_DB_READ,
 CSSM_ACL_AUTHORIZATION_DB_INSERT = CSSM_WORDID_DB_INSERT,
 CSSM_ACL_AUTHORIZATION_DB_MODIFY = CSSM_WORDID_DB_MODIFY,
 CSSM_ACL_AUTHORIZATION_DB_DELETE = CSSM_WORDID_DB_DELETE
};

typedef struct cssm_authorizationgroup {
    uint32 NumberOfAuthTags;
    CSSM_ACL_AUTHORIZATION_TAG *AuthTags;
} CSSM_AUTHORIZATIONGROUP __attribute__((deprecated)), *CSSM_AUTHORIZATIONGROUP_PTR __attribute__((deprecated));

typedef struct cssm_acl_validity_period {
    CSSM_DATA StartDate;
    CSSM_DATA EndDate;
} CSSM_ACL_VALIDITY_PERIOD __attribute__((deprecated)), *CSSM_ACL_VALIDITY_PERIOD_PTR __attribute__((deprecated));

typedef struct cssm_acl_entry_prototype {
    CSSM_LIST TypedSubject;
    CSSM_BOOL Delegate;
    CSSM_AUTHORIZATIONGROUP Authorization;
    CSSM_ACL_VALIDITY_PERIOD TimeRange;
    CSSM_STRING EntryTag;
} CSSM_ACL_ENTRY_PROTOTYPE __attribute__((deprecated)), *CSSM_ACL_ENTRY_PROTOTYPE_PTR __attribute__((deprecated));

typedef struct cssm_acl_owner_prototype {
    CSSM_LIST TypedSubject;
    CSSM_BOOL Delegate;
} CSSM_ACL_OWNER_PROTOTYPE __attribute__((deprecated)), *CSSM_ACL_OWNER_PROTOTYPE_PTR __attribute__((deprecated));

typedef CSSM_RETURN ( * CSSM_ACL_SUBJECT_CALLBACK)
    (const CSSM_LIST *SubjectRequest,
     CSSM_LIST_PTR SubjectResponse,
     void *CallerContext,
     const CSSM_MEMORY_FUNCS *MemFuncs);

typedef struct cssm_acl_entry_input {
    CSSM_ACL_ENTRY_PROTOTYPE Prototype;
    CSSM_ACL_SUBJECT_CALLBACK Callback;
    void *CallerContext;
} CSSM_ACL_ENTRY_INPUT __attribute__((deprecated)), *CSSM_ACL_ENTRY_INPUT_PTR __attribute__((deprecated));

typedef struct cssm_resource_control_context {
    CSSM_ACCESS_CREDENTIALS_PTR AccessCred;
    CSSM_ACL_ENTRY_INPUT InitialAclEntry;
} CSSM_RESOURCE_CONTROL_CONTEXT __attribute__((deprecated)), *CSSM_RESOURCE_CONTROL_CONTEXT_PTR __attribute__((deprecated));

typedef CSSM_HANDLE CSSM_ACL_HANDLE;

typedef struct cssm_acl_entry_info {
    CSSM_ACL_ENTRY_PROTOTYPE EntryPublicInfo;
    CSSM_ACL_HANDLE EntryHandle;
} CSSM_ACL_ENTRY_INFO __attribute__((deprecated)), *CSSM_ACL_ENTRY_INFO_PTR __attribute__((deprecated));

typedef uint32 CSSM_ACL_EDIT_MODE;
enum {
 CSSM_ACL_EDIT_MODE_ADD = 1,
 CSSM_ACL_EDIT_MODE_DELETE = 2,
 CSSM_ACL_EDIT_MODE_REPLACE = 3
};

typedef struct cssm_acl_edit {
    CSSM_ACL_EDIT_MODE EditMode;
    CSSM_ACL_HANDLE OldEntryHandle;
    const CSSM_ACL_ENTRY_INPUT *NewEntry;
} CSSM_ACL_EDIT __attribute__((deprecated)), *CSSM_ACL_EDIT_PTR __attribute__((deprecated));




typedef void ( *CSSM_PROC_ADDR) ();

typedef CSSM_PROC_ADDR *CSSM_PROC_ADDR_PTR;

typedef struct cssm_func_name_addr {
    CSSM_STRING Name;
    CSSM_PROC_ADDR Address;
} CSSM_FUNC_NAME_ADDR __attribute__((deprecated)), *CSSM_FUNC_NAME_ADDR_PTR __attribute__((deprecated));




typedef struct cssm_date {
    uint8 Year[4];
    uint8 Month[2];
    uint8 Day[2];
} CSSM_DATE __attribute__((deprecated)), *CSSM_DATE_PTR __attribute__((deprecated));

typedef struct cssm_range {
    uint32 Min;
    uint32 Max;
} CSSM_RANGE __attribute__((deprecated)), *CSSM_RANGE_PTR __attribute__((deprecated));

typedef struct cssm_query_size_data {
    uint32 SizeInputBlock;
    uint32 SizeOutputBlock;
} CSSM_QUERY_SIZE_DATA __attribute__((deprecated)), *CSSM_QUERY_SIZE_DATA_PTR __attribute__((deprecated));

typedef uint32 CSSM_HEADERVERSION;
enum {
 CSSM_KEYHEADER_VERSION = 2
};

typedef struct cssm_key_size {
    uint32 LogicalKeySizeInBits;
    uint32 EffectiveKeySizeInBits;
} CSSM_KEY_SIZE __attribute__((deprecated)), *CSSM_KEY_SIZE_PTR __attribute__((deprecated));

typedef uint32 CSSM_KEYBLOB_TYPE;
enum {
 CSSM_KEYBLOB_RAW = 0,
 CSSM_KEYBLOB_REFERENCE = 2,
 CSSM_KEYBLOB_WRAPPED = 3,
 CSSM_KEYBLOB_OTHER = 0xFFFFFFFF
};

typedef uint32 CSSM_KEYBLOB_FORMAT;
enum {

 CSSM_KEYBLOB_RAW_FORMAT_NONE = 0,

 CSSM_KEYBLOB_RAW_FORMAT_PKCS1 = 1,
 CSSM_KEYBLOB_RAW_FORMAT_PKCS3 = 2,
 CSSM_KEYBLOB_RAW_FORMAT_MSCAPI = 3,
 CSSM_KEYBLOB_RAW_FORMAT_PGP = 4,
 CSSM_KEYBLOB_RAW_FORMAT_FIPS186 = 5,
 CSSM_KEYBLOB_RAW_FORMAT_BSAFE = 6,
 CSSM_KEYBLOB_RAW_FORMAT_CCA = 9,
 CSSM_KEYBLOB_RAW_FORMAT_PKCS8 = 10,
 CSSM_KEYBLOB_RAW_FORMAT_SPKI = 11,
 CSSM_KEYBLOB_RAW_FORMAT_OCTET_STRING = 12,
 CSSM_KEYBLOB_RAW_FORMAT_OTHER = 0xFFFFFFFF
};
enum {

 CSSM_KEYBLOB_WRAPPED_FORMAT_NONE = 0,

 CSSM_KEYBLOB_WRAPPED_FORMAT_PKCS8 = 1,
 CSSM_KEYBLOB_WRAPPED_FORMAT_PKCS7 = 2,
 CSSM_KEYBLOB_WRAPPED_FORMAT_MSCAPI = 3,
 CSSM_KEYBLOB_WRAPPED_FORMAT_OTHER = 0xFFFFFFFF
};
enum {

 CSSM_KEYBLOB_REF_FORMAT_INTEGER = 0,
 CSSM_KEYBLOB_REF_FORMAT_STRING = 1,
 CSSM_KEYBLOB_REF_FORMAT_SPKI = 2,

 CSSM_KEYBLOB_REF_FORMAT_OTHER = 0xFFFFFFFF
};

typedef uint32 CSSM_KEYCLASS;
enum {
 CSSM_KEYCLASS_PUBLIC_KEY = 0,
 CSSM_KEYCLASS_PRIVATE_KEY = 1,
 CSSM_KEYCLASS_SESSION_KEY = 2,
 CSSM_KEYCLASS_SECRET_PART = 3,
 CSSM_KEYCLASS_OTHER = 0xFFFFFFFF
};

typedef uint32 CSSM_KEYATTR_FLAGS;
enum {

 CSSM_KEYATTR_RETURN_DEFAULT = 0x00000000,
 CSSM_KEYATTR_RETURN_DATA = 0x10000000,
 CSSM_KEYATTR_RETURN_REF = 0x20000000,
 CSSM_KEYATTR_RETURN_NONE = 0x40000000,

 CSSM_KEYATTR_PERMANENT = 0x00000001,
 CSSM_KEYATTR_PRIVATE = 0x00000002,
 CSSM_KEYATTR_MODIFIABLE = 0x00000004,
 CSSM_KEYATTR_SENSITIVE = 0x00000008,
 CSSM_KEYATTR_EXTRACTABLE = 0x00000020,

 CSSM_KEYATTR_ALWAYS_SENSITIVE = 0x00000010,
 CSSM_KEYATTR_NEVER_EXTRACTABLE = 0x00000040
};

typedef uint32 CSSM_KEYUSE;
enum {
 CSSM_KEYUSE_ANY = 0x80000000,
 CSSM_KEYUSE_ENCRYPT = 0x00000001,
 CSSM_KEYUSE_DECRYPT = 0x00000002,
 CSSM_KEYUSE_SIGN = 0x00000004,
 CSSM_KEYUSE_VERIFY = 0x00000008,
 CSSM_KEYUSE_SIGN_RECOVER = 0x00000010,
 CSSM_KEYUSE_VERIFY_RECOVER = 0x00000020,
 CSSM_KEYUSE_WRAP = 0x00000040,
 CSSM_KEYUSE_UNWRAP = 0x00000080,
 CSSM_KEYUSE_DERIVE = 0x00000100
};

typedef uint32 CSSM_ALGORITHMS;
enum {
 CSSM_ALGID_NONE = 0,
 CSSM_ALGID_CUSTOM = CSSM_ALGID_NONE + 1,
 CSSM_ALGID_DH = CSSM_ALGID_NONE + 2,
 CSSM_ALGID_PH = CSSM_ALGID_NONE + 3,
 CSSM_ALGID_KEA = CSSM_ALGID_NONE + 4,
 CSSM_ALGID_MD2 = CSSM_ALGID_NONE + 5,
 CSSM_ALGID_MD4 = CSSM_ALGID_NONE + 6,
 CSSM_ALGID_MD5 = CSSM_ALGID_NONE + 7,
 CSSM_ALGID_SHA1 = CSSM_ALGID_NONE + 8,
 CSSM_ALGID_NHASH = CSSM_ALGID_NONE + 9,
 CSSM_ALGID_HAVAL = CSSM_ALGID_NONE + 10,
 CSSM_ALGID_RIPEMD = CSSM_ALGID_NONE + 11,
 CSSM_ALGID_IBCHASH = CSSM_ALGID_NONE + 12,
 CSSM_ALGID_RIPEMAC = CSSM_ALGID_NONE + 13,
 CSSM_ALGID_DES = CSSM_ALGID_NONE + 14,
 CSSM_ALGID_DESX = CSSM_ALGID_NONE + 15,
 CSSM_ALGID_RDES = CSSM_ALGID_NONE + 16,
 CSSM_ALGID_3DES_3KEY_EDE = CSSM_ALGID_NONE + 17,
 CSSM_ALGID_3DES_2KEY_EDE = CSSM_ALGID_NONE + 18,
 CSSM_ALGID_3DES_1KEY_EEE = CSSM_ALGID_NONE + 19,
 CSSM_ALGID_3DES_3KEY = CSSM_ALGID_3DES_3KEY_EDE,
 CSSM_ALGID_3DES_3KEY_EEE = CSSM_ALGID_NONE + 20,
 CSSM_ALGID_3DES_2KEY = CSSM_ALGID_3DES_2KEY_EDE,
 CSSM_ALGID_3DES_2KEY_EEE = CSSM_ALGID_NONE + 21,
 CSSM_ALGID_3DES_1KEY = CSSM_ALGID_3DES_3KEY_EEE,
 CSSM_ALGID_IDEA = CSSM_ALGID_NONE + 22,
 CSSM_ALGID_RC2 = CSSM_ALGID_NONE + 23,
 CSSM_ALGID_RC5 = CSSM_ALGID_NONE + 24,
 CSSM_ALGID_RC4 = CSSM_ALGID_NONE + 25,
 CSSM_ALGID_SEAL = CSSM_ALGID_NONE + 26,
 CSSM_ALGID_CAST = CSSM_ALGID_NONE + 27,
 CSSM_ALGID_BLOWFISH = CSSM_ALGID_NONE + 28,
 CSSM_ALGID_SKIPJACK = CSSM_ALGID_NONE + 29,
 CSSM_ALGID_LUCIFER = CSSM_ALGID_NONE + 30,
 CSSM_ALGID_MADRYGA = CSSM_ALGID_NONE + 31,
 CSSM_ALGID_FEAL = CSSM_ALGID_NONE + 32,
 CSSM_ALGID_REDOC = CSSM_ALGID_NONE + 33,
 CSSM_ALGID_REDOC3 = CSSM_ALGID_NONE + 34,
 CSSM_ALGID_LOKI = CSSM_ALGID_NONE + 35,
 CSSM_ALGID_KHUFU = CSSM_ALGID_NONE + 36,
 CSSM_ALGID_KHAFRE = CSSM_ALGID_NONE + 37,
 CSSM_ALGID_MMB = CSSM_ALGID_NONE + 38,
 CSSM_ALGID_GOST = CSSM_ALGID_NONE + 39,
 CSSM_ALGID_SAFER = CSSM_ALGID_NONE + 40,
 CSSM_ALGID_CRAB = CSSM_ALGID_NONE + 41,
 CSSM_ALGID_RSA = CSSM_ALGID_NONE + 42,
 CSSM_ALGID_DSA = CSSM_ALGID_NONE + 43,
 CSSM_ALGID_MD5WithRSA = CSSM_ALGID_NONE + 44,
 CSSM_ALGID_MD2WithRSA = CSSM_ALGID_NONE + 45,
 CSSM_ALGID_ElGamal = CSSM_ALGID_NONE + 46,
 CSSM_ALGID_MD2Random = CSSM_ALGID_NONE + 47,
 CSSM_ALGID_MD5Random = CSSM_ALGID_NONE + 48,
 CSSM_ALGID_SHARandom = CSSM_ALGID_NONE + 49,
 CSSM_ALGID_DESRandom = CSSM_ALGID_NONE + 50,
 CSSM_ALGID_SHA1WithRSA = CSSM_ALGID_NONE + 51,
 CSSM_ALGID_CDMF = CSSM_ALGID_NONE + 52,
 CSSM_ALGID_CAST3 = CSSM_ALGID_NONE + 53,
 CSSM_ALGID_CAST5 = CSSM_ALGID_NONE + 54,
 CSSM_ALGID_GenericSecret = CSSM_ALGID_NONE + 55,
 CSSM_ALGID_ConcatBaseAndKey = CSSM_ALGID_NONE + 56,
 CSSM_ALGID_ConcatKeyAndBase = CSSM_ALGID_NONE + 57,
 CSSM_ALGID_ConcatBaseAndData = CSSM_ALGID_NONE + 58,
 CSSM_ALGID_ConcatDataAndBase = CSSM_ALGID_NONE + 59,
 CSSM_ALGID_XORBaseAndData = CSSM_ALGID_NONE + 60,
 CSSM_ALGID_ExtractFromKey = CSSM_ALGID_NONE + 61,
 CSSM_ALGID_SSL3PreMasterGen = CSSM_ALGID_NONE + 62,
 CSSM_ALGID_SSL3MasterDerive = CSSM_ALGID_NONE + 63,
 CSSM_ALGID_SSL3KeyAndMacDerive = CSSM_ALGID_NONE + 64,
 CSSM_ALGID_SSL3MD5_MAC = CSSM_ALGID_NONE + 65,
 CSSM_ALGID_SSL3SHA1_MAC = CSSM_ALGID_NONE + 66,
 CSSM_ALGID_PKCS5_PBKDF1_MD5 = CSSM_ALGID_NONE + 67,
 CSSM_ALGID_PKCS5_PBKDF1_MD2 = CSSM_ALGID_NONE + 68,
 CSSM_ALGID_PKCS5_PBKDF1_SHA1 = CSSM_ALGID_NONE + 69,
 CSSM_ALGID_WrapLynks = CSSM_ALGID_NONE + 70,
 CSSM_ALGID_WrapSET_OAEP = CSSM_ALGID_NONE + 71,
 CSSM_ALGID_BATON = CSSM_ALGID_NONE + 72,
 CSSM_ALGID_ECDSA = CSSM_ALGID_NONE + 73,
 CSSM_ALGID_MAYFLY = CSSM_ALGID_NONE + 74,
 CSSM_ALGID_JUNIPER = CSSM_ALGID_NONE + 75,
 CSSM_ALGID_FASTHASH = CSSM_ALGID_NONE + 76,
 CSSM_ALGID_3DES = CSSM_ALGID_NONE + 77,
 CSSM_ALGID_SSL3MD5 = CSSM_ALGID_NONE + 78,
 CSSM_ALGID_SSL3SHA1 = CSSM_ALGID_NONE + 79,
 CSSM_ALGID_FortezzaTimestamp = CSSM_ALGID_NONE + 80,
 CSSM_ALGID_SHA1WithDSA = CSSM_ALGID_NONE + 81,
 CSSM_ALGID_SHA1WithECDSA = CSSM_ALGID_NONE + 82,
 CSSM_ALGID_DSA_BSAFE = CSSM_ALGID_NONE + 83,
 CSSM_ALGID_ECDH = CSSM_ALGID_NONE + 84,
 CSSM_ALGID_ECMQV = CSSM_ALGID_NONE + 85,
 CSSM_ALGID_PKCS12_SHA1_PBE = CSSM_ALGID_NONE + 86,
 CSSM_ALGID_ECNRA = CSSM_ALGID_NONE + 87,
 CSSM_ALGID_SHA1WithECNRA = CSSM_ALGID_NONE + 88,
 CSSM_ALGID_ECES = CSSM_ALGID_NONE + 89,
 CSSM_ALGID_ECAES = CSSM_ALGID_NONE + 90,
 CSSM_ALGID_SHA1HMAC = CSSM_ALGID_NONE + 91,
 CSSM_ALGID_FIPS186Random = CSSM_ALGID_NONE + 92,
 CSSM_ALGID_ECC = CSSM_ALGID_NONE + 93,
 CSSM_ALGID_MQV = CSSM_ALGID_NONE + 94,
 CSSM_ALGID_NRA = CSSM_ALGID_NONE + 95,
 CSSM_ALGID_IntelPlatformRandom = CSSM_ALGID_NONE + 96,
 CSSM_ALGID_UTC = CSSM_ALGID_NONE + 97,
 CSSM_ALGID_HAVAL3 = CSSM_ALGID_NONE + 98,
 CSSM_ALGID_HAVAL4 = CSSM_ALGID_NONE + 99,
 CSSM_ALGID_HAVAL5 = CSSM_ALGID_NONE + 100,
 CSSM_ALGID_TIGER = CSSM_ALGID_NONE + 101,
 CSSM_ALGID_MD5HMAC = CSSM_ALGID_NONE + 102,
 CSSM_ALGID_PKCS5_PBKDF2 = CSSM_ALGID_NONE + 103,
 CSSM_ALGID_RUNNING_COUNTER = CSSM_ALGID_NONE + 104,
 CSSM_ALGID_LAST = CSSM_ALGID_NONE + 0x7FFFFFFF,



 CSSM_ALGID_VENDOR_DEFINED = CSSM_ALGID_NONE + 0x80000000
};

typedef uint32 CSSM_ENCRYPT_MODE;
enum {
 CSSM_ALGMODE_NONE = 0,
 CSSM_ALGMODE_CUSTOM = CSSM_ALGMODE_NONE + 1,
 CSSM_ALGMODE_ECB = CSSM_ALGMODE_NONE + 2,
 CSSM_ALGMODE_ECBPad = CSSM_ALGMODE_NONE + 3,
 CSSM_ALGMODE_CBC = CSSM_ALGMODE_NONE + 4,
 CSSM_ALGMODE_CBC_IV8 = CSSM_ALGMODE_NONE + 5,
 CSSM_ALGMODE_CBCPadIV8 = CSSM_ALGMODE_NONE + 6,
 CSSM_ALGMODE_CFB = CSSM_ALGMODE_NONE + 7,
 CSSM_ALGMODE_CFB_IV8 = CSSM_ALGMODE_NONE + 8,
 CSSM_ALGMODE_CFBPadIV8 = CSSM_ALGMODE_NONE + 9,
 CSSM_ALGMODE_OFB = CSSM_ALGMODE_NONE + 10,
 CSSM_ALGMODE_OFB_IV8 = CSSM_ALGMODE_NONE + 11,
 CSSM_ALGMODE_OFBPadIV8 = CSSM_ALGMODE_NONE + 12,
 CSSM_ALGMODE_COUNTER = CSSM_ALGMODE_NONE + 13,
 CSSM_ALGMODE_BC = CSSM_ALGMODE_NONE + 14,
 CSSM_ALGMODE_PCBC = CSSM_ALGMODE_NONE + 15,
 CSSM_ALGMODE_CBCC = CSSM_ALGMODE_NONE + 16,
 CSSM_ALGMODE_OFBNLF = CSSM_ALGMODE_NONE + 17,
 CSSM_ALGMODE_PBC = CSSM_ALGMODE_NONE + 18,
 CSSM_ALGMODE_PFB = CSSM_ALGMODE_NONE + 19,
 CSSM_ALGMODE_CBCPD = CSSM_ALGMODE_NONE + 20,
 CSSM_ALGMODE_PUBLIC_KEY = CSSM_ALGMODE_NONE + 21,
 CSSM_ALGMODE_PRIVATE_KEY = CSSM_ALGMODE_NONE + 22,
 CSSM_ALGMODE_SHUFFLE = CSSM_ALGMODE_NONE + 23,
 CSSM_ALGMODE_ECB64 = CSSM_ALGMODE_NONE + 24,
 CSSM_ALGMODE_CBC64 = CSSM_ALGMODE_NONE + 25,
 CSSM_ALGMODE_OFB64 = CSSM_ALGMODE_NONE + 26,
 CSSM_ALGMODE_CFB32 = CSSM_ALGMODE_NONE + 28,
 CSSM_ALGMODE_CFB16 = CSSM_ALGMODE_NONE + 29,
 CSSM_ALGMODE_CFB8 = CSSM_ALGMODE_NONE + 30,
 CSSM_ALGMODE_WRAP = CSSM_ALGMODE_NONE + 31,
 CSSM_ALGMODE_PRIVATE_WRAP = CSSM_ALGMODE_NONE + 32,
 CSSM_ALGMODE_RELAYX = CSSM_ALGMODE_NONE + 33,
 CSSM_ALGMODE_ECB128 = CSSM_ALGMODE_NONE + 34,
 CSSM_ALGMODE_ECB96 = CSSM_ALGMODE_NONE + 35,
 CSSM_ALGMODE_CBC128 = CSSM_ALGMODE_NONE + 36,
 CSSM_ALGMODE_OAEP_HASH = CSSM_ALGMODE_NONE + 37,
 CSSM_ALGMODE_PKCS1_EME_V15 = CSSM_ALGMODE_NONE + 38,
 CSSM_ALGMODE_PKCS1_EME_OAEP = CSSM_ALGMODE_NONE + 39,
 CSSM_ALGMODE_PKCS1_EMSA_V15 = CSSM_ALGMODE_NONE + 40,
 CSSM_ALGMODE_ISO_9796 = CSSM_ALGMODE_NONE + 41,
 CSSM_ALGMODE_X9_31 = CSSM_ALGMODE_NONE + 42,
 CSSM_ALGMODE_LAST = CSSM_ALGMODE_NONE + 0x7FFFFFFF,



 CSSM_ALGMODE_VENDOR_DEFINED = CSSM_ALGMODE_NONE + 0x80000000
};

typedef struct cssm_keyheader {
    CSSM_HEADERVERSION HeaderVersion;
    CSSM_GUID CspId;
    CSSM_KEYBLOB_TYPE BlobType;
    CSSM_KEYBLOB_FORMAT Format;
    CSSM_ALGORITHMS AlgorithmId;
    CSSM_KEYCLASS KeyClass;
    uint32 LogicalKeySizeInBits;
    CSSM_KEYATTR_FLAGS KeyAttr;
    CSSM_KEYUSE KeyUsage;
    CSSM_DATE StartDate;
    CSSM_DATE EndDate;
    CSSM_ALGORITHMS WrapAlgorithmId;
    CSSM_ENCRYPT_MODE WrapMode;
    uint32 Reserved;
} CSSM_KEYHEADER __attribute__((deprecated)), *CSSM_KEYHEADER_PTR __attribute__((deprecated));

typedef struct cssm_key {
    CSSM_KEYHEADER KeyHeader;
    CSSM_DATA KeyData;
} CSSM_KEY __attribute__((deprecated)), *CSSM_KEY_PTR __attribute__((deprecated));

typedef CSSM_KEY CSSM_WRAP_KEY, *CSSM_WRAP_KEY_PTR;

typedef uint32 CSSM_CSPTYPE;
enum {
    CSSM_CSP_SOFTWARE = 1,
    CSSM_CSP_HARDWARE = CSSM_CSP_SOFTWARE + 1,
    CSSM_CSP_HYBRID = CSSM_CSP_SOFTWARE + 2
};


typedef struct cssm_dl_db_handle {
    CSSM_DL_HANDLE DLHandle;
    CSSM_DB_HANDLE DBHandle;
} CSSM_DL_DB_HANDLE __attribute__((deprecated)), *CSSM_DL_DB_HANDLE_PTR __attribute__((deprecated));

typedef uint32 CSSM_CONTEXT_TYPE;
enum {
 CSSM_ALGCLASS_NONE = 0,
 CSSM_ALGCLASS_CUSTOM = CSSM_ALGCLASS_NONE + 1,
 CSSM_ALGCLASS_SIGNATURE = CSSM_ALGCLASS_NONE + 2,
 CSSM_ALGCLASS_SYMMETRIC = CSSM_ALGCLASS_NONE + 3,
 CSSM_ALGCLASS_DIGEST = CSSM_ALGCLASS_NONE + 4,
 CSSM_ALGCLASS_RANDOMGEN = CSSM_ALGCLASS_NONE + 5,
 CSSM_ALGCLASS_UNIQUEGEN = CSSM_ALGCLASS_NONE + 6,
 CSSM_ALGCLASS_MAC = CSSM_ALGCLASS_NONE + 7,
 CSSM_ALGCLASS_ASYMMETRIC = CSSM_ALGCLASS_NONE + 8,
 CSSM_ALGCLASS_KEYGEN = CSSM_ALGCLASS_NONE + 9,
 CSSM_ALGCLASS_DERIVEKEY = CSSM_ALGCLASS_NONE + 10
};


enum {
 CSSM_ATTRIBUTE_DATA_NONE = 0x00000000,
 CSSM_ATTRIBUTE_DATA_UINT32 = 0x10000000,
 CSSM_ATTRIBUTE_DATA_CSSM_DATA = 0x20000000,
 CSSM_ATTRIBUTE_DATA_CRYPTO_DATA = 0x30000000,
 CSSM_ATTRIBUTE_DATA_KEY = 0x40000000,
 CSSM_ATTRIBUTE_DATA_STRING = 0x50000000,
 CSSM_ATTRIBUTE_DATA_DATE = 0x60000000,
 CSSM_ATTRIBUTE_DATA_RANGE = 0x70000000,
 CSSM_ATTRIBUTE_DATA_ACCESS_CREDENTIALS = 0x80000000,
 CSSM_ATTRIBUTE_DATA_VERSION = 0x01000000,
 CSSM_ATTRIBUTE_DATA_DL_DB_HANDLE = 0x02000000,
 CSSM_ATTRIBUTE_DATA_KR_PROFILE = 0x03000000,
 CSSM_ATTRIBUTE_TYPE_MASK = 0xFF000000
};

typedef uint32 CSSM_ATTRIBUTE_TYPE;
enum {
    CSSM_ATTRIBUTE_NONE = 0,
    CSSM_ATTRIBUTE_CUSTOM = CSSM_ATTRIBUTE_DATA_CSSM_DATA | 1,
    CSSM_ATTRIBUTE_DESCRIPTION = CSSM_ATTRIBUTE_DATA_STRING | 2,
    CSSM_ATTRIBUTE_KEY = CSSM_ATTRIBUTE_DATA_KEY | 3,
    CSSM_ATTRIBUTE_INIT_VECTOR = CSSM_ATTRIBUTE_DATA_CSSM_DATA | 4,
    CSSM_ATTRIBUTE_SALT = CSSM_ATTRIBUTE_DATA_CSSM_DATA | 5,
    CSSM_ATTRIBUTE_PADDING = CSSM_ATTRIBUTE_DATA_UINT32 | 6,
    CSSM_ATTRIBUTE_RANDOM = CSSM_ATTRIBUTE_DATA_CSSM_DATA | 7,
    CSSM_ATTRIBUTE_SEED = CSSM_ATTRIBUTE_DATA_CRYPTO_DATA | 8,
    CSSM_ATTRIBUTE_PASSPHRASE = CSSM_ATTRIBUTE_DATA_CRYPTO_DATA | 9,
    CSSM_ATTRIBUTE_KEY_LENGTH = CSSM_ATTRIBUTE_DATA_UINT32 | 10,
    CSSM_ATTRIBUTE_KEY_LENGTH_RANGE = CSSM_ATTRIBUTE_DATA_RANGE | 11,
    CSSM_ATTRIBUTE_BLOCK_SIZE = CSSM_ATTRIBUTE_DATA_UINT32 | 12,
    CSSM_ATTRIBUTE_OUTPUT_SIZE = CSSM_ATTRIBUTE_DATA_UINT32 | 13,
    CSSM_ATTRIBUTE_ROUNDS = CSSM_ATTRIBUTE_DATA_UINT32 | 14,
    CSSM_ATTRIBUTE_IV_SIZE = CSSM_ATTRIBUTE_DATA_UINT32 | 15,
    CSSM_ATTRIBUTE_ALG_PARAMS = CSSM_ATTRIBUTE_DATA_CSSM_DATA | 16,
    CSSM_ATTRIBUTE_LABEL = CSSM_ATTRIBUTE_DATA_CSSM_DATA | 17,
    CSSM_ATTRIBUTE_KEY_TYPE = CSSM_ATTRIBUTE_DATA_UINT32 | 18,
    CSSM_ATTRIBUTE_MODE = CSSM_ATTRIBUTE_DATA_UINT32 | 19,
    CSSM_ATTRIBUTE_EFFECTIVE_BITS = CSSM_ATTRIBUTE_DATA_UINT32 | 20,
    CSSM_ATTRIBUTE_START_DATE = CSSM_ATTRIBUTE_DATA_DATE | 21,
    CSSM_ATTRIBUTE_END_DATE = CSSM_ATTRIBUTE_DATA_DATE | 22,
    CSSM_ATTRIBUTE_KEYUSAGE = CSSM_ATTRIBUTE_DATA_UINT32 | 23,
    CSSM_ATTRIBUTE_KEYATTR = CSSM_ATTRIBUTE_DATA_UINT32 | 24,
    CSSM_ATTRIBUTE_VERSION = CSSM_ATTRIBUTE_DATA_VERSION | 25,
    CSSM_ATTRIBUTE_PRIME = CSSM_ATTRIBUTE_DATA_CSSM_DATA | 26,
    CSSM_ATTRIBUTE_BASE = CSSM_ATTRIBUTE_DATA_CSSM_DATA | 27,
    CSSM_ATTRIBUTE_SUBPRIME = CSSM_ATTRIBUTE_DATA_CSSM_DATA | 28,
    CSSM_ATTRIBUTE_ALG_ID = CSSM_ATTRIBUTE_DATA_UINT32 | 29,
    CSSM_ATTRIBUTE_ITERATION_COUNT = CSSM_ATTRIBUTE_DATA_UINT32 | 30,
    CSSM_ATTRIBUTE_ROUNDS_RANGE = CSSM_ATTRIBUTE_DATA_RANGE | 31,
 CSSM_ATTRIBUTE_KRPROFILE_LOCAL = CSSM_ATTRIBUTE_DATA_KR_PROFILE | 32,
 CSSM_ATTRIBUTE_KRPROFILE_REMOTE = CSSM_ATTRIBUTE_DATA_KR_PROFILE | 33,
    CSSM_ATTRIBUTE_CSP_HANDLE = CSSM_ATTRIBUTE_DATA_UINT32 | 34,
    CSSM_ATTRIBUTE_DL_DB_HANDLE = CSSM_ATTRIBUTE_DATA_DL_DB_HANDLE | 35,
    CSSM_ATTRIBUTE_ACCESS_CREDENTIALS = CSSM_ATTRIBUTE_DATA_ACCESS_CREDENTIALS | 36,
    CSSM_ATTRIBUTE_PUBLIC_KEY_FORMAT = CSSM_ATTRIBUTE_DATA_UINT32 | 37,
    CSSM_ATTRIBUTE_PRIVATE_KEY_FORMAT = CSSM_ATTRIBUTE_DATA_UINT32 | 38,
    CSSM_ATTRIBUTE_SYMMETRIC_KEY_FORMAT=CSSM_ATTRIBUTE_DATA_UINT32 | 39,
    CSSM_ATTRIBUTE_WRAPPED_KEY_FORMAT = CSSM_ATTRIBUTE_DATA_UINT32 | 40
};

typedef uint32 CSSM_PADDING;
enum {
 CSSM_PADDING_NONE = 0,
 CSSM_PADDING_CUSTOM = CSSM_PADDING_NONE + 1,
 CSSM_PADDING_ZERO = CSSM_PADDING_NONE + 2,
 CSSM_PADDING_ONE = CSSM_PADDING_NONE + 3,
 CSSM_PADDING_ALTERNATE = CSSM_PADDING_NONE + 4,
 CSSM_PADDING_FF = CSSM_PADDING_NONE + 5,
 CSSM_PADDING_PKCS5 = CSSM_PADDING_NONE + 6,
 CSSM_PADDING_PKCS7 = CSSM_PADDING_NONE + 7,
 CSSM_PADDING_CIPHERSTEALING = CSSM_PADDING_NONE + 8,
 CSSM_PADDING_RANDOM = CSSM_PADDING_NONE + 9,
 CSSM_PADDING_PKCS1 = CSSM_PADDING_NONE + 10,



 CSSM_PADDING_VENDOR_DEFINED = CSSM_PADDING_NONE + 0x80000000
};

typedef CSSM_ALGORITHMS CSSM_KEY_TYPE;

typedef struct cssm_context_attribute {
    CSSM_ATTRIBUTE_TYPE AttributeType;
    uint32 AttributeLength;
    union cssm_context_attribute_value {
        char *String;
        uint32 Uint32;
        CSSM_ACCESS_CREDENTIALS_PTR AccessCredentials;
        CSSM_KEY_PTR Key;
        CSSM_DATA_PTR Data;
        CSSM_PADDING Padding;
        CSSM_DATE_PTR Date;
        CSSM_RANGE_PTR Range;
        CSSM_CRYPTO_DATA_PTR CryptoData;
        CSSM_VERSION_PTR Version;
        CSSM_DL_DB_HANDLE_PTR DLDBHandle;
        struct cssm_kr_profile *KRProfile;
    } Attribute;
} CSSM_CONTEXT_ATTRIBUTE, *CSSM_CONTEXT_ATTRIBUTE_PTR;

typedef struct cssm_context {
    CSSM_CONTEXT_TYPE ContextType;
    CSSM_ALGORITHMS AlgorithmType;
    uint32 NumberOfAttributes;
    CSSM_CONTEXT_ATTRIBUTE_PTR ContextAttributes;
    CSSM_CSP_HANDLE CSPHandle;
 CSSM_BOOL Privileged;
 uint32 EncryptionProhibited;
 uint32 WorkFactor;
 uint32 Reserved;
} CSSM_CONTEXT __attribute__((deprecated)), *CSSM_CONTEXT_PTR __attribute__((deprecated));

typedef uint32 CSSM_SC_FLAGS;
enum {
 CSSM_CSP_TOK_RNG = 0x00000001,
 CSSM_CSP_TOK_CLOCK_EXISTS = 0x00000040
};

typedef uint32 CSSM_CSP_READER_FLAGS;
enum {
 CSSM_CSP_RDR_TOKENPRESENT = 0x00000001,

 CSSM_CSP_RDR_EXISTS = 0x00000002,


 CSSM_CSP_RDR_HW = 0x00000004

};

typedef uint32 CSSM_CSP_FLAGS;
enum {
 CSSM_CSP_TOK_WRITE_PROTECTED = 0x00000002,
 CSSM_CSP_TOK_LOGIN_REQUIRED = 0x00000004,
 CSSM_CSP_TOK_USER_PIN_INITIALIZED = 0x00000008,
 CSSM_CSP_TOK_PROT_AUTHENTICATION = 0x00000100,
 CSSM_CSP_TOK_USER_PIN_EXPIRED = 0x00100000,
 CSSM_CSP_TOK_SESSION_KEY_PASSWORD = 0x00200000,
 CSSM_CSP_TOK_PRIVATE_KEY_PASSWORD = 0x00400000,
 CSSM_CSP_STORES_PRIVATE_KEYS = 0x01000000,
 CSSM_CSP_STORES_PUBLIC_KEYS = 0x02000000,
 CSSM_CSP_STORES_SESSION_KEYS = 0x04000000,
 CSSM_CSP_STORES_CERTIFICATES = 0x08000000,
 CSSM_CSP_STORES_GENERIC = 0x10000000
};

typedef uint32 CSSM_PKCS_OAEP_MGF;
enum {
 CSSM_PKCS_OAEP_MGF_NONE = 0,
 CSSM_PKCS_OAEP_MGF1_SHA1 = CSSM_PKCS_OAEP_MGF_NONE + 1,
 CSSM_PKCS_OAEP_MGF1_MD5 = CSSM_PKCS_OAEP_MGF_NONE + 2
};

typedef uint32 CSSM_PKCS_OAEP_PSOURCE;
enum {
 CSSM_PKCS_OAEP_PSOURCE_NONE = 0,
 CSSM_PKCS_OAEP_PSOURCE_Pspecified = CSSM_PKCS_OAEP_PSOURCE_NONE + 1
};

typedef struct cssm_pkcs1_oaep_params {
    uint32 HashAlgorithm;
    CSSM_DATA HashParams;
    CSSM_PKCS_OAEP_MGF MGF;
    CSSM_DATA MGFParams;
    CSSM_PKCS_OAEP_PSOURCE PSource;
    CSSM_DATA PSourceParams;
} CSSM_PKCS1_OAEP_PARAMS __attribute__((deprecated)), *CSSM_PKCS1_OAEP_PARAMS_PTR __attribute__((deprecated));

typedef struct cssm_csp_operational_statistics {
    CSSM_BOOL UserAuthenticated;

    CSSM_CSP_FLAGS DeviceFlags;
    uint32 TokenMaxSessionCount;
    uint32 TokenOpenedSessionCount;
    uint32 TokenMaxRWSessionCount;
    uint32 TokenOpenedRWSessionCount;
    uint32 TokenTotalPublicMem;
    uint32 TokenFreePublicMem;
    uint32 TokenTotalPrivateMem;
    uint32 TokenFreePrivateMem;
} CSSM_CSP_OPERATIONAL_STATISTICS __attribute__((deprecated)), *CSSM_CSP_OPERATIONAL_STATISTICS_PTR __attribute__((deprecated));



enum {
 CSSM_VALUE_NOT_AVAILABLE = (uint32)(~0)
};

typedef struct cssm_pkcs5_pbkdf1_params {
    CSSM_DATA Passphrase;
    CSSM_DATA InitVector;
} CSSM_PKCS5_PBKDF1_PARAMS __attribute__((deprecated)), *CSSM_PKCS5_PBKDF1_PARAMS_PTR __attribute__((deprecated));

typedef uint32 CSSM_PKCS5_PBKDF2_PRF;
enum {
 CSSM_PKCS5_PBKDF2_PRF_HMAC_SHA1 = 0
};

typedef struct cssm_pkcs5_pbkdf2_params {
 CSSM_DATA Passphrase;
 CSSM_PKCS5_PBKDF2_PRF PseudoRandomFunction;
} CSSM_PKCS5_PBKDF2_PARAMS __attribute__((deprecated)), *CSSM_PKCS5_PBKDF2_PARAMS_PTR __attribute__((deprecated));

typedef struct cssm_kea_derive_params {
    CSSM_DATA Rb;
    CSSM_DATA Yb;
} CSSM_KEA_DERIVE_PARAMS __attribute__((deprecated)), *CSSM_KEA_DERIVE_PARAMS_PTR __attribute__((deprecated));




typedef struct cssm_tp_authority_id {
    CSSM_DATA *AuthorityCert;
    CSSM_NET_ADDRESS_PTR AuthorityLocation;
} CSSM_TP_AUTHORITY_ID __attribute__((deprecated)), *CSSM_TP_AUTHORITY_ID_PTR __attribute__((deprecated));

typedef uint32 CSSM_TP_AUTHORITY_REQUEST_TYPE, *CSSM_TP_AUTHORITY_REQUEST_TYPE_PTR;
enum {
 CSSM_TP_AUTHORITY_REQUEST_CERTISSUE = 0x01,
 CSSM_TP_AUTHORITY_REQUEST_CERTREVOKE = 0x02,
 CSSM_TP_AUTHORITY_REQUEST_CERTSUSPEND = 0x03,
 CSSM_TP_AUTHORITY_REQUEST_CERTRESUME = 0x04,
 CSSM_TP_AUTHORITY_REQUEST_CERTVERIFY = 0x05,
 CSSM_TP_AUTHORITY_REQUEST_CERTNOTARIZE = 0x06,
 CSSM_TP_AUTHORITY_REQUEST_CERTUSERECOVER = 0x07,
 CSSM_TP_AUTHORITY_REQUEST_CRLISSUE = 0x100
};

typedef CSSM_RETURN ( * CSSM_TP_VERIFICATION_RESULTS_CALLBACK)
 (CSSM_MODULE_HANDLE ModuleHandle,
  void *CallerCtx,
  CSSM_DATA_PTR VerifiedCert);


typedef CSSM_DATA CSSM_OID, *CSSM_OID_PTR;

typedef struct cssm_field {
    CSSM_OID FieldOid;
    CSSM_DATA FieldValue;
} CSSM_FIELD __attribute__((deprecated)), *CSSM_FIELD_PTR __attribute__((deprecated));


typedef struct cssm_tp_policyinfo {
    uint32 NumberOfPolicyIds;
    CSSM_FIELD_PTR PolicyIds;
    void *PolicyControl;
} CSSM_TP_POLICYINFO __attribute__((deprecated)), *CSSM_TP_POLICYINFO_PTR __attribute__((deprecated));

typedef uint32 CSSM_TP_SERVICES;
enum {

 CSSM_TP_KEY_ARCHIVE = 0x0001,
 CSSM_TP_CERT_PUBLISH = 0x0002,
 CSSM_TP_CERT_NOTIFY_RENEW = 0x0004,
 CSSM_TP_CERT_DIR_UPDATE = 0x0008,
 CSSM_TP_CRL_DISTRIBUTE = 0x0010
};

typedef uint32 CSSM_TP_ACTION;
enum {
 CSSM_TP_ACTION_DEFAULT = 0
};

typedef uint32 CSSM_TP_STOP_ON;
enum {
    CSSM_TP_STOP_ON_POLICY = 0,
    CSSM_TP_STOP_ON_NONE = 1,
    CSSM_TP_STOP_ON_FIRST_PASS = 2,
    CSSM_TP_STOP_ON_FIRST_FAIL = 3
};

typedef char *CSSM_TIMESTRING;


typedef struct cssm_dl_db_list {
    uint32 NumHandles;
    CSSM_DL_DB_HANDLE_PTR DLDBHandle;
} CSSM_DL_DB_LIST __attribute__((deprecated)), *CSSM_DL_DB_LIST_PTR __attribute__((deprecated));


typedef struct cssm_tp_callerauth_context {
    CSSM_TP_POLICYINFO Policy;
    CSSM_TIMESTRING VerifyTime;
    CSSM_TP_STOP_ON VerificationAbortOn;
    CSSM_TP_VERIFICATION_RESULTS_CALLBACK CallbackWithVerifiedCert;
    uint32 NumberOfAnchorCerts;
    CSSM_DATA_PTR AnchorCerts;
    CSSM_DL_DB_LIST_PTR DBList;
    CSSM_ACCESS_CREDENTIALS_PTR CallerCredentials;
} CSSM_TP_CALLERAUTH_CONTEXT __attribute__((deprecated)), *CSSM_TP_CALLERAUTH_CONTEXT_PTR __attribute__((deprecated));

typedef uint32 CSSM_CRL_PARSE_FORMAT, * CSSM_CRL_PARSE_FORMAT_PTR;
enum {
 CSSM_CRL_PARSE_FORMAT_NONE = 0x00,
 CSSM_CRL_PARSE_FORMAT_CUSTOM = 0x01,
 CSSM_CRL_PARSE_FORMAT_SEXPR = 0x02,
 CSSM_CRL_PARSE_FORMAT_COMPLEX = 0x03,
 CSSM_CRL_PARSE_FORMAT_OID_NAMED = 0x04,
 CSSM_CRL_PARSE_FORMAT_TUPLE = 0x05,
 CSSM_CRL_PARSE_FORMAT_MULTIPLE = 0x7FFE,
 CSSM_CRL_PARSE_FORMAT_LAST = 0x7FFF,



 CSSM_CL_CUSTOM_CRL_PARSE_FORMAT = 0x8000
};


typedef uint32 CSSM_CRL_TYPE, *CSSM_CRL_TYPE_PTR;
enum {
    CSSM_CRL_TYPE_UNKNOWN = 0x00,
    CSSM_CRL_TYPE_X_509v1 = 0x01,
    CSSM_CRL_TYPE_X_509v2 = 0x02,
    CSSM_CRL_TYPE_SPKI = 0x03,
    CSSM_CRL_TYPE_MULTIPLE = 0x7FFE
};

typedef uint32 CSSM_CRL_ENCODING, *CSSM_CRL_ENCODING_PTR;
enum {
    CSSM_CRL_ENCODING_UNKNOWN = 0x00,
    CSSM_CRL_ENCODING_CUSTOM = 0x01,
    CSSM_CRL_ENCODING_BER = 0x02,
    CSSM_CRL_ENCODING_DER = 0x03,
    CSSM_CRL_ENCODING_BLOOM = 0x04,
    CSSM_CRL_ENCODING_SEXPR = 0x05,
    CSSM_CRL_ENCODING_MULTIPLE = 0x7FFE
};

typedef struct cssm_encoded_crl {
    CSSM_CRL_TYPE CrlType;
    CSSM_CRL_ENCODING CrlEncoding;
    CSSM_DATA CrlBlob;
} CSSM_ENCODED_CRL __attribute__((deprecated)), *CSSM_ENCODED_CRL_PTR __attribute__((deprecated));


typedef struct cssm_parsed_crl {
    CSSM_CRL_TYPE CrlType;
    CSSM_CRL_PARSE_FORMAT ParsedCrlFormat;

    void *ParsedCrl;
} CSSM_PARSED_CRL __attribute__((deprecated)), *CSSM_PARSED_CRL_PTR __attribute__((deprecated));

typedef struct cssm_crl_pair {
    CSSM_ENCODED_CRL EncodedCrl;
    CSSM_PARSED_CRL ParsedCrl;
} CSSM_CRL_PAIR __attribute__((deprecated)), *CSSM_CRL_PAIR_PTR __attribute__((deprecated));

typedef uint32 CSSM_CRLGROUP_TYPE, * CSSM_CRLGROUP_TYPE_PTR;
enum {
 CSSM_CRLGROUP_DATA = 0x00,
 CSSM_CRLGROUP_ENCODED_CRL = 0x01,
 CSSM_CRLGROUP_PARSED_CRL = 0x02,
 CSSM_CRLGROUP_CRL_PAIR = 0x03
};

typedef struct cssm_crlgroup {
    CSSM_CRL_TYPE CrlType;
    CSSM_CRL_ENCODING CrlEncoding;
    uint32 NumberOfCrls;
    union {
        CSSM_DATA_PTR CrlList;
        CSSM_ENCODED_CRL_PTR EncodedCrlList;
        CSSM_PARSED_CRL_PTR ParsedCrlList;
        CSSM_CRL_PAIR_PTR PairCrlList;
    } GroupCrlList;
    CSSM_CRLGROUP_TYPE CrlGroupType;
} CSSM_CRLGROUP, *CSSM_CRLGROUP_PTR;

typedef struct cssm_fieldgroup {
    int NumberOfFields;
    CSSM_FIELD_PTR Fields;
} CSSM_FIELDGROUP __attribute__((deprecated)), *CSSM_FIELDGROUP_PTR __attribute__((deprecated));

typedef uint32 CSSM_EVIDENCE_FORM;
enum {
 CSSM_EVIDENCE_FORM_UNSPECIFIC = 0x0,
 CSSM_EVIDENCE_FORM_CERT = 0x1,
 CSSM_EVIDENCE_FORM_CRL = 0x2,
 CSSM_EVIDENCE_FORM_CERT_ID = 0x3,
 CSSM_EVIDENCE_FORM_CRL_ID = 0x4,
 CSSM_EVIDENCE_FORM_VERIFIER_TIME = 0x5,
 CSSM_EVIDENCE_FORM_CRL_THISTIME = 0x6,
 CSSM_EVIDENCE_FORM_CRL_NEXTTIME = 0x7,
 CSSM_EVIDENCE_FORM_POLICYINFO = 0x8,
 CSSM_EVIDENCE_FORM_TUPLEGROUP = 0x9
};

typedef struct cssm_evidence {
    CSSM_EVIDENCE_FORM EvidenceForm;
    void *Evidence;
} CSSM_EVIDENCE __attribute__((deprecated)), *CSSM_EVIDENCE_PTR __attribute__((deprecated));

typedef struct cssm_tp_verify_context {
    CSSM_TP_ACTION Action;
    CSSM_DATA ActionData;
    CSSM_CRLGROUP Crls;
    CSSM_TP_CALLERAUTH_CONTEXT_PTR Cred;
} CSSM_TP_VERIFY_CONTEXT __attribute__((deprecated)), *CSSM_TP_VERIFY_CONTEXT_PTR __attribute__((deprecated));

typedef struct cssm_tp_verify_context_result {
    uint32 NumberOfEvidences;
    CSSM_EVIDENCE_PTR Evidence;
} CSSM_TP_VERIFY_CONTEXT_RESULT __attribute__((deprecated)), *CSSM_TP_VERIFY_CONTEXT_RESULT_PTR __attribute__((deprecated));

typedef struct cssm_tp_request_set {
    uint32 NumberOfRequests;
    void *Requests;
} CSSM_TP_REQUEST_SET __attribute__((deprecated)), *CSSM_TP_REQUEST_SET_PTR __attribute__((deprecated));

typedef struct cssm_tp_result_set {
    uint32 NumberOfResults;
    void *Results;
} CSSM_TP_RESULT_SET __attribute__((deprecated)), *CSSM_TP_RESULT_SET_PTR __attribute__((deprecated));

typedef uint32 CSSM_TP_CONFIRM_STATUS, *CSSM_TP_CONFIRM_STATUS_PTR;
enum {
 CSSM_TP_CONFIRM_STATUS_UNKNOWN = 0x0,

 CSSM_TP_CONFIRM_ACCEPT = 0x1,


 CSSM_TP_CONFIRM_REJECT = 0x2


};

typedef struct cssm_tp_confirm_response {
    uint32 NumberOfResponses;
    CSSM_TP_CONFIRM_STATUS_PTR Responses;
} CSSM_TP_CONFIRM_RESPONSE __attribute__((deprecated)), *CSSM_TP_CONFIRM_RESPONSE_PTR __attribute__((deprecated));

enum {
 CSSM_ESTIMATED_TIME_UNKNOWN = -1
};

enum {
 CSSM_ELAPSED_TIME_UNKNOWN = -1,
 CSSM_ELAPSED_TIME_COMPLETE = -2
};

typedef struct cssm_tp_certissue_input {
    CSSM_SUBSERVICE_UID CSPSubserviceUid;
    CSSM_CL_HANDLE CLHandle;
    uint32 NumberOfTemplateFields;
    CSSM_FIELD_PTR SubjectCertFields;
    CSSM_TP_SERVICES MoreServiceRequests;
    uint32 NumberOfServiceControls;
    CSSM_FIELD_PTR ServiceControls;
    CSSM_ACCESS_CREDENTIALS_PTR UserCredentials;
} CSSM_TP_CERTISSUE_INPUT __attribute__((deprecated)), *CSSM_TP_CERTISSUE_INPUT_PTR __attribute__((deprecated));

typedef uint32 CSSM_TP_CERTISSUE_STATUS;
enum {
 CSSM_TP_CERTISSUE_STATUS_UNKNOWN = 0x0,

 CSSM_TP_CERTISSUE_OK = 0x1,

 CSSM_TP_CERTISSUE_OKWITHCERTMODS = 0x2,


 CSSM_TP_CERTISSUE_OKWITHSERVICEMODS = 0x3,



 CSSM_TP_CERTISSUE_REJECTED = 0x4,


 CSSM_TP_CERTISSUE_NOT_AUTHORIZED = 0x5,


 CSSM_TP_CERTISSUE_WILL_BE_REVOKED = 0x6


};

typedef struct cssm_tp_certissue_output {
    CSSM_TP_CERTISSUE_STATUS IssueStatus;
    CSSM_CERTGROUP_PTR CertGroup;
    CSSM_TP_SERVICES PerformedServiceRequests;
} CSSM_TP_CERTISSUE_OUTPUT __attribute__((deprecated)), *CSSM_TP_CERTISSUE_OUTPUT_PTR __attribute__((deprecated));

typedef uint32 CSSM_TP_CERTCHANGE_ACTION;
enum {
 CSSM_TP_CERTCHANGE_NONE = 0x0,
 CSSM_TP_CERTCHANGE_REVOKE = 0x1,




 CSSM_TP_CERTCHANGE_HOLD = 0x2,
# 1538 "/System/Library/Frameworks/Security.framework/Headers/cssmtype.h" 3
 CSSM_TP_CERTCHANGE_RELEASE = 0x3





};

typedef uint32 CSSM_TP_CERTCHANGE_REASON;
enum {
 CSSM_TP_CERTCHANGE_REASON_UNKNOWN = 0x0,

 CSSM_TP_CERTCHANGE_REASON_KEYCOMPROMISE = 0x1,

 CSSM_TP_CERTCHANGE_REASON_CACOMPROMISE = 0x2,

 CSSM_TP_CERTCHANGE_REASON_CEASEOPERATION = 0x3,


 CSSM_TP_CERTCHANGE_REASON_AFFILIATIONCHANGE = 0x4,


 CSSM_TP_CERTCHANGE_REASON_SUPERCEDED = 0x5,


 CSSM_TP_CERTCHANGE_REASON_SUSPECTEDCOMPROMISE = 0x6,

 CSSM_TP_CERTCHANGE_REASON_HOLDRELEASE = 0x7


};

typedef struct cssm_tp_certchange_input {
    CSSM_TP_CERTCHANGE_ACTION Action;
    CSSM_TP_CERTCHANGE_REASON Reason;
    CSSM_CL_HANDLE CLHandle;
    CSSM_DATA_PTR Cert;
    CSSM_FIELD_PTR ChangeInfo;
    CSSM_TIMESTRING StartTime;
    CSSM_ACCESS_CREDENTIALS_PTR CallerCredentials;
} CSSM_TP_CERTCHANGE_INPUT __attribute__((deprecated)), *CSSM_TP_CERTCHANGE_INPUT_PTR __attribute__((deprecated));

typedef uint32 CSSM_TP_CERTCHANGE_STATUS;
enum {
 CSSM_TP_CERTCHANGE_STATUS_UNKNOWN = 0x0,

 CSSM_TP_CERTCHANGE_OK = 0x1,


 CSSM_TP_CERTCHANGE_OKWITHNEWTIME = 0x2,


 CSSM_TP_CERTCHANGE_WRONGCA = 0x3,



 CSSM_TP_CERTCHANGE_REJECTED = 0x4,


 CSSM_TP_CERTCHANGE_NOT_AUTHORIZED = 0x5



};

typedef struct cssm_tp_certchange_output {
    CSSM_TP_CERTCHANGE_STATUS ActionStatus;
    CSSM_FIELD RevokeInfo;
} CSSM_TP_CERTCHANGE_OUTPUT __attribute__((deprecated)), *CSSM_TP_CERTCHANGE_OUTPUT_PTR __attribute__((deprecated));

typedef struct cssm_tp_certverify_input {
    CSSM_CL_HANDLE CLHandle;
    CSSM_DATA_PTR Cert;
    CSSM_TP_VERIFY_CONTEXT_PTR VerifyContext;
} CSSM_TP_CERTVERIFY_INPUT __attribute__((deprecated)), *CSSM_TP_CERTVERIFY_INPUT_PTR __attribute__((deprecated));

typedef uint32 CSSM_TP_CERTVERIFY_STATUS;
enum {
 CSSM_TP_CERTVERIFY_UNKNOWN = 0x0,
 CSSM_TP_CERTVERIFY_VALID = 0x1,
 CSSM_TP_CERTVERIFY_INVALID = 0x2,
 CSSM_TP_CERTVERIFY_REVOKED = 0x3,
 CSSM_TP_CERTVERIFY_SUSPENDED = 0x4,
 CSSM_TP_CERTVERIFY_EXPIRED = 0x5,
 CSSM_TP_CERTVERIFY_NOT_VALID_YET = 0x6,
 CSSM_TP_CERTVERIFY_INVALID_AUTHORITY = 0x7,
 CSSM_TP_CERTVERIFY_INVALID_SIGNATURE = 0x8,
 CSSM_TP_CERTVERIFY_INVALID_CERT_VALUE = 0x9,
 CSSM_TP_CERTVERIFY_INVALID_CERTGROUP = 0xA,
 CSSM_TP_CERTVERIFY_INVALID_POLICY = 0xB,
 CSSM_TP_CERTVERIFY_INVALID_POLICY_IDS = 0xC,
 CSSM_TP_CERTVERIFY_INVALID_BASIC_CONSTRAINTS = 0xD,
 CSSM_TP_CERTVERIFY_INVALID_CRL_DIST_PT = 0xE,
 CSSM_TP_CERTVERIFY_INVALID_NAME_TREE = 0xF,
 CSSM_TP_CERTVERIFY_UNKNOWN_CRITICAL_EXT = 0x10
};

typedef struct cssm_tp_certverify_output {
    CSSM_TP_CERTVERIFY_STATUS VerifyStatus;
    uint32 NumberOfEvidence;
    CSSM_EVIDENCE_PTR Evidence;
} CSSM_TP_CERTVERIFY_OUTPUT __attribute__((deprecated)), *CSSM_TP_CERTVERIFY_OUTPUT_PTR __attribute__((deprecated));

typedef struct cssm_tp_certnotarize_input {
    CSSM_CL_HANDLE CLHandle;
    uint32 NumberOfFields;
    CSSM_FIELD_PTR MoreFields;
    CSSM_FIELD_PTR SignScope;
    uint32 ScopeSize;
    CSSM_TP_SERVICES MoreServiceRequests;
    uint32 NumberOfServiceControls;
    CSSM_FIELD_PTR ServiceControls;
    CSSM_ACCESS_CREDENTIALS_PTR UserCredentials;
} CSSM_TP_CERTNOTARIZE_INPUT __attribute__((deprecated)), *CSSM_TP_CERTNOTARIZE_INPUT_PTR __attribute__((deprecated));

typedef uint32 CSSM_TP_CERTNOTARIZE_STATUS;
enum {
 CSSM_TP_CERTNOTARIZE_STATUS_UNKNOWN = 0x0,

 CSSM_TP_CERTNOTARIZE_OK = 0x1,


 CSSM_TP_CERTNOTARIZE_OKWITHOUTFIELDS = 0x2,



 CSSM_TP_CERTNOTARIZE_OKWITHSERVICEMODS = 0x3,




 CSSM_TP_CERTNOTARIZE_REJECTED = 0x4,


 CSSM_TP_CERTNOTARIZE_NOT_AUTHORIZED = 0x5


};

typedef struct cssm_tp_certnotarize_output {
    CSSM_TP_CERTNOTARIZE_STATUS NotarizeStatus;
    CSSM_CERTGROUP_PTR NotarizedCertGroup;
    CSSM_TP_SERVICES PerformedServiceRequests;
} CSSM_TP_CERTNOTARIZE_OUTPUT __attribute__((deprecated)), *CSSM_TP_CERTNOTARIZE_OUTPUT_PTR __attribute__((deprecated));

typedef struct cssm_tp_certreclaim_input {
    CSSM_CL_HANDLE CLHandle;
    uint32 NumberOfSelectionFields;
    CSSM_FIELD_PTR SelectionFields;
    CSSM_ACCESS_CREDENTIALS_PTR UserCredentials;
} CSSM_TP_CERTRECLAIM_INPUT __attribute__((deprecated)), *CSSM_TP_CERTRECLAIM_INPUT_PTR __attribute__((deprecated));

typedef uint32 CSSM_TP_CERTRECLAIM_STATUS;
enum {
 CSSM_TP_CERTRECLAIM_STATUS_UNKNOWN = 0x0,

 CSSM_TP_CERTRECLAIM_OK = 0x1,



 CSSM_TP_CERTRECLAIM_NOMATCH = 0x2,



 CSSM_TP_CERTRECLAIM_REJECTED = 0x3,


 CSSM_TP_CERTRECLAIM_NOT_AUTHORIZED = 0x4



};

typedef struct cssm_tp_certreclaim_output {
    CSSM_TP_CERTRECLAIM_STATUS ReclaimStatus;
    CSSM_CERTGROUP_PTR ReclaimedCertGroup;
    CSSM_LONG_HANDLE KeyCacheHandle;
} CSSM_TP_CERTRECLAIM_OUTPUT __attribute__((deprecated)), *CSSM_TP_CERTRECLAIM_OUTPUT_PTR __attribute__((deprecated));

typedef struct cssm_tp_crlissue_input {
    CSSM_CL_HANDLE CLHandle;
    uint32 CrlIdentifier;
    CSSM_TIMESTRING CrlThisTime;
    CSSM_FIELD_PTR PolicyIdentifier;
    CSSM_ACCESS_CREDENTIALS_PTR CallerCredentials;
} CSSM_TP_CRLISSUE_INPUT __attribute__((deprecated)), *CSSM_TP_CRLISSUE_INPUT_PTR __attribute__((deprecated));

typedef uint32 CSSM_TP_CRLISSUE_STATUS;
enum {
 CSSM_TP_CRLISSUE_STATUS_UNKNOWN = 0x0,

 CSSM_TP_CRLISSUE_OK = 0x1,



 CSSM_TP_CRLISSUE_NOT_CURRENT = 0x2,






 CSSM_TP_CRLISSUE_INVALID_DOMAIN = 0x3,




 CSSM_TP_CRLISSUE_UNKNOWN_IDENTIFIER = 0x4,



 CSSM_TP_CRLISSUE_REJECTED = 0x5,



 CSSM_TP_CRLISSUE_NOT_AUTHORIZED = 0x6



};

typedef struct cssm_tp_crlissue_output {
    CSSM_TP_CRLISSUE_STATUS IssueStatus;
    CSSM_ENCODED_CRL_PTR Crl;
    CSSM_TIMESTRING CrlNextTime;
} CSSM_TP_CRLISSUE_OUTPUT __attribute__((deprecated)), *CSSM_TP_CRLISSUE_OUTPUT_PTR __attribute__((deprecated));

typedef uint32 CSSM_TP_FORM_TYPE;
enum {
 CSSM_TP_FORM_TYPE_GENERIC = 0x0,
 CSSM_TP_FORM_TYPE_REGISTRATION = 0x1
};



typedef uint32 CSSM_CL_TEMPLATE_TYPE;
enum {
 CSSM_CL_TEMPLATE_INTERMEDIATE_CERT = 1,


 CSSM_CL_TEMPLATE_PKIX_CERTTEMPLATE = 2

};

typedef uint32 CSSM_CERT_BUNDLE_TYPE;
enum {
    CSSM_CERT_BUNDLE_UNKNOWN = 0x00,
    CSSM_CERT_BUNDLE_CUSTOM = 0x01,
    CSSM_CERT_BUNDLE_PKCS7_SIGNED_DATA = 0x02,
    CSSM_CERT_BUNDLE_PKCS7_SIGNED_ENVELOPED_DATA = 0x03,
    CSSM_CERT_BUNDLE_PKCS12 = 0x04,
    CSSM_CERT_BUNDLE_PFX = 0x05,
    CSSM_CERT_BUNDLE_SPKI_SEQUENCE = 0x06,
    CSSM_CERT_BUNDLE_PGP_KEYRING = 0x07,
    CSSM_CERT_BUNDLE_LAST = 0x7FFF,



 CSSM_CL_CUSTOM_CERT_BUNDLE_TYPE = 0x8000
};

typedef uint32 CSSM_CERT_BUNDLE_ENCODING;
enum {
    CSSM_CERT_BUNDLE_ENCODING_UNKNOWN = 0x00,
    CSSM_CERT_BUNDLE_ENCODING_CUSTOM = 0x01,
    CSSM_CERT_BUNDLE_ENCODING_BER = 0x02,
    CSSM_CERT_BUNDLE_ENCODING_DER = 0x03,
    CSSM_CERT_BUNDLE_ENCODING_SEXPR = 0x04,
    CSSM_CERT_BUNDLE_ENCODING_PGP = 0x05
};

typedef struct cssm_cert_bundle_header {
    CSSM_CERT_BUNDLE_TYPE BundleType;
    CSSM_CERT_BUNDLE_ENCODING BundleEncoding;
} CSSM_CERT_BUNDLE_HEADER __attribute__((deprecated)), *CSSM_CERT_BUNDLE_HEADER_PTR __attribute__((deprecated));

typedef struct cssm_cert_bundle {
    CSSM_CERT_BUNDLE_HEADER BundleHeader;
    CSSM_DATA Bundle;
} CSSM_CERT_BUNDLE __attribute__((deprecated)), *CSSM_CERT_BUNDLE_PTR __attribute__((deprecated));

enum {
 CSSM_FIELDVALUE_COMPLEX_DATA_TYPE = 0xFFFFFFFF
};



typedef uint32 CSSM_DB_ATTRIBUTE_NAME_FORMAT, *CSSM_DB_ATTRIBUTE_NAME_FORMAT_PTR;
enum {
    CSSM_DB_ATTRIBUTE_NAME_AS_STRING = 0,
    CSSM_DB_ATTRIBUTE_NAME_AS_OID = 1,
 CSSM_DB_ATTRIBUTE_NAME_AS_INTEGER = 2
};

typedef uint32 CSSM_DB_ATTRIBUTE_FORMAT, *CSSM_DB_ATTRIBUTE_FORMAT_PTR;
enum {
    CSSM_DB_ATTRIBUTE_FORMAT_STRING = 0,
    CSSM_DB_ATTRIBUTE_FORMAT_SINT32 = 1,
    CSSM_DB_ATTRIBUTE_FORMAT_UINT32 = 2,
    CSSM_DB_ATTRIBUTE_FORMAT_BIG_NUM = 3,
    CSSM_DB_ATTRIBUTE_FORMAT_REAL = 4,
    CSSM_DB_ATTRIBUTE_FORMAT_TIME_DATE = 5,
    CSSM_DB_ATTRIBUTE_FORMAT_BLOB = 6,
    CSSM_DB_ATTRIBUTE_FORMAT_MULTI_UINT32 = 7,
    CSSM_DB_ATTRIBUTE_FORMAT_COMPLEX = 8
};

typedef struct cssm_db_attribute_info {
    CSSM_DB_ATTRIBUTE_NAME_FORMAT AttributeNameFormat;
    union cssm_db_attribute_label {
        char *AttributeName;
        CSSM_OID AttributeOID;
        uint32 AttributeID;
    } Label;
    CSSM_DB_ATTRIBUTE_FORMAT AttributeFormat;
} CSSM_DB_ATTRIBUTE_INFO, *CSSM_DB_ATTRIBUTE_INFO_PTR;

typedef struct cssm_db_attribute_data {
    CSSM_DB_ATTRIBUTE_INFO Info;
    uint32 NumberOfValues;
    CSSM_DATA_PTR Value;
} CSSM_DB_ATTRIBUTE_DATA __attribute__((deprecated)), *CSSM_DB_ATTRIBUTE_DATA_PTR __attribute__((deprecated));

typedef uint32 CSSM_DB_RECORDTYPE;
enum {

 CSSM_DB_RECORDTYPE_SCHEMA_START = 0x00000000,
 CSSM_DB_RECORDTYPE_SCHEMA_END = CSSM_DB_RECORDTYPE_SCHEMA_START + 4,

 CSSM_DB_RECORDTYPE_OPEN_GROUP_START = 0x0000000A,
 CSSM_DB_RECORDTYPE_OPEN_GROUP_END = CSSM_DB_RECORDTYPE_OPEN_GROUP_START + 8,

 CSSM_DB_RECORDTYPE_APP_DEFINED_START = 0x80000000,
 CSSM_DB_RECORDTYPE_APP_DEFINED_END = 0xffffffff,

 CSSM_DL_DB_SCHEMA_INFO = CSSM_DB_RECORDTYPE_SCHEMA_START + 0,
 CSSM_DL_DB_SCHEMA_INDEXES = CSSM_DB_RECORDTYPE_SCHEMA_START + 1,
 CSSM_DL_DB_SCHEMA_ATTRIBUTES = CSSM_DB_RECORDTYPE_SCHEMA_START + 2,
 CSSM_DL_DB_SCHEMA_PARSING_MODULE = CSSM_DB_RECORDTYPE_SCHEMA_START + 3,

 CSSM_DL_DB_RECORD_ANY = CSSM_DB_RECORDTYPE_OPEN_GROUP_START + 0,
 CSSM_DL_DB_RECORD_CERT = CSSM_DB_RECORDTYPE_OPEN_GROUP_START + 1,
 CSSM_DL_DB_RECORD_CRL = CSSM_DB_RECORDTYPE_OPEN_GROUP_START + 2,
 CSSM_DL_DB_RECORD_POLICY = CSSM_DB_RECORDTYPE_OPEN_GROUP_START + 3,
 CSSM_DL_DB_RECORD_GENERIC = CSSM_DB_RECORDTYPE_OPEN_GROUP_START + 4,
 CSSM_DL_DB_RECORD_PUBLIC_KEY = CSSM_DB_RECORDTYPE_OPEN_GROUP_START + 5,
 CSSM_DL_DB_RECORD_PRIVATE_KEY = CSSM_DB_RECORDTYPE_OPEN_GROUP_START + 6,
 CSSM_DL_DB_RECORD_SYMMETRIC_KEY = CSSM_DB_RECORDTYPE_OPEN_GROUP_START + 7,
 CSSM_DL_DB_RECORD_ALL_KEYS = CSSM_DB_RECORDTYPE_OPEN_GROUP_START + 8
};

enum {
 CSSM_DB_CERT_USE_TRUSTED = 0x00000001,
 CSSM_DB_CERT_USE_SYSTEM = 0x00000002,
 CSSM_DB_CERT_USE_OWNER = 0x00000004,
 CSSM_DB_CERT_USE_REVOKED = 0x00000008,
 CSSM_DB_CERT_USE_SIGNING = 0x00000010,
 CSSM_DB_CERT_USE_PRIVACY = 0x00000020
};

typedef struct cssm_db_record_attribute_info {
    CSSM_DB_RECORDTYPE DataRecordType;
    uint32 NumberOfAttributes;
    CSSM_DB_ATTRIBUTE_INFO_PTR AttributeInfo;
} CSSM_DB_RECORD_ATTRIBUTE_INFO __attribute__((deprecated)), *CSSM_DB_RECORD_ATTRIBUTE_INFO_PTR __attribute__((deprecated));

typedef struct cssm_db_record_attribute_data {
    CSSM_DB_RECORDTYPE DataRecordType;
    uint32 SemanticInformation;
    uint32 NumberOfAttributes;
    CSSM_DB_ATTRIBUTE_DATA_PTR AttributeData;
} CSSM_DB_RECORD_ATTRIBUTE_DATA __attribute__((deprecated)), *CSSM_DB_RECORD_ATTRIBUTE_DATA_PTR __attribute__((deprecated));

typedef struct cssm_db_parsing_module_info {
    CSSM_DB_RECORDTYPE RecordType;
    CSSM_SUBSERVICE_UID ModuleSubserviceUid;
} CSSM_DB_PARSING_MODULE_INFO __attribute__((deprecated)), *CSSM_DB_PARSING_MODULE_INFO_PTR __attribute__((deprecated));

typedef uint32 CSSM_DB_INDEX_TYPE;
enum {
    CSSM_DB_INDEX_UNIQUE = 0,
    CSSM_DB_INDEX_NONUNIQUE = 1
};

typedef uint32 CSSM_DB_INDEXED_DATA_LOCATION;
enum {
    CSSM_DB_INDEX_ON_UNKNOWN = 0,
    CSSM_DB_INDEX_ON_ATTRIBUTE = 1,
    CSSM_DB_INDEX_ON_RECORD = 2
};

typedef struct cssm_db_index_info {
    CSSM_DB_INDEX_TYPE IndexType;
    CSSM_DB_INDEXED_DATA_LOCATION IndexedDataLocation;
    CSSM_DB_ATTRIBUTE_INFO Info;
} CSSM_DB_INDEX_INFO __attribute__((deprecated)), *CSSM_DB_INDEX_INFO_PTR __attribute__((deprecated));

typedef struct cssm_db_unique_record {
    CSSM_DB_INDEX_INFO RecordLocator;
    CSSM_DATA RecordIdentifier;
} CSSM_DB_UNIQUE_RECORD __attribute__((deprecated)), *CSSM_DB_UNIQUE_RECORD_PTR __attribute__((deprecated));

typedef struct cssm_db_record_index_info {
    CSSM_DB_RECORDTYPE DataRecordType;
    uint32 NumberOfIndexes;
    CSSM_DB_INDEX_INFO_PTR IndexInfo;
} CSSM_DB_RECORD_INDEX_INFO __attribute__((deprecated)), *CSSM_DB_RECORD_INDEX_INFO_PTR __attribute__((deprecated));

typedef uint32 CSSM_DB_ACCESS_TYPE, *CSSM_DB_ACCESS_TYPE_PTR;
enum {
 CSSM_DB_ACCESS_READ = 0x00001,
 CSSM_DB_ACCESS_WRITE = 0x00002,
 CSSM_DB_ACCESS_PRIVILEGED = 0x00004
};

typedef uint32 CSSM_DB_MODIFY_MODE;
enum {
 CSSM_DB_MODIFY_ATTRIBUTE_NONE = 0,
 CSSM_DB_MODIFY_ATTRIBUTE_ADD = CSSM_DB_MODIFY_ATTRIBUTE_NONE + 1,
 CSSM_DB_MODIFY_ATTRIBUTE_DELETE = CSSM_DB_MODIFY_ATTRIBUTE_NONE + 2,
 CSSM_DB_MODIFY_ATTRIBUTE_REPLACE = CSSM_DB_MODIFY_ATTRIBUTE_NONE + 3
};

typedef struct cssm_dbinfo {



    uint32 NumberOfRecordTypes;
    CSSM_DB_PARSING_MODULE_INFO_PTR DefaultParsingModules;
    CSSM_DB_RECORD_ATTRIBUTE_INFO_PTR RecordAttributeNames;
    CSSM_DB_RECORD_INDEX_INFO_PTR RecordIndexes;

    CSSM_BOOL IsLocal;
    char *AccessPath;
    void *Reserved;
} CSSM_DBINFO __attribute__((deprecated)), *CSSM_DBINFO_PTR __attribute__((deprecated));

typedef uint32 CSSM_DB_OPERATOR, *CSSM_DB_OPERATOR_PTR;
enum {
    CSSM_DB_EQUAL = 0,
    CSSM_DB_NOT_EQUAL = 1,
    CSSM_DB_LESS_THAN = 2,
    CSSM_DB_GREATER_THAN = 3,
    CSSM_DB_CONTAINS = 4,
    CSSM_DB_CONTAINS_INITIAL_SUBSTRING = 5,
    CSSM_DB_CONTAINS_FINAL_SUBSTRING = 6
};

typedef uint32 CSSM_DB_CONJUNCTIVE, *CSSM_DB_CONJUNCTIVE_PTR;
enum {
    CSSM_DB_NONE = 0,
    CSSM_DB_AND = 1,
    CSSM_DB_OR = 2
};

typedef struct cssm_selection_predicate {
    CSSM_DB_OPERATOR DbOperator;
    CSSM_DB_ATTRIBUTE_DATA Attribute;
} CSSM_SELECTION_PREDICATE __attribute__((deprecated)), *CSSM_SELECTION_PREDICATE_PTR __attribute__((deprecated));

enum {
 CSSM_QUERY_TIMELIMIT_NONE = 0
};

enum {
 CSSM_QUERY_SIZELIMIT_NONE = 0
};

typedef struct cssm_query_limits {
    uint32 TimeLimit;
    uint32 SizeLimit;
} CSSM_QUERY_LIMITS __attribute__((deprecated)), *CSSM_QUERY_LIMITS_PTR __attribute__((deprecated));

typedef uint32 CSSM_QUERY_FLAGS;
enum {
 CSSM_QUERY_RETURN_DATA = 0x01
};

typedef struct cssm_query {
    CSSM_DB_RECORDTYPE RecordType;
    CSSM_DB_CONJUNCTIVE Conjunctive;
    uint32 NumSelectionPredicates;
    CSSM_SELECTION_PREDICATE_PTR SelectionPredicate;
    CSSM_QUERY_LIMITS QueryLimits;
    CSSM_QUERY_FLAGS QueryFlags;
} CSSM_QUERY __attribute__((deprecated)), *CSSM_QUERY_PTR __attribute__((deprecated));

typedef uint32 CSSM_DLTYPE, *CSSM_DLTYPE_PTR;
enum {
    CSSM_DL_UNKNOWN = 0,
    CSSM_DL_CUSTOM = 1,
    CSSM_DL_LDAP = 2,
    CSSM_DL_ODBC = 3,
    CSSM_DL_PKCS11 = 4,
    CSSM_DL_FFS = 5,
    CSSM_DL_MEMORY = 6,
    CSSM_DL_REMOTEDIR = 7
};

typedef void *CSSM_DL_CUSTOM_ATTRIBUTES;
typedef void *CSSM_DL_LDAP_ATTRIBUTES;
typedef void *CSSM_DL_ODBC_ATTRIBUTES;
typedef void *CSSM_DL_FFS_ATTRIBUTES;

typedef struct cssm_dl_pkcs11_attributes {
    uint32 DeviceAccessFlags;
} *CSSM_DL_PKCS11_ATTRIBUTE, *CSSM_DL_PKCS11_ATTRIBUTE_PTR;

enum {
 CSSM_DB_DATASTORES_UNKNOWN = 0xFFFFFFFF
};

typedef struct cssm_name_list {
    uint32 NumStrings;
    char **String;
} CSSM_NAME_LIST __attribute__((deprecated)), *CSSM_NAME_LIST_PTR __attribute__((deprecated));

typedef uint32 CSSM_DB_RETRIEVAL_MODES;
enum {
 CSSM_DB_TRANSACTIONAL_MODE = 0,
 CSSM_DB_FILESYSTEMSCAN_MODE = 1
};

typedef struct cssm_db_schema_attribute_info {
    uint32 AttributeId;
    char *AttributeName;
    CSSM_OID AttributeNameID;
    CSSM_DB_ATTRIBUTE_FORMAT DataType;
} CSSM_DB_SCHEMA_ATTRIBUTE_INFO __attribute__((deprecated)), *CSSM_DB_SCHEMA_ATTRIBUTE_INFO_PTR __attribute__((deprecated));

typedef struct cssm_db_schema_index_info {
    uint32 AttributeId;
    uint32 IndexId;
    CSSM_DB_INDEX_TYPE IndexType;
    CSSM_DB_INDEXED_DATA_LOCATION IndexedDataLocation;
} CSSM_DB_SCHEMA_INDEX_INFO __attribute__((deprecated)), *CSSM_DB_SCHEMA_INDEX_INFO_PTR __attribute__((deprecated));
# 31 "/System/Library/Frameworks/Security.framework/Headers/cssmapple.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/x509defs.h" 1 3
# 35 "/System/Library/Frameworks/Security.framework/Headers/x509defs.h" 3
typedef uint8 CSSM_BER_TAG;
# 70 "/System/Library/Frameworks/Security.framework/Headers/x509defs.h" 3
typedef struct cssm_x509_algorithm_identifier {
    CSSM_OID algorithm;
    CSSM_DATA parameters;
} CSSM_X509_ALGORITHM_IDENTIFIER __attribute__((deprecated)), *CSSM_X509_ALGORITHM_IDENTIFIER_PTR __attribute__((deprecated));


typedef struct cssm_x509_type_value_pair {
    CSSM_OID type;
    CSSM_BER_TAG valueType;

    CSSM_DATA value;
} CSSM_X509_TYPE_VALUE_PAIR __attribute__((deprecated)), *CSSM_X509_TYPE_VALUE_PAIR_PTR __attribute__((deprecated));

typedef struct cssm_x509_rdn {
    uint32 numberOfPairs;
    CSSM_X509_TYPE_VALUE_PAIR_PTR AttributeTypeAndValue;
} CSSM_X509_RDN __attribute__((deprecated)), *CSSM_X509_RDN_PTR __attribute__((deprecated));

typedef struct cssm_x509_name {
    uint32 numberOfRDNs;
    CSSM_X509_RDN_PTR RelativeDistinguishedName;
} CSSM_X509_NAME __attribute__((deprecated)), *CSSM_X509_NAME_PTR __attribute__((deprecated));


typedef struct cssm_x509_subject_public_key_info {
    CSSM_X509_ALGORITHM_IDENTIFIER algorithm;
    CSSM_DATA subjectPublicKey;
} CSSM_X509_SUBJECT_PUBLIC_KEY_INFO __attribute__((deprecated)), *CSSM_X509_SUBJECT_PUBLIC_KEY_INFO_PTR __attribute__((deprecated));

typedef struct cssm_x509_time {
    CSSM_BER_TAG timeType;
    CSSM_DATA time;
} CSSM_X509_TIME __attribute__((deprecated)), *CSSM_X509_TIME_PTR __attribute__((deprecated));


typedef struct x509_validity {
    CSSM_X509_TIME notBefore;
    CSSM_X509_TIME notAfter;
} CSSM_X509_VALIDITY __attribute__((deprecated)), *CSSM_X509_VALIDITY_PTR __attribute__((deprecated));



typedef CSSM_BOOL CSSM_X509_OPTION;

typedef struct cssm_x509ext_basicConstraints {
    CSSM_BOOL cA;
    CSSM_X509_OPTION pathLenConstraintPresent;
    uint32 pathLenConstraint;
} CSSM_X509EXT_BASICCONSTRAINTS __attribute__((deprecated)), *CSSM_X509EXT_BASICCONSTRAINTS_PTR __attribute__((deprecated));

typedef enum extension_data_format {
    CSSM_X509_DATAFORMAT_ENCODED = 0,
    CSSM_X509_DATAFORMAT_PARSED,
    CSSM_X509_DATAFORMAT_PAIR
} CSSM_X509EXT_DATA_FORMAT;

typedef struct cssm_x509_extensionTagAndValue {
    CSSM_BER_TAG type;
    CSSM_DATA value;
} CSSM_X509EXT_TAGandVALUE __attribute__((deprecated)), *CSSM_X509EXT_TAGandVALUE_PTR __attribute__((deprecated));

typedef struct cssm_x509ext_pair {
    CSSM_X509EXT_TAGandVALUE tagAndValue;
    void *parsedValue;
} CSSM_X509EXT_PAIR __attribute__((deprecated)), *CSSM_X509EXT_PAIR_PTR __attribute__((deprecated));


typedef struct cssm_x509_extension {
    CSSM_OID extnId;
    CSSM_BOOL critical;
    CSSM_X509EXT_DATA_FORMAT format;
    union cssm_x509ext_value {
        CSSM_X509EXT_TAGandVALUE *tagAndValue;
        void *parsedValue;
        CSSM_X509EXT_PAIR *valuePair;
    } value;
    CSSM_DATA BERvalue;
} CSSM_X509_EXTENSION __attribute__((deprecated)), *CSSM_X509_EXTENSION_PTR __attribute__((deprecated));

typedef struct cssm_x509_extensions {
    uint32 numberOfExtensions;
    CSSM_X509_EXTENSION_PTR extensions;
} CSSM_X509_EXTENSIONS __attribute__((deprecated)), *CSSM_X509_EXTENSIONS_PTR __attribute__((deprecated));


typedef struct cssm_x509_tbs_certificate {
    CSSM_DATA version;
    CSSM_DATA serialNumber;
    CSSM_X509_ALGORITHM_IDENTIFIER signature;
    CSSM_X509_NAME issuer;
    CSSM_X509_VALIDITY validity;
    CSSM_X509_NAME subject;
    CSSM_X509_SUBJECT_PUBLIC_KEY_INFO subjectPublicKeyInfo;
    CSSM_DATA issuerUniqueIdentifier;
    CSSM_DATA subjectUniqueIdentifier;
    CSSM_X509_EXTENSIONS extensions;
} CSSM_X509_TBS_CERTIFICATE __attribute__((deprecated)), *CSSM_X509_TBS_CERTIFICATE_PTR __attribute__((deprecated));


typedef struct cssm_x509_signature {
    CSSM_X509_ALGORITHM_IDENTIFIER algorithmIdentifier;
    CSSM_DATA encrypted;
} CSSM_X509_SIGNATURE __attribute__((deprecated)), *CSSM_X509_SIGNATURE_PTR __attribute__((deprecated));


typedef struct cssm_x509_signed_certificate {
    CSSM_X509_TBS_CERTIFICATE certificate;
    CSSM_X509_SIGNATURE signature;
} CSSM_X509_SIGNED_CERTIFICATE __attribute__((deprecated)), *CSSM_X509_SIGNED_CERTIFICATE_PTR __attribute__((deprecated));

typedef struct cssm_x509ext_policyQualifierInfo {
    CSSM_OID policyQualifierId;
    CSSM_DATA value;
} CSSM_X509EXT_POLICYQUALIFIERINFO __attribute__((deprecated)), *CSSM_X509EXT_POLICYQUALIFIERINFO_PTR __attribute__((deprecated));

typedef struct cssm_x509ext_policyQualifiers {
    uint32 numberOfPolicyQualifiers;
    CSSM_X509EXT_POLICYQUALIFIERINFO *policyQualifier;
} CSSM_X509EXT_POLICYQUALIFIERS __attribute__((deprecated)), *CSSM_X509EXT_POLICYQUALIFIERS_PTR __attribute__((deprecated));

typedef struct cssm_x509ext_policyInfo {
    CSSM_OID policyIdentifier;
    CSSM_X509EXT_POLICYQUALIFIERS policyQualifiers;
} CSSM_X509EXT_POLICYINFO __attribute__((deprecated)), *CSSM_X509EXT_POLICYINFO_PTR __attribute__((deprecated));





typedef struct cssm_x509_revoked_cert_entry {
    CSSM_DATA certificateSerialNumber;
    CSSM_X509_TIME revocationDate;
    CSSM_X509_EXTENSIONS extensions;
} CSSM_X509_REVOKED_CERT_ENTRY __attribute__((deprecated)), *CSSM_X509_REVOKED_CERT_ENTRY_PTR __attribute__((deprecated));

typedef struct cssm_x509_revoked_cert_list {
    uint32 numberOfRevokedCertEntries;
    CSSM_X509_REVOKED_CERT_ENTRY_PTR revokedCertEntry;
} CSSM_X509_REVOKED_CERT_LIST __attribute__((deprecated)), *CSSM_X509_REVOKED_CERT_LIST_PTR __attribute__((deprecated));


typedef struct cssm_x509_tbs_certlist {
    CSSM_DATA version;
    CSSM_X509_ALGORITHM_IDENTIFIER signature;
    CSSM_X509_NAME issuer;
    CSSM_X509_TIME thisUpdate;
    CSSM_X509_TIME nextUpdate;
    CSSM_X509_REVOKED_CERT_LIST_PTR revokedCertificates;
    CSSM_X509_EXTENSIONS extensions;
} CSSM_X509_TBS_CERTLIST __attribute__((deprecated)), *CSSM_X509_TBS_CERTLIST_PTR __attribute__((deprecated));

typedef struct cssm_x509_signed_crl {
    CSSM_X509_TBS_CERTLIST tbsCertList;
    CSSM_X509_SIGNATURE signature;
} CSSM_X509_SIGNED_CRL __attribute__((deprecated)), *CSSM_X509_SIGNED_CRL_PTR __attribute__((deprecated));
# 32 "/System/Library/Frameworks/Security.framework/Headers/cssmapple.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/certextensions.h" 1 3
# 80 "/System/Library/Frameworks/Security.framework/Headers/certextensions.h" 3
typedef enum __CE_GeneralNameType {
 GNT_OtherName = 0,
 GNT_RFC822Name,
 GNT_DNSName,
 GNT_X400Address,
 GNT_DirectoryName,
 GNT_EdiPartyName,
 GNT_URI,
 GNT_IPAddress,
 GNT_RegisteredID
} CE_GeneralNameType;

typedef struct __CE_OtherName {
 CSSM_OID typeId;
 CSSM_DATA value;
} CE_OtherName __attribute__((deprecated));

typedef struct __CE_GeneralName {
 CE_GeneralNameType nameType;
 CSSM_BOOL berEncoded;
 CSSM_DATA name;
} CE_GeneralName __attribute__((deprecated));

typedef struct __CE_GeneralNames {
 uint32 numNames;
 CE_GeneralName *generalName;
} CE_GeneralNames __attribute__((deprecated));
# 120 "/System/Library/Frameworks/Security.framework/Headers/certextensions.h" 3
typedef struct __CE_AuthorityKeyID {
 CSSM_BOOL keyIdentifierPresent;
 CSSM_DATA keyIdentifier;
 CSSM_BOOL generalNamesPresent;
 CE_GeneralNames *generalNames;
 CSSM_BOOL serialNumberPresent;
 CSSM_DATA serialNumber;
} CE_AuthorityKeyID __attribute__((deprecated));







typedef CSSM_DATA CE_SubjectKeyID __attribute__((deprecated));
# 154 "/System/Library/Frameworks/Security.framework/Headers/certextensions.h" 3
typedef uint16 CE_KeyUsage __attribute__((deprecated));
# 184 "/System/Library/Frameworks/Security.framework/Headers/certextensions.h" 3
typedef uint32 CE_CrlReason __attribute__((deprecated));
# 214 "/System/Library/Frameworks/Security.framework/Headers/certextensions.h" 3
typedef struct __CE_ExtendedKeyUsage {
 uint32 numPurposes;
 CSSM_OID_PTR purposes;
} CE_ExtendedKeyUsage;
# 228 "/System/Library/Frameworks/Security.framework/Headers/certextensions.h" 3
typedef struct __CE_BasicConstraints {
 CSSM_BOOL cA;
 CSSM_BOOL pathLenConstraintPresent;
 uint32 pathLenConstraint;
} CE_BasicConstraints __attribute__((deprecated));
# 285 "/System/Library/Frameworks/Security.framework/Headers/certextensions.h" 3
typedef struct __CE_PolicyQualifierInfo {
 CSSM_OID policyQualifierId;
 CSSM_DATA qualifier;

} CE_PolicyQualifierInfo __attribute__((deprecated));

typedef struct __CE_PolicyInformation {
 CSSM_OID certPolicyId;
 uint32 numPolicyQualifiers;
 CE_PolicyQualifierInfo *policyQualifiers;
} CE_PolicyInformation __attribute__((deprecated));

typedef struct __CE_CertPolicies {
 uint32 numPolicies;
 CE_PolicyInformation *policies;
} CE_CertPolicies __attribute__((deprecated));
# 309 "/System/Library/Frameworks/Security.framework/Headers/certextensions.h" 3
typedef uint16 CE_NetscapeCertType __attribute__((deprecated));
# 351 "/System/Library/Frameworks/Security.framework/Headers/certextensions.h" 3
typedef uint8 CE_CrlDistReasonFlags __attribute__((deprecated));
# 361 "/System/Library/Frameworks/Security.framework/Headers/certextensions.h" 3
typedef enum __CE_CrlDistributionPointNameType {
 CE_CDNT_FullName,
 CE_CDNT_NameRelativeToCrlIssuer
} CE_CrlDistributionPointNameType __attribute__((deprecated));

typedef struct __CE_DistributionPointName {
 CE_CrlDistributionPointNameType nameType;
 union {
  CE_GeneralNames *fullName;
  CSSM_X509_RDN_PTR rdn;
 } dpn;
} CE_DistributionPointName __attribute__((deprecated));





typedef struct __CE_CRLDistributionPoint {
 CE_DistributionPointName *distPointName;
 CSSM_BOOL reasonsPresent;
 CE_CrlDistReasonFlags reasons;
 CE_GeneralNames *crlIssuer;
} CE_CRLDistributionPoint __attribute__((deprecated));

typedef struct __CE_CRLDistPointsSyntax {
 uint32 numDistPoints;
 CE_CRLDistributionPoint *distPoints;
} CE_CRLDistPointsSyntax __attribute__((deprecated));
# 403 "/System/Library/Frameworks/Security.framework/Headers/certextensions.h" 3
typedef struct __CE_AccessDescription {
 CSSM_OID accessMethod;
 CE_GeneralName accessLocation;
} CE_AccessDescription __attribute__((deprecated));

typedef struct __CE_AuthorityInfoAccess {
 uint32 numAccessDescriptions;
 CE_AccessDescription *accessDescriptions;
} CE_AuthorityInfoAccess __attribute__((deprecated));
# 420 "/System/Library/Frameworks/Security.framework/Headers/certextensions.h" 3
typedef CE_GeneralNames CE_NameRegistrationAuthorities __attribute__((deprecated));






typedef struct __CE_SemanticsInformation {
 CSSM_OID *semanticsIdentifier;
 CE_NameRegistrationAuthorities *nameRegistrationAuthorities;
} CE_SemanticsInformation __attribute__((deprecated));
# 441 "/System/Library/Frameworks/Security.framework/Headers/certextensions.h" 3
typedef struct __CE_QC_Statement {
 CSSM_OID statementId;
 CE_SemanticsInformation *semanticsInfo;
 CSSM_DATA *otherInfo;
} CE_QC_Statement __attribute__((deprecated));




typedef struct __CE_QC_Statements {
 uint32 numQCStatements;
 CE_QC_Statement *qcStatements;
} CE_QC_Statements __attribute__((deprecated));
# 462 "/System/Library/Frameworks/Security.framework/Headers/certextensions.h" 3
typedef uint32 CE_CrlNumber;






typedef uint32 CE_DeltaCrl;
# 485 "/System/Library/Frameworks/Security.framework/Headers/certextensions.h" 3
typedef struct __CE_IssuingDistributionPoint {
 CE_DistributionPointName *distPointName;
 CSSM_BOOL onlyUserCertsPresent;
 CSSM_BOOL onlyUserCerts;
 CSSM_BOOL onlyCACertsPresent;
 CSSM_BOOL onlyCACerts;
 CSSM_BOOL onlySomeReasonsPresent;
 CE_CrlDistReasonFlags onlySomeReasons;
 CSSM_BOOL indirectCrlPresent;
 CSSM_BOOL indirectCrl;
} CE_IssuingDistributionPoint __attribute__((deprecated));
# 515 "/System/Library/Frameworks/Security.framework/Headers/certextensions.h" 3
typedef struct __CE_GeneralSubtree {
 CE_GeneralNames *base;
 uint32 minimum;
 CSSM_BOOL maximumPresent;
 uint32 maximum;
} CE_GeneralSubtree __attribute__((deprecated));

typedef struct __CE_GeneralSubtrees {
 uint32 numSubtrees;
 CE_GeneralSubtree *subtrees;
} CE_GeneralSubtrees __attribute__((deprecated));

typedef struct __CE_NameConstraints {
 CE_GeneralSubtrees *permitted;
 CE_GeneralSubtrees *excluded;
} CE_NameConstraints __attribute__((deprecated));
# 544 "/System/Library/Frameworks/Security.framework/Headers/certextensions.h" 3
typedef struct __CE_PolicyMapping {
 CSSM_OID issuerDomainPolicy;
 CSSM_OID subjectDomainPolicy;
} CE_PolicyMapping __attribute__((deprecated));

typedef struct __CE_PolicyMappings {
 uint32 numPolicyMappings;
 CE_PolicyMapping *policyMappings;
} CE_PolicyMappings __attribute__((deprecated));
# 565 "/System/Library/Frameworks/Security.framework/Headers/certextensions.h" 3
typedef struct __CE_PolicyConstraints {
 CSSM_BOOL requireExplicitPolicyPresent;
 uint32 requireExplicitPolicy;
 CSSM_BOOL inhibitPolicyMappingPresent;
 uint32 inhibitPolicyMapping;
} CE_PolicyConstraints __attribute__((deprecated));






typedef uint32 CE_InhibitAnyPolicy __attribute__((deprecated));





typedef enum __CE_DataType {
 DT_AuthorityKeyID,
 DT_SubjectKeyID,
 DT_KeyUsage,
 DT_SubjectAltName,
 DT_IssuerAltName,
 DT_ExtendedKeyUsage,
 DT_BasicConstraints,
 DT_CertPolicies,
 DT_NetscapeCertType,
 DT_CrlNumber,
 DT_DeltaCrl,
 DT_CrlReason,
 DT_CrlDistributionPoints,
 DT_IssuingDistributionPoint,
 DT_AuthorityInfoAccess,
 DT_Other,
 DT_QC_Statements,
 DT_NameConstraints,
 DT_PolicyMappings,
 DT_PolicyConstraints,
 DT_InhibitAnyPolicy
} CE_DataType;




typedef union {
 CE_AuthorityKeyID authorityKeyID;
 CE_SubjectKeyID subjectKeyID;
 CE_KeyUsage keyUsage;
 CE_GeneralNames subjectAltName;
 CE_GeneralNames issuerAltName;
 CE_ExtendedKeyUsage extendedKeyUsage;
 CE_BasicConstraints basicConstraints;
 CE_CertPolicies certPolicies;
 CE_NetscapeCertType netscapeCertType;
 CE_CrlNumber crlNumber;
 CE_DeltaCrl deltaCrl;
 CE_CrlReason crlReason;
 CE_CRLDistPointsSyntax crlDistPoints;
 CE_IssuingDistributionPoint issuingDistPoint;
 CE_AuthorityInfoAccess authorityInfoAccess;
 CE_QC_Statements qualifiedCertStatements;
 CE_NameConstraints nameConstraints;
 CE_PolicyMappings policyMappings;
 CE_PolicyConstraints policyConstraints;
 CE_InhibitAnyPolicy inhibitAnyPolicy;
 CSSM_DATA rawData;
} CE_Data __attribute__((deprecated));

typedef struct __CE_DataAndType {
 CE_DataType type;
 CE_Data extension;
 CSSM_BOOL critical;
} CE_DataAndType __attribute__((deprecated));
# 33 "/System/Library/Frameworks/Security.framework/Headers/cssmapple.h" 2 3
# 43 "/System/Library/Frameworks/Security.framework/Headers/cssmapple.h" 3
extern const CSSM_GUID gGuidCssm;


extern const CSSM_GUID gGuidAppleFileDL;


extern const CSSM_GUID gGuidAppleCSP;


extern const CSSM_GUID gGuidAppleCSPDL;


extern const CSSM_GUID gGuidAppleX509CL;


extern const CSSM_GUID gGuidAppleX509TP;


extern const CSSM_GUID gGuidAppleLDAPDL;


extern const CSSM_GUID gGuidAppleDotMacTP;


extern const CSSM_GUID gGuidAppleSdCSPDL;


extern const CSSM_GUID gGuidAppleDotMacDL;



enum
{
 CSSM_WORDID_KEYCHAIN_PROMPT = CSSM_WORDID_VENDOR_START,
    CSSM_WORDID_KEYCHAIN_LOCK,
    CSSM_WORDID_KEYCHAIN_CHANGE_LOCK,
 CSSM_WORDID_PROCESS,
 CSSM_WORDID__RESERVED_1,
 CSSM_WORDID_SYMMETRIC_KEY,
 CSSM_WORDID_SYSTEM,
 CSSM_WORDID_KEY,
 CSSM_WORDID_PIN,
 CSSM_WORDID_PREAUTH,
 CSSM_WORDID_PREAUTH_SOURCE,
 CSSM_WORDID_ASYMMETRIC_KEY,
 CSSM_WORDID__FIRST_UNUSED
};


enum
{
 CSSM_ACL_SUBJECT_TYPE_KEYCHAIN_PROMPT = CSSM_WORDID_KEYCHAIN_PROMPT,
 CSSM_ACL_SUBJECT_TYPE_PROCESS = CSSM_WORDID_PROCESS,
 CSSM_ACL_SUBJECT_TYPE_CODE_SIGNATURE = CSSM_WORDID_SIGNATURE,
 CSSM_ACL_SUBJECT_TYPE_COMMENT = CSSM_WORDID_COMMENT,
 CSSM_ACL_SUBJECT_TYPE_SYMMETRIC_KEY = CSSM_WORDID_SYMMETRIC_KEY,
 CSSM_ACL_SUBJECT_TYPE_PREAUTH = CSSM_WORDID_PREAUTH,
 CSSM_ACL_SUBJECT_TYPE_PREAUTH_SOURCE = CSSM_WORDID_PREAUTH_SOURCE,
 CSSM_ACL_SUBJECT_TYPE_ASYMMETRIC_KEY = CSSM_WORDID_ASYMMETRIC_KEY
};

enum
{
 CSSM_SAMPLE_TYPE_KEYCHAIN_PROMPT = CSSM_WORDID_KEYCHAIN_PROMPT,
    CSSM_SAMPLE_TYPE_KEYCHAIN_LOCK = CSSM_WORDID_KEYCHAIN_LOCK,
    CSSM_SAMPLE_TYPE_KEYCHAIN_CHANGE_LOCK = CSSM_WORDID_KEYCHAIN_CHANGE_LOCK,
 CSSM_SAMPLE_TYPE_PROCESS = CSSM_WORDID_PROCESS,
 CSSM_SAMPLE_TYPE_COMMENT = CSSM_WORDID_COMMENT,
 CSSM_SAMPLE_TYPE_RETRY_ID = CSSM_WORDID_PROPAGATE,
 CSSM_SAMPLE_TYPE_SYMMETRIC_KEY = CSSM_WORDID_SYMMETRIC_KEY,
 CSSM_SAMPLE_TYPE_PREAUTH = CSSM_WORDID_PREAUTH,
 CSSM_SAMPLE_TYPE_ASYMMETRIC_KEY = CSSM_WORDID_ASYMMETRIC_KEY

};



enum {
 CSSM_ACL_AUTHORIZATION_CHANGE_ACL = CSSM_ACL_AUTHORIZATION_TAG_VENDOR_DEFINED_START,
 CSSM_ACL_AUTHORIZATION_CHANGE_OWNER,


 CSSM_ACL_AUTHORIZATION_PREAUTH_BASE =
  CSSM_ACL_AUTHORIZATION_TAG_VENDOR_DEFINED_START + 0x1000000,
 CSSM_ACL_AUTHORIZATION_PREAUTH_END = CSSM_ACL_AUTHORIZATION_PREAUTH_BASE + 0x10000
};
# 142 "/System/Library/Frameworks/Security.framework/Headers/cssmapple.h" 3
enum {
    CSSM_ACL_CODE_SIGNATURE_INVALID = 0,
    CSSM_ACL_CODE_SIGNATURE_OSX = 1
};



enum {
    CSSM_ACL_MATCH_UID = 0x01,
    CSSM_ACL_MATCH_GID = 0x02,
    CSSM_ACL_MATCH_HONOR_ROOT = 0x100,
    CSSM_ACL_MATCH_BITS = CSSM_ACL_MATCH_UID | CSSM_ACL_MATCH_GID
};

enum {
    CSSM_ACL_PROCESS_SELECTOR_CURRENT_VERSION = 0x101
};

typedef struct cssm_acl_process_subject_selector {
    uint16 version;
    uint16 mask;
    uint32 uid;
    uint32 gid;
} CSSM_ACL_PROCESS_SUBJECT_SELECTOR;



enum {
 CSSM_ACL_KEYCHAIN_PROMPT_CURRENT_VERSION = 0x101
};

enum {
 CSSM_ACL_KEYCHAIN_PROMPT_REQUIRE_PASSPHRASE = 0x0001,

 CSSM_ACL_KEYCHAIN_PROMPT_UNSIGNED = 0x0010,
 CSSM_ACL_KEYCHAIN_PROMPT_UNSIGNED_ACT = 0x0020,
 CSSM_ACL_KEYCHAIN_PROMPT_INVALID = 0x0040,
 CSSM_ACL_KEYCHAIN_PROMPT_INVALID_ACT = 0x0080,
};

typedef struct cssm_acl_keychain_prompt_selector {
 uint16 version;
 uint16 flags;
} CSSM_ACL_KEYCHAIN_PROMPT_SELECTOR;


typedef uint32 CSSM_ACL_PREAUTH_TRACKING_STATE;
enum {
 CSSM_ACL_PREAUTH_TRACKING_COUNT_MASK = 0xff,
 CSSM_ACL_PREAUTH_TRACKING_BLOCKED = 0,



 CSSM_ACL_PREAUTH_TRACKING_UNKNOWN = 0x40000000,
 CSSM_ACL_PREAUTH_TRACKING_AUTHORIZED = 0x80000000
};



enum {
 CSSM_DB_ACCESS_RESET = 0x10000
};



enum
{
    CSSM_ALGID_APPLE_YARROW = CSSM_ALGID_VENDOR_DEFINED,
 CSSM_ALGID_AES,
 CSSM_ALGID_FEE,
 CSSM_ALGID_FEE_MD5,
 CSSM_ALGID_FEE_SHA1,
 CSSM_ALGID_FEED,
 CSSM_ALGID_FEEDEXP,
 CSSM_ALGID_ASC,
 CSSM_ALGID_SHA1HMAC_LEGACY,
 CSSM_ALGID_KEYCHAIN_KEY,
 CSSM_ALGID_PKCS12_PBE_ENCR,
 CSSM_ALGID_PKCS12_PBE_MAC,
 CSSM_ALGID_SECURE_PASSPHRASE,
 CSSM_ALGID_PBE_OPENSSL_MD5,
 CSSM_ALGID_SHA256,
 CSSM_ALGID_SHA384,
 CSSM_ALGID_SHA512,
 CSSM_ALGID_ENTROPY_DEFAULT,
 CSSM_ALGID_SHA224,
 CSSM_ALGID_SHA224WithRSA,
 CSSM_ALGID_SHA256WithRSA,
 CSSM_ALGID_SHA384WithRSA,
 CSSM_ALGID_SHA512WithRSA,
 CSSM_ALGID_OPENSSH1,
 CSSM_ALGID_SHA224WithECDSA,
 CSSM_ALGID_SHA256WithECDSA,
 CSSM_ALGID_SHA384WithECDSA,
 CSSM_ALGID_SHA512WithECDSA,
 CSSM_ALGID_ECDSA_SPECIFIED,
 CSSM_ALGID_ECDH_X963_KDF,
    CSSM_ALGID__FIRST_UNUSED
};


enum
{

    CSSM_PADDING_APPLE_SSLv2 = CSSM_PADDING_VENDOR_DEFINED
};



enum {
 CSSM_KEYBLOB_RAW_FORMAT_VENDOR_DEFINED = 0x80000000
};
enum {

 CSSM_KEYBLOB_RAW_FORMAT_X509 = CSSM_KEYBLOB_RAW_FORMAT_VENDOR_DEFINED,

 CSSM_KEYBLOB_RAW_FORMAT_OPENSSH,

 CSSM_KEYBLOB_RAW_FORMAT_OPENSSL,

 CSSM_KEYBLOB_RAW_FORMAT_OPENSSH2
};


enum
{
    CSSM_CUSTOM_COMMON_ERROR_EXTENT = 0x00e0,

    CSSM_ERRCODE_NO_USER_INTERACTION = 0x00e0,
    CSSM_ERRCODE_USER_CANCELED = 0x00e1,
 CSSM_ERRCODE_SERVICE_NOT_AVAILABLE = 0x00e2,
 CSSM_ERRCODE_INSUFFICIENT_CLIENT_IDENTIFICATION = 0x00e3,
 CSSM_ERRCODE_DEVICE_RESET = 0x00e4,
 CSSM_ERRCODE_DEVICE_FAILED = 0x00e5
};

enum {
 CSSMERR_CSSM_NO_USER_INTERACTION = CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_NO_USER_INTERACTION,
 CSSMERR_AC_NO_USER_INTERACTION = CSSM_AC_BASE_ERROR + CSSM_ERRCODE_NO_USER_INTERACTION,
 CSSMERR_CSP_NO_USER_INTERACTION = CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_NO_USER_INTERACTION,
 CSSMERR_CL_NO_USER_INTERACTION = CSSM_CL_BASE_ERROR + CSSM_ERRCODE_NO_USER_INTERACTION,
 CSSMERR_DL_NO_USER_INTERACTION = CSSM_DL_BASE_ERROR + CSSM_ERRCODE_NO_USER_INTERACTION,
 CSSMERR_TP_NO_USER_INTERACTION = CSSM_TP_BASE_ERROR + CSSM_ERRCODE_NO_USER_INTERACTION,

 CSSMERR_CSSM_USER_CANCELED = CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_USER_CANCELED,
 CSSMERR_AC_USER_CANCELED = CSSM_AC_BASE_ERROR + CSSM_ERRCODE_USER_CANCELED,
 CSSMERR_CSP_USER_CANCELED = CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_USER_CANCELED,
 CSSMERR_CL_USER_CANCELED = CSSM_CL_BASE_ERROR + CSSM_ERRCODE_USER_CANCELED,
 CSSMERR_DL_USER_CANCELED = CSSM_DL_BASE_ERROR + CSSM_ERRCODE_USER_CANCELED,
 CSSMERR_TP_USER_CANCELED = CSSM_TP_BASE_ERROR + CSSM_ERRCODE_USER_CANCELED,

 CSSMERR_CSSM_SERVICE_NOT_AVAILABLE = CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_SERVICE_NOT_AVAILABLE,
 CSSMERR_AC_SERVICE_NOT_AVAILABLE = CSSM_AC_BASE_ERROR + CSSM_ERRCODE_SERVICE_NOT_AVAILABLE,
 CSSMERR_CSP_SERVICE_NOT_AVAILABLE = CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_SERVICE_NOT_AVAILABLE,
 CSSMERR_CL_SERVICE_NOT_AVAILABLE = CSSM_CL_BASE_ERROR + CSSM_ERRCODE_SERVICE_NOT_AVAILABLE,
 CSSMERR_DL_SERVICE_NOT_AVAILABLE = CSSM_DL_BASE_ERROR + CSSM_ERRCODE_SERVICE_NOT_AVAILABLE,
 CSSMERR_TP_SERVICE_NOT_AVAILABLE = CSSM_TP_BASE_ERROR + CSSM_ERRCODE_SERVICE_NOT_AVAILABLE,

 CSSMERR_CSSM_INSUFFICIENT_CLIENT_IDENTIFICATION = CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_INSUFFICIENT_CLIENT_IDENTIFICATION,
 CSSMERR_AC_INSUFFICIENT_CLIENT_IDENTIFICATION = CSSM_AC_BASE_ERROR + CSSM_ERRCODE_INSUFFICIENT_CLIENT_IDENTIFICATION,
 CSSMERR_CSP_INSUFFICIENT_CLIENT_IDENTIFICATION = CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_INSUFFICIENT_CLIENT_IDENTIFICATION,
 CSSMERR_CL_INSUFFICIENT_CLIENT_IDENTIFICATION = CSSM_CL_BASE_ERROR + CSSM_ERRCODE_INSUFFICIENT_CLIENT_IDENTIFICATION,
 CSSMERR_DL_INSUFFICIENT_CLIENT_IDENTIFICATION = CSSM_DL_BASE_ERROR + CSSM_ERRCODE_INSUFFICIENT_CLIENT_IDENTIFICATION,
 CSSMERR_TP_INSUFFICIENT_CLIENT_IDENTIFICATION = CSSM_TP_BASE_ERROR + CSSM_ERRCODE_INSUFFICIENT_CLIENT_IDENTIFICATION,

 CSSMERR_CSSM_DEVICE_RESET = CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_DEVICE_RESET,
 CSSMERR_AC_DEVICE_RESET = CSSM_AC_BASE_ERROR + CSSM_ERRCODE_DEVICE_RESET,
 CSSMERR_CSP_DEVICE_RESET = CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_DEVICE_RESET,
 CSSMERR_CL_DEVICE_RESET = CSSM_CL_BASE_ERROR + CSSM_ERRCODE_DEVICE_RESET,
 CSSMERR_DL_DEVICE_RESET = CSSM_DL_BASE_ERROR + CSSM_ERRCODE_DEVICE_RESET,
 CSSMERR_TP_DEVICE_RESET = CSSM_TP_BASE_ERROR + CSSM_ERRCODE_DEVICE_RESET,

 CSSMERR_CSSM_DEVICE_FAILED = CSSM_CSSM_BASE_ERROR + CSSM_ERRCODE_DEVICE_FAILED,
 CSSMERR_AC_DEVICE_FAILED = CSSM_AC_BASE_ERROR + CSSM_ERRCODE_DEVICE_FAILED,
 CSSMERR_CSP_DEVICE_FAILED = CSSM_CSP_BASE_ERROR + CSSM_ERRCODE_DEVICE_FAILED,
 CSSMERR_CL_DEVICE_FAILED = CSSM_CL_BASE_ERROR + CSSM_ERRCODE_DEVICE_FAILED,
 CSSMERR_DL_DEVICE_FAILED = CSSM_DL_BASE_ERROR + CSSM_ERRCODE_DEVICE_FAILED,
 CSSMERR_TP_DEVICE_FAILED = CSSM_TP_BASE_ERROR + CSSM_ERRCODE_DEVICE_FAILED
};


enum {
 CSSMERR_CSP_APPLE_ADD_APPLICATION_ACL_SUBJECT = CSSM_CSP_PRIVATE_ERROR + 0,




 CSSMERR_CSP_APPLE_PUBLIC_KEY_INCOMPLETE = CSSM_CSP_PRIVATE_ERROR + 1,


 CSSMERR_CSP_APPLE_SIGNATURE_MISMATCH = CSSM_CSP_PRIVATE_ERROR + 2,


 CSSMERR_CSP_APPLE_INVALID_KEY_START_DATE = CSSM_CSP_PRIVATE_ERROR + 3,
 CSSMERR_CSP_APPLE_INVALID_KEY_END_DATE = CSSM_CSP_PRIVATE_ERROR + 4,


 CSSMERR_CSPDL_APPLE_DL_CONVERSION_ERROR = CSSM_CSP_PRIVATE_ERROR + 5,


 CSSMERR_CSP_APPLE_SSLv2_ROLLBACK = CSSM_CSP_PRIVATE_ERROR + 6
};



enum
{
    CSSM_DL_DB_RECORD_GENERIC_PASSWORD = CSSM_DB_RECORDTYPE_APP_DEFINED_START + 0,
    CSSM_DL_DB_RECORD_INTERNET_PASSWORD = CSSM_DB_RECORDTYPE_APP_DEFINED_START + 1,
    CSSM_DL_DB_RECORD_APPLESHARE_PASSWORD = CSSM_DB_RECORDTYPE_APP_DEFINED_START + 2,

    CSSM_DL_DB_RECORD_X509_CERTIFICATE = CSSM_DB_RECORDTYPE_APP_DEFINED_START + 0x1000,
 CSSM_DL_DB_RECORD_USER_TRUST,
 CSSM_DL_DB_RECORD_X509_CRL,
 CSSM_DL_DB_RECORD_UNLOCK_REFERRAL,
 CSSM_DL_DB_RECORD_EXTENDED_ATTRIBUTE,
    CSSM_DL_DB_RECORD_METADATA = CSSM_DB_RECORDTYPE_APP_DEFINED_START + 0x8000
};


enum {



 CSSM_APPLEFILEDL_TOGGLE_AUTOCOMMIT,


 CSSM_APPLEFILEDL_COMMIT,


 CSSM_APPLEFILEDL_ROLLBACK
};


enum {
 CSSM_APPLE_UNLOCK_TYPE_KEY_DIRECT = 1,
 CSSM_APPLE_UNLOCK_TYPE_WRAPPED_PRIVATE = 2
};


enum
{



 CSSMERR_APPLEDL_INVALID_OPEN_PARAMETERS = CSSM_DL_PRIVATE_ERROR + 0,


 CSSMERR_APPLEDL_DISK_FULL = CSSM_DL_PRIVATE_ERROR + 1,


 CSSMERR_APPLEDL_QUOTA_EXCEEDED = CSSM_DL_PRIVATE_ERROR + 2,


 CSSMERR_APPLEDL_FILE_TOO_BIG = CSSM_DL_PRIVATE_ERROR + 3,


    CSSMERR_APPLEDL_INVALID_DATABASE_BLOB = CSSM_DL_PRIVATE_ERROR + 4,
    CSSMERR_APPLEDL_INVALID_KEY_BLOB = CSSM_DL_PRIVATE_ERROR + 5,


    CSSMERR_APPLEDL_INCOMPATIBLE_DATABASE_BLOB = CSSM_DL_PRIVATE_ERROR + 6,
    CSSMERR_APPLEDL_INCOMPATIBLE_KEY_BLOB = CSSM_DL_PRIVATE_ERROR + 7,
};


enum
{

 CSSMERR_APPLETP_HOSTNAME_MISMATCH = CSSM_TP_PRIVATE_ERROR + 0,

 CSSMERR_APPLETP_UNKNOWN_CRITICAL_EXTEN = CSSM_TP_PRIVATE_ERROR + 1,

 CSSMERR_APPLETP_NO_BASIC_CONSTRAINTS = CSSM_TP_PRIVATE_ERROR + 2,

 CSSMERR_APPLETP_INVALID_CA = CSSM_TP_PRIVATE_ERROR + 3,

 CSSMERR_APPLETP_INVALID_AUTHORITY_ID = CSSM_TP_PRIVATE_ERROR + 4,

 CSSMERR_APPLETP_INVALID_SUBJECT_ID = CSSM_TP_PRIVATE_ERROR + 5,

 CSSMERR_APPLETP_INVALID_KEY_USAGE = CSSM_TP_PRIVATE_ERROR + 6,

 CSSMERR_APPLETP_INVALID_EXTENDED_KEY_USAGE = CSSM_TP_PRIVATE_ERROR + 7,

 CSSMERR_APPLETP_INVALID_ID_LINKAGE = CSSM_TP_PRIVATE_ERROR + 8,

 CSSMERR_APPLETP_PATH_LEN_CONSTRAINT = CSSM_TP_PRIVATE_ERROR + 9,

 CSSMERR_APPLETP_INVALID_ROOT = CSSM_TP_PRIVATE_ERROR + 10,

 CSSMERR_APPLETP_CRL_EXPIRED = CSSM_TP_PRIVATE_ERROR + 11,
 CSSMERR_APPLETP_CRL_NOT_VALID_YET = CSSM_TP_PRIVATE_ERROR + 12,

 CSSMERR_APPLETP_CRL_NOT_FOUND = CSSM_TP_PRIVATE_ERROR + 13,

 CSSMERR_APPLETP_CRL_SERVER_DOWN = CSSM_TP_PRIVATE_ERROR + 14,

 CSSMERR_APPLETP_CRL_BAD_URI = CSSM_TP_PRIVATE_ERROR + 15,

 CSSMERR_APPLETP_UNKNOWN_CERT_EXTEN = CSSM_TP_PRIVATE_ERROR + 16,
 CSSMERR_APPLETP_UNKNOWN_CRL_EXTEN = CSSM_TP_PRIVATE_ERROR + 17,

 CSSMERR_APPLETP_CRL_NOT_TRUSTED = CSSM_TP_PRIVATE_ERROR + 18,

 CSSMERR_APPLETP_CRL_INVALID_ANCHOR_CERT = CSSM_TP_PRIVATE_ERROR + 19,

 CSSMERR_APPLETP_CRL_POLICY_FAIL = CSSM_TP_PRIVATE_ERROR + 20,

 CSSMERR_APPLETP_IDP_FAIL = CSSM_TP_PRIVATE_ERROR + 21,

 CSSMERR_APPLETP_CERT_NOT_FOUND_FROM_ISSUER = CSSM_TP_PRIVATE_ERROR + 22,

 CSSMERR_APPLETP_BAD_CERT_FROM_ISSUER = CSSM_TP_PRIVATE_ERROR + 23,

 CSSMERR_APPLETP_SMIME_EMAIL_ADDRS_NOT_FOUND = CSSM_TP_PRIVATE_ERROR + 24,

 CSSMERR_APPLETP_SMIME_BAD_EXT_KEY_USE = CSSM_TP_PRIVATE_ERROR + 25,

 CSSMERR_APPLETP_SMIME_BAD_KEY_USE = CSSM_TP_PRIVATE_ERROR + 26,

 CSSMERR_APPLETP_SMIME_KEYUSAGE_NOT_CRITICAL = CSSM_TP_PRIVATE_ERROR + 27,


 CSSMERR_APPLETP_SMIME_NO_EMAIL_ADDRS = CSSM_TP_PRIVATE_ERROR + 28,


 CSSMERR_APPLETP_SMIME_SUBJ_ALT_NAME_NOT_CRIT = CSSM_TP_PRIVATE_ERROR + 29,

 CSSMERR_APPLETP_SSL_BAD_EXT_KEY_USE = CSSM_TP_PRIVATE_ERROR + 30,

 CSSMERR_APPLETP_OCSP_BAD_RESPONSE = CSSM_TP_PRIVATE_ERROR + 31,

 CSSMERR_APPLETP_OCSP_BAD_REQUEST = CSSM_TP_PRIVATE_ERROR + 32,

 CSSMERR_APPLETP_OCSP_UNAVAILABLE = CSSM_TP_PRIVATE_ERROR + 33,

 CSSMERR_APPLETP_OCSP_STATUS_UNRECOGNIZED = CSSM_TP_PRIVATE_ERROR + 34,

 CSSMERR_APPLETP_INCOMPLETE_REVOCATION_CHECK = CSSM_TP_PRIVATE_ERROR + 35,

 CSSMERR_APPLETP_NETWORK_FAILURE = CSSM_TP_PRIVATE_ERROR + 36,

 CSSMERR_APPLETP_OCSP_NOT_TRUSTED = CSSM_TP_PRIVATE_ERROR + 37,

 CSSMERR_APPLETP_OCSP_INVALID_ANCHOR_CERT = CSSM_TP_PRIVATE_ERROR + 38,

 CSSMERR_APPLETP_OCSP_SIG_ERROR = CSSM_TP_PRIVATE_ERROR + 39,

 CSSMERR_APPLETP_OCSP_NO_SIGNER = CSSM_TP_PRIVATE_ERROR + 40,

 CSSMERR_APPLETP_OCSP_RESP_MALFORMED_REQ = CSSM_TP_PRIVATE_ERROR + 41,

 CSSMERR_APPLETP_OCSP_RESP_INTERNAL_ERR = CSSM_TP_PRIVATE_ERROR + 42,

 CSSMERR_APPLETP_OCSP_RESP_TRY_LATER = CSSM_TP_PRIVATE_ERROR + 43,

 CSSMERR_APPLETP_OCSP_RESP_SIG_REQUIRED = CSSM_TP_PRIVATE_ERROR + 44,

 CSSMERR_APPLETP_OCSP_RESP_UNAUTHORIZED = CSSM_TP_PRIVATE_ERROR + 45,

 CSSMERR_APPLETP_OCSP_NONCE_MISMATCH = CSSM_TP_PRIVATE_ERROR + 46,

 CSSMERR_APPLETP_CS_BAD_CERT_CHAIN_LENGTH = CSSM_TP_PRIVATE_ERROR + 47,

 CSSMERR_APPLETP_CS_NO_BASIC_CONSTRAINTS = CSSM_TP_PRIVATE_ERROR + 48,

 CSSMERR_APPLETP_CS_BAD_PATH_LENGTH = CSSM_TP_PRIVATE_ERROR + 49,

 CSSMERR_APPLETP_CS_NO_EXTENDED_KEY_USAGE = CSSM_TP_PRIVATE_ERROR + 50,

 CSSMERR_APPLETP_CODE_SIGN_DEVELOPMENT = CSSM_TP_PRIVATE_ERROR + 51,

 CSSMERR_APPLETP_RS_BAD_CERT_CHAIN_LENGTH = CSSM_TP_PRIVATE_ERROR + 52,

 CSSMERR_APPLETP_RS_BAD_EXTENDED_KEY_USAGE = CSSM_TP_PRIVATE_ERROR + 53,

 CSSMERR_APPLETP_TRUST_SETTING_DENY = CSSM_TP_PRIVATE_ERROR + 54,

 CSSMERR_APPLETP_INVALID_EMPTY_SUBJECT = CSSM_TP_PRIVATE_ERROR + 55,

 CSSMERR_APPLETP_UNKNOWN_QUAL_CERT_STATEMENT = CSSM_TP_PRIVATE_ERROR + 56,

 CSSMERR_APPLETP_MISSING_REQUIRED_EXTENSION = CSSM_TP_PRIVATE_ERROR + 57
};


enum
{

 CSSMERR_APPLE_DOTMAC_REQ_QUEUED = CSSM_TP_PRIVATE_ERROR + 100,

 CSSMERR_APPLE_DOTMAC_REQ_REDIRECT = CSSM_TP_PRIVATE_ERROR + 101,

 CSSMERR_APPLE_DOTMAC_REQ_SERVER_ERR = CSSM_TP_PRIVATE_ERROR + 102,

 CSSMERR_APPLE_DOTMAC_REQ_SERVER_PARAM = CSSM_TP_PRIVATE_ERROR + 103,

 CSSMERR_APPLE_DOTMAC_REQ_SERVER_AUTH = CSSM_TP_PRIVATE_ERROR + 104,

 CSSMERR_APPLE_DOTMAC_REQ_SERVER_UNIMPL = CSSM_TP_PRIVATE_ERROR + 105,

 CSSMERR_APPLE_DOTMAC_REQ_SERVER_NOT_AVAIL = CSSM_TP_PRIVATE_ERROR + 106,

 CSSMERR_APPLE_DOTMAC_REQ_SERVER_ALREADY_EXIST = CSSM_TP_PRIVATE_ERROR + 107,

 CSSMERR_APPLE_DOTMAC_REQ_SERVER_SERVICE_ERROR = CSSM_TP_PRIVATE_ERROR + 108,

 CSSMERR_APPLE_DOTMAC_REQ_IS_PENDING = CSSM_TP_PRIVATE_ERROR + 109,

 CSSMERR_APPLE_DOTMAC_NO_REQ_PENDING = CSSM_TP_PRIVATE_ERROR + 110,

 CSSMERR_APPLE_DOTMAC_CSR_VERIFY_FAIL = CSSM_TP_PRIVATE_ERROR + 111,

 CSSMERR_APPLE_DOTMAC_FAILED_CONSISTENCY_CHECK = CSSM_TP_PRIVATE_ERROR + 112
};

enum
{
 CSSM_APPLEDL_OPEN_PARAMETERS_VERSION = 1
};

enum cssm_appledl_open_parameters_mask
{
 kCSSM_APPLEDL_MASK_MODE = (1 << 0)
};





typedef struct cssm_appledl_open_parameters
{
 uint32 length;
 uint32 version;
# 585 "/System/Library/Frameworks/Security.framework/Headers/cssmapple.h" 3
 CSSM_BOOL autoCommit;


 uint32 mask;


 mode_t mode;
} CSSM_APPLEDL_OPEN_PARAMETERS, *CSSM_APPLEDL_OPEN_PARAMETERS_PTR;



enum
{


 CSSM_APPLECSPDL_DB_LOCK = 0,







 CSSM_APPLECSPDL_DB_UNLOCK = 1,
# 620 "/System/Library/Frameworks/Security.framework/Headers/cssmapple.h" 3
 CSSM_APPLECSPDL_DB_GET_SETTINGS = 2,







 CSSM_APPLECSPDL_DB_SET_SETTINGS = 3,
# 639 "/System/Library/Frameworks/Security.framework/Headers/cssmapple.h" 3
 CSSM_APPLECSPDL_DB_IS_LOCKED = 4,
# 655 "/System/Library/Frameworks/Security.framework/Headers/cssmapple.h" 3
 CSSM_APPLECSPDL_DB_CHANGE_PASSWORD =5,


 CSSM_APPLECSPDL_DB_GET_HANDLE = 6,


 CSSM_APPLESCPDL_CSP_GET_KEYHANDLE = 7,

 CSSM_APPLE_PRIVATE_CSPDL_CODE_8 = 8,
 CSSM_APPLE_PRIVATE_CSPDL_CODE_9 = 9,
 CSSM_APPLE_PRIVATE_CSPDL_CODE_10 = 10,
 CSSM_APPLE_PRIVATE_CSPDL_CODE_11 = 11,
 CSSM_APPLE_PRIVATE_CSPDL_CODE_12 = 12,
 CSSM_APPLE_PRIVATE_CSPDL_CODE_13 = 13,
 CSSM_APPLE_PRIVATE_CSPDL_CODE_14 = 14,
 CSSM_APPLE_PRIVATE_CSPDL_CODE_15 = 15,
 CSSM_APPLE_PRIVATE_CSPDL_CODE_16 = 16,






 CSSM_APPLECSP_KEYDIGEST = 0x100
};




typedef struct cssm_applecspdl_db_settings_parameters
{
 uint32 idleTimeout;
 uint8 lockOnSleep;
} CSSM_APPLECSPDL_DB_SETTINGS_PARAMETERS, *CSSM_APPLECSPDL_DB_SETTINGS_PARAMETERS_PTR;


typedef struct cssm_applecspdl_db_is_locked_parameters
{
 uint8 isLocked;
} CSSM_APPLECSPDL_DB_IS_LOCKED_PARAMETERS, *CSSM_APPLECSPDL_DB_IS_LOCKED_PARAMETERS_PTR;


typedef struct cssm_applecspdl_db_change_password_parameters
{
 CSSM_ACCESS_CREDENTIALS *accessCredentials;
} CSSM_APPLECSPDL_DB_CHANGE_PASSWORD_PARAMETERS, *CSSM_APPLECSPDL_DB_CHANGE_PASSWORD_PARAMETERS_PTR;


enum {
 CSSM_KEYBLOB_WRAPPED_FORMAT_APPLE_CUSTOM = 100,
 CSSM_KEYBLOB_WRAPPED_FORMAT_OPENSSL,
 CSSM_KEYBLOB_WRAPPED_FORMAT_OPENSSH1
};




enum {
 CSSM_ATTRIBUTE_VENDOR_DEFINED = 0x800000
};

enum {



    CSSM_ATTRIBUTE_PUBLIC_KEY =
   (CSSM_ATTRIBUTE_DATA_KEY | (CSSM_ATTRIBUTE_VENDOR_DEFINED + 0)),





 CSSM_ATTRIBUTE_FEE_PRIME_TYPE =
   (CSSM_ATTRIBUTE_DATA_UINT32 | (CSSM_ATTRIBUTE_VENDOR_DEFINED + 1)),
 CSSM_ATTRIBUTE_FEE_CURVE_TYPE =
   (CSSM_ATTRIBUTE_DATA_UINT32 | (CSSM_ATTRIBUTE_VENDOR_DEFINED + 2)),





 CSSM_ATTRIBUTE_ASC_OPTIMIZATION =
   (CSSM_ATTRIBUTE_DATA_UINT32 | (CSSM_ATTRIBUTE_VENDOR_DEFINED + 3)),




 CSSM_ATTRIBUTE_RSA_BLINDING =
   (CSSM_ATTRIBUTE_DATA_UINT32 | (CSSM_ATTRIBUTE_VENDOR_DEFINED + 4)),





 CSSM_ATTRIBUTE_PARAM_KEY =
   (CSSM_ATTRIBUTE_DATA_KEY | (CSSM_ATTRIBUTE_VENDOR_DEFINED + 5)),





 CSSM_ATTRIBUTE_PROMPT =
   (CSSM_ATTRIBUTE_DATA_CSSM_DATA | (CSSM_ATTRIBUTE_VENDOR_DEFINED + 6)),





 CSSM_ATTRIBUTE_ALERT_TITLE =
   (CSSM_ATTRIBUTE_DATA_CSSM_DATA | (CSSM_ATTRIBUTE_VENDOR_DEFINED + 7)),






 CSSM_ATTRIBUTE_VERIFY_PASSPHRASE =
   (CSSM_ATTRIBUTE_DATA_UINT32 | (CSSM_ATTRIBUTE_VENDOR_DEFINED + 8))

};




enum {
 CSSM_FEE_PRIME_TYPE_DEFAULT = 0,
 CSSM_FEE_PRIME_TYPE_MERSENNE,
 CSSM_FEE_PRIME_TYPE_FEE,
 CSSM_FEE_PRIME_TYPE_GENERAL
};






enum {
 CSSM_FEE_CURVE_TYPE_DEFAULT = 0,
 CSSM_FEE_CURVE_TYPE_MONTGOMERY,
 CSSM_FEE_CURVE_TYPE_WEIERSTRASS,
 CSSM_FEE_CURVE_TYPE_ANSI_X9_62
};




enum {
 CSSM_ASC_OPTIMIZE_DEFAULT = 0,
 CSSM_ASC_OPTIMIZE_SIZE,
 CSSM_ASC_OPTIMIZE_SECURITY,
 CSSM_ASC_OPTIMIZE_TIME,
 CSSM_ASC_OPTIMIZE_TIME_SIZE,
 CSSM_ASC_OPTIMIZE_ASCII,
};




enum {




 CSSM_KEYATTR_PARTIAL = 0x00010000,





 CSSM_KEYATTR_PUBLIC_KEY_ENCRYPT = 0x00020000
};




typedef struct {
 const char *string;
 const CSSM_OID *oid;
} CSSM_APPLE_TP_NAME_OID;







typedef struct {
 CSSM_CSP_HANDLE cspHand;
 CSSM_CL_HANDLE clHand;
 uint32 serialNumber;
 uint32 numSubjectNames;
 CSSM_APPLE_TP_NAME_OID *subjectNames;







 uint32 numIssuerNames;
 CSSM_APPLE_TP_NAME_OID *issuerNames;

 CSSM_X509_NAME_PTR issuerNameX509;
 const CSSM_KEY *certPublicKey;
 const CSSM_KEY *issuerPrivateKey;



 CSSM_ALGORITHMS signatureAlg;
 CSSM_OID signatureOid;
 uint32 notBefore;
 uint32 notAfter;
 uint32 numExtensions;
 CE_DataAndType *extensions;




 const char *challengeString;
} CSSM_APPLE_TP_CERT_REQUEST;
# 890 "/System/Library/Frameworks/Security.framework/Headers/cssmapple.h" 3
typedef struct {
 uint32 Version;







 uint32 ServerNameLen;
 const char *ServerName;


 uint32 Flags;
} CSSM_APPLE_TP_SSL_OPTIONS;
# 914 "/System/Library/Frameworks/Security.framework/Headers/cssmapple.h" 3
typedef uint32 CSSM_APPLE_TP_CRL_OPT_FLAGS;
enum {

 CSSM_TP_ACTION_REQUIRE_CRL_PER_CERT = 0x00000001,

 CSSM_TP_ACTION_FETCH_CRL_FROM_NET = 0x00000002,


 CSSM_TP_ACTION_CRL_SUFFICIENT = 0x00000004,

 CSSM_TP_ACTION_REQUIRE_CRL_IF_PRESENT = 0x00000008
};

typedef struct {
 uint32 Version;
 CSSM_APPLE_TP_CRL_OPT_FLAGS CrlFlags;







 CSSM_DL_DB_HANDLE_PTR crlStore;
} CSSM_APPLE_TP_CRL_OPTIONS;
# 947 "/System/Library/Frameworks/Security.framework/Headers/cssmapple.h" 3
typedef struct {
 uint32 Version;





 CE_KeyUsage IntendedUsage;
# 963 "/System/Library/Frameworks/Security.framework/Headers/cssmapple.h" 3
 uint32 SenderEmailLen;
 const char *SenderEmail;
} CSSM_APPLE_TP_SMIME_OPTIONS;







typedef uint32 CSSM_APPLE_TP_ACTION_FLAGS;
enum {
 CSSM_TP_ACTION_ALLOW_EXPIRED = 0x00000001,
 CSSM_TP_ACTION_LEAF_IS_CA = 0x00000002,
 CSSM_TP_ACTION_FETCH_CERT_FROM_NET = 0x00000004,
 CSSM_TP_ACTION_ALLOW_EXPIRED_ROOT = 0x00000008,
 CSSM_TP_ACTION_REQUIRE_REV_PER_CERT = 0x00000010,

 CSSM_TP_ACTION_TRUST_SETTINGS = 0x00000020,

 CSSM_TP_ACTION_IMPLICIT_ANCHORS = 0x00000040

};


typedef struct {
 uint32 Version;
 CSSM_APPLE_TP_ACTION_FLAGS ActionFlags;
} CSSM_APPLE_TP_ACTION_DATA;
# 1000 "/System/Library/Frameworks/Security.framework/Headers/cssmapple.h" 3
typedef uint32 CSSM_TP_APPLE_CERT_STATUS;
enum
{
 CSSM_CERT_STATUS_EXPIRED = 0x00000001,
 CSSM_CERT_STATUS_NOT_VALID_YET = 0x00000002,
 CSSM_CERT_STATUS_IS_IN_INPUT_CERTS = 0x00000004,
 CSSM_CERT_STATUS_IS_IN_ANCHORS = 0x00000008,
 CSSM_CERT_STATUS_IS_ROOT = 0x00000010,
 CSSM_CERT_STATUS_IS_FROM_NET = 0x00000020,

 CSSM_CERT_STATUS_TRUST_SETTINGS_FOUND_USER = 0x00000040,

 CSSM_CERT_STATUS_TRUST_SETTINGS_FOUND_ADMIN = 0x00000080,

 CSSM_CERT_STATUS_TRUST_SETTINGS_FOUND_SYSTEM = 0x00000100,

 CSSM_CERT_STATUS_TRUST_SETTINGS_TRUST = 0x00000200,

 CSSM_CERT_STATUS_TRUST_SETTINGS_DENY = 0x00000400,

 CSSM_CERT_STATUS_TRUST_SETTINGS_IGNORED_ERROR = 0x00000800
};

typedef struct {
 CSSM_TP_APPLE_CERT_STATUS StatusBits;
 uint32 NumStatusCodes;
 CSSM_RETURN *StatusCodes;


 uint32 Index;


 CSSM_DL_DB_HANDLE DlDbHandle;
 CSSM_DB_UNIQUE_RECORD_PTR UniqueRecord;
} CSSM_TP_APPLE_EVIDENCE_INFO;






typedef struct
{
 uint32 Version;
} CSSM_TP_APPLE_EVIDENCE_HEADER;
# 1061 "/System/Library/Frameworks/Security.framework/Headers/cssmapple.h" 3
enum
{
 CSSM_EVIDENCE_FORM_APPLE_HEADER = 0x80000000 + 0,
 CSSM_EVIDENCE_FORM_APPLE_CERTGROUP = 0x80000000 + 1,
 CSSM_EVIDENCE_FORM_APPLE_CERT_INFO = 0x80000000 + 2
};


enum {





 CSSM_APPLEX509CL_OBTAIN_CSR,







 CSSM_APPLEX509CL_VERIFY_CSR
};






typedef struct {
 CSSM_X509_NAME_PTR subjectNameX509;



 CSSM_ALGORITHMS signatureAlg;
 CSSM_OID signatureOid;

 CSSM_CSP_HANDLE cspHand;
 const CSSM_KEY *subjectPublicKey;
 const CSSM_KEY *subjectPrivateKey;




 const char *challengeString;
} CSSM_APPLE_CL_CSR_REQUEST;
# 1126 "/System/Library/Frameworks/Security.framework/Headers/cssmapple.h" 3
void cssmPerror(const char *how, CSSM_RETURN error);


_Bool cssmOidToAlg(const CSSM_OID *oid, CSSM_ALGORITHMS *alg);
const CSSM_OID *cssmAlgToOid(CSSM_ALGORITHMS algId);
# 26 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3

# 1 "/System/Library/Frameworks/Security.framework/Headers/cssm.h" 1 3
# 30 "/System/Library/Frameworks/Security.framework/Headers/cssm.h" 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/emmtype.h" 1 3
# 37 "/System/Library/Frameworks/Security.framework/Headers/emmtype.h" 3
typedef uint32 CSSM_MANAGER_EVENT_TYPES;



typedef struct cssm_manager_event_notification {
    CSSM_SERVICE_MASK DestinationModuleManagerType;
    CSSM_SERVICE_MASK SourceModuleManagerType;
    CSSM_MANAGER_EVENT_TYPES Event;
    uint32 EventId;
    CSSM_DATA EventData;
} CSSM_MANAGER_EVENT_NOTIFICATION __attribute__((deprecated)), *CSSM_MANAGER_EVENT_NOTIFICATION_PTR __attribute__((deprecated));
# 31 "/System/Library/Frameworks/Security.framework/Headers/cssm.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/cssmapi.h" 1 3
# 47 "/System/Library/Frameworks/Security.framework/Headers/cssmapi.h" 3
CSSM_RETURN
CSSM_Init (const CSSM_VERSION *Version,
           CSSM_PRIVILEGE_SCOPE Scope,
           const CSSM_GUID *CallerGuid,
           CSSM_KEY_HIERARCHY KeyHierarchy,
           CSSM_PVC_MODE *PvcPolicy,
           const void *Reserved)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_Terminate (void)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_ModuleLoad (const CSSM_GUID *ModuleGuid,
                 CSSM_KEY_HIERARCHY KeyHierarchy,
                 CSSM_API_ModuleEventHandler AppNotifyCallback,
                 void *AppNotifyCallbackCtx)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_ModuleUnload (const CSSM_GUID *ModuleGuid,
                   CSSM_API_ModuleEventHandler AppNotifyCallback,
                   void *AppNotifyCallbackCtx)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_Introduce (const CSSM_GUID *ModuleID,
                CSSM_KEY_HIERARCHY KeyHierarchy)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_Unintroduce (const CSSM_GUID *ModuleID)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_ModuleAttach (const CSSM_GUID *ModuleGuid,
                   const CSSM_VERSION *Version,
                   const CSSM_API_MEMORY_FUNCS *MemoryFuncs,
                   uint32 SubserviceID,
                   CSSM_SERVICE_TYPE SubServiceType,
                   CSSM_ATTACH_FLAGS AttachFlags,
                   CSSM_KEY_HIERARCHY KeyHierarchy,
                   CSSM_FUNC_NAME_ADDR *FunctionTable,
                   uint32 NumFunctionTable,
                   const void *Reserved,
                   CSSM_MODULE_HANDLE_PTR NewModuleHandle)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_ModuleDetach (CSSM_MODULE_HANDLE ModuleHandle)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_SetPrivilege (CSSM_PRIVILEGE Privilege)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_GetPrivilege (CSSM_PRIVILEGE *Privilege)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_GetModuleGUIDFromHandle (CSSM_MODULE_HANDLE ModuleHandle,
                              CSSM_GUID_PTR ModuleGUID)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_GetSubserviceUIDFromHandle (CSSM_MODULE_HANDLE ModuleHandle,
                                 CSSM_SUBSERVICE_UID_PTR SubserviceUID)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_ListAttachedModuleManagers (uint32 *NumberOfModuleManagers,
                                 CSSM_GUID_PTR ModuleManagerGuids)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_GetAPIMemoryFunctions (CSSM_MODULE_HANDLE AddInHandle,
                            CSSM_API_MEMORY_FUNCS_PTR AppMemoryFuncs)
  __attribute__((deprecated));
# 192 "/System/Library/Frameworks/Security.framework/Headers/cssmapi.h" 3
CSSM_RETURN
CSSM_CSP_CreateSignatureContext (CSSM_CSP_HANDLE CSPHandle,
                                 CSSM_ALGORITHMS AlgorithmID,
                                 const CSSM_ACCESS_CREDENTIALS *AccessCred,
                                 const CSSM_KEY *Key,
                                 CSSM_CC_HANDLE *NewContextHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CSP_CreateSymmetricContext (CSSM_CSP_HANDLE CSPHandle,
                                 CSSM_ALGORITHMS AlgorithmID,
                                 CSSM_ENCRYPT_MODE Mode,
                                 const CSSM_ACCESS_CREDENTIALS *AccessCred,
                                 const CSSM_KEY *Key,
                                 const CSSM_DATA *InitVector,
                                 CSSM_PADDING Padding,
                                 void *Reserved,
                                 CSSM_CC_HANDLE *NewContextHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CSP_CreateDigestContext (CSSM_CSP_HANDLE CSPHandle,
                              CSSM_ALGORITHMS AlgorithmID,
                              CSSM_CC_HANDLE *NewContextHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CSP_CreateMacContext (CSSM_CSP_HANDLE CSPHandle,
                           CSSM_ALGORITHMS AlgorithmID,
                           const CSSM_KEY *Key,
                           CSSM_CC_HANDLE *NewContextHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CSP_CreateRandomGenContext (CSSM_CSP_HANDLE CSPHandle,
                                 CSSM_ALGORITHMS AlgorithmID,
                                 const CSSM_CRYPTO_DATA *Seed,
                                 CSSM_SIZE Length,
                                 CSSM_CC_HANDLE *NewContextHandle)
  __attribute__((deprecated));







CSSM_RETURN
CSSM_CSP_CreateAsymmetricContext (CSSM_CSP_HANDLE CSPHandle,
                                  CSSM_ALGORITHMS AlgorithmID,
                                  const CSSM_ACCESS_CREDENTIALS *AccessCred,
                                  const CSSM_KEY *Key,
                                  CSSM_PADDING Padding,
                                  CSSM_CC_HANDLE *NewContextHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CSP_CreateDeriveKeyContext (CSSM_CSP_HANDLE CSPHandle,
                                 CSSM_ALGORITHMS AlgorithmID,
                                 CSSM_KEY_TYPE DeriveKeyType,
                                 uint32 DeriveKeyLengthInBits,
                                 const CSSM_ACCESS_CREDENTIALS *AccessCred,
                                 const CSSM_KEY *BaseKey,
                                 uint32 IterationCount,
                                 const CSSM_DATA *Salt,
                                 const CSSM_CRYPTO_DATA *Seed,
                                 CSSM_CC_HANDLE *NewContextHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CSP_CreateKeyGenContext (CSSM_CSP_HANDLE CSPHandle,
                              CSSM_ALGORITHMS AlgorithmID,
                              uint32 KeySizeInBits,
                              const CSSM_CRYPTO_DATA *Seed,
                              const CSSM_DATA *Salt,
                              const CSSM_DATE *StartDate,
                              const CSSM_DATE *EndDate,
                              const CSSM_DATA *Params,
                              CSSM_CC_HANDLE *NewContextHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CSP_CreatePassThroughContext (CSSM_CSP_HANDLE CSPHandle,
                                   const CSSM_KEY *Key,
                                   CSSM_CC_HANDLE *NewContextHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_GetContext (CSSM_CC_HANDLE CCHandle,
                 CSSM_CONTEXT_PTR *Context)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_FreeContext (CSSM_CONTEXT_PTR Context)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_SetContext (CSSM_CC_HANDLE CCHandle,
                 const CSSM_CONTEXT *Context)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DeleteContext (CSSM_CC_HANDLE CCHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_GetContextAttribute (const CSSM_CONTEXT *Context,
                          uint32 AttributeType,
                          CSSM_CONTEXT_ATTRIBUTE_PTR *ContextAttribute)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_UpdateContextAttributes (CSSM_CC_HANDLE CCHandle,
                              uint32 NumberOfAttributes,
                              const CSSM_CONTEXT_ATTRIBUTE *ContextAttributes)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DeleteContextAttributes (CSSM_CC_HANDLE CCHandle,
                              uint32 NumberOfAttributes,
                              const CSSM_CONTEXT_ATTRIBUTE *ContextAttributes)
  __attribute__((deprecated));
# 392 "/System/Library/Frameworks/Security.framework/Headers/cssmapi.h" 3
CSSM_RETURN
CSSM_CSP_Login (CSSM_CSP_HANDLE CSPHandle,
                const CSSM_ACCESS_CREDENTIALS *AccessCred,
                const CSSM_DATA *LoginName,
                const void *Reserved)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CSP_Logout (CSSM_CSP_HANDLE CSPHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CSP_GetLoginAcl (CSSM_CSP_HANDLE CSPHandle,
                      const CSSM_STRING *SelectionTag,
                      uint32 *NumberOfAclInfos,
                      CSSM_ACL_ENTRY_INFO_PTR *AclInfos)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CSP_ChangeLoginAcl (CSSM_CSP_HANDLE CSPHandle,
                         const CSSM_ACCESS_CREDENTIALS *AccessCred,
                         const CSSM_ACL_EDIT *AclEdit)
  __attribute__((deprecated));
# 440 "/System/Library/Frameworks/Security.framework/Headers/cssmapi.h" 3
CSSM_RETURN
CSSM_GetKeyAcl (CSSM_CSP_HANDLE CSPHandle,
                const CSSM_KEY *Key,
                const CSSM_STRING *SelectionTag,
                uint32 *NumberOfAclInfos,
                CSSM_ACL_ENTRY_INFO_PTR *AclInfos)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_ChangeKeyAcl (CSSM_CSP_HANDLE CSPHandle,
                   const CSSM_ACCESS_CREDENTIALS *AccessCred,
                   const CSSM_ACL_EDIT *AclEdit,
                   const CSSM_KEY *Key)
  __attribute__((deprecated));
# 470 "/System/Library/Frameworks/Security.framework/Headers/cssmapi.h" 3
CSSM_RETURN
CSSM_GetKeyOwner (CSSM_CSP_HANDLE CSPHandle,
                  const CSSM_KEY *Key,
                  CSSM_ACL_OWNER_PROTOTYPE_PTR Owner)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_ChangeKeyOwner (CSSM_CSP_HANDLE CSPHandle,
                     const CSSM_ACCESS_CREDENTIALS *AccessCred,
                     const CSSM_KEY *Key,
                     const CSSM_ACL_OWNER_PROTOTYPE *NewOwner)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CSP_GetLoginOwner (CSSM_CSP_HANDLE CSPHandle,
                        CSSM_ACL_OWNER_PROTOTYPE_PTR Owner)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CSP_ChangeLoginOwner (CSSM_CSP_HANDLE CSPHandle,
                           const CSSM_ACCESS_CREDENTIALS *AccessCred,
                           const CSSM_ACL_OWNER_PROTOTYPE *NewOwner)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_SignData (CSSM_CC_HANDLE CCHandle,
               const CSSM_DATA *DataBufs,
               uint32 DataBufCount,
               CSSM_ALGORITHMS DigestAlgorithm,
               CSSM_DATA_PTR Signature)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_SignDataInit (CSSM_CC_HANDLE CCHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_SignDataUpdate (CSSM_CC_HANDLE CCHandle,
                     const CSSM_DATA *DataBufs,
                     uint32 DataBufCount)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_SignDataFinal (CSSM_CC_HANDLE CCHandle,
                    CSSM_DATA_PTR Signature)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_VerifyData (CSSM_CC_HANDLE CCHandle,
                 const CSSM_DATA *DataBufs,
                 uint32 DataBufCount,
                 CSSM_ALGORITHMS DigestAlgorithm,
                 const CSSM_DATA *Signature)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_VerifyDataInit (CSSM_CC_HANDLE CCHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_VerifyDataUpdate (CSSM_CC_HANDLE CCHandle,
                       const CSSM_DATA *DataBufs,
                       uint32 DataBufCount)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_VerifyDataFinal (CSSM_CC_HANDLE CCHandle,
                      const CSSM_DATA *Signature)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DigestData (CSSM_CC_HANDLE CCHandle,
                 const CSSM_DATA *DataBufs,
                 uint32 DataBufCount,
                 CSSM_DATA_PTR Digest)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DigestDataInit (CSSM_CC_HANDLE CCHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DigestDataUpdate (CSSM_CC_HANDLE CCHandle,
                       const CSSM_DATA *DataBufs,
                       uint32 DataBufCount)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DigestDataClone (CSSM_CC_HANDLE CCHandle,
                      CSSM_CC_HANDLE *ClonednewCCHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DigestDataFinal (CSSM_CC_HANDLE CCHandle,
                      CSSM_DATA_PTR Digest)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_GenerateMac (CSSM_CC_HANDLE CCHandle,
                  const CSSM_DATA *DataBufs,
                  uint32 DataBufCount,
                  CSSM_DATA_PTR Mac)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_GenerateMacInit (CSSM_CC_HANDLE CCHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_GenerateMacUpdate (CSSM_CC_HANDLE CCHandle,
                        const CSSM_DATA *DataBufs,
                        uint32 DataBufCount)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_GenerateMacFinal (CSSM_CC_HANDLE CCHandle,
                       CSSM_DATA_PTR Mac)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_VerifyMac (CSSM_CC_HANDLE CCHandle,
                const CSSM_DATA *DataBufs,
                uint32 DataBufCount,
                const CSSM_DATA *Mac)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_VerifyMacInit (CSSM_CC_HANDLE CCHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_VerifyMacUpdate (CSSM_CC_HANDLE CCHandle,
                      const CSSM_DATA *DataBufs,
                      uint32 DataBufCount)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_VerifyMacFinal (CSSM_CC_HANDLE CCHandle,
                     const CSSM_DATA *Mac)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_QuerySize (CSSM_CC_HANDLE CCHandle,
                CSSM_BOOL Encrypt,
                uint32 QuerySizeCount,
                CSSM_QUERY_SIZE_DATA_PTR DataBlockSizes)
  __attribute__((deprecated));







CSSM_RETURN
CSSM_EncryptData (CSSM_CC_HANDLE CCHandle,
                  const CSSM_DATA *ClearBufs,
                  uint32 ClearBufCount,
                  CSSM_DATA_PTR CipherBufs,
                  uint32 CipherBufCount,
                  CSSM_SIZE *bytesEncrypted,
                  CSSM_DATA_PTR RemData)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_EncryptDataP (CSSM_CC_HANDLE CCHandle,
                   const CSSM_DATA *ClearBufs,
                   uint32 ClearBufCount,
                   CSSM_DATA_PTR CipherBufs,
                   uint32 CipherBufCount,
                   CSSM_SIZE *bytesEncrypted,
                   CSSM_DATA_PTR RemData,
                   CSSM_PRIVILEGE Privilege)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_EncryptDataInit (CSSM_CC_HANDLE CCHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_EncryptDataInitP (CSSM_CC_HANDLE CCHandle,
                       CSSM_PRIVILEGE Privilege)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_EncryptDataUpdate (CSSM_CC_HANDLE CCHandle,
                        const CSSM_DATA *ClearBufs,
                        uint32 ClearBufCount,
                        CSSM_DATA_PTR CipherBufs,
                        uint32 CipherBufCount,
                        CSSM_SIZE *bytesEncrypted)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_EncryptDataFinal (CSSM_CC_HANDLE CCHandle,
                       CSSM_DATA_PTR RemData)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DecryptData (CSSM_CC_HANDLE CCHandle,
                  const CSSM_DATA *CipherBufs,
                  uint32 CipherBufCount,
                  CSSM_DATA_PTR ClearBufs,
                  uint32 ClearBufCount,
                  CSSM_SIZE *bytesDecrypted,
                  CSSM_DATA_PTR RemData)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DecryptDataP (CSSM_CC_HANDLE CCHandle,
                   const CSSM_DATA *CipherBufs,
                   uint32 CipherBufCount,
                   CSSM_DATA_PTR ClearBufs,
                   uint32 ClearBufCount,
                   CSSM_SIZE *bytesDecrypted,
                   CSSM_DATA_PTR RemData,
                   CSSM_PRIVILEGE Privilege)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DecryptDataInit (CSSM_CC_HANDLE CCHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DecryptDataInitP (CSSM_CC_HANDLE CCHandle,
                       CSSM_PRIVILEGE Privilege)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DecryptDataUpdate (CSSM_CC_HANDLE CCHandle,
                        const CSSM_DATA *CipherBufs,
                        uint32 CipherBufCount,
                        CSSM_DATA_PTR ClearBufs,
                        uint32 ClearBufCount,
                        CSSM_SIZE *bytesDecrypted)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DecryptDataFinal (CSSM_CC_HANDLE CCHandle,
                       CSSM_DATA_PTR RemData)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_QueryKeySizeInBits (CSSM_CSP_HANDLE CSPHandle,
                         CSSM_CC_HANDLE CCHandle,
                         const CSSM_KEY *Key,
                         CSSM_KEY_SIZE_PTR KeySize)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_GenerateKey (CSSM_CC_HANDLE CCHandle,
                  uint32 KeyUsage,
                  uint32 KeyAttr,
                  const CSSM_DATA *KeyLabel,
                  const CSSM_RESOURCE_CONTROL_CONTEXT *CredAndAclEntry,
                  CSSM_KEY_PTR Key)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_GenerateKeyP (CSSM_CC_HANDLE CCHandle,
                   uint32 KeyUsage,
                   uint32 KeyAttr,
                   const CSSM_DATA *KeyLabel,
                   const CSSM_RESOURCE_CONTROL_CONTEXT *CredAndAclEntry,
                   CSSM_KEY_PTR Key,
                   CSSM_PRIVILEGE Privilege)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_GenerateKeyPair (CSSM_CC_HANDLE CCHandle,
                      uint32 PublicKeyUsage,
                      uint32 PublicKeyAttr,
                      const CSSM_DATA *PublicKeyLabel,
                      CSSM_KEY_PTR PublicKey,
                      uint32 PrivateKeyUsage,
                      uint32 PrivateKeyAttr,
                      const CSSM_DATA *PrivateKeyLabel,
                      const CSSM_RESOURCE_CONTROL_CONTEXT *CredAndAclEntry,
                      CSSM_KEY_PTR PrivateKey)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_GenerateKeyPairP (CSSM_CC_HANDLE CCHandle,
                       uint32 PublicKeyUsage,
                       uint32 PublicKeyAttr,
                       const CSSM_DATA *PublicKeyLabel,
                       CSSM_KEY_PTR PublicKey,
                       uint32 PrivateKeyUsage,
                       uint32 PrivateKeyAttr,
                       const CSSM_DATA *PrivateKeyLabel,
                       const CSSM_RESOURCE_CONTROL_CONTEXT *CredAndAclEntry,
                       CSSM_KEY_PTR PrivateKey,
                       CSSM_PRIVILEGE Privilege)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_GenerateRandom (CSSM_CC_HANDLE CCHandle,
                     CSSM_DATA_PTR RandomNumber)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CSP_ObtainPrivateKeyFromPublicKey (CSSM_CSP_HANDLE CSPHandle,
                                        const CSSM_KEY *PublicKey,
                                        CSSM_KEY_PTR PrivateKey)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_WrapKey (CSSM_CC_HANDLE CCHandle,
              const CSSM_ACCESS_CREDENTIALS *AccessCred,
              const CSSM_KEY *Key,
              const CSSM_DATA *DescriptiveData,
              CSSM_WRAP_KEY_PTR WrappedKey)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_UnwrapKey (CSSM_CC_HANDLE CCHandle,
                const CSSM_KEY *PublicKey,
                const CSSM_WRAP_KEY *WrappedKey,
                uint32 KeyUsage,
                uint32 KeyAttr,
                const CSSM_DATA *KeyLabel,
                const CSSM_RESOURCE_CONTROL_CONTEXT *CredAndAclEntry,
                CSSM_KEY_PTR UnwrappedKey,
                CSSM_DATA_PTR DescriptiveData)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_WrapKeyP (CSSM_CC_HANDLE CCHandle,
               const CSSM_ACCESS_CREDENTIALS *AccessCred,
               const CSSM_KEY *Key,
               const CSSM_DATA *DescriptiveData,
               CSSM_WRAP_KEY_PTR WrappedKey,
               CSSM_PRIVILEGE Privilege)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_UnwrapKeyP (CSSM_CC_HANDLE CCHandle,
                 const CSSM_KEY *PublicKey,
                 const CSSM_WRAP_KEY *WrappedKey,
                 uint32 KeyUsage,
                 uint32 KeyAttr,
                 const CSSM_DATA *KeyLabel,
                 const CSSM_RESOURCE_CONTROL_CONTEXT *CredAndAclEntry,
                 CSSM_KEY_PTR UnwrappedKey,
                 CSSM_DATA_PTR DescriptiveData,
                 CSSM_PRIVILEGE Privilege)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_DeriveKey (CSSM_CC_HANDLE CCHandle,
                CSSM_DATA_PTR Param,
                uint32 KeyUsage,
                uint32 KeyAttr,
                const CSSM_DATA *KeyLabel,
                const CSSM_RESOURCE_CONTROL_CONTEXT *CredAndAclEntry,
                CSSM_KEY_PTR DerivedKey)
  __attribute__((deprecated));







CSSM_RETURN
CSSM_FreeKey (CSSM_CSP_HANDLE CSPHandle,
              const CSSM_ACCESS_CREDENTIALS *AccessCred,
              CSSM_KEY_PTR KeyPtr,
              CSSM_BOOL Delete)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_GenerateAlgorithmParams (CSSM_CC_HANDLE CCHandle,
                              uint32 ParamBits,
                              CSSM_DATA_PTR Param)
  __attribute__((deprecated));
# 1089 "/System/Library/Frameworks/Security.framework/Headers/cssmapi.h" 3
CSSM_RETURN
CSSM_CSP_GetOperationalStatistics (CSSM_CSP_HANDLE CSPHandle,
                                   CSSM_CSP_OPERATIONAL_STATISTICS *Statistics)
  __attribute__((deprecated));







CSSM_RETURN
CSSM_GetTimeValue (CSSM_CSP_HANDLE CSPHandle,
                   CSSM_ALGORITHMS TimeAlgorithm,
                   CSSM_DATA *TimeData)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_RetrieveUniqueId (CSSM_CSP_HANDLE CSPHandle,
                       CSSM_DATA_PTR UniqueID)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_RetrieveCounter (CSSM_CSP_HANDLE CSPHandle,
                      CSSM_DATA_PTR Counter)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_VerifyDevice (CSSM_CSP_HANDLE CSPHandle,
                   const CSSM_DATA *DeviceCert)
  __attribute__((deprecated));
# 1144 "/System/Library/Frameworks/Security.framework/Headers/cssmapi.h" 3
CSSM_RETURN
CSSM_CSP_PassThrough (CSSM_CC_HANDLE CCHandle,
                      uint32 PassThroughId,
                      const void *InData,
                      void **OutData)
  __attribute__((deprecated));
# 1158 "/System/Library/Frameworks/Security.framework/Headers/cssmapi.h" 3
CSSM_RETURN
CSSM_TP_SubmitCredRequest (CSSM_TP_HANDLE TPHandle,
                           const CSSM_TP_AUTHORITY_ID *PreferredAuthority,
                           CSSM_TP_AUTHORITY_REQUEST_TYPE RequestType,
                           const CSSM_TP_REQUEST_SET *RequestInput,
                           const CSSM_TP_CALLERAUTH_CONTEXT *CallerAuthContext,
                           sint32 *EstimatedTime,
                           CSSM_DATA_PTR ReferenceIdentifier)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_RetrieveCredResult (CSSM_TP_HANDLE TPHandle,
                            const CSSM_DATA *ReferenceIdentifier,
                            const CSSM_TP_CALLERAUTH_CONTEXT *CallerAuthCredentials,
                            sint32 *EstimatedTime,
                            CSSM_BOOL *ConfirmationRequired,
                            CSSM_TP_RESULT_SET_PTR *RetrieveOutput)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_ConfirmCredResult (CSSM_TP_HANDLE TPHandle,
                           const CSSM_DATA *ReferenceIdentifier,
                           const CSSM_TP_CALLERAUTH_CONTEXT *CallerAuthCredentials,
                           const CSSM_TP_CONFIRM_RESPONSE *Responses,
                           const CSSM_TP_AUTHORITY_ID *PreferredAuthority)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_ReceiveConfirmation (CSSM_TP_HANDLE TPHandle,
                             const CSSM_DATA *ReferenceIdentifier,
                             CSSM_TP_CONFIRM_RESPONSE_PTR *Responses,
                             sint32 *ElapsedTime)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_CertReclaimKey (CSSM_TP_HANDLE TPHandle,
                        const CSSM_CERTGROUP *CertGroup,
                        uint32 CertIndex,
                        CSSM_LONG_HANDLE KeyCacheHandle,
                        CSSM_CSP_HANDLE CSPHandle,
                        const CSSM_RESOURCE_CONTROL_CONTEXT *CredAndAclEntry)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_CertReclaimAbort (CSSM_TP_HANDLE TPHandle,
                          CSSM_LONG_HANDLE KeyCacheHandle)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_FormRequest (CSSM_TP_HANDLE TPHandle,
                     const CSSM_TP_AUTHORITY_ID *PreferredAuthority,
                     CSSM_TP_FORM_TYPE FormType,
                     CSSM_DATA_PTR BlankForm)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_FormSubmit (CSSM_TP_HANDLE TPHandle,
                    CSSM_TP_FORM_TYPE FormType,
                    const CSSM_DATA *Form,
                    const CSSM_TP_AUTHORITY_ID *ClearanceAuthority,
                    const CSSM_TP_AUTHORITY_ID *RepresentedAuthority,
                    CSSM_ACCESS_CREDENTIALS_PTR Credentials)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_CertGroupVerify (CSSM_TP_HANDLE TPHandle,
                         CSSM_CL_HANDLE CLHandle,
                         CSSM_CSP_HANDLE CSPHandle,
                         const CSSM_CERTGROUP *CertGroupToBeVerified,
                         const CSSM_TP_VERIFY_CONTEXT *VerifyContext,
                         CSSM_TP_VERIFY_CONTEXT_RESULT_PTR VerifyContextResult)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_CertCreateTemplate (CSSM_TP_HANDLE TPHandle,
                            CSSM_CL_HANDLE CLHandle,
                            uint32 NumberOfFields,
                            const CSSM_FIELD *CertFields,
                            CSSM_DATA_PTR CertTemplate)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_CertGetAllTemplateFields (CSSM_TP_HANDLE TPHandle,
                                  CSSM_CL_HANDLE CLHandle,
                                  const CSSM_DATA *CertTemplate,
                                  uint32 *NumberOfFields,
                                  CSSM_FIELD_PTR *CertFields)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_CertSign (CSSM_TP_HANDLE TPHandle,
                  CSSM_CL_HANDLE CLHandle,
                  CSSM_CC_HANDLE CCHandle,
                  const CSSM_DATA *CertTemplateToBeSigned,
                  const CSSM_CERTGROUP *SignerCertGroup,
                  const CSSM_TP_VERIFY_CONTEXT *SignerVerifyContext,
                  CSSM_TP_VERIFY_CONTEXT_RESULT_PTR SignerVerifyResult,
                  CSSM_DATA_PTR SignedCert)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_CrlVerify (CSSM_TP_HANDLE TPHandle,
                   CSSM_CL_HANDLE CLHandle,
                   CSSM_CSP_HANDLE CSPHandle,
                   const CSSM_ENCODED_CRL *CrlToBeVerified,
                   const CSSM_CERTGROUP *SignerCertGroup,
                   const CSSM_TP_VERIFY_CONTEXT *VerifyContext,
                   CSSM_TP_VERIFY_CONTEXT_RESULT_PTR RevokerVerifyResult)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_CrlCreateTemplate (CSSM_TP_HANDLE TPHandle,
                           CSSM_CL_HANDLE CLHandle,
                           uint32 NumberOfFields,
                           const CSSM_FIELD *CrlFields,
                           CSSM_DATA_PTR NewCrlTemplate)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_CertRevoke (CSSM_TP_HANDLE TPHandle,
                    CSSM_CL_HANDLE CLHandle,
                    CSSM_CSP_HANDLE CSPHandle,
                    const CSSM_DATA *OldCrlTemplate,
                    const CSSM_CERTGROUP *CertGroupToBeRevoked,
                    const CSSM_CERTGROUP *RevokerCertGroup,
                    const CSSM_TP_VERIFY_CONTEXT *RevokerVerifyContext,
                    CSSM_TP_VERIFY_CONTEXT_RESULT_PTR RevokerVerifyResult,
                    CSSM_TP_CERTCHANGE_REASON Reason,
                    CSSM_DATA_PTR NewCrlTemplate)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_CertRemoveFromCrlTemplate (CSSM_TP_HANDLE TPHandle,
                                   CSSM_CL_HANDLE CLHandle,
                                   CSSM_CSP_HANDLE CSPHandle,
                                   const CSSM_DATA *OldCrlTemplate,
                                   const CSSM_CERTGROUP *CertGroupToBeRemoved,
                                   const CSSM_CERTGROUP *RevokerCertGroup,
                                   const CSSM_TP_VERIFY_CONTEXT *RevokerVerifyContext,
                                   CSSM_TP_VERIFY_CONTEXT_RESULT_PTR RevokerVerifyResult,
                                   CSSM_DATA_PTR NewCrlTemplate)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_CrlSign (CSSM_TP_HANDLE TPHandle,
                 CSSM_CL_HANDLE CLHandle,
                 CSSM_CC_HANDLE CCHandle,
                 const CSSM_ENCODED_CRL *CrlToBeSigned,
                 const CSSM_CERTGROUP *SignerCertGroup,
                 const CSSM_TP_VERIFY_CONTEXT *SignerVerifyContext,
                 CSSM_TP_VERIFY_CONTEXT_RESULT_PTR SignerVerifyResult,
                 CSSM_DATA_PTR SignedCrl)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_ApplyCrlToDb (CSSM_TP_HANDLE TPHandle,
                      CSSM_CL_HANDLE CLHandle,
                      CSSM_CSP_HANDLE CSPHandle,
                      const CSSM_ENCODED_CRL *CrlToBeApplied,
                      const CSSM_CERTGROUP *SignerCertGroup,
                      const CSSM_TP_VERIFY_CONTEXT *ApplyCrlVerifyContext,
                      CSSM_TP_VERIFY_CONTEXT_RESULT_PTR ApplyCrlVerifyResult)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_CertGroupConstruct (CSSM_TP_HANDLE TPHandle,
                            CSSM_CL_HANDLE CLHandle,
                            CSSM_CSP_HANDLE CSPHandle,
                            const CSSM_DL_DB_LIST *DBList,
                            const void *ConstructParams,
                            const CSSM_CERTGROUP *CertGroupFrag,
                            CSSM_CERTGROUP_PTR *CertGroup)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_CertGroupPrune (CSSM_TP_HANDLE TPHandle,
                        CSSM_CL_HANDLE CLHandle,
                        const CSSM_DL_DB_LIST *DBList,
                        const CSSM_CERTGROUP *OrderedCertGroup,
                        CSSM_CERTGROUP_PTR *PrunedCertGroup)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_CertGroupToTupleGroup (CSSM_TP_HANDLE TPHandle,
                               CSSM_CL_HANDLE CLHandle,
                               const CSSM_CERTGROUP *CertGroup,
                               CSSM_TUPLEGROUP_PTR *TupleGroup)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_TP_TupleGroupToCertGroup (CSSM_TP_HANDLE TPHandle,
                               CSSM_CL_HANDLE CLHandle,
                               const CSSM_TUPLEGROUP *TupleGroup,
                               CSSM_CERTGROUP_PTR *CertTemplates)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_TP_PassThrough (CSSM_TP_HANDLE TPHandle,
                     CSSM_CL_HANDLE CLHandle,
                     CSSM_CC_HANDLE CCHandle,
                     const CSSM_DL_DB_LIST *DBList,
                     uint32 PassThroughId,
                     const void *InputParams,
                     void **OutputParams)
  __attribute__((deprecated));
# 1460 "/System/Library/Frameworks/Security.framework/Headers/cssmapi.h" 3
CSSM_RETURN
CSSM_AC_AuthCompute (CSSM_AC_HANDLE ACHandle,
                     const CSSM_TUPLEGROUP *BaseAuthorizations,
                     const CSSM_TUPLEGROUP *Credentials,
                     uint32 NumberOfRequestors,
                     const CSSM_LIST *Requestors,
                     const CSSM_LIST *RequestedAuthorizationPeriod,
                     const CSSM_LIST *RequestedAuthorization,
                     CSSM_TUPLEGROUP_PTR AuthorizationResult)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_AC_PassThrough (CSSM_AC_HANDLE ACHandle,
                     CSSM_TP_HANDLE TPHandle,
                     CSSM_CL_HANDLE CLHandle,
                     CSSM_CC_HANDLE CCHandle,
                     const CSSM_DL_DB_LIST *DBList,
                     uint32 PassThroughId,
                     const void *InputParams,
                     void **OutputParams)
  __attribute__((deprecated));
# 1493 "/System/Library/Frameworks/Security.framework/Headers/cssmapi.h" 3
CSSM_RETURN
CSSM_CL_CertCreateTemplate (CSSM_CL_HANDLE CLHandle,
                            uint32 NumberOfFields,
                            const CSSM_FIELD *CertFields,
                            CSSM_DATA_PTR CertTemplate)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CertGetAllTemplateFields (CSSM_CL_HANDLE CLHandle,
                                  const CSSM_DATA *CertTemplate,
                                  uint32 *NumberOfFields,
                                  CSSM_FIELD_PTR *CertFields)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CertSign (CSSM_CL_HANDLE CLHandle,
                  CSSM_CC_HANDLE CCHandle,
                  const CSSM_DATA *CertTemplate,
                  const CSSM_FIELD *SignScope,
                  uint32 ScopeSize,
                  CSSM_DATA_PTR SignedCert)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CertVerify (CSSM_CL_HANDLE CLHandle,
                    CSSM_CC_HANDLE CCHandle,
                    const CSSM_DATA *CertToBeVerified,
                    const CSSM_DATA *SignerCert,
                    const CSSM_FIELD *VerifyScope,
                    uint32 ScopeSize)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CertVerifyWithKey (CSSM_CL_HANDLE CLHandle,
                           CSSM_CC_HANDLE CCHandle,
                           const CSSM_DATA *CertToBeVerified)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CertGetFirstFieldValue (CSSM_CL_HANDLE CLHandle,
                                const CSSM_DATA *Cert,
                                const CSSM_OID *CertField,
                                CSSM_HANDLE_PTR ResultsHandle,
                                uint32 *NumberOfMatchedFields,
                                CSSM_DATA_PTR *Value)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CertGetNextFieldValue (CSSM_CL_HANDLE CLHandle,
                               CSSM_HANDLE ResultsHandle,
                               CSSM_DATA_PTR *Value)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CL_CertAbortQuery (CSSM_CL_HANDLE CLHandle,
                        CSSM_HANDLE ResultsHandle)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CertGetKeyInfo (CSSM_CL_HANDLE CLHandle,
                        const CSSM_DATA *Cert,
                        CSSM_KEY_PTR *Key)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CertGetAllFields (CSSM_CL_HANDLE CLHandle,
                          const CSSM_DATA *Cert,
                          uint32 *NumberOfFields,
                          CSSM_FIELD_PTR *CertFields)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CL_FreeFields (CSSM_CL_HANDLE CLHandle,
                    uint32 NumberOfFields,
                    CSSM_FIELD_PTR *Fields)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CL_FreeFieldValue (CSSM_CL_HANDLE CLHandle,
                        const CSSM_OID *CertOrCrlOid,
                        CSSM_DATA_PTR Value)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CL_CertCache (CSSM_CL_HANDLE CLHandle,
                   const CSSM_DATA *Cert,
                   CSSM_HANDLE_PTR CertHandle)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CertGetFirstCachedFieldValue (CSSM_CL_HANDLE CLHandle,
                                      CSSM_HANDLE CertHandle,
                                      const CSSM_OID *CertField,
                                      CSSM_HANDLE_PTR ResultsHandle,
                                      uint32 *NumberOfMatchedFields,
                                      CSSM_DATA_PTR *Value)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CertGetNextCachedFieldValue (CSSM_CL_HANDLE CLHandle,
                                     CSSM_HANDLE ResultsHandle,
                                     CSSM_DATA_PTR *Value)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CL_CertAbortCache (CSSM_CL_HANDLE CLHandle,
                        CSSM_HANDLE CertHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CL_CertGroupToSignedBundle (CSSM_CL_HANDLE CLHandle,
                                 CSSM_CC_HANDLE CCHandle,
                                 const CSSM_CERTGROUP *CertGroupToBundle,
                                 const CSSM_CERT_BUNDLE_HEADER *BundleInfo,
                                 CSSM_DATA_PTR SignedBundle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CL_CertGroupFromVerifiedBundle (CSSM_CL_HANDLE CLHandle,
                                     CSSM_CC_HANDLE CCHandle,
                                     const CSSM_CERT_BUNDLE *CertBundle,
                                     const CSSM_DATA *SignerCert,
                                     CSSM_CERTGROUP_PTR *CertGroup)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CL_CertDescribeFormat (CSSM_CL_HANDLE CLHandle,
                            uint32 *NumberOfFields,
                            CSSM_OID_PTR *OidList)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CL_CrlCreateTemplate (CSSM_CL_HANDLE CLHandle,
                           uint32 NumberOfFields,
                           const CSSM_FIELD *CrlTemplate,
                           CSSM_DATA_PTR NewCrl)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CL_CrlSetFields (CSSM_CL_HANDLE CLHandle,
                      uint32 NumberOfFields,
                      const CSSM_FIELD *CrlTemplate,
                      const CSSM_DATA *OldCrl,
                      CSSM_DATA_PTR ModifiedCrl)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CrlAddCert (CSSM_CL_HANDLE CLHandle,
                    CSSM_CC_HANDLE CCHandle,
                    const CSSM_DATA *Cert,
                    uint32 NumberOfFields,
                    const CSSM_FIELD *CrlEntryFields,
                    const CSSM_DATA *OldCrl,
                    CSSM_DATA_PTR NewCrl)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CrlRemoveCert (CSSM_CL_HANDLE CLHandle,
                       const CSSM_DATA *Cert,
                       const CSSM_DATA *OldCrl,
                       CSSM_DATA_PTR NewCrl)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CrlSign (CSSM_CL_HANDLE CLHandle,
                 CSSM_CC_HANDLE CCHandle,
                 const CSSM_DATA *UnsignedCrl,
                 const CSSM_FIELD *SignScope,
                 uint32 ScopeSize,
                 CSSM_DATA_PTR SignedCrl)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CrlVerify (CSSM_CL_HANDLE CLHandle,
                   CSSM_CC_HANDLE CCHandle,
                   const CSSM_DATA *CrlToBeVerified,
                   const CSSM_DATA *SignerCert,
                   const CSSM_FIELD *VerifyScope,
                   uint32 ScopeSize)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CrlVerifyWithKey (CSSM_CL_HANDLE CLHandle,
                          CSSM_CC_HANDLE CCHandle,
                          const CSSM_DATA *CrlToBeVerified)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CL_IsCertInCrl (CSSM_CL_HANDLE CLHandle,
                     const CSSM_DATA *Cert,
                     const CSSM_DATA *Crl,
                     CSSM_BOOL *CertFound)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CrlGetFirstFieldValue (CSSM_CL_HANDLE CLHandle,
                               const CSSM_DATA *Crl,
                               const CSSM_OID *CrlField,
                               CSSM_HANDLE_PTR ResultsHandle,
                               uint32 *NumberOfMatchedFields,
                               CSSM_DATA_PTR *Value)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CrlGetNextFieldValue (CSSM_CL_HANDLE CLHandle,
                              CSSM_HANDLE ResultsHandle,
                              CSSM_DATA_PTR *Value)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CL_CrlAbortQuery (CSSM_CL_HANDLE CLHandle,
                       CSSM_HANDLE ResultsHandle)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CrlGetAllFields (CSSM_CL_HANDLE CLHandle,
                         const CSSM_DATA *Crl,
                         uint32 *NumberOfCrlFields,
                         CSSM_FIELD_PTR *CrlFields)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CL_CrlCache (CSSM_CL_HANDLE CLHandle,
                  const CSSM_DATA *Crl,
                  CSSM_HANDLE_PTR CrlHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CL_IsCertInCachedCrl (CSSM_CL_HANDLE CLHandle,
                           const CSSM_DATA *Cert,
                           CSSM_HANDLE CrlHandle,
                           CSSM_BOOL *CertFound,
                           CSSM_DATA_PTR CrlRecordIndex)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CrlGetFirstCachedFieldValue (CSSM_CL_HANDLE CLHandle,
                                     CSSM_HANDLE CrlHandle,
                                     const CSSM_DATA *CrlRecordIndex,
                                     const CSSM_OID *CrlField,
                                     CSSM_HANDLE_PTR ResultsHandle,
                                     uint32 *NumberOfMatchedFields,
                                     CSSM_DATA_PTR *Value)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CrlGetNextCachedFieldValue (CSSM_CL_HANDLE CLHandle,
                                    CSSM_HANDLE ResultsHandle,
                                    CSSM_DATA_PTR *Value)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_CL_CrlGetAllCachedRecordFields (CSSM_CL_HANDLE CLHandle,
                                     CSSM_HANDLE CrlHandle,
                                     const CSSM_DATA *CrlRecordIndex,
                                     uint32 *NumberOfFields,
                                     CSSM_FIELD_PTR *CrlFields)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CL_CrlAbortCache (CSSM_CL_HANDLE CLHandle,
                       CSSM_HANDLE CrlHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CL_CrlDescribeFormat (CSSM_CL_HANDLE CLHandle,
                           uint32 *NumberOfFields,
                           CSSM_OID_PTR *OidList)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_CL_PassThrough (CSSM_CL_HANDLE CLHandle,
                     CSSM_CC_HANDLE CCHandle,
                     uint32 PassThroughId,
                     const void *InputParams,
                     void **OutputParams)
  __attribute__((deprecated));
# 1947 "/System/Library/Frameworks/Security.framework/Headers/cssmapi.h" 3
CSSM_RETURN
CSSM_DL_DbOpen (CSSM_DL_HANDLE DLHandle,
                const char *DbName,
                const CSSM_NET_ADDRESS *DbLocation,
                CSSM_DB_ACCESS_TYPE AccessRequest,
                const CSSM_ACCESS_CREDENTIALS *AccessCred,
                const void *OpenParameters,
                CSSM_DB_HANDLE *DbHandle)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_DL_DbClose (CSSM_DL_DB_HANDLE DLDBHandle)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_DL_DbCreate (CSSM_DL_HANDLE DLHandle,
                  const char *DbName,
                  const CSSM_NET_ADDRESS *DbLocation,
                  const CSSM_DBINFO *DBInfo,
                  CSSM_DB_ACCESS_TYPE AccessRequest,
                  const CSSM_RESOURCE_CONTROL_CONTEXT *CredAndAclEntry,
                  const void *OpenParameters,
                  CSSM_DB_HANDLE *DbHandle)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_DL_DbDelete (CSSM_DL_HANDLE DLHandle,
                  const char *DbName,
                  const CSSM_NET_ADDRESS *DbLocation,
                  const CSSM_ACCESS_CREDENTIALS *AccessCred)
    __attribute__((deprecated));






CSSM_RETURN
CSSM_DL_CreateRelation (CSSM_DL_DB_HANDLE DLDBHandle,
                        CSSM_DB_RECORDTYPE RelationID,
                        const char *RelationName,
                        uint32 NumberOfAttributes,
                        const CSSM_DB_SCHEMA_ATTRIBUTE_INFO *pAttributeInfo,
                        uint32 NumberOfIndexes,
                        const CSSM_DB_SCHEMA_INDEX_INFO *pIndexInfo)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DL_DestroyRelation (CSSM_DL_DB_HANDLE DLDBHandle,
                         CSSM_DB_RECORDTYPE RelationID)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_DL_Authenticate (CSSM_DL_DB_HANDLE DLDBHandle,
                      CSSM_DB_ACCESS_TYPE AccessRequest,
                      const CSSM_ACCESS_CREDENTIALS *AccessCred)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DL_GetDbAcl (CSSM_DL_DB_HANDLE DLDBHandle,
                  const CSSM_STRING *SelectionTag,
                  uint32 *NumberOfAclInfos,
                  CSSM_ACL_ENTRY_INFO_PTR *AclInfos)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DL_ChangeDbAcl (CSSM_DL_DB_HANDLE DLDBHandle,
                     const CSSM_ACCESS_CREDENTIALS *AccessCred,
                     const CSSM_ACL_EDIT *AclEdit)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DL_GetDbOwner (CSSM_DL_DB_HANDLE DLDBHandle,
                    CSSM_ACL_OWNER_PROTOTYPE_PTR Owner)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DL_ChangeDbOwner (CSSM_DL_DB_HANDLE DLDBHandle,
                       const CSSM_ACCESS_CREDENTIALS *AccessCred,
                       const CSSM_ACL_OWNER_PROTOTYPE *NewOwner)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DL_GetDbNames (CSSM_DL_HANDLE DLHandle,
                    CSSM_NAME_LIST_PTR *NameList)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DL_GetDbNameFromHandle (CSSM_DL_DB_HANDLE DLDBHandle,
                             char **DbName)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DL_FreeNameList (CSSM_DL_HANDLE DLHandle,
                      CSSM_NAME_LIST_PTR NameList)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DL_DataInsert (CSSM_DL_DB_HANDLE DLDBHandle,
                    CSSM_DB_RECORDTYPE RecordType,
                    const CSSM_DB_RECORD_ATTRIBUTE_DATA *Attributes,
                    const CSSM_DATA *Data,
                    CSSM_DB_UNIQUE_RECORD_PTR *UniqueId)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_DL_DataDelete (CSSM_DL_DB_HANDLE DLDBHandle,
                    const CSSM_DB_UNIQUE_RECORD *UniqueRecordIdentifier)
  __attribute__((deprecated));





CSSM_RETURN
CSSM_DL_DataModify (CSSM_DL_DB_HANDLE DLDBHandle,
                    CSSM_DB_RECORDTYPE RecordType,
                    CSSM_DB_UNIQUE_RECORD_PTR UniqueRecordIdentifier,
                    const CSSM_DB_RECORD_ATTRIBUTE_DATA *AttributesToBeModified,
                    const CSSM_DATA *DataToBeModified,
                    CSSM_DB_MODIFY_MODE ModifyMode)
  __attribute__((deprecated));







CSSM_RETURN
CSSM_DL_DataGetFirst (CSSM_DL_DB_HANDLE DLDBHandle,
                      const CSSM_QUERY *Query,
                      CSSM_HANDLE_PTR ResultsHandle,
                      CSSM_DB_RECORD_ATTRIBUTE_DATA_PTR Attributes,
                      CSSM_DATA_PTR Data,
                      CSSM_DB_UNIQUE_RECORD_PTR *UniqueId)
  __attribute__((deprecated));







CSSM_RETURN
CSSM_DL_DataGetNext (CSSM_DL_DB_HANDLE DLDBHandle,
                     CSSM_HANDLE ResultsHandle,
                     CSSM_DB_RECORD_ATTRIBUTE_DATA_PTR Attributes,
                     CSSM_DATA_PTR Data,
                     CSSM_DB_UNIQUE_RECORD_PTR *UniqueId)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DL_DataAbortQuery (CSSM_DL_DB_HANDLE DLDBHandle,
                        CSSM_HANDLE ResultsHandle)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DL_DataGetFromUniqueRecordId (CSSM_DL_DB_HANDLE DLDBHandle,
                              const CSSM_DB_UNIQUE_RECORD *UniqueRecord,
                              CSSM_DB_RECORD_ATTRIBUTE_DATA_PTR Attributes,
                              CSSM_DATA_PTR Data)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DL_FreeUniqueRecord (CSSM_DL_DB_HANDLE DLDBHandle,
                          CSSM_DB_UNIQUE_RECORD_PTR UniqueRecord)
  __attribute__((deprecated));






CSSM_RETURN
CSSM_DL_PassThrough (CSSM_DL_DB_HANDLE DLDBHandle,
                uint32 PassThroughId,
                const void *InputParams,
                void **OutputParams)
  __attribute__((deprecated));
# 32 "/System/Library/Frameworks/Security.framework/Headers/cssm.h" 2 3
# 28 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/cssmaci.h" 1 3
# 35 "/System/Library/Frameworks/Security.framework/Headers/cssmaci.h" 3
typedef struct cssm_spi_ac_funcs {
    CSSM_RETURN ( *AuthCompute)
        (CSSM_AC_HANDLE ACHandle,
         const CSSM_TUPLEGROUP *BaseAuthorizations,
         const CSSM_TUPLEGROUP *Credentials,
         uint32 NumberOfRequestors,
         const CSSM_LIST *Requestors,
         const CSSM_LIST *RequestedAuthorizationPeriod,
         const CSSM_LIST *RequestedAuthorization,
         CSSM_TUPLEGROUP_PTR AuthorizationResult);
    CSSM_RETURN ( *PassThrough)
        (CSSM_AC_HANDLE ACHandle,
         CSSM_TP_HANDLE TPHandle,
         CSSM_CL_HANDLE CLHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_DL_DB_LIST *DBList,
         uint32 PassThroughId,
         const void *InputParams,
         void **OutputParams);
} CSSM_SPI_AC_FUNCS __attribute__((deprecated)), *CSSM_SPI_AC_FUNCS_PTR __attribute__((deprecated));
# 29 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3

# 1 "/System/Library/Frameworks/Security.framework/Headers/cssmcli.h" 1 3
# 35 "/System/Library/Frameworks/Security.framework/Headers/cssmcli.h" 3
typedef struct cssm_spi_cl_funcs {
    CSSM_RETURN ( *CertCreateTemplate)
        (CSSM_CL_HANDLE CLHandle,
         uint32 NumberOfFields,
         const CSSM_FIELD *CertFields,
         CSSM_DATA_PTR CertTemplate);
    CSSM_RETURN ( *CertGetAllTemplateFields)
        (CSSM_CL_HANDLE CLHandle,
         const CSSM_DATA *CertTemplate,
         uint32 *NumberOfFields,
         CSSM_FIELD_PTR *CertFields);
    CSSM_RETURN ( *CertSign)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_DATA *CertTemplate,
         const CSSM_FIELD *SignScope,
         uint32 ScopeSize,
         CSSM_DATA_PTR SignedCert);
    CSSM_RETURN ( *CertVerify)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_DATA *CertToBeVerified,
         const CSSM_DATA *SignerCert,
         const CSSM_FIELD *VerifyScope,
         uint32 ScopeSize);
    CSSM_RETURN ( *CertVerifyWithKey)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_DATA *CertToBeVerified);
    CSSM_RETURN ( *CertGetFirstFieldValue)
        (CSSM_CL_HANDLE CLHandle,
         const CSSM_DATA *Cert,
         const CSSM_OID *CertField,
         CSSM_HANDLE_PTR ResultsHandle,
         uint32 *NumberOfMatchedFields,
         CSSM_DATA_PTR *Value);
    CSSM_RETURN ( *CertGetNextFieldValue)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_HANDLE ResultsHandle,
         CSSM_DATA_PTR *Value);
    CSSM_RETURN ( *CertAbortQuery)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_HANDLE ResultsHandle);
    CSSM_RETURN ( *CertGetKeyInfo)
        (CSSM_CL_HANDLE CLHandle,
         const CSSM_DATA *Cert,
         CSSM_KEY_PTR *Key);
    CSSM_RETURN ( *CertGetAllFields)
        (CSSM_CL_HANDLE CLHandle,
         const CSSM_DATA *Cert,
         uint32 *NumberOfFields,
         CSSM_FIELD_PTR *CertFields);
 CSSM_RETURN ( *FreeFields)
  (CSSM_CL_HANDLE CLHandle,
   uint32 NumberOfFields,
   CSSM_FIELD_PTR *FieldArray);
    CSSM_RETURN ( *FreeFieldValue)
        (CSSM_CL_HANDLE CLHandle,
         const CSSM_OID *CertOrCrlOid,
         CSSM_DATA_PTR Value);
    CSSM_RETURN ( *CertCache)
        (CSSM_CL_HANDLE CLHandle,
         const CSSM_DATA *Cert,
         CSSM_HANDLE_PTR CertHandle);
    CSSM_RETURN ( *CertGetFirstCachedFieldValue)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_HANDLE CertHandle,
         const CSSM_OID *CertField,
         CSSM_HANDLE_PTR ResultsHandle,
         uint32 *NumberOfMatchedFields,
         CSSM_DATA_PTR *Value);
    CSSM_RETURN ( *CertGetNextCachedFieldValue)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_HANDLE ResultsHandle,
         CSSM_DATA_PTR *Value);
    CSSM_RETURN ( *CertAbortCache)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_HANDLE CertHandle);
    CSSM_RETURN ( *CertGroupToSignedBundle)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CERTGROUP *CertGroupToBundle,
         const CSSM_CERT_BUNDLE_HEADER *BundleInfo,
         CSSM_DATA_PTR SignedBundle);
    CSSM_RETURN ( *CertGroupFromVerifiedBundle)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CERT_BUNDLE *CertBundle,
         const CSSM_DATA *SignerCert,
         CSSM_CERTGROUP_PTR *CertGroup);
    CSSM_RETURN ( *CertDescribeFormat)
        (CSSM_CL_HANDLE CLHandle,
         uint32 *NumberOfFields,
         CSSM_OID_PTR *OidList);
    CSSM_RETURN ( *CrlCreateTemplate)
        (CSSM_CL_HANDLE CLHandle,
         uint32 NumberOfFields,
         const CSSM_FIELD *CrlTemplate,
         CSSM_DATA_PTR NewCrl);
    CSSM_RETURN ( *CrlSetFields)
        (CSSM_CL_HANDLE CLHandle,
         uint32 NumberOfFields,
         const CSSM_FIELD *CrlTemplate,
         const CSSM_DATA *OldCrl,
         CSSM_DATA_PTR ModifiedCrl);
    CSSM_RETURN ( *CrlAddCert)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_DATA *Cert,
         uint32 NumberOfFields,
         const CSSM_FIELD *CrlEntryFields,
         const CSSM_DATA *OldCrl,
         CSSM_DATA_PTR NewCrl);
    CSSM_RETURN ( *CrlRemoveCert)
        (CSSM_CL_HANDLE CLHandle,
         const CSSM_DATA *Cert,
         const CSSM_DATA *OldCrl,
         CSSM_DATA_PTR NewCrl);
    CSSM_RETURN ( *CrlSign)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_DATA *UnsignedCrl,
         const CSSM_FIELD *SignScope,
         uint32 ScopeSize,
         CSSM_DATA_PTR SignedCrl);
    CSSM_RETURN ( *CrlVerify)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_DATA *CrlToBeVerified,
         const CSSM_DATA *SignerCert,
         const CSSM_FIELD *VerifyScope,
         uint32 ScopeSize);
    CSSM_RETURN ( *CrlVerifyWithKey)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_DATA *CrlToBeVerified);
    CSSM_RETURN ( *IsCertInCrl)
        (CSSM_CL_HANDLE CLHandle,
         const CSSM_DATA *Cert,
         const CSSM_DATA *Crl,
         CSSM_BOOL *CertFound);
    CSSM_RETURN ( *CrlGetFirstFieldValue)
        (CSSM_CL_HANDLE CLHandle,
         const CSSM_DATA *Crl,
         const CSSM_OID *CrlField,
         CSSM_HANDLE_PTR ResultsHandle,
         uint32 *NumberOfMatchedFields,
         CSSM_DATA_PTR *Value);
    CSSM_RETURN ( *CrlGetNextFieldValue)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_HANDLE ResultsHandle,
         CSSM_DATA_PTR *Value);
    CSSM_RETURN ( *CrlAbortQuery)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_HANDLE ResultsHandle);
    CSSM_RETURN ( *CrlGetAllFields)
        (CSSM_CL_HANDLE CLHandle,
         const CSSM_DATA *Crl,
         uint32 *NumberOfCrlFields,
         CSSM_FIELD_PTR *CrlFields);
    CSSM_RETURN ( *CrlCache)
        (CSSM_CL_HANDLE CLHandle,
         const CSSM_DATA *Crl,
         CSSM_HANDLE_PTR CrlHandle);
    CSSM_RETURN ( *IsCertInCachedCrl)
        (CSSM_CL_HANDLE CLHandle,
         const CSSM_DATA *Cert,
         CSSM_HANDLE CrlHandle,
         CSSM_BOOL *CertFound,
         CSSM_DATA_PTR CrlRecordIndex);
    CSSM_RETURN ( *CrlGetFirstCachedFieldValue)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_HANDLE CrlHandle,
         const CSSM_DATA *CrlRecordIndex,
         const CSSM_OID *CrlField,
         CSSM_HANDLE_PTR ResultsHandle,
         uint32 *NumberOfMatchedFields,
         CSSM_DATA_PTR *Value);
    CSSM_RETURN ( *CrlGetNextCachedFieldValue)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_HANDLE ResultsHandle,
         CSSM_DATA_PTR *Value);
    CSSM_RETURN ( *CrlGetAllCachedRecordFields)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_HANDLE CrlHandle,
         const CSSM_DATA *CrlRecordIndex,
         uint32 *NumberOfFields,
         CSSM_FIELD_PTR *CrlFields);
    CSSM_RETURN ( *CrlAbortCache)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_HANDLE CrlHandle);
    CSSM_RETURN ( *CrlDescribeFormat)
        (CSSM_CL_HANDLE CLHandle,
         uint32 *NumberOfFields,
         CSSM_OID_PTR *OidList);
    CSSM_RETURN ( *PassThrough)
        (CSSM_CL_HANDLE CLHandle,
         CSSM_CC_HANDLE CCHandle,
         uint32 PassThroughId,
         const void *InputParams,
         void **OutputParams);
} CSSM_SPI_CL_FUNCS __attribute__((deprecated)), *CSSM_SPI_CL_FUNCS_PTR __attribute__((deprecated));
# 31 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/cssmcspi.h" 1 3
# 30 "/System/Library/Frameworks/Security.framework/Headers/cssmcspi.h" 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/cssmspi.h" 1 3
# 35 "/System/Library/Frameworks/Security.framework/Headers/cssmspi.h" 3
typedef CSSM_RETURN ( *CSSM_SPI_ModuleEventHandler)
    (const CSSM_GUID *ModuleGuid,
     void *CssmNotifyCallbackCtx,
     uint32 SubserviceId,
     CSSM_SERVICE_TYPE ServiceType,
     CSSM_MODULE_EVENT EventType);

typedef uint32 CSSM_CONTEXT_EVENT;
enum {
    CSSM_CONTEXT_EVENT_CREATE = 1,
    CSSM_CONTEXT_EVENT_DELETE = 2,
    CSSM_CONTEXT_EVENT_UPDATE = 3
};

typedef struct cssm_module_funcs {
    CSSM_SERVICE_TYPE ServiceType;
    uint32 NumberOfServiceFuncs;
    const CSSM_PROC_ADDR *ServiceFuncs;
} CSSM_MODULE_FUNCS __attribute__((deprecated)), *CSSM_MODULE_FUNCS_PTR __attribute__((deprecated));

typedef void *( *CSSM_UPCALLS_MALLOC)
    (CSSM_HANDLE AddInHandle,
     uint32 size) __attribute__((deprecated));

typedef void ( *CSSM_UPCALLS_FREE)
    (CSSM_HANDLE AddInHandle,
     void *memblock) __attribute__((deprecated));

typedef void *( *CSSM_UPCALLS_REALLOC)
    (CSSM_HANDLE AddInHandle,
     void *memblock,
     uint32 size) __attribute__((deprecated));

typedef void *( *CSSM_UPCALLS_CALLOC)
    (CSSM_HANDLE AddInHandle,
     uint32 num,
     uint32 size) __attribute__((deprecated));

typedef struct cssm_upcalls {
    CSSM_UPCALLS_MALLOC malloc_func;
    CSSM_UPCALLS_FREE free_func;
    CSSM_UPCALLS_REALLOC realloc_func;
    CSSM_UPCALLS_CALLOC calloc_func;
    CSSM_RETURN ( *CcToHandle_func)
        (CSSM_CC_HANDLE Cc,
         CSSM_MODULE_HANDLE_PTR ModuleHandle);
    CSSM_RETURN ( *GetModuleInfo_func)
        (CSSM_MODULE_HANDLE Module,
         CSSM_GUID_PTR Guid,
         CSSM_VERSION_PTR Version,
         uint32 *SubServiceId,
         CSSM_SERVICE_TYPE *SubServiceType,
         CSSM_ATTACH_FLAGS *AttachFlags,
         CSSM_KEY_HIERARCHY *KeyHierarchy,
         CSSM_API_MEMORY_FUNCS_PTR AttachedMemFuncs,
         CSSM_FUNC_NAME_ADDR_PTR FunctionTable,
         uint32 NumFunctions);
} CSSM_UPCALLS __attribute__((deprecated)), *CSSM_UPCALLS_PTR __attribute__((deprecated));

CSSM_RETURN
CSSM_SPI_ModuleLoad (const CSSM_GUID *CssmGuid,
                     const CSSM_GUID *ModuleGuid,
                     CSSM_SPI_ModuleEventHandler CssmNotifyCallback,
                     void *CssmNotifyCallbackCtx)
     __attribute__((deprecated));

CSSM_RETURN
CSSM_SPI_ModuleUnload (const CSSM_GUID *CssmGuid,
                       const CSSM_GUID *ModuleGuid,
                       CSSM_SPI_ModuleEventHandler CssmNotifyCallback,
                       void *CssmNotifyCallbackCtx)
     __attribute__((deprecated));

CSSM_RETURN
CSSM_SPI_ModuleAttach (const CSSM_GUID *ModuleGuid,
                       const CSSM_VERSION *Version,
                       uint32 SubserviceID,
                       CSSM_SERVICE_TYPE SubServiceType,
                       CSSM_ATTACH_FLAGS AttachFlags,
                       CSSM_MODULE_HANDLE ModuleHandle,
                       CSSM_KEY_HIERARCHY KeyHierarchy,
                       const CSSM_GUID *CssmGuid,
                       const CSSM_GUID *ModuleManagerGuid,
                       const CSSM_GUID *CallerGuid,
                       const CSSM_UPCALLS *Upcalls,
                       CSSM_MODULE_FUNCS_PTR *FuncTbl)
     __attribute__((deprecated));

CSSM_RETURN
CSSM_SPI_ModuleDetach (CSSM_MODULE_HANDLE ModuleHandle)
 __attribute__((deprecated));
# 31 "/System/Library/Frameworks/Security.framework/Headers/cssmcspi.h" 2 3





typedef struct cssm_spi_csp_funcs {
    CSSM_RETURN ( *EventNotify)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CONTEXT_EVENT Event,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context);
    CSSM_RETURN ( *QuerySize)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context,
         CSSM_BOOL Encrypt,
         uint32 QuerySizeCount,
         CSSM_QUERY_SIZE_DATA_PTR DataBlock);
    CSSM_RETURN ( *SignData)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context,
         const CSSM_DATA *DataBufs,
         uint32 DataBufCount,
         CSSM_ALGORITHMS DigestAlgorithm,
         CSSM_DATA_PTR Signature);
    CSSM_RETURN ( *SignDataInit)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context);
    CSSM_RETURN ( *SignDataUpdate)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_DATA *DataBufs,
         uint32 DataBufCount);
    CSSM_RETURN ( *SignDataFinal)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         CSSM_DATA_PTR Signature);
    CSSM_RETURN ( *VerifyData)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context,
         const CSSM_DATA *DataBufs,
         uint32 DataBufCount,
         CSSM_ALGORITHMS DigestAlgorithm,
         const CSSM_DATA *Signature);
    CSSM_RETURN ( *VerifyDataInit)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context);
    CSSM_RETURN ( *VerifyDataUpdate)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_DATA *DataBufs,
         uint32 DataBufCount);
    CSSM_RETURN ( *VerifyDataFinal)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_DATA *Signature);
    CSSM_RETURN ( *DigestData)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context,
         const CSSM_DATA *DataBufs,
         uint32 DataBufCount,
         CSSM_DATA_PTR Digest);
    CSSM_RETURN ( *DigestDataInit)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context);
    CSSM_RETURN ( *DigestDataUpdate)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_DATA *DataBufs,
         uint32 DataBufCount);
    CSSM_RETURN ( *DigestDataClone)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         CSSM_CC_HANDLE ClonedCCHandle);
    CSSM_RETURN ( *DigestDataFinal)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         CSSM_DATA_PTR Digest);
    CSSM_RETURN ( *GenerateMac)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context,
         const CSSM_DATA *DataBufs,
         uint32 DataBufCount,
         CSSM_DATA_PTR Mac);
    CSSM_RETURN ( *GenerateMacInit)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context);
    CSSM_RETURN ( *GenerateMacUpdate)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_DATA *DataBufs,
         uint32 DataBufCount);
    CSSM_RETURN ( *GenerateMacFinal)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         CSSM_DATA_PTR Mac);
    CSSM_RETURN ( *VerifyMac)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context,
         const CSSM_DATA *DataBufs,
         uint32 DataBufCount,
         const CSSM_DATA *Mac);
    CSSM_RETURN ( *VerifyMacInit)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context);
    CSSM_RETURN ( *VerifyMacUpdate)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_DATA *DataBufs,
         uint32 DataBufCount);
    CSSM_RETURN ( *VerifyMacFinal)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_DATA *Mac);
    CSSM_RETURN ( *EncryptData)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context,
         const CSSM_DATA *ClearBufs,
         uint32 ClearBufCount,
         CSSM_DATA_PTR CipherBufs,
         uint32 CipherBufCount,
         CSSM_SIZE *bytesEncrypted,
         CSSM_DATA_PTR RemData,
         CSSM_PRIVILEGE Privilege);
    CSSM_RETURN ( *EncryptDataInit)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context,
         CSSM_PRIVILEGE Privilege);
    CSSM_RETURN ( *EncryptDataUpdate)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_DATA *ClearBufs,
         uint32 ClearBufCount,
         CSSM_DATA_PTR CipherBufs,
         uint32 CipherBufCount,
         CSSM_SIZE *bytesEncrypted);
    CSSM_RETURN ( *EncryptDataFinal)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         CSSM_DATA_PTR RemData);
    CSSM_RETURN ( *DecryptData)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context,
         const CSSM_DATA *CipherBufs,
         uint32 CipherBufCount,
         CSSM_DATA_PTR ClearBufs,
         uint32 ClearBufCount,
         CSSM_SIZE *bytesDecrypted,
         CSSM_DATA_PTR RemData,
         CSSM_PRIVILEGE Privilege);
    CSSM_RETURN ( *DecryptDataInit)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context,
         CSSM_PRIVILEGE Privilege);
    CSSM_RETURN ( *DecryptDataUpdate)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_DATA *CipherBufs,
         uint32 CipherBufCount,
         CSSM_DATA_PTR ClearBufs,
         uint32 ClearBufCount,
         CSSM_SIZE *bytesDecrypted);
    CSSM_RETURN ( *DecryptDataFinal)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         CSSM_DATA_PTR RemData);
    CSSM_RETURN ( *QueryKeySizeInBits)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context,
         const CSSM_KEY *Key,
         CSSM_KEY_SIZE_PTR KeySize);
    CSSM_RETURN ( *GenerateKey)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context,
         uint32 KeyUsage,
         uint32 KeyAttr,
         const CSSM_DATA *KeyLabel,
         const CSSM_RESOURCE_CONTROL_CONTEXT *CredAndAclEntry,
         CSSM_KEY_PTR Key,
         CSSM_PRIVILEGE Privilege);
    CSSM_RETURN ( *GenerateKeyPair)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context,
         uint32 PublicKeyUsage,
         uint32 PublicKeyAttr,
         const CSSM_DATA *PublicKeyLabel,
         CSSM_KEY_PTR PublicKey,
         uint32 PrivateKeyUsage,
         uint32 PrivateKeyAttr,
         const CSSM_DATA *PrivateKeyLabel,
         const CSSM_RESOURCE_CONTROL_CONTEXT *CredAndAclEntry,
         CSSM_KEY_PTR PrivateKey,
         CSSM_PRIVILEGE Privilege);
   CSSM_RETURN ( *GenerateRandom)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context,
         CSSM_DATA_PTR RandomNumber);
    CSSM_RETURN ( *GenerateAlgorithmParams)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context,
         uint32 ParamBits,
         CSSM_DATA_PTR Param,
         uint32 *NumberOfUpdatedAttibutes,
         CSSM_CONTEXT_ATTRIBUTE_PTR *UpdatedAttributes);
    CSSM_RETURN ( *WrapKey)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context,
         const CSSM_ACCESS_CREDENTIALS *AccessCred,
         const CSSM_KEY *Key,
         const CSSM_DATA *DescriptiveData,
         CSSM_WRAP_KEY_PTR WrappedKey,
         CSSM_PRIVILEGE Privilege);
    CSSM_RETURN ( *UnwrapKey)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context,
         const CSSM_KEY *PublicKey,
         const CSSM_WRAP_KEY *WrappedKey,
         uint32 KeyUsage,
         uint32 KeyAttr,
         const CSSM_DATA *KeyLabel,
         const CSSM_RESOURCE_CONTROL_CONTEXT *CredAndAclEntry,
         CSSM_KEY_PTR UnwrappedKey,
         CSSM_DATA_PTR DescriptiveData,
         CSSM_PRIVILEGE Privilege);
    CSSM_RETURN ( *DeriveKey)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context,
         CSSM_DATA_PTR Param,
         uint32 KeyUsage,
         uint32 KeyAttr,
         const CSSM_DATA *KeyLabel,
         const CSSM_RESOURCE_CONTROL_CONTEXT *CredAndAclEntry,
         CSSM_KEY_PTR DerivedKey);
    CSSM_RETURN ( *FreeKey)
        (CSSM_CSP_HANDLE CSPHandle,
         const CSSM_ACCESS_CREDENTIALS *AccessCred,
         CSSM_KEY_PTR KeyPtr,
         CSSM_BOOL Delete);
    CSSM_RETURN ( *PassThrough)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_CONTEXT *Context,
         uint32 PassThroughId,
         const void *InData,
         void **OutData);
    CSSM_RETURN ( *Login)
        (CSSM_CSP_HANDLE CSPHandle,
         const CSSM_ACCESS_CREDENTIALS *AccessCred,
         const CSSM_DATA *LoginName,
         const void *Reserved);
    CSSM_RETURN ( *Logout)
        (CSSM_CSP_HANDLE CSPHandle);
    CSSM_RETURN ( *ChangeLoginAcl)
        (CSSM_CSP_HANDLE CSPHandle,
         const CSSM_ACCESS_CREDENTIALS *AccessCred,
         const CSSM_ACL_EDIT *AclEdit);
    CSSM_RETURN ( *ObtainPrivateKeyFromPublicKey)
        (CSSM_CSP_HANDLE CSPHandle,
         const CSSM_KEY *PublicKey,
         CSSM_KEY_PTR PrivateKey);
    CSSM_RETURN ( *RetrieveUniqueId)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_DATA_PTR UniqueID);
    CSSM_RETURN ( *RetrieveCounter)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_DATA_PTR Counter);
    CSSM_RETURN ( *VerifyDevice)
        (CSSM_CSP_HANDLE CSPHandle,
         const CSSM_DATA *DeviceCert);
    CSSM_RETURN ( *GetTimeValue)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_ALGORITHMS TimeAlgorithm,
         CSSM_DATA *TimeData);
    CSSM_RETURN ( *GetOperationalStatistics)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_CSP_OPERATIONAL_STATISTICS *Statistics);
    CSSM_RETURN ( *GetLoginAcl)
        (CSSM_CSP_HANDLE CSPHandle,
         const CSSM_STRING *SelectionTag,
         uint32 *NumberOfAclInfos,
         CSSM_ACL_ENTRY_INFO_PTR *AclInfos);
    CSSM_RETURN ( *GetKeyAcl)
        (CSSM_CSP_HANDLE CSPHandle,
         const CSSM_KEY *Key,
         const CSSM_STRING *SelectionTag,
         uint32 *NumberOfAclInfos,
         CSSM_ACL_ENTRY_INFO_PTR *AclInfos);
    CSSM_RETURN ( *ChangeKeyAcl)
        (CSSM_CSP_HANDLE CSPHandle,
         const CSSM_ACCESS_CREDENTIALS *AccessCred,
         const CSSM_ACL_EDIT *AclEdit,
         const CSSM_KEY *Key);
    CSSM_RETURN ( *GetKeyOwner)
        (CSSM_CSP_HANDLE CSPHandle,
         const CSSM_KEY *Key,
         CSSM_ACL_OWNER_PROTOTYPE_PTR Owner);
    CSSM_RETURN ( *ChangeKeyOwner)
        (CSSM_CSP_HANDLE CSPHandle,
         const CSSM_ACCESS_CREDENTIALS *AccessCred,
         const CSSM_KEY *Key,
         const CSSM_ACL_OWNER_PROTOTYPE *NewOwner);
    CSSM_RETURN ( *GetLoginOwner)
        (CSSM_CSP_HANDLE CSPHandle,
         CSSM_ACL_OWNER_PROTOTYPE_PTR Owner);
    CSSM_RETURN ( *ChangeLoginOwner)
        (CSSM_CSP_HANDLE CSPHandle,
         const CSSM_ACCESS_CREDENTIALS *AccessCred,
         const CSSM_ACL_OWNER_PROTOTYPE *NewOwner);
} CSSM_SPI_CSP_FUNCS __attribute__((deprecated)), *CSSM_SPI_CSP_FUNCS_PTR __attribute__((deprecated));
# 32 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/cssmdli.h" 1 3
# 35 "/System/Library/Frameworks/Security.framework/Headers/cssmdli.h" 3
typedef struct cssm_spi_dl_funcs {
    CSSM_RETURN ( *DbOpen)
        (CSSM_DL_HANDLE DLHandle,
         const char *DbName,
         const CSSM_NET_ADDRESS *DbLocation,
         CSSM_DB_ACCESS_TYPE AccessRequest,
         const CSSM_ACCESS_CREDENTIALS *AccessCred,
         const void *OpenParameters,
         CSSM_DB_HANDLE *DbHandle);
    CSSM_RETURN ( *DbClose)
        (CSSM_DL_DB_HANDLE DLDBHandle);
    CSSM_RETURN ( *DbCreate)
        (CSSM_DL_HANDLE DLHandle,
         const char *DbName,
         const CSSM_NET_ADDRESS *DbLocation,
         const CSSM_DBINFO *DBInfo,
         CSSM_DB_ACCESS_TYPE AccessRequest,
         const CSSM_RESOURCE_CONTROL_CONTEXT *CredAndAclEntry,
         const void *OpenParameters,
         CSSM_DB_HANDLE *DbHandle);
    CSSM_RETURN ( *DbDelete)
        (CSSM_DL_HANDLE DLHandle,
         const char *DbName,
         const CSSM_NET_ADDRESS *DbLocation,
         const CSSM_ACCESS_CREDENTIALS *AccessCred);
    CSSM_RETURN ( *CreateRelation)
        (CSSM_DL_DB_HANDLE DLDBHandle,
         CSSM_DB_RECORDTYPE RelationID,
         const char *RelationName,
         uint32 NumberOfAttributes,
         const CSSM_DB_SCHEMA_ATTRIBUTE_INFO *pAttributeInfo,
         uint32 NumberOfIndexes,
         const CSSM_DB_SCHEMA_INDEX_INFO *pIndexInfo);
    CSSM_RETURN ( *DestroyRelation)
        (CSSM_DL_DB_HANDLE DLDBHandle,
         CSSM_DB_RECORDTYPE RelationID);
    CSSM_RETURN ( *Authenticate)
        (CSSM_DL_DB_HANDLE DLDBHandle,
         CSSM_DB_ACCESS_TYPE AccessRequest,
         const CSSM_ACCESS_CREDENTIALS *AccessCred);
    CSSM_RETURN ( *GetDbAcl)
        (CSSM_DL_DB_HANDLE DLDBHandle,
         const CSSM_STRING *SelectionTag,
         uint32 *NumberOfAclInfos,
         CSSM_ACL_ENTRY_INFO_PTR *AclInfos);
    CSSM_RETURN ( *ChangeDbAcl)
        (CSSM_DL_DB_HANDLE DLDBHandle,
         const CSSM_ACCESS_CREDENTIALS *AccessCred,
         const CSSM_ACL_EDIT *AclEdit);
    CSSM_RETURN ( *GetDbOwner)
        (CSSM_DL_DB_HANDLE DLDBHandle,
         CSSM_ACL_OWNER_PROTOTYPE_PTR Owner);
    CSSM_RETURN ( *ChangeDbOwner)
        (CSSM_DL_DB_HANDLE DLDBHandle,
         const CSSM_ACCESS_CREDENTIALS *AccessCred,
         const CSSM_ACL_OWNER_PROTOTYPE *NewOwner);
    CSSM_RETURN ( *GetDbNames)
        (CSSM_DL_HANDLE DLHandle,
         CSSM_NAME_LIST_PTR *NameList);
    CSSM_RETURN ( *GetDbNameFromHandle)
        (CSSM_DL_DB_HANDLE DLDBHandle,
         char **DbName);
    CSSM_RETURN ( *FreeNameList)
        (CSSM_DL_HANDLE DLHandle,
         CSSM_NAME_LIST_PTR NameList);
    CSSM_RETURN ( *DataInsert)
        (CSSM_DL_DB_HANDLE DLDBHandle,
         CSSM_DB_RECORDTYPE RecordType,
         const CSSM_DB_RECORD_ATTRIBUTE_DATA *Attributes,
         const CSSM_DATA *Data,
         CSSM_DB_UNIQUE_RECORD_PTR *UniqueId);
    CSSM_RETURN ( *DataDelete)
        (CSSM_DL_DB_HANDLE DLDBHandle,
         const CSSM_DB_UNIQUE_RECORD *UniqueRecordIdentifier);
    CSSM_RETURN ( *DataModify)
        (CSSM_DL_DB_HANDLE DLDBHandle,
         CSSM_DB_RECORDTYPE RecordType,
         CSSM_DB_UNIQUE_RECORD_PTR UniqueRecordIdentifier,
         const CSSM_DB_RECORD_ATTRIBUTE_DATA *AttributesToBeModified,
         const CSSM_DATA *DataToBeModified,
         CSSM_DB_MODIFY_MODE ModifyMode);
    CSSM_RETURN ( *DataGetFirst)
        (CSSM_DL_DB_HANDLE DLDBHandle,
         const CSSM_QUERY *Query,
         CSSM_HANDLE_PTR ResultsHandle,
         CSSM_DB_RECORD_ATTRIBUTE_DATA_PTR Attributes,
         CSSM_DATA_PTR Data,
         CSSM_DB_UNIQUE_RECORD_PTR *UniqueId);
    CSSM_RETURN ( *DataGetNext)
        (CSSM_DL_DB_HANDLE DLDBHandle,
         CSSM_HANDLE ResultsHandle,
         CSSM_DB_RECORD_ATTRIBUTE_DATA_PTR Attributes,
         CSSM_DATA_PTR Data,
         CSSM_DB_UNIQUE_RECORD_PTR *UniqueId);
    CSSM_RETURN ( *DataAbortQuery)
        (CSSM_DL_DB_HANDLE DLDBHandle,
         CSSM_HANDLE ResultsHandle);
    CSSM_RETURN ( *DataGetFromUniqueRecordId)
        (CSSM_DL_DB_HANDLE DLDBHandle,
         const CSSM_DB_UNIQUE_RECORD *UniqueRecord,
         CSSM_DB_RECORD_ATTRIBUTE_DATA_PTR Attributes,
         CSSM_DATA_PTR Data);
    CSSM_RETURN ( *FreeUniqueRecord)
        (CSSM_DL_DB_HANDLE DLDBHandle,
         CSSM_DB_UNIQUE_RECORD_PTR UniqueRecord);
    CSSM_RETURN ( *PassThrough)
        (CSSM_DL_DB_HANDLE DLDBHandle,
         uint32 PassThroughId,
         const void *InputParams,
         void **OutputParams);
} CSSM_SPI_DL_FUNCS __attribute__((deprecated)), *CSSM_SPI_DL_FUNCS_PTR __attribute__((deprecated));
# 33 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3

# 1 "/System/Library/Frameworks/Security.framework/Headers/cssmkrapi.h" 1 3
# 35 "/System/Library/Frameworks/Security.framework/Headers/cssmkrapi.h" 3
typedef uint32 CSSM_KRSP_HANDLE;

typedef struct cssm_kr_name {
    uint8 Type;
    uint8 Length;
    char *Name;
} CSSM_KR_NAME __attribute__((deprecated));

typedef struct cssm_kr_profile {
    CSSM_KR_NAME UserName;
    CSSM_CERTGROUP_PTR UserCertificate;
    CSSM_CERTGROUP_PTR KRSCertChain;
    uint8 LE_KRANum;
    CSSM_CERTGROUP_PTR LE_KRACertChainList;
    uint8 ENT_KRANum;
    CSSM_CERTGROUP_PTR ENT_KRACertChainList;
    uint8 INDIV_KRANum;
    CSSM_CERTGROUP_PTR INDIV_KRACertChainList;
    CSSM_DATA_PTR INDIV_AuthenticationInfo;
    uint32 KRSPFlags;
    CSSM_DATA_PTR KRSPExtensions;
} CSSM_KR_PROFILE __attribute__((deprecated)), *CSSM_KR_PROFILE_PTR __attribute__((deprecated));

typedef struct cssm_kr_wrappedproductinfo {
    CSSM_VERSION StandardVersion;
    CSSM_STRING StandardDescription;
    CSSM_VERSION ProductVersion;
    CSSM_STRING ProductDescription;
    CSSM_STRING ProductVendor;
    uint32 ProductFlags;
} CSSM_KR_WRAPPEDPRODUCT_INFO __attribute__((deprecated)), *CSSM_KR_WRAPPEDPRODUCT_INFO_PTR __attribute__((deprecated));

typedef struct cssm_krsubservice {
    uint32 SubServiceId;
    char *Description;
    CSSM_KR_WRAPPEDPRODUCT_INFO WrappedProduct;
} CSSM_KRSUBSERVICE, *CSSM_KRSUBSERVICE_PTR;

typedef uint32 CSSM_KR_POLICY_TYPE;





typedef uint32 CSSM_KR_POLICY_FLAGS;
# 89 "/System/Library/Frameworks/Security.framework/Headers/cssmkrapi.h" 3
typedef struct cssm_kr_policy_list_item {
    struct kr_policy_list_item *next;
    CSSM_ALGORITHMS AlgorithmId;
    CSSM_ENCRYPT_MODE Mode;
    uint32 MaxKeyLength;
    uint32 MaxRounds;
    uint8 WorkFactor;
    CSSM_KR_POLICY_FLAGS PolicyFlags;
    CSSM_CONTEXT_TYPE AlgClass;
} CSSM_KR_POLICY_LIST_ITEM __attribute__((deprecated)), *CSSM_KR_POLICY_LIST_ITEM_PTR __attribute__((deprecated));

typedef struct cssm_kr_policy_info {
    CSSM_BOOL krbNotAllowed;
    uint32 numberOfEntries;
    CSSM_KR_POLICY_LIST_ITEM *policyEntry;
} CSSM_KR_POLICY_INFO __attribute__((deprecated)), *CSSM_KR_POLICY_INFO_PTR __attribute__((deprecated));




CSSM_RETURN
CSSM_KR_SetEnterpriseRecoveryPolicy (const CSSM_DATA *RecoveryPolicyFileName,
                                     const CSSM_ACCESS_CREDENTIALS *OldPassPhrase,
                                     const CSSM_ACCESS_CREDENTIALS *NewPassPhrase)
  __attribute__((deprecated));




CSSM_RETURN
CSSM_KR_CreateRecoveryRegistrationContext (CSSM_KRSP_HANDLE KRSPHandle,
                                           CSSM_CC_HANDLE *NewContext)
  __attribute__((deprecated));

CSSM_RETURN
CSSM_KR_CreateRecoveryEnablementContext (CSSM_KRSP_HANDLE KRSPHandle,
                                         const CSSM_KR_PROFILE *LocalProfile,
                                         const CSSM_KR_PROFILE *RemoteProfile,
                                         CSSM_CC_HANDLE *NewContext)
  __attribute__((deprecated));

CSSM_RETURN
CSSM_KR_CreateRecoveryRequestContext (CSSM_KRSP_HANDLE KRSPHandle,
                                      const CSSM_KR_PROFILE *LocalProfile,
                                      CSSM_CC_HANDLE *NewContext)
  __attribute__((deprecated));

CSSM_RETURN
CSSM_KR_GetPolicyInfo (CSSM_CC_HANDLE CCHandle,
                       CSSM_KR_POLICY_FLAGS *EncryptionProhibited,
                       uint32 *WorkFactor)
  __attribute__((deprecated));




CSSM_RETURN
CSSM_KR_RegistrationRequest (CSSM_CC_HANDLE RecoveryRegistrationContext,
                             const CSSM_DATA *KRInData,
                             const CSSM_ACCESS_CREDENTIALS *AccessCredentials,
                             CSSM_KR_POLICY_FLAGS KRFlags,
                             sint32 *EstimatedTime,
                             CSSM_HANDLE_PTR ReferenceHandle)
  __attribute__((deprecated));

CSSM_RETURN
CSSM_KR_RegistrationRetrieve (CSSM_KRSP_HANDLE KRSPHandle,
                              CSSM_HANDLE ReferenceHandle,
                              const CSSM_ACCESS_CREDENTIALS *AccessCredentials,
                              sint32 *EstimatedTime,
                              CSSM_KR_PROFILE_PTR KRProfile)
  __attribute__((deprecated));




CSSM_RETURN
CSSM_KR_GenerateRecoveryFields (CSSM_CC_HANDLE KeyRecoveryContext,
                                CSSM_CC_HANDLE CCHandle,
                                const CSSM_DATA *KRSPOptions,
                                CSSM_KR_POLICY_FLAGS KRFlags,
                                CSSM_DATA_PTR KRFields,
                                CSSM_CC_HANDLE *NewCCHandle)
  __attribute__((deprecated));

CSSM_RETURN
CSSM_KR_ProcessRecoveryFields (CSSM_CC_HANDLE KeyRecoveryContext,
                               CSSM_CC_HANDLE CryptoContext,
                               const CSSM_DATA *KRSPOptions,
                               CSSM_KR_POLICY_FLAGS KRFlags,
                               const CSSM_DATA *KRFields,
                               CSSM_CC_HANDLE *NewCryptoContext)
  __attribute__((deprecated));




CSSM_RETURN
CSSM_KR_RecoveryRequest (CSSM_CC_HANDLE RecoveryRequestContext,
                         const CSSM_DATA *KRInData,
                         const CSSM_ACCESS_CREDENTIALS *AccessCredentials,
                         sint32 *EstimatedTime,
                         CSSM_HANDLE_PTR ReferenceHandle)
  __attribute__((deprecated));

CSSM_RETURN
CSSM_KR_RecoveryRetrieve (CSSM_KRSP_HANDLE KRSPHandle,
                          CSSM_HANDLE ReferenceHandle,
                          const CSSM_ACCESS_CREDENTIALS *AccessCredentials,
                          sint32 *EstimatedTime,
                          CSSM_HANDLE_PTR CacheHandle,
                          uint32 *NumberOfRecoveredKeys)
  __attribute__((deprecated));

CSSM_RETURN
CSSM_KR_GetRecoveredObject (CSSM_KRSP_HANDLE KRSPHandle,
                            CSSM_HANDLE CacheHandle,
                            uint32 IndexInResults,
                            CSSM_CSP_HANDLE CSPHandle,
                            const CSSM_RESOURCE_CONTROL_CONTEXT *CredAndAclEntry,
                            uint32 Flags,
                            CSSM_KEY_PTR RecoveredKey,
                            CSSM_DATA_PTR OtherInfo)
  __attribute__((deprecated));

CSSM_RETURN
CSSM_KR_RecoveryRequestAbort (CSSM_KRSP_HANDLE KRSPHandle,
                              CSSM_HANDLE CacheHandle)
  __attribute__((deprecated));

CSSM_RETURN
CSSM_KR_QueryPolicyInfo (CSSM_KRSP_HANDLE KRSPHandle,
                         CSSM_ALGORITHMS AlgorithmID,
                         CSSM_ENCRYPT_MODE Mode,
                         CSSM_CONTEXT_TYPE Class,
                         CSSM_KR_POLICY_INFO_PTR *PolicyInfoData)
  __attribute__((deprecated));




CSSM_RETURN
CSSM_KR_PassThrough (CSSM_KRSP_HANDLE KRSPHandle,
                     CSSM_CC_HANDLE KeyRecoveryContext,
                     CSSM_CC_HANDLE CryptoContext,
                     uint32 PassThroughId,
                     const void *InputParams,
                     void **OutputParams)
  __attribute__((deprecated));
# 35 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/cssmkrspi.h" 1 3
# 37 "/System/Library/Frameworks/Security.framework/Headers/cssmkrspi.h" 3
typedef struct cssm_spi_kr_funcs {
    CSSM_RETURN ( *RegistrationRequest)
        (CSSM_KRSP_HANDLE KRSPHandle,
         CSSM_CC_HANDLE KRRegistrationContextHandle,
         const CSSM_CONTEXT *KRRegistrationContext,
         const CSSM_DATA *KRInData,
         const CSSM_ACCESS_CREDENTIALS *AccessCredentials,
         CSSM_KR_POLICY_FLAGS KRFlags,
         sint32 *EstimatedTime,
         CSSM_HANDLE_PTR ReferenceHandle);
    CSSM_RETURN ( *RegistrationRetrieve)
        (CSSM_KRSP_HANDLE KRSPHandle,
         CSSM_HANDLE ReferenceHandle,
         sint32 *EstimatedTime,
         CSSM_KR_PROFILE_PTR KRProfile);
    CSSM_RETURN ( *GenerateRecoveryFields)
        (CSSM_KRSP_HANDLE KRSPHandle,
         CSSM_CC_HANDLE KREnablementContextHandle,
         const CSSM_CONTEXT *KREnablementContext,
         CSSM_CC_HANDLE CryptoContextHandle,
         const CSSM_CONTEXT *CryptoContext,
         const CSSM_DATA *KRSPOptions,
         CSSM_KR_POLICY_FLAGS KRFlags,
         CSSM_DATA_PTR KRFields);
    CSSM_RETURN ( *ProcessRecoveryFields)
        (CSSM_KRSP_HANDLE KRSPHandle,
         CSSM_CC_HANDLE KREnablementContextHandle,
         const CSSM_CONTEXT *KREnablementContext,
         CSSM_CC_HANDLE CryptoContextHandle,
         const CSSM_CONTEXT *CryptoContext,
         const CSSM_DATA *KRSPOptions,
         CSSM_KR_POLICY_FLAGS KRFlags,
         const CSSM_DATA *KRFields);
    CSSM_RETURN ( *RecoveryRequest)
        (CSSM_KRSP_HANDLE KRSPHandle,
         CSSM_CC_HANDLE KRRequestContextHandle,
         const CSSM_CONTEXT *KRRequestContext,
         const CSSM_DATA *KRInData,
         const CSSM_ACCESS_CREDENTIALS *AccessCredentials,
         sint32 *EstimatedTime,
         CSSM_HANDLE_PTR ReferenceHandle);
    CSSM_RETURN ( *RecoveryRetrieve)
        (CSSM_KRSP_HANDLE KRSPHandle,
         CSSM_HANDLE ReferenceHandle,
         sint32 *EstimatedTime,
         CSSM_HANDLE_PTR CacheHandle,
         uint32 *NumberOfRecoveredKeys);
    CSSM_RETURN ( *GetRecoveredObject)
        (CSSM_KRSP_HANDLE KRSPHandle,
         CSSM_HANDLE CacheHandle,
         uint32 IndexInResults,
         CSSM_CSP_HANDLE CSPHandle,
         const CSSM_RESOURCE_CONTROL_CONTEXT *CredAndAclEntry,
         uint32 Flags,
         CSSM_KEY_PTR RecoveredKey,
         CSSM_DATA_PTR OtherInfo);
    CSSM_RETURN ( *RecoveryRequestAbort)
        (CSSM_KRSP_HANDLE KRSPHandle,
         CSSM_HANDLE ResultsHandle);
    CSSM_RETURN ( *PassThrough)
        (CSSM_KRSP_HANDLE KRSPHandle,
         CSSM_CC_HANDLE KeyRecoveryContextHandle,
         const CSSM_CONTEXT *KeyRecoveryContext,
         CSSM_CC_HANDLE CryptoContextHandle,
         const CSSM_CONTEXT *CryptoContext,
         uint32 PassThroughId,
         const void *InputParams,
         void **OutputParams);
} CSSM_SPI_KR_FUNCS __attribute__((deprecated)), *CSSM_SPI_KR_FUNCS_PTR __attribute__((deprecated));
# 36 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3

# 1 "/System/Library/Frameworks/Security.framework/Headers/cssmtpi.h" 1 3
# 35 "/System/Library/Frameworks/Security.framework/Headers/cssmtpi.h" 3
typedef struct cssm_spi_tp_funcs {
    CSSM_RETURN ( *SubmitCredRequest)
        (CSSM_TP_HANDLE TPHandle,
         const CSSM_TP_AUTHORITY_ID *PreferredAuthority,
         CSSM_TP_AUTHORITY_REQUEST_TYPE RequestType,
         const CSSM_TP_REQUEST_SET *RequestInput,
         const CSSM_TP_CALLERAUTH_CONTEXT *CallerAuthContext,
         sint32 *EstimatedTime,
         CSSM_DATA_PTR ReferenceIdentifier);
    CSSM_RETURN ( *RetrieveCredResult)
        (CSSM_TP_HANDLE TPHandle,
         const CSSM_DATA *ReferenceIdentifier,
         const CSSM_TP_CALLERAUTH_CONTEXT *CallerAuthCredentials,
         sint32 *EstimatedTime,
         CSSM_BOOL *ConfirmationRequired,
         CSSM_TP_RESULT_SET_PTR *RetrieveOutput);
    CSSM_RETURN ( *ConfirmCredResult)
        (CSSM_TP_HANDLE TPHandle,
         const CSSM_DATA *ReferenceIdentifier,
         const CSSM_TP_CALLERAUTH_CONTEXT *CallerAuthCredentials,
         const CSSM_TP_CONFIRM_RESPONSE *Responses,
         const CSSM_TP_AUTHORITY_ID *PreferredAuthority);
    CSSM_RETURN ( *ReceiveConfirmation)
        (CSSM_TP_HANDLE TPHandle,
         const CSSM_DATA *ReferenceIdentifier,
         CSSM_TP_CONFIRM_RESPONSE_PTR *Responses,
         sint32 *ElapsedTime);
    CSSM_RETURN ( *CertReclaimKey)
        (CSSM_TP_HANDLE TPHandle,
         const CSSM_CERTGROUP *CertGroup,
         uint32 CertIndex,
         CSSM_LONG_HANDLE KeyCacheHandle,
         CSSM_CSP_HANDLE CSPHandle,
         const CSSM_RESOURCE_CONTROL_CONTEXT *CredAndAclEntry);
    CSSM_RETURN ( *CertReclaimAbort)
        (CSSM_TP_HANDLE TPHandle,
         CSSM_LONG_HANDLE KeyCacheHandle);
    CSSM_RETURN ( *FormRequest)
        (CSSM_TP_HANDLE TPHandle,
         const CSSM_TP_AUTHORITY_ID *PreferredAuthority,
         CSSM_TP_FORM_TYPE FormType,
         CSSM_DATA_PTR BlankForm);
    CSSM_RETURN ( *FormSubmit)
        (CSSM_TP_HANDLE TPHandle,
         CSSM_TP_FORM_TYPE FormType,
         const CSSM_DATA *Form,
         const CSSM_TP_AUTHORITY_ID *ClearanceAuthority,
         const CSSM_TP_AUTHORITY_ID *RepresentedAuthority,
         CSSM_ACCESS_CREDENTIALS_PTR Credentials);
    CSSM_RETURN ( *CertGroupVerify)
        (CSSM_TP_HANDLE TPHandle,
         CSSM_CL_HANDLE CLHandle,
         CSSM_CSP_HANDLE CSPHandle,
         const CSSM_CERTGROUP *CertGroupToBeVerified,
         const CSSM_TP_VERIFY_CONTEXT *VerifyContext,
         CSSM_TP_VERIFY_CONTEXT_RESULT_PTR VerifyContextResult);
    CSSM_RETURN ( *CertCreateTemplate)
        (CSSM_TP_HANDLE TPHandle,
         CSSM_CL_HANDLE CLHandle,
         uint32 NumberOfFields,
         const CSSM_FIELD *CertFields,
         CSSM_DATA_PTR CertTemplate);
    CSSM_RETURN ( *CertGetAllTemplateFields)
        (CSSM_TP_HANDLE TPHandle,
         CSSM_CL_HANDLE CLHandle,
         const CSSM_DATA *CertTemplate,
         uint32 *NumberOfFields,
         CSSM_FIELD_PTR *CertFields);
    CSSM_RETURN ( *CertSign)
        (CSSM_TP_HANDLE TPHandle,
         CSSM_CL_HANDLE CLHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_DATA *CertTemplateToBeSigned,
         const CSSM_CERTGROUP *SignerCertGroup,
         const CSSM_TP_VERIFY_CONTEXT *SignerVerifyContext,
         CSSM_TP_VERIFY_CONTEXT_RESULT_PTR SignerVerifyResult,
         CSSM_DATA_PTR SignedCert);
    CSSM_RETURN ( *CrlVerify)
        (CSSM_TP_HANDLE TPHandle,
         CSSM_CL_HANDLE CLHandle,
         CSSM_CSP_HANDLE CSPHandle,
         const CSSM_ENCODED_CRL *CrlToBeVerified,
         const CSSM_CERTGROUP *SignerCertGroup,
         const CSSM_TP_VERIFY_CONTEXT *VerifyContext,
         CSSM_TP_VERIFY_CONTEXT_RESULT_PTR RevokerVerifyResult);
    CSSM_RETURN ( *CrlCreateTemplate)
        (CSSM_TP_HANDLE TPHandle,
         CSSM_CL_HANDLE CLHandle,
         uint32 NumberOfFields,
         const CSSM_FIELD *CrlFields,
         CSSM_DATA_PTR NewCrlTemplate);
    CSSM_RETURN ( *CertRevoke)
        (CSSM_TP_HANDLE TPHandle,
         CSSM_CL_HANDLE CLHandle,
         CSSM_CSP_HANDLE CSPHandle,
         const CSSM_DATA *OldCrlTemplate,
         const CSSM_CERTGROUP *CertGroupToBeRevoked,
         const CSSM_CERTGROUP *RevokerCertGroup,
         const CSSM_TP_VERIFY_CONTEXT *RevokerVerifyContext,
         CSSM_TP_VERIFY_CONTEXT_RESULT_PTR RevokerVerifyResult,
         CSSM_TP_CERTCHANGE_REASON Reason,
         CSSM_DATA_PTR NewCrlTemplate);
    CSSM_RETURN ( *CertRemoveFromCrlTemplate)
        (CSSM_TP_HANDLE TPHandle,
         CSSM_CL_HANDLE CLHandle,
         CSSM_CSP_HANDLE CSPHandle,
         const CSSM_DATA *OldCrlTemplate,
         const CSSM_CERTGROUP *CertGroupToBeRemoved,
         const CSSM_CERTGROUP *RevokerCertGroup,
         const CSSM_TP_VERIFY_CONTEXT *RevokerVerifyContext,
         CSSM_TP_VERIFY_CONTEXT_RESULT_PTR RevokerVerifyResult,
         CSSM_DATA_PTR NewCrlTemplate);
    CSSM_RETURN ( *CrlSign)
        (CSSM_TP_HANDLE TPHandle,
         CSSM_CL_HANDLE CLHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_ENCODED_CRL *CrlToBeSigned,
         const CSSM_CERTGROUP *SignerCertGroup,
         const CSSM_TP_VERIFY_CONTEXT *SignerVerifyContext,
         CSSM_TP_VERIFY_CONTEXT_RESULT_PTR SignerVerifyResult,
         CSSM_DATA_PTR SignedCrl);
    CSSM_RETURN ( *ApplyCrlToDb)
        (CSSM_TP_HANDLE TPHandle,
         CSSM_CL_HANDLE CLHandle,
         CSSM_CSP_HANDLE CSPHandle,
         const CSSM_ENCODED_CRL *CrlToBeApplied,
         const CSSM_CERTGROUP *SignerCertGroup,
         const CSSM_TP_VERIFY_CONTEXT *ApplyCrlVerifyContext,
         CSSM_TP_VERIFY_CONTEXT_RESULT_PTR ApplyCrlVerifyResult);
    CSSM_RETURN ( *CertGroupConstruct)
        (CSSM_TP_HANDLE TPHandle,
         CSSM_CL_HANDLE CLHandle,
         CSSM_CSP_HANDLE CSPHandle,
         const CSSM_DL_DB_LIST *DBList,
         const void *ConstructParams,
         const CSSM_CERTGROUP *CertGroupFrag,
         CSSM_CERTGROUP_PTR *CertGroup);
    CSSM_RETURN ( *CertGroupPrune)
        (CSSM_TP_HANDLE TPHandle,
         CSSM_CL_HANDLE CLHandle,
         const CSSM_DL_DB_LIST *DBList,
         const CSSM_CERTGROUP *OrderedCertGroup,
         CSSM_CERTGROUP_PTR *PrunedCertGroup);
    CSSM_RETURN ( *CertGroupToTupleGroup)
        (CSSM_TP_HANDLE TPHandle,
         CSSM_CL_HANDLE CLHandle,
         const CSSM_CERTGROUP *CertGroup,
         CSSM_TUPLEGROUP_PTR *TupleGroup);
    CSSM_RETURN ( *TupleGroupToCertGroup)
        (CSSM_TP_HANDLE TPHandle,
         CSSM_CL_HANDLE CLHandle,
         const CSSM_TUPLEGROUP *TupleGroup,
         CSSM_CERTGROUP_PTR *CertTemplates);
    CSSM_RETURN ( *PassThrough)
        (CSSM_TP_HANDLE TPHandle,
         CSSM_CL_HANDLE CLHandle,
         CSSM_CC_HANDLE CCHandle,
         const CSSM_DL_DB_LIST *DBList,
         uint32 PassThroughId,
         const void *InputParams,
         void **OutputParams);
} CSSM_SPI_TP_FUNCS __attribute__((deprecated)), *CSSM_SPI_TP_FUNCS_PTR __attribute__((deprecated));
# 38 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3

# 1 "/System/Library/Frameworks/Security.framework/Headers/emmspi.h" 1 3
# 35 "/System/Library/Frameworks/Security.framework/Headers/emmspi.h" 3
typedef struct cssm_state_funcs {
    CSSM_RETURN ( *cssm_GetAttachFunctions)
        (CSSM_MODULE_HANDLE hAddIn,
         CSSM_SERVICE_MASK AddinType,
         void **SPFunctions,
         CSSM_GUID_PTR Guid,
  CSSM_BOOL *Serialized);
    CSSM_RETURN ( *cssm_ReleaseAttachFunctions)
        (CSSM_MODULE_HANDLE hAddIn);
    CSSM_RETURN ( *cssm_GetAppMemoryFunctions)
        (CSSM_MODULE_HANDLE hAddIn,
         CSSM_UPCALLS_PTR UpcallTable);
    CSSM_RETURN ( *cssm_IsFuncCallValid)
        (CSSM_MODULE_HANDLE hAddin,
         CSSM_PROC_ADDR SrcAddress,
         CSSM_PROC_ADDR DestAddress,
         CSSM_PRIVILEGE InPriv,
         CSSM_PRIVILEGE *OutPriv,
         CSSM_BITMASK Hints,
         CSSM_BOOL *IsOK);
    CSSM_RETURN ( *cssm_DeregisterManagerServices)
        (const CSSM_GUID *GUID);
    CSSM_RETURN ( *cssm_DeliverModuleManagerEvent)
        (const CSSM_MANAGER_EVENT_NOTIFICATION *EventDescription);
} CSSM_STATE_FUNCS __attribute__((deprecated)), *CSSM_STATE_FUNCS_PTR __attribute__((deprecated));

typedef struct cssm_manager_registration_info {

    CSSM_RETURN ( *Initialize)
        (uint32 VerMajor,
         uint32 VerMinor);
    CSSM_RETURN ( *Terminate) (void);
    CSSM_RETURN ( *RegisterDispatchTable)
        (CSSM_STATE_FUNCS_PTR CssmStateCallTable);
    CSSM_RETURN ( *DeregisterDispatchTable) (void);
    CSSM_RETURN ( *EventNotifyManager)
        (const CSSM_MANAGER_EVENT_NOTIFICATION *EventDescription);
    CSSM_RETURN ( *RefreshFunctionTable)
        (CSSM_FUNC_NAME_ADDR_PTR FuncNameAddrPtr,
         uint32 NumOfFuncNameAddr);
} CSSM_MANAGER_REGISTRATION_INFO __attribute__((deprecated)), *CSSM_MANAGER_REGISTRATION_INFO_PTR __attribute__((deprecated));

enum {
 CSSM_HINT_NONE = 0,
 CSSM_HINT_ADDRESS_APP = 1 << 0,
 CSSM_HINT_ADDRESS_SP = 1 << 1
};

CSSM_RETURN
ModuleManagerAuthenticate (CSSM_KEY_HIERARCHY KeyHierarchy,
                           const CSSM_GUID *CssmGuid,
                           const CSSM_GUID *AppGuid,
                           CSSM_MANAGER_REGISTRATION_INFO_PTR FunctionTable)
      __attribute__((deprecated));
# 40 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3

# 1 "/System/Library/Frameworks/Security.framework/Headers/mds.h" 1 3
# 36 "/System/Library/Frameworks/Security.framework/Headers/mds.h" 3
typedef CSSM_DL_HANDLE MDS_HANDLE;

typedef CSSM_DL_DB_HANDLE MDS_DB_HANDLE;

typedef struct mds_funcs {
    CSSM_RETURN ( *DbOpen)
        (MDS_HANDLE MdsHandle,
         const char *DbName,
         const CSSM_NET_ADDRESS *DbLocation,
         CSSM_DB_ACCESS_TYPE AccessRequest,
         const CSSM_ACCESS_CREDENTIALS *AccessCred,
         const void *OpenParameters,
         CSSM_DB_HANDLE *hMds);

    CSSM_RETURN ( *DbClose)
        (MDS_DB_HANDLE MdsDbHandle);

    CSSM_RETURN ( *GetDbNames)
        (MDS_HANDLE MdsHandle,
         CSSM_NAME_LIST_PTR *NameList);

    CSSM_RETURN ( *GetDbNameFromHandle)
        (MDS_DB_HANDLE MdsDbHandle,
         char **DbName);

    CSSM_RETURN ( *FreeNameList)
        (MDS_HANDLE MdsHandle,
         CSSM_NAME_LIST_PTR NameList);

    CSSM_RETURN ( *DataInsert)
        (MDS_DB_HANDLE MdsDbHandle,
         CSSM_DB_RECORDTYPE RecordType,
         const CSSM_DB_RECORD_ATTRIBUTE_DATA *Attributes,
         const CSSM_DATA *Data,
         CSSM_DB_UNIQUE_RECORD_PTR *UniqueId);

    CSSM_RETURN ( *DataDelete)
        (MDS_DB_HANDLE MdsDbHandle,
         const CSSM_DB_UNIQUE_RECORD *UniqueRecordIdentifier);

    CSSM_RETURN ( *DataModify)
        (MDS_DB_HANDLE MdsDbHandle,
         CSSM_DB_RECORDTYPE RecordType,
         CSSM_DB_UNIQUE_RECORD_PTR UniqueRecordIdentifier,
         const CSSM_DB_RECORD_ATTRIBUTE_DATA *AttributesToBeModified,
         const CSSM_DATA *DataToBeModified,
         CSSM_DB_MODIFY_MODE ModifyMode);

    CSSM_RETURN ( *DataGetFirst)
        (MDS_DB_HANDLE MdsDbHandle,
         const CSSM_QUERY *Query,
         CSSM_HANDLE_PTR ResultsHandle,
         CSSM_DB_RECORD_ATTRIBUTE_DATA_PTR Attributes,
         CSSM_DATA_PTR Data,
         CSSM_DB_UNIQUE_RECORD_PTR *UniqueId);

    CSSM_RETURN ( *DataGetNext)
        (MDS_DB_HANDLE MdsDbHandle,
         CSSM_HANDLE ResultsHandle,
         CSSM_DB_RECORD_ATTRIBUTE_DATA_PTR Attributes,
         CSSM_DATA_PTR Data,
         CSSM_DB_UNIQUE_RECORD_PTR *UniqueId);

    CSSM_RETURN ( *DataAbortQuery)
        (MDS_DB_HANDLE MdsDbHandle,
         CSSM_HANDLE ResultsHandle);

    CSSM_RETURN ( *DataGetFromUniqueRecordId)
        (MDS_DB_HANDLE MdsDbHandle,
         const CSSM_DB_UNIQUE_RECORD *UniqueRecord,
         CSSM_DB_RECORD_ATTRIBUTE_DATA_PTR Attributes,
         CSSM_DATA_PTR Data);

    CSSM_RETURN ( *FreeUniqueRecord)
        (MDS_DB_HANDLE MdsDbHandle,
         CSSM_DB_UNIQUE_RECORD_PTR UniqueRecord);

    CSSM_RETURN ( *CreateRelation)
        (MDS_DB_HANDLE MdsDbHandle,
         CSSM_DB_RECORDTYPE RelationID,
         const char *RelationName,
         uint32 NumberOfAttributes,
         const CSSM_DB_SCHEMA_ATTRIBUTE_INFO *pAttributeInfo,
         uint32 NumberOfIndexes,
         const CSSM_DB_SCHEMA_INDEX_INFO *pIndexInfo);

    CSSM_RETURN ( *DestroyRelation)
        (MDS_DB_HANDLE MdsDbHandle,
         CSSM_DB_RECORDTYPE RelationID);
} MDS_FUNCS __attribute__((deprecated)), *MDS_FUNCS_PTR __attribute__((deprecated));




CSSM_RETURN
MDS_Initialize (const CSSM_GUID *pCallerGuid,
                const CSSM_MEMORY_FUNCS *pMemoryFunctions,
                MDS_FUNCS_PTR pDlFunctions,
                MDS_HANDLE *hMds)
    __attribute__((deprecated));

CSSM_RETURN
MDS_Terminate (MDS_HANDLE MdsHandle)
 __attribute__((deprecated));

CSSM_RETURN
MDS_Install (MDS_HANDLE MdsHandle)
 __attribute__((deprecated));

CSSM_RETURN
MDS_Uninstall (MDS_HANDLE MdsHandle)
 __attribute__((deprecated));
# 42 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/mds_schema.h" 1 3
# 43 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/oidsalg.h" 1 3
# 35 "/System/Library/Frameworks/Security.framework/Headers/oidsalg.h" 3
extern const CSSM_OID
 CSSMOID_MD2 __attribute__((deprecated)),
 CSSMOID_MD4 __attribute__((deprecated)),
 CSSMOID_MD5 __attribute__((deprecated)),
 CSSMOID_RSA __attribute__((deprecated)),
 CSSMOID_MD2WithRSA __attribute__((deprecated)),
 CSSMOID_MD4WithRSA __attribute__((deprecated)),
 CSSMOID_MD5WithRSA __attribute__((deprecated)),
 CSSMOID_SHA1WithRSA __attribute__((deprecated)),
 CSSMOID_SHA224WithRSA __attribute__((deprecated)),
 CSSMOID_SHA256WithRSA __attribute__((deprecated)),
 CSSMOID_SHA384WithRSA __attribute__((deprecated)),
 CSSMOID_SHA512WithRSA __attribute__((deprecated)),
 CSSMOID_SHA1WithRSA_OIW __attribute__((deprecated)),
 CSSMOID_RSAWithOAEP __attribute__((deprecated)),
 CSSMOID_OAEP_MGF1 __attribute__((deprecated)),
 CSSMOID_OAEP_ID_PSPECIFIED __attribute__((deprecated)),
 CSSMOID_DES_CBC __attribute__((deprecated)),
 CSSMOID_ANSI_DH_PUB_NUMBER __attribute__((deprecated)),
 CSSMOID_ANSI_DH_STATIC __attribute__((deprecated)),
 CSSMOID_ANSI_DH_ONE_FLOW __attribute__((deprecated)),
 CSSMOID_ANSI_DH_EPHEM __attribute__((deprecated)),
 CSSMOID_ANSI_DH_HYBRID1 __attribute__((deprecated)),
 CSSMOID_ANSI_DH_HYBRID2 __attribute__((deprecated)),
 CSSMOID_ANSI_DH_HYBRID_ONEFLOW __attribute__((deprecated)),
 CSSMOID_ANSI_MQV1 __attribute__((deprecated)),
 CSSMOID_ANSI_MQV2 __attribute__((deprecated)),
 CSSMOID_ANSI_DH_STATIC_SHA1 __attribute__((deprecated)),
 CSSMOID_ANSI_DH_ONE_FLOW_SHA1 __attribute__((deprecated)),
 CSSMOID_ANSI_DH_EPHEM_SHA1 __attribute__((deprecated)),
 CSSMOID_ANSI_DH_HYBRID1_SHA1 __attribute__((deprecated)),
 CSSMOID_ANSI_DH_HYBRID2_SHA1 __attribute__((deprecated)),
 CSSMOID_ANSI_MQV1_SHA1 __attribute__((deprecated)),
 CSSMOID_ANSI_MQV2_SHA1 __attribute__((deprecated)),
 CSSMOID_PKCS3 __attribute__((deprecated)),
 CSSMOID_DH __attribute__((deprecated)),
 CSSMOID_DSA __attribute__((deprecated)),
 CSSMOID_DSA_CMS __attribute__((deprecated)),
 CSSMOID_DSA_JDK __attribute__((deprecated)),
 CSSMOID_SHA1WithDSA __attribute__((deprecated)),
 CSSMOID_SHA1WithDSA_CMS __attribute__((deprecated)),
 CSSMOID_SHA1WithDSA_JDK __attribute__((deprecated)),
 CSSMOID_SHA1 __attribute__((deprecated)),
 CSSMOID_SHA224 __attribute__((deprecated)),
 CSSMOID_SHA256 __attribute__((deprecated)),
 CSSMOID_SHA384 __attribute__((deprecated)),
 CSSMOID_SHA512 __attribute__((deprecated)),
 CSSMOID_ecPublicKey __attribute__((deprecated)),
 CSSMOID_ECDSA_WithSHA1 __attribute__((deprecated)),
 CSSMOID_ECDSA_WithSHA224 __attribute__((deprecated)),
 CSSMOID_ECDSA_WithSHA256 __attribute__((deprecated)),
 CSSMOID_ECDSA_WithSHA384 __attribute__((deprecated)),
 CSSMOID_ECDSA_WithSHA512 __attribute__((deprecated)),
 CSSMOID_ECDSA_WithSpecified __attribute__((deprecated)),
 CSSMOID_APPLE_ISIGN __attribute__((deprecated)),
 CSSMOID_APPLE_X509_BASIC __attribute__((deprecated)),
 CSSMOID_APPLE_TP_SSL __attribute__((deprecated)),
 CSSMOID_APPLE_TP_LOCAL_CERT_GEN __attribute__((deprecated)),
 CSSMOID_APPLE_TP_CSR_GEN __attribute__((deprecated)),
 CSSMOID_APPLE_TP_REVOCATION_CRL __attribute__((deprecated)),
 CSSMOID_APPLE_TP_REVOCATION_OCSP __attribute__((deprecated)),
 CSSMOID_APPLE_TP_SMIME __attribute__((deprecated)),
 CSSMOID_APPLE_TP_EAP __attribute__((deprecated)),
 CSSMOID_APPLE_TP_CODE_SIGN __attribute__((deprecated)),
 CSSMOID_APPLE_TP_SW_UPDATE_SIGNING __attribute__((deprecated)),
 CSSMOID_APPLE_TP_IP_SEC __attribute__((deprecated)),
 CSSMOID_APPLE_TP_ICHAT __attribute__((deprecated)),
 CSSMOID_APPLE_TP_RESOURCE_SIGN __attribute__((deprecated)),
 CSSMOID_APPLE_TP_PKINIT_CLIENT __attribute__((deprecated)),
 CSSMOID_APPLE_TP_PKINIT_SERVER __attribute__((deprecated)),
 CSSMOID_APPLE_TP_CODE_SIGNING __attribute__((deprecated)),
 CSSMOID_APPLE_TP_PACKAGE_SIGNING __attribute__((deprecated)),
 CSSMOID_APPLE_TP_MACAPPSTORE_RECEIPT __attribute__((deprecated)),
 CSSMOID_APPLE_TP_APPLEID_SHARING __attribute__((deprecated)),
 CSSMOID_APPLE_FEE __attribute__((deprecated)),
 CSSMOID_APPLE_ASC __attribute__((deprecated)),
 CSSMOID_APPLE_FEE_MD5 __attribute__((deprecated)),
 CSSMOID_APPLE_FEE_SHA1 __attribute__((deprecated)),
 CSSMOID_APPLE_FEED __attribute__((deprecated)),
 CSSMOID_APPLE_FEEDEXP __attribute__((deprecated)),
 CSSMOID_APPLE_ECDSA __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_REQ __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_REQ_IDENTITY __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_REQ_EMAIL_SIGN __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_REQ_EMAIL_ENCRYPT __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_REQ_ARCHIVE_LIST __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_REQ_ARCHIVE_STORE __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_REQ_ARCHIVE_FETCH __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_REQ_ARCHIVE_REMOVE __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_REQ_SHARED_SERVICES __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_REQ_VALUE_USERNAME __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_REQ_VALUE_PASSWORD __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_REQ_VALUE_HOSTNAME __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_REQ_VALUE_RENEW __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_REQ_VALUE_ASYNC __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_REQ_VALUE_IS_PENDING __attribute__((deprecated)),
 CSSMOID_PKCS5_DIGEST_ALG __attribute__((deprecated)),
 CSSMOID_PKCS5_ENCRYPT_ALG __attribute__((deprecated)),
 CSSMOID_PKCS5_HMAC_SHA1 __attribute__((deprecated)),
 CSSMOID_PKCS5_pbeWithMD2AndDES __attribute__((deprecated)),
 CSSMOID_PKCS5_pbeWithMD2AndRC2 __attribute__((deprecated)),
 CSSMOID_PKCS5_pbeWithMD5AndDES __attribute__((deprecated)),
 CSSMOID_PKCS5_pbeWithMD5AndRC2 __attribute__((deprecated)),
 CSSMOID_PKCS5_pbeWithSHA1AndDES __attribute__((deprecated)),
 CSSMOID_PKCS5_pbeWithSHA1AndRC2 __attribute__((deprecated)),
 CSSMOID_PKCS5_PBKDF2 __attribute__((deprecated)),
 CSSMOID_PKCS5_PBES2 __attribute__((deprecated)),
 CSSMOID_PKCS5_PBMAC1 __attribute__((deprecated)),
 CSSMOID_PKCS5_RC2_CBC __attribute__((deprecated)),
 CSSMOID_PKCS5_DES_EDE3_CBC __attribute__((deprecated)),
 CSSMOID_PKCS5_RC5_CBC __attribute__((deprecated)),
 CSSMOID_PKCS12_pbeWithSHAAnd128BitRC4 __attribute__((deprecated)),
 CSSMOID_PKCS12_pbeWithSHAAnd40BitRC4 __attribute__((deprecated)),
 CSSMOID_PKCS12_pbeWithSHAAnd3Key3DESCBC __attribute__((deprecated)),
 CSSMOID_PKCS12_pbeWithSHAAnd2Key3DESCBC __attribute__((deprecated)),
 CSSMOID_PKCS12_pbeWithSHAAnd128BitRC2CBC __attribute__((deprecated)),
 CSSMOID_PKCS12_pbewithSHAAnd40BitRC2CBC __attribute__((deprecated));
# 44 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/oidsattr.h" 1 3
# 30 "/System/Library/Frameworks/Security.framework/Headers/oidsattr.h" 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/oidsbase.h" 1 3
# 31 "/System/Library/Frameworks/Security.framework/Headers/oidsattr.h" 2 3




extern const CSSM_OID
 CSSMOID_ObjectClass __attribute__((deprecated)),
 CSSMOID_AliasedEntryName __attribute__((deprecated)),
 CSSMOID_KnowledgeInformation __attribute__((deprecated)),
 CSSMOID_CommonName __attribute__((deprecated)),
 CSSMOID_Surname __attribute__((deprecated)),
 CSSMOID_SerialNumber __attribute__((deprecated)),
 CSSMOID_CountryName __attribute__((deprecated)),
 CSSMOID_LocalityName __attribute__((deprecated)),
 CSSMOID_StateProvinceName __attribute__((deprecated)),
 CSSMOID_CollectiveStateProvinceName __attribute__((deprecated)),
 CSSMOID_StreetAddress __attribute__((deprecated)),
 CSSMOID_CollectiveStreetAddress __attribute__((deprecated)),
 CSSMOID_OrganizationName __attribute__((deprecated)),
 CSSMOID_CollectiveOrganizationName __attribute__((deprecated)),
 CSSMOID_OrganizationalUnitName __attribute__((deprecated)),
 CSSMOID_CollectiveOrganizationalUnitName __attribute__((deprecated)),
 CSSMOID_Title __attribute__((deprecated)),
 CSSMOID_Description __attribute__((deprecated)),
 CSSMOID_SearchGuide __attribute__((deprecated)),
 CSSMOID_BusinessCategory __attribute__((deprecated)),
 CSSMOID_PostalAddress __attribute__((deprecated)),
 CSSMOID_CollectivePostalAddress __attribute__((deprecated)),
 CSSMOID_PostalCode __attribute__((deprecated)),
 CSSMOID_CollectivePostalCode __attribute__((deprecated)),
 CSSMOID_PostOfficeBox __attribute__((deprecated)),
 CSSMOID_CollectivePostOfficeBox __attribute__((deprecated)),
 CSSMOID_PhysicalDeliveryOfficeName __attribute__((deprecated)),
 CSSMOID_CollectivePhysicalDeliveryOfficeName __attribute__((deprecated)),
 CSSMOID_TelephoneNumber __attribute__((deprecated)),
 CSSMOID_CollectiveTelephoneNumber __attribute__((deprecated)),
 CSSMOID_TelexNumber __attribute__((deprecated)),
 CSSMOID_CollectiveTelexNumber __attribute__((deprecated)),
 CSSMOID_TelexTerminalIdentifier __attribute__((deprecated)),
 CSSMOID_CollectiveTelexTerminalIdentifier __attribute__((deprecated)),
 CSSMOID_FacsimileTelephoneNumber __attribute__((deprecated)),
 CSSMOID_CollectiveFacsimileTelephoneNumber __attribute__((deprecated)),
 CSSMOID_X_121Address __attribute__((deprecated)),
 CSSMOID_InternationalISDNNumber __attribute__((deprecated)),
 CSSMOID_CollectiveInternationalISDNNumber __attribute__((deprecated)),
 CSSMOID_RegisteredAddress __attribute__((deprecated)),
 CSSMOID_DestinationIndicator __attribute__((deprecated)),
 CSSMOID_PreferredDeliveryMethod __attribute__((deprecated)),
 CSSMOID_PresentationAddress __attribute__((deprecated)),
 CSSMOID_SupportedApplicationContext __attribute__((deprecated)),
 CSSMOID_Member __attribute__((deprecated)),
 CSSMOID_Owner __attribute__((deprecated)),
 CSSMOID_RoleOccupant __attribute__((deprecated)),
 CSSMOID_SeeAlso __attribute__((deprecated)),
 CSSMOID_UserPassword __attribute__((deprecated)),
 CSSMOID_UserCertificate __attribute__((deprecated)),
 CSSMOID_CACertificate __attribute__((deprecated)),
 CSSMOID_AuthorityRevocationList __attribute__((deprecated)),
 CSSMOID_CertificateRevocationList __attribute__((deprecated)),
 CSSMOID_CrossCertificatePair __attribute__((deprecated)),
 CSSMOID_Name __attribute__((deprecated)),
 CSSMOID_GivenName __attribute__((deprecated)),
 CSSMOID_Initials __attribute__((deprecated)),
 CSSMOID_GenerationQualifier __attribute__((deprecated)),
 CSSMOID_UniqueIdentifier __attribute__((deprecated)),
 CSSMOID_DNQualifier __attribute__((deprecated)),
 CSSMOID_EnhancedSearchGuide __attribute__((deprecated)),
 CSSMOID_ProtocolInformation __attribute__((deprecated)),
 CSSMOID_DistinguishedName __attribute__((deprecated)),
 CSSMOID_UniqueMember __attribute__((deprecated)),
 CSSMOID_HouseIdentifier __attribute__((deprecated));


extern const CSSM_OID
 CSSMOID_EmailAddress __attribute__((deprecated)),
 CSSMOID_UnstructuredName __attribute__((deprecated)),
 CSSMOID_ContentType __attribute__((deprecated)),
 CSSMOID_MessageDigest __attribute__((deprecated)),
 CSSMOID_SigningTime __attribute__((deprecated)),
 CSSMOID_CounterSignature __attribute__((deprecated)),
 CSSMOID_ChallengePassword __attribute__((deprecated)),
 CSSMOID_UnstructuredAddress __attribute__((deprecated)),
 CSSMOID_ExtendedCertificateAttributes __attribute__((deprecated));


extern const CSSM_OID
 CSSMOID_QT_CPS __attribute__((deprecated)),
 CSSMOID_QT_UNOTICE __attribute__((deprecated)),
 CSSMOID_AD_OCSP __attribute__((deprecated)),
 CSSMOID_AD_CA_ISSUERS __attribute__((deprecated)),
 CSSMOID_AD_TIME_STAMPING __attribute__((deprecated)),
 CSSMOID_AD_CA_REPOSITORY __attribute__((deprecated)),
 CSSMOID_PDA_DATE_OF_BIRTH __attribute__((deprecated)),
 CSSMOID_PDA_PLACE_OF_BIRTH __attribute__((deprecated)),
 CSSMOID_PDA_GENDER __attribute__((deprecated)),
 CSSMOID_PDA_COUNTRY_CITIZEN __attribute__((deprecated)),
 CSSMOID_PDA_COUNTRY_RESIDENCE __attribute__((deprecated)),
 CSSMOID_OID_QCS_SYNTAX_V1 __attribute__((deprecated)),
 CSSMOID_OID_QCS_SYNTAX_V2 __attribute__((deprecated));


extern const CSSM_OID
 CSSMOID_ETSI_QCS_QC_COMPLIANCE __attribute__((deprecated)),
 CSSMOID_ETSI_QCS_QC_LIMIT_VALUE __attribute__((deprecated)),
 CSSMOID_ETSI_QCS_QC_RETENTION __attribute__((deprecated)),
 CSSMOID_ETSI_QCS_QC_SSCD __attribute__((deprecated));


extern const CSSM_OID
 CSSMOID_PKCS7_Data __attribute__((deprecated)),
 CSSMOID_PKCS7_SignedData __attribute__((deprecated)),
 CSSMOID_PKCS7_EnvelopedData __attribute__((deprecated)),
 CSSMOID_PKCS7_SignedAndEnvelopedData __attribute__((deprecated)),
 CSSMOID_PKCS7_DigestedData __attribute__((deprecated)),
 CSSMOID_PKCS7_EncryptedData __attribute__((deprecated)),
 CSSMOID_PKCS7_DataWithAttributes __attribute__((deprecated)),
 CSSMOID_PKCS7_EncryptedPrivateKeyInfo __attribute__((deprecated)),


 CSSMOID_PKCS9_FriendlyName __attribute__((deprecated)),
 CSSMOID_PKCS9_LocalKeyId __attribute__((deprecated)),
 CSSMOID_PKCS9_CertTypes __attribute__((deprecated)),
 CSSMOID_PKCS9_CrlTypes __attribute__((deprecated)),
 CSSMOID_PKCS9_X509Certificate __attribute__((deprecated)),
 CSSMOID_PKCS9_SdsiCertificate __attribute__((deprecated)),
 CSSMOID_PKCS9_X509Crl __attribute__((deprecated)),


 CSSMOID_PKCS12_keyBag __attribute__((deprecated)),
 CSSMOID_PKCS12_shroudedKeyBag __attribute__((deprecated)),
 CSSMOID_PKCS12_certBag __attribute__((deprecated)),
 CSSMOID_PKCS12_crlBag __attribute__((deprecated)),
 CSSMOID_PKCS12_secretBag __attribute__((deprecated)),
 CSSMOID_PKCS12_safeContentsBag __attribute__((deprecated)),


 CSSMOID_UserID __attribute__((deprecated)),


 CSSMOID_DomainComponent __attribute__((deprecated)),


 CSSMOID_KERBv5_PKINIT_AUTH_DATA __attribute__((deprecated)),
 CSSMOID_KERBv5_PKINIT_DH_KEY_DATA __attribute__((deprecated)),
 CSSMOID_KERBv5_PKINIT_RKEY_DATA __attribute__((deprecated));


extern const CSSM_OID
 CSSMOID_X9_62 __attribute__((deprecated)),
 CSSMOID_X9_62_FieldType __attribute__((deprecated)),
 CSSMOID_X9_62_PubKeyType __attribute__((deprecated)),
 CSSMOID_X9_62_EllCurve __attribute__((deprecated)),
 CSSMOID_X9_62_C_TwoCurve __attribute__((deprecated)),
 CSSMOID_X9_62_PrimeCurve __attribute__((deprecated)),
 CSSMOID_X9_62_SigType __attribute__((deprecated)),
 CSSMOID_secp192r1 __attribute__((deprecated)),
 CSSMOID_secp256r1 __attribute__((deprecated)),
 CSSMOID_Certicom __attribute__((deprecated)),
 CSSMOID_CerticomEllCurve __attribute__((deprecated)),
 CSSMOID_secp112r1 __attribute__((deprecated)),
 CSSMOID_secp112r2 __attribute__((deprecated)),
 CSSMOID_secp128r1 __attribute__((deprecated)),
 CSSMOID_secp128r2 __attribute__((deprecated)),
 CSSMOID_secp160k1 __attribute__((deprecated)),
 CSSMOID_secp160r1 __attribute__((deprecated)),
 CSSMOID_secp160r2 __attribute__((deprecated)),
 CSSMOID_secp192k1 __attribute__((deprecated)),
 CSSMOID_secp224k1 __attribute__((deprecated)),
 CSSMOID_secp224r1 __attribute__((deprecated)),
 CSSMOID_secp256k1 __attribute__((deprecated)),
 CSSMOID_secp384r1 __attribute__((deprecated)),
 CSSMOID_secp521r1 __attribute__((deprecated)),
 CSSMOID_sect113r1 __attribute__((deprecated)),
 CSSMOID_sect113r2 __attribute__((deprecated)),
 CSSMOID_sect131r1 __attribute__((deprecated)),
 CSSMOID_sect131r2 __attribute__((deprecated)),
 CSSMOID_sect163k1 __attribute__((deprecated)),
 CSSMOID_sect163r1 __attribute__((deprecated)),
 CSSMOID_sect163r2 __attribute__((deprecated)),
 CSSMOID_sect193r1 __attribute__((deprecated)),
 CSSMOID_sect193r2 __attribute__((deprecated)),
 CSSMOID_sect233k1 __attribute__((deprecated)),
 CSSMOID_sect233r1 __attribute__((deprecated)),
 CSSMOID_sect239k1 __attribute__((deprecated)),
 CSSMOID_sect283k1 __attribute__((deprecated)),
 CSSMOID_sect283r1 __attribute__((deprecated)),
 CSSMOID_sect409k1 __attribute__((deprecated)),
 CSSMOID_sect409r1 __attribute__((deprecated)),
 CSSMOID_sect571k1 __attribute__((deprecated)),
 CSSMOID_sect571r1 __attribute__((deprecated));
# 45 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3

# 1 "/System/Library/Frameworks/Security.framework/Headers/oidscert.h" 1 3
# 55 "/System/Library/Frameworks/Security.framework/Headers/oidscert.h" 3
extern const CSSM_OID

 CSSMOID_X509V3SignedCertificate __attribute__((deprecated)),
 CSSMOID_X509V3SignedCertificateCStruct __attribute__((deprecated)),
 CSSMOID_X509V3Certificate __attribute__((deprecated)),
 CSSMOID_X509V3CertificateCStruct __attribute__((deprecated)),
 CSSMOID_X509V1Version __attribute__((deprecated)),
 CSSMOID_X509V1SerialNumber __attribute__((deprecated)),
 CSSMOID_X509V1IssuerName __attribute__((deprecated)),
 CSSMOID_X509V1IssuerNameStd __attribute__((deprecated)),
 CSSMOID_X509V1IssuerNameCStruct __attribute__((deprecated)),
 CSSMOID_X509V1IssuerNameLDAP __attribute__((deprecated)),
 CSSMOID_X509V1ValidityNotBefore __attribute__((deprecated)),
 CSSMOID_X509V1ValidityNotAfter __attribute__((deprecated)),
 CSSMOID_X509V1SubjectName __attribute__((deprecated)),
 CSSMOID_X509V1SubjectNameStd __attribute__((deprecated)),
 CSSMOID_X509V1SubjectNameCStruct __attribute__((deprecated)),
 CSSMOID_X509V1SubjectNameLDAP __attribute__((deprecated)),
 CSSMOID_CSSMKeyStruct __attribute__((deprecated)),
 CSSMOID_X509V1SubjectPublicKeyCStruct __attribute__((deprecated)),
 CSSMOID_X509V1SubjectPublicKeyAlgorithm __attribute__((deprecated)),
 CSSMOID_X509V1SubjectPublicKeyAlgorithmParameters __attribute__((deprecated)),
 CSSMOID_X509V1SubjectPublicKey __attribute__((deprecated)),
 CSSMOID_X509V1CertificateIssuerUniqueId __attribute__((deprecated)),
 CSSMOID_X509V1CertificateSubjectUniqueId __attribute__((deprecated)),
 CSSMOID_X509V3CertificateExtensionsStruct __attribute__((deprecated)),
 CSSMOID_X509V3CertificateExtensionsCStruct __attribute__((deprecated)),
 CSSMOID_X509V3CertificateNumberOfExtensions __attribute__((deprecated)),
 CSSMOID_X509V3CertificateExtensionStruct __attribute__((deprecated)),
 CSSMOID_X509V3CertificateExtensionCStruct __attribute__((deprecated)),
 CSSMOID_X509V3CertificateExtensionId __attribute__((deprecated)),
 CSSMOID_X509V3CertificateExtensionCritical __attribute__((deprecated)),
 CSSMOID_X509V3CertificateExtensionType __attribute__((deprecated)),
 CSSMOID_X509V3CertificateExtensionValue __attribute__((deprecated)),


 CSSMOID_X509V1SignatureStruct __attribute__((deprecated)),
 CSSMOID_X509V1SignatureCStruct __attribute__((deprecated)),
 CSSMOID_X509V1SignatureAlgorithm __attribute__((deprecated)),
 CSSMOID_X509V1SignatureAlgorithmTBS __attribute__((deprecated)),
 CSSMOID_X509V1SignatureAlgorithmParameters __attribute__((deprecated)),
 CSSMOID_X509V1Signature __attribute__((deprecated)),


 CSSMOID_SubjectSignatureBitmap __attribute__((deprecated)),
 CSSMOID_SubjectPicture __attribute__((deprecated)),
 CSSMOID_SubjectEmailAddress __attribute__((deprecated)),
 CSSMOID_UseExemptions __attribute__((deprecated));
# 111 "/System/Library/Frameworks/Security.framework/Headers/oidscert.h" 3
extern const CSSM_OID
 CSSMOID_SubjectDirectoryAttributes __attribute__((deprecated)),
 CSSMOID_SubjectKeyIdentifier __attribute__((deprecated)),
 CSSMOID_KeyUsage __attribute__((deprecated)),
 CSSMOID_PrivateKeyUsagePeriod __attribute__((deprecated)),
 CSSMOID_SubjectAltName __attribute__((deprecated)),
 CSSMOID_IssuerAltName __attribute__((deprecated)),
 CSSMOID_BasicConstraints __attribute__((deprecated)),
 CSSMOID_CrlNumber __attribute__((deprecated)),
 CSSMOID_CrlReason __attribute__((deprecated)),
 CSSMOID_HoldInstructionCode __attribute__((deprecated)),
 CSSMOID_InvalidityDate __attribute__((deprecated)),
 CSSMOID_DeltaCrlIndicator __attribute__((deprecated)),
 CSSMOID_IssuingDistributionPoint __attribute__((deprecated)),
 CSSMOID_IssuingDistributionPoints __attribute__((deprecated)),
 CSSMOID_CertIssuer __attribute__((deprecated)),
 CSSMOID_NameConstraints __attribute__((deprecated)),
 CSSMOID_CrlDistributionPoints __attribute__((deprecated)),
 CSSMOID_CertificatePolicies __attribute__((deprecated)),
 CSSMOID_PolicyMappings __attribute__((deprecated)),
 CSSMOID_PolicyConstraints __attribute__((deprecated)),
 CSSMOID_AuthorityKeyIdentifier __attribute__((deprecated)),
 CSSMOID_ExtendedKeyUsage __attribute__((deprecated)),
 CSSMOID_InhibitAnyPolicy __attribute__((deprecated)),
 CSSMOID_AuthorityInfoAccess __attribute__((deprecated)),
 CSSMOID_BiometricInfo __attribute__((deprecated)),
 CSSMOID_QC_Statements __attribute__((deprecated)),
 CSSMOID_SubjectInfoAccess __attribute__((deprecated)),
 CSSMOID_ExtendedKeyUsageAny __attribute__((deprecated)),
 CSSMOID_ServerAuth __attribute__((deprecated)),
 CSSMOID_ClientAuth __attribute__((deprecated)),
 CSSMOID_ExtendedUseCodeSigning __attribute__((deprecated)),
 CSSMOID_EmailProtection __attribute__((deprecated)),
 CSSMOID_TimeStamping __attribute__((deprecated)),
 CSSMOID_OCSPSigning __attribute__((deprecated)),
 CSSMOID_KERBv5_PKINIT_KP_CLIENT_AUTH __attribute__((deprecated)),
 CSSMOID_KERBv5_PKINIT_KP_KDC __attribute__((deprecated)),
 CSSMOID_EKU_IPSec __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_EXTENSION __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_IDENTITY __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_EMAIL_SIGN __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_EMAIL_ENCRYPT __attribute__((deprecated)),
 CSSMOID_APPLE_CERT_POLICY __attribute__((deprecated)),
 CSSMOID_DOTMAC_CERT_POLICY __attribute__((deprecated)),
 CSSMOID_ADC_CERT_POLICY __attribute__((deprecated)),
 CSSMOID_MACAPPSTORE_CERT_POLICY __attribute__((deprecated)),
 CSSMOID_MACAPPSTORE_RECEIPT_CERT_POLICY __attribute__((deprecated)),
 CSSMOID_APPLEID_CERT_POLICY __attribute__((deprecated)),
 CSSMOID_APPLEID_SHARING_CERT_POLICY __attribute__((deprecated)),
 CSSMOID_APPLE_EKU_CODE_SIGNING __attribute__((deprecated)),
 CSSMOID_APPLE_EKU_CODE_SIGNING_DEV __attribute__((deprecated)),
 CSSMOID_APPLE_EKU_RESOURCE_SIGNING __attribute__((deprecated)),
 CSSMOID_APPLE_EKU_ICHAT_SIGNING __attribute__((deprecated)),
 CSSMOID_APPLE_EKU_ICHAT_ENCRYPTION __attribute__((deprecated)),
 CSSMOID_APPLE_EKU_SYSTEM_IDENTITY __attribute__((deprecated)),
 CSSMOID_APPLE_EXTENSION __attribute__((deprecated)),
 CSSMOID_APPLE_EXTENSION_CODE_SIGNING __attribute__((deprecated)),
 CSSMOID_APPLE_EXTENSION_APPLE_SIGNING __attribute__((deprecated)),
 CSSMOID_APPLE_EXTENSION_ADC_DEV_SIGNING __attribute__((deprecated)),
 CSSMOID_APPLE_EXTENSION_ADC_APPLE_SIGNING __attribute__((deprecated)),
 CSSMOID_APPLE_EXTENSION_MACAPPSTORE_RECEIPT __attribute__((deprecated)),
 CSSMOID_APPLE_EXTENSION_INTERMEDIATE_MARKER __attribute__((deprecated)),
 CSSMOID_APPLE_EXTENSION_WWDR_INTERMEDIATE __attribute__((deprecated)),
 CSSMOID_APPLE_EXTENSION_ITMS_INTERMEDIATE __attribute__((deprecated)),
 CSSMOID_APPLE_EXTENSION_AAI_INTERMEDIATE __attribute__((deprecated)),
 CSSMOID_APPLE_EXTENSION_APPLEID_SHARING __attribute__((deprecated))
;




extern const CSSM_OID
 CSSMOID_NetscapeCertType __attribute__((deprecated)),
 CSSMOID_NetscapeCertSequence __attribute__((deprecated)),
 CSSMOID_NetscapeSGC __attribute__((deprecated));

extern const CSSM_OID CSSMOID_MicrosoftSGC __attribute__((deprecated));
# 47 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/oidscrl.h" 1 3
# 41 "/System/Library/Frameworks/Security.framework/Headers/oidscrl.h" 3
extern const CSSM_OID

 CSSMOID_X509V2CRLSignedCrlStruct __attribute__((deprecated)),
 CSSMOID_X509V2CRLSignedCrlCStruct __attribute__((deprecated)),
 CSSMOID_X509V2CRLTbsCertListStruct __attribute__((deprecated)),
 CSSMOID_X509V2CRLTbsCertListCStruct __attribute__((deprecated)),
 CSSMOID_X509V2CRLVersion __attribute__((deprecated)),
 CSSMOID_X509V1CRLIssuerStruct __attribute__((deprecated)),
 CSSMOID_X509V1CRLIssuerNameCStruct __attribute__((deprecated)),
 CSSMOID_X509V1CRLIssuerNameLDAP __attribute__((deprecated)),
 CSSMOID_X509V1CRLThisUpdate __attribute__((deprecated)),
 CSSMOID_X509V1CRLNextUpdate __attribute__((deprecated)),


 CSSMOID_X509V1CRLRevokedCertificatesStruct __attribute__((deprecated)),
 CSSMOID_X509V1CRLRevokedCertificatesCStruct __attribute__((deprecated)),
 CSSMOID_X509V1CRLNumberOfRevokedCertEntries __attribute__((deprecated)),
 CSSMOID_X509V1CRLRevokedEntryStruct __attribute__((deprecated)),
 CSSMOID_X509V1CRLRevokedEntryCStruct __attribute__((deprecated)),
 CSSMOID_X509V1CRLRevokedEntrySerialNumber __attribute__((deprecated)),
 CSSMOID_X509V1CRLRevokedEntryRevocationDate __attribute__((deprecated)),


 CSSMOID_X509V2CRLRevokedEntryAllExtensionsStruct __attribute__((deprecated)),
 CSSMOID_X509V2CRLRevokedEntryAllExtensionsCStruct __attribute__((deprecated)),
 CSSMOID_X509V2CRLRevokedEntryNumberOfExtensions __attribute__((deprecated)),
 CSSMOID_X509V2CRLRevokedEntrySingleExtensionStruct __attribute__((deprecated)),
 CSSMOID_X509V2CRLRevokedEntrySingleExtensionCStruct __attribute__((deprecated)),
 CSSMOID_X509V2CRLRevokedEntryExtensionId __attribute__((deprecated)),
 CSSMOID_X509V2CRLRevokedEntryExtensionCritical __attribute__((deprecated)),
 CSSMOID_X509V2CRLRevokedEntryExtensionType __attribute__((deprecated)),
 CSSMOID_X509V2CRLRevokedEntryExtensionValue __attribute__((deprecated)),


 CSSMOID_X509V2CRLAllExtensionsStruct __attribute__((deprecated)),
 CSSMOID_X509V2CRLAllExtensionsCStruct __attribute__((deprecated)),
 CSSMOID_X509V2CRLNumberOfExtensions __attribute__((deprecated)),
 CSSMOID_X509V2CRLSingleExtensionStruct __attribute__((deprecated)),
 CSSMOID_X509V2CRLSingleExtensionCStruct __attribute__((deprecated)),
 CSSMOID_X509V2CRLExtensionId __attribute__((deprecated)),
 CSSMOID_X509V2CRLExtensionCritical __attribute__((deprecated)),
 CSSMOID_X509V2CRLExtensionType __attribute__((deprecated)),


 CSSMOID_PKIX_OCSP __attribute__((deprecated)),
 CSSMOID_PKIX_OCSP_BASIC __attribute__((deprecated)),
 CSSMOID_PKIX_OCSP_NONCE __attribute__((deprecated)),
 CSSMOID_PKIX_OCSP_CRL __attribute__((deprecated)),
 CSSMOID_PKIX_OCSP_RESPONSE __attribute__((deprecated)),
 CSSMOID_PKIX_OCSP_NOCHECK __attribute__((deprecated)),
 CSSMOID_PKIX_OCSP_ARCHIVE_CUTOFF __attribute__((deprecated)),
 CSSMOID_PKIX_OCSP_SERVICE_LOCATOR __attribute__((deprecated));
# 48 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3


# 1 "/System/Library/Frameworks/Security.framework/Headers/SecBase.h" 1 3
# 45 "/System/Library/Frameworks/Security.framework/Headers/SecBase.h" 3
typedef struct OpaqueSecKeychainRef *SecKeychainRef;





typedef struct OpaqueSecKeychainItemRef *SecKeychainItemRef;





typedef struct OpaqueSecKeychainSearchRef *SecKeychainSearchRef;





typedef OSType SecKeychainAttrType;
# 72 "/System/Library/Frameworks/Security.framework/Headers/SecBase.h" 3
struct SecKeychainAttribute
{
    SecKeychainAttrType tag;
    UInt32 length;
    void *data;
};
typedef struct SecKeychainAttribute SecKeychainAttribute;





typedef SecKeychainAttribute *SecKeychainAttributePtr;







struct SecKeychainAttributeList
{
    UInt32 count;
    SecKeychainAttribute *attr;
};
typedef struct SecKeychainAttributeList SecKeychainAttributeList;





typedef UInt32 SecKeychainStatus;






typedef struct OpaqueSecTrustedApplicationRef *SecTrustedApplicationRef;





typedef struct OpaqueSecPolicyRef *SecPolicyRef;





typedef struct OpaqueSecCertificateRef *SecCertificateRef;





typedef struct OpaqueSecAccessRef *SecAccessRef;





typedef struct OpaqueSecIdentityRef *SecIdentityRef;





typedef struct OpaqueSecKeyRef *SecKeyRef;





typedef struct OpaqueSecTrustRef *SecACLRef;





typedef struct OpaqueSecPasswordRef *SecPasswordRef;
# 162 "/System/Library/Frameworks/Security.framework/Headers/SecBase.h" 3
struct SecKeychainAttributeInfo
{
    UInt32 count;
    UInt32 *tag;
 UInt32 *format;
};
typedef struct SecKeychainAttributeInfo SecKeychainAttributeInfo;
# 177 "/System/Library/Frameworks/Security.framework/Headers/SecBase.h" 3
CFStringRef SecCopyErrorMessageString(OSStatus status, void *reserved);
# 241 "/System/Library/Frameworks/Security.framework/Headers/SecBase.h" 3
enum
{
    errSecSuccess = 0,
    errSecUnimplemented = -4,
    errSecParam = -50,
    errSecAllocate = -108,

    errSecNotAvailable = -25291,
    errSecReadOnly = -25292,
    errSecAuthFailed = -25293,
    errSecNoSuchKeychain = -25294,
    errSecInvalidKeychain = -25295,
    errSecDuplicateKeychain = -25296,
    errSecDuplicateCallback = -25297,
    errSecInvalidCallback = -25298,
    errSecDuplicateItem = -25299,
    errSecItemNotFound = -25300,
    errSecBufferTooSmall = -25301,
    errSecDataTooLarge = -25302,
    errSecNoSuchAttr = -25303,
    errSecInvalidItemRef = -25304,
    errSecInvalidSearchRef = -25305,
    errSecNoSuchClass = -25306,
    errSecNoDefaultKeychain = -25307,
    errSecInteractionNotAllowed = -25308,
    errSecReadOnlyAttr = -25309,
    errSecWrongSecVersion = -25310,
    errSecKeySizeNotAllowed = -25311,
    errSecNoStorageModule = -25312,
    errSecNoCertificateModule = -25313,
    errSecNoPolicyModule = -25314,
    errSecInteractionRequired = -25315,
    errSecDataNotAvailable = -25316,
    errSecDataNotModifiable = -25317,
    errSecCreateChainFailed = -25318,
    errSecInvalidPrefsDomain = -25319,

 errSecACLNotSimple = -25240,
 errSecPolicyNotFound = -25241,
 errSecInvalidTrustSetting = -25242,
 errSecNoAccessForItem = -25243,
 errSecInvalidOwnerEdit = -25244,
 errSecTrustNotAvailable = -25245,
 errSecUnsupportedFormat = -25256,
 errSecUnknownFormat = -25257,
 errSecKeyIsSensitive = -25258,
 errSecMultiplePrivKeys = -25259,
 errSecPassphraseRequired = -25260,
 errSecInvalidPasswordRef = -25261,
 errSecInvalidTrustSettings = -25262,
 errSecNoTrustSettings = -25263,
 errSecPkcs12VerifyFailure = -25264,
 errSecNotSigner = -26267,

 errSecDecode = -26275,

 errSecServiceNotAvailable = -67585,
 errSecInsufficientClientID = -67586,
 errSecDeviceReset = -67587,
 errSecDeviceFailed = -67588,
 errSecAppleAddAppACLSubject = -67589,
 errSecApplePublicKeyIncomplete = -67590,
 errSecAppleSignatureMismatch = -67591,
 errSecAppleInvalidKeyStartDate = -67592,
 errSecAppleInvalidKeyEndDate = -67593,
 errSecConversionError = -67594,
 errSecAppleSSLv2Rollback = -67595,
 errSecDiskFull = -34,
 errSecQuotaExceeded = -67596,
 errSecFileTooBig = -67597,
 errSecInvalidDatabaseBlob = -67598,
 errSecInvalidKeyBlob = -67599,
 errSecIncompatibleDatabaseBlob = -67600,
 errSecIncompatibleKeyBlob = -67601,
 errSecHostNameMismatch = -67602,
 errSecUnknownCriticalExtensionFlag = -67603,
 errSecNoBasicConstraints = -67604,
 errSecNoBasicConstraintsCA = -67605,
 errSecInvalidAuthorityKeyID = -67606,
 errSecInvalidSubjectKeyID = -67607,
 errSecInvalidKeyUsageForPolicy = -67608,
 errSecInvalidExtendedKeyUsage = -67609,
 errSecInvalidIDLinkage = -67610,
 errSecPathLengthConstraintExceeded = -67611,
 errSecInvalidRoot = -67612,
 errSecCRLExpired = -67613,
 errSecCRLNotValidYet = -67614,
 errSecCRLNotFound = -67615,
 errSecCRLServerDown = -67616,
 errSecCRLBadURI = -67617,
 errSecUnknownCertExtension = -67618,
 errSecUnknownCRLExtension = -67619,
 errSecCRLNotTrusted = -67620,
 errSecCRLPolicyFailed = -67621,
 errSecIDPFailure = -67622,
 errSecSMIMEEmailAddressesNotFound = -67623,
 errSecSMIMEBadExtendedKeyUsage = -67624,
 errSecSMIMEBadKeyUsage = -67625,
 errSecSMIMEKeyUsageNotCritical = -67626,
 errSecSMIMENoEmailAddress = -67627,
 errSecSMIMESubjAltNameNotCritical = -67628,
 errSecSSLBadExtendedKeyUsage = -67629,
 errSecOCSPBadResponse = -67630,
 errSecOCSPBadRequest = -67631,
 errSecOCSPUnavailable = -67632,
 errSecOCSPStatusUnrecognized = -67633,
 errSecEndOfData = -67634,
 errSecIncompleteCertRevocationCheck = -67635,
 errSecNetworkFailure = -67636,
 errSecOCSPNotTrustedToAnchor = -67637,
 errSecRecordModified = -67638,
 errSecOCSPSignatureError = -67639,
 errSecOCSPNoSigner = -67640,
 errSecOCSPResponderMalformedReq = -67641,
 errSecOCSPResponderInternalError = -67642,
 errSecOCSPResponderTryLater = -67643,
 errSecOCSPResponderSignatureRequired = -67644,
 errSecOCSPResponderUnauthorized = -67645,
 errSecOCSPResponseNonceMismatch = -67646,
 errSecCodeSigningBadCertChainLength = -67647,
 errSecCodeSigningNoBasicConstraints = -67648,
 errSecCodeSigningBadPathLengthConstraint= -67649,
 errSecCodeSigningNoExtendedKeyUsage = -67650,
 errSecCodeSigningDevelopment = -67651,
 errSecResourceSignBadCertChainLength = -67652,
 errSecResourceSignBadExtKeyUsage = -67653,
 errSecTrustSettingDeny = -67654,
 errSecInvalidSubjectName = -67655,
 errSecUnknownQualifiedCertStatement = -67656,
 errSecMobileMeRequestQueued = -67657,
 errSecMobileMeRequestRedirected = -67658,
 errSecMobileMeServerError = -67659,
 errSecMobileMeServerNotAvailable = -67660,
 errSecMobileMeServerAlreadyExists = -67661,
 errSecMobileMeServerServiceErr = -67662,
 errSecMobileMeRequestAlreadyPending = -67663,
 errSecMobileMeNoRequestPending = -67664,
 errSecMobileMeCSRVerifyFailure = -67665,
 errSecMobileMeFailedConsistencyCheck = -67666,
 errSecNotInitialized = -67667,
 errSecInvalidHandleUsage = -67668,
 errSecPVCReferentNotFound = -67669,
 errSecFunctionIntegrityFail = -67670,
 errSecInternalError = -67671,
 errSecMemoryError = -67672,
 errSecInvalidData = -67673,
 errSecMDSError = -67674,
 errSecInvalidPointer = -67675,
 errSecSelfCheckFailed = -67676,
 errSecFunctionFailed = -67677,
 errSecModuleManifestVerifyFailed = -67678,
 errSecInvalidGUID = -67679,
 errSecInvalidHandle = -67680,
 errSecInvalidDBList = -67681,
 errSecInvalidPassthroughID = -67682,
 errSecInvalidNetworkAddress = -67683,
 errSecCRLAlreadySigned = -67684,
 errSecInvalidNumberOfFields = -67685,
 errSecVerificationFailure = -67686,
 errSecUnknownTag = -67687,
 errSecInvalidSignature = -67688,
 errSecInvalidName = -67689,
 errSecInvalidCertificateRef = -67690,
 errSecInvalidCertificateGroup = -67691,
 errSecTagNotFound = -67692,
 errSecInvalidQuery = -67693,
 errSecInvalidValue = -67694,
 errSecCallbackFailed = -67695,
 errSecACLDeleteFailed = -67696,
 errSecACLReplaceFailed = -67697,
 errSecACLAddFailed = -67698,
 errSecACLChangeFailed = -67699,
 errSecInvalidAccessCredentials = -67700,
 errSecInvalidRecord = -67701,
 errSecInvalidACL = -67702,
 errSecInvalidSampleValue = -67703,
 errSecIncompatibleVersion = -67704,
 errSecPrivilegeNotGranted = -67705,
 errSecInvalidScope = -67706,
 errSecPVCAlreadyConfigured = -67707,
 errSecInvalidPVC = -67708,
 errSecEMMLoadFailed = -67709,
 errSecEMMUnloadFailed = -67710,
 errSecAddinLoadFailed = -67711,
 errSecInvalidKeyRef = -67712,
 errSecInvalidKeyHierarchy = -67713,
 errSecAddinUnloadFailed = -67714,
 errSecLibraryReferenceNotFound = -67715,
 errSecInvalidAddinFunctionTable = -67716,
 errSecInvalidServiceMask = -67717,
 errSecModuleNotLoaded = -67718,
 errSecInvalidSubServiceID = -67719,
 errSecAttributeNotInContext = -67720,
 errSecModuleManagerInitializeFailed = -67721,
 errSecModuleManagerNotFound = -67722,
 errSecEventNotificationCallbackNotFound = -67723,
 errSecInputLengthError = -67724,
 errSecOutputLengthError = -67725,
 errSecPrivilegeNotSupported = -67726,
 errSecDeviceError = -67727,
 errSecAttachHandleBusy = -67728,
 errSecNotLoggedIn = -67729,
 errSecAlgorithmMismatch = -67730,
 errSecKeyUsageIncorrect = -67731,
 errSecKeyBlobTypeIncorrect = -67732,
 errSecKeyHeaderInconsistent = -67733,
 errSecUnsupportedKeyFormat = -67734,
 errSecUnsupportedKeySize = -67735,
 errSecInvalidKeyUsageMask = -67736,
 errSecUnsupportedKeyUsageMask = -67737,
 errSecInvalidKeyAttributeMask = -67738,
 errSecUnsupportedKeyAttributeMask = -67739,
 errSecInvalidKeyLabel = -67740,
 errSecUnsupportedKeyLabel = -67741,
 errSecInvalidKeyFormat = -67742,
 errSecUnsupportedVectorOfBuffers = -67743,
 errSecInvalidInputVector = -67744,
 errSecInvalidOutputVector = -67745,
 errSecInvalidContext = -67746,
 errSecInvalidAlgorithm = -67747,
 errSecInvalidAttributeKey = -67748,
 errSecMissingAttributeKey = -67749,
 errSecInvalidAttributeInitVector = -67750,
 errSecMissingAttributeInitVector = -67751,
 errSecInvalidAttributeSalt = -67752,
 errSecMissingAttributeSalt = -67753,
 errSecInvalidAttributePadding = -67754,
 errSecMissingAttributePadding = -67755,
 errSecInvalidAttributeRandom = -67756,
 errSecMissingAttributeRandom = -67757,
 errSecInvalidAttributeSeed = -67758,
 errSecMissingAttributeSeed = -67759,
 errSecInvalidAttributePassphrase = -67760,
 errSecMissingAttributePassphrase = -67761,
 errSecInvalidAttributeKeyLength = -67762,
 errSecMissingAttributeKeyLength = -67763,
 errSecInvalidAttributeBlockSize = -67764,
 errSecMissingAttributeBlockSize = -67765,
 errSecInvalidAttributeOutputSize = -67766,
 errSecMissingAttributeOutputSize = -67767,
 errSecInvalidAttributeRounds = -67768,
 errSecMissingAttributeRounds = -67769,
 errSecInvalidAlgorithmParms = -67770,
 errSecMissingAlgorithmParms = -67771,
 errSecInvalidAttributeLabel = -67772,
 errSecMissingAttributeLabel = -67773,
 errSecInvalidAttributeKeyType = -67774,
 errSecMissingAttributeKeyType = -67775,
 errSecInvalidAttributeMode = -67776,
 errSecMissingAttributeMode = -67777,
 errSecInvalidAttributeEffectiveBits = -67778,
 errSecMissingAttributeEffectiveBits = -67779,
 errSecInvalidAttributeStartDate = -67780,
 errSecMissingAttributeStartDate = -67781,
 errSecInvalidAttributeEndDate = -67782,
 errSecMissingAttributeEndDate = -67783,
 errSecInvalidAttributeVersion = -67784,
 errSecMissingAttributeVersion = -67785,
 errSecInvalidAttributePrime = -67786,
 errSecMissingAttributePrime = -67787,
 errSecInvalidAttributeBase = -67788,
 errSecMissingAttributeBase = -67789,
 errSecInvalidAttributeSubprime = -67790,
 errSecMissingAttributeSubprime = -67791,
 errSecInvalidAttributeIterationCount = -67792,
 errSecMissingAttributeIterationCount = -67793,
 errSecInvalidAttributeDLDBHandle = -67794,
 errSecMissingAttributeDLDBHandle = -67795,
 errSecInvalidAttributeAccessCredentials = -67796,
 errSecMissingAttributeAccessCredentials = -67797,
 errSecInvalidAttributePublicKeyFormat = -67798,
 errSecMissingAttributePublicKeyFormat = -67799,
 errSecInvalidAttributePrivateKeyFormat = -67800,
 errSecMissingAttributePrivateKeyFormat = -67801,
 errSecInvalidAttributeSymmetricKeyFormat = -67802,
 errSecMissingAttributeSymmetricKeyFormat = -67803,
 errSecInvalidAttributeWrappedKeyFormat = -67804,
 errSecMissingAttributeWrappedKeyFormat = -67805,
 errSecStagedOperationInProgress = -67806,
 errSecStagedOperationNotStarted = -67807,
 errSecVerifyFailed = -67808,
 errSecQuerySizeUnknown = -67809,
 errSecBlockSizeMismatch = -67810,
 errSecPublicKeyInconsistent = -67811,
 errSecDeviceVerifyFailed = -67812,
 errSecInvalidLoginName = -67813,
 errSecAlreadyLoggedIn = -67814,
 errSecInvalidDigestAlgorithm = -67815,
 errSecInvalidCRLGroup = -67816,
 errSecCertificateCannotOperate = -67817,
 errSecCertificateExpired = -67818,
 errSecCertificateNotValidYet = -67819,
 errSecCertificateRevoked = -67820,
 errSecCertificateSuspended = -67821,
 errSecInsufficientCredentials = -67822,
 errSecInvalidAction = -67823,
 errSecInvalidAuthority = -67824,
 errSecVerifyActionFailed = -67825,
 errSecInvalidCertAuthority = -67826,
 errSecInvaldCRLAuthority = -67827,
 errSecInvalidCRLEncoding = -67828,
 errSecInvalidCRLType = -67829,
 errSecInvalidCRL = -67830,
 errSecInvalidFormType = -67831,
 errSecInvalidID = -67832,
 errSecInvalidIdentifier = -67833,
 errSecInvalidIndex = -67834,
 errSecInvalidPolicyIdentifiers = -67835,
 errSecInvalidTimeString = -67836,
 errSecInvalidReason = -67837,
 errSecInvalidRequestInputs = -67838,
 errSecInvalidResponseVector = -67839,
 errSecInvalidStopOnPolicy = -67840,
 errSecInvalidTuple = -67841,
 errSecMultipleValuesUnsupported = -67842,
 errSecNotTrusted = -67843,
 errSecNoDefaultAuthority = -67844,
 errSecRejectedForm = -67845,
 errSecRequestLost = -67846,
 errSecRequestRejected = -67847,
 errSecUnsupportedAddressType = -67848,
 errSecUnsupportedService = -67849,
 errSecInvalidTupleGroup = -67850,
 errSecInvalidBaseACLs = -67851,
 errSecInvalidTupleCredendtials = -67852,
 errSecInvalidEncoding = -67853,
 errSecInvalidValidityPeriod = -67854,
 errSecInvalidRequestor = -67855,
 errSecRequestDescriptor = -67856,
 errSecInvalidBundleInfo = -67857,
 errSecInvalidCRLIndex = -67858,
 errSecNoFieldValues = -67859,
 errSecUnsupportedFieldFormat = -67860,
 errSecUnsupportedIndexInfo = -67861,
 errSecUnsupportedLocality = -67862,
 errSecUnsupportedNumAttributes = -67863,
 errSecUnsupportedNumIndexes = -67864,
 errSecUnsupportedNumRecordTypes = -67865,
 errSecFieldSpecifiedMultiple = -67866,
 errSecIncompatibleFieldFormat = -67867,
 errSecInvalidParsingModule = -67868,
 errSecDatabaseLocked = -67869,
 errSecDatastoreIsOpen = -67870,
 errSecMissingValue = -67871,
 errSecUnsupportedQueryLimits = -67872,
 errSecUnsupportedNumSelectionPreds = -67873,
 errSecUnsupportedOperator = -67874,
 errSecInvalidDBLocation = -67875,
 errSecInvalidAccessRequest = -67876,
 errSecInvalidIndexInfo = -67877,
 errSecInvalidNewOwner = -67878,
 errSecInvalidModifyMode = -67879,
};
# 51 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecAccess.h" 1 3
# 47 "/System/Library/Frameworks/Security.framework/Headers/SecAccess.h" 3
typedef UInt32 SecAccessOwnerType;
enum
{
 kSecUseOnlyUID = 1,
 kSecUseOnlyGID = 2,
 kSecHonorRoot = 0x100,
 kSecMatchBits = (kSecUseOnlyUID | kSecUseOnlyGID)
};



extern CFTypeRef kSecACLAuthorizationAny
 __attribute__((visibility("default")));

extern CFTypeRef kSecACLAuthorizationLogin
 __attribute__((visibility("default")));
extern CFTypeRef kSecACLAuthorizationGenKey
 __attribute__((visibility("default")));
extern CFTypeRef kSecACLAuthorizationDelete
 __attribute__((visibility("default")));
extern CFTypeRef kSecACLAuthorizationExportWrapped
 __attribute__((visibility("default")));
extern CFTypeRef kSecACLAuthorizationExportClear
 __attribute__((visibility("default")));
extern CFTypeRef kSecACLAuthorizationImportWrapped
 __attribute__((visibility("default")));
extern CFTypeRef kSecACLAuthorizationImportClear
 __attribute__((visibility("default")));
extern CFTypeRef kSecACLAuthorizationSign
 __attribute__((visibility("default")));
extern CFTypeRef kSecACLAuthorizationEncrypt
 __attribute__((visibility("default")));
extern CFTypeRef kSecACLAuthorizationDecrypt
 __attribute__((visibility("default")));
extern CFTypeRef kSecACLAuthorizationMAC
 __attribute__((visibility("default")));
extern CFTypeRef kSecACLAuthorizationDerive
 __attribute__((visibility("default")));


extern CFTypeRef kSecACLAuthorizationKeychainCreate
 __attribute__((visibility("default")));
extern CFTypeRef kSecACLAuthorizationKeychainDelete
 __attribute__((visibility("default")));
extern CFTypeRef kSecACLAuthorizationKeychainItemRead
 __attribute__((visibility("default")));
extern CFTypeRef kSecACLAuthorizationKeychainItemInsert
 __attribute__((visibility("default")));
extern CFTypeRef kSecACLAuthorizationKeychainItemModify
 __attribute__((visibility("default")));
extern CFTypeRef kSecACLAuthorizationKeychainItemDelete
 __attribute__((visibility("default")));

extern CFTypeRef kSecACLAuthorizationChangeACL
 __attribute__((visibility("default")));
extern CFTypeRef kSecACLAuthorizationChangeOwner
 __attribute__((visibility("default")));







CFTypeID SecAccessGetTypeID(void);
# 126 "/System/Library/Frameworks/Security.framework/Headers/SecAccess.h" 3
OSStatus SecAccessCreate(CFStringRef descriptor, CFArrayRef trustedlist, SecAccessRef *accessRef);
# 138 "/System/Library/Frameworks/Security.framework/Headers/SecAccess.h" 3
OSStatus SecAccessCreateFromOwnerAndACL(const CSSM_ACL_OWNER_PROTOTYPE *owner, uint32 aclCount, const CSSM_ACL_ENTRY_INFO *acls, SecAccessRef *accessRef)
 __attribute__((deprecated));
# 151 "/System/Library/Frameworks/Security.framework/Headers/SecAccess.h" 3
SecAccessRef SecAccessCreateWithOwnerAndACL(uid_t userId, gid_t groupId, SecAccessOwnerType ownerType, CFArrayRef acls, CFErrorRef *error)
 __attribute__((visibility("default")));
# 164 "/System/Library/Frameworks/Security.framework/Headers/SecAccess.h" 3
OSStatus SecAccessGetOwnerAndACL(SecAccessRef accessRef, CSSM_ACL_OWNER_PROTOTYPE_PTR *owner, uint32 *aclCount, CSSM_ACL_ENTRY_INFO_PTR *acls)
 __attribute__((deprecated));
# 178 "/System/Library/Frameworks/Security.framework/Headers/SecAccess.h" 3
OSStatus SecAccessCopyOwnerAndACL(SecAccessRef accessRef, uid_t* userId, gid_t* groupId, SecAccessOwnerType* ownerType, CFArrayRef* aclList)
 __attribute__((visibility("default")));
# 188 "/System/Library/Frameworks/Security.framework/Headers/SecAccess.h" 3
OSStatus SecAccessCopyACLList(SecAccessRef accessRef, CFArrayRef *aclList);
# 199 "/System/Library/Frameworks/Security.framework/Headers/SecAccess.h" 3
OSStatus SecAccessCopySelectedACLList(SecAccessRef accessRef, CSSM_ACL_AUTHORIZATION_TAG action, CFArrayRef *aclList)
 __attribute__((deprecated));
# 210 "/System/Library/Frameworks/Security.framework/Headers/SecAccess.h" 3
CFArrayRef SecAccessCopyMatchingACLList(SecAccessRef accessRef, CFTypeRef authorizationTag)
 __attribute__((visibility("default")));
# 52 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecACL.h" 1 3
# 43 "/System/Library/Frameworks/Security.framework/Headers/SecACL.h" 3
 typedef uint16 SecKeychainPromptSelector;
 enum
 {
  kSecKeychainPromptRequirePassphase = 0x0001,

  kSecKeychainPromptUnsigned = 0x0010,
  kSecKeychainPromptUnsignedAct = 0x0020,
  kSecKeychainPromptInvalid = 0x0040,
  kSecKeychainPromptInvalidAct = 0x0080,
 };







 CFTypeID SecACLGetTypeID(void)
 __attribute__((visibility("default")));
# 75 "/System/Library/Frameworks/Security.framework/Headers/SecACL.h" 3
 OSStatus SecACLCreateFromSimpleContents(SecAccessRef access,
           CFArrayRef applicationList,
           CFStringRef description, const CSSM_ACL_KEYCHAIN_PROMPT_SELECTOR *promptSelector,
           SecACLRef *newAcl)
  __attribute__((deprecated));
# 91 "/System/Library/Frameworks/Security.framework/Headers/SecACL.h" 3
 OSStatus SecACLCreateWithSimpleContents(SecAccessRef access,
           CFArrayRef applicationList,
           CFStringRef description,
           SecKeychainPromptSelector promptSelector,
           SecACLRef *newAcl)
 __attribute__((visibility("default")));







 OSStatus SecACLRemove(SecACLRef aclRef)
 __attribute__((visibility("default")));
# 118 "/System/Library/Frameworks/Security.framework/Headers/SecACL.h" 3
 OSStatus SecACLCopySimpleContents(SecACLRef acl,
           CFArrayRef *applicationList,
           CFStringRef *description, CSSM_ACL_KEYCHAIN_PROMPT_SELECTOR *promptSelector)
  __attribute__((deprecated));
# 132 "/System/Library/Frameworks/Security.framework/Headers/SecACL.h" 3
 OSStatus SecACLCopyContents(SecACLRef acl,
        CFArrayRef *applicationList,
        CFStringRef *description,
        SecKeychainPromptSelector *promptSelector)
 __attribute__((visibility("default")));
# 148 "/System/Library/Frameworks/Security.framework/Headers/SecACL.h" 3
 OSStatus SecACLSetSimpleContents(SecACLRef acl,
          CFArrayRef applicationList,
          CFStringRef description, const CSSM_ACL_KEYCHAIN_PROMPT_SELECTOR *promptSelector)
  __attribute__((deprecated));
# 162 "/System/Library/Frameworks/Security.framework/Headers/SecACL.h" 3
 OSStatus SecACLSetContents(SecACLRef acl,
          CFArrayRef applicationList,
          CFStringRef description,
          SecKeychainPromptSelector promptSelector)
 __attribute__((visibility("default")));
# 178 "/System/Library/Frameworks/Security.framework/Headers/SecACL.h" 3
 OSStatus SecACLGetAuthorizations(SecACLRef acl,
          CSSM_ACL_AUTHORIZATION_TAG *tags, uint32 *tagCount)
  __attribute__((deprecated));







 CFArrayRef SecACLCopyAuthorizations(SecACLRef acl)
 __attribute__((visibility("default")));
# 201 "/System/Library/Frameworks/Security.framework/Headers/SecACL.h" 3
 OSStatus SecACLSetAuthorizations(SecACLRef acl,
          CSSM_ACL_AUTHORIZATION_TAG *tags, uint32 tagCount)
  __attribute__((deprecated));
# 213 "/System/Library/Frameworks/Security.framework/Headers/SecACL.h" 3
 OSStatus SecACLUpdateAuthorizations(SecACLRef acl, CFArrayRef authorizations)
 __attribute__((visibility("default")));
# 53 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 1 3
# 64 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
enum
{
    kSecSubjectItemAttr = 'subj',
    kSecIssuerItemAttr = 'issu',
    kSecSerialNumberItemAttr = 'snbr',
    kSecPublicKeyHashItemAttr = 'hpky',
    kSecSubjectKeyIdentifierItemAttr = 'skid',
 kSecCertTypeItemAttr = 'ctyp',
 kSecCertEncodingItemAttr = 'cenc'
} ;






CFTypeID SecCertificateGetTypeID(void)
 __attribute__((visibility("default")));

       
# 95 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
OSStatus SecCertificateCreateFromData(const CSSM_DATA *data, CSSM_CERT_TYPE type, CSSM_CERT_ENCODING encoding, SecCertificateRef *certificate)
 __attribute__((deprecated));
# 105 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
SecCertificateRef SecCertificateCreateWithData(CFAllocatorRef allocator, CFDataRef data)
 __attribute__((visibility("default")));
# 117 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
OSStatus SecCertificateAddToKeychain(SecCertificateRef certificate, SecKeychainRef keychain)
 __attribute__((visibility("default")));
# 128 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
OSStatus SecCertificateGetData(SecCertificateRef certificate, CSSM_DATA_PTR data)
 __attribute__((deprecated));







CFDataRef SecCertificateCopyData(SecCertificateRef certificate)
 __attribute__((visibility("default")));
# 148 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
OSStatus SecCertificateGetType(SecCertificateRef certificate, CSSM_CERT_TYPE *certificateType)
 __attribute__((deprecated));
# 166 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
OSStatus SecCertificateGetSubject(SecCertificateRef certificate, const CSSM_X509_NAME **subject)
 __attribute__((deprecated));
# 184 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
OSStatus SecCertificateGetIssuer(SecCertificateRef certificate, const CSSM_X509_NAME **issuer)
 __attribute__((deprecated));
# 195 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
OSStatus SecCertificateGetCLHandle(SecCertificateRef certificate, CSSM_CL_HANDLE *clHandle)
 __attribute__((deprecated));
# 206 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
OSStatus SecCertificateGetAlgorithmID(SecCertificateRef certificate, const CSSM_X509_ALGORITHM_IDENTIFIER **algid)
 __attribute__((deprecated));
# 216 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
OSStatus SecCertificateCopyPublicKey(SecCertificateRef certificate, SecKeyRef *key)
 __attribute__((visibility("default")));
# 229 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
OSStatus SecCertificateCopyCommonName(SecCertificateRef certificate, CFStringRef *commonName)
 __attribute__((visibility("default")));
# 239 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
CFStringRef SecCertificateCopySubjectSummary(SecCertificateRef certificate)
 __attribute__((visibility("default")));
# 250 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
OSStatus SecCertificateCopyEmailAddresses(SecCertificateRef certificate, CFArrayRef *emailAddresses)
 __attribute__((visibility("default")));
# 263 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
OSStatus SecCertificateCopyPreference(CFStringRef name, uint32 keyUsage, SecCertificateRef *certificate)
 __attribute__((deprecated));
# 275 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
SecCertificateRef SecCertificateCopyPreferred(CFStringRef name, CFArrayRef keyUsage)
 __attribute__((visibility("default")));
# 289 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
OSStatus SecCertificateSetPreference(SecCertificateRef certificate, CFStringRef name, uint32 keyUsage, CFDateRef date)
 __attribute__((visibility("default")));
# 302 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
OSStatus SecCertificateSetPreferred(SecCertificateRef certificate, CFStringRef name, CFArrayRef keyUsage)
 __attribute__((visibility("default")));
# 314 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
extern CFStringRef kSecPropertyKeyType __attribute__((visibility("default")));
extern CFStringRef kSecPropertyKeyLabel __attribute__((visibility("default")));
extern CFStringRef kSecPropertyKeyLocalizedLabel __attribute__((visibility("default")));
extern CFStringRef kSecPropertyKeyValue __attribute__((visibility("default")));






extern CFStringRef kSecPropertyTypeWarning __attribute__((visibility("default")));
extern CFStringRef kSecPropertyTypeSuccess __attribute__((visibility("default")));
extern CFStringRef kSecPropertyTypeSection __attribute__((visibility("default")));
extern CFStringRef kSecPropertyTypeData __attribute__((visibility("default")));
extern CFStringRef kSecPropertyTypeString __attribute__((visibility("default")));
extern CFStringRef kSecPropertyTypeURL __attribute__((visibility("default")));
extern CFStringRef kSecPropertyTypeDate __attribute__((visibility("default")));
# 355 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
CFDictionaryRef SecCertificateCopyValues(SecCertificateRef certificate, CFArrayRef keys, CFErrorRef *error)
 __attribute__((visibility("default")));
# 369 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
extern const CFStringRef kSecCertificateUsageSigning __attribute__((visibility("default")));
extern const CFStringRef kSecCertificateUsageSigningAndEncrypting __attribute__((visibility("default")));
extern const CFStringRef kSecCertificateUsageDeriveAndSign __attribute__((visibility("default")));
# 390 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
CFStringRef SecCertificateCopyLongDescription(CFAllocatorRef alloc, SecCertificateRef certificate, CFErrorRef *error)
     __attribute__((visibility("default")));
# 410 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
CFStringRef SecCertificateCopyShortDescription(CFAllocatorRef alloc, SecCertificateRef certificate, CFErrorRef *error)
  __attribute__((visibility("default")));
# 425 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
CFDataRef SecCertificateCopySerialNumber(SecCertificateRef certificate, CFErrorRef *error)
  __attribute__((visibility("default")));
# 442 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
CFDataRef SecCertificateCopyNormalizedIssuerContent(SecCertificateRef certificate, CFErrorRef *error)
  __attribute__((visibility("default")));
# 459 "/System/Library/Frameworks/Security.framework/Headers/SecCertificate.h" 3
CFDataRef SecCertificateCopyNormalizedSubjectContent(SecCertificateRef certificate, CFErrorRef *error)
  __attribute__((visibility("default")));
# 54 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecCertificateOIDs.h" 1 3
# 41 "/System/Library/Frameworks/Security.framework/Headers/SecCertificateOIDs.h" 3
extern CFTypeRef kSecOIDADC_CERT_POLICY __attribute__((visibility("default")));
extern CFTypeRef kSecOIDAPPLE_CERT_POLICY __attribute__((visibility("default")));
extern CFTypeRef kSecOIDAPPLE_EKU_CODE_SIGNING __attribute__((visibility("default")));
extern CFTypeRef kSecOIDAPPLE_EKU_CODE_SIGNING_DEV __attribute__((visibility("default")));
extern CFTypeRef kSecOIDAPPLE_EKU_ICHAT_ENCRYPTION __attribute__((visibility("default")));
extern CFTypeRef kSecOIDAPPLE_EKU_ICHAT_SIGNING __attribute__((visibility("default")));
extern CFTypeRef kSecOIDAPPLE_EKU_RESOURCE_SIGNING __attribute__((visibility("default")));
extern CFTypeRef kSecOIDAPPLE_EKU_SYSTEM_IDENTITY __attribute__((visibility("default")));
extern CFTypeRef kSecOIDAPPLE_EXTENSION __attribute__((visibility("default")));
extern CFTypeRef kSecOIDAPPLE_EXTENSION_ADC_APPLE_SIGNING __attribute__((visibility("default")));
extern CFTypeRef kSecOIDAPPLE_EXTENSION_ADC_DEV_SIGNING __attribute__((visibility("default")));
extern CFTypeRef kSecOIDAPPLE_EXTENSION_APPLE_SIGNING __attribute__((visibility("default")));
extern CFTypeRef kSecOIDAPPLE_EXTENSION_CODE_SIGNING __attribute__((visibility("default")));
extern CFTypeRef kSecOIDAPPLE_EXTENSION_INTERMEDIATE_MARKER __attribute__((visibility("default")));
extern CFTypeRef kSecOIDAPPLE_EXTENSION_WWDR_INTERMEDIATE __attribute__((visibility("default")));
extern CFTypeRef kSecOIDAPPLE_EXTENSION_ITMS_INTERMEDIATE __attribute__((visibility("default")));
extern CFTypeRef kSecOIDAPPLE_EXTENSION_AAI_INTERMEDIATE __attribute__((visibility("default")));
extern CFTypeRef kSecOIDAuthorityInfoAccess __attribute__((visibility("default")));
extern CFTypeRef kSecOIDAuthorityKeyIdentifier __attribute__((visibility("default")));
extern CFTypeRef kSecOIDBasicConstraints __attribute__((visibility("default")));
extern CFTypeRef kSecOIDBiometricInfo __attribute__((visibility("default")));
extern CFTypeRef kSecOIDCSSMKeyStruct __attribute__((visibility("default")));
extern CFTypeRef kSecOIDCertIssuer __attribute__((visibility("default")));
extern CFTypeRef kSecOIDCertificatePolicies __attribute__((visibility("default")));
extern CFTypeRef kSecOIDClientAuth __attribute__((visibility("default")));
extern CFTypeRef kSecOIDCollectiveStateProvinceName __attribute__((visibility("default")));
extern CFTypeRef kSecOIDCollectiveStreetAddress __attribute__((visibility("default")));
extern CFTypeRef kSecOIDCommonName __attribute__((visibility("default")));
extern CFTypeRef kSecOIDCountryName __attribute__((visibility("default")));
extern CFTypeRef kSecOIDCrlDistributionPoints __attribute__((visibility("default")));
extern CFTypeRef kSecOIDCrlNumber __attribute__((visibility("default")));
extern CFTypeRef kSecOIDCrlReason __attribute__((visibility("default")));
extern CFTypeRef kSecOIDDOTMAC_CERT_EMAIL_ENCRYPT __attribute__((visibility("default")));
extern CFTypeRef kSecOIDDOTMAC_CERT_EMAIL_SIGN __attribute__((visibility("default")));
extern CFTypeRef kSecOIDDOTMAC_CERT_EXTENSION __attribute__((visibility("default")));
extern CFTypeRef kSecOIDDOTMAC_CERT_IDENTITY __attribute__((visibility("default")));
extern CFTypeRef kSecOIDDOTMAC_CERT_POLICY __attribute__((visibility("default")));
extern CFTypeRef kSecOIDDeltaCrlIndicator __attribute__((visibility("default")));
extern CFTypeRef kSecOIDDescription __attribute__((visibility("default")));
extern CFTypeRef kSecOIDEKU_IPSec __attribute__((visibility("default")));
extern CFTypeRef kSecOIDEmailAddress __attribute__((visibility("default")));
extern CFTypeRef kSecOIDEmailProtection __attribute__((visibility("default")));
extern CFTypeRef kSecOIDExtendedKeyUsage __attribute__((visibility("default")));
extern CFTypeRef kSecOIDExtendedKeyUsageAny __attribute__((visibility("default")));
extern CFTypeRef kSecOIDExtendedUseCodeSigning __attribute__((visibility("default")));
extern CFTypeRef kSecOIDGivenName __attribute__((visibility("default")));
extern CFTypeRef kSecOIDHoldInstructionCode __attribute__((visibility("default")));
extern CFTypeRef kSecOIDInvalidityDate __attribute__((visibility("default")));
extern CFTypeRef kSecOIDIssuerAltName __attribute__((visibility("default")));
extern CFTypeRef kSecOIDIssuingDistributionPoint __attribute__((visibility("default")));
extern CFTypeRef kSecOIDIssuingDistributionPoints __attribute__((visibility("default")));
extern CFTypeRef kSecOIDKERBv5_PKINIT_KP_CLIENT_AUTH __attribute__((visibility("default")));
extern CFTypeRef kSecOIDKERBv5_PKINIT_KP_KDC __attribute__((visibility("default")));
extern CFTypeRef kSecOIDKeyUsage __attribute__((visibility("default")));
extern CFTypeRef kSecOIDLocalityName __attribute__((visibility("default")));
extern CFTypeRef kSecOIDMS_NTPrincipalName __attribute__((visibility("default")));
extern CFTypeRef kSecOIDMicrosoftSGC __attribute__((visibility("default")));
extern CFTypeRef kSecOIDNameConstraints __attribute__((visibility("default")));
extern CFTypeRef kSecOIDNetscapeCertSequence __attribute__((visibility("default")));
extern CFTypeRef kSecOIDNetscapeCertType __attribute__((visibility("default")));
extern CFTypeRef kSecOIDNetscapeSGC __attribute__((visibility("default")));
extern CFTypeRef kSecOIDOCSPSigning __attribute__((visibility("default")));
extern CFTypeRef kSecOIDOrganizationName __attribute__((visibility("default")));
extern CFTypeRef kSecOIDOrganizationalUnitName __attribute__((visibility("default")));
extern CFTypeRef kSecOIDPolicyConstraints __attribute__((visibility("default")));
extern CFTypeRef kSecOIDPolicyMappings __attribute__((visibility("default")));
extern CFTypeRef kSecOIDPrivateKeyUsagePeriod __attribute__((visibility("default")));
extern CFTypeRef kSecOIDQC_Statements __attribute__((visibility("default")));
extern CFTypeRef kSecOIDSerialNumber __attribute__((visibility("default")));
extern CFTypeRef kSecOIDServerAuth __attribute__((visibility("default")));
extern CFTypeRef kSecOIDStateProvinceName __attribute__((visibility("default")));
extern CFTypeRef kSecOIDStreetAddress __attribute__((visibility("default")));
extern CFTypeRef kSecOIDSubjectAltName __attribute__((visibility("default")));
extern CFTypeRef kSecOIDSubjectDirectoryAttributes __attribute__((visibility("default")));
extern CFTypeRef kSecOIDSubjectEmailAddress __attribute__((visibility("default")));
extern CFTypeRef kSecOIDSubjectInfoAccess __attribute__((visibility("default")));
extern CFTypeRef kSecOIDSubjectKeyIdentifier __attribute__((visibility("default")));
extern CFTypeRef kSecOIDSubjectPicture __attribute__((visibility("default")));
extern CFTypeRef kSecOIDSubjectSignatureBitmap __attribute__((visibility("default")));
extern CFTypeRef kSecOIDSurname __attribute__((visibility("default")));
extern CFTypeRef kSecOIDTimeStamping __attribute__((visibility("default")));
extern CFTypeRef kSecOIDTitle __attribute__((visibility("default")));
extern CFTypeRef kSecOIDUseExemptions __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1CertificateIssuerUniqueId __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1CertificateSubjectUniqueId __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1IssuerName __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1IssuerNameCStruct __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1IssuerNameLDAP __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1IssuerNameStd __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1SerialNumber __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1Signature __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1SignatureAlgorithm __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1SignatureAlgorithmParameters __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1SignatureAlgorithmTBS __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1SignatureCStruct __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1SignatureStruct __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1SubjectName __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1SubjectNameCStruct __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1SubjectNameLDAP __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1SubjectNameStd __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1SubjectPublicKey __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1SubjectPublicKeyAlgorithm __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1SubjectPublicKeyAlgorithmParameters __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1SubjectPublicKeyCStruct __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1ValidityNotAfter __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1ValidityNotBefore __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V1Version __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V3Certificate __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V3CertificateCStruct __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V3CertificateExtensionCStruct __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V3CertificateExtensionCritical __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V3CertificateExtensionId __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V3CertificateExtensionStruct __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V3CertificateExtensionType __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V3CertificateExtensionValue __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V3CertificateExtensionsCStruct __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V3CertificateExtensionsStruct __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V3CertificateNumberOfExtensions __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V3SignedCertificate __attribute__((visibility("default")));
extern CFTypeRef kSecOIDX509V3SignedCertificateCStruct __attribute__((visibility("default")));
# 55 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecIdentity.h" 1 3
# 47 "/System/Library/Frameworks/Security.framework/Headers/SecIdentity.h" 3
CFTypeID SecIdentityGetTypeID(void)
 __attribute__((visibility("default")));
# 58 "/System/Library/Frameworks/Security.framework/Headers/SecIdentity.h" 3
OSStatus SecIdentityCreateWithCertificate(
   CFTypeRef keychainOrArray,
   SecCertificateRef certificateRef,
            SecIdentityRef *identityRef)
 __attribute__((visibility("default")));
# 71 "/System/Library/Frameworks/Security.framework/Headers/SecIdentity.h" 3
OSStatus SecIdentityCopyCertificate(
            SecIdentityRef identityRef,
            SecCertificateRef *certificateRef)
 __attribute__((visibility("default")));
# 83 "/System/Library/Frameworks/Security.framework/Headers/SecIdentity.h" 3
OSStatus SecIdentityCopyPrivateKey(
            SecIdentityRef identityRef,
            SecKeyRef *privateKeyRef)
 __attribute__((visibility("default")));
# 98 "/System/Library/Frameworks/Security.framework/Headers/SecIdentity.h" 3
OSStatus SecIdentityCopyPreference(CFStringRef name, CSSM_KEYUSE keyUsage, CFArrayRef validIssuers, SecIdentityRef *identity)
 __attribute__((deprecated));
# 111 "/System/Library/Frameworks/Security.framework/Headers/SecIdentity.h" 3
SecIdentityRef SecIdentityCopyPreferred(CFStringRef name, CFArrayRef keyUsage, CFArrayRef validIssuers)
 __attribute__((visibility("default")));
# 123 "/System/Library/Frameworks/Security.framework/Headers/SecIdentity.h" 3
OSStatus SecIdentitySetPreference(SecIdentityRef identity, CFStringRef name, CSSM_KEYUSE keyUsage)
 __attribute__((deprecated));
# 134 "/System/Library/Frameworks/Security.framework/Headers/SecIdentity.h" 3
OSStatus SecIdentitySetPreferred(SecIdentityRef identity, CFStringRef name, CFArrayRef keyUsage)
 __attribute__((visibility("default")));
# 155 "/System/Library/Frameworks/Security.framework/Headers/SecIdentity.h" 3
OSStatus SecIdentityCopySystemIdentity(
   CFStringRef domain,
   SecIdentityRef *idRef,
   CFStringRef *actualDomain)
 __attribute__((visibility("default")));
# 174 "/System/Library/Frameworks/Security.framework/Headers/SecIdentity.h" 3
OSStatus SecIdentitySetSystemIdentity(
   CFStringRef domain,
   SecIdentityRef idRef)
 __attribute__((visibility("default")));
# 187 "/System/Library/Frameworks/Security.framework/Headers/SecIdentity.h" 3
extern const CFStringRef kSecIdentityDomainDefault __attribute__((visibility("default")));




extern const CFStringRef kSecIdentityDomainKerberosKDC __attribute__((visibility("default")));
# 56 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecIdentitySearch.h" 1 3
# 48 "/System/Library/Frameworks/Security.framework/Headers/SecIdentitySearch.h" 3
typedef struct OpaqueSecIdentitySearchRef *SecIdentitySearchRef;







CFTypeID SecIdentitySearchGetTypeID(void)
  __attribute__((deprecated));
# 69 "/System/Library/Frameworks/Security.framework/Headers/SecIdentitySearch.h" 3
OSStatus SecIdentitySearchCreate(CFTypeRef keychainOrArray, CSSM_KEYUSE keyUsage, SecIdentitySearchRef *searchRef)
  __attribute__((deprecated));
# 80 "/System/Library/Frameworks/Security.framework/Headers/SecIdentitySearch.h" 3
OSStatus SecIdentitySearchCopyNext(SecIdentitySearchRef searchRef, SecIdentityRef *identity)
  __attribute__((deprecated));
# 57 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecItem.h" 1 3
# 51 "/System/Library/Frameworks/Security.framework/Headers/SecItem.h" 3
extern const CFTypeRef kSecClass
 __attribute__((visibility("default")));
# 66 "/System/Library/Frameworks/Security.framework/Headers/SecItem.h" 3
extern const CFTypeRef kSecClassInternetPassword
 __attribute__((visibility("default")));
extern const CFTypeRef kSecClassGenericPassword
 __attribute__((visibility("default")));
extern const CFTypeRef kSecClassCertificate
 __attribute__((visibility("default")));
extern const CFTypeRef kSecClassKey
 __attribute__((visibility("default")));
extern const CFTypeRef kSecClassIdentity
 __attribute__((visibility("default")));
# 321 "/System/Library/Frameworks/Security.framework/Headers/SecItem.h" 3
extern const CFTypeRef kSecAttrAccess
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrCreationDate
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrModificationDate
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrDescription
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrComment
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrCreator
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrType
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrLabel
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrIsInvisible
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrIsNegative
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrAccount
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrService
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrGeneric
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrSecurityDomain
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrServer
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocol
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrAuthenticationType
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrPort
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrPath
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrSubject
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrIssuer
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrSerialNumber
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrSubjectKeyID
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrPublicKeyHash
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrCertificateType
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrCertificateEncoding
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrKeyClass
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrApplicationLabel
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrIsPermanent
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrApplicationTag
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrKeyType
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrPRF
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrSalt
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrRounds
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrKeySizeInBits
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrEffectiveKeySize
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrCanEncrypt
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrCanDecrypt
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrCanDerive
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrCanSign
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrCanVerify
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrCanWrap
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrCanUnwrap
 __attribute__((visibility("default")));
# 445 "/System/Library/Frameworks/Security.framework/Headers/SecItem.h" 3
extern const CFTypeRef kSecAttrProtocolFTP
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolFTPAccount
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolHTTP
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolIRC
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolNNTP
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolPOP3
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolSMTP
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolSOCKS
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolIMAP
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolLDAP
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolAppleTalk
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolAFP
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolTelnet
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolSSH
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolFTPS
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolHTTPS
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolHTTPProxy
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolHTTPSProxy
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolFTPProxy
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolSMB
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolRTSP
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolRTSPProxy
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolDAAP
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolEPPC
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolIPP
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolNNTPS
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolLDAPS
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolTelnetS
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolIMAPS
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolIRCS
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrProtocolPOP3S
 __attribute__((visibility("default")));
# 522 "/System/Library/Frameworks/Security.framework/Headers/SecItem.h" 3
extern const CFTypeRef kSecAttrAuthenticationTypeNTLM
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrAuthenticationTypeMSN
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrAuthenticationTypeDPA
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrAuthenticationTypeRPA
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrAuthenticationTypeHTTPBasic
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrAuthenticationTypeHTTPDigest
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrAuthenticationTypeHTMLForm
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrAuthenticationTypeDefault
 __attribute__((visibility("default")));
# 548 "/System/Library/Frameworks/Security.framework/Headers/SecItem.h" 3
extern const CFTypeRef kSecAttrKeyClassPublic
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrKeyClassPrivate
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrKeyClassSymmetric
 __attribute__((visibility("default")));
# 569 "/System/Library/Frameworks/Security.framework/Headers/SecItem.h" 3
extern const CFTypeRef kSecAttrKeyTypeRSA
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrKeyTypeDSA
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrKeyTypeAES
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrKeyTypeDES
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrKeyType3DES
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrKeyTypeRC4
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrKeyTypeRC2
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrKeyTypeCAST
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrKeyTypeECDSA
 __attribute__((visibility("default")));
# 598 "/System/Library/Frameworks/Security.framework/Headers/SecItem.h" 3
extern const CFTypeRef kSecAttrPRFHmacAlgSHA1
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrPRFHmacAlgSHA224
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrPRFHmacAlgSHA256
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrPRFHmacAlgSHA384
 __attribute__((visibility("default")));
extern const CFTypeRef kSecAttrPRFHmacAlgSHA512
   __attribute__((visibility("default")));
# 673 "/System/Library/Frameworks/Security.framework/Headers/SecItem.h" 3
extern const CFTypeRef kSecMatchPolicy
 __attribute__((visibility("default")));
extern const CFTypeRef kSecMatchItemList
 __attribute__((visibility("default")));
extern const CFTypeRef kSecMatchSearchList
 __attribute__((visibility("default")));
extern const CFTypeRef kSecMatchIssuers
 __attribute__((visibility("default")));
extern const CFTypeRef kSecMatchEmailAddressIfPresent
 __attribute__((visibility("default")));
extern const CFTypeRef kSecMatchSubjectContains
 __attribute__((visibility("default")));
extern const CFTypeRef kSecMatchSubjectStartsWith
 __attribute__((visibility("default")));
extern const CFTypeRef kSecMatchSubjectEndsWith
 __attribute__((visibility("default")));
extern const CFTypeRef kSecMatchSubjectWholeString
 __attribute__((visibility("default")));
extern const CFTypeRef kSecMatchCaseInsensitive
 __attribute__((visibility("default")));
extern const CFTypeRef kSecMatchDiacriticInsensitive
 __attribute__((visibility("default")));
extern const CFTypeRef kSecMatchWidthInsensitive
 __attribute__((visibility("default")));
extern const CFTypeRef kSecMatchTrustedOnly
 __attribute__((visibility("default")));
extern const CFTypeRef kSecMatchValidOnDate
 __attribute__((visibility("default")));
extern const CFTypeRef kSecMatchLimit
 __attribute__((visibility("default")));
extern const CFTypeRef kSecMatchLimitOne
 __attribute__((visibility("default")));
extern const CFTypeRef kSecMatchLimitAll
 __attribute__((visibility("default")));
# 735 "/System/Library/Frameworks/Security.framework/Headers/SecItem.h" 3
extern const CFTypeRef kSecReturnData
 __attribute__((visibility("default")));
extern const CFTypeRef kSecReturnAttributes
 __attribute__((visibility("default")));
extern const CFTypeRef kSecReturnRef
 __attribute__((visibility("default")));
extern const CFTypeRef kSecReturnPersistentRef
 __attribute__((visibility("default")));
# 762 "/System/Library/Frameworks/Security.framework/Headers/SecItem.h" 3
extern const CFTypeRef kSecValueData
 __attribute__((visibility("default")));
extern const CFTypeRef kSecValueRef
 __attribute__((visibility("default")));
extern const CFTypeRef kSecValuePersistentRef
 __attribute__((visibility("default")));
# 784 "/System/Library/Frameworks/Security.framework/Headers/SecItem.h" 3
extern const CFTypeRef kSecUseItemList
 __attribute__((visibility("default")));
extern const CFTypeRef kSecUseKeychain
 __attribute__((visibility("default")));
# 846 "/System/Library/Frameworks/Security.framework/Headers/SecItem.h" 3
OSStatus SecItemCopyMatching(CFDictionaryRef query, CFTypeRef *result)
 __attribute__((visibility("default")));
# 885 "/System/Library/Frameworks/Security.framework/Headers/SecItem.h" 3
OSStatus SecItemAdd(CFDictionaryRef attributes, CFTypeRef *result)
 __attribute__((visibility("default")));
# 904 "/System/Library/Frameworks/Security.framework/Headers/SecItem.h" 3
OSStatus SecItemUpdate(CFDictionaryRef query, CFDictionaryRef attributesToUpdate)
 __attribute__((visibility("default")));
# 930 "/System/Library/Frameworks/Security.framework/Headers/SecItem.h" 3
OSStatus SecItemDelete(CFDictionaryRef query)
 __attribute__((visibility("default")));
# 58 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecKey.h" 1 3
# 118 "/System/Library/Frameworks/Security.framework/Headers/SecKey.h" 3
enum
{
    kSecKeyKeyClass = 0,
    kSecKeyPrintName = 1,
    kSecKeyAlias = 2,
    kSecKeyPermanent = 3,
    kSecKeyPrivate = 4,
    kSecKeyModifiable = 5,
    kSecKeyLabel = 6,
    kSecKeyApplicationTag = 7,
    kSecKeyKeyCreator = 8,
    kSecKeyKeyType = 9,
    kSecKeyKeySizeInBits = 10,
    kSecKeyEffectiveKeySize = 11,
    kSecKeyStartDate = 12,
    kSecKeyEndDate = 13,
    kSecKeySensitive = 14,
    kSecKeyAlwaysSensitive = 15,
    kSecKeyExtractable = 16,
    kSecKeyNeverExtractable = 17,
    kSecKeyEncrypt = 18,
    kSecKeyDecrypt = 19,
    kSecKeyDerive = 20,
    kSecKeySign = 21,
    kSecKeyVerify = 22,
    kSecKeySignRecover = 23,
    kSecKeyVerifyRecover = 24,
    kSecKeyWrap = 25,
    kSecKeyUnwrap = 26
};





typedef uint32 SecCredentialType;
# 162 "/System/Library/Frameworks/Security.framework/Headers/SecKey.h" 3
enum
{
 kSecCredentialTypeDefault = 0,
 kSecCredentialTypeWithUI,
 kSecCredentialTypeNoUI
};





typedef uint32_t SecPadding;
enum
{
    kSecPaddingNone = 0,
    kSecPaddingPKCS1 = 1,




    kSecPaddingPKCS1MD2 = 0x8000,




    kSecPaddingPKCS1MD5 = 0x8001,




    kSecPaddingPKCS1SHA1 = 0x8002,
};





typedef uint32_t SecKeySizes;
enum
{
    kSecDefaultKeySize = 0,


    kSec3DES192 = 192,
    kSecAES128 = 128,
    kSecAES192 = 192,
    kSecAES256 = 256,



    kSecp192r1 = 192,
    kSecp256r1 = 256,
    kSecp384r1 = 384,
    kSecp521r1 = 521,



    kSecRSAMin = 1024,
    kSecRSAMax = 4096
};







CFTypeID SecKeyGetTypeID(void);
# 250 "/System/Library/Frameworks/Security.framework/Headers/SecKey.h" 3
OSStatus SecKeyCreatePair(
        SecKeychainRef keychainRef,
        CSSM_ALGORITHMS algorithm,
        uint32 keySizeInBits,
        CSSM_CC_HANDLE contextHandle,
        CSSM_KEYUSE publicKeyUsage,
        uint32 publicKeyAttr,
        CSSM_KEYUSE privateKeyUsage,
        uint32 privateKeyAttr,
        SecAccessRef initialAccess,
        SecKeyRef* publicKey,
        SecKeyRef* privateKey)
  __attribute__((deprecated));
# 278 "/System/Library/Frameworks/Security.framework/Headers/SecKey.h" 3
OSStatus SecKeyGenerate(
        SecKeychainRef keychainRef,
        CSSM_ALGORITHMS algorithm,
        uint32 keySizeInBits,
        CSSM_CC_HANDLE contextHandle,
        CSSM_KEYUSE keyUsage,
        uint32 keyAttr,
        SecAccessRef initialAccess,
        SecKeyRef* keyRef)
  __attribute__((deprecated));
# 297 "/System/Library/Frameworks/Security.framework/Headers/SecKey.h" 3
OSStatus SecKeyGetCSSMKey(SecKeyRef key, const CSSM_KEY **cssmKey)
 __attribute__((deprecated));;
# 308 "/System/Library/Frameworks/Security.framework/Headers/SecKey.h" 3
OSStatus SecKeyGetCSPHandle(SecKeyRef keyRef, CSSM_CSP_HANDLE *cspHandle)
 __attribute__((deprecated));
# 320 "/System/Library/Frameworks/Security.framework/Headers/SecKey.h" 3
OSStatus SecKeyGetCredentials(
        SecKeyRef keyRef,
        CSSM_ACL_AUTHORIZATION_TAG operation,
        SecCredentialType credentialType,
        const CSSM_ACCESS_CREDENTIALS **outCredentials)
  __attribute__((deprecated));
# 335 "/System/Library/Frameworks/Security.framework/Headers/SecKey.h" 3
size_t SecKeyGetBlockSize(SecKeyRef key);
# 380 "/System/Library/Frameworks/Security.framework/Headers/SecKey.h" 3
SecKeyRef SecKeyGenerateSymmetric(CFDictionaryRef parameters, CFErrorRef *error)
 __attribute__((visibility("default")));
# 408 "/System/Library/Frameworks/Security.framework/Headers/SecKey.h" 3
SecKeyRef SecKeyCreateFromData(CFDictionaryRef parameters,
 CFDataRef keyData, CFErrorRef *error)
 __attribute__((visibility("default")));
# 452 "/System/Library/Frameworks/Security.framework/Headers/SecKey.h" 3
OSStatus SecKeyGeneratePair(CFDictionaryRef parameters,
 SecKeyRef *publicKey, SecKeyRef *privateKey)
 __attribute__((visibility("default")));
# 465 "/System/Library/Frameworks/Security.framework/Headers/SecKey.h" 3
typedef void (^SecKeyGeneratePairBlock)(SecKeyRef publicKey, SecKeyRef privateKey, CFErrorRef error);
# 507 "/System/Library/Frameworks/Security.framework/Headers/SecKey.h" 3
void SecKeyGeneratePairAsync(CFDictionaryRef parameters,
 dispatch_queue_t deliveryQueue, SecKeyGeneratePairBlock result)
 __attribute__((visibility("default")));
# 544 "/System/Library/Frameworks/Security.framework/Headers/SecKey.h" 3
SecKeyRef SecKeyDeriveFromPassword(CFStringRef password,
 CFDictionaryRef parameters, CFErrorRef *error)
 __attribute__((visibility("default")));
# 564 "/System/Library/Frameworks/Security.framework/Headers/SecKey.h" 3
CFDataRef SecKeyWrapSymmetric(SecKeyRef keyToWrap,
 SecKeyRef wrappingKey, CFDictionaryRef parameters, CFErrorRef *error)
 __attribute__((visibility("default")));
# 584 "/System/Library/Frameworks/Security.framework/Headers/SecKey.h" 3
SecKeyRef SecKeyUnwrapSymmetric(CFDataRef *keyToUnwrap,
 SecKeyRef unwrappingKey, CFDictionaryRef parameters, CFErrorRef *error)
 __attribute__((visibility("default")));
# 59 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 1 3
# 47 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
enum
{
    kSecUnlockStateStatus = 1,
    kSecReadPermStatus = 2,
    kSecWritePermStatus = 4
};
# 65 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
struct SecKeychainSettings
{
 UInt32 version;
 Boolean lockOnSleep;
 Boolean useLockInterval;
 UInt32 lockInterval;
};
typedef struct SecKeychainSettings SecKeychainSettings;





typedef FourCharCode SecAuthenticationType;
# 100 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
enum
{
    kSecAuthenticationTypeNTLM = (('ntlm' >> 24) | (('ntlm' >> 8) & 0xff00) | (('ntlm' << 8) & 0xff0000) | ('ntlm' & 0xff) << 24),
    kSecAuthenticationTypeMSN = (('msna' >> 24) | (('msna' >> 8) & 0xff00) | (('msna' << 8) & 0xff0000) | ('msna' & 0xff) << 24),
    kSecAuthenticationTypeDPA = (('dpaa' >> 24) | (('dpaa' >> 8) & 0xff00) | (('dpaa' << 8) & 0xff0000) | ('dpaa' & 0xff) << 24),
    kSecAuthenticationTypeRPA = (('rpaa' >> 24) | (('rpaa' >> 8) & 0xff00) | (('rpaa' << 8) & 0xff0000) | ('rpaa' & 0xff) << 24),
    kSecAuthenticationTypeHTTPBasic = (('http' >> 24) | (('http' >> 8) & 0xff00) | (('http' << 8) & 0xff0000) | ('http' & 0xff) << 24),
    kSecAuthenticationTypeHTTPDigest = (('httd' >> 24) | (('httd' >> 8) & 0xff00) | (('httd' << 8) & 0xff0000) | ('httd' & 0xff) << 24),
    kSecAuthenticationTypeHTMLForm = (('form' >> 24) | (('form' >> 8) & 0xff00) | (('form' << 8) & 0xff0000) | ('form' & 0xff) << 24),
    kSecAuthenticationTypeDefault = (('dflt' >> 24) | (('dflt' >> 8) & 0xff00) | (('dflt' << 8) & 0xff0000) | ('dflt' & 0xff) << 24),
    kSecAuthenticationTypeAny = ((0 >> 24) | ((0 >> 8) & 0xff00) | ((0 << 8) & 0xff0000) | (0 & 0xff) << 24)
};





typedef FourCharCode SecProtocolType;
# 157 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
enum
{
    kSecProtocolTypeFTP = 'ftp ',
    kSecProtocolTypeFTPAccount = 'ftpa',
    kSecProtocolTypeHTTP = 'http',
    kSecProtocolTypeIRC = 'irc ',
    kSecProtocolTypeNNTP = 'nntp',
    kSecProtocolTypePOP3 = 'pop3',
    kSecProtocolTypeSMTP = 'smtp',
    kSecProtocolTypeSOCKS = 'sox ',
    kSecProtocolTypeIMAP = 'imap',
    kSecProtocolTypeLDAP = 'ldap',
    kSecProtocolTypeAppleTalk = 'atlk',
    kSecProtocolTypeAFP = 'afp ',
    kSecProtocolTypeTelnet = 'teln',
    kSecProtocolTypeSSH = 'ssh ',
    kSecProtocolTypeFTPS = 'ftps',
    kSecProtocolTypeHTTPS = 'htps',
    kSecProtocolTypeHTTPProxy = 'htpx',
    kSecProtocolTypeHTTPSProxy = 'htsx',
    kSecProtocolTypeFTPProxy = 'ftpx',
    kSecProtocolTypeCIFS = 'cifs',
    kSecProtocolTypeSMB = 'smb ',
    kSecProtocolTypeRTSP = 'rtsp',
    kSecProtocolTypeRTSPProxy = 'rtsx',
    kSecProtocolTypeDAAP = 'daap',
    kSecProtocolTypeEPPC = 'eppc',
    kSecProtocolTypeIPP = 'ipp ',
    kSecProtocolTypeNNTPS = 'ntps',
    kSecProtocolTypeLDAPS = 'ldps',
    kSecProtocolTypeTelnetS = 'tels',
    kSecProtocolTypeIMAPS = 'imps',
    kSecProtocolTypeIRCS = 'ircs',
    kSecProtocolTypePOP3S = 'pops',
    kSecProtocolTypeCVSpserver = 'cvsp',
    kSecProtocolTypeSVN = 'svn ',
    kSecProtocolTypeAny = 0
};





typedef UInt32 SecKeychainEvent;
# 216 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
enum
{
    kSecLockEvent = 1,
    kSecUnlockEvent = 2,
    kSecAddEvent = 3,
    kSecDeleteEvent = 4,
    kSecUpdateEvent = 5,
    kSecPasswordChangedEvent = 6,
    kSecDefaultChangedEvent = 9,
    kSecDataAccessEvent = 10,
    kSecKeychainListChangedEvent = 11,
 kSecTrustSettingsChangedEvent = 12
};





typedef UInt32 SecKeychainEventMask;
# 250 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
enum
{
    kSecLockEventMask = 1 << kSecLockEvent,
    kSecUnlockEventMask = 1 << kSecUnlockEvent,
    kSecAddEventMask = 1 << kSecAddEvent,
    kSecDeleteEventMask = 1 << kSecDeleteEvent,
    kSecUpdateEventMask = 1 << kSecUpdateEvent,
    kSecPasswordChangedEventMask = 1 << kSecPasswordChangedEvent,
    kSecDefaultChangedEventMask = 1 << kSecDefaultChangedEvent,
    kSecDataAccessEventMask = 1 << kSecDataAccessEvent,
    kSecKeychainListChangedMask = 1 << kSecKeychainListChangedEvent,
 kSecTrustSettingsChangedEventMask = 1 << kSecTrustSettingsChangedEvent,
    kSecEveryEventMask = 0xffffffff
};
# 274 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
struct SecKeychainCallbackInfo
{
    UInt32 version;
    SecKeychainItemRef item;
    SecKeychainRef keychain;
 pid_t pid;
};
typedef struct SecKeychainCallbackInfo SecKeychainCallbackInfo;






CFTypeID SecKeychainGetTypeID(void);







OSStatus SecKeychainGetVersion(UInt32 *returnVers);

       
# 308 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
OSStatus SecKeychainOpen(const char *pathName, SecKeychainRef *keychain);
# 321 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
OSStatus SecKeychainCreate(const char *pathName, UInt32 passwordLength, const void *password, Boolean promptUser, SecAccessRef initialAccess, SecKeychainRef *keychain);







OSStatus SecKeychainDelete(SecKeychainRef keychainOrArray);
# 338 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
OSStatus SecKeychainSetSettings(SecKeychainRef keychain, const SecKeychainSettings *newSettings);
# 347 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
OSStatus SecKeychainCopySettings(SecKeychainRef keychain, SecKeychainSettings *outSettings);
# 359 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
OSStatus SecKeychainUnlock(SecKeychainRef keychain, UInt32 passwordLength, const void *password, Boolean usePassword);







OSStatus SecKeychainLock(SecKeychainRef keychain);






OSStatus SecKeychainLockAll(void);







OSStatus SecKeychainCopyDefault(SecKeychainRef *keychain);







OSStatus SecKeychainSetDefault(SecKeychainRef keychain);







OSStatus SecKeychainCopySearchList(CFArrayRef *searchList);







OSStatus SecKeychainSetSearchList(CFArrayRef searchList);






typedef enum {
 kSecPreferencesDomainUser,
 kSecPreferencesDomainSystem,
 kSecPreferencesDomainCommon,
 kSecPreferencesDomainDynamic
} SecPreferencesDomain;

OSStatus SecKeychainCopyDomainDefault(SecPreferencesDomain domain, SecKeychainRef *keychain);
OSStatus SecKeychainSetDomainDefault(SecPreferencesDomain domain, SecKeychainRef keychain);
OSStatus SecKeychainCopyDomainSearchList(SecPreferencesDomain domain, CFArrayRef *searchList);
OSStatus SecKeychainSetDomainSearchList(SecPreferencesDomain domain, CFArrayRef searchList);
OSStatus SecKeychainSetPreferenceDomain(SecPreferencesDomain domain);
OSStatus SecKeychainGetPreferenceDomain(SecPreferencesDomain *domain);
# 435 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
OSStatus SecKeychainGetStatus(SecKeychainRef keychain, SecKeychainStatus *keychainStatus);
# 445 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
OSStatus SecKeychainGetPath(SecKeychainRef keychain, UInt32 *ioPathLength, char *pathName);

       
# 457 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
OSStatus SecKeychainAttributeInfoForItemID(SecKeychainRef keychain, UInt32 itemID, SecKeychainAttributeInfo **info);







OSStatus SecKeychainFreeAttributeInfo(SecKeychainAttributeInfo *info);

       
# 484 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
typedef OSStatus (*SecKeychainCallback)(SecKeychainEvent keychainEvent, SecKeychainCallbackInfo *info, void *context);
# 494 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
OSStatus SecKeychainAddCallback(SecKeychainCallback callbackFunction, SecKeychainEventMask eventMask, void* userContext);







OSStatus SecKeychainRemoveCallback(SecKeychainCallback callbackFunction);

       
# 526 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
OSStatus SecKeychainAddInternetPassword(SecKeychainRef keychain, UInt32 serverNameLength, const char *serverName, UInt32 securityDomainLength, const char *securityDomain, UInt32 accountNameLength, const char *accountName, UInt32 pathLength, const char *path, UInt16 port, SecProtocolType protocol, SecAuthenticationType authenticationType, UInt32 passwordLength, const void *passwordData, SecKeychainItemRef *itemRef);
# 549 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
OSStatus SecKeychainFindInternetPassword(CFTypeRef keychainOrArray, UInt32 serverNameLength, const char *serverName, UInt32 securityDomainLength, const char *securityDomain, UInt32 accountNameLength, const char *accountName, UInt32 pathLength, const char *path, UInt16 port, SecProtocolType protocol, SecAuthenticationType authenticationType, UInt32 *passwordLength, void **passwordData, SecKeychainItemRef *itemRef);
# 565 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
OSStatus SecKeychainAddGenericPassword(SecKeychainRef keychain, UInt32 serviceNameLength, const char *serviceName, UInt32 accountNameLength, const char *accountName, UInt32 passwordLength, const void *passwordData, SecKeychainItemRef *itemRef);
# 581 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
OSStatus SecKeychainFindGenericPassword(CFTypeRef keychainOrArray, UInt32 serviceNameLength, const char *serviceName, UInt32 accountNameLength, const char *accountName, UInt32 *passwordLength, void **passwordData, SecKeychainItemRef *itemRef);

       






OSStatus SecKeychainSetUserInteractionAllowed(Boolean state);







OSStatus SecKeychainGetUserInteractionAllowed(Boolean *state);

       
# 609 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
OSStatus SecKeychainGetCSPHandle(SecKeychainRef keychain, CSSM_CSP_HANDLE *cspHandle)
 __attribute__((deprecated));
# 620 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
OSStatus SecKeychainGetDLDBHandle(SecKeychainRef keychain, CSSM_DL_DB_HANDLE *dldbHandle)
 __attribute__((deprecated));

       







OSStatus SecKeychainCopyAccess(SecKeychainRef keychain, SecAccessRef *access);
# 640 "/System/Library/Frameworks/Security.framework/Headers/SecKeychain.h" 3
OSStatus SecKeychainSetAccess(SecKeychainRef keychain, SecAccessRef access);
# 60 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainItem.h" 1 3
# 46 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainItem.h" 3
typedef FourCharCode SecItemClass;
# 60 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainItem.h" 3
enum
{
    kSecInternetPasswordItemClass = 'inet',
    kSecGenericPasswordItemClass = 'genp',
    kSecAppleSharePasswordItemClass = 'ashp',
    kSecCertificateItemClass = CSSM_DL_DB_RECORD_X509_CERTIFICATE,
    kSecPublicKeyItemClass = CSSM_DL_DB_RECORD_PUBLIC_KEY,
    kSecPrivateKeyItemClass = CSSM_DL_DB_RECORD_PRIVATE_KEY,
    kSecSymmetricKeyItemClass = CSSM_DL_DB_RECORD_SYMMETRIC_KEY
};






typedef FourCharCode SecItemAttr;
# 111 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainItem.h" 3
enum
{
    kSecCreationDateItemAttr = 'cdat',
    kSecModDateItemAttr = 'mdat',
    kSecDescriptionItemAttr = 'desc',
    kSecCommentItemAttr = 'icmt',
    kSecCreatorItemAttr = 'crtr',
    kSecTypeItemAttr = 'type',
    kSecScriptCodeItemAttr = 'scrp',
    kSecLabelItemAttr = 'labl',
    kSecInvisibleItemAttr = 'invi',
    kSecNegativeItemAttr = 'nega',
    kSecCustomIconItemAttr = 'cusi',
    kSecAccountItemAttr = 'acct',
    kSecServiceItemAttr = 'svce',
    kSecGenericItemAttr = 'gena',
    kSecSecurityDomainItemAttr = 'sdmn',
    kSecServerItemAttr = 'srvr',
    kSecAuthenticationTypeItemAttr = 'atyp',
    kSecPortItemAttr = 'port',
    kSecPathItemAttr = 'path',
    kSecVolumeItemAttr = 'vlme',
    kSecAddressItemAttr = 'addr',
    kSecSignatureItemAttr = 'ssig',
    kSecProtocolItemAttr = 'ptcl',
 kSecCertificateType = 'ctyp',
 kSecCertificateEncoding = 'cenc',
 kSecCrlType = 'crtp',
 kSecCrlEncoding = 'crnc',
 kSecAlias = 'alis'
};





typedef UInt8 SecAFPServerSignature[16];





typedef UInt8 SecPublicKeyHash[20];

       





CFTypeID SecKeychainItemGetTypeID(void);
# 173 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainItem.h" 3
OSStatus SecKeychainItemModifyAttributesAndData(SecKeychainItemRef itemRef, const SecKeychainAttributeList *attrList, UInt32 length, const void *data);
# 187 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainItem.h" 3
OSStatus SecKeychainItemCreateFromContent(SecItemClass itemClass, SecKeychainAttributeList *attrList,
  UInt32 length, const void *data, SecKeychainRef keychainRef,
  SecAccessRef initialAccess, SecKeychainItemRef *itemRef);
# 200 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainItem.h" 3
OSStatus SecKeychainItemModifyContent(SecKeychainItemRef itemRef, const SecKeychainAttributeList *attrList, UInt32 length, const void *data);
# 212 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainItem.h" 3
OSStatus SecKeychainItemCopyContent(SecKeychainItemRef itemRef, SecItemClass *itemClass, SecKeychainAttributeList *attrList, UInt32 *length, void **outData);







OSStatus SecKeychainItemFreeContent(SecKeychainAttributeList *attrList, void *data);
# 233 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainItem.h" 3
OSStatus SecKeychainItemCopyAttributesAndData(SecKeychainItemRef itemRef, SecKeychainAttributeInfo *info, SecItemClass *itemClass, SecKeychainAttributeList **attrList, UInt32 *length, void **outData);
# 242 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainItem.h" 3
OSStatus SecKeychainItemFreeAttributesAndData(SecKeychainAttributeList *attrList, void *data);
# 251 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainItem.h" 3
OSStatus SecKeychainItemDelete(SecKeychainItemRef itemRef);
# 260 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainItem.h" 3
OSStatus SecKeychainItemCopyKeychain(SecKeychainItemRef itemRef, SecKeychainRef *keychainRef);
# 271 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainItem.h" 3
OSStatus SecKeychainItemCreateCopy(SecKeychainItemRef itemRef, SecKeychainRef destKeychainRef,
 SecAccessRef initialAccess, SecKeychainItemRef *itemCopy);
# 281 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainItem.h" 3
OSStatus SecKeychainItemCreatePersistentReference(SecKeychainItemRef itemRef, CFDataRef *persistentItemRef);
# 291 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainItem.h" 3
OSStatus SecKeychainItemCopyFromPersistentReference(CFDataRef persistentItemRef, SecKeychainItemRef *itemRef);


       
# 303 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainItem.h" 3
OSStatus SecKeychainItemGetDLDBHandle(SecKeychainItemRef keyItemRef, CSSM_DL_DB_HANDLE *dldbHandle)
 __attribute__((deprecated));
# 314 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainItem.h" 3
OSStatus SecKeychainItemGetUniqueRecordID(SecKeychainItemRef itemRef, const CSSM_DB_UNIQUE_RECORD **uniqueRecordID)
 __attribute__((deprecated));

       







OSStatus SecKeychainItemCopyAccess(SecKeychainItemRef itemRef, SecAccessRef *access);
# 334 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainItem.h" 3
OSStatus SecKeychainItemSetAccess(SecKeychainItemRef itemRef, SecAccessRef access);
# 61 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainSearch.h" 1 3
# 45 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainSearch.h" 3
CFTypeID SecKeychainSearchGetTypeID(void)
  __attribute__((deprecated));
# 58 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainSearch.h" 3
OSStatus SecKeychainSearchCreateFromAttributes(CFTypeRef keychainOrArray, SecItemClass itemClass, const SecKeychainAttributeList *attrList, SecKeychainSearchRef *searchRef)
  __attribute__((deprecated));
# 69 "/System/Library/Frameworks/Security.framework/Headers/SecKeychainSearch.h" 3
OSStatus SecKeychainSearchCopyNext(SecKeychainSearchRef searchRef, SecKeychainItemRef *itemRef)
  __attribute__((deprecated));
# 62 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecPolicy.h" 1 3
# 57 "/System/Library/Frameworks/Security.framework/Headers/SecPolicy.h" 3
extern CFTypeRef kSecPolicyAppleX509Basic
    __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyAppleSSL
    __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyAppleSMIME
    __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyAppleEAP
    __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyAppleIPsec
    __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyAppleiChat
    __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyApplePKINITClient
    __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyApplePKINITServer
    __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyAppleCodeSigning
    __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyMacAppStoreReceipt
    __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyAppleIDValidation
    __attribute__((visibility("default")));
# 148 "/System/Library/Frameworks/Security.framework/Headers/SecPolicy.h" 3
extern CFTypeRef kSecPolicyOid
    __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyName
 __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyClient
 __attribute__((visibility("default")));

extern CFTypeRef kSecPolicyKU_DigitalSignature
 __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyKU_NonRepudiation
 __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyKU_KeyEncipherment
 __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyKU_DataEncipherment
 __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyKU_KeyAgreement
 __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyKU_KeyCertSign
 __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyKU_CRLSign
 __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyKU_EncipherOnly
 __attribute__((visibility("default")));
extern CFTypeRef kSecPolicyKU_DecipherOnly
 __attribute__((visibility("default")));







CFTypeID SecPolicyGetTypeID(void)
    __attribute__((visibility("default")));
# 192 "/System/Library/Frameworks/Security.framework/Headers/SecPolicy.h" 3
OSStatus SecPolicyGetOID(SecPolicyRef policyRef, CSSM_OID *oid)
 __attribute__((deprecated));
# 204 "/System/Library/Frameworks/Security.framework/Headers/SecPolicy.h" 3
OSStatus SecPolicyGetValue(SecPolicyRef policyRef, CSSM_DATA *value)
 __attribute__((deprecated));
# 218 "/System/Library/Frameworks/Security.framework/Headers/SecPolicy.h" 3
CFDictionaryRef SecPolicyCopyProperties(SecPolicyRef policyRef)
    __attribute__((visibility("default")));
# 231 "/System/Library/Frameworks/Security.framework/Headers/SecPolicy.h" 3
OSStatus SecPolicySetValue(SecPolicyRef policyRef, const CSSM_DATA *value)
 __attribute__((deprecated));
# 244 "/System/Library/Frameworks/Security.framework/Headers/SecPolicy.h" 3
OSStatus SecPolicySetProperties(SecPolicyRef policyRef,
 CFDictionaryRef properties)
    __attribute__((visibility("default")));
# 256 "/System/Library/Frameworks/Security.framework/Headers/SecPolicy.h" 3
OSStatus SecPolicyGetTPHandle(SecPolicyRef policyRef, CSSM_TP_HANDLE *tpHandle)
 __attribute__((deprecated));







SecPolicyRef SecPolicyCreateBasicX509(void)
    __attribute__((visibility("default")));
# 278 "/System/Library/Frameworks/Security.framework/Headers/SecPolicy.h" 3
SecPolicyRef SecPolicyCreateSSL(Boolean server, CFStringRef hostname)
    __attribute__((visibility("default")));
# 290 "/System/Library/Frameworks/Security.framework/Headers/SecPolicy.h" 3
SecPolicyRef SecPolicyCreateWithOID(CFTypeRef policyOID)
    __attribute__((visibility("default")));
# 63 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecPolicySearch.h" 1 3
# 44 "/System/Library/Frameworks/Security.framework/Headers/SecPolicySearch.h" 3
typedef struct OpaquePolicySearchRef *SecPolicySearchRef;







CFTypeID SecPolicySearchGetTypeID(void)
  __attribute__((deprecated));
# 65 "/System/Library/Frameworks/Security.framework/Headers/SecPolicySearch.h" 3
OSStatus SecPolicySearchCreate(CSSM_CERT_TYPE certType, const CSSM_OID *policyOID, const CSSM_DATA *value, SecPolicySearchRef *searchRef)
  __attribute__((deprecated));
# 76 "/System/Library/Frameworks/Security.framework/Headers/SecPolicySearch.h" 3
OSStatus SecPolicySearchCopyNext(SecPolicySearchRef searchRef, SecPolicyRef *policyRef)
  __attribute__((deprecated));
# 64 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 1 3
# 72 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
typedef uint32_t SecTrustResultType;
enum {
    kSecTrustResultInvalid,
    kSecTrustResultProceed,
    kSecTrustResultConfirm,
    kSecTrustResultDeny,
    kSecTrustResultUnspecified,
    kSecTrustResultRecoverableTrustFailure,
    kSecTrustResultFatalTrustFailure,
    kSecTrustResultOtherError
};





typedef SecTrustResultType SecTrustUserSetting;
# 104 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
typedef uint32_t SecTrustOptionFlags;
enum {
 kSecTrustOptionAllowExpired = 0x00000001,
 kSecTrustOptionLeafIsCA = 0x00000002,
 kSecTrustOptionFetchIssuerFromNet = 0x00000004,
 kSecTrustOptionAllowExpiredRoot = 0x00000008,
 kSecTrustOptionRequireRevPerCert = 0x00000010,
 kSecTrustOptionUseTrustSettings = 0x00000020,
 kSecTrustOptionImplicitAnchors = 0x00000040
};
# 124 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
extern CFTypeRef kSecPropertyTypeTitle
    __attribute__((visibility("default")));
extern CFTypeRef kSecPropertyTypeError
    __attribute__((visibility("default")));






typedef struct OpaqueSecTrustRef *SecTrustRef;
# 144 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
typedef void (^SecTrustCallback)(SecTrustRef trustRef, SecTrustResultType trustResult);







CFTypeID SecTrustGetTypeID(void)
    __attribute__((visibility("default")));
# 167 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
OSStatus SecTrustCreateWithCertificates(CFArrayRef certificates,
    CFTypeRef policies, SecTrustRef *trustRef)
    __attribute__((visibility("default")));
# 180 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
OSStatus SecTrustSetPolicies(SecTrustRef trust, CFTypeRef policies)
    __attribute__((visibility("default")));
# 190 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
OSStatus SecTrustSetOptions(SecTrustRef trustRef, SecTrustOptionFlags options)
    __attribute__((visibility("default")));
# 203 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
OSStatus SecTrustSetParameters(SecTrustRef trustRef,
 CSSM_TP_ACTION action, CFDataRef actionData)
 __attribute__((deprecated));
# 217 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
OSStatus SecTrustSetAnchorCertificates(SecTrustRef trust,
    CFArrayRef anchorCertificates)
    __attribute__((visibility("default")));
# 231 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
OSStatus SecTrustSetAnchorCertificatesOnly(SecTrustRef trust,
    Boolean anchorCertificatesOnly)
    __attribute__((visibility("default")));
# 246 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
OSStatus SecTrustSetKeychains(SecTrustRef trust, CFTypeRef keychainOrArray)
    __attribute__((visibility("default")));
# 261 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
OSStatus SecTrustSetVerifyDate(SecTrustRef trust, CFDateRef verifyDate)
    __attribute__((visibility("default")));
# 275 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
CFAbsoluteTime SecTrustGetVerifyTime(SecTrustRef trust)
    __attribute__((visibility("default")));
# 292 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
OSStatus SecTrustEvaluate(SecTrustRef trust, SecTrustResultType *result)
    __attribute__((visibility("default")));
# 306 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
OSStatus SecTrustEvaluateAsync(SecTrustRef trust,
 dispatch_queue_t queue, SecTrustCallback result)
    __attribute__((visibility("default")));
# 329 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
OSStatus SecTrustGetResult(SecTrustRef trustRef, SecTrustResultType *result,
 CFArrayRef *certChain, CSSM_TP_APPLE_EVIDENCE_INFO **statusChain)
 __attribute__((deprecated));
# 344 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
OSStatus SecTrustGetCssmResult(SecTrustRef trust,
 CSSM_TP_VERIFY_CONTEXT_RESULT_PTR *result)
 __attribute__((deprecated));
# 364 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
OSStatus SecTrustGetCssmResultCode(SecTrustRef trust, OSStatus *resultCode)
 __attribute__((deprecated));
# 377 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
OSStatus SecTrustGetTrustResult(SecTrustRef trustRef,
 SecTrustResultType *result)
    __attribute__((visibility("default")));
# 389 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
OSStatus SecTrustGetTPHandle(SecTrustRef trust, CSSM_TP_HANDLE *handle)
 __attribute__((deprecated));
# 400 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
OSStatus SecTrustCopyPolicies(SecTrustRef trust, CFArrayRef *policies)
    __attribute__((visibility("default")));
# 414 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
OSStatus SecTrustCopyCustomAnchorCertificates(SecTrustRef trust,
 CFArrayRef *anchors)
    __attribute__((visibility("default")));
# 426 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
OSStatus SecTrustCopyAnchorCertificates(CFArrayRef *anchors)
    __attribute__((visibility("default")));
# 439 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
SecKeyRef SecTrustCopyPublicKey(SecTrustRef trust)
    __attribute__((visibility("default")));
# 451 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
CFIndex SecTrustGetCertificateCount(SecTrustRef trust)
    __attribute__((visibility("default")));
# 464 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
SecCertificateRef SecTrustGetCertificateAtIndex(SecTrustRef trust, CFIndex ix)
    __attribute__((visibility("default")));
# 481 "/System/Library/Frameworks/Security.framework/Headers/SecTrust.h" 3
CFArrayRef SecTrustCopyProperties(SecTrustRef trust)
    __attribute__((visibility("default")));
# 65 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecTrustedApplication.h" 1 3
# 46 "/System/Library/Frameworks/Security.framework/Headers/SecTrustedApplication.h" 3
CFTypeID SecTrustedApplicationGetTypeID(void);
# 57 "/System/Library/Frameworks/Security.framework/Headers/SecTrustedApplication.h" 3
OSStatus SecTrustedApplicationCreateFromPath(const char *path, SecTrustedApplicationRef *app);
# 66 "/System/Library/Frameworks/Security.framework/Headers/SecTrustedApplication.h" 3
OSStatus SecTrustedApplicationCopyData(SecTrustedApplicationRef appRef, CFDataRef *data);
# 75 "/System/Library/Frameworks/Security.framework/Headers/SecTrustedApplication.h" 3
OSStatus SecTrustedApplicationSetData(SecTrustedApplicationRef appRef, CFDataRef data);
# 66 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecTrustSettings.h" 1 3
# 181 "/System/Library/Frameworks/Security.framework/Headers/SecTrustSettings.h" 3
enum {

 kSecTrustSettingsKeyUseSignature = 0x00000001,

 kSecTrustSettingsKeyUseEnDecryptData = 0x00000002,

 kSecTrustSettingsKeyUseEnDecryptKey = 0x00000004,

 kSecTrustSettingsKeyUseSignCert = 0x00000008,

 kSecTrustSettingsKeyUseSignRevocation = 0x00000010,

 kSecTrustSettingsKeyUseKeyExchange = 0x00000020,

 kSecTrustSettingsKeyUseAny = 0xffffffff
};
typedef uint32 SecTrustSettingsKeyUsage;




enum {
 kSecTrustSettingsResultInvalid = 0,

 kSecTrustSettingsResultTrustRoot,
 kSecTrustSettingsResultTrustAsRoot,
 kSecTrustSettingsResultDeny,
 kSecTrustSettingsResultUnspecified

};
typedef uint32 SecTrustSettingsResult;






enum {
 kSecTrustSettingsDomainUser = 0,
 kSecTrustSettingsDomainAdmin,
 kSecTrustSettingsDomainSystem
};
typedef uint32 SecTrustSettingsDomain;
# 249 "/System/Library/Frameworks/Security.framework/Headers/SecTrustSettings.h" 3
OSStatus SecTrustSettingsCopyTrustSettings(
 SecCertificateRef certRef,
 SecTrustSettingsDomain domain,
 CFArrayRef *trustSettings);
# 262 "/System/Library/Frameworks/Security.framework/Headers/SecTrustSettings.h" 3
OSStatus SecTrustSettingsSetTrustSettings(
 SecCertificateRef certRef,
 SecTrustSettingsDomain domain,
 CFTypeRef trustSettingsDictOrArray);





OSStatus SecTrustSettingsRemoveTrustSettings(
 SecCertificateRef certRef,
 SecTrustSettingsDomain domain);
# 283 "/System/Library/Frameworks/Security.framework/Headers/SecTrustSettings.h" 3
OSStatus SecTrustSettingsCopyCertificates(
 SecTrustSettingsDomain domain,
 CFArrayRef *certArray);







OSStatus SecTrustSettingsCopyModificationDate(
 SecCertificateRef certRef,
 SecTrustSettingsDomain domain,
 CFDateRef *modificationDate);







OSStatus SecTrustSettingsCreateExternalRepresentation(
 SecTrustSettingsDomain domain,
 CFDataRef *trustSettings);





OSStatus SecTrustSettingsImportExternalRepresentation(
 SecTrustSettingsDomain domain,
 CFDataRef trustSettings);
# 67 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecImportExport.h" 1 3
# 44 "/System/Library/Frameworks/Security.framework/Headers/SecImportExport.h" 3
enum
{




 kSecFormatUnknown = 0,





 kSecFormatOpenSSL,
 kSecFormatSSH,
 kSecFormatBSAFE,


 kSecFormatRawKey,


 kSecFormatWrappedPKCS8,
 kSecFormatWrappedOpenSSL,
 kSecFormatWrappedSSH,
 kSecFormatWrappedLSH,


 kSecFormatX509Cert,


 kSecFormatPEMSequence,

 kSecFormatPKCS7,
 kSecFormatPKCS12,
 kSecFormatNetscapeCertSequence,


 kSecFormatSSHv2


};
typedef uint32_t SecExternalFormat;




enum {
 kSecItemTypeUnknown,
 kSecItemTypePrivateKey,
 kSecItemTypePublicKey,
 kSecItemTypeSessionKey,
 kSecItemTypeCertificate,
 kSecItemTypeAggregate
};
typedef uint32_t SecExternalItemType;




enum
{
 kSecItemPemArmour = 0x00000001,
};
typedef uint32_t SecItemImportExportFlags;




enum
{




 kSecKeyImportOnlyOne = 0x00000001,
# 126 "/System/Library/Frameworks/Security.framework/Headers/SecImportExport.h" 3
 kSecKeySecurePassphrase = 0x00000002,







 kSecKeyNoAccessControl = 0x00000004
};
typedef uint32_t SecKeyImportExportFlags;
# 146 "/System/Library/Frameworks/Security.framework/Headers/SecImportExport.h" 3
typedef struct
{

 uint32_t version;
 SecKeyImportExportFlags flags;
 CFTypeRef passphrase;


 CFStringRef alertTitle;
 CFStringRef alertPrompt;


 SecAccessRef accessRef;

 CSSM_KEYUSE keyUsage;

 CSSM_KEYATTR_FLAGS keyAttributes;
} SecKeyImportExportParameters;


typedef struct
{

 uint32_t version;
 SecKeyImportExportFlags flags;
 CFTypeRef passphrase;


 CFStringRef alertTitle;
 CFStringRef alertPrompt;


 SecAccessRef accessRef;

 CFArrayRef keyUsage;



 CFArrayRef keyAttributes;
} SecItemImportExportKeyParameters;
# 236 "/System/Library/Frameworks/Security.framework/Headers/SecImportExport.h" 3
OSStatus SecKeychainItemExport(
 CFTypeRef keychainItemOrArray,
 SecExternalFormat outputFormat,
 SecItemImportExportFlags flags,
 const SecKeyImportExportParameters *keyParams,
 CFDataRef *exportedData)
  __attribute__((deprecated));
# 293 "/System/Library/Frameworks/Security.framework/Headers/SecImportExport.h" 3
OSStatus SecItemExport(
 CFTypeRef secItemOrArray,
 SecExternalFormat outputFormat,
 SecItemImportExportFlags flags,
 const SecItemImportExportKeyParameters *keyParams,
 CFDataRef *exportedData)
  __attribute__((visibility("default")));
# 448 "/System/Library/Frameworks/Security.framework/Headers/SecImportExport.h" 3
OSStatus SecKeychainItemImport(
 CFDataRef importedData,
 CFStringRef fileNameOrExtension,
 SecExternalFormat *inputFormat,
 SecExternalItemType *itemType,
 SecItemImportExportFlags flags,
 const SecKeyImportExportParameters *keyParams,
 SecKeychainRef importKeychain,
 CFArrayRef *outItems)
  __attribute__((deprecated));
# 606 "/System/Library/Frameworks/Security.framework/Headers/SecImportExport.h" 3
OSStatus SecItemImport(
 CFDataRef importedData,
 CFStringRef fileNameOrExtension,
 SecExternalFormat *inputFormat,
 SecExternalItemType *itemType,
 SecItemImportExportFlags flags,
 const SecItemImportExportKeyParameters *keyParams,
 SecKeychainRef importKeychain,
 CFArrayRef *outItems)
  __attribute__((visibility("default")));







extern CFStringRef kSecImportExportPassphrase;
extern CFStringRef kSecImportExportKeychain;
extern CFStringRef kSecImportExportAccess;
# 636 "/System/Library/Frameworks/Security.framework/Headers/SecImportExport.h" 3
extern CFStringRef kSecImportItemLabel;
extern CFStringRef kSecImportItemKeyID;
extern CFStringRef kSecImportItemTrust;
extern CFStringRef kSecImportItemCertChain;
extern CFStringRef kSecImportItemIdentity;
# 651 "/System/Library/Frameworks/Security.framework/Headers/SecImportExport.h" 3
OSStatus SecPKCS12Import(CFDataRef pkcs12_data, CFDictionaryRef options, CFArrayRef *items);
# 68 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecStaticCode.h" 1 3
# 41 "/System/Library/Frameworks/Security.framework/Headers/SecStaticCode.h" 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/CSCommon.h" 1 3
# 44 "/System/Library/Frameworks/Security.framework/Headers/CSCommon.h" 3
enum {
 errSecCSUnimplemented = -67072,
 errSecCSInvalidObjectRef = -67071,
 errSecCSInvalidFlags = -67070,
 errSecCSObjectRequired = -67069,
 errSecCSStaticCodeNotFound = -67068,
 errSecCSUnsupportedGuestAttributes = -67067,
 errSecCSInvalidAttributeValues = -67066,
 errSecCSNoSuchCode = -67065,
 errSecCSMultipleGuests = -67064,
 errSecCSGuestInvalid = -67063,
 errSecCSUnsigned = -67062,
 errSecCSSignatureFailed = -67061,
 errSecCSSignatureNotVerifiable = -67060,
 errSecCSSignatureUnsupported = -67059,
 errSecCSBadDictionaryFormat = -67058,
 errSecCSResourcesNotSealed = -67057,
 errSecCSResourcesNotFound = -67056,
 errSecCSResourcesInvalid = -67055,
 errSecCSBadResource = -67054,
 errSecCSResourceRulesInvalid = -67053,
 errSecCSReqInvalid = -67052,
 errSecCSReqUnsupported = -67051,
 errSecCSReqFailed = -67050,
 errSecCSBadObjectFormat = -67049,
 errSecCSInternalError = -67048,
 errSecCSHostReject = -67047,
 errSecCSNotAHost = -67046,
 errSecCSSignatureInvalid = -67045,
 errSecCSHostProtocolRelativePath = -67044,
 errSecCSHostProtocolContradiction = -67043,
 errSecCSHostProtocolDedicationError = -67042,
 errSecCSHostProtocolNotProxy = -67041,
 errSecCSHostProtocolStateError = -67040,
 errSecCSHostProtocolUnrelated = -67039,

 errSecCSNotSupported = -67037,
 errSecCSCMSTooLarge = -67036,
 errSecCSHostProtocolInvalidHash = -67035,
 errSecCSStaticCodeChanged = -67034,
 errSecCSSigDBDenied = -67033,
 errSecCSSigDBAccess = -67032,
 errSecCSHostProtocolInvalidAttribute = -67031,
 errSecCSInfoPlistFailed = -67030,
 errSecCSNoMainExecutable = -67029,
};
# 101 "/System/Library/Frameworks/Security.framework/Headers/CSCommon.h" 3
extern const CFStringRef kSecCFErrorArchitecture;
extern const CFStringRef kSecCFErrorPattern;
extern const CFStringRef kSecCFErrorResourceSeal;
extern const CFStringRef kSecCFErrorResourceAdded;
extern const CFStringRef kSecCFErrorResourceAltered;
extern const CFStringRef kSecCFErrorResourceMissing;
extern const CFStringRef kSecCFErrorInfoPlist;
extern const CFStringRef kSecCFErrorGuestAttributes;
extern const CFStringRef kSecCFErrorRequirementSyntax;
# 120 "/System/Library/Frameworks/Security.framework/Headers/CSCommon.h" 3
typedef struct __SecCode *SecCodeRef;





typedef struct __SecCode const *SecStaticCodeRef;





typedef struct __SecRequirement *SecRequirementRef;
# 142 "/System/Library/Frameworks/Security.framework/Headers/CSCommon.h" 3
typedef u_int32_t SecGuestRef;

enum {
 kSecNoGuest = 0,
};
# 169 "/System/Library/Frameworks/Security.framework/Headers/CSCommon.h" 3
typedef uint32_t SecCSFlags;

enum {
 kSecCSDefaultFlags = 0,

 kSecCSConsiderExpiration = 1 << 31,
};
# 209 "/System/Library/Frameworks/Security.framework/Headers/CSCommon.h" 3
typedef uint32_t SecCodeSignatureFlags;

enum {
 kSecCodeSignatureHost = 0x0001,
 kSecCodeSignatureAdhoc = 0x0002,
 kSecCodeSignatureForceHard = 0x0100,
 kSecCodeSignatureForceKill = 0x0200,
 kSecCodeSignatureForceExpiration = 0x0400,
};
# 260 "/System/Library/Frameworks/Security.framework/Headers/CSCommon.h" 3
typedef uint32_t SecCodeStatus;
enum {
 kSecCodeStatusValid = 0x0001,
 kSecCodeStatusHard = 0x0100,
 kSecCodeStatusKill = 0x0200,
};






typedef uint32_t SecRequirementType;

enum {
 kSecHostRequirementType = 1,
 kSecGuestRequirementType = 2,
 kSecDesignatedRequirementType = 3,
 kSecLibraryRequirementType = 4,
 kSecPluginRequirementType = 5,
 kSecInvalidRequirementType,
 kSecRequirementTypeCount = kSecInvalidRequirementType
};
# 42 "/System/Library/Frameworks/Security.framework/Headers/SecStaticCode.h" 2 3
# 52 "/System/Library/Frameworks/Security.framework/Headers/SecStaticCode.h" 3
CFTypeID SecStaticCodeGetTypeID(void);
# 89 "/System/Library/Frameworks/Security.framework/Headers/SecStaticCode.h" 3
extern const CFStringRef kSecCodeAttributeArchitecture;
extern const CFStringRef kSecCodeAttributeSubarchitecture;
extern const CFStringRef kSecCodeAttributeBundleVersion;

OSStatus SecStaticCodeCreateWithPath(CFURLRef path, SecCSFlags flags, SecStaticCodeRef *staticCode);

OSStatus SecStaticCodeCreateWithPathAndAttributes(CFURLRef path, SecCSFlags flags, CFDictionaryRef attributes,
 SecStaticCodeRef *staticCode);
# 134 "/System/Library/Frameworks/Security.framework/Headers/SecStaticCode.h" 3
enum {
 kSecCSCheckAllArchitectures = 1 << 0,
 kSecCSDoNotValidateExecutable = 1 << 1,
 kSecCSDoNotValidateResources = 1 << 2,
 kSecCSBasicValidateOnly = kSecCSDoNotValidateExecutable | kSecCSDoNotValidateResources
};

OSStatus SecStaticCodeCheckValidity(SecStaticCodeRef staticCode, SecCSFlags flags,
 SecRequirementRef requirement);

OSStatus SecStaticCodeCheckValidityWithErrors(SecStaticCodeRef staticCode, SecCSFlags flags,
 SecRequirementRef requirement, CFErrorRef *errors);
# 69 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3

# 1 "/System/Library/Frameworks/Security.framework/Headers/Authorization.h" 1 3
# 87 "/System/Library/Frameworks/Security.framework/Headers/Authorization.h" 3
enum {
 errAuthorizationSuccess = 0,
 errAuthorizationInvalidSet = -60001,
 errAuthorizationInvalidRef = -60002,
 errAuthorizationInvalidTag = -60003,
 errAuthorizationInvalidPointer = -60004,
 errAuthorizationDenied = -60005,
 errAuthorizationCanceled = -60006,
 errAuthorizationInteractionNotAllowed = -60007,
 errAuthorizationInternal = -60008,
 errAuthorizationExternalizeNotAllowed = -60009,
 errAuthorizationInternalizeNotAllowed = -60010,
 errAuthorizationInvalidFlags = -60011,
 errAuthorizationToolExecuteFailure = -60031,
 errAuthorizationToolEnvironmentError = -60032,
 errAuthorizationBadAddress = -60033,
};






enum {
 kAuthorizationFlagDefaults = 0,
 kAuthorizationFlagInteractionAllowed = (1 << 0),
 kAuthorizationFlagExtendRights = (1 << 1),
 kAuthorizationFlagPartialRights = (1 << 2),
 kAuthorizationFlagDestroyRights = (1 << 3),
 kAuthorizationFlagPreAuthorize = (1 << 4),


 kAuthorizationFlagNoData = (1 << 20)
};






typedef UInt32 AuthorizationFlags;






enum {
 kAuthorizationFlagCanNotPreAuthorize = (1 << 0)
};






typedef const struct AuthorizationOpaqueRef *AuthorizationRef;






typedef const char *AuthorizationString;
# 165 "/System/Library/Frameworks/Security.framework/Headers/Authorization.h" 3
typedef struct {
 AuthorizationString name;
 size_t valueLength;
 void *value;
 UInt32 flags;
} AuthorizationItem;
# 180 "/System/Library/Frameworks/Security.framework/Headers/Authorization.h" 3
typedef struct {
 UInt32 count;
 AuthorizationItem *items;
} AuthorizationItemSet;
# 198 "/System/Library/Frameworks/Security.framework/Headers/Authorization.h" 3
enum {
 kAuthorizationExternalFormLength = 32
};

typedef struct {
 char bytes[kAuthorizationExternalFormLength];
} AuthorizationExternalForm;
# 213 "/System/Library/Frameworks/Security.framework/Headers/Authorization.h" 3
typedef AuthorizationItemSet AuthorizationRights;







typedef AuthorizationItemSet AuthorizationEnvironment;
# 254 "/System/Library/Frameworks/Security.framework/Headers/Authorization.h" 3
OSStatus AuthorizationCreate(const AuthorizationRights *rights,
 const AuthorizationEnvironment *environment,
 AuthorizationFlags flags,
 AuthorizationRef *authorization);
# 276 "/System/Library/Frameworks/Security.framework/Headers/Authorization.h" 3
OSStatus AuthorizationFree(AuthorizationRef authorization, AuthorizationFlags flags);
# 312 "/System/Library/Frameworks/Security.framework/Headers/Authorization.h" 3
OSStatus AuthorizationCopyRights(AuthorizationRef authorization,
 const AuthorizationRights *rights,
 const AuthorizationEnvironment *environment,
 AuthorizationFlags flags,
 AuthorizationRights **authorizedRights);
# 328 "/System/Library/Frameworks/Security.framework/Headers/Authorization.h" 3
typedef void (^AuthorizationAsyncCallback)(OSStatus err, AuthorizationRights *blockAuthorizedRights);







void AuthorizationCopyRightsAsync(AuthorizationRef authorization,
 const AuthorizationRights *rights,
 const AuthorizationEnvironment *environment,
 AuthorizationFlags flags,
 AuthorizationAsyncCallback callbackBlock);
# 363 "/System/Library/Frameworks/Security.framework/Headers/Authorization.h" 3
OSStatus AuthorizationCopyInfo(AuthorizationRef authorization,
 AuthorizationString tag,
 AuthorizationItemSet **info);
# 387 "/System/Library/Frameworks/Security.framework/Headers/Authorization.h" 3
OSStatus AuthorizationMakeExternalForm(AuthorizationRef authorization,
 AuthorizationExternalForm *extForm);
# 400 "/System/Library/Frameworks/Security.framework/Headers/Authorization.h" 3
OSStatus AuthorizationCreateFromExternalForm(const AuthorizationExternalForm *extForm,
 AuthorizationRef *authorization);
# 415 "/System/Library/Frameworks/Security.framework/Headers/Authorization.h" 3
OSStatus AuthorizationFreeItemSet(AuthorizationItemSet *set);
# 439 "/System/Library/Frameworks/Security.framework/Headers/Authorization.h" 3
OSStatus AuthorizationExecuteWithPrivileges(AuthorizationRef authorization,
 const char *pathToTool,
 AuthorizationFlags options,
 char * const *arguments,
 FILE **communicationsPipe) __attribute__((deprecated,visibility("default")));
# 458 "/System/Library/Frameworks/Security.framework/Headers/Authorization.h" 3
OSStatus AuthorizationCopyPrivilegedReference(AuthorizationRef *authorization,
 AuthorizationFlags flags) __attribute__((deprecated,visibility("default")));
# 71 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/AuthorizationTags.h" 1 3
# 72 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/AuthorizationDB.h" 1 3
# 109 "/System/Library/Frameworks/Security.framework/Headers/AuthorizationDB.h" 3
OSStatus AuthorizationRightGet(const char *rightName,
 CFDictionaryRef *rightDefinition);
# 133 "/System/Library/Frameworks/Security.framework/Headers/AuthorizationDB.h" 3
OSStatus AuthorizationRightSet(AuthorizationRef authRef,
 const char *rightName,
 CFTypeRef rightDefinition,
 CFStringRef descriptionKey,
 CFBundleRef bundle,
 CFStringRef localeTableName);
# 151 "/System/Library/Frameworks/Security.framework/Headers/AuthorizationDB.h" 3
OSStatus AuthorizationRightRemove(AuthorizationRef authRef,
 const char *rightName);
# 73 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3

# 1 "/System/Library/Frameworks/Security.framework/Headers/CMSDecoder.h" 1 3
# 48 "/System/Library/Frameworks/Security.framework/Headers/CMSDecoder.h" 3
typedef struct _CMSDecoder *CMSDecoderRef;

CFTypeID CMSDecoderGetTypeID(void);




enum {
 kCMSSignerUnsigned = 0,
 kCMSSignerValid,
 kCMSSignerNeedsDetachedContent,

 kCMSSignerInvalidSignature,
 kCMSSignerInvalidCert,

 kCMSSignerInvalidIndex
};
typedef uint32_t CMSSignerStatus;




OSStatus CMSDecoderCreate(
 CMSDecoderRef *cmsDecoderOut)
    __attribute__((visibility("default")));







OSStatus CMSDecoderUpdateMessage(
 CMSDecoderRef cmsDecoder,
 const void *msgBytes,
 size_t msgBytesLen)
    __attribute__((visibility("default")));







OSStatus CMSDecoderFinalizeMessage(
 CMSDecoderRef cmsDecoder)
    __attribute__((visibility("default")));
# 107 "/System/Library/Frameworks/Security.framework/Headers/CMSDecoder.h" 3
OSStatus CMSDecoderSetDetachedContent(
 CMSDecoderRef cmsDecoder,
 CFDataRef detachedContent)
    __attribute__((visibility("default")));






OSStatus CMSDecoderCopyDetachedContent(
 CMSDecoderRef cmsDecoder,
 CFDataRef *detachedContentOut)
    __attribute__((visibility("default")));
# 130 "/System/Library/Frameworks/Security.framework/Headers/CMSDecoder.h" 3
OSStatus CMSDecoderSetSearchKeychain(
 CMSDecoderRef cmsDecoder,
 CFTypeRef keychainOrArray)
    __attribute__((visibility("default")));






OSStatus CMSDecoderGetNumSigners(
 CMSDecoderRef cmsDecoder,
 size_t *numSignersOut)
    __attribute__((visibility("default")));
# 219 "/System/Library/Frameworks/Security.framework/Headers/CMSDecoder.h" 3
OSStatus CMSDecoderCopySignerStatus(
 CMSDecoderRef cmsDecoder,
 size_t signerIndex,
 CFTypeRef policyOrArray,
 Boolean evaluateSecTrust,
 CMSSignerStatus *signerStatusOut,
 SecTrustRef *secTrustOut,
 OSStatus *certVerifyResultCodeOut)
    __attribute__((visibility("default")));
# 238 "/System/Library/Frameworks/Security.framework/Headers/CMSDecoder.h" 3
OSStatus CMSDecoderCopySignerEmailAddress(
 CMSDecoderRef cmsDecoder,
 size_t signerIndex,
 CFStringRef *signerEmailAddressOut)
    __attribute__((visibility("default")));
# 253 "/System/Library/Frameworks/Security.framework/Headers/CMSDecoder.h" 3
OSStatus CMSDecoderCopySignerCert(
 CMSDecoderRef cmsDecoder,
 size_t signerIndex,
 SecCertificateRef *signerCertOut)
    __attribute__((visibility("default")));
# 266 "/System/Library/Frameworks/Security.framework/Headers/CMSDecoder.h" 3
OSStatus CMSDecoderIsContentEncrypted(
 CMSDecoderRef cmsDecoder,
 Boolean *isEncryptedOut)
    __attribute__((visibility("default")));
# 278 "/System/Library/Frameworks/Security.framework/Headers/CMSDecoder.h" 3
OSStatus CMSDecoderCopyEncapsulatedContentType(
 CMSDecoderRef cmsDecoder,
 CFDataRef *eContentTypeOut)
    __attribute__((visibility("default")));
# 291 "/System/Library/Frameworks/Security.framework/Headers/CMSDecoder.h" 3
OSStatus CMSDecoderCopyAllCerts(
 CMSDecoderRef cmsDecoder,
 CFArrayRef *certsOut)
    __attribute__((visibility("default")));







OSStatus CMSDecoderCopyContent(
 CMSDecoderRef cmsDecoder,
 CFDataRef *contentOut)
    __attribute__((visibility("default")));
# 75 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/CMSEncoder.h" 1 3
# 57 "/System/Library/Frameworks/Security.framework/Headers/CMSEncoder.h" 3
typedef struct _CMSEncoder *CMSEncoderRef;

CFTypeID CMSEncoderGetTypeID(void)
    __attribute__((visibility("default")));




OSStatus CMSEncoderCreate(
 CMSEncoderRef *cmsEncoderOut)
 __attribute__((visibility("default")));
# 79 "/System/Library/Frameworks/Security.framework/Headers/CMSEncoder.h" 3
OSStatus CMSEncoderAddSigners(
 CMSEncoderRef cmsEncoder,
 CFTypeRef signerOrArray)
    __attribute__((visibility("default")));






OSStatus CMSEncoderCopySigners(
 CMSEncoderRef cmsEncoder,
 CFArrayRef *signersOut)
    __attribute__((visibility("default")));
# 105 "/System/Library/Frameworks/Security.framework/Headers/CMSEncoder.h" 3
OSStatus CMSEncoderAddRecipients(
 CMSEncoderRef cmsEncoder,
 CFTypeRef recipientOrArray)
    __attribute__((visibility("default")));







OSStatus CMSEncoderCopyRecipients(
 CMSEncoderRef cmsEncoder,
 CFArrayRef *recipientsOut)
    __attribute__((visibility("default")));
# 132 "/System/Library/Frameworks/Security.framework/Headers/CMSEncoder.h" 3
OSStatus CMSEncoderSetHasDetachedContent(
 CMSEncoderRef cmsEncoder,
 Boolean detachedContent)
    __attribute__((visibility("default")));







OSStatus CMSEncoderGetHasDetachedContent(
 CMSEncoderRef cmsEncoder,
 Boolean *detachedContentOut)
    __attribute__((visibility("default")));
# 160 "/System/Library/Frameworks/Security.framework/Headers/CMSEncoder.h" 3
OSStatus CMSEncoderSetEncapsulatedContentType(
 CMSEncoderRef cmsEncoder,
 const CSSM_OID *eContentType)

    __attribute__((visibility("default")));
# 178 "/System/Library/Frameworks/Security.framework/Headers/CMSEncoder.h" 3
OSStatus CMSEncoderSetEncapsulatedContentTypeOID(
 CMSEncoderRef cmsEncoder,
 CFTypeRef eContentTypeOID)
    __attribute__((visibility("default")));
# 191 "/System/Library/Frameworks/Security.framework/Headers/CMSEncoder.h" 3
OSStatus CMSEncoderCopyEncapsulatedContentType(
 CMSEncoderRef cmsEncoder,
 CFDataRef *eContentTypeOut)
    __attribute__((visibility("default")));
# 216 "/System/Library/Frameworks/Security.framework/Headers/CMSEncoder.h" 3
OSStatus CMSEncoderAddSupportingCerts(
 CMSEncoderRef cmsEncoder,
 CFTypeRef certOrArray)
    __attribute__((visibility("default")));







OSStatus CMSEncoderCopySupportingCerts(
 CMSEncoderRef cmsEncoder,
 CFArrayRef *certsOut)
    __attribute__((visibility("default")));





enum {
 kCMSAttrNone = 0x0000,




    kCMSAttrSmimeCapabilities = 0x0001,



    kCMSAttrSmimeEncryptionKeyPrefs = 0x0002,




    kCMSAttrSmimeMSEncryptionKeyPrefs = 0x0004,



    kCMSAttrSigningTime = 0x0008
};
typedef uint32_t CMSSignedAttributes;






OSStatus CMSEncoderAddSignedAttributes(
 CMSEncoderRef cmsEncoder,
 CMSSignedAttributes signedAttributes)
    __attribute__((visibility("default")));




enum {
 kCMSCertificateNone = 0,
 kCMSCertificateSignerOnly,
 kCMSCertificateChain,

 kCMSCertificateChainWithRoot
};
typedef uint32_t CMSCertificateChainMode;
# 290 "/System/Library/Frameworks/Security.framework/Headers/CMSEncoder.h" 3
OSStatus CMSEncoderSetCertificateChainMode(
 CMSEncoderRef cmsEncoder,
 CMSCertificateChainMode chainMode)
    __attribute__((visibility("default")));





OSStatus CMSEncoderGetCertificateChainMode(
 CMSEncoderRef cmsEncoder,
 CMSCertificateChainMode *chainModeOut)
    __attribute__((visibility("default")));






OSStatus CMSEncoderUpdateContent(
 CMSEncoderRef cmsEncoder,
 const void *content,
 size_t contentLen)
    __attribute__((visibility("default")));





OSStatus CMSEncoderCopyEncodedContent(
 CMSEncoderRef cmsEncoder,
 CFDataRef *encodedContentOut)
    __attribute__((visibility("default")));
# 347 "/System/Library/Frameworks/Security.framework/Headers/CMSEncoder.h" 3
OSStatus CMSEncode(
 CFTypeRef signers,
 CFTypeRef recipients,
 const CSSM_OID *eContentType,
 Boolean detachedContent,
 CMSSignedAttributes signedAttributes,
 const void *content,
 size_t contentLen,
 CFDataRef *encodedContentOut)

    __attribute__((visibility("default")));
# 381 "/System/Library/Frameworks/Security.framework/Headers/CMSEncoder.h" 3
OSStatus CMSEncodeContent(
 CFTypeRef signers,
 CFTypeRef recipients,
 CFTypeRef eContentTypeOID,
 Boolean detachedContent,
 CMSSignedAttributes signedAttributes,
 const void *content,
 size_t contentLen,
 CFDataRef *encodedContentOut)
    __attribute__((visibility("default")));
# 76 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3

# 1 "/System/Library/Frameworks/Security.framework/Headers/CipherSuite.h" 1 3
# 37 "/System/Library/Frameworks/Security.framework/Headers/CipherSuite.h" 3
typedef UInt32 SSLCipherSuite;

enum
{ SSL_NULL_WITH_NULL_NULL = 0x0000,
    SSL_RSA_WITH_NULL_MD5 = 0x0001,
    SSL_RSA_WITH_NULL_SHA = 0x0002,
    SSL_RSA_EXPORT_WITH_RC4_40_MD5 = 0x0003,
    SSL_RSA_WITH_RC4_128_MD5 = 0x0004,
    SSL_RSA_WITH_RC4_128_SHA = 0x0005,
    SSL_RSA_EXPORT_WITH_RC2_CBC_40_MD5 = 0x0006,
    SSL_RSA_WITH_IDEA_CBC_SHA = 0x0007,
    SSL_RSA_EXPORT_WITH_DES40_CBC_SHA = 0x0008,
    SSL_RSA_WITH_DES_CBC_SHA = 0x0009,
    SSL_RSA_WITH_3DES_EDE_CBC_SHA = 0x000A,
    SSL_DH_DSS_EXPORT_WITH_DES40_CBC_SHA = 0x000B,
    SSL_DH_DSS_WITH_DES_CBC_SHA = 0x000C,
    SSL_DH_DSS_WITH_3DES_EDE_CBC_SHA = 0x000D,
    SSL_DH_RSA_EXPORT_WITH_DES40_CBC_SHA = 0x000E,
    SSL_DH_RSA_WITH_DES_CBC_SHA = 0x000F,
    SSL_DH_RSA_WITH_3DES_EDE_CBC_SHA = 0x0010,
    SSL_DHE_DSS_EXPORT_WITH_DES40_CBC_SHA = 0x0011,
    SSL_DHE_DSS_WITH_DES_CBC_SHA = 0x0012,
    SSL_DHE_DSS_WITH_3DES_EDE_CBC_SHA = 0x0013,
    SSL_DHE_RSA_EXPORT_WITH_DES40_CBC_SHA = 0x0014,
    SSL_DHE_RSA_WITH_DES_CBC_SHA = 0x0015,
    SSL_DHE_RSA_WITH_3DES_EDE_CBC_SHA = 0x0016,
    SSL_DH_anon_EXPORT_WITH_RC4_40_MD5 = 0x0017,
    SSL_DH_anon_WITH_RC4_128_MD5 = 0x0018,
    SSL_DH_anon_EXPORT_WITH_DES40_CBC_SHA = 0x0019,
    SSL_DH_anon_WITH_DES_CBC_SHA = 0x001A,
    SSL_DH_anon_WITH_3DES_EDE_CBC_SHA = 0x001B,
    SSL_FORTEZZA_DMS_WITH_NULL_SHA = 0x001C,
    SSL_FORTEZZA_DMS_WITH_FORTEZZA_CBC_SHA = 0x001D,


 TLS_RSA_WITH_AES_128_CBC_SHA = 0x002F,
 TLS_DH_DSS_WITH_AES_128_CBC_SHA = 0x0030,
 TLS_DH_RSA_WITH_AES_128_CBC_SHA = 0x0031,
 TLS_DHE_DSS_WITH_AES_128_CBC_SHA = 0x0032,
 TLS_DHE_RSA_WITH_AES_128_CBC_SHA = 0x0033,
 TLS_DH_anon_WITH_AES_128_CBC_SHA = 0x0034,
 TLS_RSA_WITH_AES_256_CBC_SHA = 0x0035,
 TLS_DH_DSS_WITH_AES_256_CBC_SHA = 0x0036,
 TLS_DH_RSA_WITH_AES_256_CBC_SHA = 0x0037,
 TLS_DHE_DSS_WITH_AES_256_CBC_SHA = 0x0038,
 TLS_DHE_RSA_WITH_AES_256_CBC_SHA = 0x0039,
 TLS_DH_anon_WITH_AES_256_CBC_SHA = 0x003A,


 TLS_ECDH_ECDSA_WITH_NULL_SHA = 0xC001,
 TLS_ECDH_ECDSA_WITH_RC4_128_SHA = 0xC002,
 TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA = 0xC003,
 TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA = 0xC004,
 TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA = 0xC005,
 TLS_ECDHE_ECDSA_WITH_NULL_SHA = 0xC006,
 TLS_ECDHE_ECDSA_WITH_RC4_128_SHA = 0xC007,
 TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA = 0xC008,
 TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA = 0xC009,
 TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA = 0xC00A,
 TLS_ECDH_RSA_WITH_NULL_SHA = 0xC00B,
 TLS_ECDH_RSA_WITH_RC4_128_SHA = 0xC00C,
 TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA = 0xC00D,
 TLS_ECDH_RSA_WITH_AES_128_CBC_SHA = 0xC00E,
 TLS_ECDH_RSA_WITH_AES_256_CBC_SHA = 0xC00F,
 TLS_ECDHE_RSA_WITH_NULL_SHA = 0xC010,
 TLS_ECDHE_RSA_WITH_RC4_128_SHA = 0xC011,
 TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA = 0xC012,
 TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA = 0xC013,
 TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA = 0xC014,
 TLS_ECDH_anon_WITH_NULL_SHA = 0xC015,
 TLS_ECDH_anon_WITH_RC4_128_SHA = 0xC016,
 TLS_ECDH_anon_WITH_3DES_EDE_CBC_SHA = 0xC017,
 TLS_ECDH_anon_WITH_AES_128_CBC_SHA = 0xC018,
 TLS_ECDH_anon_WITH_AES_256_CBC_SHA = 0xC019,





    SSL_RSA_WITH_RC2_CBC_MD5 = 0xFF80,
    SSL_RSA_WITH_IDEA_CBC_MD5 = 0xFF81,
    SSL_RSA_WITH_DES_CBC_MD5 = 0xFF82,
    SSL_RSA_WITH_3DES_EDE_CBC_MD5 = 0xFF83,
    SSL_NO_SUCH_CIPHERSUITE = 0xFFFF
};
# 78 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 1 3
# 75 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
struct SSLContext;
typedef struct SSLContext *SSLContextRef;


typedef const void * SSLConnectionRef;


typedef enum {
 kSSLProtocolUnknown,
 kSSLProtocol2,
 kSSLProtocol3,
 kSSLProtocol3Only,

 kTLSProtocol1,
 kTLSProtocol1Only,
 kSSLProtocolAll
} SSLProtocol;


typedef enum {







 kSSLSessionOptionBreakOnServerAuth,




 kSSLSessionOptionBreakOnCertRequested
} SSLSessionOption;


typedef enum {
 kSSLIdle,
 kSSLHandshake,
 kSSLConnected,
 kSSLClosed,
 kSSLAborted
} SSLSessionState;





typedef enum {

 kSSLClientCertNone,

 kSSLClientCertRequested,






 kSSLClientCertSent,




 kSSLClientCertRejected
} SSLClientCertificateState;
# 159 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
typedef OSStatus
(*SSLReadFunc) (SSLConnectionRef connection,
        void *data,


        size_t *dataLength);
typedef OSStatus
(*SSLWriteFunc) (SSLConnectionRef connection,
        const void *data,
        size_t *dataLength);
# 182 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
enum {
 errSSLProtocol = -9800,
 errSSLNegotiation = -9801,
 errSSLFatalAlert = -9802,
 errSSLWouldBlock = -9803,
    errSSLSessionNotFound = -9804,
    errSSLClosedGraceful = -9805,
    errSSLClosedAbort = -9806,
    errSSLXCertChainInvalid = -9807,
    errSSLBadCert = -9808,
 errSSLCrypto = -9809,
 errSSLInternal = -9810,
 errSSLModuleAttach = -9811,
    errSSLUnknownRootCert = -9812,
    errSSLNoRootCert = -9813,
 errSSLCertExpired = -9814,
 errSSLCertNotYetValid = -9815,
 errSSLClosedNoNotify = -9816,
 errSSLBufferOverflow = -9817,
 errSSLBadCipherSuite = -9818,


 errSSLPeerUnexpectedMsg = -9819,
 errSSLPeerBadRecordMac = -9820,
 errSSLPeerDecryptionFail = -9821,
 errSSLPeerRecordOverflow = -9822,
 errSSLPeerDecompressFail = -9823,
 errSSLPeerHandshakeFail = -9824,
 errSSLPeerBadCert = -9825,
 errSSLPeerUnsupportedCert = -9826,
 errSSLPeerCertRevoked = -9827,
 errSSLPeerCertExpired = -9828,
 errSSLPeerCertUnknown = -9829,
 errSSLIllegalParam = -9830,
 errSSLPeerUnknownCA = -9831,
 errSSLPeerAccessDenied = -9832,
 errSSLPeerDecodeError = -9833,
 errSSLPeerDecryptError = -9834,
 errSSLPeerExportRestriction = -9835,
 errSSLPeerProtocolVersion = -9836,
 errSSLPeerInsufficientSecurity = -9837,
 errSSLPeerInternalError = -9838,
 errSSLPeerUserCancelled = -9839,
 errSSLPeerNoRenegotiation = -9840,


 errSSLServerAuthCompleted = -9841,
 errSSLClientCertRequested = -9842,


 errSSLHostNameMismatch = -9843,
 errSSLConnectionRefused = -9844,
 errSSLDecryptionFail = -9845,
 errSSLBadRecordMac = -9846,
 errSSLRecordOverflow = -9847,
 errSSLBadConfiguration = -9848,
 errSSLLast = -9849
};
# 249 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLNewContext (Boolean isServer,
        SSLContextRef *contextPtr);




OSStatus
SSLDisposeContext (SSLContextRef context);




OSStatus
SSLGetSessionState (SSLContextRef context,
        SSLSessionState *state);





OSStatus
SSLSetSessionOption (SSLContextRef context,
        SSLSessionOption option,
        Boolean value);




OSStatus
SSLGetSessionOption (SSLContextRef context,
        SSLSessionOption option,
        Boolean *value);
# 292 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLSetIOFuncs (SSLContextRef context,
        SSLReadFunc read,
        SSLWriteFunc write);
# 310 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLSetProtocolVersionEnabled (SSLContextRef context,
        SSLProtocol protocol,
        Boolean enable);




OSStatus
SSLGetProtocolVersionEnabled(SSLContextRef context,
        SSLProtocol protocol,
        Boolean *enable);
# 332 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLSetProtocolVersion (SSLContextRef context,
        SSLProtocol version);
# 344 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLGetProtocolVersion (SSLContextRef context,
        SSLProtocol *protocol);
# 374 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLSetCertificate (SSLContextRef context,
        CFArrayRef certRefs);
# 388 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLSetConnection (SSLContextRef context,
        SSLConnectionRef connection);

OSStatus
SSLGetConnection (SSLContextRef context,
        SSLConnectionRef *connection);
# 403 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLSetPeerDomainName (SSLContextRef context,
        const char *peerName,
        size_t peerNameLen);




OSStatus
SSLGetPeerDomainNameLength (SSLContextRef context,
        size_t *peerNameLen);




OSStatus
SSLGetPeerDomainName (SSLContextRef context,
        char *peerName,
        size_t *peerNameLen);







OSStatus
SSLGetNegotiatedProtocolVersion (SSLContextRef context,
          SSLProtocol *protocol);







OSStatus
SSLGetNumberSupportedCiphers (SSLContextRef context,
         size_t *numCiphers);

OSStatus
SSLGetSupportedCiphers (SSLContextRef context,
         SSLCipherSuite *ciphers,
         size_t *numCiphers);







OSStatus
SSLSetEnabledCiphers (SSLContextRef context,
        const SSLCipherSuite *ciphers,
        size_t numCiphers);







OSStatus
SSLGetNumberEnabledCiphers (SSLContextRef context,
        size_t *numCiphers);

OSStatus
SSLGetEnabledCiphers (SSLContextRef context,
        SSLCipherSuite *ciphers,
        size_t *numCiphers);
# 481 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLSetEnableCertVerify (SSLContextRef context,
        Boolean enableVerify);

OSStatus
SSLGetEnableCertVerify (SSLContextRef context,
        Boolean *enableVerify);
# 496 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLSetAllowsExpiredCerts (SSLContextRef context,
        Boolean allowsExpired);




OSStatus
SSLGetAllowsExpiredCerts (SSLContextRef context,
        Boolean *allowsExpired);







OSStatus
SSLSetAllowsExpiredRoots (SSLContextRef context,
        Boolean allowsExpired);

OSStatus
SSLGetAllowsExpiredRoots (SSLContextRef context,
        Boolean *allowsExpired);
# 536 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLSetAllowsAnyRoot (SSLContextRef context,
        Boolean anyRoot);




OSStatus
SSLGetAllowsAnyRoot (SSLContextRef context,
        Boolean *anyRoot);
# 559 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLSetTrustedRoots (SSLContextRef context,
        CFArrayRef trustedRoots,
        Boolean replaceExisting);
# 573 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLGetTrustedRoots (SSLContextRef context,
        CFArrayRef *trustedRoots)
        __attribute__((deprecated));
# 585 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLCopyTrustedRoots (SSLContextRef context,
        CFArrayRef *trustedRoots);
# 603 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLGetPeerCertificates (SSLContextRef context,
        CFArrayRef *certs)
        __attribute__((deprecated));
# 619 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLCopyPeerCertificates (SSLContextRef context,
        CFArrayRef *certs);






OSStatus
SSLCopyPeerTrust (SSLContextRef context,
        SecTrustRef *trust);
# 646 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLSetPeerID (SSLContextRef context,
        const void *peerID,
        size_t peerIDLen);





OSStatus
SSLGetPeerID (SSLContextRef context,
        const void **peerID,
        size_t *peerIDLen);





OSStatus
SSLGetNegotiatedCipher (SSLContextRef context,
        SSLCipherSuite *cipherSuite);
# 705 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLSetEncryptionCertificate (SSLContextRef context,
        CFArrayRef certRefs);







typedef enum {
 kNeverAuthenticate,
 kAlwaysAuthenticate,
 kTryAuthenticate

} SSLAuthenticate;

OSStatus
SSLSetClientSideAuthenticate (SSLContextRef context,
         SSLAuthenticate auth);





OSStatus
SSLAddDistinguishedName (SSLContextRef context,
        const void *derDN,
        size_t derDNLen);
# 748 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLSetCertificateAuthorities(SSLContextRef context,
        CFTypeRef certificateOrArray,
        Boolean replaceExisting);







OSStatus
SSLCopyCertificateAuthorities(SSLContextRef context,
         CFArrayRef *certificates);
# 776 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLCopyDistinguishedNames (SSLContextRef context,
        CFArrayRef *names);
# 787 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLGetClientCertificateState (SSLContextRef context,
         SSLClientCertificateState *clientState);







OSStatus SSLSetDiffieHellmanParams (SSLContextRef context,
          const void *dhParams,
          size_t dhParamsLen);





OSStatus SSLGetDiffieHellmanParams (SSLContextRef context,
          const void **dhParams,
          size_t *dhParamsLen);






OSStatus SSLSetRsaBlinding (SSLContextRef context,
          Boolean blinding);

OSStatus SSLGetRsaBlinding (SSLContextRef context,
          Boolean *blinding);
# 870 "/System/Library/Frameworks/Security.framework/Headers/SecureTransport.h" 3
OSStatus
SSLHandshake (SSLContextRef context);






OSStatus
SSLWrite (SSLContextRef context,
        const void * data,
        size_t dataLength,
        size_t *processed);






OSStatus
SSLRead (SSLContextRef context,
        void * data,
        size_t dataLength,
        size_t *processed);






OSStatus
SSLGetBufferedReadSize (SSLContextRef context,
        size_t *bufSize);




OSStatus
SSLClose (SSLContextRef context);
# 79 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3


# 1 "/System/Library/Frameworks/Security.framework/Headers/SecTransform.h" 1 3
# 29 "/System/Library/Frameworks/Security.framework/Headers/SecTransform.h" 3

# 72 "/System/Library/Frameworks/Security.framework/Headers/SecTransform.h" 3
extern const CFStringRef kSecTransformErrorDomain;
# 81 "/System/Library/Frameworks/Security.framework/Headers/SecTransform.h" 3
extern const CFStringRef kSecTransformPreviousErrorKey;






extern const CFStringRef kSecTransformAbortOriginatorKey;
# 178 "/System/Library/Frameworks/Security.framework/Headers/SecTransform.h" 3
enum
{
 kSecTransformErrorAttributeNotFound = 1,
 kSecTransformErrorInvalidOperation = 2,
 kSecTransformErrorNotInitializedCorrectly = 3,
 kSecTransformErrorMoreThanOneOutput = 4,
 kSecTransformErrorInvalidInputDictionary = 5,
 kSecTransformErrorInvalidAlgorithm = 6,
 kSecTransformErrorInvalidLength = 7,
 kSecTransformErrorInvalidType = 8,
 kSecTransformErrorInvalidInput = 10,
   kSecTransformErrorNameAlreadyRegistered = 11,
   kSecTransformErrorUnsupportedAttribute = 12,
 kSecTransformOperationNotSupportedOnGroup = 13,
 kSecTransformErrorMissingParameter = 14,
 kSecTransformErrorInvalidConnection = 15,
 kSecTransformTransformIsExecuting = 16,
 kSecTransformInvalidOverride = 17,
 kSecTransformTransformIsNotRegistered = 18,
 kSecTransformErrorAbortInProgress = 19,
 kSecTransformErrorAborted = 20,
 kSecTransformInvalidArgument = 21

};

typedef CFTypeRef SecTransformRef;
typedef CFTypeRef SecGroupTransformRef;







extern CFTypeID SecTransformGetTypeID(void);
# 221 "/System/Library/Frameworks/Security.framework/Headers/SecTransform.h" 3
extern CFTypeID SecGroupTransformGetTypeID(void);







extern const CFStringRef kSecTransformInputAttributeName __attribute__((visibility("default")));





extern const CFStringRef kSecTransformOutputAttributeName __attribute__((visibility("default")));
# 246 "/System/Library/Frameworks/Security.framework/Headers/SecTransform.h" 3
extern const CFStringRef kSecTransformDebugAttributeName __attribute__((visibility("default")));





extern const CFStringRef kSecTransformTransformName __attribute__((visibility("default")));





extern const CFStringRef kSecTransformAbortAttributeName __attribute__((visibility("default")));
# 279 "/System/Library/Frameworks/Security.framework/Headers/SecTransform.h" 3
extern
SecTransformRef SecTransformCreateFromExternalRepresentation(
        CFDictionaryRef dictionary,
        CFErrorRef *error)
        __attribute__((visibility("default")));
# 304 "/System/Library/Frameworks/Security.framework/Headers/SecTransform.h" 3
extern
CFDictionaryRef SecTransformCopyExternalRepresentation(
          SecTransformRef transformRef)
       __attribute__((visibility("default")));
# 330 "/System/Library/Frameworks/Security.framework/Headers/SecTransform.h" 3
extern
SecGroupTransformRef SecTransformCreateGroupTransform(void);
# 429 "/System/Library/Frameworks/Security.framework/Headers/SecTransform.h" 3
extern
SecGroupTransformRef SecTransformConnectTransforms(SecTransformRef sourceTransformRef,
         CFStringRef sourceAttributeName,
         SecTransformRef destinationTransformRef,
          CFStringRef destinationAttributeName,
         SecGroupTransformRef group,
         CFErrorRef *error)
      __attribute__((visibility("default")));
# 467 "/System/Library/Frameworks/Security.framework/Headers/SecTransform.h" 3
extern
Boolean SecTransformSetAttribute(SecTransformRef transformRef,
        CFStringRef key,
        CFTypeRef value,
        CFErrorRef *error)
        __attribute__((visibility("default")));
# 492 "/System/Library/Frameworks/Security.framework/Headers/SecTransform.h" 3
extern
CFTypeRef SecTransformGetAttribute(SecTransformRef transformRef,
           CFStringRef key)
        __attribute__((visibility("default")));
# 517 "/System/Library/Frameworks/Security.framework/Headers/SecTransform.h" 3
extern
SecTransformRef SecTransformFindByName(SecGroupTransformRef transform,
        CFStringRef name)
        __attribute__((visibility("default")));
# 558 "/System/Library/Frameworks/Security.framework/Headers/SecTransform.h" 3
extern
CFTypeRef SecTransformExecute(SecTransformRef transformRef, CFErrorRef* errorRef)
         __attribute__((visibility("default")));
# 579 "/System/Library/Frameworks/Security.framework/Headers/SecTransform.h" 3
typedef void (^SecMessageBlock)(CFTypeRef message, CFErrorRef error,
        Boolean isFinal);
# 609 "/System/Library/Frameworks/Security.framework/Headers/SecTransform.h" 3
extern
void SecTransformExecuteAsync(SecTransformRef transformRef,
       dispatch_queue_t deliveryQueue,
       SecMessageBlock deliveryBlock)
         __attribute__((visibility("default")));



# 82 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 1 3
# 31 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3

# 306 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
enum
{
    kSecTransformMetaAttributeValue,
    kSecTransformMetaAttributeName,
    kSecTransformMetaAttributeRef,
    kSecTransformMetaAttributeRequired,
    kSecTransformMetaAttributeRequiresOutboundConnection,
    kSecTransformMetaAttributeDeferred,
    kSecTransformMetaAttributeStream,
    kSecTransformMetaAttributeCanCycle,
    kSecTransformMetaAttributeExternalize,
    kSecTransformMetaAttributeHasOutboundConnections,
    kSecTransformMetaAttributeHasInboundConnection
};

typedef CFIndex SecTransformMetaAttributeType;
# 331 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
typedef CFTypeRef SecTransformAttributeRef;
# 340 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
typedef CFTypeRef SecTransformStringOrAttributeRef;
# 405 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
typedef CFTypeRef (^SecTransformActionBlock)(void);
# 427 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
typedef CFTypeRef (^SecTransformAttributeActionBlock)(
                                SecTransformAttributeRef attribute,
                                CFTypeRef value);
# 457 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
typedef CFTypeRef (^SecTransformDataBlock)(CFTypeRef data);
# 473 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
typedef CFErrorRef (^SecTransformInstanceBlock)(void);
# 482 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
typedef const struct OpaqueSecTransformImplementation* SecTransformImplementationRef;
# 532 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
extern
CFErrorRef SecTransformSetAttributeAction(SecTransformImplementationRef ref,
                                CFStringRef action,
                                SecTransformStringOrAttributeRef attribute,
                                SecTransformAttributeActionBlock newAction);
# 586 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
extern
CFErrorRef SecTransformSetDataAction(SecTransformImplementationRef ref,
                                    CFStringRef action,
                                    SecTransformDataBlock newAction);
# 636 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
extern
CFErrorRef SecTransformSetTransformAction(SecTransformImplementationRef ref,
                                CFStringRef action,
                                SecTransformActionBlock newAction);
# 659 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
extern
CFTypeRef SecTranformCustomGetAttribute(SecTransformImplementationRef ref,
                                SecTransformStringOrAttributeRef attribute,
                                SecTransformMetaAttributeType type);
# 689 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
extern
CFTypeRef SecTransformCustomSetAttribute(SecTransformImplementationRef ref,
                                    SecTransformStringOrAttributeRef attribute,
                                    SecTransformMetaAttributeType type,
                                    CFTypeRef value);
# 714 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
extern
CFTypeRef SecTransformPushbackAttribute(SecTransformImplementationRef ref,
                                SecTransformStringOrAttributeRef attribute,
                                CFTypeRef value);
# 746 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
typedef SecTransformInstanceBlock (*SecTransformCreateFP)(CFStringRef name,
                            SecTransformRef newTransform,
                            SecTransformImplementationRef ref);
# 763 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
extern const CFStringRef kSecTransformActionCanExecute;







extern const CFStringRef kSecTransformActionStartingExecution;
# 780 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
extern const CFStringRef kSecTransformActionFinalize;
# 791 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
extern const CFStringRef kSecTransformActionExternalizeExtraData;
# 800 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
extern const CFStringRef kSecTransformActionProcessData;
# 813 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
extern const CFStringRef kSecTransformActionInternalizeExtraData;
# 825 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
extern const CFStringRef kSecTransformActionAttributeNotification;
# 835 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
extern const CFStringRef kSecTransformActionAttributeValidation;
# 860 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
extern
Boolean SecTransformRegister(CFStringRef uniqueName,
                                    SecTransformCreateFP createTransformFunction,
                                    CFErrorRef* error)
                            __attribute__((visibility("default")));
# 883 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
extern
SecTransformRef SecTransformCreate(CFStringRef name, CFErrorRef *error)
                            __attribute__((visibility("default")));
# 914 "/System/Library/Frameworks/Security.framework/Headers/SecCustomTransform.h" 3
extern
CFTypeRef SecTransformNoData(void);


# 83 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecDecodeTransform.h" 1 3
# 27 "/System/Library/Frameworks/Security.framework/Headers/SecDecodeTransform.h" 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecEncodeTransform.h" 1 3
# 27 "/System/Library/Frameworks/Security.framework/Headers/SecEncodeTransform.h" 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecTransform.h" 1 3
# 28 "/System/Library/Frameworks/Security.framework/Headers/SecEncodeTransform.h" 2 3
# 36 "/System/Library/Frameworks/Security.framework/Headers/SecEncodeTransform.h" 3
extern const CFStringRef kSecBase64Encoding;




extern const CFStringRef kSecBase32Encoding;




extern const CFStringRef kSecZLibEncoding;







extern const CFStringRef kSecEncodeLineLengthAttribute;
extern const CFStringRef kSecEncodeTypeAttribute;
extern const CFStringRef kSecCompressionRatio;
# 77 "/System/Library/Frameworks/Security.framework/Headers/SecEncodeTransform.h" 3
SecTransformRef SecEncodeTransformCreate(CFTypeRef encodeType,
           CFErrorRef* error
           )
__attribute__((visibility("default")));
# 28 "/System/Library/Frameworks/Security.framework/Headers/SecDecodeTransform.h" 2 3
# 39 "/System/Library/Frameworks/Security.framework/Headers/SecDecodeTransform.h" 3
 extern const CFStringRef kSecDecodeTypeAttribute;
# 60 "/System/Library/Frameworks/Security.framework/Headers/SecDecodeTransform.h" 3
 SecTransformRef SecDecodeTransformCreate(CFTypeRef DecodeType,
            CFErrorRef* error
            )
 __attribute__((visibility("default")));
# 84 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecDigestTransform.h" 1 3
# 39 "/System/Library/Frameworks/Security.framework/Headers/SecDigestTransform.h" 3
extern const CFStringRef kSecDigestMD2;





extern const CFStringRef kSecDigestMD4;





extern const CFStringRef kSecDigestMD5;





extern const CFStringRef kSecDigestSHA1;





extern const CFStringRef kSecDigestSHA2;





extern const CFStringRef kSecDigestHMACMD5;





extern const CFStringRef kSecDigestHMACSHA1;





extern const CFStringRef kSecDigestHMACSHA2;







extern const CFStringRef kSecDigestTypeAttribute;






extern const CFStringRef kSecDigestLengthAttribute;
# 105 "/System/Library/Frameworks/Security.framework/Headers/SecDigestTransform.h" 3
extern const CFStringRef kSecDigestHMACKeyAttribute;
# 128 "/System/Library/Frameworks/Security.framework/Headers/SecDigestTransform.h" 3
SecTransformRef SecDigestTransformCreate(CFTypeRef digestType,
           CFIndex digestLength,
           CFErrorRef* error
           )
           __attribute__((visibility("default")));
# 141 "/System/Library/Frameworks/Security.framework/Headers/SecDigestTransform.h" 3
CFTypeID SecDigestTransformGetTypeID()
           __attribute__((visibility("default")));
# 85 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecEncodeTransform.h" 1 3
# 86 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecEncryptTransform.h" 1 3
# 46 "/System/Library/Frameworks/Security.framework/Headers/SecEncryptTransform.h" 3
 extern CFStringRef kSecPaddingNoneKey;

 extern CFStringRef kSecPaddingPKCS1Key;

 extern CFStringRef kSecPaddingPKCS5Key;

 extern CFStringRef kSecPaddingPKCS7Key;


 extern CFStringRef kSecModeNoneKey;

 extern CFStringRef kSecModeECBKey;

 extern CFStringRef kSecModeCBCKey;

 extern CFStringRef kSecModeCFBKey;

 extern CFStringRef kSecModeOFBKey;





 extern CFStringRef kSecEncryptKey;
# 78 "/System/Library/Frameworks/Security.framework/Headers/SecEncryptTransform.h" 3
 extern CFStringRef kSecPaddingKey;
# 87 "/System/Library/Frameworks/Security.framework/Headers/SecEncryptTransform.h" 3
 extern CFStringRef kSecIVKey;
# 96 "/System/Library/Frameworks/Security.framework/Headers/SecEncryptTransform.h" 3
 extern CFStringRef kSecEncryptionMode;
# 113 "/System/Library/Frameworks/Security.framework/Headers/SecEncryptTransform.h" 3
 SecTransformRef SecEncryptTransformCreate(SecKeyRef keyRef,
             CFErrorRef* error)
 __attribute__((visibility("default")));
# 131 "/System/Library/Frameworks/Security.framework/Headers/SecEncryptTransform.h" 3
 SecTransformRef SecDecryptTransformCreate(SecKeyRef keyRef,
             CFErrorRef* error)
 __attribute__((visibility("default")));







 CFTypeID SecDecryptTransformGetTypeID()
 __attribute__((visibility("default")));







 CFTypeID SecEncryptTransformGetTypeID()
 __attribute__((visibility("default")));
# 87 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecSignVerifyTransform.h" 1 3
# 36 "/System/Library/Frameworks/Security.framework/Headers/SecSignVerifyTransform.h" 3
 extern CFStringRef kSecKeyAttributeName, kSecSignatureAttributeName, kSecInputIsAttributeName;

 extern CFStringRef kSecInputIsPlainText, kSecInputIsDigest, kSecInputIsRaw;
# 58 "/System/Library/Frameworks/Security.framework/Headers/SecSignVerifyTransform.h" 3
 SecTransformRef SecSignTransformCreate(SecKeyRef key,
            CFErrorRef* error
            )
 __attribute__((visibility("default")));
# 83 "/System/Library/Frameworks/Security.framework/Headers/SecSignVerifyTransform.h" 3
 SecTransformRef SecVerifyTransformCreate(SecKeyRef key,
            CFDataRef signature,
            CFErrorRef* error
            )
 __attribute__((visibility("default")));
# 88 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecReadTransform.h" 1 3
# 1 "/System/Library/Frameworks/Security.framework/Headers/SecTransformReadTransform.h" 1 3
# 58 "/System/Library/Frameworks/Security.framework/Headers/SecTransformReadTransform.h" 3
SecTransformRef SecTransformCreateReadTransformWithReadStream(CFReadStreamRef inputStream)
 __attribute__((visibility("default")));
# 2 "/System/Library/Frameworks/Security.framework/Headers/SecReadTransform.h" 2 3
# 89 "/System/Library/Frameworks/Security.framework/Headers/Security.h" 2 3
# 36 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 2 3
# 71 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
typedef const struct __SCPreferences * SCPreferencesRef;
# 83 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
enum {
 kSCPreferencesNotificationCommit = 1<<0,
 kSCPreferencesNotificationApply = 1<<1
};

typedef uint32_t SCPreferencesNotification;
# 109 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
typedef struct {
 CFIndex version;
 void * info;
 const void *(*retain)(const void *info);
 void (*release)(const void *info);
 CFStringRef (*copyDescription)(const void *info);
} SCPreferencesContext;
# 126 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
typedef void (*SCPreferencesCallBack) (
     SCPreferencesRef prefs,
     SCPreferencesNotification notificationType,
     void *info
     );








CFTypeID
SCPreferencesGetTypeID (void) __attribute__((visibility("default")));
# 159 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
SCPreferencesRef
SCPreferencesCreate (
     CFAllocatorRef allocator,
     CFStringRef name,
     CFStringRef prefsID
     ) __attribute__((visibility("default")));
# 187 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
SCPreferencesRef
SCPreferencesCreateWithAuthorization (
     CFAllocatorRef allocator,
     CFStringRef name,
     CFStringRef prefsID,
     AuthorizationRef authorization
     ) __attribute__((visibility("default")));
# 210 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
Boolean
SCPreferencesLock (
     SCPreferencesRef prefs,
     Boolean wait
     ) __attribute__((visibility("default")));
# 233 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
Boolean
SCPreferencesCommitChanges (
     SCPreferencesRef prefs
     ) __attribute__((visibility("default")));
# 246 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
Boolean
SCPreferencesApplyChanges (
     SCPreferencesRef prefs
     ) __attribute__((visibility("default")));
# 262 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
Boolean
SCPreferencesUnlock (
     SCPreferencesRef prefs
     ) __attribute__((visibility("default")));
# 275 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
CFDataRef
SCPreferencesGetSignature (
     SCPreferencesRef prefs
     ) __attribute__((visibility("default")));
# 287 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
CFArrayRef
SCPreferencesCopyKeyList (
     SCPreferencesRef prefs
     ) __attribute__((visibility("default")));
# 306 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
CFPropertyListRef
SCPreferencesGetValue (
     SCPreferencesRef prefs,
     CFStringRef key
     ) __attribute__((visibility("default")));
# 327 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
Boolean
SCPreferencesAddValue (
     SCPreferencesRef prefs,
     CFStringRef key,
     CFPropertyListRef value
     ) __attribute__((visibility("default")));
# 348 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
Boolean
SCPreferencesSetValue (
     SCPreferencesRef prefs,
     CFStringRef key,
     CFPropertyListRef value
     ) __attribute__((visibility("default")));
# 367 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
Boolean
SCPreferencesRemoveValue (
     SCPreferencesRef prefs,
     CFStringRef key
     ) __attribute__((visibility("default")));
# 386 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
Boolean
SCPreferencesSetCallback (
     SCPreferencesRef prefs,
     SCPreferencesCallBack callout,
     SCPreferencesContext *context
     ) __attribute__((visibility("default")));
# 406 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
Boolean
SCPreferencesScheduleWithRunLoop (
     SCPreferencesRef prefs,
     CFRunLoopRef runLoop,
     CFStringRef runLoopMode
     ) __attribute__((visibility("default")));
# 426 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
Boolean
SCPreferencesUnscheduleFromRunLoop (
     SCPreferencesRef prefs,
     CFRunLoopRef runLoop,
     CFStringRef runLoopMode
     ) __attribute__((visibility("default")));
# 442 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
Boolean
SCPreferencesSetDispatchQueue (
      SCPreferencesRef prefs,
      dispatch_queue_t queue
      ) __attribute__((visibility("default")));
# 459 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferences.h" 3
void
SCPreferencesSynchronize (
     SCPreferencesRef prefs
     ) __attribute__((visibility("default")));


# 122 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SystemConfiguration.h" 2 3
# 1 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferencesPath.h" 1 3
# 79 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferencesPath.h" 3

# 90 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferencesPath.h" 3
CFStringRef
SCPreferencesPathCreateUniqueChild (
     SCPreferencesRef prefs,
     CFStringRef prefix
     ) __attribute__((visibility("default")));
# 105 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferencesPath.h" 3
CFDictionaryRef
SCPreferencesPathGetValue (
     SCPreferencesRef prefs,
     CFStringRef path
     ) __attribute__((visibility("default")));
# 120 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferencesPath.h" 3
CFStringRef
SCPreferencesPathGetLink (
     SCPreferencesRef prefs,
     CFStringRef path
     ) __attribute__((visibility("default")));
# 135 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferencesPath.h" 3
Boolean
SCPreferencesPathSetValue (
     SCPreferencesRef prefs,
     CFStringRef path,
     CFDictionaryRef value
     ) __attribute__((visibility("default")));
# 152 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferencesPath.h" 3
Boolean
SCPreferencesPathSetLink (
     SCPreferencesRef prefs,
     CFStringRef path,
     CFStringRef link
     ) __attribute__((visibility("default")));
# 166 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferencesPath.h" 3
Boolean
SCPreferencesPathRemoveValue (
     SCPreferencesRef prefs,
     CFStringRef path
     ) __attribute__((visibility("default")));


# 123 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SystemConfiguration.h" 2 3
# 1 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferencesSetSpecific.h" 1 3
# 45 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferencesSetSpecific.h" 3

# 60 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferencesSetSpecific.h" 3
Boolean
SCPreferencesSetComputerName (
     SCPreferencesRef prefs,
     CFStringRef name,
     CFStringEncoding nameEncoding
     ) __attribute__((visibility("default")));
# 82 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCPreferencesSetSpecific.h" 3
Boolean
SCPreferencesSetLocalHostName (
     SCPreferencesRef prefs,
     CFStringRef name
     ) __attribute__((visibility("default")));


# 124 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SystemConfiguration.h" 2 3


# 1 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCSchemaDefinitions.h" 1 3
# 2376 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCSchemaDefinitions.h" 3
  extern const CFStringRef kSCResvLink __attribute__((visibility("default")));





  extern const CFStringRef kSCResvInactive __attribute__((visibility("default")));





  extern const CFStringRef kSCPropInterfaceName __attribute__((visibility("default")));





  extern const CFStringRef kSCPropMACAddress __attribute__((visibility("default")));





  extern const CFStringRef kSCPropUserDefinedName __attribute__((visibility("default")));





  extern const CFStringRef kSCPropVersion __attribute__((visibility("default")));





  extern const CFStringRef kSCPrefCurrentSet __attribute__((visibility("default")));





  extern const CFStringRef kSCPrefNetworkServices __attribute__((visibility("default")));





  extern const CFStringRef kSCPrefSets __attribute__((visibility("default")));





  extern const CFStringRef kSCPrefSystem __attribute__((visibility("default")));





  extern const CFStringRef kSCCompNetwork __attribute__((visibility("default")));





  extern const CFStringRef kSCCompService __attribute__((visibility("default")));





  extern const CFStringRef kSCCompGlobal __attribute__((visibility("default")));





  extern const CFStringRef kSCCompHostNames __attribute__((visibility("default")));





  extern const CFStringRef kSCCompInterface __attribute__((visibility("default")));





  extern const CFStringRef kSCCompSystem __attribute__((visibility("default")));





  extern const CFStringRef kSCCompUsers __attribute__((visibility("default")));





  extern const CFStringRef kSCCompAnyRegex __attribute__((visibility("default")));





  extern const CFStringRef kSCEntNetAirPort __attribute__((visibility("default")));







  extern const CFStringRef kSCEntNetAppleTalk __attribute__((deprecated,visibility("default")));







  extern const CFStringRef kSCEntNetDHCP __attribute__((visibility("default")));





  extern const CFStringRef kSCEntNetDNS __attribute__((visibility("default")));





  extern const CFStringRef kSCEntNetEthernet __attribute__((visibility("default")));





  extern const CFStringRef kSCEntNetFireWire __attribute__((visibility("default")));





  extern const CFStringRef kSCEntNetInterface __attribute__((visibility("default")));





  extern const CFStringRef kSCEntNetIPSec __attribute__((visibility("default")));





  extern const CFStringRef kSCEntNetIPv4 __attribute__((visibility("default")));





  extern const CFStringRef kSCEntNetIPv6 __attribute__((visibility("default")));





  extern const CFStringRef kSCEntNetL2TP __attribute__((visibility("default")));





  extern const CFStringRef kSCEntNetLink __attribute__((visibility("default")));





  extern const CFStringRef kSCEntNetModem __attribute__((visibility("default")));







  extern const CFStringRef kSCEntNetNetInfo __attribute__((deprecated,visibility("default")));







  extern const CFStringRef kSCEntNetPPP __attribute__((visibility("default")));





  extern const CFStringRef kSCEntNetPPPoE __attribute__((visibility("default")));





  extern const CFStringRef kSCEntNetPPPSerial __attribute__((visibility("default")));





  extern const CFStringRef kSCEntNetPPTP __attribute__((visibility("default")));





  extern const CFStringRef kSCEntNetProxies __attribute__((visibility("default")));







  extern const CFStringRef kSCEntNetSMB __attribute__((visibility("default")));







  extern const CFStringRef kSCEntNet6to4 __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetOverridePrimary __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetServiceOrder __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPOverridePrimary __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetInterfaces __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetLocalHostName __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetAirPortAllowNetCreation __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetAirPortAuthPassword __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetAirPortAuthPasswordEncryption __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetAirPortJoinMode __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetAirPortPowerEnabled __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetAirPortPreferredNetwork __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetAirPortSavePasswords __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetAirPortJoinModeAutomatic __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetAirPortJoinModePreferred __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetAirPortJoinModeRanked __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetAirPortJoinModeRecent __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetAirPortJoinModeStrongest __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetAirPortAuthPasswordEncryptionKeychain __attribute__((visibility("default")));







  extern const CFStringRef kSCPropNetAppleTalkComputerName __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCPropNetAppleTalkComputerNameEncoding __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCPropNetAppleTalkConfigMethod __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCPropNetAppleTalkDefaultZone __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCPropNetAppleTalkNetworkID __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCPropNetAppleTalkNetworkRange __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCPropNetAppleTalkNodeID __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCPropNetAppleTalkSeedNetworkRange __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCPropNetAppleTalkSeedZones __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCValNetAppleTalkConfigMethodNode __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCValNetAppleTalkConfigMethodRouter __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCValNetAppleTalkConfigMethodSeedRouter __attribute__((deprecated,visibility("default")));







  extern const CFStringRef kSCPropNetDNSDomainName __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetDNSOptions __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetDNSSearchDomains __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetDNSSearchOrder __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetDNSServerAddresses __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetDNSServerPort __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetDNSServerTimeout __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetDNSSortList __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetDNSSupplementalMatchDomains __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetDNSSupplementalMatchOrders __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetEthernetMediaSubType __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetEthernetMediaOptions __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetEthernetMTU __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetInterfaceDeviceName __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetInterfaceHardware __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetInterfaceType __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetInterfaceSubType __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetInterfaceSupportsModemOnHold __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetInterfaceTypeEthernet __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetInterfaceTypeFireWire __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetInterfaceTypePPP __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetInterfaceType6to4 __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetInterfaceTypeIPSec __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetInterfaceSubTypePPPoE __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetInterfaceSubTypePPPSerial __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetInterfaceSubTypePPTP __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetInterfaceSubTypeL2TP __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPSecAuthenticationMethod __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPSecLocalCertificate __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPSecLocalIdentifier __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPSecLocalIdentifierType __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPSecSharedSecret __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPSecSharedSecretEncryption __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPSecConnectTime __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPSecRemoteAddress __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPSecStatus __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPSecXAuthEnabled __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPSecXAuthName __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPSecXAuthPassword __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPSecXAuthPasswordEncryption __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetIPSecAuthenticationMethodSharedSecret __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetIPSecAuthenticationMethodCertificate __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetIPSecAuthenticationMethodHybrid __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetIPSecLocalIdentifierTypeKeyID __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetIPSecSharedSecretEncryptionKeychain __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetIPSecXAuthPasswordEncryptionKeychain __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetIPSecXAuthPasswordEncryptionPrompt __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPv4Addresses __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPv4ConfigMethod __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPv4DHCPClientID __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPv4Router __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPv4SubnetMasks __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPv4DestAddresses __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPv4BroadcastAddresses __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetIPv4ConfigMethodAutomatic __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetIPv4ConfigMethodBOOTP __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetIPv4ConfigMethodDHCP __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetIPv4ConfigMethodINFORM __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetIPv4ConfigMethodLinkLocal __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetIPv4ConfigMethodManual __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetIPv4ConfigMethodPPP __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPv6Addresses __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPv6ConfigMethod __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPv6DestAddresses __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPv6Flags __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPv6PrefixLength __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetIPv6Router __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetIPv6ConfigMethodAutomatic __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetIPv6ConfigMethodLinkLocal __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetIPv6ConfigMethodManual __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetIPv6ConfigMethodRouterAdvertisement __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetIPv6ConfigMethod6to4 __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNet6to4Relay __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetLinkActive __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetLinkDetaching __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetModemAccessPointName __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetModemConnectionPersonality __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetModemConnectionScript __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetModemConnectSpeed __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetModemDataCompression __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetModemDeviceContextID __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetModemDeviceModel __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetModemDeviceVendor __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetModemDialMode __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetModemErrorCorrection __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetModemHoldCallWaitingAudibleAlert __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetModemHoldDisconnectOnAnswer __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetModemHoldEnabled __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetModemHoldReminder __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetModemHoldReminderTime __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetModemNote __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetModemPulseDial __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetModemSpeaker __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetModemSpeed __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetModemDialModeIgnoreDialTone __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetModemDialModeManual __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetModemDialModeWaitForDialTone __attribute__((visibility("default")));







  extern const CFStringRef kSCPropNetNetInfoBindingMethods __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCPropNetNetInfoServerAddresses __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCPropNetNetInfoServerTags __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCPropNetNetInfoBroadcastServerTag __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCValNetNetInfoBindingMethodsBroadcast __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCValNetNetInfoBindingMethodsDHCP __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCValNetNetInfoBindingMethodsManual __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCValNetNetInfoDefaultServerTag __attribute__((deprecated,visibility("default")));







  extern const CFStringRef kSCPropNetPPPACSPEnabled __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPConnectTime __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPDeviceLastCause __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPDialOnDemand __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPDisconnectOnFastUserSwitch __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPDisconnectOnIdle __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPDisconnectOnIdleTimer __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPDisconnectOnLogout __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPDisconnectOnSleep __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPDisconnectTime __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPIdleReminderTimer __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPIdleReminder __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPLastCause __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPLogfile __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPPlugins __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPRetryConnectTime __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPSessionTimer __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPStatus __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPUseSessionTimer __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPVerboseLogging __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPAuthEAPPlugins __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPAuthName __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPAuthPassword __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPAuthPasswordEncryption __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPAuthPrompt __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPAuthProtocol __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetPPPAuthPasswordEncryptionKeychain __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetPPPAuthPasswordEncryptionToken __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetPPPAuthPromptBefore __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetPPPAuthPromptAfter __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetPPPAuthProtocolCHAP __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetPPPAuthProtocolEAP __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetPPPAuthProtocolMSCHAP1 __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetPPPAuthProtocolMSCHAP2 __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetPPPAuthProtocolPAP __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPCommAlternateRemoteAddress __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPCommConnectDelay __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPCommDisplayTerminalWindow __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPCommRedialCount __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPCommRedialEnabled __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPCommRedialInterval __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPCommRemoteAddress __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPCommTerminalScript __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPCommUseTerminalScript __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPCCPEnabled __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPCCPMPPE40Enabled __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPCCPMPPE128Enabled __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPIPCPCompressionVJ __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPIPCPUsePeerDNS __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPLCPEchoEnabled __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPLCPEchoFailure __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPLCPEchoInterval __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPLCPCompressionACField __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPLCPCompressionPField __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPLCPMRU __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPLCPMTU __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPLCPReceiveACCM __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetPPPLCPTransmitACCM __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetL2TPIPSecSharedSecret __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetL2TPIPSecSharedSecretEncryption __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetL2TPTransport __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetL2TPIPSecSharedSecretEncryptionKeychain __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetL2TPTransportIP __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetL2TPTransportIPSec __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesExceptionsList __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesExcludeSimpleHostnames __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesFTPEnable __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesFTPPassive __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesFTPPort __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesFTPProxy __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesGopherEnable __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesGopherPort __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesGopherProxy __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesHTTPEnable __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesHTTPPort __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesHTTPProxy __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesHTTPSEnable __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesHTTPSPort __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesHTTPSProxy __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesRTSPEnable __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesRTSPPort __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesRTSPProxy __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesSOCKSEnable __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesSOCKSPort __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesSOCKSProxy __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesProxyAutoConfigEnable __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesProxyAutoConfigJavaScript __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesProxyAutoConfigURLString __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetProxiesProxyAutoDiscoveryEnable __attribute__((visibility("default")));







  extern const CFStringRef kSCPropNetSMBNetBIOSName __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetSMBNetBIOSNodeType __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetSMBNetBIOSScope __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCPropNetSMBWINSAddresses __attribute__((visibility("default")));





  extern const CFStringRef kSCPropNetSMBWorkgroup __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetSMBNetBIOSNodeTypeBroadcast __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetSMBNetBIOSNodeTypePeer __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetSMBNetBIOSNodeTypeMixed __attribute__((visibility("default")));





  extern const CFStringRef kSCValNetSMBNetBIOSNodeTypeHybrid __attribute__((visibility("default")));
# 4034 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCSchemaDefinitions.h" 3
  extern const CFStringRef kSCEntUsersConsoleUser __attribute__((visibility("default")));







  extern const CFStringRef kSCPropSystemComputerName __attribute__((visibility("default")));





  extern const CFStringRef kSCPropSystemComputerNameEncoding __attribute__((visibility("default")));





  extern const CFStringRef kSCDynamicStoreDomainFile __attribute__((visibility("default")));





  extern const CFStringRef kSCDynamicStoreDomainPlugin __attribute__((visibility("default")));





  extern const CFStringRef kSCDynamicStoreDomainSetup __attribute__((visibility("default")));





  extern const CFStringRef kSCDynamicStoreDomainState __attribute__((visibility("default")));





  extern const CFStringRef kSCDynamicStoreDomainPrefs __attribute__((visibility("default")));





  extern const CFStringRef kSCDynamicStorePropSetupCurrentSet __attribute__((visibility("default")));





  extern const CFStringRef kSCDynamicStorePropSetupLastUpdated __attribute__((visibility("default")));





  extern const CFStringRef kSCDynamicStorePropNetInterfaces __attribute__((visibility("default")));





  extern const CFStringRef kSCDynamicStorePropNetPrimaryInterface __attribute__((visibility("default")));





  extern const CFStringRef kSCDynamicStorePropNetPrimaryService __attribute__((visibility("default")));





  extern const CFStringRef kSCDynamicStorePropNetServiceIDs __attribute__((visibility("default")));







  extern const CFStringRef kSCPropUsersConsoleUserName __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCPropUsersConsoleUserUID __attribute__((deprecated,visibility("default")));





  extern const CFStringRef kSCPropUsersConsoleUserGID __attribute__((deprecated,visibility("default")));
# 127 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SystemConfiguration.h" 2 3


# 1 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 1 3
# 31 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
# 1 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SystemConfiguration.h" 1 3
# 32 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 2 3
# 52 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
       
       






typedef const struct __SCNetworkInterface * SCNetworkInterfaceRef;




extern const CFStringRef kSCNetworkInterfaceType6to4 __attribute__((visibility("default")));




extern const CFStringRef kSCNetworkInterfaceTypeBluetooth __attribute__((visibility("default")));




extern const CFStringRef kSCNetworkInterfaceTypeBond __attribute__((visibility("default")));




extern const CFStringRef kSCNetworkInterfaceTypeEthernet __attribute__((visibility("default")));




extern const CFStringRef kSCNetworkInterfaceTypeFireWire __attribute__((visibility("default")));




extern const CFStringRef kSCNetworkInterfaceTypeIEEE80211 __attribute__((visibility("default")));




extern const CFStringRef kSCNetworkInterfaceTypeIPSec __attribute__((visibility("default")));




extern const CFStringRef kSCNetworkInterfaceTypeIrDA __attribute__((visibility("default")));




extern const CFStringRef kSCNetworkInterfaceTypeL2TP __attribute__((visibility("default")));




extern const CFStringRef kSCNetworkInterfaceTypeModem __attribute__((visibility("default")));




extern const CFStringRef kSCNetworkInterfaceTypePPP __attribute__((visibility("default")));




extern const CFStringRef kSCNetworkInterfaceTypePPTP __attribute__((visibility("default")));




extern const CFStringRef kSCNetworkInterfaceTypeSerial __attribute__((visibility("default")));




extern const CFStringRef kSCNetworkInterfaceTypeVLAN __attribute__((visibility("default")));




extern const CFStringRef kSCNetworkInterfaceTypeWWAN __attribute__((visibility("default")));






extern const CFStringRef kSCNetworkInterfaceTypeIPv4 __attribute__((visibility("default")));







extern const SCNetworkInterfaceRef kSCNetworkInterfaceIPv4 __attribute__((visibility("default")));





       






typedef SCNetworkInterfaceRef SCBondInterfaceRef;






typedef const struct __SCBondStatus * SCBondStatusRef;
# 181 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
enum {
 kSCBondStatusOK = 0,
 kSCBondStatusLinkInvalid = 1,
 kSCBondStatusNoPartner = 2,
 kSCBondStatusNotInActiveGroup = 3,
 kSCBondStatusUnknown = 999
};




extern const CFStringRef kSCBondStatusDeviceAggregationStatus __attribute__((visibility("default")));




extern const CFStringRef kSCBondStatusDeviceCollecting __attribute__((visibility("default")));




extern const CFStringRef kSCBondStatusDeviceDistributing __attribute__((visibility("default")));





       






typedef SCNetworkInterfaceRef SCVLANInterfaceRef;






       
       






typedef const struct __SCNetworkProtocol * SCNetworkProtocolRef;






extern const CFStringRef kSCNetworkProtocolTypeAppleTalk __attribute__((deprecated,visibility("default")));




extern const CFStringRef kSCNetworkProtocolTypeDNS __attribute__((visibility("default")));




extern const CFStringRef kSCNetworkProtocolTypeIPv4 __attribute__((visibility("default")));




extern const CFStringRef kSCNetworkProtocolTypeIPv6 __attribute__((visibility("default")));




extern const CFStringRef kSCNetworkProtocolTypeProxies __attribute__((visibility("default")));




extern const CFStringRef kSCNetworkProtocolTypeSMB __attribute__((visibility("default")));





       
       






typedef const struct __SCNetworkService * SCNetworkServiceRef;






       
       






typedef const struct __SCNetworkSet * SCNetworkSetRef;



# 305 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
       
       





CFTypeID
SCNetworkInterfaceGetTypeID (void) __attribute__((visibility("default")));







CFArrayRef
SCNetworkInterfaceCopyAll (void) __attribute__((visibility("default")));
# 332 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFArrayRef
SCNetworkInterfaceGetSupportedInterfaceTypes (SCNetworkInterfaceRef interface) __attribute__((visibility("default")));
# 343 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFArrayRef
SCNetworkInterfaceGetSupportedProtocolTypes (SCNetworkInterfaceRef interface) __attribute__((visibility("default")));
# 357 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
SCNetworkInterfaceRef
SCNetworkInterfaceCreateWithInterface (SCNetworkInterfaceRef interface,
       CFStringRef interfaceType) __attribute__((visibility("default")));
# 369 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFStringRef
SCNetworkInterfaceGetBSDName (SCNetworkInterfaceRef interface) __attribute__((visibility("default")));
# 380 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFDictionaryRef
SCNetworkInterfaceGetConfiguration (SCNetworkInterfaceRef interface) __attribute__((visibility("default")));
# 392 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFDictionaryRef
SCNetworkInterfaceGetExtendedConfiguration (SCNetworkInterfaceRef interface,
       CFStringRef extendedType) __attribute__((visibility("default")));







CFStringRef
SCNetworkInterfaceGetHardwareAddressString (SCNetworkInterfaceRef interface) __attribute__((visibility("default")));
# 412 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
SCNetworkInterfaceRef
SCNetworkInterfaceGetInterface (SCNetworkInterfaceRef interface) __attribute__((visibility("default")));







CFStringRef
SCNetworkInterfaceGetInterfaceType (SCNetworkInterfaceRef interface) __attribute__((visibility("default")));
# 432 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFStringRef
SCNetworkInterfaceGetLocalizedDisplayName (SCNetworkInterfaceRef interface) __attribute__((visibility("default")));
# 442 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkInterfaceSetConfiguration (SCNetworkInterfaceRef interface,
       CFDictionaryRef config) __attribute__((visibility("default")));
# 453 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkInterfaceSetExtendedConfiguration (SCNetworkInterfaceRef interface,
       CFStringRef extendedType,
       CFDictionaryRef config) __attribute__((visibility("default")));

       
# 480 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkInterfaceCopyMediaOptions (SCNetworkInterfaceRef interface,
       CFDictionaryRef *current,
       CFDictionaryRef *active,
       CFArrayRef *available,
       Boolean filter) __attribute__((visibility("default")));
# 496 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFArrayRef
SCNetworkInterfaceCopyMediaSubTypes (CFArrayRef available) __attribute__((visibility("default")));
# 510 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFArrayRef
SCNetworkInterfaceCopyMediaSubTypeOptions (CFArrayRef available,
       CFStringRef subType) __attribute__((visibility("default")));
# 530 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkInterfaceCopyMTU (SCNetworkInterfaceRef interface,
       int *mtu_cur,
       int *mtu_min,
       int *mtu_max) __attribute__((visibility("default")));
# 545 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkInterfaceSetMediaOptions (SCNetworkInterfaceRef interface,
       CFStringRef subtype,
       CFArrayRef options) __attribute__((visibility("default")));
# 558 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkInterfaceSetMTU (SCNetworkInterfaceRef interface,
       int mtu) __attribute__((visibility("default")));
# 582 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkInterfaceForceConfigurationRefresh (SCNetworkInterfaceRef interface) __attribute__((visibility("default")));





       
       
# 599 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFArrayRef
SCBondInterfaceCopyAll (SCPreferencesRef prefs) __attribute__((visibility("default")));
# 610 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFArrayRef
SCBondInterfaceCopyAvailableMemberInterfaces (SCPreferencesRef prefs) __attribute__((visibility("default")));
# 620 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
SCBondInterfaceRef
SCBondInterfaceCreate (SCPreferencesRef prefs) __attribute__((visibility("default")));







Boolean
SCBondInterfaceRemove (SCBondInterfaceRef bond) __attribute__((visibility("default")));







CFArrayRef
SCBondInterfaceGetMemberInterfaces (SCBondInterfaceRef bond) __attribute__((visibility("default")));
# 648 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFDictionaryRef
SCBondInterfaceGetOptions (SCBondInterfaceRef bond) __attribute__((visibility("default")));
# 658 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCBondInterfaceSetMemberInterfaces (SCBondInterfaceRef bond,
       CFArrayRef members)
            __attribute__((visibility("default")));
# 670 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCBondInterfaceSetLocalizedDisplayName (SCBondInterfaceRef bond,
       CFStringRef newName) __attribute__((visibility("default")));
# 681 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCBondInterfaceSetOptions (SCBondInterfaceRef bond,
       CFDictionaryRef newOptions) __attribute__((visibility("default")));

       
# 694 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
SCBondStatusRef
SCBondInterfaceCopyStatus (SCBondInterfaceRef bond) __attribute__((visibility("default")));





CFTypeID
SCBondStatusGetTypeID (void) __attribute__((visibility("default")));
# 711 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFArrayRef
SCBondStatusGetMemberInterfaces (SCBondStatusRef bondStatus) __attribute__((visibility("default")));
# 727 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFDictionaryRef
SCBondStatusGetInterfaceStatus (SCBondStatusRef bondStatus,
       SCNetworkInterfaceRef interface) __attribute__((visibility("default")));





       
       







CFArrayRef
SCVLANInterfaceCopyAll (SCPreferencesRef prefs) __attribute__((visibility("default")));
# 754 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFArrayRef
SCVLANInterfaceCopyAvailablePhysicalInterfaces (void) __attribute__((visibility("default")));
# 768 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
SCVLANInterfaceRef
SCVLANInterfaceCreate (SCPreferencesRef prefs,
       SCNetworkInterfaceRef physical,
       CFNumberRef tag) __attribute__((visibility("default")));







Boolean
SCVLANInterfaceRemove (SCVLANInterfaceRef vlan) __attribute__((visibility("default")));







SCNetworkInterfaceRef
SCVLANInterfaceGetPhysicalInterface (SCVLANInterfaceRef vlan) __attribute__((visibility("default")));







CFNumberRef
SCVLANInterfaceGetTag (SCVLANInterfaceRef vlan) __attribute__((visibility("default")));
# 807 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFDictionaryRef
SCVLANInterfaceGetOptions (SCVLANInterfaceRef vlan) __attribute__((visibility("default")));
# 820 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCVLANInterfaceSetPhysicalInterfaceAndTag (SCVLANInterfaceRef vlan,
       SCNetworkInterfaceRef physical,
       CFNumberRef tag) __attribute__((visibility("default")));
# 832 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCVLANInterfaceSetLocalizedDisplayName (SCVLANInterfaceRef vlan,
       CFStringRef newName) __attribute__((visibility("default")));
# 843 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCVLANInterfaceSetOptions (SCVLANInterfaceRef vlan,
       CFDictionaryRef newOptions) __attribute__((visibility("default")));
# 856 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
       
       





CFTypeID
SCNetworkProtocolGetTypeID (void) __attribute__((visibility("default")));
# 874 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFDictionaryRef
SCNetworkProtocolGetConfiguration (SCNetworkProtocolRef protocol) __attribute__((visibility("default")));







Boolean
SCNetworkProtocolGetEnabled (SCNetworkProtocolRef protocol) __attribute__((visibility("default")));







CFStringRef
SCNetworkProtocolGetProtocolType (SCNetworkProtocolRef protocol) __attribute__((visibility("default")));
# 902 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkProtocolSetConfiguration (SCNetworkProtocolRef protocol,
       CFDictionaryRef config) __attribute__((visibility("default")));
# 913 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkProtocolSetEnabled (SCNetworkProtocolRef protocol,
       Boolean enabled) __attribute__((visibility("default")));
# 925 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
       
       





CFTypeID
SCNetworkServiceGetTypeID (void) __attribute__((visibility("default")));
# 946 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkServiceAddProtocolType (SCNetworkServiceRef service,
       CFStringRef protocolType) __attribute__((visibility("default")));
# 957 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFArrayRef
SCNetworkServiceCopyAll (SCPreferencesRef prefs) __attribute__((visibility("default")));
# 967 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFArrayRef
SCNetworkServiceCopyProtocols (SCNetworkServiceRef service) __attribute__((visibility("default")));
# 978 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
SCNetworkServiceRef
SCNetworkServiceCreate (SCPreferencesRef prefs,
       SCNetworkInterfaceRef interface) __attribute__((visibility("default")));
# 992 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
SCNetworkServiceRef
SCNetworkServiceCopy (SCPreferencesRef prefs,
       CFStringRef serviceID) __attribute__((visibility("default")));
# 1005 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkServiceEstablishDefaultConfiguration (SCNetworkServiceRef service) __attribute__((visibility("default")));







Boolean
SCNetworkServiceGetEnabled (SCNetworkServiceRef service) __attribute__((visibility("default")));
# 1024 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
SCNetworkInterfaceRef
SCNetworkServiceGetInterface (SCNetworkServiceRef service) __attribute__((visibility("default")));







CFStringRef
SCNetworkServiceGetName (SCNetworkServiceRef service) __attribute__((visibility("default")));
# 1045 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
SCNetworkProtocolRef
SCNetworkServiceCopyProtocol (SCNetworkServiceRef service,
       CFStringRef protocolType) __attribute__((visibility("default")));







CFStringRef
SCNetworkServiceGetServiceID (SCNetworkServiceRef service) __attribute__((visibility("default")));







Boolean
SCNetworkServiceRemove (SCNetworkServiceRef service) __attribute__((visibility("default")));
# 1075 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkServiceRemoveProtocolType (SCNetworkServiceRef service,
       CFStringRef protocolType) __attribute__((visibility("default")));
# 1086 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkServiceSetEnabled (SCNetworkServiceRef service,
       Boolean enabled) __attribute__((visibility("default")));
# 1102 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkServiceSetName (SCNetworkServiceRef service,
       CFStringRef name) __attribute__((visibility("default")));
# 1115 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
       
       





CFTypeID
SCNetworkSetGetTypeID (void) __attribute__((visibility("default")));
# 1138 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkSetAddService (SCNetworkSetRef set,
       SCNetworkServiceRef service) __attribute__((visibility("default")));
# 1150 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkSetContainsInterface (SCNetworkSetRef set,
       SCNetworkInterfaceRef interface) __attribute__((visibility("default")));
# 1161 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFArrayRef
SCNetworkSetCopyAll (SCPreferencesRef prefs) __attribute__((visibility("default")));







SCNetworkSetRef
SCNetworkSetCopyCurrent (SCPreferencesRef prefs) __attribute__((visibility("default")));
# 1180 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFArrayRef
SCNetworkSetCopyServices (SCNetworkSetRef set) __attribute__((visibility("default")));
# 1190 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
SCNetworkSetRef
SCNetworkSetCreate (SCPreferencesRef prefs) __attribute__((visibility("default")));
# 1203 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
SCNetworkSetRef
SCNetworkSetCopy (SCPreferencesRef prefs,
       CFStringRef setID) __attribute__((visibility("default")));







CFStringRef
SCNetworkSetGetName (SCNetworkSetRef set) __attribute__((visibility("default")));







CFStringRef
SCNetworkSetGetSetID (SCNetworkSetRef set) __attribute__((visibility("default")));
# 1235 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
CFArrayRef
SCNetworkSetGetServiceOrder (SCNetworkSetRef set) __attribute__((visibility("default")));







Boolean
SCNetworkSetRemove (SCNetworkSetRef set) __attribute__((visibility("default")));
# 1255 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkSetRemoveService (SCNetworkSetRef set,
       SCNetworkServiceRef service) __attribute__((visibility("default")));
# 1266 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkSetSetCurrent (SCNetworkSetRef set) __attribute__((visibility("default")));
# 1280 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkSetSetName (SCNetworkSetRef set,
       CFStringRef name) __attribute__((visibility("default")));
# 1291 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConfiguration.h" 3
Boolean
SCNetworkSetSetServiceOrder (SCNetworkSetRef set,
       CFArrayRef newOrder) __attribute__((visibility("default")));



# 130 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SystemConfiguration.h" 2 3


# 1 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetwork.h" 1 3
# 30 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetwork.h" 3
# 1 "/usr/include/sys/socket.h" 1 3 4
# 77 "/usr/include/sys/socket.h" 3 4
# 1 "/usr/include/machine/_param.h" 1 3 4
# 29 "/usr/include/machine/_param.h" 3 4
# 1 "/usr/include/i386/_param.h" 1 3 4
# 30 "/usr/include/machine/_param.h" 2 3 4
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


# 31 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetwork.h" 2 3
# 105 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetwork.h" 3
enum {
 kSCNetworkFlagsTransientConnection = 1<<0,
 kSCNetworkFlagsReachable = 1<<1,
 kSCNetworkFlagsConnectionRequired = 1<<2,
 kSCNetworkFlagsConnectionAutomatic = 1<<3,
 kSCNetworkFlagsInterventionRequired = 1<<4,
 kSCNetworkFlagsIsLocalAddress = 1<<16,
 kSCNetworkFlagsIsDirect = 1<<17,
};
typedef uint32_t SCNetworkConnectionFlags;


# 142 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetwork.h" 3
Boolean
SCNetworkCheckReachabilityByAddress (
     const struct sockaddr *address,
     socklen_t addrlen,
     SCNetworkConnectionFlags *flags
     ) __attribute__((deprecated,visibility("default")));
# 174 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetwork.h" 3
Boolean
SCNetworkCheckReachabilityByName (
     const char *nodename,
     SCNetworkConnectionFlags *flags
     ) __attribute__((deprecated,visibility("default")));
# 192 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetwork.h" 3
Boolean
SCNetworkInterfaceRefreshConfiguration (
     CFStringRef ifName
     ) __attribute__((deprecated,visibility("default")));


# 133 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SystemConfiguration.h" 2 3
# 1 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkReachability.h" 1 3
# 55 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkReachability.h" 3
typedef const struct __SCNetworkReachability * SCNetworkReachabilityRef;
# 75 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkReachability.h" 3
typedef struct {
 CFIndex version;
 void * info;
 const void *(*retain)(const void *info);
 void (*release)(const void *info);
 CFStringRef (*copyDescription)(const void *info);
} SCNetworkReachabilityContext;
# 147 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkReachability.h" 3
enum {
 kSCNetworkReachabilityFlagsTransientConnection = 1<<0,
 kSCNetworkReachabilityFlagsReachable = 1<<1,
 kSCNetworkReachabilityFlagsConnectionRequired = 1<<2,
 kSCNetworkReachabilityFlagsConnectionOnTraffic = 1<<3,
 kSCNetworkReachabilityFlagsInterventionRequired = 1<<4,
 kSCNetworkReachabilityFlagsConnectionOnDemand = 1<<5,
 kSCNetworkReachabilityFlagsIsLocalAddress = 1<<16,
 kSCNetworkReachabilityFlagsIsDirect = 1<<17,




 kSCNetworkReachabilityFlagsConnectionAutomatic = kSCNetworkReachabilityFlagsConnectionOnTraffic
};
typedef uint32_t SCNetworkReachabilityFlags;
# 174 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkReachability.h" 3
typedef void (*SCNetworkReachabilityCallBack) (
      SCNetworkReachabilityRef target,
      SCNetworkReachabilityFlags flags,
      void *info
      );


# 192 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkReachability.h" 3
SCNetworkReachabilityRef
SCNetworkReachabilityCreateWithAddress (
      CFAllocatorRef allocator,
      const struct sockaddr *address
      ) __attribute__((visibility("default")));
# 211 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkReachability.h" 3
SCNetworkReachabilityRef
SCNetworkReachabilityCreateWithAddressPair (
      CFAllocatorRef allocator,
      const struct sockaddr *localAddress,
      const struct sockaddr *remoteAddress
      ) __attribute__((visibility("default")));
# 230 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkReachability.h" 3
SCNetworkReachabilityRef
SCNetworkReachabilityCreateWithName (
      CFAllocatorRef allocator,
      const char *nodename
      ) __attribute__((visibility("default")));






CFTypeID
SCNetworkReachabilityGetTypeID (void) __attribute__((visibility("default")));
# 257 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkReachability.h" 3
Boolean
SCNetworkReachabilityGetFlags (
      SCNetworkReachabilityRef target,
      SCNetworkReachabilityFlags *flags
      ) __attribute__((visibility("default")));
# 276 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkReachability.h" 3
Boolean
SCNetworkReachabilitySetCallback (
      SCNetworkReachabilityRef target,
      SCNetworkReachabilityCallBack callout,
      SCNetworkReachabilityContext *context
      ) __attribute__((visibility("default")));
# 295 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkReachability.h" 3
Boolean
SCNetworkReachabilityScheduleWithRunLoop (
      SCNetworkReachabilityRef target,
      CFRunLoopRef runLoop,
      CFStringRef runLoopMode
      ) __attribute__((visibility("default")));
# 315 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkReachability.h" 3
Boolean
SCNetworkReachabilityUnscheduleFromRunLoop (
      SCNetworkReachabilityRef target,
      CFRunLoopRef runLoop,
      CFStringRef runLoopMode
      ) __attribute__((visibility("default")));
# 332 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkReachability.h" 3
Boolean
SCNetworkReachabilitySetDispatchQueue (
      SCNetworkReachabilityRef target,
      dispatch_queue_t queue
      ) __attribute__((visibility("default")));


# 134 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SystemConfiguration.h" 2 3
# 1 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConnection.h" 1 3
# 56 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConnection.h" 3
typedef const struct __SCNetworkConnection * SCNetworkConnectionRef;
# 77 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConnection.h" 3
typedef struct {
 CFIndex version;
 void * info;
 const void *(*retain)(const void *info);
 void (*release)(const void *info);
 CFStringRef (*copyDescription)(const void *info);
} SCNetworkConnectionContext;
# 105 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConnection.h" 3
enum {
 kSCNetworkConnectionInvalid = -1,
 kSCNetworkConnectionDisconnected = 0,
 kSCNetworkConnectionConnecting = 1,
 kSCNetworkConnectionConnected = 2,
 kSCNetworkConnectionDisconnecting = 3
};
typedef int32_t SCNetworkConnectionStatus;
# 159 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConnection.h" 3
enum {
 kSCNetworkConnectionPPPDisconnected = 0,
 kSCNetworkConnectionPPPInitializing = 1,
 kSCNetworkConnectionPPPConnectingLink = 2,
 kSCNetworkConnectionPPPDialOnTraffic = 3,
 kSCNetworkConnectionPPPNegotiatingLink = 4,
 kSCNetworkConnectionPPPAuthenticating = 5,
 kSCNetworkConnectionPPPWaitingForCallBack = 6,
 kSCNetworkConnectionPPPNegotiatingNetwork = 7,
 kSCNetworkConnectionPPPConnected = 8,
 kSCNetworkConnectionPPPTerminating = 9,
 kSCNetworkConnectionPPPDisconnectingLink = 10,
 kSCNetworkConnectionPPPHoldingLinkOff = 11,
 kSCNetworkConnectionPPPSuspended = 12,
 kSCNetworkConnectionPPPWaitingForRedial = 13
};
typedef int32_t SCNetworkConnectionPPPStatus;
# 186 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConnection.h" 3
typedef void (*SCNetworkConnectionCallBack) (
      SCNetworkConnectionRef connection,
      SCNetworkConnectionStatus status,
      void *info
      );
# 227 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConnection.h" 3







CFTypeID
SCNetworkConnectionGetTypeID (void) __attribute__((visibility("default")));
# 253 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConnection.h" 3
Boolean
SCNetworkConnectionCopyUserPreferences (
      CFDictionaryRef selectionOptions,
      CFStringRef *serviceID,
      CFDictionaryRef *userOptions
      ) __attribute__((visibility("default")));
# 282 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConnection.h" 3
SCNetworkConnectionRef
SCNetworkConnectionCreateWithServiceID (
      CFAllocatorRef allocator,
      CFStringRef serviceID,
      SCNetworkConnectionCallBack callout,
      SCNetworkConnectionContext *context
      ) __attribute__((visibility("default")));
# 297 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConnection.h" 3
CFStringRef
SCNetworkConnectionCopyServiceID (
      SCNetworkConnectionRef connection
      ) __attribute__((visibility("default")));
# 320 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConnection.h" 3
SCNetworkConnectionStatus
SCNetworkConnectionGetStatus (
      SCNetworkConnectionRef connection
      ) __attribute__((visibility("default")));
# 368 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConnection.h" 3
CFDictionaryRef
SCNetworkConnectionCopyExtendedStatus (
      SCNetworkConnectionRef connection
      ) __attribute__((visibility("default")));
# 410 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConnection.h" 3
CFDictionaryRef
SCNetworkConnectionCopyStatistics (
      SCNetworkConnectionRef connection
      ) __attribute__((visibility("default")));
# 460 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConnection.h" 3
Boolean
SCNetworkConnectionStart (
      SCNetworkConnectionRef connection,
      CFDictionaryRef userOptions,
      Boolean linger
      ) __attribute__((visibility("default")));
# 487 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConnection.h" 3
Boolean
SCNetworkConnectionStop (
      SCNetworkConnectionRef connection,
      Boolean forceDisconnect
      ) __attribute__((visibility("default")));
# 504 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConnection.h" 3
CFDictionaryRef
SCNetworkConnectionCopyUserOptions (
      SCNetworkConnectionRef connection
      ) __attribute__((visibility("default")));
# 520 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConnection.h" 3
Boolean
SCNetworkConnectionScheduleWithRunLoop (
      SCNetworkConnectionRef connection,
      CFRunLoopRef runLoop,
      CFStringRef runLoopMode
      ) __attribute__((visibility("default")));
# 538 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConnection.h" 3
Boolean
SCNetworkConnectionUnscheduleFromRunLoop (
      SCNetworkConnectionRef connection,
      CFRunLoopRef runLoop,
      CFStringRef runLoopMode
      ) __attribute__((visibility("default")));
# 556 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SCNetworkConnection.h" 3
Boolean
SCNetworkConnectionSetDispatchQueue (
       SCNetworkConnectionRef connection,
       dispatch_queue_t queue
       ) __attribute__((visibility("default")));


# 135 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SystemConfiguration.h" 2 3






extern const CFStringRef kCFErrorDomainSystemConfiguration __attribute__((visibility("default")));









CFErrorRef SCCopyLastError (void) __attribute__((visibility("default")));







int SCError (void) __attribute__((visibility("default")));
# 168 "/System/Library/Frameworks/SystemConfiguration.framework/Headers/SystemConfiguration.h" 3
const char * SCErrorString (int status) __attribute__((visibility("default")));


# 7 "_scproxy.c" 2

static int32_t
cfnum_to_int32(CFNumberRef num)
{
    int32_t result;

    CFNumberGetValue(num, kCFNumberSInt32Type, &result);
    return result;
}

static PyObject*
cfstring_to_pystring(CFStringRef ref)
{
    const char* s;

    s = CFStringGetCStringPtr(ref, kCFStringEncodingUTF8);
    if (s) {
        return PyUnicode_DecodeUTF8(
                        s, strlen(s), ((void *)0));

    } else {
        CFIndex len = CFStringGetLength(ref);
        Boolean ok;
        PyObject* result;
        char* buf;

        buf = PyMem_Malloc(len*4);
        if (buf == ((void *)0)) {
            PyErr_NoMemory();
            return ((void *)0);
        }

        ok = CFStringGetCString(ref,
                        buf, len * 4,
                        kCFStringEncodingUTF8);
        if (!ok) {
            PyMem_Free(buf);
            return ((void *)0);
        } else {
            result = PyUnicode_DecodeUTF8(
                            buf, strlen(buf), ((void *)0));
            PyMem_Free(buf);
        }
        return result;
    }
}


static PyObject*
get_proxy_settings(PyObject* mod __attribute__((__unused__)))
{
    CFDictionaryRef proxyDict = ((void *)0);
    CFNumberRef aNum = ((void *)0);
    CFArrayRef anArray = ((void *)0);
    PyObject* result = ((void *)0);
    PyObject* v;
    int r;

    proxyDict = SCDynamicStoreCopyProxies(((void *)0));
    if (!proxyDict) {
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        return (&_Py_NoneStruct);
    }

    result = PyDict_New();
    if (result == ((void *)0)) goto error;

    if (&kSCPropNetProxiesExcludeSimpleHostnames != ((void *)0)) {
        aNum = CFDictionaryGetValue(proxyDict,
            kSCPropNetProxiesExcludeSimpleHostnames);
        if (aNum == ((void *)0)) {
            v = PyBool_FromLong(0);
        } else {
            v = PyBool_FromLong(cfnum_to_int32(aNum));
        }
    } else {
        v = PyBool_FromLong(0);
    }

    if (v == ((void *)0)) goto error;

    r = PyDict_SetItemString(result, "exclude_simple", v);
    do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0); v = ((void *)0);
    if (r == -1) goto error;

    anArray = CFDictionaryGetValue(proxyDict,
                    kSCPropNetProxiesExceptionsList);
    if (anArray != ((void *)0)) {
        CFIndex len = CFArrayGetCount(anArray);
        CFIndex i;
        v = PyTuple_New(len);
        if (v == ((void *)0)) goto error;

        r = PyDict_SetItemString(result, "exceptions", v);
        do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
        if (r == -1) goto error;

        for (i = 0; i < len; i++) {
            CFStringRef aString = ((void *)0);

            aString = CFArrayGetValueAtIndex(anArray, i);
            if (aString == ((void *)0)) {
                PyTuple_SetItem(v, i, (&_Py_NoneStruct));
                ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
            } else {
                PyObject* t = cfstring_to_pystring(aString);
                if (!t) {
                    PyTuple_SetItem(v, i, (&_Py_NoneStruct));
                    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
                } else {
                    PyTuple_SetItem(v, i, t);
                }
            }
        }
    }

    CFRelease(proxyDict);
    return result;

error:
    if (proxyDict) CFRelease(proxyDict);
    do { if ((result) == ((void *)0)) ; else do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0); } while (0);
    return ((void *)0);
}

static int
set_proxy(PyObject* proxies, char* proto, CFDictionaryRef proxyDict,
                CFStringRef enabledKey,
                CFStringRef hostKey, CFStringRef portKey)
{
    CFNumberRef aNum;

    aNum = CFDictionaryGetValue(proxyDict, enabledKey);
    if (aNum && cfnum_to_int32(aNum)) {
        CFStringRef hostString;

        hostString = CFDictionaryGetValue(proxyDict, hostKey);
        aNum = CFDictionaryGetValue(proxyDict, portKey);

        if (hostString) {
            int r;
            PyObject* h = cfstring_to_pystring(hostString);
            PyObject* v;
            if (h) {
                if (aNum) {
                    int32_t port = cfnum_to_int32(aNum);
                    v = PyUnicode_FromFormat("http://%U:%ld",
                        h, (long)port);
                } else {
                    v = PyUnicode_FromFormat("http://%U", h);
                }
                do { if ( --((PyObject*)(h))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(h)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(h)))); } while (0);
                if (!v) return -1;
                r = PyDict_SetItemString(proxies, proto,
                    v);
                do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
                return r;
            }
        }

    }
    return 0;
}



static PyObject*
get_proxies(PyObject* mod __attribute__((__unused__)))
{
    PyObject* result = ((void *)0);
    int r;
    CFDictionaryRef proxyDict = ((void *)0);

    proxyDict = SCDynamicStoreCopyProxies(((void *)0));
    if (proxyDict == ((void *)0)) {
        return PyDict_New();
    }

    result = PyDict_New();
    if (result == ((void *)0)) goto error;

    r = set_proxy(result, "http", proxyDict,
        kSCPropNetProxiesHTTPEnable,
        kSCPropNetProxiesHTTPProxy,
        kSCPropNetProxiesHTTPPort);
    if (r == -1) goto error;
    r = set_proxy(result, "https", proxyDict,
        kSCPropNetProxiesHTTPSEnable,
        kSCPropNetProxiesHTTPSProxy,
        kSCPropNetProxiesHTTPSPort);
    if (r == -1) goto error;
    r = set_proxy(result, "ftp", proxyDict,
        kSCPropNetProxiesFTPEnable,
        kSCPropNetProxiesFTPProxy,
        kSCPropNetProxiesFTPPort);
    if (r == -1) goto error;
    r = set_proxy(result, "gopher", proxyDict,
        kSCPropNetProxiesGopherEnable,
        kSCPropNetProxiesGopherProxy,
        kSCPropNetProxiesGopherPort);
    if (r == -1) goto error;

    CFRelease(proxyDict);
    return result;
error:
    if (proxyDict) CFRelease(proxyDict);
    do { if ((result) == ((void *)0)) ; else do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0); } while (0);
    return ((void *)0);
}

static PyMethodDef mod_methods[] = {
    {
        "_get_proxy_settings",
        (PyCFunction)get_proxy_settings,
        0x0004,
        ((void *)0),
    },
    {
        "_get_proxies",
        (PyCFunction)get_proxies,
        0x0004,
        ((void *)0),
    },
    { 0, 0, 0, 0 }
};



static struct PyModuleDef mod_module = {
    { { 1, ((void *)0) }, ((void *)0), 0, ((void *)0), },
    "_scproxy",
    ((void *)0),
    -1,
    mod_methods,
    ((void *)0),
    ((void *)0),
    ((void *)0),
    ((void *)0)
};






PyObject*
PyInit__scproxy(void)
{
    return PyModule_Create2(&mod_module, 1013);
}
