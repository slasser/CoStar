# 1 "formatter_unicode.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "formatter_unicode.c"




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
# 6 "formatter_unicode.c" 2
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

# 7 "formatter_unicode.c" 2




static void
unknown_presentation_type(Py_UCS4 presentation_type,
                          const char* type_name)
{

    if (presentation_type > 32 && presentation_type < 128)
        PyErr_Format(PyExc_ValueError,
                     "Unknown format code '%c' "
                     "for object of type '%.200s'",
                     (char)presentation_type,
                     type_name);
    else
        PyErr_Format(PyExc_ValueError,
                     "Unknown format code '\\x%x' "
                     "for object of type '%.200s'",
                     (unsigned int)presentation_type,
                     type_name);
}

static void
invalid_comma_type(Py_UCS4 presentation_type)
{
    if (presentation_type > 32 && presentation_type < 128)
        PyErr_Format(PyExc_ValueError,
                     "Cannot specify ',' with '%c'.",
                     (char)presentation_type);
    else
        PyErr_Format(PyExc_ValueError,
                     "Cannot specify ',' with '\\x%x'.",
                     (unsigned int)presentation_type);
}
# 50 "formatter_unicode.c"
static int
get_integer(PyObject *str, Py_ssize_t *pos, Py_ssize_t end,
                  Py_ssize_t *result)
{
    Py_ssize_t accumulator, digitval;
    int numdigits;
    accumulator = numdigits = 0;
    for (;;(*pos)++, numdigits++) {
        if (*pos >= end)
            break;
        digitval = _PyUnicode_ToDecimalDigit(((__builtin_expect(!(((((((PyObject*)(str))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 60, "PyUnicode_Check(str)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)str)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 60, "PyUnicode_IS_READY(str)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((str)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 60, "PyUnicode_Check((str))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(str))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 60, "PyUnicode_IS_READY((str))") : (void)0), ((PyASCIIObject *)((str)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((str)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 60, "PyUnicode_Check((str))") : (void)0), (((PyASCIIObject*)((str)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((str)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 60, "PyUnicode_Check((str))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(str))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 60, "PyUnicode_IS_READY((str))") : (void)0), ((PyASCIIObject*)(str))->state.ascii) ? ((void*)((PyASCIIObject*)((str)) + 1)) : ((void*)((PyCompactUnicodeObject*)((str)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((str)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 60, "((PyUnicodeObject*)((str)))->data.any") : (void)0), ((((PyUnicodeObject *)((str)))->data.any))))))[(*pos)] : (((__builtin_expect(!(((((((PyObject*)((str)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 60, "PyUnicode_Check((str))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(str))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 60, "PyUnicode_IS_READY((str))") : (void)0), ((PyASCIIObject *)((str)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((str)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 60, "PyUnicode_Check((str))") : (void)0), (((PyASCIIObject*)((str)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((str)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 60, "PyUnicode_Check((str))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(str))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 60, "PyUnicode_IS_READY((str))") : (void)0), ((PyASCIIObject*)(str))->state.ascii) ? ((void*)((PyASCIIObject*)((str)) + 1)) : ((void*)((PyCompactUnicodeObject*)((str)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((str)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 60, "((PyUnicodeObject*)((str)))->data.any") : (void)0), ((((PyUnicodeObject *)((str)))->data.any))))))[(*pos)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((str)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 60, "PyUnicode_Check((str))") : (void)0), (((PyASCIIObject*)((str)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((str)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 60, "PyUnicode_Check((str))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(str))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 60, "PyUnicode_IS_READY((str))") : (void)0), ((PyASCIIObject*)(str))->state.ascii) ? ((void*)((PyASCIIObject*)((str)) + 1)) : ((void*)((PyCompactUnicodeObject*)((str)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((str)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 60, "((PyUnicodeObject*)((str)))->data.any") : (void)0), ((((PyUnicodeObject *)((str)))->data.any))))))[(*pos)] ) )));
        if (digitval < 0)
            break;






        if (accumulator > (((Py_ssize_t)(((size_t)-1)>>1)) - digitval) / 10) {
            PyErr_Format(PyExc_ValueError,
                         "Too many decimal digits in format string");
            return -1;
        }
        accumulator = accumulator * 10 + digitval;
    }
    *result = accumulator;
    return numdigits;
}






static inline int
is_alignment_token(Py_UCS4 c)
{
    switch (c) {
    case '<': case '>': case '=': case '^':
        return 1;
    default:
        return 0;
    }
}


static inline int
is_sign_element(Py_UCS4 c)
{
    switch (c) {
    case ' ': case '+': case '-':
        return 1;
    default:
        return 0;
    }
}


typedef struct {
    Py_UCS4 fill_char;
    Py_UCS4 align;
    int alternate;
    Py_UCS4 sign;
    Py_ssize_t width;
    int thousands_separators;
    Py_ssize_t precision;
    Py_UCS4 type;
} InternalFormatSpec;
# 145 "formatter_unicode.c"
static int
parse_internal_render_format_spec(PyObject *format_spec,
                                  Py_ssize_t start, Py_ssize_t end,
                                  InternalFormatSpec *format,
                                  char default_type,
                                  char default_align)
{
    Py_ssize_t pos = start;




    Py_ssize_t consumed;
    int align_specified = 0;

    format->fill_char = '\0';
    format->align = default_align;
    format->alternate = 0;
    format->sign = '\0';
    format->width = -1;
    format->thousands_separators = 0;
    format->precision = -1;
    format->type = default_type;



    if (end-pos >= 2 && is_alignment_token(((__builtin_expect(!(((((((PyObject*)(format_spec))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 171, "PyUnicode_Check(format_spec)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)format_spec)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 171, "PyUnicode_IS_READY(format_spec)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 171, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 171, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 171, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 171, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 171, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 171, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos+1)] : (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 171, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 171, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 171, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 171, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 171, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 171, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos+1)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 171, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 171, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 171, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 171, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos+1)] ) )))) {
        format->align = ((__builtin_expect(!(((((((PyObject*)(format_spec))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 172, "PyUnicode_Check(format_spec)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)format_spec)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 172, "PyUnicode_IS_READY(format_spec)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 172, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 172, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 172, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 172, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 172, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 172, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos+1)] : (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 172, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 172, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 172, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 172, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 172, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 172, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos+1)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 172, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 172, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 172, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 172, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos+1)] ) ));
        format->fill_char = ((__builtin_expect(!(((((((PyObject*)(format_spec))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 173, "PyUnicode_Check(format_spec)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)format_spec)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 173, "PyUnicode_IS_READY(format_spec)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 173, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 173, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 173, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 173, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 173, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 173, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 173, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 173, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 173, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 173, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 173, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 173, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 173, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 173, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 173, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 173, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] ) ));
        align_specified = 1;
        pos += 2;
    }
    else if (end-pos >= 1 && is_alignment_token(((__builtin_expect(!(((((((PyObject*)(format_spec))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 177, "PyUnicode_Check(format_spec)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)format_spec)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 177, "PyUnicode_IS_READY(format_spec)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 177, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 177, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 177, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 177, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 177, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 177, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 177, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 177, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 177, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 177, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 177, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 177, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 177, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 177, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 177, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 177, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] ) )))) {
        format->align = ((__builtin_expect(!(((((((PyObject*)(format_spec))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 178, "PyUnicode_Check(format_spec)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)format_spec)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 178, "PyUnicode_IS_READY(format_spec)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 178, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 178, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 178, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 178, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 178, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 178, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 178, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 178, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 178, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 178, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 178, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 178, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 178, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 178, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 178, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 178, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] ) ));
        align_specified = 1;
        ++pos;
    }


    if (end-pos >= 1 && is_sign_element(((__builtin_expect(!(((((((PyObject*)(format_spec))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 184, "PyUnicode_Check(format_spec)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)format_spec)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 184, "PyUnicode_IS_READY(format_spec)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 184, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 184, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 184, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 184, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 184, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 184, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 184, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 184, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 184, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 184, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 184, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 184, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 184, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 184, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 184, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 184, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] ) )))) {
        format->sign = ((__builtin_expect(!(((((((PyObject*)(format_spec))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 185, "PyUnicode_Check(format_spec)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)format_spec)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 185, "PyUnicode_IS_READY(format_spec)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 185, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 185, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 185, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 185, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 185, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 185, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 185, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 185, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 185, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 185, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 185, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 185, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 185, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 185, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 185, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 185, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] ) ));
        ++pos;
    }



    if (end-pos >= 1 && ((__builtin_expect(!(((((((PyObject*)(format_spec))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 191, "PyUnicode_Check(format_spec)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)format_spec)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 191, "PyUnicode_IS_READY(format_spec)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 191, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 191, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 191, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 191, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 191, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 191, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 191, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 191, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 191, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 191, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 191, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 191, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 191, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 191, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 191, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 191, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] ) )) == '#') {
        format->alternate = 1;
        ++pos;
    }


    if (format->fill_char == '\0' && end-pos >= 1 && ((__builtin_expect(!(((((((PyObject*)(format_spec))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 197, "PyUnicode_Check(format_spec)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)format_spec)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 197, "PyUnicode_IS_READY(format_spec)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 197, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 197, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 197, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 197, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 197, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 197, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 197, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 197, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 197, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 197, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 197, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 197, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 197, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 197, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 197, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 197, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] ) )) == '0') {
        format->fill_char = '0';
        if (!align_specified) {
            format->align = '=';
        }
        ++pos;
    }

    consumed = get_integer(format_spec, &pos, end, &format->width);
    if (consumed == -1)

        return 0;





    if (consumed == 0)
        format->width = -1;


    if (end-pos && ((__builtin_expect(!(((((((PyObject*)(format_spec))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 218, "PyUnicode_Check(format_spec)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)format_spec)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 218, "PyUnicode_IS_READY(format_spec)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 218, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 218, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 218, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 218, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 218, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 218, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 218, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 218, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 218, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 218, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 218, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 218, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 218, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 218, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 218, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 218, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] ) )) == ',') {
        format->thousands_separators = 1;
        ++pos;
    }


    if (end-pos && ((__builtin_expect(!(((((((PyObject*)(format_spec))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 224, "PyUnicode_Check(format_spec)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)format_spec)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 224, "PyUnicode_IS_READY(format_spec)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 224, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 224, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 224, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 224, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 224, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 224, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 224, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 224, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 224, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 224, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 224, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 224, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 224, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 224, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 224, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 224, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] ) )) == '.') {
        ++pos;

        consumed = get_integer(format_spec, &pos, end, &format->precision);
        if (consumed == -1)

            return 0;


        if (consumed == 0) {
            PyErr_Format(PyExc_ValueError,
                         "Format specifier missing precision");
            return 0;
        }

    }



    if (end-pos > 1) {

        PyErr_Format(PyExc_ValueError, "Invalid format specifier");
        return 0;
    }

    if (end-pos == 1) {
        format->type = ((__builtin_expect(!(((((((PyObject*)(format_spec))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 250, "PyUnicode_Check(format_spec)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)format_spec)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 250, "PyUnicode_IS_READY(format_spec)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 250, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 250, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 250, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 250, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 250, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 250, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 250, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 250, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject *)((format_spec)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 250, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 250, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 250, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 250, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 250, "PyUnicode_Check((format_spec))") : (void)0), (((PyASCIIObject*)((format_spec)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((format_spec)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 250, "PyUnicode_Check((format_spec))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(format_spec))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 250, "PyUnicode_IS_READY((format_spec))") : (void)0), ((PyASCIIObject*)(format_spec))->state.ascii) ? ((void*)((PyASCIIObject*)((format_spec)) + 1)) : ((void*)((PyCompactUnicodeObject*)((format_spec)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((format_spec)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 250, "((PyUnicodeObject*)((format_spec)))->data.any") : (void)0), ((((PyUnicodeObject *)((format_spec)))->data.any))))))[(pos)] ) ));
        ++pos;
    }





    if (format->thousands_separators) {
        switch (format->type) {
        case 'd':
        case 'e':
        case 'f':
        case 'g':
        case 'E':
        case 'G':
        case '%':
        case 'F':
        case '\0':

            break;
        default:
            invalid_comma_type(format->type);
            return 0;
        }
    }

    (__builtin_expect(!(format->align <= 127), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 277, "format->align <= 127") : (void)0);
    (__builtin_expect(!(format->sign <= 127), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 278, "format->sign <= 127") : (void)0);
    return 1;
}


static void
calc_padding(Py_ssize_t nchars, Py_ssize_t width, Py_UCS4 align,
             Py_ssize_t *n_lpadding, Py_ssize_t *n_rpadding,
             Py_ssize_t *n_total)
{
    if (width >= 0) {
        if (nchars > width)
            *n_total = nchars;
        else
            *n_total = width;
    }
    else {

        *n_total = nchars;
    }



    if (align == '>')
        *n_lpadding = *n_total - nchars;
    else if (align == '^')
        *n_lpadding = (*n_total - nchars) / 2;
    else if (align == '<' || align == '=')
        *n_lpadding = 0;
    else {

        *n_lpadding = 0;
        (__builtin_expect(!(0), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 310, "0") : (void)0);
    }

    *n_rpadding = *n_total - nchars - *n_lpadding;
}



static Py_ssize_t
fill_padding(_PyUnicodeWriter *writer,
             Py_ssize_t nchars,
             Py_UCS4 fill_char, Py_ssize_t n_lpadding,
             Py_ssize_t n_rpadding)
{
    Py_ssize_t pos;


    if (n_lpadding) {
        pos = writer->pos;
        _PyUnicode_FastFill(writer->buffer, pos, n_lpadding, fill_char);
    }


    if (n_rpadding) {
        pos = writer->pos + nchars + n_lpadding;
        _PyUnicode_FastFill(writer->buffer, pos, n_rpadding, fill_char);
    }


    writer->pos += n_lpadding;
    return 0;
}
# 355 "formatter_unicode.c"
typedef struct {
    PyObject *decimal_point;
    PyObject *thousands_sep;
    const char *grouping;
} LocaleInfo;





typedef struct {
    Py_ssize_t n_lpadding;
    Py_ssize_t n_prefix;
    Py_ssize_t n_spadding;
    Py_ssize_t n_rpadding;
    char sign;
    Py_ssize_t n_sign;
    Py_ssize_t n_grouped_digits;

    Py_ssize_t n_decimal;
    Py_ssize_t n_remainder;





    Py_ssize_t n_digits;

    Py_ssize_t n_min_width;

} NumberFieldWidths;
# 398 "formatter_unicode.c"
static void
parse_number(PyObject *s, Py_ssize_t pos, Py_ssize_t end,
             Py_ssize_t *n_remainder, int *has_decimal)
{
    Py_ssize_t remainder;

    while (pos<end && (_Py_ctype_table[((unsigned char)((((__builtin_expect(!(((((((PyObject*)(s))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 404, "PyUnicode_Check(s)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)s)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 404, "PyUnicode_IS_READY(s)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((s)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 404, "PyUnicode_Check((s))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(s))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 404, "PyUnicode_IS_READY((s))") : (void)0), ((PyASCIIObject *)((s)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((s)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 404, "PyUnicode_Check((s))") : (void)0), (((PyASCIIObject*)((s)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((s)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 404, "PyUnicode_Check((s))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(s))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 404, "PyUnicode_IS_READY((s))") : (void)0), ((PyASCIIObject*)(s))->state.ascii) ? ((void*)((PyASCIIObject*)((s)) + 1)) : ((void*)((PyCompactUnicodeObject*)((s)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((s)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 404, "((PyUnicodeObject*)((s)))->data.any") : (void)0), ((((PyUnicodeObject *)((s)))->data.any))))))[(pos)] : (((__builtin_expect(!(((((((PyObject*)((s)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 404, "PyUnicode_Check((s))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(s))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 404, "PyUnicode_IS_READY((s))") : (void)0), ((PyASCIIObject *)((s)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((s)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 404, "PyUnicode_Check((s))") : (void)0), (((PyASCIIObject*)((s)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((s)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 404, "PyUnicode_Check((s))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(s))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 404, "PyUnicode_IS_READY((s))") : (void)0), ((PyASCIIObject*)(s))->state.ascii) ? ((void*)((PyASCIIObject*)((s)) + 1)) : ((void*)((PyCompactUnicodeObject*)((s)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((s)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 404, "((PyUnicodeObject*)((s)))->data.any") : (void)0), ((((PyUnicodeObject *)((s)))->data.any))))))[(pos)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((s)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 404, "PyUnicode_Check((s))") : (void)0), (((PyASCIIObject*)((s)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((s)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 404, "PyUnicode_Check((s))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(s))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 404, "PyUnicode_IS_READY((s))") : (void)0), ((PyASCIIObject*)(s))->state.ascii) ? ((void*)((PyASCIIObject*)((s)) + 1)) : ((void*)((PyCompactUnicodeObject*)((s)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((s)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 404, "((PyUnicodeObject*)((s)))->data.any") : (void)0), ((((PyUnicodeObject *)((s)))->data.any))))))[(pos)] ) ))) & 0xff))] & 0x04))
        ++pos;
    remainder = pos;


    *has_decimal = pos<end && ((__builtin_expect(!(((((((PyObject*)(s))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 409, "PyUnicode_Check(s)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)s)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 409, "PyUnicode_IS_READY(s)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((s)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 409, "PyUnicode_Check((s))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(s))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 409, "PyUnicode_IS_READY((s))") : (void)0), ((PyASCIIObject *)((s)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((s)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 409, "PyUnicode_Check((s))") : (void)0), (((PyASCIIObject*)((s)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((s)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 409, "PyUnicode_Check((s))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(s))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 409, "PyUnicode_IS_READY((s))") : (void)0), ((PyASCIIObject*)(s))->state.ascii) ? ((void*)((PyASCIIObject*)((s)) + 1)) : ((void*)((PyCompactUnicodeObject*)((s)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((s)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 409, "((PyUnicodeObject*)((s)))->data.any") : (void)0), ((((PyUnicodeObject *)((s)))->data.any))))))[(remainder)] : (((__builtin_expect(!(((((((PyObject*)((s)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 409, "PyUnicode_Check((s))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(s))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 409, "PyUnicode_IS_READY((s))") : (void)0), ((PyASCIIObject *)((s)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((s)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 409, "PyUnicode_Check((s))") : (void)0), (((PyASCIIObject*)((s)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((s)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 409, "PyUnicode_Check((s))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(s))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 409, "PyUnicode_IS_READY((s))") : (void)0), ((PyASCIIObject*)(s))->state.ascii) ? ((void*)((PyASCIIObject*)((s)) + 1)) : ((void*)((PyCompactUnicodeObject*)((s)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((s)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 409, "((PyUnicodeObject*)((s)))->data.any") : (void)0), ((((PyUnicodeObject *)((s)))->data.any))))))[(remainder)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((s)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 409, "PyUnicode_Check((s))") : (void)0), (((PyASCIIObject*)((s)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((s)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 409, "PyUnicode_Check((s))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(s))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 409, "PyUnicode_IS_READY((s))") : (void)0), ((PyASCIIObject*)(s))->state.ascii) ? ((void*)((PyASCIIObject*)((s)) + 1)) : ((void*)((PyCompactUnicodeObject*)((s)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((s)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 409, "((PyUnicodeObject*)((s)))->data.any") : (void)0), ((((PyUnicodeObject *)((s)))->data.any))))))[(remainder)] ) )) == '.';


    if (*has_decimal)
        remainder++;

    *n_remainder = end - remainder;
}





static Py_ssize_t
calc_number_widths(NumberFieldWidths *spec, Py_ssize_t n_prefix,
                   Py_UCS4 sign_char, PyObject *number, Py_ssize_t n_start,
                   Py_ssize_t n_end, Py_ssize_t n_remainder,
                   int has_decimal, const LocaleInfo *locale,
                   const InternalFormatSpec *format, Py_UCS4 *maxchar)
{
    Py_ssize_t n_non_digit_non_padding;
    Py_ssize_t n_padding;

    spec->n_digits = n_end - n_start - n_remainder - (has_decimal?1:0);
    spec->n_lpadding = 0;
    spec->n_prefix = n_prefix;
    spec->n_decimal = has_decimal ? ((__builtin_expect(!(((((((PyObject*)(locale->decimal_point))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 435, "PyUnicode_Check(locale->decimal_point)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)locale->decimal_point)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 435, "PyUnicode_IS_READY(locale->decimal_point)") : (void)0), ((PyASCIIObject *)(locale->decimal_point))->length) : 0;
    spec->n_remainder = n_remainder;
    spec->n_spadding = 0;
    spec->n_rpadding = 0;
    spec->sign = '\0';
    spec->n_sign = 0;
# 462 "formatter_unicode.c"
    switch (format->sign) {
    case '+':

        spec->n_sign = 1;
        spec->sign = (sign_char == '-' ? '-' : '+');
        break;
    case ' ':
        spec->n_sign = 1;
        spec->sign = (sign_char == '-' ? '-' : ' ');
        break;
    default:

        if (sign_char == '-') {
            spec->n_sign = 1;
            spec->sign = '-';
        }
    }


    n_non_digit_non_padding = spec->n_sign + spec->n_prefix + spec->n_decimal +
        spec->n_remainder;



    if (format->fill_char == '0' && format->align == '=')
        spec->n_min_width = format->width - n_non_digit_non_padding;
    else
        spec->n_min_width = 0;

    if (spec->n_digits == 0)



        spec->n_grouped_digits = 0;
    else {
        Py_UCS4 grouping_maxchar;
        spec->n_grouped_digits = _PyUnicode_InsertThousandsGrouping(
            ((void *)0), 0,
            0, ((void *)0),
            spec->n_digits, spec->n_min_width,
            locale->grouping, locale->thousands_sep, &grouping_maxchar);
        *maxchar = (((*maxchar) > (grouping_maxchar)) ? (*maxchar) : (grouping_maxchar));
    }





    n_padding = format->width -
                        (n_non_digit_non_padding + spec->n_grouped_digits);
    if (n_padding > 0) {

        switch (format->align) {
        case '<':
            spec->n_rpadding = n_padding;
            break;
        case '^':
            spec->n_lpadding = n_padding / 2;
            spec->n_rpadding = n_padding - spec->n_lpadding;
            break;
        case '=':
            spec->n_spadding = n_padding;
            break;
        case '>':
            spec->n_lpadding = n_padding;
            break;
        default:

            spec->n_lpadding = n_padding;
            (__builtin_expect(!(0), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 531, "0") : (void)0);
            break;
        }
    }

    if (spec->n_lpadding || spec->n_spadding || spec->n_rpadding)
        *maxchar = (((*maxchar) > (format->fill_char)) ? (*maxchar) : (format->fill_char));

    if (spec->n_decimal)
        *maxchar = (((*maxchar) > (((__builtin_expect(!((((PyASCIIObject*)locale->decimal_point)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 540, "PyUnicode_IS_READY(locale->decimal_point)") : (void)0), (((__builtin_expect(!(((((((PyObject*)(locale->decimal_point))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 540, "PyUnicode_Check(locale->decimal_point)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)locale->decimal_point)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 540, "PyUnicode_IS_READY(locale->decimal_point)") : (void)0), ((PyASCIIObject*)locale->decimal_point)->state.ascii) ? (0x7f) : (((__builtin_expect(!(((((((PyObject*)(locale->decimal_point))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 540, "PyUnicode_Check(locale->decimal_point)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)locale->decimal_point)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 540, "PyUnicode_IS_READY(locale->decimal_point)") : (void)0), ((PyASCIIObject *)(locale->decimal_point))->state.kind) == PyUnicode_1BYTE_KIND ? (0xffU) : (((__builtin_expect(!(((((((PyObject*)(locale->decimal_point))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 540, "PyUnicode_Check(locale->decimal_point)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)locale->decimal_point)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 540, "PyUnicode_IS_READY(locale->decimal_point)") : (void)0), ((PyASCIIObject *)(locale->decimal_point))->state.kind) == PyUnicode_2BYTE_KIND ? (0xffffU) : (0x10ffffU))))))) ? (*maxchar) : (((__builtin_expect(!((((PyASCIIObject*)locale->decimal_point)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 540, "PyUnicode_IS_READY(locale->decimal_point)") : (void)0), (((__builtin_expect(!(((((((PyObject*)(locale->decimal_point))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 540, "PyUnicode_Check(locale->decimal_point)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)locale->decimal_point)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 540, "PyUnicode_IS_READY(locale->decimal_point)") : (void)0), ((PyASCIIObject*)locale->decimal_point)->state.ascii) ? (0x7f) : (((__builtin_expect(!(((((((PyObject*)(locale->decimal_point))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 540, "PyUnicode_Check(locale->decimal_point)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)locale->decimal_point)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 540, "PyUnicode_IS_READY(locale->decimal_point)") : (void)0), ((PyASCIIObject *)(locale->decimal_point))->state.kind) == PyUnicode_1BYTE_KIND ? (0xffU) : (((__builtin_expect(!(((((((PyObject*)(locale->decimal_point))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 540, "PyUnicode_Check(locale->decimal_point)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)locale->decimal_point)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 540, "PyUnicode_IS_READY(locale->decimal_point)") : (void)0), ((PyASCIIObject *)(locale->decimal_point))->state.kind) == PyUnicode_2BYTE_KIND ? (0xffffU) : (0x10ffffU)))))));

    return spec->n_lpadding + spec->n_sign + spec->n_prefix +
        spec->n_spadding + spec->n_grouped_digits + spec->n_decimal +
        spec->n_remainder + spec->n_rpadding;
}




static int
fill_number(_PyUnicodeWriter *writer, const NumberFieldWidths *spec,
            PyObject *digits, Py_ssize_t d_start, Py_ssize_t d_end,
            PyObject *prefix, Py_ssize_t p_start,
            Py_UCS4 fill_char,
            LocaleInfo *locale, int toupper)
{

    Py_ssize_t d_pos = d_start;
    const enum PyUnicode_Kind kind = writer->kind;
    const void *data = writer->data;
    Py_ssize_t r;

    if (spec->n_lpadding) {
        _PyUnicode_FastFill(writer->buffer,
                            writer->pos, spec->n_lpadding, fill_char);
        writer->pos += spec->n_lpadding;
    }
    if (spec->n_sign == 1) {
        do { switch ((kind)) { case PyUnicode_1BYTE_KIND: { ((Py_UCS1 *)(data))[(writer->pos)] = (Py_UCS1)(spec->sign); break; } case PyUnicode_2BYTE_KIND: { ((Py_UCS2 *)(data))[(writer->pos)] = (Py_UCS2)(spec->sign); break; } default: { (__builtin_expect(!((kind) == PyUnicode_4BYTE_KIND), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 569, "(kind) == PyUnicode_4BYTE_KIND") : (void)0); ((Py_UCS4 *)(data))[(writer->pos)] = (Py_UCS4)(spec->sign); } } } while (0);
        writer->pos++;
    }
    if (spec->n_prefix) {
        _PyUnicode_FastCopyCharacters(writer->buffer, writer->pos,
                                      prefix, p_start,
                                      spec->n_prefix);
        if (toupper) {
            Py_ssize_t t;
            for (t = 0; t < spec->n_prefix; t++) {
                Py_UCS4 c = ((Py_UCS4) ((kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(data))[(writer->pos + t)] : ((kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(data))[(writer->pos + t)] : ((const Py_UCS4 *)(data))[(writer->pos + t)] ) ));
                c = (_Py_ctype_toupper[((unsigned char)((c) & 0xff))]);
                (__builtin_expect(!(c <= 127), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 581, "c <= 127") : (void)0);
                do { switch ((kind)) { case PyUnicode_1BYTE_KIND: { ((Py_UCS1 *)(data))[(writer->pos + t)] = (Py_UCS1)(c); break; } case PyUnicode_2BYTE_KIND: { ((Py_UCS2 *)(data))[(writer->pos + t)] = (Py_UCS2)(c); break; } default: { (__builtin_expect(!((kind) == PyUnicode_4BYTE_KIND), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 582, "(kind) == PyUnicode_4BYTE_KIND") : (void)0); ((Py_UCS4 *)(data))[(writer->pos + t)] = (Py_UCS4)(c); } } } while (0);
            }
        }
        writer->pos += spec->n_prefix;
    }
    if (spec->n_spadding) {
        _PyUnicode_FastFill(writer->buffer,
                            writer->pos, spec->n_spadding, fill_char);
        writer->pos += spec->n_spadding;
    }


    if (spec->n_digits != 0) {

        char *pdigits;
        if (((__builtin_expect(!(((((((PyObject*)(digits))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 597, "PyUnicode_Check(digits)") : (void)0), ((((PyASCIIObject*)digits)->state.ready) ? 0 : _PyUnicode_Ready((PyObject *)(digits)))))
            return -1;
        pdigits = ((__builtin_expect(!(((((((PyObject*)(digits))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 599, "PyUnicode_Check(digits)") : (void)0), (((PyASCIIObject*)(digits))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)(digits))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 599, "PyUnicode_Check(digits)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)digits)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 599, "PyUnicode_IS_READY(digits)") : (void)0), ((PyASCIIObject*)digits)->state.ascii) ? ((void*)((PyASCIIObject*)(digits) + 1)) : ((void*)((PyCompactUnicodeObject*)(digits) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)(digits))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 599, "((PyUnicodeObject*)(digits))->data.any") : (void)0), ((((PyUnicodeObject *)(digits))->data.any))));
        if (((__builtin_expect(!(((((((PyObject*)(digits))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 600, "PyUnicode_Check(digits)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)digits)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 600, "PyUnicode_IS_READY(digits)") : (void)0), ((PyASCIIObject *)(digits))->state.kind) < kind) {
            pdigits = _PyUnicode_AsKind(digits, kind);
            if (pdigits == ((void *)0))
                return -1;
        }
        r = _PyUnicode_InsertThousandsGrouping(
                writer->buffer, writer->pos,
                spec->n_grouped_digits,
                pdigits + kind * d_pos,
                spec->n_digits, spec->n_min_width,
                locale->grouping, locale->thousands_sep, ((void *)0));
        if (r == -1)
            return -1;
        (__builtin_expect(!(r == spec->n_grouped_digits), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 613, "r == spec->n_grouped_digits") : (void)0);
        if (((__builtin_expect(!(((((((PyObject*)(digits))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 614, "PyUnicode_Check(digits)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)digits)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 614, "PyUnicode_IS_READY(digits)") : (void)0), ((PyASCIIObject *)(digits))->state.kind) < kind)
            PyMem_Free(pdigits);
        d_pos += spec->n_digits;
    }
    if (toupper) {
        Py_ssize_t t;
        for (t = 0; t < spec->n_grouped_digits; t++) {
            Py_UCS4 c = ((Py_UCS4) ((kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(data))[(writer->pos + t)] : ((kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(data))[(writer->pos + t)] : ((const Py_UCS4 *)(data))[(writer->pos + t)] ) ));
            c = (_Py_ctype_toupper[((unsigned char)((c) & 0xff))]);
            if (c > 127) {
                PyErr_SetString(PyExc_SystemError, "non-ascii grouped digit");
                return -1;
            }
            do { switch ((kind)) { case PyUnicode_1BYTE_KIND: { ((Py_UCS1 *)(data))[(writer->pos + t)] = (Py_UCS1)(c); break; } case PyUnicode_2BYTE_KIND: { ((Py_UCS2 *)(data))[(writer->pos + t)] = (Py_UCS2)(c); break; } default: { (__builtin_expect(!((kind) == PyUnicode_4BYTE_KIND), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 627, "(kind) == PyUnicode_4BYTE_KIND") : (void)0); ((Py_UCS4 *)(data))[(writer->pos + t)] = (Py_UCS4)(c); } } } while (0);
        }
    }
    writer->pos += spec->n_grouped_digits;

    if (spec->n_decimal) {
        _PyUnicode_FastCopyCharacters(
            writer->buffer, writer->pos,
            locale->decimal_point, 0, spec->n_decimal);
        writer->pos += spec->n_decimal;
        d_pos += 1;
    }

    if (spec->n_remainder) {
        _PyUnicode_FastCopyCharacters(
            writer->buffer, writer->pos,
            digits, d_pos, spec->n_remainder);
        writer->pos += spec->n_remainder;

    }

    if (spec->n_rpadding) {
        _PyUnicode_FastFill(writer->buffer,
                            writer->pos, spec->n_rpadding,
                            fill_char);
        writer->pos += spec->n_rpadding;
    }
    return 0;
}

static char no_grouping[1] = {127};





static int
get_locale_info(int type, LocaleInfo *locale_info)
{
    switch (type) {
    case 0: {
        struct lconv *locale_data = localeconv();
        locale_info->decimal_point = PyUnicode_DecodeLocale(
                                         locale_data->decimal_point,
                                         ((void *)0));
        if (locale_info->decimal_point == ((void *)0))
            return -1;
        locale_info->thousands_sep = PyUnicode_DecodeLocale(
                                         locale_data->thousands_sep,
                                         ((void *)0));
        if (locale_info->thousands_sep == ((void *)0)) {
            do { if ( --((PyObject*)(locale_info->decimal_point))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(locale_info->decimal_point)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(locale_info->decimal_point)))); } while (0);
            return -1;
        }
        locale_info->grouping = locale_data->grouping;
        break;
    }
    case 1:
        locale_info->decimal_point = PyUnicode_FromOrdinal('.');
        locale_info->thousands_sep = PyUnicode_FromOrdinal(',');
        if (!locale_info->decimal_point || !locale_info->thousands_sep) {
            do { if ((locale_info->decimal_point) == ((void *)0)) ; else do { if ( --((PyObject*)(locale_info->decimal_point))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(locale_info->decimal_point)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(locale_info->decimal_point)))); } while (0); } while (0);
            do { if ((locale_info->thousands_sep) == ((void *)0)) ; else do { if ( --((PyObject*)(locale_info->thousands_sep))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(locale_info->thousands_sep)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(locale_info->thousands_sep)))); } while (0); } while (0);
            return -1;
        }
        locale_info->grouping = "\3";


        break;
    case 2:
        locale_info->decimal_point = PyUnicode_FromOrdinal('.');
        locale_info->thousands_sep = PyUnicode_New(0, 0);
        if (!locale_info->decimal_point || !locale_info->thousands_sep) {
            do { if ((locale_info->decimal_point) == ((void *)0)) ; else do { if ( --((PyObject*)(locale_info->decimal_point))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(locale_info->decimal_point)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(locale_info->decimal_point)))); } while (0); } while (0);
            do { if ((locale_info->thousands_sep) == ((void *)0)) ; else do { if ( --((PyObject*)(locale_info->thousands_sep))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(locale_info->thousands_sep)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(locale_info->thousands_sep)))); } while (0); } while (0);
            return -1;
        }
        locale_info->grouping = no_grouping;
        break;
    default:
        (__builtin_expect(!(0), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 707, "0") : (void)0);
    }
    return 0;
}

static void
free_locale_info(LocaleInfo *locale_info)
{
    do { if ((locale_info->decimal_point) == ((void *)0)) ; else do { if ( --((PyObject*)(locale_info->decimal_point))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(locale_info->decimal_point)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(locale_info->decimal_point)))); } while (0); } while (0);
    do { if ((locale_info->thousands_sep) == ((void *)0)) ; else do { if ( --((PyObject*)(locale_info->thousands_sep))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(locale_info->thousands_sep)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(locale_info->thousands_sep)))); } while (0); } while (0);
}





static int
format_string_internal(PyObject *value, const InternalFormatSpec *format,
                       _PyUnicodeWriter *writer)
{
    Py_ssize_t lpad;
    Py_ssize_t rpad;
    Py_ssize_t total;
    Py_ssize_t len;
    int result = -1;
    Py_UCS4 maxchar;

    (__builtin_expect(!((((PyASCIIObject*)value)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 734, "PyUnicode_IS_READY(value)") : (void)0);
    len = ((__builtin_expect(!(((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 735, "PyUnicode_Check(value)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)value)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 735, "PyUnicode_IS_READY(value)") : (void)0), ((PyASCIIObject *)(value))->length);


    if (format->sign != '\0') {
        PyErr_SetString(PyExc_ValueError,
                        "Sign not allowed in string format specifier");
        goto done;
    }


    if (format->alternate) {
        PyErr_SetString(PyExc_ValueError,
                        "Alternate form (#) not allowed in string format "
                        "specifier");
        goto done;
    }


    if (format->align == '=') {
        PyErr_SetString(PyExc_ValueError,
                        "'=' alignment not allowed "
                        "in string format specifier");
        goto done;
    }

    if (format->width == -1 && format->precision == -1) {

        return _PyUnicodeWriter_WriteStr(writer, value);
    }



    if (format->precision >= 0 && len >= format->precision) {
        len = format->precision;
    }

    calc_padding(len, format->width, format->align, &lpad, &rpad, &total);

    maxchar = _PyUnicode_FindMaxChar(value, 0, len);
    if (lpad != 0 || rpad != 0)
        maxchar = (((maxchar) > (format->fill_char)) ? (maxchar) : (format->fill_char));


    if ((((maxchar) <= (writer)->maxchar && (total) <= (writer)->size - (writer)->pos) ? 0 : (((total) == 0) ? 0 : _PyUnicodeWriter_PrepareInternal((writer), (total), (maxchar)))) == -1)
        goto done;


    result = fill_padding(writer, len,
                          format->fill_char=='\0'?' ':format->fill_char,
                          lpad, rpad);
    if (result == -1)
        goto done;


    if (len) {
        _PyUnicode_FastCopyCharacters(writer->buffer, writer->pos,
                                      value, 0, len);
    }
    writer->pos += (len + rpad);
    result = 0;

done:
    return result;
}






static int
format_long_internal(PyObject *value, const InternalFormatSpec *format,
                     _PyUnicodeWriter *writer)
{
    int result = -1;
    Py_UCS4 maxchar = 127;
    PyObject *tmp = ((void *)0);
    Py_ssize_t inumeric_chars;
    Py_UCS4 sign_char = '\0';
    Py_ssize_t n_digits;

    Py_ssize_t n_remainder = 0;

    Py_ssize_t n_prefix = 0;
    Py_ssize_t n_total;
    Py_ssize_t prefix = 0;
    NumberFieldWidths spec;
    long x;



    LocaleInfo locale = {0, 0, 0};


    if (format->precision != -1) {
        PyErr_SetString(PyExc_ValueError,
                        "Precision not allowed in integer format specifier");
        goto done;
    }


    if (format->type == 'c') {

        if (format->sign != '\0') {
            PyErr_SetString(PyExc_ValueError,
                            "Sign not allowed with integer"
                            " format specifier 'c'");
            goto done;
        }



        x = PyLong_AsLong(value);
        if (x == -1 && PyErr_Occurred())
            goto done;
        if (x < 0 || x > 0x10ffff) {
            PyErr_SetString(PyExc_OverflowError,
                            "%c arg not in range(0x110000)");
            goto done;
        }
        tmp = PyUnicode_FromOrdinal(x);
        inumeric_chars = 0;
        n_digits = 1;
        maxchar = (((maxchar) > ((Py_UCS4)x)) ? (maxchar) : ((Py_UCS4)x));






        n_remainder = 1;
    }
    else {
        int base;
        int leading_chars_to_skip = 0;





        switch (format->type) {
        case 'b':
            base = 2;
            leading_chars_to_skip = 2;
            break;
        case 'o':
            base = 8;
            leading_chars_to_skip = 2;
            break;
        case 'x':
        case 'X':
            base = 16;
            leading_chars_to_skip = 2;
            break;
        default:
        case 'd':
        case 'n':
            base = 10;
            break;
        }

        if (format->sign != '+' && format->sign != ' '
            && format->width == -1
            && format->type != 'X' && format->type != 'n'
            && !format->thousands_separators
            && ((((PyObject*)(value))->ob_type) == &PyLong_Type))
        {

            return _PyLong_FormatWriter(writer, value, base, format->alternate);
        }



        if (format->alternate)
            n_prefix = leading_chars_to_skip;


        tmp = _PyLong_Format(value, base);
        if (tmp == ((void *)0) || ((__builtin_expect(!(((((((PyObject*)(tmp))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 913, "PyUnicode_Check(tmp)") : (void)0), ((((PyASCIIObject*)tmp)->state.ready) ? 0 : _PyUnicode_Ready((PyObject *)(tmp)))) == -1)
            goto done;

        inumeric_chars = 0;
        n_digits = ((__builtin_expect(!(((((((PyObject*)(tmp))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 917, "PyUnicode_Check(tmp)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)tmp)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 917, "PyUnicode_IS_READY(tmp)") : (void)0), ((PyASCIIObject *)(tmp))->length);

        prefix = inumeric_chars;



        if (((__builtin_expect(!(((((((PyObject*)(tmp))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 923, "PyUnicode_Check(tmp)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)tmp)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 923, "PyUnicode_IS_READY(tmp)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 923, "PyUnicode_Check((tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 923, "PyUnicode_IS_READY((tmp))") : (void)0), ((PyASCIIObject *)((tmp)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 923, "PyUnicode_Check((tmp))") : (void)0), (((PyASCIIObject*)((tmp)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 923, "PyUnicode_Check((tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 923, "PyUnicode_IS_READY((tmp))") : (void)0), ((PyASCIIObject*)(tmp))->state.ascii) ? ((void*)((PyASCIIObject*)((tmp)) + 1)) : ((void*)((PyCompactUnicodeObject*)((tmp)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((tmp)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 923, "((PyUnicodeObject*)((tmp)))->data.any") : (void)0), ((((PyUnicodeObject *)((tmp)))->data.any))))))[(inumeric_chars)] : (((__builtin_expect(!(((((((PyObject*)((tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 923, "PyUnicode_Check((tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 923, "PyUnicode_IS_READY((tmp))") : (void)0), ((PyASCIIObject *)((tmp)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 923, "PyUnicode_Check((tmp))") : (void)0), (((PyASCIIObject*)((tmp)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 923, "PyUnicode_Check((tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 923, "PyUnicode_IS_READY((tmp))") : (void)0), ((PyASCIIObject*)(tmp))->state.ascii) ? ((void*)((PyASCIIObject*)((tmp)) + 1)) : ((void*)((PyCompactUnicodeObject*)((tmp)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((tmp)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 923, "((PyUnicodeObject*)((tmp)))->data.any") : (void)0), ((((PyUnicodeObject *)((tmp)))->data.any))))))[(inumeric_chars)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 923, "PyUnicode_Check((tmp))") : (void)0), (((PyASCIIObject*)((tmp)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 923, "PyUnicode_Check((tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 923, "PyUnicode_IS_READY((tmp))") : (void)0), ((PyASCIIObject*)(tmp))->state.ascii) ? ((void*)((PyASCIIObject*)((tmp)) + 1)) : ((void*)((PyCompactUnicodeObject*)((tmp)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((tmp)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 923, "((PyUnicodeObject*)((tmp)))->data.any") : (void)0), ((((PyUnicodeObject *)((tmp)))->data.any))))))[(inumeric_chars)] ) )) == '-') {
            sign_char = '-';
            ++prefix;
            ++leading_chars_to_skip;
        }


        n_digits -= leading_chars_to_skip;
        inumeric_chars += leading_chars_to_skip;
    }


    if (get_locale_info(format->type == 'n' ? 0 :
                        (format->thousands_separators ?
                         1 :
                         2),
                        &locale) == -1)
        goto done;


    n_total = calc_number_widths(&spec, n_prefix, sign_char, tmp, inumeric_chars,
                                 inumeric_chars + n_digits, n_remainder, 0,
                                 &locale, format, &maxchar);


    if ((((maxchar) <= (writer)->maxchar && (n_total) <= (writer)->size - (writer)->pos) ? 0 : (((n_total) == 0) ? 0 : _PyUnicodeWriter_PrepareInternal((writer), (n_total), (maxchar)))) == -1)
        goto done;


    result = fill_number(writer, &spec,
                         tmp, inumeric_chars, inumeric_chars + n_digits,
                         tmp, prefix,
                         format->fill_char == '\0' ? ' ' : format->fill_char,
                         &locale, format->type == 'X');

done:
    do { if ((tmp) == ((void *)0)) ; else do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0); } while (0);
    free_locale_info(&locale);
    return result;
}






static int
format_float_internal(PyObject *value,
                      const InternalFormatSpec *format,
                      _PyUnicodeWriter *writer)
{
    char *buf = ((void *)0);
    Py_ssize_t n_digits;
    Py_ssize_t n_remainder;
    Py_ssize_t n_total;
    int has_decimal;
    double val;
    Py_ssize_t precision = format->precision;
    Py_ssize_t default_precision = 6;
    Py_UCS4 type = format->type;
    int add_pct = 0;
    Py_ssize_t index;
    NumberFieldWidths spec;
    int flags = 0;
    int result = -1;
    Py_UCS4 maxchar = 127;
    Py_UCS4 sign_char = '\0';
    int float_type;
    PyObject *unicode_tmp = ((void *)0);



    LocaleInfo locale = {0, 0, 0};

    if (format->alternate)
        flags |= 0x04;

    if (type == '\0') {



        flags |= 0x02;
        type = 'r';
        default_precision = 0;
    }

    if (type == 'n')


        type = 'g';

    val = PyFloat_AsDouble(value);
    if (val == -1.0 && PyErr_Occurred())
        goto done;

    if (type == '%') {
        type = 'f';
        val *= 100;
        add_pct = 1;
    }

    if (precision < 0)
        precision = default_precision;
    else if (type == 'r')
        type = 'g';




    buf = PyOS_double_to_string(val, (char)type, precision, flags,
                                &float_type);
    if (buf == ((void *)0))
        goto done;
    n_digits = strlen(buf);

    if (add_pct) {



        buf[n_digits] = '%';
        n_digits += 1;
    }



    unicode_tmp = _PyUnicode_FromASCII(buf, n_digits);
    PyMem_Free(buf);
    if (unicode_tmp == ((void *)0))
        goto done;

    if (format->sign != '+' && format->sign != ' '
        && format->width == -1
        && format->type != 'n'
        && !format->thousands_separators)
    {

        result = _PyUnicodeWriter_WriteStr(writer, unicode_tmp);
        do { if ( --((PyObject*)(unicode_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(unicode_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(unicode_tmp)))); } while (0);
        return result;
    }



    index = 0;
    if (((__builtin_expect(!(((((((PyObject*)(unicode_tmp))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1067, "PyUnicode_Check(unicode_tmp)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)unicode_tmp)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1067, "PyUnicode_IS_READY(unicode_tmp)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1067, "PyUnicode_Check((unicode_tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(unicode_tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1067, "PyUnicode_IS_READY((unicode_tmp))") : (void)0), ((PyASCIIObject *)((unicode_tmp)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1067, "PyUnicode_Check((unicode_tmp))") : (void)0), (((PyASCIIObject*)((unicode_tmp)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1067, "PyUnicode_Check((unicode_tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(unicode_tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1067, "PyUnicode_IS_READY((unicode_tmp))") : (void)0), ((PyASCIIObject*)(unicode_tmp))->state.ascii) ? ((void*)((PyASCIIObject*)((unicode_tmp)) + 1)) : ((void*)((PyCompactUnicodeObject*)((unicode_tmp)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((unicode_tmp)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1067, "((PyUnicodeObject*)((unicode_tmp)))->data.any") : (void)0), ((((PyUnicodeObject *)((unicode_tmp)))->data.any))))))[(index)] : (((__builtin_expect(!(((((((PyObject*)((unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1067, "PyUnicode_Check((unicode_tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(unicode_tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1067, "PyUnicode_IS_READY((unicode_tmp))") : (void)0), ((PyASCIIObject *)((unicode_tmp)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1067, "PyUnicode_Check((unicode_tmp))") : (void)0), (((PyASCIIObject*)((unicode_tmp)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1067, "PyUnicode_Check((unicode_tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(unicode_tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1067, "PyUnicode_IS_READY((unicode_tmp))") : (void)0), ((PyASCIIObject*)(unicode_tmp))->state.ascii) ? ((void*)((PyASCIIObject*)((unicode_tmp)) + 1)) : ((void*)((PyCompactUnicodeObject*)((unicode_tmp)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((unicode_tmp)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1067, "((PyUnicodeObject*)((unicode_tmp)))->data.any") : (void)0), ((((PyUnicodeObject *)((unicode_tmp)))->data.any))))))[(index)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1067, "PyUnicode_Check((unicode_tmp))") : (void)0), (((PyASCIIObject*)((unicode_tmp)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1067, "PyUnicode_Check((unicode_tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(unicode_tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1067, "PyUnicode_IS_READY((unicode_tmp))") : (void)0), ((PyASCIIObject*)(unicode_tmp))->state.ascii) ? ((void*)((PyASCIIObject*)((unicode_tmp)) + 1)) : ((void*)((PyCompactUnicodeObject*)((unicode_tmp)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((unicode_tmp)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1067, "((PyUnicodeObject*)((unicode_tmp)))->data.any") : (void)0), ((((PyUnicodeObject *)((unicode_tmp)))->data.any))))))[(index)] ) )) == '-') {
        sign_char = '-';
        ++index;
        --n_digits;
    }



    parse_number(unicode_tmp, index, index + n_digits, &n_remainder, &has_decimal);


    if (get_locale_info(format->type == 'n' ? 0 :
                        (format->thousands_separators ?
                         1 :
                         2),
                        &locale) == -1)
        goto done;


    n_total = calc_number_widths(&spec, 0, sign_char, unicode_tmp, index,
                                 index + n_digits, n_remainder, has_decimal,
                                 &locale, format, &maxchar);


    if ((((maxchar) <= (writer)->maxchar && (n_total) <= (writer)->size - (writer)->pos) ? 0 : (((n_total) == 0) ? 0 : _PyUnicodeWriter_PrepareInternal((writer), (n_total), (maxchar)))) == -1)
        goto done;


    result = fill_number(writer, &spec,
                         unicode_tmp, index, index + n_digits,
                         ((void *)0), 0,
                         format->fill_char == '\0' ? ' ' : format->fill_char,
                         &locale, 0);

done:
    do { if ((unicode_tmp) == ((void *)0)) ; else do { if ( --((PyObject*)(unicode_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(unicode_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(unicode_tmp)))); } while (0); } while (0);
    free_locale_info(&locale);
    return result;
}





static int
format_complex_internal(PyObject *value,
                        const InternalFormatSpec *format,
                        _PyUnicodeWriter *writer)
{
    double re;
    double im;
    char *re_buf = ((void *)0);
    char *im_buf = ((void *)0);

    InternalFormatSpec tmp_format = *format;
    Py_ssize_t n_re_digits;
    Py_ssize_t n_im_digits;
    Py_ssize_t n_re_remainder;
    Py_ssize_t n_im_remainder;
    Py_ssize_t n_re_total;
    Py_ssize_t n_im_total;
    int re_has_decimal;
    int im_has_decimal;
    Py_ssize_t precision = format->precision;
    Py_ssize_t default_precision = 6;
    Py_UCS4 type = format->type;
    Py_ssize_t i_re;
    Py_ssize_t i_im;
    NumberFieldWidths re_spec;
    NumberFieldWidths im_spec;
    int flags = 0;
    int result = -1;
    Py_UCS4 maxchar = 127;
    enum PyUnicode_Kind rkind;
    void *rdata;
    Py_UCS4 re_sign_char = '\0';
    Py_UCS4 im_sign_char = '\0';
    int re_float_type;
    int im_float_type;
    int add_parens = 0;
    int skip_re = 0;
    Py_ssize_t lpad;
    Py_ssize_t rpad;
    Py_ssize_t total;
    PyObject *re_unicode_tmp = ((void *)0);
    PyObject *im_unicode_tmp = ((void *)0);



    LocaleInfo locale = {0, 0, 0};


    if (format->fill_char == '0') {
        PyErr_SetString(PyExc_ValueError,
                        "Zero padding is not allowed in complex format "
                        "specifier");
        goto done;
    }


    if (format->align == '=') {
        PyErr_SetString(PyExc_ValueError,
                        "'=' alignment flag is not allowed in complex format "
                        "specifier");
        goto done;
    }

    re = PyComplex_RealAsDouble(value);
    if (re == -1.0 && PyErr_Occurred())
        goto done;
    im = PyComplex_ImagAsDouble(value);
    if (im == -1.0 && PyErr_Occurred())
        goto done;

    if (format->alternate)
        flags |= 0x04;

    if (type == '\0') {

        type = 'r';
        default_precision = 0;
        if (re == 0.0 && copysign(1.0, re) == 1.0)
            skip_re = 1;
        else
            add_parens = 1;
    }

    if (type == 'n')


        type = 'g';

    if (precision < 0)
        precision = default_precision;
    else if (type == 'r')
        type = 'g';




    re_buf = PyOS_double_to_string(re, (char)type, precision, flags,
                                   &re_float_type);
    if (re_buf == ((void *)0))
        goto done;
    im_buf = PyOS_double_to_string(im, (char)type, precision, flags,
                                   &im_float_type);
    if (im_buf == ((void *)0))
        goto done;

    n_re_digits = strlen(re_buf);
    n_im_digits = strlen(im_buf);



    re_unicode_tmp = _PyUnicode_FromASCII(re_buf, n_re_digits);
    if (re_unicode_tmp == ((void *)0))
        goto done;
    i_re = 0;

    im_unicode_tmp = _PyUnicode_FromASCII(im_buf, n_im_digits);
    if (im_unicode_tmp == ((void *)0))
        goto done;
    i_im = 0;



    if (((__builtin_expect(!(((((((PyObject*)(re_unicode_tmp))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1233, "PyUnicode_Check(re_unicode_tmp)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)re_unicode_tmp)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1233, "PyUnicode_IS_READY(re_unicode_tmp)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((re_unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1233, "PyUnicode_Check((re_unicode_tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(re_unicode_tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1233, "PyUnicode_IS_READY((re_unicode_tmp))") : (void)0), ((PyASCIIObject *)((re_unicode_tmp)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((re_unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1233, "PyUnicode_Check((re_unicode_tmp))") : (void)0), (((PyASCIIObject*)((re_unicode_tmp)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((re_unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1233, "PyUnicode_Check((re_unicode_tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(re_unicode_tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1233, "PyUnicode_IS_READY((re_unicode_tmp))") : (void)0), ((PyASCIIObject*)(re_unicode_tmp))->state.ascii) ? ((void*)((PyASCIIObject*)((re_unicode_tmp)) + 1)) : ((void*)((PyCompactUnicodeObject*)((re_unicode_tmp)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((re_unicode_tmp)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1233, "((PyUnicodeObject*)((re_unicode_tmp)))->data.any") : (void)0), ((((PyUnicodeObject *)((re_unicode_tmp)))->data.any))))))[(i_re)] : (((__builtin_expect(!(((((((PyObject*)((re_unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1233, "PyUnicode_Check((re_unicode_tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(re_unicode_tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1233, "PyUnicode_IS_READY((re_unicode_tmp))") : (void)0), ((PyASCIIObject *)((re_unicode_tmp)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((re_unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1233, "PyUnicode_Check((re_unicode_tmp))") : (void)0), (((PyASCIIObject*)((re_unicode_tmp)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((re_unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1233, "PyUnicode_Check((re_unicode_tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(re_unicode_tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1233, "PyUnicode_IS_READY((re_unicode_tmp))") : (void)0), ((PyASCIIObject*)(re_unicode_tmp))->state.ascii) ? ((void*)((PyASCIIObject*)((re_unicode_tmp)) + 1)) : ((void*)((PyCompactUnicodeObject*)((re_unicode_tmp)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((re_unicode_tmp)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1233, "((PyUnicodeObject*)((re_unicode_tmp)))->data.any") : (void)0), ((((PyUnicodeObject *)((re_unicode_tmp)))->data.any))))))[(i_re)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((re_unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1233, "PyUnicode_Check((re_unicode_tmp))") : (void)0), (((PyASCIIObject*)((re_unicode_tmp)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((re_unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1233, "PyUnicode_Check((re_unicode_tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(re_unicode_tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1233, "PyUnicode_IS_READY((re_unicode_tmp))") : (void)0), ((PyASCIIObject*)(re_unicode_tmp))->state.ascii) ? ((void*)((PyASCIIObject*)((re_unicode_tmp)) + 1)) : ((void*)((PyCompactUnicodeObject*)((re_unicode_tmp)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((re_unicode_tmp)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1233, "((PyUnicodeObject*)((re_unicode_tmp)))->data.any") : (void)0), ((((PyUnicodeObject *)((re_unicode_tmp)))->data.any))))))[(i_re)] ) )) == '-') {
        re_sign_char = '-';
        ++i_re;
        --n_re_digits;
    }
    if (((__builtin_expect(!(((((((PyObject*)(im_unicode_tmp))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1238, "PyUnicode_Check(im_unicode_tmp)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)im_unicode_tmp)->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1238, "PyUnicode_IS_READY(im_unicode_tmp)") : (void)0), (Py_UCS4) (((__builtin_expect(!(((((((PyObject*)((im_unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1238, "PyUnicode_Check((im_unicode_tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(im_unicode_tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1238, "PyUnicode_IS_READY((im_unicode_tmp))") : (void)0), ((PyASCIIObject *)((im_unicode_tmp)))->state.kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(((__builtin_expect(!(((((((PyObject*)((im_unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1238, "PyUnicode_Check((im_unicode_tmp))") : (void)0), (((PyASCIIObject*)((im_unicode_tmp)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((im_unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1238, "PyUnicode_Check((im_unicode_tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(im_unicode_tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1238, "PyUnicode_IS_READY((im_unicode_tmp))") : (void)0), ((PyASCIIObject*)(im_unicode_tmp))->state.ascii) ? ((void*)((PyASCIIObject*)((im_unicode_tmp)) + 1)) : ((void*)((PyCompactUnicodeObject*)((im_unicode_tmp)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((im_unicode_tmp)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1238, "((PyUnicodeObject*)((im_unicode_tmp)))->data.any") : (void)0), ((((PyUnicodeObject *)((im_unicode_tmp)))->data.any))))))[(i_im)] : (((__builtin_expect(!(((((((PyObject*)((im_unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1238, "PyUnicode_Check((im_unicode_tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(im_unicode_tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1238, "PyUnicode_IS_READY((im_unicode_tmp))") : (void)0), ((PyASCIIObject *)((im_unicode_tmp)))->state.kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(((__builtin_expect(!(((((((PyObject*)((im_unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1238, "PyUnicode_Check((im_unicode_tmp))") : (void)0), (((PyASCIIObject*)((im_unicode_tmp)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((im_unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1238, "PyUnicode_Check((im_unicode_tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(im_unicode_tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1238, "PyUnicode_IS_READY((im_unicode_tmp))") : (void)0), ((PyASCIIObject*)(im_unicode_tmp))->state.ascii) ? ((void*)((PyASCIIObject*)((im_unicode_tmp)) + 1)) : ((void*)((PyCompactUnicodeObject*)((im_unicode_tmp)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((im_unicode_tmp)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1238, "((PyUnicodeObject*)((im_unicode_tmp)))->data.any") : (void)0), ((((PyUnicodeObject *)((im_unicode_tmp)))->data.any))))))[(i_im)] : ((const Py_UCS4 *)(((__builtin_expect(!(((((((PyObject*)((im_unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1238, "PyUnicode_Check((im_unicode_tmp))") : (void)0), (((PyASCIIObject*)((im_unicode_tmp)))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)((im_unicode_tmp)))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1238, "PyUnicode_Check((im_unicode_tmp))") : (void)0), (__builtin_expect(!((((PyASCIIObject*)(im_unicode_tmp))->state.ready)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1238, "PyUnicode_IS_READY((im_unicode_tmp))") : (void)0), ((PyASCIIObject*)(im_unicode_tmp))->state.ascii) ? ((void*)((PyASCIIObject*)((im_unicode_tmp)) + 1)) : ((void*)((PyCompactUnicodeObject*)((im_unicode_tmp)) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)((im_unicode_tmp)))->data.any), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1238, "((PyUnicodeObject*)((im_unicode_tmp)))->data.any") : (void)0), ((((PyUnicodeObject *)((im_unicode_tmp)))->data.any))))))[(i_im)] ) )) == '-') {
        im_sign_char = '-';
        ++i_im;
        --n_im_digits;
    }



    parse_number(re_unicode_tmp, i_re, i_re + n_re_digits,
                 &n_re_remainder, &re_has_decimal);
    parse_number(im_unicode_tmp, i_im, i_im + n_im_digits,
                 &n_im_remainder, &im_has_decimal);


    if (get_locale_info(format->type == 'n' ? 0 :
                        (format->thousands_separators ?
                         1 :
                         2),
                        &locale) == -1)
        goto done;



    tmp_format.fill_char = '\0';
    tmp_format.align = '<';
    tmp_format.width = -1;


    n_re_total = calc_number_widths(&re_spec, 0, re_sign_char, re_unicode_tmp,
                                    i_re, i_re + n_re_digits, n_re_remainder,
                                    re_has_decimal, &locale, &tmp_format,
                                    &maxchar);




    if (!skip_re)
        tmp_format.sign = '+';
    n_im_total = calc_number_widths(&im_spec, 0, im_sign_char, im_unicode_tmp,
                                    i_im, i_im + n_im_digits, n_im_remainder,
                                    im_has_decimal, &locale, &tmp_format,
                                    &maxchar);

    if (skip_re)
        n_re_total = 0;


    calc_padding(n_re_total + n_im_total + 1 + add_parens * 2,
                 format->width, format->align, &lpad, &rpad, &total);

    if (lpad || rpad)
        maxchar = (((maxchar) > (format->fill_char)) ? (maxchar) : (format->fill_char));

    if ((((maxchar) <= (writer)->maxchar && (total) <= (writer)->size - (writer)->pos) ? 0 : (((total) == 0) ? 0 : _PyUnicodeWriter_PrepareInternal((writer), (total), (maxchar)))) == -1)
        goto done;
    rkind = writer->kind;
    rdata = writer->data;


    result = fill_padding(writer,
                          n_re_total + n_im_total + 1 + add_parens * 2,
                          format->fill_char=='\0' ? ' ' : format->fill_char,
                          lpad, rpad);
    if (result == -1)
        goto done;

    if (add_parens) {
        do { switch ((rkind)) { case PyUnicode_1BYTE_KIND: { ((Py_UCS1 *)(rdata))[(writer->pos)] = (Py_UCS1)('('); break; } case PyUnicode_2BYTE_KIND: { ((Py_UCS2 *)(rdata))[(writer->pos)] = (Py_UCS2)('('); break; } default: { (__builtin_expect(!((rkind) == PyUnicode_4BYTE_KIND), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1305, "(rkind) == PyUnicode_4BYTE_KIND") : (void)0); ((Py_UCS4 *)(rdata))[(writer->pos)] = (Py_UCS4)('('); } } } while (0);
        writer->pos++;
    }

    if (!skip_re) {
        result = fill_number(writer, &re_spec,
                             re_unicode_tmp, i_re, i_re + n_re_digits,
                             ((void *)0), 0,
                             0,
                             &locale, 0);
        if (result == -1)
            goto done;
    }
    result = fill_number(writer, &im_spec,
                         im_unicode_tmp, i_im, i_im + n_im_digits,
                         ((void *)0), 0,
                         0,
                         &locale, 0);
    if (result == -1)
        goto done;
    do { switch ((rkind)) { case PyUnicode_1BYTE_KIND: { ((Py_UCS1 *)(rdata))[(writer->pos)] = (Py_UCS1)('j'); break; } case PyUnicode_2BYTE_KIND: { ((Py_UCS2 *)(rdata))[(writer->pos)] = (Py_UCS2)('j'); break; } default: { (__builtin_expect(!((rkind) == PyUnicode_4BYTE_KIND), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1325, "(rkind) == PyUnicode_4BYTE_KIND") : (void)0); ((Py_UCS4 *)(rdata))[(writer->pos)] = (Py_UCS4)('j'); } } } while (0);
    writer->pos++;

    if (add_parens) {
        do { switch ((rkind)) { case PyUnicode_1BYTE_KIND: { ((Py_UCS1 *)(rdata))[(writer->pos)] = (Py_UCS1)(')'); break; } case PyUnicode_2BYTE_KIND: { ((Py_UCS2 *)(rdata))[(writer->pos)] = (Py_UCS2)(')'); break; } default: { (__builtin_expect(!((rkind) == PyUnicode_4BYTE_KIND), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1329, "(rkind) == PyUnicode_4BYTE_KIND") : (void)0); ((Py_UCS4 *)(rdata))[(writer->pos)] = (Py_UCS4)(')'); } } } while (0);
        writer->pos++;
    }

    writer->pos += rpad;

done:
    PyMem_Free(re_buf);
    PyMem_Free(im_buf);
    do { if ((re_unicode_tmp) == ((void *)0)) ; else do { if ( --((PyObject*)(re_unicode_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(re_unicode_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(re_unicode_tmp)))); } while (0); } while (0);
    do { if ((im_unicode_tmp) == ((void *)0)) ; else do { if ( --((PyObject*)(im_unicode_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(im_unicode_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(im_unicode_tmp)))); } while (0); } while (0);
    free_locale_info(&locale);
    return result;
}




static int
format_obj(PyObject *obj, _PyUnicodeWriter *writer)
{
    PyObject *str;
    int err;

    str = PyObject_Str(obj);
    if (str == ((void *)0))
        return -1;
    err = _PyUnicodeWriter_WriteStr(writer, str);
    do { if ( --((PyObject*)(str))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(str)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(str)))); } while (0);
    return err;
}

int
_PyUnicode_FormatAdvancedWriter(_PyUnicodeWriter *writer,
                                PyObject *obj,
                                PyObject *format_spec,
                                Py_ssize_t start, Py_ssize_t end)
{
    InternalFormatSpec format;

    (__builtin_expect(!(((((((PyObject*)(obj))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "formatter_unicode.c", 1369, "PyUnicode_Check(obj)") : (void)0);



    if (start == end) {
        if (((((PyObject*)(obj))->ob_type) == &PyUnicode_Type))
            return _PyUnicodeWriter_WriteStr(writer, obj);
        else
            return format_obj(obj, writer);
    }


    if (!parse_internal_render_format_spec(format_spec, start, end,
                                           &format, 's', '<'))
        return -1;


    switch (format.type) {
    case 's':

        return format_string_internal(obj, &format, writer);
    default:

        unknown_presentation_type(format.type, obj->ob_type->tp_name);
        return -1;
    }
}

int
_PyLong_FormatAdvancedWriter(_PyUnicodeWriter *writer,
                             PyObject *obj,
                             PyObject *format_spec,
                             Py_ssize_t start, Py_ssize_t end)
{
    PyObject *tmp = ((void *)0), *str = ((void *)0);
    InternalFormatSpec format;
    int result = -1;



    if (start == end) {
        if (((((PyObject*)(obj))->ob_type) == &PyLong_Type))
            return _PyLong_FormatWriter(writer, obj, 10, 0);
        else
            return format_obj(obj, writer);
    }


    if (!parse_internal_render_format_spec(format_spec, start, end,
                                           &format, 'd', '>'))
        goto done;


    switch (format.type) {
    case 'b':
    case 'c':
    case 'd':
    case 'o':
    case 'x':
    case 'X':
    case 'n':


        result = format_long_internal(obj, &format, writer);
        break;

    case 'e':
    case 'E':
    case 'f':
    case 'F':
    case 'g':
    case 'G':
    case '%':

        tmp = PyNumber_Float(obj);
        if (tmp == ((void *)0))
            goto done;
        result = format_float_internal(tmp, &format, writer);
        break;

    default:

        unknown_presentation_type(format.type, obj->ob_type->tp_name);
        goto done;
    }

done:
    do { if ((tmp) == ((void *)0)) ; else do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0); } while (0);
    do { if ((str) == ((void *)0)) ; else do { if ( --((PyObject*)(str))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(str)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(str)))); } while (0); } while (0);
    return result;
}

int
_PyFloat_FormatAdvancedWriter(_PyUnicodeWriter *writer,
                              PyObject *obj,
                              PyObject *format_spec,
                              Py_ssize_t start, Py_ssize_t end)
{
    InternalFormatSpec format;



    if (start == end)
        return format_obj(obj, writer);


    if (!parse_internal_render_format_spec(format_spec, start, end,
                                           &format, '\0', '>'))
        return -1;


    switch (format.type) {
    case '\0':
    case 'e':
    case 'E':
    case 'f':
    case 'F':
    case 'g':
    case 'G':
    case 'n':
    case '%':

        return format_float_internal(obj, &format, writer);

    default:

        unknown_presentation_type(format.type, obj->ob_type->tp_name);
        return -1;
    }
}

int
_PyComplex_FormatAdvancedWriter(_PyUnicodeWriter *writer,
                                PyObject *obj,
                                PyObject *format_spec,
                                Py_ssize_t start, Py_ssize_t end)
{
    InternalFormatSpec format;



    if (start == end)
        return format_obj(obj, writer);


    if (!parse_internal_render_format_spec(format_spec, start, end,
                                           &format, '\0', '>'))
        return -1;


    switch (format.type) {
    case '\0':
    case 'e':
    case 'E':
    case 'f':
    case 'F':
    case 'g':
    case 'G':
    case 'n':

        return format_complex_internal(obj, &format, writer);

    default:

        unknown_presentation_type(format.type, obj->ob_type->tp_name);
        return -1;
    }
}
