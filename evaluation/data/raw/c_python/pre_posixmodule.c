# 1 "posixmodule.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "posixmodule.c"
# 20 "posixmodule.c"
#pragma weak lchown
#pragma weak statvfs
#pragma weak fstatvfs





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
# 29 "posixmodule.c" 2

# 1 "posixmodule.h" 1
# 10 "posixmodule.h"
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
# 11 "posixmodule.h" 2




PyObject * _PyLong_FromUid(uid_t);
PyObject * _PyLong_FromGid(gid_t);
int _Py_Uid_Converter(PyObject *, void *);
int _Py_Gid_Converter(PyObject *, void *);
# 31 "posixmodule.c" 2
# 42 "posixmodule.c"
static char posix__doc__[] = "This module provides access to operating system functionality that is\nstandardized by the C Standard and the POSIX standard (a thinly\ndisguised Unix interface).  Refer to the library manual and\ncorresponding Unix manual entries for more information on calls.";
# 66 "posixmodule.c"
# 1 "/usr/include/sys/uio.h" 1 3 4
# 90 "/usr/include/sys/uio.h" 3 4
struct iovec {
 void * iov_base;
 size_t iov_len;
};
# 103 "/usr/include/sys/uio.h" 3 4
enum uio_rw { UIO_READ, UIO_WRITE };





ssize_t readv(int, const struct iovec *, int) __asm("_" "readv" );
ssize_t writev(int, const struct iovec *, int) __asm("_" "writev" );

# 67 "posixmodule.c" 2
# 82 "posixmodule.c"
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
# 83 "posixmodule.c" 2



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
# 87 "posixmodule.c" 2



# 1 "/usr/include/grp.h" 1 3 4
# 87 "/usr/include/grp.h" 3 4
struct group {
 char *gr_name;
 char *gr_passwd;
 gid_t gr_gid;
 char **gr_mem;
};





struct group *getgrgid(gid_t);
struct group *getgrnam(const char *);

int getgrgid_r(gid_t, struct group *, char *, size_t, struct group **);
int getgrnam_r(const char *, struct group *, char *, size_t, struct group **);

struct group *getgrent(void);
void setgrent(void);
void endgrent(void);



char *group_from_gid(gid_t, int);

void setgrfile(const char *);
int setgroupent(int);


# 91 "posixmodule.c" 2



# 1 "/usr/include/sysexits.h" 1 3 4
# 95 "posixmodule.c" 2







# 1 "/usr/include/langinfo.h" 1 3 4
# 35 "/usr/include/langinfo.h" 3 4
typedef __darwin_nl_item nl_item;
# 116 "/usr/include/langinfo.h" 3 4

char *nl_langinfo(nl_item);

# 103 "posixmodule.c" 2







# 1 "/usr/include/sched.h" 1 3 4
# 27 "/usr/include/sched.h" 3 4
# 1 "/usr/include/pthread_impl.h" 1 3 4
# 28 "/usr/include/sched.h" 2 3 4







struct sched_param { int sched_priority; char __opaque[4]; };


extern int sched_yield(void);
extern int sched_get_priority_min(int);
extern int sched_get_priority_max(int);

# 111 "posixmodule.c" 2
# 127 "posixmodule.c"
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


# 128 "posixmodule.c" 2




# 1 "/usr/include/dlfcn.h" 1 3 4
# 40 "/usr/include/dlfcn.h" 3 4
# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stdbool.h" 1 3 4
# 41 "/usr/include/dlfcn.h" 2 3 4




typedef struct dl_info {
        const char *dli_fname;
        void *dli_fbase;
        const char *dli_sname;
        void *dli_saddr;
} Dl_info;

extern int dladdr(const void *, Dl_info *);


extern int dlclose(void * __handle);
extern char * dlerror(void);
extern void * dlopen(const char * __path, int __mode);
extern void * dlsym(void * __handle, const char * __symbol);


extern _Bool dlopen_preflight(const char* __path) ;
# 133 "posixmodule.c" 2





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

# 139 "posixmodule.c" 2
# 266 "posixmodule.c"
# 1 "/usr/include/utime.h" 1 3 4
# 68 "/usr/include/utime.h" 3 4
struct utimbuf {
 time_t actime;
 time_t modtime;
};




int utime(const char *, const struct utimbuf *);

# 267 "posixmodule.c" 2
# 275 "posixmodule.c"
# 1 "/usr/include/sys/times.h" 1 3 4
# 85 "/usr/include/sys/times.h" 3 4
struct tms {
 clock_t tms_utime;
 clock_t tms_stime;
 clock_t tms_cutime;
 clock_t tms_cstime;
};


clock_t times(struct tms *);

# 276 "posixmodule.c" 2



# 1 "/usr/include/sys/param.h" 1 3 4
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
# 280 "posixmodule.c" 2



# 1 "/usr/include/sys/utsname.h" 1 3 4
# 74 "/usr/include/sys/utsname.h" 3 4
struct utsname {
 char sysname[256];
 char nodename[256];
 char release[256];
 char version[256];
 char machine[256];
};


int uname(struct utsname *);

# 284 "posixmodule.c" 2



# 1 "/usr/include/dirent.h" 1 3 4
# 65 "/usr/include/dirent.h" 3 4
# 1 "/usr/include/sys/dirent.h" 1 3 4
# 89 "/usr/include/sys/dirent.h" 3 4
#pragma pack(4)
# 101 "/usr/include/sys/dirent.h" 3 4
#pragma pack()
# 115 "/usr/include/sys/dirent.h" 3 4
struct dirent { __uint64_t d_ino; __uint64_t d_seekoff; __uint16_t d_reclen; __uint16_t d_namlen; __uint8_t d_type; char d_name[1024]; };
# 66 "/usr/include/dirent.h" 2 3 4


struct _telldir;


typedef struct {
 int __dd_fd;
 long __dd_loc;
 long __dd_size;
 char *__dd_buf;
 int __dd_len;
 long __dd_seek;
 long __dd_rewind;
 int __dd_flags;
 __darwin_pthread_mutex_t __dd_lock;
 struct _telldir *__dd_td;
} DIR;
# 102 "/usr/include/dirent.h" 3 4


int alphasort(const void *, const void *) __asm("_" "alphasort" "$INODE64");

int closedir(DIR *) __asm("_" "closedir" );

int getdirentries(int, char *, int, long *)





      __asm("_getdirentries_is_not_available_when_64_bit_inodes_are_in_effect")



;

DIR *opendir(const char *) __asm("_" "opendir" "$INODE64" );

DIR *__opendir2(const char *, int) __asm("_" "__opendir2" "$INODE64" );

struct dirent *readdir(DIR *) __asm("_" "readdir" "$INODE64");
int readdir_r(DIR *, struct dirent *, struct dirent **) __asm("_" "readdir_r" "$INODE64");
void rewinddir(DIR *) __asm("_" "rewinddir" "$INODE64" );

int scandir(const char *, struct dirent ***,
    int (*)(struct dirent *), int (*)(const void *, const void *)) __asm("_" "scandir" "$INODE64");

int scandir_b(const char *, struct dirent ***,
    int (^)(struct dirent *), int (^)(const void *, const void *)) __asm("_" "scandir_b" "$INODE64") __attribute__((visibility("default")));


void seekdir(DIR *, long) __asm("_" "seekdir" "$INODE64" );
long telldir(DIR *) __asm("_" "telldir" "$INODE64" );

# 288 "posixmodule.c" 2
# 420 "posixmodule.c"
PyObject *
_PyLong_FromUid(uid_t uid)
{
    if (uid == (uid_t)-1)
        return PyLong_FromLong(-1);
    return PyLong_FromUnsignedLong(uid);
}

PyObject *
_PyLong_FromGid(gid_t gid)
{
    if (gid == (gid_t)-1)
        return PyLong_FromLong(-1);
    return PyLong_FromUnsignedLong(gid);
}

int
_Py_Uid_Converter(PyObject *obj, void *p)
{
    int overflow;
    long result;
    if (((((PyObject*)(obj))->ob_type) == (&PyFloat_Type) || PyType_IsSubtype((((PyObject*)(obj))->ob_type), (&PyFloat_Type)))) {
        PyErr_SetString(PyExc_TypeError,
                        "integer argument expected, got float");
        return 0;
    }
    result = PyLong_AsLongAndOverflow(obj, &overflow);
    if (overflow < 0)
        goto OverflowDown;
    if (!overflow && result == -1) {

        if (PyErr_Occurred())
            return 0;
        *(uid_t *)p = (uid_t)-1;
    }
    else {

        unsigned long uresult;
        if (overflow > 0) {
            uresult = PyLong_AsUnsignedLong(obj);
            if (PyErr_Occurred()) {
                if (PyErr_ExceptionMatches(PyExc_OverflowError))
                    goto OverflowUp;
                return 0;
            }
            if ((uid_t)uresult == (uid_t)-1)
                goto OverflowUp;
        } else {
            if (result < 0)
                goto OverflowDown;
            uresult = result;
        }
        if (sizeof(uid_t) < sizeof(long) &&
            (unsigned long)(uid_t)uresult != uresult)
            goto OverflowUp;
        *(uid_t *)p = (uid_t)uresult;
    }
    return 1;

OverflowDown:
    PyErr_SetString(PyExc_OverflowError,
                    "user id is less than minimum");
    return 0;

OverflowUp:
    PyErr_SetString(PyExc_OverflowError,
                    "user id is greater than maximum");
    return 0;
}

int
_Py_Gid_Converter(PyObject *obj, void *p)
{
    int overflow;
    long result;
    if (((((PyObject*)(obj))->ob_type) == (&PyFloat_Type) || PyType_IsSubtype((((PyObject*)(obj))->ob_type), (&PyFloat_Type)))) {
        PyErr_SetString(PyExc_TypeError,
                        "integer argument expected, got float");
        return 0;
    }
    result = PyLong_AsLongAndOverflow(obj, &overflow);
    if (overflow < 0)
        goto OverflowDown;
    if (!overflow && result == -1) {

        if (PyErr_Occurred())
            return 0;
        *(gid_t *)p = (gid_t)-1;
    }
    else {

        unsigned long uresult;
        if (overflow > 0) {
            uresult = PyLong_AsUnsignedLong(obj);
            if (PyErr_Occurred()) {
                if (PyErr_ExceptionMatches(PyExc_OverflowError))
                    goto OverflowUp;
                return 0;
            }
            if ((gid_t)uresult == (gid_t)-1)
                goto OverflowUp;
        } else {
            if (result < 0)
                goto OverflowDown;
            uresult = result;
        }
        if (sizeof(gid_t) < sizeof(long) &&
            (unsigned long)(gid_t)uresult != uresult)
            goto OverflowUp;
        *(gid_t *)p = (gid_t)uresult;
    }
    return 1;

OverflowDown:
    PyErr_SetString(PyExc_OverflowError,
                    "group id is less than minimum");
    return 0;

OverflowUp:
    PyErr_SetString(PyExc_OverflowError,
                    "group id is greater than maximum");
    return 0;
}
# 559 "posixmodule.c"
static int
_fd_converter(PyObject *o, int *p, const char *allowed)
{
    int overflow;
    long long_value = PyLong_AsLongAndOverflow(o, &overflow);
    if (((((PyObject*)(o))->ob_type) == (&PyFloat_Type) || PyType_IsSubtype((((PyObject*)(o))->ob_type), (&PyFloat_Type))) ||
        (long_value == -1 && !overflow && PyErr_Occurred())) {
        PyErr_Clear();
        PyErr_Format(PyExc_TypeError,
                        "argument should be %s, not %.200s",
                        allowed, (((PyObject*)(o))->ob_type)->tp_name);
        return 0;
    }
    if (overflow > 0 || long_value > 2147483647) {
        PyErr_SetString(PyExc_OverflowError,
                        "signed integer is greater than maximum");
        return 0;
    }
    if (overflow < 0 || long_value < (-2147483647 - 1)) {
        PyErr_SetString(PyExc_OverflowError,
                        "signed integer is less than minimum");
        return 0;
    }
    *p = (int)long_value;
    return 1;
}

static int
dir_fd_converter(PyObject *o, void *p)
{
    if (o == (&_Py_NoneStruct)) {
        *(int *)p = (-100);
        return 1;
    }
    return _fd_converter(o, (int *)p, "integer");
}
# 680 "posixmodule.c"
typedef struct {
    char *function_name;
    char *argument_name;
    int nullable;
    int allow_fd;
    wchar_t *wide;
    char *narrow;
    int fd;
    Py_ssize_t length;
    PyObject *object;
    PyObject *cleanup;
} path_t;

static void
path_cleanup(path_t *path) {
    if (path->cleanup) {
        do { if ( --((PyObject*)(path->cleanup))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(path->cleanup)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(path->cleanup)))); } while (0);
        path->cleanup = ((void *)0);
    }
}

static int
path_converter(PyObject *o, void *p) {
    path_t *path = (path_t *)p;
    PyObject *unicode, *bytes;
    Py_ssize_t length;
    char *narrow;
# 715 "posixmodule.c"
    if (o == ((void *)0)) {
        path_cleanup(path);
        return 1;
    }


    path->cleanup = ((void *)0);

    if (o == (&_Py_NoneStruct)) {
        if (!path->nullable) {
            PyErr_Format(PyExc_TypeError, "%s%s" "can't specify None for %s argument", path->function_name ? path->function_name : "", path->function_name ? ": " : "", path->argument_name ? path->argument_name : "path");

            return 0;
        }
        path->wide = ((void *)0);
        path->narrow = ((void *)0);
        path->length = 0;
        path->object = o;
        path->fd = -1;
        return 1;
    }

    unicode = PyUnicode_FromObject(o);
    if (unicode) {
# 762 "posixmodule.c"
        int converted = PyUnicode_FSConverter(unicode, &bytes);
        do { if ( --((PyObject*)(unicode))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(unicode)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(unicode)))); } while (0);
        if (!converted)
            bytes = ((void *)0);

    }
    else {
        PyErr_Clear();
        if ((((o)->ob_type->tp_as_buffer != ((void *)0)) && ((o)->ob_type->tp_as_buffer->bf_getbuffer != ((void *)0))))
            bytes = PyBytes_FromObject(o);
        else
            bytes = ((void *)0);
        if (!bytes) {
            PyErr_Clear();
            if (path->allow_fd) {
                int fd;
                int result = _fd_converter(o, &fd,
                        "string, bytes or integer");
                if (result) {
                    path->wide = ((void *)0);
                    path->narrow = ((void *)0);
                    path->length = 0;
                    path->object = o;
                    path->fd = fd;
                    return result;
                }
            }
        }
    }

    if (!bytes) {
        if (!PyErr_Occurred())
            PyErr_Format(PyExc_TypeError, "%s%s" "illegal type for %s parameter", path->function_name ? path->function_name : "", path->function_name ? ": " : "", path->argument_name ? path->argument_name : "path");
        return 0;
    }
# 805 "posixmodule.c"
    length = ((__builtin_expect(!(((((((PyObject*)(bytes))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "posixmodule.c", 805, "PyBytes_Check(bytes)") : (void)0),(((PyVarObject*)(bytes))->ob_size));
# 814 "posixmodule.c"
    narrow = ((__builtin_expect(!(((((((PyObject*)(bytes))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "posixmodule.c", 814, "PyBytes_Check(bytes)") : (void)0), (((PyBytesObject *)(bytes))->ob_sval));
    if (length != strlen(narrow)) {
        PyErr_Format(PyExc_ValueError, "%s%s" "embedded NUL character in %s", path->function_name ? path->function_name : "", path->function_name ? ": " : "", path->argument_name ? path->argument_name : "path");
        do { if ( --((PyObject*)(bytes))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(bytes)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(bytes)))); } while (0);
        return 0;
    }

    path->wide = ((void *)0);
    path->narrow = narrow;
    path->length = length;
    path->object = o;
    path->fd = -1;
    path->cleanup = bytes;
    return 0x20000;
}

static void
argument_unavailable_error(char *function_name, char *argument_name) {
    PyErr_Format(PyExc_NotImplementedError,
        "%s%s%s unavailable on this platform",
        (function_name != ((void *)0)) ? function_name : "",
        (function_name != ((void *)0)) ? ": ": "",
        argument_name);
}

static int
dir_fd_unavailable(PyObject *o, void *p)
{
    int dir_fd;
    if (!dir_fd_converter(o, &dir_fd))
        return 0;
    if (dir_fd != (-100)) {
        argument_unavailable_error(((void *)0), "dir_fd");
        return 0;
    }
    *(int *)p = dir_fd;
    return 1;
}

static int
fd_specified(char *function_name, int fd) {
    if (fd == -1)
        return 0;

    argument_unavailable_error(function_name, "fd");
    return 1;
}

static int
follow_symlinks_specified(char *function_name, int follow_symlinks) {
    if (follow_symlinks)
        return 0;

    argument_unavailable_error(function_name, "follow_symlinks");
    return 1;
}

static int
path_and_dir_fd_invalid(char *function_name, path_t *path, int dir_fd) {
    if (!path->narrow && !path->wide && (dir_fd != (-100))) {
        PyErr_Format(PyExc_ValueError,
                     "%s: can't specify dir_fd without matching path",
                     function_name);
        return 1;
    }
    return 0;
}

static int
dir_fd_and_fd_invalid(char *function_name, int dir_fd, int fd) {
    if ((dir_fd != (-100)) && (fd != -1)) {
        PyErr_Format(PyExc_ValueError,
                     "%s: can't specify both dir_fd and fd",
                     function_name);
        return 1;
    }
    return 0;
}

static int
fd_and_follow_symlinks_invalid(char *function_name, int fd,
                               int follow_symlinks) {
    if ((fd > 0) && (!follow_symlinks)) {
        PyErr_Format(PyExc_ValueError,
                     "%s: cannot use fd and follow_symlinks together",
                     function_name);
        return 1;
    }
    return 0;
}

static int
dir_fd_and_follow_symlinks_invalid(char *function_name, int dir_fd,
                                   int follow_symlinks) {
    if ((dir_fd != (-100)) && (!follow_symlinks)) {
        PyErr_Format(PyExc_ValueError,
                     "%s: cannot use dir_fd and follow_symlinks together",
                     function_name);
        return 1;
    }
    return 0;
}



static int
_parse_off_t(PyObject* arg, void* addr)
{

    *((off_t*)addr) = PyLong_AsLong(arg);



    if (PyErr_Occurred())
        return 0;
    return 1;
}
# 1096 "posixmodule.c"
extern char **environ;


static PyObject *
convertenviron(void)
{
    PyObject *d;



    char **e;






    d = PyDict_New();
    if (d == ((void *)0))
        return ((void *)0);
# 1152 "posixmodule.c"
    if (environ == ((void *)0))
        return d;

    for (e = environ; *e != ((void *)0); e++) {
        PyObject *k;
        PyObject *v;
        char *p = strchr(*e, '=');
        if (p == ((void *)0))
            continue;
        k = PyBytes_FromStringAndSize(*e, (int)(p-*e));
        if (k == ((void *)0)) {
            PyErr_Clear();
            continue;
        }
        v = PyBytes_FromStringAndSize(p+1, strlen(p+1));
        if (v == ((void *)0)) {
            PyErr_Clear();
            do { if ( --((PyObject*)(k))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(k)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(k)))); } while (0);
            continue;
        }
        if (PyDict_GetItem(d, k) == ((void *)0)) {
            if (PyDict_SetItem(d, k, v) != 0)
                PyErr_Clear();
        }
        do { if ( --((PyObject*)(k))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(k)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(k)))); } while (0);
        do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
    }
# 1194 "posixmodule.c"
    return d;
}



static PyObject *
posix_error(void)
{
    return PyErr_SetFromErrno(PyExc_OSError);
}
static PyObject *
posix_error_with_filename(char* name)
{
    return PyErr_SetFromErrnoWithFilename(PyExc_OSError, name);
}


static PyObject *
posix_error_with_allocated_filename(PyObject* name)
{
    PyObject *name_str, *rc;
    name_str = PyUnicode_DecodeFSDefaultAndSize(PyBytes_AsString(name),
                                                ((__builtin_expect(!(((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "posixmodule.c", 1216, "PyBytes_Check(name)") : (void)0),(((PyVarObject*)(name))->ob_size)));
    do { if ( --((PyObject*)(name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(name)))); } while (0);
    rc = PyErr_SetFromErrnoWithFilenameObject(PyExc_OSError,
                                              name_str);
    do { if ((name_str) == ((void *)0)) ; else do { if ( --((PyObject*)(name_str))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(name_str)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(name_str)))); } while (0); } while (0);
    return rc;
}
# 1271 "posixmodule.c"
static PyObject *
path_posix_error(char *function_name, path_t *path)
{
    if (path->narrow)
        return posix_error_with_filename(path->narrow);
    return posix_error();
}

static PyObject *
path_error(char *function_name, path_t *path)
{







    return path_posix_error(function_name, path);

}
# 1372 "posixmodule.c"
static PyObject *
posix_fildes(PyObject *fdobj, int (*func)(int))
{
    int fd;
    int res;
    fd = PyObject_AsFileDescriptor(fdobj);
    if (fd < 0)
        return ((void *)0);
    if (!(1))
        return posix_error();
    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = (*func)(fd);
    PyEval_RestoreThread(_save); }
    if (res < 0)
        return posix_error();
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static PyObject *
posix_1str(PyObject *args, char *format, int (*func)(const char*))
{
    PyObject *opath1 = ((void *)0);
    char *path1;
    int res;
    if (!_PyArg_ParseTuple_SizeT(args, format,
                          PyUnicode_FSConverter, &opath1))
        return ((void *)0);
    path1 = PyBytes_AsString(opath1);
    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = (*func)(path1);
    PyEval_RestoreThread(_save); }
    if (res < 0)
        return posix_error_with_allocated_filename(opath1);
    do { if ( --((PyObject*)(opath1))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(opath1)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(opath1)))); } while (0);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}
# 2020 "posixmodule.c"
static char stat_result__doc__[] = "stat_result: Result from stat, fstat, or lstat.\n\nThis object may be accessed either as a tuple of\n  (mode, ino, dev, nlink, uid, gid, size, atime, mtime, ctime)\nor via the attributes st_mode, st_ino, st_dev, st_nlink, st_uid, and so on.\n\nPosix/windows: If your platform supports st_blksize, st_blocks, st_rdev,\nor st_flags, they are available as attributes only.\n\nSee os.stat for more information.";
# 2031 "posixmodule.c"
static PyStructSequence_Field stat_result_fields[] = {
    {"st_mode", "protection bits"},
    {"st_ino", "inode"},
    {"st_dev", "device"},
    {"st_nlink", "number of hard links"},
    {"st_uid", "user ID of owner"},
    {"st_gid", "group ID of owner"},
    {"st_size", "total size, in bytes"},

    {((void *)0), "integer time of last access"},
    {((void *)0), "integer time of last modification"},
    {((void *)0), "integer time of last change"},
    {"st_atime", "time of last access"},
    {"st_mtime", "time of last modification"},
    {"st_ctime", "time of last change"},
    {"st_atime_ns", "time of last access in nanoseconds"},
    {"st_mtime_ns", "time of last modification in nanoseconds"},
    {"st_ctime_ns", "time of last change in nanoseconds"},

    {"st_blksize", "blocksize for filesystem I/O"},


    {"st_blocks", "number of blocks allocated"},


    {"st_rdev", "device type (if inode device)"},


    {"st_flags", "user defined flags for file"},


    {"st_gen", "generation number"},


    {"st_birthtime", "time of creation"},

    {0}
};
# 2106 "posixmodule.c"
static PyStructSequence_Desc stat_result_desc = {
    "stat_result",
    stat_result__doc__,
    stat_result_fields,
    10
};

static char statvfs_result__doc__[] = "statvfs_result: Result from statvfs or fstatvfs.\n\nThis object may be accessed either as a tuple of\n  (bsize, frsize, blocks, bfree, bavail, files, ffree, favail, flag, namemax),\nor via the attributes f_bsize, f_frsize, f_blocks, f_bfree, and so on.\n\nSee os.statvfs for more information.";







static PyStructSequence_Field statvfs_result_fields[] = {
    {"f_bsize", },
    {"f_frsize", },
    {"f_blocks", },
    {"f_bfree", },
    {"f_bavail", },
    {"f_files", },
    {"f_ffree", },
    {"f_favail", },
    {"f_flag", },
    {"f_namemax",},
    {0}
};

static PyStructSequence_Desc statvfs_result_desc = {
    "statvfs_result",
    statvfs_result__doc__,
    statvfs_result_fields,
    10
};
# 2169 "posixmodule.c"
static int initialized;
static PyTypeObject StatResultType;
static PyTypeObject StatVFSResultType;



static newfunc structseq_new;

static PyObject *
statresult_new(PyTypeObject *type, PyObject *args, PyObject *kwds)
{
    PyStructSequence *result;
    int i;

    result = (PyStructSequence*)structseq_new(type, args, kwds);
    if (!result)
        return ((void *)0);



    for (i = 7; i <= 9; i++) {
        if (result->ob_item[i+3] == (&_Py_NoneStruct)) {
            do { if ( --((PyObject*)((&_Py_NoneStruct)))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)((&_Py_NoneStruct))))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)((&_Py_NoneStruct))))); } while (0);
            ( ((PyObject*)(result->ob_item[i]))->ob_refcnt++);
            result->ob_item[i+3] = result->ob_item[i];
        }
    }
    return (PyObject*)result;
}




static int _stat_float_times = 1;

static char stat_float_times__doc__[] = "stat_float_times([newval]) -> oldval\n\nDetermine whether os.[lf]stat represents time stamps as float objects.\nIf newval is True, future calls to stat() return floats, if it is False,\nfuture calls return ints. \nIf newval is omitted, return the current setting.\n";






static PyObject*
stat_float_times(PyObject* self, PyObject *args)
{
    int newval = -1;
    if (!_PyArg_ParseTuple_SizeT(args, "|i:stat_float_times", &newval))
        return ((void *)0);
    if (PyErr_WarnEx(PyExc_DeprecationWarning,
                     "stat_float_times() is deprecated",
                     1))
        return ((void *)0);
    if (newval == -1)

        return PyBool_FromLong(_stat_float_times);
    _stat_float_times = newval;
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static PyObject *billion = ((void *)0);

static void
fill_time(PyObject *v, int index, time_t sec, unsigned long nsec)
{
    PyObject *s = _PyLong_FromTime_t(sec);
    PyObject *ns_fractional = PyLong_FromUnsignedLong(nsec);
    PyObject *s_in_ns = ((void *)0);
    PyObject *ns_total = ((void *)0);
    PyObject *float_s = ((void *)0);

    if (!(s && ns_fractional))
        goto exit;

    s_in_ns = PyNumber_Multiply(s, billion);
    if (!s_in_ns)
        goto exit;

    ns_total = PyNumber_Add(s_in_ns, ns_fractional);
    if (!ns_total)
        goto exit;

    if (_stat_float_times) {
        float_s = PyFloat_FromDouble(sec + 1e-9*nsec);
        if (!float_s)
            goto exit;
    }
    else {
        float_s = s;
        ( ((PyObject*)(float_s))->ob_refcnt++);
    }

    (((PyTupleObject *)(v))->ob_item[index] = s);
    (((PyTupleObject *)(v))->ob_item[index+3] = float_s);
    (((PyTupleObject *)(v))->ob_item[index+6] = ns_total);
    s = ((void *)0);
    float_s = ((void *)0);
    ns_total = ((void *)0);
exit:
    do { if ((s) == ((void *)0)) ; else do { if ( --((PyObject*)(s))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(s)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(s)))); } while (0); } while (0);
    do { if ((ns_fractional) == ((void *)0)) ; else do { if ( --((PyObject*)(ns_fractional))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(ns_fractional)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(ns_fractional)))); } while (0); } while (0);
    do { if ((s_in_ns) == ((void *)0)) ; else do { if ( --((PyObject*)(s_in_ns))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(s_in_ns)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(s_in_ns)))); } while (0); } while (0);
    do { if ((ns_total) == ((void *)0)) ; else do { if ( --((PyObject*)(ns_total))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(ns_total)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(ns_total)))); } while (0); } while (0);
    do { if ((float_s) == ((void *)0)) ; else do { if ( --((PyObject*)(float_s))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(float_s)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(float_s)))); } while (0); } while (0);
}



static PyObject*
_pystat_fromstructstat(struct stat *st)
{
    unsigned long ansec, mnsec, cnsec;
    PyObject *v = PyStructSequence_New(&StatResultType);
    if (v == ((void *)0))
        return ((void *)0);

    (((PyTupleObject *)(v))->ob_item[0] = PyLong_FromLong((long)st->st_mode));




    (((PyTupleObject *)(v))->ob_item[1] = PyLong_FromLong((long)st->st_ino));


    (((PyTupleObject *)(v))->ob_item[2] = PyLong_FromLongLong((long long)st->st_dev));




    (((PyTupleObject *)(v))->ob_item[3] = PyLong_FromLong((long)st->st_nlink));




    (((PyTupleObject *)(v))->ob_item[4] = _PyLong_FromUid(st->st_uid));
    (((PyTupleObject *)(v))->ob_item[5] = _PyLong_FromGid(st->st_gid));





    (((PyTupleObject *)(v))->ob_item[6] = PyLong_FromLong(st->st_size));







    ansec = st->st_atimespec.tv_nsec;
    mnsec = st->st_mtimespec.tv_nsec;
    cnsec = st->st_ctimespec.tv_nsec;







    fill_time(v, 7, st->st_atimespec.tv_sec, ansec);
    fill_time(v, 8, st->st_mtimespec.tv_sec, mnsec);
    fill_time(v, 9, st->st_ctimespec.tv_sec, cnsec);


    (((PyTupleObject *)(v))->ob_item[16] = PyLong_FromLong((long)st->st_blksize));



    (((PyTupleObject *)(v))->ob_item[(16 +1)] = PyLong_FromLong((long)st->st_blocks));



    (((PyTupleObject *)(v))->ob_item[((16 +1)+1)] = PyLong_FromLong((long)st->st_rdev));



    (((PyTupleObject *)(v))->ob_item[((((16 +1)+1)+1)+1)] = PyLong_FromLong((long)st->st_gen));



    {
      PyObject *val;
      unsigned long bsec,bnsec;
      bsec = (long)st->st_birthtimespec.tv_sec;

      bnsec = st->st_birthtimespec.tv_nsec;



      if (_stat_float_times) {
        val = PyFloat_FromDouble(bsec + 1e-9*bnsec);
      } else {
        val = PyLong_FromLong((long)bsec);
      }
      (((PyTupleObject *)(v))->ob_item[(((((16 +1)+1)+1)+1)+1)] = val);

    }


    (((PyTupleObject *)(v))->ob_item[(((16 +1)+1)+1)] = PyLong_FromLong((long)st->st_flags));



    if (PyErr_Occurred()) {
        do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
        return ((void *)0);
    }

    return v;
}




static PyObject *
posix_do_stat(char *function_name, path_t *path,
              int dir_fd, int follow_symlinks)
{
    struct stat st;
    int result;






    if (path_and_dir_fd_invalid("stat", path, dir_fd) ||
        dir_fd_and_fd_invalid("stat", dir_fd, path->fd) ||
        fd_and_follow_symlinks_invalid("stat", path->fd, follow_symlinks))
        return ((void *)0);

    { PyThreadState *_save; _save = PyEval_SaveThread();
    if (path->fd != -1)
        result = fstat(path->fd, &st);
    else
# 2414 "posixmodule.c"
    if ((!follow_symlinks) && (dir_fd == (-100)))
        result = lstat(path->narrow, &st);
    else







        result = stat(path->narrow, &st);
    PyEval_RestoreThread(_save); }

    if (result != 0)
        return path_error("stat", path);

    return _pystat_fromstructstat(&st);
}

static char posix_stat__doc__[] = "stat(path, *, dir_fd=None, follow_symlinks=True) -> stat result\n\nPerform a stat system call on the given path.\n\npath may be specified as either a string or as an open file descriptor.\n\nIf dir_fd is not None, it should be a file descriptor open to a directory,\n  and path should be relative; path will then be relative to that directory.\n  dir_fd may not be supported on your platform; if it is unavailable, using\n  it will raise a NotImplementedError.\nIf follow_symlinks is False, and the last element of the path is a symbolic\n  link, stat will examine the symbolic link itself instead of the file the\n  link points to.\nIt is an error to use dir_fd or follow_symlinks when specifying path as\n  an open file descriptor.";
# 2449 "posixmodule.c"
static PyObject *
posix_stat(PyObject *self, PyObject *args, PyObject *kwargs)
{
    static char *keywords[] = {"path", "dir_fd", "follow_symlinks", ((void *)0)};
    path_t path;
    int dir_fd = (-100);
    int follow_symlinks = 1;
    PyObject *return_value;

    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));
    path.allow_fd = 1;
    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&|$O&p:stat", keywords,
        path_converter, &path,



        dir_fd_unavailable, &dir_fd,

        &follow_symlinks))
        return ((void *)0);
    return_value = posix_do_stat("stat", &path, dir_fd, follow_symlinks);
    path_cleanup(&path);
    return return_value;
}

static char posix_lstat__doc__[] = "lstat(path, *, dir_fd=None) -> stat result\n\nLike stat(), but do not follow symbolic links.\nEquivalent to stat(path, follow_symlinks=False).";




static PyObject *
posix_lstat(PyObject *self, PyObject *args, PyObject *kwargs)
{
    static char *keywords[] = {"path", "dir_fd", ((void *)0)};
    path_t path;
    int dir_fd = (-100);
    int follow_symlinks = 0;
    PyObject *return_value;

    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));
    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&|$O&:lstat", keywords,
        path_converter, &path,



        dir_fd_unavailable, &dir_fd

        ))
        return ((void *)0);
    return_value = posix_do_stat("stat", &path, dir_fd, follow_symlinks);
    path_cleanup(&path);
    return return_value;
}

static char posix_access__doc__[] = "access(path, mode, *, dir_fd=None, effective_ids=False, follow_symlinks=True)\n\nUse the real uid/gid to test for access to a path.  Returns True if granted,\nFalse otherwise.\n\nIf dir_fd is not None, it should be a file descriptor open to a directory,\n  and path should be relative; path will then be relative to that directory.\nIf effective_ids is True, access will use the effective uid/gid instead of\n  the real uid/gid.\nIf follow_symlinks is False, and the last element of the path is a symbolic\n  link, access will examine the symbolic link itself instead of the file the\n  link points to.\ndir_fd, effective_ids, and follow_symlinks may not be implemented\n  on your platform.  If they are unavailable, using them will raise a\n  NotImplementedError.\n\nNote that most operations will use the effective uid/gid, therefore this\n  routine can be used in a suid/sgid environment to test if the invoking user\n  has the specified access to the path.\nThe mode argument can be F_OK to test existence, or the inclusive-OR\n  of R_OK, W_OK, and X_OK.";
# 2526 "posixmodule.c"
static PyObject *
posix_access(PyObject *self, PyObject *args, PyObject *kwargs)
{
    static char *keywords[] = {"path", "mode", "dir_fd", "effective_ids",
                                "follow_symlinks", ((void *)0)};
    path_t path;
    int mode;
    int dir_fd = (-100);
    int effective_ids = 0;
    int follow_symlinks = 1;
    PyObject *return_value = ((void *)0);




    int result;


    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));
    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&i|$O&pp:access", keywords,
        path_converter, &path, &mode,



        dir_fd_unavailable, &dir_fd,

        &effective_ids, &follow_symlinks))
        return ((void *)0);


    if (follow_symlinks_specified("access", follow_symlinks))
        goto exit;

    if (effective_ids) {
        argument_unavailable_error("access", "effective_ids");
        goto exit;
    }
# 2588 "posixmodule.c"
    { PyThreadState *_save; _save = PyEval_SaveThread();
# 2602 "posixmodule.c"
        result = access(path.narrow, mode);
    PyEval_RestoreThread(_save); }
    return_value = PyBool_FromLong(!result);



exit:

    path_cleanup(&path);
    return return_value;
}
# 2628 "posixmodule.c"
static char posix_ttyname__doc__[] = "ttyname(fd) -> string\n\nReturn the name of the terminal device connected to 'fd'.";



static PyObject *
posix_ttyname(PyObject *self, PyObject *args)
{
    int id;
    char *ret;

    if (!_PyArg_ParseTuple_SizeT(args, "i:ttyname", &id))
        return ((void *)0);
# 2650 "posixmodule.c"
    ret = ttyname(id);

    if (ret == ((void *)0))
        return posix_error();
    return PyUnicode_DecodeFSDefault(ret);
}



static char posix_ctermid__doc__[] = "ctermid() -> string\n\nReturn the name of the controlling terminal for this process.";



static PyObject *
posix_ctermid(PyObject *self, PyObject *noargs)
{
    char *ret;
    char buffer[1024];


    ret = ctermid_r(buffer);



    if (ret == ((void *)0))
        return posix_error();
    return PyUnicode_DecodeFSDefault(buffer);
}


static char posix_chdir__doc__[] = "chdir(path)\n\nChange the current working directory to the specified path.\n\npath may always be specified as a string.\nOn some platforms, path may also be specified as an open file descriptor.\n  If this functionality is unavailable, using it raises an exception.";







static PyObject *
posix_chdir(PyObject *self, PyObject *args, PyObject *kwargs)
{
    path_t path;
    int result;
    PyObject *return_value = ((void *)0);
    static char *keywords[] = {"path", ((void *)0)};

    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));

    path.allow_fd = 1;

    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&:chdir", keywords,
        path_converter, &path
        ))
        return ((void *)0);

    { PyThreadState *_save; _save = PyEval_SaveThread();
# 2716 "posixmodule.c"
    if (path.fd != -1)
        result = fchdir(path.fd);
    else

        result = chdir(path.narrow);

    PyEval_RestoreThread(_save); }

    if (result) {
        return_value = path_error("chdir", &path);
        goto exit;
    }

    return_value = (&_Py_NoneStruct);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);

exit:
    path_cleanup(&path);
    return return_value;
}


static char posix_fchdir__doc__[] = "fchdir(fd)\n\nChange to the directory of the given file descriptor.  fd must be\nopened on a directory, not a file.  Equivalent to os.chdir(fd).";




static PyObject *
posix_fchdir(PyObject *self, PyObject *fdobj)
{
    return posix_fildes(fdobj, fchdir);
}



static char posix_chmod__doc__[] = "chmod(path, mode, *, dir_fd=None, follow_symlinks=True)\n\nChange the access permissions of a file.\n\npath may always be specified as a string.\nOn some platforms, path may also be specified as an open file descriptor.\n  If this functionality is unavailable, using it raises an exception.\nIf dir_fd is not None, it should be a file descriptor open to a directory,\n  and path should be relative; path will then be relative to that directory.\nIf follow_symlinks is False, and the last element of the path is a symbolic\n  link, chmod will modify the symbolic link itself instead of the file the\n  link points to.\nIt is an error to use dir_fd or follow_symlinks when specifying path as\n  an open file descriptor.\ndir_fd and follow_symlinks may not be implemented on your platform.\n  If they are unavailable, using them will raise a NotImplementedError.";
# 2768 "posixmodule.c"
static PyObject *
posix_chmod(PyObject *self, PyObject *args, PyObject *kwargs)
{
    path_t path;
    int mode;
    int dir_fd = (-100);
    int follow_symlinks = 1;
    int result;
    PyObject *return_value = ((void *)0);
    static char *keywords[] = {"path", "mode", "dir_fd",
                               "follow_symlinks", ((void *)0)};
# 2788 "posixmodule.c"
    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));

    path.allow_fd = 1;

    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&i|$O&p:chmod", keywords,
        path_converter, &path,
        &mode,



        dir_fd_unavailable, &dir_fd,

        &follow_symlinks))
        return ((void *)0);
# 2833 "posixmodule.c"
    { PyThreadState *_save; _save = PyEval_SaveThread();

    if (path.fd != -1)
        result = fchmod(path.fd, mode);
    else


    if ((!follow_symlinks) && (dir_fd == (-100)))
        result = lchmod(path.narrow, mode);
    else
# 2869 "posixmodule.c"
        result = chmod(path.narrow, mode);
    PyEval_RestoreThread(_save); }

    if (result) {
# 2883 "posixmodule.c"
            return_value = path_error("chmod", &path);
        goto exit;
    }


    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return_value = (&_Py_NoneStruct);
exit:
    path_cleanup(&path);
    return return_value;
}



static char posix_fchmod__doc__[] = "fchmod(fd, mode)\n\nChange the access permissions of the file given by file\ndescriptor fd.  Equivalent to os.chmod(fd, mode).";




static PyObject *
posix_fchmod(PyObject *self, PyObject *args)
{
    int fd, mode, res;
    if (!_PyArg_ParseTuple_SizeT(args, "ii:fchmod", &fd, &mode))
        return ((void *)0);
    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = fchmod(fd, mode);
    PyEval_RestoreThread(_save); }
    if (res < 0)
        return posix_error();
    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}



static char posix_lchmod__doc__[] = "lchmod(path, mode)\n\nChange the access permissions of a file. If path is a symlink, this\naffects the link itself rather than the target.\nEquivalent to chmod(path, mode, follow_symlinks=False).";





static PyObject *
posix_lchmod(PyObject *self, PyObject *args)
{
    PyObject *opath;
    char *path;
    int i;
    int res;
    if (!_PyArg_ParseTuple_SizeT(args, "O&i:lchmod", PyUnicode_FSConverter,
                          &opath, &i))
        return ((void *)0);
    path = PyBytes_AsString(opath);
    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = lchmod(path, i);
    PyEval_RestoreThread(_save); }
    if (res < 0)
        return posix_error_with_allocated_filename(opath);
    do { if ( --((PyObject*)(opath))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(opath)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(opath)))); } while (0);
    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}




static char posix_chflags__doc__[] = "chflags(path, flags, *, follow_symlinks=True)\n\nSet file flags.\n\nIf follow_symlinks is False, and the last element of the path is a symbolic\n  link, chflags will change flags on the symbolic link itself instead of the\n  file the link points to.\nfollow_symlinks may not be implemented on your platform.  If it is\nunavailable, using it will raise a NotImplementedError.";
# 2957 "posixmodule.c"
static PyObject *
posix_chflags(PyObject *self, PyObject *args, PyObject *kwargs)
{
    path_t path;
    unsigned long flags;
    int follow_symlinks = 1;
    int result;
    PyObject *return_value;
    static char *keywords[] = {"path", "flags", "follow_symlinks", ((void *)0)};

    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));
    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&k|$i:chflags", keywords,
                          path_converter, &path,
                          &flags, &follow_symlinks))
        return ((void *)0);






    { PyThreadState *_save; _save = PyEval_SaveThread();

    if (!follow_symlinks)
        result = lchflags(path.narrow, flags);
    else

        result = chflags(path.narrow, flags);
    PyEval_RestoreThread(_save); }

    if (result) {
        return_value = path_posix_error("chflags", &path);
        goto exit;
    }

    return_value = (&_Py_NoneStruct);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);

exit:
    path_cleanup(&path);
    return return_value;
}



static char posix_lchflags__doc__[] = "lchflags(path, flags)\n\nSet file flags.\nThis function will not follow symbolic links.\nEquivalent to chflags(path, flags, follow_symlinks=False).";





static PyObject *
posix_lchflags(PyObject *self, PyObject *args)
{
    PyObject *opath;
    char *path;
    unsigned long flags;
    int res;
    if (!_PyArg_ParseTuple_SizeT(args, "O&k:lchflags",
                          PyUnicode_FSConverter, &opath, &flags))
        return ((void *)0);
    path = PyBytes_AsString(opath);
    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = lchflags(path, flags);
    PyEval_RestoreThread(_save); }
    if (res < 0)
        return posix_error_with_allocated_filename(opath);
    do { if ( --((PyObject*)(opath))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(opath)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(opath)))); } while (0);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}



static char posix_chroot__doc__[] = "chroot(path)\n\nChange root directory to path.";



static PyObject *
posix_chroot(PyObject *self, PyObject *args)
{
    return posix_1str(args, "O&:chroot", chroot);
}



static char posix_fsync__doc__[] = "fsync(fildes)\n\nforce write of file with filedescriptor to disk.";



static PyObject *
posix_fsync(PyObject *self, PyObject *fdobj)
{
    return posix_fildes(fdobj, fsync);
}



static char posix_sync__doc__[] = "sync()\n\nForce write of everything to disk.";



static PyObject *
posix_sync(PyObject *self, PyObject *noargs)
{
    { PyThreadState *_save; _save = PyEval_SaveThread();
    sync();
    PyEval_RestoreThread(_save); }
    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}
# 3089 "posixmodule.c"
static char posix_chown__doc__[] = "chown(path, uid, gid, *, dir_fd=None, follow_symlinks=True)\n\nChange the owner and group id of path to the numeric uid and gid.\n\npath may always be specified as a string.\nOn some platforms, path may also be specified as an open file descriptor.\n  If this functionality is unavailable, using it raises an exception.\nIf dir_fd is not None, it should be a file descriptor open to a directory,\n  and path should be relative; path will then be relative to that directory.\nIf follow_symlinks is False, and the last element of the path is a symbolic\n  link, chown will modify the symbolic link itself instead of the file the\n  link points to.\nIt is an error to use dir_fd or follow_symlinks when specifying path as\n  an open file descriptor.\ndir_fd and follow_symlinks may not be implemented on your platform.\n  If they are unavailable, using them will raise a NotImplementedError.";
# 3106 "posixmodule.c"
static PyObject *
posix_chown(PyObject *self, PyObject *args, PyObject *kwargs)
{
    path_t path;
    uid_t uid;
    gid_t gid;
    int dir_fd = (-100);
    int follow_symlinks = 1;
    int result;
    PyObject *return_value = ((void *)0);
    static char *keywords[] = {"path", "uid", "gid", "dir_fd",
                               "follow_symlinks", ((void *)0)};

    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));

    path.allow_fd = 1;

    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&O&O&|$O&p:chown", keywords,
                                     path_converter, &path,
                                     _Py_Uid_Converter, &uid,
                                     _Py_Gid_Converter, &gid,



                                     dir_fd_unavailable, &dir_fd,

                                     &follow_symlinks))
        return ((void *)0);





    if (dir_fd_and_fd_invalid("chown", dir_fd, path.fd) ||
        fd_and_follow_symlinks_invalid("chown", path.fd, follow_symlinks))
        goto exit;
# 3150 "posixmodule.c"
    if ((!follow_symlinks) && (lchown == ((void *)0))) {
        follow_symlinks_specified("chown", follow_symlinks);
        goto exit;
    }


    { PyThreadState *_save; _save = PyEval_SaveThread();

    if (path.fd != -1)
        result = fchown(path.fd, uid, gid);
    else


    if ((!follow_symlinks) && (dir_fd == (-100)))
        result = lchown(path.narrow, uid, gid);
    else







        result = chown(path.narrow, uid, gid);
    PyEval_RestoreThread(_save); }

    if (result) {
        return_value = path_posix_error("chown", &path);
        goto exit;
    }

    return_value = (&_Py_NoneStruct);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);

exit:
    path_cleanup(&path);
    return return_value;
}



static char posix_fchown__doc__[] = "fchown(fd, uid, gid)\n\nChange the owner and group id of the file given by file descriptor\nfd to the numeric uid and gid.  Equivalent to os.chown(fd, uid, gid).";




static PyObject *
posix_fchown(PyObject *self, PyObject *args)
{
    int fd;
    uid_t uid;
    gid_t gid;
    int res;
    if (!_PyArg_ParseTuple_SizeT(args, "iO&O&:fchown", &fd,
                          _Py_Uid_Converter, &uid,
                          _Py_Gid_Converter, &gid))
        return ((void *)0);
    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = fchown(fd, uid, gid);
    PyEval_RestoreThread(_save); }
    if (res < 0)
        return posix_error();
    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}



static char posix_lchown__doc__[] = "lchown(path, uid, gid)\n\nChange the owner and group id of path to the numeric uid and gid.\nThis function will not follow symbolic links.\nEquivalent to os.chown(path, uid, gid, follow_symlinks=False).";





static PyObject *
posix_lchown(PyObject *self, PyObject *args)
{
    PyObject *opath;
    char *path;
    uid_t uid;
    gid_t gid;
    int res;
    if (!_PyArg_ParseTuple_SizeT(args, "O&O&O&:lchown",
                          PyUnicode_FSConverter, &opath,
                          _Py_Uid_Converter, &uid,
                          _Py_Gid_Converter, &gid))
        return ((void *)0);
    path = PyBytes_AsString(opath);
    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = lchown(path, uid, gid);
    PyEval_RestoreThread(_save); }
    if (res < 0)
        return posix_error_with_allocated_filename(opath);
    do { if ( --((PyObject*)(opath))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(opath)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(opath)))); } while (0);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}




static PyObject *
posix_getcwd(int use_bytes)
{
    char buf[1026];
    char *res;
# 3290 "posixmodule.c"
    { PyThreadState *_save; _save = PyEval_SaveThread();



    res = getcwd(buf, sizeof buf);

    PyEval_RestoreThread(_save); }
    if (res == ((void *)0))
        return posix_error();
    if (use_bytes)
        return PyBytes_FromStringAndSize(buf, strlen(buf));
    return PyUnicode_DecodeFSDefault(buf);
}

static char posix_getcwd__doc__[] = "getcwd() -> path\n\nReturn a unicode string representing the current working directory.";



static PyObject *
posix_getcwd_unicode(PyObject *self)
{
    return posix_getcwd(0);
}

static char posix_getcwdb__doc__[] = "getcwdb() -> path\n\nReturn a bytes string representing the current working directory.";



static PyObject *
posix_getcwd_bytes(PyObject *self)
{
    return posix_getcwd(1);
}







static char posix_link__doc__[] = "link(src, dst, *, src_dir_fd=None, dst_dir_fd=None, follow_symlinks=True)\n\nCreate a hard link to a file.\n\nIf either src_dir_fd or dst_dir_fd is not None, it should be a file\n  descriptor open to a directory, and the respective path string (src or dst)\n  should be relative; the path will then be relative to that directory.\nIf follow_symlinks is False, and the last element of src is a symbolic\n  link, link will create a link to the symbolic link itself instead of the\n  file the link points to.\nsrc_dir_fd, dst_dir_fd, and follow_symlinks may not be implemented on your\n  platform.  If they are unavailable, using them will raise a\n  NotImplementedError.";
# 3344 "posixmodule.c"
static PyObject *
posix_link(PyObject *self, PyObject *args, PyObject *kwargs)
{
    path_t src, dst;
    int src_dir_fd = (-100);
    int dst_dir_fd = (-100);
    int follow_symlinks = 1;
    PyObject *return_value = ((void *)0);
    static char *keywords[] = {"src", "dst", "src_dir_fd", "dst_dir_fd",
                               "follow_symlinks", ((void *)0)};



    int result;


    ((__builtin_object_size (&src, 0) != (size_t) -1) ? __builtin___memset_chk (&src, 0, sizeof(src), __builtin_object_size (&src, 0)) : __inline_memset_chk (&src, 0, sizeof(src)));
    ((__builtin_object_size (&dst, 0) != (size_t) -1) ? __builtin___memset_chk (&dst, 0, sizeof(dst), __builtin_object_size (&dst, 0)) : __inline_memset_chk (&dst, 0, sizeof(dst)));
    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&O&|O&O&p:link", keywords,
            path_converter, &src,
            path_converter, &dst,
            dir_fd_converter, &src_dir_fd,
            dir_fd_converter, &dst_dir_fd,
            &follow_symlinks))
        return ((void *)0);


    if ((src_dir_fd != (-100)) || (dst_dir_fd != (-100))) {
        argument_unavailable_error("link", "src_dir_fd and dst_dir_fd");
        goto exit;
    }


    if ((src.narrow && dst.wide) || (src.wide && dst.narrow)) {
        PyErr_SetString(PyExc_NotImplementedError,
                        "link: src and dst must be the same type");
        goto exit;
    }
# 3396 "posixmodule.c"
    { PyThreadState *_save; _save = PyEval_SaveThread();
# 3406 "posixmodule.c"
        result = link(src.narrow, dst.narrow);
    PyEval_RestoreThread(_save); }

    if (result) {
        return_value = path_error("link", &dst);
        goto exit;
    }


    return_value = (&_Py_NoneStruct);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);

exit:
    path_cleanup(&src);
    path_cleanup(&dst);
    return return_value;
}




static char posix_listdir__doc__[] = "listdir(path='.') -> list_of_filenames\n\nReturn a list containing the names of the files in the directory.\nThe list is in arbitrary order.  It does not include the special\nentries '.' and '..' even if they are present in the directory.\n\npath can be specified as either str or bytes.  If path is bytes,\n  the filenames returned will also be bytes; in all other circumstances\n  the filenames returned will be str.\nOn some platforms, path may also be specified as an open file descriptor;\n  the file descriptor must refer to a directory.\n  If this functionality is unavailable, using it raises NotImplementedError.";
# 3440 "posixmodule.c"
static PyObject *
posix_listdir(PyObject *self, PyObject *args, PyObject *kwargs)
{
    path_t path;
    PyObject *list = ((void *)0);
    static char *keywords[] = {"path", ((void *)0)};
    int fd = -1;
# 3471 "posixmodule.c"
    PyObject *v;
    DIR *dirp = ((void *)0);
    struct dirent *ep;
    int return_str;


    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));
    path.nullable = 1;




    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "|O&:listdir", keywords,
        path_converter, &path
        ))
        return ((void *)0);
# 3695 "posixmodule.c"
    (*__error()) = 0;
# 3716 "posixmodule.c"
    {
        char *name;
        if (path.narrow) {
            name = path.narrow;

            return_str = !(((((((PyObject*)(path.object))->ob_type))->tp_flags & ((1L<<27))) != 0));
        }
        else {
            name = ".";
            return_str = 1;
        }

        { PyThreadState *_save; _save = PyEval_SaveThread();
        dirp = opendir(name);
        PyEval_RestoreThread(_save); }
    }

    if (dirp == ((void *)0)) {
        list = path_error("listdir", &path);
        goto exit;
    }
    if ((list = PyList_New(0)) == ((void *)0)) {
        goto exit;
    }
    for (;;) {
        (*__error()) = 0;
        { PyThreadState *_save; _save = PyEval_SaveThread();
        ep = readdir(dirp);
        PyEval_RestoreThread(_save); }
        if (ep == ((void *)0)) {
            if ((*__error()) == 0) {
                break;
            } else {
                do { if ( --((PyObject*)(list))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(list)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(list)))); } while (0);
                list = path_error("listdir", &path);
                goto exit;
            }
        }
        if (ep->d_name[0] == '.' &&
            (strlen((ep)->d_name) == 1 ||
             (ep->d_name[1] == '.' && strlen((ep)->d_name) == 2)))
            continue;
        if (return_str)
            v = PyUnicode_DecodeFSDefaultAndSize(ep->d_name, strlen((ep)->d_name));
        else
            v = PyBytes_FromStringAndSize(ep->d_name, strlen((ep)->d_name));
        if (v == ((void *)0)) {
            do { if (list) { PyObject *_py_tmp = (PyObject *)(list); (list) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
            break;
        }
        if (PyList_Append(list, v) != 0) {
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            do { if (list) { PyObject *_py_tmp = (PyObject *)(list); (list) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
            break;
        }
        do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
    }

exit:
    if (dirp != ((void *)0)) {
        { PyThreadState *_save; _save = PyEval_SaveThread();
        if (fd > -1)
            rewinddir(dirp);
        closedir(dirp);
        PyEval_RestoreThread(_save); }
    }

    path_cleanup(&path);

    return list;


}
# 3979 "posixmodule.c"
static char posix_mkdir__doc__[] = "mkdir(path, mode=0o777, *, dir_fd=None)\n\nCreate a directory.\n\nIf dir_fd is not None, it should be a file descriptor open to a directory,\n  and path should be relative; path will then be relative to that directory.\ndir_fd may not be implemented on your platform.\n  If it is unavailable, using it will raise a NotImplementedError.\n\nThe mode argument is ignored on Windows.";
# 3990 "posixmodule.c"
static PyObject *
posix_mkdir(PyObject *self, PyObject *args, PyObject *kwargs)
{
    path_t path;
    int mode = 0777;
    int dir_fd = (-100);
    static char *keywords[] = {"path", "mode", "dir_fd", ((void *)0)};
    PyObject *return_value = ((void *)0);
    int result;

    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));
    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&|i$O&:mkdir", keywords,
        path_converter, &path, &mode,



        dir_fd_unavailable, &dir_fd

        ))
        return ((void *)0);
# 4024 "posixmodule.c"
    { PyThreadState *_save; _save = PyEval_SaveThread();
# 4033 "posixmodule.c"
        result = mkdir(path.narrow, mode);

    PyEval_RestoreThread(_save); }
    if (result < 0) {
        return_value = path_error("mkdir", &path);
        goto exit;
    }

    return_value = (&_Py_NoneStruct);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
exit:
    path_cleanup(&path);
    return return_value;
}
# 4056 "posixmodule.c"
static char posix_nice__doc__[] = "nice(inc) -> new_priority\n\nDecrease the priority of process by inc and return the new priority.";



static PyObject *
posix_nice(PyObject *self, PyObject *args)
{
    int increment, value;

    if (!_PyArg_ParseTuple_SizeT(args, "i:nice", &increment))
        return ((void *)0);
# 4078 "posixmodule.c"
    (*__error()) = 0;
    value = nice(increment);




    if (value == -1 && (*__error()) != 0)

        return posix_error();
    return PyLong_FromLong((long) value);
}




static char posix_getpriority__doc__[] = "getpriority(which, who) -> current_priority\n\nGet program scheduling priority.";



static PyObject *
posix_getpriority(PyObject *self, PyObject *args)
{
    int which, who, retval;

    if (!_PyArg_ParseTuple_SizeT(args, "ii", &which, &who))
        return ((void *)0);
    (*__error()) = 0;
    retval = getpriority(which, who);
    if ((*__error()) != 0)
        return posix_error();
    return PyLong_FromLong((long)retval);
}




static char posix_setpriority__doc__[] = "setpriority(which, who, prio) -> None\n\nSet program scheduling priority.";



static PyObject *
posix_setpriority(PyObject *self, PyObject *args)
{
    int which, who, prio, retval;

    if (!_PyArg_ParseTuple_SizeT(args, "iii", &which, &who, &prio))
        return ((void *)0);
    retval = setpriority(which, who, prio);
    if (retval == -1)
        return posix_error();
    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}



static PyObject *
internal_rename(PyObject *args, PyObject *kwargs, int is_replace)
{
    char *function_name = is_replace ? "replace" : "rename";
    path_t src;
    path_t dst;
    int src_dir_fd = (-100);
    int dst_dir_fd = (-100);
    int dir_fd_specified;
    PyObject *return_value = ((void *)0);
    char format[24];
    static char *keywords[] = {"src", "dst", "src_dir_fd", "dst_dir_fd", ((void *)0)};





    int result;


    ((__builtin_object_size (&src, 0) != (size_t) -1) ? __builtin___memset_chk (&src, 0, sizeof(src), __builtin_object_size (&src, 0)) : __inline_memset_chk (&src, 0, sizeof(src)));
    ((__builtin_object_size (&dst, 0) != (size_t) -1) ? __builtin___memset_chk (&dst, 0, sizeof(dst), __builtin_object_size (&dst, 0)) : __inline_memset_chk (&dst, 0, sizeof(dst)));
    ((__builtin_object_size (format, 0) != (size_t) -1) ? __builtin___strcpy_chk (format, "O&O&|$O&O&:", __builtin_object_size (format, 2 > 1)) : __inline_strcpy_chk (format, "O&O&|$O&O&:"));
    ((__builtin_object_size (format, 0) != (size_t) -1) ? __builtin___strcat_chk (format, function_name, __builtin_object_size (format, 2 > 1)) : __inline_strcat_chk (format, function_name));
    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, format, keywords,
        path_converter, &src,
        path_converter, &dst,
        dir_fd_converter, &src_dir_fd,
        dir_fd_converter, &dst_dir_fd))
        return ((void *)0);

    dir_fd_specified = (src_dir_fd != (-100)) ||
                       (dst_dir_fd != (-100));

    if (dir_fd_specified) {
        argument_unavailable_error(function_name, "src_dir_fd and dst_dir_fd");
        goto exit;
    }


    if ((src.narrow && dst.wide) || (src.wide && dst.narrow)) {
        PyErr_Format(PyExc_ValueError,
                     "%s: src and dst must be the same type", function_name);
        goto exit;
    }
# 4193 "posixmodule.c"
    { PyThreadState *_save; _save = PyEval_SaveThread();





        result = rename(src.narrow, dst.narrow);
    PyEval_RestoreThread(_save); }

    if (result) {
        return_value = path_error(function_name, &dst);
        goto exit;
    }


    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return_value = (&_Py_NoneStruct);
exit:
    path_cleanup(&src);
    path_cleanup(&dst);
    return return_value;
}

static char posix_rename__doc__[] = "rename(src, dst, *, src_dir_fd=None, dst_dir_fd=None)\n\nRename a file or directory.\n\nIf either src_dir_fd or dst_dir_fd is not None, it should be a file\n  descriptor open to a directory, and the respective path string (src or dst)\n  should be relative; the path will then be relative to that directory.\nsrc_dir_fd and dst_dir_fd, may not be implemented on your platform.\n  If they are unavailable, using them will raise a NotImplementedError.";
# 4226 "posixmodule.c"
static PyObject *
posix_rename(PyObject *self, PyObject *args, PyObject *kwargs)
{
    return internal_rename(args, kwargs, 0);
}

static char posix_replace__doc__[] = "replace(src, dst, *, src_dir_fd=None, dst_dir_fd=None)\n\nRename a file or directory, overwriting the destination.\n\nIf either src_dir_fd or dst_dir_fd is not None, it should be a file\n  descriptor open to a directory, and the respective path string (src or dst)\n  should be relative; the path will then be relative to that directory.\nsrc_dir_fd and dst_dir_fd, may not be implemented on your platform.\n  If they are unavailable, using them will raise a NotImplementedError.";
# 4242 "posixmodule.c"
static PyObject *
posix_replace(PyObject *self, PyObject *args, PyObject *kwargs)
{
    return internal_rename(args, kwargs, 1);
}

static char posix_rmdir__doc__[] = "rmdir(path, *, dir_fd=None)\n\nRemove a directory.\n\nIf dir_fd is not None, it should be a file descriptor open to a directory,\n  and path should be relative; path will then be relative to that directory.\ndir_fd may not be implemented on your platform.\n  If it is unavailable, using it will raise a NotImplementedError.";
# 4257 "posixmodule.c"
static PyObject *
posix_rmdir(PyObject *self, PyObject *args, PyObject *kwargs)
{
    path_t path;
    int dir_fd = (-100);
    static char *keywords[] = {"path", "dir_fd", ((void *)0)};
    int result;
    PyObject *return_value = ((void *)0);

    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));
    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&|$O&:rmdir", keywords,
            path_converter, &path,



            dir_fd_unavailable, &dir_fd

            ))
        return ((void *)0);

    { PyThreadState *_save; _save = PyEval_SaveThread();
# 4290 "posixmodule.c"
        result = rmdir(path.narrow);

    PyEval_RestoreThread(_save); }

    if (result) {
        return_value = path_error("rmdir", &path);
        goto exit;
    }

    return_value = (&_Py_NoneStruct);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);

exit:
    path_cleanup(&path);
    return return_value;
}



static char posix_system__doc__[] = "system(command) -> exit_status\n\nExecute the command (a string) in a subshell.";



static PyObject *
posix_system(PyObject *self, PyObject *args)
{
    long sts;
# 4326 "posixmodule.c"
    PyObject *command_obj;
    char *command;
    if (!_PyArg_ParseTuple_SizeT(args, "O&:system",
                          PyUnicode_FSConverter, &command_obj))
        return ((void *)0);

    command = PyBytes_AsString(command_obj);
    { PyThreadState *_save; _save = PyEval_SaveThread();
    sts = system(command);
    PyEval_RestoreThread(_save); }
    do { if ( --((PyObject*)(command_obj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(command_obj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(command_obj)))); } while (0);

    return PyLong_FromLong(sts);
}



static char posix_umask__doc__[] = "umask(new_mask) -> old_mask\n\nSet the current numeric umask and return the previous umask.";



static PyObject *
posix_umask(PyObject *self, PyObject *args)
{
    int i;
    if (!_PyArg_ParseTuple_SizeT(args, "i:umask", &i))
        return ((void *)0);
    i = (int)umask(i);
    if (i < 0)
        return posix_error();
    return PyLong_FromLong((long)i);
}
# 4395 "posixmodule.c"
static char posix_unlink__doc__[] = "unlink(path, *, dir_fd=None)\n\nRemove a file (same as remove()).\n\nIf dir_fd is not None, it should be a file descriptor open to a directory,\n  and path should be relative; path will then be relative to that directory.\ndir_fd may not be implemented on your platform.\n  If it is unavailable, using it will raise a NotImplementedError.";
# 4404 "posixmodule.c"
static char posix_remove__doc__[] = "remove(path, *, dir_fd=None)\n\nRemove a file (same as unlink()).\n\nIf dir_fd is not None, it should be a file descriptor open to a directory,\n  and path should be relative; path will then be relative to that directory.\ndir_fd may not be implemented on your platform.\n  If it is unavailable, using it will raise a NotImplementedError.";
# 4413 "posixmodule.c"
static PyObject *
posix_unlink(PyObject *self, PyObject *args, PyObject *kwargs)
{
    path_t path;
    int dir_fd = (-100);
    static char *keywords[] = {"path", "dir_fd", ((void *)0)};
    int result;
    PyObject *return_value = ((void *)0);

    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));
    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&|$O&:unlink", keywords,
            path_converter, &path,



            dir_fd_unavailable, &dir_fd

            ))
        return ((void *)0);

    { PyThreadState *_save; _save = PyEval_SaveThread();
# 4446 "posixmodule.c"
        result = unlink(path.narrow);

    PyEval_RestoreThread(_save); }

    if (result) {
        return_value = path_error("unlink", &path);
        goto exit;
    }

    return_value = (&_Py_NoneStruct);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);

exit:
    path_cleanup(&path);
    return return_value;
}


static char posix_uname__doc__[] = "uname() -> uname_result\n\nReturn an object identifying the current operating system.\nThe object behaves like a named tuple with the following fields:\n  (sysname, nodename, release, version, machine)";





static PyStructSequence_Field uname_result_fields[] = {
    {"sysname", "operating system name"},
    {"nodename", "name of machine on network (implementation-defined)"},
    {"release", "operating system release"},
    {"version", "operating system version"},
    {"machine", "hardware identifier"},
    {((void *)0)}
};

static char uname_result__doc__[] = "uname_result: Result from os.uname().\n\nThis object may be accessed either as a tuple of\n  (sysname, nodename, release, version, machine),\nor via the attributes sysname, nodename, release, version, and machine.\n\nSee os.uname for more information.";







static PyStructSequence_Desc uname_result_desc = {
    "uname_result",
    uname_result__doc__,
    uname_result_fields,
    5
};

static PyTypeObject UnameResultType;



static PyObject *
posix_uname(PyObject *self, PyObject *noargs)
{
    struct utsname u;
    int res;
    PyObject *value;

    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = uname(&u);
    PyEval_RestoreThread(_save); }
    if (res < 0)
        return posix_error();

    value = PyStructSequence_New(&UnameResultType);
    if (value == ((void *)0))
        return ((void *)0);
# 4525 "posixmodule.c"
    { PyObject *o = PyUnicode_DecodeASCII(u.sysname, strlen(u.sysname), ((void *)0)); if (!o) { do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); return ((void *)0); } (((PyTupleObject *)(value))->ob_item[0] = o); };
    { PyObject *o = PyUnicode_DecodeASCII(u.nodename, strlen(u.nodename), ((void *)0)); if (!o) { do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); return ((void *)0); } (((PyTupleObject *)(value))->ob_item[1] = o); };
    { PyObject *o = PyUnicode_DecodeASCII(u.release, strlen(u.release), ((void *)0)); if (!o) { do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); return ((void *)0); } (((PyTupleObject *)(value))->ob_item[2] = o); };
    { PyObject *o = PyUnicode_DecodeASCII(u.version, strlen(u.version), ((void *)0)); if (!o) { do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); return ((void *)0); } (((PyTupleObject *)(value))->ob_item[3] = o); };
    { PyObject *o = PyUnicode_DecodeASCII(u.machine, strlen(u.machine), ((void *)0)); if (!o) { do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); return ((void *)0); } (((PyTupleObject *)(value))->ob_item[4] = o); };



    return value;
}



static char posix_utime__doc__[] = "utime(path, times=None, *, ns=None, dir_fd=None, follow_symlinks=True)\nSet the access and modified time of path.\n\npath may always be specified as a string.\nOn some platforms, path may also be specified as an open file descriptor.\n  If this functionality is unavailable, using it raises an exception.\n\nIf times is not None, it must be a tuple (atime, mtime);\n    atime and mtime should be expressed as float seconds since the epoch.\nIf ns is not None, it must be a tuple (atime_ns, mtime_ns);\n    atime_ns and mtime_ns should be expressed as integer nanoseconds\n    since the epoch.\nIf both times and ns are None, utime uses the current time.\nSpecifying tuples for both times and ns is an error.\n\nIf dir_fd is not None, it should be a file descriptor open to a directory,\n  and path should be relative; path will then be relative to that directory.\nIf follow_symlinks is False, and the last element of the path is a symbolic\n  link, utime will modify the symbolic link itself instead of the file the\n  link points to.\nIt is an error to use dir_fd or follow_symlinks when specifying path\n  as an open file descriptor.\ndir_fd and follow_symlinks may not be available on your platform.\n  If they are unavailable, using them will raise a NotImplementedError.";
# 4564 "posixmodule.c"
typedef struct {
    int now;
    time_t atime_s;
    long atime_ns;
    time_t mtime_s;
    long mtime_ns;
} utime_t;
# 4654 "posixmodule.c"
static int
utime_fd(utime_t *utime, int fd)
{




    struct timeval tv[2]; struct timeval *time; if (utime->now) time = ((void *)0); else { tv[0].tv_sec = utime->atime_s; tv[0].tv_usec = utime->atime_ns / 1000; tv[1].tv_sec = utime->mtime_s; tv[1].tv_usec = utime->mtime_ns / 1000; time = tv; };
    return futimes(fd, time);

}
# 4674 "posixmodule.c"
static int
utime_nofollow_symlinks(utime_t *utime, char *path)
{




    struct timeval tv[2]; struct timeval *time; if (utime->now) time = ((void *)0); else { tv[0].tv_sec = utime->atime_s; tv[0].tv_usec = utime->atime_ns / 1000; tv[1].tv_sec = utime->mtime_s; tv[1].tv_usec = utime->mtime_ns / 1000; time = tv; };
    return lutimes(path, time);

}





static int
utime_default(utime_t *utime, char *path)
{




    struct timeval tv[2]; struct timeval *time; if (utime->now) time = ((void *)0); else { tv[0].tv_sec = utime->atime_s; tv[0].tv_usec = utime->atime_ns / 1000; tv[1].tv_sec = utime->mtime_s; tv[1].tv_usec = utime->mtime_ns / 1000; time = tv; };
    return utimes(path, time);







}



static int
split_py_long_to_s_and_ns(PyObject *py_long, time_t *s, long *ns)
{
    int result = 0;
    PyObject *divmod;
    divmod = PyNumber_Divmod(py_long, billion);
    if (!divmod)
        goto exit;
    *s = _PyLong_AsTime_t((((PyTupleObject *)(divmod))->ob_item[0]));
    if ((*s == -1) && PyErr_Occurred())
        goto exit;
    *ns = PyLong_AsLong((((PyTupleObject *)(divmod))->ob_item[1]));
    if ((*ns == -1) && PyErr_Occurred())
        goto exit;

    result = 1;
exit:
    do { if ((divmod) == ((void *)0)) ; else do { if ( --((PyObject*)(divmod))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(divmod)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(divmod)))); } while (0); } while (0);
    return result;
}

static PyObject *
posix_utime(PyObject *self, PyObject *args, PyObject *kwargs)
{
    path_t path;
    PyObject *times = ((void *)0);
    PyObject *ns = ((void *)0);
    int dir_fd = (-100);
    int follow_symlinks = 1;
    char *keywords[] = {"path", "times", "ns", "dir_fd",
                        "follow_symlinks", ((void *)0)};

    utime_t utime;





    int result;


    PyObject *return_value = ((void *)0);

    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));

    path.allow_fd = 1;

    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs,
            "O&|O$OO&p:utime", keywords,
            path_converter, &path,
            &times, &ns,



            dir_fd_unavailable, &dir_fd,

            &follow_symlinks
            ))
        return ((void *)0);

    if (times && (times != (&_Py_NoneStruct)) && ns) {
        PyErr_SetString(PyExc_ValueError,
                     "utime: you may specify either 'times'"
                     " or 'ns' but not both");
        goto exit;
    }

    if (times && (times != (&_Py_NoneStruct))) {
        if (!((((PyObject*)(times))->ob_type) == &PyTuple_Type) || (PyTuple_Size(times) != 2)) {
            PyErr_SetString(PyExc_TypeError,
                         "utime: 'times' must be either"
                         " a tuple of two ints or None");
            goto exit;
        }
        utime.now = 0;
        if (_PyTime_ObjectToTimespec((((PyTupleObject *)(times))->ob_item[0]),
                                     &utime.atime_s, &utime.atime_ns) == -1 ||
            _PyTime_ObjectToTimespec((((PyTupleObject *)(times))->ob_item[1]),
                                     &utime.mtime_s, &utime.mtime_ns) == -1) {
            goto exit;
        }
    }
    else if (ns) {
        if (!((((PyObject*)(ns))->ob_type) == &PyTuple_Type) || (PyTuple_Size(ns) != 2)) {
            PyErr_SetString(PyExc_TypeError,
                         "utime: 'ns' must be a tuple of two ints");
            goto exit;
        }
        utime.now = 0;
        if (!split_py_long_to_s_and_ns((((PyTupleObject *)(ns))->ob_item[0]),
                                      &utime.atime_s, &utime.atime_ns) ||
            !split_py_long_to_s_and_ns((((PyTupleObject *)(ns))->ob_item[1]),
                                       &utime.mtime_s, &utime.mtime_ns)) {
            goto exit;
        }
    }
    else {

        utime.now = 1;
    }






    if (path_and_dir_fd_invalid("utime", &path, dir_fd) ||
        dir_fd_and_fd_invalid("utime", dir_fd, path.fd) ||
        fd_and_follow_symlinks_invalid("utime", path.fd, follow_symlinks))
        goto exit;


    if ((dir_fd != (-100)) && (!follow_symlinks)) {
        PyErr_SetString(PyExc_ValueError,
                     "utime: cannot use dir_fd and follow_symlinks "
                     "together on this platform");
        goto exit;
    }
# 4868 "posixmodule.c"
    { PyThreadState *_save; _save = PyEval_SaveThread();


    if ((!follow_symlinks) && (dir_fd == (-100)))
        result = utime_nofollow_symlinks(&utime, path.narrow);
    else
# 4883 "posixmodule.c"
    if (path.fd != -1)
        result = utime_fd(&utime, path.fd);
    else


    result = utime_default(&utime, path.narrow);

    PyEval_RestoreThread(_save); }

    if (result < 0) {

        return_value = posix_error();
        goto exit;
    }



    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return_value = (&_Py_NoneStruct);

exit:
    path_cleanup(&path);




    return return_value;
}



static char posix__exit__doc__[] = "_exit(status)\n\nExit to the system with specified status, without normal exit processing.";



static PyObject *
posix__exit(PyObject *self, PyObject *args)
{
    int sts;
    if (!_PyArg_ParseTuple_SizeT(args, "i:_exit", &sts))
        return ((void *)0);
    _exit(sts);
    return ((void *)0);
}


static void
free_string_array(char **array, Py_ssize_t count)
{
    Py_ssize_t i;
    for (i = 0; i < count; i++)
        PyMem_Free(array[i]);
    free(array);
}

static
int fsconvert_strdup(PyObject *o, char**out)
{
    PyObject *bytes;
    Py_ssize_t size;
    if (!PyUnicode_FSConverter(o, &bytes))
        return 0;
    size = ((__builtin_expect(!(((((((PyObject*)(bytes))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "posixmodule.c", 4945, "PyBytes_Check(bytes)") : (void)0),(((PyVarObject*)(bytes))->ob_size));
    *out = PyMem_Malloc(size+1);
    if (!*out)
        return 0;
    ((__builtin_object_size (*out, 0) != (size_t) -1) ? __builtin___memcpy_chk (*out, PyBytes_AsString(bytes), size+1, __builtin_object_size (*out, 0)) : __inline_memcpy_chk (*out, PyBytes_AsString(bytes), size+1));
    do { if ( --((PyObject*)(bytes))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(bytes)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(bytes)))); } while (0);
    return 1;
}



static char**
parse_envlist(PyObject* env, Py_ssize_t *envc_ptr)
{
    char **envlist;
    Py_ssize_t i, pos, envc;
    PyObject *keys=((void *)0), *vals=((void *)0);
    PyObject *key, *val, *key2, *val2;
    char *p, *k, *v;
    size_t len;

    i = PyMapping_Size(env);
    if (i < 0)
        return ((void *)0);
    envlist = ( ((size_t)(i + 1) > ((Py_ssize_t)(((size_t)-1)>>1)) / sizeof(char *)) ? ((void *)0) : ( (char * *) ((size_t)((i + 1) * sizeof(char *)) > (size_t)((Py_ssize_t)(((size_t)-1)>>1)) ? ((void *)0) : malloc(((i + 1) * sizeof(char *)) ? ((i + 1) * sizeof(char *)) : 1)) ) );
    if (envlist == ((void *)0)) {
        PyErr_NoMemory();
        return ((void *)0);
    }
    envc = 0;
    keys = PyMapping_Keys(env);
    vals = PyMapping_Values(env);
    if (!keys || !vals)
        goto error;
    if (!((((((PyObject*)(keys))->ob_type))->tp_flags & ((1L<<25))) != 0) || !((((((PyObject*)(vals))->ob_type))->tp_flags & ((1L<<25))) != 0)) {
        PyErr_Format(PyExc_TypeError,
                     "env.keys() or env.values() is not a list");
        goto error;
    }

    for (pos = 0; pos < i; pos++) {
        key = PyList_GetItem(keys, pos);
        val = PyList_GetItem(vals, pos);
        if (!key || !val)
            goto error;

        if (PyUnicode_FSConverter(key, &key2) == 0)
            goto error;
        if (PyUnicode_FSConverter(val, &val2) == 0) {
            do { if ( --((PyObject*)(key2))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key2)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key2)))); } while (0);
            goto error;
        }





        k = PyBytes_AsString(key2);
        v = PyBytes_AsString(val2);
        len = ((__builtin_expect(!(((((((PyObject*)(key2))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "posixmodule.c", 5004, "PyBytes_Check(key2)") : (void)0),(((PyVarObject*)(key2))->ob_size)) + ((__builtin_expect(!(((((((PyObject*)(val2))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "posixmodule.c", 5004, "PyBytes_Check(val2)") : (void)0),(((PyVarObject*)(val2))->ob_size)) + 2;

        p = ( ((size_t)(len) > ((Py_ssize_t)(((size_t)-1)>>1)) / sizeof(char)) ? ((void *)0) : ( (char *) ((size_t)((len) * sizeof(char)) > (size_t)((Py_ssize_t)(((size_t)-1)>>1)) ? ((void *)0) : malloc(((len) * sizeof(char)) ? ((len) * sizeof(char)) : 1)) ) );
        if (p == ((void *)0)) {
            PyErr_NoMemory();
            do { if ( --((PyObject*)(key2))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key2)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key2)))); } while (0);
            do { if ( --((PyObject*)(val2))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(val2)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(val2)))); } while (0);
            goto error;
        }
        PyOS_snprintf(p, len, "%s=%s", k, v);
        envlist[envc++] = p;
        do { if ( --((PyObject*)(key2))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key2)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key2)))); } while (0);
        do { if ( --((PyObject*)(val2))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(val2)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(val2)))); } while (0);



    }
    do { if ( --((PyObject*)(vals))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(vals)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(vals)))); } while (0);
    do { if ( --((PyObject*)(keys))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(keys)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(keys)))); } while (0);

    envlist[envc] = 0;
    *envc_ptr = envc;
    return envlist;

error:
    do { if ((keys) == ((void *)0)) ; else do { if ( --((PyObject*)(keys))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(keys)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(keys)))); } while (0); } while (0);
    do { if ((vals) == ((void *)0)) ; else do { if ( --((PyObject*)(vals))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(vals)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(vals)))); } while (0); } while (0);
    while (--envc >= 0)
        free(envlist[envc]);
    free(envlist);
    return ((void *)0);
}

static char**
parse_arglist(PyObject* argv, Py_ssize_t *argc)
{
    int i;
    char **argvlist = ( ((size_t)(*argc+1) > ((Py_ssize_t)(((size_t)-1)>>1)) / sizeof(char *)) ? ((void *)0) : ( (char * *) ((size_t)((*argc+1) * sizeof(char *)) > (size_t)((Py_ssize_t)(((size_t)-1)>>1)) ? ((void *)0) : malloc(((*argc+1) * sizeof(char *)) ? ((*argc+1) * sizeof(char *)) : 1)) ) );
    if (argvlist == ((void *)0)) {
        PyErr_NoMemory();
        return ((void *)0);
    }
    for (i = 0; i < *argc; i++) {
        PyObject* item = ( (((PyObject*)(argv))->ob_type)->tp_as_sequence->sq_item(argv, i) );
        if (item == ((void *)0))
            goto fail;
        if (!fsconvert_strdup(item, &argvlist[i])) {
            do { if ( --((PyObject*)(item))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(item)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(item)))); } while (0);
            goto fail;
        }
        do { if ( --((PyObject*)(item))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(item)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(item)))); } while (0);
    }
    argvlist[*argc] = ((void *)0);
    return argvlist;
fail:
    *argc = i;
    free_string_array(argvlist, *argc);
    return ((void *)0);
}



static char posix_execv__doc__[] = "execv(path, args)\n\nExecute an executable path with arguments, replacing current process.\n\n    path: path of executable file\n    args: tuple or list of strings";






static PyObject *
posix_execv(PyObject *self, PyObject *args)
{
    PyObject *opath;
    char *path;
    PyObject *argv;
    char **argvlist;
    Py_ssize_t argc;




    if (!_PyArg_ParseTuple_SizeT(args, "O&O:execv",
                          PyUnicode_FSConverter,
                          &opath, &argv))
        return ((void *)0);
    path = PyBytes_AsString(opath);
    if (!((((((PyObject*)(argv))->ob_type))->tp_flags & ((1L<<25))) != 0) && !((((((PyObject*)(argv))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
        PyErr_SetString(PyExc_TypeError,
                        "execv() arg 2 must be a tuple or list");
        do { if ( --((PyObject*)(opath))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(opath)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(opath)))); } while (0);
        return ((void *)0);
    }
    argc = PySequence_Size(argv);
    if (argc < 1) {
        PyErr_SetString(PyExc_ValueError, "execv() arg 2 must not be empty");
        do { if ( --((PyObject*)(opath))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(opath)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(opath)))); } while (0);
        return ((void *)0);
    }

    argvlist = parse_arglist(argv, &argc);
    if (argvlist == ((void *)0)) {
        do { if ( --((PyObject*)(opath))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(opath)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(opath)))); } while (0);
        return ((void *)0);
    }

    execv(path, argvlist);



    free_string_array(argvlist, argc);
    do { if ( --((PyObject*)(opath))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(opath)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(opath)))); } while (0);
    return posix_error();
}

static char posix_execve__doc__[] = "execve(path, args, env)\n\nExecute a path with arguments and environment, replacing current process.\n\n    path: path of executable file\n    args: tuple or list of arguments\n    env: dictionary of strings mapping to strings\n\nOn some platforms, you may specify an open file descriptor for path;\n  execve will execute the program the file descriptor is open to.\n  If this functionality is unavailable, using it raises NotImplementedError.";
# 5130 "posixmodule.c"
static PyObject *
posix_execve(PyObject *self, PyObject *args, PyObject *kwargs)
{
    path_t path;
    PyObject *argv, *env;
    char **argvlist = ((void *)0);
    char **envlist;
    Py_ssize_t argc, envc;
    static char *keywords[] = {"path", "argv", "environment", ((void *)0)};





    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));



    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&OO:execve", keywords,
                          path_converter, &path,
                          &argv, &env
                          ))
        return ((void *)0);

    if (!((((((PyObject*)(argv))->ob_type))->tp_flags & ((1L<<25))) != 0) && !((((((PyObject*)(argv))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
        PyErr_SetString(PyExc_TypeError,
                        "execve: argv must be a tuple or list");
        goto fail;
    }
    argc = PySequence_Size(argv);
    if (!PyMapping_Check(env)) {
        PyErr_SetString(PyExc_TypeError,
                        "execve: environment must be a mapping object");
        goto fail;
    }

    argvlist = parse_arglist(argv, &argc);
    if (argvlist == ((void *)0)) {
        goto fail;
    }

    envlist = parse_envlist(env, &envc);
    if (envlist == ((void *)0))
        goto fail;






        execve(path.narrow, argvlist, envlist);



    path_posix_error("execve", &path);

    while (--envc >= 0)
        free(envlist[envc]);
    free(envlist);
  fail:
    if (argvlist)
        free_string_array(argvlist, argc);
    path_cleanup(&path);
    return ((void *)0);
}
# 5606 "posixmodule.c"
static char posix_fork__doc__[] = "fork() -> pid\n\nFork a child process.\nReturn 0 to child process and PID of child to parent process.";




static PyObject *
posix_fork(PyObject *self, PyObject *noargs)
{
    pid_t pid;
    int result = 0;
    _PyImport_AcquireLock();
    pid = fork();
    if (pid == 0) {

        PyOS_AfterFork();
    } else {

        result = _PyImport_ReleaseLock();
    }
    if (pid == -1)
        return posix_error();
    if (result < 0) {

        PyErr_SetString(PyExc_RuntimeError,
                        "not holding the import lock");
        return ((void *)0);
    }
    return PyLong_FromLong(pid);
}






static char posix_sched_get_priority_max__doc__[] = "sched_get_priority_max(policy)\n\nGet the maximum scheduling priority for *policy*.";



static PyObject *
posix_sched_get_priority_max(PyObject *self, PyObject *args)
{
    int policy, max;

    if (!_PyArg_ParseTuple_SizeT(args, "i:sched_get_priority_max", &policy))
        return ((void *)0);
    max = sched_get_priority_max(policy);
    if (max < 0)
        return posix_error();
    return PyLong_FromLong(max);
}

static char posix_sched_get_priority_min__doc__[] = "sched_get_priority_min(policy)\n\nGet the minimum scheduling priority for *policy*.";



static PyObject *
posix_sched_get_priority_min(PyObject *self, PyObject *args)
{
    int policy, min;

    if (!_PyArg_ParseTuple_SizeT(args, "i:sched_get_priority_min", &policy))
        return ((void *)0);
    min = sched_get_priority_min(policy);
    if (min < 0)
        return posix_error();
    return PyLong_FromLong(min);
}
# 5859 "posixmodule.c"
static char posix_sched_yield__doc__[] = "sched_yield()\n\nVoluntarily relinquish the CPU.";



static PyObject *
posix_sched_yield(PyObject *self, PyObject *noargs)
{
    if (sched_yield())
        return posix_error();
    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}
# 6053 "posixmodule.c"
# 1 "/usr/include/util.h" 1 3 4
# 65 "/usr/include/util.h" 3 4
# 1 "/usr/include/pwd.h" 1 3 4
# 119 "/usr/include/pwd.h" 3 4
struct passwd {
 char *pw_name;
 char *pw_passwd;
 uid_t pw_uid;
 gid_t pw_gid;
 __darwin_time_t pw_change;
 char *pw_class;
 char *pw_gecos;
 char *pw_dir;
 char *pw_shell;
 __darwin_time_t pw_expire;
};




struct passwd *getpwuid(uid_t);
struct passwd *getpwnam(const char *);
int getpwuid_r(uid_t, struct passwd *, char *, size_t, struct passwd **);
int getpwnam_r(const char *, struct passwd *, char *, size_t, struct passwd **);
struct passwd *getpwent(void);

int setpassent(int);
char *user_from_uid(uid_t, int);

void setpwent(void);
void endpwent(void);

# 66 "/usr/include/util.h" 2 3 4
# 87 "/usr/include/util.h" 3 4

struct utmp;
void login(struct utmp *) __attribute__((deprecated,visibility("default")));
int login_tty(int);
int logout(const char *) __attribute__((deprecated,visibility("default")));
void logwtmp(const char *, const char *, const char *) __attribute__((deprecated,visibility("default")));
int opendev(char *, int, int, char **);
int openpty(int *, int *, char *, struct termios *,
       struct winsize *);
char *fparseln(FILE *, size_t *, size_t *, const char[3], int);
pid_t forkpty(int *, char *, struct termios *, struct winsize *);
int pidlock(const char *, int, pid_t *, const char *);
int ttylock(const char *, int, pid_t *);
int ttyunlock(const char *);
int ttyaction(char *tty, char *act, char *user);
struct iovec;
char *ttymsg(struct iovec *, int, const char *, int);



# 1 "/usr/include/utmp.h" 1 3 4
# 90 "/usr/include/utmp.h" 3 4
struct lastlog {
 time_t ll_time;
 char ll_line[8];
 char ll_host[16];
} __attribute__((deprecated));

struct utmp {
 char ut_line[8];
 char ut_name[8];
 char ut_host[16];
 long ut_time;
} __attribute__((deprecated));
# 108 "/usr/include/util.h" 2 3 4
# 6054 "posixmodule.c" 2
# 6063 "posixmodule.c"
static char posix_openpty__doc__[] = "openpty() -> (master_fd, slave_fd)\n\nOpen a pseudo-terminal, returning open fd's for both master and slave end.\n";



static PyObject *
posix_openpty(PyObject *self, PyObject *noargs)
{
    int master_fd, slave_fd;
# 6082 "posixmodule.c"
    if (openpty(&master_fd, &slave_fd, ((void *)0), ((void *)0), ((void *)0)) != 0)
        return posix_error();
# 6123 "posixmodule.c"
    return _Py_BuildValue_SizeT("(ii)", master_fd, slave_fd);

}



static char posix_forkpty__doc__[] = "forkpty() -> (pid, master_fd)\n\nFork a new process with a new pseudo-terminal as controlling tty.\n\nLike fork(), return 0 as pid to child process, and PID of child to parent.\nTo both, return fd of newly opened pseudo-terminal.\n";





static PyObject *
posix_forkpty(PyObject *self, PyObject *noargs)
{
    int master_fd = -1, result = 0;
    pid_t pid;

    _PyImport_AcquireLock();
    pid = forkpty(&master_fd, ((void *)0), ((void *)0), ((void *)0));
    if (pid == 0) {

        PyOS_AfterFork();
    } else {

        result = _PyImport_ReleaseLock();
    }
    if (pid == -1)
        return posix_error();
    if (result < 0) {

        PyErr_SetString(PyExc_RuntimeError,
                        "not holding the import lock");
        return ((void *)0);
    }
    return _Py_BuildValue_SizeT("(Ni)", PyLong_FromLong(pid), master_fd);
}




static char posix_getegid__doc__[] = "getegid() -> egid\n\nReturn the current process's effective group id.";



static PyObject *
posix_getegid(PyObject *self, PyObject *noargs)
{
    return _PyLong_FromGid(getegid());
}




static char posix_geteuid__doc__[] = "geteuid() -> euid\n\nReturn the current process's effective user id.";



static PyObject *
posix_geteuid(PyObject *self, PyObject *noargs)
{
    return _PyLong_FromUid(geteuid());
}




static char posix_getgid__doc__[] = "getgid() -> gid\n\nReturn the current process's group id.";



static PyObject *
posix_getgid(PyObject *self, PyObject *noargs)
{
    return _PyLong_FromGid(getgid());
}



static char posix_getpid__doc__[] = "getpid() -> pid\n\nReturn the current process id";



static PyObject *
posix_getpid(PyObject *self, PyObject *noargs)
{
    return PyLong_FromLong(getpid());
}


static char posix_getgrouplist__doc__[] = "getgrouplist(user, group) -> list of groups to which a user belongs\n\nReturns a list of groups to which a user belongs.\n\n    user: username to lookup\n    group: base group id of the user";





static PyObject *
posix_getgrouplist(PyObject *self, PyObject *args)
{







    const char *user;
    int i, ngroups;
    PyObject *list;

    int *groups, basegid;



    ngroups = 16;


    if (!_PyArg_ParseTuple_SizeT(args, "si:getgrouplist", &user, &basegid))
        return ((void *)0);







    groups = PyMem_Malloc(ngroups * sizeof(int));



    if (groups == ((void *)0))
        return PyErr_NoMemory();

    if (getgrouplist(user, basegid, groups, &ngroups) == -1) {
        PyMem_Free(groups);
        return posix_error();
    }

    list = PyList_New(ngroups);
    if (list == ((void *)0)) {
        PyMem_Free(groups);
        return ((void *)0);
    }

    for (i = 0; i < ngroups; i++) {

        PyObject *o = PyLong_FromUnsignedLong((unsigned long)groups[i]);



        if (o == ((void *)0)) {
            do { if ( --((PyObject*)(list))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(list)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(list)))); } while (0);
            PyMem_Free(groups);
            return ((void *)0);
        }
        (((PyListObject *)(list))->ob_item[i] = (o));
    }

    PyMem_Free(groups);

    return list;
}



static char posix_getgroups__doc__[] = "getgroups() -> list of group IDs\n\nReturn list of supplemental group IDs for the process.";



static PyObject *
posix_getgroups(PyObject *self, PyObject *noargs)
{
    PyObject *result = ((void *)0);







    gid_t grouplist[16];
# 6313 "posixmodule.c"
    gid_t* alt_grouplist = grouplist;
    int n;

    n = getgroups(16, grouplist);
    if (n < 0) {
        if ((*__error()) == 22) {
            n = getgroups(0, ((void *)0));
            if (n == -1) {
                return posix_error();
            }
            if (n == 0) {

                alt_grouplist = grouplist;
            } else {
                alt_grouplist = PyMem_Malloc(n * sizeof(gid_t));
                if (alt_grouplist == ((void *)0)) {
                    (*__error()) = 22;
                    return posix_error();
                }
                n = getgroups(n, alt_grouplist);
                if (n == -1) {
                    PyMem_Free(alt_grouplist);
                    return posix_error();
                }
            }
        } else {
            return posix_error();
        }
    }
    result = PyList_New(n);
    if (result != ((void *)0)) {
        int i;
        for (i = 0; i < n; ++i) {
            PyObject *o = _PyLong_FromGid(alt_grouplist[i]);
            if (o == ((void *)0)) {
                do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0);
                result = ((void *)0);
                break;
            }
            (((PyListObject *)(result))->ob_item[i] = (o));
        }
    }

    if (alt_grouplist != grouplist) {
        PyMem_Free(alt_grouplist);
    }

    return result;
}



static char posix_initgroups__doc__[] = "initgroups(username, gid) -> None\n\nCall the system initgroups() to initialize the group access list with all of\nthe groups of which the specified username is a member, plus the specified\ngroup id.";





static PyObject *
posix_initgroups(PyObject *self, PyObject *args)
{
    PyObject *oname;
    char *username;
    int res;

    int gid;





    if (!_PyArg_ParseTuple_SizeT(args, "O&i:initgroups",
                          PyUnicode_FSConverter, &oname,
                          &gid))





        return ((void *)0);
    username = ((__builtin_expect(!(((((((PyObject*)(oname))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "posixmodule.c", 6393, "PyBytes_Check(oname)") : (void)0), (((PyBytesObject *)(oname))->ob_sval));

    res = initgroups(username, gid);
    do { if ( --((PyObject*)(oname))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(oname)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(oname)))); } while (0);
    if (res == -1)
        return PyErr_SetFromErrno(PyExc_OSError);

    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}



static char posix_getpgid__doc__[] = "getpgid(pid) -> pgid\n\nCall the system call getpgid().";



static PyObject *
posix_getpgid(PyObject *self, PyObject *args)
{
    pid_t pid, pgid;
    if (!_PyArg_ParseTuple_SizeT(args, "i" ":getpgid", &pid))
        return ((void *)0);
    pgid = getpgid(pid);
    if (pgid < 0)
        return posix_error();
    return PyLong_FromLong(pgid);
}




static char posix_getpgrp__doc__[] = "getpgrp() -> pgrp\n\nReturn the current process group id.";



static PyObject *
posix_getpgrp(PyObject *self, PyObject *noargs)
{



    return PyLong_FromLong(getpgrp());

}




static char posix_setpgrp__doc__[] = "setpgrp()\n\nMake this process the process group leader.";



static PyObject *
posix_setpgrp(PyObject *self, PyObject *noargs)
{



    if (setpgrp() < 0)

        return posix_error();
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}
# 6505 "posixmodule.c"
static char posix_getppid__doc__[] = "getppid() -> ppid\n\nReturn the parent's process id.  If the parent process has already exited,\nWindows machines will still return its id; others systems will return the id\nof the 'init' process (1).";





static PyObject *
posix_getppid(PyObject *self, PyObject *noargs)
{



    return PyLong_FromLong(getppid());

}




static char posix_getlogin__doc__[] = "getlogin() -> string\n\nReturn the actual login name.";



static PyObject *
posix_getlogin(PyObject *self, PyObject *noargs)
{
    PyObject *result = ((void *)0);
# 6543 "posixmodule.c"
    char *name;
    int old_errno = (*__error());

    (*__error()) = 0;
    name = getlogin();
    if (name == ((void *)0)) {
        if ((*__error()))
            posix_error();
        else
            PyErr_SetString(PyExc_OSError, "unable to determine login name");
    }
    else
        result = PyUnicode_DecodeFSDefault(name);
    (*__error()) = old_errno;

    return result;
}



static char posix_getuid__doc__[] = "getuid() -> uid\n\nReturn the current process's user id.";



static PyObject *
posix_getuid(PyObject *self, PyObject *noargs)
{
    return _PyLong_FromUid(getuid());
}




static char posix_kill__doc__[] = "kill(pid, sig)\n\nKill a process with a signal.";



static PyObject *
posix_kill(PyObject *self, PyObject *args)
{
    pid_t pid;
    int sig;
    if (!_PyArg_ParseTuple_SizeT(args, "i" "i:kill", &pid, &sig))
        return ((void *)0);
# 6601 "posixmodule.c"
    if (kill(pid, sig) == -1)
        return posix_error();

    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}



static char posix_killpg__doc__[] = "killpg(pgid, sig)\n\nKill a process group with a signal.";



static PyObject *
posix_killpg(PyObject *self, PyObject *args)
{
    int sig;
    pid_t pgid;




    if (!_PyArg_ParseTuple_SizeT(args, "i" "i:killpg", &pgid, &sig))
        return ((void *)0);
    if (killpg(pgid, sig) == -1)
        return posix_error();
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}
# 6703 "posixmodule.c"
static char posix_setuid__doc__[] = "setuid(uid)\n\nSet the current process's user id.";



static PyObject *
posix_setuid(PyObject *self, PyObject *args)
{
    uid_t uid;
    if (!_PyArg_ParseTuple_SizeT(args, "O&:setuid", _Py_Uid_Converter, &uid))
        return ((void *)0);
    if (setuid(uid) < 0)
        return posix_error();
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}




static char posix_seteuid__doc__[] = "seteuid(uid)\n\nSet the current process's effective user id.";



static PyObject *
posix_seteuid (PyObject *self, PyObject *args)
{
    uid_t euid;
    if (!_PyArg_ParseTuple_SizeT(args, "O&:seteuid", _Py_Uid_Converter, &euid))
        return ((void *)0);
    if (seteuid(euid) < 0) {
        return posix_error();
    } else {
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        return (&_Py_NoneStruct);
    }
}



static char posix_setegid__doc__[] = "setegid(gid)\n\nSet the current process's effective group id.";



static PyObject *
posix_setegid (PyObject *self, PyObject *args)
{
    gid_t egid;
    if (!_PyArg_ParseTuple_SizeT(args, "O&:setegid", _Py_Gid_Converter, &egid))
        return ((void *)0);
    if (setegid(egid) < 0) {
        return posix_error();
    } else {
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        return (&_Py_NoneStruct);
    }
}



static char posix_setreuid__doc__[] = "setreuid(ruid, euid)\n\nSet the current process's real and effective user ids.";



static PyObject *
posix_setreuid (PyObject *self, PyObject *args)
{
    uid_t ruid, euid;
    if (!_PyArg_ParseTuple_SizeT(args, "O&O&:setreuid",
                          _Py_Uid_Converter, &ruid,
                          _Py_Uid_Converter, &euid))
        return ((void *)0);
    if (setreuid(ruid, euid) < 0) {
        return posix_error();
    } else {
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        return (&_Py_NoneStruct);
    }
}



static char posix_setregid__doc__[] = "setregid(rgid, egid)\n\nSet the current process's real and effective group ids.";



static PyObject *
posix_setregid (PyObject *self, PyObject *args)
{
    gid_t rgid, egid;
    if (!_PyArg_ParseTuple_SizeT(args, "O&O&:setregid",
                          _Py_Gid_Converter, &rgid,
                          _Py_Gid_Converter, &egid))
        return ((void *)0);
    if (setregid(rgid, egid) < 0) {
        return posix_error();
    } else {
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        return (&_Py_NoneStruct);
    }
}



static char posix_setgid__doc__[] = "setgid(gid)\n\nSet the current process's group id.";



static PyObject *
posix_setgid(PyObject *self, PyObject *args)
{
    gid_t gid;
    if (!_PyArg_ParseTuple_SizeT(args, "O&:setgid", _Py_Gid_Converter, &gid))
        return ((void *)0);
    if (setgid(gid) < 0)
        return posix_error();
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}



static char posix_setgroups__doc__[] = "setgroups(list)\n\nSet the groups of the current process to list.";



static PyObject *
posix_setgroups(PyObject *self, PyObject *groups)
{
    int i, len;
    gid_t grouplist[16];

    if (!PySequence_Check(groups)) {
        PyErr_SetString(PyExc_TypeError, "setgroups argument must be a sequence");
        return ((void *)0);
    }
    len = PySequence_Size(groups);
    if (len > 16) {
        PyErr_SetString(PyExc_ValueError, "too many groups");
        return ((void *)0);
    }
    for(i = 0; i < len; i++) {
        PyObject *elem;
        elem = PySequence_GetItem(groups, i);
        if (!elem)
            return ((void *)0);
        if (!((((((PyObject*)(elem))->ob_type))->tp_flags & ((1L<<24))) != 0)) {
            PyErr_SetString(PyExc_TypeError,
                            "groups must be integers");
            do { if ( --((PyObject*)(elem))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(elem)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(elem)))); } while (0);
            return ((void *)0);
        } else {
            if (!_Py_Gid_Converter(elem, &grouplist[i])) {
                do { if ( --((PyObject*)(elem))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(elem)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(elem)))); } while (0);
                return ((void *)0);
            }
        }
        do { if ( --((PyObject*)(elem))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(elem)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(elem)))); } while (0);
    }

    if (setgroups(len, grouplist) < 0)
        return posix_error();
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}



static PyObject *
wait_helper(pid_t pid, int status, struct rusage *ru)
{
    PyObject *result;
    static PyObject *struct_rusage;
    static _Py_Identifier PyId_struct_rusage = { 0, "struct_rusage", 0 };

    if (pid == -1)
        return posix_error();

    if (struct_rusage == ((void *)0)) {
        PyObject *m = PyImport_ImportModuleNoBlock("resource");
        if (m == ((void *)0))
            return ((void *)0);
        struct_rusage = _PyObject_GetAttrId(m, &PyId_struct_rusage);
        do { if ( --((PyObject*)(m))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(m)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(m)))); } while (0);
        if (struct_rusage == ((void *)0))
            return ((void *)0);
    }


    result = PyStructSequence_New((PyTypeObject*) struct_rusage);
    if (!result)
        return ((void *)0);





    (((PyTupleObject *)(result))->ob_item[0] = PyFloat_FromDouble(((double)(ru->ru_utime).tv_sec + (ru->ru_utime).tv_usec * 0.000001)));

    (((PyTupleObject *)(result))->ob_item[1] = PyFloat_FromDouble(((double)(ru->ru_stime).tv_sec + (ru->ru_stime).tv_usec * 0.000001)));



    (((PyTupleObject *)(result))->ob_item[2] = PyLong_FromLong(ru->ru_maxrss));
    (((PyTupleObject *)(result))->ob_item[3] = PyLong_FromLong(ru->ru_ixrss));
    (((PyTupleObject *)(result))->ob_item[4] = PyLong_FromLong(ru->ru_idrss));
    (((PyTupleObject *)(result))->ob_item[5] = PyLong_FromLong(ru->ru_isrss));
    (((PyTupleObject *)(result))->ob_item[6] = PyLong_FromLong(ru->ru_minflt));
    (((PyTupleObject *)(result))->ob_item[7] = PyLong_FromLong(ru->ru_majflt));
    (((PyTupleObject *)(result))->ob_item[8] = PyLong_FromLong(ru->ru_nswap));
    (((PyTupleObject *)(result))->ob_item[9] = PyLong_FromLong(ru->ru_inblock));
    (((PyTupleObject *)(result))->ob_item[10] = PyLong_FromLong(ru->ru_oublock));
    (((PyTupleObject *)(result))->ob_item[11] = PyLong_FromLong(ru->ru_msgsnd));
    (((PyTupleObject *)(result))->ob_item[12] = PyLong_FromLong(ru->ru_msgrcv));
    (((PyTupleObject *)(result))->ob_item[13] = PyLong_FromLong(ru->ru_nsignals));
    (((PyTupleObject *)(result))->ob_item[14] = PyLong_FromLong(ru->ru_nvcsw));
    (((PyTupleObject *)(result))->ob_item[15] = PyLong_FromLong(ru->ru_nivcsw));


    if (PyErr_Occurred()) {
        do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0);
        return ((void *)0);
    }

    return _Py_BuildValue_SizeT("NiN", PyLong_FromLong(pid), status, result);
}



static char posix_wait3__doc__[] = "wait3(options) -> (pid, status, rusage)\n\nWait for completion of a child process.";



static PyObject *
posix_wait3(PyObject *self, PyObject *args)
{
    pid_t pid;
    int options;
    struct rusage ru;
    int status;
    (status) = 0;

    if (!_PyArg_ParseTuple_SizeT(args, "i:wait3", &options))
        return ((void *)0);

    { PyThreadState *_save; _save = PyEval_SaveThread();
    pid = wait3(&status, options, &ru);
    PyEval_RestoreThread(_save); }

    return wait_helper(pid, (status), &ru);
}



static char posix_wait4__doc__[] = "wait4(pid, options) -> (pid, status, rusage)\n\nWait for completion of a given child process.";



static PyObject *
posix_wait4(PyObject *self, PyObject *args)
{
    pid_t pid;
    int options;
    struct rusage ru;
    int status;
    (status) = 0;

    if (!_PyArg_ParseTuple_SizeT(args, "i" "i:wait4", &pid, &options))
        return ((void *)0);

    { PyThreadState *_save; _save = PyEval_SaveThread();
    pid = wait4(pid, &status, options, &ru);
    PyEval_RestoreThread(_save); }

    return wait_helper(pid, (status), &ru);
}
# 7030 "posixmodule.c"
static char posix_waitpid__doc__[] = "waitpid(pid, options) -> (pid, status)\n\nWait for completion of a given child process.";



static PyObject *
posix_waitpid(PyObject *self, PyObject *args)
{
    pid_t pid;
    int options;
    int status;
    (status) = 0;

    if (!_PyArg_ParseTuple_SizeT(args, "i" "i:waitpid", &pid, &options))
        return ((void *)0);
    { PyThreadState *_save; _save = PyEval_SaveThread();
    pid = waitpid(pid, &status, options);
    PyEval_RestoreThread(_save); }
    if (pid == -1)
        return posix_error();

    return _Py_BuildValue_SizeT("Ni", PyLong_FromLong(pid), (status));
}
# 7080 "posixmodule.c"
static char posix_wait__doc__[] = "wait() -> (pid, status)\n\nWait for completion of a child process.";



static PyObject *
posix_wait(PyObject *self, PyObject *noargs)
{
    pid_t pid;
    int status;
    (status) = 0;

    { PyThreadState *_save; _save = PyEval_SaveThread();
    pid = wait(&status);
    PyEval_RestoreThread(_save); }
    if (pid == -1)
        return posix_error();

    return _Py_BuildValue_SizeT("Ni", PyLong_FromLong(pid), (status));
}




static char readlink__doc__[] = "readlink(path, *, dir_fd=None) -> path\n\nReturn a string representing the path to which the symbolic link points.\n\nIf dir_fd is not None, it should be a file descriptor open to a directory,\n  and path should be relative; path will then be relative to that directory.\ndir_fd may not be implemented on your platform.\n  If it is unavailable, using it will raise a NotImplementedError.";
# 7115 "posixmodule.c"
static PyObject *
posix_readlink(PyObject *self, PyObject *args, PyObject *kwargs)
{
    path_t path;
    int dir_fd = (-100);
    char buffer[1024];
    ssize_t length;
    PyObject *return_value = ((void *)0);
    static char *keywords[] = {"path", "dir_fd", ((void *)0)};

    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));
    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&|$O&:readlink", keywords,
                          path_converter, &path,



                          dir_fd_unavailable, &dir_fd

                          ))
        return ((void *)0);

    { PyThreadState *_save; _save = PyEval_SaveThread();





        length = readlink(path.narrow, buffer, sizeof(buffer));
    PyEval_RestoreThread(_save); }

    if (length < 0) {
        return_value = path_posix_error("readlink", &path);
        goto exit;
    }

    if (((((((PyObject*)(path.object))->ob_type))->tp_flags & ((1L<<28))) != 0))
        return_value = PyUnicode_DecodeFSDefaultAndSize(buffer, length);
    else
        return_value = PyBytes_FromStringAndSize(buffer, length);
exit:
    path_cleanup(&path);
    return return_value;
}






static char posix_symlink__doc__[] = "symlink(src, dst, target_is_directory=False, *, dir_fd=None)\n\nCreate a symbolic link pointing to src named dst.\n\ntarget_is_directory is required on Windows if the target is to be\n  interpreted as a directory.  (On Windows, symlink requires\n  Windows 6.0 or greater, and raises a NotImplementedError otherwise.)\n  target_is_directory is ignored on non-Windows platforms.\n\nIf dir_fd is not None, it should be a file descriptor open to a directory,\n  and path should be relative; path will then be relative to that directory.\ndir_fd may not be implemented on your platform.\n  If it is unavailable, using it will raise a NotImplementedError.";
# 7199 "posixmodule.c"
static PyObject *
posix_symlink(PyObject *self, PyObject *args, PyObject *kwargs)
{
    path_t src;
    path_t dst;
    int dir_fd = (-100);
    int target_is_directory = 0;
    static char *keywords[] = {"src", "dst", "target_is_directory",
                               "dir_fd", ((void *)0)};
    PyObject *return_value;



    int result;


    ((__builtin_object_size (&src, 0) != (size_t) -1) ? __builtin___memset_chk (&src, 0, sizeof(src), __builtin_object_size (&src, 0)) : __inline_memset_chk (&src, 0, sizeof(src)));
    src.argument_name = "src";
    ((__builtin_object_size (&dst, 0) != (size_t) -1) ? __builtin___memset_chk (&dst, 0, sizeof(dst), __builtin_object_size (&dst, 0)) : __inline_memset_chk (&dst, 0, sizeof(dst)));
    dst.argument_name = "dst";
# 7232 "posixmodule.c"
    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&O&|i$O&:symlink",
            keywords,
            path_converter, &src,
            path_converter, &dst,
            &target_is_directory,



            dir_fd_unavailable, &dir_fd

            ))
        return ((void *)0);

    if ((src.narrow && dst.wide) || (src.wide && dst.narrow)) {
        PyErr_SetString(PyExc_ValueError,
            "symlink: src and dst must be the same type");
        return_value = ((void *)0);
        goto exit;
    }
# 7269 "posixmodule.c"
    { PyThreadState *_save; _save = PyEval_SaveThread();





        result = symlink(src.narrow, dst.narrow);
    PyEval_RestoreThread(_save); }

    if (result) {
        return_value = path_error("symlink", &dst);
        goto exit;
    }


    return_value = (&_Py_NoneStruct);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    goto exit;
exit:
    path_cleanup(&src);
    path_cleanup(&dst);
    return return_value;
}
# 7372 "posixmodule.c"
static PyStructSequence_Field times_result_fields[] = {
    {"user", "user time"},
    {"system", "system time"},
    {"children_user", "user time of children"},
    {"children_system", "system time of children"},
    {"elapsed", "elapsed time since an arbitrary point in the past"},
    {((void *)0)}
};

static char times_result__doc__[] = "times_result: Result from os.times().\n\nThis object may be accessed either as a tuple of\n  (user, system, children_user, children_system, elapsed),\nor via the attributes user, system, children_user, children_system,\nand elapsed.\n\nSee os.times for more information.";
# 7390 "posixmodule.c"
static PyStructSequence_Desc times_result_desc = {
    "times_result",
    times_result__doc__,
    times_result_fields,
    5
};

static PyTypeObject TimesResultType;







static PyObject *
build_times_result(double user, double system,
    double children_user, double children_system,
    double elapsed)
{
    PyObject *value = PyStructSequence_New(&TimesResultType);
    if (value == ((void *)0))
        return ((void *)0);
# 7424 "posixmodule.c"
    { PyObject *o = PyFloat_FromDouble(user); if (!o) { do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); return ((void *)0); } (((PyTupleObject *)(value))->ob_item[0] = o); };
    { PyObject *o = PyFloat_FromDouble(system); if (!o) { do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); return ((void *)0); } (((PyTupleObject *)(value))->ob_item[1] = o); };
    { PyObject *o = PyFloat_FromDouble(children_user); if (!o) { do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); return ((void *)0); } (((PyTupleObject *)(value))->ob_item[2] = o); };
    { PyObject *o = PyFloat_FromDouble(children_system); if (!o) { do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); return ((void *)0); } (((PyTupleObject *)(value))->ob_item[3] = o); };
    { PyObject *o = PyFloat_FromDouble(elapsed); if (!o) { do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); return ((void *)0); } (((PyTupleObject *)(value))->ob_item[4] = o); };



    return value;
}

static char posix_times__doc__[] = "times() -> times_result\n\nReturn an object containing floating point numbers indicating process\ntimes.  The object behaves like a named tuple with these fields:\n  (utime, stime, cutime, cstime, elapsed_time)";
# 7489 "posixmodule.c"
static long ticks_per_second = -1;
static PyObject *
posix_times(PyObject *self, PyObject *noargs)
{
    struct tms t;
    clock_t c;
    (*__error()) = 0;
    c = times(&t);
    if (c == (clock_t) -1)
        return posix_error();
    return build_times_result(
                         (double)t.tms_utime / ticks_per_second,
                         (double)t.tms_stime / ticks_per_second,
                         (double)t.tms_cutime / ticks_per_second,
                         (double)t.tms_cstime / ticks_per_second,
                         (double)c / ticks_per_second);
}






static char posix_getsid__doc__[] = "getsid(pid) -> sid\n\nCall the system call getsid().";



static PyObject *
posix_getsid(PyObject *self, PyObject *args)
{
    pid_t pid;
    int sid;
    if (!_PyArg_ParseTuple_SizeT(args, "i" ":getsid", &pid))
        return ((void *)0);
    sid = getsid(pid);
    if (sid < 0)
        return posix_error();
    return PyLong_FromLong((long)sid);
}




static char posix_setsid__doc__[] = "setsid()\n\nCall the system call setsid().";



static PyObject *
posix_setsid(PyObject *self, PyObject *noargs)
{
    if (setsid() < 0)
        return posix_error();
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}



static char posix_setpgid__doc__[] = "setpgid(pid, pgrp)\n\nCall the system call setpgid().";



static PyObject *
posix_setpgid(PyObject *self, PyObject *args)
{
    pid_t pid;
    int pgrp;
    if (!_PyArg_ParseTuple_SizeT(args, "i" "i:setpgid", &pid, &pgrp))
        return ((void *)0);
    if (setpgid(pid, pgrp) < 0)
        return posix_error();
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}




static char posix_tcgetpgrp__doc__[] = "tcgetpgrp(fd) -> pgid\n\nReturn the process group associated with the terminal given by a fd.";



static PyObject *
posix_tcgetpgrp(PyObject *self, PyObject *args)
{
    int fd;
    pid_t pgid;
    if (!_PyArg_ParseTuple_SizeT(args, "i:tcgetpgrp", &fd))
        return ((void *)0);
    pgid = tcgetpgrp(fd);
    if (pgid < 0)
        return posix_error();
    return PyLong_FromLong(pgid);
}




static char posix_tcsetpgrp__doc__[] = "tcsetpgrp(fd, pgid)\n\nSet the process group associated with the terminal given by a fd.";



static PyObject *
posix_tcsetpgrp(PyObject *self, PyObject *args)
{
    int fd;
    pid_t pgid;
    if (!_PyArg_ParseTuple_SizeT(args, "i" "i" ":tcsetpgrp", &fd, &pgid))
        return ((void *)0);
    if (tcsetpgrp(fd, pgid) < 0)
        return posix_error();
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}




static char posix_open__doc__[] = "open(path, flags, mode=0o777, *, dir_fd=None)\n\nOpen a file for low level IO.  Returns a file handle (integer).\n\nIf dir_fd is not None, it should be a file descriptor open to a directory,\n  and path should be relative; path will then be relative to that directory.\ndir_fd may not be implemented on your platform.\n  If it is unavailable, using it will raise a NotImplementedError.";
# 7616 "posixmodule.c"
static PyObject *
posix_open(PyObject *self, PyObject *args, PyObject *kwargs)
{
    path_t path;
    int flags;
    int mode = 0777;
    int dir_fd = (-100);
    int fd;
    PyObject *return_value = ((void *)0);
    static char *keywords[] = {"path", "flags", "mode", "dir_fd", ((void *)0)};

    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));
    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&i|i$O&:open", keywords,
        path_converter, &path,
        &flags, &mode,



        dir_fd_unavailable, &dir_fd

        ))
        return ((void *)0);

    { PyThreadState *_save; _save = PyEval_SaveThread();
# 7650 "posixmodule.c"
        fd = open(path.narrow, flags, mode);
    PyEval_RestoreThread(_save); }

    if (fd == -1) {






        return_value = path_error("open", &path);
        goto exit;
    }

    return_value = PyLong_FromLong((long)fd);

exit:
    path_cleanup(&path);
    return return_value;
}

static char posix_close__doc__[] = "close(fd)\n\nClose a file descriptor (for low level IO).";



static PyObject *
posix_close(PyObject *self, PyObject *args)
{
    int fd, res;
    if (!_PyArg_ParseTuple_SizeT(args, "i:close", &fd))
        return ((void *)0);
    if (!(1))
        return posix_error();
    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = close(fd);
    PyEval_RestoreThread(_save); }
    if (res < 0)
        return posix_error();
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}


static char posix_closerange__doc__[] = "closerange(fd_low, fd_high)\n\nCloses all file descriptors in [fd_low, fd_high), ignoring errors.";



static PyObject *
posix_closerange(PyObject *self, PyObject *args)
{
    int fd_from, fd_to, i;
    if (!_PyArg_ParseTuple_SizeT(args, "ii:closerange", &fd_from, &fd_to))
        return ((void *)0);
    { PyThreadState *_save; _save = PyEval_SaveThread();
    for (i = fd_from; i < fd_to; i++)
        if ((1))
            close(i);
    PyEval_RestoreThread(_save); }
    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}


static char posix_dup__doc__[] = "dup(fd) -> fd2\n\nReturn a duplicate of a file descriptor.";



static PyObject *
posix_dup(PyObject *self, PyObject *args)
{
    int fd;
    if (!_PyArg_ParseTuple_SizeT(args, "i:dup", &fd))
        return ((void *)0);
    if (!(1))
        return posix_error();
    fd = dup(fd);
    if (fd < 0)
        return posix_error();
    return PyLong_FromLong((long)fd);
}


static char posix_dup2__doc__[] = "dup2(old_fd, new_fd)\n\nDuplicate file descriptor.";



static PyObject *
posix_dup2(PyObject *self, PyObject *args)
{
    int fd, fd2, res;
    if (!_PyArg_ParseTuple_SizeT(args, "ii:dup2", &fd, &fd2))
        return ((void *)0);
    if (!(1))
        return posix_error();
    res = dup2(fd, fd2);
    if (res < 0)
        return posix_error();
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}


static char posix_lockf__doc__[] = "lockf(fd, cmd, len)\n\nApply, test or remove a POSIX lock on an open file descriptor.\n\nfd is an open file descriptor.\ncmd specifies the command to use - one of F_LOCK, F_TLOCK, F_ULOCK or\nF_TEST.\nlen specifies the section of the file to lock.";







static PyObject *
posix_lockf(PyObject *self, PyObject *args)
{
    int fd, cmd, res;
    off_t len;
    if (!_PyArg_ParseTuple_SizeT(args, "iiO&:lockf",
            &fd, &cmd, _parse_off_t, &len))
        return ((void *)0);

    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = lockf(fd, cmd, len);
    PyEval_RestoreThread(_save); }

    if (res < 0)
        return posix_error();

    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}



static char posix_lseek__doc__[] = "lseek(fd, pos, how) -> newpos\n\nSet the current position of a file descriptor.\nReturn the new cursor position in bytes, starting from the beginning.";




static PyObject *
posix_lseek(PyObject *self, PyObject *args)
{
    int fd, how;



    off_t pos, res;

    PyObject *posobj;
    if (!_PyArg_ParseTuple_SizeT(args, "iOi:lseek", &fd, &posobj, &how))
        return ((void *)0);


    switch (how) {
    case 0: how = 0; break;
    case 1: how = 1; break;
    case 2: how = 2; break;
    }



    pos = PyLong_AsLong(posobj);



    if (PyErr_Occurred())
        return ((void *)0);

    if (!(1))
        return posix_error();
    { PyThreadState *_save; _save = PyEval_SaveThread();



    res = lseek(fd, pos, how);

    PyEval_RestoreThread(_save); }
    if (res < 0)
        return posix_error();


    return PyLong_FromLong(res);



}


static char posix_read__doc__[] = "read(fd, buffersize) -> string\n\nRead a file descriptor.";



static PyObject *
posix_read(PyObject *self, PyObject *args)
{
    int fd, size;
    Py_ssize_t n;
    PyObject *buffer;
    if (!_PyArg_ParseTuple_SizeT(args, "ii:read", &fd, &size))
        return ((void *)0);
    if (size < 0) {
        (*__error()) = 22;
        return posix_error();
    }
    buffer = PyBytes_FromStringAndSize((char *)((void *)0), size);
    if (buffer == ((void *)0))
        return ((void *)0);
    if (!(1)) {
        do { if ( --((PyObject*)(buffer))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(buffer)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(buffer)))); } while (0);
        return posix_error();
    }
    { PyThreadState *_save; _save = PyEval_SaveThread();
    n = read(fd, ((__builtin_expect(!(((((((PyObject*)(buffer))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "posixmodule.c", 7858, "PyBytes_Check(buffer)") : (void)0), (((PyBytesObject *)(buffer))->ob_sval)), size);
    PyEval_RestoreThread(_save); }
    if (n < 0) {
        do { if ( --((PyObject*)(buffer))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(buffer)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(buffer)))); } while (0);
        return posix_error();
    }
    if (n != size)
        _PyBytes_Resize(&buffer, n);
    return buffer;
}



static Py_ssize_t
iov_setup(struct iovec **iov, Py_buffer **buf, PyObject *seq, int cnt, int type)
{
    int i, j;
    Py_ssize_t blen, total = 0;

    *iov = ( ((size_t)(cnt) > ((Py_ssize_t)(((size_t)-1)>>1)) / sizeof(struct iovec)) ? ((void *)0) : ( (struct iovec *) PyMem_Malloc((cnt) * sizeof(struct iovec)) ) );
    if (*iov == ((void *)0)) {
        PyErr_NoMemory();
        return total;
    }

    *buf = ( ((size_t)(cnt) > ((Py_ssize_t)(((size_t)-1)>>1)) / sizeof(Py_buffer)) ? ((void *)0) : ( (Py_buffer *) PyMem_Malloc((cnt) * sizeof(Py_buffer)) ) );
    if (*buf == ((void *)0)) {
        PyMem_Free(*iov);
        PyErr_NoMemory();
        return total;
    }

    for (i = 0; i < cnt; i++) {
        PyObject *item = PySequence_GetItem(seq, i);
        if (item == ((void *)0))
            goto fail;
        if (PyObject_GetBuffer(item, &(*buf)[i], type) == -1) {
            do { if ( --((PyObject*)(item))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(item)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(item)))); } while (0);
            goto fail;
        }
        do { if ( --((PyObject*)(item))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(item)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(item)))); } while (0);
        (*iov)[i].iov_base = (*buf)[i].buf;
        blen = (*buf)[i].len;
        (*iov)[i].iov_len = blen;
        total += blen;
    }
    return total;

fail:
    PyMem_Free(*iov);
    for (j = 0; j < i; j++) {
        PyBuffer_Release(&(*buf)[j]);
    }
    PyMem_Free(*buf);
    return 0;
}

static void
iov_cleanup(struct iovec *iov, Py_buffer *buf, int cnt)
{
    int i;
    PyMem_Free(iov);
    for (i = 0; i < cnt; i++) {
        PyBuffer_Release(&buf[i]);
    }
    PyMem_Free(buf);
}



static char posix_readv__doc__[] = "readv(fd, buffers) -> bytesread\n\nRead from a file descriptor into a number of writable buffers. buffers\nis an arbitrary sequence of writable buffers.\nReturns the total number of bytes read.";





static PyObject *
posix_readv(PyObject *self, PyObject *args)
{
    int fd, cnt;
    Py_ssize_t n;
    PyObject *seq;
    struct iovec *iov;
    Py_buffer *buf;

    if (!_PyArg_ParseTuple_SizeT(args, "iO:readv", &fd, &seq))
        return ((void *)0);
    if (!PySequence_Check(seq)) {
        PyErr_SetString(PyExc_TypeError,
            "readv() arg 2 must be a sequence");
        return ((void *)0);
    }
    cnt = PySequence_Size(seq);

    if (!iov_setup(&iov, &buf, seq, cnt, 0x0001))
        return ((void *)0);

    { PyThreadState *_save; _save = PyEval_SaveThread();
    n = readv(fd, iov, cnt);
    PyEval_RestoreThread(_save); }

    iov_cleanup(iov, buf, cnt);
    return PyLong_FromSsize_t(n);
}



static char posix_pread__doc__[] = "pread(fd, buffersize, offset) -> string\n\nRead from a file descriptor, fd, at a position of offset. It will read up\nto buffersize number of bytes. The file offset remains unchanged.";




static PyObject *
posix_pread(PyObject *self, PyObject *args)
{
    int fd, size;
    off_t offset;
    Py_ssize_t n;
    PyObject *buffer;
    if (!_PyArg_ParseTuple_SizeT(args, "iiO&:pread", &fd, &size, _parse_off_t, &offset))
        return ((void *)0);

    if (size < 0) {
        (*__error()) = 22;
        return posix_error();
    }
    buffer = PyBytes_FromStringAndSize((char *)((void *)0), size);
    if (buffer == ((void *)0))
        return ((void *)0);
    if (!(1)) {
        do { if ( --((PyObject*)(buffer))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(buffer)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(buffer)))); } while (0);
        return posix_error();
    }
    { PyThreadState *_save; _save = PyEval_SaveThread();
    n = pread(fd, ((__builtin_expect(!(((((((PyObject*)(buffer))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "posixmodule.c", 7992, "PyBytes_Check(buffer)") : (void)0), (((PyBytesObject *)(buffer))->ob_sval)), size, offset);
    PyEval_RestoreThread(_save); }
    if (n < 0) {
        do { if ( --((PyObject*)(buffer))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(buffer)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(buffer)))); } while (0);
        return posix_error();
    }
    if (n != size)
        _PyBytes_Resize(&buffer, n);
    return buffer;
}


static char posix_write__doc__[] = "write(fd, string) -> byteswritten\n\nWrite a string to a file descriptor.";



static PyObject *
posix_write(PyObject *self, PyObject *args)
{
    Py_buffer pbuf;
    int fd;
    Py_ssize_t size, len;

    if (!_PyArg_ParseTuple_SizeT(args, "iy*:write", &fd, &pbuf))
        return ((void *)0);
    if (!(1)) {
        PyBuffer_Release(&pbuf);
        return posix_error();
    }
    len = pbuf.len;
    { PyThreadState *_save; _save = PyEval_SaveThread();





    size = write(fd, pbuf.buf, len);

    PyEval_RestoreThread(_save); }
    PyBuffer_Release(&pbuf);
    if (size < 0)
        return posix_error();
    return PyLong_FromSsize_t(size);
}


static char posix_sendfile__doc__[] = "sendfile(out, in, offset, nbytes) -> byteswritten\nsendfile(out, in, offset, nbytes, headers=None, trailers=None, flags=0)\n            -> byteswritten\nCopy nbytes bytes from file descriptor in to file descriptor out.";





static PyObject *
posix_sendfile(PyObject *self, PyObject *args, PyObject *kwdict)
{
    int in, out;
    Py_ssize_t ret;
    off_t offset;





    PyObject *headers = ((void *)0), *trailers = ((void *)0);
    Py_buffer *hbuf, *tbuf;
    off_t sbytes;
    struct sf_hdtr sf;
    int flags = 0;
    sf.headers = ((void *)0);
    sf.trailers = ((void *)0);
    static char *keywords[] = {"out", "in",
                                "offset", "count",
                                "headers", "trailers", "flags", ((void *)0)};


    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwdict, "iiO&O&|OOi:sendfile",
        keywords, &out, &in, _parse_off_t, &offset, _parse_off_t, &sbytes,




                &headers, &trailers, &flags))
            return ((void *)0);
    if (headers != ((void *)0)) {
        if (!PySequence_Check(headers)) {
            PyErr_SetString(PyExc_TypeError,
                "sendfile() headers must be a sequence or None");
            return ((void *)0);
        } else {
            Py_ssize_t i = 0;
            sf.hdr_cnt = PySequence_Size(headers);
            if (sf.hdr_cnt > 0 &&
                !(i = iov_setup(&(sf.headers), &hbuf,
                                headers, sf.hdr_cnt, 0)))
                return ((void *)0);

            sbytes += i;

        }
    }
    if (trailers != ((void *)0)) {
        if (!PySequence_Check(trailers)) {
            PyErr_SetString(PyExc_TypeError,
                "sendfile() trailers must be a sequence or None");
            return ((void *)0);
        } else {
            Py_ssize_t i = 0;
            sf.trl_cnt = PySequence_Size(trailers);
            if (sf.trl_cnt > 0 &&
                !(i = iov_setup(&(sf.trailers), &tbuf,
                                trailers, sf.trl_cnt, 0)))
                return ((void *)0);

            sbytes += i;

        }
    }

    { PyThreadState *_save; _save = PyEval_SaveThread();

    ret = sendfile(in, out, offset, &sbytes, &sf, flags);



    PyEval_RestoreThread(_save); }

    if (sf.headers != ((void *)0))
        iov_cleanup(sf.headers, hbuf, sf.hdr_cnt);
    if (sf.trailers != ((void *)0))
        iov_cleanup(sf.trailers, tbuf, sf.trl_cnt);

    if (ret < 0) {
        if (((*__error()) == 35) || ((*__error()) == 16)) {
            if (sbytes != 0) {

                goto done;
            }
            else {


                return posix_error();
            }
        }
        return posix_error();
    }
    goto done;

done:

        return _Py_BuildValue_SizeT("l", sbytes);
# 8173 "posixmodule.c"
}


static char posix_fstat__doc__[] = "fstat(fd) -> stat result\n\nLike stat(), but for an open file descriptor.\nEquivalent to stat(fd=fd).";




static PyObject *
posix_fstat(PyObject *self, PyObject *args)
{
    int fd;
    struct stat st;
    int res;
    if (!_PyArg_ParseTuple_SizeT(args, "i:fstat", &fd))
        return ((void *)0);




    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = fstat(fd, &st);
    PyEval_RestoreThread(_save); }
    if (res != 0) {



        return posix_error();

    }

    return _pystat_fromstructstat(&st);
}

static char posix_isatty__doc__[] = "isatty(fd) -> bool\n\nReturn True if the file descriptor 'fd' is an open file descriptor\nconnected to the slave end of a terminal.";




static PyObject *
posix_isatty(PyObject *self, PyObject *args)
{
    int fd;
    if (!_PyArg_ParseTuple_SizeT(args, "i:isatty", &fd))
        return ((void *)0);
    if (!(1))
        return PyBool_FromLong(0);
    return PyBool_FromLong(isatty(fd));
}


static char posix_pipe__doc__[] = "pipe() -> (read_end, write_end)\n\nCreate a pipe.";



static PyObject *
posix_pipe(PyObject *self, PyObject *noargs)
{
# 8242 "posixmodule.c"
    int fds[2];
    int res;
    res = pipe(fds);
    if (res != 0)
        return posix_error();
    return _Py_BuildValue_SizeT("(ii)", fds[0], fds[1]);
# 8260 "posixmodule.c"
}
# 8290 "posixmodule.c"
static char posix_writev__doc__[] = "writev(fd, buffers) -> byteswritten\n\nWrite the contents of buffers to a file descriptor, where buffers is an\narbitrary sequence of buffers.\nReturns the total bytes written.";





static PyObject *
posix_writev(PyObject *self, PyObject *args)
{
    int fd, cnt;
    Py_ssize_t res;
    PyObject *seq;
    struct iovec *iov;
    Py_buffer *buf;
    if (!_PyArg_ParseTuple_SizeT(args, "iO:writev", &fd, &seq))
        return ((void *)0);
    if (!PySequence_Check(seq)) {
        PyErr_SetString(PyExc_TypeError,
            "writev() arg 2 must be a sequence");
        return ((void *)0);
    }
    cnt = PySequence_Size(seq);

    if (!iov_setup(&iov, &buf, seq, cnt, 0)) {
        return ((void *)0);
    }

    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = writev(fd, iov, cnt);
    PyEval_RestoreThread(_save); }

    iov_cleanup(iov, buf, cnt);
    return PyLong_FromSsize_t(res);
}



static char posix_pwrite__doc__[] = "pwrite(fd, string, offset) -> byteswritten\n\nWrite string to a file descriptor, fd, from offset, leaving the file\noffset unchanged.";




static PyObject *
posix_pwrite(PyObject *self, PyObject *args)
{
    Py_buffer pbuf;
    int fd;
    off_t offset;
    Py_ssize_t size;

    if (!_PyArg_ParseTuple_SizeT(args, "iy*O&:pwrite", &fd, &pbuf, _parse_off_t, &offset))
        return ((void *)0);

    if (!(1)) {
        PyBuffer_Release(&pbuf);
        return posix_error();
    }
    { PyThreadState *_save; _save = PyEval_SaveThread();
    size = pwrite(fd, pbuf.buf, (size_t)pbuf.len, offset);
    PyEval_RestoreThread(_save); }
    PyBuffer_Release(&pbuf);
    if (size < 0)
        return posix_error();
    return PyLong_FromSsize_t(size);
}



static char posix_mkfifo__doc__[] = "mkfifo(path, mode=0o666, *, dir_fd=None)\n\nCreate a FIFO (a POSIX named pipe).\n\nIf dir_fd is not None, it should be a file descriptor open to a directory,\n  and path should be relative; path will then be relative to that directory.\ndir_fd may not be implemented on your platform.\n  If it is unavailable, using it will raise a NotImplementedError.";
# 8367 "posixmodule.c"
static PyObject *
posix_mkfifo(PyObject *self, PyObject *args, PyObject *kwargs)
{
    path_t path;
    int mode = 0666;
    int dir_fd = (-100);
    int result;
    PyObject *return_value = ((void *)0);
    static char *keywords[] = {"path", "mode", "dir_fd", ((void *)0)};

    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));
    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&|i$O&:mkfifo", keywords,
        path_converter, &path,
        &mode,



        dir_fd_unavailable, &dir_fd

        ))
        return ((void *)0);

    { PyThreadState *_save; _save = PyEval_SaveThread();





        result = mkfifo(path.narrow, mode);
    PyEval_RestoreThread(_save); }

    if (result < 0) {
        return_value = posix_error();
        goto exit;
    }

    return_value = (&_Py_NoneStruct);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);

exit:
    path_cleanup(&path);
    return return_value;
}



static char posix_mknod__doc__[] = "mknod(filename, mode=0o600, device=0, *, dir_fd=None)\n\nCreate a filesystem node (file, device special file or named pipe)\nnamed filename. mode specifies both the permissions to use and the\ntype of node to be created, being combined (bitwise OR) with one of\nS_IFREG, S_IFCHR, S_IFBLK, and S_IFIFO. For S_IFCHR and S_IFBLK,\ndevice defines the newly created device special file (probably using\nos.makedev()), otherwise it is ignored.\n\nIf dir_fd is not None, it should be a file descriptor open to a directory,\n  and path should be relative; path will then be relative to that directory.\ndir_fd may not be implemented on your platform.\n  If it is unavailable, using it will raise a NotImplementedError.";
# 8428 "posixmodule.c"
static PyObject *
posix_mknod(PyObject *self, PyObject *args, PyObject *kwargs)
{
    path_t path;
    int mode = 0666;
    int device = 0;
    int dir_fd = (-100);
    int result;
    PyObject *return_value = ((void *)0);
    static char *keywords[] = {"path", "mode", "device", "dir_fd", ((void *)0)};

    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));
    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&|ii$O&:mknod", keywords,
        path_converter, &path,
        &mode, &device,



        dir_fd_unavailable, &dir_fd

        ))
        return ((void *)0);

    { PyThreadState *_save; _save = PyEval_SaveThread();





        result = mknod(path.narrow, mode, device);
    PyEval_RestoreThread(_save); }

    if (result < 0) {
        return_value = posix_error();
        goto exit;
    }

    return_value = (&_Py_NoneStruct);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);

exit:
    path_cleanup(&path);
    return return_value;
}



static char posix_major__doc__[] = "major(device) -> major number\nExtracts a device major number from a raw device number.";



static PyObject *
posix_major(PyObject *self, PyObject *args)
{
    int device;
    if (!_PyArg_ParseTuple_SizeT(args, "i:major", &device))
        return ((void *)0);
    return PyLong_FromLong((long)((int32_t)(((u_int32_t)(device) >> 24) & 0xff)));
}

static char posix_minor__doc__[] = "minor(device) -> minor number\nExtracts a device minor number from a raw device number.";



static PyObject *
posix_minor(PyObject *self, PyObject *args)
{
    int device;
    if (!_PyArg_ParseTuple_SizeT(args, "i:minor", &device))
        return ((void *)0);
    return PyLong_FromLong((long)((int32_t)((device) & 0xffffff)));
}

static char posix_makedev__doc__[] = "makedev(major, minor) -> device number\nComposes a raw device number from the major and minor device numbers.";



static PyObject *
posix_makedev(PyObject *self, PyObject *args)
{
    int major, minor;
    if (!_PyArg_ParseTuple_SizeT(args, "ii:makedev", &major, &minor))
        return ((void *)0);
    return PyLong_FromLong((long)((dev_t)(((major) << 24) | (minor))));
}




static char posix_ftruncate__doc__[] = "ftruncate(fd, length)\n\nTruncate a file to a specified length.";



static PyObject *
posix_ftruncate(PyObject *self, PyObject *args)
{
    int fd;
    off_t length;
    int res;

    if (!_PyArg_ParseTuple_SizeT(args, "iO&:ftruncate", &fd, _parse_off_t, &length))
        return ((void *)0);

    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = ftruncate(fd, length);
    PyEval_RestoreThread(_save); }
    if (res < 0)
        return posix_error();
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}



static char posix_truncate__doc__[] = "truncate(path, length)\n\nTruncate the file given by path to length bytes.\nOn some platforms, path may also be specified as an open file descriptor.\n  If this functionality is unavailable, using it raises an exception.";





static PyObject *
posix_truncate(PyObject *self, PyObject *args, PyObject *kwargs)
{
    path_t path;
    off_t length;
    int res;
    PyObject *result = ((void *)0);
    static char *keywords[] = {"path", "length", ((void *)0)};

    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));

    path.allow_fd = 1;

    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&O&:truncate", keywords,
                                     path_converter, &path,
                                     _parse_off_t, &length))
        return ((void *)0);

    { PyThreadState *_save; _save = PyEval_SaveThread();

    if (path.fd != -1)
        res = ftruncate(path.fd, length);
    else

        res = truncate(path.narrow, length);
    PyEval_RestoreThread(_save); }
    if (res < 0)
        result = path_posix_error("truncate", &path);
    else {
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        result = (&_Py_NoneStruct);
    }
    path_cleanup(&path);
    return result;
}
# 8645 "posixmodule.c"
static char posix_putenv__doc__[] = "putenv(key, value)\n\nChange or add an environment variable.";





static PyObject *posix_putenv_garbage;

static PyObject *
posix_putenv(PyObject *self, PyObject *args)
{
    PyObject *newstr = ((void *)0);
# 8686 "posixmodule.c"
    PyObject *os1, *os2;
    char *s1, *s2;
    char *newenv;

    if (!_PyArg_ParseTuple_SizeT(args,
                          "O&O&:putenv",
                          PyUnicode_FSConverter, &os1,
                          PyUnicode_FSConverter, &os2))
        return ((void *)0);
    s1 = PyBytes_AsString(os1);
    s2 = PyBytes_AsString(os2);

    newstr = PyBytes_FromFormat("%s=%s", s1, s2);
    if (newstr == ((void *)0)) {
        PyErr_NoMemory();
        goto error;
    }

    newenv = ((__builtin_expect(!(((((((PyObject*)(newstr))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "posixmodule.c", 8704, "PyBytes_Check(newstr)") : (void)0), (((PyBytesObject *)(newstr))->ob_sval));
    if (putenv(newenv)) {
        posix_error();
        goto error;
    }






    if (PyDict_SetItem(posix_putenv_garbage, os1, newstr)) {

        PyErr_Clear();
    }
    else {
        do { if ( --((PyObject*)(newstr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(newstr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(newstr)))); } while (0);
    }


    do { if ( --((PyObject*)(os1))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(os1)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(os1)))); } while (0);
    do { if ( --((PyObject*)(os2))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(os2)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(os2)))); } while (0);

    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);

error:

    do { if ( --((PyObject*)(os1))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(os1)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(os1)))); } while (0);
    do { if ( --((PyObject*)(os2))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(os2)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(os2)))); } while (0);

    do { if ((newstr) == ((void *)0)) ; else do { if ( --((PyObject*)(newstr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(newstr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(newstr)))); } while (0); } while (0);
    return ((void *)0);
}



static char posix_unsetenv__doc__[] = "unsetenv(key)\n\nDelete an environment variable.";



static PyObject *
posix_unsetenv(PyObject *self, PyObject *args)
{
    PyObject *name;

    int err;


    if (!_PyArg_ParseTuple_SizeT(args, "O&:unsetenv",

                          PyUnicode_FSConverter, &name))
        return ((void *)0);




    err = unsetenv(((__builtin_expect(!(((((((PyObject*)(name))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "posixmodule.c", 8760, "PyBytes_Check(name)") : (void)0), (((PyBytesObject *)(name))->ob_sval)));
    if (err) {
        do { if ( --((PyObject*)(name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(name)))); } while (0);
        return posix_error();
    }







    if (PyDict_DelItem(posix_putenv_garbage, name)) {

        PyErr_Clear();
    }
    do { if ( --((PyObject*)(name))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(name)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(name)))); } while (0);
    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}


static char posix_strerror__doc__[] = "strerror(code) -> string\n\nTranslate an error code to a message string.";



static PyObject *
posix_strerror(PyObject *self, PyObject *args)
{
    int code;
    char *message;
    if (!_PyArg_ParseTuple_SizeT(args, "i:strerror", &code))
        return ((void *)0);
    message = strerror(code);
    if (message == ((void *)0)) {
        PyErr_SetString(PyExc_ValueError,
                        "strerror() argument out of range");
        return ((void *)0);
    }
    return PyUnicode_DecodeLocale(message, "surrogateescape");
}





static char posix_WCOREDUMP__doc__[] = "WCOREDUMP(status) -> bool\n\nReturn True if the process returning 'status' was dumped to a core file.";



static PyObject *
posix_WCOREDUMP(PyObject *self, PyObject *args)
{
    int status;
    (status) = 0;

    if (!_PyArg_ParseTuple_SizeT(args, "i:WCOREDUMP", &(status)))
        return ((void *)0);

    return PyBool_FromLong(((*(int *)&(status)) & 0200));
}



static char posix_WIFCONTINUED__doc__[] = "WIFCONTINUED(status) -> bool\n\nReturn True if the process returning 'status' was continued from a\njob control stop.";




static PyObject *
posix_WIFCONTINUED(PyObject *self, PyObject *args)
{
    int status;
    (status) = 0;

    if (!_PyArg_ParseTuple_SizeT(args, "i:WCONTINUED", &(status)))
        return ((void *)0);

    return PyBool_FromLong((((*(int *)&(status)) & 0177) == 0177 && ((*(int *)&(status)) >> 8) == 0x13));
}



static char posix_WIFSTOPPED__doc__[] = "WIFSTOPPED(status) -> bool\n\nReturn True if the process returning 'status' was stopped.";



static PyObject *
posix_WIFSTOPPED(PyObject *self, PyObject *args)
{
    int status;
    (status) = 0;

    if (!_PyArg_ParseTuple_SizeT(args, "i:WIFSTOPPED", &(status)))
        return ((void *)0);

    return PyBool_FromLong((((*(int *)&(status)) & 0177) == 0177 && ((*(int *)&(status)) >> 8) != 0x13));
}



static char posix_WIFSIGNALED__doc__[] = "WIFSIGNALED(status) -> bool\n\nReturn True if the process returning 'status' was terminated by a signal.";



static PyObject *
posix_WIFSIGNALED(PyObject *self, PyObject *args)
{
    int status;
    (status) = 0;

    if (!_PyArg_ParseTuple_SizeT(args, "i:WIFSIGNALED", &(status)))
        return ((void *)0);

    return PyBool_FromLong((((*(int *)&(status)) & 0177) != 0177 && ((*(int *)&(status)) & 0177) != 0));
}



static char posix_WIFEXITED__doc__[] = "WIFEXITED(status) -> bool\n\nReturn true if the process returning 'status' exited using the exit()\nsystem call.";




static PyObject *
posix_WIFEXITED(PyObject *self, PyObject *args)
{
    int status;
    (status) = 0;

    if (!_PyArg_ParseTuple_SizeT(args, "i:WIFEXITED", &(status)))
        return ((void *)0);

    return PyBool_FromLong((((*(int *)&(status)) & 0177) == 0));
}



static char posix_WEXITSTATUS__doc__[] = "WEXITSTATUS(status) -> integer\n\nReturn the process return code from 'status'.";



static PyObject *
posix_WEXITSTATUS(PyObject *self, PyObject *args)
{
    int status;
    (status) = 0;

    if (!_PyArg_ParseTuple_SizeT(args, "i:WEXITSTATUS", &(status)))
        return ((void *)0);

    return _Py_BuildValue_SizeT("i", (((*(int *)&(status)) >> 8) & 0x000000ff));
}



static char posix_WTERMSIG__doc__[] = "WTERMSIG(status) -> integer\n\nReturn the signal that terminated the process that provided the 'status'\nvalue.";




static PyObject *
posix_WTERMSIG(PyObject *self, PyObject *args)
{
    int status;
    (status) = 0;

    if (!_PyArg_ParseTuple_SizeT(args, "i:WTERMSIG", &(status)))
        return ((void *)0);

    return _Py_BuildValue_SizeT("i", (((*(int *)&(status)) & 0177)));
}



static char posix_WSTOPSIG__doc__[] = "WSTOPSIG(status) -> integer\n\nReturn the signal that stopped the process that provided\nthe 'status' value.";




static PyObject *
posix_WSTOPSIG(PyObject *self, PyObject *args)
{
    int status;
    (status) = 0;

    if (!_PyArg_ParseTuple_SizeT(args, "i:WSTOPSIG", &(status)))
        return ((void *)0);

    return _Py_BuildValue_SizeT("i", ((*(int *)&(status)) >> 8));
}
# 8961 "posixmodule.c"
# 1 "/usr/include/sys/statvfs.h" 1 3 4
# 44 "/usr/include/sys/statvfs.h" 3 4
struct statvfs {
 unsigned long f_bsize;
 unsigned long f_frsize;
 fsblkcnt_t f_blocks;
 fsblkcnt_t f_bfree;
 fsblkcnt_t f_bavail;
 fsfilcnt_t f_files;
 fsfilcnt_t f_ffree;
 fsfilcnt_t f_favail;
 unsigned long f_fsid;
 unsigned long f_flag;
 unsigned long f_namemax;
};






int fstatvfs(int, struct statvfs *);
int statvfs(const char * , struct statvfs * );

# 8962 "posixmodule.c" 2

static PyObject*
_pystatvfs_fromstructstatvfs(struct statvfs st) {
    PyObject *v = PyStructSequence_New(&StatVFSResultType);
    if (v == ((void *)0))
        return ((void *)0);


    (((PyTupleObject *)(v))->ob_item[0] = PyLong_FromLong((long) st.f_bsize));
    (((PyTupleObject *)(v))->ob_item[1] = PyLong_FromLong((long) st.f_frsize));
    (((PyTupleObject *)(v))->ob_item[2] = PyLong_FromLong((long) st.f_blocks));
    (((PyTupleObject *)(v))->ob_item[3] = PyLong_FromLong((long) st.f_bfree));
    (((PyTupleObject *)(v))->ob_item[4] = PyLong_FromLong((long) st.f_bavail));
    (((PyTupleObject *)(v))->ob_item[5] = PyLong_FromLong((long) st.f_files));
    (((PyTupleObject *)(v))->ob_item[6] = PyLong_FromLong((long) st.f_ffree));
    (((PyTupleObject *)(v))->ob_item[7] = PyLong_FromLong((long) st.f_favail));
    (((PyTupleObject *)(v))->ob_item[8] = PyLong_FromLong((long) st.f_flag));
    (((PyTupleObject *)(v))->ob_item[9] = PyLong_FromLong((long) st.f_namemax));
# 8999 "posixmodule.c"
    return v;
}

static char posix_fstatvfs__doc__[] = "fstatvfs(fd) -> statvfs result\n\nPerform an fstatvfs system call on the given fd.\nEquivalent to statvfs(fd).";




static PyObject *
posix_fstatvfs(PyObject *self, PyObject *args)
{
    int fd, res;
    struct statvfs st;

    if (!_PyArg_ParseTuple_SizeT(args, "i:fstatvfs", &fd))
        return ((void *)0);
    { PyThreadState *_save; _save = PyEval_SaveThread();
    res = fstatvfs(fd, &st);
    PyEval_RestoreThread(_save); }
    if (res != 0)
        return posix_error();

    return _pystatvfs_fromstructstatvfs(st);
}






static char posix_statvfs__doc__[] = "statvfs(path)\n\nPerform a statvfs system call on the given path.\n\npath may always be specified as a string.\nOn some platforms, path may also be specified as an open file descriptor.\n  If this functionality is unavailable, using it raises an exception.";







static PyObject *
posix_statvfs(PyObject *self, PyObject *args, PyObject *kwargs)
{
    static char *keywords[] = {"path", ((void *)0)};
    path_t path;
    int result;
    PyObject *return_value = ((void *)0);
    struct statvfs st;

    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));

    path.allow_fd = 1;

    if (!_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&:statvfs", keywords,
        path_converter, &path
        ))
        return ((void *)0);

    { PyThreadState *_save; _save = PyEval_SaveThread();

    if (path.fd != -1) {


        if (fstatvfs == ((void *)0)) {
            fd_specified("statvfs", path.fd);
            goto exit;
        }

        result = fstatvfs(path.fd, &st);
    }
    else

        result = statvfs(path.narrow, &st);
    PyEval_RestoreThread(_save); }

    if (result) {
        return_value = path_posix_error("statvfs", &path);
        goto exit;
    }

    return_value = _pystatvfs_fromstructstatvfs(st);

exit:
    path_cleanup(&path);
    return return_value;
}
# 9122 "posixmodule.c"
struct constdef {
    char *name;
    long value;
};

static int
conv_confname(PyObject *arg, int *valuep, struct constdef *table,
              size_t tablesize)
{
    if (((((((PyObject*)(arg))->ob_type))->tp_flags & ((1L<<24))) != 0)) {
        *valuep = PyLong_AsLong(arg);
        return 1;
    }
    else {

        size_t lo = 0;
        size_t mid;
        size_t hi = tablesize;
        int cmp;
        const char *confname;
        if (!((((((PyObject*)(arg))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
            PyErr_SetString(PyExc_TypeError,
                "configuration names must be strings or integers");
            return 0;
        }
        confname = PyUnicode_AsUTF8(arg);
        if (confname == ((void *)0))
            return 0;
        while (lo < hi) {
            mid = (lo + hi) / 2;
            cmp = strcmp(confname, table[mid].name);
            if (cmp < 0)
                hi = mid;
            else if (cmp > 0)
                lo = mid + 1;
            else {
                *valuep = table[mid].value;
                return 1;
            }
        }
        PyErr_SetString(PyExc_ValueError, "unrecognized configuration name");
        return 0;
    }
}



static struct constdef posix_constants_pathconf[] = {







    {"PC_ASYNC_IO", 17},


    {"PC_CHOWN_RESTRICTED", 7},


    {"PC_FILESIZEBITS", 18},





    {"PC_LINK_MAX", 1},


    {"PC_MAX_CANON", 2},


    {"PC_MAX_INPUT", 3},


    {"PC_NAME_MAX", 4},


    {"PC_NO_TRUNC", 8},


    {"PC_PATH_MAX", 5},


    {"PC_PIPE_BUF", 6},


    {"PC_PRIO_IO", 19},





    {"PC_SYNC_IO", 25},


    {"PC_VDISABLE", 9},
# 9228 "posixmodule.c"
    {"PC_ALLOC_SIZE_MIN", 16},


    {"PC_REC_INCR_XFER_SIZE", 20},


    {"PC_REC_MAX_XFER_SIZE", 21},


    {"PC_REC_MIN_XFER_SIZE", 22},


    {"PC_REC_XFER_ALIGN", 23},


    {"PC_SYMLINK_MAX", 24},
# 9254 "posixmodule.c"
};

static int
conv_path_confname(PyObject *arg, int *valuep)
{
    return conv_confname(arg, valuep, posix_constants_pathconf,
                         sizeof(posix_constants_pathconf)
                           / sizeof(struct constdef));
}



static char posix_fpathconf__doc__[] = "fpathconf(fd, name) -> integer\n\nReturn the configuration limit name for the file descriptor fd.\nIf there is no limit, return -1.";




static PyObject *
posix_fpathconf(PyObject *self, PyObject *args)
{
    PyObject *result = ((void *)0);
    int name, fd;

    if (_PyArg_ParseTuple_SizeT(args, "iO&:fpathconf", &fd,
                         conv_path_confname, &name)) {
        long limit;

        (*__error()) = 0;
        limit = fpathconf(fd, name);
        if (limit == -1 && (*__error()) != 0)
            posix_error();
        else
            result = PyLong_FromLong(limit);
    }
    return result;
}




static char posix_pathconf__doc__[] = "pathconf(path, name) -> integer\n\nReturn the configuration limit name for the file or directory path.\nIf there is no limit, return -1.\nOn some platforms, path may also be specified as an open file descriptor.\n  If this functionality is unavailable, using it raises an exception.";






static PyObject *
posix_pathconf(PyObject *self, PyObject *args, PyObject *kwargs)
{
    path_t path;
    PyObject *result = ((void *)0);
    int name;
    static char *keywords[] = {"path", "name", ((void *)0)};

    ((__builtin_object_size (&path, 0) != (size_t) -1) ? __builtin___memset_chk (&path, 0, sizeof(path), __builtin_object_size (&path, 0)) : __inline_memset_chk (&path, 0, sizeof(path)));

    path.allow_fd = 1;

    if (_PyArg_ParseTupleAndKeywords_SizeT(args, kwargs, "O&O&:pathconf", keywords,
                                    path_converter, &path,
                                    conv_path_confname, &name)) {
    long limit;

    (*__error()) = 0;

    if (path.fd != -1)
        limit = fpathconf(path.fd, name);
    else

        limit = pathconf(path.narrow, name);
    if (limit == -1 && (*__error()) != 0) {
        if ((*__error()) == 22)

            posix_error();
        else
            result = path_posix_error("pathconf", &path);
    }
    else
        result = PyLong_FromLong(limit);
    }
    path_cleanup(&path);
    return result;
}



static struct constdef posix_constants_confstr[] = {
# 9391 "posixmodule.c"
    {"CS_PATH", 1},
# 9406 "posixmodule.c"
    {"CS_XBS5_ILP32_OFF32_CFLAGS", 20},


    {"CS_XBS5_ILP32_OFF32_LDFLAGS", 21},


    {"CS_XBS5_ILP32_OFF32_LIBS", 22},


    {"CS_XBS5_ILP32_OFF32_LINTFLAGS", 23},


    {"CS_XBS5_ILP32_OFFBIG_CFLAGS", 24},


    {"CS_XBS5_ILP32_OFFBIG_LDFLAGS", 25},


    {"CS_XBS5_ILP32_OFFBIG_LIBS", 26},


    {"CS_XBS5_ILP32_OFFBIG_LINTFLAGS", 27},


    {"CS_XBS5_LP64_OFF64_CFLAGS", 28},


    {"CS_XBS5_LP64_OFF64_LDFLAGS", 29},


    {"CS_XBS5_LP64_OFF64_LIBS", 30},


    {"CS_XBS5_LP64_OFF64_LINTFLAGS", 31},


    {"CS_XBS5_LPBIG_OFFBIG_CFLAGS", 32},


    {"CS_XBS5_LPBIG_OFFBIG_LDFLAGS", 33},


    {"CS_XBS5_LPBIG_OFFBIG_LIBS", 34},


    {"CS_XBS5_LPBIG_OFFBIG_LINTFLAGS", 35},
# 9492 "posixmodule.c"
};

static int
conv_confstr_confname(PyObject *arg, int *valuep)
{
    return conv_confname(arg, valuep, posix_constants_confstr,
                         sizeof(posix_constants_confstr)
                           / sizeof(struct constdef));
}

static char posix_confstr__doc__[] = "confstr(name) -> string\n\nReturn a string-valued system configuration variable.";



static PyObject *
posix_confstr(PyObject *self, PyObject *args)
{
    PyObject *result = ((void *)0);
    int name;
    char buffer[255];
    int len;

    if (!_PyArg_ParseTuple_SizeT(args, "O&:confstr", conv_confstr_confname, &name))
        return ((void *)0);

    (*__error()) = 0;
    len = confstr(name, buffer, sizeof(buffer));
    if (len == 0) {
        if ((*__error())) {
            posix_error();
            return ((void *)0);
        }
        else {
            return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
        }
    }

    if ((unsigned int)len >= sizeof(buffer)) {
        char *buf = PyMem_Malloc(len);
        if (buf == ((void *)0))
            return PyErr_NoMemory();
        confstr(name, buf, len);
        result = PyUnicode_DecodeFSDefaultAndSize(buf, len-1);
        PyMem_Free(buf);
    }
    else
        result = PyUnicode_DecodeFSDefaultAndSize(buffer, len-1);
    return result;
}




static struct constdef posix_constants_sysconf[] = {

    {"SC_2_CHAR_TERM", 20},


    {"SC_2_C_BIND", 18},


    {"SC_2_C_DEV", 19},





    {"SC_2_FORT_DEV", 21},


    {"SC_2_FORT_RUN", 22},


    {"SC_2_LOCALEDEF", 23},


    {"SC_2_SW_DEV", 24},


    {"SC_2_UPE", 25},


    {"SC_2_VERSION", 17},
# 9583 "posixmodule.c"
    {"SC_AIO_LISTIO_MAX", 42},


    {"SC_AIO_MAX", 43},


    {"SC_AIO_PRIO_DELTA_MAX", 44},


    {"SC_ARG_MAX", 1},


    {"SC_ASYNCHRONOUS_IO", 28},


    {"SC_ATEXIT_MAX", 107},
# 9607 "posixmodule.c"
    {"SC_BC_BASE_MAX", 9},


    {"SC_BC_DIM_MAX", 10},


    {"SC_BC_SCALE_MAX", 11},


    {"SC_BC_STRING_MAX", 12},
# 9634 "posixmodule.c"
    {"SC_CHILD_MAX", 2},


    {"SC_CLK_TCK", 3},





    {"SC_COLL_WEIGHTS_MAX", 13},
# 9661 "posixmodule.c"
    {"SC_DELAYTIMER_MAX", 45},





    {"SC_EXPR_NEST_MAX", 14},


    {"SC_FSYNC", 38},


    {"SC_GETGR_R_SIZE_MAX", 70},


    {"SC_GETPW_R_SIZE_MAX", 71},
# 9700 "posixmodule.c"
    {"SC_IOV_MAX", 56},





    {"SC_JOB_CONTROL", 6},
# 9715 "posixmodule.c"
    {"SC_LINE_MAX", 15},


    {"SC_LOGIN_NAME_MAX", 73},
# 9730 "posixmodule.c"
    {"SC_MAPPED_FILES", 47},
# 9739 "posixmodule.c"
    {"SC_MEMLOCK", 30},


    {"SC_MEMLOCK_RANGE", 31},


    {"SC_MEMORY_PROTECTION", 32},


    {"SC_MESSAGE_PASSING", 33},





    {"SC_MQ_OPEN_MAX", 46},


    {"SC_MQ_PRIO_MAX", 75},





    {"SC_NGROUPS_MAX", 4},
# 9784 "posixmodule.c"
    {"SC_NPROCESSORS_CONF", 57},


    {"SC_NPROCESSORS_ONLN", 58},
# 9799 "posixmodule.c"
    {"SC_OPEN_MAX", 5},


    {"SC_PAGESIZE", 29},


    {"SC_PAGE_SIZE", 29},


    {"SC_PASS_MAX", 131},
# 9847 "posixmodule.c"
    {"SC_PRIORITIZED_IO", 34},


    {"SC_PRIORITY_SCHEDULING", 35},


    {"SC_REALTIME_SIGNALS", 36},


    {"SC_RE_DUP_MAX", 16},


    {"SC_RTSIG_MAX", 48},


    {"SC_SAVED_IDS", 7},
# 9874 "posixmodule.c"
    {"SC_SEMAPHORES", 37},


    {"SC_SEM_NSEMS_MAX", 49},


    {"SC_SEM_VALUE_MAX", 50},


    {"SC_SHARED_MEMORY_OBJECTS", 39},
# 9892 "posixmodule.c"
    {"SC_SIGQUEUE_MAX", 51},
# 9913 "posixmodule.c"
    {"SC_STREAM_MAX", 26},


    {"SC_SYNCHRONIZED_IO", 40},


    {"SC_THREADS", 96},


    {"SC_THREAD_ATTR_STACKADDR", 82},


    {"SC_THREAD_ATTR_STACKSIZE", 83},


    {"SC_THREAD_DESTRUCTOR_ITERATIONS", 85},


    {"SC_THREAD_KEYS_MAX", 86},


    {"SC_THREAD_PRIORITY_SCHEDULING", 89},


    {"SC_THREAD_PRIO_INHERIT", 87},


    {"SC_THREAD_PRIO_PROTECT", 88},


    {"SC_THREAD_PROCESS_SHARED", 90},


    {"SC_THREAD_SAFE_FUNCTIONS", 91},


    {"SC_THREAD_STACK_MIN", 93},


    {"SC_THREAD_THREADS_MAX", 94},


    {"SC_TIMERS", 41},


    {"SC_TIMER_MAX", 52},


    {"SC_TTY_NAME_MAX", 101},


    {"SC_TZNAME_MAX", 27},
# 9985 "posixmodule.c"
    {"SC_VERSION", 8},





    {"SC_XBS5_ILP32_OFF32", 122},


    {"SC_XBS5_ILP32_OFFBIG", 123},


    {"SC_XBS5_LP64_OFF64", 124},


    {"SC_XBS5_LPBIG_OFFBIG", 125},


    {"SC_XOPEN_CRYPT", 108},


    {"SC_XOPEN_ENH_I18N", 109},


    {"SC_XOPEN_LEGACY", 110},


    {"SC_XOPEN_REALTIME", 111},


    {"SC_XOPEN_REALTIME_THREADS", 112},


    {"SC_XOPEN_SHM", 113},


    {"SC_XOPEN_UNIX", 115},


    {"SC_XOPEN_VERSION", 116},


    {"SC_XOPEN_XCU_VERSION", 121},
# 10038 "posixmodule.c"
};

static int
conv_sysconf_confname(PyObject *arg, int *valuep)
{
    return conv_confname(arg, valuep, posix_constants_sysconf,
                         sizeof(posix_constants_sysconf)
                           / sizeof(struct constdef));
}

static char posix_sysconf__doc__[] = "sysconf(name) -> integer\n\nReturn an integer-valued system configuration variable.";



static PyObject *
posix_sysconf(PyObject *self, PyObject *args)
{
    PyObject *result = ((void *)0);
    int name;

    if (_PyArg_ParseTuple_SizeT(args, "O&:sysconf", conv_sysconf_confname, &name)) {
        int value;

        (*__error()) = 0;
        value = sysconf(name);
        if (value == -1 && (*__error()) != 0)
            posix_error();
        else
            result = PyLong_FromLong(value);
    }
    return result;
}
# 10083 "posixmodule.c"
static int
cmp_constdefs(const void *v1, const void *v2)
{
    const struct constdef *c1 =
    (const struct constdef *) v1;
    const struct constdef *c2 =
    (const struct constdef *) v2;

    return strcmp(c1->name, c2->name);
}

static int
setup_confname_table(struct constdef *table, size_t tablesize,
                     char *tablename, PyObject *module)
{
    PyObject *d = ((void *)0);
    size_t i;

    qsort(table, tablesize, sizeof(struct constdef), cmp_constdefs);
    d = PyDict_New();
    if (d == ((void *)0))
        return -1;

    for (i=0; i < tablesize; ++i) {
        PyObject *o = PyLong_FromLong(table[i].value);
        if (o == ((void *)0) || PyDict_SetItemString(d, table[i].name, o) == -1) {
            do { if ((o) == ((void *)0)) ; else do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0); } while (0);
            do { if ( --((PyObject*)(d))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(d)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(d)))); } while (0);
            return -1;
        }
        do { if ( --((PyObject*)(o))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(o)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(o)))); } while (0);
    }
    return PyModule_AddObject(module, tablename, d);
}


static int
setup_confname_tables(PyObject *module)
{

    if (setup_confname_table(posix_constants_pathconf,
                             sizeof(posix_constants_pathconf)
                               / sizeof(struct constdef),
                             "pathconf_names", module))
        return -1;


    if (setup_confname_table(posix_constants_confstr,
                             sizeof(posix_constants_confstr)
                               / sizeof(struct constdef),
                             "confstr_names", module))
        return -1;


    if (setup_confname_table(posix_constants_sysconf,
                             sizeof(posix_constants_sysconf)
                               / sizeof(struct constdef),
                             "sysconf_names", module))
        return -1;

    return 0;
}


static char posix_abort__doc__[] = "abort() -> does not return!\n\nAbort the interpreter immediately.  This 'dumps core' or otherwise fails\nin the hardest way possible on the hosting operating system.";




static PyObject *
posix_abort(PyObject *self, PyObject *noargs)
{
    abort();

    Py_FatalError("abort() called from Python code didn't abort!");
    return ((void *)0);
}
# 10257 "posixmodule.c"
static char posix_getloadavg__doc__[] = "getloadavg() -> (float, float, float)\n\nReturn the number of processes in the system run queue averaged over\nthe last 1, 5, and 15 minutes or raises OSError if the load average\nwas unobtainable";





static PyObject *
posix_getloadavg(PyObject *self, PyObject *noargs)
{
    double loadavg[3];
    if (getloadavg(loadavg, 3)!=3) {
        PyErr_SetString(PyExc_OSError, "Load averages are unobtainable");
        return ((void *)0);
    } else
        return _Py_BuildValue_SizeT("ddd", loadavg[0], loadavg[1], loadavg[2]);
}


static char device_encoding__doc__[] = "device_encoding(fd) -> str\n\nReturn a string describing the encoding of the device\nif the output is a terminal; else return None.";




static PyObject *
device_encoding(PyObject *self, PyObject *args)
{
    int fd;

    if (!_PyArg_ParseTuple_SizeT(args, "i:device_encoding", &fd))
        return ((void *)0);

    return _Py_device_encoding(fd);
}
# 10666 "posixmodule.c"
static char posix_urandom__doc__[] = "urandom(n) -> str\n\nReturn n random bytes suitable for cryptographic use.";



static PyObject *
posix_urandom(PyObject *self, PyObject *args)
{
    Py_ssize_t size;
    PyObject *result;
    int ret;


    if (!_PyArg_ParseTuple_SizeT(args, "n:urandom", &size))
        return ((void *)0);
    if (size < 0)
        return PyErr_Format(PyExc_ValueError,
                            "negative argument not allowed");
    result = PyBytes_FromStringAndSize(((void *)0), size);
    if (result == ((void *)0))
        return ((void *)0);

    ret = _PyOS_URandom(((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "posixmodule.c", 10687, "PyBytes_Check(result)") : (void)0), (((PyBytesObject *)(result))->ob_sval)),
                        ((__builtin_expect(!(((((((PyObject*)(result))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "posixmodule.c", 10688, "PyBytes_Check(result)") : (void)0),(((PyVarObject*)(result))->ob_size)));
    if (ret == -1) {
        do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0);
        return ((void *)0);
    }
    return result;
}



static PyTypeObject TerminalSizeType;

static char TerminalSize_docstring[] = "A tuple of (columns, lines) for holding terminal window size";


static PyStructSequence_Field TerminalSize_fields[] = {
    {"columns", "width of the terminal window in characters"},
    {"lines", "height of the terminal window in characters"},
    {((void *)0), ((void *)0)}
};

static PyStructSequence_Desc TerminalSize_desc = {
    "os.terminal_size",
    TerminalSize_docstring,
    TerminalSize_fields,
    2,
};


static char termsize__doc__[] = "Return the size of the terminal window as (columns, lines).\n" "\n" "The optional argument fd (default standard output) specifies\n" "which file descriptor should be queried.\n" "\n" "If the file descriptor is not connected to a terminal, an OSError\n" "is thrown.\n" "\n" "This function will only be defined if an implementation is\n" "available for this system.\n" "\n" "shutil.get_terminal_size is the high-level function which should \n" "normally be used, os.get_terminal_size is the low-level implementation.";
# 10732 "posixmodule.c"
static PyObject*
get_terminal_size(PyObject *self, PyObject *args)
{
    int columns, lines;
    PyObject *termsize;

    int fd = fileno(__stdoutp);
# 10747 "posixmodule.c"
    if (!_PyArg_ParseTuple_SizeT(args, "|i", &fd))
        return ((void *)0);


    {
        struct winsize w;
        if (ioctl(fd, ((__uint32_t)0x40000000 | ((sizeof(struct winsize) & 0x1fff) << 16) | ((('t')) << 8) | ((104))), &w))
            return PyErr_SetFromErrno(PyExc_OSError);
        columns = w.ws_col;
        lines = w.ws_row;
    }
# 10789 "posixmodule.c"
    termsize = PyStructSequence_New(&TerminalSizeType);
    if (termsize == ((void *)0))
        return ((void *)0);
    (((PyTupleObject *)(termsize))->ob_item[0] = PyLong_FromLong(columns));
    (((PyTupleObject *)(termsize))->ob_item[1] = PyLong_FromLong(lines));
    if (PyErr_Occurred()) {
        do { if ( --((PyObject*)(termsize))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(termsize)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(termsize)))); } while (0);
        return ((void *)0);
    }
    return termsize;
}



static PyMethodDef posix_methods[] = {
    {"access", (PyCFunction)posix_access,
                        0x0001 | 0x0002,
                        posix_access__doc__},

    {"ttyname", posix_ttyname, 0x0001, posix_ttyname__doc__},

    {"chdir", (PyCFunction)posix_chdir,
                        0x0001 | 0x0002,
                        posix_chdir__doc__},

    {"chflags", (PyCFunction)posix_chflags,
                        0x0001 | 0x0002,
                        posix_chflags__doc__},

    {"chmod", (PyCFunction)posix_chmod,
                        0x0001 | 0x0002,
                        posix_chmod__doc__},

    {"fchmod", posix_fchmod, 0x0001, posix_fchmod__doc__},


    {"chown", (PyCFunction)posix_chown,
                        0x0001 | 0x0002,
                        posix_chown__doc__},


    {"lchmod", posix_lchmod, 0x0001, posix_lchmod__doc__},


    {"fchown", posix_fchown, 0x0001, posix_fchown__doc__},


    {"lchflags", posix_lchflags, 0x0001, posix_lchflags__doc__},


    {"lchown", posix_lchown, 0x0001, posix_lchown__doc__},


    {"chroot", posix_chroot, 0x0001, posix_chroot__doc__},


    {"ctermid", posix_ctermid, 0x0004, posix_ctermid__doc__},


    {"getcwd", (PyCFunction)posix_getcwd_unicode,
    0x0004, posix_getcwd__doc__},
    {"getcwdb", (PyCFunction)posix_getcwd_bytes,
    0x0004, posix_getcwdb__doc__},


    {"link", (PyCFunction)posix_link,
                        0x0001 | 0x0002,
                        posix_link__doc__},

    {"listdir", (PyCFunction)posix_listdir,
                        0x0001 | 0x0002,
                        posix_listdir__doc__},
    {"lstat", (PyCFunction)posix_lstat,
                        0x0001 | 0x0002,
                        posix_lstat__doc__},
    {"mkdir", (PyCFunction)posix_mkdir,
                        0x0001 | 0x0002,
                        posix_mkdir__doc__},

    {"nice", posix_nice, 0x0001, posix_nice__doc__},


    {"getpriority", posix_getpriority, 0x0001, posix_getpriority__doc__},


    {"setpriority", posix_setpriority, 0x0001, posix_setpriority__doc__},


    {"readlink", (PyCFunction)posix_readlink,
                        0x0001 | 0x0002,
                        readlink__doc__},






    {"rename", (PyCFunction)posix_rename,
                        0x0001 | 0x0002,
                        posix_rename__doc__},
    {"replace", (PyCFunction)posix_replace,
                        0x0001 | 0x0002,
                        posix_replace__doc__},
    {"rmdir", (PyCFunction)posix_rmdir,
                        0x0001 | 0x0002,
                        posix_rmdir__doc__},
    {"stat", (PyCFunction)posix_stat,
                        0x0001 | 0x0002,
                        posix_stat__doc__},
    {"stat_float_times", stat_float_times, 0x0001, stat_float_times__doc__},

    {"symlink", (PyCFunction)posix_symlink,
                        0x0001 | 0x0002,
                        posix_symlink__doc__},


    {"system", posix_system, 0x0001, posix_system__doc__},

    {"umask", posix_umask, 0x0001, posix_umask__doc__},

    {"uname", posix_uname, 0x0004, posix_uname__doc__},

    {"unlink", (PyCFunction)posix_unlink,
                        0x0001 | 0x0002,
                        posix_unlink__doc__},
    {"remove", (PyCFunction)posix_unlink,
                        0x0001 | 0x0002,
                        posix_remove__doc__},
    {"utime", (PyCFunction)posix_utime,
                        0x0001 | 0x0002, posix_utime__doc__},

    {"times", posix_times, 0x0004, posix_times__doc__},

    {"_exit", posix__exit, 0x0001, posix__exit__doc__},

    {"execv", posix_execv, 0x0001, posix_execv__doc__},
    {"execve", (PyCFunction)posix_execve,
                        0x0001 | 0x0002,
                        posix_execve__doc__},
# 10941 "posixmodule.c"
    {"fork", posix_fork, 0x0004, posix_fork__doc__},



    {"sched_get_priority_max", posix_sched_get_priority_max, 0x0001, posix_sched_get_priority_max__doc__},
    {"sched_get_priority_min", posix_sched_get_priority_min, 0x0001, posix_sched_get_priority_min__doc__},
# 10963 "posixmodule.c"
    {"sched_yield", posix_sched_yield, 0x0004, posix_sched_yield__doc__},






    {"openpty", posix_openpty, 0x0004, posix_openpty__doc__},


    {"forkpty", posix_forkpty, 0x0004, posix_forkpty__doc__},


    {"getegid", posix_getegid, 0x0004, posix_getegid__doc__},


    {"geteuid", posix_geteuid, 0x0004, posix_geteuid__doc__},


    {"getgid", posix_getgid, 0x0004, posix_getgid__doc__},


    {"getgrouplist", posix_getgrouplist, 0x0001, posix_getgrouplist__doc__},


    {"getgroups", posix_getgroups, 0x0004, posix_getgroups__doc__},

    {"getpid", posix_getpid, 0x0004, posix_getpid__doc__},

    {"getpgrp", posix_getpgrp, 0x0004, posix_getpgrp__doc__},


    {"getppid", posix_getppid, 0x0004, posix_getppid__doc__},


    {"getuid", posix_getuid, 0x0004, posix_getuid__doc__},


    {"getlogin", posix_getlogin, 0x0004, posix_getlogin__doc__},


    {"kill", posix_kill, 0x0001, posix_kill__doc__},


    {"killpg", posix_killpg, 0x0001, posix_killpg__doc__},
# 11017 "posixmodule.c"
    {"setuid", posix_setuid, 0x0001, posix_setuid__doc__},


    {"seteuid", posix_seteuid, 0x0001, posix_seteuid__doc__},


    {"setegid", posix_setegid, 0x0001, posix_setegid__doc__},


    {"setreuid", posix_setreuid, 0x0001, posix_setreuid__doc__},


    {"setregid", posix_setregid, 0x0001, posix_setregid__doc__},


    {"setgid", posix_setgid, 0x0001, posix_setgid__doc__},


    {"setgroups", posix_setgroups, 0x0008, posix_setgroups__doc__},


    {"initgroups", posix_initgroups, 0x0001, posix_initgroups__doc__},


    {"getpgid", posix_getpgid, 0x0001, posix_getpgid__doc__},


    {"setpgrp", posix_setpgrp, 0x0004, posix_setpgrp__doc__},


    {"wait", posix_wait, 0x0004, posix_wait__doc__},


    {"wait3", posix_wait3, 0x0001, posix_wait3__doc__},


    {"wait4", posix_wait4, 0x0001, posix_wait4__doc__},





    {"waitpid", posix_waitpid, 0x0001, posix_waitpid__doc__},


    {"getsid", posix_getsid, 0x0001, posix_getsid__doc__},


    {"setsid", posix_setsid, 0x0004, posix_setsid__doc__},


    {"setpgid", posix_setpgid, 0x0001, posix_setpgid__doc__},


    {"tcgetpgrp", posix_tcgetpgrp, 0x0001, posix_tcgetpgrp__doc__},


    {"tcsetpgrp", posix_tcsetpgrp, 0x0001, posix_tcsetpgrp__doc__},

    {"open", (PyCFunction)posix_open, 0x0001 | 0x0002,

                        posix_open__doc__},
    {"close", posix_close, 0x0001, posix_close__doc__},
    {"closerange", posix_closerange, 0x0001, posix_closerange__doc__},
    {"device_encoding", device_encoding, 0x0001, device_encoding__doc__},
    {"dup", posix_dup, 0x0001, posix_dup__doc__},
    {"dup2", posix_dup2, 0x0001, posix_dup2__doc__},

    {"lockf", posix_lockf, 0x0001, posix_lockf__doc__},

    {"lseek", posix_lseek, 0x0001, posix_lseek__doc__},
    {"read", posix_read, 0x0001, posix_read__doc__},

    {"readv", posix_readv, 0x0001, posix_readv__doc__},


    {"pread", posix_pread, 0x0001, posix_pread__doc__},

    {"write", posix_write, 0x0001, posix_write__doc__},

    {"writev", posix_writev, 0x0001, posix_writev__doc__},


    {"pwrite", posix_pwrite, 0x0001, posix_pwrite__doc__},


    {"sendfile", (PyCFunction)posix_sendfile, 0x0001 | 0x0002,
                            posix_sendfile__doc__},

    {"fstat", posix_fstat, 0x0001, posix_fstat__doc__},
    {"isatty", posix_isatty, 0x0001, posix_isatty__doc__},

    {"pipe", posix_pipe, 0x0004, posix_pipe__doc__},





    {"mkfifo", (PyCFunction)posix_mkfifo,
                        0x0001 | 0x0002,
                        posix_mkfifo__doc__},


    {"mknod", (PyCFunction)posix_mknod,
                        0x0001 | 0x0002,
                        posix_mknod__doc__},


    {"major", posix_major, 0x0001, posix_major__doc__},
    {"minor", posix_minor, 0x0001, posix_minor__doc__},
    {"makedev", posix_makedev, 0x0001, posix_makedev__doc__},


    {"ftruncate", posix_ftruncate, 0x0001, posix_ftruncate__doc__},


    {"truncate", (PyCFunction)posix_truncate,
                        0x0001 | 0x0002,
                        posix_truncate__doc__},
# 11144 "posixmodule.c"
    {"putenv", posix_putenv, 0x0001, posix_putenv__doc__},


    {"unsetenv", posix_unsetenv, 0x0001, posix_unsetenv__doc__},

    {"strerror", posix_strerror, 0x0001, posix_strerror__doc__},

    {"fchdir", posix_fchdir, 0x0008, posix_fchdir__doc__},


    {"fsync", posix_fsync, 0x0008, posix_fsync__doc__},


    {"sync", posix_sync, 0x0004, posix_sync__doc__},






    {"WCOREDUMP", posix_WCOREDUMP, 0x0001, posix_WCOREDUMP__doc__},


    {"WIFCONTINUED",posix_WIFCONTINUED, 0x0001, posix_WIFCONTINUED__doc__},


    {"WIFSTOPPED", posix_WIFSTOPPED, 0x0001, posix_WIFSTOPPED__doc__},


    {"WIFSIGNALED", posix_WIFSIGNALED, 0x0001, posix_WIFSIGNALED__doc__},


    {"WIFEXITED", posix_WIFEXITED, 0x0001, posix_WIFEXITED__doc__},


    {"WEXITSTATUS", posix_WEXITSTATUS, 0x0001, posix_WEXITSTATUS__doc__},


    {"WTERMSIG", posix_WTERMSIG, 0x0001, posix_WTERMSIG__doc__},


    {"WSTOPSIG", posix_WSTOPSIG, 0x0001, posix_WSTOPSIG__doc__},



    {"fstatvfs", posix_fstatvfs, 0x0001, posix_fstatvfs__doc__},


    {"statvfs", (PyCFunction)posix_statvfs,
                        0x0001 | 0x0002,
                        posix_statvfs__doc__},


    {"confstr", posix_confstr, 0x0001, posix_confstr__doc__},


    {"sysconf", posix_sysconf, 0x0001, posix_sysconf__doc__},


    {"fpathconf", posix_fpathconf, 0x0001, posix_fpathconf__doc__},


    {"pathconf", (PyCFunction)posix_pathconf,
                        0x0001 | 0x0002,
                        posix_pathconf__doc__},

    {"abort", posix_abort, 0x0004, posix_abort__doc__},
# 11219 "posixmodule.c"
    {"getloadavg", posix_getloadavg, 0x0004, posix_getloadavg__doc__},

    {"urandom", posix_urandom, 0x0001, posix_urandom__doc__},
# 11250 "posixmodule.c"
    {"get_terminal_size", get_terminal_size, 0x0001, termsize__doc__},

    {((void *)0), ((void *)0)}
};


static int
ins(PyObject *module, char *symbol, long value)
{
    return PyModule_AddIntConstant(module, symbol, value);
}
# 11344 "posixmodule.c"
static int
all_ins(PyObject *d)
{

    if (ins(d, "F_OK", (long)0)) return -1;


    if (ins(d, "R_OK", (long)(1<<2))) return -1;


    if (ins(d, "W_OK", (long)(1<<1))) return -1;


    if (ins(d, "X_OK", (long)(1<<0))) return -1;


    if (ins(d, "NGROUPS_MAX", (long)16)) return -1;


    if (ins(d, "TMP_MAX", (long)308915776)) return -1;


    if (ins(d, "WCONTINUED", (long)0x00000010)) return -1;


    if (ins(d, "WNOHANG", (long)0x00000001)) return -1;


    if (ins(d, "WUNTRACED", (long)0x00000002)) return -1;


    if (ins(d, "O_RDONLY", (long)0x0000)) return -1;


    if (ins(d, "O_WRONLY", (long)0x0001)) return -1;


    if (ins(d, "O_RDWR", (long)0x0002)) return -1;


    if (ins(d, "O_NDELAY", (long)0x0004)) return -1;


    if (ins(d, "O_NONBLOCK", (long)0x0004)) return -1;


    if (ins(d, "O_APPEND", (long)0x0008)) return -1;


    if (ins(d, "O_DSYNC", (long)0x400000)) return -1;





    if (ins(d, "O_SYNC", (long)0x0080)) return -1;


    if (ins(d, "O_NOCTTY", (long)0x20000)) return -1;


    if (ins(d, "O_CREAT", (long)0x0200)) return -1;


    if (ins(d, "O_EXCL", (long)0x0800)) return -1;


    if (ins(d, "O_TRUNC", (long)0x0400)) return -1;
# 11426 "posixmodule.c"
    if (ins(d, "O_SHLOCK", (long)0x0010)) return -1;


    if (ins(d, "O_EXLOCK", (long)0x0020)) return -1;
# 11441 "posixmodule.c"
    if (ins(d, "PRIO_PROCESS", (long)0)) return -1;


    if (ins(d, "PRIO_PGRP", (long)1)) return -1;


    if (ins(d, "PRIO_USER", (long)2)) return -1;


    if (ins(d, "O_CLOEXEC", (long)0x1000000)) return -1;


    if (ins(d, "O_ACCMODE", (long)0x0003)) return -1;
# 11491 "posixmodule.c"
    if (ins(d, "O_ASYNC", (long)0x0040)) return -1;







    if (ins(d, "O_DIRECTORY", (long)0x100000)) return -1;



    if (ins(d, "O_NOFOLLOW", (long)0x0100)) return -1;
# 11516 "posixmodule.c"
    if (ins(d, "EX_OK", (long)0)) return -1;


    if (ins(d, "EX_USAGE", (long)64)) return -1;


    if (ins(d, "EX_DATAERR", (long)65)) return -1;


    if (ins(d, "EX_NOINPUT", (long)66)) return -1;


    if (ins(d, "EX_NOUSER", (long)67)) return -1;


    if (ins(d, "EX_NOHOST", (long)68)) return -1;


    if (ins(d, "EX_UNAVAILABLE", (long)69)) return -1;


    if (ins(d, "EX_SOFTWARE", (long)70)) return -1;


    if (ins(d, "EX_OSERR", (long)71)) return -1;


    if (ins(d, "EX_OSFILE", (long)72)) return -1;


    if (ins(d, "EX_CANTCREAT", (long)73)) return -1;


    if (ins(d, "EX_IOERR", (long)74)) return -1;


    if (ins(d, "EX_TEMPFAIL", (long)75)) return -1;


    if (ins(d, "EX_PROTOCOL", (long)76)) return -1;


    if (ins(d, "EX_NOPERM", (long)77)) return -1;


    if (ins(d, "EX_CONFIG", (long)78)) return -1;







    if (ins(d, "ST_RDONLY", (long)0x00000001)) return -1;


    if (ins(d, "ST_NOSUID", (long)0x00000002)) return -1;
# 11608 "posixmodule.c"
    if (ins(d, "P_PID", (long)P_PID)) return -1;
    if (ins(d, "P_PGID", (long)P_PGID)) return -1;
    if (ins(d, "P_ALL", (long)P_ALL)) return -1;


    if (ins(d, "WEXITED", (long)0x00000004)) return -1;


    if (ins(d, "WNOWAIT", (long)0x00000020)) return -1;


    if (ins(d, "WSTOPPED", (long)0x00000008)) return -1;


    if (ins(d, "CLD_EXITED", (long)1)) return -1;


    if (ins(d, "CLD_DUMPED", (long)3)) return -1;


    if (ins(d, "CLD_TRAPPED", (long)4)) return -1;


    if (ins(d, "CLD_CONTINUED", (long)6)) return -1;




    if (ins(d, "F_LOCK", (long)1)) return -1;


    if (ins(d, "F_TLOCK", (long)2)) return -1;


    if (ins(d, "F_ULOCK", (long)0)) return -1;


    if (ins(d, "F_TEST", (long)3)) return -1;
# 11680 "posixmodule.c"
    if (ins(d, "SCHED_OTHER", (long)1)) return -1;
    if (ins(d, "SCHED_FIFO", (long)4)) return -1;
    if (ins(d, "SCHED_RR", (long)2)) return -1;
# 11716 "posixmodule.c"
    if (PyModule_AddIntConstant(d, "RTLD_LAZY", 0x1)) return -1;


    if (PyModule_AddIntConstant(d, "RTLD_NOW", 0x2)) return -1;


    if (PyModule_AddIntConstant(d, "RTLD_GLOBAL", 0x8)) return -1;


    if (PyModule_AddIntConstant(d, "RTLD_LOCAL", 0x4)) return -1;


    if (PyModule_AddIntConstant(d, "RTLD_NODELETE", 0x80)) return -1;


    if (PyModule_AddIntConstant(d, "RTLD_NOLOAD", 0x10)) return -1;
# 11740 "posixmodule.c"
    return 0;
}
# 11757 "posixmodule.c"
static struct PyModuleDef posixmodule = {
    { { 1, ((void *)0) }, ((void *)0), 0, ((void *)0), },
    "posix",
    posix__doc__,
    -1,
    posix_methods,
    ((void *)0),
    ((void *)0),
    ((void *)0),
    ((void *)0)
};


static char *have_functions[] = {






    "HAVE_FCHDIR",



    "HAVE_FCHMOD",







    "HAVE_FCHOWN",
# 11801 "posixmodule.c"
    "HAVE_FPATHCONF",







    "HAVE_FSTATVFS",



    "HAVE_FTRUNCATE",







    "HAVE_FUTIMES",
# 11833 "posixmodule.c"
    "HAVE_LCHFLAGS",



    "HAVE_LCHMOD",



    "HAVE_LCHOWN",



    "HAVE_LSTAT",



    "HAVE_LUTIMES",
# 11892 "posixmodule.c"
    ((void *)0)
};


PyObject*
PyInit_posix(void)
{
    PyObject *m, *v;
    PyObject *list;
    char **trace;





    m = PyModule_Create2(&posixmodule, 1013);
    if (m == ((void *)0))
        return ((void *)0);


    v = convertenviron();
    do { if ((v) == ((void *)0)) ; else ( ((PyObject*)(v))->ob_refcnt++); } while (0);
    if (v == ((void *)0) || PyModule_AddObject(m, "environ", v) != 0)
        return ((void *)0);
    do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);

    if (all_ins(m))
        return ((void *)0);

    if (setup_confname_tables(m))
        return ((void *)0);

    ( ((PyObject*)(PyExc_OSError))->ob_refcnt++);
    PyModule_AddObject(m, "error", PyExc_OSError);


    if (posix_putenv_garbage == ((void *)0))
        posix_putenv_garbage = PyDict_New();


    if (!initialized) {





        stat_result_desc.name = "posix" ".stat_result";
        stat_result_desc.fields[7].name = PyStructSequence_UnnamedField;
        stat_result_desc.fields[8].name = PyStructSequence_UnnamedField;
        stat_result_desc.fields[9].name = PyStructSequence_UnnamedField;
        PyStructSequence_InitType(&StatResultType, &stat_result_desc);
        structseq_new = StatResultType.tp_new;
        StatResultType.tp_new = statresult_new;

        statvfs_result_desc.name = "posix" ".statvfs_result";
        PyStructSequence_InitType(&StatVFSResultType, &statvfs_result_desc);


        ticks_per_second = sysconf(3);
# 11965 "posixmodule.c"
        PyStructSequence_InitType(&TerminalSizeType, &TerminalSize_desc);
    }




    ( ((PyObject*)((PyObject*) &StatResultType))->ob_refcnt++);
    PyModule_AddObject(m, "stat_result", (PyObject*) &StatResultType);
    ( ((PyObject*)((PyObject*) &StatVFSResultType))->ob_refcnt++);
    PyModule_AddObject(m, "statvfs_result",
                       (PyObject*) &StatVFSResultType);






    times_result_desc.name = "posix" ".times_result";
    PyStructSequence_InitType(&TimesResultType, &times_result_desc);
    PyModule_AddObject(m, "times_result", (PyObject *)&TimesResultType);

    uname_result_desc.name = "posix" ".uname_result";
    PyStructSequence_InitType(&UnameResultType, &uname_result_desc);
    PyModule_AddObject(m, "uname_result", (PyObject *)&UnameResultType);
# 12002 "posixmodule.c"
    if (fstatvfs == ((void *)0)) {
        if (PyObject_SetAttrString((m),("fstatvfs"),((void *)0)) == -1) {
            return ((void *)0);
        }
    }



    if (statvfs == ((void *)0)) {
        if (PyObject_SetAttrString((m),("statvfs"),((void *)0)) == -1) {
            return ((void *)0);
        }
    }



    if (lchown == ((void *)0)) {
        if (PyObject_SetAttrString((m),("lchown"),((void *)0)) == -1) {
            return ((void *)0);
        }
    }





    ( ((PyObject*)(&TerminalSizeType))->ob_refcnt++);
    PyModule_AddObject(m, "terminal_size", (PyObject*) &TerminalSizeType);

    billion = PyLong_FromLong(1000000000);
    if (!billion)
        return ((void *)0);


    {
    int ignored;
    fd_specified("", -1);
    follow_symlinks_specified("", 1);
    dir_fd_and_follow_symlinks_invalid("chmod", (-100), 1);
    dir_fd_converter((&_Py_NoneStruct), &ignored);
    dir_fd_unavailable((&_Py_NoneStruct), &ignored);
    }





    list = PyList_New(0);
    if (!list)
        return ((void *)0);
    for (trace = have_functions; *trace; trace++) {
        PyObject *unicode = PyUnicode_DecodeASCII(*trace, strlen(*trace), ((void *)0));
        if (!unicode)
            return ((void *)0);
        if (PyList_Append(list, unicode))
            return ((void *)0);
        do { if ( --((PyObject*)(unicode))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(unicode)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(unicode)))); } while (0);
    }
    PyModule_AddObject(m, "_have_functions", list);

    initialized = 1;

    return m;

}
