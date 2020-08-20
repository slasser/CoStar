# 1 "_tkinter.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "_tkinter.c"
# 25 "_tkinter.c"
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
# 26 "_tkinter.c" 2



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
# 30 "_tkinter.c" 2
# 66 "_tkinter.c"
# 1 "/usr/include/tcl.h" 1 3 4
# 310 "/usr/include/tcl.h" 3 4
 typedef void *ClientData;
# 400 "/usr/include/tcl.h" 3 4
typedef long Tcl_WideInt;
typedef unsigned long Tcl_WideUInt;


typedef struct stat Tcl_StatBuf;
# 450 "/usr/include/tcl.h" 3 4
typedef struct Tcl_Interp {
    char *result;

    void (*freeProc) (char *blockPtr);







    int errorLine;


} Tcl_Interp;

typedef struct Tcl_AsyncHandler_ *Tcl_AsyncHandler;
typedef struct Tcl_Channel_ *Tcl_Channel;
typedef struct Tcl_ChannelTypeVersion_ *Tcl_ChannelTypeVersion;
typedef struct Tcl_Command_ *Tcl_Command;
typedef struct Tcl_Condition_ *Tcl_Condition;
typedef struct Tcl_Dict_ *Tcl_Dict;
typedef struct Tcl_EncodingState_ *Tcl_EncodingState;
typedef struct Tcl_Encoding_ *Tcl_Encoding;
typedef struct Tcl_Event Tcl_Event;
typedef struct Tcl_InterpState_ *Tcl_InterpState;
typedef struct Tcl_LoadHandle_ *Tcl_LoadHandle;
typedef struct Tcl_Mutex_ *Tcl_Mutex;
typedef struct Tcl_Pid_ *Tcl_Pid;
typedef struct Tcl_RegExp_ *Tcl_RegExp;
typedef struct Tcl_ThreadDataKey_ *Tcl_ThreadDataKey;
typedef struct Tcl_ThreadId_ *Tcl_ThreadId;
typedef struct Tcl_TimerToken_ *Tcl_TimerToken;
typedef struct Tcl_Trace_ *Tcl_Trace;
typedef struct Tcl_Var_ *Tcl_Var;
# 495 "/usr/include/tcl.h" 3 4
typedef void (Tcl_ThreadCreateProc) (ClientData clientData);
# 560 "/usr/include/tcl.h" 3 4
typedef struct Tcl_RegExpIndices {
    long start;

    long end;

} Tcl_RegExpIndices;

typedef struct Tcl_RegExpInfo {
    int nsubs;

    Tcl_RegExpIndices *matches;
    long extendStart;

    long reserved;
} Tcl_RegExpInfo;






typedef Tcl_StatBuf *Tcl_Stat_;
typedef struct stat *Tcl_OldStat_;
# 625 "/usr/include/tcl.h" 3 4
typedef enum {
    TCL_INT, TCL_DOUBLE, TCL_EITHER, TCL_WIDE_INT
} Tcl_ValueType;

typedef struct Tcl_Value {
    Tcl_ValueType type;

    long intValue;
    double doubleValue;
    Tcl_WideInt wideValue;
} Tcl_Value;






struct Tcl_Obj;





typedef int (Tcl_AppInitProc) (Tcl_Interp *interp);
typedef int (Tcl_AsyncProc) (ClientData clientData, Tcl_Interp *interp, int code);

typedef void (Tcl_ChannelProc) (ClientData clientData, int mask);
typedef void (Tcl_CloseProc) (ClientData data);
typedef void (Tcl_CmdDeleteProc) (ClientData clientData);
typedef int (Tcl_CmdProc) (ClientData clientData, Tcl_Interp *interp, int argc, char *argv[]);

typedef void (Tcl_CmdTraceProc) (ClientData clientData, Tcl_Interp *interp, int level, char *command, Tcl_CmdProc *proc, ClientData cmdClientData, int argc, char *argv[]);


typedef int (Tcl_CmdObjTraceProc) (ClientData clientData, Tcl_Interp *interp, int level, const char *command, Tcl_Command commandInfo, int objc, struct Tcl_Obj * const * objv);


typedef void (Tcl_CmdObjTraceDeleteProc) (ClientData clientData);
typedef void (Tcl_DupInternalRepProc) (struct Tcl_Obj *srcPtr, struct Tcl_Obj *dupPtr);

typedef int (Tcl_EncodingConvertProc)(ClientData clientData, const char *src, int srcLen, int flags, Tcl_EncodingState *statePtr, char *dst, int dstLen, int *srcReadPtr, int *dstWrotePtr, int *dstCharsPtr);



typedef void (Tcl_EncodingFreeProc)(ClientData clientData);
typedef int (Tcl_EventProc) (Tcl_Event *evPtr, int flags);
typedef void (Tcl_EventCheckProc) (ClientData clientData, int flags);

typedef int (Tcl_EventDeleteProc) (Tcl_Event *evPtr, ClientData clientData);

typedef void (Tcl_EventSetupProc) (ClientData clientData, int flags);

typedef void (Tcl_ExitProc) (ClientData clientData);
typedef void (Tcl_FileProc) (ClientData clientData, int mask);
typedef void (Tcl_FileFreeProc) (ClientData clientData);
typedef void (Tcl_FreeInternalRepProc) (struct Tcl_Obj *objPtr);
typedef void (Tcl_FreeProc) (char *blockPtr);
typedef void (Tcl_IdleProc) (ClientData clientData);
typedef void (Tcl_InterpDeleteProc) (ClientData clientData, Tcl_Interp *interp);

typedef int (Tcl_MathProc) (ClientData clientData, Tcl_Interp *interp, Tcl_Value *args, Tcl_Value *resultPtr);

typedef void (Tcl_NamespaceDeleteProc) (ClientData clientData);
typedef int (Tcl_ObjCmdProc) (ClientData clientData, Tcl_Interp *interp, int objc, struct Tcl_Obj * const * objv);

typedef int (Tcl_PackageInitProc) (Tcl_Interp *interp);
typedef int (Tcl_PackageUnloadProc) (Tcl_Interp *interp, int flags);

typedef void (Tcl_PanicProc) (const char *format, ...);
typedef void (Tcl_TcpAcceptProc) (ClientData callbackData, Tcl_Channel chan, char *address, int port);

typedef void (Tcl_TimerProc) (ClientData clientData);
typedef int (Tcl_SetFromAnyProc) (Tcl_Interp *interp, struct Tcl_Obj *objPtr);

typedef void (Tcl_UpdateStringProc) (struct Tcl_Obj *objPtr);
typedef char *(Tcl_VarTraceProc) (ClientData clientData, Tcl_Interp *interp, char *part1, char *part2, int flags);


typedef void (Tcl_CommandTraceProc) (ClientData clientData, Tcl_Interp *interp, const char *oldName, const char *newName, int flags);


typedef void (Tcl_CreateFileHandlerProc) (int fd, int mask, Tcl_FileProc *proc, ClientData clientData);

typedef void (Tcl_DeleteFileHandlerProc) (int fd);
typedef void (Tcl_AlertNotifierProc) (ClientData clientData);
typedef void (Tcl_ServiceModeHookProc) (int mode);
typedef ClientData (Tcl_InitNotifierProc) (void);
typedef void (Tcl_FinalizeNotifierProc) (ClientData clientData);
typedef void (Tcl_MainLoopProc) (void);







typedef struct Tcl_ObjType {
    char *name;
    Tcl_FreeInternalRepProc *freeIntRepProc;



    Tcl_DupInternalRepProc *dupIntRepProc;


    Tcl_UpdateStringProc *updateStringProc;


    Tcl_SetFromAnyProc *setFromAnyProc;



} Tcl_ObjType;







typedef struct Tcl_Obj {
    int refCount;
    char *bytes;
# 758 "/usr/include/tcl.h" 3 4
    int length;

    Tcl_ObjType *typePtr;



    union {
 long longValue;
 double doubleValue;
 void *otherValuePtr;
 Tcl_WideInt wideValue;
 struct {
     void *ptr1;
     void *ptr2;
 } twoPtrValue;
 struct {

     void *ptr;
     unsigned long value;

 } ptrAndLongRep;
    } internalRep;
} Tcl_Obj;
# 793 "/usr/include/tcl.h" 3 4
void Tcl_IncrRefCount (Tcl_Obj *objPtr);
void Tcl_DecrRefCount (Tcl_Obj *objPtr);
int Tcl_IsShared (Tcl_Obj *objPtr);







typedef struct Tcl_SavedResult {
    char *result;
    Tcl_FreeProc *freeProc;
    Tcl_Obj *objResultPtr;
    char *appendResult;
    int appendAvl;
    int appendUsed;
    char resultSpace[200 +1];
} Tcl_SavedResult;







typedef struct Tcl_Namespace {
    char *name;



    char *fullName;

    ClientData clientData;

    Tcl_NamespaceDeleteProc *deleteProc;


    struct Tcl_Namespace *parentPtr;



} Tcl_Namespace;
# 859 "/usr/include/tcl.h" 3 4
typedef struct Tcl_CallFrame {
    Tcl_Namespace *nsPtr;
    int dummy1;
    int dummy2;
    void *dummy3;
    void *dummy4;
    void *dummy5;
    int dummy6;
    void *dummy7;
    void *dummy8;
    int dummy9;
    void *dummy10;
    void *dummy11;
    void *dummy12;
    void *dummy13;
} Tcl_CallFrame;
# 890 "/usr/include/tcl.h" 3 4
typedef struct Tcl_CmdInfo {
    int isNativeObjectProc;



    Tcl_ObjCmdProc *objProc;
    ClientData objClientData;
    Tcl_CmdProc *proc;
    ClientData clientData;
    Tcl_CmdDeleteProc *deleteProc;


    ClientData deleteData;

    Tcl_Namespace *namespacePtr;




} Tcl_CmdInfo;
# 918 "/usr/include/tcl.h" 3 4
typedef struct Tcl_DString {
    char *string;

    int length;

    int spaceAvl;

    char staticSpace[200];


} Tcl_DString;
# 1077 "/usr/include/tcl.h" 3 4
typedef struct Tcl_HashKeyType Tcl_HashKeyType;
typedef struct Tcl_HashTable Tcl_HashTable;
typedef struct Tcl_HashEntry Tcl_HashEntry;

typedef unsigned int (Tcl_HashKeyProc) (Tcl_HashTable *tablePtr, void *keyPtr);

typedef int (Tcl_CompareHashKeysProc) (void *keyPtr, Tcl_HashEntry *hPtr);

typedef Tcl_HashEntry *(Tcl_AllocHashEntryProc) ( Tcl_HashTable *tablePtr, void *keyPtr);

typedef void (Tcl_FreeHashEntryProc) (Tcl_HashEntry *hPtr);
# 1106 "/usr/include/tcl.h" 3 4
struct Tcl_HashEntry {
    Tcl_HashEntry *nextPtr;

    Tcl_HashTable *tablePtr;

    void *hash;







    ClientData clientData;

    union {
 char *oneWordValue;
 Tcl_Obj *objPtr;
 int words[1];


 char string[4];

    } key;
};
# 1155 "/usr/include/tcl.h" 3 4
struct Tcl_HashKeyType {
    int version;



    int flags;
    Tcl_HashKeyProc *hashKeyProc;



    Tcl_CompareHashKeysProc *compareKeysProc;




    Tcl_AllocHashEntryProc *allocEntryProc;
# 1184 "/usr/include/tcl.h" 3 4
    Tcl_FreeHashEntryProc *freeEntryProc;






};
# 1200 "/usr/include/tcl.h" 3 4
struct Tcl_HashTable {
    Tcl_HashEntry **buckets;


    Tcl_HashEntry *staticBuckets[4];


    int numBuckets;

    int numEntries;

    int rebuildSize;

    int downShift;


    int mask;
    int keyType;




    Tcl_HashEntry *(*findProc) (Tcl_HashTable *tablePtr, const char *key);

    Tcl_HashEntry *(*createProc) (Tcl_HashTable *tablePtr, const char *key, int *newPtr);

    Tcl_HashKeyType *typePtr;

};






typedef struct Tcl_HashSearch {
    Tcl_HashTable *tablePtr;
    int nextIndex;

    Tcl_HashEntry *nextEntryPtr;

} Tcl_HashSearch;
# 1275 "/usr/include/tcl.h" 3 4
typedef struct {
    void *next;

    int epoch;

    Tcl_Dict dictionaryPtr;
} Tcl_DictSearch;
# 1304 "/usr/include/tcl.h" 3 4
struct Tcl_Event {
    Tcl_EventProc *proc;
    struct Tcl_Event *nextPtr;
};





typedef enum {
    TCL_QUEUE_TAIL, TCL_QUEUE_HEAD, TCL_QUEUE_MARK
} Tcl_QueuePosition;
# 1331 "/usr/include/tcl.h" 3 4
typedef struct Tcl_Time {
    long sec;
    long usec;
} Tcl_Time;

typedef void (Tcl_SetTimerProc) (Tcl_Time *timePtr);
typedef int (Tcl_WaitForEventProc) (Tcl_Time *timePtr);





typedef void (Tcl_GetTimeProc) (Tcl_Time *timebuf, ClientData clientData);

typedef void (Tcl_ScaleTimeProc) (Tcl_Time *timebuf, ClientData clientData);
# 1404 "/usr/include/tcl.h" 3 4
typedef int (Tcl_DriverBlockModeProc) ( ClientData instanceData, int mode);

typedef int (Tcl_DriverCloseProc) (ClientData instanceData, Tcl_Interp *interp);

typedef int (Tcl_DriverClose2Proc) (ClientData instanceData, Tcl_Interp *interp, int flags);

typedef int (Tcl_DriverInputProc) (ClientData instanceData, char *buf, int toRead, int *errorCodePtr);

typedef int (Tcl_DriverOutputProc) (ClientData instanceData, char *buf, int toWrite, int *errorCodePtr);

typedef int (Tcl_DriverSeekProc) (ClientData instanceData, long offset, int mode, int *errorCodePtr);

typedef int (Tcl_DriverSetOptionProc) ( ClientData instanceData, Tcl_Interp *interp, const char *optionName, const char *value);


typedef int (Tcl_DriverGetOptionProc) ( ClientData instanceData, Tcl_Interp *interp, char *optionName, Tcl_DString *dsPtr);


typedef void (Tcl_DriverWatchProc) ( ClientData instanceData, int mask);

typedef int (Tcl_DriverGetHandleProc) ( ClientData instanceData, int direction, ClientData *handlePtr);


typedef int (Tcl_DriverFlushProc) (ClientData instanceData);
typedef int (Tcl_DriverHandlerProc) ( ClientData instanceData, int interestMask);

typedef Tcl_WideInt (Tcl_DriverWideSeekProc) ( ClientData instanceData, Tcl_WideInt offset, int mode, int *errorCodePtr);





typedef void (Tcl_DriverThreadActionProc) ( ClientData instanceData, int action);




typedef int (Tcl_DriverTruncateProc) ( ClientData instanceData, Tcl_WideInt length);
# 1455 "/usr/include/tcl.h" 3 4
typedef struct Tcl_ChannelType {
    char *typeName;


    Tcl_ChannelTypeVersion version;

    Tcl_DriverCloseProc *closeProc;



    Tcl_DriverInputProc *inputProc;

    Tcl_DriverOutputProc *outputProc;

    Tcl_DriverSeekProc *seekProc;


    Tcl_DriverSetOptionProc *setOptionProc;

    Tcl_DriverGetOptionProc *getOptionProc;

    Tcl_DriverWatchProc *watchProc;


    Tcl_DriverGetHandleProc *getHandleProc;


    Tcl_DriverClose2Proc *close2Proc;



    Tcl_DriverBlockModeProc *blockModeProc;





    Tcl_DriverFlushProc *flushProc;


    Tcl_DriverHandlerProc *handlerProc;






    Tcl_DriverWideSeekProc *wideSeekProc;
# 1511 "/usr/include/tcl.h" 3 4
    Tcl_DriverThreadActionProc *threadActionProc;
# 1520 "/usr/include/tcl.h" 3 4
    Tcl_DriverTruncateProc *truncateProc;



} Tcl_ChannelType;
# 1540 "/usr/include/tcl.h" 3 4
typedef enum Tcl_PathType {
    TCL_PATH_ABSOLUTE,
    TCL_PATH_RELATIVE,
    TCL_PATH_VOLUME_RELATIVE
} Tcl_PathType;






typedef struct Tcl_GlobTypeData {
    int type;
    int perm;
    Tcl_Obj *macType;
    Tcl_Obj *macCreator;
} Tcl_GlobTypeData;
# 1588 "/usr/include/tcl.h" 3 4
typedef int (Tcl_FSStatProc) (Tcl_Obj *pathPtr, Tcl_StatBuf *buf);
typedef int (Tcl_FSAccessProc) (Tcl_Obj *pathPtr, int mode);
typedef Tcl_Channel (Tcl_FSOpenFileChannelProc) ( Tcl_Interp *interp, Tcl_Obj *pathPtr, int mode, int permissions);

typedef int (Tcl_FSMatchInDirectoryProc) (Tcl_Interp *interp, Tcl_Obj *result, Tcl_Obj *pathPtr, const char *pattern, Tcl_GlobTypeData * types);


typedef Tcl_Obj * (Tcl_FSGetCwdProc) (Tcl_Interp *interp);
typedef int (Tcl_FSChdirProc) (Tcl_Obj *pathPtr);
typedef int (Tcl_FSLstatProc) (Tcl_Obj *pathPtr, Tcl_StatBuf *buf);

typedef int (Tcl_FSCreateDirectoryProc) (Tcl_Obj *pathPtr);
typedef int (Tcl_FSDeleteFileProc) (Tcl_Obj *pathPtr);
typedef int (Tcl_FSCopyDirectoryProc) (Tcl_Obj *srcPathPtr, Tcl_Obj *destPathPtr, Tcl_Obj **errorPtr);

typedef int (Tcl_FSCopyFileProc) (Tcl_Obj *srcPathPtr, Tcl_Obj *destPathPtr);

typedef int (Tcl_FSRemoveDirectoryProc) (Tcl_Obj *pathPtr, int recursive, Tcl_Obj **errorPtr);

typedef int (Tcl_FSRenameFileProc) (Tcl_Obj *srcPathPtr, Tcl_Obj *destPathPtr);

typedef void (Tcl_FSUnloadFileProc) (Tcl_LoadHandle loadHandle);
typedef Tcl_Obj * (Tcl_FSListVolumesProc) (void);

struct utimbuf;
typedef int (Tcl_FSUtimeProc) (Tcl_Obj *pathPtr, struct utimbuf *tval);

typedef int (Tcl_FSNormalizePathProc) (Tcl_Interp *interp, Tcl_Obj *pathPtr, int nextCheckpoint);

typedef int (Tcl_FSFileAttrsGetProc) (Tcl_Interp *interp, int index, Tcl_Obj *pathPtr, Tcl_Obj **objPtrRef);

typedef const char ** (Tcl_FSFileAttrStringsProc) ( Tcl_Obj *pathPtr, Tcl_Obj **objPtrRef);

typedef int (Tcl_FSFileAttrsSetProc) (Tcl_Interp *interp, int index, Tcl_Obj *pathPtr, Tcl_Obj *objPtr);

typedef Tcl_Obj * (Tcl_FSLinkProc) (Tcl_Obj *pathPtr, Tcl_Obj *toPtr, int linkType);

typedef int (Tcl_FSLoadFileProc) (Tcl_Interp * interp, Tcl_Obj *pathPtr, Tcl_LoadHandle *handlePtr, Tcl_FSUnloadFileProc **unloadProcPtr);


typedef int (Tcl_FSPathInFilesystemProc) (Tcl_Obj *pathPtr, ClientData *clientDataPtr);

typedef Tcl_Obj * (Tcl_FSFilesystemPathTypeProc) ( Tcl_Obj *pathPtr);

typedef Tcl_Obj * (Tcl_FSFilesystemSeparatorProc) ( Tcl_Obj *pathPtr);

typedef void (Tcl_FSFreeInternalRepProc) (ClientData clientData);
typedef ClientData (Tcl_FSDupInternalRepProc) ( ClientData clientData);

typedef Tcl_Obj * (Tcl_FSInternalToNormalizedProc) ( ClientData clientData);

typedef ClientData (Tcl_FSCreateInternalRepProc) ( Tcl_Obj *pathPtr);


typedef struct Tcl_FSVersion_ *Tcl_FSVersion;
# 1668 "/usr/include/tcl.h" 3 4
typedef struct Tcl_Filesystem {
    const char *typeName;
    int structureLength;

    Tcl_FSVersion version;
    Tcl_FSPathInFilesystemProc *pathInFilesystemProc;



    Tcl_FSDupInternalRepProc *dupInternalRepProc;


    Tcl_FSFreeInternalRepProc *freeInternalRepProc;



    Tcl_FSInternalToNormalizedProc *internalToNormalizedProc;




    Tcl_FSCreateInternalRepProc *createInternalRepProc;







    Tcl_FSNormalizePathProc *normalizePathProc;




    Tcl_FSFilesystemPathTypeProc *filesystemPathTypeProc;


    Tcl_FSFilesystemSeparatorProc *filesystemSeparatorProc;



    Tcl_FSStatProc *statProc;


    Tcl_FSAccessProc *accessProc;



    Tcl_FSOpenFileChannelProc *openFileChannelProc;




    Tcl_FSMatchInDirectoryProc *matchInDirectoryProc;





    Tcl_FSUtimeProc *utimeProc;




    Tcl_FSLinkProc *linkProc;



    Tcl_FSListVolumesProc *listVolumesProc;




    Tcl_FSFileAttrStringsProc *fileAttrStringsProc;






    Tcl_FSFileAttrsGetProc *fileAttrsGetProc;



    Tcl_FSFileAttrsSetProc *fileAttrsSetProc;



    Tcl_FSCreateDirectoryProc *createDirectoryProc;



    Tcl_FSRemoveDirectoryProc *removeDirectoryProc;



    Tcl_FSDeleteFileProc *deleteFileProc;



    Tcl_FSCopyFileProc *copyFileProc;





    Tcl_FSRenameFileProc *renameFileProc;




    Tcl_FSCopyDirectoryProc *copyDirectoryProc;






    Tcl_FSLstatProc *lstatProc;


    Tcl_FSLoadFileProc *loadFileProc;




    Tcl_FSGetCwdProc *getCwdProc;





    Tcl_FSChdirProc *chdirProc;
# 1815 "/usr/include/tcl.h" 3 4
} Tcl_Filesystem;
# 1835 "/usr/include/tcl.h" 3 4
typedef struct Tcl_NotifierProcs {
    Tcl_SetTimerProc *setTimerProc;
    Tcl_WaitForEventProc *waitForEventProc;
    Tcl_CreateFileHandlerProc *createFileHandlerProc;
    Tcl_DeleteFileHandlerProc *deleteFileHandlerProc;
    Tcl_InitNotifierProc *initNotifierProc;
    Tcl_FinalizeNotifierProc *finalizeNotifierProc;
    Tcl_AlertNotifierProc *alertNotifierProc;
    Tcl_ServiceModeHookProc *serviceModeHookProc;
} Tcl_NotifierProcs;






typedef struct Tcl_EncodingType {
    const char *encodingName;


    Tcl_EncodingConvertProc *toUtfProc;


    Tcl_EncodingConvertProc *fromUtfProc;


    Tcl_EncodingFreeProc *freeProc;


    ClientData clientData;

    int nullSize;




} Tcl_EncodingType;
# 1917 "/usr/include/tcl.h" 3 4
typedef struct Tcl_Token {
    int type;

    const char *start;
    int size;
    int numComponents;




} Tcl_Token;
# 2033 "/usr/include/tcl.h" 3 4
typedef struct Tcl_Parse {
    const char *commentStart;

    int commentSize;



    const char *commandStart;

    int commandSize;



    int numWords;

    Tcl_Token *tokenPtr;




    int numTokens;
    int tokensAvailable;

    int errorType;







    const char *string;

    const char *end;

    Tcl_Interp *interp;

    const char *term;





    int incomplete;



    Tcl_Token staticTokens[20];





} Tcl_Parse;
# 2152 "/usr/include/tcl.h" 3 4
typedef unsigned short Tcl_UniChar;







typedef struct Tcl_Config {
    const char *key;

    const char *value;

} Tcl_Config;
# 2180 "/usr/include/tcl.h" 3 4
typedef void (Tcl_LimitHandlerProc) (ClientData clientData, Tcl_Interp *interp);

typedef void (Tcl_LimitHandlerDeleteProc) (ClientData clientData);

typedef struct mp_int mp_int;

typedef unsigned int mp_digit;
# 2206 "/usr/include/tcl.h" 3 4
extern const char * Tcl_InitStubs (Tcl_Interp *interp, const char *version, int exact);

extern const char * TclTomMathInitializeStubs ( Tcl_Interp *interp, const char *version, int epoch, int revision);
# 2233 "/usr/include/tcl.h" 3 4
extern void Tcl_Main (int argc, char **argv, Tcl_AppInitProc *appInitProc);

extern const char * Tcl_PkgInitStubsCheck (Tcl_Interp *interp, const char *version, int exact);
# 2246 "/usr/include/tcl.h" 3 4
# 1 "/usr/include/tclDecls.h" 1 3 4
# 43 "/usr/include/tclDecls.h" 3 4
extern int Tcl_PkgProvideEx(Tcl_Interp *interp,
    const char *name, const char *version,
    ClientData clientData);




extern const char * Tcl_PkgRequireEx(Tcl_Interp *interp,
    const char *name, const char *version,
    int exact, ClientData *clientDataPtr);




extern void Tcl_Panic(const char *format, ...);




extern char * Tcl_Alloc(unsigned int size);




extern void Tcl_Free(char *ptr);




extern char * Tcl_Realloc(char *ptr, unsigned int size);




extern char * Tcl_DbCkalloc(unsigned int size, const char *file,
    int line);




extern int Tcl_DbCkfree(char *ptr, const char *file, int line);




extern char * Tcl_DbCkrealloc(char *ptr, unsigned int size,
    const char *file, int line);





extern void Tcl_CreateFileHandler(int fd, int mask,
    Tcl_FileProc *proc, ClientData clientData);
# 111 "/usr/include/tclDecls.h" 3 4
extern void Tcl_DeleteFileHandler(int fd);
# 124 "/usr/include/tclDecls.h" 3 4
extern void Tcl_SetTimer(Tcl_Time *timePtr);




extern void Tcl_Sleep(int ms);




extern int Tcl_WaitForEvent(Tcl_Time *timePtr);




extern int Tcl_AppendAllObjTypes(Tcl_Interp *interp,
    Tcl_Obj *objPtr);




extern void Tcl_AppendStringsToObj(Tcl_Obj *objPtr, ...);




extern void Tcl_AppendToObj(Tcl_Obj *objPtr, const char *bytes,
    int length);




extern Tcl_Obj * Tcl_ConcatObj(int objc, Tcl_Obj *const objv[]);




extern int Tcl_ConvertToType(Tcl_Interp *interp,
    Tcl_Obj *objPtr, Tcl_ObjType *typePtr);




extern void Tcl_DbDecrRefCount(Tcl_Obj *objPtr, const char *file,
    int line);




extern void Tcl_DbIncrRefCount(Tcl_Obj *objPtr, const char *file,
    int line);




extern int Tcl_DbIsShared(Tcl_Obj *objPtr, const char *file,
    int line);




extern Tcl_Obj * Tcl_DbNewBooleanObj(int boolValue, const char *file,
    int line);




extern Tcl_Obj * Tcl_DbNewByteArrayObj(const unsigned char *bytes,
    int length, const char *file, int line);




extern Tcl_Obj * Tcl_DbNewDoubleObj(double doubleValue,
    const char *file, int line);




extern Tcl_Obj * Tcl_DbNewListObj(int objc, Tcl_Obj *const *objv,
    const char *file, int line);




extern Tcl_Obj * Tcl_DbNewLongObj(long longValue, const char *file,
    int line);




extern Tcl_Obj * Tcl_DbNewObj(const char *file, int line);




extern Tcl_Obj * Tcl_DbNewStringObj(const char *bytes, int length,
    const char *file, int line);




extern Tcl_Obj * Tcl_DuplicateObj(Tcl_Obj *objPtr);




extern void TclFreeObj(Tcl_Obj *objPtr);




extern int Tcl_GetBoolean(Tcl_Interp *interp, const char *src,
    int *boolPtr);




extern int Tcl_GetBooleanFromObj(Tcl_Interp *interp,
    Tcl_Obj *objPtr, int *boolPtr);




extern unsigned char * Tcl_GetByteArrayFromObj(Tcl_Obj *objPtr,
    int *lengthPtr);




extern int Tcl_GetDouble(Tcl_Interp *interp, const char *src,
    double *doublePtr);




extern int Tcl_GetDoubleFromObj(Tcl_Interp *interp,
    Tcl_Obj *objPtr, double *doublePtr);




extern int Tcl_GetIndexFromObj(Tcl_Interp *interp,
    Tcl_Obj *objPtr, char **tablePtr,
    const char *msg, int flags, int *indexPtr);




extern int Tcl_GetInt(Tcl_Interp *interp, const char *src,
    int *intPtr);




extern int Tcl_GetIntFromObj(Tcl_Interp *interp,
    Tcl_Obj *objPtr, int *intPtr);




extern int Tcl_GetLongFromObj(Tcl_Interp *interp,
    Tcl_Obj *objPtr, long *longPtr);




extern Tcl_ObjType * Tcl_GetObjType(const char *typeName);




extern char * Tcl_GetStringFromObj(Tcl_Obj *objPtr, int *lengthPtr);




extern void Tcl_InvalidateStringRep(Tcl_Obj *objPtr);




extern int Tcl_ListObjAppendList(Tcl_Interp *interp,
    Tcl_Obj *listPtr, Tcl_Obj *elemListPtr);




extern int Tcl_ListObjAppendElement(Tcl_Interp *interp,
    Tcl_Obj *listPtr, Tcl_Obj *objPtr);




extern int Tcl_ListObjGetElements(Tcl_Interp *interp,
    Tcl_Obj *listPtr, int *objcPtr,
    Tcl_Obj ***objvPtr);




extern int Tcl_ListObjIndex(Tcl_Interp *interp,
    Tcl_Obj *listPtr, int index,
    Tcl_Obj **objPtrPtr);




extern int Tcl_ListObjLength(Tcl_Interp *interp,
    Tcl_Obj *listPtr, int *lengthPtr);




extern int Tcl_ListObjReplace(Tcl_Interp *interp,
    Tcl_Obj *listPtr, int first, int count,
    int objc, Tcl_Obj *const objv[]);




extern Tcl_Obj * Tcl_NewBooleanObj(int boolValue);




extern Tcl_Obj * Tcl_NewByteArrayObj(const unsigned char *bytes,
    int length);




extern Tcl_Obj * Tcl_NewDoubleObj(double doubleValue);




extern Tcl_Obj * Tcl_NewIntObj(int intValue);




extern Tcl_Obj * Tcl_NewListObj(int objc, Tcl_Obj *const objv[]);




extern Tcl_Obj * Tcl_NewLongObj(long longValue);




extern Tcl_Obj * Tcl_NewObj(void);




extern Tcl_Obj * Tcl_NewStringObj(const char *bytes, int length);




extern void Tcl_SetBooleanObj(Tcl_Obj *objPtr, int boolValue);




extern unsigned char * Tcl_SetByteArrayLength(Tcl_Obj *objPtr, int length);




extern void Tcl_SetByteArrayObj(Tcl_Obj *objPtr,
    const unsigned char *bytes, int length);




extern void Tcl_SetDoubleObj(Tcl_Obj *objPtr, double doubleValue);




extern void Tcl_SetIntObj(Tcl_Obj *objPtr, int intValue);




extern void Tcl_SetListObj(Tcl_Obj *objPtr, int objc,
    Tcl_Obj *const objv[]);




extern void Tcl_SetLongObj(Tcl_Obj *objPtr, long longValue);




extern void Tcl_SetObjLength(Tcl_Obj *objPtr, int length);




extern void Tcl_SetStringObj(Tcl_Obj *objPtr, const char *bytes,
    int length);




extern void Tcl_AddErrorInfo(Tcl_Interp *interp,
    const char *message);




extern void Tcl_AddObjErrorInfo(Tcl_Interp *interp,
    const char *message, int length);




extern void Tcl_AllowExceptions(Tcl_Interp *interp);




extern void Tcl_AppendElement(Tcl_Interp *interp,
    const char *element);




extern void Tcl_AppendResult(Tcl_Interp *interp, ...);




extern Tcl_AsyncHandler Tcl_AsyncCreate(Tcl_AsyncProc *proc,
    ClientData clientData);




extern void Tcl_AsyncDelete(Tcl_AsyncHandler async);




extern int Tcl_AsyncInvoke(Tcl_Interp *interp, int code);




extern void Tcl_AsyncMark(Tcl_AsyncHandler async);




extern int Tcl_AsyncReady(void);




extern void Tcl_BackgroundError(Tcl_Interp *interp);




extern char Tcl_Backslash(const char *src, int *readPtr);




extern int Tcl_BadChannelOption(Tcl_Interp *interp,
    const char *optionName,
    const char *optionList);




extern void Tcl_CallWhenDeleted(Tcl_Interp *interp,
    Tcl_InterpDeleteProc *proc,
    ClientData clientData);




extern void Tcl_CancelIdleCall(Tcl_IdleProc *idleProc,
    ClientData clientData);




extern int Tcl_Close(Tcl_Interp *interp, Tcl_Channel chan);




extern int Tcl_CommandComplete(const char *cmd);




extern char * Tcl_Concat(int argc, char *const *argv);




extern int Tcl_ConvertElement(const char *src, char *dst,
    int flags);




extern int Tcl_ConvertCountedElement(const char *src,
    int length, char *dst, int flags);




extern int Tcl_CreateAlias(Tcl_Interp *slave,
    const char *slaveCmd, Tcl_Interp *target,
    const char *targetCmd, int argc,
    char *const *argv);




extern int Tcl_CreateAliasObj(Tcl_Interp *slave,
    const char *slaveCmd, Tcl_Interp *target,
    const char *targetCmd, int objc,
    Tcl_Obj *const objv[]);




extern Tcl_Channel Tcl_CreateChannel(Tcl_ChannelType *typePtr,
    const char *chanName,
    ClientData instanceData, int mask);




extern void Tcl_CreateChannelHandler(Tcl_Channel chan, int mask,
    Tcl_ChannelProc *proc, ClientData clientData);




extern void Tcl_CreateCloseHandler(Tcl_Channel chan,
    Tcl_CloseProc *proc, ClientData clientData);




extern Tcl_Command Tcl_CreateCommand(Tcl_Interp *interp,
    const char *cmdName, Tcl_CmdProc *proc,
    ClientData clientData,
    Tcl_CmdDeleteProc *deleteProc);




extern void Tcl_CreateEventSource(Tcl_EventSetupProc *setupProc,
    Tcl_EventCheckProc *checkProc,
    ClientData clientData);




extern void Tcl_CreateExitHandler(Tcl_ExitProc *proc,
    ClientData clientData);




extern Tcl_Interp * Tcl_CreateInterp(void);




extern void Tcl_CreateMathFunc(Tcl_Interp *interp,
    const char *name, int numArgs,
    Tcl_ValueType *argTypes, Tcl_MathProc *proc,
    ClientData clientData);




extern Tcl_Command Tcl_CreateObjCommand(Tcl_Interp *interp,
    const char *cmdName, Tcl_ObjCmdProc *proc,
    ClientData clientData,
    Tcl_CmdDeleteProc *deleteProc);




extern Tcl_Interp * Tcl_CreateSlave(Tcl_Interp *interp,
    const char *slaveName, int isSafe);




extern Tcl_TimerToken Tcl_CreateTimerHandler(int milliseconds,
    Tcl_TimerProc *proc, ClientData clientData);




extern Tcl_Trace Tcl_CreateTrace(Tcl_Interp *interp, int level,
    Tcl_CmdTraceProc *proc,
    ClientData clientData);




extern void Tcl_DeleteAssocData(Tcl_Interp *interp,
    const char *name);




extern void Tcl_DeleteChannelHandler(Tcl_Channel chan,
    Tcl_ChannelProc *proc, ClientData clientData);




extern void Tcl_DeleteCloseHandler(Tcl_Channel chan,
    Tcl_CloseProc *proc, ClientData clientData);




extern int Tcl_DeleteCommand(Tcl_Interp *interp,
    const char *cmdName);




extern int Tcl_DeleteCommandFromToken(Tcl_Interp *interp,
    Tcl_Command command);




extern void Tcl_DeleteEvents(Tcl_EventDeleteProc *proc,
    ClientData clientData);




extern void Tcl_DeleteEventSource(Tcl_EventSetupProc *setupProc,
    Tcl_EventCheckProc *checkProc,
    ClientData clientData);




extern void Tcl_DeleteExitHandler(Tcl_ExitProc *proc,
    ClientData clientData);




extern void Tcl_DeleteHashEntry(Tcl_HashEntry *entryPtr);




extern void Tcl_DeleteHashTable(Tcl_HashTable *tablePtr);




extern void Tcl_DeleteInterp(Tcl_Interp *interp);




extern void Tcl_DetachPids(int numPids, Tcl_Pid *pidPtr);




extern void Tcl_DeleteTimerHandler(Tcl_TimerToken token);




extern void Tcl_DeleteTrace(Tcl_Interp *interp, Tcl_Trace trace);




extern void Tcl_DontCallWhenDeleted(Tcl_Interp *interp,
    Tcl_InterpDeleteProc *proc,
    ClientData clientData);




extern int Tcl_DoOneEvent(int flags);




extern void Tcl_DoWhenIdle(Tcl_IdleProc *proc,
    ClientData clientData);




extern char * Tcl_DStringAppend(Tcl_DString *dsPtr,
    const char *bytes, int length);




extern char * Tcl_DStringAppendElement(Tcl_DString *dsPtr,
    const char *element);




extern void Tcl_DStringEndSublist(Tcl_DString *dsPtr);




extern void Tcl_DStringFree(Tcl_DString *dsPtr);




extern void Tcl_DStringGetResult(Tcl_Interp *interp,
    Tcl_DString *dsPtr);




extern void Tcl_DStringInit(Tcl_DString *dsPtr);




extern void Tcl_DStringResult(Tcl_Interp *interp,
    Tcl_DString *dsPtr);




extern void Tcl_DStringSetLength(Tcl_DString *dsPtr, int length);




extern void Tcl_DStringStartSublist(Tcl_DString *dsPtr);




extern int Tcl_Eof(Tcl_Channel chan);




extern const char * Tcl_ErrnoId(void);




extern const char * Tcl_ErrnoMsg(int err);




extern int Tcl_Eval(Tcl_Interp *interp, const char *script);




extern int Tcl_EvalFile(Tcl_Interp *interp,
    const char *fileName);




extern int Tcl_EvalObj(Tcl_Interp *interp, Tcl_Obj *objPtr);




extern void Tcl_EventuallyFree(ClientData clientData,
    Tcl_FreeProc *freeProc);




extern void Tcl_Exit(int status);




extern int Tcl_ExposeCommand(Tcl_Interp *interp,
    const char *hiddenCmdToken,
    const char *cmdName);




extern int Tcl_ExprBoolean(Tcl_Interp *interp, const char *expr,
    int *ptr);




extern int Tcl_ExprBooleanObj(Tcl_Interp *interp,
    Tcl_Obj *objPtr, int *ptr);




extern int Tcl_ExprDouble(Tcl_Interp *interp, const char *expr,
    double *ptr);




extern int Tcl_ExprDoubleObj(Tcl_Interp *interp,
    Tcl_Obj *objPtr, double *ptr);




extern int Tcl_ExprLong(Tcl_Interp *interp, const char *expr,
    long *ptr);




extern int Tcl_ExprLongObj(Tcl_Interp *interp, Tcl_Obj *objPtr,
    long *ptr);




extern int Tcl_ExprObj(Tcl_Interp *interp, Tcl_Obj *objPtr,
    Tcl_Obj **resultPtrPtr);




extern int Tcl_ExprString(Tcl_Interp *interp, const char *expr);




extern void Tcl_Finalize(void);




extern void Tcl_FindExecutable(const char *argv0);




extern Tcl_HashEntry * Tcl_FirstHashEntry(Tcl_HashTable *tablePtr,
    Tcl_HashSearch *searchPtr);




extern int Tcl_Flush(Tcl_Channel chan);




extern void Tcl_FreeResult(Tcl_Interp *interp);




extern int Tcl_GetAlias(Tcl_Interp *interp,
    const char *slaveCmd,
    Tcl_Interp **targetInterpPtr,
    char **targetCmdPtr, int *argcPtr,
    char ***argvPtr);




extern int Tcl_GetAliasObj(Tcl_Interp *interp,
    const char *slaveCmd,
    Tcl_Interp **targetInterpPtr,
    char **targetCmdPtr, int *objcPtr,
    Tcl_Obj ***objv);




extern ClientData Tcl_GetAssocData(Tcl_Interp *interp,
    const char *name,
    Tcl_InterpDeleteProc **procPtr);




extern Tcl_Channel Tcl_GetChannel(Tcl_Interp *interp,
    const char *chanName, int *modePtr);




extern int Tcl_GetChannelBufferSize(Tcl_Channel chan);




extern int Tcl_GetChannelHandle(Tcl_Channel chan, int direction,
    ClientData *handlePtr);




extern ClientData Tcl_GetChannelInstanceData(Tcl_Channel chan);




extern int Tcl_GetChannelMode(Tcl_Channel chan);




extern const char * Tcl_GetChannelName(Tcl_Channel chan);




extern int Tcl_GetChannelOption(Tcl_Interp *interp,
    Tcl_Channel chan, const char *optionName,
    Tcl_DString *dsPtr);




extern Tcl_ChannelType * Tcl_GetChannelType(Tcl_Channel chan);




extern int Tcl_GetCommandInfo(Tcl_Interp *interp,
    const char *cmdName, Tcl_CmdInfo *infoPtr);




extern const char * Tcl_GetCommandName(Tcl_Interp *interp,
    Tcl_Command command);




extern int Tcl_GetErrno(void);




extern const char * Tcl_GetHostName(void);




extern int Tcl_GetInterpPath(Tcl_Interp *askInterp,
    Tcl_Interp *slaveInterp);




extern Tcl_Interp * Tcl_GetMaster(Tcl_Interp *interp);




extern const char * Tcl_GetNameOfExecutable(void);




extern Tcl_Obj * Tcl_GetObjResult(Tcl_Interp *interp);





extern int Tcl_GetOpenFile(Tcl_Interp *interp,
    const char *chanID, int forWriting,
    int checkUsage, ClientData *filePtr);
# 1039 "/usr/include/tclDecls.h" 3 4
extern Tcl_PathType Tcl_GetPathType(const char *path);




extern int Tcl_Gets(Tcl_Channel chan, Tcl_DString *dsPtr);




extern int Tcl_GetsObj(Tcl_Channel chan, Tcl_Obj *objPtr);




extern int Tcl_GetServiceMode(void);




extern Tcl_Interp * Tcl_GetSlave(Tcl_Interp *interp,
    const char *slaveName);




extern Tcl_Channel Tcl_GetStdChannel(int type);




extern const char * Tcl_GetStringResult(Tcl_Interp *interp);




extern const char * Tcl_GetVar(Tcl_Interp *interp,
    const char *varName, int flags);




extern const char * Tcl_GetVar2(Tcl_Interp *interp,
    const char *part1, const char *part2,
    int flags);




extern int Tcl_GlobalEval(Tcl_Interp *interp,
    const char *command);




extern int Tcl_GlobalEvalObj(Tcl_Interp *interp,
    Tcl_Obj *objPtr);




extern int Tcl_HideCommand(Tcl_Interp *interp,
    const char *cmdName,
    const char *hiddenCmdToken);




extern int Tcl_Init(Tcl_Interp *interp);




extern void Tcl_InitHashTable(Tcl_HashTable *tablePtr,
    int keyType);




extern int Tcl_InputBlocked(Tcl_Channel chan);




extern int Tcl_InputBuffered(Tcl_Channel chan);




extern int Tcl_InterpDeleted(Tcl_Interp *interp);




extern int Tcl_IsSafe(Tcl_Interp *interp);




extern char * Tcl_JoinPath(int argc, char *const *argv,
    Tcl_DString *resultPtr);




extern int Tcl_LinkVar(Tcl_Interp *interp, const char *varName,
    char *addr, int type);





extern Tcl_Channel Tcl_MakeFileChannel(ClientData handle, int mode);




extern int Tcl_MakeSafe(Tcl_Interp *interp);




extern Tcl_Channel Tcl_MakeTcpClientChannel(ClientData tcpSocket);




extern char * Tcl_Merge(int argc, char *const *argv);




extern Tcl_HashEntry * Tcl_NextHashEntry(Tcl_HashSearch *searchPtr);




extern void Tcl_NotifyChannel(Tcl_Channel channel, int mask);




extern Tcl_Obj * Tcl_ObjGetVar2(Tcl_Interp *interp, Tcl_Obj *part1Ptr,
    Tcl_Obj *part2Ptr, int flags);




extern Tcl_Obj * Tcl_ObjSetVar2(Tcl_Interp *interp, Tcl_Obj *part1Ptr,
    Tcl_Obj *part2Ptr, Tcl_Obj *newValuePtr,
    int flags);




extern Tcl_Channel Tcl_OpenCommandChannel(Tcl_Interp *interp, int argc,
    char **argv, int flags);




extern Tcl_Channel Tcl_OpenFileChannel(Tcl_Interp *interp,
    const char *fileName, const char *modeString,
    int permissions);




extern Tcl_Channel Tcl_OpenTcpClient(Tcl_Interp *interp, int port,
    const char *address, const char *myaddr,
    int myport, int async);




extern Tcl_Channel Tcl_OpenTcpServer(Tcl_Interp *interp, int port,
    const char *host,
    Tcl_TcpAcceptProc *acceptProc,
    ClientData callbackData);




extern void Tcl_Preserve(ClientData data);




extern void Tcl_PrintDouble(Tcl_Interp *interp, double value,
    char *dst);




extern int Tcl_PutEnv(const char *assignment);




extern const char * Tcl_PosixError(Tcl_Interp *interp);




extern void Tcl_QueueEvent(Tcl_Event *evPtr,
    Tcl_QueuePosition position);




extern int Tcl_Read(Tcl_Channel chan, char *bufPtr, int toRead);




extern void Tcl_ReapDetachedProcs(void);




extern int Tcl_RecordAndEval(Tcl_Interp *interp,
    const char *cmd, int flags);




extern int Tcl_RecordAndEvalObj(Tcl_Interp *interp,
    Tcl_Obj *cmdPtr, int flags);




extern void Tcl_RegisterChannel(Tcl_Interp *interp,
    Tcl_Channel chan);




extern void Tcl_RegisterObjType(Tcl_ObjType *typePtr);




extern Tcl_RegExp Tcl_RegExpCompile(Tcl_Interp *interp,
    const char *pattern);




extern int Tcl_RegExpExec(Tcl_Interp *interp, Tcl_RegExp regexp,
    const char *text, const char *start);




extern int Tcl_RegExpMatch(Tcl_Interp *interp, const char *text,
    const char *pattern);




extern void Tcl_RegExpRange(Tcl_RegExp regexp, int index,
    char **startPtr,
    char **endPtr);




extern void Tcl_Release(ClientData clientData);




extern void Tcl_ResetResult(Tcl_Interp *interp);




extern int Tcl_ScanElement(const char *str, int *flagPtr);




extern int Tcl_ScanCountedElement(const char *str, int length,
    int *flagPtr);




extern int Tcl_SeekOld(Tcl_Channel chan, int offset, int mode);




extern int Tcl_ServiceAll(void);




extern int Tcl_ServiceEvent(int flags);




extern void Tcl_SetAssocData(Tcl_Interp *interp,
    const char *name, Tcl_InterpDeleteProc *proc,
    ClientData clientData);




extern void Tcl_SetChannelBufferSize(Tcl_Channel chan, int sz);




extern int Tcl_SetChannelOption(Tcl_Interp *interp,
    Tcl_Channel chan, const char *optionName,
    const char *newValue);




extern int Tcl_SetCommandInfo(Tcl_Interp *interp,
    const char *cmdName,
    const Tcl_CmdInfo *infoPtr);




extern void Tcl_SetErrno(int err);




extern void Tcl_SetErrorCode(Tcl_Interp *interp, ...);




extern void Tcl_SetMaxBlockTime(Tcl_Time *timePtr);




extern void Tcl_SetPanicProc(Tcl_PanicProc *panicProc);




extern int Tcl_SetRecursionLimit(Tcl_Interp *interp, int depth);




extern void Tcl_SetResult(Tcl_Interp *interp, char *result,
    Tcl_FreeProc *freeProc);




extern int Tcl_SetServiceMode(int mode);




extern void Tcl_SetObjErrorCode(Tcl_Interp *interp,
    Tcl_Obj *errorObjPtr);




extern void Tcl_SetObjResult(Tcl_Interp *interp,
    Tcl_Obj *resultObjPtr);




extern void Tcl_SetStdChannel(Tcl_Channel channel, int type);




extern const char * Tcl_SetVar(Tcl_Interp *interp,
    const char *varName, const char *newValue,
    int flags);




extern const char * Tcl_SetVar2(Tcl_Interp *interp,
    const char *part1, const char *part2,
    const char *newValue, int flags);




extern const char * Tcl_SignalId(int sig);




extern const char * Tcl_SignalMsg(int sig);




extern void Tcl_SourceRCFile(Tcl_Interp *interp);




extern int Tcl_SplitList(Tcl_Interp *interp,
    const char *listStr, int *argcPtr,
    char ***argvPtr);




extern void Tcl_SplitPath(const char *path, int *argcPtr,
    char ***argvPtr);




extern void Tcl_StaticPackage(Tcl_Interp *interp,
    const char *pkgName,
    Tcl_PackageInitProc *initProc,
    Tcl_PackageInitProc *safeInitProc);




extern int Tcl_StringMatch(const char *str, const char *pattern);




extern int Tcl_TellOld(Tcl_Channel chan);




extern int Tcl_TraceVar(Tcl_Interp *interp, const char *varName,
    int flags, Tcl_VarTraceProc *proc,
    ClientData clientData);




extern int Tcl_TraceVar2(Tcl_Interp *interp, const char *part1,
    const char *part2, int flags,
    Tcl_VarTraceProc *proc,
    ClientData clientData);




extern char * Tcl_TranslateFileName(Tcl_Interp *interp,
    const char *name, Tcl_DString *bufferPtr);




extern int Tcl_Ungets(Tcl_Channel chan, const char *str,
    int len, int atHead);




extern void Tcl_UnlinkVar(Tcl_Interp *interp,
    const char *varName);




extern int Tcl_UnregisterChannel(Tcl_Interp *interp,
    Tcl_Channel chan);




extern int Tcl_UnsetVar(Tcl_Interp *interp, const char *varName,
    int flags);




extern int Tcl_UnsetVar2(Tcl_Interp *interp, const char *part1,
    const char *part2, int flags);




extern void Tcl_UntraceVar(Tcl_Interp *interp,
    const char *varName, int flags,
    Tcl_VarTraceProc *proc,
    ClientData clientData);




extern void Tcl_UntraceVar2(Tcl_Interp *interp,
    const char *part1, const char *part2,
    int flags, Tcl_VarTraceProc *proc,
    ClientData clientData);




extern void Tcl_UpdateLinkedVar(Tcl_Interp *interp,
    const char *varName);




extern int Tcl_UpVar(Tcl_Interp *interp, const char *frameName,
    const char *varName, const char *localName,
    int flags);




extern int Tcl_UpVar2(Tcl_Interp *interp, const char *frameName,
    const char *part1, const char *part2,
    const char *localName, int flags);




extern int Tcl_VarEval(Tcl_Interp *interp, ...);




extern ClientData Tcl_VarTraceInfo(Tcl_Interp *interp,
    const char *varName, int flags,
    Tcl_VarTraceProc *procPtr,
    ClientData prevClientData);




extern ClientData Tcl_VarTraceInfo2(Tcl_Interp *interp,
    const char *part1, const char *part2,
    int flags, Tcl_VarTraceProc *procPtr,
    ClientData prevClientData);




extern int Tcl_Write(Tcl_Channel chan, const char *s, int slen);




extern void Tcl_WrongNumArgs(Tcl_Interp *interp, int objc,
    Tcl_Obj *const objv[], const char *message);




extern int Tcl_DumpActiveMemory(const char *fileName);




extern void Tcl_ValidateAllMemory(const char *file, int line);




extern void Tcl_AppendResultVA(Tcl_Interp *interp,
    va_list argList);




extern void Tcl_AppendStringsToObjVA(Tcl_Obj *objPtr,
    va_list argList);




extern char * Tcl_HashStats(Tcl_HashTable *tablePtr);




extern const char * Tcl_ParseVar(Tcl_Interp *interp,
    const char *start, char **termPtr);




extern const char * Tcl_PkgPresent(Tcl_Interp *interp,
    const char *name, const char *version,
    int exact);




extern const char * Tcl_PkgPresentEx(Tcl_Interp *interp,
    const char *name, const char *version,
    int exact, ClientData *clientDataPtr);




extern int Tcl_PkgProvide(Tcl_Interp *interp, const char *name,
    const char *version);




extern const char * Tcl_PkgRequire(Tcl_Interp *interp,
    const char *name, const char *version,
    int exact);




extern void Tcl_SetErrorCodeVA(Tcl_Interp *interp,
    va_list argList);




extern int Tcl_VarEvalVA(Tcl_Interp *interp, va_list argList);




extern Tcl_Pid Tcl_WaitPid(Tcl_Pid pid, int *statPtr, int options);




extern void Tcl_PanicVA(const char *format, va_list argList);




extern void Tcl_GetVersion(int *major, int *minor,
    int *patchLevel, int *type);




extern void Tcl_InitMemory(Tcl_Interp *interp);




extern Tcl_Channel Tcl_StackChannel(Tcl_Interp *interp,
    Tcl_ChannelType *typePtr,
    ClientData instanceData, int mask,
    Tcl_Channel prevChan);




extern int Tcl_UnstackChannel(Tcl_Interp *interp,
    Tcl_Channel chan);




extern Tcl_Channel Tcl_GetStackedChannel(Tcl_Channel chan);




extern void Tcl_SetMainLoop(Tcl_MainLoopProc *proc);





extern void Tcl_AppendObjToObj(Tcl_Obj *objPtr,
    Tcl_Obj *appendObjPtr);




extern Tcl_Encoding Tcl_CreateEncoding(const Tcl_EncodingType *typePtr);




extern void Tcl_CreateThreadExitHandler(Tcl_ExitProc *proc,
    ClientData clientData);




extern void Tcl_DeleteThreadExitHandler(Tcl_ExitProc *proc,
    ClientData clientData);




extern void Tcl_DiscardResult(Tcl_SavedResult *statePtr);




extern int Tcl_EvalEx(Tcl_Interp *interp, const char *script,
    int numBytes, int flags);




extern int Tcl_EvalObjv(Tcl_Interp *interp, int objc,
    Tcl_Obj *const objv[], int flags);




extern int Tcl_EvalObjEx(Tcl_Interp *interp, Tcl_Obj *objPtr,
    int flags);




extern void Tcl_ExitThread(int status);




extern int Tcl_ExternalToUtf(Tcl_Interp *interp,
    Tcl_Encoding encoding, const char *src,
    int srcLen, int flags,
    Tcl_EncodingState *statePtr, char *dst,
    int dstLen, int *srcReadPtr,
    int *dstWrotePtr, int *dstCharsPtr);




extern char * Tcl_ExternalToUtfDString(Tcl_Encoding encoding,
    const char *src, int srcLen,
    Tcl_DString *dsPtr);




extern void Tcl_FinalizeThread(void);




extern void Tcl_FinalizeNotifier(ClientData clientData);




extern void Tcl_FreeEncoding(Tcl_Encoding encoding);




extern Tcl_ThreadId Tcl_GetCurrentThread(void);




extern Tcl_Encoding Tcl_GetEncoding(Tcl_Interp *interp, const char *name);




extern const char * Tcl_GetEncodingName(Tcl_Encoding encoding);




extern void Tcl_GetEncodingNames(Tcl_Interp *interp);




extern int Tcl_GetIndexFromObjStruct(Tcl_Interp *interp,
    Tcl_Obj *objPtr, const void *tablePtr,
    int offset, const char *msg, int flags,
    int *indexPtr);




extern void * Tcl_GetThreadData(Tcl_ThreadDataKey *keyPtr,
    int size);




extern Tcl_Obj * Tcl_GetVar2Ex(Tcl_Interp *interp, const char *part1,
    const char *part2, int flags);




extern ClientData Tcl_InitNotifier(void);




extern void Tcl_MutexLock(Tcl_Mutex *mutexPtr);




extern void Tcl_MutexUnlock(Tcl_Mutex *mutexPtr);




extern void Tcl_ConditionNotify(Tcl_Condition *condPtr);




extern void Tcl_ConditionWait(Tcl_Condition *condPtr,
    Tcl_Mutex *mutexPtr, Tcl_Time *timePtr);




extern int Tcl_NumUtfChars(const char *src, int length);




extern int Tcl_ReadChars(Tcl_Channel channel, Tcl_Obj *objPtr,
    int charsToRead, int appendFlag);




extern void Tcl_RestoreResult(Tcl_Interp *interp,
    Tcl_SavedResult *statePtr);




extern void Tcl_SaveResult(Tcl_Interp *interp,
    Tcl_SavedResult *statePtr);




extern int Tcl_SetSystemEncoding(Tcl_Interp *interp,
    const char *name);




extern Tcl_Obj * Tcl_SetVar2Ex(Tcl_Interp *interp, const char *part1,
    const char *part2, Tcl_Obj *newValuePtr,
    int flags);




extern void Tcl_ThreadAlert(Tcl_ThreadId threadId);




extern void Tcl_ThreadQueueEvent(Tcl_ThreadId threadId,
    Tcl_Event *evPtr, Tcl_QueuePosition position);




extern Tcl_UniChar Tcl_UniCharAtIndex(const char *src, int index);




extern Tcl_UniChar Tcl_UniCharToLower(int ch);




extern Tcl_UniChar Tcl_UniCharToTitle(int ch);




extern Tcl_UniChar Tcl_UniCharToUpper(int ch);




extern int Tcl_UniCharToUtf(int ch, char *buf);




extern const char * Tcl_UtfAtIndex(const char *src, int index);




extern int Tcl_UtfCharComplete(const char *src, int length);




extern int Tcl_UtfBackslash(const char *src, int *readPtr,
    char *dst);




extern const char * Tcl_UtfFindFirst(const char *src, int ch);




extern const char * Tcl_UtfFindLast(const char *src, int ch);




extern const char * Tcl_UtfNext(const char *src);




extern const char * Tcl_UtfPrev(const char *src, const char *start);




extern int Tcl_UtfToExternal(Tcl_Interp *interp,
    Tcl_Encoding encoding, const char *src,
    int srcLen, int flags,
    Tcl_EncodingState *statePtr, char *dst,
    int dstLen, int *srcReadPtr,
    int *dstWrotePtr, int *dstCharsPtr);




extern char * Tcl_UtfToExternalDString(Tcl_Encoding encoding,
    const char *src, int srcLen,
    Tcl_DString *dsPtr);




extern int Tcl_UtfToLower(char *src);




extern int Tcl_UtfToTitle(char *src);




extern int Tcl_UtfToUniChar(const char *src, Tcl_UniChar *chPtr);




extern int Tcl_UtfToUpper(char *src);




extern int Tcl_WriteChars(Tcl_Channel chan, const char *src,
    int srcLen);




extern int Tcl_WriteObj(Tcl_Channel chan, Tcl_Obj *objPtr);




extern char * Tcl_GetString(Tcl_Obj *objPtr);




extern const char * Tcl_GetDefaultEncodingDir(void);




extern void Tcl_SetDefaultEncodingDir(const char *path);




extern void Tcl_AlertNotifier(ClientData clientData);




extern void Tcl_ServiceModeHook(int mode);




extern int Tcl_UniCharIsAlnum(int ch);




extern int Tcl_UniCharIsAlpha(int ch);




extern int Tcl_UniCharIsDigit(int ch);




extern int Tcl_UniCharIsLower(int ch);




extern int Tcl_UniCharIsSpace(int ch);




extern int Tcl_UniCharIsUpper(int ch);




extern int Tcl_UniCharIsWordChar(int ch);




extern int Tcl_UniCharLen(const Tcl_UniChar *uniStr);




extern int Tcl_UniCharNcmp(const Tcl_UniChar *ucs,
    const Tcl_UniChar *uct,
    unsigned long numChars);




extern char * Tcl_UniCharToUtfDString(const Tcl_UniChar *uniStr,
    int uniLength, Tcl_DString *dsPtr);




extern Tcl_UniChar * Tcl_UtfToUniCharDString(const char *src, int length,
    Tcl_DString *dsPtr);




extern Tcl_RegExp Tcl_GetRegExpFromObj(Tcl_Interp *interp,
    Tcl_Obj *patObj, int flags);




extern Tcl_Obj * Tcl_EvalTokens(Tcl_Interp *interp,
    Tcl_Token *tokenPtr, int count);




extern void Tcl_FreeParse(Tcl_Parse *parsePtr);




extern void Tcl_LogCommandInfo(Tcl_Interp *interp,
    const char *script, const char *command,
    int length);




extern int Tcl_ParseBraces(Tcl_Interp *interp,
    const char *start, int numBytes,
    Tcl_Parse *parsePtr, int append,
    char **termPtr);




extern int Tcl_ParseCommand(Tcl_Interp *interp,
    const char *start, int numBytes, int nested,
    Tcl_Parse *parsePtr);




extern int Tcl_ParseExpr(Tcl_Interp *interp, const char *start,
    int numBytes, Tcl_Parse *parsePtr);




extern int Tcl_ParseQuotedString(Tcl_Interp *interp,
    const char *start, int numBytes,
    Tcl_Parse *parsePtr, int append,
    char **termPtr);




extern int Tcl_ParseVarName(Tcl_Interp *interp,
    const char *start, int numBytes,
    Tcl_Parse *parsePtr, int append);




extern char * Tcl_GetCwd(Tcl_Interp *interp, Tcl_DString *cwdPtr);




extern int Tcl_Chdir(const char *dirName);




extern int Tcl_Access(const char *path, int mode);




extern int Tcl_Stat(const char *path, struct stat *bufPtr);




extern int Tcl_UtfNcmp(const char *s1, const char *s2,
    unsigned long n);




extern int Tcl_UtfNcasecmp(const char *s1, const char *s2,
    unsigned long n);




extern int Tcl_StringCaseMatch(const char *str,
    const char *pattern, int nocase);




extern int Tcl_UniCharIsControl(int ch);




extern int Tcl_UniCharIsGraph(int ch);




extern int Tcl_UniCharIsPrint(int ch);




extern int Tcl_UniCharIsPunct(int ch);




extern int Tcl_RegExpExecObj(Tcl_Interp *interp,
    Tcl_RegExp regexp, Tcl_Obj *textObj,
    int offset, int nmatches, int flags);




extern void Tcl_RegExpGetInfo(Tcl_RegExp regexp,
    Tcl_RegExpInfo *infoPtr);




extern Tcl_Obj * Tcl_NewUnicodeObj(const Tcl_UniChar *unicode,
    int numChars);




extern void Tcl_SetUnicodeObj(Tcl_Obj *objPtr,
    const Tcl_UniChar *unicode, int numChars);




extern int Tcl_GetCharLength(Tcl_Obj *objPtr);




extern Tcl_UniChar Tcl_GetUniChar(Tcl_Obj *objPtr, int index);




extern Tcl_UniChar * Tcl_GetUnicode(Tcl_Obj *objPtr);




extern Tcl_Obj * Tcl_GetRange(Tcl_Obj *objPtr, int first, int last);




extern void Tcl_AppendUnicodeToObj(Tcl_Obj *objPtr,
    const Tcl_UniChar *unicode, int length);




extern int Tcl_RegExpMatchObj(Tcl_Interp *interp,
    Tcl_Obj *textObj, Tcl_Obj *patternObj);




extern void Tcl_SetNotifier(Tcl_NotifierProcs *notifierProcPtr);




extern Tcl_Mutex * Tcl_GetAllocMutex(void);




extern int Tcl_GetChannelNames(Tcl_Interp *interp);




extern int Tcl_GetChannelNamesEx(Tcl_Interp *interp,
    const char *pattern);




extern int Tcl_ProcObjCmd(ClientData clientData,
    Tcl_Interp *interp, int objc,
    Tcl_Obj *const objv[]);




extern void Tcl_ConditionFinalize(Tcl_Condition *condPtr);




extern void Tcl_MutexFinalize(Tcl_Mutex *mutex);




extern int Tcl_CreateThread(Tcl_ThreadId *idPtr,
    Tcl_ThreadCreateProc proc,
    ClientData clientData, int stackSize,
    int flags);




extern int Tcl_ReadRaw(Tcl_Channel chan, char *dst,
    int bytesToRead);




extern int Tcl_WriteRaw(Tcl_Channel chan, const char *src,
    int srcLen);




extern Tcl_Channel Tcl_GetTopChannel(Tcl_Channel chan);




extern int Tcl_ChannelBuffered(Tcl_Channel chan);




extern const char * Tcl_ChannelName(
    const Tcl_ChannelType *chanTypePtr);




extern Tcl_ChannelTypeVersion Tcl_ChannelVersion(
    const Tcl_ChannelType *chanTypePtr);




extern Tcl_DriverBlockModeProc * Tcl_ChannelBlockModeProc(
    const Tcl_ChannelType *chanTypePtr);




extern Tcl_DriverCloseProc * Tcl_ChannelCloseProc(
    const Tcl_ChannelType *chanTypePtr);




extern Tcl_DriverClose2Proc * Tcl_ChannelClose2Proc(
    const Tcl_ChannelType *chanTypePtr);




extern Tcl_DriverInputProc * Tcl_ChannelInputProc(
    const Tcl_ChannelType *chanTypePtr);




extern Tcl_DriverOutputProc * Tcl_ChannelOutputProc(
    const Tcl_ChannelType *chanTypePtr);




extern Tcl_DriverSeekProc * Tcl_ChannelSeekProc(
    const Tcl_ChannelType *chanTypePtr);




extern Tcl_DriverSetOptionProc * Tcl_ChannelSetOptionProc(
    const Tcl_ChannelType *chanTypePtr);




extern Tcl_DriverGetOptionProc * Tcl_ChannelGetOptionProc(
    const Tcl_ChannelType *chanTypePtr);




extern Tcl_DriverWatchProc * Tcl_ChannelWatchProc(
    const Tcl_ChannelType *chanTypePtr);




extern Tcl_DriverGetHandleProc * Tcl_ChannelGetHandleProc(
    const Tcl_ChannelType *chanTypePtr);




extern Tcl_DriverFlushProc * Tcl_ChannelFlushProc(
    const Tcl_ChannelType *chanTypePtr);




extern Tcl_DriverHandlerProc * Tcl_ChannelHandlerProc(
    const Tcl_ChannelType *chanTypePtr);




extern int Tcl_JoinThread(Tcl_ThreadId threadId, int *result);




extern int Tcl_IsChannelShared(Tcl_Channel channel);




extern int Tcl_IsChannelRegistered(Tcl_Interp *interp,
    Tcl_Channel channel);




extern void Tcl_CutChannel(Tcl_Channel channel);




extern void Tcl_SpliceChannel(Tcl_Channel channel);




extern void Tcl_ClearChannelHandlers(Tcl_Channel channel);




extern int Tcl_IsChannelExisting(const char *channelName);




extern int Tcl_UniCharNcasecmp(const Tcl_UniChar *ucs,
    const Tcl_UniChar *uct,
    unsigned long numChars);




extern int Tcl_UniCharCaseMatch(const Tcl_UniChar *uniStr,
    const Tcl_UniChar *uniPattern, int nocase);




extern Tcl_HashEntry * Tcl_FindHashEntry(Tcl_HashTable *tablePtr,
    const char *key);




extern Tcl_HashEntry * Tcl_CreateHashEntry(Tcl_HashTable *tablePtr,
    const char *key, int *newPtr);




extern void Tcl_InitCustomHashTable(Tcl_HashTable *tablePtr,
    int keyType, Tcl_HashKeyType *typePtr);




extern void Tcl_InitObjHashTable(Tcl_HashTable *tablePtr);




extern ClientData Tcl_CommandTraceInfo(Tcl_Interp *interp,
    const char *varName, int flags,
    Tcl_CommandTraceProc *procPtr,
    ClientData prevClientData);




extern int Tcl_TraceCommand(Tcl_Interp *interp,
    const char *varName, int flags,
    Tcl_CommandTraceProc *proc,
    ClientData clientData);




extern void Tcl_UntraceCommand(Tcl_Interp *interp,
    const char *varName, int flags,
    Tcl_CommandTraceProc *proc,
    ClientData clientData);




extern char * Tcl_AttemptAlloc(unsigned int size);




extern char * Tcl_AttemptDbCkalloc(unsigned int size,
    const char *file, int line);




extern char * Tcl_AttemptRealloc(char *ptr, unsigned int size);




extern char * Tcl_AttemptDbCkrealloc(char *ptr, unsigned int size,
    const char *file, int line);




extern int Tcl_AttemptSetObjLength(Tcl_Obj *objPtr, int length);




extern Tcl_ThreadId Tcl_GetChannelThread(Tcl_Channel channel);




extern Tcl_UniChar * Tcl_GetUnicodeFromObj(Tcl_Obj *objPtr,
    int *lengthPtr);




extern int Tcl_GetMathFuncInfo(Tcl_Interp *interp,
    const char *name, int *numArgsPtr,
    Tcl_ValueType **argTypesPtr,
    Tcl_MathProc **procPtr,
    ClientData *clientDataPtr);




extern Tcl_Obj * Tcl_ListMathFuncs(Tcl_Interp *interp,
    const char *pattern);




extern Tcl_Obj * Tcl_SubstObj(Tcl_Interp *interp, Tcl_Obj *objPtr,
    int flags);




extern int Tcl_DetachChannel(Tcl_Interp *interp,
    Tcl_Channel channel);




extern int Tcl_IsStandardChannel(Tcl_Channel channel);




extern int Tcl_FSCopyFile(Tcl_Obj *srcPathPtr,
    Tcl_Obj *destPathPtr);




extern int Tcl_FSCopyDirectory(Tcl_Obj *srcPathPtr,
    Tcl_Obj *destPathPtr, Tcl_Obj **errorPtr);




extern int Tcl_FSCreateDirectory(Tcl_Obj *pathPtr);




extern int Tcl_FSDeleteFile(Tcl_Obj *pathPtr);




extern int Tcl_FSLoadFile(Tcl_Interp *interp, Tcl_Obj *pathPtr,
    const char *sym1, const char *sym2,
    Tcl_PackageInitProc **proc1Ptr,
    Tcl_PackageInitProc **proc2Ptr,
    Tcl_LoadHandle *handlePtr,
    Tcl_FSUnloadFileProc **unloadProcPtr);




extern int Tcl_FSMatchInDirectory(Tcl_Interp *interp,
    Tcl_Obj *result, Tcl_Obj *pathPtr,
    const char *pattern, Tcl_GlobTypeData *types);




extern Tcl_Obj * Tcl_FSLink(Tcl_Obj *pathPtr, Tcl_Obj *toPtr,
    int linkAction);




extern int Tcl_FSRemoveDirectory(Tcl_Obj *pathPtr,
    int recursive, Tcl_Obj **errorPtr);




extern int Tcl_FSRenameFile(Tcl_Obj *srcPathPtr,
    Tcl_Obj *destPathPtr);




extern int Tcl_FSLstat(Tcl_Obj *pathPtr, Tcl_StatBuf *buf);




extern int Tcl_FSUtime(Tcl_Obj *pathPtr, struct utimbuf *tval);




extern int Tcl_FSFileAttrsGet(Tcl_Interp *interp, int index,
    Tcl_Obj *pathPtr, Tcl_Obj **objPtrRef);




extern int Tcl_FSFileAttrsSet(Tcl_Interp *interp, int index,
    Tcl_Obj *pathPtr, Tcl_Obj *objPtr);




extern const char ** Tcl_FSFileAttrStrings(Tcl_Obj *pathPtr,
    Tcl_Obj **objPtrRef);




extern int Tcl_FSStat(Tcl_Obj *pathPtr, Tcl_StatBuf *buf);




extern int Tcl_FSAccess(Tcl_Obj *pathPtr, int mode);




extern Tcl_Channel Tcl_FSOpenFileChannel(Tcl_Interp *interp,
    Tcl_Obj *pathPtr, const char *modeString,
    int permissions);




extern Tcl_Obj * Tcl_FSGetCwd(Tcl_Interp *interp);




extern int Tcl_FSChdir(Tcl_Obj *pathPtr);




extern int Tcl_FSConvertToPathType(Tcl_Interp *interp,
    Tcl_Obj *pathPtr);




extern Tcl_Obj * Tcl_FSJoinPath(Tcl_Obj *listObj, int elements);




extern Tcl_Obj * Tcl_FSSplitPath(Tcl_Obj *pathPtr, int *lenPtr);




extern int Tcl_FSEqualPaths(Tcl_Obj *firstPtr,
    Tcl_Obj *secondPtr);




extern Tcl_Obj * Tcl_FSGetNormalizedPath(Tcl_Interp *interp,
    Tcl_Obj *pathPtr);




extern Tcl_Obj * Tcl_FSJoinToPath(Tcl_Obj *pathPtr, int objc,
    Tcl_Obj *const objv[]);




extern ClientData Tcl_FSGetInternalRep(Tcl_Obj *pathPtr,
    Tcl_Filesystem *fsPtr);




extern Tcl_Obj * Tcl_FSGetTranslatedPath(Tcl_Interp *interp,
    Tcl_Obj *pathPtr);




extern int Tcl_FSEvalFile(Tcl_Interp *interp, Tcl_Obj *fileName);




extern Tcl_Obj * Tcl_FSNewNativePath(Tcl_Filesystem *fromFilesystem,
    ClientData clientData);




extern const char * Tcl_FSGetNativePath(Tcl_Obj *pathPtr);




extern Tcl_Obj * Tcl_FSFileSystemInfo(Tcl_Obj *pathPtr);




extern Tcl_Obj * Tcl_FSPathSeparator(Tcl_Obj *pathPtr);




extern Tcl_Obj * Tcl_FSListVolumes(void);




extern int Tcl_FSRegister(ClientData clientData,
    Tcl_Filesystem *fsPtr);




extern int Tcl_FSUnregister(Tcl_Filesystem *fsPtr);




extern ClientData Tcl_FSData(Tcl_Filesystem *fsPtr);




extern const char * Tcl_FSGetTranslatedStringPath(Tcl_Interp *interp,
    Tcl_Obj *pathPtr);




extern Tcl_Filesystem * Tcl_FSGetFileSystemForPath(Tcl_Obj *pathPtr);




extern Tcl_PathType Tcl_FSGetPathType(Tcl_Obj *pathPtr);




extern int Tcl_OutputBuffered(Tcl_Channel chan);




extern void Tcl_FSMountsChanged(Tcl_Filesystem *fsPtr);




extern int Tcl_EvalTokensStandard(Tcl_Interp *interp,
    Tcl_Token *tokenPtr, int count);




extern void Tcl_GetTime(Tcl_Time *timeBuf);




extern Tcl_Trace Tcl_CreateObjTrace(Tcl_Interp *interp, int level,
    int flags, Tcl_CmdObjTraceProc *objProc,
    ClientData clientData,
    Tcl_CmdObjTraceDeleteProc *delProc);




extern int Tcl_GetCommandInfoFromToken(Tcl_Command token,
    Tcl_CmdInfo *infoPtr);




extern int Tcl_SetCommandInfoFromToken(Tcl_Command token,
    const Tcl_CmdInfo *infoPtr);




extern Tcl_Obj * Tcl_DbNewWideIntObj(Tcl_WideInt wideValue,
    const char *file, int line);




extern int Tcl_GetWideIntFromObj(Tcl_Interp *interp,
    Tcl_Obj *objPtr, Tcl_WideInt *widePtr);




extern Tcl_Obj * Tcl_NewWideIntObj(Tcl_WideInt wideValue);




extern void Tcl_SetWideIntObj(Tcl_Obj *objPtr,
    Tcl_WideInt wideValue);




extern Tcl_StatBuf * Tcl_AllocStatBuf(void);




extern Tcl_WideInt Tcl_Seek(Tcl_Channel chan, Tcl_WideInt offset,
    int mode);




extern Tcl_WideInt Tcl_Tell(Tcl_Channel chan);




extern Tcl_DriverWideSeekProc * Tcl_ChannelWideSeekProc(
    const Tcl_ChannelType *chanTypePtr);




extern int Tcl_DictObjPut(Tcl_Interp *interp, Tcl_Obj *dictPtr,
    Tcl_Obj *keyPtr, Tcl_Obj *valuePtr);




extern int Tcl_DictObjGet(Tcl_Interp *interp, Tcl_Obj *dictPtr,
    Tcl_Obj *keyPtr, Tcl_Obj **valuePtrPtr);




extern int Tcl_DictObjRemove(Tcl_Interp *interp,
    Tcl_Obj *dictPtr, Tcl_Obj *keyPtr);




extern int Tcl_DictObjSize(Tcl_Interp *interp, Tcl_Obj *dictPtr,
    int *sizePtr);




extern int Tcl_DictObjFirst(Tcl_Interp *interp,
    Tcl_Obj *dictPtr, Tcl_DictSearch *searchPtr,
    Tcl_Obj **keyPtrPtr, Tcl_Obj **valuePtrPtr,
    int *donePtr);




extern void Tcl_DictObjNext(Tcl_DictSearch *searchPtr,
    Tcl_Obj **keyPtrPtr, Tcl_Obj **valuePtrPtr,
    int *donePtr);




extern void Tcl_DictObjDone(Tcl_DictSearch *searchPtr);




extern int Tcl_DictObjPutKeyList(Tcl_Interp *interp,
    Tcl_Obj *dictPtr, int keyc,
    Tcl_Obj *const *keyv, Tcl_Obj *valuePtr);




extern int Tcl_DictObjRemoveKeyList(Tcl_Interp *interp,
    Tcl_Obj *dictPtr, int keyc,
    Tcl_Obj *const *keyv);




extern Tcl_Obj * Tcl_NewDictObj(void);




extern Tcl_Obj * Tcl_DbNewDictObj(const char *file, int line);




extern void Tcl_RegisterConfig(Tcl_Interp *interp,
    const char *pkgName,
    Tcl_Config *configuration,
    const char *valEncoding);




extern Tcl_Namespace * Tcl_CreateNamespace(Tcl_Interp *interp,
    const char *name, ClientData clientData,
    Tcl_NamespaceDeleteProc *deleteProc);




extern void Tcl_DeleteNamespace(Tcl_Namespace *nsPtr);




extern int Tcl_AppendExportList(Tcl_Interp *interp,
    Tcl_Namespace *nsPtr, Tcl_Obj *objPtr);




extern int Tcl_Export(Tcl_Interp *interp, Tcl_Namespace *nsPtr,
    const char *pattern, int resetListFirst);




extern int Tcl_Import(Tcl_Interp *interp, Tcl_Namespace *nsPtr,
    const char *pattern, int allowOverwrite);




extern int Tcl_ForgetImport(Tcl_Interp *interp,
    Tcl_Namespace *nsPtr, const char *pattern);




extern Tcl_Namespace * Tcl_GetCurrentNamespace(Tcl_Interp *interp);




extern Tcl_Namespace * Tcl_GetGlobalNamespace(Tcl_Interp *interp);




extern Tcl_Namespace * Tcl_FindNamespace(Tcl_Interp *interp,
    const char *name,
    Tcl_Namespace *contextNsPtr, int flags);




extern Tcl_Command Tcl_FindCommand(Tcl_Interp *interp, const char *name,
    Tcl_Namespace *contextNsPtr, int flags);




extern Tcl_Command Tcl_GetCommandFromObj(Tcl_Interp *interp,
    Tcl_Obj *objPtr);




extern void Tcl_GetCommandFullName(Tcl_Interp *interp,
    Tcl_Command command, Tcl_Obj *objPtr);




extern int Tcl_FSEvalFileEx(Tcl_Interp *interp,
    Tcl_Obj *fileName, const char *encodingName);




extern Tcl_ExitProc * Tcl_SetExitProc(Tcl_ExitProc *proc);




extern void Tcl_LimitAddHandler(Tcl_Interp *interp, int type,
    Tcl_LimitHandlerProc *handlerProc,
    ClientData clientData,
    Tcl_LimitHandlerDeleteProc *deleteProc);




extern void Tcl_LimitRemoveHandler(Tcl_Interp *interp, int type,
    Tcl_LimitHandlerProc *handlerProc,
    ClientData clientData);




extern int Tcl_LimitReady(Tcl_Interp *interp);




extern int Tcl_LimitCheck(Tcl_Interp *interp);




extern int Tcl_LimitExceeded(Tcl_Interp *interp);




extern void Tcl_LimitSetCommands(Tcl_Interp *interp,
    int commandLimit);




extern void Tcl_LimitSetTime(Tcl_Interp *interp,
    Tcl_Time *timeLimitPtr);




extern void Tcl_LimitSetGranularity(Tcl_Interp *interp, int type,
    int granularity);




extern int Tcl_LimitTypeEnabled(Tcl_Interp *interp, int type);




extern int Tcl_LimitTypeExceeded(Tcl_Interp *interp, int type);




extern void Tcl_LimitTypeSet(Tcl_Interp *interp, int type);




extern void Tcl_LimitTypeReset(Tcl_Interp *interp, int type);




extern int Tcl_LimitGetCommands(Tcl_Interp *interp);




extern void Tcl_LimitGetTime(Tcl_Interp *interp,
    Tcl_Time *timeLimitPtr);




extern int Tcl_LimitGetGranularity(Tcl_Interp *interp, int type);




extern Tcl_InterpState Tcl_SaveInterpState(Tcl_Interp *interp, int status);




extern int Tcl_RestoreInterpState(Tcl_Interp *interp,
    Tcl_InterpState state);




extern void Tcl_DiscardInterpState(Tcl_InterpState state);




extern int Tcl_SetReturnOptions(Tcl_Interp *interp,
    Tcl_Obj *options);




extern Tcl_Obj * Tcl_GetReturnOptions(Tcl_Interp *interp, int result);




extern int Tcl_IsEnsemble(Tcl_Command token);




extern Tcl_Command Tcl_CreateEnsemble(Tcl_Interp *interp,
    const char *name,
    Tcl_Namespace *namespacePtr, int flags);




extern Tcl_Command Tcl_FindEnsemble(Tcl_Interp *interp,
    Tcl_Obj *cmdNameObj, int flags);




extern int Tcl_SetEnsembleSubcommandList(Tcl_Interp *interp,
    Tcl_Command token, Tcl_Obj *subcmdList);




extern int Tcl_SetEnsembleMappingDict(Tcl_Interp *interp,
    Tcl_Command token, Tcl_Obj *mapDict);




extern int Tcl_SetEnsembleUnknownHandler(Tcl_Interp *interp,
    Tcl_Command token, Tcl_Obj *unknownList);




extern int Tcl_SetEnsembleFlags(Tcl_Interp *interp,
    Tcl_Command token, int flags);




extern int Tcl_GetEnsembleSubcommandList(Tcl_Interp *interp,
    Tcl_Command token, Tcl_Obj **subcmdListPtr);




extern int Tcl_GetEnsembleMappingDict(Tcl_Interp *interp,
    Tcl_Command token, Tcl_Obj **mapDictPtr);




extern int Tcl_GetEnsembleUnknownHandler(Tcl_Interp *interp,
    Tcl_Command token, Tcl_Obj **unknownListPtr);




extern int Tcl_GetEnsembleFlags(Tcl_Interp *interp,
    Tcl_Command token, int *flagsPtr);




extern int Tcl_GetEnsembleNamespace(Tcl_Interp *interp,
    Tcl_Command token,
    Tcl_Namespace **namespacePtrPtr);




extern void Tcl_SetTimeProc(Tcl_GetTimeProc *getProc,
    Tcl_ScaleTimeProc *scaleProc,
    ClientData clientData);




extern void Tcl_QueryTimeProc(Tcl_GetTimeProc **getProc,
    Tcl_ScaleTimeProc **scaleProc,
    ClientData *clientData);




extern Tcl_DriverThreadActionProc * Tcl_ChannelThreadActionProc(
    const Tcl_ChannelType *chanTypePtr);




extern Tcl_Obj * Tcl_NewBignumObj(mp_int *value);




extern Tcl_Obj * Tcl_DbNewBignumObj(mp_int *value, const char *file,
    int line);




extern void Tcl_SetBignumObj(Tcl_Obj *obj, mp_int *value);




extern int Tcl_GetBignumFromObj(Tcl_Interp *interp,
    Tcl_Obj *obj, mp_int *value);




extern int Tcl_TakeBignumFromObj(Tcl_Interp *interp,
    Tcl_Obj *obj, mp_int *value);




extern int Tcl_TruncateChannel(Tcl_Channel chan,
    Tcl_WideInt length);




extern Tcl_DriverTruncateProc * Tcl_ChannelTruncateProc(
    const Tcl_ChannelType *chanTypePtr);




extern void Tcl_SetChannelErrorInterp(Tcl_Interp *interp,
    Tcl_Obj *msg);




extern void Tcl_GetChannelErrorInterp(Tcl_Interp *interp,
    Tcl_Obj **msg);




extern void Tcl_SetChannelError(Tcl_Channel chan, Tcl_Obj *msg);




extern void Tcl_GetChannelError(Tcl_Channel chan, Tcl_Obj **msg);




extern int Tcl_InitBignumFromDouble(Tcl_Interp *interp,
    double initval, mp_int *toInit);




extern Tcl_Obj * Tcl_GetNamespaceUnknownHandler(Tcl_Interp *interp,
    Tcl_Namespace *nsPtr);




extern int Tcl_SetNamespaceUnknownHandler(Tcl_Interp *interp,
    Tcl_Namespace *nsPtr, Tcl_Obj *handlerPtr);




extern int Tcl_GetEncodingFromObj(Tcl_Interp *interp,
    Tcl_Obj *objPtr, Tcl_Encoding *encodingPtr);




extern Tcl_Obj * Tcl_GetEncodingSearchPath(void);




extern int Tcl_SetEncodingSearchPath(Tcl_Obj *searchPath);




extern const char * Tcl_GetEncodingNameFromEnvironment(
    Tcl_DString *bufPtr);




extern int Tcl_PkgRequireProc(Tcl_Interp *interp,
    const char *name, int objc,
    Tcl_Obj *const objv[],
    ClientData *clientDataPtr);




extern void Tcl_AppendObjToErrorInfo(Tcl_Interp *interp,
    Tcl_Obj *objPtr);




extern void Tcl_AppendLimitedToObj(Tcl_Obj *objPtr,
    const char *bytes, int length, int limit,
    const char *ellipsis);




extern Tcl_Obj * Tcl_Format(Tcl_Interp *interp, const char *format,
    int objc, Tcl_Obj *const objv[]);




extern int Tcl_AppendFormatToObj(Tcl_Interp *interp,
    Tcl_Obj *objPtr, const char *format,
    int objc, Tcl_Obj *const objv[]);




extern Tcl_Obj * Tcl_ObjPrintf(const char *format, ...);




extern void Tcl_AppendPrintfToObj(Tcl_Obj *objPtr,
    const char *format, ...);


typedef struct TclStubHooks {
    struct TclPlatStubs *tclPlatStubs;
    struct TclIntStubs *tclIntStubs;
    struct TclIntPlatStubs *tclIntPlatStubs;
} TclStubHooks;

typedef struct TclStubs {
    int magic;
    struct TclStubHooks *hooks;

    int (*tcl_PkgProvideEx) (Tcl_Interp *interp, const char *name, const char *version, ClientData clientData);
    const char * (*tcl_PkgRequireEx) (Tcl_Interp *interp, const char *name, const char *version, int exact, ClientData *clientDataPtr);
    void (*tcl_Panic) (const char *format, ...);
    char * (*tcl_Alloc) (unsigned int size);
    void (*tcl_Free) (char *ptr);
    char * (*tcl_Realloc) (char *ptr, unsigned int size);
    char * (*tcl_DbCkalloc) (unsigned int size, const char *file, int line);
    int (*tcl_DbCkfree) (char *ptr, const char *file, int line);
    char * (*tcl_DbCkrealloc) (char *ptr, unsigned int size, const char *file, int line);

    void (*tcl_CreateFileHandler) (int fd, int mask, Tcl_FileProc *proc, ClientData clientData);
# 3443 "/usr/include/tclDecls.h" 3 4
    void (*tcl_DeleteFileHandler) (int fd);







    void (*tcl_SetTimer) (Tcl_Time *timePtr);
    void (*tcl_Sleep) (int ms);
    int (*tcl_WaitForEvent) (Tcl_Time *timePtr);
    int (*tcl_AppendAllObjTypes) (Tcl_Interp *interp, Tcl_Obj *objPtr);
    void (*tcl_AppendStringsToObj) (Tcl_Obj *objPtr, ...);
    void (*tcl_AppendToObj) (Tcl_Obj *objPtr, const char *bytes, int length);
    Tcl_Obj * (*tcl_ConcatObj) (int objc, Tcl_Obj *const objv[]);
    int (*tcl_ConvertToType) (Tcl_Interp *interp, Tcl_Obj *objPtr, Tcl_ObjType *typePtr);
    void (*tcl_DbDecrRefCount) (Tcl_Obj *objPtr, const char *file, int line);
    void (*tcl_DbIncrRefCount) (Tcl_Obj *objPtr, const char *file, int line);
    int (*tcl_DbIsShared) (Tcl_Obj *objPtr, const char *file, int line);
    Tcl_Obj * (*tcl_DbNewBooleanObj) (int boolValue, const char *file, int line);
    Tcl_Obj * (*tcl_DbNewByteArrayObj) (const unsigned char *bytes, int length, const char *file, int line);
    Tcl_Obj * (*tcl_DbNewDoubleObj) (double doubleValue, const char *file, int line);
    Tcl_Obj * (*tcl_DbNewListObj) (int objc, Tcl_Obj *const *objv, const char *file, int line);
    Tcl_Obj * (*tcl_DbNewLongObj) (long longValue, const char *file, int line);
    Tcl_Obj * (*tcl_DbNewObj) (const char *file, int line);
    Tcl_Obj * (*tcl_DbNewStringObj) (const char *bytes, int length, const char *file, int line);
    Tcl_Obj * (*tcl_DuplicateObj) (Tcl_Obj *objPtr);
    void (*tclFreeObj) (Tcl_Obj *objPtr);
    int (*tcl_GetBoolean) (Tcl_Interp *interp, const char *src, int *boolPtr);
    int (*tcl_GetBooleanFromObj) (Tcl_Interp *interp, Tcl_Obj *objPtr, int *boolPtr);
    unsigned char * (*tcl_GetByteArrayFromObj) (Tcl_Obj *objPtr, int *lengthPtr);
    int (*tcl_GetDouble) (Tcl_Interp *interp, const char *src, double *doublePtr);
    int (*tcl_GetDoubleFromObj) (Tcl_Interp *interp, Tcl_Obj *objPtr, double *doublePtr);
    int (*tcl_GetIndexFromObj) (Tcl_Interp *interp, Tcl_Obj *objPtr, char **tablePtr, const char *msg, int flags, int *indexPtr);
    int (*tcl_GetInt) (Tcl_Interp *interp, const char *src, int *intPtr);
    int (*tcl_GetIntFromObj) (Tcl_Interp *interp, Tcl_Obj *objPtr, int *intPtr);
    int (*tcl_GetLongFromObj) (Tcl_Interp *interp, Tcl_Obj *objPtr, long *longPtr);
    Tcl_ObjType * (*tcl_GetObjType) (const char *typeName);
    char * (*tcl_GetStringFromObj) (Tcl_Obj *objPtr, int *lengthPtr);
    void (*tcl_InvalidateStringRep) (Tcl_Obj *objPtr);
    int (*tcl_ListObjAppendList) (Tcl_Interp *interp, Tcl_Obj *listPtr, Tcl_Obj *elemListPtr);
    int (*tcl_ListObjAppendElement) (Tcl_Interp *interp, Tcl_Obj *listPtr, Tcl_Obj *objPtr);
    int (*tcl_ListObjGetElements) (Tcl_Interp *interp, Tcl_Obj *listPtr, int *objcPtr, Tcl_Obj ***objvPtr);
    int (*tcl_ListObjIndex) (Tcl_Interp *interp, Tcl_Obj *listPtr, int index, Tcl_Obj **objPtrPtr);
    int (*tcl_ListObjLength) (Tcl_Interp *interp, Tcl_Obj *listPtr, int *lengthPtr);
    int (*tcl_ListObjReplace) (Tcl_Interp *interp, Tcl_Obj *listPtr, int first, int count, int objc, Tcl_Obj *const objv[]);
    Tcl_Obj * (*tcl_NewBooleanObj) (int boolValue);
    Tcl_Obj * (*tcl_NewByteArrayObj) (const unsigned char *bytes, int length);
    Tcl_Obj * (*tcl_NewDoubleObj) (double doubleValue);
    Tcl_Obj * (*tcl_NewIntObj) (int intValue);
    Tcl_Obj * (*tcl_NewListObj) (int objc, Tcl_Obj *const objv[]);
    Tcl_Obj * (*tcl_NewLongObj) (long longValue);
    Tcl_Obj * (*tcl_NewObj) (void);
    Tcl_Obj * (*tcl_NewStringObj) (const char *bytes, int length);
    void (*tcl_SetBooleanObj) (Tcl_Obj *objPtr, int boolValue);
    unsigned char * (*tcl_SetByteArrayLength) (Tcl_Obj *objPtr, int length);
    void (*tcl_SetByteArrayObj) (Tcl_Obj *objPtr, const unsigned char *bytes, int length);
    void (*tcl_SetDoubleObj) (Tcl_Obj *objPtr, double doubleValue);
    void (*tcl_SetIntObj) (Tcl_Obj *objPtr, int intValue);
    void (*tcl_SetListObj) (Tcl_Obj *objPtr, int objc, Tcl_Obj *const objv[]);
    void (*tcl_SetLongObj) (Tcl_Obj *objPtr, long longValue);
    void (*tcl_SetObjLength) (Tcl_Obj *objPtr, int length);
    void (*tcl_SetStringObj) (Tcl_Obj *objPtr, const char *bytes, int length);
    void (*tcl_AddErrorInfo) (Tcl_Interp *interp, const char *message);
    void (*tcl_AddObjErrorInfo) (Tcl_Interp *interp, const char *message, int length);
    void (*tcl_AllowExceptions) (Tcl_Interp *interp);
    void (*tcl_AppendElement) (Tcl_Interp *interp, const char *element);
    void (*tcl_AppendResult) (Tcl_Interp *interp, ...);
    Tcl_AsyncHandler (*tcl_AsyncCreate) (Tcl_AsyncProc *proc, ClientData clientData);
    void (*tcl_AsyncDelete) (Tcl_AsyncHandler async);
    int (*tcl_AsyncInvoke) (Tcl_Interp *interp, int code);
    void (*tcl_AsyncMark) (Tcl_AsyncHandler async);
    int (*tcl_AsyncReady) (void);
    void (*tcl_BackgroundError) (Tcl_Interp *interp);
    char (*tcl_Backslash) (const char *src, int *readPtr);
    int (*tcl_BadChannelOption) (Tcl_Interp *interp, const char *optionName, const char *optionList);
    void (*tcl_CallWhenDeleted) (Tcl_Interp *interp, Tcl_InterpDeleteProc *proc, ClientData clientData);
    void (*tcl_CancelIdleCall) (Tcl_IdleProc *idleProc, ClientData clientData);
    int (*tcl_Close) (Tcl_Interp *interp, Tcl_Channel chan);
    int (*tcl_CommandComplete) (const char *cmd);
    char * (*tcl_Concat) (int argc, char *const *argv);
    int (*tcl_ConvertElement) (const char *src, char *dst, int flags);
    int (*tcl_ConvertCountedElement) (const char *src, int length, char *dst, int flags);
    int (*tcl_CreateAlias) (Tcl_Interp *slave, const char *slaveCmd, Tcl_Interp *target, const char *targetCmd, int argc, char *const *argv);
    int (*tcl_CreateAliasObj) (Tcl_Interp *slave, const char *slaveCmd, Tcl_Interp *target, const char *targetCmd, int objc, Tcl_Obj *const objv[]);
    Tcl_Channel (*tcl_CreateChannel) (Tcl_ChannelType *typePtr, const char *chanName, ClientData instanceData, int mask);
    void (*tcl_CreateChannelHandler) (Tcl_Channel chan, int mask, Tcl_ChannelProc *proc, ClientData clientData);
    void (*tcl_CreateCloseHandler) (Tcl_Channel chan, Tcl_CloseProc *proc, ClientData clientData);
    Tcl_Command (*tcl_CreateCommand) (Tcl_Interp *interp, const char *cmdName, Tcl_CmdProc *proc, ClientData clientData, Tcl_CmdDeleteProc *deleteProc);
    void (*tcl_CreateEventSource) (Tcl_EventSetupProc *setupProc, Tcl_EventCheckProc *checkProc, ClientData clientData);
    void (*tcl_CreateExitHandler) (Tcl_ExitProc *proc, ClientData clientData);
    Tcl_Interp * (*tcl_CreateInterp) (void);
    void (*tcl_CreateMathFunc) (Tcl_Interp *interp, const char *name, int numArgs, Tcl_ValueType *argTypes, Tcl_MathProc *proc, ClientData clientData);
    Tcl_Command (*tcl_CreateObjCommand) (Tcl_Interp *interp, const char *cmdName, Tcl_ObjCmdProc *proc, ClientData clientData, Tcl_CmdDeleteProc *deleteProc);
    Tcl_Interp * (*tcl_CreateSlave) (Tcl_Interp *interp, const char *slaveName, int isSafe);
    Tcl_TimerToken (*tcl_CreateTimerHandler) (int milliseconds, Tcl_TimerProc *proc, ClientData clientData);
    Tcl_Trace (*tcl_CreateTrace) (Tcl_Interp *interp, int level, Tcl_CmdTraceProc *proc, ClientData clientData);
    void (*tcl_DeleteAssocData) (Tcl_Interp *interp, const char *name);
    void (*tcl_DeleteChannelHandler) (Tcl_Channel chan, Tcl_ChannelProc *proc, ClientData clientData);
    void (*tcl_DeleteCloseHandler) (Tcl_Channel chan, Tcl_CloseProc *proc, ClientData clientData);
    int (*tcl_DeleteCommand) (Tcl_Interp *interp, const char *cmdName);
    int (*tcl_DeleteCommandFromToken) (Tcl_Interp *interp, Tcl_Command command);
    void (*tcl_DeleteEvents) (Tcl_EventDeleteProc *proc, ClientData clientData);
    void (*tcl_DeleteEventSource) (Tcl_EventSetupProc *setupProc, Tcl_EventCheckProc *checkProc, ClientData clientData);
    void (*tcl_DeleteExitHandler) (Tcl_ExitProc *proc, ClientData clientData);
    void (*tcl_DeleteHashEntry) (Tcl_HashEntry *entryPtr);
    void (*tcl_DeleteHashTable) (Tcl_HashTable *tablePtr);
    void (*tcl_DeleteInterp) (Tcl_Interp *interp);
    void (*tcl_DetachPids) (int numPids, Tcl_Pid *pidPtr);
    void (*tcl_DeleteTimerHandler) (Tcl_TimerToken token);
    void (*tcl_DeleteTrace) (Tcl_Interp *interp, Tcl_Trace trace);
    void (*tcl_DontCallWhenDeleted) (Tcl_Interp *interp, Tcl_InterpDeleteProc *proc, ClientData clientData);
    int (*tcl_DoOneEvent) (int flags);
    void (*tcl_DoWhenIdle) (Tcl_IdleProc *proc, ClientData clientData);
    char * (*tcl_DStringAppend) (Tcl_DString *dsPtr, const char *bytes, int length);
    char * (*tcl_DStringAppendElement) (Tcl_DString *dsPtr, const char *element);
    void (*tcl_DStringEndSublist) (Tcl_DString *dsPtr);
    void (*tcl_DStringFree) (Tcl_DString *dsPtr);
    void (*tcl_DStringGetResult) (Tcl_Interp *interp, Tcl_DString *dsPtr);
    void (*tcl_DStringInit) (Tcl_DString *dsPtr);
    void (*tcl_DStringResult) (Tcl_Interp *interp, Tcl_DString *dsPtr);
    void (*tcl_DStringSetLength) (Tcl_DString *dsPtr, int length);
    void (*tcl_DStringStartSublist) (Tcl_DString *dsPtr);
    int (*tcl_Eof) (Tcl_Channel chan);
    const char * (*tcl_ErrnoId) (void);
    const char * (*tcl_ErrnoMsg) (int err);
    int (*tcl_Eval) (Tcl_Interp *interp, const char *script);
    int (*tcl_EvalFile) (Tcl_Interp *interp, const char *fileName);
    int (*tcl_EvalObj) (Tcl_Interp *interp, Tcl_Obj *objPtr);
    void (*tcl_EventuallyFree) (ClientData clientData, Tcl_FreeProc *freeProc);
    void (*tcl_Exit) (int status);
    int (*tcl_ExposeCommand) (Tcl_Interp *interp, const char *hiddenCmdToken, const char *cmdName);
    int (*tcl_ExprBoolean) (Tcl_Interp *interp, const char *expr, int *ptr);
    int (*tcl_ExprBooleanObj) (Tcl_Interp *interp, Tcl_Obj *objPtr, int *ptr);
    int (*tcl_ExprDouble) (Tcl_Interp *interp, const char *expr, double *ptr);
    int (*tcl_ExprDoubleObj) (Tcl_Interp *interp, Tcl_Obj *objPtr, double *ptr);
    int (*tcl_ExprLong) (Tcl_Interp *interp, const char *expr, long *ptr);
    int (*tcl_ExprLongObj) (Tcl_Interp *interp, Tcl_Obj *objPtr, long *ptr);
    int (*tcl_ExprObj) (Tcl_Interp *interp, Tcl_Obj *objPtr, Tcl_Obj **resultPtrPtr);
    int (*tcl_ExprString) (Tcl_Interp *interp, const char *expr);
    void (*tcl_Finalize) (void);
    void (*tcl_FindExecutable) (const char *argv0);
    Tcl_HashEntry * (*tcl_FirstHashEntry) (Tcl_HashTable *tablePtr, Tcl_HashSearch *searchPtr);
    int (*tcl_Flush) (Tcl_Channel chan);
    void (*tcl_FreeResult) (Tcl_Interp *interp);
    int (*tcl_GetAlias) (Tcl_Interp *interp, const char *slaveCmd, Tcl_Interp **targetInterpPtr, char **targetCmdPtr, int *argcPtr, char ***argvPtr);
    int (*tcl_GetAliasObj) (Tcl_Interp *interp, const char *slaveCmd, Tcl_Interp **targetInterpPtr, char **targetCmdPtr, int *objcPtr, Tcl_Obj ***objv);
    ClientData (*tcl_GetAssocData) (Tcl_Interp *interp, const char *name, Tcl_InterpDeleteProc **procPtr);
    Tcl_Channel (*tcl_GetChannel) (Tcl_Interp *interp, const char *chanName, int *modePtr);
    int (*tcl_GetChannelBufferSize) (Tcl_Channel chan);
    int (*tcl_GetChannelHandle) (Tcl_Channel chan, int direction, ClientData *handlePtr);
    ClientData (*tcl_GetChannelInstanceData) (Tcl_Channel chan);
    int (*tcl_GetChannelMode) (Tcl_Channel chan);
    const char * (*tcl_GetChannelName) (Tcl_Channel chan);
    int (*tcl_GetChannelOption) (Tcl_Interp *interp, Tcl_Channel chan, const char *optionName, Tcl_DString *dsPtr);
    Tcl_ChannelType * (*tcl_GetChannelType) (Tcl_Channel chan);
    int (*tcl_GetCommandInfo) (Tcl_Interp *interp, const char *cmdName, Tcl_CmdInfo *infoPtr);
    const char * (*tcl_GetCommandName) (Tcl_Interp *interp, Tcl_Command command);
    int (*tcl_GetErrno) (void);
    const char * (*tcl_GetHostName) (void);
    int (*tcl_GetInterpPath) (Tcl_Interp *askInterp, Tcl_Interp *slaveInterp);
    Tcl_Interp * (*tcl_GetMaster) (Tcl_Interp *interp);
    const char * (*tcl_GetNameOfExecutable) (void);
    Tcl_Obj * (*tcl_GetObjResult) (Tcl_Interp *interp);

    int (*tcl_GetOpenFile) (Tcl_Interp *interp, const char *chanID, int forWriting, int checkUsage, ClientData *filePtr);







    Tcl_PathType (*tcl_GetPathType) (const char *path);
    int (*tcl_Gets) (Tcl_Channel chan, Tcl_DString *dsPtr);
    int (*tcl_GetsObj) (Tcl_Channel chan, Tcl_Obj *objPtr);
    int (*tcl_GetServiceMode) (void);
    Tcl_Interp * (*tcl_GetSlave) (Tcl_Interp *interp, const char *slaveName);
    Tcl_Channel (*tcl_GetStdChannel) (int type);
    const char * (*tcl_GetStringResult) (Tcl_Interp *interp);
    const char * (*tcl_GetVar) (Tcl_Interp *interp, const char *varName, int flags);
    const char * (*tcl_GetVar2) (Tcl_Interp *interp, const char *part1, const char *part2, int flags);
    int (*tcl_GlobalEval) (Tcl_Interp *interp, const char *command);
    int (*tcl_GlobalEvalObj) (Tcl_Interp *interp, Tcl_Obj *objPtr);
    int (*tcl_HideCommand) (Tcl_Interp *interp, const char *cmdName, const char *hiddenCmdToken);
    int (*tcl_Init) (Tcl_Interp *interp);
    void (*tcl_InitHashTable) (Tcl_HashTable *tablePtr, int keyType);
    int (*tcl_InputBlocked) (Tcl_Channel chan);
    int (*tcl_InputBuffered) (Tcl_Channel chan);
    int (*tcl_InterpDeleted) (Tcl_Interp *interp);
    int (*tcl_IsSafe) (Tcl_Interp *interp);
    char * (*tcl_JoinPath) (int argc, char *const *argv, Tcl_DString *resultPtr);
    int (*tcl_LinkVar) (Tcl_Interp *interp, const char *varName, char *addr, int type);
    void *reserved188;
    Tcl_Channel (*tcl_MakeFileChannel) (ClientData handle, int mode);
    int (*tcl_MakeSafe) (Tcl_Interp *interp);
    Tcl_Channel (*tcl_MakeTcpClientChannel) (ClientData tcpSocket);
    char * (*tcl_Merge) (int argc, char *const *argv);
    Tcl_HashEntry * (*tcl_NextHashEntry) (Tcl_HashSearch *searchPtr);
    void (*tcl_NotifyChannel) (Tcl_Channel channel, int mask);
    Tcl_Obj * (*tcl_ObjGetVar2) (Tcl_Interp *interp, Tcl_Obj *part1Ptr, Tcl_Obj *part2Ptr, int flags);
    Tcl_Obj * (*tcl_ObjSetVar2) (Tcl_Interp *interp, Tcl_Obj *part1Ptr, Tcl_Obj *part2Ptr, Tcl_Obj *newValuePtr, int flags);
    Tcl_Channel (*tcl_OpenCommandChannel) (Tcl_Interp *interp, int argc, char **argv, int flags);
    Tcl_Channel (*tcl_OpenFileChannel) (Tcl_Interp *interp, const char *fileName, const char *modeString, int permissions);
    Tcl_Channel (*tcl_OpenTcpClient) (Tcl_Interp *interp, int port, const char *address, const char *myaddr, int myport, int async);
    Tcl_Channel (*tcl_OpenTcpServer) (Tcl_Interp *interp, int port, const char *host, Tcl_TcpAcceptProc *acceptProc, ClientData callbackData);
    void (*tcl_Preserve) (ClientData data);
    void (*tcl_PrintDouble) (Tcl_Interp *interp, double value, char *dst);
    int (*tcl_PutEnv) (const char *assignment);
    const char * (*tcl_PosixError) (Tcl_Interp *interp);
    void (*tcl_QueueEvent) (Tcl_Event *evPtr, Tcl_QueuePosition position);
    int (*tcl_Read) (Tcl_Channel chan, char *bufPtr, int toRead);
    void (*tcl_ReapDetachedProcs) (void);
    int (*tcl_RecordAndEval) (Tcl_Interp *interp, const char *cmd, int flags);
    int (*tcl_RecordAndEvalObj) (Tcl_Interp *interp, Tcl_Obj *cmdPtr, int flags);
    void (*tcl_RegisterChannel) (Tcl_Interp *interp, Tcl_Channel chan);
    void (*tcl_RegisterObjType) (Tcl_ObjType *typePtr);
    Tcl_RegExp (*tcl_RegExpCompile) (Tcl_Interp *interp, const char *pattern);
    int (*tcl_RegExpExec) (Tcl_Interp *interp, Tcl_RegExp regexp, const char *text, const char *start);
    int (*tcl_RegExpMatch) (Tcl_Interp *interp, const char *text, const char *pattern);
    void (*tcl_RegExpRange) (Tcl_RegExp regexp, int index, char **startPtr, char **endPtr);
    void (*tcl_Release) (ClientData clientData);
    void (*tcl_ResetResult) (Tcl_Interp *interp);
    int (*tcl_ScanElement) (const char *str, int *flagPtr);
    int (*tcl_ScanCountedElement) (const char *str, int length, int *flagPtr);
    int (*tcl_SeekOld) (Tcl_Channel chan, int offset, int mode);
    int (*tcl_ServiceAll) (void);
    int (*tcl_ServiceEvent) (int flags);
    void (*tcl_SetAssocData) (Tcl_Interp *interp, const char *name, Tcl_InterpDeleteProc *proc, ClientData clientData);
    void (*tcl_SetChannelBufferSize) (Tcl_Channel chan, int sz);
    int (*tcl_SetChannelOption) (Tcl_Interp *interp, Tcl_Channel chan, const char *optionName, const char *newValue);
    int (*tcl_SetCommandInfo) (Tcl_Interp *interp, const char *cmdName, const Tcl_CmdInfo *infoPtr);
    void (*tcl_SetErrno) (int err);
    void (*tcl_SetErrorCode) (Tcl_Interp *interp, ...);
    void (*tcl_SetMaxBlockTime) (Tcl_Time *timePtr);
    void (*tcl_SetPanicProc) (Tcl_PanicProc *panicProc);
    int (*tcl_SetRecursionLimit) (Tcl_Interp *interp, int depth);
    void (*tcl_SetResult) (Tcl_Interp *interp, char *result, Tcl_FreeProc *freeProc);
    int (*tcl_SetServiceMode) (int mode);
    void (*tcl_SetObjErrorCode) (Tcl_Interp *interp, Tcl_Obj *errorObjPtr);
    void (*tcl_SetObjResult) (Tcl_Interp *interp, Tcl_Obj *resultObjPtr);
    void (*tcl_SetStdChannel) (Tcl_Channel channel, int type);
    const char * (*tcl_SetVar) (Tcl_Interp *interp, const char *varName, const char *newValue, int flags);
    const char * (*tcl_SetVar2) (Tcl_Interp *interp, const char *part1, const char *part2, const char *newValue, int flags);
    const char * (*tcl_SignalId) (int sig);
    const char * (*tcl_SignalMsg) (int sig);
    void (*tcl_SourceRCFile) (Tcl_Interp *interp);
    int (*tcl_SplitList) (Tcl_Interp *interp, const char *listStr, int *argcPtr, char ***argvPtr);
    void (*tcl_SplitPath) (const char *path, int *argcPtr, char ***argvPtr);
    void (*tcl_StaticPackage) (Tcl_Interp *interp, const char *pkgName, Tcl_PackageInitProc *initProc, Tcl_PackageInitProc *safeInitProc);
    int (*tcl_StringMatch) (const char *str, const char *pattern);
    int (*tcl_TellOld) (Tcl_Channel chan);
    int (*tcl_TraceVar) (Tcl_Interp *interp, const char *varName, int flags, Tcl_VarTraceProc *proc, ClientData clientData);
    int (*tcl_TraceVar2) (Tcl_Interp *interp, const char *part1, const char *part2, int flags, Tcl_VarTraceProc *proc, ClientData clientData);
    char * (*tcl_TranslateFileName) (Tcl_Interp *interp, const char *name, Tcl_DString *bufferPtr);
    int (*tcl_Ungets) (Tcl_Channel chan, const char *str, int len, int atHead);
    void (*tcl_UnlinkVar) (Tcl_Interp *interp, const char *varName);
    int (*tcl_UnregisterChannel) (Tcl_Interp *interp, Tcl_Channel chan);
    int (*tcl_UnsetVar) (Tcl_Interp *interp, const char *varName, int flags);
    int (*tcl_UnsetVar2) (Tcl_Interp *interp, const char *part1, const char *part2, int flags);
    void (*tcl_UntraceVar) (Tcl_Interp *interp, const char *varName, int flags, Tcl_VarTraceProc *proc, ClientData clientData);
    void (*tcl_UntraceVar2) (Tcl_Interp *interp, const char *part1, const char *part2, int flags, Tcl_VarTraceProc *proc, ClientData clientData);
    void (*tcl_UpdateLinkedVar) (Tcl_Interp *interp, const char *varName);
    int (*tcl_UpVar) (Tcl_Interp *interp, const char *frameName, const char *varName, const char *localName, int flags);
    int (*tcl_UpVar2) (Tcl_Interp *interp, const char *frameName, const char *part1, const char *part2, const char *localName, int flags);
    int (*tcl_VarEval) (Tcl_Interp *interp, ...);
    ClientData (*tcl_VarTraceInfo) (Tcl_Interp *interp, const char *varName, int flags, Tcl_VarTraceProc *procPtr, ClientData prevClientData);
    ClientData (*tcl_VarTraceInfo2) (Tcl_Interp *interp, const char *part1, const char *part2, int flags, Tcl_VarTraceProc *procPtr, ClientData prevClientData);
    int (*tcl_Write) (Tcl_Channel chan, const char *s, int slen);
    void (*tcl_WrongNumArgs) (Tcl_Interp *interp, int objc, Tcl_Obj *const objv[], const char *message);
    int (*tcl_DumpActiveMemory) (const char *fileName);
    void (*tcl_ValidateAllMemory) (const char *file, int line);
    void (*tcl_AppendResultVA) (Tcl_Interp *interp, va_list argList);
    void (*tcl_AppendStringsToObjVA) (Tcl_Obj *objPtr, va_list argList);
    char * (*tcl_HashStats) (Tcl_HashTable *tablePtr);
    const char * (*tcl_ParseVar) (Tcl_Interp *interp, const char *start, char **termPtr);
    const char * (*tcl_PkgPresent) (Tcl_Interp *interp, const char *name, const char *version, int exact);
    const char * (*tcl_PkgPresentEx) (Tcl_Interp *interp, const char *name, const char *version, int exact, ClientData *clientDataPtr);
    int (*tcl_PkgProvide) (Tcl_Interp *interp, const char *name, const char *version);
    const char * (*tcl_PkgRequire) (Tcl_Interp *interp, const char *name, const char *version, int exact);
    void (*tcl_SetErrorCodeVA) (Tcl_Interp *interp, va_list argList);
    int (*tcl_VarEvalVA) (Tcl_Interp *interp, va_list argList);
    Tcl_Pid (*tcl_WaitPid) (Tcl_Pid pid, int *statPtr, int options);
    void (*tcl_PanicVA) (const char *format, va_list argList);
    void (*tcl_GetVersion) (int *major, int *minor, int *patchLevel, int *type);
    void (*tcl_InitMemory) (Tcl_Interp *interp);
    Tcl_Channel (*tcl_StackChannel) (Tcl_Interp *interp, Tcl_ChannelType *typePtr, ClientData instanceData, int mask, Tcl_Channel prevChan);
    int (*tcl_UnstackChannel) (Tcl_Interp *interp, Tcl_Channel chan);
    Tcl_Channel (*tcl_GetStackedChannel) (Tcl_Channel chan);
    void (*tcl_SetMainLoop) (Tcl_MainLoopProc *proc);
    void *reserved285;
    void (*tcl_AppendObjToObj) (Tcl_Obj *objPtr, Tcl_Obj *appendObjPtr);
    Tcl_Encoding (*tcl_CreateEncoding) (const Tcl_EncodingType *typePtr);
    void (*tcl_CreateThreadExitHandler) (Tcl_ExitProc *proc, ClientData clientData);
    void (*tcl_DeleteThreadExitHandler) (Tcl_ExitProc *proc, ClientData clientData);
    void (*tcl_DiscardResult) (Tcl_SavedResult *statePtr);
    int (*tcl_EvalEx) (Tcl_Interp *interp, const char *script, int numBytes, int flags);
    int (*tcl_EvalObjv) (Tcl_Interp *interp, int objc, Tcl_Obj *const objv[], int flags);
    int (*tcl_EvalObjEx) (Tcl_Interp *interp, Tcl_Obj *objPtr, int flags);
    void (*tcl_ExitThread) (int status);
    int (*tcl_ExternalToUtf) (Tcl_Interp *interp, Tcl_Encoding encoding, const char *src, int srcLen, int flags, Tcl_EncodingState *statePtr, char *dst, int dstLen, int *srcReadPtr, int *dstWrotePtr, int *dstCharsPtr);
    char * (*tcl_ExternalToUtfDString) (Tcl_Encoding encoding, const char *src, int srcLen, Tcl_DString *dsPtr);
    void (*tcl_FinalizeThread) (void);
    void (*tcl_FinalizeNotifier) (ClientData clientData);
    void (*tcl_FreeEncoding) (Tcl_Encoding encoding);
    Tcl_ThreadId (*tcl_GetCurrentThread) (void);
    Tcl_Encoding (*tcl_GetEncoding) (Tcl_Interp *interp, const char *name);
    const char * (*tcl_GetEncodingName) (Tcl_Encoding encoding);
    void (*tcl_GetEncodingNames) (Tcl_Interp *interp);
    int (*tcl_GetIndexFromObjStruct) (Tcl_Interp *interp, Tcl_Obj *objPtr, const void *tablePtr, int offset, const char *msg, int flags, int *indexPtr);
    void * (*tcl_GetThreadData) (Tcl_ThreadDataKey *keyPtr, int size);
    Tcl_Obj * (*tcl_GetVar2Ex) (Tcl_Interp *interp, const char *part1, const char *part2, int flags);
    ClientData (*tcl_InitNotifier) (void);
    void (*tcl_MutexLock) (Tcl_Mutex *mutexPtr);
    void (*tcl_MutexUnlock) (Tcl_Mutex *mutexPtr);
    void (*tcl_ConditionNotify) (Tcl_Condition *condPtr);
    void (*tcl_ConditionWait) (Tcl_Condition *condPtr, Tcl_Mutex *mutexPtr, Tcl_Time *timePtr);
    int (*tcl_NumUtfChars) (const char *src, int length);
    int (*tcl_ReadChars) (Tcl_Channel channel, Tcl_Obj *objPtr, int charsToRead, int appendFlag);
    void (*tcl_RestoreResult) (Tcl_Interp *interp, Tcl_SavedResult *statePtr);
    void (*tcl_SaveResult) (Tcl_Interp *interp, Tcl_SavedResult *statePtr);
    int (*tcl_SetSystemEncoding) (Tcl_Interp *interp, const char *name);
    Tcl_Obj * (*tcl_SetVar2Ex) (Tcl_Interp *interp, const char *part1, const char *part2, Tcl_Obj *newValuePtr, int flags);
    void (*tcl_ThreadAlert) (Tcl_ThreadId threadId);
    void (*tcl_ThreadQueueEvent) (Tcl_ThreadId threadId, Tcl_Event *evPtr, Tcl_QueuePosition position);
    Tcl_UniChar (*tcl_UniCharAtIndex) (const char *src, int index);
    Tcl_UniChar (*tcl_UniCharToLower) (int ch);
    Tcl_UniChar (*tcl_UniCharToTitle) (int ch);
    Tcl_UniChar (*tcl_UniCharToUpper) (int ch);
    int (*tcl_UniCharToUtf) (int ch, char *buf);
    const char * (*tcl_UtfAtIndex) (const char *src, int index);
    int (*tcl_UtfCharComplete) (const char *src, int length);
    int (*tcl_UtfBackslash) (const char *src, int *readPtr, char *dst);
    const char * (*tcl_UtfFindFirst) (const char *src, int ch);
    const char * (*tcl_UtfFindLast) (const char *src, int ch);
    const char * (*tcl_UtfNext) (const char *src);
    const char * (*tcl_UtfPrev) (const char *src, const char *start);
    int (*tcl_UtfToExternal) (Tcl_Interp *interp, Tcl_Encoding encoding, const char *src, int srcLen, int flags, Tcl_EncodingState *statePtr, char *dst, int dstLen, int *srcReadPtr, int *dstWrotePtr, int *dstCharsPtr);
    char * (*tcl_UtfToExternalDString) (Tcl_Encoding encoding, const char *src, int srcLen, Tcl_DString *dsPtr);
    int (*tcl_UtfToLower) (char *src);
    int (*tcl_UtfToTitle) (char *src);
    int (*tcl_UtfToUniChar) (const char *src, Tcl_UniChar *chPtr);
    int (*tcl_UtfToUpper) (char *src);
    int (*tcl_WriteChars) (Tcl_Channel chan, const char *src, int srcLen);
    int (*tcl_WriteObj) (Tcl_Channel chan, Tcl_Obj *objPtr);
    char * (*tcl_GetString) (Tcl_Obj *objPtr);
    const char * (*tcl_GetDefaultEncodingDir) (void);
    void (*tcl_SetDefaultEncodingDir) (const char *path);
    void (*tcl_AlertNotifier) (ClientData clientData);
    void (*tcl_ServiceModeHook) (int mode);
    int (*tcl_UniCharIsAlnum) (int ch);
    int (*tcl_UniCharIsAlpha) (int ch);
    int (*tcl_UniCharIsDigit) (int ch);
    int (*tcl_UniCharIsLower) (int ch);
    int (*tcl_UniCharIsSpace) (int ch);
    int (*tcl_UniCharIsUpper) (int ch);
    int (*tcl_UniCharIsWordChar) (int ch);
    int (*tcl_UniCharLen) (const Tcl_UniChar *uniStr);
    int (*tcl_UniCharNcmp) (const Tcl_UniChar *ucs, const Tcl_UniChar *uct, unsigned long numChars);
    char * (*tcl_UniCharToUtfDString) (const Tcl_UniChar *uniStr, int uniLength, Tcl_DString *dsPtr);
    Tcl_UniChar * (*tcl_UtfToUniCharDString) (const char *src, int length, Tcl_DString *dsPtr);
    Tcl_RegExp (*tcl_GetRegExpFromObj) (Tcl_Interp *interp, Tcl_Obj *patObj, int flags);
    Tcl_Obj * (*tcl_EvalTokens) (Tcl_Interp *interp, Tcl_Token *tokenPtr, int count);
    void (*tcl_FreeParse) (Tcl_Parse *parsePtr);
    void (*tcl_LogCommandInfo) (Tcl_Interp *interp, const char *script, const char *command, int length);
    int (*tcl_ParseBraces) (Tcl_Interp *interp, const char *start, int numBytes, Tcl_Parse *parsePtr, int append, char **termPtr);
    int (*tcl_ParseCommand) (Tcl_Interp *interp, const char *start, int numBytes, int nested, Tcl_Parse *parsePtr);
    int (*tcl_ParseExpr) (Tcl_Interp *interp, const char *start, int numBytes, Tcl_Parse *parsePtr);
    int (*tcl_ParseQuotedString) (Tcl_Interp *interp, const char *start, int numBytes, Tcl_Parse *parsePtr, int append, char **termPtr);
    int (*tcl_ParseVarName) (Tcl_Interp *interp, const char *start, int numBytes, Tcl_Parse *parsePtr, int append);
    char * (*tcl_GetCwd) (Tcl_Interp *interp, Tcl_DString *cwdPtr);
    int (*tcl_Chdir) (const char *dirName);
    int (*tcl_Access) (const char *path, int mode);
    int (*tcl_Stat) (const char *path, struct stat *bufPtr);
    int (*tcl_UtfNcmp) (const char *s1, const char *s2, unsigned long n);
    int (*tcl_UtfNcasecmp) (const char *s1, const char *s2, unsigned long n);
    int (*tcl_StringCaseMatch) (const char *str, const char *pattern, int nocase);
    int (*tcl_UniCharIsControl) (int ch);
    int (*tcl_UniCharIsGraph) (int ch);
    int (*tcl_UniCharIsPrint) (int ch);
    int (*tcl_UniCharIsPunct) (int ch);
    int (*tcl_RegExpExecObj) (Tcl_Interp *interp, Tcl_RegExp regexp, Tcl_Obj *textObj, int offset, int nmatches, int flags);
    void (*tcl_RegExpGetInfo) (Tcl_RegExp regexp, Tcl_RegExpInfo *infoPtr);
    Tcl_Obj * (*tcl_NewUnicodeObj) (const Tcl_UniChar *unicode, int numChars);
    void (*tcl_SetUnicodeObj) (Tcl_Obj *objPtr, const Tcl_UniChar *unicode, int numChars);
    int (*tcl_GetCharLength) (Tcl_Obj *objPtr);
    Tcl_UniChar (*tcl_GetUniChar) (Tcl_Obj *objPtr, int index);
    Tcl_UniChar * (*tcl_GetUnicode) (Tcl_Obj *objPtr);
    Tcl_Obj * (*tcl_GetRange) (Tcl_Obj *objPtr, int first, int last);
    void (*tcl_AppendUnicodeToObj) (Tcl_Obj *objPtr, const Tcl_UniChar *unicode, int length);
    int (*tcl_RegExpMatchObj) (Tcl_Interp *interp, Tcl_Obj *textObj, Tcl_Obj *patternObj);
    void (*tcl_SetNotifier) (Tcl_NotifierProcs *notifierProcPtr);
    Tcl_Mutex * (*tcl_GetAllocMutex) (void);
    int (*tcl_GetChannelNames) (Tcl_Interp *interp);
    int (*tcl_GetChannelNamesEx) (Tcl_Interp *interp, const char *pattern);
    int (*tcl_ProcObjCmd) (ClientData clientData, Tcl_Interp *interp, int objc, Tcl_Obj *const objv[]);
    void (*tcl_ConditionFinalize) (Tcl_Condition *condPtr);
    void (*tcl_MutexFinalize) (Tcl_Mutex *mutex);
    int (*tcl_CreateThread) (Tcl_ThreadId *idPtr, Tcl_ThreadCreateProc proc, ClientData clientData, int stackSize, int flags);
    int (*tcl_ReadRaw) (Tcl_Channel chan, char *dst, int bytesToRead);
    int (*tcl_WriteRaw) (Tcl_Channel chan, const char *src, int srcLen);
    Tcl_Channel (*tcl_GetTopChannel) (Tcl_Channel chan);
    int (*tcl_ChannelBuffered) (Tcl_Channel chan);
    const char * (*tcl_ChannelName) (const Tcl_ChannelType *chanTypePtr);
    Tcl_ChannelTypeVersion (*tcl_ChannelVersion) (const Tcl_ChannelType *chanTypePtr);
    Tcl_DriverBlockModeProc * (*tcl_ChannelBlockModeProc) (const Tcl_ChannelType *chanTypePtr);
    Tcl_DriverCloseProc * (*tcl_ChannelCloseProc) (const Tcl_ChannelType *chanTypePtr);
    Tcl_DriverClose2Proc * (*tcl_ChannelClose2Proc) (const Tcl_ChannelType *chanTypePtr);
    Tcl_DriverInputProc * (*tcl_ChannelInputProc) (const Tcl_ChannelType *chanTypePtr);
    Tcl_DriverOutputProc * (*tcl_ChannelOutputProc) (const Tcl_ChannelType *chanTypePtr);
    Tcl_DriverSeekProc * (*tcl_ChannelSeekProc) (const Tcl_ChannelType *chanTypePtr);
    Tcl_DriverSetOptionProc * (*tcl_ChannelSetOptionProc) (const Tcl_ChannelType *chanTypePtr);
    Tcl_DriverGetOptionProc * (*tcl_ChannelGetOptionProc) (const Tcl_ChannelType *chanTypePtr);
    Tcl_DriverWatchProc * (*tcl_ChannelWatchProc) (const Tcl_ChannelType *chanTypePtr);
    Tcl_DriverGetHandleProc * (*tcl_ChannelGetHandleProc) (const Tcl_ChannelType *chanTypePtr);
    Tcl_DriverFlushProc * (*tcl_ChannelFlushProc) (const Tcl_ChannelType *chanTypePtr);
    Tcl_DriverHandlerProc * (*tcl_ChannelHandlerProc) (const Tcl_ChannelType *chanTypePtr);
    int (*tcl_JoinThread) (Tcl_ThreadId threadId, int *result);
    int (*tcl_IsChannelShared) (Tcl_Channel channel);
    int (*tcl_IsChannelRegistered) (Tcl_Interp *interp, Tcl_Channel channel);
    void (*tcl_CutChannel) (Tcl_Channel channel);
    void (*tcl_SpliceChannel) (Tcl_Channel channel);
    void (*tcl_ClearChannelHandlers) (Tcl_Channel channel);
    int (*tcl_IsChannelExisting) (const char *channelName);
    int (*tcl_UniCharNcasecmp) (const Tcl_UniChar *ucs, const Tcl_UniChar *uct, unsigned long numChars);
    int (*tcl_UniCharCaseMatch) (const Tcl_UniChar *uniStr, const Tcl_UniChar *uniPattern, int nocase);
    Tcl_HashEntry * (*tcl_FindHashEntry) (Tcl_HashTable *tablePtr, const char *key);
    Tcl_HashEntry * (*tcl_CreateHashEntry) (Tcl_HashTable *tablePtr, const char *key, int *newPtr);
    void (*tcl_InitCustomHashTable) (Tcl_HashTable *tablePtr, int keyType, Tcl_HashKeyType *typePtr);
    void (*tcl_InitObjHashTable) (Tcl_HashTable *tablePtr);
    ClientData (*tcl_CommandTraceInfo) (Tcl_Interp *interp, const char *varName, int flags, Tcl_CommandTraceProc *procPtr, ClientData prevClientData);
    int (*tcl_TraceCommand) (Tcl_Interp *interp, const char *varName, int flags, Tcl_CommandTraceProc *proc, ClientData clientData);
    void (*tcl_UntraceCommand) (Tcl_Interp *interp, const char *varName, int flags, Tcl_CommandTraceProc *proc, ClientData clientData);
    char * (*tcl_AttemptAlloc) (unsigned int size);
    char * (*tcl_AttemptDbCkalloc) (unsigned int size, const char *file, int line);
    char * (*tcl_AttemptRealloc) (char *ptr, unsigned int size);
    char * (*tcl_AttemptDbCkrealloc) (char *ptr, unsigned int size, const char *file, int line);
    int (*tcl_AttemptSetObjLength) (Tcl_Obj *objPtr, int length);
    Tcl_ThreadId (*tcl_GetChannelThread) (Tcl_Channel channel);
    Tcl_UniChar * (*tcl_GetUnicodeFromObj) (Tcl_Obj *objPtr, int *lengthPtr);
    int (*tcl_GetMathFuncInfo) (Tcl_Interp *interp, const char *name, int *numArgsPtr, Tcl_ValueType **argTypesPtr, Tcl_MathProc **procPtr, ClientData *clientDataPtr);
    Tcl_Obj * (*tcl_ListMathFuncs) (Tcl_Interp *interp, const char *pattern);
    Tcl_Obj * (*tcl_SubstObj) (Tcl_Interp *interp, Tcl_Obj *objPtr, int flags);
    int (*tcl_DetachChannel) (Tcl_Interp *interp, Tcl_Channel channel);
    int (*tcl_IsStandardChannel) (Tcl_Channel channel);
    int (*tcl_FSCopyFile) (Tcl_Obj *srcPathPtr, Tcl_Obj *destPathPtr);
    int (*tcl_FSCopyDirectory) (Tcl_Obj *srcPathPtr, Tcl_Obj *destPathPtr, Tcl_Obj **errorPtr);
    int (*tcl_FSCreateDirectory) (Tcl_Obj *pathPtr);
    int (*tcl_FSDeleteFile) (Tcl_Obj *pathPtr);
    int (*tcl_FSLoadFile) (Tcl_Interp *interp, Tcl_Obj *pathPtr, const char *sym1, const char *sym2, Tcl_PackageInitProc **proc1Ptr, Tcl_PackageInitProc **proc2Ptr, Tcl_LoadHandle *handlePtr, Tcl_FSUnloadFileProc **unloadProcPtr);
    int (*tcl_FSMatchInDirectory) (Tcl_Interp *interp, Tcl_Obj *result, Tcl_Obj *pathPtr, const char *pattern, Tcl_GlobTypeData *types);
    Tcl_Obj * (*tcl_FSLink) (Tcl_Obj *pathPtr, Tcl_Obj *toPtr, int linkAction);
    int (*tcl_FSRemoveDirectory) (Tcl_Obj *pathPtr, int recursive, Tcl_Obj **errorPtr);
    int (*tcl_FSRenameFile) (Tcl_Obj *srcPathPtr, Tcl_Obj *destPathPtr);
    int (*tcl_FSLstat) (Tcl_Obj *pathPtr, Tcl_StatBuf *buf);
    int (*tcl_FSUtime) (Tcl_Obj *pathPtr, struct utimbuf *tval);
    int (*tcl_FSFileAttrsGet) (Tcl_Interp *interp, int index, Tcl_Obj *pathPtr, Tcl_Obj **objPtrRef);
    int (*tcl_FSFileAttrsSet) (Tcl_Interp *interp, int index, Tcl_Obj *pathPtr, Tcl_Obj *objPtr);
    const char ** (*tcl_FSFileAttrStrings) (Tcl_Obj *pathPtr, Tcl_Obj **objPtrRef);
    int (*tcl_FSStat) (Tcl_Obj *pathPtr, Tcl_StatBuf *buf);
    int (*tcl_FSAccess) (Tcl_Obj *pathPtr, int mode);
    Tcl_Channel (*tcl_FSOpenFileChannel) (Tcl_Interp *interp, Tcl_Obj *pathPtr, const char *modeString, int permissions);
    Tcl_Obj * (*tcl_FSGetCwd) (Tcl_Interp *interp);
    int (*tcl_FSChdir) (Tcl_Obj *pathPtr);
    int (*tcl_FSConvertToPathType) (Tcl_Interp *interp, Tcl_Obj *pathPtr);
    Tcl_Obj * (*tcl_FSJoinPath) (Tcl_Obj *listObj, int elements);
    Tcl_Obj * (*tcl_FSSplitPath) (Tcl_Obj *pathPtr, int *lenPtr);
    int (*tcl_FSEqualPaths) (Tcl_Obj *firstPtr, Tcl_Obj *secondPtr);
    Tcl_Obj * (*tcl_FSGetNormalizedPath) (Tcl_Interp *interp, Tcl_Obj *pathPtr);
    Tcl_Obj * (*tcl_FSJoinToPath) (Tcl_Obj *pathPtr, int objc, Tcl_Obj *const objv[]);
    ClientData (*tcl_FSGetInternalRep) (Tcl_Obj *pathPtr, Tcl_Filesystem *fsPtr);
    Tcl_Obj * (*tcl_FSGetTranslatedPath) (Tcl_Interp *interp, Tcl_Obj *pathPtr);
    int (*tcl_FSEvalFile) (Tcl_Interp *interp, Tcl_Obj *fileName);
    Tcl_Obj * (*tcl_FSNewNativePath) (Tcl_Filesystem *fromFilesystem, ClientData clientData);
    const char * (*tcl_FSGetNativePath) (Tcl_Obj *pathPtr);
    Tcl_Obj * (*tcl_FSFileSystemInfo) (Tcl_Obj *pathPtr);
    Tcl_Obj * (*tcl_FSPathSeparator) (Tcl_Obj *pathPtr);
    Tcl_Obj * (*tcl_FSListVolumes) (void);
    int (*tcl_FSRegister) (ClientData clientData, Tcl_Filesystem *fsPtr);
    int (*tcl_FSUnregister) (Tcl_Filesystem *fsPtr);
    ClientData (*tcl_FSData) (Tcl_Filesystem *fsPtr);
    const char * (*tcl_FSGetTranslatedStringPath) (Tcl_Interp *interp, Tcl_Obj *pathPtr);
    Tcl_Filesystem * (*tcl_FSGetFileSystemForPath) (Tcl_Obj *pathPtr);
    Tcl_PathType (*tcl_FSGetPathType) (Tcl_Obj *pathPtr);
    int (*tcl_OutputBuffered) (Tcl_Channel chan);
    void (*tcl_FSMountsChanged) (Tcl_Filesystem *fsPtr);
    int (*tcl_EvalTokensStandard) (Tcl_Interp *interp, Tcl_Token *tokenPtr, int count);
    void (*tcl_GetTime) (Tcl_Time *timeBuf);
    Tcl_Trace (*tcl_CreateObjTrace) (Tcl_Interp *interp, int level, int flags, Tcl_CmdObjTraceProc *objProc, ClientData clientData, Tcl_CmdObjTraceDeleteProc *delProc);
    int (*tcl_GetCommandInfoFromToken) (Tcl_Command token, Tcl_CmdInfo *infoPtr);
    int (*tcl_SetCommandInfoFromToken) (Tcl_Command token, const Tcl_CmdInfo *infoPtr);
    Tcl_Obj * (*tcl_DbNewWideIntObj) (Tcl_WideInt wideValue, const char *file, int line);
    int (*tcl_GetWideIntFromObj) (Tcl_Interp *interp, Tcl_Obj *objPtr, Tcl_WideInt *widePtr);
    Tcl_Obj * (*tcl_NewWideIntObj) (Tcl_WideInt wideValue);
    void (*tcl_SetWideIntObj) (Tcl_Obj *objPtr, Tcl_WideInt wideValue);
    Tcl_StatBuf * (*tcl_AllocStatBuf) (void);
    Tcl_WideInt (*tcl_Seek) (Tcl_Channel chan, Tcl_WideInt offset, int mode);
    Tcl_WideInt (*tcl_Tell) (Tcl_Channel chan);
    Tcl_DriverWideSeekProc * (*tcl_ChannelWideSeekProc) (const Tcl_ChannelType *chanTypePtr);
    int (*tcl_DictObjPut) (Tcl_Interp *interp, Tcl_Obj *dictPtr, Tcl_Obj *keyPtr, Tcl_Obj *valuePtr);
    int (*tcl_DictObjGet) (Tcl_Interp *interp, Tcl_Obj *dictPtr, Tcl_Obj *keyPtr, Tcl_Obj **valuePtrPtr);
    int (*tcl_DictObjRemove) (Tcl_Interp *interp, Tcl_Obj *dictPtr, Tcl_Obj *keyPtr);
    int (*tcl_DictObjSize) (Tcl_Interp *interp, Tcl_Obj *dictPtr, int *sizePtr);
    int (*tcl_DictObjFirst) (Tcl_Interp *interp, Tcl_Obj *dictPtr, Tcl_DictSearch *searchPtr, Tcl_Obj **keyPtrPtr, Tcl_Obj **valuePtrPtr, int *donePtr);
    void (*tcl_DictObjNext) (Tcl_DictSearch *searchPtr, Tcl_Obj **keyPtrPtr, Tcl_Obj **valuePtrPtr, int *donePtr);
    void (*tcl_DictObjDone) (Tcl_DictSearch *searchPtr);
    int (*tcl_DictObjPutKeyList) (Tcl_Interp *interp, Tcl_Obj *dictPtr, int keyc, Tcl_Obj *const *keyv, Tcl_Obj *valuePtr);
    int (*tcl_DictObjRemoveKeyList) (Tcl_Interp *interp, Tcl_Obj *dictPtr, int keyc, Tcl_Obj *const *keyv);
    Tcl_Obj * (*tcl_NewDictObj) (void);
    Tcl_Obj * (*tcl_DbNewDictObj) (const char *file, int line);
    void (*tcl_RegisterConfig) (Tcl_Interp *interp, const char *pkgName, Tcl_Config *configuration, const char *valEncoding);
    Tcl_Namespace * (*tcl_CreateNamespace) (Tcl_Interp *interp, const char *name, ClientData clientData, Tcl_NamespaceDeleteProc *deleteProc);
    void (*tcl_DeleteNamespace) (Tcl_Namespace *nsPtr);
    int (*tcl_AppendExportList) (Tcl_Interp *interp, Tcl_Namespace *nsPtr, Tcl_Obj *objPtr);
    int (*tcl_Export) (Tcl_Interp *interp, Tcl_Namespace *nsPtr, const char *pattern, int resetListFirst);
    int (*tcl_Import) (Tcl_Interp *interp, Tcl_Namespace *nsPtr, const char *pattern, int allowOverwrite);
    int (*tcl_ForgetImport) (Tcl_Interp *interp, Tcl_Namespace *nsPtr, const char *pattern);
    Tcl_Namespace * (*tcl_GetCurrentNamespace) (Tcl_Interp *interp);
    Tcl_Namespace * (*tcl_GetGlobalNamespace) (Tcl_Interp *interp);
    Tcl_Namespace * (*tcl_FindNamespace) (Tcl_Interp *interp, const char *name, Tcl_Namespace *contextNsPtr, int flags);
    Tcl_Command (*tcl_FindCommand) (Tcl_Interp *interp, const char *name, Tcl_Namespace *contextNsPtr, int flags);
    Tcl_Command (*tcl_GetCommandFromObj) (Tcl_Interp *interp, Tcl_Obj *objPtr);
    void (*tcl_GetCommandFullName) (Tcl_Interp *interp, Tcl_Command command, Tcl_Obj *objPtr);
    int (*tcl_FSEvalFileEx) (Tcl_Interp *interp, Tcl_Obj *fileName, const char *encodingName);
    Tcl_ExitProc * (*tcl_SetExitProc) (Tcl_ExitProc *proc);
    void (*tcl_LimitAddHandler) (Tcl_Interp *interp, int type, Tcl_LimitHandlerProc *handlerProc, ClientData clientData, Tcl_LimitHandlerDeleteProc *deleteProc);
    void (*tcl_LimitRemoveHandler) (Tcl_Interp *interp, int type, Tcl_LimitHandlerProc *handlerProc, ClientData clientData);
    int (*tcl_LimitReady) (Tcl_Interp *interp);
    int (*tcl_LimitCheck) (Tcl_Interp *interp);
    int (*tcl_LimitExceeded) (Tcl_Interp *interp);
    void (*tcl_LimitSetCommands) (Tcl_Interp *interp, int commandLimit);
    void (*tcl_LimitSetTime) (Tcl_Interp *interp, Tcl_Time *timeLimitPtr);
    void (*tcl_LimitSetGranularity) (Tcl_Interp *interp, int type, int granularity);
    int (*tcl_LimitTypeEnabled) (Tcl_Interp *interp, int type);
    int (*tcl_LimitTypeExceeded) (Tcl_Interp *interp, int type);
    void (*tcl_LimitTypeSet) (Tcl_Interp *interp, int type);
    void (*tcl_LimitTypeReset) (Tcl_Interp *interp, int type);
    int (*tcl_LimitGetCommands) (Tcl_Interp *interp);
    void (*tcl_LimitGetTime) (Tcl_Interp *interp, Tcl_Time *timeLimitPtr);
    int (*tcl_LimitGetGranularity) (Tcl_Interp *interp, int type);
    Tcl_InterpState (*tcl_SaveInterpState) (Tcl_Interp *interp, int status);
    int (*tcl_RestoreInterpState) (Tcl_Interp *interp, Tcl_InterpState state);
    void (*tcl_DiscardInterpState) (Tcl_InterpState state);
    int (*tcl_SetReturnOptions) (Tcl_Interp *interp, Tcl_Obj *options);
    Tcl_Obj * (*tcl_GetReturnOptions) (Tcl_Interp *interp, int result);
    int (*tcl_IsEnsemble) (Tcl_Command token);
    Tcl_Command (*tcl_CreateEnsemble) (Tcl_Interp *interp, const char *name, Tcl_Namespace *namespacePtr, int flags);
    Tcl_Command (*tcl_FindEnsemble) (Tcl_Interp *interp, Tcl_Obj *cmdNameObj, int flags);
    int (*tcl_SetEnsembleSubcommandList) (Tcl_Interp *interp, Tcl_Command token, Tcl_Obj *subcmdList);
    int (*tcl_SetEnsembleMappingDict) (Tcl_Interp *interp, Tcl_Command token, Tcl_Obj *mapDict);
    int (*tcl_SetEnsembleUnknownHandler) (Tcl_Interp *interp, Tcl_Command token, Tcl_Obj *unknownList);
    int (*tcl_SetEnsembleFlags) (Tcl_Interp *interp, Tcl_Command token, int flags);
    int (*tcl_GetEnsembleSubcommandList) (Tcl_Interp *interp, Tcl_Command token, Tcl_Obj **subcmdListPtr);
    int (*tcl_GetEnsembleMappingDict) (Tcl_Interp *interp, Tcl_Command token, Tcl_Obj **mapDictPtr);
    int (*tcl_GetEnsembleUnknownHandler) (Tcl_Interp *interp, Tcl_Command token, Tcl_Obj **unknownListPtr);
    int (*tcl_GetEnsembleFlags) (Tcl_Interp *interp, Tcl_Command token, int *flagsPtr);
    int (*tcl_GetEnsembleNamespace) (Tcl_Interp *interp, Tcl_Command token, Tcl_Namespace **namespacePtrPtr);
    void (*tcl_SetTimeProc) (Tcl_GetTimeProc *getProc, Tcl_ScaleTimeProc *scaleProc, ClientData clientData);
    void (*tcl_QueryTimeProc) (Tcl_GetTimeProc **getProc, Tcl_ScaleTimeProc **scaleProc, ClientData *clientData);
    Tcl_DriverThreadActionProc * (*tcl_ChannelThreadActionProc) (const Tcl_ChannelType *chanTypePtr);
    Tcl_Obj * (*tcl_NewBignumObj) (mp_int *value);
    Tcl_Obj * (*tcl_DbNewBignumObj) (mp_int *value, const char *file, int line);
    void (*tcl_SetBignumObj) (Tcl_Obj *obj, mp_int *value);
    int (*tcl_GetBignumFromObj) (Tcl_Interp *interp, Tcl_Obj *obj, mp_int *value);
    int (*tcl_TakeBignumFromObj) (Tcl_Interp *interp, Tcl_Obj *obj, mp_int *value);
    int (*tcl_TruncateChannel) (Tcl_Channel chan, Tcl_WideInt length);
    Tcl_DriverTruncateProc * (*tcl_ChannelTruncateProc) (const Tcl_ChannelType *chanTypePtr);
    void (*tcl_SetChannelErrorInterp) (Tcl_Interp *interp, Tcl_Obj *msg);
    void (*tcl_GetChannelErrorInterp) (Tcl_Interp *interp, Tcl_Obj **msg);
    void (*tcl_SetChannelError) (Tcl_Channel chan, Tcl_Obj *msg);
    void (*tcl_GetChannelError) (Tcl_Channel chan, Tcl_Obj **msg);
    int (*tcl_InitBignumFromDouble) (Tcl_Interp *interp, double initval, mp_int *toInit);
    Tcl_Obj * (*tcl_GetNamespaceUnknownHandler) (Tcl_Interp *interp, Tcl_Namespace *nsPtr);
    int (*tcl_SetNamespaceUnknownHandler) (Tcl_Interp *interp, Tcl_Namespace *nsPtr, Tcl_Obj *handlerPtr);
    int (*tcl_GetEncodingFromObj) (Tcl_Interp *interp, Tcl_Obj *objPtr, Tcl_Encoding *encodingPtr);
    Tcl_Obj * (*tcl_GetEncodingSearchPath) (void);
    int (*tcl_SetEncodingSearchPath) (Tcl_Obj *searchPath);
    const char * (*tcl_GetEncodingNameFromEnvironment) (Tcl_DString *bufPtr);
    int (*tcl_PkgRequireProc) (Tcl_Interp *interp, const char *name, int objc, Tcl_Obj *const objv[], ClientData *clientDataPtr);
    void (*tcl_AppendObjToErrorInfo) (Tcl_Interp *interp, Tcl_Obj *objPtr);
    void (*tcl_AppendLimitedToObj) (Tcl_Obj *objPtr, const char *bytes, int length, int limit, const char *ellipsis);
    Tcl_Obj * (*tcl_Format) (Tcl_Interp *interp, const char *format, int objc, Tcl_Obj *const objv[]);
    int (*tcl_AppendFormatToObj) (Tcl_Interp *interp, Tcl_Obj *objPtr, const char *format, int objc, Tcl_Obj *const objv[]);
    Tcl_Obj * (*tcl_ObjPrintf) (const char *format, ...);
    void (*tcl_AppendPrintfToObj) (Tcl_Obj *objPtr, const char *format, ...);
} TclStubs;




extern TclStubs *tclStubsPtr;
# 2247 "/usr/include/tcl.h" 2 3 4






# 1 "/usr/include/tclPlatDecls.h" 1 3 4
# 77 "/usr/include/tclPlatDecls.h" 3 4
typedef struct TclPlatStubs {
    int magic;
    struct TclPlatStubHooks *hooks;
# 89 "/usr/include/tclPlatDecls.h" 3 4
} TclPlatStubs;




extern TclPlatStubs *tclPlatStubsPtr;
# 2254 "/usr/include/tcl.h" 2 3 4
# 2429 "/usr/include/tcl.h" 3 4
extern int Tcl_AppInit (Tcl_Interp *interp);
# 67 "_tkinter.c" 2
# 1 "/usr/include/tk.h" 1 3 4
# 78 "/usr/include/tk.h" 3 4
# 1 "/usr/include/X11/Xlib.h" 1 3 4
# 38 "/usr/include/X11/Xlib.h" 3 4
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
# 39 "/usr/include/X11/Xlib.h" 2 3 4





# 1 "/usr/include/X11/X.h" 1 3 4
# 66 "/usr/include/X11/X.h" 3 4
typedef unsigned long XID;



typedef unsigned long Mask;



typedef unsigned long Atom;

typedef unsigned long VisualID;
typedef unsigned long Time;
# 96 "/usr/include/X11/X.h" 3 4
typedef XID Window;
typedef XID Drawable;


typedef XID Font;

typedef XID Pixmap;
typedef XID Cursor;
typedef XID Colormap;
typedef XID GContext;
typedef XID KeySym;

typedef unsigned char KeyCode;
# 45 "/usr/include/X11/Xlib.h" 2 3 4


# 1 "/usr/include/X11/Xfuncproto.h" 1 3 4
# 48 "/usr/include/X11/Xlib.h" 2 3 4
# 1 "/usr/include/X11/Xosdefs.h" 1 3 4
# 49 "/usr/include/X11/Xlib.h" 2 3 4


# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stddef.h" 1 3 4
# 152 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stddef.h" 3 4
typedef long int ptrdiff_t;
# 52 "/usr/include/X11/Xlib.h" 2 3 4
# 69 "/usr/include/X11/Xlib.h" 3 4
extern int
_Xmblen(




    char *str,
    int len

    );





typedef char *XPointer;
# 156 "/usr/include/X11/Xlib.h" 3 4
typedef struct _XExtData {
 int number;
 struct _XExtData *next;
 int (*free_private)(
 struct _XExtData *extension
 );
 XPointer private_data;
} XExtData;




typedef struct {
 int extension;
 int major_opcode;
 int first_event;
 int first_error;
} XExtCodes;





typedef struct {
    int depth;
    int bits_per_pixel;
    int scanline_pad;
} XPixmapFormatValues;





typedef struct {
 int function;
 unsigned long plane_mask;
 unsigned long foreground;
 unsigned long background;
 int line_width;
 int line_style;
 int cap_style;

 int join_style;
 int fill_style;

 int fill_rule;
 int arc_mode;
 Pixmap tile;
 Pixmap stipple;
 int ts_x_origin;
 int ts_y_origin;
        Font font;
 int subwindow_mode;
 int graphics_exposures;
 int clip_x_origin;
 int clip_y_origin;
 Pixmap clip_mask;
 int dash_offset;
 char dashes;
} XGCValues;






typedef struct _XGC







*GC;




typedef struct {
 XExtData *ext_data;
 VisualID visualid;



 int class;

 unsigned long red_mask, green_mask, blue_mask;
 int bits_per_rgb;
 int map_entries;
} Visual;




typedef struct {
 int depth;
 int nvisuals;
 Visual *visuals;
} Depth;







struct _XDisplay;

typedef struct {
 XExtData *ext_data;
 struct _XDisplay *display;
 Window root;
 int width, height;
 int mwidth, mheight;
 int ndepths;
 Depth *depths;
 int root_depth;
 Visual *root_visual;
 GC default_gc;
 Colormap cmap;
 unsigned long white_pixel;
 unsigned long black_pixel;
 int max_maps, min_maps;
 int backing_store;
 int save_unders;
 long root_input_mask;
} Screen;




typedef struct {
 XExtData *ext_data;
 int depth;
 int bits_per_pixel;
 int scanline_pad;
} ScreenFormat;




typedef struct {
    Pixmap background_pixmap;
    unsigned long background_pixel;
    Pixmap border_pixmap;
    unsigned long border_pixel;
    int bit_gravity;
    int win_gravity;
    int backing_store;
    unsigned long backing_planes;
    unsigned long backing_pixel;
    int save_under;
    long event_mask;
    long do_not_propagate_mask;
    int override_redirect;
    Colormap colormap;
    Cursor cursor;
} XSetWindowAttributes;

typedef struct {
    int x, y;
    int width, height;
    int border_width;
    int depth;
    Visual *visual;
    Window root;



    int class;

    int bit_gravity;
    int win_gravity;
    int backing_store;
    unsigned long backing_planes;
    unsigned long backing_pixel;
    int save_under;
    Colormap colormap;
    int map_installed;
    int map_state;
    long all_event_masks;
    long your_event_mask;
    long do_not_propagate_mask;
    int override_redirect;
    Screen *screen;
} XWindowAttributes;






typedef struct {
 int family;
 int length;
 char *address;
} XHostAddress;




typedef struct {
 int typelength;
 int valuelength;
 char *type;
 char *value;
} XServerInterpretedAddress;




typedef struct _XImage {
    int width, height;
    int xoffset;
    int format;
    char *data;
    int byte_order;
    int bitmap_unit;
    int bitmap_bit_order;
    int bitmap_pad;
    int depth;
    int bytes_per_line;
    int bits_per_pixel;
    unsigned long red_mask;
    unsigned long green_mask;
    unsigned long blue_mask;
    XPointer obdata;
    struct funcs {
 struct _XImage *(*create_image)(
  struct _XDisplay* ,
  Visual* ,
  unsigned int ,
  int ,
  int ,
  char* ,
  unsigned int ,
  unsigned int ,
  int ,
  int );
 int (*destroy_image) (struct _XImage *);
 unsigned long (*get_pixel) (struct _XImage *, int, int);
 int (*put_pixel) (struct _XImage *, int, int, unsigned long);
 struct _XImage *(*sub_image)(struct _XImage *, int, int, unsigned int, unsigned int);
 int (*add_pixel) (struct _XImage *, long);
 } f;
} XImage;




typedef struct {
    int x, y;
    int width, height;
    int border_width;
    Window sibling;
    int stack_mode;
} XWindowChanges;




typedef struct {
 unsigned long pixel;
 unsigned short red, green, blue;
 char flags;
 char pad;
} XColor;






typedef struct {
    short x1, y1, x2, y2;
} XSegment;

typedef struct {
    short x, y;
} XPoint;

typedef struct {
    short x, y;
    unsigned short width, height;
} XRectangle;

typedef struct {
    short x, y;
    unsigned short width, height;
    short angle1, angle2;
} XArc;




typedef struct {
        int key_click_percent;
        int bell_percent;
        int bell_pitch;
        int bell_duration;
        int led;
        int led_mode;
        int key;
        int auto_repeat_mode;
} XKeyboardControl;



typedef struct {
        int key_click_percent;
 int bell_percent;
 unsigned int bell_pitch, bell_duration;
 unsigned long led_mask;
 int global_auto_repeat;
 char auto_repeats[32];
} XKeyboardState;



typedef struct {
        Time time;
 short x, y;
} XTimeCoord;



typedef struct {
  int max_keypermod;
  KeyCode *modifiermap;
} XModifierKeymap;
# 495 "/usr/include/X11/Xlib.h" 3 4
typedef struct _XDisplay Display;


struct _XPrivate;
struct _XrmHashBucketRec;

typedef struct



{
 XExtData *ext_data;
 struct _XPrivate *private1;
 int fd;
 int private2;
 int proto_major_version;
 int proto_minor_version;
 char *vendor;
        XID private3;
 XID private4;
 XID private5;
 int private6;
 XID (*resource_alloc)(
  struct _XDisplay*
 );
 int byte_order;
 int bitmap_unit;
 int bitmap_pad;
 int bitmap_bit_order;
 int nformats;
 ScreenFormat *pixmap_format;
 int private8;
 int release;
 struct _XPrivate *private9, *private10;
 int qlen;
 unsigned long last_request_read;
 unsigned long request;
 XPointer private11;
 XPointer private12;
 XPointer private13;
 XPointer private14;
 unsigned max_request_size;
 struct _XrmHashBucketRec *db;
 int (*private15)(
  struct _XDisplay*
  );
 char *display_name;
 int default_screen;
 int nscreens;
 Screen *screens;
 unsigned long motion_buffer;
 unsigned long private16;
 int min_keycode;
 int max_keycode;
 XPointer private17;
 XPointer private18;
 int private19;
 char *xdefaults;

}



*_XPrivDisplay;






typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window window;
 Window root;
 Window subwindow;
 Time time;
 int x, y;
 int x_root, y_root;
 unsigned int state;
 unsigned int keycode;
 int same_screen;
} XKeyEvent;
typedef XKeyEvent XKeyPressedEvent;
typedef XKeyEvent XKeyReleasedEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window window;
 Window root;
 Window subwindow;
 Time time;
 int x, y;
 int x_root, y_root;
 unsigned int state;
 unsigned int button;
 int same_screen;
} XButtonEvent;
typedef XButtonEvent XButtonPressedEvent;
typedef XButtonEvent XButtonReleasedEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window window;
 Window root;
 Window subwindow;
 Time time;
 int x, y;
 int x_root, y_root;
 unsigned int state;
 char is_hint;
 int same_screen;
} XMotionEvent;
typedef XMotionEvent XPointerMovedEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window window;
 Window root;
 Window subwindow;
 Time time;
 int x, y;
 int x_root, y_root;
 int mode;
 int detail;




 int same_screen;
 int focus;
 unsigned int state;
} XCrossingEvent;
typedef XCrossingEvent XEnterWindowEvent;
typedef XCrossingEvent XLeaveWindowEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window window;
 int mode;

 int detail;





} XFocusChangeEvent;
typedef XFocusChangeEvent XFocusInEvent;
typedef XFocusChangeEvent XFocusOutEvent;


typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window window;
 char key_vector[32];
} XKeymapEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window window;
 int x, y;
 int width, height;
 int count;
} XExposeEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Drawable drawable;
 int x, y;
 int width, height;
 int count;
 int major_code;
 int minor_code;
} XGraphicsExposeEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Drawable drawable;
 int major_code;
 int minor_code;
} XNoExposeEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window window;
 int state;
} XVisibilityEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window parent;
 Window window;
 int x, y;
 int width, height;
 int border_width;
 int override_redirect;
} XCreateWindowEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window event;
 Window window;
} XDestroyWindowEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window event;
 Window window;
 int from_configure;
} XUnmapEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window event;
 Window window;
 int override_redirect;
} XMapEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window parent;
 Window window;
} XMapRequestEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window event;
 Window window;
 Window parent;
 int x, y;
 int override_redirect;
} XReparentEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window event;
 Window window;
 int x, y;
 int width, height;
 int border_width;
 Window above;
 int override_redirect;
} XConfigureEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window event;
 Window window;
 int x, y;
} XGravityEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window window;
 int width, height;
} XResizeRequestEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window parent;
 Window window;
 int x, y;
 int width, height;
 int border_width;
 Window above;
 int detail;
 unsigned long value_mask;
} XConfigureRequestEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window event;
 Window window;
 int place;
} XCirculateEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window parent;
 Window window;
 int place;
} XCirculateRequestEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window window;
 Atom atom;
 Time time;
 int state;
} XPropertyEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window window;
 Atom selection;
 Time time;
} XSelectionClearEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window owner;
 Window requestor;
 Atom selection;
 Atom target;
 Atom property;
 Time time;
} XSelectionRequestEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window requestor;
 Atom selection;
 Atom target;
 Atom property;
 Time time;
} XSelectionEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window window;
 Colormap colormap;



 int new;

 int state;
} XColormapEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window window;
 Atom message_type;
 int format;
 union {
  char b[20];
  short s[10];
  long l[5];
  } data;
} XClientMessageEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window window;
 int request;

 int first_keycode;
 int count;
} XMappingEvent;

typedef struct {
 int type;
 Display *display;
 XID resourceid;
 unsigned long serial;
 unsigned char error_code;
 unsigned char request_code;
 unsigned char minor_code;
} XErrorEvent;

typedef struct {
 int type;
 unsigned long serial;
 int send_event;
 Display *display;
 Window window;
} XAnyEvent;







typedef struct
    {
    int type;
    unsigned long serial;
    int send_event;
    Display *display;
    int extension;
    int evtype;
    } XGenericEvent;

typedef struct {
    int type;
    unsigned long serial;
    int send_event;
    Display *display;
    int extension;
    int evtype;
    unsigned int cookie;
    void *data;
} XGenericEventCookie;





typedef union _XEvent {
        int type;
 XAnyEvent xany;
 XKeyEvent xkey;
 XButtonEvent xbutton;
 XMotionEvent xmotion;
 XCrossingEvent xcrossing;
 XFocusChangeEvent xfocus;
 XExposeEvent xexpose;
 XGraphicsExposeEvent xgraphicsexpose;
 XNoExposeEvent xnoexpose;
 XVisibilityEvent xvisibility;
 XCreateWindowEvent xcreatewindow;
 XDestroyWindowEvent xdestroywindow;
 XUnmapEvent xunmap;
 XMapEvent xmap;
 XMapRequestEvent xmaprequest;
 XReparentEvent xreparent;
 XConfigureEvent xconfigure;
 XGravityEvent xgravity;
 XResizeRequestEvent xresizerequest;
 XConfigureRequestEvent xconfigurerequest;
 XCirculateEvent xcirculate;
 XCirculateRequestEvent xcirculaterequest;
 XPropertyEvent xproperty;
 XSelectionClearEvent xselectionclear;
 XSelectionRequestEvent xselectionrequest;
 XSelectionEvent xselection;
 XColormapEvent xcolormap;
 XClientMessageEvent xclient;
 XMappingEvent xmapping;
 XErrorEvent xerror;
 XKeymapEvent xkeymap;
 XGenericEvent xgeneric;
 XGenericEventCookie xcookie;
 long pad[24];
} XEvent;







typedef struct {
    short lbearing;
    short rbearing;
    short width;
    short ascent;
    short descent;
    unsigned short attributes;
} XCharStruct;





typedef struct {
    Atom name;
    unsigned long card32;
} XFontProp;

typedef struct {
    XExtData *ext_data;
    Font fid;
    unsigned direction;
    unsigned min_char_or_byte2;
    unsigned max_char_or_byte2;
    unsigned min_byte1;
    unsigned max_byte1;
    int all_chars_exist;
    unsigned default_char;
    int n_properties;
    XFontProp *properties;
    XCharStruct min_bounds;
    XCharStruct max_bounds;
    XCharStruct *per_char;
    int ascent;
    int descent;
} XFontStruct;




typedef struct {
    char *chars;
    int nchars;
    int delta;
    Font font;
} XTextItem;

typedef struct {
    unsigned char byte1;
    unsigned char byte2;
} XChar2b;

typedef struct {
    XChar2b *chars;
    int nchars;
    int delta;
    Font font;
} XTextItem16;


typedef union { Display *display;
  GC gc;
  Visual *visual;
  Screen *screen;
  ScreenFormat *pixmap_format;
  XFontStruct *font; } XEDataObject;

typedef struct {
    XRectangle max_ink_extent;
    XRectangle max_logical_extent;
} XFontSetExtents;





typedef struct _XOM *XOM;
typedef struct _XOC *XOC, *XFontSet;

typedef struct {
    char *chars;
    int nchars;
    int delta;
    XFontSet font_set;
} XmbTextItem;

typedef struct {
    wchar_t *chars;
    int nchars;
    int delta;
    XFontSet font_set;
} XwcTextItem;
# 1129 "/usr/include/X11/Xlib.h" 3 4
typedef struct {
    int charset_count;
    char **charset_list;
} XOMCharSetList;

typedef enum {
    XOMOrientation_LTR_TTB,
    XOMOrientation_RTL_TTB,
    XOMOrientation_TTB_LTR,
    XOMOrientation_TTB_RTL,
    XOMOrientation_Context
} XOrientation;

typedef struct {
    int num_orientation;
    XOrientation *orientation;
} XOMOrientation;

typedef struct {
    int num_font;
    XFontStruct **font_struct_list;
    char **font_name_list;
} XOMFontInfo;

typedef struct _XIM *XIM;
typedef struct _XIC *XIC;

typedef void (*XIMProc)(
    XIM,
    XPointer,
    XPointer
);

typedef int (*XICProc)(
    XIC,
    XPointer,
    XPointer
);

typedef void (*XIDProc)(
    Display*,
    XPointer,
    XPointer
);

typedef unsigned long XIMStyle;

typedef struct {
    unsigned short count_styles;
    XIMStyle *supported_styles;
} XIMStyles;
# 1241 "/usr/include/X11/Xlib.h" 3 4
typedef void *XVaNestedList;

typedef struct {
    XPointer client_data;
    XIMProc callback;
} XIMCallback;

typedef struct {
    XPointer client_data;
    XICProc callback;
} XICCallback;

typedef unsigned long XIMFeedback;
# 1265 "/usr/include/X11/Xlib.h" 3 4
typedef struct _XIMText {
    unsigned short length;
    XIMFeedback *feedback;
    int encoding_is_wchar;
    union {
 char *multi_byte;
 wchar_t *wide_char;
    } string;
} XIMText;

typedef unsigned long XIMPreeditState;





typedef struct _XIMPreeditStateNotifyCallbackStruct {
    XIMPreeditState state;
} XIMPreeditStateNotifyCallbackStruct;

typedef unsigned long XIMResetState;




typedef unsigned long XIMStringConversionFeedback;
# 1299 "/usr/include/X11/Xlib.h" 3 4
typedef struct _XIMStringConversionText {
    unsigned short length;
    XIMStringConversionFeedback *feedback;
    int encoding_is_wchar;
    union {
 char *mbs;
 wchar_t *wcs;
    } string;
} XIMStringConversionText;

typedef unsigned short XIMStringConversionPosition;

typedef unsigned short XIMStringConversionType;






typedef unsigned short XIMStringConversionOperation;




typedef enum {
    XIMForwardChar, XIMBackwardChar,
    XIMForwardWord, XIMBackwardWord,
    XIMCaretUp, XIMCaretDown,
    XIMNextLine, XIMPreviousLine,
    XIMLineStart, XIMLineEnd,
    XIMAbsolutePosition,
    XIMDontChange
} XIMCaretDirection;

typedef struct _XIMStringConversionCallbackStruct {
    XIMStringConversionPosition position;
    XIMCaretDirection direction;
    XIMStringConversionOperation operation;
    unsigned short factor;
    XIMStringConversionText *text;
} XIMStringConversionCallbackStruct;

typedef struct _XIMPreeditDrawCallbackStruct {
    int caret;
    int chg_first;
    int chg_length;
    XIMText *text;
} XIMPreeditDrawCallbackStruct;

typedef enum {
    XIMIsInvisible,
    XIMIsPrimary,
    XIMIsSecondary
} XIMCaretStyle;

typedef struct _XIMPreeditCaretCallbackStruct {
    int position;
    XIMCaretDirection direction;
    XIMCaretStyle style;
} XIMPreeditCaretCallbackStruct;

typedef enum {
    XIMTextType,
    XIMBitmapType
} XIMStatusDataType;

typedef struct _XIMStatusDrawCallbackStruct {
    XIMStatusDataType type;
    union {
 XIMText *text;
 Pixmap bitmap;
    } data;
} XIMStatusDrawCallbackStruct;

typedef struct _XIMHotKeyTrigger {
    KeySym keysym;
    int modifier;
    int modifier_mask;
} XIMHotKeyTrigger;

typedef struct _XIMHotKeyTriggers {
    int num_hot_key;
    XIMHotKeyTrigger *key;
} XIMHotKeyTriggers;

typedef unsigned long XIMHotKeyState;




typedef struct {
    unsigned short count_values;
    char **supported_values;
} XIMValuesList;







extern int _Xdebug;

extern XFontStruct *XLoadQueryFont(
    Display* ,
    const char*
);

extern XFontStruct *XQueryFont(
    Display* ,
    XID
);


extern XTimeCoord *XGetMotionEvents(
    Display* ,
    Window ,
    Time ,
    Time ,
    int*
);

extern XModifierKeymap *XDeleteModifiermapEntry(
    XModifierKeymap* ,

    unsigned int ,



    int
);

extern XModifierKeymap *XGetModifierMapping(
    Display*
);

extern XModifierKeymap *XInsertModifiermapEntry(
    XModifierKeymap* ,

    unsigned int ,



    int
);

extern XModifierKeymap *XNewModifiermap(
    int
);

extern XImage *XCreateImage(
    Display* ,
    Visual* ,
    unsigned int ,
    int ,
    int ,
    char* ,
    unsigned int ,
    unsigned int ,
    int ,
    int
);
extern int XInitImage(
    XImage*
);
extern XImage *XGetImage(
    Display* ,
    Drawable ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    unsigned long ,
    int
);
extern XImage *XGetSubImage(
    Display* ,
    Drawable ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    unsigned long ,
    int ,
    XImage* ,
    int ,
    int
);




extern Display *XOpenDisplay(
    const char*
);

extern void XrmInitialize(
    void
);

extern char *XFetchBytes(
    Display* ,
    int*
);
extern char *XFetchBuffer(
    Display* ,
    int* ,
    int
);
extern char *XGetAtomName(
    Display* ,
    Atom
);
extern int XGetAtomNames(
    Display* ,
    Atom* ,
    int ,
    char**
);
extern char *XGetDefault(
    Display* ,
    const char* ,
    const char*
);
extern char *XDisplayName(
    const char*
);
extern char *XKeysymToString(
    KeySym
);

extern int (*XSynchronize(
    Display* ,
    int
))(
    Display*
);
extern int (*XSetAfterFunction(
    Display* ,
    int (*) (
      Display*
            )
))(
    Display*
);
extern Atom XInternAtom(
    Display* ,
    const char* ,
    int
);
extern int XInternAtoms(
    Display* ,
    char** ,
    int ,
    int ,
    Atom*
);
extern Colormap XCopyColormapAndFree(
    Display* ,
    Colormap
);
extern Colormap XCreateColormap(
    Display* ,
    Window ,
    Visual* ,
    int
);
extern Cursor XCreatePixmapCursor(
    Display* ,
    Pixmap ,
    Pixmap ,
    XColor* ,
    XColor* ,
    unsigned int ,
    unsigned int
);
extern Cursor XCreateGlyphCursor(
    Display* ,
    Font ,
    Font ,
    unsigned int ,
    unsigned int ,
    XColor const * ,
    XColor const *
);
extern Cursor XCreateFontCursor(
    Display* ,
    unsigned int
);
extern Font XLoadFont(
    Display* ,
    const char*
);
extern GC XCreateGC(
    Display* ,
    Drawable ,
    unsigned long ,
    XGCValues*
);
extern GContext XGContextFromGC(
    GC
);
extern void XFlushGC(
    Display* ,
    GC
);
extern Pixmap XCreatePixmap(
    Display* ,
    Drawable ,
    unsigned int ,
    unsigned int ,
    unsigned int
);
extern Pixmap XCreateBitmapFromData(
    Display* ,
    Drawable ,
    const char* ,
    unsigned int ,
    unsigned int
);
extern Pixmap XCreatePixmapFromBitmapData(
    Display* ,
    Drawable ,
    char* ,
    unsigned int ,
    unsigned int ,
    unsigned long ,
    unsigned long ,
    unsigned int
);
extern Window XCreateSimpleWindow(
    Display* ,
    Window ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    unsigned int ,
    unsigned long ,
    unsigned long
);
extern Window XGetSelectionOwner(
    Display* ,
    Atom
);
extern Window XCreateWindow(
    Display* ,
    Window ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    unsigned int ,
    int ,
    unsigned int ,
    Visual* ,
    unsigned long ,
    XSetWindowAttributes*
);
extern Colormap *XListInstalledColormaps(
    Display* ,
    Window ,
    int*
);
extern char **XListFonts(
    Display* ,
    const char* ,
    int ,
    int*
);
extern char **XListFontsWithInfo(
    Display* ,
    const char* ,
    int ,
    int* ,
    XFontStruct**
);
extern char **XGetFontPath(
    Display* ,
    int*
);
extern char **XListExtensions(
    Display* ,
    int*
);
extern Atom *XListProperties(
    Display* ,
    Window ,
    int*
);
extern XHostAddress *XListHosts(
    Display* ,
    int* ,
    int*
);
extern KeySym XKeycodeToKeysym(
    Display* ,

    unsigned int ,



    int
);
extern KeySym XLookupKeysym(
    XKeyEvent* ,
    int
);
extern KeySym *XGetKeyboardMapping(
    Display* ,

    unsigned int ,



    int ,
    int*
);
extern KeySym XStringToKeysym(
    const char*
);
extern long XMaxRequestSize(
    Display*
);
extern long XExtendedMaxRequestSize(
    Display*
);
extern char *XResourceManagerString(
    Display*
);
extern char *XScreenResourceString(
 Screen*
);
extern unsigned long XDisplayMotionBufferSize(
    Display*
);
extern VisualID XVisualIDFromVisual(
    Visual*
);



extern int XInitThreads(
    void
);

extern void XLockDisplay(
    Display*
);

extern void XUnlockDisplay(
    Display*
);



extern XExtCodes *XInitExtension(
    Display* ,
    const char*
);

extern XExtCodes *XAddExtension(
    Display*
);
extern XExtData *XFindOnExtensionList(
    XExtData** ,
    int
);
extern XExtData **XEHeadOfExtensionList(
    XEDataObject
);


extern Window XRootWindow(
    Display* ,
    int
);
extern Window XDefaultRootWindow(
    Display*
);
extern Window XRootWindowOfScreen(
    Screen*
);
extern Visual *XDefaultVisual(
    Display* ,
    int
);
extern Visual *XDefaultVisualOfScreen(
    Screen*
);
extern GC XDefaultGC(
    Display* ,
    int
);
extern GC XDefaultGCOfScreen(
    Screen*
);
extern unsigned long XBlackPixel(
    Display* ,
    int
);
extern unsigned long XWhitePixel(
    Display* ,
    int
);
extern unsigned long XAllPlanes(
    void
);
extern unsigned long XBlackPixelOfScreen(
    Screen*
);
extern unsigned long XWhitePixelOfScreen(
    Screen*
);
extern unsigned long XNextRequest(
    Display*
);
extern unsigned long XLastKnownRequestProcessed(
    Display*
);
extern char *XServerVendor(
    Display*
);
extern char *XDisplayString(
    Display*
);
extern Colormap XDefaultColormap(
    Display* ,
    int
);
extern Colormap XDefaultColormapOfScreen(
    Screen*
);
extern Display *XDisplayOfScreen(
    Screen*
);
extern Screen *XScreenOfDisplay(
    Display* ,
    int
);
extern Screen *XDefaultScreenOfDisplay(
    Display*
);
extern long XEventMaskOfScreen(
    Screen*
);

extern int XScreenNumberOfScreen(
    Screen*
);

typedef int (*XErrorHandler) (
    Display* ,
    XErrorEvent*
);

extern XErrorHandler XSetErrorHandler (
    XErrorHandler
);


typedef int (*XIOErrorHandler) (
    Display*
);

extern XIOErrorHandler XSetIOErrorHandler (
    XIOErrorHandler
);


extern XPixmapFormatValues *XListPixmapFormats(
    Display* ,
    int*
);
extern int *XListDepths(
    Display* ,
    int ,
    int*
);



extern int XReconfigureWMWindow(
    Display* ,
    Window ,
    int ,
    unsigned int ,
    XWindowChanges*
);

extern int XGetWMProtocols(
    Display* ,
    Window ,
    Atom** ,
    int*
);
extern int XSetWMProtocols(
    Display* ,
    Window ,
    Atom* ,
    int
);
extern int XIconifyWindow(
    Display* ,
    Window ,
    int
);
extern int XWithdrawWindow(
    Display* ,
    Window ,
    int
);
extern int XGetCommand(
    Display* ,
    Window ,
    char*** ,
    int*
);
extern int XGetWMColormapWindows(
    Display* ,
    Window ,
    Window** ,
    int*
);
extern int XSetWMColormapWindows(
    Display* ,
    Window ,
    Window* ,
    int
);
extern void XFreeStringList(
    char**
);
extern int XSetTransientForHint(
    Display* ,
    Window ,
    Window
);



extern int XActivateScreenSaver(
    Display*
);

extern int XAddHost(
    Display* ,
    XHostAddress*
);

extern int XAddHosts(
    Display* ,
    XHostAddress* ,
    int
);

extern int XAddToExtensionList(
    struct _XExtData** ,
    XExtData*
);

extern int XAddToSaveSet(
    Display* ,
    Window
);

extern int XAllocColor(
    Display* ,
    Colormap ,
    XColor*
);

extern int XAllocColorCells(
    Display* ,
    Colormap ,
    int ,
    unsigned long* ,
    unsigned int ,
    unsigned long* ,
    unsigned int
);

extern int XAllocColorPlanes(
    Display* ,
    Colormap ,
    int ,
    unsigned long* ,
    int ,
    int ,
    int ,
    int ,
    unsigned long* ,
    unsigned long* ,
    unsigned long*
);

extern int XAllocNamedColor(
    Display* ,
    Colormap ,
    const char* ,
    XColor* ,
    XColor*
);

extern int XAllowEvents(
    Display* ,
    int ,
    Time
);

extern int XAutoRepeatOff(
    Display*
);

extern int XAutoRepeatOn(
    Display*
);

extern int XBell(
    Display* ,
    int
);

extern int XBitmapBitOrder(
    Display*
);

extern int XBitmapPad(
    Display*
);

extern int XBitmapUnit(
    Display*
);

extern int XCellsOfScreen(
    Screen*
);

extern int XChangeActivePointerGrab(
    Display* ,
    unsigned int ,
    Cursor ,
    Time
);

extern int XChangeGC(
    Display* ,
    GC ,
    unsigned long ,
    XGCValues*
);

extern int XChangeKeyboardControl(
    Display* ,
    unsigned long ,
    XKeyboardControl*
);

extern int XChangeKeyboardMapping(
    Display* ,
    int ,
    int ,
    KeySym* ,
    int
);

extern int XChangePointerControl(
    Display* ,
    int ,
    int ,
    int ,
    int ,
    int
);

extern int XChangeProperty(
    Display* ,
    Window ,
    Atom ,
    Atom ,
    int ,
    int ,
    const unsigned char* ,
    int
);

extern int XChangeSaveSet(
    Display* ,
    Window ,
    int
);

extern int XChangeWindowAttributes(
    Display* ,
    Window ,
    unsigned long ,
    XSetWindowAttributes*
);

extern int XCheckIfEvent(
    Display* ,
    XEvent* ,
    int (*) (
        Display* ,
               XEvent* ,
               XPointer
             ) ,
    XPointer
);

extern int XCheckMaskEvent(
    Display* ,
    long ,
    XEvent*
);

extern int XCheckTypedEvent(
    Display* ,
    int ,
    XEvent*
);

extern int XCheckTypedWindowEvent(
    Display* ,
    Window ,
    int ,
    XEvent*
);

extern int XCheckWindowEvent(
    Display* ,
    Window ,
    long ,
    XEvent*
);

extern int XCirculateSubwindows(
    Display* ,
    Window ,
    int
);

extern int XCirculateSubwindowsDown(
    Display* ,
    Window
);

extern int XCirculateSubwindowsUp(
    Display* ,
    Window
);

extern int XClearArea(
    Display* ,
    Window ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    int
);

extern int XClearWindow(
    Display* ,
    Window
);

extern int XCloseDisplay(
    Display*
);

extern int XConfigureWindow(
    Display* ,
    Window ,
    unsigned int ,
    XWindowChanges*
);

extern int XConnectionNumber(
    Display*
);

extern int XConvertSelection(
    Display* ,
    Atom ,
    Atom ,
    Atom ,
    Window ,
    Time
);

extern int XCopyArea(
    Display* ,
    Drawable ,
    Drawable ,
    GC ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    int ,
    int
);

extern int XCopyGC(
    Display* ,
    GC ,
    unsigned long ,
    GC
);

extern int XCopyPlane(
    Display* ,
    Drawable ,
    Drawable ,
    GC ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    int ,
    int ,
    unsigned long
);

extern int XDefaultDepth(
    Display* ,
    int
);

extern int XDefaultDepthOfScreen(
    Screen*
);

extern int XDefaultScreen(
    Display*
);

extern int XDefineCursor(
    Display* ,
    Window ,
    Cursor
);

extern int XDeleteProperty(
    Display* ,
    Window ,
    Atom
);

extern int XDestroyWindow(
    Display* ,
    Window
);

extern int XDestroySubwindows(
    Display* ,
    Window
);

extern int XDoesBackingStore(
    Screen*
);

extern int XDoesSaveUnders(
    Screen*
);

extern int XDisableAccessControl(
    Display*
);


extern int XDisplayCells(
    Display* ,
    int
);

extern int XDisplayHeight(
    Display* ,
    int
);

extern int XDisplayHeightMM(
    Display* ,
    int
);

extern int XDisplayKeycodes(
    Display* ,
    int* ,
    int*
);

extern int XDisplayPlanes(
    Display* ,
    int
);

extern int XDisplayWidth(
    Display* ,
    int
);

extern int XDisplayWidthMM(
    Display* ,
    int
);

extern int XDrawArc(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    int ,
    int
);

extern int XDrawArcs(
    Display* ,
    Drawable ,
    GC ,
    XArc* ,
    int
);

extern int XDrawImageString(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    const char* ,
    int
);

extern int XDrawImageString16(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    const XChar2b* ,
    int
);

extern int XDrawLine(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    int ,
    int
);

extern int XDrawLines(
    Display* ,
    Drawable ,
    GC ,
    XPoint* ,
    int ,
    int
);

extern int XDrawPoint(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int
);

extern int XDrawPoints(
    Display* ,
    Drawable ,
    GC ,
    XPoint* ,
    int ,
    int
);

extern int XDrawRectangle(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    unsigned int ,
    unsigned int
);

extern int XDrawRectangles(
    Display* ,
    Drawable ,
    GC ,
    XRectangle* ,
    int
);

extern int XDrawSegments(
    Display* ,
    Drawable ,
    GC ,
    XSegment* ,
    int
);

extern int XDrawString(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    const char* ,
    int
);

extern int XDrawString16(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    const XChar2b* ,
    int
);

extern int XDrawText(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    XTextItem* ,
    int
);

extern int XDrawText16(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    XTextItem16* ,
    int
);

extern int XEnableAccessControl(
    Display*
);

extern int XEventsQueued(
    Display* ,
    int
);

extern int XFetchName(
    Display* ,
    Window ,
    char**
);

extern int XFillArc(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    int ,
    int
);

extern int XFillArcs(
    Display* ,
    Drawable ,
    GC ,
    XArc* ,
    int
);

extern int XFillPolygon(
    Display* ,
    Drawable ,
    GC ,
    XPoint* ,
    int ,
    int ,
    int
);

extern int XFillRectangle(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    unsigned int ,
    unsigned int
);

extern int XFillRectangles(
    Display* ,
    Drawable ,
    GC ,
    XRectangle* ,
    int
);

extern int XFlush(
    Display*
);

extern int XForceScreenSaver(
    Display* ,
    int
);

extern int XFree(
    void*
);

extern int XFreeColormap(
    Display* ,
    Colormap
);

extern int XFreeColors(
    Display* ,
    Colormap ,
    unsigned long* ,
    int ,
    unsigned long
);

extern int XFreeCursor(
    Display* ,
    Cursor
);

extern int XFreeExtensionList(
    char**
);

extern int XFreeFont(
    Display* ,
    XFontStruct*
);

extern int XFreeFontInfo(
    char** ,
    XFontStruct* ,
    int
);

extern int XFreeFontNames(
    char**
);

extern int XFreeFontPath(
    char**
);

extern int XFreeGC(
    Display* ,
    GC
);

extern int XFreeModifiermap(
    XModifierKeymap*
);

extern int XFreePixmap(
    Display* ,
    Pixmap
);

extern int XGeometry(
    Display* ,
    int ,
    const char* ,
    const char* ,
    unsigned int ,
    unsigned int ,
    unsigned int ,
    int ,
    int ,
    int* ,
    int* ,
    int* ,
    int*
);

extern int XGetErrorDatabaseText(
    Display* ,
    const char* ,
    const char* ,
    const char* ,
    char* ,
    int
);

extern int XGetErrorText(
    Display* ,
    int ,
    char* ,
    int
);

extern int XGetFontProperty(
    XFontStruct* ,
    Atom ,
    unsigned long*
);

extern int XGetGCValues(
    Display* ,
    GC ,
    unsigned long ,
    XGCValues*
);

extern int XGetGeometry(
    Display* ,
    Drawable ,
    Window* ,
    int* ,
    int* ,
    unsigned int* ,
    unsigned int* ,
    unsigned int* ,
    unsigned int*
);

extern int XGetIconName(
    Display* ,
    Window ,
    char**
);

extern int XGetInputFocus(
    Display* ,
    Window* ,
    int*
);

extern int XGetKeyboardControl(
    Display* ,
    XKeyboardState*
);

extern int XGetPointerControl(
    Display* ,
    int* ,
    int* ,
    int*
);

extern int XGetPointerMapping(
    Display* ,
    unsigned char* ,
    int
);

extern int XGetScreenSaver(
    Display* ,
    int* ,
    int* ,
    int* ,
    int*
);

extern int XGetTransientForHint(
    Display* ,
    Window ,
    Window*
);

extern int XGetWindowProperty(
    Display* ,
    Window ,
    Atom ,
    long ,
    long ,
    int ,
    Atom ,
    Atom* ,
    int* ,
    unsigned long* ,
    unsigned long* ,
    unsigned char**
);

extern int XGetWindowAttributes(
    Display* ,
    Window ,
    XWindowAttributes*
);

extern int XGrabButton(
    Display* ,
    unsigned int ,
    unsigned int ,
    Window ,
    int ,
    unsigned int ,
    int ,
    int ,
    Window ,
    Cursor
);

extern int XGrabKey(
    Display* ,
    int ,
    unsigned int ,
    Window ,
    int ,
    int ,
    int
);

extern int XGrabKeyboard(
    Display* ,
    Window ,
    int ,
    int ,
    int ,
    Time
);

extern int XGrabPointer(
    Display* ,
    Window ,
    int ,
    unsigned int ,
    int ,
    int ,
    Window ,
    Cursor ,
    Time
);

extern int XGrabServer(
    Display*
);

extern int XHeightMMOfScreen(
    Screen*
);

extern int XHeightOfScreen(
    Screen*
);

extern int XIfEvent(
    Display* ,
    XEvent* ,
    int (*) (
        Display* ,
               XEvent* ,
               XPointer
             ) ,
    XPointer
);

extern int XImageByteOrder(
    Display*
);

extern int XInstallColormap(
    Display* ,
    Colormap
);

extern KeyCode XKeysymToKeycode(
    Display* ,
    KeySym
);

extern int XKillClient(
    Display* ,
    XID
);

extern int XLookupColor(
    Display* ,
    Colormap ,
    const char* ,
    XColor* ,
    XColor*
);

extern int XLowerWindow(
    Display* ,
    Window
);

extern int XMapRaised(
    Display* ,
    Window
);

extern int XMapSubwindows(
    Display* ,
    Window
);

extern int XMapWindow(
    Display* ,
    Window
);

extern int XMaskEvent(
    Display* ,
    long ,
    XEvent*
);

extern int XMaxCmapsOfScreen(
    Screen*
);

extern int XMinCmapsOfScreen(
    Screen*
);

extern int XMoveResizeWindow(
    Display* ,
    Window ,
    int ,
    int ,
    unsigned int ,
    unsigned int
);

extern int XMoveWindow(
    Display* ,
    Window ,
    int ,
    int
);

extern int XNextEvent(
    Display* ,
    XEvent*
);

extern int XNoOp(
    Display*
);

extern int XParseColor(
    Display* ,
    Colormap ,
    const char* ,
    XColor*
);

extern int XParseGeometry(
    const char* ,
    int* ,
    int* ,
    unsigned int* ,
    unsigned int*
);

extern int XPeekEvent(
    Display* ,
    XEvent*
);

extern int XPeekIfEvent(
    Display* ,
    XEvent* ,
    int (*) (
        Display* ,
               XEvent* ,
               XPointer
             ) ,
    XPointer
);

extern int XPending(
    Display*
);

extern int XPlanesOfScreen(
    Screen*
);

extern int XProtocolRevision(
    Display*
);

extern int XProtocolVersion(
    Display*
);


extern int XPutBackEvent(
    Display* ,
    XEvent*
);

extern int XPutImage(
    Display* ,
    Drawable ,
    GC ,
    XImage* ,
    int ,
    int ,
    int ,
    int ,
    unsigned int ,
    unsigned int
);

extern int XQLength(
    Display*
);

extern int XQueryBestCursor(
    Display* ,
    Drawable ,
    unsigned int ,
    unsigned int ,
    unsigned int* ,
    unsigned int*
);

extern int XQueryBestSize(
    Display* ,
    int ,
    Drawable ,
    unsigned int ,
    unsigned int ,
    unsigned int* ,
    unsigned int*
);

extern int XQueryBestStipple(
    Display* ,
    Drawable ,
    unsigned int ,
    unsigned int ,
    unsigned int* ,
    unsigned int*
);

extern int XQueryBestTile(
    Display* ,
    Drawable ,
    unsigned int ,
    unsigned int ,
    unsigned int* ,
    unsigned int*
);

extern int XQueryColor(
    Display* ,
    Colormap ,
    XColor*
);

extern int XQueryColors(
    Display* ,
    Colormap ,
    XColor* ,
    int
);

extern int XQueryExtension(
    Display* ,
    const char* ,
    int* ,
    int* ,
    int*
);

extern int XQueryKeymap(
    Display* ,
    char [32]
);

extern int XQueryPointer(
    Display* ,
    Window ,
    Window* ,
    Window* ,
    int* ,
    int* ,
    int* ,
    int* ,
    unsigned int*
);

extern int XQueryTextExtents(
    Display* ,
    XID ,
    const char* ,
    int ,
    int* ,
    int* ,
    int* ,
    XCharStruct*
);

extern int XQueryTextExtents16(
    Display* ,
    XID ,
    const XChar2b* ,
    int ,
    int* ,
    int* ,
    int* ,
    XCharStruct*
);

extern int XQueryTree(
    Display* ,
    Window ,
    Window* ,
    Window* ,
    Window** ,
    unsigned int*
);

extern int XRaiseWindow(
    Display* ,
    Window
);

extern int XReadBitmapFile(
    Display* ,
    Drawable ,
    const char* ,
    unsigned int* ,
    unsigned int* ,
    Pixmap* ,
    int* ,
    int*
);

extern int XReadBitmapFileData(
    const char* ,
    unsigned int* ,
    unsigned int* ,
    unsigned char** ,
    int* ,
    int*
);

extern int XRebindKeysym(
    Display* ,
    KeySym ,
    KeySym* ,
    int ,
    const unsigned char* ,
    int
);

extern int XRecolorCursor(
    Display* ,
    Cursor ,
    XColor* ,
    XColor*
);

extern int XRefreshKeyboardMapping(
    XMappingEvent*
);

extern int XRemoveFromSaveSet(
    Display* ,
    Window
);

extern int XRemoveHost(
    Display* ,
    XHostAddress*
);

extern int XRemoveHosts(
    Display* ,
    XHostAddress* ,
    int
);

extern int XReparentWindow(
    Display* ,
    Window ,
    Window ,
    int ,
    int
);

extern int XResetScreenSaver(
    Display*
);

extern int XResizeWindow(
    Display* ,
    Window ,
    unsigned int ,
    unsigned int
);

extern int XRestackWindows(
    Display* ,
    Window* ,
    int
);

extern int XRotateBuffers(
    Display* ,
    int
);

extern int XRotateWindowProperties(
    Display* ,
    Window ,
    Atom* ,
    int ,
    int
);

extern int XScreenCount(
    Display*
);

extern int XSelectInput(
    Display* ,
    Window ,
    long
);

extern int XSendEvent(
    Display* ,
    Window ,
    int ,
    long ,
    XEvent*
);

extern int XSetAccessControl(
    Display* ,
    int
);

extern int XSetArcMode(
    Display* ,
    GC ,
    int
);

extern int XSetBackground(
    Display* ,
    GC ,
    unsigned long
);

extern int XSetClipMask(
    Display* ,
    GC ,
    Pixmap
);

extern int XSetClipOrigin(
    Display* ,
    GC ,
    int ,
    int
);

extern int XSetClipRectangles(
    Display* ,
    GC ,
    int ,
    int ,
    XRectangle* ,
    int ,
    int
);

extern int XSetCloseDownMode(
    Display* ,
    int
);

extern int XSetCommand(
    Display* ,
    Window ,
    char** ,
    int
);

extern int XSetDashes(
    Display* ,
    GC ,
    int ,
    const char* ,
    int
);

extern int XSetFillRule(
    Display* ,
    GC ,
    int
);

extern int XSetFillStyle(
    Display* ,
    GC ,
    int
);

extern int XSetFont(
    Display* ,
    GC ,
    Font
);

extern int XSetFontPath(
    Display* ,
    char** ,
    int
);

extern int XSetForeground(
    Display* ,
    GC ,
    unsigned long
);

extern int XSetFunction(
    Display* ,
    GC ,
    int
);

extern int XSetGraphicsExposures(
    Display* ,
    GC ,
    int
);

extern int XSetIconName(
    Display* ,
    Window ,
    const char*
);

extern int XSetInputFocus(
    Display* ,
    Window ,
    int ,
    Time
);

extern int XSetLineAttributes(
    Display* ,
    GC ,
    unsigned int ,
    int ,
    int ,
    int
);

extern int XSetModifierMapping(
    Display* ,
    XModifierKeymap*
);

extern int XSetPlaneMask(
    Display* ,
    GC ,
    unsigned long
);

extern int XSetPointerMapping(
    Display* ,
    const unsigned char* ,
    int
);

extern int XSetScreenSaver(
    Display* ,
    int ,
    int ,
    int ,
    int
);

extern int XSetSelectionOwner(
    Display* ,
    Atom ,
    Window ,
    Time
);

extern int XSetState(
    Display* ,
    GC ,
    unsigned long ,
    unsigned long ,
    int ,
    unsigned long
);

extern int XSetStipple(
    Display* ,
    GC ,
    Pixmap
);

extern int XSetSubwindowMode(
    Display* ,
    GC ,
    int
);

extern int XSetTSOrigin(
    Display* ,
    GC ,
    int ,
    int
);

extern int XSetTile(
    Display* ,
    GC ,
    Pixmap
);

extern int XSetWindowBackground(
    Display* ,
    Window ,
    unsigned long
);

extern int XSetWindowBackgroundPixmap(
    Display* ,
    Window ,
    Pixmap
);

extern int XSetWindowBorder(
    Display* ,
    Window ,
    unsigned long
);

extern int XSetWindowBorderPixmap(
    Display* ,
    Window ,
    Pixmap
);

extern int XSetWindowBorderWidth(
    Display* ,
    Window ,
    unsigned int
);

extern int XSetWindowColormap(
    Display* ,
    Window ,
    Colormap
);

extern int XStoreBuffer(
    Display* ,
    const char* ,
    int ,
    int
);

extern int XStoreBytes(
    Display* ,
    const char* ,
    int
);

extern int XStoreColor(
    Display* ,
    Colormap ,
    XColor*
);

extern int XStoreColors(
    Display* ,
    Colormap ,
    XColor* ,
    int
);

extern int XStoreName(
    Display* ,
    Window ,
    const char*
);

extern int XStoreNamedColor(
    Display* ,
    Colormap ,
    const char* ,
    unsigned long ,
    int
);

extern int XSync(
    Display* ,
    int
);

extern int XTextExtents(
    XFontStruct* ,
    const char* ,
    int ,
    int* ,
    int* ,
    int* ,
    XCharStruct*
);

extern int XTextExtents16(
    XFontStruct* ,
    const XChar2b* ,
    int ,
    int* ,
    int* ,
    int* ,
    XCharStruct*
);

extern int XTextWidth(
    XFontStruct* ,
    const char* ,
    int
);

extern int XTextWidth16(
    XFontStruct* ,
    const XChar2b* ,
    int
);

extern int XTranslateCoordinates(
    Display* ,
    Window ,
    Window ,
    int ,
    int ,
    int* ,
    int* ,
    Window*
);

extern int XUndefineCursor(
    Display* ,
    Window
);

extern int XUngrabButton(
    Display* ,
    unsigned int ,
    unsigned int ,
    Window
);

extern int XUngrabKey(
    Display* ,
    int ,
    unsigned int ,
    Window
);

extern int XUngrabKeyboard(
    Display* ,
    Time
);

extern int XUngrabPointer(
    Display* ,
    Time
);

extern int XUngrabServer(
    Display*
);

extern int XUninstallColormap(
    Display* ,
    Colormap
);

extern int XUnloadFont(
    Display* ,
    Font
);

extern int XUnmapSubwindows(
    Display* ,
    Window
);

extern int XUnmapWindow(
    Display* ,
    Window
);

extern int XVendorRelease(
    Display*
);

extern int XWarpPointer(
    Display* ,
    Window ,
    Window ,
    int ,
    int ,
    unsigned int ,
    unsigned int ,
    int ,
    int
);

extern int XWidthMMOfScreen(
    Screen*
);

extern int XWidthOfScreen(
    Screen*
);

extern int XWindowEvent(
    Display* ,
    Window ,
    long ,
    XEvent*
);

extern int XWriteBitmapFile(
    Display* ,
    const char* ,
    Pixmap ,
    unsigned int ,
    unsigned int ,
    int ,
    int
);

extern int XSupportsLocale (void);

extern char *XSetLocaleModifiers(
    const char*
);

extern XOM XOpenOM(
    Display* ,
    struct _XrmHashBucketRec* ,
    const char* ,
    const char*
);

extern int XCloseOM(
    XOM
);

extern char *XSetOMValues(
    XOM ,
    ...
) __attribute__ ((__sentinel__(0)));

extern char *XGetOMValues(
    XOM ,
    ...
) __attribute__ ((__sentinel__(0)));

extern Display *XDisplayOfOM(
    XOM
);

extern char *XLocaleOfOM(
    XOM
);

extern XOC XCreateOC(
    XOM ,
    ...
) __attribute__ ((__sentinel__(0)));

extern void XDestroyOC(
    XOC
);

extern XOM XOMOfOC(
    XOC
);

extern char *XSetOCValues(
    XOC ,
    ...
) __attribute__ ((__sentinel__(0)));

extern char *XGetOCValues(
    XOC ,
    ...
) __attribute__ ((__sentinel__(0)));

extern XFontSet XCreateFontSet(
    Display* ,
    const char* ,
    char*** ,
    int* ,
    char**
);

extern void XFreeFontSet(
    Display* ,
    XFontSet
);

extern int XFontsOfFontSet(
    XFontSet ,
    XFontStruct*** ,
    char***
);

extern char *XBaseFontNameListOfFontSet(
    XFontSet
);

extern char *XLocaleOfFontSet(
    XFontSet
);

extern int XContextDependentDrawing(
    XFontSet
);

extern int XDirectionalDependentDrawing(
    XFontSet
);

extern int XContextualDrawing(
    XFontSet
);

extern XFontSetExtents *XExtentsOfFontSet(
    XFontSet
);

extern int XmbTextEscapement(
    XFontSet ,
    const char* ,
    int
);

extern int XwcTextEscapement(
    XFontSet ,
    const wchar_t* ,
    int
);

extern int Xutf8TextEscapement(
    XFontSet ,
    const char* ,
    int
);

extern int XmbTextExtents(
    XFontSet ,
    const char* ,
    int ,
    XRectangle* ,
    XRectangle*
);

extern int XwcTextExtents(
    XFontSet ,
    const wchar_t* ,
    int ,
    XRectangle* ,
    XRectangle*
);

extern int Xutf8TextExtents(
    XFontSet ,
    const char* ,
    int ,
    XRectangle* ,
    XRectangle*
);

extern int XmbTextPerCharExtents(
    XFontSet ,
    const char* ,
    int ,
    XRectangle* ,
    XRectangle* ,
    int ,
    int* ,
    XRectangle* ,
    XRectangle*
);

extern int XwcTextPerCharExtents(
    XFontSet ,
    const wchar_t* ,
    int ,
    XRectangle* ,
    XRectangle* ,
    int ,
    int* ,
    XRectangle* ,
    XRectangle*
);

extern int Xutf8TextPerCharExtents(
    XFontSet ,
    const char* ,
    int ,
    XRectangle* ,
    XRectangle* ,
    int ,
    int* ,
    XRectangle* ,
    XRectangle*
);

extern void XmbDrawText(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    XmbTextItem* ,
    int
);

extern void XwcDrawText(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    XwcTextItem* ,
    int
);

extern void Xutf8DrawText(
    Display* ,
    Drawable ,
    GC ,
    int ,
    int ,
    XmbTextItem* ,
    int
);

extern void XmbDrawString(
    Display* ,
    Drawable ,
    XFontSet ,
    GC ,
    int ,
    int ,
    const char* ,
    int
);

extern void XwcDrawString(
    Display* ,
    Drawable ,
    XFontSet ,
    GC ,
    int ,
    int ,
    const wchar_t* ,
    int
);

extern void Xutf8DrawString(
    Display* ,
    Drawable ,
    XFontSet ,
    GC ,
    int ,
    int ,
    const char* ,
    int
);

extern void XmbDrawImageString(
    Display* ,
    Drawable ,
    XFontSet ,
    GC ,
    int ,
    int ,
    const char* ,
    int
);

extern void XwcDrawImageString(
    Display* ,
    Drawable ,
    XFontSet ,
    GC ,
    int ,
    int ,
    const wchar_t* ,
    int
);

extern void Xutf8DrawImageString(
    Display* ,
    Drawable ,
    XFontSet ,
    GC ,
    int ,
    int ,
    const char* ,
    int
);

extern XIM XOpenIM(
    Display* ,
    struct _XrmHashBucketRec* ,
    char* ,
    char*
);

extern int XCloseIM(
    XIM
);

extern char *XGetIMValues(
    XIM , ...
) __attribute__ ((__sentinel__(0)));

extern char *XSetIMValues(
    XIM , ...
) __attribute__ ((__sentinel__(0)));

extern Display *XDisplayOfIM(
    XIM
);

extern char *XLocaleOfIM(
    XIM
);

extern XIC XCreateIC(
    XIM , ...
) __attribute__ ((__sentinel__(0)));

extern void XDestroyIC(
    XIC
);

extern void XSetICFocus(
    XIC
);

extern void XUnsetICFocus(
    XIC
);

extern wchar_t *XwcResetIC(
    XIC
);

extern char *XmbResetIC(
    XIC
);

extern char *Xutf8ResetIC(
    XIC
);

extern char *XSetICValues(
    XIC , ...
) __attribute__ ((__sentinel__(0)));

extern char *XGetICValues(
    XIC , ...
) __attribute__ ((__sentinel__(0)));

extern XIM XIMOfIC(
    XIC
);

extern int XFilterEvent(
    XEvent* ,
    Window
);

extern int XmbLookupString(
    XIC ,
    XKeyPressedEvent* ,
    char* ,
    int ,
    KeySym* ,
    int*
);

extern int XwcLookupString(
    XIC ,
    XKeyPressedEvent* ,
    wchar_t* ,
    int ,
    KeySym* ,
    int*
);

extern int Xutf8LookupString(
    XIC ,
    XKeyPressedEvent* ,
    char* ,
    int ,
    KeySym* ,
    int*
);

extern XVaNestedList XVaCreateNestedList(
    int , ...
) __attribute__ ((__sentinel__(0)));



extern int XRegisterIMInstantiateCallback(
    Display* ,
    struct _XrmHashBucketRec* ,
    char* ,
    char* ,
    XIDProc ,
    XPointer
);

extern int XUnregisterIMInstantiateCallback(
    Display* ,
    struct _XrmHashBucketRec* ,
    char* ,
    char* ,
    XIDProc ,
    XPointer
);

typedef void (*XConnectionWatchProc)(
    Display* ,
    XPointer ,
    int ,
    int ,
    XPointer*
);


extern int XInternalConnectionNumbers(
    Display* ,
    int** ,
    int*
);

extern void XProcessInternalConnection(
    Display* ,
    int
);

extern int XAddConnectionWatch(
    Display* ,
    XConnectionWatchProc ,
    XPointer
);

extern void XRemoveConnectionWatch(
    Display* ,
    XConnectionWatchProc ,
    XPointer
);

extern void XSetAuthorization(
    char * ,
    int ,
    char * ,
    int
);

extern int _Xmbtowc(
    wchar_t * ,




    char * ,
    int

);

extern int _Xwctomb(
    char * ,
    wchar_t
);

extern int XGetEventData(
    Display* ,
    XGenericEventCookie*
);

extern void XFreeEventData(
    Display* ,
    XGenericEventCookie*
);


# 79 "/usr/include/tk.h" 2 3 4



# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stddef.h" 1 3 4
# 83 "/usr/include/tk.h" 2 3 4
# 102 "/usr/include/tk.h" 3 4
typedef struct Tk_BindingTable_ *Tk_BindingTable;
typedef struct Tk_Canvas_ *Tk_Canvas;
typedef struct Tk_Cursor_ *Tk_Cursor;
typedef struct Tk_ErrorHandler_ *Tk_ErrorHandler;
typedef struct Tk_Font_ *Tk_Font;
typedef struct Tk_Image__ *Tk_Image;
typedef struct Tk_ImageMaster_ *Tk_ImageMaster;
typedef struct Tk_OptionTable_ *Tk_OptionTable;
typedef struct Tk_PostscriptInfo_ *Tk_PostscriptInfo;
typedef struct Tk_TextLayout_ *Tk_TextLayout;
typedef struct Tk_Window_ *Tk_Window;
typedef struct Tk_3DBorder_ *Tk_3DBorder;
typedef struct Tk_Style_ *Tk_Style;
typedef struct Tk_StyleEngine_ *Tk_StyleEngine;
typedef struct Tk_StyledElement_ *Tk_StyledElement;





typedef const char *Tk_Uid;






typedef enum {
    TK_OPTION_BOOLEAN,
    TK_OPTION_INT,
    TK_OPTION_DOUBLE,
    TK_OPTION_STRING,
    TK_OPTION_STRING_TABLE,
    TK_OPTION_COLOR,
    TK_OPTION_FONT,
    TK_OPTION_BITMAP,
    TK_OPTION_BORDER,
    TK_OPTION_RELIEF,
    TK_OPTION_CURSOR,
    TK_OPTION_JUSTIFY,
    TK_OPTION_ANCHOR,
    TK_OPTION_SYNONYM,
    TK_OPTION_PIXELS,
    TK_OPTION_WINDOW,
    TK_OPTION_END,
    TK_OPTION_CUSTOM,
    TK_OPTION_STYLE
} Tk_OptionType;
# 158 "/usr/include/tk.h" 3 4
typedef struct Tk_OptionSpec {
    Tk_OptionType type;


    const char *optionName;

    const char *dbName;
    const char *dbClass;
    const char *defValue;


    int objOffset;





    int internalOffset;







    int flags;

    ClientData clientData;


    int typeMask;






} Tk_OptionSpec;
# 211 "/usr/include/tk.h" 3 4
typedef int (Tk_CustomOptionSetProc) (ClientData clientData, Tcl_Interp *interp, Tk_Window tkwin, Tcl_Obj **value, char *widgRec, int offset, char *saveInternalPtr, int flags);


typedef Tcl_Obj *(Tk_CustomOptionGetProc) (ClientData clientData, Tk_Window tkwin, char *widgRec, int offset);

typedef void (Tk_CustomOptionRestoreProc) (ClientData clientData, Tk_Window tkwin, char *internalPtr, char *saveInternalPtr);

typedef void (Tk_CustomOptionFreeProc) (ClientData clientData, Tk_Window tkwin, char *internalPtr);


typedef struct Tk_ObjCustomOption {
    const char *name;
    Tk_CustomOptionSetProc *setProc;


    Tk_CustomOptionGetProc *getProc;



    Tk_CustomOptionRestoreProc *restoreProc;


    Tk_CustomOptionFreeProc *freeProc;


    ClientData clientData;

} Tk_ObjCustomOption;
# 260 "/usr/include/tk.h" 3 4
typedef struct Tk_SavedOption {
    struct TkOption *optionPtr;

    Tcl_Obj *valuePtr;


    double internalForm;
# 276 "/usr/include/tk.h" 3 4
} Tk_SavedOption;







typedef struct Tk_SavedOptions {
    char *recordPtr;

    Tk_Window tkwin;

    int numItems;
    Tk_SavedOption items[20];

    struct Tk_SavedOptions *nextPtr;




} Tk_SavedOptions;
# 313 "/usr/include/tk.h" 3 4
typedef int (Tk_OptionParseProc) (ClientData clientData, Tcl_Interp *interp, Tk_Window tkwin, char *value, char *widgRec, int offset);


typedef char *(Tk_OptionPrintProc) (ClientData clientData, Tk_Window tkwin, char *widgRec, int offset, Tcl_FreeProc **freeProcPtr);



typedef struct Tk_CustomOption {
    Tk_OptionParseProc *parseProc;


    Tk_OptionPrintProc *printProc;


    ClientData clientData;


} Tk_CustomOption;
# 339 "/usr/include/tk.h" 3 4
typedef struct Tk_ConfigSpec {
    int type;


    char *argvName;

    Tk_Uid dbName;
    Tk_Uid dbClass;
    Tk_Uid defValue;

    int offset;


    int specFlags;


    Tk_CustomOption *customPtr;



} Tk_ConfigSpec;






typedef enum {
    TK_CONFIG_BOOLEAN, TK_CONFIG_INT, TK_CONFIG_DOUBLE, TK_CONFIG_STRING,
    TK_CONFIG_UID, TK_CONFIG_COLOR, TK_CONFIG_FONT, TK_CONFIG_BITMAP,
    TK_CONFIG_BORDER, TK_CONFIG_RELIEF, TK_CONFIG_CURSOR,
    TK_CONFIG_ACTIVE_CURSOR, TK_CONFIG_JUSTIFY, TK_CONFIG_ANCHOR,
    TK_CONFIG_SYNONYM, TK_CONFIG_CAP_STYLE, TK_CONFIG_JOIN_STYLE,
    TK_CONFIG_PIXELS, TK_CONFIG_MM, TK_CONFIG_WINDOW, TK_CONFIG_CUSTOM,
    TK_CONFIG_END
} Tk_ConfigTypes;
# 402 "/usr/include/tk.h" 3 4
typedef struct {
    char *key;

    int type;
    char *src;

    char *dst;

    char *help;

} Tk_ArgvInfo;
# 447 "/usr/include/tk.h" 3 4
typedef enum {
    TK_DEFER_EVENT, TK_PROCESS_EVENT, TK_DISCARD_EVENT
} Tk_RestrictAction;
# 494 "/usr/include/tk.h" 3 4
typedef enum {
    TK_ANCHOR_N, TK_ANCHOR_NE, TK_ANCHOR_E, TK_ANCHOR_SE,
    TK_ANCHOR_S, TK_ANCHOR_SW, TK_ANCHOR_W, TK_ANCHOR_NW,
    TK_ANCHOR_CENTER
} Tk_Anchor;





typedef enum {
    TK_JUSTIFY_LEFT, TK_JUSTIFY_RIGHT, TK_JUSTIFY_CENTER
} Tk_Justify;






typedef struct Tk_FontMetrics {
    int ascent;



    int descent;



    int linespace;




} Tk_FontMetrics;
# 549 "/usr/include/tk.h" 3 4
typedef Window (Tk_ClassCreateProc) (Tk_Window tkwin, Window parent, ClientData instanceData);

typedef void (Tk_ClassWorldChangedProc) (ClientData instanceData);
typedef void (Tk_ClassModalProc) (Tk_Window tkwin, XEvent *eventPtr);


typedef struct Tk_ClassProcs {
    unsigned int size;
    Tk_ClassWorldChangedProc *worldChangedProc;



    Tk_ClassCreateProc *createProc;


    Tk_ClassModalProc *modalProc;



} Tk_ClassProcs;
# 594 "/usr/include/tk.h" 3 4
typedef void (Tk_GeomRequestProc) (ClientData clientData, Tk_Window tkwin);

typedef void (Tk_GeomLostSlaveProc) (ClientData clientData, Tk_Window tkwin);


typedef struct Tk_GeomMgr {
    const char *name;


    Tk_GeomRequestProc *requestProc;


    Tk_GeomLostSlaveProc *lostSlaveProc;




} Tk_GeomMgr;
# 652 "/usr/include/tk.h" 3 4
typedef struct {
    int type;
    unsigned long serial;
    int send_event;

    Display *display;
    Window event;
    Window root;
    Window subwindow;
    Time time;
    int x, y;

    int x_root, y_root;
    unsigned int state;
    Tk_Uid name;
    int same_screen;
    Tcl_Obj *user_data;



} XVirtualEvent;

typedef struct {
    int type;
    unsigned long serial;
    int send_event;

    Display *display;
    Window window;
} XActivateDeactivateEvent;
typedef XActivateDeactivateEvent XActivateEvent;
typedef XActivateDeactivateEvent XDeactivateEvent;
# 755 "/usr/include/tk.h" 3 4
typedef struct Tk_FakeWin {
    Display *display;
    char *dummy1;
    int screenNum;
    Visual *visual;
    int depth;
    Window window;
    char *dummy2;
    char *dummy3;
    Tk_Window parentPtr;
    char *dummy4;
    char *dummy5;
    char *pathName;
    Tk_Uid nameUid;
    Tk_Uid classUid;
    XWindowChanges changes;
    unsigned int dummy6;
    XSetWindowAttributes atts;
    unsigned long dummy7;
    unsigned int flags;
    char *dummy8;

    XIC dummy9;

    ClientData *dummy10;
    int dummy11;
    int dummy12;
    char *dummy13;
    char *dummy14;
    ClientData dummy15;
    int reqWidth, reqHeight;
    int internalBorderLeft;
    char *dummy16;
    char *dummy17;
    ClientData dummy18;
    char *dummy19;
    int internalBorderRight;
    int internalBorderTop;
    int internalBorderBottom;
    int minReqWidth;
    int minReqHeight;
} Tk_FakeWin;
# 895 "/usr/include/tk.h" 3 4
typedef enum {
    TK_STATE_NULL = -1, TK_STATE_ACTIVE, TK_STATE_DISABLED,
    TK_STATE_NORMAL, TK_STATE_HIDDEN
} Tk_State;

typedef struct Tk_SmoothMethod {
    char *name;
    int (*coordProc) (Tk_Canvas canvas, double *pointPtr, int numPoints, int numSteps, XPoint xPoints[], double dblPoints[]);


    void (*postscriptProc) (Tcl_Interp *interp, Tk_Canvas canvas, double *coordPtr, int numPoints, int numSteps);


} Tk_SmoothMethod;
# 918 "/usr/include/tk.h" 3 4
typedef struct Tk_Item {
    int id;

    struct Tk_Item *nextPtr;


    Tk_Uid staticTagSpace[3];

    Tk_Uid *tagPtr;


    int tagSpace;

    int numTags;

    struct Tk_ItemType *typePtr;

    int x1, y1, x2, y2;




    struct Tk_Item *prevPtr;


    Tk_State state;
    char *reserved1;
    int redraw_flags;
# 955 "/usr/include/tk.h" 3 4
} Tk_Item;
# 986 "/usr/include/tk.h" 3 4
typedef int Tk_ItemCreateProc (Tcl_Interp *interp, Tk_Canvas canvas, Tk_Item *itemPtr, int argc, Tcl_Obj *const objv[]);


typedef int Tk_ItemConfigureProc (Tcl_Interp *interp, Tk_Canvas canvas, Tk_Item *itemPtr, int argc, Tcl_Obj *const objv[], int flags);


typedef int Tk_ItemCoordProc (Tcl_Interp *interp, Tk_Canvas canvas, Tk_Item *itemPtr, int argc, Tcl_Obj *const argv[]);



typedef void Tk_ItemDeleteProc (Tk_Canvas canvas, Tk_Item *itemPtr, Display *display);

typedef void Tk_ItemDisplayProc (Tk_Canvas canvas, Tk_Item *itemPtr, Display *display, Drawable dst, int x, int y, int width, int height);


typedef double Tk_ItemPointProc (Tk_Canvas canvas, Tk_Item *itemPtr, double *pointPtr);

typedef int Tk_ItemAreaProc (Tk_Canvas canvas, Tk_Item *itemPtr, double *rectPtr);

typedef int Tk_ItemPostscriptProc (Tcl_Interp *interp, Tk_Canvas canvas, Tk_Item *itemPtr, int prepass);

typedef void Tk_ItemScaleProc (Tk_Canvas canvas, Tk_Item *itemPtr, double originX, double originY, double scaleX, double scaleY);


typedef void Tk_ItemTranslateProc (Tk_Canvas canvas, Tk_Item *itemPtr, double deltaX, double deltaY);

typedef int Tk_ItemIndexProc (Tcl_Interp *interp, Tk_Canvas canvas, Tk_Item *itemPtr, char *indexString, int *indexPtr);


typedef void Tk_ItemCursorProc (Tk_Canvas canvas, Tk_Item *itemPtr, int index);

typedef int Tk_ItemSelectionProc (Tk_Canvas canvas, Tk_Item *itemPtr, int offset, char *buffer, int maxBytes);


typedef void Tk_ItemInsertProc (Tk_Canvas canvas, Tk_Item *itemPtr, int beforeThis, char *string);

typedef void Tk_ItemDCharsProc (Tk_Canvas canvas, Tk_Item *itemPtr, int first, int last);




typedef struct Tk_ItemType {
    char *name;

    int itemSize;

    Tk_ItemCreateProc *createProc;


    Tk_ConfigSpec *configSpecs;


    Tk_ItemConfigureProc *configProc;


    Tk_ItemCoordProc *coordProc;

    Tk_ItemDeleteProc *deleteProc;


    Tk_ItemDisplayProc *displayProc;

    int alwaysRedraw;


    Tk_ItemPointProc *pointProc;

    Tk_ItemAreaProc *areaProc;

    Tk_ItemPostscriptProc *postscriptProc;


    Tk_ItemScaleProc *scaleProc;
    Tk_ItemTranslateProc *translateProc;


    Tk_ItemIndexProc *indexProc;


    Tk_ItemCursorProc *icursorProc;


    Tk_ItemSelectionProc *selectionProc;


    Tk_ItemInsertProc *insertProc;


    Tk_ItemDCharsProc *dCharsProc;


    struct Tk_ItemType *nextPtr;
    char *reserved1;
    int reserved2;
    char *reserved3;
    char *reserved4;
} Tk_ItemType;
# 1094 "/usr/include/tk.h" 3 4
typedef struct Tk_CanvasTextInfo {
    Tk_3DBorder selBorder;

    int selBorderWidth;

    XColor *selFgColorPtr;

    Tk_Item *selItemPtr;


    int selectFirst;

    int selectLast;

    Tk_Item *anchorItemPtr;


    int selectAnchor;



    Tk_3DBorder insertBorder;

    int insertWidth;

    int insertBorderWidth;

    Tk_Item *focusItemPtr;

    int gotFocus;

    int cursorOn;


} Tk_CanvasTextInfo;





typedef struct Tk_Dash {
    int number;
    union {
 char *pt;
 char array[sizeof(char *)];
    } pattern;
} Tk_Dash;

typedef struct Tk_TSOffset {
    int flags;
    int xoffset;
    int yoffset;
} Tk_TSOffset;
# 1161 "/usr/include/tk.h" 3 4
typedef struct Tk_Outline {
    GC gc;
    double width;
    double activeWidth;
    double disabledWidth;
    int offset;
    Tk_Dash dash;
    Tk_Dash activeDash;
    Tk_Dash disabledDash;
    void *reserved1;
    void *reserved2;
    void *reserved3;
    Tk_TSOffset tsoffset;
    XColor *color;
    XColor *activeColor;
    XColor *disabledColor;
    Pixmap stipple;
    Pixmap activeStipple;

    Pixmap disabledStipple;

} Tk_Outline;
# 1192 "/usr/include/tk.h" 3 4
typedef struct Tk_ImageType Tk_ImageType;





typedef int (Tk_ImageCreateProc) (Tcl_Interp *interp, char *name, int objc, Tcl_Obj *const objv[], Tk_ImageType *typePtr, Tk_ImageMaster master, ClientData *masterDataPtr);



typedef ClientData (Tk_ImageGetProc) (Tk_Window tkwin, ClientData masterData);

typedef void (Tk_ImageDisplayProc) (ClientData instanceData, Display *display, Drawable drawable, int imageX, int imageY, int width, int height, int drawableX, int drawableY);


typedef void (Tk_ImageFreeProc) (ClientData instanceData, Display *display);

typedef void (Tk_ImageDeleteProc) (ClientData masterData);
typedef void (Tk_ImageChangedProc) (ClientData clientData, int x, int y, int width, int height, int imageWidth, int imageHeight);


typedef int (Tk_ImagePostscriptProc) (ClientData clientData, Tcl_Interp *interp, Tk_Window tkwin, Tk_PostscriptInfo psinfo, int x, int y, int width, int height, int prepass);
# 1225 "/usr/include/tk.h" 3 4
struct Tk_ImageType {
    char *name;
    Tk_ImageCreateProc *createProc;


    Tk_ImageGetProc *getProc;


    Tk_ImageDisplayProc *displayProc;


    Tk_ImageFreeProc *freeProc;


    Tk_ImageDeleteProc *deleteProc;



    Tk_ImagePostscriptProc *postscriptProc;


    struct Tk_ImageType *nextPtr;



    char *reserved;
};
# 1266 "/usr/include/tk.h" 3 4
typedef void *Tk_PhotoHandle;





typedef struct Tk_PhotoImageBlock {
    unsigned char *pixelPtr;
    int width;
    int height;
    int pitch;

    int pixelSize;

    int offset[4];


} Tk_PhotoImageBlock;
# 1298 "/usr/include/tk.h" 3 4
typedef struct Tk_PhotoImageFormat Tk_PhotoImageFormat;
# 1317 "/usr/include/tk.h" 3 4
typedef int (Tk_ImageFileMatchProc) (Tcl_Channel chan, const char *fileName, Tcl_Obj *format, int *widthPtr, int *heightPtr, Tcl_Interp *interp);


typedef int (Tk_ImageStringMatchProc) (Tcl_Obj *dataObj, Tcl_Obj *format, int *widthPtr, int *heightPtr, Tcl_Interp *interp);


typedef int (Tk_ImageFileReadProc) (Tcl_Interp *interp, Tcl_Channel chan, const char *fileName, Tcl_Obj *format, Tk_PhotoHandle imageHandle, int destX, int destY, int width, int height, int srcX, int srcY);



typedef int (Tk_ImageStringReadProc) (Tcl_Interp *interp, Tcl_Obj *dataObj, Tcl_Obj *format, Tk_PhotoHandle imageHandle, int destX, int destY, int width, int height, int srcX, int srcY);


typedef int (Tk_ImageFileWriteProc) (Tcl_Interp *interp, const char *fileName, Tcl_Obj *format, Tk_PhotoImageBlock *blockPtr);

typedef int (Tk_ImageStringWriteProc) (Tcl_Interp *interp, Tcl_Obj *format, Tk_PhotoImageBlock *blockPtr);
# 1342 "/usr/include/tk.h" 3 4
struct Tk_PhotoImageFormat {
    char *name;
    Tk_ImageFileMatchProc *fileMatchProc;


    Tk_ImageStringMatchProc *stringMatchProc;


    Tk_ImageFileReadProc *fileReadProc;


    Tk_ImageStringReadProc *stringReadProc;


    Tk_ImageFileWriteProc *fileWriteProc;


    Tk_ImageStringWriteProc *stringWriteProc;



    struct Tk_PhotoImageFormat *nextPtr;



};
# 1394 "/usr/include/tk.h" 3 4
typedef void (Tk_GetElementSizeProc) (ClientData clientData, char *recordPtr, const Tk_OptionSpec **optionsPtr, Tk_Window tkwin, int width, int height, int inner, int *widthPtr, int *heightPtr);


typedef void (Tk_GetElementBoxProc) (ClientData clientData, char *recordPtr, const Tk_OptionSpec **optionsPtr, Tk_Window tkwin, int x, int y, int width, int height, int inner, int *xPtr, int *yPtr, int *widthPtr, int *heightPtr);



typedef int (Tk_GetElementBorderWidthProc) (ClientData clientData, char *recordPtr, const Tk_OptionSpec **optionsPtr, Tk_Window tkwin);

typedef void (Tk_DrawElementProc) (ClientData clientData, char *recordPtr, const Tk_OptionSpec **optionsPtr, Tk_Window tkwin, Drawable d, int x, int y, int width, int height, int state);



typedef struct Tk_ElementOptionSpec {
    char *name;
    Tk_OptionType type;

} Tk_ElementOptionSpec;

typedef struct Tk_ElementSpec {
    int version;
    char *name;
    Tk_ElementOptionSpec *options;


    Tk_GetElementSizeProc *getSize;



    Tk_GetElementBoxProc *getBox;


    Tk_GetElementBorderWidthProc *getBorderWidth;


    Tk_DrawElementProc *draw;

} Tk_ElementSpec;
# 1490 "/usr/include/tk.h" 3 4
const char * Tk_InitStubs (Tcl_Interp *interp, const char *version, int exact);

extern const char * Tk_PkgInitStubsCheck (Tcl_Interp *interp, const char *version, int exact);
# 1513 "/usr/include/tk.h" 3 4
typedef int (Tk_ErrorProc) (ClientData clientData, XErrorEvent *errEventPtr);

typedef void (Tk_EventProc) (ClientData clientData, XEvent *eventPtr);

typedef int (Tk_GenericProc) (ClientData clientData, XEvent *eventPtr);

typedef int (Tk_ClientMessageProc) (Tk_Window tkwin, XEvent *eventPtr);

typedef int (Tk_GetSelProc) (ClientData clientData, Tcl_Interp *interp, char *portion);

typedef void (Tk_LostSelProc) (ClientData clientData);
typedef Tk_RestrictAction (Tk_RestrictProc) ( ClientData clientData, XEvent *eventPtr);

typedef int (Tk_SelectionProc) (ClientData clientData, int offset, char *buffer, int maxBytes);
# 1537 "/usr/include/tk.h" 3 4
# 1 "/usr/include/tkDecls.h" 1 3 4
# 37 "/usr/include/tkDecls.h" 3 4
extern void Tk_MainLoop(void);




extern XColor * Tk_3DBorderColor(Tk_3DBorder border);




extern GC Tk_3DBorderGC(Tk_Window tkwin, Tk_3DBorder border,
    int which);




extern void Tk_3DHorizontalBevel(Tk_Window tkwin,
    Drawable drawable, Tk_3DBorder border, int x,
    int y, int width, int height, int leftIn,
    int rightIn, int topBevel, int relief);




extern void Tk_3DVerticalBevel(Tk_Window tkwin,
    Drawable drawable, Tk_3DBorder border, int x,
    int y, int width, int height, int leftBevel,
    int relief);




extern void Tk_AddOption(Tk_Window tkwin, const char *name,
    const char *value, int priority);




extern void Tk_BindEvent(Tk_BindingTable bindingTable,
    XEvent *eventPtr, Tk_Window tkwin,
    int numObjects, ClientData *objectPtr);




extern void Tk_CanvasDrawableCoords(Tk_Canvas canvas, double x,
    double y, short *drawableXPtr,
    short *drawableYPtr);




extern void Tk_CanvasEventuallyRedraw(Tk_Canvas canvas, int x1,
    int y1, int x2, int y2);




extern int Tk_CanvasGetCoord(Tcl_Interp *interp,
    Tk_Canvas canvas, const char *str,
    double *doublePtr);




extern Tk_CanvasTextInfo * Tk_CanvasGetTextInfo(Tk_Canvas canvas);




extern int Tk_CanvasPsBitmap(Tcl_Interp *interp,
    Tk_Canvas canvas, Pixmap bitmap, int x,
    int y, int width, int height);




extern int Tk_CanvasPsColor(Tcl_Interp *interp,
    Tk_Canvas canvas, XColor *colorPtr);




extern int Tk_CanvasPsFont(Tcl_Interp *interp, Tk_Canvas canvas,
    Tk_Font font);




extern void Tk_CanvasPsPath(Tcl_Interp *interp, Tk_Canvas canvas,
    double *coordPtr, int numPoints);




extern int Tk_CanvasPsStipple(Tcl_Interp *interp,
    Tk_Canvas canvas, Pixmap bitmap);




extern double Tk_CanvasPsY(Tk_Canvas canvas, double y);




extern void Tk_CanvasSetStippleOrigin(Tk_Canvas canvas, GC gc);




extern int Tk_CanvasTagsParseProc(ClientData clientData,
    Tcl_Interp *interp, Tk_Window tkwin,
    const char *value, char *widgRec, int offset);




extern char * Tk_CanvasTagsPrintProc(ClientData clientData,
    Tk_Window tkwin, char *widgRec, int offset,
    Tcl_FreeProc **freeProcPtr);




extern Tk_Window Tk_CanvasTkwin(Tk_Canvas canvas);




extern void Tk_CanvasWindowCoords(Tk_Canvas canvas, double x,
    double y, short *screenXPtr,
    short *screenYPtr);




extern void Tk_ChangeWindowAttributes(Tk_Window tkwin,
    unsigned long valueMask,
    XSetWindowAttributes *attsPtr);




extern int Tk_CharBbox(Tk_TextLayout layout, int index,
    int *xPtr, int *yPtr, int *widthPtr,
    int *heightPtr);




extern void Tk_ClearSelection(Tk_Window tkwin, Atom selection);




extern int Tk_ClipboardAppend(Tcl_Interp *interp,
    Tk_Window tkwin, Atom target, Atom format,
    char *buffer);




extern int Tk_ClipboardClear(Tcl_Interp *interp,
    Tk_Window tkwin);




extern int Tk_ConfigureInfo(Tcl_Interp *interp, Tk_Window tkwin,
    Tk_ConfigSpec *specs, char *widgRec,
    const char *argvName, int flags);




extern int Tk_ConfigureValue(Tcl_Interp *interp,
    Tk_Window tkwin, Tk_ConfigSpec *specs,
    char *widgRec, const char *argvName,
    int flags);




extern int Tk_ConfigureWidget(Tcl_Interp *interp,
    Tk_Window tkwin, Tk_ConfigSpec *specs,
    int argc, char **argv, char *widgRec,
    int flags);




extern void Tk_ConfigureWindow(Tk_Window tkwin,
    unsigned int valueMask,
    XWindowChanges *valuePtr);




extern Tk_TextLayout Tk_ComputeTextLayout(Tk_Font font, const char *str,
    int numChars, int wrapLength,
    Tk_Justify justify, int flags, int *widthPtr,
    int *heightPtr);




extern Tk_Window Tk_CoordsToWindow(int rootX, int rootY,
    Tk_Window tkwin);




extern unsigned long Tk_CreateBinding(Tcl_Interp *interp,
    Tk_BindingTable bindingTable,
    ClientData object, const char *eventStr,
    const char *command, int append);




extern Tk_BindingTable Tk_CreateBindingTable(Tcl_Interp *interp);




extern Tk_ErrorHandler Tk_CreateErrorHandler(Display *display, int errNum,
    int request, int minorCode,
    Tk_ErrorProc *errorProc,
    ClientData clientData);




extern void Tk_CreateEventHandler(Tk_Window token,
    unsigned long mask, Tk_EventProc *proc,
    ClientData clientData);




extern void Tk_CreateGenericHandler(Tk_GenericProc *proc,
    ClientData clientData);




extern void Tk_CreateImageType(Tk_ImageType *typePtr);




extern void Tk_CreateItemType(Tk_ItemType *typePtr);




extern void Tk_CreatePhotoImageFormat(
    Tk_PhotoImageFormat *formatPtr);




extern void Tk_CreateSelHandler(Tk_Window tkwin, Atom selection,
    Atom target, Tk_SelectionProc *proc,
    ClientData clientData, Atom format);




extern Tk_Window Tk_CreateWindow(Tcl_Interp *interp, Tk_Window parent,
    const char *name, const char *screenName);




extern Tk_Window Tk_CreateWindowFromPath(Tcl_Interp *interp,
    Tk_Window tkwin, const char *pathName,
    const char *screenName);




extern int Tk_DefineBitmap(Tcl_Interp *interp, const char *name,
    const char *source, int width, int height);




extern void Tk_DefineCursor(Tk_Window window, Tk_Cursor cursor);




extern void Tk_DeleteAllBindings(Tk_BindingTable bindingTable,
    ClientData object);




extern int Tk_DeleteBinding(Tcl_Interp *interp,
    Tk_BindingTable bindingTable,
    ClientData object, const char *eventStr);




extern void Tk_DeleteBindingTable(Tk_BindingTable bindingTable);




extern void Tk_DeleteErrorHandler(Tk_ErrorHandler handler);




extern void Tk_DeleteEventHandler(Tk_Window token,
    unsigned long mask, Tk_EventProc *proc,
    ClientData clientData);




extern void Tk_DeleteGenericHandler(Tk_GenericProc *proc,
    ClientData clientData);




extern void Tk_DeleteImage(Tcl_Interp *interp, const char *name);




extern void Tk_DeleteSelHandler(Tk_Window tkwin, Atom selection,
    Atom target);




extern void Tk_DestroyWindow(Tk_Window tkwin);




extern const char * Tk_DisplayName(Tk_Window tkwin);




extern int Tk_DistanceToTextLayout(Tk_TextLayout layout, int x,
    int y);




extern void Tk_Draw3DPolygon(Tk_Window tkwin, Drawable drawable,
    Tk_3DBorder border, XPoint *pointPtr,
    int numPoints, int borderWidth,
    int leftRelief);




extern void Tk_Draw3DRectangle(Tk_Window tkwin,
    Drawable drawable, Tk_3DBorder border, int x,
    int y, int width, int height,
    int borderWidth, int relief);




extern void Tk_DrawChars(Display *display, Drawable drawable,
    GC gc, Tk_Font tkfont, const char *source,
    int numBytes, int x, int y);




extern void Tk_DrawFocusHighlight(Tk_Window tkwin, GC gc,
    int width, Drawable drawable);




extern void Tk_DrawTextLayout(Display *display,
    Drawable drawable, GC gc,
    Tk_TextLayout layout, int x, int y,
    int firstChar, int lastChar);




extern void Tk_Fill3DPolygon(Tk_Window tkwin, Drawable drawable,
    Tk_3DBorder border, XPoint *pointPtr,
    int numPoints, int borderWidth,
    int leftRelief);




extern void Tk_Fill3DRectangle(Tk_Window tkwin,
    Drawable drawable, Tk_3DBorder border, int x,
    int y, int width, int height,
    int borderWidth, int relief);




extern Tk_PhotoHandle Tk_FindPhoto(Tcl_Interp *interp,
    const char *imageName);




extern Font Tk_FontId(Tk_Font font);




extern void Tk_Free3DBorder(Tk_3DBorder border);




extern void Tk_FreeBitmap(Display *display, Pixmap bitmap);




extern void Tk_FreeColor(XColor *colorPtr);




extern void Tk_FreeColormap(Display *display, Colormap colormap);




extern void Tk_FreeCursor(Display *display, Tk_Cursor cursor);




extern void Tk_FreeFont(Tk_Font f);




extern void Tk_FreeGC(Display *display, GC gc);




extern void Tk_FreeImage(Tk_Image image);




extern void Tk_FreeOptions(Tk_ConfigSpec *specs, char *widgRec,
    Display *display, int needFlags);




extern void Tk_FreePixmap(Display *display, Pixmap pixmap);




extern void Tk_FreeTextLayout(Tk_TextLayout textLayout);




extern void Tk_FreeXId(Display *display, XID xid);




extern GC Tk_GCForColor(XColor *colorPtr, Drawable drawable);




extern void Tk_GeometryRequest(Tk_Window tkwin, int reqWidth,
    int reqHeight);




extern Tk_3DBorder Tk_Get3DBorder(Tcl_Interp *interp, Tk_Window tkwin,
    Tk_Uid colorName);




extern void Tk_GetAllBindings(Tcl_Interp *interp,
    Tk_BindingTable bindingTable,
    ClientData object);




extern int Tk_GetAnchor(Tcl_Interp *interp, const char *str,
    Tk_Anchor *anchorPtr);




extern const char * Tk_GetAtomName(Tk_Window tkwin, Atom atom);




extern const char * Tk_GetBinding(Tcl_Interp *interp,
    Tk_BindingTable bindingTable,
    ClientData object, const char *eventStr);




extern Pixmap Tk_GetBitmap(Tcl_Interp *interp, Tk_Window tkwin,
    const char *str);




extern Pixmap Tk_GetBitmapFromData(Tcl_Interp *interp,
    Tk_Window tkwin, const char *source,
    int width, int height);




extern int Tk_GetCapStyle(Tcl_Interp *interp, const char *str,
    int *capPtr);




extern XColor * Tk_GetColor(Tcl_Interp *interp, Tk_Window tkwin,
    Tk_Uid name);




extern XColor * Tk_GetColorByValue(Tk_Window tkwin, XColor *colorPtr);




extern Colormap Tk_GetColormap(Tcl_Interp *interp, Tk_Window tkwin,
    const char *str);




extern Tk_Cursor Tk_GetCursor(Tcl_Interp *interp, Tk_Window tkwin,
    Tk_Uid str);




extern Tk_Cursor Tk_GetCursorFromData(Tcl_Interp *interp,
    Tk_Window tkwin, const char *source,
    const char *mask, int width, int height,
    int xHot, int yHot, Tk_Uid fg, Tk_Uid bg);




extern Tk_Font Tk_GetFont(Tcl_Interp *interp, Tk_Window tkwin,
    const char *str);




extern Tk_Font Tk_GetFontFromObj(Tk_Window tkwin, Tcl_Obj *objPtr);




extern void Tk_GetFontMetrics(Tk_Font font,
    Tk_FontMetrics *fmPtr);




extern GC Tk_GetGC(Tk_Window tkwin, unsigned long valueMask,
    XGCValues *valuePtr);




extern Tk_Image Tk_GetImage(Tcl_Interp *interp, Tk_Window tkwin,
    const char *name,
    Tk_ImageChangedProc *changeProc,
    ClientData clientData);




extern ClientData Tk_GetImageMasterData(Tcl_Interp *interp,
    const char *name, Tk_ImageType **typePtrPtr);




extern Tk_ItemType * Tk_GetItemTypes(void);




extern int Tk_GetJoinStyle(Tcl_Interp *interp, const char *str,
    int *joinPtr);




extern int Tk_GetJustify(Tcl_Interp *interp, const char *str,
    Tk_Justify *justifyPtr);




extern int Tk_GetNumMainWindows(void);




extern Tk_Uid Tk_GetOption(Tk_Window tkwin, const char *name,
    const char *className);




extern int Tk_GetPixels(Tcl_Interp *interp, Tk_Window tkwin,
    const char *str, int *intPtr);




extern Pixmap Tk_GetPixmap(Display *display, Drawable d, int width,
    int height, int depth);




extern int Tk_GetRelief(Tcl_Interp *interp, const char *name,
    int *reliefPtr);




extern void Tk_GetRootCoords(Tk_Window tkwin, int *xPtr,
    int *yPtr);




extern int Tk_GetScrollInfo(Tcl_Interp *interp, int argc,
    char **argv, double *dblPtr,
    int *intPtr);




extern int Tk_GetScreenMM(Tcl_Interp *interp, Tk_Window tkwin,
    const char *str, double *doublePtr);




extern int Tk_GetSelection(Tcl_Interp *interp, Tk_Window tkwin,
    Atom selection, Atom target,
    Tk_GetSelProc *proc, ClientData clientData);




extern Tk_Uid Tk_GetUid(const char *str);




extern Visual * Tk_GetVisual(Tcl_Interp *interp, Tk_Window tkwin,
    const char *str, int *depthPtr,
    Colormap *colormapPtr);




extern void Tk_GetVRootGeometry(Tk_Window tkwin, int *xPtr,
    int *yPtr, int *widthPtr, int *heightPtr);




extern int Tk_Grab(Tcl_Interp *interp, Tk_Window tkwin,
    int grabGlobal);




extern void Tk_HandleEvent(XEvent *eventPtr);




extern Tk_Window Tk_IdToWindow(Display *display, Window window);




extern void Tk_ImageChanged(Tk_ImageMaster master, int x, int y,
    int width, int height, int imageWidth,
    int imageHeight);




extern int Tk_Init(Tcl_Interp *interp);




extern Atom Tk_InternAtom(Tk_Window tkwin, const char *name);




extern int Tk_IntersectTextLayout(Tk_TextLayout layout, int x,
    int y, int width, int height);




extern void Tk_MaintainGeometry(Tk_Window slave,
    Tk_Window master, int x, int y, int width,
    int height);




extern Tk_Window Tk_MainWindow(Tcl_Interp *interp);




extern void Tk_MakeWindowExist(Tk_Window tkwin);




extern void Tk_ManageGeometry(Tk_Window tkwin,
    const Tk_GeomMgr *mgrPtr,
    ClientData clientData);




extern void Tk_MapWindow(Tk_Window tkwin);




extern int Tk_MeasureChars(Tk_Font tkfont, const char *source,
    int numBytes, int maxPixels, int flags,
    int *lengthPtr);




extern void Tk_MoveResizeWindow(Tk_Window tkwin, int x, int y,
    int width, int height);




extern void Tk_MoveWindow(Tk_Window tkwin, int x, int y);




extern void Tk_MoveToplevelWindow(Tk_Window tkwin, int x, int y);




extern const char * Tk_NameOf3DBorder(Tk_3DBorder border);




extern const char * Tk_NameOfAnchor(Tk_Anchor anchor);




extern const char * Tk_NameOfBitmap(Display *display, Pixmap bitmap);




extern const char * Tk_NameOfCapStyle(int cap);




extern const char * Tk_NameOfColor(XColor *colorPtr);




extern const char * Tk_NameOfCursor(Display *display,
    Tk_Cursor cursor);




extern const char * Tk_NameOfFont(Tk_Font font);




extern const char * Tk_NameOfImage(Tk_ImageMaster imageMaster);




extern const char * Tk_NameOfJoinStyle(int join);




extern const char * Tk_NameOfJustify(Tk_Justify justify);




extern const char * Tk_NameOfRelief(int relief);




extern Tk_Window Tk_NameToWindow(Tcl_Interp *interp,
    const char *pathName, Tk_Window tkwin);




extern void Tk_OwnSelection(Tk_Window tkwin, Atom selection,
    Tk_LostSelProc *proc, ClientData clientData);




extern int Tk_ParseArgv(Tcl_Interp *interp, Tk_Window tkwin,
    int *argcPtr, char **argv,
    Tk_ArgvInfo *argTable, int flags);




extern void Tk_PhotoPutBlock_NoComposite(Tk_PhotoHandle handle,
    Tk_PhotoImageBlock *blockPtr, int x, int y,
    int width, int height);




extern void Tk_PhotoPutZoomedBlock_NoComposite(
    Tk_PhotoHandle handle,
    Tk_PhotoImageBlock *blockPtr, int x, int y,
    int width, int height, int zoomX, int zoomY,
    int subsampleX, int subsampleY);




extern int Tk_PhotoGetImage(Tk_PhotoHandle handle,
    Tk_PhotoImageBlock *blockPtr);




extern void Tk_PhotoBlank(Tk_PhotoHandle handle);




extern void Tk_PhotoExpand_Panic(Tk_PhotoHandle handle,
    int width, int height);




extern void Tk_PhotoGetSize(Tk_PhotoHandle handle, int *widthPtr,
    int *heightPtr);




extern void Tk_PhotoSetSize_Panic(Tk_PhotoHandle handle,
    int width, int height);




extern int Tk_PointToChar(Tk_TextLayout layout, int x, int y);




extern int Tk_PostscriptFontName(Tk_Font tkfont,
    Tcl_DString *dsPtr);




extern void Tk_PreserveColormap(Display *display,
    Colormap colormap);




extern void Tk_QueueWindowEvent(XEvent *eventPtr,
    Tcl_QueuePosition position);




extern void Tk_RedrawImage(Tk_Image image, int imageX,
    int imageY, int width, int height,
    Drawable drawable, int drawableX,
    int drawableY);




extern void Tk_ResizeWindow(Tk_Window tkwin, int width,
    int height);




extern int Tk_RestackWindow(Tk_Window tkwin, int aboveBelow,
    Tk_Window other);




extern Tk_RestrictProc * Tk_RestrictEvents(Tk_RestrictProc *proc,
    ClientData arg, ClientData *prevArgPtr);




extern int Tk_SafeInit(Tcl_Interp *interp);




extern const char * Tk_SetAppName(Tk_Window tkwin, const char *name);




extern void Tk_SetBackgroundFromBorder(Tk_Window tkwin,
    Tk_3DBorder border);




extern void Tk_SetClass(Tk_Window tkwin, const char *className);




extern void Tk_SetGrid(Tk_Window tkwin, int reqWidth,
    int reqHeight, int gridWidth, int gridHeight);




extern void Tk_SetInternalBorder(Tk_Window tkwin, int width);




extern void Tk_SetWindowBackground(Tk_Window tkwin,
    unsigned long pixel);




extern void Tk_SetWindowBackgroundPixmap(Tk_Window tkwin,
    Pixmap pixmap);




extern void Tk_SetWindowBorder(Tk_Window tkwin,
    unsigned long pixel);




extern void Tk_SetWindowBorderWidth(Tk_Window tkwin, int width);




extern void Tk_SetWindowBorderPixmap(Tk_Window tkwin,
    Pixmap pixmap);




extern void Tk_SetWindowColormap(Tk_Window tkwin,
    Colormap colormap);




extern int Tk_SetWindowVisual(Tk_Window tkwin, Visual *visual,
    int depth, Colormap colormap);




extern void Tk_SizeOfBitmap(Display *display, Pixmap bitmap,
    int *widthPtr, int *heightPtr);




extern void Tk_SizeOfImage(Tk_Image image, int *widthPtr,
    int *heightPtr);




extern int Tk_StrictMotif(Tk_Window tkwin);




extern void Tk_TextLayoutToPostscript(Tcl_Interp *interp,
    Tk_TextLayout layout);




extern int Tk_TextWidth(Tk_Font font, const char *str,
    int numBytes);




extern void Tk_UndefineCursor(Tk_Window window);




extern void Tk_UnderlineChars(Display *display,
    Drawable drawable, GC gc, Tk_Font tkfont,
    const char *source, int x, int y,
    int firstByte, int lastByte);




extern void Tk_UnderlineTextLayout(Display *display,
    Drawable drawable, GC gc,
    Tk_TextLayout layout, int x, int y,
    int underline);




extern void Tk_Ungrab(Tk_Window tkwin);




extern void Tk_UnmaintainGeometry(Tk_Window slave,
    Tk_Window master);




extern void Tk_UnmapWindow(Tk_Window tkwin);




extern void Tk_UnsetGrid(Tk_Window tkwin);




extern void Tk_UpdatePointer(Tk_Window tkwin, int x, int y,
    int state);




extern Pixmap Tk_AllocBitmapFromObj(Tcl_Interp *interp,
    Tk_Window tkwin, Tcl_Obj *objPtr);




extern Tk_3DBorder Tk_Alloc3DBorderFromObj(Tcl_Interp *interp,
    Tk_Window tkwin, Tcl_Obj *objPtr);




extern XColor * Tk_AllocColorFromObj(Tcl_Interp *interp,
    Tk_Window tkwin, Tcl_Obj *objPtr);




extern Tk_Cursor Tk_AllocCursorFromObj(Tcl_Interp *interp,
    Tk_Window tkwin, Tcl_Obj *objPtr);




extern Tk_Font Tk_AllocFontFromObj(Tcl_Interp *interp,
    Tk_Window tkwin, Tcl_Obj *objPtr);




extern Tk_OptionTable Tk_CreateOptionTable(Tcl_Interp *interp,
    const Tk_OptionSpec *templatePtr);




extern void Tk_DeleteOptionTable(Tk_OptionTable optionTable);




extern void Tk_Free3DBorderFromObj(Tk_Window tkwin,
    Tcl_Obj *objPtr);




extern void Tk_FreeBitmapFromObj(Tk_Window tkwin,
    Tcl_Obj *objPtr);




extern void Tk_FreeColorFromObj(Tk_Window tkwin, Tcl_Obj *objPtr);




extern void Tk_FreeConfigOptions(char *recordPtr,
    Tk_OptionTable optionToken, Tk_Window tkwin);




extern void Tk_FreeSavedOptions(Tk_SavedOptions *savePtr);




extern void Tk_FreeCursorFromObj(Tk_Window tkwin,
    Tcl_Obj *objPtr);




extern void Tk_FreeFontFromObj(Tk_Window tkwin, Tcl_Obj *objPtr);




extern Tk_3DBorder Tk_Get3DBorderFromObj(Tk_Window tkwin,
    Tcl_Obj *objPtr);




extern int Tk_GetAnchorFromObj(Tcl_Interp *interp,
    Tcl_Obj *objPtr, Tk_Anchor *anchorPtr);




extern Pixmap Tk_GetBitmapFromObj(Tk_Window tkwin, Tcl_Obj *objPtr);




extern XColor * Tk_GetColorFromObj(Tk_Window tkwin, Tcl_Obj *objPtr);




extern Tk_Cursor Tk_GetCursorFromObj(Tk_Window tkwin, Tcl_Obj *objPtr);




extern Tcl_Obj * Tk_GetOptionInfo(Tcl_Interp *interp, char *recordPtr,
    Tk_OptionTable optionTable, Tcl_Obj *namePtr,
    Tk_Window tkwin);




extern Tcl_Obj * Tk_GetOptionValue(Tcl_Interp *interp,
    char *recordPtr, Tk_OptionTable optionTable,
    Tcl_Obj *namePtr, Tk_Window tkwin);




extern int Tk_GetJustifyFromObj(Tcl_Interp *interp,
    Tcl_Obj *objPtr, Tk_Justify *justifyPtr);




extern int Tk_GetMMFromObj(Tcl_Interp *interp, Tk_Window tkwin,
    Tcl_Obj *objPtr, double *doublePtr);




extern int Tk_GetPixelsFromObj(Tcl_Interp *interp,
    Tk_Window tkwin, Tcl_Obj *objPtr,
    int *intPtr);




extern int Tk_GetReliefFromObj(Tcl_Interp *interp,
    Tcl_Obj *objPtr, int *resultPtr);




extern int Tk_GetScrollInfoObj(Tcl_Interp *interp, int objc,
    Tcl_Obj *const objv[], double *dblPtr,
    int *intPtr);




extern int Tk_InitOptions(Tcl_Interp *interp, char *recordPtr,
    Tk_OptionTable optionToken, Tk_Window tkwin);




extern void Tk_MainEx(int argc, char **argv,
    Tcl_AppInitProc *appInitProc,
    Tcl_Interp *interp);




extern void Tk_RestoreSavedOptions(Tk_SavedOptions *savePtr);




extern int Tk_SetOptions(Tcl_Interp *interp, char *recordPtr,
    Tk_OptionTable optionTable, int objc,
    Tcl_Obj *const objv[], Tk_Window tkwin,
    Tk_SavedOptions *savePtr, int *maskPtr);




extern void Tk_InitConsoleChannels(Tcl_Interp *interp);




extern int Tk_CreateConsoleWindow(Tcl_Interp *interp);




extern void Tk_CreateSmoothMethod(Tcl_Interp *interp,
    Tk_SmoothMethod *method);






extern int Tk_GetDash(Tcl_Interp *interp, const char *value,
    Tk_Dash *dash);




extern void Tk_CreateOutline(Tk_Outline *outline);




extern void Tk_DeleteOutline(Display *display,
    Tk_Outline *outline);




extern int Tk_ConfigOutlineGC(XGCValues *gcValues,
    Tk_Canvas canvas, Tk_Item *item,
    Tk_Outline *outline);




extern int Tk_ChangeOutlineGC(Tk_Canvas canvas, Tk_Item *item,
    Tk_Outline *outline);




extern int Tk_ResetOutlineGC(Tk_Canvas canvas, Tk_Item *item,
    Tk_Outline *outline);




extern int Tk_CanvasPsOutline(Tk_Canvas canvas, Tk_Item *item,
    Tk_Outline *outline);




extern void Tk_SetTSOrigin(Tk_Window tkwin, GC gc, int x, int y);




extern int Tk_CanvasGetCoordFromObj(Tcl_Interp *interp,
    Tk_Canvas canvas, Tcl_Obj *obj,
    double *doublePtr);




extern void Tk_CanvasSetOffset(Tk_Canvas canvas, GC gc,
    Tk_TSOffset *offset);




extern void Tk_DitherPhoto(Tk_PhotoHandle handle, int x, int y,
    int width, int height);




extern int Tk_PostscriptBitmap(Tcl_Interp *interp,
    Tk_Window tkwin, Tk_PostscriptInfo psInfo,
    Pixmap bitmap, int startX, int startY,
    int width, int height);




extern int Tk_PostscriptColor(Tcl_Interp *interp,
    Tk_PostscriptInfo psInfo, XColor *colorPtr);




extern int Tk_PostscriptFont(Tcl_Interp *interp,
    Tk_PostscriptInfo psInfo, Tk_Font font);




extern int Tk_PostscriptImage(Tk_Image image,
    Tcl_Interp *interp, Tk_Window tkwin,
    Tk_PostscriptInfo psinfo, int x, int y,
    int width, int height, int prepass);




extern void Tk_PostscriptPath(Tcl_Interp *interp,
    Tk_PostscriptInfo psInfo, double *coordPtr,
    int numPoints);




extern int Tk_PostscriptStipple(Tcl_Interp *interp,
    Tk_Window tkwin, Tk_PostscriptInfo psInfo,
    Pixmap bitmap);




extern double Tk_PostscriptY(double y, Tk_PostscriptInfo psInfo);




extern int Tk_PostscriptPhoto(Tcl_Interp *interp,
    Tk_PhotoImageBlock *blockPtr,
    Tk_PostscriptInfo psInfo, int width,
    int height);




extern void Tk_CreateClientMessageHandler(
    Tk_ClientMessageProc *proc);




extern void Tk_DeleteClientMessageHandler(
    Tk_ClientMessageProc *proc);




extern Tk_Window Tk_CreateAnonymousWindow(Tcl_Interp *interp,
    Tk_Window parent, const char *screenName);




extern void Tk_SetClassProcs(Tk_Window tkwin,
    Tk_ClassProcs *procs,
    ClientData instanceData);




extern void Tk_SetInternalBorderEx(Tk_Window tkwin, int left,
    int right, int top, int bottom);




extern void Tk_SetMinimumRequestSize(Tk_Window tkwin,
    int minWidth, int minHeight);




extern void Tk_SetCaretPos(Tk_Window tkwin, int x, int y,
    int height);




extern void Tk_PhotoPutBlock_Panic(Tk_PhotoHandle handle,
    Tk_PhotoImageBlock *blockPtr, int x, int y,
    int width, int height, int compRule);




extern void Tk_PhotoPutZoomedBlock_Panic(Tk_PhotoHandle handle,
    Tk_PhotoImageBlock *blockPtr, int x, int y,
    int width, int height, int zoomX, int zoomY,
    int subsampleX, int subsampleY, int compRule);




extern int Tk_CollapseMotionEvents(Display *display,
    int collapse);




extern Tk_StyleEngine Tk_RegisterStyleEngine(const char *name,
    Tk_StyleEngine parent);




extern Tk_StyleEngine Tk_GetStyleEngine(const char *name);




extern int Tk_RegisterStyledElement(Tk_StyleEngine engine,
    Tk_ElementSpec *templatePtr);




extern int Tk_GetElementId(const char *name);




extern Tk_Style Tk_CreateStyle(const char *name,
    Tk_StyleEngine engine, ClientData clientData);




extern Tk_Style Tk_GetStyle(Tcl_Interp *interp, const char *name);




extern void Tk_FreeStyle(Tk_Style style);




extern const char * Tk_NameOfStyle(Tk_Style style);




extern Tk_Style Tk_AllocStyleFromObj(Tcl_Interp *interp,
    Tcl_Obj *objPtr);




extern Tk_Style Tk_GetStyleFromObj(Tcl_Obj *objPtr);




extern void Tk_FreeStyleFromObj(Tcl_Obj *objPtr);




extern Tk_StyledElement Tk_GetStyledElement(Tk_Style style, int elementId,
    Tk_OptionTable optionTable);




extern void Tk_GetElementSize(Tk_Style style,
    Tk_StyledElement element, char *recordPtr,
    Tk_Window tkwin, int width, int height,
    int inner, int *widthPtr, int *heightPtr);




extern void Tk_GetElementBox(Tk_Style style,
    Tk_StyledElement element, char *recordPtr,
    Tk_Window tkwin, int x, int y, int width,
    int height, int inner, int *xPtr, int *yPtr,
    int *widthPtr, int *heightPtr);




extern int Tk_GetElementBorderWidth(Tk_Style style,
    Tk_StyledElement element, char *recordPtr,
    Tk_Window tkwin);




extern void Tk_DrawElement(Tk_Style style,
    Tk_StyledElement element, char *recordPtr,
    Tk_Window tkwin, Drawable d, int x, int y,
    int width, int height, int state);




extern int Tk_PhotoExpand(Tcl_Interp *interp,
    Tk_PhotoHandle handle, int width, int height);




extern int Tk_PhotoPutBlock(Tcl_Interp *interp,
    Tk_PhotoHandle handle,
    Tk_PhotoImageBlock *blockPtr, int x, int y,
    int width, int height, int compRule);




extern int Tk_PhotoPutZoomedBlock(Tcl_Interp *interp,
    Tk_PhotoHandle handle,
    Tk_PhotoImageBlock *blockPtr, int x, int y,
    int width, int height, int zoomX, int zoomY,
    int subsampleX, int subsampleY, int compRule);




extern int Tk_PhotoSetSize(Tcl_Interp *interp,
    Tk_PhotoHandle handle, int width, int height);




extern long Tk_GetUserInactiveTime(Display *dpy);




extern void Tk_ResetUserInactiveTime(Display *dpy);




extern Tcl_Interp * Tk_Interp(Tk_Window tkwin);




extern void Tk_CreateOldImageType(Tk_ImageType *typePtr);




extern void Tk_CreateOldPhotoImageFormat(
    Tk_PhotoImageFormat *formatPtr);


typedef struct TkStubHooks {
    struct TkPlatStubs *tkPlatStubs;
    struct TkIntStubs *tkIntStubs;
    struct TkIntPlatStubs *tkIntPlatStubs;
    struct TkIntXlibStubs *tkIntXlibStubs;
} TkStubHooks;

typedef struct TkStubs {
    int magic;
    struct TkStubHooks *hooks;

    void (*tk_MainLoop) (void);
    XColor * (*tk_3DBorderColor) (Tk_3DBorder border);
    GC (*tk_3DBorderGC) (Tk_Window tkwin, Tk_3DBorder border, int which);
    void (*tk_3DHorizontalBevel) (Tk_Window tkwin, Drawable drawable, Tk_3DBorder border, int x, int y, int width, int height, int leftIn, int rightIn, int topBevel, int relief);
    void (*tk_3DVerticalBevel) (Tk_Window tkwin, Drawable drawable, Tk_3DBorder border, int x, int y, int width, int height, int leftBevel, int relief);
    void (*tk_AddOption) (Tk_Window tkwin, const char *name, const char *value, int priority);
    void (*tk_BindEvent) (Tk_BindingTable bindingTable, XEvent *eventPtr, Tk_Window tkwin, int numObjects, ClientData *objectPtr);
    void (*tk_CanvasDrawableCoords) (Tk_Canvas canvas, double x, double y, short *drawableXPtr, short *drawableYPtr);
    void (*tk_CanvasEventuallyRedraw) (Tk_Canvas canvas, int x1, int y1, int x2, int y2);
    int (*tk_CanvasGetCoord) (Tcl_Interp *interp, Tk_Canvas canvas, const char *str, double *doublePtr);
    Tk_CanvasTextInfo * (*tk_CanvasGetTextInfo) (Tk_Canvas canvas);
    int (*tk_CanvasPsBitmap) (Tcl_Interp *interp, Tk_Canvas canvas, Pixmap bitmap, int x, int y, int width, int height);
    int (*tk_CanvasPsColor) (Tcl_Interp *interp, Tk_Canvas canvas, XColor *colorPtr);
    int (*tk_CanvasPsFont) (Tcl_Interp *interp, Tk_Canvas canvas, Tk_Font font);
    void (*tk_CanvasPsPath) (Tcl_Interp *interp, Tk_Canvas canvas, double *coordPtr, int numPoints);
    int (*tk_CanvasPsStipple) (Tcl_Interp *interp, Tk_Canvas canvas, Pixmap bitmap);
    double (*tk_CanvasPsY) (Tk_Canvas canvas, double y);
    void (*tk_CanvasSetStippleOrigin) (Tk_Canvas canvas, GC gc);
    int (*tk_CanvasTagsParseProc) (ClientData clientData, Tcl_Interp *interp, Tk_Window tkwin, const char *value, char *widgRec, int offset);
    char * (*tk_CanvasTagsPrintProc) (ClientData clientData, Tk_Window tkwin, char *widgRec, int offset, Tcl_FreeProc **freeProcPtr);
    Tk_Window (*tk_CanvasTkwin) (Tk_Canvas canvas);
    void (*tk_CanvasWindowCoords) (Tk_Canvas canvas, double x, double y, short *screenXPtr, short *screenYPtr);
    void (*tk_ChangeWindowAttributes) (Tk_Window tkwin, unsigned long valueMask, XSetWindowAttributes *attsPtr);
    int (*tk_CharBbox) (Tk_TextLayout layout, int index, int *xPtr, int *yPtr, int *widthPtr, int *heightPtr);
    void (*tk_ClearSelection) (Tk_Window tkwin, Atom selection);
    int (*tk_ClipboardAppend) (Tcl_Interp *interp, Tk_Window tkwin, Atom target, Atom format, char *buffer);
    int (*tk_ClipboardClear) (Tcl_Interp *interp, Tk_Window tkwin);
    int (*tk_ConfigureInfo) (Tcl_Interp *interp, Tk_Window tkwin, Tk_ConfigSpec *specs, char *widgRec, const char *argvName, int flags);
    int (*tk_ConfigureValue) (Tcl_Interp *interp, Tk_Window tkwin, Tk_ConfigSpec *specs, char *widgRec, const char *argvName, int flags);
    int (*tk_ConfigureWidget) (Tcl_Interp *interp, Tk_Window tkwin, Tk_ConfigSpec *specs, int argc, char **argv, char *widgRec, int flags);
    void (*tk_ConfigureWindow) (Tk_Window tkwin, unsigned int valueMask, XWindowChanges *valuePtr);
    Tk_TextLayout (*tk_ComputeTextLayout) (Tk_Font font, const char *str, int numChars, int wrapLength, Tk_Justify justify, int flags, int *widthPtr, int *heightPtr);
    Tk_Window (*tk_CoordsToWindow) (int rootX, int rootY, Tk_Window tkwin);
    unsigned long (*tk_CreateBinding) (Tcl_Interp *interp, Tk_BindingTable bindingTable, ClientData object, const char *eventStr, const char *command, int append);
    Tk_BindingTable (*tk_CreateBindingTable) (Tcl_Interp *interp);
    Tk_ErrorHandler (*tk_CreateErrorHandler) (Display *display, int errNum, int request, int minorCode, Tk_ErrorProc *errorProc, ClientData clientData);
    void (*tk_CreateEventHandler) (Tk_Window token, unsigned long mask, Tk_EventProc *proc, ClientData clientData);
    void (*tk_CreateGenericHandler) (Tk_GenericProc *proc, ClientData clientData);
    void (*tk_CreateImageType) (Tk_ImageType *typePtr);
    void (*tk_CreateItemType) (Tk_ItemType *typePtr);
    void (*tk_CreatePhotoImageFormat) (Tk_PhotoImageFormat *formatPtr);
    void (*tk_CreateSelHandler) (Tk_Window tkwin, Atom selection, Atom target, Tk_SelectionProc *proc, ClientData clientData, Atom format);
    Tk_Window (*tk_CreateWindow) (Tcl_Interp *interp, Tk_Window parent, const char *name, const char *screenName);
    Tk_Window (*tk_CreateWindowFromPath) (Tcl_Interp *interp, Tk_Window tkwin, const char *pathName, const char *screenName);
    int (*tk_DefineBitmap) (Tcl_Interp *interp, const char *name, const char *source, int width, int height);
    void (*tk_DefineCursor) (Tk_Window window, Tk_Cursor cursor);
    void (*tk_DeleteAllBindings) (Tk_BindingTable bindingTable, ClientData object);
    int (*tk_DeleteBinding) (Tcl_Interp *interp, Tk_BindingTable bindingTable, ClientData object, const char *eventStr);
    void (*tk_DeleteBindingTable) (Tk_BindingTable bindingTable);
    void (*tk_DeleteErrorHandler) (Tk_ErrorHandler handler);
    void (*tk_DeleteEventHandler) (Tk_Window token, unsigned long mask, Tk_EventProc *proc, ClientData clientData);
    void (*tk_DeleteGenericHandler) (Tk_GenericProc *proc, ClientData clientData);
    void (*tk_DeleteImage) (Tcl_Interp *interp, const char *name);
    void (*tk_DeleteSelHandler) (Tk_Window tkwin, Atom selection, Atom target);
    void (*tk_DestroyWindow) (Tk_Window tkwin);
    const char * (*tk_DisplayName) (Tk_Window tkwin);
    int (*tk_DistanceToTextLayout) (Tk_TextLayout layout, int x, int y);
    void (*tk_Draw3DPolygon) (Tk_Window tkwin, Drawable drawable, Tk_3DBorder border, XPoint *pointPtr, int numPoints, int borderWidth, int leftRelief);
    void (*tk_Draw3DRectangle) (Tk_Window tkwin, Drawable drawable, Tk_3DBorder border, int x, int y, int width, int height, int borderWidth, int relief);
    void (*tk_DrawChars) (Display *display, Drawable drawable, GC gc, Tk_Font tkfont, const char *source, int numBytes, int x, int y);
    void (*tk_DrawFocusHighlight) (Tk_Window tkwin, GC gc, int width, Drawable drawable);
    void (*tk_DrawTextLayout) (Display *display, Drawable drawable, GC gc, Tk_TextLayout layout, int x, int y, int firstChar, int lastChar);
    void (*tk_Fill3DPolygon) (Tk_Window tkwin, Drawable drawable, Tk_3DBorder border, XPoint *pointPtr, int numPoints, int borderWidth, int leftRelief);
    void (*tk_Fill3DRectangle) (Tk_Window tkwin, Drawable drawable, Tk_3DBorder border, int x, int y, int width, int height, int borderWidth, int relief);
    Tk_PhotoHandle (*tk_FindPhoto) (Tcl_Interp *interp, const char *imageName);
    Font (*tk_FontId) (Tk_Font font);
    void (*tk_Free3DBorder) (Tk_3DBorder border);
    void (*tk_FreeBitmap) (Display *display, Pixmap bitmap);
    void (*tk_FreeColor) (XColor *colorPtr);
    void (*tk_FreeColormap) (Display *display, Colormap colormap);
    void (*tk_FreeCursor) (Display *display, Tk_Cursor cursor);
    void (*tk_FreeFont) (Tk_Font f);
    void (*tk_FreeGC) (Display *display, GC gc);
    void (*tk_FreeImage) (Tk_Image image);
    void (*tk_FreeOptions) (Tk_ConfigSpec *specs, char *widgRec, Display *display, int needFlags);
    void (*tk_FreePixmap) (Display *display, Pixmap pixmap);
    void (*tk_FreeTextLayout) (Tk_TextLayout textLayout);
    void (*tk_FreeXId) (Display *display, XID xid);
    GC (*tk_GCForColor) (XColor *colorPtr, Drawable drawable);
    void (*tk_GeometryRequest) (Tk_Window tkwin, int reqWidth, int reqHeight);
    Tk_3DBorder (*tk_Get3DBorder) (Tcl_Interp *interp, Tk_Window tkwin, Tk_Uid colorName);
    void (*tk_GetAllBindings) (Tcl_Interp *interp, Tk_BindingTable bindingTable, ClientData object);
    int (*tk_GetAnchor) (Tcl_Interp *interp, const char *str, Tk_Anchor *anchorPtr);
    const char * (*tk_GetAtomName) (Tk_Window tkwin, Atom atom);
    const char * (*tk_GetBinding) (Tcl_Interp *interp, Tk_BindingTable bindingTable, ClientData object, const char *eventStr);
    Pixmap (*tk_GetBitmap) (Tcl_Interp *interp, Tk_Window tkwin, const char *str);
    Pixmap (*tk_GetBitmapFromData) (Tcl_Interp *interp, Tk_Window tkwin, const char *source, int width, int height);
    int (*tk_GetCapStyle) (Tcl_Interp *interp, const char *str, int *capPtr);
    XColor * (*tk_GetColor) (Tcl_Interp *interp, Tk_Window tkwin, Tk_Uid name);
    XColor * (*tk_GetColorByValue) (Tk_Window tkwin, XColor *colorPtr);
    Colormap (*tk_GetColormap) (Tcl_Interp *interp, Tk_Window tkwin, const char *str);
    Tk_Cursor (*tk_GetCursor) (Tcl_Interp *interp, Tk_Window tkwin, Tk_Uid str);
    Tk_Cursor (*tk_GetCursorFromData) (Tcl_Interp *interp, Tk_Window tkwin, const char *source, const char *mask, int width, int height, int xHot, int yHot, Tk_Uid fg, Tk_Uid bg);
    Tk_Font (*tk_GetFont) (Tcl_Interp *interp, Tk_Window tkwin, const char *str);
    Tk_Font (*tk_GetFontFromObj) (Tk_Window tkwin, Tcl_Obj *objPtr);
    void (*tk_GetFontMetrics) (Tk_Font font, Tk_FontMetrics *fmPtr);
    GC (*tk_GetGC) (Tk_Window tkwin, unsigned long valueMask, XGCValues *valuePtr);
    Tk_Image (*tk_GetImage) (Tcl_Interp *interp, Tk_Window tkwin, const char *name, Tk_ImageChangedProc *changeProc, ClientData clientData);
    ClientData (*tk_GetImageMasterData) (Tcl_Interp *interp, const char *name, Tk_ImageType **typePtrPtr);
    Tk_ItemType * (*tk_GetItemTypes) (void);
    int (*tk_GetJoinStyle) (Tcl_Interp *interp, const char *str, int *joinPtr);
    int (*tk_GetJustify) (Tcl_Interp *interp, const char *str, Tk_Justify *justifyPtr);
    int (*tk_GetNumMainWindows) (void);
    Tk_Uid (*tk_GetOption) (Tk_Window tkwin, const char *name, const char *className);
    int (*tk_GetPixels) (Tcl_Interp *interp, Tk_Window tkwin, const char *str, int *intPtr);
    Pixmap (*tk_GetPixmap) (Display *display, Drawable d, int width, int height, int depth);
    int (*tk_GetRelief) (Tcl_Interp *interp, const char *name, int *reliefPtr);
    void (*tk_GetRootCoords) (Tk_Window tkwin, int *xPtr, int *yPtr);
    int (*tk_GetScrollInfo) (Tcl_Interp *interp, int argc, char **argv, double *dblPtr, int *intPtr);
    int (*tk_GetScreenMM) (Tcl_Interp *interp, Tk_Window tkwin, const char *str, double *doublePtr);
    int (*tk_GetSelection) (Tcl_Interp *interp, Tk_Window tkwin, Atom selection, Atom target, Tk_GetSelProc *proc, ClientData clientData);
    Tk_Uid (*tk_GetUid) (const char *str);
    Visual * (*tk_GetVisual) (Tcl_Interp *interp, Tk_Window tkwin, const char *str, int *depthPtr, Colormap *colormapPtr);
    void (*tk_GetVRootGeometry) (Tk_Window tkwin, int *xPtr, int *yPtr, int *widthPtr, int *heightPtr);
    int (*tk_Grab) (Tcl_Interp *interp, Tk_Window tkwin, int grabGlobal);
    void (*tk_HandleEvent) (XEvent *eventPtr);
    Tk_Window (*tk_IdToWindow) (Display *display, Window window);
    void (*tk_ImageChanged) (Tk_ImageMaster master, int x, int y, int width, int height, int imageWidth, int imageHeight);
    int (*tk_Init) (Tcl_Interp *interp);
    Atom (*tk_InternAtom) (Tk_Window tkwin, const char *name);
    int (*tk_IntersectTextLayout) (Tk_TextLayout layout, int x, int y, int width, int height);
    void (*tk_MaintainGeometry) (Tk_Window slave, Tk_Window master, int x, int y, int width, int height);
    Tk_Window (*tk_MainWindow) (Tcl_Interp *interp);
    void (*tk_MakeWindowExist) (Tk_Window tkwin);
    void (*tk_ManageGeometry) (Tk_Window tkwin, const Tk_GeomMgr *mgrPtr, ClientData clientData);
    void (*tk_MapWindow) (Tk_Window tkwin);
    int (*tk_MeasureChars) (Tk_Font tkfont, const char *source, int numBytes, int maxPixels, int flags, int *lengthPtr);
    void (*tk_MoveResizeWindow) (Tk_Window tkwin, int x, int y, int width, int height);
    void (*tk_MoveWindow) (Tk_Window tkwin, int x, int y);
    void (*tk_MoveToplevelWindow) (Tk_Window tkwin, int x, int y);
    const char * (*tk_NameOf3DBorder) (Tk_3DBorder border);
    const char * (*tk_NameOfAnchor) (Tk_Anchor anchor);
    const char * (*tk_NameOfBitmap) (Display *display, Pixmap bitmap);
    const char * (*tk_NameOfCapStyle) (int cap);
    const char * (*tk_NameOfColor) (XColor *colorPtr);
    const char * (*tk_NameOfCursor) (Display *display, Tk_Cursor cursor);
    const char * (*tk_NameOfFont) (Tk_Font font);
    const char * (*tk_NameOfImage) (Tk_ImageMaster imageMaster);
    const char * (*tk_NameOfJoinStyle) (int join);
    const char * (*tk_NameOfJustify) (Tk_Justify justify);
    const char * (*tk_NameOfRelief) (int relief);
    Tk_Window (*tk_NameToWindow) (Tcl_Interp *interp, const char *pathName, Tk_Window tkwin);
    void (*tk_OwnSelection) (Tk_Window tkwin, Atom selection, Tk_LostSelProc *proc, ClientData clientData);
    int (*tk_ParseArgv) (Tcl_Interp *interp, Tk_Window tkwin, int *argcPtr, char **argv, Tk_ArgvInfo *argTable, int flags);
    void (*tk_PhotoPutBlock_NoComposite) (Tk_PhotoHandle handle, Tk_PhotoImageBlock *blockPtr, int x, int y, int width, int height);
    void (*tk_PhotoPutZoomedBlock_NoComposite) (Tk_PhotoHandle handle, Tk_PhotoImageBlock *blockPtr, int x, int y, int width, int height, int zoomX, int zoomY, int subsampleX, int subsampleY);
    int (*tk_PhotoGetImage) (Tk_PhotoHandle handle, Tk_PhotoImageBlock *blockPtr);
    void (*tk_PhotoBlank) (Tk_PhotoHandle handle);
    void (*tk_PhotoExpand_Panic) (Tk_PhotoHandle handle, int width, int height);
    void (*tk_PhotoGetSize) (Tk_PhotoHandle handle, int *widthPtr, int *heightPtr);
    void (*tk_PhotoSetSize_Panic) (Tk_PhotoHandle handle, int width, int height);
    int (*tk_PointToChar) (Tk_TextLayout layout, int x, int y);
    int (*tk_PostscriptFontName) (Tk_Font tkfont, Tcl_DString *dsPtr);
    void (*tk_PreserveColormap) (Display *display, Colormap colormap);
    void (*tk_QueueWindowEvent) (XEvent *eventPtr, Tcl_QueuePosition position);
    void (*tk_RedrawImage) (Tk_Image image, int imageX, int imageY, int width, int height, Drawable drawable, int drawableX, int drawableY);
    void (*tk_ResizeWindow) (Tk_Window tkwin, int width, int height);
    int (*tk_RestackWindow) (Tk_Window tkwin, int aboveBelow, Tk_Window other);
    Tk_RestrictProc * (*tk_RestrictEvents) (Tk_RestrictProc *proc, ClientData arg, ClientData *prevArgPtr);
    int (*tk_SafeInit) (Tcl_Interp *interp);
    const char * (*tk_SetAppName) (Tk_Window tkwin, const char *name);
    void (*tk_SetBackgroundFromBorder) (Tk_Window tkwin, Tk_3DBorder border);
    void (*tk_SetClass) (Tk_Window tkwin, const char *className);
    void (*tk_SetGrid) (Tk_Window tkwin, int reqWidth, int reqHeight, int gridWidth, int gridHeight);
    void (*tk_SetInternalBorder) (Tk_Window tkwin, int width);
    void (*tk_SetWindowBackground) (Tk_Window tkwin, unsigned long pixel);
    void (*tk_SetWindowBackgroundPixmap) (Tk_Window tkwin, Pixmap pixmap);
    void (*tk_SetWindowBorder) (Tk_Window tkwin, unsigned long pixel);
    void (*tk_SetWindowBorderWidth) (Tk_Window tkwin, int width);
    void (*tk_SetWindowBorderPixmap) (Tk_Window tkwin, Pixmap pixmap);
    void (*tk_SetWindowColormap) (Tk_Window tkwin, Colormap colormap);
    int (*tk_SetWindowVisual) (Tk_Window tkwin, Visual *visual, int depth, Colormap colormap);
    void (*tk_SizeOfBitmap) (Display *display, Pixmap bitmap, int *widthPtr, int *heightPtr);
    void (*tk_SizeOfImage) (Tk_Image image, int *widthPtr, int *heightPtr);
    int (*tk_StrictMotif) (Tk_Window tkwin);
    void (*tk_TextLayoutToPostscript) (Tcl_Interp *interp, Tk_TextLayout layout);
    int (*tk_TextWidth) (Tk_Font font, const char *str, int numBytes);
    void (*tk_UndefineCursor) (Tk_Window window);
    void (*tk_UnderlineChars) (Display *display, Drawable drawable, GC gc, Tk_Font tkfont, const char *source, int x, int y, int firstByte, int lastByte);
    void (*tk_UnderlineTextLayout) (Display *display, Drawable drawable, GC gc, Tk_TextLayout layout, int x, int y, int underline);
    void (*tk_Ungrab) (Tk_Window tkwin);
    void (*tk_UnmaintainGeometry) (Tk_Window slave, Tk_Window master);
    void (*tk_UnmapWindow) (Tk_Window tkwin);
    void (*tk_UnsetGrid) (Tk_Window tkwin);
    void (*tk_UpdatePointer) (Tk_Window tkwin, int x, int y, int state);
    Pixmap (*tk_AllocBitmapFromObj) (Tcl_Interp *interp, Tk_Window tkwin, Tcl_Obj *objPtr);
    Tk_3DBorder (*tk_Alloc3DBorderFromObj) (Tcl_Interp *interp, Tk_Window tkwin, Tcl_Obj *objPtr);
    XColor * (*tk_AllocColorFromObj) (Tcl_Interp *interp, Tk_Window tkwin, Tcl_Obj *objPtr);
    Tk_Cursor (*tk_AllocCursorFromObj) (Tcl_Interp *interp, Tk_Window tkwin, Tcl_Obj *objPtr);
    Tk_Font (*tk_AllocFontFromObj) (Tcl_Interp *interp, Tk_Window tkwin, Tcl_Obj *objPtr);
    Tk_OptionTable (*tk_CreateOptionTable) (Tcl_Interp *interp, const Tk_OptionSpec *templatePtr);
    void (*tk_DeleteOptionTable) (Tk_OptionTable optionTable);
    void (*tk_Free3DBorderFromObj) (Tk_Window tkwin, Tcl_Obj *objPtr);
    void (*tk_FreeBitmapFromObj) (Tk_Window tkwin, Tcl_Obj *objPtr);
    void (*tk_FreeColorFromObj) (Tk_Window tkwin, Tcl_Obj *objPtr);
    void (*tk_FreeConfigOptions) (char *recordPtr, Tk_OptionTable optionToken, Tk_Window tkwin);
    void (*tk_FreeSavedOptions) (Tk_SavedOptions *savePtr);
    void (*tk_FreeCursorFromObj) (Tk_Window tkwin, Tcl_Obj *objPtr);
    void (*tk_FreeFontFromObj) (Tk_Window tkwin, Tcl_Obj *objPtr);
    Tk_3DBorder (*tk_Get3DBorderFromObj) (Tk_Window tkwin, Tcl_Obj *objPtr);
    int (*tk_GetAnchorFromObj) (Tcl_Interp *interp, Tcl_Obj *objPtr, Tk_Anchor *anchorPtr);
    Pixmap (*tk_GetBitmapFromObj) (Tk_Window tkwin, Tcl_Obj *objPtr);
    XColor * (*tk_GetColorFromObj) (Tk_Window tkwin, Tcl_Obj *objPtr);
    Tk_Cursor (*tk_GetCursorFromObj) (Tk_Window tkwin, Tcl_Obj *objPtr);
    Tcl_Obj * (*tk_GetOptionInfo) (Tcl_Interp *interp, char *recordPtr, Tk_OptionTable optionTable, Tcl_Obj *namePtr, Tk_Window tkwin);
    Tcl_Obj * (*tk_GetOptionValue) (Tcl_Interp *interp, char *recordPtr, Tk_OptionTable optionTable, Tcl_Obj *namePtr, Tk_Window tkwin);
    int (*tk_GetJustifyFromObj) (Tcl_Interp *interp, Tcl_Obj *objPtr, Tk_Justify *justifyPtr);
    int (*tk_GetMMFromObj) (Tcl_Interp *interp, Tk_Window tkwin, Tcl_Obj *objPtr, double *doublePtr);
    int (*tk_GetPixelsFromObj) (Tcl_Interp *interp, Tk_Window tkwin, Tcl_Obj *objPtr, int *intPtr);
    int (*tk_GetReliefFromObj) (Tcl_Interp *interp, Tcl_Obj *objPtr, int *resultPtr);
    int (*tk_GetScrollInfoObj) (Tcl_Interp *interp, int objc, Tcl_Obj *const objv[], double *dblPtr, int *intPtr);
    int (*tk_InitOptions) (Tcl_Interp *interp, char *recordPtr, Tk_OptionTable optionToken, Tk_Window tkwin);
    void (*tk_MainEx) (int argc, char **argv, Tcl_AppInitProc *appInitProc, Tcl_Interp *interp);
    void (*tk_RestoreSavedOptions) (Tk_SavedOptions *savePtr);
    int (*tk_SetOptions) (Tcl_Interp *interp, char *recordPtr, Tk_OptionTable optionTable, int objc, Tcl_Obj *const objv[], Tk_Window tkwin, Tk_SavedOptions *savePtr, int *maskPtr);
    void (*tk_InitConsoleChannels) (Tcl_Interp *interp);
    int (*tk_CreateConsoleWindow) (Tcl_Interp *interp);
    void (*tk_CreateSmoothMethod) (Tcl_Interp *interp, Tk_SmoothMethod *method);
    void *reserved218;
    void *reserved219;
    int (*tk_GetDash) (Tcl_Interp *interp, const char *value, Tk_Dash *dash);
    void (*tk_CreateOutline) (Tk_Outline *outline);
    void (*tk_DeleteOutline) (Display *display, Tk_Outline *outline);
    int (*tk_ConfigOutlineGC) (XGCValues *gcValues, Tk_Canvas canvas, Tk_Item *item, Tk_Outline *outline);
    int (*tk_ChangeOutlineGC) (Tk_Canvas canvas, Tk_Item *item, Tk_Outline *outline);
    int (*tk_ResetOutlineGC) (Tk_Canvas canvas, Tk_Item *item, Tk_Outline *outline);
    int (*tk_CanvasPsOutline) (Tk_Canvas canvas, Tk_Item *item, Tk_Outline *outline);
    void (*tk_SetTSOrigin) (Tk_Window tkwin, GC gc, int x, int y);
    int (*tk_CanvasGetCoordFromObj) (Tcl_Interp *interp, Tk_Canvas canvas, Tcl_Obj *obj, double *doublePtr);
    void (*tk_CanvasSetOffset) (Tk_Canvas canvas, GC gc, Tk_TSOffset *offset);
    void (*tk_DitherPhoto) (Tk_PhotoHandle handle, int x, int y, int width, int height);
    int (*tk_PostscriptBitmap) (Tcl_Interp *interp, Tk_Window tkwin, Tk_PostscriptInfo psInfo, Pixmap bitmap, int startX, int startY, int width, int height);
    int (*tk_PostscriptColor) (Tcl_Interp *interp, Tk_PostscriptInfo psInfo, XColor *colorPtr);
    int (*tk_PostscriptFont) (Tcl_Interp *interp, Tk_PostscriptInfo psInfo, Tk_Font font);
    int (*tk_PostscriptImage) (Tk_Image image, Tcl_Interp *interp, Tk_Window tkwin, Tk_PostscriptInfo psinfo, int x, int y, int width, int height, int prepass);
    void (*tk_PostscriptPath) (Tcl_Interp *interp, Tk_PostscriptInfo psInfo, double *coordPtr, int numPoints);
    int (*tk_PostscriptStipple) (Tcl_Interp *interp, Tk_Window tkwin, Tk_PostscriptInfo psInfo, Pixmap bitmap);
    double (*tk_PostscriptY) (double y, Tk_PostscriptInfo psInfo);
    int (*tk_PostscriptPhoto) (Tcl_Interp *interp, Tk_PhotoImageBlock *blockPtr, Tk_PostscriptInfo psInfo, int width, int height);
    void (*tk_CreateClientMessageHandler) (Tk_ClientMessageProc *proc);
    void (*tk_DeleteClientMessageHandler) (Tk_ClientMessageProc *proc);
    Tk_Window (*tk_CreateAnonymousWindow) (Tcl_Interp *interp, Tk_Window parent, const char *screenName);
    void (*tk_SetClassProcs) (Tk_Window tkwin, Tk_ClassProcs *procs, ClientData instanceData);
    void (*tk_SetInternalBorderEx) (Tk_Window tkwin, int left, int right, int top, int bottom);
    void (*tk_SetMinimumRequestSize) (Tk_Window tkwin, int minWidth, int minHeight);
    void (*tk_SetCaretPos) (Tk_Window tkwin, int x, int y, int height);
    void (*tk_PhotoPutBlock_Panic) (Tk_PhotoHandle handle, Tk_PhotoImageBlock *blockPtr, int x, int y, int width, int height, int compRule);
    void (*tk_PhotoPutZoomedBlock_Panic) (Tk_PhotoHandle handle, Tk_PhotoImageBlock *blockPtr, int x, int y, int width, int height, int zoomX, int zoomY, int subsampleX, int subsampleY, int compRule);
    int (*tk_CollapseMotionEvents) (Display *display, int collapse);
    Tk_StyleEngine (*tk_RegisterStyleEngine) (const char *name, Tk_StyleEngine parent);
    Tk_StyleEngine (*tk_GetStyleEngine) (const char *name);
    int (*tk_RegisterStyledElement) (Tk_StyleEngine engine, Tk_ElementSpec *templatePtr);
    int (*tk_GetElementId) (const char *name);
    Tk_Style (*tk_CreateStyle) (const char *name, Tk_StyleEngine engine, ClientData clientData);
    Tk_Style (*tk_GetStyle) (Tcl_Interp *interp, const char *name);
    void (*tk_FreeStyle) (Tk_Style style);
    const char * (*tk_NameOfStyle) (Tk_Style style);
    Tk_Style (*tk_AllocStyleFromObj) (Tcl_Interp *interp, Tcl_Obj *objPtr);
    Tk_Style (*tk_GetStyleFromObj) (Tcl_Obj *objPtr);
    void (*tk_FreeStyleFromObj) (Tcl_Obj *objPtr);
    Tk_StyledElement (*tk_GetStyledElement) (Tk_Style style, int elementId, Tk_OptionTable optionTable);
    void (*tk_GetElementSize) (Tk_Style style, Tk_StyledElement element, char *recordPtr, Tk_Window tkwin, int width, int height, int inner, int *widthPtr, int *heightPtr);
    void (*tk_GetElementBox) (Tk_Style style, Tk_StyledElement element, char *recordPtr, Tk_Window tkwin, int x, int y, int width, int height, int inner, int *xPtr, int *yPtr, int *widthPtr, int *heightPtr);
    int (*tk_GetElementBorderWidth) (Tk_Style style, Tk_StyledElement element, char *recordPtr, Tk_Window tkwin);
    void (*tk_DrawElement) (Tk_Style style, Tk_StyledElement element, char *recordPtr, Tk_Window tkwin, Drawable d, int x, int y, int width, int height, int state);
    int (*tk_PhotoExpand) (Tcl_Interp *interp, Tk_PhotoHandle handle, int width, int height);
    int (*tk_PhotoPutBlock) (Tcl_Interp *interp, Tk_PhotoHandle handle, Tk_PhotoImageBlock *blockPtr, int x, int y, int width, int height, int compRule);
    int (*tk_PhotoPutZoomedBlock) (Tcl_Interp *interp, Tk_PhotoHandle handle, Tk_PhotoImageBlock *blockPtr, int x, int y, int width, int height, int zoomX, int zoomY, int subsampleX, int subsampleY, int compRule);
    int (*tk_PhotoSetSize) (Tcl_Interp *interp, Tk_PhotoHandle handle, int width, int height);
    long (*tk_GetUserInactiveTime) (Display *dpy);
    void (*tk_ResetUserInactiveTime) (Display *dpy);
    Tcl_Interp * (*tk_Interp) (Tk_Window tkwin);
    void (*tk_CreateOldImageType) (Tk_ImageType *typePtr);
    void (*tk_CreateOldPhotoImageFormat) (Tk_PhotoImageFormat *formatPtr);
} TkStubs;




extern TkStubs *tkStubsPtr;
# 1538 "/usr/include/tk.h" 2 3 4
# 68 "_tkinter.c" 2


# 1 "tkinter.h" 1
# 71 "_tkinter.c" 2
# 177 "_tkinter.c"
static PyThread_type_lock tcl_lock = 0;


static Tcl_ThreadDataKey state_key;
typedef PyThreadState *ThreadSpecificData;
# 233 "_tkinter.c"
static PyTypeObject Tkapp_Type;

typedef struct {
    PyObject ob_base;
    Tcl_Interp *interp;
    int wantobjects;
    int threaded;
    Tcl_ThreadId thread_id;
    int dispatching;


    Tcl_ObjType *BooleanType;
    Tcl_ObjType *ByteArrayType;
    Tcl_ObjType *DoubleType;
    Tcl_ObjType *IntType;
    Tcl_ObjType *ListType;
    Tcl_ObjType *ProcBodyType;
    Tcl_ObjType *StringType;
} TkappObject;
# 264 "_tkinter.c"
static PyObject *Tkinter_TclError;
static int quitMainLoop = 0;
static int errorInCmd = 0;
static PyObject *excInCmd;
static PyObject *valInCmd;
static PyObject *trbInCmd;






static PyObject *
Tkinter_Error(PyObject *v)
{
    PyErr_SetString(Tkinter_TclError, Tcl_GetStringResult((((TkappObject *) (v))->interp)));
    return ((void *)0);
}





static int Tkinter_busywaitinterval = 20;






static void
Sleep(int milli)
{

    struct timeval t;
    t.tv_sec = milli/1000;
    t.tv_usec = (milli%1000) * 1000;
    select(0, (fd_set *)0, (fd_set *)0, (fd_set *)0, &t);
}




static int
WaitForMainloop(TkappObject* self)
{
    int i;
    for (i = 0; i < 10; i++) {
        if (self->dispatching)
            return 1;
        { PyThreadState *_save; _save = PyEval_SaveThread();
        Sleep(100);
        PyEval_RestoreThread(_save); }
    }
    if (self->dispatching)
        return 1;
    PyErr_SetString(PyExc_RuntimeError, "main thread is not in main loop");
    return 0;
}



static char *
AsString(PyObject *value, PyObject *tmp)
{
    if (((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<27))) != 0))
        return PyBytes_AsString(value);
    else if (((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        PyObject *v = PyUnicode_AsUTF8String(value);
        if (v == ((void *)0))
            return ((void *)0);
        if (PyList_Append(tmp, v) != 0) {
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            return ((void *)0);
        }
        do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
        return PyBytes_AsString(v);
    }
    else {
        PyObject *v = PyObject_Str(value);
        if (v == ((void *)0))
            return ((void *)0);
        if (PyList_Append(tmp, v) != 0) {
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            return ((void *)0);
        }
        do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
        return PyBytes_AsString(v);
    }
}





static char *
Merge(PyObject *args)
{
    PyObject *tmp = ((void *)0);
    char *argvStore[64];
    char **argv = ((void *)0);
    int fvStore[64];
    int *fv = ((void *)0);
    int argc = 0, fvc = 0, i;
    char *res = ((void *)0);

    if (!(tmp = PyList_New(0)))
        return ((void *)0);

    argv = argvStore;
    fv = fvStore;

    if (args == ((void *)0))
        argc = 0;

    else if (!((((((PyObject*)(args))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
        argc = 1;
        fv[0] = 0;
        if (!(argv[0] = AsString(args, tmp)))
            goto finally;
    }
    else {
        argc = PyTuple_Size(args);

        if (argc > 64) {
            argv = (char **)Tcl_Alloc(argc * sizeof(char *));
            fv = (int *)Tcl_Alloc(argc * sizeof(int));
            if (argv == ((void *)0) || fv == ((void *)0)) {
                PyErr_NoMemory();
                goto finally;
            }
        }

        for (i = 0; i < argc; i++) {
            PyObject *v = PyTuple_GetItem(args, i);
            if (((((((PyObject*)(v))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
                fv[i] = 1;
                if (!(argv[i] = Merge(v)))
                    goto finally;
                fvc++;
            }
            else if (v == (&_Py_NoneStruct)) {
                argc = i;
                break;
            }
            else {
                fv[i] = 0;
                if (!(argv[i] = AsString(v, tmp)))
                    goto finally;
                fvc++;
            }
        }
    }
    res = Tcl_Merge(argc, argv);
    if (res == ((void *)0))
        PyErr_SetString(Tkinter_TclError, "merge failed");

  finally:
    for (i = 0; i < fvc; i++)
        if (fv[i]) {
            Tcl_Free(argv[i]);
        }
    if (argv != argvStore)
        Tcl_Free((char *) argv);
    if (fv != fvStore)
        Tcl_Free((char *) fv);

    do { if ( --((PyObject*)(tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tmp)))); } while (0);
    return res;
}



static PyObject *
Split(char *list)
{
    int argc;
    char **argv;
    PyObject *v;

    if (list == ((void *)0)) {
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        return (&_Py_NoneStruct);
    }

    if (Tcl_SplitList((Tcl_Interp *)((void *)0), list, &argc, &argv) != 0) {




        return PyUnicode_FromString(list);
    }

    if (argc == 0)
        v = PyUnicode_FromString("");
    else if (argc == 1)
        v = PyUnicode_FromString(argv[0]);
    else if ((v = PyTuple_New(argc)) != ((void *)0)) {
        int i;
        PyObject *w;

        for (i = 0; i < argc; i++) {
            if ((w = Split(argv[i])) == ((void *)0)) {
                do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
                v = ((void *)0);
                break;
            }
            PyTuple_SetItem(v, i, w);
        }
    }
    Tcl_Free((char *) argv);
    return v;
}





static PyObject *
SplitObj(PyObject *arg)
{
    if (((((((PyObject*)(arg))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
        int i, size;
        PyObject *elem, *newelem, *result;

        size = PyTuple_Size(arg);
        result = ((void *)0);



        for(i = 0; i < size; i++) {
            elem = PyTuple_GetItem(arg, i);
            newelem = SplitObj(elem);
            if (!newelem) {
                do { if ((result) == ((void *)0)) ; else do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0); } while (0);
                return ((void *)0);
            }
            if (!result) {
                int k;
                if (newelem == elem) {
                    do { if ( --((PyObject*)(newelem))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(newelem)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(newelem)))); } while (0);
                    continue;
                }
                result = PyTuple_New(size);
                if (!result)
                    return ((void *)0);
                for(k = 0; k < i; k++) {
                    elem = PyTuple_GetItem(arg, k);
                    ( ((PyObject*)(elem))->ob_refcnt++);
                    PyTuple_SetItem(result, k, elem);
                }
            }
            PyTuple_SetItem(result, i, newelem);
        }
        if (result)
            return result;

    }
    else if (((((((PyObject*)(arg))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
        int argc;
        char **argv;
        char *list = PyBytes_AsString(arg);

        if (Tcl_SplitList((Tcl_Interp *)((void *)0), list, &argc, &argv) != 0) {
            ( ((PyObject*)(arg))->ob_refcnt++);
            return arg;
        }
        Tcl_Free((char *) argv);
        if (argc > 1)
            return Split(PyBytes_AsString(arg));

    }
    ( ((PyObject*)(arg))->ob_refcnt++);
    return arg;
}





int
Tcl_AppInit(Tcl_Interp *interp)
{
    const char * _tkinter_skip_tk_init;

    if (Tcl_Init(interp) == 1) {
        PySys_WriteStderr("Tcl_Init error: %s\n", Tcl_GetStringResult(interp));
        return 1;
    }

    _tkinter_skip_tk_init = Tcl_GetVar(interp,
                    "_tkinter_skip_tk_init", 1);
    if (_tkinter_skip_tk_init != ((void *)0) &&
                    strcmp(_tkinter_skip_tk_init, "1") == 0) {
        return 0;
    }
# 568 "_tkinter.c"
    if (Tk_Init(interp) == 1) {



        PySys_WriteStderr("Tk_Init error: %s\n", Tcl_GetStringResult(interp));
        return 1;
    }

    return 0;
}
# 587 "_tkinter.c"
static void EnableEventHook(void);
static void DisableEventHook(void);

static TkappObject *
Tkapp_New(char *screenName, char *className,
          int interactive, int wantobjects, int wantTk, int sync, char *use)
{
    TkappObject *v;
    char *argv0;

    v = ( (TkappObject *) _PyObject_New(&Tkapp_Type) );
    if (v == ((void *)0))
        return ((void *)0);

    v->interp = Tcl_CreateInterp();
    v->wantobjects = wantobjects;
    v->threaded = Tcl_GetVar2Ex(v->interp, "tcl_platform", "threaded",
                                1) != ((void *)0);
    v->thread_id = Tcl_GetCurrentThread();
    v->dispatching = 0;
# 616 "_tkinter.c"
    if (v->threaded && tcl_lock) {

        PyThread_free_lock(tcl_lock);
        tcl_lock = ((void *)0);
    }


    v->BooleanType = Tcl_GetObjType("boolean");
    v->ByteArrayType = Tcl_GetObjType("bytearray");
    v->DoubleType = Tcl_GetObjType("double");
    v->IntType = Tcl_GetObjType("int");
    v->ListType = Tcl_GetObjType("list");
    v->ProcBodyType = Tcl_GetObjType("procbody");
    v->StringType = Tcl_GetObjType("string");


    Tcl_DeleteCommand(v->interp, "exit");

    if (screenName != ((void *)0))
        Tcl_SetVar2(v->interp, "env", "DISPLAY",
                    screenName, 1);

    if (interactive)
        Tcl_SetVar(v->interp, "tcl_interactive", "1", 1);
    else
        Tcl_SetVar(v->interp, "tcl_interactive", "0", 1);


    argv0 = (char*)Tcl_Alloc(strlen(className) + 1);
    if (!argv0) {
        PyErr_NoMemory();
        do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
        return ((void *)0);
    }

    ((__builtin_object_size (argv0, 0) != (size_t) -1) ? __builtin___strcpy_chk (argv0, className, __builtin_object_size (argv0, 2 > 1)) : __inline_strcpy_chk (argv0, className));
    if ((_Py_ctype_table[((unsigned char)((((unsigned char)((argv0[0]) & 0xff))) & 0xff))] & 0x02))
        argv0[0] = (_Py_ctype_tolower[((unsigned char)((((unsigned char)((argv0[0]) & 0xff))) & 0xff))]);
    Tcl_SetVar(v->interp, "argv0", argv0, 1);
    Tcl_Free(argv0);

    if (! wantTk) {
        Tcl_SetVar(v->interp,
                        "_tkinter_skip_tk_init", "1", 1);
    }
# 669 "_tkinter.c"
    if (sync || use) {
        char *args;
        int len = 0;

        if (sync)
            len += sizeof "-sync";
        if (use)
            len += strlen(use) + sizeof "-use ";

        args = (char*)Tcl_Alloc(len);
        if (!args) {
            PyErr_NoMemory();
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            return ((void *)0);
        }

        args[0] = '\0';
        if (sync)
            ((__builtin_object_size (args, 0) != (size_t) -1) ? __builtin___strcat_chk (args, "-sync", __builtin_object_size (args, 2 > 1)) : __inline_strcat_chk (args, "-sync"));
        if (use) {
            if (sync)
                ((__builtin_object_size (args, 0) != (size_t) -1) ? __builtin___strcat_chk (args, " ", __builtin_object_size (args, 2 > 1)) : __inline_strcat_chk (args, " "));
            ((__builtin_object_size (args, 0) != (size_t) -1) ? __builtin___strcat_chk (args, "-use ", __builtin_object_size (args, 2 > 1)) : __inline_strcat_chk (args, "-use "));
            ((__builtin_object_size (args, 0) != (size_t) -1) ? __builtin___strcat_chk (args, use, __builtin_object_size (args, 2 > 1)) : __inline_strcat_chk (args, use));
        }

        Tcl_SetVar(v->interp, "argv", args, 1);
        Tcl_Free(args);
    }

    if (Tcl_AppInit(v->interp) != 0) {
        PyObject *result = Tkinter_Error((PyObject *)v);
# 713 "_tkinter.c"
        do { if ( --((PyObject*)((PyObject *)v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)((PyObject *)v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)((PyObject *)v)))); } while (0);
        return (TkappObject *)result;
    }

    EnableEventHook();

    return v;
}



static void
Tkapp_ThreadSend(TkappObject *self, Tcl_Event *ev,
                 Tcl_Condition *cond, Tcl_Mutex *mutex)
{
    { PyThreadState *_save; _save = PyEval_SaveThread();;
    Tcl_MutexLock(mutex);
    Tcl_ThreadQueueEvent(self->thread_id, ev, TCL_QUEUE_TAIL);
    Tcl_ThreadAlert(self->thread_id);
    Tcl_ConditionWait(cond, mutex, ((void *)0));
    Tcl_MutexUnlock(mutex);
    PyEval_RestoreThread(_save); }
}





typedef struct {
    PyObject ob_base;
    Tcl_Obj *value;
    PyObject *string;
} PyTclObject;

static PyTypeObject PyTclObject_Type;


static PyObject *
newPyTclObject(Tcl_Obj *arg)
{
    PyTclObject *self;
    self = ( (PyTclObject *) _PyObject_New(&PyTclObject_Type) );
    if (self == ((void *)0))
        return ((void *)0);
    ++(arg)->refCount;
    self->value = arg;
    self->string = ((void *)0);
    return (PyObject*)self;
}

static void
PyTclObject_dealloc(PyTclObject *self)
{
    do { if (--(self->value)->refCount <= 0) TclFreeObj(self->value); } while(0);
    do { if ((self->string) == ((void *)0)) ; else do { if ( --((PyObject*)(self->string))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->string)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->string)))); } while (0); } while (0);
    PyObject_Free(self);
}

static char*
PyTclObject_TclString(PyObject *self)
{
    return Tcl_GetString(((PyTclObject*)self)->value);
}


static char PyTclObject_string__doc__[] = "the string representation of this object, either as str or bytes";


static PyObject *
PyTclObject_string(PyTclObject *self, void *ignored)
{
    char *s;
    int len;
    if (!self->string) {
        s = Tcl_GetStringFromObj(self->value, &len);
        self->string = PyUnicode_FromStringAndSize(s, len);
        if (!self->string)
            return ((void *)0);
    }
    ( ((PyObject*)(self->string))->ob_refcnt++);
    return self->string;
}

static PyObject *
PyTclObject_str(PyTclObject *self, void *ignored)
{
    char *s;
    int len;
    if (self->string && ((((((PyObject*)(self->string))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        ( ((PyObject*)(self->string))->ob_refcnt++);
        return self->string;
    }

    s = Tcl_GetStringFromObj(self->value, &len);
    return PyUnicode_DecodeUTF8(s, len, "strict");
}

static PyObject *
PyTclObject_repr(PyTclObject *self)
{
    return PyUnicode_FromFormat("<%s object at %p>",
                                self->value->typePtr->name, self->value);
}



static PyObject *
PyTclObject_richcompare(PyObject *self, PyObject *other, int op)
{
    int result;
    PyObject *v;


    if (self == ((void *)0) || other == ((void *)0)) {
        _PyErr_BadInternalCall("_tkinter.c", 827);
        return ((void *)0);
    }


    if (!((self)->ob_type == &PyTclObject_Type) || !((other)->ob_type == &PyTclObject_Type)) {
        v = (&_Py_NotImplementedStruct);
        goto finished;
    }

    if (self == other)

        result = 0;
    else
        result = strcmp(Tcl_GetString(((PyTclObject *)self)->value),
                        Tcl_GetString(((PyTclObject *)other)->value));

    switch (op) {
    case 2:
        v = ((result == 0) ? ((PyObject *) &_Py_TrueStruct) : ((PyObject *) &_Py_FalseStruct));
        break;
    case 3:
        v = ((result != 0) ? ((PyObject *) &_Py_TrueStruct) : ((PyObject *) &_Py_FalseStruct));
        break;
    case 1:
        v = ((result <= 0) ? ((PyObject *) &_Py_TrueStruct) : ((PyObject *) &_Py_FalseStruct));
        break;
    case 5:
        v = ((result >= 0) ? ((PyObject *) &_Py_TrueStruct) : ((PyObject *) &_Py_FalseStruct));
        break;
    case 0:
        v = ((result < 0) ? ((PyObject *) &_Py_TrueStruct) : ((PyObject *) &_Py_FalseStruct));
        break;
    case 4:
        v = ((result > 0) ? ((PyObject *) &_Py_TrueStruct) : ((PyObject *) &_Py_FalseStruct));
        break;
    default:
        PyErr_BadArgument();
        return ((void *)0);
    }
  finished:
    ( ((PyObject*)(v))->ob_refcnt++);
    return v;
}

static char get_typename__doc__[] = "name of the Tcl type";

static PyObject*
get_typename(PyTclObject* obj, void* ignored)
{
    return PyUnicode_FromString(obj->value->typePtr->name);
}


static PyGetSetDef PyTclObject_getsetlist[] = {
    {"typename", (getter)get_typename, ((void *)0), get_typename__doc__},
    {"string", (getter)PyTclObject_string, ((void *)0),
     PyTclObject_string__doc__},
    {0},
};

static PyTypeObject PyTclObject_Type = {
    { { 1, ((void *)0) }, 0 },
    "_tkinter.Tcl_Obj",
    sizeof(PyTclObject),
    0,

    (destructor)PyTclObject_dealloc,
    0,
    0,
    0,
    0,
    (reprfunc)PyTclObject_repr,
    0,
    0,
    0,
    0,
    0,
    (reprfunc)PyTclObject_str,
    PyObject_GenericGetAttr,
    0,
    0,
    ( 0 | (1L<<18) | 0),
    0,
    0,
    0,
    PyTclObject_richcompare,
    0,
    0,
    0,
    0,
    0,
    PyTclObject_getsetlist,
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
};

static Tcl_Obj*
AsObj(PyObject *value)
{
    Tcl_Obj *result;
    long longVal;
    int overflow;

    if (((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<27))) != 0))
        return Tcl_NewStringObj(((__builtin_expect(!(((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_tkinter.c", 940, "PyBytes_Check(value)") : (void)0), (((PyBytesObject *)(value))->ob_sval)),
                                ((__builtin_expect(!(((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_tkinter.c", 941, "PyBytes_Check(value)") : (void)0),(((PyVarObject*)(value))->ob_size)));
    else if (((((PyObject*)(value))->ob_type) == &PyBool_Type))
        return Tcl_NewBooleanObj(PyObject_IsTrue(value));
    else if (((((PyObject*)(value))->ob_type) == &PyLong_Type) &&
             ((longVal = PyLong_AsLongAndOverflow(value, &overflow)),
              !overflow)) {


        return Tcl_NewLongObj(longVal);
    }
    else if (((((PyObject*)(value))->ob_type) == (&PyFloat_Type) || PyType_IsSubtype((((PyObject*)(value))->ob_type), (&PyFloat_Type))))
        return Tcl_NewDoubleObj((((PyFloatObject *)(value))->ob_fval));
    else if (((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
        Tcl_Obj **argv = (Tcl_Obj**)
            Tcl_Alloc(PyTuple_Size(value)*sizeof(Tcl_Obj*));
        int i;
        if(!argv)
          return 0;
        for(i=0;i<PyTuple_Size(value);i++)
          argv[i] = AsObj(PyTuple_GetItem(value,i));
        result = Tcl_NewListObj(PyTuple_Size(value), argv);
        Tcl_Free((char *) argv);
        return result;
    }
    else if (((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        void *inbuf;
        Py_ssize_t size;
        int kind;
        Tcl_UniChar *outbuf = ((void *)0);
        Py_ssize_t i;
        size_t allocsize;

        if (((__builtin_expect(!(((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_tkinter.c", 973, "PyUnicode_Check(value)") : (void)0), ((((PyASCIIObject*)value)->state.ready) ? 0 : _PyUnicode_Ready((PyObject *)(value)))) == -1)
            return ((void *)0);

        inbuf = ((__builtin_expect(!(((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_tkinter.c", 976, "PyUnicode_Check(value)") : (void)0), (((PyASCIIObject*)(value))->state.compact) ? (((__builtin_expect(!(((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_tkinter.c", 976, "PyUnicode_Check(value)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)value)->state.ready)), 0) ? __assert_rtn(__func__, "_tkinter.c", 976, "PyUnicode_IS_READY(value)") : (void)0), ((PyASCIIObject*)value)->state.ascii) ? ((void*)((PyASCIIObject*)(value) + 1)) : ((void*)((PyCompactUnicodeObject*)(value) + 1))) : ((__builtin_expect(!(((PyUnicodeObject*)(value))->data.any), 0) ? __assert_rtn(__func__, "_tkinter.c", 976, "((PyUnicodeObject*)(value))->data.any") : (void)0), ((((PyUnicodeObject *)(value))->data.any))));
        size = ((__builtin_expect(!(((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_tkinter.c", 977, "PyUnicode_Check(value)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)value)->state.ready)), 0) ? __assert_rtn(__func__, "_tkinter.c", 977, "PyUnicode_IS_READY(value)") : (void)0), ((PyASCIIObject *)(value))->length);
        kind = ((__builtin_expect(!(((((((PyObject*)(value))->ob_type))->tp_flags & ((1L<<28))) != 0)), 0) ? __assert_rtn(__func__, "_tkinter.c", 978, "PyUnicode_Check(value)") : (void)0), (__builtin_expect(!((((PyASCIIObject*)value)->state.ready)), 0) ? __assert_rtn(__func__, "_tkinter.c", 978, "PyUnicode_IS_READY(value)") : (void)0), ((PyASCIIObject *)(value))->state.kind);
        allocsize = ((size_t)size) * sizeof(Tcl_UniChar);
        outbuf = (Tcl_UniChar*)Tcl_Alloc(allocsize);

        if (!outbuf) {
            PyErr_NoMemory();
            return ((void *)0);
        }
        for (i = 0; i < size; i++) {
            Py_UCS4 ch = ((Py_UCS4) ((kind) == PyUnicode_1BYTE_KIND ? ((const Py_UCS1 *)(inbuf))[(i)] : ((kind) == PyUnicode_2BYTE_KIND ? ((const Py_UCS2 *)(inbuf))[(i)] : ((const Py_UCS4 *)(inbuf))[(i)] ) ));



            if (ch >= 0x10000) {

                PyErr_Format(Tkinter_TclError,
                             "character U+%x is above the range "
                             "(U+0000-U+FFFF) allowed by Tcl",
                             ch);
                Tcl_Free((char *) outbuf);
                return ((void *)0);
            }

            outbuf[i] = ch;
        }
        result = Tcl_NewUnicodeObj(outbuf, size);
        Tcl_Free((char *) outbuf);
        return result;
    }
    else if(((value)->ob_type == &PyTclObject_Type)) {
        Tcl_Obj *v = ((PyTclObject*)value)->value;
        ++(v)->refCount;
        return v;
    }
    else {
        PyObject *v = PyObject_Str(value);
        if (!v)
            return 0;
        result = AsObj(v);
        do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
        return result;
    }
}

static PyObject*
FromObj(PyObject* tkapp, Tcl_Obj *value)
{
    PyObject *result = ((void *)0);
    TkappObject *app = (TkappObject*)tkapp;

    if (value->typePtr == ((void *)0)) {
        return PyUnicode_FromStringAndSize(value->bytes,
                                           value->length);
    }

    if (value->typePtr == app->BooleanType) {
        result = value->internalRep.longValue ? ((PyObject *) &_Py_TrueStruct) : ((PyObject *) &_Py_FalseStruct);
        ( ((PyObject*)(result))->ob_refcnt++);
        return result;
    }

    if (value->typePtr == app->ByteArrayType) {
        int size;
        char *data = (char*)Tcl_GetByteArrayFromObj(value, &size);
        return PyBytes_FromStringAndSize(data, size);
    }

    if (value->typePtr == app->DoubleType) {
        return PyFloat_FromDouble(value->internalRep.doubleValue);
    }

    if (value->typePtr == app->IntType) {
        return PyLong_FromLong(value->internalRep.longValue);
    }

    if (value->typePtr == app->ListType) {
        int size;
        int i, status;
        PyObject *elem;
        Tcl_Obj *tcl_elem;

        status = Tcl_ListObjLength((((TkappObject *) (tkapp))->interp), value, &size);
        if (status == 1)
            return Tkinter_Error(tkapp);
        result = PyTuple_New(size);
        if (!result)
            return ((void *)0);
        for (i = 0; i < size; i++) {
            status = Tcl_ListObjIndex((((TkappObject *) (tkapp))->interp),
                                      value, i, &tcl_elem);
            if (status == 1) {
                do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0);
                return Tkinter_Error(tkapp);
            }
            elem = FromObj(tkapp, tcl_elem);
            if (!elem) {
                do { if ( --((PyObject*)(result))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(result)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(result)))); } while (0);
                return ((void *)0);
            }
            PyTuple_SetItem(result, i, elem);
        }
        return result;
    }

    if (value->typePtr == app->ProcBodyType) {

    }

    if (value->typePtr == app->StringType) {

        return PyUnicode_FromKindAndData(
            PyUnicode_2BYTE_KIND, Tcl_GetUnicode(value),
            Tcl_GetCharLength(value));





    }

    return newPyTclObject(value);
}



static Tcl_Mutex call_mutex;

typedef struct Tkapp_CallEvent {
    Tcl_Event ev;
    TkappObject *self;
    PyObject *args;
    int flags;
    PyObject **res;
    PyObject **exc_type, **exc_value, **exc_tb;
    Tcl_Condition *done;
} Tkapp_CallEvent;


void
Tkapp_CallDeallocArgs(Tcl_Obj** objv, Tcl_Obj** objStore, int objc)
{
    int i;
    for (i = 0; i < objc; i++)
        do { if (--(objv[i])->refCount <= 0) TclFreeObj(objv[i]); } while(0);
    if (objv != objStore)
        Tcl_Free((char *) objv);
}




static Tcl_Obj**
Tkapp_CallArgs(PyObject *args, Tcl_Obj** objStore, int *pobjc)
{
    Tcl_Obj **objv = objStore;
    int objc = 0, i;
    if (args == ((void *)0))
                        ;

    else if (!((((((PyObject*)(args))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
        objv[0] = AsObj(args);
        if (objv[0] == 0)
            goto finally;
        objc = 1;
        ++(objv[0])->refCount;
    }
    else {
        objc = PyTuple_Size(args);

        if (objc > 64) {
            objv = (Tcl_Obj **)Tcl_Alloc(objc * sizeof(char *));
            if (objv == ((void *)0)) {
                PyErr_NoMemory();
                objc = 0;
                goto finally;
            }
        }

        for (i = 0; i < objc; i++) {
            PyObject *v = PyTuple_GetItem(args, i);
            if (v == (&_Py_NoneStruct)) {
                objc = i;
                break;
            }
            objv[i] = AsObj(v);
            if (!objv[i]) {


                objc = i;
                goto finally;
            }
            ++(objv[i])->refCount;
        }
    }
    *pobjc = objc;
    return objv;
finally:
    Tkapp_CallDeallocArgs(objv, objStore, objc);
    return ((void *)0);
}



static PyObject*
Tkapp_CallResult(TkappObject *self)
{
    PyObject *res = ((void *)0);
    if(self->wantobjects) {
        Tcl_Obj *value = Tcl_GetObjResult(self->interp);



        ++(value)->refCount;
        res = FromObj((PyObject*)self, value);
        do { if (--(value)->refCount <= 0) TclFreeObj(value); } while(0);
    } else {
        const char *s = Tcl_GetStringResult(self->interp);
        const char *p = s;

        res = PyUnicode_FromStringAndSize(s, (int)(p-s));
    }
    return res;
}







static int
Tkapp_CallProc(Tkapp_CallEvent *e, int flags)
{
    Tcl_Obj *objStore[64];
    Tcl_Obj **objv;
    int objc;
    int i;
    { PyThreadState *tstate = (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); PyEval_RestoreThread((tstate)); }
    objv = Tkapp_CallArgs(e->args, objStore, &objc);
    if (!objv) {
        PyErr_Fetch(e->exc_type, e->exc_value, e->exc_tb);
        *(e->res) = ((void *)0);
    }
    { PyThreadState *tstate = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate; }
    if (!objv)
        goto done;
    i = Tcl_EvalObjv(e->self->interp, objc, objv, e->flags);
    { PyThreadState *tstate = (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); PyEval_RestoreThread((tstate)); }
    if (i == 1) {
        *(e->res) = ((void *)0);
        *(e->exc_type) = ((void *)0);
        *(e->exc_tb) = ((void *)0);
        *(e->exc_value) = PyObject_CallFunction(
            Tkinter_TclError, "s",
            Tcl_GetStringResult(e->self->interp));
    }
    else {
        *(e->res) = Tkapp_CallResult(e->self);
    }
    { PyThreadState *tstate = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate; }

    Tkapp_CallDeallocArgs(objv, objStore, objc);
done:

    Tcl_MutexLock(&call_mutex);
    Tcl_ConditionNotify(e->done);
    Tcl_MutexUnlock(&call_mutex);
    return 1;
}
# 1262 "_tkinter.c"
static PyObject *
Tkapp_Call(PyObject *selfptr, PyObject *args)
{
    Tcl_Obj *objStore[64];
    Tcl_Obj **objv = ((void *)0);
    int objc, i;
    PyObject *res = ((void *)0);
    TkappObject *self = (TkappObject*)selfptr;
    int flags = 0x40000 | 0x20000;


    if (1 == PyTuple_Size(args)){
        PyObject* item = PyTuple_GetItem(args, 0);
        if (((((((PyObject*)(item))->ob_type))->tp_flags & ((1L<<26))) != 0))
            args = item;
    }

    if (self->threaded && self->thread_id != Tcl_GetCurrentThread()) {


        Tkapp_CallEvent *ev;
        Tcl_Condition cond = ((void *)0);
        PyObject *exc_type, *exc_value, *exc_tb;
        if (!WaitForMainloop(self))
            return ((void *)0);
        ev = (Tkapp_CallEvent*)Tcl_Alloc(sizeof(Tkapp_CallEvent));
        ev->ev.proc = (Tcl_EventProc*)Tkapp_CallProc;
        ev->self = self;
        ev->args = args;
        ev->res = &res;
        ev->exc_type = &exc_type;
        ev->exc_value = &exc_value;
        ev->exc_tb = &exc_tb;
        ev->done = &cond;

        Tkapp_ThreadSend(self, (Tcl_Event*)ev, &cond, &call_mutex);

        if (res == ((void *)0)) {
            if (exc_type)
                PyErr_Restore(exc_type, exc_value, exc_tb);
            else
                PyErr_SetObject(Tkinter_TclError, exc_value);
        }
        Tcl_ConditionFinalize(&cond);
    }
    else

    {

        objv = Tkapp_CallArgs(args, objStore, &objc);
        if (!objv)
            return ((void *)0);

        { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;

        i = Tcl_EvalObjv(self->interp, objc, objv, flags);

        PyEval_RestoreThread(_save); }

        if (i == 1)
            Tkinter_Error(selfptr);
        else
            res = Tkapp_CallResult(self);

        (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); }

        Tkapp_CallDeallocArgs(objv, objStore, objc);
    }
    return res;
}


static PyObject *
Tkapp_GlobalCall(PyObject *self, PyObject *args)
{






    char *cmd;
    PyObject *res = ((void *)0);

    if (PyErr_WarnEx(PyExc_DeprecationWarning,
                     "globalcall is deprecated and will be removed in 3.4",
                     1) < 0)
        return 0;

    if (((TkappObject *)self)->threaded && ((TkappObject *)self)->thread_id != Tcl_GetCurrentThread()) { PyErr_SetString(PyExc_RuntimeError, "Calling Tcl from different appartment"); return 0; };

    cmd = Merge(args);
    if (cmd) {
        int err;
        { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
        err = Tcl_GlobalEval((((TkappObject *) (self))->interp), cmd);
        PyEval_RestoreThread(_save); }
        if (err == 1)
            res = Tkinter_Error(self);
        else
            res = PyUnicode_FromString(Tcl_GetStringResult((((TkappObject *) (self))->interp)));
        (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); }
        Tcl_Free(cmd);
    }

    return res;
}

static PyObject *
Tkapp_Eval(PyObject *self, PyObject *args)
{
    char *script;
    PyObject *res = ((void *)0);
    int err;

    if (!PyArg_ParseTuple(args, "s:eval", &script))
        return ((void *)0);

    if (((TkappObject *)self)->threaded && ((TkappObject *)self)->thread_id != Tcl_GetCurrentThread()) { PyErr_SetString(PyExc_RuntimeError, "Calling Tcl from different appartment"); return 0; };

    { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
    err = Tcl_Eval((((TkappObject *) (self))->interp), script);
    PyEval_RestoreThread(_save); }
    if (err == 1)
        res = Tkinter_Error(self);
    else
        res = PyUnicode_FromString(Tcl_GetStringResult((((TkappObject *) (self))->interp)));
    (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); }
    return res;
}

static PyObject *
Tkapp_GlobalEval(PyObject *self, PyObject *args)
{
    char *script;
    PyObject *res = ((void *)0);
    int err;

    if (PyErr_WarnEx(PyExc_DeprecationWarning,
                     "globaleval is deprecated and will be removed in 3.4",
                     1) < 0)
        return 0;

    if (!PyArg_ParseTuple(args, "s:globaleval", &script))
        return ((void *)0);

    if (((TkappObject *)self)->threaded && ((TkappObject *)self)->thread_id != Tcl_GetCurrentThread()) { PyErr_SetString(PyExc_RuntimeError, "Calling Tcl from different appartment"); return 0; };

    { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
    err = Tcl_GlobalEval((((TkappObject *) (self))->interp), script);
    PyEval_RestoreThread(_save); }
    if (err == 1)
        res = Tkinter_Error(self);
    else
        res = PyUnicode_FromString(Tcl_GetStringResult((((TkappObject *) (self))->interp)));
    (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); }
    return res;
}

static PyObject *
Tkapp_EvalFile(PyObject *self, PyObject *args)
{
    char *fileName;
    PyObject *res = ((void *)0);
    int err;

    if (!PyArg_ParseTuple(args, "s:evalfile", &fileName))
        return ((void *)0);

    if (((TkappObject *)self)->threaded && ((TkappObject *)self)->thread_id != Tcl_GetCurrentThread()) { PyErr_SetString(PyExc_RuntimeError, "Calling Tcl from different appartment"); return 0; };

    { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
    err = Tcl_EvalFile((((TkappObject *) (self))->interp), fileName);
    PyEval_RestoreThread(_save); }
    if (err == 1)
        res = Tkinter_Error(self);

    else
        res = PyUnicode_FromString(Tcl_GetStringResult((((TkappObject *) (self))->interp)));
    (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); }
    return res;
}

static PyObject *
Tkapp_Record(PyObject *self, PyObject *args)
{
    char *script;
    PyObject *res = ((void *)0);
    int err;

    if (!PyArg_ParseTuple(args, "s", &script))
        return ((void *)0);

    if (((TkappObject *)self)->threaded && ((TkappObject *)self)->thread_id != Tcl_GetCurrentThread()) { PyErr_SetString(PyExc_RuntimeError, "Calling Tcl from different appartment"); return 0; };

    { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
    err = Tcl_RecordAndEval((((TkappObject *) (self))->interp), script, 0x10000);
    PyEval_RestoreThread(_save); }
    if (err == 1)
        res = Tkinter_Error(self);
    else
        res = PyUnicode_FromString(Tcl_GetStringResult((((TkappObject *) (self))->interp)));
    (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); }
    return res;
}

static PyObject *
Tkapp_AddErrorInfo(PyObject *self, PyObject *args)
{
    char *msg;

    if (!PyArg_ParseTuple(args, "s:adderrorinfo", &msg))
        return ((void *)0);
    if (((TkappObject *)self)->threaded && ((TkappObject *)self)->thread_id != Tcl_GetCurrentThread()) { PyErr_SetString(PyExc_RuntimeError, "Calling Tcl from different appartment"); return 0; };

    { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
    Tcl_AddErrorInfo((((TkappObject *) (self))->interp), msg);
    (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); PyEval_RestoreThread(_save); }}

    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}





typedef PyObject* (*EventFunc)(PyObject*, PyObject *args, int flags);


static Tcl_Mutex var_mutex;

typedef struct VarEvent {
    Tcl_Event ev;
    PyObject *self;
    PyObject *args;
    int flags;
    EventFunc func;
    PyObject **res;
    PyObject **exc_type;
    PyObject **exc_val;
    Tcl_Condition *cond;
} VarEvent;


static int
varname_converter(PyObject *in, void *_out)
{
    char **out = (char**)_out;
    if (((((((PyObject*)(in))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
        *out = PyBytes_AsString(in);
        return 1;
    }
    if (((((((PyObject*)(in))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        *out = PyUnicode_AsUTF8(in);
        return 1;
    }
    if (((in)->ob_type == &PyTclObject_Type)) {
        *out = PyTclObject_TclString(in);
        return 1;
    }

    return 0;
}



static void
var_perform(VarEvent *ev)
{
    *(ev->res) = ev->func(ev->self, ev->args, ev->flags);
    if (!*(ev->res)) {
        PyObject *exc, *val, *tb;
        PyErr_Fetch(&exc, &val, &tb);
        PyErr_NormalizeException(&exc, &val, &tb);
        *(ev->exc_type) = exc;
        *(ev->exc_val) = val;
        do { if ( --((PyObject*)(tb))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(tb)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(tb)))); } while (0);
    }

}

static int
var_proc(VarEvent* ev, int flags)
{
    { PyThreadState *tstate = (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); PyEval_RestoreThread((tstate)); }
    var_perform(ev);
    Tcl_MutexLock(&var_mutex);
    Tcl_ConditionNotify(ev->cond);
    Tcl_MutexUnlock(&var_mutex);
    { PyThreadState *tstate = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate; }
    return 1;
}



static PyObject*
var_invoke(EventFunc func, PyObject *selfptr, PyObject *args, int flags)
{

    TkappObject *self = (TkappObject*)selfptr;
    if (self->threaded && self->thread_id != Tcl_GetCurrentThread()) {
        TkappObject *self = (TkappObject*)selfptr;
        VarEvent *ev;
        PyObject *res, *exc_type, *exc_val;
        Tcl_Condition cond = ((void *)0);




        if (!WaitForMainloop(self))
            return ((void *)0);

        ev = (VarEvent*)Tcl_Alloc(sizeof(VarEvent));

        ev->self = selfptr;
        ev->args = args;
        ev->flags = flags;
        ev->func = func;
        ev->res = &res;
        ev->exc_type = &exc_type;
        ev->exc_val = &exc_val;
        ev->cond = &cond;
        ev->ev.proc = (Tcl_EventProc*)var_proc;
        Tkapp_ThreadSend(self, (Tcl_Event*)ev, &cond, &var_mutex);
        Tcl_ConditionFinalize(&cond);
        if (!res) {
            PyErr_SetObject(exc_type, exc_val);
            do { if ( --((PyObject*)(exc_type))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(exc_type)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(exc_type)))); } while (0);
            do { if ( --((PyObject*)(exc_val))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(exc_val)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(exc_val)))); } while (0);
            return ((void *)0);
        }
        return res;
    }


    return func(selfptr, args, flags);
}

static PyObject *
SetVar(PyObject *self, PyObject *args, int flags)
{
    char *name1, *name2;
    PyObject *newValue;
    PyObject *res = ((void *)0);
    Tcl_Obj *newval, *ok;

    if (PyArg_ParseTuple(args, "O&O:setvar",
                         varname_converter, &name1, &newValue)) {

        newval = AsObj(newValue);
        if (newval == ((void *)0))
            return ((void *)0);
        { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
        ok = Tcl_SetVar2Ex((((TkappObject *) (self))->interp), name1, ((void *)0),
                           newval, flags);
        PyEval_RestoreThread(_save); }
        if (!ok)
            Tkinter_Error(self);
        else {
            res = (&_Py_NoneStruct);
            ( ((PyObject*)(res))->ob_refcnt++);
        }
        (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); }
    }
    else {
        PyErr_Clear();
        if (PyArg_ParseTuple(args, "ssO:setvar",
                             &name1, &name2, &newValue)) {

            newval = AsObj(newValue);
            { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
            ok = Tcl_SetVar2Ex((((TkappObject *) (self))->interp), name1, name2, newval, flags);
            PyEval_RestoreThread(_save); }
            if (!ok)
                Tkinter_Error(self);
            else {
                res = (&_Py_NoneStruct);
                ( ((PyObject*)(res))->ob_refcnt++);
            }
            (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); }
        }
        else {
            return ((void *)0);
        }
    }
    return res;
}

static PyObject *
Tkapp_SetVar(PyObject *self, PyObject *args)
{
    return var_invoke(SetVar, self, args, 0x200);
}

static PyObject *
Tkapp_GlobalSetVar(PyObject *self, PyObject *args)
{
    return var_invoke(SetVar, self, args, 0x200 | 1);
}



static PyObject *
GetVar(PyObject *self, PyObject *args, int flags)
{
    char *name1, *name2=((void *)0);
    PyObject *res = ((void *)0);
    Tcl_Obj *tres;

    if (!PyArg_ParseTuple(args, "O&|s:getvar",
                          varname_converter, &name1, &name2))
        return ((void *)0);

    { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
    tres = Tcl_GetVar2Ex((((TkappObject *) (self))->interp), name1, name2, flags);
    PyEval_RestoreThread(_save); }
    if (tres == ((void *)0)) {
        PyErr_SetString(Tkinter_TclError, Tcl_GetStringResult((((TkappObject *) (self))->interp)));
    } else {
        if (((TkappObject*)self)->wantobjects) {
            res = FromObj(self, tres);
        }
        else {
            res = PyUnicode_FromString(Tcl_GetString(tres));
        }
    }
    (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); }
    return res;
}

static PyObject *
Tkapp_GetVar(PyObject *self, PyObject *args)
{
    return var_invoke(GetVar, self, args, 0x200);
}

static PyObject *
Tkapp_GlobalGetVar(PyObject *self, PyObject *args)
{
    return var_invoke(GetVar, self, args, 0x200 | 1);
}



static PyObject *
UnsetVar(PyObject *self, PyObject *args, int flags)
{
    char *name1, *name2=((void *)0);
    int code;
    PyObject *res = ((void *)0);

    if (!PyArg_ParseTuple(args, "s|s:unsetvar", &name1, &name2))
        return ((void *)0);

    { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
    code = Tcl_UnsetVar2((((TkappObject *) (self))->interp), name1, name2, flags);
    PyEval_RestoreThread(_save); }
    if (code == 1)
        res = Tkinter_Error(self);
    else {
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        res = (&_Py_NoneStruct);
    }
    (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); }
    return res;
}

static PyObject *
Tkapp_UnsetVar(PyObject *self, PyObject *args)
{
    return var_invoke(UnsetVar, self, args, 0x200);
}

static PyObject *
Tkapp_GlobalUnsetVar(PyObject *self, PyObject *args)
{
    return var_invoke(UnsetVar, self, args, 0x200 | 1);
}





static PyObject *
Tkapp_GetInt(PyObject *self, PyObject *args)
{
    char *s;
    int v;

    if (PyTuple_Size(args) == 1) {
        PyObject* o = PyTuple_GetItem(args, 0);
        if (((((((PyObject*)(o))->ob_type))->tp_flags & ((1L<<24))) != 0)) {
            ( ((PyObject*)(o))->ob_refcnt++);
            return o;
        }
    }
    if (!PyArg_ParseTuple(args, "s:getint", &s))
        return ((void *)0);
    if (Tcl_GetInt((((TkappObject *) (self))->interp), s, &v) == 1)
        return Tkinter_Error(self);
    return Py_BuildValue("i", v);
}

static PyObject *
Tkapp_GetDouble(PyObject *self, PyObject *args)
{
    char *s;
    double v;

    if (PyTuple_Size(args) == 1) {
        PyObject *o = PyTuple_GetItem(args, 0);
        if (((((PyObject*)(o))->ob_type) == (&PyFloat_Type) || PyType_IsSubtype((((PyObject*)(o))->ob_type), (&PyFloat_Type)))) {
            ( ((PyObject*)(o))->ob_refcnt++);
            return o;
        }
    }
    if (!PyArg_ParseTuple(args, "s:getdouble", &s))
        return ((void *)0);
    if (Tcl_GetDouble((((TkappObject *) (self))->interp), s, &v) == 1)
        return Tkinter_Error(self);
    return Py_BuildValue("d", v);
}

static PyObject *
Tkapp_GetBoolean(PyObject *self, PyObject *args)
{
    char *s;
    int v;

    if (PyTuple_Size(args) == 1) {
        PyObject *o = PyTuple_GetItem(args, 0);
        if (((((((PyObject*)(o))->ob_type))->tp_flags & ((1L<<24))) != 0)) {
            ( ((PyObject*)(o))->ob_refcnt++);
            return o;
        }
    }
    if (!PyArg_ParseTuple(args, "s:getboolean", &s))
        return ((void *)0);
    if (Tcl_GetBoolean((((TkappObject *) (self))->interp), s, &v) == 1)
        return Tkinter_Error(self);
    return PyBool_FromLong(v);
}

static PyObject *
Tkapp_ExprString(PyObject *self, PyObject *args)
{
    char *s;
    PyObject *res = ((void *)0);
    int retval;

    if (!PyArg_ParseTuple(args, "s:exprstring", &s))
        return ((void *)0);

    if (((TkappObject *)self)->threaded && ((TkappObject *)self)->thread_id != Tcl_GetCurrentThread()) { PyErr_SetString(PyExc_RuntimeError, "Calling Tcl from different appartment"); return 0; };

    { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
    retval = Tcl_ExprString((((TkappObject *) (self))->interp), s);
    PyEval_RestoreThread(_save); }
    if (retval == 1)
        res = Tkinter_Error(self);
    else
        res = Py_BuildValue("s", Tcl_GetStringResult((((TkappObject *) (self))->interp)));
    (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); }
    return res;
}

static PyObject *
Tkapp_ExprLong(PyObject *self, PyObject *args)
{
    char *s;
    PyObject *res = ((void *)0);
    int retval;
    long v;

    if (!PyArg_ParseTuple(args, "s:exprlong", &s))
        return ((void *)0);

    if (((TkappObject *)self)->threaded && ((TkappObject *)self)->thread_id != Tcl_GetCurrentThread()) { PyErr_SetString(PyExc_RuntimeError, "Calling Tcl from different appartment"); return 0; };

    { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
    retval = Tcl_ExprLong((((TkappObject *) (self))->interp), s, &v);
    PyEval_RestoreThread(_save); }
    if (retval == 1)
        res = Tkinter_Error(self);
    else
        res = Py_BuildValue("l", v);
    (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); }
    return res;
}

static PyObject *
Tkapp_ExprDouble(PyObject *self, PyObject *args)
{
    char *s;
    PyObject *res = ((void *)0);
    double v;
    int retval;

    if (!PyArg_ParseTuple(args, "s:exprdouble", &s))
        return ((void *)0);
    if (((TkappObject *)self)->threaded && ((TkappObject *)self)->thread_id != Tcl_GetCurrentThread()) { PyErr_SetString(PyExc_RuntimeError, "Calling Tcl from different appartment"); return 0; };
   
    { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
    retval = Tcl_ExprDouble((((TkappObject *) (self))->interp), s, &v);
    PyEval_RestoreThread(_save); }
   
    if (retval == 1)
        res = Tkinter_Error(self);
    else
        res = Py_BuildValue("d", v);
    (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); }
    return res;
}

static PyObject *
Tkapp_ExprBoolean(PyObject *self, PyObject *args)
{
    char *s;
    PyObject *res = ((void *)0);
    int retval;
    int v;

    if (!PyArg_ParseTuple(args, "s:exprboolean", &s))
        return ((void *)0);
    if (((TkappObject *)self)->threaded && ((TkappObject *)self)->thread_id != Tcl_GetCurrentThread()) { PyErr_SetString(PyExc_RuntimeError, "Calling Tcl from different appartment"); return 0; };
    { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
    retval = Tcl_ExprBoolean((((TkappObject *) (self))->interp), s, &v);
    PyEval_RestoreThread(_save); }
    if (retval == 1)
        res = Tkinter_Error(self);
    else
        res = Py_BuildValue("i", v);
    (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); }
    return res;
}



static PyObject *
Tkapp_SplitList(PyObject *self, PyObject *args)
{
    char *list;
    int argc;
    char **argv;
    PyObject *v;
    int i;

    if (PyTuple_Size(args) == 1) {
        v = PyTuple_GetItem(args, 0);
        if (((((((PyObject*)(v))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
            ( ((PyObject*)(v))->ob_refcnt++);
            return v;
        }
    }
    if (!PyArg_ParseTuple(args, "et:splitlist", "utf-8", &list))
        return ((void *)0);

    if (Tcl_SplitList((((TkappObject *) (self))->interp), list,
                      &argc, &argv) == 1) {
        PyMem_Free(list);
        return Tkinter_Error(self);
    }

    if (!(v = PyTuple_New(argc)))
        goto finally;

    for (i = 0; i < argc; i++) {
        PyObject *s = PyUnicode_FromString(argv[i]);
        if (!s || PyTuple_SetItem(v, i, s)) {
            do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
            v = ((void *)0);
            goto finally;
        }
    }

  finally:
    Tcl_Free((char *) argv);
    PyMem_Free(list);
    return v;
}

static PyObject *
Tkapp_Split(PyObject *self, PyObject *args)
{
    PyObject *v;
    char *list;

    if (PyTuple_Size(args) == 1) {
        PyObject* o = PyTuple_GetItem(args, 0);
        if (((((((PyObject*)(o))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
            o = SplitObj(o);
            return o;
        }
    }
    if (!PyArg_ParseTuple(args, "et:split", "utf-8", &list))
        return ((void *)0);
    v = Split(list);
    PyMem_Free(list);
    return v;
}

static PyObject *
Tkapp_Merge(PyObject *self, PyObject *args)
{
    char *s;
    PyObject *res = ((void *)0);

    if (PyErr_WarnEx(PyExc_DeprecationWarning,
                     "merge is deprecated and will be removed in 3.4",
                     1) < 0)
        return 0;

    s = Merge(args);

    if (s) {
        res = PyUnicode_FromString(s);
        Tcl_Free(s);
    }

    return res;
}






typedef struct {
    PyObject *self;
    PyObject *func;
} PythonCmd_ClientData;

static int
PythonCmd_Error(Tcl_Interp *interp)
{
    errorInCmd = 1;
    PyErr_Fetch(&excInCmd, &valInCmd, &trbInCmd);
    { PyThreadState *tstate = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate; }
    return 1;
}




static int
PythonCmd(ClientData clientData, Tcl_Interp *interp, int argc, char *argv[])
{
    PythonCmd_ClientData *data = (PythonCmd_ClientData *)clientData;
    PyObject *func, *arg, *res;
    int i, rv;
    Tcl_Obj *obj_res;

    { PyThreadState *tstate = (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); PyEval_RestoreThread((tstate)); }




    func = data->func;


    if (!(arg = PyTuple_New(argc - 1)))
        return PythonCmd_Error(interp);

    for (i = 0; i < (argc - 1); i++) {
        PyObject *s = PyUnicode_FromString(argv[i + 1]);
        if (!s) {

            if (PyErr_ExceptionMatches(PyExc_UnicodeDecodeError) &&
                !strcmp(argv[i + 1], "\xC0\x80")) {
                PyErr_Clear();

                s = PyUnicode_FromString("\0");
            } else {
                do { if ( --((PyObject*)(arg))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(arg)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(arg)))); } while (0);
                return PythonCmd_Error(interp);
            }
        }
        if (PyTuple_SetItem(arg, i, s)) {
            do { if ( --((PyObject*)(arg))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(arg)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(arg)))); } while (0);
            return PythonCmd_Error(interp);
        }
    }
    res = PyEval_CallObjectWithKeywords(func, arg, (PyObject *)((void *)0));
    do { if ( --((PyObject*)(arg))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(arg)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(arg)))); } while (0);

    if (res == ((void *)0))
        return PythonCmd_Error(interp);

    obj_res = AsObj(res);
    if (obj_res == ((void *)0)) {
        do { if ( --((PyObject*)(res))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(res)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(res)))); } while (0);
        return PythonCmd_Error(interp);
    }
    else {
        Tcl_SetObjResult(interp, obj_res);
        rv = 0;
    }

    do { if ( --((PyObject*)(res))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(res)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(res)))); } while (0);

    { PyThreadState *tstate = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate; }

    return rv;
}

static void
PythonCmdDelete(ClientData clientData)
{
    PythonCmd_ClientData *data = (PythonCmd_ClientData *)clientData;

    { PyThreadState *tstate = (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); PyEval_RestoreThread((tstate)); }
    do { if ((data->self) == ((void *)0)) ; else do { if ( --((PyObject*)(data->self))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(data->self)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(data->self)))); } while (0); } while (0);
    do { if ((data->func) == ((void *)0)) ; else do { if ( --((PyObject*)(data->func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(data->func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(data->func)))); } while (0); } while (0);
    free(data);
    { PyThreadState *tstate = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate; }
}





static Tcl_Mutex command_mutex;

typedef struct CommandEvent{
    Tcl_Event ev;
    Tcl_Interp* interp;
    char *name;
    int create;
    int *status;
    ClientData *data;
    Tcl_Condition *done;
} CommandEvent;

static int
Tkapp_CommandProc(CommandEvent *ev, int flags)
{
    if (ev->create)
        *ev->status = Tcl_CreateCommand(
            ev->interp, ev->name, PythonCmd,
            ev->data, PythonCmdDelete) == ((void *)0);
    else
        *ev->status = Tcl_DeleteCommand(ev->interp, ev->name);
    Tcl_MutexLock(&command_mutex);
    Tcl_ConditionNotify(ev->done);
    Tcl_MutexUnlock(&command_mutex);
    return 1;
}


static PyObject *
Tkapp_CreateCommand(PyObject *selfptr, PyObject *args)
{
    TkappObject *self = (TkappObject*)selfptr;
    PythonCmd_ClientData *data;
    char *cmdName;
    PyObject *func;
    int err;

    if (!PyArg_ParseTuple(args, "sO:createcommand", &cmdName, &func))
        return ((void *)0);
    if (!PyCallable_Check(func)) {
        PyErr_SetString(PyExc_TypeError, "command not callable");
        return ((void *)0);
    }


    if (self->threaded && self->thread_id != Tcl_GetCurrentThread() &&
        !WaitForMainloop(self))
        return ((void *)0);


    data = ( ((size_t)(1) > ((Py_ssize_t)(((size_t)-1)>>1)) / sizeof(PythonCmd_ClientData)) ? ((void *)0) : ( (PythonCmd_ClientData *) ((size_t)((1) * sizeof(PythonCmd_ClientData)) > (size_t)((Py_ssize_t)(((size_t)-1)>>1)) ? ((void *)0) : malloc(((1) * sizeof(PythonCmd_ClientData)) ? ((1) * sizeof(PythonCmd_ClientData)) : 1)) ) );
    if (!data)
        return PyErr_NoMemory();
    ( ((PyObject*)(self))->ob_refcnt++);
    ( ((PyObject*)(func))->ob_refcnt++);
    data->self = selfptr;
    data->func = func;

    if (self->threaded && self->thread_id != Tcl_GetCurrentThread()) {
        Tcl_Condition cond = ((void *)0);
        CommandEvent *ev = (CommandEvent*)Tcl_Alloc(sizeof(CommandEvent));
        ev->ev.proc = (Tcl_EventProc*)Tkapp_CommandProc;
        ev->interp = self->interp;
        ev->create = 1;
        ev->name = cmdName;
        ev->data = (ClientData)data;
        ev->status = &err;
        ev->done = &cond;
        Tkapp_ThreadSend(self, (Tcl_Event*)ev, &cond, &command_mutex);
        Tcl_ConditionFinalize(&cond);
    }
    else

    {
        { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
        err = Tcl_CreateCommand(
            (((TkappObject *) (self))->interp), cmdName, PythonCmd,
            (ClientData)data, PythonCmdDelete) == ((void *)0);
        (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); PyEval_RestoreThread(_save); }}
    }
    if (err) {
        PyErr_SetString(Tkinter_TclError, "can't create Tcl command");
        free(data);
        return ((void *)0);
    }

    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}



static PyObject *
Tkapp_DeleteCommand(PyObject *selfptr, PyObject *args)
{
    TkappObject *self = (TkappObject*)selfptr;
    char *cmdName;
    int err;

    if (!PyArg_ParseTuple(args, "s:deletecommand", &cmdName))
        return ((void *)0);


    if (self->threaded && self->thread_id != Tcl_GetCurrentThread()) {
        Tcl_Condition cond = ((void *)0);
        CommandEvent *ev;
        ev = (CommandEvent*)Tcl_Alloc(sizeof(CommandEvent));
        ev->ev.proc = (Tcl_EventProc*)Tkapp_CommandProc;
        ev->interp = self->interp;
        ev->create = 0;
        ev->name = cmdName;
        ev->status = &err;
        ev->done = &cond;
        Tkapp_ThreadSend(self, (Tcl_Event*)ev, &cond,
                         &command_mutex);
        Tcl_ConditionFinalize(&cond);
    }
    else

    {
        { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
        err = Tcl_DeleteCommand(self->interp, cmdName);
        (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); PyEval_RestoreThread(_save); }}
    }
    if (err == -1) {
        PyErr_SetString(Tkinter_TclError, "can't delete Tcl command");
        return ((void *)0);
    }
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}






typedef struct _fhcdata {
    PyObject *func;
    PyObject *file;
    int id;
    struct _fhcdata *next;
} FileHandler_ClientData;

static FileHandler_ClientData *HeadFHCD;

static FileHandler_ClientData *
NewFHCD(PyObject *func, PyObject *file, int id)
{
    FileHandler_ClientData *p;
    p = ( ((size_t)(1) > ((Py_ssize_t)(((size_t)-1)>>1)) / sizeof(FileHandler_ClientData)) ? ((void *)0) : ( (FileHandler_ClientData *) ((size_t)((1) * sizeof(FileHandler_ClientData)) > (size_t)((Py_ssize_t)(((size_t)-1)>>1)) ? ((void *)0) : malloc(((1) * sizeof(FileHandler_ClientData)) ? ((1) * sizeof(FileHandler_ClientData)) : 1)) ) );
    if (p != ((void *)0)) {
        do { if ((func) == ((void *)0)) ; else ( ((PyObject*)(func))->ob_refcnt++); } while (0);
        do { if ((file) == ((void *)0)) ; else ( ((PyObject*)(file))->ob_refcnt++); } while (0);
        p->func = func;
        p->file = file;
        p->id = id;
        p->next = HeadFHCD;
        HeadFHCD = p;
    }
    return p;
}

static void
DeleteFHCD(int id)
{
    FileHandler_ClientData *p, **pp;

    pp = &HeadFHCD;
    while ((p = *pp) != ((void *)0)) {
        if (p->id == id) {
            *pp = p->next;
            do { if ((p->func) == ((void *)0)) ; else do { if ( --((PyObject*)(p->func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(p->func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(p->func)))); } while (0); } while (0);
            do { if ((p->file) == ((void *)0)) ; else do { if ( --((PyObject*)(p->file))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(p->file)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(p->file)))); } while (0); } while (0);
            free(p);
        }
        else
            pp = &p->next;
    }
}

static void
FileHandler(ClientData clientData, int mask)
{
    FileHandler_ClientData *data = (FileHandler_ClientData *)clientData;
    PyObject *func, *file, *arg, *res;

    { PyThreadState *tstate = (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); PyEval_RestoreThread((tstate)); }
    func = data->func;
    file = data->file;

    arg = Py_BuildValue("(Oi)", file, (long) mask);
    res = PyEval_CallObjectWithKeywords(func, arg, (PyObject *)((void *)0));
    do { if ( --((PyObject*)(arg))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(arg)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(arg)))); } while (0);

    if (res == ((void *)0)) {
        errorInCmd = 1;
        PyErr_Fetch(&excInCmd, &valInCmd, &trbInCmd);
    }
    do { if ((res) == ((void *)0)) ; else do { if ( --((PyObject*)(res))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(res)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(res)))); } while (0); } while (0);
    { PyThreadState *tstate = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate; }
}

static PyObject *
Tkapp_CreateFileHandler(PyObject *self, PyObject *args)

{
    FileHandler_ClientData *data;
    PyObject *file, *func;
    int mask, tfile;

    if (!PyArg_ParseTuple(args, "OiO:createfilehandler",
                          &file, &mask, &func))
        return ((void *)0);

    if (((TkappObject *)self)->threaded && ((TkappObject *)self)->thread_id != Tcl_GetCurrentThread()) { PyErr_SetString(PyExc_RuntimeError, "Calling Tcl from different appartment"); return 0; };

    tfile = PyObject_AsFileDescriptor(file);
    if (tfile < 0)
        return ((void *)0);
    if (!PyCallable_Check(func)) {
        PyErr_SetString(PyExc_TypeError, "bad argument list");
        return ((void *)0);
    }

    data = NewFHCD(func, file, tfile);
    if (data == ((void *)0))
        return ((void *)0);


    { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
    Tcl_CreateFileHandler(tfile, mask, FileHandler, (ClientData) data);
    (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); PyEval_RestoreThread(_save); }}
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static PyObject *
Tkapp_DeleteFileHandler(PyObject *self, PyObject *args)
{
    PyObject *file;
    int tfile;

    if (!PyArg_ParseTuple(args, "O:deletefilehandler", &file))
        return ((void *)0);

    if (((TkappObject *)self)->threaded && ((TkappObject *)self)->thread_id != Tcl_GetCurrentThread()) { PyErr_SetString(PyExc_RuntimeError, "Calling Tcl from different appartment"); return 0; };

    tfile = PyObject_AsFileDescriptor(file);
    if (tfile < 0)
        return ((void *)0);

    DeleteFHCD(tfile);


    { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
    Tcl_DeleteFileHandler(tfile);
    (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); PyEval_RestoreThread(_save); }}
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}





static PyTypeObject Tktt_Type;

typedef struct {
    PyObject ob_base;
    Tcl_TimerToken token;
    PyObject *func;
} TkttObject;

static PyObject *
Tktt_DeleteTimerHandler(PyObject *self, PyObject *args)
{
    TkttObject *v = (TkttObject *)self;
    PyObject *func = v->func;

    if (!PyArg_ParseTuple(args, ":deletetimerhandler"))
        return ((void *)0);
    if (v->token != ((void *)0)) {
        Tcl_DeleteTimerHandler(v->token);
        v->token = ((void *)0);
    }
    if (func != ((void *)0)) {
        v->func = ((void *)0);
        do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0);
        do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
    }
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static PyMethodDef Tktt_methods[] =
{
    {"deletetimerhandler", Tktt_DeleteTimerHandler, 0x0001},
    {((void *)0), ((void *)0)}
};

static TkttObject *
Tktt_New(PyObject *func)
{
    TkttObject *v;

    v = ( (TkttObject *) _PyObject_New(&Tktt_Type) );
    if (v == ((void *)0))
        return ((void *)0);

    ( ((PyObject*)(func))->ob_refcnt++);
    v->token = ((void *)0);
    v->func = func;


    ( ((PyObject*)(v))->ob_refcnt++);
    return v;
}

static void
Tktt_Dealloc(PyObject *self)
{
    TkttObject *v = (TkttObject *)self;
    PyObject *func = v->func;

    do { if ((func) == ((void *)0)) ; else do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0); } while (0);

    PyObject_Free(self);
}

static PyObject *
Tktt_Repr(PyObject *self)
{
    TkttObject *v = (TkttObject *)self;
    return PyUnicode_FromFormat("<tktimertoken at %p%s>",
                                v,
                                v->func == ((void *)0) ? ", handler deleted" : "");
}

static PyTypeObject Tktt_Type =
{
    { { 1, ((void *)0) }, 0 },
    "tktimertoken",
    sizeof(TkttObject),
    0,
    Tktt_Dealloc,
    0,
    0,
    0,
    0,
    Tktt_Repr,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    ( 0 | (1L<<18) | 0),
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    Tktt_methods,
};





static void
TimerHandler(ClientData clientData)
{
    TkttObject *v = (TkttObject *)clientData;
    PyObject *func = v->func;
    PyObject *res;

    if (func == ((void *)0))
        return;

    v->func = ((void *)0);

    { PyThreadState *tstate = (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); PyEval_RestoreThread((tstate)); }

    res = PyEval_CallObjectWithKeywords(func, ((void *)0), (PyObject *)((void *)0));
    do { if ( --((PyObject*)(func))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(func)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(func)))); } while (0);
    do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);

    if (res == ((void *)0)) {
        errorInCmd = 1;
        PyErr_Fetch(&excInCmd, &valInCmd, &trbInCmd);
    }
    else
        do { if ( --((PyObject*)(res))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(res)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(res)))); } while (0);

    { PyThreadState *tstate = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate; }
}

static PyObject *
Tkapp_CreateTimerHandler(PyObject *self, PyObject *args)
{
    int milliseconds;
    PyObject *func;
    TkttObject *v;

    if (!PyArg_ParseTuple(args, "iO:createtimerhandler",
                          &milliseconds, &func))
        return ((void *)0);
    if (!PyCallable_Check(func)) {
        PyErr_SetString(PyExc_TypeError, "bad argument list");
        return ((void *)0);
    }

    if (((TkappObject *)self)->threaded && ((TkappObject *)self)->thread_id != Tcl_GetCurrentThread()) { PyErr_SetString(PyExc_RuntimeError, "Calling Tcl from different appartment"); return 0; };

    v = Tktt_New(func);
    if (v) {
        v->token = Tcl_CreateTimerHandler(milliseconds, TimerHandler,
                                          (ClientData)v);
    }

    return (PyObject *) v;
}




static PyObject *
Tkapp_MainLoop(PyObject *selfptr, PyObject *args)
{
    int threshold = 0;
    TkappObject *self = (TkappObject*)selfptr;

    PyThreadState *tstate = PyThreadState_Get();


    if (!PyArg_ParseTuple(args, "|i:mainloop", &threshold))
        return ((void *)0);

    if (((TkappObject *)self)->threaded && ((TkappObject *)self)->thread_id != Tcl_GetCurrentThread()) { PyErr_SetString(PyExc_RuntimeError, "Calling Tcl from different appartment"); return 0; };
    self->dispatching = 1;

    quitMainLoop = 0;
    while (Tk_GetNumMainWindows() > threshold &&
           !quitMainLoop &&
           !errorInCmd)
    {
        int result;


        if (self->threaded) {

            { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
            result = Tcl_DoOneEvent(0);
            (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); PyEval_RestoreThread(_save); }}
        }
        else {
            { PyThreadState *_save; _save = PyEval_SaveThread();
            if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1);
            (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
            result = Tcl_DoOneEvent((1<<1));
            (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0);
            if(tcl_lock)PyThread_release_lock(tcl_lock);
            if (result == 0)
                Sleep(Tkinter_busywaitinterval);
            PyEval_RestoreThread(_save); }
        }




        if (PyErr_CheckSignals() != 0) {
            self->dispatching = 0;
            return ((void *)0);
        }
        if (result < 0)
            break;
    }
    self->dispatching = 0;
    quitMainLoop = 0;

    if (errorInCmd) {
        errorInCmd = 0;
        PyErr_Restore(excInCmd, valInCmd, trbInCmd);
        excInCmd = valInCmd = trbInCmd = ((void *)0);
        return ((void *)0);
    }
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static PyObject *
Tkapp_DoOneEvent(PyObject *self, PyObject *args)
{
    int flags = 0;
    int rv;

    if (!PyArg_ParseTuple(args, "|i:dooneevent", &flags))
        return ((void *)0);

    { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
    rv = Tcl_DoOneEvent(flags);
    (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); PyEval_RestoreThread(_save); }}
    return Py_BuildValue("i", rv);
}

static PyObject *
Tkapp_Quit(PyObject *self, PyObject *args)
{

    if (!PyArg_ParseTuple(args, ":quit"))
        return ((void *)0);

    quitMainLoop = 1;
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static PyObject *
Tkapp_InterpAddr(PyObject *self, PyObject *args)
{

    if (!PyArg_ParseTuple(args, ":interpaddr"))
        return ((void *)0);

    return PyLong_FromLong((long)(((TkappObject *) (self))->interp));
}

static PyObject *
Tkapp_TkInit(PyObject *self, PyObject *args)
{
    Tcl_Interp *interp = (((TkappObject *) (self))->interp);
    const char * _tk_exists = ((void *)0);
    int err;
# 2637 "_tkinter.c"
    if (((TkappObject *)self)->threaded && ((TkappObject *)self)->thread_id != Tcl_GetCurrentThread()) { PyErr_SetString(PyExc_RuntimeError, "Calling Tcl from different appartment"); return 0; };
    { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
    err = Tcl_Eval((((TkappObject *) (self))->interp), "info exists     tk_version");
    PyEval_RestoreThread(_save); }
    if (err == 1) {


        Tkinter_Error(self);
    } else {
        _tk_exists = Tcl_GetStringResult((((TkappObject *) (self))->interp));
    }
    (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); }
    if (err == 1) {
        return ((void *)0);
    }
    if (_tk_exists == ((void *)0) || strcmp(_tk_exists, "1") != 0) {
        if (Tk_Init(interp) == 1) {
            PyErr_SetString(Tkinter_TclError, Tcl_GetStringResult((((TkappObject *) (self))->interp)));



            return ((void *)0);
        }
    }
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static PyObject *
Tkapp_WantObjects(PyObject *self, PyObject *args)
{

    int wantobjects = -1;
    if (!PyArg_ParseTuple(args, "|i:wantobjects", &wantobjects))
        return ((void *)0);
    if (wantobjects == -1)
        return PyBool_FromLong(((TkappObject*)self)->wantobjects);
    ((TkappObject*)self)->wantobjects = wantobjects;

    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static PyObject *
Tkapp_WillDispatch(PyObject *self, PyObject *args)
{

    ((TkappObject*)self)->dispatching = 1;

    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}




static PyMethodDef Tkapp_methods[] =
{
    {"willdispatch", Tkapp_WillDispatch, 0x0004},
    {"wantobjects", Tkapp_WantObjects, 0x0001},
    {"call", Tkapp_Call, 0x0001},
    {"globalcall", Tkapp_GlobalCall, 0x0001},
    {"eval", Tkapp_Eval, 0x0001},
    {"globaleval", Tkapp_GlobalEval, 0x0001},
    {"evalfile", Tkapp_EvalFile, 0x0001},
    {"record", Tkapp_Record, 0x0001},
    {"adderrorinfo", Tkapp_AddErrorInfo, 0x0001},
    {"setvar", Tkapp_SetVar, 0x0001},
    {"globalsetvar", Tkapp_GlobalSetVar, 0x0001},
    {"getvar", Tkapp_GetVar, 0x0001},
    {"globalgetvar", Tkapp_GlobalGetVar, 0x0001},
    {"unsetvar", Tkapp_UnsetVar, 0x0001},
    {"globalunsetvar", Tkapp_GlobalUnsetVar, 0x0001},
    {"getint", Tkapp_GetInt, 0x0001},
    {"getdouble", Tkapp_GetDouble, 0x0001},
    {"getboolean", Tkapp_GetBoolean, 0x0001},
    {"exprstring", Tkapp_ExprString, 0x0001},
    {"exprlong", Tkapp_ExprLong, 0x0001},
    {"exprdouble", Tkapp_ExprDouble, 0x0001},
    {"exprboolean", Tkapp_ExprBoolean, 0x0001},
    {"splitlist", Tkapp_SplitList, 0x0001},
    {"split", Tkapp_Split, 0x0001},
    {"merge", Tkapp_Merge, 0x0001},
    {"createcommand", Tkapp_CreateCommand, 0x0001},
    {"deletecommand", Tkapp_DeleteCommand, 0x0001},

    {"createfilehandler", Tkapp_CreateFileHandler, 0x0001},
    {"deletefilehandler", Tkapp_DeleteFileHandler, 0x0001},

    {"createtimerhandler", Tkapp_CreateTimerHandler, 0x0001},
    {"mainloop", Tkapp_MainLoop, 0x0001},
    {"dooneevent", Tkapp_DoOneEvent, 0x0001},
    {"quit", Tkapp_Quit, 0x0001},
    {"interpaddr", Tkapp_InterpAddr, 0x0001},
    {"loadtk", Tkapp_TkInit, 0x0004},
    {((void *)0), ((void *)0)}
};





static void
Tkapp_Dealloc(PyObject *self)
{

    { PyThreadState *tstate = PyThreadState_Get(); { PyThreadState *_save; _save = PyEval_SaveThread(); if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1); (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = tstate;
    Tcl_DeleteInterp((((TkappObject *) (self))->interp));
    (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0); if(tcl_lock)PyThread_release_lock(tcl_lock); PyEval_RestoreThread(_save); }}
    PyObject_Free(self);
    DisableEventHook();
}

static PyTypeObject Tkapp_Type =
{
    { { 1, ((void *)0) }, 0 },
    "tkapp",
    sizeof(TkappObject),
    0,
    Tkapp_Dealloc,
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
    ( 0 | (1L<<18) | 0),
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    Tkapp_methods,
};





typedef struct {
    PyObject* tuple;
    int size;
    int maxsize;
} FlattenContext;

static int
_bump(FlattenContext* context, int size)
{



    int maxsize = context->maxsize * 2;

    if (maxsize < context->size + size)
        maxsize = context->size + size;

    context->maxsize = maxsize;

    return _PyTuple_Resize(&context->tuple, maxsize) >= 0;
}

static int
_flatten1(FlattenContext* context, PyObject* item, int depth)
{


    int i, size;

    if (depth > 1000) {
        PyErr_SetString(PyExc_ValueError,
                        "nesting too deep in _flatten");
        return 0;
    } else if (((((((PyObject*)(item))->ob_type))->tp_flags & ((1L<<25))) != 0)) {
        size = (((PyVarObject*)(item))->ob_size);

        if (context->size + size > context->maxsize &&
            !_bump(context, size))
            return 0;

        for (i = 0; i < size; i++) {
            PyObject *o = (((PyListObject *)(item))->ob_item[i]);
            if (((((((PyObject*)(o))->ob_type))->tp_flags & ((1L<<25))) != 0) || ((((((PyObject*)(o))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
                if (!_flatten1(context, o, depth + 1))
                    return 0;
            } else if (o != (&_Py_NoneStruct)) {
                if (context->size + 1 > context->maxsize &&
                    !_bump(context, 1))
                    return 0;
                ( ((PyObject*)(o))->ob_refcnt++);
                (((PyTupleObject *)(context->tuple))->ob_item[context->size++] = o);

            }
        }
    } else if (((((((PyObject*)(item))->ob_type))->tp_flags & ((1L<<26))) != 0)) {

        size = (((PyVarObject*)(item))->ob_size);
        if (context->size + size > context->maxsize &&
            !_bump(context, size))
            return 0;
        for (i = 0; i < size; i++) {
            PyObject *o = (((PyTupleObject *)(item))->ob_item[i]);
            if (((((((PyObject*)(o))->ob_type))->tp_flags & ((1L<<25))) != 0) || ((((((PyObject*)(o))->ob_type))->tp_flags & ((1L<<26))) != 0)) {
                if (!_flatten1(context, o, depth + 1))
                    return 0;
            } else if (o != (&_Py_NoneStruct)) {
                if (context->size + 1 > context->maxsize &&
                    !_bump(context, 1))
                    return 0;
                ( ((PyObject*)(o))->ob_refcnt++);
                (((PyTupleObject *)(context->tuple))->ob_item[context->size++] = o);

            }
        }
    } else {
        PyErr_SetString(PyExc_TypeError, "argument must be sequence");
        return 0;
    }
    return 1;
}

static PyObject *
Tkinter_Flatten(PyObject* self, PyObject* args)
{
    FlattenContext context;
    PyObject* item;

    if (!PyArg_ParseTuple(args, "O:_flatten", &item))
        return ((void *)0);

    context.maxsize = PySequence_Size(item);
    if (context.maxsize < 0)
        return ((void *)0);
    if (context.maxsize == 0)
        return PyTuple_New(0);

    context.tuple = PyTuple_New(context.maxsize);
    if (!context.tuple)
        return ((void *)0);

    context.size = 0;

    if (!_flatten1(&context, item,0))
        return ((void *)0);

    if (_PyTuple_Resize(&context.tuple, context.size))
        return ((void *)0);

    return context.tuple;
}

static PyObject *
Tkinter_Create(PyObject *self, PyObject *args)
{
    char *screenName = ((void *)0);
    char *baseName = ((void *)0);

    char *className = ((void *)0);
    int interactive = 0;
    int wantobjects = 0;
    int wantTk = 1;
    int sync = 0;
    char *use = ((void *)0);

    className = "Tk";

    if (!PyArg_ParseTuple(args, "|zssiiiiz:create",
                          &screenName, &baseName, &className,
                          &interactive, &wantobjects, &wantTk,
                          &sync, &use))
        return ((void *)0);

    return (PyObject *) Tkapp_New(screenName, className,
                                  interactive, wantobjects, wantTk,
                                  sync, use);
}

static PyObject *
Tkinter_setbusywaitinterval(PyObject *self, PyObject *args)
{
    int new_val;
    if (!PyArg_ParseTuple(args, "i:setbusywaitinterval", &new_val))
        return ((void *)0);
    if (new_val < 0) {
        PyErr_SetString(PyExc_ValueError,
                        "busywaitinterval must be >= 0");
        return ((void *)0);
    }
    Tkinter_busywaitinterval = new_val;
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static char setbusywaitinterval_doc[] =
"setbusywaitinterval(n) -> None\n\nSet the busy-wait interval in milliseconds between successive\ncalls to Tcl_DoOneEvent in a threaded Python interpreter.\nIt should be set to a divisor of the maximum time between\nframes in an animation.";






static PyObject *
Tkinter_getbusywaitinterval(PyObject *self, PyObject *args)
{
    return PyLong_FromLong(Tkinter_busywaitinterval);
}

static char getbusywaitinterval_doc[] =
"getbusywaitinterval() -> int\n\nReturn the current busy-wait interval between successive\ncalls to Tcl_DoOneEvent in a threaded Python interpreter.";




static PyMethodDef moduleMethods[] =
{
    {"_flatten", Tkinter_Flatten, 0x0001},
    {"create", Tkinter_Create, 0x0001},
    {"setbusywaitinterval",Tkinter_setbusywaitinterval, 0x0001,
                           setbusywaitinterval_doc},
    {"getbusywaitinterval",(PyCFunction)Tkinter_getbusywaitinterval,
                           0x0004, getbusywaitinterval_doc},
    {((void *)0), ((void *)0)}
};



static int stdin_ready = 0;


static void
MyFileProc(void *clientData, int mask)
{
    stdin_ready = 1;
}



static PyThreadState *event_tstate = ((void *)0);


static int
EventHook(void)
{

    int tfile;


    PyEval_RestoreThread(event_tstate);

    stdin_ready = 0;
    errorInCmd = 0;

    tfile = fileno(__stdinp);
    Tcl_CreateFileHandler(tfile, (1<<1), MyFileProc, ((void *)0));

    while (!errorInCmd && !stdin_ready) {
        int result;







        { PyThreadState *_save; _save = PyEval_SaveThread();
        if(tcl_lock)PyThread_acquire_lock(tcl_lock, 1);
        (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = event_tstate;

        result = Tcl_DoOneEvent((1<<1));

        (*(PyThreadState**)Tcl_GetThreadData(&state_key, sizeof(PyThreadState*))) = ((void *)0);
        if(tcl_lock)PyThread_release_lock(tcl_lock);
        if (result == 0)
            Sleep(Tkinter_busywaitinterval);
        PyEval_RestoreThread(_save); }




        if (result < 0)
            break;
    }

    Tcl_DeleteFileHandler(tfile);

    if (errorInCmd) {
        errorInCmd = 0;
        PyErr_Restore(excInCmd, valInCmd, trbInCmd);
        excInCmd = valInCmd = trbInCmd = ((void *)0);
        PyErr_Print();
    }

    PyEval_SaveThread();

    return 0;
}



static void
EnableEventHook(void)
{

    if (PyOS_InputHook == ((void *)0)) {

        event_tstate = PyThreadState_Get();

        PyOS_InputHook = EventHook;
    }

}

static void
DisableEventHook(void)
{

    if (Tk_GetNumMainWindows() == 0 && PyOS_InputHook == EventHook) {
        PyOS_InputHook = ((void *)0);
    }

}



static void
ins_long(PyObject *d, char *name, long val)
{
    PyObject *v = PyLong_FromLong(val);
    if (v) {
        PyDict_SetItemString(d, name, v);
        do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
    }
}
static void
ins_string(PyObject *d, char *name, char *val)
{
    PyObject *v = PyUnicode_FromString(val);
    if (v) {
        PyDict_SetItemString(d, name, v);
        do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
    }
}


static struct PyModuleDef _tkintermodule = {
    { { 1, ((void *)0) }, ((void *)0), 0, ((void *)0), },
    "_tkinter",
    ((void *)0),
    -1,
    moduleMethods,
    ((void *)0),
    ((void *)0),
    ((void *)0),
    ((void *)0)
};

PyObject*
PyInit__tkinter(void)
{
    PyObject *m, *d, *uexe, *cexe;

    if (PyType_Ready(&Tkapp_Type) < 0)
        return ((void *)0);


    tcl_lock = PyThread_allocate_lock();


    m = PyModule_Create2(&_tkintermodule, 1013);
    if (m == ((void *)0))
        return ((void *)0);

    d = PyModule_GetDict(m);
    Tkinter_TclError = PyErr_NewException("_tkinter.TclError", ((void *)0), ((void *)0));
    PyDict_SetItemString(d, "TclError", Tkinter_TclError);

    ins_long(d, "READABLE", (1<<1));
    ins_long(d, "WRITABLE", (1<<2));
    ins_long(d, "EXCEPTION", (1<<3));
    ins_long(d, "WINDOW_EVENTS", (1<<2));
    ins_long(d, "FILE_EVENTS", (1<<3));
    ins_long(d, "TIMER_EVENTS", (1<<4));
    ins_long(d, "IDLE_EVENTS", (1<<5));
    ins_long(d, "ALL_EVENTS", (~(1<<1)));
    ins_long(d, "DONT_WAIT", (1<<1));
    ins_string(d, "TK_VERSION", "8.5");
    ins_string(d, "TCL_VERSION", "8.5");

    PyDict_SetItemString(d, "TkappType", (PyObject *)&Tkapp_Type);

    if (PyType_Ready(&Tktt_Type) < 0) {
        do { if ( --((PyObject*)(m))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(m)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(m)))); } while (0);
        return ((void *)0);
    }
    PyDict_SetItemString(d, "TkttType", (PyObject *)&Tktt_Type);

    (((PyObject*)(&PyTclObject_Type))->ob_type) = &PyType_Type;
    PyDict_SetItemString(d, "Tcl_Obj", (PyObject *)&PyTclObject_Type);
# 3162 "_tkinter.c"
    uexe = PyUnicode_FromWideChar(Py_GetProgramName(), -1);
    if (uexe) {
        cexe = PyUnicode_EncodeFSDefault(uexe);
        if (cexe)
            Tcl_FindExecutable(PyBytes_AsString(cexe));
        do { if ((cexe) == ((void *)0)) ; else do { if ( --((PyObject*)(cexe))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(cexe)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(cexe)))); } while (0); } while (0);
        do { if ( --((PyObject*)(uexe))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(uexe)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(uexe)))); } while (0);
    }

    if (PyErr_Occurred()) {
        do { if ( --((PyObject*)(m))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(m)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(m)))); } while (0);
        return ((void *)0);
    }







    return m;
}
