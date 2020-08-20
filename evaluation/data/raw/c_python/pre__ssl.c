# 1 "_ssl.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "_ssl.c"
# 17 "_ssl.c"
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
# 18 "_ssl.c" 2


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
# 21 "_ssl.c" 2
# 43 "_ssl.c"
enum py_ssl_error {

    PY_SSL_ERROR_NONE,
    PY_SSL_ERROR_SSL,
    PY_SSL_ERROR_WANT_READ,
    PY_SSL_ERROR_WANT_WRITE,
    PY_SSL_ERROR_WANT_X509_LOOKUP,
    PY_SSL_ERROR_SYSCALL,
    PY_SSL_ERROR_ZERO_RETURN,
    PY_SSL_ERROR_WANT_CONNECT,

    PY_SSL_ERROR_EOF,
    PY_SSL_ERROR_NO_SOCKET,
    PY_SSL_ERROR_INVALID_ERROR_CODE
};

enum py_ssl_server_or_client {
    PY_SSL_CLIENT,
    PY_SSL_SERVER
};

enum py_ssl_cert_requirements {
    PY_SSL_CERT_NONE,
    PY_SSL_CERT_OPTIONAL,
    PY_SSL_CERT_REQUIRED
};

enum py_ssl_version {

    PY_SSL_VERSION_SSL2,

    PY_SSL_VERSION_SSL3=1,
    PY_SSL_VERSION_SSL23,
    PY_SSL_VERSION_TLS1
};

struct py_ssl_error_code {
    const char *mnemonic;
    int library, reason;
};

struct py_ssl_library_code {
    const char *library;
    int code;
};


# 1 "socketmodule.h" 1







# 1 "/usr/include/sys/socket.h" 1 3 4
# 75 "/usr/include/sys/socket.h" 3 4
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
# 76 "/usr/include/sys/socket.h" 2 3 4

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


# 9 "socketmodule.h" 2

# 1 "/usr/include/netinet/in.h" 1 3 4
# 307 "/usr/include/netinet/in.h" 3 4
struct in_addr {
 in_addr_t s_addr;
};
# 380 "/usr/include/netinet/in.h" 3 4
struct sockaddr_in {
 __uint8_t sin_len;
 sa_family_t sin_family;
 in_port_t sin_port;
 struct in_addr sin_addr;
 char sin_zero[8];
};
# 398 "/usr/include/netinet/in.h" 3 4
struct ip_opts {
 struct in_addr ip_dst;
 char ip_opts[40];
};
# 506 "/usr/include/netinet/in.h" 3 4
struct ip_mreq {
 struct in_addr imr_multiaddr;
 struct in_addr imr_interface;
};






struct ip_mreqn {
 struct in_addr imr_multiaddr;
 struct in_addr imr_address;
 int imr_ifindex;
};

#pragma pack(4)



struct ip_mreq_source {
 struct in_addr imr_multiaddr;
 struct in_addr imr_sourceaddr;
 struct in_addr imr_interface;
};





struct group_req {
 uint32_t gr_interface;
 struct sockaddr_storage gr_group;
};

struct group_source_req {
 uint32_t gsr_interface;
 struct sockaddr_storage gsr_group;
 struct sockaddr_storage gsr_source;
};
# 554 "/usr/include/netinet/in.h" 3 4
struct __msfilterreq {
 uint32_t msfr_ifindex;
 uint32_t msfr_fmode;
 uint32_t msfr_nsrcs;
 uint32_t __msfr_align;
 struct sockaddr_storage msfr_group;
 struct sockaddr_storage *msfr_srcs;
};



#pragma pack()
struct sockaddr;






int setipv4sourcefilter(int, struct in_addr, struct in_addr, uint32_t,
     uint32_t, struct in_addr *) __attribute__((visibility("default")));
int getipv4sourcefilter(int, struct in_addr, struct in_addr, uint32_t *,
     uint32_t *, struct in_addr *) __attribute__((visibility("default")));
int setsourcefilter(int, uint32_t, struct sockaddr *, socklen_t,
     uint32_t, uint32_t, struct sockaddr_storage *) __attribute__((visibility("default")));
int getsourcefilter(int, uint32_t, struct sockaddr *, socklen_t,
     uint32_t *, uint32_t *, struct sockaddr_storage *) __attribute__((visibility("default")));
# 617 "/usr/include/netinet/in.h" 3 4
struct in_pktinfo {
 unsigned int ipi_ifindex;
 struct in_addr ipi_spec_dst;
 struct in_addr ipi_addr;
};
# 661 "/usr/include/netinet/in.h" 3 4
# 1 "/usr/include/netinet6/in6.h" 1 3 4
# 158 "/usr/include/netinet6/in6.h" 3 4
struct in6_addr {
 union {
  __uint8_t __u6_addr8[16];
  __uint16_t __u6_addr16[8];
  __uint32_t __u6_addr32[4];
 } __u6_addr;
};
# 176 "/usr/include/netinet6/in6.h" 3 4
struct sockaddr_in6 {
 __uint8_t sin6_len;
 sa_family_t sin6_family;
 in_port_t sin6_port;
 __uint32_t sin6_flowinfo;
 struct in6_addr sin6_addr;
 __uint32_t sin6_scope_id;
};
# 218 "/usr/include/netinet6/in6.h" 3 4
extern const struct in6_addr in6addr_any;
extern const struct in6_addr in6addr_loopback;

extern const struct in6_addr in6addr_nodelocal_allnodes;
extern const struct in6_addr in6addr_linklocal_allnodes;
extern const struct in6_addr in6addr_linklocal_allrouters;
extern const struct in6_addr in6addr_linklocal_allv2routers;
# 526 "/usr/include/netinet6/in6.h" 3 4
struct ipv6_mreq {
 struct in6_addr ipv6mr_multiaddr;
 unsigned int ipv6mr_interface;
};




struct in6_pktinfo {
 struct in6_addr ipi6_addr;
 unsigned int ipi6_ifindex;
};




struct ip6_mtuinfo {
 struct sockaddr_in6 ip6m_addr;
 uint32_t ip6m_mtu;
};
# 621 "/usr/include/netinet6/in6.h" 3 4

struct cmsghdr;

extern int inet6_option_space(int);
extern int inet6_option_init(void *, struct cmsghdr **, int);
extern int inet6_option_append(struct cmsghdr *, const __uint8_t *,
 int, int);
extern __uint8_t *inet6_option_alloc(struct cmsghdr *, int, int, int);
extern int inet6_option_next(const struct cmsghdr *, __uint8_t **);
extern int inet6_option_find(const struct cmsghdr *, __uint8_t **, int);

extern size_t inet6_rthdr_space(int, int);
extern struct cmsghdr *inet6_rthdr_init(void *, int);
extern int inet6_rthdr_add(struct cmsghdr *, const struct in6_addr *,
  unsigned int);
extern int inet6_rthdr_lasthop(struct cmsghdr *, unsigned int);



extern int inet6_rthdr_segments(const struct cmsghdr *);
extern struct in6_addr *inet6_rthdr_getaddr(struct cmsghdr *, int);
extern int inet6_rthdr_getflags(const struct cmsghdr *, int);

extern int inet6_opt_init(void *, socklen_t);
extern int inet6_opt_append(void *, socklen_t, int, __uint8_t,
     socklen_t, __uint8_t, void **);
extern int inet6_opt_finish(void *, socklen_t, int);
extern int inet6_opt_set_val(void *, int, void *, socklen_t);

extern int inet6_opt_next(void *, socklen_t, int, __uint8_t *,
          socklen_t *, void **);
extern int inet6_opt_find(void *, socklen_t, int, __uint8_t,
     socklen_t *, void **);
extern int inet6_opt_get_val(void *, int, void *, socklen_t);
extern socklen_t inet6_rth_space(int, int);
extern void *inet6_rth_init(void *, socklen_t, int, int);
extern int inet6_rth_add(void *, const struct in6_addr *);
extern int inet6_rth_reverse(const void *, void *);
extern int inet6_rth_segments(const void *);
extern struct in6_addr *inet6_rth_getaddr(const void *, int);
extern void addrsel_policy_init(void);

# 662 "/usr/include/netinet/in.h" 2 3 4





int bindresvport(int, struct sockaddr_in *);
struct sockaddr;
int bindresvport_sa(int, struct sockaddr *);

# 11 "socketmodule.h" 2

# 1 "/usr/include/netinet/tcp.h" 1 3 4
# 71 "/usr/include/netinet/tcp.h" 3 4
typedef __uint32_t tcp_seq;
typedef __uint32_t tcp_cc;
# 81 "/usr/include/netinet/tcp.h" 3 4
struct tcphdr {
 unsigned short th_sport;
 unsigned short th_dport;
 tcp_seq th_seq;
 tcp_seq th_ack;

 unsigned int th_x2:4,
   th_off:4;





 unsigned char th_flags;
# 105 "/usr/include/netinet/tcp.h" 3 4
 unsigned short th_win;
 unsigned short th_sum;
 unsigned short th_urp;
};
# 13 "socketmodule.h" 2
# 36 "socketmodule.h"
# 1 "/usr/include/sys/un.h" 1 3 4
# 79 "/usr/include/sys/un.h" 3 4
struct sockaddr_un {
 unsigned char sun_len;
 sa_family_t sun_family;
 char sun_path[104];
};
# 37 "socketmodule.h" 2
# 63 "socketmodule.h"
# 1 "/usr/include/net/if.h" 1 3 4
# 101 "/usr/include/net/if.h" 3 4
# 1 "/usr/include/net/if_var.h" 1 3 4
# 71 "/usr/include/net/if_var.h" 3 4
# 1 "/usr/include/sys/queue.h" 1 3 4
# 72 "/usr/include/net/if_var.h" 2 3 4
# 129 "/usr/include/net/if_var.h" 3 4
struct net_event_data {
 u_int32_t if_family;
 u_int32_t if_unit;
 char if_name[16];
};



# 1 "/usr/include/sys/_structs.h" 1 3 4
# 112 "/usr/include/sys/_structs.h" 3 4
struct timeval32
{
 __int32_t tv_sec;
 __int32_t tv_usec;
};
# 138 "/usr/include/net/if_var.h" 2 3 4





#pragma pack(4)





struct if_data {

 u_char ifi_type;
 u_char ifi_typelen;
 u_char ifi_physical;
 u_char ifi_addrlen;
 u_char ifi_hdrlen;
 u_char ifi_recvquota;
 u_char ifi_xmitquota;
 u_char ifi_unused1;
 u_int32_t ifi_mtu;
 u_int32_t ifi_metric;
 u_int32_t ifi_baudrate;

 u_int32_t ifi_ipackets;
 u_int32_t ifi_ierrors;
 u_int32_t ifi_opackets;
 u_int32_t ifi_oerrors;
 u_int32_t ifi_collisions;
 u_int32_t ifi_ibytes;
 u_int32_t ifi_obytes;
 u_int32_t ifi_imcasts;
 u_int32_t ifi_omcasts;
 u_int32_t ifi_iqdrops;
 u_int32_t ifi_noproto;
 u_int32_t ifi_recvtiming;
 u_int32_t ifi_xmittiming;
 struct timeval32 ifi_lastchange;
 u_int32_t ifi_unused2;
 u_int32_t ifi_hwassist;
 u_int32_t ifi_reserved1;
 u_int32_t ifi_reserved2;
};





struct if_data64 {

 u_char ifi_type;
 u_char ifi_typelen;
 u_char ifi_physical;
 u_char ifi_addrlen;
 u_char ifi_hdrlen;
 u_char ifi_recvquota;
 u_char ifi_xmitquota;
 u_char ifi_unused1;
 u_int32_t ifi_mtu;
 u_int32_t ifi_metric;
 u_int64_t ifi_baudrate;

 u_int64_t ifi_ipackets;
 u_int64_t ifi_ierrors;
 u_int64_t ifi_opackets;
 u_int64_t ifi_oerrors;
 u_int64_t ifi_collisions;
 u_int64_t ifi_ibytes;
 u_int64_t ifi_obytes;
 u_int64_t ifi_imcasts;
 u_int64_t ifi_omcasts;
 u_int64_t ifi_iqdrops;
 u_int64_t ifi_noproto;
 u_int32_t ifi_recvtiming;
 u_int32_t ifi_xmittiming;
 struct timeval32 ifi_lastchange;
};


#pragma pack()




struct ifqueue {
 void *ifq_head;
 void *ifq_tail;
 int ifq_len;
 int ifq_maxlen;
 int ifq_drops;
};
# 102 "/usr/include/net/if.h" 2 3 4
# 166 "/usr/include/net/if.h" 3 4
struct if_msghdr {
 unsigned short ifm_msglen;
 unsigned char ifm_version;
 unsigned char ifm_type;
 int ifm_addrs;
 int ifm_flags;
 unsigned short ifm_index;
 struct if_data ifm_data;
};





struct ifa_msghdr {
 unsigned short ifam_msglen;
 unsigned char ifam_version;
 unsigned char ifam_type;
 int ifam_addrs;
 int ifam_flags;
 unsigned short ifam_index;
 int ifam_metric;
};





struct ifma_msghdr {
 unsigned short ifmam_msglen;
 unsigned char ifmam_version;
 unsigned char ifmam_type;
 int ifmam_addrs;
 int ifmam_flags;
 unsigned short ifmam_index;
};





struct if_msghdr2 {
 u_short ifm_msglen;
 u_char ifm_version;
 u_char ifm_type;
 int ifm_addrs;
 int ifm_flags;
 u_short ifm_index;
 int ifm_snd_len;
 int ifm_snd_maxlen;
 int ifm_snd_drops;
 int ifm_timer;
 struct if_data64 ifm_data;
};





struct ifma_msghdr2 {
 u_short ifmam_msglen;
 u_char ifmam_version;
 u_char ifmam_type;
 int ifmam_addrs;
 int ifmam_flags;
 u_short ifmam_index;
 int32_t ifmam_refcount;
};






struct ifdevmtu {
 int ifdm_current;
 int ifdm_min;
 int ifdm_max;
};

#pragma pack(4)
# 273 "/usr/include/net/if.h" 3 4
struct ifkpi {
 unsigned int ifk_module_id;
 unsigned int ifk_type;
 union {
  void *ifk_ptr;
  int ifk_value;
 } ifk_data;
};





#pragma pack()







struct ifreq {



 char ifr_name[16];
 union {
  struct sockaddr ifru_addr;
  struct sockaddr ifru_dstaddr;
  struct sockaddr ifru_broadaddr;
  short ifru_flags;
  int ifru_metric;
  int ifru_mtu;
  int ifru_phys;
  int ifru_media;
  int ifru_intval;
  caddr_t ifru_data;
  struct ifdevmtu ifru_devmtu;
  struct ifkpi ifru_kpi;
  u_int32_t ifru_wake_flags;
  u_int32_t ifru_route_refcnt;
  int ifru_cap[2];
 } ifr_ifru;
# 337 "/usr/include/net/if.h" 3 4
};






struct ifaliasreq {
 char ifra_name[16];
 struct sockaddr ifra_addr;
 struct sockaddr ifra_broadaddr;
 struct sockaddr ifra_mask;
};

struct rslvmulti_req {
     struct sockaddr *sa;
     struct sockaddr **llsa;
};

#pragma pack(4)

struct ifmediareq {
 char ifm_name[16];
 int ifm_current;
 int ifm_mask;
 int ifm_status;
 int ifm_active;
 int ifm_count;
 int *ifm_ulist;
};

#pragma pack()



#pragma pack(4)
struct ifdrv {
 char ifd_name[16];
 unsigned long ifd_cmd;
 size_t ifd_len;
 void *ifd_data;
};
#pragma pack()
# 390 "/usr/include/net/if.h" 3 4
struct ifstat {
 char ifs_name[16];
 char ascii[800 + 1];
};







#pragma pack(4)
struct ifconf {
 int ifc_len;
 union {
  caddr_t ifcu_buf;
  struct ifreq *ifcu_req;
 } ifc_ifcu;
};
#pragma pack()







struct kev_dl_proto_data {
     struct net_event_data link_data;
     u_int32_t proto_family;
     u_int32_t proto_remaining_count;
};




struct if_laddrreq {
 char iflr_name[16];
 unsigned int flags;

 unsigned int prefixlen;
 struct sockaddr_storage addr;
 struct sockaddr_storage dstaddr;
};



struct if_nameindex {
 unsigned int if_index;
 char *if_name;
};


unsigned int if_nametoindex(const char *);
char *if_indextoname(unsigned int, char *);
struct if_nameindex *if_nameindex(void);
void if_freenameindex(struct if_nameindex *);

# 64 "socketmodule.h" 2
# 84 "socketmodule.h"
# 1 "/usr/include/sys/sys_domain.h" 1 3 4
# 47 "/usr/include/sys/sys_domain.h" 3 4
struct sockaddr_sys
{
 u_char ss_len;
 u_char ss_family;
 u_int16_t ss_sysaddr;
 u_int32_t ss_reserved[7];
};
# 85 "socketmodule.h" 2


# 1 "/usr/include/sys/kern_control.h" 1 3 4
# 72 "/usr/include/sys/kern_control.h" 3 4
struct ctl_event_data {
    u_int32_t ctl_id;
    u_int32_t ctl_unit;
};
# 114 "/usr/include/sys/kern_control.h" 3 4
struct ctl_info {
    u_int32_t ctl_id;
    char ctl_name[96];
};
# 137 "/usr/include/sys/kern_control.h" 3 4
struct sockaddr_ctl {
    u_char sc_len;
    u_char sc_family;
    u_int16_t ss_sysaddr;
    u_int32_t sc_id;
    u_int32_t sc_unit;
    u_int32_t sc_reserved[5];
};
# 88 "socketmodule.h" 2
# 110 "socketmodule.h"
typedef int SOCKET_T;
# 123 "socketmodule.h"
typedef union sock_addr {
    struct sockaddr_in in;
    struct sockaddr sa;

    struct sockaddr_un un;





    struct sockaddr_in6 in6;
    struct sockaddr_storage storage;
# 149 "socketmodule.h"
    struct sockaddr_ctl ctl;

} sock_addr_t;





typedef struct {
    PyObject ob_base;
    SOCKET_T sock_fd;
    int sock_family;
    int sock_type;
    int sock_proto;
    PyObject *(*errorhandler)(void);


    double sock_timeout;

} PySocketSockObject;
# 221 "socketmodule.h"
typedef struct {
    PyTypeObject *Sock_Type;
    PyObject *error;
    PyObject *timeout_error;
} PySocketModule_APIObject;
# 91 "_ssl.c" 2

static PySocketModule_APIObject PySocketModule;


# 1 "/usr/include/poll.h" 1 3 4
# 23 "/usr/include/poll.h" 3 4
# 1 "/usr/include/sys/poll.h" 1 3 4
# 96 "/usr/include/sys/poll.h" 3 4
struct pollfd
{
 int fd;
 short events;
 short revents;
};

typedef unsigned int nfds_t;










extern int poll (struct pollfd *, nfds_t, int) __asm("_" "poll" );


# 24 "/usr/include/poll.h" 2 3 4
# 96 "_ssl.c" 2





# 1 "/usr/include/openssl/rsa.h" 1 3 4
# 64 "/usr/include/openssl/rsa.h" 3 4
# 1 "/usr/include/openssl/asn1.h" 1 3 4
# 65 "/usr/include/openssl/asn1.h" 3 4
# 1 "/usr/include/openssl/e_os2.h" 1 3 4
# 56 "/usr/include/openssl/e_os2.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 57 "/usr/include/openssl/e_os2.h" 2 3 4
# 66 "/usr/include/openssl/asn1.h" 2 3 4

# 1 "/usr/include/openssl/bio.h" 1 3 4
# 64 "/usr/include/openssl/bio.h" 3 4
# 1 "/usr/include/openssl/e_os2.h" 1 3 4
# 56 "/usr/include/openssl/e_os2.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 57 "/usr/include/openssl/e_os2.h" 2 3 4
# 65 "/usr/include/openssl/bio.h" 2 3 4






# 1 "/usr/include/openssl/crypto.h" 1 3 4
# 124 "/usr/include/openssl/crypto.h" 3 4
# 1 "/usr/include/openssl/e_os2.h" 1 3 4
# 56 "/usr/include/openssl/e_os2.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 57 "/usr/include/openssl/e_os2.h" 2 3 4
# 125 "/usr/include/openssl/crypto.h" 2 3 4





# 1 "/usr/include/openssl/stack.h" 1 3 4
# 68 "/usr/include/openssl/stack.h" 3 4
typedef struct stack_st
 {
 int num;
 char **data;
 int sorted;

 int num_alloc;
 int (*comp)(const char * const *, const char * const *);
 } STACK;




int sk_num(const STACK *) __attribute__((deprecated));
char *sk_value(const STACK *, int) __attribute__((deprecated));

char *sk_set(STACK *, int, char *) __attribute__((deprecated));

STACK *sk_new(int (*cmp)(const char * const *, const char * const *)) __attribute__((deprecated));
STACK *sk_new_null(void) __attribute__((deprecated));
void sk_free(STACK *) __attribute__((deprecated));
void sk_pop_free(STACK *st, void (*func)(void *)) __attribute__((deprecated));
int sk_insert(STACK *sk,char *data,int where) __attribute__((deprecated));
char *sk_delete(STACK *st,int loc) __attribute__((deprecated));
char *sk_delete_ptr(STACK *st, char *p) __attribute__((deprecated));
int sk_find(STACK *st,char *data) __attribute__((deprecated));
int sk_find_ex(STACK *st,char *data) __attribute__((deprecated));
int sk_push(STACK *st,char *data) __attribute__((deprecated));
int sk_unshift(STACK *st,char *data) __attribute__((deprecated));
char *sk_shift(STACK *st) __attribute__((deprecated));
char *sk_pop(STACK *st) __attribute__((deprecated));
void sk_zero(STACK *st) __attribute__((deprecated));
int (*sk_set_cmp_func(STACK *sk, int (*c)(const char * const *,
   const char * const *)))
   (const char * const *, const char * const *) __attribute__((deprecated));
STACK *sk_dup(STACK *st) __attribute__((deprecated));
void sk_sort(STACK *st) __attribute__((deprecated));
int sk_is_sorted(const STACK *st) __attribute__((deprecated));
# 131 "/usr/include/openssl/crypto.h" 2 3 4
# 1 "/usr/include/openssl/safestack.h" 1 3 4
# 132 "/usr/include/openssl/crypto.h" 2 3 4
# 1 "/usr/include/openssl/opensslv.h" 1 3 4
# 133 "/usr/include/openssl/crypto.h" 2 3 4
# 1 "/usr/include/openssl/ossl_typ.h" 1 3 4
# 58 "/usr/include/openssl/ossl_typ.h" 3 4
# 1 "/usr/include/openssl/e_os2.h" 1 3 4
# 56 "/usr/include/openssl/e_os2.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 57 "/usr/include/openssl/e_os2.h" 2 3 4
# 59 "/usr/include/openssl/ossl_typ.h" 2 3 4
# 79 "/usr/include/openssl/ossl_typ.h" 3 4
typedef struct asn1_string_st ASN1_INTEGER;
typedef struct asn1_string_st ASN1_ENUMERATED;
typedef struct asn1_string_st ASN1_BIT_STRING;
typedef struct asn1_string_st ASN1_OCTET_STRING;
typedef struct asn1_string_st ASN1_PRINTABLESTRING;
typedef struct asn1_string_st ASN1_T61STRING;
typedef struct asn1_string_st ASN1_IA5STRING;
typedef struct asn1_string_st ASN1_GENERALSTRING;
typedef struct asn1_string_st ASN1_UNIVERSALSTRING;
typedef struct asn1_string_st ASN1_BMPSTRING;
typedef struct asn1_string_st ASN1_UTCTIME;
typedef struct asn1_string_st ASN1_TIME;
typedef struct asn1_string_st ASN1_GENERALIZEDTIME;
typedef struct asn1_string_st ASN1_VISIBLESTRING;
typedef struct asn1_string_st ASN1_UTF8STRING;
typedef int ASN1_BOOLEAN;
typedef int ASN1_NULL;
# 110 "/usr/include/openssl/ossl_typ.h" 3 4
typedef struct bignum_st BIGNUM;
typedef struct bignum_ctx BN_CTX;
typedef struct bn_blinding_st BN_BLINDING;
typedef struct bn_mont_ctx_st BN_MONT_CTX;
typedef struct bn_recp_ctx_st BN_RECP_CTX;
typedef struct bn_gencb_st BN_GENCB;

typedef struct buf_mem_st BUF_MEM;

typedef struct evp_cipher_st EVP_CIPHER;
typedef struct evp_cipher_ctx_st EVP_CIPHER_CTX;
typedef struct env_md_st EVP_MD;
typedef struct env_md_ctx_st EVP_MD_CTX;
typedef struct evp_pkey_st EVP_PKEY;

typedef struct dh_st DH;
typedef struct dh_method DH_METHOD;

typedef struct dsa_st DSA;
typedef struct dsa_method DSA_METHOD;

typedef struct rsa_st RSA;
typedef struct rsa_meth_st RSA_METHOD;

typedef struct rand_meth_st RAND_METHOD;

typedef struct ecdh_method ECDH_METHOD;
typedef struct ecdsa_method ECDSA_METHOD;

typedef struct x509_st X509;
typedef struct X509_algor_st X509_ALGOR;
typedef struct X509_crl_st X509_CRL;
typedef struct X509_name_st X509_NAME;
typedef struct x509_store_st X509_STORE;
typedef struct x509_store_ctx_st X509_STORE_CTX;
typedef struct ssl_st SSL;
typedef struct ssl_ctx_st SSL_CTX;

typedef struct v3_ext_ctx X509V3_CTX;
typedef struct conf_st CONF;

typedef struct store_st STORE;
typedef struct store_method_st STORE_METHOD;

typedef struct ui_st UI;
typedef struct ui_method_st UI_METHOD;

typedef struct st_ERR_FNS ERR_FNS;

typedef struct engine_st ENGINE;

typedef struct X509_POLICY_NODE_st X509_POLICY_NODE;
typedef struct X509_POLICY_LEVEL_st X509_POLICY_LEVEL;
typedef struct X509_POLICY_TREE_st X509_POLICY_TREE;
typedef struct X509_POLICY_CACHE_st X509_POLICY_CACHE;





typedef struct crypto_ex_data_st CRYPTO_EX_DATA;

typedef int CRYPTO_EX_new(void *parent, void *ptr, CRYPTO_EX_DATA *ad,
     int idx, long argl, void *argp);
typedef void CRYPTO_EX_free(void *parent, void *ptr, CRYPTO_EX_DATA *ad,
     int idx, long argl, void *argp);
typedef int CRYPTO_EX_dup(CRYPTO_EX_DATA *to, CRYPTO_EX_DATA *from, void *from_d,
     int idx, long argl, void *argp);

typedef struct ocsp_req_ctx_st OCSP_REQ_CTX;
typedef struct ocsp_response_st OCSP_RESPONSE;
typedef struct ocsp_responder_id_st OCSP_RESPID;
# 134 "/usr/include/openssl/crypto.h" 2 3 4







# 1 "/usr/include/openssl/symhacks.h" 1 3 4
# 58 "/usr/include/openssl/symhacks.h" 3 4
# 1 "/usr/include/openssl/e_os2.h" 1 3 4
# 56 "/usr/include/openssl/e_os2.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 57 "/usr/include/openssl/e_os2.h" 2 3 4
# 59 "/usr/include/openssl/symhacks.h" 2 3 4
# 142 "/usr/include/openssl/crypto.h" 2 3 4
# 173 "/usr/include/openssl/crypto.h" 3 4
typedef struct openssl_item_st
 {
 int code;
 void *value;
 size_t value_size;
 size_t *value_length;
 } OPENSSL_ITEM;
# 262 "/usr/include/openssl/crypto.h" 3 4
typedef struct
 {
 int references;
 struct CRYPTO_dynlock_value *data;
 } CRYPTO_dynlock;
# 289 "/usr/include/openssl/crypto.h" 3 4
typedef struct bio_st BIO_dummy;

struct crypto_ex_data_st
 {
 STACK *sk;
 int dummy;
 };




typedef struct crypto_ex_data_func_st
 {
 long argl;
 void *argp;
 CRYPTO_EX_new *new_func;
 CRYPTO_EX_free *free_func;
 CRYPTO_EX_dup *dup_func;
 } CRYPTO_EX_DATA_FUNCS;


# 352 "/usr/include/openssl/crypto.h" 3 4
void CRYPTO_malloc_debug_init(void) __attribute__((deprecated));

int CRYPTO_mem_ctrl(int mode) __attribute__((deprecated));
int CRYPTO_is_mem_check_on(void) __attribute__((deprecated));
# 382 "/usr/include/openssl/crypto.h" 3 4
const char *SSLeay_version(int type) __attribute__((deprecated));
unsigned long SSLeay(void) __attribute__((deprecated));

int OPENSSL_issetugid(void) __attribute__((deprecated));


typedef struct st_CRYPTO_EX_DATA_IMPL CRYPTO_EX_DATA_IMPL;

const CRYPTO_EX_DATA_IMPL *CRYPTO_get_ex_data_implementation(void) __attribute__((deprecated));

int CRYPTO_set_ex_data_implementation(const CRYPTO_EX_DATA_IMPL *i) __attribute__((deprecated));

int CRYPTO_ex_data_new_class(void) __attribute__((deprecated));

int CRYPTO_get_ex_new_index(int class_index, long argl, void *argp,
  CRYPTO_EX_new *new_func, CRYPTO_EX_dup *dup_func,
  CRYPTO_EX_free *free_func) __attribute__((deprecated));


int CRYPTO_new_ex_data(int class_index, void *obj, CRYPTO_EX_DATA *ad) __attribute__((deprecated));
int CRYPTO_dup_ex_data(int class_index, CRYPTO_EX_DATA *to,
  CRYPTO_EX_DATA *from) __attribute__((deprecated));
void CRYPTO_free_ex_data(int class_index, void *obj, CRYPTO_EX_DATA *ad) __attribute__((deprecated));


int CRYPTO_set_ex_data(CRYPTO_EX_DATA *ad, int idx, void *val) __attribute__((deprecated));
void *CRYPTO_get_ex_data(const CRYPTO_EX_DATA *ad,int idx) __attribute__((deprecated));


void CRYPTO_cleanup_all_ex_data(void) __attribute__((deprecated));

int CRYPTO_get_new_lockid(char *name) __attribute__((deprecated));

int CRYPTO_num_locks(void) __attribute__((deprecated));
void CRYPTO_lock(int mode, int type,const char *file,int line) __attribute__((deprecated));
void CRYPTO_set_locking_callback(void (*func)(int mode,int type,
           const char *file,int line)) __attribute__((deprecated));
void (*CRYPTO_get_locking_callback(void))(int mode,int type,const char *file,
  int line) __attribute__((deprecated));
void CRYPTO_set_add_lock_callback(int (*func)(int *num,int mount,int type,
           const char *file, int line)) __attribute__((deprecated));
int (*CRYPTO_get_add_lock_callback(void))(int *num,int mount,int type,
       const char *file,int line) __attribute__((deprecated));
void CRYPTO_set_id_callback(unsigned long (*func)(void)) __attribute__((deprecated));
unsigned long (*CRYPTO_get_id_callback(void))(void) __attribute__((deprecated));
unsigned long CRYPTO_thread_id(void) __attribute__((deprecated));
const char *CRYPTO_get_lock_name(int type) __attribute__((deprecated));
int CRYPTO_add_lock(int *pointer,int amount,int type, const char *file,
      int line) __attribute__((deprecated));

void int_CRYPTO_set_do_dynlock_callback(
 void (*do_dynlock_cb)(int mode, int type, const char *file, int line)) __attribute__((deprecated));

int CRYPTO_get_new_dynlockid(void) __attribute__((deprecated));
void CRYPTO_destroy_dynlockid(int i) __attribute__((deprecated));
struct CRYPTO_dynlock_value *CRYPTO_get_dynlock_value(int i) __attribute__((deprecated));
void CRYPTO_set_dynlock_create_callback(struct CRYPTO_dynlock_value *(*dyn_create_function)(const char *file, int line)) __attribute__((deprecated));
void CRYPTO_set_dynlock_lock_callback(void (*dyn_lock_function)(int mode, struct CRYPTO_dynlock_value *l, const char *file, int line)) __attribute__((deprecated));
void CRYPTO_set_dynlock_destroy_callback(void (*dyn_destroy_function)(struct CRYPTO_dynlock_value *l, const char *file, int line)) __attribute__((deprecated));
struct CRYPTO_dynlock_value *(*CRYPTO_get_dynlock_create_callback(void))(const char *file,int line) __attribute__((deprecated));
void (*CRYPTO_get_dynlock_lock_callback(void))(int mode, struct CRYPTO_dynlock_value *l, const char *file,int line) __attribute__((deprecated));
void (*CRYPTO_get_dynlock_destroy_callback(void))(struct CRYPTO_dynlock_value *l, const char *file,int line) __attribute__((deprecated));



int CRYPTO_set_mem_functions(void *(*m)(size_t),void *(*r)(void *,size_t), void (*f)(void *)) __attribute__((deprecated));
int CRYPTO_set_locked_mem_functions(void *(*m)(size_t), void (*free_func)(void *)) __attribute__((deprecated));
int CRYPTO_set_mem_ex_functions(void *(*m)(size_t,const char *,int),
                                void *(*r)(void *,size_t,const char *,int),
                                void (*f)(void *)) __attribute__((deprecated));
int CRYPTO_set_locked_mem_ex_functions(void *(*m)(size_t,const char *,int),
                                       void (*free_func)(void *)) __attribute__((deprecated));
int CRYPTO_set_mem_debug_functions(void (*m)(void *,int,const char *,int,int),
       void (*r)(void *,void *,int,const char *,int,int),
       void (*f)(void *,int),
       void (*so)(long),
       long (*go)(void)) __attribute__((deprecated));
void CRYPTO_set_mem_info_functions(
 int (*push_info_fn)(const char *info, const char *file, int line),
 int (*pop_info_fn)(void),
 int (*remove_all_info_fn)(void)) __attribute__((deprecated));
void CRYPTO_get_mem_functions(void *(**m)(size_t),void *(**r)(void *, size_t), void (**f)(void *)) __attribute__((deprecated));
void CRYPTO_get_locked_mem_functions(void *(**m)(size_t), void (**f)(void *)) __attribute__((deprecated));
void CRYPTO_get_mem_ex_functions(void *(**m)(size_t,const char *,int),
                                 void *(**r)(void *, size_t,const char *,int),
                                 void (**f)(void *)) __attribute__((deprecated));
void CRYPTO_get_locked_mem_ex_functions(void *(**m)(size_t,const char *,int),
                                        void (**f)(void *)) __attribute__((deprecated));
void CRYPTO_get_mem_debug_functions(void (**m)(void *,int,const char *,int,int),
        void (**r)(void *,void *,int,const char *,int,int),
        void (**f)(void *,int),
        void (**so)(long),
        long (**go)(void)) __attribute__((deprecated));

void *CRYPTO_malloc_locked(int num, const char *file, int line) __attribute__((deprecated));
void CRYPTO_free_locked(void *) __attribute__((deprecated));
void *CRYPTO_malloc(int num, const char *file, int line) __attribute__((deprecated));
char *CRYPTO_strdup(const char *str, const char *file, int line) __attribute__((deprecated));
void CRYPTO_free(void *) __attribute__((deprecated));
void *CRYPTO_realloc(void *addr,int num, const char *file, int line) __attribute__((deprecated));
void *CRYPTO_realloc_clean(void *addr,int old_num,int num,const char *file,
      int line) __attribute__((deprecated));
void *CRYPTO_remalloc(void *addr,int num, const char *file, int line) __attribute__((deprecated));

void OPENSSL_cleanse(void *ptr, size_t len) __attribute__((deprecated));

void CRYPTO_set_mem_debug_options(long bits) __attribute__((deprecated));
long CRYPTO_get_mem_debug_options(void) __attribute__((deprecated));



int CRYPTO_push_info_(const char *info, const char *file, int line) __attribute__((deprecated));
int CRYPTO_pop_info(void) __attribute__((deprecated));
int CRYPTO_remove_all_info(void) __attribute__((deprecated));
# 505 "/usr/include/openssl/crypto.h" 3 4
void CRYPTO_dbg_malloc(void *addr,int num,const char *file,int line,int before_p) __attribute__((deprecated));
void CRYPTO_dbg_realloc(void *addr1,void *addr2,int num,const char *file,int line,int before_p) __attribute__((deprecated));
void CRYPTO_dbg_free(void *addr,int before_p) __attribute__((deprecated));
# 516 "/usr/include/openssl/crypto.h" 3 4
void CRYPTO_dbg_set_options(long bits) __attribute__((deprecated));
long CRYPTO_dbg_get_options(void) __attribute__((deprecated));

int CRYPTO_dbg_push_info(const char *info, const char *file, int line) __attribute__((deprecated));
int CRYPTO_dbg_pop_info(void) __attribute__((deprecated));
int CRYPTO_dbg_remove_all_info(void) __attribute__((deprecated));


void CRYPTO_mem_leaks_fp(FILE *) __attribute__((deprecated));

void CRYPTO_mem_leaks(struct bio_st *bio) __attribute__((deprecated));

typedef void *CRYPTO_MEM_LEAK_CB(unsigned long, const char *, int, int, void *);
void CRYPTO_mem_leaks_cb(CRYPTO_MEM_LEAK_CB *cb) __attribute__((deprecated));


void OpenSSLDie(const char *file,int line,const char *assertion) __attribute__((deprecated));


unsigned long *OPENSSL_ia32cap_loc(void) __attribute__((deprecated));

int OPENSSL_isservice(void) __attribute__((deprecated));
# 597 "/usr/include/openssl/crypto.h" 3 4
void ERR_load_CRYPTO_strings(void) __attribute__((deprecated));


void OPENSSL_init(void) __attribute__((deprecated));
# 72 "/usr/include/openssl/bio.h" 2 3 4
# 205 "/usr/include/openssl/bio.h" 3 4
typedef struct bio_st BIO;

void BIO_set_flags(BIO *b, int flags) __attribute__((deprecated));
int BIO_test_flags(const BIO *b, int flags) __attribute__((deprecated));
void BIO_clear_flags(BIO *b, int flags) __attribute__((deprecated));
# 259 "/usr/include/openssl/bio.h" 3 4
long (*BIO_get_callback(const BIO *b)) (struct bio_st *,int,const char *,int, long,long) __attribute__((deprecated));
void BIO_set_callback(BIO *b,
 long (*callback)(struct bio_st *,int,const char *,int, long,long)) __attribute__((deprecated));
char *BIO_get_callback_arg(const BIO *b) __attribute__((deprecated));
void BIO_set_callback_arg(BIO *b, char *arg) __attribute__((deprecated));

const char * BIO_method_name(const BIO *b) __attribute__((deprecated));
int BIO_method_type(const BIO *b) __attribute__((deprecated));

typedef void bio_info_cb(struct bio_st *, int, const char *, int, long, long);


typedef struct bio_method_st
 {
 int type;
 const char *name;
 int (*bwrite)(BIO *, const char *, int);
 int (*bread)(BIO *, char *, int);
 int (*bputs)(BIO *, const char *);
 int (*bgets)(BIO *, char *, int);
 long (*ctrl)(BIO *, int, long, void *);
 int (*create)(BIO *);
 int (*destroy)(BIO *);
        long (*callback_ctrl)(BIO *, int, bio_info_cb *);
 } BIO_METHOD;
# 300 "/usr/include/openssl/bio.h" 3 4
struct bio_st
 {
 BIO_METHOD *method;

 long (*callback)(struct bio_st *,int,const char *,int, long,long);
 char *cb_arg;

 int init;
 int shutdown;
 int flags;
 int retry_reason;
 int num;
 void *ptr;
 struct bio_st *next_bio;
 struct bio_st *prev_bio;
 int references;
 unsigned long num_read;
 unsigned long num_write;

 CRYPTO_EX_DATA ex_data;
 };



typedef struct bio_f_buffer_ctx_struct
 {

 int ibuf_size;
 int obuf_size;

 char *ibuf;
 int ibuf_len;
 int ibuf_off;

 char *obuf;
 int obuf_len;
 int obuf_off;
 } BIO_F_BUFFER_CTX;
# 517 "/usr/include/openssl/bio.h" 3 4
size_t BIO_ctrl_pending(BIO *b) __attribute__((deprecated));
size_t BIO_ctrl_wpending(BIO *b) __attribute__((deprecated));
# 536 "/usr/include/openssl/bio.h" 3 4
size_t BIO_ctrl_get_write_guarantee(BIO *b) __attribute__((deprecated));
size_t BIO_ctrl_get_read_request(BIO *b) __attribute__((deprecated));
int BIO_ctrl_reset_read_request(BIO *b) __attribute__((deprecated));
# 557 "/usr/include/openssl/bio.h" 3 4
int BIO_set_ex_data(BIO *bio,int idx,void *data) __attribute__((deprecated));
void *BIO_get_ex_data(BIO *bio,int idx) __attribute__((deprecated));
int BIO_get_ex_new_index(long argl, void *argp, CRYPTO_EX_new *new_func,
 CRYPTO_EX_dup *dup_func, CRYPTO_EX_free *free_func) __attribute__((deprecated));
unsigned long BIO_number_read(BIO *bio) __attribute__((deprecated));
unsigned long BIO_number_written(BIO *bio) __attribute__((deprecated));
# 573 "/usr/include/openssl/bio.h" 3 4
BIO_METHOD *BIO_s_file(void ) __attribute__((deprecated));
BIO *BIO_new_file(const char *filename, const char *mode) __attribute__((deprecated));
BIO *BIO_new_fp(FILE *stream, int close_flag) __attribute__((deprecated));





BIO * BIO_new(BIO_METHOD *type) __attribute__((deprecated));
int BIO_set(BIO *a,BIO_METHOD *type) __attribute__((deprecated));
int BIO_free(BIO *a) __attribute__((deprecated));
void BIO_vfree(BIO *a) __attribute__((deprecated));
int BIO_read(BIO *b, void *data, int len) __attribute__((deprecated));
int BIO_gets(BIO *bp,char *buf, int size) __attribute__((deprecated));
int BIO_write(BIO *b, const void *data, int len) __attribute__((deprecated));
int BIO_puts(BIO *bp,const char *buf) __attribute__((deprecated));
int BIO_indent(BIO *b,int indent,int max) __attribute__((deprecated));
long BIO_ctrl(BIO *bp,int cmd,long larg,void *parg) __attribute__((deprecated));
long BIO_callback_ctrl(BIO *b, int cmd, void (*fp)(struct bio_st *, int, const char *, int, long, long)) __attribute__((deprecated));
char * BIO_ptr_ctrl(BIO *bp,int cmd,long larg) __attribute__((deprecated));
long BIO_int_ctrl(BIO *bp,int cmd,long larg,int iarg) __attribute__((deprecated));
BIO * BIO_push(BIO *b,BIO *append) __attribute__((deprecated));
BIO * BIO_pop(BIO *b) __attribute__((deprecated));
void BIO_free_all(BIO *a) __attribute__((deprecated));
BIO * BIO_find_type(BIO *b,int bio_type) __attribute__((deprecated));
BIO * BIO_next(BIO *b) __attribute__((deprecated));
BIO * BIO_get_retry_BIO(BIO *bio, int *reason) __attribute__((deprecated));
int BIO_get_retry_reason(BIO *bio) __attribute__((deprecated));
BIO * BIO_dup_chain(BIO *in) __attribute__((deprecated));

int BIO_nread0(BIO *bio, char **buf) __attribute__((deprecated));
int BIO_nread(BIO *bio, char **buf, int num) __attribute__((deprecated));
int BIO_nwrite0(BIO *bio, char **buf) __attribute__((deprecated));
int BIO_nwrite(BIO *bio, char **buf, int num) __attribute__((deprecated));


long BIO_debug_callback(BIO *bio,int cmd,const char *argp,int argi,
 long argl,long ret) __attribute__((deprecated));





BIO_METHOD *BIO_s_mem(void) __attribute__((deprecated));
BIO *BIO_new_mem_buf(void *buf, int len) __attribute__((deprecated));
BIO_METHOD *BIO_s_socket(void) __attribute__((deprecated));
BIO_METHOD *BIO_s_connect(void) __attribute__((deprecated));
BIO_METHOD *BIO_s_accept(void) __attribute__((deprecated));
BIO_METHOD *BIO_s_fd(void) __attribute__((deprecated));

BIO_METHOD *BIO_s_log(void) __attribute__((deprecated));

BIO_METHOD *BIO_s_bio(void) __attribute__((deprecated));
BIO_METHOD *BIO_s_null(void) __attribute__((deprecated));
BIO_METHOD *BIO_f_null(void) __attribute__((deprecated));
BIO_METHOD *BIO_f_buffer(void) __attribute__((deprecated));



BIO_METHOD *BIO_f_nbio_test(void) __attribute__((deprecated));

BIO_METHOD *BIO_s_datagram(void) __attribute__((deprecated));




int BIO_sock_should_retry(int i) __attribute__((deprecated));
int BIO_sock_non_fatal_error(int error) __attribute__((deprecated));
int BIO_dgram_non_fatal_error(int error) __attribute__((deprecated));

int BIO_fd_should_retry(int i) __attribute__((deprecated));
int BIO_fd_non_fatal_error(int error) __attribute__((deprecated));
int BIO_dump_cb(int (*cb)(const void *data, size_t len, void *u),
  void *u, const char *s, int len) __attribute__((deprecated));
int BIO_dump_indent_cb(int (*cb)(const void *data, size_t len, void *u),
         void *u, const char *s, int len, int indent) __attribute__((deprecated));
int BIO_dump(BIO *b,const char *bytes,int len) __attribute__((deprecated));
int BIO_dump_indent(BIO *b,const char *bytes,int len,int indent) __attribute__((deprecated));

int BIO_dump_fp(FILE *fp, const char *s, int len) __attribute__((deprecated));
int BIO_dump_indent_fp(FILE *fp, const char *s, int len, int indent) __attribute__((deprecated));

struct hostent *BIO_gethostbyname(const char *name) __attribute__((deprecated));
# 664 "/usr/include/openssl/bio.h" 3 4
int BIO_sock_error(int sock) __attribute__((deprecated));
int BIO_socket_ioctl(int fd, long type, void *arg) __attribute__((deprecated));
int BIO_socket_nbio(int fd,int mode) __attribute__((deprecated));
int BIO_get_port(const char *str, unsigned short *port_ptr) __attribute__((deprecated));
int BIO_get_host_ip(const char *str, unsigned char *ip) __attribute__((deprecated));
int BIO_get_accept_socket(char *host_port,int mode) __attribute__((deprecated));
int BIO_accept(int sock,char **ip_port) __attribute__((deprecated));
int BIO_sock_init(void ) __attribute__((deprecated));
void BIO_sock_cleanup(void) __attribute__((deprecated));
int BIO_set_tcp_ndelay(int sock,int turn_on) __attribute__((deprecated));

BIO *BIO_new_socket(int sock, int close_flag) __attribute__((deprecated));
BIO *BIO_new_dgram(int fd, int close_flag) __attribute__((deprecated));
BIO *BIO_new_fd(int fd, int close_flag) __attribute__((deprecated));
BIO *BIO_new_connect(char *host_port) __attribute__((deprecated));
BIO *BIO_new_accept(char *host_port) __attribute__((deprecated));

int BIO_new_bio_pair(BIO **bio1, size_t writebuf1,
 BIO **bio2, size_t writebuf2) __attribute__((deprecated));





void BIO_copy_next_retry(BIO *b) __attribute__((deprecated));
# 697 "/usr/include/openssl/bio.h" 3 4
int BIO_printf(BIO *bio, const char *format, ...)
 __attribute__((__format__(__printf__,2,3))) __attribute__((deprecated));
int BIO_vprintf(BIO *bio, const char *format, va_list args)
 __attribute__((__format__(__printf__,2,0))) __attribute__((deprecated));
int BIO_snprintf(char *buf, size_t n, const char *format, ...)
 __attribute__((__format__(__printf__,3,4))) __attribute__((deprecated));
int BIO_vsnprintf(char *buf, size_t n, const char *format, va_list args)
 __attribute__((__format__(__printf__,3,0))) __attribute__((deprecated));






void ERR_load_BIO_strings(void) __attribute__((deprecated));
# 68 "/usr/include/openssl/asn1.h" 2 3 4




# 1 "/usr/include/openssl/symhacks.h" 1 3 4
# 73 "/usr/include/openssl/asn1.h" 2 3 4



# 1 "/usr/include/openssl/bn.h" 1 3 4
# 77 "/usr/include/openssl/bn.h" 3 4
# 1 "/usr/include/openssl/e_os2.h" 1 3 4
# 56 "/usr/include/openssl/e_os2.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 57 "/usr/include/openssl/e_os2.h" 2 3 4
# 78 "/usr/include/openssl/bn.h" 2 3 4
# 290 "/usr/include/openssl/bn.h" 3 4
struct bignum_st
 {
 unsigned long long *d;
 int top;

 int dmax;
 int neg;
 int flags;
 };


struct bn_mont_ctx_st
 {
 int ri;
 BIGNUM RR;
 BIGNUM N;
 BIGNUM Ni;





 unsigned long long n0;

 int flags;
 };




struct bn_recp_ctx_st
 {
 BIGNUM N;
 BIGNUM Nr;
 int num_bits;
 int shift;
 int flags;
 };


struct bn_gencb_st
 {
 unsigned int ver;
 void *arg;
 union
  {

  void (*cb_1)(int, int, void *);

  int (*cb_2)(int, int, BN_GENCB *);
  } cb;
 };

int BN_GENCB_call(BN_GENCB *cb, int a, int b) __attribute__((deprecated));
# 401 "/usr/include/openssl/bn.h" 3 4
const BIGNUM *BN_value_one(void) __attribute__((deprecated));
char * BN_options(void) __attribute__((deprecated));
BN_CTX *BN_CTX_new(void) __attribute__((deprecated));

void BN_CTX_init(BN_CTX *c) __attribute__((deprecated));

void BN_CTX_free(BN_CTX *c) __attribute__((deprecated));
void BN_CTX_start(BN_CTX *ctx) __attribute__((deprecated));
BIGNUM *BN_CTX_get(BN_CTX *ctx) __attribute__((deprecated));
void BN_CTX_end(BN_CTX *ctx) __attribute__((deprecated));
int BN_rand(BIGNUM *rnd, int bits, int top,int bottom) __attribute__((deprecated));
int BN_pseudo_rand(BIGNUM *rnd, int bits, int top,int bottom) __attribute__((deprecated));
int BN_rand_range(BIGNUM *rnd, const BIGNUM *range) __attribute__((deprecated));
int BN_pseudo_rand_range(BIGNUM *rnd, const BIGNUM *range) __attribute__((deprecated));
int BN_num_bits(const BIGNUM *a) __attribute__((deprecated));
int BN_num_bits_word(unsigned long long) __attribute__((deprecated));
BIGNUM *BN_new(void) __attribute__((deprecated));
void BN_init(BIGNUM *) __attribute__((deprecated));
void BN_clear_free(BIGNUM *a) __attribute__((deprecated));
BIGNUM *BN_copy(BIGNUM *a, const BIGNUM *b) __attribute__((deprecated));
void BN_swap(BIGNUM *a, BIGNUM *b) __attribute__((deprecated));
BIGNUM *BN_bin2bn(const unsigned char *s,int len,BIGNUM *ret) __attribute__((deprecated));
int BN_bn2bin(const BIGNUM *a, unsigned char *to) __attribute__((deprecated));
BIGNUM *BN_mpi2bn(const unsigned char *s,int len,BIGNUM *ret) __attribute__((deprecated));
int BN_bn2mpi(const BIGNUM *a, unsigned char *to) __attribute__((deprecated));
int BN_sub(BIGNUM *r, const BIGNUM *a, const BIGNUM *b) __attribute__((deprecated));
int BN_usub(BIGNUM *r, const BIGNUM *a, const BIGNUM *b) __attribute__((deprecated));
int BN_uadd(BIGNUM *r, const BIGNUM *a, const BIGNUM *b) __attribute__((deprecated));
int BN_add(BIGNUM *r, const BIGNUM *a, const BIGNUM *b) __attribute__((deprecated));
int BN_mul(BIGNUM *r, const BIGNUM *a, const BIGNUM *b, BN_CTX *ctx) __attribute__((deprecated));
int BN_sqr(BIGNUM *r, const BIGNUM *a,BN_CTX *ctx) __attribute__((deprecated));




void BN_set_negative(BIGNUM *b, int n) __attribute__((deprecated));






int BN_div(BIGNUM *dv, BIGNUM *rem, const BIGNUM *m, const BIGNUM *d,
 BN_CTX *ctx) __attribute__((deprecated));

int BN_nnmod(BIGNUM *r, const BIGNUM *m, const BIGNUM *d, BN_CTX *ctx) __attribute__((deprecated));
int BN_mod_add(BIGNUM *r, const BIGNUM *a, const BIGNUM *b, const BIGNUM *m, BN_CTX *ctx) __attribute__((deprecated));
int BN_mod_add_quick(BIGNUM *r, const BIGNUM *a, const BIGNUM *b, const BIGNUM *m) __attribute__((deprecated));
int BN_mod_sub(BIGNUM *r, const BIGNUM *a, const BIGNUM *b, const BIGNUM *m, BN_CTX *ctx) __attribute__((deprecated));
int BN_mod_sub_quick(BIGNUM *r, const BIGNUM *a, const BIGNUM *b, const BIGNUM *m) __attribute__((deprecated));
int BN_mod_mul(BIGNUM *r, const BIGNUM *a, const BIGNUM *b,
 const BIGNUM *m, BN_CTX *ctx) __attribute__((deprecated));
int BN_mod_sqr(BIGNUM *r, const BIGNUM *a, const BIGNUM *m, BN_CTX *ctx) __attribute__((deprecated));
int BN_mod_lshift1(BIGNUM *r, const BIGNUM *a, const BIGNUM *m, BN_CTX *ctx) __attribute__((deprecated));
int BN_mod_lshift1_quick(BIGNUM *r, const BIGNUM *a, const BIGNUM *m) __attribute__((deprecated));
int BN_mod_lshift(BIGNUM *r, const BIGNUM *a, int n, const BIGNUM *m, BN_CTX *ctx) __attribute__((deprecated));
int BN_mod_lshift_quick(BIGNUM *r, const BIGNUM *a, int n, const BIGNUM *m) __attribute__((deprecated));

unsigned long long BN_mod_word(const BIGNUM *a, unsigned long long w) __attribute__((deprecated));
unsigned long long BN_div_word(BIGNUM *a, unsigned long long w) __attribute__((deprecated));
int BN_mul_word(BIGNUM *a, unsigned long long w) __attribute__((deprecated));
int BN_add_word(BIGNUM *a, unsigned long long w) __attribute__((deprecated));
int BN_sub_word(BIGNUM *a, unsigned long long w) __attribute__((deprecated));
int BN_set_word(BIGNUM *a, unsigned long long w) __attribute__((deprecated));
unsigned long long BN_get_word(const BIGNUM *a) __attribute__((deprecated));

int BN_cmp(const BIGNUM *a, const BIGNUM *b) __attribute__((deprecated));
void BN_free(BIGNUM *a) __attribute__((deprecated));
int BN_is_bit_set(const BIGNUM *a, int n) __attribute__((deprecated));
int BN_lshift(BIGNUM *r, const BIGNUM *a, int n) __attribute__((deprecated));
int BN_lshift1(BIGNUM *r, const BIGNUM *a) __attribute__((deprecated));
int BN_exp(BIGNUM *r, const BIGNUM *a, const BIGNUM *p,BN_CTX *ctx) __attribute__((deprecated));

int BN_mod_exp(BIGNUM *r, const BIGNUM *a, const BIGNUM *p,
 const BIGNUM *m,BN_CTX *ctx) __attribute__((deprecated));
int BN_mod_exp_mont(BIGNUM *r, const BIGNUM *a, const BIGNUM *p,
 const BIGNUM *m, BN_CTX *ctx, BN_MONT_CTX *m_ctx) __attribute__((deprecated));
int BN_mod_exp_mont_consttime(BIGNUM *rr, const BIGNUM *a, const BIGNUM *p,
 const BIGNUM *m, BN_CTX *ctx, BN_MONT_CTX *in_mont) __attribute__((deprecated));
int BN_mod_exp_mont_word(BIGNUM *r, unsigned long long a, const BIGNUM *p,
 const BIGNUM *m, BN_CTX *ctx, BN_MONT_CTX *m_ctx) __attribute__((deprecated));
int BN_mod_exp2_mont(BIGNUM *r, const BIGNUM *a1, const BIGNUM *p1,
 const BIGNUM *a2, const BIGNUM *p2,const BIGNUM *m,
 BN_CTX *ctx,BN_MONT_CTX *m_ctx) __attribute__((deprecated));
int BN_mod_exp_simple(BIGNUM *r, const BIGNUM *a, const BIGNUM *p,
 const BIGNUM *m,BN_CTX *ctx) __attribute__((deprecated));

int BN_mask_bits(BIGNUM *a,int n) __attribute__((deprecated));

int BN_print_fp(FILE *fp, const BIGNUM *a) __attribute__((deprecated));


int BN_print(BIO *fp, const BIGNUM *a) __attribute__((deprecated));



int BN_reciprocal(BIGNUM *r, const BIGNUM *m, int len, BN_CTX *ctx) __attribute__((deprecated));
int BN_rshift(BIGNUM *r, const BIGNUM *a, int n) __attribute__((deprecated));
int BN_rshift1(BIGNUM *r, const BIGNUM *a) __attribute__((deprecated));
void BN_clear(BIGNUM *a) __attribute__((deprecated));
BIGNUM *BN_dup(const BIGNUM *a) __attribute__((deprecated));
int BN_ucmp(const BIGNUM *a, const BIGNUM *b) __attribute__((deprecated));
int BN_set_bit(BIGNUM *a, int n) __attribute__((deprecated));
int BN_clear_bit(BIGNUM *a, int n) __attribute__((deprecated));
char * BN_bn2hex(const BIGNUM *a) __attribute__((deprecated));
char * BN_bn2dec(const BIGNUM *a) __attribute__((deprecated));
int BN_hex2bn(BIGNUM **a, const char *str) __attribute__((deprecated));
int BN_dec2bn(BIGNUM **a, const char *str) __attribute__((deprecated));
int BN_gcd(BIGNUM *r,const BIGNUM *a,const BIGNUM *b,BN_CTX *ctx) __attribute__((deprecated));
int BN_kronecker(const BIGNUM *a,const BIGNUM *b,BN_CTX *ctx) __attribute__((deprecated));
BIGNUM *BN_mod_inverse(BIGNUM *ret,
 const BIGNUM *a, const BIGNUM *n,BN_CTX *ctx) __attribute__((deprecated));
BIGNUM *BN_mod_sqrt(BIGNUM *ret,
 const BIGNUM *a, const BIGNUM *n,BN_CTX *ctx) __attribute__((deprecated));



BIGNUM *BN_generate_prime(BIGNUM *ret,int bits,int safe,
 const BIGNUM *add, const BIGNUM *rem,
 void (*callback)(int,int,void *),void *cb_arg) __attribute__((deprecated));
int BN_is_prime(const BIGNUM *p,int nchecks,
 void (*callback)(int,int,void *),
 BN_CTX *ctx,void *cb_arg) __attribute__((deprecated));
int BN_is_prime_fasttest(const BIGNUM *p,int nchecks,
 void (*callback)(int,int,void *),BN_CTX *ctx,void *cb_arg,
 int do_trial_division) __attribute__((deprecated));



int BN_generate_prime_ex(BIGNUM *ret,int bits,int safe, const BIGNUM *add,
  const BIGNUM *rem, BN_GENCB *cb) __attribute__((deprecated));
int BN_is_prime_ex(const BIGNUM *p,int nchecks, BN_CTX *ctx, BN_GENCB *cb) __attribute__((deprecated));
int BN_is_prime_fasttest_ex(const BIGNUM *p,int nchecks, BN_CTX *ctx,
  int do_trial_division, BN_GENCB *cb) __attribute__((deprecated));

int BN_X931_generate_Xpq(BIGNUM *Xp, BIGNUM *Xq, int nbits, BN_CTX *ctx) __attribute__((deprecated));

int BN_X931_derive_prime_ex(BIGNUM *p, BIGNUM *p1, BIGNUM *p2,
   const BIGNUM *Xp, const BIGNUM *Xp1, const BIGNUM *Xp2,
   const BIGNUM *e, BN_CTX *ctx, BN_GENCB *cb) __attribute__((deprecated));
int BN_X931_generate_prime_ex(BIGNUM *p, BIGNUM *p1, BIGNUM *p2,
   BIGNUM *Xp1, BIGNUM *Xp2,
   const BIGNUM *Xp,
   const BIGNUM *e, BN_CTX *ctx,
   BN_GENCB *cb) __attribute__((deprecated));

BN_MONT_CTX *BN_MONT_CTX_new(void ) __attribute__((deprecated));
void BN_MONT_CTX_init(BN_MONT_CTX *ctx) __attribute__((deprecated));
int BN_mod_mul_montgomery(BIGNUM *r,const BIGNUM *a,const BIGNUM *b,
 BN_MONT_CTX *mont, BN_CTX *ctx) __attribute__((deprecated));


int BN_from_montgomery(BIGNUM *r,const BIGNUM *a,
 BN_MONT_CTX *mont, BN_CTX *ctx) __attribute__((deprecated));
void BN_MONT_CTX_free(BN_MONT_CTX *mont) __attribute__((deprecated));
int BN_MONT_CTX_set(BN_MONT_CTX *mont,const BIGNUM *mod,BN_CTX *ctx) __attribute__((deprecated));
BN_MONT_CTX *BN_MONT_CTX_copy(BN_MONT_CTX *to,BN_MONT_CTX *from) __attribute__((deprecated));
BN_MONT_CTX *BN_MONT_CTX_set_locked(BN_MONT_CTX **pmont, int lock,
     const BIGNUM *mod, BN_CTX *ctx) __attribute__((deprecated));





BN_BLINDING *BN_BLINDING_new(const BIGNUM *A, const BIGNUM *Ai, BIGNUM *mod) __attribute__((deprecated));
void BN_BLINDING_free(BN_BLINDING *b) __attribute__((deprecated));
int BN_BLINDING_update(BN_BLINDING *b,BN_CTX *ctx) __attribute__((deprecated));
int BN_BLINDING_convert(BIGNUM *n, BN_BLINDING *b, BN_CTX *ctx) __attribute__((deprecated));
int BN_BLINDING_invert(BIGNUM *n, BN_BLINDING *b, BN_CTX *ctx) __attribute__((deprecated));
int BN_BLINDING_convert_ex(BIGNUM *n, BIGNUM *r, BN_BLINDING *b, BN_CTX *) __attribute__((deprecated));
int BN_BLINDING_invert_ex(BIGNUM *n, const BIGNUM *r, BN_BLINDING *b, BN_CTX *) __attribute__((deprecated));
unsigned long BN_BLINDING_get_thread_id(const BN_BLINDING *) __attribute__((deprecated));
void BN_BLINDING_set_thread_id(BN_BLINDING *, unsigned long) __attribute__((deprecated));
unsigned long BN_BLINDING_get_flags(const BN_BLINDING *) __attribute__((deprecated));
void BN_BLINDING_set_flags(BN_BLINDING *, unsigned long) __attribute__((deprecated));
BN_BLINDING *BN_BLINDING_create_param(BN_BLINDING *b,
 const BIGNUM *e, BIGNUM *m, BN_CTX *ctx,
 int (*bn_mod_exp)(BIGNUM *r, const BIGNUM *a, const BIGNUM *p,
     const BIGNUM *m, BN_CTX *ctx, BN_MONT_CTX *m_ctx),
 BN_MONT_CTX *m_ctx) __attribute__((deprecated));


void BN_set_params(int mul,int high,int low,int mont) __attribute__((deprecated));
int BN_get_params(int which) __attribute__((deprecated));


void BN_RECP_CTX_init(BN_RECP_CTX *recp) __attribute__((deprecated));
BN_RECP_CTX *BN_RECP_CTX_new(void) __attribute__((deprecated));
void BN_RECP_CTX_free(BN_RECP_CTX *recp) __attribute__((deprecated));
int BN_RECP_CTX_set(BN_RECP_CTX *recp,const BIGNUM *rdiv,BN_CTX *ctx) __attribute__((deprecated));
int BN_mod_mul_reciprocal(BIGNUM *r, const BIGNUM *x, const BIGNUM *y,
 BN_RECP_CTX *recp,BN_CTX *ctx) __attribute__((deprecated));
int BN_mod_exp_recp(BIGNUM *r, const BIGNUM *a, const BIGNUM *p,
 const BIGNUM *m, BN_CTX *ctx) __attribute__((deprecated));
int BN_div_recp(BIGNUM *dv, BIGNUM *rem, const BIGNUM *m,
 BN_RECP_CTX *recp, BN_CTX *ctx) __attribute__((deprecated));
# 607 "/usr/include/openssl/bn.h" 3 4
int BN_GF2m_add(BIGNUM *r, const BIGNUM *a, const BIGNUM *b) __attribute__((deprecated));

int BN_GF2m_mod(BIGNUM *r, const BIGNUM *a, const BIGNUM *p) __attribute__((deprecated));
int BN_GF2m_mod_mul(BIGNUM *r, const BIGNUM *a, const BIGNUM *b,
 const BIGNUM *p, BN_CTX *ctx) __attribute__((deprecated));
int BN_GF2m_mod_sqr(BIGNUM *r, const BIGNUM *a, const BIGNUM *p,
 BN_CTX *ctx) __attribute__((deprecated));
int BN_GF2m_mod_inv(BIGNUM *r, const BIGNUM *b, const BIGNUM *p,
 BN_CTX *ctx) __attribute__((deprecated));
int BN_GF2m_mod_div(BIGNUM *r, const BIGNUM *a, const BIGNUM *b,
 const BIGNUM *p, BN_CTX *ctx) __attribute__((deprecated));
int BN_GF2m_mod_exp(BIGNUM *r, const BIGNUM *a, const BIGNUM *b,
 const BIGNUM *p, BN_CTX *ctx) __attribute__((deprecated));
int BN_GF2m_mod_sqrt(BIGNUM *r, const BIGNUM *a, const BIGNUM *p,
 BN_CTX *ctx) __attribute__((deprecated));
int BN_GF2m_mod_solve_quad(BIGNUM *r, const BIGNUM *a, const BIGNUM *p,
 BN_CTX *ctx) __attribute__((deprecated));






int BN_GF2m_mod_arr(BIGNUM *r, const BIGNUM *a, const unsigned int p[]) __attribute__((deprecated));

int BN_GF2m_mod_mul_arr(BIGNUM *r, const BIGNUM *a, const BIGNUM *b,
 const unsigned int p[], BN_CTX *ctx) __attribute__((deprecated));
int BN_GF2m_mod_sqr_arr(BIGNUM *r, const BIGNUM *a, const unsigned int p[],
 BN_CTX *ctx) __attribute__((deprecated));
int BN_GF2m_mod_inv_arr(BIGNUM *r, const BIGNUM *b, const unsigned int p[],
 BN_CTX *ctx) __attribute__((deprecated));
int BN_GF2m_mod_div_arr(BIGNUM *r, const BIGNUM *a, const BIGNUM *b,
 const unsigned int p[], BN_CTX *ctx) __attribute__((deprecated));
int BN_GF2m_mod_exp_arr(BIGNUM *r, const BIGNUM *a, const BIGNUM *b,
 const unsigned int p[], BN_CTX *ctx) __attribute__((deprecated));
int BN_GF2m_mod_sqrt_arr(BIGNUM *r, const BIGNUM *a,
 const unsigned int p[], BN_CTX *ctx) __attribute__((deprecated));
int BN_GF2m_mod_solve_quad_arr(BIGNUM *r, const BIGNUM *a,
 const unsigned int p[], BN_CTX *ctx) __attribute__((deprecated));
int BN_GF2m_poly2arr(const BIGNUM *a, unsigned int p[], int max) __attribute__((deprecated));
int BN_GF2m_arr2poly(const unsigned int p[], BIGNUM *a) __attribute__((deprecated));



int BN_nist_mod_192(BIGNUM *r, const BIGNUM *a, const BIGNUM *p, BN_CTX *ctx) __attribute__((deprecated));
int BN_nist_mod_224(BIGNUM *r, const BIGNUM *a, const BIGNUM *p, BN_CTX *ctx) __attribute__((deprecated));
int BN_nist_mod_256(BIGNUM *r, const BIGNUM *a, const BIGNUM *p, BN_CTX *ctx) __attribute__((deprecated));
int BN_nist_mod_384(BIGNUM *r, const BIGNUM *a, const BIGNUM *p, BN_CTX *ctx) __attribute__((deprecated));
int BN_nist_mod_521(BIGNUM *r, const BIGNUM *a, const BIGNUM *p, BN_CTX *ctx) __attribute__((deprecated));

const BIGNUM *BN_get0_nist_prime_192(void) __attribute__((deprecated));
const BIGNUM *BN_get0_nist_prime_224(void) __attribute__((deprecated));
const BIGNUM *BN_get0_nist_prime_256(void) __attribute__((deprecated));
const BIGNUM *BN_get0_nist_prime_384(void) __attribute__((deprecated));
const BIGNUM *BN_get0_nist_prime_521(void) __attribute__((deprecated));






BIGNUM *bn_expand2(BIGNUM *a, int words) __attribute__((deprecated));

BIGNUM *bn_dup_expand(const BIGNUM *a, int words) __attribute__((deprecated));
# 764 "/usr/include/openssl/bn.h" 3 4
unsigned long long bn_mul_add_words(unsigned long long *rp, const unsigned long long *ap, int num, unsigned long long w) __attribute__((deprecated));
unsigned long long bn_mul_words(unsigned long long *rp, const unsigned long long *ap, int num, unsigned long long w) __attribute__((deprecated));
void bn_sqr_words(unsigned long long *rp, const unsigned long long *ap, int num) __attribute__((deprecated));
unsigned long long bn_div_words(unsigned long long h, unsigned long long l, unsigned long long d) __attribute__((deprecated));
unsigned long long bn_add_words(unsigned long long *rp, const unsigned long long *ap, const unsigned long long *bp,int num) __attribute__((deprecated));
unsigned long long bn_sub_words(unsigned long long *rp, const unsigned long long *ap, const unsigned long long *bp,int num) __attribute__((deprecated));


BIGNUM *get_rfc2409_prime_768(BIGNUM *bn) __attribute__((deprecated));
BIGNUM *get_rfc2409_prime_1024(BIGNUM *bn) __attribute__((deprecated));


BIGNUM *get_rfc3526_prime_1536(BIGNUM *bn) __attribute__((deprecated));
BIGNUM *get_rfc3526_prime_2048(BIGNUM *bn) __attribute__((deprecated));
BIGNUM *get_rfc3526_prime_3072(BIGNUM *bn) __attribute__((deprecated));
BIGNUM *get_rfc3526_prime_4096(BIGNUM *bn) __attribute__((deprecated));
BIGNUM *get_rfc3526_prime_6144(BIGNUM *bn) __attribute__((deprecated));
BIGNUM *get_rfc3526_prime_8192(BIGNUM *bn) __attribute__((deprecated));

int BN_bntest_rand(BIGNUM *rnd, int bits, int top,int bottom) __attribute__((deprecated));





void ERR_load_BN_strings(void) __attribute__((deprecated));
# 77 "/usr/include/openssl/asn1.h" 2 3 4
# 167 "/usr/include/openssl/asn1.h" 3 4
struct X509_algor_st;

# 177 "/usr/include/openssl/asn1.h" 3 4
typedef struct asn1_ctx_st
 {
 unsigned char *p;
 int eos;
 int error;
 int inf;
 int tag;
 int xclass;
 long slen;
 unsigned char *max;
 unsigned char *q;
 unsigned char **pp;
 int line;
 } ASN1_CTX;

typedef struct asn1_const_ctx_st
 {
 const unsigned char *p;
 int eos;
 int error;
 int inf;
 int tag;
 int xclass;
 long slen;
 const unsigned char *max;
 const unsigned char *q;
 const unsigned char **pp;
 int line;
 } ASN1_const_CTX;







typedef struct asn1_object_st
 {
 const char *sn,*ln;
 int nid;
 int length;
 unsigned char *data;
 int flags;
 } ASN1_OBJECT;
# 236 "/usr/include/openssl/asn1.h" 3 4
typedef struct asn1_string_st
 {
 int length;
 int type;
 unsigned char *data;




 long flags;
 } ASN1_STRING;






typedef struct ASN1_ENCODING_st
 {
 unsigned char *enc;
 long len;
 int modified;
 } ASN1_ENCODING;
# 269 "/usr/include/openssl/asn1.h" 3 4
typedef struct asn1_string_table_st {
 int nid;
 long minsize;
 long maxsize;
 unsigned long mask;
 unsigned long flags;
} ASN1_STRING_TABLE;


# 293 "/usr/include/openssl/asn1.h" 3 4
typedef struct ASN1_TEMPLATE_st ASN1_TEMPLATE;
typedef struct ASN1_ITEM_st ASN1_ITEM;
typedef struct ASN1_TLC_st ASN1_TLC;

typedef struct ASN1_VALUE_st ASN1_VALUE;
# 356 "/usr/include/openssl/asn1.h" 3 4
typedef void *d2i_of_void(void **,const unsigned char **,long); typedef int i2d_of_void(void *,unsigned char **);
# 396 "/usr/include/openssl/asn1.h" 3 4
typedef const ASN1_ITEM ASN1_ITEM_EXP;
# 510 "/usr/include/openssl/asn1.h" 3 4





typedef struct asn1_type_st
 {
 int type;
 union {
  char *ptr;
  ASN1_BOOLEAN boolean;
  ASN1_STRING * asn1_string;
  ASN1_OBJECT * object;
  ASN1_INTEGER * integer;
  ASN1_ENUMERATED * enumerated;
  ASN1_BIT_STRING * bit_string;
  ASN1_OCTET_STRING * octet_string;
  ASN1_PRINTABLESTRING * printablestring;
  ASN1_T61STRING * t61string;
  ASN1_IA5STRING * ia5string;
  ASN1_GENERALSTRING * generalstring;
  ASN1_BMPSTRING * bmpstring;
  ASN1_UNIVERSALSTRING * universalstring;
  ASN1_UTCTIME * utctime;
  ASN1_GENERALIZEDTIME * generalizedtime;
  ASN1_VISIBLESTRING * visiblestring;
  ASN1_UTF8STRING * utf8string;


  ASN1_STRING * set;
  ASN1_STRING * sequence;
  ASN1_VALUE * asn1_value;
  } value;
 } ASN1_TYPE;




typedef struct asn1_method_st
 {
 i2d_of_void *i2d;
 d2i_of_void *d2i;
 void *(*create)(void);
 void (*destroy)(void *);
 } ASN1_METHOD;


typedef struct asn1_header_st
 {
 ASN1_OCTET_STRING *header;
 void *data;
 ASN1_METHOD *meth;
 } ASN1_HEADER;


typedef struct BIT_STRING_BITNAME_st {
 int bitnum;
 const char *lname;
 const char *sname;
} BIT_STRING_BITNAME;
# 769 "/usr/include/openssl/asn1.h" 3 4
ASN1_TYPE *ASN1_TYPE_new(void); void ASN1_TYPE_free(ASN1_TYPE *a); ASN1_TYPE *d2i_ASN1_TYPE(ASN1_TYPE **a, const unsigned char **in, long len); int i2d_ASN1_TYPE(ASN1_TYPE *a, unsigned char **out); extern const ASN1_ITEM ASN1_ANY_it;

int ASN1_TYPE_get(ASN1_TYPE *a) __attribute__((deprecated));
void ASN1_TYPE_set(ASN1_TYPE *a, int type, void *value) __attribute__((deprecated));
int ASN1_TYPE_set1(ASN1_TYPE *a, int type, const void *value) __attribute__((deprecated));

ASN1_OBJECT * ASN1_OBJECT_new(void ) __attribute__((deprecated));
void ASN1_OBJECT_free(ASN1_OBJECT *a) __attribute__((deprecated));
int i2d_ASN1_OBJECT(ASN1_OBJECT *a,unsigned char **pp) __attribute__((deprecated));
ASN1_OBJECT * c2i_ASN1_OBJECT(ASN1_OBJECT **a,const unsigned char **pp,
   long length) __attribute__((deprecated));
ASN1_OBJECT * d2i_ASN1_OBJECT(ASN1_OBJECT **a,const unsigned char **pp,
   long length) __attribute__((deprecated));

extern const ASN1_ITEM ASN1_OBJECT_it;




ASN1_STRING * ASN1_STRING_new(void) __attribute__((deprecated));
void ASN1_STRING_free(ASN1_STRING *a) __attribute__((deprecated));
ASN1_STRING * ASN1_STRING_dup(ASN1_STRING *a) __attribute__((deprecated));
ASN1_STRING * ASN1_STRING_type_new(int type ) __attribute__((deprecated));
int ASN1_STRING_cmp(ASN1_STRING *a, ASN1_STRING *b) __attribute__((deprecated));


int ASN1_STRING_set(ASN1_STRING *str, const void *data, int len) __attribute__((deprecated));
void ASN1_STRING_set0(ASN1_STRING *str, void *data, int len) __attribute__((deprecated));
int ASN1_STRING_length(ASN1_STRING *x) __attribute__((deprecated));
void ASN1_STRING_length_set(ASN1_STRING *x, int n) __attribute__((deprecated));
int ASN1_STRING_type(ASN1_STRING *x) __attribute__((deprecated));
unsigned char * ASN1_STRING_data(ASN1_STRING *x) __attribute__((deprecated));

ASN1_BIT_STRING *ASN1_BIT_STRING_new(void); void ASN1_BIT_STRING_free(ASN1_BIT_STRING *a); ASN1_BIT_STRING *d2i_ASN1_BIT_STRING(ASN1_BIT_STRING **a, const unsigned char **in, long len); int i2d_ASN1_BIT_STRING(ASN1_BIT_STRING *a, unsigned char **out); extern const ASN1_ITEM ASN1_BIT_STRING_it;
int i2c_ASN1_BIT_STRING(ASN1_BIT_STRING *a,unsigned char **pp) __attribute__((deprecated));
ASN1_BIT_STRING *c2i_ASN1_BIT_STRING(ASN1_BIT_STRING **a,const unsigned char **pp,
   long length) __attribute__((deprecated));
int ASN1_BIT_STRING_set(ASN1_BIT_STRING *a, unsigned char *d,
   int length ) __attribute__((deprecated));
int ASN1_BIT_STRING_set_bit(ASN1_BIT_STRING *a, int n, int value) __attribute__((deprecated));
int ASN1_BIT_STRING_get_bit(ASN1_BIT_STRING *a, int n) __attribute__((deprecated));


int ASN1_BIT_STRING_name_print(BIO *out, ASN1_BIT_STRING *bs,
    BIT_STRING_BITNAME *tbl, int indent) __attribute__((deprecated));

int ASN1_BIT_STRING_num_asc(char *name, BIT_STRING_BITNAME *tbl) __attribute__((deprecated));
int ASN1_BIT_STRING_set_asc(ASN1_BIT_STRING *bs, char *name, int value,
    BIT_STRING_BITNAME *tbl) __attribute__((deprecated));

int i2d_ASN1_BOOLEAN(int a,unsigned char **pp) __attribute__((deprecated));
int d2i_ASN1_BOOLEAN(int *a,const unsigned char **pp,long length) __attribute__((deprecated));

ASN1_INTEGER *ASN1_INTEGER_new(void); void ASN1_INTEGER_free(ASN1_INTEGER *a); ASN1_INTEGER *d2i_ASN1_INTEGER(ASN1_INTEGER **a, const unsigned char **in, long len); int i2d_ASN1_INTEGER(ASN1_INTEGER *a, unsigned char **out); extern const ASN1_ITEM ASN1_INTEGER_it;
int i2c_ASN1_INTEGER(ASN1_INTEGER *a,unsigned char **pp) __attribute__((deprecated));
ASN1_INTEGER *c2i_ASN1_INTEGER(ASN1_INTEGER **a,const unsigned char **pp,
   long length) __attribute__((deprecated));
ASN1_INTEGER *d2i_ASN1_UINTEGER(ASN1_INTEGER **a,const unsigned char **pp,
   long length) __attribute__((deprecated));
ASN1_INTEGER * ASN1_INTEGER_dup(ASN1_INTEGER *x) __attribute__((deprecated));
int ASN1_INTEGER_cmp(ASN1_INTEGER *x, ASN1_INTEGER *y) __attribute__((deprecated));

ASN1_ENUMERATED *ASN1_ENUMERATED_new(void); void ASN1_ENUMERATED_free(ASN1_ENUMERATED *a); ASN1_ENUMERATED *d2i_ASN1_ENUMERATED(ASN1_ENUMERATED **a, const unsigned char **in, long len); int i2d_ASN1_ENUMERATED(ASN1_ENUMERATED *a, unsigned char **out); extern const ASN1_ITEM ASN1_ENUMERATED_it;

int ASN1_UTCTIME_check(ASN1_UTCTIME *a) __attribute__((deprecated));
ASN1_UTCTIME *ASN1_UTCTIME_set(ASN1_UTCTIME *s,time_t t) __attribute__((deprecated));
int ASN1_UTCTIME_set_string(ASN1_UTCTIME *s, const char *str) __attribute__((deprecated));
int ASN1_UTCTIME_cmp_time_t(const ASN1_UTCTIME *s, time_t t) __attribute__((deprecated));




int ASN1_GENERALIZEDTIME_check(ASN1_GENERALIZEDTIME *a) __attribute__((deprecated));
ASN1_GENERALIZEDTIME *ASN1_GENERALIZEDTIME_set(ASN1_GENERALIZEDTIME *s,time_t t) __attribute__((deprecated));
int ASN1_GENERALIZEDTIME_set_string(ASN1_GENERALIZEDTIME *s, const char *str) __attribute__((deprecated));

ASN1_OCTET_STRING *ASN1_OCTET_STRING_new(void); void ASN1_OCTET_STRING_free(ASN1_OCTET_STRING *a); ASN1_OCTET_STRING *d2i_ASN1_OCTET_STRING(ASN1_OCTET_STRING **a, const unsigned char **in, long len); int i2d_ASN1_OCTET_STRING(ASN1_OCTET_STRING *a, unsigned char **out); extern const ASN1_ITEM ASN1_OCTET_STRING_it;
ASN1_OCTET_STRING * ASN1_OCTET_STRING_dup(ASN1_OCTET_STRING *a) __attribute__((deprecated));
int ASN1_OCTET_STRING_cmp(ASN1_OCTET_STRING *a, ASN1_OCTET_STRING *b) __attribute__((deprecated));
int ASN1_OCTET_STRING_set(ASN1_OCTET_STRING *str, const unsigned char *data, int len) __attribute__((deprecated));

ASN1_VISIBLESTRING *ASN1_VISIBLESTRING_new(void); void ASN1_VISIBLESTRING_free(ASN1_VISIBLESTRING *a); ASN1_VISIBLESTRING *d2i_ASN1_VISIBLESTRING(ASN1_VISIBLESTRING **a, const unsigned char **in, long len); int i2d_ASN1_VISIBLESTRING(ASN1_VISIBLESTRING *a, unsigned char **out); extern const ASN1_ITEM ASN1_VISIBLESTRING_it;
ASN1_UNIVERSALSTRING *ASN1_UNIVERSALSTRING_new(void); void ASN1_UNIVERSALSTRING_free(ASN1_UNIVERSALSTRING *a); ASN1_UNIVERSALSTRING *d2i_ASN1_UNIVERSALSTRING(ASN1_UNIVERSALSTRING **a, const unsigned char **in, long len); int i2d_ASN1_UNIVERSALSTRING(ASN1_UNIVERSALSTRING *a, unsigned char **out); extern const ASN1_ITEM ASN1_UNIVERSALSTRING_it;
ASN1_UTF8STRING *ASN1_UTF8STRING_new(void); void ASN1_UTF8STRING_free(ASN1_UTF8STRING *a); ASN1_UTF8STRING *d2i_ASN1_UTF8STRING(ASN1_UTF8STRING **a, const unsigned char **in, long len); int i2d_ASN1_UTF8STRING(ASN1_UTF8STRING *a, unsigned char **out); extern const ASN1_ITEM ASN1_UTF8STRING_it;
ASN1_NULL *ASN1_NULL_new(void); void ASN1_NULL_free(ASN1_NULL *a); ASN1_NULL *d2i_ASN1_NULL(ASN1_NULL **a, const unsigned char **in, long len); int i2d_ASN1_NULL(ASN1_NULL *a, unsigned char **out); extern const ASN1_ITEM ASN1_NULL_it;
ASN1_BMPSTRING *ASN1_BMPSTRING_new(void); void ASN1_BMPSTRING_free(ASN1_BMPSTRING *a); ASN1_BMPSTRING *d2i_ASN1_BMPSTRING(ASN1_BMPSTRING **a, const unsigned char **in, long len); int i2d_ASN1_BMPSTRING(ASN1_BMPSTRING *a, unsigned char **out); extern const ASN1_ITEM ASN1_BMPSTRING_it;

int UTF8_getc(const unsigned char *str, int len, unsigned long *val) __attribute__((deprecated));
int UTF8_putc(unsigned char *str, int len, unsigned long value) __attribute__((deprecated));

ASN1_STRING *ASN1_PRINTABLE_new(void); void ASN1_PRINTABLE_free(ASN1_STRING *a); ASN1_STRING *d2i_ASN1_PRINTABLE(ASN1_STRING **a, const unsigned char **in, long len); int i2d_ASN1_PRINTABLE(ASN1_STRING *a, unsigned char **out); extern const ASN1_ITEM ASN1_PRINTABLE_it;

ASN1_STRING *DIRECTORYSTRING_new(void); void DIRECTORYSTRING_free(ASN1_STRING *a); ASN1_STRING *d2i_DIRECTORYSTRING(ASN1_STRING **a, const unsigned char **in, long len); int i2d_DIRECTORYSTRING(ASN1_STRING *a, unsigned char **out); extern const ASN1_ITEM DIRECTORYSTRING_it;
ASN1_STRING *DISPLAYTEXT_new(void); void DISPLAYTEXT_free(ASN1_STRING *a); ASN1_STRING *d2i_DISPLAYTEXT(ASN1_STRING **a, const unsigned char **in, long len); int i2d_DISPLAYTEXT(ASN1_STRING *a, unsigned char **out); extern const ASN1_ITEM DISPLAYTEXT_it;
ASN1_PRINTABLESTRING *ASN1_PRINTABLESTRING_new(void); void ASN1_PRINTABLESTRING_free(ASN1_PRINTABLESTRING *a); ASN1_PRINTABLESTRING *d2i_ASN1_PRINTABLESTRING(ASN1_PRINTABLESTRING **a, const unsigned char **in, long len); int i2d_ASN1_PRINTABLESTRING(ASN1_PRINTABLESTRING *a, unsigned char **out); extern const ASN1_ITEM ASN1_PRINTABLESTRING_it;
ASN1_T61STRING *ASN1_T61STRING_new(void); void ASN1_T61STRING_free(ASN1_T61STRING *a); ASN1_T61STRING *d2i_ASN1_T61STRING(ASN1_T61STRING **a, const unsigned char **in, long len); int i2d_ASN1_T61STRING(ASN1_T61STRING *a, unsigned char **out); extern const ASN1_ITEM ASN1_T61STRING_it;
ASN1_IA5STRING *ASN1_IA5STRING_new(void); void ASN1_IA5STRING_free(ASN1_IA5STRING *a); ASN1_IA5STRING *d2i_ASN1_IA5STRING(ASN1_IA5STRING **a, const unsigned char **in, long len); int i2d_ASN1_IA5STRING(ASN1_IA5STRING *a, unsigned char **out); extern const ASN1_ITEM ASN1_IA5STRING_it;
ASN1_GENERALSTRING *ASN1_GENERALSTRING_new(void); void ASN1_GENERALSTRING_free(ASN1_GENERALSTRING *a); ASN1_GENERALSTRING *d2i_ASN1_GENERALSTRING(ASN1_GENERALSTRING **a, const unsigned char **in, long len); int i2d_ASN1_GENERALSTRING(ASN1_GENERALSTRING *a, unsigned char **out); extern const ASN1_ITEM ASN1_GENERALSTRING_it;
ASN1_UTCTIME *ASN1_UTCTIME_new(void); void ASN1_UTCTIME_free(ASN1_UTCTIME *a); ASN1_UTCTIME *d2i_ASN1_UTCTIME(ASN1_UTCTIME **a, const unsigned char **in, long len); int i2d_ASN1_UTCTIME(ASN1_UTCTIME *a, unsigned char **out); extern const ASN1_ITEM ASN1_UTCTIME_it;
ASN1_GENERALIZEDTIME *ASN1_GENERALIZEDTIME_new(void); void ASN1_GENERALIZEDTIME_free(ASN1_GENERALIZEDTIME *a); ASN1_GENERALIZEDTIME *d2i_ASN1_GENERALIZEDTIME(ASN1_GENERALIZEDTIME **a, const unsigned char **in, long len); int i2d_ASN1_GENERALIZEDTIME(ASN1_GENERALIZEDTIME *a, unsigned char **out); extern const ASN1_ITEM ASN1_GENERALIZEDTIME_it;
ASN1_TIME *ASN1_TIME_new(void); void ASN1_TIME_free(ASN1_TIME *a); ASN1_TIME *d2i_ASN1_TIME(ASN1_TIME **a, const unsigned char **in, long len); int i2d_ASN1_TIME(ASN1_TIME *a, unsigned char **out); extern const ASN1_ITEM ASN1_TIME_it;

extern const ASN1_ITEM ASN1_OCTET_STRING_NDEF_it;

ASN1_TIME *ASN1_TIME_set(ASN1_TIME *s,time_t t) __attribute__((deprecated));
int ASN1_TIME_check(ASN1_TIME *t) __attribute__((deprecated));
ASN1_GENERALIZEDTIME *ASN1_TIME_to_generalizedtime(ASN1_TIME *t, ASN1_GENERALIZEDTIME **out) __attribute__((deprecated));

int i2d_ASN1_SET(STACK *a, unsigned char **pp,
   i2d_of_void *i2d, int ex_tag, int ex_class, int is_set) __attribute__((deprecated));
STACK * d2i_ASN1_SET(STACK **a, const unsigned char **pp, long length,
       d2i_of_void *d2i, void (*free_func)(void *),
       int ex_tag, int ex_class) __attribute__((deprecated));


int i2a_ASN1_INTEGER(BIO *bp, ASN1_INTEGER *a) __attribute__((deprecated));
int a2i_ASN1_INTEGER(BIO *bp,ASN1_INTEGER *bs,char *buf,int size) __attribute__((deprecated));
int i2a_ASN1_ENUMERATED(BIO *bp, ASN1_ENUMERATED *a) __attribute__((deprecated));
int a2i_ASN1_ENUMERATED(BIO *bp,ASN1_ENUMERATED *bs,char *buf,int size) __attribute__((deprecated));
int i2a_ASN1_OBJECT(BIO *bp,ASN1_OBJECT *a) __attribute__((deprecated));
int a2i_ASN1_STRING(BIO *bp,ASN1_STRING *bs,char *buf,int size) __attribute__((deprecated));
int i2a_ASN1_STRING(BIO *bp, ASN1_STRING *a, int type) __attribute__((deprecated));

int i2t_ASN1_OBJECT(char *buf,int buf_len,ASN1_OBJECT *a) __attribute__((deprecated));

int a2d_ASN1_OBJECT(unsigned char *out,int olen, const char *buf, int num) __attribute__((deprecated));
ASN1_OBJECT *ASN1_OBJECT_create(int nid, unsigned char *data,int len,
 const char *sn, const char *ln) __attribute__((deprecated));

int ASN1_INTEGER_set(ASN1_INTEGER *a, long v) __attribute__((deprecated));
long ASN1_INTEGER_get(ASN1_INTEGER *a) __attribute__((deprecated));
ASN1_INTEGER *BN_to_ASN1_INTEGER(BIGNUM *bn, ASN1_INTEGER *ai) __attribute__((deprecated));
BIGNUM *ASN1_INTEGER_to_BN(ASN1_INTEGER *ai,BIGNUM *bn) __attribute__((deprecated));

int ASN1_ENUMERATED_set(ASN1_ENUMERATED *a, long v) __attribute__((deprecated));
long ASN1_ENUMERATED_get(ASN1_ENUMERATED *a) __attribute__((deprecated));
ASN1_ENUMERATED *BN_to_ASN1_ENUMERATED(BIGNUM *bn, ASN1_ENUMERATED *ai) __attribute__((deprecated));
BIGNUM *ASN1_ENUMERATED_to_BN(ASN1_ENUMERATED *ai,BIGNUM *bn) __attribute__((deprecated));



int ASN1_PRINTABLE_type(const unsigned char *s, int max) __attribute__((deprecated));

int i2d_ASN1_bytes(ASN1_STRING *a, unsigned char **pp, int tag, int xclass) __attribute__((deprecated));
ASN1_STRING *d2i_ASN1_bytes(ASN1_STRING **a, const unsigned char **pp,
 long length, int Ptag, int Pclass) __attribute__((deprecated));
unsigned long ASN1_tag2bit(int tag) __attribute__((deprecated));

ASN1_STRING *d2i_ASN1_type_bytes(ASN1_STRING **a,const unsigned char **pp,
  long length,int type) __attribute__((deprecated));


int asn1_Finish(ASN1_CTX *c) __attribute__((deprecated));
int asn1_const_Finish(ASN1_const_CTX *c) __attribute__((deprecated));


int ASN1_get_object(const unsigned char **pp, long *plength, int *ptag,
 int *pclass, long omax) __attribute__((deprecated));
int ASN1_check_infinite_end(unsigned char **p,long len) __attribute__((deprecated));
int ASN1_const_check_infinite_end(const unsigned char **p,long len) __attribute__((deprecated));
void ASN1_put_object(unsigned char **pp, int constructed, int length,
 int tag, int xclass) __attribute__((deprecated));
int ASN1_put_eoc(unsigned char **pp) __attribute__((deprecated));
int ASN1_object_size(int constructed, int length, int tag) __attribute__((deprecated));


void *ASN1_dup(i2d_of_void *i2d, d2i_of_void *d2i, char *x) __attribute__((deprecated));
# 947 "/usr/include/openssl/asn1.h" 3 4
void *ASN1_item_dup(const ASN1_ITEM *it, void *x) __attribute__((deprecated));
# 956 "/usr/include/openssl/asn1.h" 3 4
void *ASN1_d2i_fp(void *(*xnew)(void), d2i_of_void *d2i, FILE *in, void **x) __attribute__((deprecated));







void *ASN1_item_d2i_fp(const ASN1_ITEM *it, FILE *in, void *x) __attribute__((deprecated));
int ASN1_i2d_fp(i2d_of_void *i2d,FILE *out,void *x) __attribute__((deprecated));
# 977 "/usr/include/openssl/asn1.h" 3 4
int ASN1_item_i2d_fp(const ASN1_ITEM *it, FILE *out, void *x) __attribute__((deprecated));
int ASN1_STRING_print_ex_fp(FILE *fp, ASN1_STRING *str, unsigned long flags) __attribute__((deprecated));


int ASN1_STRING_to_UTF8(unsigned char **out, ASN1_STRING *in) __attribute__((deprecated));


void *ASN1_d2i_bio(void *(*xnew)(void), d2i_of_void *d2i, BIO *in, void **x) __attribute__((deprecated));







void *ASN1_item_d2i_bio(const ASN1_ITEM *it, BIO *in, void *x) __attribute__((deprecated));
int ASN1_i2d_bio(i2d_of_void *i2d,BIO *out, unsigned char *x) __attribute__((deprecated));
# 1005 "/usr/include/openssl/asn1.h" 3 4
int ASN1_item_i2d_bio(const ASN1_ITEM *it, BIO *out, void *x) __attribute__((deprecated));
int ASN1_UTCTIME_print(BIO *fp,ASN1_UTCTIME *a) __attribute__((deprecated));
int ASN1_GENERALIZEDTIME_print(BIO *fp,ASN1_GENERALIZEDTIME *a) __attribute__((deprecated));
int ASN1_TIME_print(BIO *fp,ASN1_TIME *a) __attribute__((deprecated));
int ASN1_STRING_print(BIO *bp,ASN1_STRING *v) __attribute__((deprecated));
int ASN1_STRING_print_ex(BIO *out, ASN1_STRING *str, unsigned long flags) __attribute__((deprecated));
int ASN1_parse(BIO *bp,const unsigned char *pp,long len,int indent) __attribute__((deprecated));
int ASN1_parse_dump(BIO *bp,const unsigned char *pp,long len,int indent,int dump) __attribute__((deprecated));

const char *ASN1_tag2str(int tag) __attribute__((deprecated));


int i2d_ASN1_HEADER(ASN1_HEADER *a,unsigned char **pp) __attribute__((deprecated));
ASN1_HEADER *d2i_ASN1_HEADER(ASN1_HEADER **a,const unsigned char **pp, long length) __attribute__((deprecated));
ASN1_HEADER *ASN1_HEADER_new(void ) __attribute__((deprecated));
void ASN1_HEADER_free(ASN1_HEADER *a) __attribute__((deprecated));

int ASN1_UNIVERSALSTRING_to_string(ASN1_UNIVERSALSTRING *s) __attribute__((deprecated));


ASN1_METHOD *X509_asn1_meth(void) __attribute__((deprecated));
ASN1_METHOD *RSAPrivateKey_asn1_meth(void) __attribute__((deprecated));
ASN1_METHOD *ASN1_IA5STRING_asn1_meth(void) __attribute__((deprecated));
ASN1_METHOD *ASN1_BIT_STRING_asn1_meth(void) __attribute__((deprecated));

int ASN1_TYPE_set_octetstring(ASN1_TYPE *a,
 unsigned char *data, int len) __attribute__((deprecated));
int ASN1_TYPE_get_octetstring(ASN1_TYPE *a,
 unsigned char *data, int max_len) __attribute__((deprecated));
int ASN1_TYPE_set_int_octetstring(ASN1_TYPE *a, long num,
 unsigned char *data, int len) __attribute__((deprecated));
int ASN1_TYPE_get_int_octetstring(ASN1_TYPE *a,long *num,
 unsigned char *data, int max_len) __attribute__((deprecated));

STACK *ASN1_seq_unpack(const unsigned char *buf, int len,
         d2i_of_void *d2i, void (*free_func)(void *)) __attribute__((deprecated));
unsigned char *ASN1_seq_pack(STACK *safes, i2d_of_void *i2d,
        unsigned char **buf, int *len ) __attribute__((deprecated));
void *ASN1_unpack_string(ASN1_STRING *oct, d2i_of_void *d2i) __attribute__((deprecated));
void *ASN1_item_unpack(ASN1_STRING *oct, const ASN1_ITEM *it) __attribute__((deprecated));
ASN1_STRING *ASN1_pack_string(void *obj, i2d_of_void *i2d,
         ASN1_OCTET_STRING **oct) __attribute__((deprecated));






ASN1_STRING *ASN1_item_pack(void *obj, const ASN1_ITEM *it, ASN1_OCTET_STRING **oct) __attribute__((deprecated));

void ASN1_STRING_set_default_mask(unsigned long mask) __attribute__((deprecated));
int ASN1_STRING_set_default_mask_asc(const char *p) __attribute__((deprecated));
unsigned long ASN1_STRING_get_default_mask(void) __attribute__((deprecated));
int ASN1_mbstring_copy(ASN1_STRING **out, const unsigned char *in, int len,
     int inform, unsigned long mask) __attribute__((deprecated));
int ASN1_mbstring_ncopy(ASN1_STRING **out, const unsigned char *in, int len,
     int inform, unsigned long mask,
     long minsize, long maxsize) __attribute__((deprecated));

ASN1_STRING *ASN1_STRING_set_by_NID(ASN1_STRING **out,
  const unsigned char *in, int inlen, int inform, int nid) __attribute__((deprecated));
ASN1_STRING_TABLE *ASN1_STRING_TABLE_get(int nid) __attribute__((deprecated));
int ASN1_STRING_TABLE_add(int, long, long, unsigned long, unsigned long) __attribute__((deprecated));
void ASN1_STRING_TABLE_cleanup(void) __attribute__((deprecated));




ASN1_VALUE *ASN1_item_new(const ASN1_ITEM *it) __attribute__((deprecated));
void ASN1_item_free(ASN1_VALUE *val, const ASN1_ITEM *it) __attribute__((deprecated));
ASN1_VALUE * ASN1_item_d2i(ASN1_VALUE **val, const unsigned char **in, long len, const ASN1_ITEM *it) __attribute__((deprecated));
int ASN1_item_i2d(ASN1_VALUE *val, unsigned char **out, const ASN1_ITEM *it) __attribute__((deprecated));
int ASN1_item_ndef_i2d(ASN1_VALUE *val, unsigned char **out, const ASN1_ITEM *it) __attribute__((deprecated));

void ASN1_add_oid_module(void) __attribute__((deprecated));

ASN1_TYPE *ASN1_generate_nconf(char *str, CONF *nconf) __attribute__((deprecated));
ASN1_TYPE *ASN1_generate_v3(char *str, X509V3_CTX *cnf) __attribute__((deprecated));

typedef int asn1_output_data_fn(BIO *out, BIO *data, ASN1_VALUE *val, int flags,
     const ASN1_ITEM *it);

int int_smime_write_ASN1(BIO *bio, ASN1_VALUE *val, BIO *data, int flags,
    int ctype_nid, int econt_nid,
    STACK *mdalgs,
    asn1_output_data_fn *data_fn,
    const ASN1_ITEM *it) __attribute__((deprecated));
ASN1_VALUE *SMIME_read_ASN1(BIO *bio, BIO **bcont, const ASN1_ITEM *it) __attribute__((deprecated));





void ERR_load_ASN1_strings(void) __attribute__((deprecated));
# 65 "/usr/include/openssl/rsa.h" 2 3 4
# 106 "/usr/include/openssl/rsa.h" 3 4
struct rsa_meth_st
 {
 const char *name;
 int (*rsa_pub_enc)(int flen,const unsigned char *from,
      unsigned char *to,
      RSA *rsa,int padding);
 int (*rsa_pub_dec)(int flen,const unsigned char *from,
      unsigned char *to,
      RSA *rsa,int padding);
 int (*rsa_priv_enc)(int flen,const unsigned char *from,
       unsigned char *to,
       RSA *rsa,int padding);
 int (*rsa_priv_dec)(int flen,const unsigned char *from,
       unsigned char *to,
       RSA *rsa,int padding);
 int (*rsa_mod_exp)(BIGNUM *r0,const BIGNUM *I,RSA *rsa,BN_CTX *ctx);
 int (*bn_mod_exp)(BIGNUM *r, const BIGNUM *a, const BIGNUM *p,
     const BIGNUM *m, BN_CTX *ctx,
     BN_MONT_CTX *m_ctx);
 int (*init)(RSA *rsa);
 int (*finish)(RSA *rsa);
 int flags;
 char *app_data;







 int (*rsa_sign)(int type,
  const unsigned char *m, unsigned int m_length,
  unsigned char *sigret, unsigned int *siglen, const RSA *rsa);
 int (*rsa_verify)(int dtype,
  const unsigned char *m, unsigned int m_length,
  unsigned char *sigbuf, unsigned int siglen, const RSA *rsa);




 int (*rsa_keygen)(RSA *rsa, int bits, BIGNUM *e, BN_GENCB *cb);
 };

struct rsa_st
 {


 int pad;
 long version;
 const RSA_METHOD *meth;

 ENGINE *engine;
 BIGNUM *n;
 BIGNUM *e;
 BIGNUM *d;
 BIGNUM *p;
 BIGNUM *q;
 BIGNUM *dmp1;
 BIGNUM *dmq1;
 BIGNUM *iqmp;

 CRYPTO_EX_DATA ex_data;
 int references;
 int flags;


 BN_MONT_CTX *_method_mod_n;
 BN_MONT_CTX *_method_mod_p;
 BN_MONT_CTX *_method_mod_q;



 char *bignum_data;
 BN_BLINDING *blinding;
 BN_BLINDING *mt_blinding;
 };
# 254 "/usr/include/openssl/rsa.h" 3 4
RSA * RSA_new(void) __attribute__((deprecated));
RSA * RSA_new_method(ENGINE *engine) __attribute__((deprecated));
int RSA_size(const RSA *) __attribute__((deprecated));



RSA * RSA_generate_key(int bits, unsigned long e,void
  (*callback)(int,int,void *),void *cb_arg) __attribute__((deprecated));



int RSA_generate_key_ex(RSA *rsa, int bits, BIGNUM *e, BN_GENCB *cb) __attribute__((deprecated));
int RSA_X931_derive_ex(RSA *rsa, BIGNUM *p1, BIGNUM *p2, BIGNUM *q1, BIGNUM *q2,
   const BIGNUM *Xp1, const BIGNUM *Xp2, const BIGNUM *Xp,
   const BIGNUM *Xq1, const BIGNUM *Xq2, const BIGNUM *Xq,
   const BIGNUM *e, BN_GENCB *cb) __attribute__((deprecated));
int RSA_X931_generate_key_ex(RSA *rsa, int bits, const BIGNUM *e, BN_GENCB *cb) __attribute__((deprecated));

int RSA_check_key(const RSA *) __attribute__((deprecated));

int RSA_public_encrypt(int flen, const unsigned char *from,
  unsigned char *to, RSA *rsa,int padding) __attribute__((deprecated));
int RSA_private_encrypt(int flen, const unsigned char *from,
  unsigned char *to, RSA *rsa,int padding) __attribute__((deprecated));
int RSA_public_decrypt(int flen, const unsigned char *from,
  unsigned char *to, RSA *rsa,int padding) __attribute__((deprecated));
int RSA_private_decrypt(int flen, const unsigned char *from,
  unsigned char *to, RSA *rsa,int padding) __attribute__((deprecated));
void RSA_free (RSA *r) __attribute__((deprecated));

int RSA_up_ref(RSA *r) __attribute__((deprecated));

int RSA_flags(const RSA *r) __attribute__((deprecated));






void RSA_set_default_method(const RSA_METHOD *meth) __attribute__((deprecated));
const RSA_METHOD *RSA_get_default_method(void) __attribute__((deprecated));
const RSA_METHOD *RSA_get_method(const RSA *rsa) __attribute__((deprecated));
int RSA_set_method(RSA *rsa, const RSA_METHOD *meth) __attribute__((deprecated));


int RSA_memory_lock(RSA *r) __attribute__((deprecated));


const RSA_METHOD *RSA_PKCS1_SSLeay(void) __attribute__((deprecated));

const RSA_METHOD *RSA_null_method(void) __attribute__((deprecated));

RSA *d2i_RSAPublicKey(RSA **a, const unsigned char **in, long len); int i2d_RSAPublicKey(const RSA *a, unsigned char **out); extern const ASN1_ITEM RSAPublicKey_it;
RSA *d2i_RSAPrivateKey(RSA **a, const unsigned char **in, long len); int i2d_RSAPrivateKey(const RSA *a, unsigned char **out); extern const ASN1_ITEM RSAPrivateKey_it;


int RSA_print_fp(FILE *fp, const RSA *r,int offset) __attribute__((deprecated));



int RSA_print(BIO *bp, const RSA *r,int offset) __attribute__((deprecated));



int i2d_RSA_NET(const RSA *a, unsigned char **pp,
  int (*cb)(char *buf, int len, const char *prompt, int verify),
  int sgckey) __attribute__((deprecated));
RSA *d2i_RSA_NET(RSA **a, const unsigned char **pp, long length,
   int (*cb)(char *buf, int len, const char *prompt, int verify),
   int sgckey) __attribute__((deprecated));

int i2d_Netscape_RSA(const RSA *a, unsigned char **pp,
       int (*cb)(char *buf, int len, const char *prompt,
          int verify)) __attribute__((deprecated));
RSA *d2i_Netscape_RSA(RSA **a, const unsigned char **pp, long length,
        int (*cb)(char *buf, int len, const char *prompt,
    int verify)) __attribute__((deprecated));




int RSA_sign(int type, const unsigned char *m, unsigned int m_length,
 unsigned char *sigret, unsigned int *siglen, RSA *rsa) __attribute__((deprecated));
int RSA_verify(int type, const unsigned char *m, unsigned int m_length,
 unsigned char *sigbuf, unsigned int siglen, RSA *rsa) __attribute__((deprecated));



int RSA_sign_ASN1_OCTET_STRING(int type,
 const unsigned char *m, unsigned int m_length,
 unsigned char *sigret, unsigned int *siglen, RSA *rsa) __attribute__((deprecated));
int RSA_verify_ASN1_OCTET_STRING(int type,
 const unsigned char *m, unsigned int m_length,
 unsigned char *sigbuf, unsigned int siglen, RSA *rsa) __attribute__((deprecated));

int RSA_blinding_on(RSA *rsa, BN_CTX *ctx) __attribute__((deprecated));
void RSA_blinding_off(RSA *rsa) __attribute__((deprecated));
BN_BLINDING *RSA_setup_blinding(RSA *rsa, BN_CTX *ctx) __attribute__((deprecated));

int RSA_padding_add_PKCS1_type_1(unsigned char *to,int tlen,
 const unsigned char *f,int fl) __attribute__((deprecated));
int RSA_padding_check_PKCS1_type_1(unsigned char *to,int tlen,
 const unsigned char *f,int fl,int rsa_len) __attribute__((deprecated));
int RSA_padding_add_PKCS1_type_2(unsigned char *to,int tlen,
 const unsigned char *f,int fl) __attribute__((deprecated));
int RSA_padding_check_PKCS1_type_2(unsigned char *to,int tlen,
 const unsigned char *f,int fl,int rsa_len) __attribute__((deprecated));
int PKCS1_MGF1(unsigned char *mask, long len,
 const unsigned char *seed, long seedlen, const EVP_MD *dgst) __attribute__((deprecated));
int RSA_padding_add_PKCS1_OAEP(unsigned char *to,int tlen,
 const unsigned char *f,int fl,
 const unsigned char *p,int pl) __attribute__((deprecated));
int RSA_padding_check_PKCS1_OAEP(unsigned char *to,int tlen,
 const unsigned char *f,int fl,int rsa_len,
 const unsigned char *p,int pl) __attribute__((deprecated));
int RSA_padding_add_SSLv23(unsigned char *to,int tlen,
 const unsigned char *f,int fl) __attribute__((deprecated));
int RSA_padding_check_SSLv23(unsigned char *to,int tlen,
 const unsigned char *f,int fl,int rsa_len) __attribute__((deprecated));
int RSA_padding_add_none(unsigned char *to,int tlen,
 const unsigned char *f,int fl) __attribute__((deprecated));
int RSA_padding_check_none(unsigned char *to,int tlen,
 const unsigned char *f,int fl,int rsa_len) __attribute__((deprecated));
int RSA_padding_add_X931(unsigned char *to,int tlen,
 const unsigned char *f,int fl) __attribute__((deprecated));
int RSA_padding_check_X931(unsigned char *to,int tlen,
 const unsigned char *f,int fl,int rsa_len) __attribute__((deprecated));
int RSA_X931_hash_id(int nid) __attribute__((deprecated));

int RSA_verify_PKCS1_PSS(RSA *rsa, const unsigned char *mHash,
   const EVP_MD *Hash, const unsigned char *EM, int sLen) __attribute__((deprecated));
int RSA_padding_add_PKCS1_PSS(RSA *rsa, unsigned char *EM,
   const unsigned char *mHash,
   const EVP_MD *Hash, int sLen) __attribute__((deprecated));

int RSA_get_ex_new_index(long argl, void *argp, CRYPTO_EX_new *new_func,
 CRYPTO_EX_dup *dup_func, CRYPTO_EX_free *free_func) __attribute__((deprecated));
int RSA_set_ex_data(RSA *r,int idx,void *arg) __attribute__((deprecated));
void *RSA_get_ex_data(const RSA *r, int idx) __attribute__((deprecated));

RSA *RSAPublicKey_dup(RSA *rsa) __attribute__((deprecated));
RSA *RSAPrivateKey_dup(RSA *rsa) __attribute__((deprecated));





void ERR_load_RSA_strings(void) __attribute__((deprecated));
# 102 "_ssl.c" 2

# 1 "/usr/include/openssl/x509.h" 1 3 4
# 69 "/usr/include/openssl/x509.h" 3 4
# 1 "/usr/include/openssl/e_os2.h" 1 3 4
# 56 "/usr/include/openssl/e_os2.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 57 "/usr/include/openssl/e_os2.h" 2 3 4
# 70 "/usr/include/openssl/x509.h" 2 3 4
# 1 "/usr/include/openssl/symhacks.h" 1 3 4
# 71 "/usr/include/openssl/x509.h" 2 3 4

# 1 "/usr/include/openssl/buffer.h" 1 3 4
# 70 "/usr/include/openssl/buffer.h" 3 4
# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stddef.h" 1 3 4
# 152 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stddef.h" 3 4
typedef long int ptrdiff_t;
# 71 "/usr/include/openssl/buffer.h" 2 3 4
# 79 "/usr/include/openssl/buffer.h" 3 4
struct buf_mem_st
 {
 int length;
 char *data;
 int max;
 };

BUF_MEM *BUF_MEM_new(void) __attribute__((deprecated));
void BUF_MEM_free(BUF_MEM *a) __attribute__((deprecated));
int BUF_MEM_grow(BUF_MEM *str, int len) __attribute__((deprecated));
int BUF_MEM_grow_clean(BUF_MEM *str, int len) __attribute__((deprecated));
char * BUF_strdup(const char *str) __attribute__((deprecated));
char * BUF_strndup(const char *str, size_t siz) __attribute__((deprecated));
void * BUF_memdup(const void *data, size_t siz) __attribute__((deprecated));


size_t BUF_strlcpy(char *dst,const char *src,size_t siz) __attribute__((deprecated));
size_t BUF_strlcat(char *dst,const char *src,size_t siz) __attribute__((deprecated));






void ERR_load_BUF_strings(void) __attribute__((deprecated));
# 73 "/usr/include/openssl/x509.h" 2 3 4


# 1 "/usr/include/openssl/evp.h" 1 3 4
# 68 "/usr/include/openssl/evp.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 69 "/usr/include/openssl/evp.h" 2 3 4





# 1 "/usr/include/openssl/symhacks.h" 1 3 4
# 75 "/usr/include/openssl/evp.h" 2 3 4
# 100 "/usr/include/openssl/evp.h" 3 4
# 1 "/usr/include/openssl/objects.h" 1 3 4
# 67 "/usr/include/openssl/objects.h" 3 4
# 1 "/usr/include/openssl/obj_mac.h" 1 3 4
# 68 "/usr/include/openssl/objects.h" 2 3 4
# 981 "/usr/include/openssl/objects.h" 3 4
typedef struct obj_name_st
 {
 int type;
 int alias;
 const char *name;
 const char *data;
 } OBJ_NAME;




int OBJ_NAME_init(void) __attribute__((deprecated));
int OBJ_NAME_new_index(unsigned long (*hash_func)(const char *),
         int (*cmp_func)(const char *, const char *),
         void (*free_func)(const char *, int, const char *)) __attribute__((deprecated));
const char *OBJ_NAME_get(const char *name,int type) __attribute__((deprecated));
int OBJ_NAME_add(const char *name,int type,const char *data) __attribute__((deprecated));
int OBJ_NAME_remove(const char *name,int type) __attribute__((deprecated));
void OBJ_NAME_cleanup(int type) __attribute__((deprecated));
void OBJ_NAME_do_all(int type,void (*fn)(const OBJ_NAME *,void *arg),
       void *arg) __attribute__((deprecated));
void OBJ_NAME_do_all_sorted(int type,void (*fn)(const OBJ_NAME *,void *arg),
       void *arg) __attribute__((deprecated));

ASN1_OBJECT * OBJ_dup(const ASN1_OBJECT *o) __attribute__((deprecated));
ASN1_OBJECT * OBJ_nid2obj(int n) __attribute__((deprecated));
const char * OBJ_nid2ln(int n) __attribute__((deprecated));
const char * OBJ_nid2sn(int n) __attribute__((deprecated));
int OBJ_obj2nid(const ASN1_OBJECT *o) __attribute__((deprecated));
ASN1_OBJECT * OBJ_txt2obj(const char *s, int no_name) __attribute__((deprecated));
int OBJ_obj2txt(char *buf, int buf_len, const ASN1_OBJECT *a, int no_name) __attribute__((deprecated));
int OBJ_txt2nid(const char *s) __attribute__((deprecated));
int OBJ_ln2nid(const char *s) __attribute__((deprecated));
int OBJ_sn2nid(const char *s) __attribute__((deprecated));
int OBJ_cmp(const ASN1_OBJECT *a,const ASN1_OBJECT *b) __attribute__((deprecated));
const char * OBJ_bsearch(const char *key,const char *base,int num,int size,
 int (*cmp)(const void *, const void *)) __attribute__((deprecated));
const char * OBJ_bsearch_ex(const char *key,const char *base,int num,
 int size, int (*cmp)(const void *, const void *), int flags) __attribute__((deprecated));

int OBJ_new_nid(int num) __attribute__((deprecated));
int OBJ_add_object(const ASN1_OBJECT *obj) __attribute__((deprecated));
int OBJ_create(const char *oid,const char *sn,const char *ln) __attribute__((deprecated));
void OBJ_cleanup(void ) __attribute__((deprecated));
int OBJ_create_objects(BIO *in) __attribute__((deprecated));





void ERR_load_OBJ_strings(void) __attribute__((deprecated));
# 101 "/usr/include/openssl/evp.h" 2 3 4
# 132 "/usr/include/openssl/evp.h" 3 4
struct evp_pkey_st
 {
 int type;
 int save_type;
 int references;
 union {
  char *ptr;

  struct rsa_st *rsa;


  struct dsa_st *dsa;


  struct dh_st *dh;


  struct ec_key_st *ec;

  } pkey;
 int save_parameters;
 STACK *attributes;
 } ;
# 229 "/usr/include/openssl/evp.h" 3 4
struct env_md_st
 {
 int type;
 int pkey_type;
 int md_size;
 unsigned long flags;
 int (*init)(EVP_MD_CTX *ctx);
 int (*update)(EVP_MD_CTX *ctx,const void *data,size_t count);
 int (*final)(EVP_MD_CTX *ctx,unsigned char *md);
 int (*copy)(EVP_MD_CTX *to,const EVP_MD_CTX *from);
 int (*cleanup)(EVP_MD_CTX *ctx);


 int (*sign)(int type, const unsigned char *m, unsigned int m_length,
      unsigned char *sigret, unsigned int *siglen, void *key);
 int (*verify)(int type, const unsigned char *m, unsigned int m_length,
        const unsigned char *sigbuf, unsigned int siglen,
        void *key);
 int required_pkey_type[5];
 int block_size;
 int ctx_size;
 } ;

typedef int evp_sign_method(int type,const unsigned char *m,
       unsigned int m_length,unsigned char *sigret,
       unsigned int *siglen, void *key);
typedef int evp_verify_method(int type,const unsigned char *m,
       unsigned int m_length,const unsigned char *sigbuf,
       unsigned int siglen, void *key);

typedef struct
 {
 EVP_MD_CTX *mctx;
 void *key;
 } EVP_MD_SVCTX;
# 306 "/usr/include/openssl/evp.h" 3 4
struct env_md_ctx_st
 {
 const EVP_MD *digest;
 ENGINE *engine;
 unsigned long flags;
 void *md_data;
 } ;
# 334 "/usr/include/openssl/evp.h" 3 4
struct evp_cipher_st
 {
 int nid;
 int block_size;
 int key_len;
 int iv_len;
 unsigned long flags;
 int (*init)(EVP_CIPHER_CTX *ctx, const unsigned char *key,
      const unsigned char *iv, int enc);
 int (*do_cipher)(EVP_CIPHER_CTX *ctx, unsigned char *out,
    const unsigned char *in, unsigned int inl);
 int (*cleanup)(EVP_CIPHER_CTX *);
 int ctx_size;
 int (*set_asn1_parameters)(EVP_CIPHER_CTX *, ASN1_TYPE *);
 int (*get_asn1_parameters)(EVP_CIPHER_CTX *, ASN1_TYPE *);
 int (*ctrl)(EVP_CIPHER_CTX *, int type, int arg, void *ptr);
 void *app_data;
 } ;
# 396 "/usr/include/openssl/evp.h" 3 4
typedef struct evp_cipher_info_st
 {
 const EVP_CIPHER *cipher;
 unsigned char iv[16];
 } EVP_CIPHER_INFO;

struct evp_cipher_ctx_st
 {
 const EVP_CIPHER *cipher;
 ENGINE *engine;
 int encrypt;
 int buf_len;

 unsigned char oiv[16];
 unsigned char iv[16];
 unsigned char buf[32];
 int num;

 void *app_data;
 int key_len;
 unsigned long flags;
 void *cipher_data;
 int final_used;
 int block_mask;
 unsigned char final[32];
 } ;

typedef struct evp_Encode_Ctx_st
 {
 int num;
 int length;




 unsigned char enc_data[80];
 int line_num;
 int expect_nl;
 } EVP_ENCODE_CTX;


typedef int (EVP_PBE_KEYGEN)(EVP_CIPHER_CTX *ctx, const char *pass, int passlen,
  ASN1_TYPE *param, const EVP_CIPHER *cipher,
                const EVP_MD *md, int en_de);
# 479 "/usr/include/openssl/evp.h" 3 4
int EVP_MD_type(const EVP_MD *md) __attribute__((deprecated));


int EVP_MD_pkey_type(const EVP_MD *md) __attribute__((deprecated));
int EVP_MD_size(const EVP_MD *md) __attribute__((deprecated));
int EVP_MD_block_size(const EVP_MD *md) __attribute__((deprecated));

const EVP_MD * EVP_MD_CTX_md(const EVP_MD_CTX *ctx) __attribute__((deprecated));




int EVP_CIPHER_nid(const EVP_CIPHER *cipher) __attribute__((deprecated));

int EVP_CIPHER_block_size(const EVP_CIPHER *cipher) __attribute__((deprecated));
int EVP_CIPHER_key_length(const EVP_CIPHER *cipher) __attribute__((deprecated));
int EVP_CIPHER_iv_length(const EVP_CIPHER *cipher) __attribute__((deprecated));
unsigned long EVP_CIPHER_flags(const EVP_CIPHER *cipher) __attribute__((deprecated));


const EVP_CIPHER * EVP_CIPHER_CTX_cipher(const EVP_CIPHER_CTX *ctx) __attribute__((deprecated));
int EVP_CIPHER_CTX_nid(const EVP_CIPHER_CTX *ctx) __attribute__((deprecated));
int EVP_CIPHER_CTX_block_size(const EVP_CIPHER_CTX *ctx) __attribute__((deprecated));
int EVP_CIPHER_CTX_key_length(const EVP_CIPHER_CTX *ctx) __attribute__((deprecated));
int EVP_CIPHER_CTX_iv_length(const EVP_CIPHER_CTX *ctx) __attribute__((deprecated));
void * EVP_CIPHER_CTX_get_app_data(const EVP_CIPHER_CTX *ctx) __attribute__((deprecated));
void EVP_CIPHER_CTX_set_app_data(EVP_CIPHER_CTX *ctx, void *data) __attribute__((deprecated));

unsigned long EVP_CIPHER_CTX_flags(const EVP_CIPHER_CTX *ctx) __attribute__((deprecated));
# 533 "/usr/include/openssl/evp.h" 3 4
int EVP_Cipher(EVP_CIPHER_CTX *c,
  unsigned char *out,
  const unsigned char *in,
  unsigned int inl) __attribute__((deprecated));
# 547 "/usr/include/openssl/evp.h" 3 4
void EVP_MD_CTX_init(EVP_MD_CTX *ctx) __attribute__((deprecated));
int EVP_MD_CTX_cleanup(EVP_MD_CTX *ctx) __attribute__((deprecated));
EVP_MD_CTX *EVP_MD_CTX_create(void) __attribute__((deprecated));
void EVP_MD_CTX_destroy(EVP_MD_CTX *ctx) __attribute__((deprecated));
int EVP_MD_CTX_copy_ex(EVP_MD_CTX *out,const EVP_MD_CTX *in) __attribute__((deprecated));
void EVP_MD_CTX_set_flags(EVP_MD_CTX *ctx, int flags) __attribute__((deprecated));
void EVP_MD_CTX_clear_flags(EVP_MD_CTX *ctx, int flags) __attribute__((deprecated));
int EVP_MD_CTX_test_flags(const EVP_MD_CTX *ctx,int flags) __attribute__((deprecated));
int EVP_DigestInit_ex(EVP_MD_CTX *ctx, const EVP_MD *type, ENGINE *impl) __attribute__((deprecated));
int EVP_DigestUpdate(EVP_MD_CTX *ctx,const void *d,
    size_t cnt) __attribute__((deprecated));
int EVP_DigestFinal_ex(EVP_MD_CTX *ctx,unsigned char *md,unsigned int *s) __attribute__((deprecated));
int EVP_Digest(const void *data, size_t count,
  unsigned char *md, unsigned int *size, const EVP_MD *type, ENGINE *impl) __attribute__((deprecated));

int EVP_MD_CTX_copy(EVP_MD_CTX *out,const EVP_MD_CTX *in) __attribute__((deprecated));
int EVP_DigestInit(EVP_MD_CTX *ctx, const EVP_MD *type) __attribute__((deprecated));
int EVP_DigestFinal(EVP_MD_CTX *ctx,unsigned char *md,unsigned int *s) __attribute__((deprecated));

int EVP_read_pw_string(char *buf,int length,const char *prompt,int verify) __attribute__((deprecated));
void EVP_set_pw_prompt(const char *prompt) __attribute__((deprecated));
char * EVP_get_pw_prompt(void) __attribute__((deprecated));

int EVP_BytesToKey(const EVP_CIPHER *type,const EVP_MD *md,
  const unsigned char *salt, const unsigned char *data,
  int datal, int count, unsigned char *key,unsigned char *iv) __attribute__((deprecated));

void EVP_CIPHER_CTX_set_flags(EVP_CIPHER_CTX *ctx, int flags) __attribute__((deprecated));
void EVP_CIPHER_CTX_clear_flags(EVP_CIPHER_CTX *ctx, int flags) __attribute__((deprecated));
int EVP_CIPHER_CTX_test_flags(const EVP_CIPHER_CTX *ctx,int flags) __attribute__((deprecated));

int EVP_EncryptInit(EVP_CIPHER_CTX *ctx,const EVP_CIPHER *cipher,
  const unsigned char *key, const unsigned char *iv) __attribute__((deprecated));
int EVP_EncryptInit_ex(EVP_CIPHER_CTX *ctx,const EVP_CIPHER *cipher, ENGINE *impl,
  const unsigned char *key, const unsigned char *iv) __attribute__((deprecated));
int EVP_EncryptUpdate(EVP_CIPHER_CTX *ctx, unsigned char *out,
  int *outl, const unsigned char *in, int inl) __attribute__((deprecated));
int EVP_EncryptFinal_ex(EVP_CIPHER_CTX *ctx, unsigned char *out, int *outl) __attribute__((deprecated));
int EVP_EncryptFinal(EVP_CIPHER_CTX *ctx, unsigned char *out, int *outl) __attribute__((deprecated));

int EVP_DecryptInit(EVP_CIPHER_CTX *ctx,const EVP_CIPHER *cipher,
  const unsigned char *key, const unsigned char *iv) __attribute__((deprecated));
int EVP_DecryptInit_ex(EVP_CIPHER_CTX *ctx,const EVP_CIPHER *cipher, ENGINE *impl,
  const unsigned char *key, const unsigned char *iv) __attribute__((deprecated));
int EVP_DecryptUpdate(EVP_CIPHER_CTX *ctx, unsigned char *out,
  int *outl, const unsigned char *in, int inl) __attribute__((deprecated));
int EVP_DecryptFinal(EVP_CIPHER_CTX *ctx, unsigned char *outm, int *outl) __attribute__((deprecated));
int EVP_DecryptFinal_ex(EVP_CIPHER_CTX *ctx, unsigned char *outm, int *outl) __attribute__((deprecated));

int EVP_CipherInit(EVP_CIPHER_CTX *ctx,const EVP_CIPHER *cipher,
         const unsigned char *key,const unsigned char *iv,
         int enc) __attribute__((deprecated));
int EVP_CipherInit_ex(EVP_CIPHER_CTX *ctx,const EVP_CIPHER *cipher, ENGINE *impl,
         const unsigned char *key,const unsigned char *iv,
         int enc) __attribute__((deprecated));
int EVP_CipherUpdate(EVP_CIPHER_CTX *ctx, unsigned char *out,
  int *outl, const unsigned char *in, int inl) __attribute__((deprecated));
int EVP_CipherFinal(EVP_CIPHER_CTX *ctx, unsigned char *outm, int *outl) __attribute__((deprecated));
int EVP_CipherFinal_ex(EVP_CIPHER_CTX *ctx, unsigned char *outm, int *outl) __attribute__((deprecated));

int EVP_SignFinal(EVP_MD_CTX *ctx,unsigned char *md,unsigned int *s,
  EVP_PKEY *pkey) __attribute__((deprecated));

int EVP_VerifyFinal(EVP_MD_CTX *ctx,const unsigned char *sigbuf,
  unsigned int siglen,EVP_PKEY *pkey) __attribute__((deprecated));

int EVP_OpenInit(EVP_CIPHER_CTX *ctx,const EVP_CIPHER *type,
  const unsigned char *ek, int ekl, const unsigned char *iv,
  EVP_PKEY *priv) __attribute__((deprecated));
int EVP_OpenFinal(EVP_CIPHER_CTX *ctx, unsigned char *out, int *outl) __attribute__((deprecated));

int EVP_SealInit(EVP_CIPHER_CTX *ctx, const EVP_CIPHER *type,
   unsigned char **ek, int *ekl, unsigned char *iv,
  EVP_PKEY **pubk, int npubk) __attribute__((deprecated));
int EVP_SealFinal(EVP_CIPHER_CTX *ctx,unsigned char *out,int *outl) __attribute__((deprecated));

void EVP_EncodeInit(EVP_ENCODE_CTX *ctx) __attribute__((deprecated));
void EVP_EncodeUpdate(EVP_ENCODE_CTX *ctx,unsigned char *out,int *outl,
  const unsigned char *in,int inl) __attribute__((deprecated));
void EVP_EncodeFinal(EVP_ENCODE_CTX *ctx,unsigned char *out,int *outl) __attribute__((deprecated));
int EVP_EncodeBlock(unsigned char *t, const unsigned char *f, int n) __attribute__((deprecated));

void EVP_DecodeInit(EVP_ENCODE_CTX *ctx) __attribute__((deprecated));
int EVP_DecodeUpdate(EVP_ENCODE_CTX *ctx,unsigned char *out,int *outl,
  const unsigned char *in, int inl) __attribute__((deprecated));
int EVP_DecodeFinal(EVP_ENCODE_CTX *ctx, unsigned
  char *out, int *outl) __attribute__((deprecated));
int EVP_DecodeBlock(unsigned char *t, const unsigned char *f, int n) __attribute__((deprecated));

void EVP_CIPHER_CTX_init(EVP_CIPHER_CTX *a) __attribute__((deprecated));
int EVP_CIPHER_CTX_cleanup(EVP_CIPHER_CTX *a) __attribute__((deprecated));
EVP_CIPHER_CTX *EVP_CIPHER_CTX_new(void) __attribute__((deprecated));
void EVP_CIPHER_CTX_free(EVP_CIPHER_CTX *a) __attribute__((deprecated));
int EVP_CIPHER_CTX_set_key_length(EVP_CIPHER_CTX *x, int keylen) __attribute__((deprecated));
int EVP_CIPHER_CTX_set_padding(EVP_CIPHER_CTX *c, int pad) __attribute__((deprecated));
int EVP_CIPHER_CTX_ctrl(EVP_CIPHER_CTX *ctx, int type, int arg, void *ptr) __attribute__((deprecated));
int EVP_CIPHER_CTX_rand_key(EVP_CIPHER_CTX *ctx, unsigned char *key) __attribute__((deprecated));


BIO_METHOD *BIO_f_md(void) __attribute__((deprecated));
BIO_METHOD *BIO_f_base64(void) __attribute__((deprecated));
BIO_METHOD *BIO_f_cipher(void) __attribute__((deprecated));
BIO_METHOD *BIO_f_reliable(void) __attribute__((deprecated));
void BIO_set_cipher(BIO *b,const EVP_CIPHER *c,const unsigned char *k,
  const unsigned char *i, int enc) __attribute__((deprecated));


const EVP_MD *EVP_md_null(void) __attribute__((deprecated));

const EVP_MD *EVP_md2(void) __attribute__((deprecated));


const EVP_MD *EVP_md4(void) __attribute__((deprecated));


const EVP_MD *EVP_md5(void) __attribute__((deprecated));


const EVP_MD *EVP_sha(void) __attribute__((deprecated));
const EVP_MD *EVP_sha1(void) __attribute__((deprecated));
const EVP_MD *EVP_dss(void) __attribute__((deprecated));
const EVP_MD *EVP_dss1(void) __attribute__((deprecated));
const EVP_MD *EVP_ecdsa(void) __attribute__((deprecated));


const EVP_MD *EVP_sha224(void) __attribute__((deprecated));
const EVP_MD *EVP_sha256(void) __attribute__((deprecated));


const EVP_MD *EVP_sha384(void) __attribute__((deprecated));
const EVP_MD *EVP_sha512(void) __attribute__((deprecated));


const EVP_MD *EVP_mdc2(void) __attribute__((deprecated));


const EVP_MD *EVP_ripemd160(void) __attribute__((deprecated));

const EVP_CIPHER *EVP_enc_null(void) __attribute__((deprecated));

const EVP_CIPHER *EVP_des_ecb(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_des_ede(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_des_ede3(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_des_ede_ecb(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_des_ede3_ecb(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_des_cfb64(void) __attribute__((deprecated));

const EVP_CIPHER *EVP_des_cfb1(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_des_cfb8(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_des_ede_cfb64(void) __attribute__((deprecated));





const EVP_CIPHER *EVP_des_ede3_cfb64(void) __attribute__((deprecated));

const EVP_CIPHER *EVP_des_ede3_cfb1(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_des_ede3_cfb8(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_des_ofb(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_des_ede_ofb(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_des_ede3_ofb(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_des_cbc(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_des_ede_cbc(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_des_ede3_cbc(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_desx_cbc(void) __attribute__((deprecated));
# 724 "/usr/include/openssl/evp.h" 3 4
const EVP_CIPHER *EVP_rc4(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_rc4_40(void) __attribute__((deprecated));
# 735 "/usr/include/openssl/evp.h" 3 4
const EVP_CIPHER *EVP_rc2_ecb(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_rc2_cbc(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_rc2_40_cbc(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_rc2_64_cbc(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_rc2_cfb64(void) __attribute__((deprecated));

const EVP_CIPHER *EVP_rc2_ofb(void) __attribute__((deprecated));


const EVP_CIPHER *EVP_bf_ecb(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_bf_cbc(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_bf_cfb64(void) __attribute__((deprecated));

const EVP_CIPHER *EVP_bf_ofb(void) __attribute__((deprecated));


const EVP_CIPHER *EVP_cast5_ecb(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_cast5_cbc(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_cast5_cfb64(void) __attribute__((deprecated));

const EVP_CIPHER *EVP_cast5_ofb(void) __attribute__((deprecated));


const EVP_CIPHER *EVP_rc5_32_12_16_cbc(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_rc5_32_12_16_ecb(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_rc5_32_12_16_cfb64(void) __attribute__((deprecated));

const EVP_CIPHER *EVP_rc5_32_12_16_ofb(void) __attribute__((deprecated));


const EVP_CIPHER *EVP_aes_128_ecb(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_aes_128_cbc(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_aes_128_cfb1(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_aes_128_cfb8(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_aes_128_cfb128(void) __attribute__((deprecated));

const EVP_CIPHER *EVP_aes_128_ofb(void) __attribute__((deprecated));



const EVP_CIPHER *EVP_aes_192_ecb(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_aes_192_cbc(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_aes_192_cfb1(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_aes_192_cfb8(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_aes_192_cfb128(void) __attribute__((deprecated));

const EVP_CIPHER *EVP_aes_192_ofb(void) __attribute__((deprecated));



const EVP_CIPHER *EVP_aes_256_ecb(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_aes_256_cbc(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_aes_256_cfb1(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_aes_256_cfb8(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_aes_256_cfb128(void) __attribute__((deprecated));

const EVP_CIPHER *EVP_aes_256_ofb(void) __attribute__((deprecated));
# 821 "/usr/include/openssl/evp.h" 3 4
const EVP_CIPHER *EVP_seed_ecb(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_seed_cbc(void) __attribute__((deprecated));
const EVP_CIPHER *EVP_seed_cfb128(void) __attribute__((deprecated));

const EVP_CIPHER *EVP_seed_ofb(void) __attribute__((deprecated));


void OPENSSL_add_all_algorithms_noconf(void) __attribute__((deprecated));
void OPENSSL_add_all_algorithms_conf(void) __attribute__((deprecated));
# 839 "/usr/include/openssl/evp.h" 3 4
void OpenSSL_add_all_ciphers(void) __attribute__((deprecated));
void OpenSSL_add_all_digests(void) __attribute__((deprecated));




int EVP_add_cipher(const EVP_CIPHER *cipher) __attribute__((deprecated));
int EVP_add_digest(const EVP_MD *digest) __attribute__((deprecated));

const EVP_CIPHER *EVP_get_cipherbyname(const char *name) __attribute__((deprecated));
const EVP_MD *EVP_get_digestbyname(const char *name) __attribute__((deprecated));
void EVP_cleanup(void) __attribute__((deprecated));

int EVP_PKEY_decrypt(unsigned char *dec_key,
   const unsigned char *enc_key,int enc_key_len,
   EVP_PKEY *private_key) __attribute__((deprecated));
int EVP_PKEY_encrypt(unsigned char *enc_key,
   const unsigned char *key,int key_len,
   EVP_PKEY *pub_key) __attribute__((deprecated));
int EVP_PKEY_type(int type) __attribute__((deprecated));
int EVP_PKEY_bits(EVP_PKEY *pkey) __attribute__((deprecated));
int EVP_PKEY_size(EVP_PKEY *pkey) __attribute__((deprecated));
int EVP_PKEY_assign(EVP_PKEY *pkey,int type,char *key) __attribute__((deprecated));


struct rsa_st;
int EVP_PKEY_set1_RSA(EVP_PKEY *pkey,struct rsa_st *key) __attribute__((deprecated));
struct rsa_st *EVP_PKEY_get1_RSA(EVP_PKEY *pkey) __attribute__((deprecated));


struct dsa_st;
int EVP_PKEY_set1_DSA(EVP_PKEY *pkey,struct dsa_st *key) __attribute__((deprecated));
struct dsa_st *EVP_PKEY_get1_DSA(EVP_PKEY *pkey) __attribute__((deprecated));


struct dh_st;
int EVP_PKEY_set1_DH(EVP_PKEY *pkey,struct dh_st *key) __attribute__((deprecated));
struct dh_st *EVP_PKEY_get1_DH(EVP_PKEY *pkey) __attribute__((deprecated));


struct ec_key_st;
int EVP_PKEY_set1_EC_KEY(EVP_PKEY *pkey,struct ec_key_st *key) __attribute__((deprecated));
struct ec_key_st *EVP_PKEY_get1_EC_KEY(EVP_PKEY *pkey) __attribute__((deprecated));


EVP_PKEY * EVP_PKEY_new(void) __attribute__((deprecated));
void EVP_PKEY_free(EVP_PKEY *pkey) __attribute__((deprecated));

EVP_PKEY * d2i_PublicKey(int type,EVP_PKEY **a, const unsigned char **pp,
   long length) __attribute__((deprecated));
int i2d_PublicKey(EVP_PKEY *a, unsigned char **pp) __attribute__((deprecated));

EVP_PKEY * d2i_PrivateKey(int type,EVP_PKEY **a, const unsigned char **pp,
   long length) __attribute__((deprecated));
EVP_PKEY * d2i_AutoPrivateKey(EVP_PKEY **a, const unsigned char **pp,
   long length) __attribute__((deprecated));
int i2d_PrivateKey(EVP_PKEY *a, unsigned char **pp) __attribute__((deprecated));

int EVP_PKEY_copy_parameters(EVP_PKEY *to, const EVP_PKEY *from) __attribute__((deprecated));
int EVP_PKEY_missing_parameters(const EVP_PKEY *pkey) __attribute__((deprecated));
int EVP_PKEY_save_parameters(EVP_PKEY *pkey,int mode) __attribute__((deprecated));
int EVP_PKEY_cmp_parameters(const EVP_PKEY *a, const EVP_PKEY *b) __attribute__((deprecated));

int EVP_PKEY_cmp(const EVP_PKEY *a, const EVP_PKEY *b) __attribute__((deprecated));

int EVP_CIPHER_type(const EVP_CIPHER *ctx) __attribute__((deprecated));


int EVP_CIPHER_param_to_asn1(EVP_CIPHER_CTX *c, ASN1_TYPE *type) __attribute__((deprecated));
int EVP_CIPHER_asn1_to_param(EVP_CIPHER_CTX *c, ASN1_TYPE *type) __attribute__((deprecated));


int EVP_CIPHER_set_asn1_iv(EVP_CIPHER_CTX *c,ASN1_TYPE *type) __attribute__((deprecated));
int EVP_CIPHER_get_asn1_iv(EVP_CIPHER_CTX *c,ASN1_TYPE *type) __attribute__((deprecated));


int PKCS5_PBE_keyivgen(EVP_CIPHER_CTX *ctx, const char *pass, int passlen,
    ASN1_TYPE *param, const EVP_CIPHER *cipher, const EVP_MD *md,
    int en_de) __attribute__((deprecated));
int PKCS5_PBKDF2_HMAC_SHA1(const char *pass, int passlen,
      const unsigned char *salt, int saltlen, int iter,
      int keylen, unsigned char *out) __attribute__((deprecated));
int PKCS5_v2_PBE_keyivgen(EVP_CIPHER_CTX *ctx, const char *pass, int passlen,
    ASN1_TYPE *param, const EVP_CIPHER *cipher, const EVP_MD *md,
    int en_de) __attribute__((deprecated));

void PKCS5_PBE_add(void) __attribute__((deprecated));

int EVP_PBE_CipherInit (ASN1_OBJECT *pbe_obj, const char *pass, int passlen,
      ASN1_TYPE *param, EVP_CIPHER_CTX *ctx, int en_de) __attribute__((deprecated));
int EVP_PBE_alg_add(int nid, const EVP_CIPHER *cipher, const EVP_MD *md,
      EVP_PBE_KEYGEN *keygen) __attribute__((deprecated));
void EVP_PBE_cleanup(void) __attribute__((deprecated));
# 949 "/usr/include/openssl/evp.h" 3 4
void EVP_add_alg_module(void) __attribute__((deprecated));





void ERR_load_EVP_strings(void) __attribute__((deprecated));
# 76 "/usr/include/openssl/x509.h" 2 3 4
# 85 "/usr/include/openssl/x509.h" 3 4
# 1 "/usr/include/openssl/ec.h" 1 3 4
# 77 "/usr/include/openssl/ec.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 78 "/usr/include/openssl/ec.h" 2 3 4






# 1 "/usr/include/openssl/symhacks.h" 1 3 4
# 85 "/usr/include/openssl/ec.h" 2 3 4
# 102 "/usr/include/openssl/ec.h" 3 4
typedef enum {

 POINT_CONVERSION_COMPRESSED = 2,
 POINT_CONVERSION_UNCOMPRESSED = 4,
 POINT_CONVERSION_HYBRID = 6
} point_conversion_form_t;


typedef struct ec_method_st EC_METHOD;

typedef struct ec_group_st
# 121 "/usr/include/openssl/ec.h" 3 4
 EC_GROUP;

typedef struct ec_point_st EC_POINT;





const EC_METHOD *EC_GFp_simple_method(void) __attribute__((deprecated));
const EC_METHOD *EC_GFp_mont_method(void) __attribute__((deprecated));
const EC_METHOD *EC_GFp_nist_method(void) __attribute__((deprecated));



const EC_METHOD *EC_GF2m_simple_method(void) __attribute__((deprecated));


EC_GROUP *EC_GROUP_new(const EC_METHOD *) __attribute__((deprecated));
void EC_GROUP_free(EC_GROUP *) __attribute__((deprecated));
void EC_GROUP_clear_free(EC_GROUP *) __attribute__((deprecated));
int EC_GROUP_copy(EC_GROUP *, const EC_GROUP *) __attribute__((deprecated));
EC_GROUP *EC_GROUP_dup(const EC_GROUP *) __attribute__((deprecated));

const EC_METHOD *EC_GROUP_method_of(const EC_GROUP *) __attribute__((deprecated));
int EC_METHOD_get_field_type(const EC_METHOD *) __attribute__((deprecated));

int EC_GROUP_set_generator(EC_GROUP *, const EC_POINT *generator, const BIGNUM *order, const BIGNUM *cofactor) __attribute__((deprecated));
const EC_POINT *EC_GROUP_get0_generator(const EC_GROUP *) __attribute__((deprecated));
int EC_GROUP_get_order(const EC_GROUP *, BIGNUM *order, BN_CTX *) __attribute__((deprecated));
int EC_GROUP_get_cofactor(const EC_GROUP *, BIGNUM *cofactor, BN_CTX *) __attribute__((deprecated));

void EC_GROUP_set_curve_name(EC_GROUP *, int nid) __attribute__((deprecated));
int EC_GROUP_get_curve_name(const EC_GROUP *) __attribute__((deprecated));

void EC_GROUP_set_asn1_flag(EC_GROUP *, int flag) __attribute__((deprecated));
int EC_GROUP_get_asn1_flag(const EC_GROUP *) __attribute__((deprecated));

void EC_GROUP_set_point_conversion_form(EC_GROUP *, point_conversion_form_t) __attribute__((deprecated));
point_conversion_form_t EC_GROUP_get_point_conversion_form(const EC_GROUP *) __attribute__((deprecated));

unsigned char *EC_GROUP_get0_seed(const EC_GROUP *) __attribute__((deprecated));
size_t EC_GROUP_get_seed_len(const EC_GROUP *) __attribute__((deprecated));
size_t EC_GROUP_set_seed(EC_GROUP *, const unsigned char *, size_t len) __attribute__((deprecated));

int EC_GROUP_set_curve_GFp(EC_GROUP *, const BIGNUM *p, const BIGNUM *a, const BIGNUM *b, BN_CTX *) __attribute__((deprecated));
int EC_GROUP_get_curve_GFp(const EC_GROUP *, BIGNUM *p, BIGNUM *a, BIGNUM *b, BN_CTX *) __attribute__((deprecated));
int EC_GROUP_set_curve_GF2m(EC_GROUP *, const BIGNUM *p, const BIGNUM *a, const BIGNUM *b, BN_CTX *) __attribute__((deprecated));
int EC_GROUP_get_curve_GF2m(const EC_GROUP *, BIGNUM *p, BIGNUM *a, BIGNUM *b, BN_CTX *) __attribute__((deprecated));


int EC_GROUP_get_degree(const EC_GROUP *) __attribute__((deprecated));


int EC_GROUP_check(const EC_GROUP *group, BN_CTX *ctx) __attribute__((deprecated));


int EC_GROUP_check_discriminant(const EC_GROUP *, BN_CTX *) __attribute__((deprecated));


int EC_GROUP_cmp(const EC_GROUP *, const EC_GROUP *, BN_CTX *) __attribute__((deprecated));



EC_GROUP *EC_GROUP_new_curve_GFp(const BIGNUM *p, const BIGNUM *a, const BIGNUM *b, BN_CTX *) __attribute__((deprecated));
EC_GROUP *EC_GROUP_new_curve_GF2m(const BIGNUM *p, const BIGNUM *a, const BIGNUM *b, BN_CTX *) __attribute__((deprecated));



EC_GROUP *EC_GROUP_new_by_curve_name(int nid) __attribute__((deprecated));

typedef struct {
 int nid;
 const char *comment;
 } EC_builtin_curve;




size_t EC_get_builtin_curves(EC_builtin_curve *r, size_t nitems) __attribute__((deprecated));




EC_POINT *EC_POINT_new(const EC_GROUP *) __attribute__((deprecated));
void EC_POINT_free(EC_POINT *) __attribute__((deprecated));
void EC_POINT_clear_free(EC_POINT *) __attribute__((deprecated));
int EC_POINT_copy(EC_POINT *, const EC_POINT *) __attribute__((deprecated));
EC_POINT *EC_POINT_dup(const EC_POINT *, const EC_GROUP *) __attribute__((deprecated));

const EC_METHOD *EC_POINT_method_of(const EC_POINT *) __attribute__((deprecated));

int EC_POINT_set_to_infinity(const EC_GROUP *, EC_POINT *) __attribute__((deprecated));
int EC_POINT_set_Jprojective_coordinates_GFp(const EC_GROUP *, EC_POINT *,
 const BIGNUM *x, const BIGNUM *y, const BIGNUM *z, BN_CTX *) __attribute__((deprecated));
int EC_POINT_get_Jprojective_coordinates_GFp(const EC_GROUP *, const EC_POINT *,
 BIGNUM *x, BIGNUM *y, BIGNUM *z, BN_CTX *) __attribute__((deprecated));
int EC_POINT_set_affine_coordinates_GFp(const EC_GROUP *, EC_POINT *,
 const BIGNUM *x, const BIGNUM *y, BN_CTX *) __attribute__((deprecated));
int EC_POINT_get_affine_coordinates_GFp(const EC_GROUP *, const EC_POINT *,
 BIGNUM *x, BIGNUM *y, BN_CTX *) __attribute__((deprecated));
int EC_POINT_set_compressed_coordinates_GFp(const EC_GROUP *, EC_POINT *,
 const BIGNUM *x, int y_bit, BN_CTX *) __attribute__((deprecated));

int EC_POINT_set_affine_coordinates_GF2m(const EC_GROUP *, EC_POINT *,
 const BIGNUM *x, const BIGNUM *y, BN_CTX *) __attribute__((deprecated));
int EC_POINT_get_affine_coordinates_GF2m(const EC_GROUP *, const EC_POINT *,
 BIGNUM *x, BIGNUM *y, BN_CTX *) __attribute__((deprecated));
int EC_POINT_set_compressed_coordinates_GF2m(const EC_GROUP *, EC_POINT *,
 const BIGNUM *x, int y_bit, BN_CTX *) __attribute__((deprecated));

size_t EC_POINT_point2oct(const EC_GROUP *, const EC_POINT *, point_conversion_form_t form,
        unsigned char *buf, size_t len, BN_CTX *) __attribute__((deprecated));
int EC_POINT_oct2point(const EC_GROUP *, EC_POINT *,
        const unsigned char *buf, size_t len, BN_CTX *) __attribute__((deprecated));


BIGNUM *EC_POINT_point2bn(const EC_GROUP *, const EC_POINT *,
 point_conversion_form_t form, BIGNUM *, BN_CTX *) __attribute__((deprecated));
EC_POINT *EC_POINT_bn2point(const EC_GROUP *, const BIGNUM *,
 EC_POINT *, BN_CTX *) __attribute__((deprecated));
char *EC_POINT_point2hex(const EC_GROUP *, const EC_POINT *,
 point_conversion_form_t form, BN_CTX *) __attribute__((deprecated));
EC_POINT *EC_POINT_hex2point(const EC_GROUP *, const char *,
 EC_POINT *, BN_CTX *) __attribute__((deprecated));

int EC_POINT_add(const EC_GROUP *, EC_POINT *r, const EC_POINT *a, const EC_POINT *b, BN_CTX *) __attribute__((deprecated));
int EC_POINT_dbl(const EC_GROUP *, EC_POINT *r, const EC_POINT *a, BN_CTX *) __attribute__((deprecated));
int EC_POINT_invert(const EC_GROUP *, EC_POINT *, BN_CTX *) __attribute__((deprecated));

int EC_POINT_is_at_infinity(const EC_GROUP *, const EC_POINT *) __attribute__((deprecated));
int EC_POINT_is_on_curve(const EC_GROUP *, const EC_POINT *, BN_CTX *) __attribute__((deprecated));
int EC_POINT_cmp(const EC_GROUP *, const EC_POINT *a, const EC_POINT *b, BN_CTX *) __attribute__((deprecated));

int EC_POINT_make_affine(const EC_GROUP *, EC_POINT *, BN_CTX *) __attribute__((deprecated));
int EC_POINTs_make_affine(const EC_GROUP *, size_t num, EC_POINT *[], BN_CTX *) __attribute__((deprecated));


int EC_POINTs_mul(const EC_GROUP *, EC_POINT *r, const BIGNUM *, size_t num, const EC_POINT *[], const BIGNUM *[], BN_CTX *) __attribute__((deprecated));
int EC_POINT_mul(const EC_GROUP *, EC_POINT *r, const BIGNUM *, const EC_POINT *, const BIGNUM *, BN_CTX *) __attribute__((deprecated));


int EC_GROUP_precompute_mult(EC_GROUP *, BN_CTX *) __attribute__((deprecated));

int EC_GROUP_have_precompute_mult(const EC_GROUP *) __attribute__((deprecated));







int EC_GROUP_get_basis_type(const EC_GROUP *) __attribute__((deprecated));
int EC_GROUP_get_trinomial_basis(const EC_GROUP *, unsigned int *k) __attribute__((deprecated));
int EC_GROUP_get_pentanomial_basis(const EC_GROUP *, unsigned int *k1,
 unsigned int *k2, unsigned int *k3) __attribute__((deprecated));



typedef struct ecpk_parameters_st ECPKPARAMETERS;

EC_GROUP *d2i_ECPKParameters(EC_GROUP **, const unsigned char **in, long len) __attribute__((deprecated));
int i2d_ECPKParameters(const EC_GROUP *, unsigned char **out) __attribute__((deprecated));
# 292 "/usr/include/openssl/ec.h" 3 4
int ECPKParameters_print(BIO *bp, const EC_GROUP *x, int off) __attribute__((deprecated));


int ECPKParameters_print_fp(FILE *fp, const EC_GROUP *x, int off) __attribute__((deprecated));



typedef struct ec_key_st EC_KEY;





EC_KEY *EC_KEY_new(void) __attribute__((deprecated));
EC_KEY *EC_KEY_new_by_curve_name(int nid) __attribute__((deprecated));
void EC_KEY_free(EC_KEY *) __attribute__((deprecated));
EC_KEY *EC_KEY_copy(EC_KEY *, const EC_KEY *) __attribute__((deprecated));
EC_KEY *EC_KEY_dup(const EC_KEY *) __attribute__((deprecated));

int EC_KEY_up_ref(EC_KEY *) __attribute__((deprecated));

const EC_GROUP *EC_KEY_get0_group(const EC_KEY *) __attribute__((deprecated));
int EC_KEY_set_group(EC_KEY *, const EC_GROUP *) __attribute__((deprecated));
const BIGNUM *EC_KEY_get0_private_key(const EC_KEY *) __attribute__((deprecated));
int EC_KEY_set_private_key(EC_KEY *, const BIGNUM *) __attribute__((deprecated));
const EC_POINT *EC_KEY_get0_public_key(const EC_KEY *) __attribute__((deprecated));
int EC_KEY_set_public_key(EC_KEY *, const EC_POINT *) __attribute__((deprecated));
unsigned EC_KEY_get_enc_flags(const EC_KEY *) __attribute__((deprecated));
void EC_KEY_set_enc_flags(EC_KEY *, unsigned int) __attribute__((deprecated));
point_conversion_form_t EC_KEY_get_conv_form(const EC_KEY *) __attribute__((deprecated));
void EC_KEY_set_conv_form(EC_KEY *, point_conversion_form_t) __attribute__((deprecated));

void *EC_KEY_get_key_method_data(EC_KEY *,
 void *(*dup_func)(void *), void (*free_func)(void *), void (*clear_free_func)(void *)) __attribute__((deprecated));
void EC_KEY_insert_key_method_data(EC_KEY *, void *data,
 void *(*dup_func)(void *), void (*free_func)(void *), void (*clear_free_func)(void *)) __attribute__((deprecated));

void EC_KEY_set_asn1_flag(EC_KEY *, int) __attribute__((deprecated));
int EC_KEY_precompute_mult(EC_KEY *, BN_CTX *ctx) __attribute__((deprecated));


int EC_KEY_generate_key(EC_KEY *) __attribute__((deprecated));

int EC_KEY_check_key(const EC_KEY *) __attribute__((deprecated));


EC_KEY *d2i_ECPrivateKey(EC_KEY **a, const unsigned char **in, long len) __attribute__((deprecated));
int i2d_ECPrivateKey(EC_KEY *a, unsigned char **out) __attribute__((deprecated));

EC_KEY *d2i_ECParameters(EC_KEY **a, const unsigned char **in, long len) __attribute__((deprecated));
int i2d_ECParameters(EC_KEY *a, unsigned char **out) __attribute__((deprecated));


EC_KEY *o2i_ECPublicKey(EC_KEY **a, const unsigned char **in, long len) __attribute__((deprecated));
int i2o_ECPublicKey(EC_KEY *a, unsigned char **out) __attribute__((deprecated));


int ECParameters_print(BIO *bp, const EC_KEY *x) __attribute__((deprecated));
int EC_KEY_print(BIO *bp, const EC_KEY *x, int off) __attribute__((deprecated));


int ECParameters_print_fp(FILE *fp, const EC_KEY *x) __attribute__((deprecated));
int EC_KEY_print_fp(FILE *fp, const EC_KEY *x, int off) __attribute__((deprecated));
# 371 "/usr/include/openssl/ec.h" 3 4
void ERR_load_EC_strings(void) __attribute__((deprecated));
# 86 "/usr/include/openssl/x509.h" 2 3 4



# 1 "/usr/include/openssl/ecdsa.h" 1 3 4
# 64 "/usr/include/openssl/ecdsa.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 65 "/usr/include/openssl/ecdsa.h" 2 3 4
# 80 "/usr/include/openssl/ecdsa.h" 3 4
typedef struct ECDSA_SIG_st
 {
 BIGNUM *r;
 BIGNUM *s;
 } ECDSA_SIG;





ECDSA_SIG *ECDSA_SIG_new(void) __attribute__((deprecated));





void ECDSA_SIG_free(ECDSA_SIG *a) __attribute__((deprecated));
# 105 "/usr/include/openssl/ecdsa.h" 3 4
int i2d_ECDSA_SIG(const ECDSA_SIG *a, unsigned char **pp) __attribute__((deprecated));
# 115 "/usr/include/openssl/ecdsa.h" 3 4
ECDSA_SIG *d2i_ECDSA_SIG(ECDSA_SIG **v, const unsigned char **pp, long len) __attribute__((deprecated));
# 125 "/usr/include/openssl/ecdsa.h" 3 4
ECDSA_SIG *ECDSA_do_sign(const unsigned char *dgst,int dgst_len,EC_KEY *eckey) __attribute__((deprecated));
# 138 "/usr/include/openssl/ecdsa.h" 3 4
ECDSA_SIG *ECDSA_do_sign_ex(const unsigned char *dgst, int dgstlen,
  const BIGNUM *kinv, const BIGNUM *rp, EC_KEY *eckey) __attribute__((deprecated));
# 150 "/usr/include/openssl/ecdsa.h" 3 4
int ECDSA_do_verify(const unsigned char *dgst, int dgst_len,
  const ECDSA_SIG *sig, EC_KEY* eckey) __attribute__((deprecated));

const ECDSA_METHOD *ECDSA_OpenSSL(void) __attribute__((deprecated));





void ECDSA_set_default_method(const ECDSA_METHOD *meth) __attribute__((deprecated));





const ECDSA_METHOD *ECDSA_get_default_method(void) __attribute__((deprecated));







int ECDSA_set_method(EC_KEY *eckey, const ECDSA_METHOD *meth) __attribute__((deprecated));






int ECDSA_size(const EC_KEY *eckey) __attribute__((deprecated));
# 190 "/usr/include/openssl/ecdsa.h" 3 4
int ECDSA_sign_setup(EC_KEY *eckey, BN_CTX *ctx, BIGNUM **kinv,
  BIGNUM **rp) __attribute__((deprecated));
# 204 "/usr/include/openssl/ecdsa.h" 3 4
int ECDSA_sign(int type, const unsigned char *dgst, int dgstlen,
  unsigned char *sig, unsigned int *siglen, EC_KEY *eckey) __attribute__((deprecated));
# 222 "/usr/include/openssl/ecdsa.h" 3 4
int ECDSA_sign_ex(int type, const unsigned char *dgst, int dgstlen,
  unsigned char *sig, unsigned int *siglen, const BIGNUM *kinv,
  const BIGNUM *rp, EC_KEY *eckey) __attribute__((deprecated));
# 237 "/usr/include/openssl/ecdsa.h" 3 4
int ECDSA_verify(int type, const unsigned char *dgst, int dgstlen,
  const unsigned char *sig, int siglen, EC_KEY *eckey) __attribute__((deprecated));


int ECDSA_get_ex_new_index(long argl, void *argp, CRYPTO_EX_new
  *new_func, CRYPTO_EX_dup *dup_func, CRYPTO_EX_free *free_func) __attribute__((deprecated));
int ECDSA_set_ex_data(EC_KEY *d, int idx, void *arg) __attribute__((deprecated));
void *ECDSA_get_ex_data(EC_KEY *d, int idx) __attribute__((deprecated));






void ERR_load_ECDSA_strings(void) __attribute__((deprecated));
# 90 "/usr/include/openssl/x509.h" 2 3 4



# 1 "/usr/include/openssl/ecdh.h" 1 3 4
# 74 "/usr/include/openssl/ecdh.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 75 "/usr/include/openssl/ecdh.h" 2 3 4
# 90 "/usr/include/openssl/ecdh.h" 3 4
const ECDH_METHOD *ECDH_OpenSSL(void) __attribute__((deprecated));

void ECDH_set_default_method(const ECDH_METHOD *) __attribute__((deprecated));
const ECDH_METHOD *ECDH_get_default_method(void) __attribute__((deprecated));
int ECDH_set_method(EC_KEY *, const ECDH_METHOD *) __attribute__((deprecated));

int ECDH_compute_key(void *out, size_t outlen, const EC_POINT *pub_key, EC_KEY *ecdh,
                     void *(*KDF)(const void *in, size_t inlen, void *out, size_t *outlen)) __attribute__((deprecated));

int ECDH_get_ex_new_index(long argl, void *argp, CRYPTO_EX_new
  *new_func, CRYPTO_EX_dup *dup_func, CRYPTO_EX_free *free_func) __attribute__((deprecated));
int ECDH_set_ex_data(EC_KEY *d, int idx, void *arg) __attribute__((deprecated));
void *ECDH_get_ex_data(EC_KEY *d, int idx) __attribute__((deprecated));






void ERR_load_ECDH_strings(void) __attribute__((deprecated));
# 94 "/usr/include/openssl/x509.h" 2 3 4




# 1 "/usr/include/openssl/rsa.h" 1 3 4
# 99 "/usr/include/openssl/x509.h" 2 3 4


# 1 "/usr/include/openssl/dsa.h" 1 3 4
# 70 "/usr/include/openssl/dsa.h" 3 4
# 1 "/usr/include/openssl/e_os2.h" 1 3 4
# 56 "/usr/include/openssl/e_os2.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 57 "/usr/include/openssl/e_os2.h" 2 3 4
# 71 "/usr/include/openssl/dsa.h" 2 3 4
# 85 "/usr/include/openssl/dsa.h" 3 4
# 1 "/usr/include/openssl/dh.h" 1 3 4
# 64 "/usr/include/openssl/dh.h" 3 4
# 1 "/usr/include/openssl/e_os2.h" 1 3 4
# 56 "/usr/include/openssl/e_os2.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 57 "/usr/include/openssl/e_os2.h" 2 3 4
# 65 "/usr/include/openssl/dh.h" 2 3 4
# 101 "/usr/include/openssl/dh.h" 3 4
struct dh_method
 {
 const char *name;

 int (*generate_key)(DH *dh);
 int (*compute_key)(unsigned char *key,const BIGNUM *pub_key,DH *dh);
 int (*bn_mod_exp)(const DH *dh, BIGNUM *r, const BIGNUM *a,
    const BIGNUM *p, const BIGNUM *m, BN_CTX *ctx,
    BN_MONT_CTX *m_ctx);

 int (*init)(DH *dh);
 int (*finish)(DH *dh);
 int flags;
 char *app_data;

 int (*generate_params)(DH *dh, int prime_len, int generator, BN_GENCB *cb);
 };

struct dh_st
 {


 int pad;
 int version;
 BIGNUM *p;
 BIGNUM *g;
 long length;
 BIGNUM *pub_key;
 BIGNUM *priv_key;

 int flags;
 BN_MONT_CTX *method_mont_p;

 BIGNUM *q;
 BIGNUM *j;
 unsigned char *seed;
 int seedlen;
 BIGNUM *counter;

 int references;
 CRYPTO_EX_DATA ex_data;
 const DH_METHOD *meth;
 ENGINE *engine;
 };
# 172 "/usr/include/openssl/dh.h" 3 4
const DH_METHOD *DH_OpenSSL(void) __attribute__((deprecated));






void DH_set_default_method(const DH_METHOD *meth) __attribute__((deprecated));
const DH_METHOD *DH_get_default_method(void) __attribute__((deprecated));
int DH_set_method(DH *dh, const DH_METHOD *meth) __attribute__((deprecated));
DH *DH_new_method(ENGINE *engine) __attribute__((deprecated));

DH * DH_new(void) __attribute__((deprecated));
void DH_free(DH *dh) __attribute__((deprecated));
int DH_up_ref(DH *dh) __attribute__((deprecated));
int DH_size(const DH *dh) __attribute__((deprecated));
int DH_get_ex_new_index(long argl, void *argp, CRYPTO_EX_new *new_func,
      CRYPTO_EX_dup *dup_func, CRYPTO_EX_free *free_func) __attribute__((deprecated));
int DH_set_ex_data(DH *d, int idx, void *arg) __attribute__((deprecated));
void *DH_get_ex_data(DH *d, int idx) __attribute__((deprecated));



DH * DH_generate_parameters(int prime_len,int generator,
  void (*callback)(int,int,void *),void *cb_arg);



int DH_generate_parameters_ex(DH *dh, int prime_len,int generator, BN_GENCB *cb) __attribute__((deprecated));

int DH_check(const DH *dh,int *codes) __attribute__((deprecated));
int DH_check_pub_key(const DH *dh,const BIGNUM *pub_key, int *codes) __attribute__((deprecated));
int DH_generate_key(DH *dh) __attribute__((deprecated));
int DH_compute_key(unsigned char *key,const BIGNUM *pub_key,DH *dh) __attribute__((deprecated));
DH * d2i_DHparams(DH **a,const unsigned char **pp, long length) __attribute__((deprecated));
int i2d_DHparams(const DH *a,unsigned char **pp) __attribute__((deprecated));

int DHparams_print_fp(FILE *fp, const DH *x) __attribute__((deprecated));


int DHparams_print(BIO *bp, const DH *x) __attribute__((deprecated));
# 221 "/usr/include/openssl/dh.h" 3 4
void ERR_load_DH_strings(void) __attribute__((deprecated));
# 86 "/usr/include/openssl/dsa.h" 2 3 4
# 131 "/usr/include/openssl/dsa.h" 3 4
typedef struct DSA_SIG_st
 {
 BIGNUM *r;
 BIGNUM *s;
 } DSA_SIG;

struct dsa_method
 {
 const char *name;
 DSA_SIG * (*dsa_do_sign)(const unsigned char *dgst, int dlen, DSA *dsa);
 int (*dsa_sign_setup)(DSA *dsa, BN_CTX *ctx_in, BIGNUM **kinvp,
        BIGNUM **rp);
 int (*dsa_do_verify)(const unsigned char *dgst, int dgst_len,
       DSA_SIG *sig, DSA *dsa);
 int (*dsa_mod_exp)(DSA *dsa, BIGNUM *rr, BIGNUM *a1, BIGNUM *p1,
   BIGNUM *a2, BIGNUM *p2, BIGNUM *m, BN_CTX *ctx,
   BN_MONT_CTX *in_mont);
 int (*bn_mod_exp)(DSA *dsa, BIGNUM *r, BIGNUM *a, const BIGNUM *p,
    const BIGNUM *m, BN_CTX *ctx,
    BN_MONT_CTX *m_ctx);
 int (*init)(DSA *dsa);
 int (*finish)(DSA *dsa);
 int flags;
 char *app_data;

 int (*dsa_paramgen)(DSA *dsa, int bits,
   unsigned char *seed, int seed_len,
   int *counter_ret, unsigned long *h_ret,
   BN_GENCB *cb);

 int (*dsa_keygen)(DSA *dsa);
 };

struct dsa_st
 {


 int pad;
 long version;
 int write_params;
 BIGNUM *p;
 BIGNUM *q;
 BIGNUM *g;

 BIGNUM *pub_key;
 BIGNUM *priv_key;

 BIGNUM *kinv;
 BIGNUM *r;

 int flags;

 BN_MONT_CTX *method_mont_p;
 int references;
 CRYPTO_EX_DATA ex_data;
 const DSA_METHOD *meth;

 ENGINE *engine;
 };
# 200 "/usr/include/openssl/dsa.h" 3 4
DSA_SIG * DSA_SIG_new(void) __attribute__((deprecated));
void DSA_SIG_free(DSA_SIG *a) __attribute__((deprecated));
int i2d_DSA_SIG(const DSA_SIG *a, unsigned char **pp) __attribute__((deprecated));
DSA_SIG * d2i_DSA_SIG(DSA_SIG **v, const unsigned char **pp, long length) __attribute__((deprecated));

DSA_SIG * DSA_do_sign(const unsigned char *dgst,int dlen,DSA *dsa) __attribute__((deprecated));
int DSA_do_verify(const unsigned char *dgst,int dgst_len,
        DSA_SIG *sig,DSA *dsa) __attribute__((deprecated));

const DSA_METHOD *DSA_OpenSSL(void) __attribute__((deprecated));

void DSA_set_default_method(const DSA_METHOD *) __attribute__((deprecated));
const DSA_METHOD *DSA_get_default_method(void) __attribute__((deprecated));
int DSA_set_method(DSA *dsa, const DSA_METHOD *) __attribute__((deprecated));






DSA * DSA_new(void) __attribute__((deprecated));
DSA * DSA_new_method(ENGINE *engine) __attribute__((deprecated));
void DSA_free (DSA *r) __attribute__((deprecated));

int DSA_up_ref(DSA *r) __attribute__((deprecated));
int DSA_size(const DSA *) __attribute__((deprecated));

int DSA_sign_setup( DSA *dsa,BN_CTX *ctx_in,BIGNUM **kinvp,BIGNUM **rp) __attribute__((deprecated));
int DSA_sign(int type,const unsigned char *dgst,int dlen,
  unsigned char *sig, unsigned int *siglen, DSA *dsa) __attribute__((deprecated));
int DSA_verify(int type,const unsigned char *dgst,int dgst_len,
  const unsigned char *sigbuf, int siglen, DSA *dsa) __attribute__((deprecated));
int DSA_get_ex_new_index(long argl, void *argp, CRYPTO_EX_new *new_func,
      CRYPTO_EX_dup *dup_func, CRYPTO_EX_free *free_func) __attribute__((deprecated));
int DSA_set_ex_data(DSA *d, int idx, void *arg) __attribute__((deprecated));
void *DSA_get_ex_data(DSA *d, int idx) __attribute__((deprecated));

DSA * d2i_DSAPublicKey(DSA **a, const unsigned char **pp, long length) __attribute__((deprecated));
DSA * d2i_DSAPrivateKey(DSA **a, const unsigned char **pp, long length) __attribute__((deprecated));
DSA * d2i_DSAparams(DSA **a, const unsigned char **pp, long length) __attribute__((deprecated));



DSA * DSA_generate_parameters(int bits,
  unsigned char *seed,int seed_len,
  int *counter_ret, unsigned long *h_ret,void
  (*callback)(int, int, void *),void *cb_arg) __attribute__((deprecated));



int DSA_generate_parameters_ex(DSA *dsa, int bits,
  unsigned char *seed,int seed_len,
  int *counter_ret, unsigned long *h_ret, BN_GENCB *cb) __attribute__((deprecated));

int DSA_generate_key(DSA *a) __attribute__((deprecated));
int i2d_DSAPublicKey(const DSA *a, unsigned char **pp) __attribute__((deprecated));
int i2d_DSAPrivateKey(const DSA *a, unsigned char **pp) __attribute__((deprecated));
int i2d_DSAparams(const DSA *a,unsigned char **pp) __attribute__((deprecated));


int DSAparams_print(BIO *bp, const DSA *x) __attribute__((deprecated));
int DSA_print(BIO *bp, const DSA *x, int off) __attribute__((deprecated));


int DSAparams_print_fp(FILE *fp, const DSA *x) __attribute__((deprecated));
int DSA_print_fp(FILE *bp, const DSA *x, int off) __attribute__((deprecated));
# 277 "/usr/include/openssl/dsa.h" 3 4
DH *DSA_dup_DH(const DSA *r) __attribute__((deprecated));
# 289 "/usr/include/openssl/dsa.h" 3 4
void ERR_load_DSA_strings(void) __attribute__((deprecated));
# 102 "/usr/include/openssl/x509.h" 2 3 4







# 1 "/usr/include/openssl/sha.h" 1 3 4
# 64 "/usr/include/openssl/sha.h" 3 4
# 1 "/usr/include/openssl/e_os2.h" 1 3 4
# 56 "/usr/include/openssl/e_os2.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 57 "/usr/include/openssl/e_os2.h" 2 3 4
# 65 "/usr/include/openssl/sha.h" 2 3 4
# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stddef.h" 1 3 4
# 66 "/usr/include/openssl/sha.h" 2 3 4
# 102 "/usr/include/openssl/sha.h" 3 4
typedef struct SHAstate_st
 {
 unsigned int h0,h1,h2,h3,h4;
 unsigned int Nl,Nh;
 unsigned int data[16];
 unsigned int num;
 } SHA_CTX;





int SHA_Init(SHA_CTX *c) __attribute__((deprecated));
int SHA_Update(SHA_CTX *c, const void *data, size_t len) __attribute__((deprecated));
int SHA_Final(unsigned char *md, SHA_CTX *c) __attribute__((deprecated));
unsigned char *SHA(const unsigned char *d, size_t n, unsigned char *md) __attribute__((deprecated));
void SHA_Transform(SHA_CTX *c, const unsigned char *data) __attribute__((deprecated));


int SHA1_Init(SHA_CTX *c) __attribute__((deprecated));
int SHA1_Update(SHA_CTX *c, const void *data, size_t len) __attribute__((deprecated));
int SHA1_Final(unsigned char *md, SHA_CTX *c) __attribute__((deprecated));
unsigned char *SHA1(const unsigned char *d, size_t n, unsigned char *md) __attribute__((deprecated));
void SHA1_Transform(SHA_CTX *c, const unsigned char *data) __attribute__((deprecated));
# 134 "/usr/include/openssl/sha.h" 3 4
typedef struct SHA256state_st
 {
 unsigned int h[8];
 unsigned int Nl,Nh;
 unsigned int data[16];
 unsigned int num,md_len;
 } SHA256_CTX;


int SHA224_Init(SHA256_CTX *c) __attribute__((deprecated));
int SHA224_Update(SHA256_CTX *c, const void *data, size_t len) __attribute__((deprecated));
int SHA224_Final(unsigned char *md, SHA256_CTX *c) __attribute__((deprecated));
unsigned char *SHA224(const unsigned char *d, size_t n,unsigned char *md) __attribute__((deprecated));
int SHA256_Init(SHA256_CTX *c) __attribute__((deprecated));
int SHA256_Update(SHA256_CTX *c, const void *data, size_t len) __attribute__((deprecated));
int SHA256_Final(unsigned char *md, SHA256_CTX *c) __attribute__((deprecated));
unsigned char *SHA256(const unsigned char *d, size_t n,unsigned char *md) __attribute__((deprecated));
void SHA256_Transform(SHA256_CTX *c, const unsigned char *data) __attribute__((deprecated));
# 177 "/usr/include/openssl/sha.h" 3 4
typedef struct SHA512state_st
 {
 unsigned long long h[8];
 unsigned long long Nl,Nh;
 union {
  unsigned long long d[16];
  unsigned char p[(16*8)];
 } u;
 unsigned int num,md_len;
 } SHA512_CTX;



int SHA384_Init(SHA512_CTX *c) __attribute__((deprecated));
int SHA384_Update(SHA512_CTX *c, const void *data, size_t len) __attribute__((deprecated));
int SHA384_Final(unsigned char *md, SHA512_CTX *c) __attribute__((deprecated));
unsigned char *SHA384(const unsigned char *d, size_t n,unsigned char *md) __attribute__((deprecated));
int SHA512_Init(SHA512_CTX *c) __attribute__((deprecated));
int SHA512_Update(SHA512_CTX *c, const void *data, size_t len) __attribute__((deprecated));
int SHA512_Final(unsigned char *md, SHA512_CTX *c) __attribute__((deprecated));
unsigned char *SHA512(const unsigned char *d, size_t n,unsigned char *md) __attribute__((deprecated));
void SHA512_Transform(SHA512_CTX *c, const unsigned char *data) __attribute__((deprecated));
# 110 "/usr/include/openssl/x509.h" 2 3 4
# 139 "/usr/include/openssl/x509.h" 3 4
typedef struct X509_objects_st
 {
 int nid;
 int (*a2i)(void);
 int (*i2a)(void);
 } X509_OBJECTS;

struct X509_algor_st
 {
 ASN1_OBJECT *algorithm;
 ASN1_TYPE *parameter;
 } ;



typedef STACK X509_ALGORS;

typedef struct X509_val_st
 {
 ASN1_TIME *notBefore;
 ASN1_TIME *notAfter;
 } X509_VAL;

typedef struct X509_pubkey_st
 {
 X509_ALGOR *algor;
 ASN1_BIT_STRING *public_key;
 EVP_PKEY *pkey;
 } X509_PUBKEY;

typedef struct X509_sig_st
 {
 X509_ALGOR *algor;
 ASN1_OCTET_STRING *digest;
 } X509_SIG;

typedef struct X509_name_entry_st
 {
 ASN1_OBJECT *object;
 ASN1_STRING *value;
 int set;
 int size;
 } X509_NAME_ENTRY;





struct X509_name_st
 {
 STACK *entries;
 int modified;

 BUF_MEM *bytes;



 unsigned long hash;
 } ;





typedef struct X509_extension_st
 {
 ASN1_OBJECT *object;
 ASN1_BOOLEAN critical;
 ASN1_OCTET_STRING *value;
 } X509_EXTENSION;

typedef STACK X509_EXTENSIONS;





typedef struct x509_attributes_st
 {
 ASN1_OBJECT *object;
 int single;
 union {
  char *ptr;
         STACK *set;
         ASN1_TYPE *single;
  } value;
 } X509_ATTRIBUTE;





typedef struct X509_req_info_st
 {
 ASN1_ENCODING enc;
 ASN1_INTEGER *version;
 X509_NAME *subject;
 X509_PUBKEY *pubkey;

 STACK *attributes;
 } X509_REQ_INFO;

typedef struct X509_req_st
 {
 X509_REQ_INFO *req_info;
 X509_ALGOR *sig_alg;
 ASN1_BIT_STRING *signature;
 int references;
 } X509_REQ;

typedef struct x509_cinf_st
 {
 ASN1_INTEGER *version;
 ASN1_INTEGER *serialNumber;
 X509_ALGOR *signature;
 X509_NAME *issuer;
 X509_VAL *validity;
 X509_NAME *subject;
 X509_PUBKEY *key;
 ASN1_BIT_STRING *issuerUID;
 ASN1_BIT_STRING *subjectUID;
 STACK *extensions;
 ASN1_ENCODING enc;
 } X509_CINF;







typedef struct x509_cert_aux_st
 {
 STACK *trust;
 STACK *reject;
 ASN1_UTF8STRING *alias;
 ASN1_OCTET_STRING *keyid;
 STACK *other;
 } X509_CERT_AUX;

struct x509_st
 {
 X509_CINF *cert_info;
 X509_ALGOR *sig_alg;
 ASN1_BIT_STRING *signature;
 int valid;
 int references;
 char *name;
 CRYPTO_EX_DATA ex_data;

 long ex_pathlen;
 long ex_pcpathlen;
 unsigned long ex_flags;
 unsigned long ex_kusage;
 unsigned long ex_xkusage;
 unsigned long ex_nscert;
 ASN1_OCTET_STRING *skid;
 struct AUTHORITY_KEYID_st *akid;
 X509_POLICY_CACHE *policy_cache;





 unsigned char sha1_hash[20];

 X509_CERT_AUX *aux;
 } ;






typedef struct x509_trust_st {
 int trust;
 int flags;
 int (*check_trust)(struct x509_trust_st *, X509 *, int);
 char *name;
 int arg1;
 void *arg2;
} X509_TRUST;



typedef struct x509_cert_pair_st {
 X509 *forward;
 X509 *reverse;
} X509_CERT_PAIR;
# 430 "/usr/include/openssl/x509.h" 3 4
typedef struct X509_revoked_st
 {
 ASN1_INTEGER *serialNumber;
 ASN1_TIME *revocationDate;
 STACK *extensions;
 int sequence;
 } X509_REVOKED;




typedef struct X509_crl_info_st
 {
 ASN1_INTEGER *version;
 X509_ALGOR *sig_alg;
 X509_NAME *issuer;
 ASN1_TIME *lastUpdate;
 ASN1_TIME *nextUpdate;
 STACK *revoked;
 STACK *extensions;
 ASN1_ENCODING enc;
 } X509_CRL_INFO;

struct X509_crl_st
 {

 X509_CRL_INFO *crl;
 X509_ALGOR *sig_alg;
 ASN1_BIT_STRING *signature;
 int references;
 } ;




typedef struct private_key_st
 {
 int version;

 X509_ALGOR *enc_algor;
 ASN1_OCTET_STRING *enc_pkey;


 EVP_PKEY *dec_pkey;


 int key_length;
 char *key_data;
 int key_free;


 EVP_CIPHER_INFO cipher;

 int references;
 } X509_PKEY;


typedef struct X509_info_st
 {
 X509 *x509;
 X509_CRL *crl;
 X509_PKEY *x_pkey;

 EVP_CIPHER_INFO enc_cipher;
 int enc_len;
 char *enc_data;

 int references;
 } X509_INFO;








typedef struct Netscape_spkac_st
 {
 X509_PUBKEY *pubkey;
 ASN1_IA5STRING *challenge;
 } NETSCAPE_SPKAC;

typedef struct Netscape_spki_st
 {
 NETSCAPE_SPKAC *spkac;
 X509_ALGOR *sig_algor;
 ASN1_BIT_STRING *signature;
 } NETSCAPE_SPKI;


typedef struct Netscape_certificate_sequence
 {
 ASN1_OBJECT *type;
 STACK *certs;
 } NETSCAPE_CERT_SEQUENCE;
# 536 "/usr/include/openssl/x509.h" 3 4
typedef struct PBEPARAM_st {
ASN1_OCTET_STRING *salt;
ASN1_INTEGER *iter;
} PBEPARAM;



typedef struct PBE2PARAM_st {
X509_ALGOR *keyfunc;
X509_ALGOR *encryption;
} PBE2PARAM;

typedef struct PBKDF2PARAM_st {
ASN1_TYPE *salt;
ASN1_INTEGER *iter;
ASN1_INTEGER *keylength;
X509_ALGOR *prf;
} PBKDF2PARAM;




typedef struct pkcs8_priv_key_info_st
        {
        int broken;




        ASN1_INTEGER *version;
        X509_ALGOR *pkeyalg;
        ASN1_TYPE *pkey;
        STACK *attributes;
        } PKCS8_PRIV_KEY_INFO;





# 1 "/usr/include/openssl/x509_vfy.h" 1 3 4
# 70 "/usr/include/openssl/x509_vfy.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 71 "/usr/include/openssl/x509_vfy.h" 2 3 4

# 1 "/usr/include/openssl/lhash.h" 1 3 4
# 68 "/usr/include/openssl/lhash.h" 3 4
# 1 "/usr/include/openssl/e_os2.h" 1 3 4
# 56 "/usr/include/openssl/e_os2.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 57 "/usr/include/openssl/e_os2.h" 2 3 4
# 69 "/usr/include/openssl/lhash.h" 2 3 4
# 81 "/usr/include/openssl/lhash.h" 3 4
typedef struct lhash_node_st
 {
 void *data;
 struct lhash_node_st *next;

 unsigned long hash;

 } LHASH_NODE;

typedef int (*LHASH_COMP_FN_TYPE)(const void *, const void *);
typedef unsigned long (*LHASH_HASH_FN_TYPE)(const void *);
typedef void (*LHASH_DOALL_FN_TYPE)(void *);
typedef void (*LHASH_DOALL_ARG_FN_TYPE)(void *, void *);
# 140 "/usr/include/openssl/lhash.h" 3 4
typedef struct lhash_st
 {
 LHASH_NODE **b;
 LHASH_COMP_FN_TYPE comp;
 LHASH_HASH_FN_TYPE hash;
 unsigned int num_nodes;
 unsigned int num_alloc_nodes;
 unsigned int p;
 unsigned int pmax;
 unsigned long up_load;
 unsigned long down_load;
 unsigned long num_items;

 unsigned long num_expands;
 unsigned long num_expand_reallocs;
 unsigned long num_contracts;
 unsigned long num_contract_reallocs;
 unsigned long num_hash_calls;
 unsigned long num_comp_calls;
 unsigned long num_insert;
 unsigned long num_replace;
 unsigned long num_delete;
 unsigned long num_no_delete;
 unsigned long num_retrieve;
 unsigned long num_retrieve_miss;
 unsigned long num_hash_comps;

 int error;
 } LHASH;







LHASH *lh_new(LHASH_HASH_FN_TYPE h, LHASH_COMP_FN_TYPE c) __attribute__((deprecated));
void lh_free(LHASH *lh) __attribute__((deprecated));
void *lh_insert(LHASH *lh, void *data) __attribute__((deprecated));
void *lh_delete(LHASH *lh, const void *data) __attribute__((deprecated));
void *lh_retrieve(LHASH *lh, const void *data) __attribute__((deprecated));
void lh_doall(LHASH *lh, LHASH_DOALL_FN_TYPE func) __attribute__((deprecated));
void lh_doall_arg(LHASH *lh, LHASH_DOALL_ARG_FN_TYPE func, void *arg) __attribute__((deprecated));
unsigned long lh_strhash(const char *c) __attribute__((deprecated));
unsigned long lh_num_items(const LHASH *lh) __attribute__((deprecated));


void lh_stats(const LHASH *lh, FILE *out) __attribute__((deprecated));
void lh_node_stats(const LHASH *lh, FILE *out) __attribute__((deprecated));
void lh_node_usage_stats(const LHASH *lh, FILE *out) __attribute__((deprecated));



void lh_stats_bio(const LHASH *lh, BIO *out) __attribute__((deprecated));
void lh_node_stats_bio(const LHASH *lh, BIO *out) __attribute__((deprecated));
void lh_node_usage_stats_bio(const LHASH *lh, BIO *out) __attribute__((deprecated));
# 73 "/usr/include/openssl/x509_vfy.h" 2 3 4



# 1 "/usr/include/openssl/symhacks.h" 1 3 4
# 77 "/usr/include/openssl/x509_vfy.h" 2 3 4






typedef struct x509_hash_dir_st
 {
 int num_dirs;
 char **dirs;
 int *dirs_type;
 int num_dirs_alloced;
 } X509_HASH_DIR_CTX;

typedef struct x509_file_st
 {
 int num_paths;
 int num_alloced;
 char **paths;
 int *path_type;
 } X509_CERT_FILE_CTX;
# 123 "/usr/include/openssl/x509_vfy.h" 3 4
typedef struct x509_object_st
 {

 int type;
 union {
  char *ptr;
  X509 *x509;
  X509_CRL *crl;
  EVP_PKEY *pkey;
  } data;
 } X509_OBJECT;

typedef struct x509_lookup_st X509_LOOKUP;





typedef struct x509_lookup_method_st
 {
 const char *name;
 int (*new_item)(X509_LOOKUP *ctx);
 void (*free)(X509_LOOKUP *ctx);
 int (*init)(X509_LOOKUP *ctx);
 int (*shutdown)(X509_LOOKUP *ctx);
 int (*ctrl)(X509_LOOKUP *ctx,int cmd,const char *argc,long argl,
   char **ret);
 int (*get_by_subject)(X509_LOOKUP *ctx,int type,X509_NAME *name,
         X509_OBJECT *ret);
 int (*get_by_issuer_serial)(X509_LOOKUP *ctx,int type,X509_NAME *name,
        ASN1_INTEGER *serial,X509_OBJECT *ret);
 int (*get_by_fingerprint)(X509_LOOKUP *ctx,int type,
      unsigned char *bytes,int len,
      X509_OBJECT *ret);
 int (*get_by_alias)(X509_LOOKUP *ctx,int type,char *str,int len,
       X509_OBJECT *ret);
 } X509_LOOKUP_METHOD;






typedef struct X509_VERIFY_PARAM_st
 {
 char *name;
 time_t check_time;
 unsigned long inh_flags;
 unsigned long flags;
 int purpose;
 int trust;
 int depth;
 STACK *policies;
 } X509_VERIFY_PARAM;






struct x509_store_st
 {

 int cache;
 STACK *objs;


 STACK *get_cert_methods;

 X509_VERIFY_PARAM *param;


 int (*verify)(X509_STORE_CTX *ctx);
 int (*verify_cb)(int ok,X509_STORE_CTX *ctx);
 int (*get_issuer)(X509 **issuer, X509_STORE_CTX *ctx, X509 *x);
 int (*check_issued)(X509_STORE_CTX *ctx, X509 *x, X509 *issuer);
 int (*check_revocation)(X509_STORE_CTX *ctx);
 int (*get_crl)(X509_STORE_CTX *ctx, X509_CRL **crl, X509 *x);
 int (*check_crl)(X509_STORE_CTX *ctx, X509_CRL *crl);
 int (*cert_crl)(X509_STORE_CTX *ctx, X509_CRL *crl, X509 *x);
 int (*cleanup)(X509_STORE_CTX *ctx);

 CRYPTO_EX_DATA ex_data;
 int references;
 } ;

int X509_STORE_set_depth(X509_STORE *store, int depth) __attribute__((deprecated));





struct x509_lookup_st
 {
 int init;
 int skip;
 X509_LOOKUP_METHOD *method;
 char *method_data;

 X509_STORE *store_ctx;
 } ;




struct x509_store_ctx_st
 {
 X509_STORE *ctx;
 int current_method;


 X509 *cert;
 STACK *untrusted;
 STACK *crls;

 X509_VERIFY_PARAM *param;
 void *other_ctx;


 int (*verify)(X509_STORE_CTX *ctx);
 int (*verify_cb)(int ok,X509_STORE_CTX *ctx);
 int (*get_issuer)(X509 **issuer, X509_STORE_CTX *ctx, X509 *x);
 int (*check_issued)(X509_STORE_CTX *ctx, X509 *x, X509 *issuer);
 int (*check_revocation)(X509_STORE_CTX *ctx);
 int (*get_crl)(X509_STORE_CTX *ctx, X509_CRL **crl, X509 *x);
 int (*check_crl)(X509_STORE_CTX *ctx, X509_CRL *crl);
 int (*cert_crl)(X509_STORE_CTX *ctx, X509_CRL *crl, X509 *x);
 int (*check_policy)(X509_STORE_CTX *ctx);
 int (*cleanup)(X509_STORE_CTX *ctx);


 int valid;
 int last_untrusted;
 STACK *chain;
 X509_POLICY_TREE *tree;

 int explicit_policy;


 int error_depth;
 int error;
 X509 *current_cert;
 X509 *current_issuer;
 X509_CRL *current_crl;

 CRYPTO_EX_DATA ex_data;
 } ;

void X509_STORE_CTX_set_depth(X509_STORE_CTX *ctx, int depth) __attribute__((deprecated));
# 383 "/usr/include/openssl/x509_vfy.h" 3 4
int X509_OBJECT_idx_by_subject(STACK *h, int type,
      X509_NAME *name) __attribute__((deprecated));
X509_OBJECT *X509_OBJECT_retrieve_by_subject(STACK *h,int type,X509_NAME *name) __attribute__((deprecated));
X509_OBJECT *X509_OBJECT_retrieve_match(STACK *h, X509_OBJECT *x) __attribute__((deprecated));
void X509_OBJECT_up_ref_count(X509_OBJECT *a) __attribute__((deprecated));
void X509_OBJECT_free_contents(X509_OBJECT *a) __attribute__((deprecated));
X509_STORE *X509_STORE_new(void ) __attribute__((deprecated));
void X509_STORE_free(X509_STORE *v) __attribute__((deprecated));

int X509_STORE_set_flags(X509_STORE *ctx, unsigned long flags) __attribute__((deprecated));
int X509_STORE_set_purpose(X509_STORE *ctx, int purpose) __attribute__((deprecated));
int X509_STORE_set_trust(X509_STORE *ctx, int trust) __attribute__((deprecated));
int X509_STORE_set1_param(X509_STORE *ctx, X509_VERIFY_PARAM *pm) __attribute__((deprecated));

X509_STORE_CTX *X509_STORE_CTX_new(void) __attribute__((deprecated));

int X509_STORE_CTX_get1_issuer(X509 **issuer, X509_STORE_CTX *ctx, X509 *x) __attribute__((deprecated));

void X509_STORE_CTX_free(X509_STORE_CTX *ctx) __attribute__((deprecated));
int X509_STORE_CTX_init(X509_STORE_CTX *ctx, X509_STORE *store,
    X509 *x509, STACK *chain) __attribute__((deprecated));
void X509_STORE_CTX_trusted_stack(X509_STORE_CTX *ctx, STACK *sk) __attribute__((deprecated));
void X509_STORE_CTX_cleanup(X509_STORE_CTX *ctx) __attribute__((deprecated));

X509_LOOKUP *X509_STORE_add_lookup(X509_STORE *v, X509_LOOKUP_METHOD *m) __attribute__((deprecated));

X509_LOOKUP_METHOD *X509_LOOKUP_hash_dir(void) __attribute__((deprecated));
X509_LOOKUP_METHOD *X509_LOOKUP_file(void) __attribute__((deprecated));

int X509_STORE_add_cert(X509_STORE *ctx, X509 *x) __attribute__((deprecated));
int X509_STORE_add_crl(X509_STORE *ctx, X509_CRL *x) __attribute__((deprecated));

int X509_STORE_get_by_subject(X509_STORE_CTX *vs,int type,X509_NAME *name,
 X509_OBJECT *ret) __attribute__((deprecated));

int X509_LOOKUP_ctrl(X509_LOOKUP *ctx, int cmd, const char *argc,
 long argl, char **ret) __attribute__((deprecated));


int X509_load_cert_file(X509_LOOKUP *ctx, const char *file, int type) __attribute__((deprecated));
int X509_load_crl_file(X509_LOOKUP *ctx, const char *file, int type) __attribute__((deprecated));
int X509_load_cert_crl_file(X509_LOOKUP *ctx, const char *file, int type) __attribute__((deprecated));



X509_LOOKUP *X509_LOOKUP_new(X509_LOOKUP_METHOD *method) __attribute__((deprecated));
void X509_LOOKUP_free(X509_LOOKUP *ctx) __attribute__((deprecated));
int X509_LOOKUP_init(X509_LOOKUP *ctx) __attribute__((deprecated));
int X509_LOOKUP_by_subject(X509_LOOKUP *ctx, int type, X509_NAME *name,
 X509_OBJECT *ret) __attribute__((deprecated));
int X509_LOOKUP_by_issuer_serial(X509_LOOKUP *ctx, int type, X509_NAME *name,
 ASN1_INTEGER *serial, X509_OBJECT *ret) __attribute__((deprecated));
int X509_LOOKUP_by_fingerprint(X509_LOOKUP *ctx, int type,
 unsigned char *bytes, int len, X509_OBJECT *ret) __attribute__((deprecated));
int X509_LOOKUP_by_alias(X509_LOOKUP *ctx, int type, char *str,
 int len, X509_OBJECT *ret) __attribute__((deprecated));
int X509_LOOKUP_shutdown(X509_LOOKUP *ctx) __attribute__((deprecated));


int X509_STORE_load_locations (X509_STORE *ctx,
  const char *file, const char *dir) __attribute__((deprecated));
int X509_STORE_set_default_paths(X509_STORE *ctx) __attribute__((deprecated));


int X509_STORE_CTX_get_ex_new_index(long argl, void *argp, CRYPTO_EX_new *new_func,
 CRYPTO_EX_dup *dup_func, CRYPTO_EX_free *free_func) __attribute__((deprecated));
int X509_STORE_CTX_set_ex_data(X509_STORE_CTX *ctx,int idx,void *data) __attribute__((deprecated));
void * X509_STORE_CTX_get_ex_data(X509_STORE_CTX *ctx,int idx) __attribute__((deprecated));
int X509_STORE_CTX_get_error(X509_STORE_CTX *ctx) __attribute__((deprecated));
void X509_STORE_CTX_set_error(X509_STORE_CTX *ctx,int s) __attribute__((deprecated));
int X509_STORE_CTX_get_error_depth(X509_STORE_CTX *ctx) __attribute__((deprecated));
X509 * X509_STORE_CTX_get_current_cert(X509_STORE_CTX *ctx) __attribute__((deprecated));
STACK *X509_STORE_CTX_get_chain(X509_STORE_CTX *ctx) __attribute__((deprecated));
STACK *X509_STORE_CTX_get1_chain(X509_STORE_CTX *ctx) __attribute__((deprecated));
void X509_STORE_CTX_set_cert(X509_STORE_CTX *c,X509 *x) __attribute__((deprecated));
void X509_STORE_CTX_set_chain(X509_STORE_CTX *c,STACK *sk) __attribute__((deprecated));
void X509_STORE_CTX_set0_crls(X509_STORE_CTX *c,STACK *sk) __attribute__((deprecated));
int X509_STORE_CTX_set_purpose(X509_STORE_CTX *ctx, int purpose) __attribute__((deprecated));
int X509_STORE_CTX_set_trust(X509_STORE_CTX *ctx, int trust) __attribute__((deprecated));
int X509_STORE_CTX_purpose_inherit(X509_STORE_CTX *ctx, int def_purpose,
    int purpose, int trust) __attribute__((deprecated));
void X509_STORE_CTX_set_flags(X509_STORE_CTX *ctx, unsigned long flags) __attribute__((deprecated));
void X509_STORE_CTX_set_time(X509_STORE_CTX *ctx, unsigned long flags,
        time_t t) __attribute__((deprecated));
void X509_STORE_CTX_set_verify_cb(X509_STORE_CTX *ctx,
      int (*verify_cb)(int, X509_STORE_CTX *)) __attribute__((deprecated));

X509_POLICY_TREE *X509_STORE_CTX_get0_policy_tree(X509_STORE_CTX *ctx) __attribute__((deprecated));
int X509_STORE_CTX_get_explicit_policy(X509_STORE_CTX *ctx) __attribute__((deprecated));

X509_VERIFY_PARAM *X509_STORE_CTX_get0_param(X509_STORE_CTX *ctx) __attribute__((deprecated));
void X509_STORE_CTX_set0_param(X509_STORE_CTX *ctx, X509_VERIFY_PARAM *param) __attribute__((deprecated));
int X509_STORE_CTX_set_default(X509_STORE_CTX *ctx, const char *name) __attribute__((deprecated));



X509_VERIFY_PARAM *X509_VERIFY_PARAM_new(void) __attribute__((deprecated));
void X509_VERIFY_PARAM_free(X509_VERIFY_PARAM *param) __attribute__((deprecated));
int X509_VERIFY_PARAM_inherit(X509_VERIFY_PARAM *to,
      const X509_VERIFY_PARAM *from) __attribute__((deprecated));
int X509_VERIFY_PARAM_set1(X509_VERIFY_PARAM *to,
      const X509_VERIFY_PARAM *from) __attribute__((deprecated));
int X509_VERIFY_PARAM_set1_name(X509_VERIFY_PARAM *param, const char *name) __attribute__((deprecated));
int X509_VERIFY_PARAM_set_flags(X509_VERIFY_PARAM *param, unsigned long flags) __attribute__((deprecated));
int X509_VERIFY_PARAM_clear_flags(X509_VERIFY_PARAM *param,
       unsigned long flags) __attribute__((deprecated));
unsigned long X509_VERIFY_PARAM_get_flags(X509_VERIFY_PARAM *param) __attribute__((deprecated));
int X509_VERIFY_PARAM_set_purpose(X509_VERIFY_PARAM *param, int purpose) __attribute__((deprecated));
int X509_VERIFY_PARAM_set_trust(X509_VERIFY_PARAM *param, int trust) __attribute__((deprecated));
void X509_VERIFY_PARAM_set_depth(X509_VERIFY_PARAM *param, int depth) __attribute__((deprecated));
void X509_VERIFY_PARAM_set_time(X509_VERIFY_PARAM *param, time_t t) __attribute__((deprecated));
int X509_VERIFY_PARAM_add0_policy(X509_VERIFY_PARAM *param,
      ASN1_OBJECT *policy) __attribute__((deprecated));
int X509_VERIFY_PARAM_set1_policies(X509_VERIFY_PARAM *param,
     STACK *policies) __attribute__((deprecated));
int X509_VERIFY_PARAM_get_depth(const X509_VERIFY_PARAM *param) __attribute__((deprecated));

int X509_VERIFY_PARAM_add0_table(X509_VERIFY_PARAM *param) __attribute__((deprecated));
const X509_VERIFY_PARAM *X509_VERIFY_PARAM_lookup(const char *name) __attribute__((deprecated));
void X509_VERIFY_PARAM_table_cleanup(void) __attribute__((deprecated));

int X509_policy_check(X509_POLICY_TREE **ptree, int *pexplicit_policy,
   STACK *certs,
   STACK *policy_oids,
   unsigned int flags) __attribute__((deprecated));

void X509_policy_tree_free(X509_POLICY_TREE *tree) __attribute__((deprecated));

int X509_policy_tree_level_count(const X509_POLICY_TREE *tree) __attribute__((deprecated));
X509_POLICY_LEVEL *
 X509_policy_tree_get0_level(const X509_POLICY_TREE *tree, int i) __attribute__((deprecated));

STACK *
 X509_policy_tree_get0_policies(const X509_POLICY_TREE *tree) __attribute__((deprecated));

STACK *
 X509_policy_tree_get0_user_policies(const X509_POLICY_TREE *tree) __attribute__((deprecated));

int X509_policy_level_node_count(X509_POLICY_LEVEL *level) __attribute__((deprecated));

X509_POLICY_NODE *X509_policy_level_get0_node(X509_POLICY_LEVEL *level, int i) __attribute__((deprecated));

const ASN1_OBJECT *X509_policy_node_get0_policy(const X509_POLICY_NODE *node) __attribute__((deprecated));

STACK *
 X509_policy_node_get0_qualifiers(const X509_POLICY_NODE *node) __attribute__((deprecated));
const X509_POLICY_NODE *
 X509_policy_node_get0_parent(const X509_POLICY_NODE *node) __attribute__((deprecated));
# 576 "/usr/include/openssl/x509.h" 2 3 4
# 1 "/usr/include/openssl/pkcs7.h" 1 3 4
# 66 "/usr/include/openssl/pkcs7.h" 3 4
# 1 "/usr/include/openssl/e_os2.h" 1 3 4
# 56 "/usr/include/openssl/e_os2.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 57 "/usr/include/openssl/e_os2.h" 2 3 4
# 67 "/usr/include/openssl/pkcs7.h" 2 3 4

# 1 "/usr/include/openssl/symhacks.h" 1 3 4
# 69 "/usr/include/openssl/pkcs7.h" 2 3 4
# 88 "/usr/include/openssl/pkcs7.h" 3 4
typedef struct pkcs7_issuer_and_serial_st
 {
 X509_NAME *issuer;
 ASN1_INTEGER *serial;
 } PKCS7_ISSUER_AND_SERIAL;

typedef struct pkcs7_signer_info_st
 {
 ASN1_INTEGER *version;
 PKCS7_ISSUER_AND_SERIAL *issuer_and_serial;
 X509_ALGOR *digest_alg;
 STACK *auth_attr;
 X509_ALGOR *digest_enc_alg;
 ASN1_OCTET_STRING *enc_digest;
 STACK *unauth_attr;


 EVP_PKEY *pkey;
 } PKCS7_SIGNER_INFO;




typedef struct pkcs7_recip_info_st
 {
 ASN1_INTEGER *version;
 PKCS7_ISSUER_AND_SERIAL *issuer_and_serial;
 X509_ALGOR *key_enc_algor;
 ASN1_OCTET_STRING *enc_key;
 X509 *cert;
 } PKCS7_RECIP_INFO;




typedef struct pkcs7_signed_st
 {
 ASN1_INTEGER *version;
 STACK *md_algs;
 STACK *cert;
 STACK *crl;
 STACK *signer_info;

 struct pkcs7_st *contents;
 } PKCS7_SIGNED;



typedef struct pkcs7_enc_content_st
 {
 ASN1_OBJECT *content_type;
 X509_ALGOR *algorithm;
 ASN1_OCTET_STRING *enc_data;
 const EVP_CIPHER *cipher;
 } PKCS7_ENC_CONTENT;

typedef struct pkcs7_enveloped_st
 {
 ASN1_INTEGER *version;
 STACK *recipientinfo;
 PKCS7_ENC_CONTENT *enc_data;
 } PKCS7_ENVELOPE;

typedef struct pkcs7_signedandenveloped_st
 {
 ASN1_INTEGER *version;
 STACK *md_algs;
 STACK *cert;
 STACK *crl;
 STACK *signer_info;

 PKCS7_ENC_CONTENT *enc_data;
 STACK *recipientinfo;
 } PKCS7_SIGN_ENVELOPE;

typedef struct pkcs7_digest_st
 {
 ASN1_INTEGER *version;
 X509_ALGOR *md;
 struct pkcs7_st *contents;
 ASN1_OCTET_STRING *digest;
 } PKCS7_DIGEST;

typedef struct pkcs7_encrypted_st
 {
 ASN1_INTEGER *version;
 PKCS7_ENC_CONTENT *enc_data;
 } PKCS7_ENCRYPT;

typedef struct pkcs7_st
 {


 unsigned char *asn1;
 long length;




 int state;

 int detached;

 ASN1_OBJECT *type;



 union {
  char *ptr;


  ASN1_OCTET_STRING *data;


  PKCS7_SIGNED *sign;


  PKCS7_ENVELOPE *enveloped;


  PKCS7_SIGN_ENVELOPE *signed_and_enveloped;


  PKCS7_DIGEST *digest;


  PKCS7_ENCRYPT *encrypted;


  ASN1_TYPE *other;
  } d;
 } PKCS7;




# 284 "/usr/include/openssl/pkcs7.h" 3 4
PKCS7_ISSUER_AND_SERIAL *PKCS7_ISSUER_AND_SERIAL_new(void); void PKCS7_ISSUER_AND_SERIAL_free(PKCS7_ISSUER_AND_SERIAL *a); PKCS7_ISSUER_AND_SERIAL *d2i_PKCS7_ISSUER_AND_SERIAL(PKCS7_ISSUER_AND_SERIAL **a, const unsigned char **in, long len); int i2d_PKCS7_ISSUER_AND_SERIAL(PKCS7_ISSUER_AND_SERIAL *a, unsigned char **out); extern const ASN1_ITEM PKCS7_ISSUER_AND_SERIAL_it;


int PKCS7_ISSUER_AND_SERIAL_digest(PKCS7_ISSUER_AND_SERIAL *data,const EVP_MD *type,
 unsigned char *md,unsigned int *len) __attribute__((deprecated));

PKCS7 *d2i_PKCS7_fp(FILE *fp,PKCS7 **p7) __attribute__((deprecated));
int i2d_PKCS7_fp(FILE *fp,PKCS7 *p7) __attribute__((deprecated));

PKCS7 *PKCS7_dup(PKCS7 *p7) __attribute__((deprecated));
PKCS7 *d2i_PKCS7_bio(BIO *bp,PKCS7 **p7) __attribute__((deprecated));
int i2d_PKCS7_bio(BIO *bp,PKCS7 *p7) __attribute__((deprecated));


PKCS7_SIGNER_INFO *PKCS7_SIGNER_INFO_new(void); void PKCS7_SIGNER_INFO_free(PKCS7_SIGNER_INFO *a); PKCS7_SIGNER_INFO *d2i_PKCS7_SIGNER_INFO(PKCS7_SIGNER_INFO **a, const unsigned char **in, long len); int i2d_PKCS7_SIGNER_INFO(PKCS7_SIGNER_INFO *a, unsigned char **out); extern const ASN1_ITEM PKCS7_SIGNER_INFO_it;
PKCS7_RECIP_INFO *PKCS7_RECIP_INFO_new(void); void PKCS7_RECIP_INFO_free(PKCS7_RECIP_INFO *a); PKCS7_RECIP_INFO *d2i_PKCS7_RECIP_INFO(PKCS7_RECIP_INFO **a, const unsigned char **in, long len); int i2d_PKCS7_RECIP_INFO(PKCS7_RECIP_INFO *a, unsigned char **out); extern const ASN1_ITEM PKCS7_RECIP_INFO_it;
PKCS7_SIGNED *PKCS7_SIGNED_new(void); void PKCS7_SIGNED_free(PKCS7_SIGNED *a); PKCS7_SIGNED *d2i_PKCS7_SIGNED(PKCS7_SIGNED **a, const unsigned char **in, long len); int i2d_PKCS7_SIGNED(PKCS7_SIGNED *a, unsigned char **out); extern const ASN1_ITEM PKCS7_SIGNED_it;
PKCS7_ENC_CONTENT *PKCS7_ENC_CONTENT_new(void); void PKCS7_ENC_CONTENT_free(PKCS7_ENC_CONTENT *a); PKCS7_ENC_CONTENT *d2i_PKCS7_ENC_CONTENT(PKCS7_ENC_CONTENT **a, const unsigned char **in, long len); int i2d_PKCS7_ENC_CONTENT(PKCS7_ENC_CONTENT *a, unsigned char **out); extern const ASN1_ITEM PKCS7_ENC_CONTENT_it;
PKCS7_ENVELOPE *PKCS7_ENVELOPE_new(void); void PKCS7_ENVELOPE_free(PKCS7_ENVELOPE *a); PKCS7_ENVELOPE *d2i_PKCS7_ENVELOPE(PKCS7_ENVELOPE **a, const unsigned char **in, long len); int i2d_PKCS7_ENVELOPE(PKCS7_ENVELOPE *a, unsigned char **out); extern const ASN1_ITEM PKCS7_ENVELOPE_it;
PKCS7_SIGN_ENVELOPE *PKCS7_SIGN_ENVELOPE_new(void); void PKCS7_SIGN_ENVELOPE_free(PKCS7_SIGN_ENVELOPE *a); PKCS7_SIGN_ENVELOPE *d2i_PKCS7_SIGN_ENVELOPE(PKCS7_SIGN_ENVELOPE **a, const unsigned char **in, long len); int i2d_PKCS7_SIGN_ENVELOPE(PKCS7_SIGN_ENVELOPE *a, unsigned char **out); extern const ASN1_ITEM PKCS7_SIGN_ENVELOPE_it;
PKCS7_DIGEST *PKCS7_DIGEST_new(void); void PKCS7_DIGEST_free(PKCS7_DIGEST *a); PKCS7_DIGEST *d2i_PKCS7_DIGEST(PKCS7_DIGEST **a, const unsigned char **in, long len); int i2d_PKCS7_DIGEST(PKCS7_DIGEST *a, unsigned char **out); extern const ASN1_ITEM PKCS7_DIGEST_it;
PKCS7_ENCRYPT *PKCS7_ENCRYPT_new(void); void PKCS7_ENCRYPT_free(PKCS7_ENCRYPT *a); PKCS7_ENCRYPT *d2i_PKCS7_ENCRYPT(PKCS7_ENCRYPT **a, const unsigned char **in, long len); int i2d_PKCS7_ENCRYPT(PKCS7_ENCRYPT *a, unsigned char **out); extern const ASN1_ITEM PKCS7_ENCRYPT_it;
PKCS7 *PKCS7_new(void); void PKCS7_free(PKCS7 *a); PKCS7 *d2i_PKCS7(PKCS7 **a, const unsigned char **in, long len); int i2d_PKCS7(PKCS7 *a, unsigned char **out); extern const ASN1_ITEM PKCS7_it;

extern const ASN1_ITEM PKCS7_ATTR_SIGN_it;
extern const ASN1_ITEM PKCS7_ATTR_VERIFY_it;

int i2d_PKCS7_NDEF(PKCS7 *a, unsigned char **out);

long PKCS7_ctrl(PKCS7 *p7, int cmd, long larg, char *parg) __attribute__((deprecated));

int PKCS7_set_type(PKCS7 *p7, int type) __attribute__((deprecated));
int PKCS7_set0_type_other(PKCS7 *p7, int type, ASN1_TYPE *other) __attribute__((deprecated));
int PKCS7_set_content(PKCS7 *p7, PKCS7 *p7_data) __attribute__((deprecated));
int PKCS7_SIGNER_INFO_set(PKCS7_SIGNER_INFO *p7i, X509 *x509, EVP_PKEY *pkey,
 const EVP_MD *dgst) __attribute__((deprecated));
int PKCS7_add_signer(PKCS7 *p7, PKCS7_SIGNER_INFO *p7i) __attribute__((deprecated));
int PKCS7_add_certificate(PKCS7 *p7, X509 *x509) __attribute__((deprecated));
int PKCS7_add_crl(PKCS7 *p7, X509_CRL *x509) __attribute__((deprecated));
int PKCS7_content_new(PKCS7 *p7, int nid) __attribute__((deprecated));
int PKCS7_dataVerify(X509_STORE *cert_store, X509_STORE_CTX *ctx,
 BIO *bio, PKCS7 *p7, PKCS7_SIGNER_INFO *si) __attribute__((deprecated));
int PKCS7_signatureVerify(BIO *bio, PKCS7 *p7, PKCS7_SIGNER_INFO *si,
        X509 *x509) __attribute__((deprecated));

BIO *PKCS7_dataInit(PKCS7 *p7, BIO *bio) __attribute__((deprecated));
int PKCS7_dataFinal(PKCS7 *p7, BIO *bio) __attribute__((deprecated));
BIO *PKCS7_dataDecode(PKCS7 *p7, EVP_PKEY *pkey, BIO *in_bio, X509 *pcert) __attribute__((deprecated));


PKCS7_SIGNER_INFO *PKCS7_add_signature(PKCS7 *p7, X509 *x509,
 EVP_PKEY *pkey, const EVP_MD *dgst) __attribute__((deprecated));
X509 *PKCS7_cert_from_signer_info(PKCS7 *p7, PKCS7_SIGNER_INFO *si) __attribute__((deprecated));
int PKCS7_set_digest(PKCS7 *p7, const EVP_MD *md) __attribute__((deprecated));
STACK *PKCS7_get_signer_info(PKCS7 *p7) __attribute__((deprecated));

PKCS7_RECIP_INFO *PKCS7_add_recipient(PKCS7 *p7, X509 *x509) __attribute__((deprecated));
int PKCS7_add_recipient_info(PKCS7 *p7, PKCS7_RECIP_INFO *ri) __attribute__((deprecated));
int PKCS7_RECIP_INFO_set(PKCS7_RECIP_INFO *p7i, X509 *x509) __attribute__((deprecated));
int PKCS7_set_cipher(PKCS7 *p7, const EVP_CIPHER *cipher) __attribute__((deprecated));

PKCS7_ISSUER_AND_SERIAL *PKCS7_get_issuer_and_serial(PKCS7 *p7, int idx) __attribute__((deprecated));
ASN1_OCTET_STRING *PKCS7_digest_from_attributes(STACK *sk) __attribute__((deprecated));
int PKCS7_add_signed_attribute(PKCS7_SIGNER_INFO *p7si,int nid,int type,
 void *data) __attribute__((deprecated));
int PKCS7_add_attribute (PKCS7_SIGNER_INFO *p7si, int nid, int atrtype,
 void *value) __attribute__((deprecated));
ASN1_TYPE *PKCS7_get_attribute(PKCS7_SIGNER_INFO *si, int nid) __attribute__((deprecated));
ASN1_TYPE *PKCS7_get_signed_attribute(PKCS7_SIGNER_INFO *si, int nid) __attribute__((deprecated));
int PKCS7_set_signed_attributes(PKCS7_SIGNER_INFO *p7si,
    STACK *sk) __attribute__((deprecated));
int PKCS7_set_attributes(PKCS7_SIGNER_INFO *p7si,STACK *sk) __attribute__((deprecated));


PKCS7 *PKCS7_sign(X509 *signcert, EVP_PKEY *pkey, STACK *certs,
       BIO *data, int flags) __attribute__((deprecated));
int PKCS7_verify(PKCS7 *p7, STACK *certs, X509_STORE *store,
     BIO *indata, BIO *out, int flags) __attribute__((deprecated));
STACK *PKCS7_get0_signers(PKCS7 *p7, STACK *certs, int flags) __attribute__((deprecated));
PKCS7 *PKCS7_encrypt(STACK *certs, BIO *in, const EVP_CIPHER *cipher,
        int flags) __attribute__((deprecated));
int PKCS7_decrypt(PKCS7 *p7, EVP_PKEY *pkey, X509 *cert, BIO *data, int flags) __attribute__((deprecated));

int PKCS7_add_attrib_smimecap(PKCS7_SIGNER_INFO *si,
         STACK *cap) __attribute__((deprecated));
STACK *PKCS7_get_smimecap(PKCS7_SIGNER_INFO *si) __attribute__((deprecated));
int PKCS7_simple_smimecap(STACK *sk, int nid, int arg) __attribute__((deprecated));

int SMIME_write_PKCS7(BIO *bio, PKCS7 *p7, BIO *data, int flags) __attribute__((deprecated));
PKCS7 *SMIME_read_PKCS7(BIO *bio, BIO **bcont) __attribute__((deprecated));
int SMIME_crlf_copy(BIO *in, BIO *out, int flags) __attribute__((deprecated));
int SMIME_text(BIO *in, BIO *out) __attribute__((deprecated));





void ERR_load_PKCS7_strings(void) __attribute__((deprecated));
# 577 "/usr/include/openssl/x509.h" 2 3 4
# 752 "/usr/include/openssl/x509.h" 3 4
const char *X509_verify_cert_error_string(long n) __attribute__((deprecated));



int X509_verify(X509 *a, EVP_PKEY *r) __attribute__((deprecated));

int X509_REQ_verify(X509_REQ *a, EVP_PKEY *r) __attribute__((deprecated));
int X509_CRL_verify(X509_CRL *a, EVP_PKEY *r) __attribute__((deprecated));
int NETSCAPE_SPKI_verify(NETSCAPE_SPKI *a, EVP_PKEY *r) __attribute__((deprecated));

NETSCAPE_SPKI * NETSCAPE_SPKI_b64_decode(const char *str, int len) __attribute__((deprecated));
char * NETSCAPE_SPKI_b64_encode(NETSCAPE_SPKI *x) __attribute__((deprecated));
EVP_PKEY *NETSCAPE_SPKI_get_pubkey(NETSCAPE_SPKI *x) __attribute__((deprecated));
int NETSCAPE_SPKI_set_pubkey(NETSCAPE_SPKI *x, EVP_PKEY *pkey) __attribute__((deprecated));

int NETSCAPE_SPKI_print(BIO *out, NETSCAPE_SPKI *spki) __attribute__((deprecated));

int X509_signature_print(BIO *bp,X509_ALGOR *alg, ASN1_STRING *sig) __attribute__((deprecated));

int X509_sign(X509 *x, EVP_PKEY *pkey, const EVP_MD *md) __attribute__((deprecated));
int X509_REQ_sign(X509_REQ *x, EVP_PKEY *pkey, const EVP_MD *md) __attribute__((deprecated));
int X509_CRL_sign(X509_CRL *x, EVP_PKEY *pkey, const EVP_MD *md) __attribute__((deprecated));
int NETSCAPE_SPKI_sign(NETSCAPE_SPKI *x, EVP_PKEY *pkey, const EVP_MD *md) __attribute__((deprecated));

int X509_pubkey_digest(const X509 *data,const EVP_MD *type,
  unsigned char *md, unsigned int *len) __attribute__((deprecated));
int X509_digest(const X509 *data,const EVP_MD *type,
  unsigned char *md, unsigned int *len) __attribute__((deprecated));
int X509_CRL_digest(const X509_CRL *data,const EVP_MD *type,
  unsigned char *md, unsigned int *len) __attribute__((deprecated));
int X509_REQ_digest(const X509_REQ *data,const EVP_MD *type,
  unsigned char *md, unsigned int *len) __attribute__((deprecated));
int X509_NAME_digest(const X509_NAME *data,const EVP_MD *type,
  unsigned char *md, unsigned int *len) __attribute__((deprecated));



X509 *d2i_X509_fp(FILE *fp, X509 **x509) __attribute__((deprecated));
int i2d_X509_fp(FILE *fp,X509 *x509) __attribute__((deprecated));
X509_CRL *d2i_X509_CRL_fp(FILE *fp,X509_CRL **crl) __attribute__((deprecated));
int i2d_X509_CRL_fp(FILE *fp,X509_CRL *crl) __attribute__((deprecated));
X509_REQ *d2i_X509_REQ_fp(FILE *fp,X509_REQ **req) __attribute__((deprecated));
int i2d_X509_REQ_fp(FILE *fp,X509_REQ *req) __attribute__((deprecated));

RSA *d2i_RSAPrivateKey_fp(FILE *fp,RSA **rsa) __attribute__((deprecated));
int i2d_RSAPrivateKey_fp(FILE *fp,RSA *rsa) __attribute__((deprecated));
RSA *d2i_RSAPublicKey_fp(FILE *fp,RSA **rsa) __attribute__((deprecated));
int i2d_RSAPublicKey_fp(FILE *fp,RSA *rsa) __attribute__((deprecated));
RSA *d2i_RSA_PUBKEY_fp(FILE *fp,RSA **rsa) __attribute__((deprecated));
int i2d_RSA_PUBKEY_fp(FILE *fp,RSA *rsa) __attribute__((deprecated));


DSA *d2i_DSA_PUBKEY_fp(FILE *fp, DSA **dsa) __attribute__((deprecated));
int i2d_DSA_PUBKEY_fp(FILE *fp, DSA *dsa) __attribute__((deprecated));
DSA *d2i_DSAPrivateKey_fp(FILE *fp, DSA **dsa) __attribute__((deprecated));
int i2d_DSAPrivateKey_fp(FILE *fp, DSA *dsa) __attribute__((deprecated));


EC_KEY *d2i_EC_PUBKEY_fp(FILE *fp, EC_KEY **eckey) __attribute__((deprecated));
int i2d_EC_PUBKEY_fp(FILE *fp, EC_KEY *eckey) __attribute__((deprecated));
EC_KEY *d2i_ECPrivateKey_fp(FILE *fp, EC_KEY **eckey) __attribute__((deprecated));
int i2d_ECPrivateKey_fp(FILE *fp, EC_KEY *eckey) __attribute__((deprecated));

X509_SIG *d2i_PKCS8_fp(FILE *fp,X509_SIG **p8) __attribute__((deprecated));
int i2d_PKCS8_fp(FILE *fp,X509_SIG *p8) __attribute__((deprecated));
PKCS8_PRIV_KEY_INFO *d2i_PKCS8_PRIV_KEY_INFO_fp(FILE *fp,
      PKCS8_PRIV_KEY_INFO **p8inf) __attribute__((deprecated));
int i2d_PKCS8_PRIV_KEY_INFO_fp(FILE *fp,PKCS8_PRIV_KEY_INFO *p8inf) __attribute__((deprecated));
int i2d_PKCS8PrivateKeyInfo_fp(FILE *fp, EVP_PKEY *key) __attribute__((deprecated));
int i2d_PrivateKey_fp(FILE *fp, EVP_PKEY *pkey) __attribute__((deprecated));
EVP_PKEY *d2i_PrivateKey_fp(FILE *fp, EVP_PKEY **a) __attribute__((deprecated));
int i2d_PUBKEY_fp(FILE *fp, EVP_PKEY *pkey) __attribute__((deprecated));
EVP_PKEY *d2i_PUBKEY_fp(FILE *fp, EVP_PKEY **a) __attribute__((deprecated));



X509 *d2i_X509_bio(BIO *bp,X509 **x509) __attribute__((deprecated));
int i2d_X509_bio(BIO *bp,X509 *x509) __attribute__((deprecated));
X509_CRL *d2i_X509_CRL_bio(BIO *bp,X509_CRL **crl) __attribute__((deprecated));
int i2d_X509_CRL_bio(BIO *bp,X509_CRL *crl) __attribute__((deprecated));
X509_REQ *d2i_X509_REQ_bio(BIO *bp,X509_REQ **req) __attribute__((deprecated));
int i2d_X509_REQ_bio(BIO *bp,X509_REQ *req) __attribute__((deprecated));

RSA *d2i_RSAPrivateKey_bio(BIO *bp,RSA **rsa) __attribute__((deprecated));
int i2d_RSAPrivateKey_bio(BIO *bp,RSA *rsa) __attribute__((deprecated));
RSA *d2i_RSAPublicKey_bio(BIO *bp,RSA **rsa) __attribute__((deprecated));
int i2d_RSAPublicKey_bio(BIO *bp,RSA *rsa) __attribute__((deprecated));
RSA *d2i_RSA_PUBKEY_bio(BIO *bp,RSA **rsa) __attribute__((deprecated));
int i2d_RSA_PUBKEY_bio(BIO *bp,RSA *rsa) __attribute__((deprecated));


DSA *d2i_DSA_PUBKEY_bio(BIO *bp, DSA **dsa) __attribute__((deprecated));
int i2d_DSA_PUBKEY_bio(BIO *bp, DSA *dsa) __attribute__((deprecated));
DSA *d2i_DSAPrivateKey_bio(BIO *bp, DSA **dsa) __attribute__((deprecated));
int i2d_DSAPrivateKey_bio(BIO *bp, DSA *dsa) __attribute__((deprecated));


EC_KEY *d2i_EC_PUBKEY_bio(BIO *bp, EC_KEY **eckey) __attribute__((deprecated));
int i2d_EC_PUBKEY_bio(BIO *bp, EC_KEY *eckey) __attribute__((deprecated));
EC_KEY *d2i_ECPrivateKey_bio(BIO *bp, EC_KEY **eckey) __attribute__((deprecated));
int i2d_ECPrivateKey_bio(BIO *bp, EC_KEY *eckey) __attribute__((deprecated));

X509_SIG *d2i_PKCS8_bio(BIO *bp,X509_SIG **p8) __attribute__((deprecated));
int i2d_PKCS8_bio(BIO *bp,X509_SIG *p8) __attribute__((deprecated));
PKCS8_PRIV_KEY_INFO *d2i_PKCS8_PRIV_KEY_INFO_bio(BIO *bp,
      PKCS8_PRIV_KEY_INFO **p8inf) __attribute__((deprecated));
int i2d_PKCS8_PRIV_KEY_INFO_bio(BIO *bp,PKCS8_PRIV_KEY_INFO *p8inf) __attribute__((deprecated));
int i2d_PKCS8PrivateKeyInfo_bio(BIO *bp, EVP_PKEY *key) __attribute__((deprecated));
int i2d_PrivateKey_bio(BIO *bp, EVP_PKEY *pkey) __attribute__((deprecated));
EVP_PKEY *d2i_PrivateKey_bio(BIO *bp, EVP_PKEY **a) __attribute__((deprecated));
int i2d_PUBKEY_bio(BIO *bp, EVP_PKEY *pkey) __attribute__((deprecated));
EVP_PKEY *d2i_PUBKEY_bio(BIO *bp, EVP_PKEY **a) __attribute__((deprecated));


X509 *X509_dup(X509 *x509) __attribute__((deprecated));
X509_ATTRIBUTE *X509_ATTRIBUTE_dup(X509_ATTRIBUTE *xa) __attribute__((deprecated));
X509_EXTENSION *X509_EXTENSION_dup(X509_EXTENSION *ex) __attribute__((deprecated));
X509_CRL *X509_CRL_dup(X509_CRL *crl) __attribute__((deprecated));
X509_REQ *X509_REQ_dup(X509_REQ *req) __attribute__((deprecated));
X509_ALGOR *X509_ALGOR_dup(X509_ALGOR *xn) __attribute__((deprecated));
int X509_ALGOR_set0(X509_ALGOR *alg, ASN1_OBJECT *aobj, int ptype, void *pval) __attribute__((deprecated));
void X509_ALGOR_get0(ASN1_OBJECT **paobj, int *pptype, void **ppval,
      X509_ALGOR *algor) __attribute__((deprecated));

X509_NAME *X509_NAME_dup(X509_NAME *xn) __attribute__((deprecated));
X509_NAME_ENTRY *X509_NAME_ENTRY_dup(X509_NAME_ENTRY *ne) __attribute__((deprecated));



int X509_cmp_time(ASN1_TIME *s, time_t *t) __attribute__((deprecated));
int X509_cmp_current_time(ASN1_TIME *s) __attribute__((deprecated));
ASN1_TIME * X509_time_adj(ASN1_TIME *s, long adj, time_t *t) __attribute__((deprecated));
ASN1_TIME * X509_gmtime_adj(ASN1_TIME *s, long adj) __attribute__((deprecated));

const char * X509_get_default_cert_area(void ) __attribute__((deprecated));
const char * X509_get_default_cert_dir(void ) __attribute__((deprecated));
const char * X509_get_default_cert_file(void ) __attribute__((deprecated));
const char * X509_get_default_cert_dir_env(void ) __attribute__((deprecated));
const char * X509_get_default_cert_file_env(void ) __attribute__((deprecated));
const char * X509_get_default_private_dir(void ) __attribute__((deprecated));

X509_REQ * X509_to_X509_REQ(X509 *x, EVP_PKEY *pkey, const EVP_MD *md) __attribute__((deprecated));
X509 * X509_REQ_to_X509(X509_REQ *r, int days,EVP_PKEY *pkey) __attribute__((deprecated));

X509_ALGOR *X509_ALGOR_new(void); void X509_ALGOR_free(X509_ALGOR *a); X509_ALGOR *d2i_X509_ALGOR(X509_ALGOR **a, const unsigned char **in, long len); int i2d_X509_ALGOR(X509_ALGOR *a, unsigned char **out); extern const ASN1_ITEM X509_ALGOR_it;
X509_ALGORS *d2i_X509_ALGORS(X509_ALGORS **a, const unsigned char **in, long len); int i2d_X509_ALGORS(X509_ALGORS *a, unsigned char **out); extern const ASN1_ITEM X509_ALGORS_it;
X509_VAL *X509_VAL_new(void); void X509_VAL_free(X509_VAL *a); X509_VAL *d2i_X509_VAL(X509_VAL **a, const unsigned char **in, long len); int i2d_X509_VAL(X509_VAL *a, unsigned char **out); extern const ASN1_ITEM X509_VAL_it;

X509_PUBKEY *X509_PUBKEY_new(void); void X509_PUBKEY_free(X509_PUBKEY *a); X509_PUBKEY *d2i_X509_PUBKEY(X509_PUBKEY **a, const unsigned char **in, long len); int i2d_X509_PUBKEY(X509_PUBKEY *a, unsigned char **out); extern const ASN1_ITEM X509_PUBKEY_it;

int X509_PUBKEY_set(X509_PUBKEY **x, EVP_PKEY *pkey) __attribute__((deprecated));
EVP_PKEY * X509_PUBKEY_get(X509_PUBKEY *key) __attribute__((deprecated));
int X509_get_pubkey_parameters(EVP_PKEY *pkey,
        STACK *chain) __attribute__((deprecated));
int i2d_PUBKEY(EVP_PKEY *a,unsigned char **pp) __attribute__((deprecated));
EVP_PKEY * d2i_PUBKEY(EVP_PKEY **a,const unsigned char **pp,
   long length) __attribute__((deprecated));

int i2d_RSA_PUBKEY(RSA *a,unsigned char **pp) __attribute__((deprecated));
RSA * d2i_RSA_PUBKEY(RSA **a,const unsigned char **pp,
   long length) __attribute__((deprecated));


int i2d_DSA_PUBKEY(DSA *a,unsigned char **pp) __attribute__((deprecated));
DSA * d2i_DSA_PUBKEY(DSA **a,const unsigned char **pp,
   long length) __attribute__((deprecated));


int i2d_EC_PUBKEY(EC_KEY *a, unsigned char **pp) __attribute__((deprecated));
EC_KEY *d2i_EC_PUBKEY(EC_KEY **a, const unsigned char **pp,
   long length) __attribute__((deprecated));


X509_SIG *X509_SIG_new(void); void X509_SIG_free(X509_SIG *a); X509_SIG *d2i_X509_SIG(X509_SIG **a, const unsigned char **in, long len); int i2d_X509_SIG(X509_SIG *a, unsigned char **out); extern const ASN1_ITEM X509_SIG_it;
X509_REQ_INFO *X509_REQ_INFO_new(void); void X509_REQ_INFO_free(X509_REQ_INFO *a); X509_REQ_INFO *d2i_X509_REQ_INFO(X509_REQ_INFO **a, const unsigned char **in, long len); int i2d_X509_REQ_INFO(X509_REQ_INFO *a, unsigned char **out); extern const ASN1_ITEM X509_REQ_INFO_it;
X509_REQ *X509_REQ_new(void); void X509_REQ_free(X509_REQ *a); X509_REQ *d2i_X509_REQ(X509_REQ **a, const unsigned char **in, long len); int i2d_X509_REQ(X509_REQ *a, unsigned char **out); extern const ASN1_ITEM X509_REQ_it;

X509_ATTRIBUTE *X509_ATTRIBUTE_new(void); void X509_ATTRIBUTE_free(X509_ATTRIBUTE *a); X509_ATTRIBUTE *d2i_X509_ATTRIBUTE(X509_ATTRIBUTE **a, const unsigned char **in, long len); int i2d_X509_ATTRIBUTE(X509_ATTRIBUTE *a, unsigned char **out); extern const ASN1_ITEM X509_ATTRIBUTE_it;
X509_ATTRIBUTE *X509_ATTRIBUTE_create(int nid, int atrtype, void *value) __attribute__((deprecated));

X509_EXTENSION *X509_EXTENSION_new(void); void X509_EXTENSION_free(X509_EXTENSION *a); X509_EXTENSION *d2i_X509_EXTENSION(X509_EXTENSION **a, const unsigned char **in, long len); int i2d_X509_EXTENSION(X509_EXTENSION *a, unsigned char **out); extern const ASN1_ITEM X509_EXTENSION_it;
X509_EXTENSIONS *d2i_X509_EXTENSIONS(X509_EXTENSIONS **a, const unsigned char **in, long len); int i2d_X509_EXTENSIONS(X509_EXTENSIONS *a, unsigned char **out); extern const ASN1_ITEM X509_EXTENSIONS_it;

X509_NAME_ENTRY *X509_NAME_ENTRY_new(void); void X509_NAME_ENTRY_free(X509_NAME_ENTRY *a); X509_NAME_ENTRY *d2i_X509_NAME_ENTRY(X509_NAME_ENTRY **a, const unsigned char **in, long len); int i2d_X509_NAME_ENTRY(X509_NAME_ENTRY *a, unsigned char **out); extern const ASN1_ITEM X509_NAME_ENTRY_it;

X509_NAME *X509_NAME_new(void); void X509_NAME_free(X509_NAME *a); X509_NAME *d2i_X509_NAME(X509_NAME **a, const unsigned char **in, long len); int i2d_X509_NAME(X509_NAME *a, unsigned char **out); extern const ASN1_ITEM X509_NAME_it;

int X509_NAME_set(X509_NAME **xn, X509_NAME *name) __attribute__((deprecated));

X509_CINF *X509_CINF_new(void); void X509_CINF_free(X509_CINF *a); X509_CINF *d2i_X509_CINF(X509_CINF **a, const unsigned char **in, long len); int i2d_X509_CINF(X509_CINF *a, unsigned char **out); extern const ASN1_ITEM X509_CINF_it;

X509 *X509_new(void); void X509_free(X509 *a); X509 *d2i_X509(X509 **a, const unsigned char **in, long len); int i2d_X509(X509 *a, unsigned char **out); extern const ASN1_ITEM X509_it;
X509_CERT_AUX *X509_CERT_AUX_new(void); void X509_CERT_AUX_free(X509_CERT_AUX *a); X509_CERT_AUX *d2i_X509_CERT_AUX(X509_CERT_AUX **a, const unsigned char **in, long len); int i2d_X509_CERT_AUX(X509_CERT_AUX *a, unsigned char **out); extern const ASN1_ITEM X509_CERT_AUX_it;

X509_CERT_PAIR *X509_CERT_PAIR_new(void); void X509_CERT_PAIR_free(X509_CERT_PAIR *a); X509_CERT_PAIR *d2i_X509_CERT_PAIR(X509_CERT_PAIR **a, const unsigned char **in, long len); int i2d_X509_CERT_PAIR(X509_CERT_PAIR *a, unsigned char **out); extern const ASN1_ITEM X509_CERT_PAIR_it;

int X509_get_ex_new_index(long argl, void *argp, CRYPTO_EX_new *new_func,
      CRYPTO_EX_dup *dup_func, CRYPTO_EX_free *free_func) __attribute__((deprecated));
int X509_set_ex_data(X509 *r, int idx, void *arg) __attribute__((deprecated));
void *X509_get_ex_data(X509 *r, int idx) __attribute__((deprecated));
int i2d_X509_AUX(X509 *a,unsigned char **pp) __attribute__((deprecated));
X509 * d2i_X509_AUX(X509 **a,const unsigned char **pp,long length) __attribute__((deprecated));

int X509_alias_set1(X509 *x, unsigned char *name, int len) __attribute__((deprecated));
int X509_keyid_set1(X509 *x, unsigned char *id, int len) __attribute__((deprecated));
unsigned char * X509_alias_get0(X509 *x, int *len) __attribute__((deprecated));
unsigned char * X509_keyid_get0(X509 *x, int *len) __attribute__((deprecated));
int (*X509_TRUST_set_default(int (*trust)(int , X509 *, int)))(int, X509 *, int) __attribute__((deprecated));
int X509_TRUST_set(int *t, int trust) __attribute__((deprecated));
int X509_add1_trust_object(X509 *x, ASN1_OBJECT *obj) __attribute__((deprecated));
int X509_add1_reject_object(X509 *x, ASN1_OBJECT *obj) __attribute__((deprecated));
void X509_trust_clear(X509 *x) __attribute__((deprecated));
void X509_reject_clear(X509 *x) __attribute__((deprecated));

X509_REVOKED *X509_REVOKED_new(void); void X509_REVOKED_free(X509_REVOKED *a); X509_REVOKED *d2i_X509_REVOKED(X509_REVOKED **a, const unsigned char **in, long len); int i2d_X509_REVOKED(X509_REVOKED *a, unsigned char **out); extern const ASN1_ITEM X509_REVOKED_it;
X509_CRL_INFO *X509_CRL_INFO_new(void); void X509_CRL_INFO_free(X509_CRL_INFO *a); X509_CRL_INFO *d2i_X509_CRL_INFO(X509_CRL_INFO **a, const unsigned char **in, long len); int i2d_X509_CRL_INFO(X509_CRL_INFO *a, unsigned char **out); extern const ASN1_ITEM X509_CRL_INFO_it;
X509_CRL *X509_CRL_new(void); void X509_CRL_free(X509_CRL *a); X509_CRL *d2i_X509_CRL(X509_CRL **a, const unsigned char **in, long len); int i2d_X509_CRL(X509_CRL *a, unsigned char **out); extern const ASN1_ITEM X509_CRL_it;

int X509_CRL_add0_revoked(X509_CRL *crl, X509_REVOKED *rev) __attribute__((deprecated));

X509_PKEY * X509_PKEY_new(void ) __attribute__((deprecated));
void X509_PKEY_free(X509_PKEY *a) __attribute__((deprecated));
int i2d_X509_PKEY(X509_PKEY *a,unsigned char **pp) __attribute__((deprecated));
X509_PKEY * d2i_X509_PKEY(X509_PKEY **a,const unsigned char **pp,long length) __attribute__((deprecated));

NETSCAPE_SPKI *NETSCAPE_SPKI_new(void); void NETSCAPE_SPKI_free(NETSCAPE_SPKI *a); NETSCAPE_SPKI *d2i_NETSCAPE_SPKI(NETSCAPE_SPKI **a, const unsigned char **in, long len); int i2d_NETSCAPE_SPKI(NETSCAPE_SPKI *a, unsigned char **out); extern const ASN1_ITEM NETSCAPE_SPKI_it;
NETSCAPE_SPKAC *NETSCAPE_SPKAC_new(void); void NETSCAPE_SPKAC_free(NETSCAPE_SPKAC *a); NETSCAPE_SPKAC *d2i_NETSCAPE_SPKAC(NETSCAPE_SPKAC **a, const unsigned char **in, long len); int i2d_NETSCAPE_SPKAC(NETSCAPE_SPKAC *a, unsigned char **out); extern const ASN1_ITEM NETSCAPE_SPKAC_it;
NETSCAPE_CERT_SEQUENCE *NETSCAPE_CERT_SEQUENCE_new(void); void NETSCAPE_CERT_SEQUENCE_free(NETSCAPE_CERT_SEQUENCE *a); NETSCAPE_CERT_SEQUENCE *d2i_NETSCAPE_CERT_SEQUENCE(NETSCAPE_CERT_SEQUENCE **a, const unsigned char **in, long len); int i2d_NETSCAPE_CERT_SEQUENCE(NETSCAPE_CERT_SEQUENCE *a, unsigned char **out); extern const ASN1_ITEM NETSCAPE_CERT_SEQUENCE_it;


X509_INFO * X509_INFO_new(void) __attribute__((deprecated));
void X509_INFO_free(X509_INFO *a) __attribute__((deprecated));
char * X509_NAME_oneline(X509_NAME *a,char *buf,int size) __attribute__((deprecated));

int ASN1_verify(i2d_of_void *i2d, X509_ALGOR *algor1,
  ASN1_BIT_STRING *signature,char *data,EVP_PKEY *pkey) __attribute__((deprecated));

int ASN1_digest(i2d_of_void *i2d,const EVP_MD *type,char *data,
  unsigned char *md,unsigned int *len) __attribute__((deprecated));

int ASN1_sign(i2d_of_void *i2d, X509_ALGOR *algor1,
       X509_ALGOR *algor2, ASN1_BIT_STRING *signature,
       char *data,EVP_PKEY *pkey, const EVP_MD *type) __attribute__((deprecated));

int ASN1_item_digest(const ASN1_ITEM *it,const EVP_MD *type,void *data,
 unsigned char *md,unsigned int *len) __attribute__((deprecated));

int ASN1_item_verify(const ASN1_ITEM *it, X509_ALGOR *algor1,
 ASN1_BIT_STRING *signature,void *data,EVP_PKEY *pkey) __attribute__((deprecated));

int ASN1_item_sign(const ASN1_ITEM *it, X509_ALGOR *algor1, X509_ALGOR *algor2,
 ASN1_BIT_STRING *signature,
 void *data, EVP_PKEY *pkey, const EVP_MD *type) __attribute__((deprecated));


int X509_set_version(X509 *x,long version) __attribute__((deprecated));
int X509_set_serialNumber(X509 *x, ASN1_INTEGER *serial) __attribute__((deprecated));
ASN1_INTEGER * X509_get_serialNumber(X509 *x) __attribute__((deprecated));
int X509_set_issuer_name(X509 *x, X509_NAME *name) __attribute__((deprecated));
X509_NAME * X509_get_issuer_name(X509 *a) __attribute__((deprecated));
int X509_set_subject_name(X509 *x, X509_NAME *name) __attribute__((deprecated));
X509_NAME * X509_get_subject_name(X509 *a) __attribute__((deprecated));
int X509_set_notBefore(X509 *x, ASN1_TIME *tm) __attribute__((deprecated));
int X509_set_notAfter(X509 *x, ASN1_TIME *tm) __attribute__((deprecated));
int X509_set_pubkey(X509 *x, EVP_PKEY *pkey) __attribute__((deprecated));
EVP_PKEY * X509_get_pubkey(X509 *x) __attribute__((deprecated));
ASN1_BIT_STRING * X509_get0_pubkey_bitstr(const X509 *x) __attribute__((deprecated));
int X509_certificate_type(X509 *x,EVP_PKEY *pubkey ) __attribute__((deprecated));

int X509_REQ_set_version(X509_REQ *x,long version) __attribute__((deprecated));
int X509_REQ_set_subject_name(X509_REQ *req,X509_NAME *name) __attribute__((deprecated));
int X509_REQ_set_pubkey(X509_REQ *x, EVP_PKEY *pkey) __attribute__((deprecated));
EVP_PKEY * X509_REQ_get_pubkey(X509_REQ *req) __attribute__((deprecated));
int X509_REQ_extension_nid(int nid) __attribute__((deprecated));
int * X509_REQ_get_extension_nids(void) __attribute__((deprecated));
void X509_REQ_set_extension_nids(int *nids) __attribute__((deprecated));
STACK *X509_REQ_get_extensions(X509_REQ *req) __attribute__((deprecated));
int X509_REQ_add_extensions_nid(X509_REQ *req, STACK *exts,
    int nid) __attribute__((deprecated));
int X509_REQ_add_extensions(X509_REQ *req, STACK *exts) __attribute__((deprecated));
int X509_REQ_get_attr_count(const X509_REQ *req) __attribute__((deprecated));
int X509_REQ_get_attr_by_NID(const X509_REQ *req, int nid,
     int lastpos) __attribute__((deprecated));
int X509_REQ_get_attr_by_OBJ(const X509_REQ *req, ASN1_OBJECT *obj,
     int lastpos) __attribute__((deprecated));
X509_ATTRIBUTE *X509_REQ_get_attr(const X509_REQ *req, int loc) __attribute__((deprecated));
X509_ATTRIBUTE *X509_REQ_delete_attr(X509_REQ *req, int loc) __attribute__((deprecated));
int X509_REQ_add1_attr(X509_REQ *req, X509_ATTRIBUTE *attr) __attribute__((deprecated));
int X509_REQ_add1_attr_by_OBJ(X509_REQ *req,
   const ASN1_OBJECT *obj, int type,
   const unsigned char *bytes, int len) __attribute__((deprecated));
int X509_REQ_add1_attr_by_NID(X509_REQ *req,
   int nid, int type,
   const unsigned char *bytes, int len) __attribute__((deprecated));
int X509_REQ_add1_attr_by_txt(X509_REQ *req,
   const char *attrname, int type,
   const unsigned char *bytes, int len) __attribute__((deprecated));

int X509_CRL_set_version(X509_CRL *x, long version) __attribute__((deprecated));
int X509_CRL_set_issuer_name(X509_CRL *x, X509_NAME *name) __attribute__((deprecated));
int X509_CRL_set_lastUpdate(X509_CRL *x, ASN1_TIME *tm) __attribute__((deprecated));
int X509_CRL_set_nextUpdate(X509_CRL *x, ASN1_TIME *tm) __attribute__((deprecated));
int X509_CRL_sort(X509_CRL *crl) __attribute__((deprecated));

int X509_REVOKED_set_serialNumber(X509_REVOKED *x, ASN1_INTEGER *serial) __attribute__((deprecated));
int X509_REVOKED_set_revocationDate(X509_REVOKED *r, ASN1_TIME *tm) __attribute__((deprecated));

int X509_REQ_check_private_key(X509_REQ *x509,EVP_PKEY *pkey) __attribute__((deprecated));

int X509_check_private_key(X509 *x509,EVP_PKEY *pkey) __attribute__((deprecated));

int X509_issuer_and_serial_cmp(const X509 *a, const X509 *b) __attribute__((deprecated));
unsigned long X509_issuer_and_serial_hash(X509 *a) __attribute__((deprecated));

int X509_issuer_name_cmp(const X509 *a, const X509 *b) __attribute__((deprecated));
unsigned long X509_issuer_name_hash(X509 *a) __attribute__((deprecated));

int X509_subject_name_cmp(const X509 *a, const X509 *b) __attribute__((deprecated));
unsigned long X509_subject_name_hash(X509 *x) __attribute__((deprecated));

int X509_cmp(const X509 *a, const X509 *b) __attribute__((deprecated));
int X509_NAME_cmp(const X509_NAME *a, const X509_NAME *b) __attribute__((deprecated));
unsigned long X509_NAME_hash(X509_NAME *x) __attribute__((deprecated));

int X509_CRL_cmp(const X509_CRL *a, const X509_CRL *b) __attribute__((deprecated));

int X509_print_ex_fp(FILE *bp,X509 *x, unsigned long nmflag, unsigned long cflag) __attribute__((deprecated));
int X509_print_fp(FILE *bp,X509 *x) __attribute__((deprecated));
int X509_CRL_print_fp(FILE *bp,X509_CRL *x) __attribute__((deprecated));
int X509_REQ_print_fp(FILE *bp,X509_REQ *req) __attribute__((deprecated));
int X509_NAME_print_ex_fp(FILE *fp, X509_NAME *nm, int indent, unsigned long flags) __attribute__((deprecated));



int X509_NAME_print(BIO *bp, X509_NAME *name, int obase) __attribute__((deprecated));
int X509_NAME_print_ex(BIO *out, X509_NAME *nm, int indent, unsigned long flags) __attribute__((deprecated));
int X509_print_ex(BIO *bp,X509 *x, unsigned long nmflag, unsigned long cflag) __attribute__((deprecated));
int X509_print(BIO *bp,X509 *x) __attribute__((deprecated));
int X509_ocspid_print(BIO *bp,X509 *x) __attribute__((deprecated));
int X509_CERT_AUX_print(BIO *bp,X509_CERT_AUX *x, int indent) __attribute__((deprecated));
int X509_CRL_print(BIO *bp,X509_CRL *x) __attribute__((deprecated));
int X509_REQ_print_ex(BIO *bp, X509_REQ *x, unsigned long nmflag, unsigned long cflag) __attribute__((deprecated));
int X509_REQ_print(BIO *bp,X509_REQ *req) __attribute__((deprecated));


int X509_NAME_entry_count(X509_NAME *name) __attribute__((deprecated));
int X509_NAME_get_text_by_NID(X509_NAME *name, int nid,
   char *buf,int len) __attribute__((deprecated));
int X509_NAME_get_text_by_OBJ(X509_NAME *name, ASN1_OBJECT *obj,
   char *buf,int len) __attribute__((deprecated));



int X509_NAME_get_index_by_NID(X509_NAME *name,int nid,int lastpos) __attribute__((deprecated));
int X509_NAME_get_index_by_OBJ(X509_NAME *name,ASN1_OBJECT *obj,
   int lastpos) __attribute__((deprecated));
X509_NAME_ENTRY *X509_NAME_get_entry(X509_NAME *name, int loc) __attribute__((deprecated));
X509_NAME_ENTRY *X509_NAME_delete_entry(X509_NAME *name, int loc) __attribute__((deprecated));
int X509_NAME_add_entry(X509_NAME *name,X509_NAME_ENTRY *ne,
   int loc, int set) __attribute__((deprecated));
int X509_NAME_add_entry_by_OBJ(X509_NAME *name, ASN1_OBJECT *obj, int type,
   unsigned char *bytes, int len, int loc, int set) __attribute__((deprecated));
int X509_NAME_add_entry_by_NID(X509_NAME *name, int nid, int type,
   unsigned char *bytes, int len, int loc, int set) __attribute__((deprecated));
X509_NAME_ENTRY *X509_NAME_ENTRY_create_by_txt(X509_NAME_ENTRY **ne,
  const char *field, int type, const unsigned char *bytes, int len) __attribute__((deprecated));
X509_NAME_ENTRY *X509_NAME_ENTRY_create_by_NID(X509_NAME_ENTRY **ne, int nid,
   int type,unsigned char *bytes, int len) __attribute__((deprecated));
int X509_NAME_add_entry_by_txt(X509_NAME *name, const char *field, int type,
   const unsigned char *bytes, int len, int loc, int set) __attribute__((deprecated));
X509_NAME_ENTRY *X509_NAME_ENTRY_create_by_OBJ(X509_NAME_ENTRY **ne,
   ASN1_OBJECT *obj, int type,const unsigned char *bytes,
   int len) __attribute__((deprecated));
int X509_NAME_ENTRY_set_object(X509_NAME_ENTRY *ne,
   ASN1_OBJECT *obj) __attribute__((deprecated));
int X509_NAME_ENTRY_set_data(X509_NAME_ENTRY *ne, int type,
   const unsigned char *bytes, int len) __attribute__((deprecated));
ASN1_OBJECT * X509_NAME_ENTRY_get_object(X509_NAME_ENTRY *ne) __attribute__((deprecated));
ASN1_STRING * X509_NAME_ENTRY_get_data(X509_NAME_ENTRY *ne) __attribute__((deprecated));

int X509v3_get_ext_count(const STACK *x) __attribute__((deprecated));
int X509v3_get_ext_by_NID(const STACK *x,
          int nid, int lastpos) __attribute__((deprecated));
int X509v3_get_ext_by_OBJ(const STACK *x,
          ASN1_OBJECT *obj,int lastpos) __attribute__((deprecated));
int X509v3_get_ext_by_critical(const STACK *x,
        int crit, int lastpos) __attribute__((deprecated));
X509_EXTENSION *X509v3_get_ext(const STACK *x, int loc) __attribute__((deprecated));
X509_EXTENSION *X509v3_delete_ext(STACK *x, int loc) __attribute__((deprecated));
STACK *X509v3_add_ext(STACK **x,
      X509_EXTENSION *ex, int loc) __attribute__((deprecated));

int X509_get_ext_count(X509 *x) __attribute__((deprecated));
int X509_get_ext_by_NID(X509 *x, int nid, int lastpos) __attribute__((deprecated));
int X509_get_ext_by_OBJ(X509 *x,ASN1_OBJECT *obj,int lastpos) __attribute__((deprecated));
int X509_get_ext_by_critical(X509 *x, int crit, int lastpos) __attribute__((deprecated));
X509_EXTENSION *X509_get_ext(X509 *x, int loc) __attribute__((deprecated));
X509_EXTENSION *X509_delete_ext(X509 *x, int loc) __attribute__((deprecated));
int X509_add_ext(X509 *x, X509_EXTENSION *ex, int loc) __attribute__((deprecated));
void * X509_get_ext_d2i(X509 *x, int nid, int *crit, int *idx) __attribute__((deprecated));
int X509_add1_ext_i2d(X509 *x, int nid, void *value, int crit,
       unsigned long flags) __attribute__((deprecated));

int X509_CRL_get_ext_count(X509_CRL *x) __attribute__((deprecated));
int X509_CRL_get_ext_by_NID(X509_CRL *x, int nid, int lastpos) __attribute__((deprecated));
int X509_CRL_get_ext_by_OBJ(X509_CRL *x,ASN1_OBJECT *obj,int lastpos) __attribute__((deprecated));
int X509_CRL_get_ext_by_critical(X509_CRL *x, int crit, int lastpos) __attribute__((deprecated));
X509_EXTENSION *X509_CRL_get_ext(X509_CRL *x, int loc) __attribute__((deprecated));
X509_EXTENSION *X509_CRL_delete_ext(X509_CRL *x, int loc) __attribute__((deprecated));
int X509_CRL_add_ext(X509_CRL *x, X509_EXTENSION *ex, int loc) __attribute__((deprecated));
void * X509_CRL_get_ext_d2i(X509_CRL *x, int nid, int *crit, int *idx) __attribute__((deprecated));
int X509_CRL_add1_ext_i2d(X509_CRL *x, int nid, void *value, int crit,
       unsigned long flags) __attribute__((deprecated));

int X509_REVOKED_get_ext_count(X509_REVOKED *x) __attribute__((deprecated));
int X509_REVOKED_get_ext_by_NID(X509_REVOKED *x, int nid, int lastpos) __attribute__((deprecated));
int X509_REVOKED_get_ext_by_OBJ(X509_REVOKED *x,ASN1_OBJECT *obj,int lastpos) __attribute__((deprecated));
int X509_REVOKED_get_ext_by_critical(X509_REVOKED *x, int crit, int lastpos) __attribute__((deprecated));
X509_EXTENSION *X509_REVOKED_get_ext(X509_REVOKED *x, int loc) __attribute__((deprecated));
X509_EXTENSION *X509_REVOKED_delete_ext(X509_REVOKED *x, int loc) __attribute__((deprecated));
int X509_REVOKED_add_ext(X509_REVOKED *x, X509_EXTENSION *ex, int loc) __attribute__((deprecated));
void * X509_REVOKED_get_ext_d2i(X509_REVOKED *x, int nid, int *crit, int *idx) __attribute__((deprecated));
int X509_REVOKED_add1_ext_i2d(X509_REVOKED *x, int nid, void *value, int crit,
       unsigned long flags) __attribute__((deprecated));

X509_EXTENSION *X509_EXTENSION_create_by_NID(X509_EXTENSION **ex,
   int nid, int crit, ASN1_OCTET_STRING *data) __attribute__((deprecated));
X509_EXTENSION *X509_EXTENSION_create_by_OBJ(X509_EXTENSION **ex,
   ASN1_OBJECT *obj,int crit,ASN1_OCTET_STRING *data) __attribute__((deprecated));
int X509_EXTENSION_set_object(X509_EXTENSION *ex,ASN1_OBJECT *obj) __attribute__((deprecated));
int X509_EXTENSION_set_critical(X509_EXTENSION *ex, int crit) __attribute__((deprecated));
int X509_EXTENSION_set_data(X509_EXTENSION *ex,
   ASN1_OCTET_STRING *data) __attribute__((deprecated));
ASN1_OBJECT * X509_EXTENSION_get_object(X509_EXTENSION *ex) __attribute__((deprecated));
ASN1_OCTET_STRING *X509_EXTENSION_get_data(X509_EXTENSION *ne) __attribute__((deprecated));
int X509_EXTENSION_get_critical(X509_EXTENSION *ex) __attribute__((deprecated));

int X509at_get_attr_count(const STACK *x) __attribute__((deprecated));
int X509at_get_attr_by_NID(const STACK *x, int nid,
     int lastpos) __attribute__((deprecated));
int X509at_get_attr_by_OBJ(const STACK *sk, ASN1_OBJECT *obj,
     int lastpos) __attribute__((deprecated));
X509_ATTRIBUTE *X509at_get_attr(const STACK *x, int loc) __attribute__((deprecated));
X509_ATTRIBUTE *X509at_delete_attr(STACK *x, int loc) __attribute__((deprecated));
STACK *X509at_add1_attr(STACK **x,
      X509_ATTRIBUTE *attr) __attribute__((deprecated));
STACK *X509at_add1_attr_by_OBJ(STACK **x,
   const ASN1_OBJECT *obj, int type,
   const unsigned char *bytes, int len) __attribute__((deprecated));
STACK *X509at_add1_attr_by_NID(STACK **x,
   int nid, int type,
   const unsigned char *bytes, int len) __attribute__((deprecated));
STACK *X509at_add1_attr_by_txt(STACK **x,
   const char *attrname, int type,
   const unsigned char *bytes, int len) __attribute__((deprecated));
void *X509at_get0_data_by_OBJ(STACK *x,
    ASN1_OBJECT *obj, int lastpos, int type) __attribute__((deprecated));
X509_ATTRIBUTE *X509_ATTRIBUTE_create_by_NID(X509_ATTRIBUTE **attr, int nid,
      int atrtype, const void *data, int len) __attribute__((deprecated));
X509_ATTRIBUTE *X509_ATTRIBUTE_create_by_OBJ(X509_ATTRIBUTE **attr,
      const ASN1_OBJECT *obj, int atrtype, const void *data, int len) __attribute__((deprecated));
X509_ATTRIBUTE *X509_ATTRIBUTE_create_by_txt(X509_ATTRIBUTE **attr,
  const char *atrname, int type, const unsigned char *bytes, int len) __attribute__((deprecated));
int X509_ATTRIBUTE_set1_object(X509_ATTRIBUTE *attr, const ASN1_OBJECT *obj) __attribute__((deprecated));
int X509_ATTRIBUTE_set1_data(X509_ATTRIBUTE *attr, int attrtype, const void *data, int len) __attribute__((deprecated));
void *X509_ATTRIBUTE_get0_data(X509_ATTRIBUTE *attr, int idx,
     int atrtype, void *data) __attribute__((deprecated));
int X509_ATTRIBUTE_count(X509_ATTRIBUTE *attr) __attribute__((deprecated));
ASN1_OBJECT *X509_ATTRIBUTE_get0_object(X509_ATTRIBUTE *attr) __attribute__((deprecated));
ASN1_TYPE *X509_ATTRIBUTE_get0_type(X509_ATTRIBUTE *attr, int idx) __attribute__((deprecated));

int EVP_PKEY_get_attr_count(const EVP_PKEY *key) __attribute__((deprecated));
int EVP_PKEY_get_attr_by_NID(const EVP_PKEY *key, int nid,
     int lastpos) __attribute__((deprecated));
int EVP_PKEY_get_attr_by_OBJ(const EVP_PKEY *key, ASN1_OBJECT *obj,
     int lastpos) __attribute__((deprecated));
X509_ATTRIBUTE *EVP_PKEY_get_attr(const EVP_PKEY *key, int loc) __attribute__((deprecated));
X509_ATTRIBUTE *EVP_PKEY_delete_attr(EVP_PKEY *key, int loc) __attribute__((deprecated));
int EVP_PKEY_add1_attr(EVP_PKEY *key, X509_ATTRIBUTE *attr) __attribute__((deprecated));
int EVP_PKEY_add1_attr_by_OBJ(EVP_PKEY *key,
   const ASN1_OBJECT *obj, int type,
   const unsigned char *bytes, int len) __attribute__((deprecated));
int EVP_PKEY_add1_attr_by_NID(EVP_PKEY *key,
   int nid, int type,
   const unsigned char *bytes, int len) __attribute__((deprecated));
int EVP_PKEY_add1_attr_by_txt(EVP_PKEY *key,
   const char *attrname, int type,
   const unsigned char *bytes, int len) __attribute__((deprecated));

int X509_verify_cert(X509_STORE_CTX *ctx) __attribute__((deprecated));


X509 *X509_find_by_issuer_and_serial(STACK *sk,X509_NAME *name,
         ASN1_INTEGER *serial) __attribute__((deprecated));
X509 *X509_find_by_subject(STACK *sk,X509_NAME *name) __attribute__((deprecated));

PBEPARAM *PBEPARAM_new(void); void PBEPARAM_free(PBEPARAM *a); PBEPARAM *d2i_PBEPARAM(PBEPARAM **a, const unsigned char **in, long len); int i2d_PBEPARAM(PBEPARAM *a, unsigned char **out); extern const ASN1_ITEM PBEPARAM_it;
PBE2PARAM *PBE2PARAM_new(void); void PBE2PARAM_free(PBE2PARAM *a); PBE2PARAM *d2i_PBE2PARAM(PBE2PARAM **a, const unsigned char **in, long len); int i2d_PBE2PARAM(PBE2PARAM *a, unsigned char **out); extern const ASN1_ITEM PBE2PARAM_it;
PBKDF2PARAM *PBKDF2PARAM_new(void); void PBKDF2PARAM_free(PBKDF2PARAM *a); PBKDF2PARAM *d2i_PBKDF2PARAM(PBKDF2PARAM **a, const unsigned char **in, long len); int i2d_PBKDF2PARAM(PBKDF2PARAM *a, unsigned char **out); extern const ASN1_ITEM PBKDF2PARAM_it;

X509_ALGOR *PKCS5_pbe_set(int alg, int iter, unsigned char *salt, int saltlen) __attribute__((deprecated));
X509_ALGOR *PKCS5_pbe2_set(const EVP_CIPHER *cipher, int iter,
      unsigned char *salt, int saltlen) __attribute__((deprecated));



PKCS8_PRIV_KEY_INFO *PKCS8_PRIV_KEY_INFO_new(void); void PKCS8_PRIV_KEY_INFO_free(PKCS8_PRIV_KEY_INFO *a); PKCS8_PRIV_KEY_INFO *d2i_PKCS8_PRIV_KEY_INFO(PKCS8_PRIV_KEY_INFO **a, const unsigned char **in, long len); int i2d_PKCS8_PRIV_KEY_INFO(PKCS8_PRIV_KEY_INFO *a, unsigned char **out); extern const ASN1_ITEM PKCS8_PRIV_KEY_INFO_it;

EVP_PKEY *EVP_PKCS82PKEY(PKCS8_PRIV_KEY_INFO *p8) __attribute__((deprecated));
PKCS8_PRIV_KEY_INFO *EVP_PKEY2PKCS8(EVP_PKEY *pkey) __attribute__((deprecated));
PKCS8_PRIV_KEY_INFO *EVP_PKEY2PKCS8_broken(EVP_PKEY *pkey, int broken) __attribute__((deprecated));
PKCS8_PRIV_KEY_INFO *PKCS8_set_broken(PKCS8_PRIV_KEY_INFO *p8, int broken) __attribute__((deprecated));

int X509_check_trust(X509 *x, int id, int flags) __attribute__((deprecated));
int X509_TRUST_get_count(void) __attribute__((deprecated));
X509_TRUST * X509_TRUST_get0(int idx) __attribute__((deprecated));
int X509_TRUST_get_by_id(int id) __attribute__((deprecated));
int X509_TRUST_add(int id, int flags, int (*ck)(X509_TRUST *, X509 *, int),
     char *name, int arg1, void *arg2) __attribute__((deprecated));
void X509_TRUST_cleanup(void) __attribute__((deprecated));
int X509_TRUST_get_flags(X509_TRUST *xp) __attribute__((deprecated));
char *X509_TRUST_get0_name(X509_TRUST *xp) __attribute__((deprecated));
int X509_TRUST_get_trust(X509_TRUST *xp) __attribute__((deprecated));





void ERR_load_X509_strings(void) __attribute__((deprecated));
# 104 "_ssl.c" 2
# 1 "/usr/include/openssl/x509v3.h" 1 3 4
# 64 "/usr/include/openssl/x509v3.h" 3 4
# 1 "/usr/include/openssl/x509.h" 1 3 4
# 65 "/usr/include/openssl/x509v3.h" 2 3 4
# 1 "/usr/include/openssl/conf.h" 1 3 4
# 68 "/usr/include/openssl/conf.h" 3 4
# 1 "/usr/include/openssl/e_os2.h" 1 3 4
# 56 "/usr/include/openssl/e_os2.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 57 "/usr/include/openssl/e_os2.h" 2 3 4
# 69 "/usr/include/openssl/conf.h" 2 3 4







typedef struct
 {
 char *section;
 char *name;
 char *value;
 } CONF_VALUE;





struct conf_st;
struct conf_method_st;
typedef struct conf_method_st CONF_METHOD;

struct conf_method_st
 {
 const char *name;
 CONF *(*create)(CONF_METHOD *meth);
 int (*init)(CONF *conf);
 int (*destroy)(CONF *conf);
 int (*destroy_data)(CONF *conf);
 int (*load_bio)(CONF *conf, BIO *bp, long *eline);
 int (*dump)(const CONF *conf, BIO *bp);
 int (*is_number)(const CONF *conf, char c);
 int (*to_int)(const CONF *conf, char c);
 int (*load)(CONF *conf, const char *name, long *eline);
 };



typedef struct conf_imodule_st CONF_IMODULE;
typedef struct conf_module_st CONF_MODULE;


typedef int conf_init_func(CONF_IMODULE *md, const CONF *cnf);
typedef void conf_finish_func(CONF_IMODULE *md);
# 121 "/usr/include/openssl/conf.h" 3 4
int CONF_set_default_method(CONF_METHOD *meth) __attribute__((deprecated));
void CONF_set_nconf(CONF *conf,LHASH *hash) __attribute__((deprecated));
LHASH *CONF_load(LHASH *conf,const char *file,long *eline) __attribute__((deprecated));

LHASH *CONF_load_fp(LHASH *conf, FILE *fp,long *eline) __attribute__((deprecated));

LHASH *CONF_load_bio(LHASH *conf, BIO *bp,long *eline) __attribute__((deprecated));
STACK *CONF_get_section(LHASH *conf,const char *section) __attribute__((deprecated));
char *CONF_get_string(LHASH *conf,const char *group,const char *name) __attribute__((deprecated));
long CONF_get_number(LHASH *conf,const char *group,const char *name) __attribute__((deprecated));
void CONF_free(LHASH *conf) __attribute__((deprecated));
int CONF_dump_fp(LHASH *conf, FILE *out) __attribute__((deprecated));
int CONF_dump_bio(LHASH *conf, BIO *out) __attribute__((deprecated));

void OPENSSL_config(const char *config_name) __attribute__((deprecated));
void OPENSSL_no_config(void) __attribute__((deprecated));




struct conf_st
 {
 CONF_METHOD *meth;
 void *meth_data;
 LHASH *data;
 };

CONF *NCONF_new(CONF_METHOD *meth) __attribute__((deprecated));
CONF_METHOD *NCONF_default(void) __attribute__((deprecated));
CONF_METHOD *NCONF_WIN32(void) __attribute__((deprecated));



void NCONF_free(CONF *conf) __attribute__((deprecated));
void NCONF_free_data(CONF *conf) __attribute__((deprecated));

int NCONF_load(CONF *conf,const char *file,long *eline) __attribute__((deprecated));

int NCONF_load_fp(CONF *conf, FILE *fp,long *eline) __attribute__((deprecated));

int NCONF_load_bio(CONF *conf, BIO *bp,long *eline) __attribute__((deprecated));
STACK *NCONF_get_section(const CONF *conf,const char *section) __attribute__((deprecated));
char *NCONF_get_string(const CONF *conf,const char *group,const char *name) __attribute__((deprecated));
int NCONF_get_number_e(const CONF *conf,const char *group,const char *name,
         long *result) __attribute__((deprecated));
int NCONF_dump_fp(const CONF *conf, FILE *out) __attribute__((deprecated));
int NCONF_dump_bio(const CONF *conf, BIO *out) __attribute__((deprecated));
# 178 "/usr/include/openssl/conf.h" 3 4
int CONF_modules_load(const CONF *cnf, const char *appname,
        unsigned long flags) __attribute__((deprecated));
int CONF_modules_load_file(const char *filename, const char *appname,
      unsigned long flags) __attribute__((deprecated));
void CONF_modules_unload(int all) __attribute__((deprecated));
void CONF_modules_finish(void) __attribute__((deprecated));
void CONF_modules_free(void) __attribute__((deprecated));
int CONF_module_add(const char *name, conf_init_func *ifunc,
      conf_finish_func *ffunc) __attribute__((deprecated));

const char *CONF_imodule_get_name(const CONF_IMODULE *md) __attribute__((deprecated));
const char *CONF_imodule_get_value(const CONF_IMODULE *md) __attribute__((deprecated));
void *CONF_imodule_get_usr_data(const CONF_IMODULE *md) __attribute__((deprecated));
void CONF_imodule_set_usr_data(CONF_IMODULE *md, void *usr_data) __attribute__((deprecated));
CONF_MODULE *CONF_imodule_get_module(const CONF_IMODULE *md) __attribute__((deprecated));
unsigned long CONF_imodule_get_flags(const CONF_IMODULE *md) __attribute__((deprecated));
void CONF_imodule_set_flags(CONF_IMODULE *md, unsigned long flags) __attribute__((deprecated));
void *CONF_module_get_usr_data(CONF_MODULE *pmod) __attribute__((deprecated));
void CONF_module_set_usr_data(CONF_MODULE *pmod, void *usr_data) __attribute__((deprecated));

char *CONF_get1_default_config_file(void) __attribute__((deprecated));

int CONF_parse_list(const char *list, int sep, int nospc,
 int (*list_cb)(const char *elem, int len, void *usr), void *arg) __attribute__((deprecated));

void OPENSSL_load_builtin_modules(void) __attribute__((deprecated));





void ERR_load_CONF_strings(void) __attribute__((deprecated));
# 66 "/usr/include/openssl/x509v3.h" 2 3 4






struct v3_ext_method;
struct v3_ext_ctx;



typedef void * (*X509V3_EXT_NEW)(void);
typedef void (*X509V3_EXT_FREE)(void *);
typedef void * (*X509V3_EXT_D2I)(void *, const unsigned char ** , long);
typedef int (*X509V3_EXT_I2D)(void *, unsigned char **);
typedef STACK * (*X509V3_EXT_I2V)(struct v3_ext_method *method, void *ext, STACK *extlist);
typedef void * (*X509V3_EXT_V2I)(struct v3_ext_method *method, struct v3_ext_ctx *ctx, STACK *values);
typedef char * (*X509V3_EXT_I2S)(struct v3_ext_method *method, void *ext);
typedef void * (*X509V3_EXT_S2I)(struct v3_ext_method *method, struct v3_ext_ctx *ctx, const char *str);
typedef int (*X509V3_EXT_I2R)(struct v3_ext_method *method, void *ext, BIO *out, int indent);
typedef void * (*X509V3_EXT_R2I)(struct v3_ext_method *method, struct v3_ext_ctx *ctx, const char *str);



struct v3_ext_method {
int ext_nid;
int ext_flags;

ASN1_ITEM_EXP *it;

X509V3_EXT_NEW ext_new;
X509V3_EXT_FREE ext_free;
X509V3_EXT_D2I d2i;
X509V3_EXT_I2D i2d;


X509V3_EXT_I2S i2s;
X509V3_EXT_S2I s2i;


X509V3_EXT_I2V i2v;
X509V3_EXT_V2I v2i;


X509V3_EXT_I2R i2r;
X509V3_EXT_R2I r2i;

void *usr_data;
};

typedef struct X509V3_CONF_METHOD_st {
char * (*get_string)(void *db, char *section, char *value);
STACK * (*get_section)(void *db, char *section);
void (*free_string)(void *db, char * string);
void (*free_section)(void *db, STACK *section);
} X509V3_CONF_METHOD;


struct v3_ext_ctx {

int flags;
X509 *issuer_cert;
X509 *subject_cert;
X509_REQ *subject_req;
X509_CRL *crl;
X509V3_CONF_METHOD *db_meth;
void *db;

};

typedef struct v3_ext_method X509V3_EXT_METHOD;








typedef BIT_STRING_BITNAME ENUMERATED_NAMES;

typedef struct BASIC_CONSTRAINTS_st {
int ca;
ASN1_INTEGER *pathlen;
} BASIC_CONSTRAINTS;


typedef struct PKEY_USAGE_PERIOD_st {
ASN1_GENERALIZEDTIME *notBefore;
ASN1_GENERALIZEDTIME *notAfter;
} PKEY_USAGE_PERIOD;

typedef struct otherName_st {
ASN1_OBJECT *type_id;
ASN1_TYPE *value;
} OTHERNAME;

typedef struct EDIPartyName_st {
 ASN1_STRING *nameAssigner;
 ASN1_STRING *partyName;
} EDIPARTYNAME;

typedef struct GENERAL_NAME_st {
# 180 "/usr/include/openssl/x509v3.h" 3 4
int type;
union {
 char *ptr;
 OTHERNAME *otherName;
 ASN1_IA5STRING *rfc822Name;
 ASN1_IA5STRING *dNSName;
 ASN1_TYPE *x400Address;
 X509_NAME *directoryName;
 EDIPARTYNAME *ediPartyName;
 ASN1_IA5STRING *uniformResourceIdentifier;
 ASN1_OCTET_STRING *iPAddress;
 ASN1_OBJECT *registeredID;


 ASN1_OCTET_STRING *ip;
 X509_NAME *dirn;
 ASN1_IA5STRING *ia5;
 ASN1_OBJECT *rid;
 ASN1_TYPE *other;
} d;
} GENERAL_NAME;

typedef STACK GENERAL_NAMES;

typedef struct ACCESS_DESCRIPTION_st {
 ASN1_OBJECT *method;
 GENERAL_NAME *location;
} ACCESS_DESCRIPTION;

typedef STACK AUTHORITY_INFO_ACCESS;

typedef STACK EXTENDED_KEY_USAGE;







typedef struct DIST_POINT_NAME_st {
int type;
union {
 GENERAL_NAMES *fullname;
 STACK *relativename;
} name;
} DIST_POINT_NAME;

typedef struct DIST_POINT_st {
DIST_POINT_NAME *distpoint;
ASN1_BIT_STRING *reasons;
GENERAL_NAMES *CRLissuer;
} DIST_POINT;

typedef STACK CRL_DIST_POINTS;




typedef struct AUTHORITY_KEYID_st {
ASN1_OCTET_STRING *keyid;
GENERAL_NAMES *issuer;
ASN1_INTEGER *serial;
} AUTHORITY_KEYID;



typedef struct SXNET_ID_st {
 ASN1_INTEGER *zone;
 ASN1_OCTET_STRING *user;
} SXNETID;




typedef struct SXNET_st {
 ASN1_INTEGER *version;
 STACK *ids;
} SXNET;

typedef struct NOTICEREF_st {
 ASN1_STRING *organization;
 STACK *noticenos;
} NOTICEREF;

typedef struct USERNOTICE_st {
 NOTICEREF *noticeref;
 ASN1_STRING *exptext;
} USERNOTICE;

typedef struct POLICYQUALINFO_st {
 ASN1_OBJECT *pqualid;
 union {
  ASN1_IA5STRING *cpsuri;
  USERNOTICE *usernotice;
  ASN1_TYPE *other;
 } d;
} POLICYQUALINFO;




typedef struct POLICYINFO_st {
 ASN1_OBJECT *policyid;
 STACK *qualifiers;
} POLICYINFO;

typedef STACK CERTIFICATEPOLICIES;




typedef struct POLICY_MAPPING_st {
 ASN1_OBJECT *issuerDomainPolicy;
 ASN1_OBJECT *subjectDomainPolicy;
} POLICY_MAPPING;



typedef STACK POLICY_MAPPINGS;

typedef struct GENERAL_SUBTREE_st {
 GENERAL_NAME *base;
 ASN1_INTEGER *minimum;
 ASN1_INTEGER *maximum;
} GENERAL_SUBTREE;



typedef struct NAME_CONSTRAINTS_st {
 STACK *permittedSubtrees;
 STACK *excludedSubtrees;
} NAME_CONSTRAINTS;

typedef struct POLICY_CONSTRAINTS_st {
 ASN1_INTEGER *requireExplicitPolicy;
 ASN1_INTEGER *inhibitPolicyMapping;
} POLICY_CONSTRAINTS;


typedef struct PROXY_POLICY_st
 {
 ASN1_OBJECT *policyLanguage;
 ASN1_OCTET_STRING *policy;
 } PROXY_POLICY;

typedef struct PROXY_CERT_INFO_EXTENSION_st
 {
 ASN1_INTEGER *pcPathLengthConstraint;
 PROXY_POLICY *proxyPolicy;
 } PROXY_CERT_INFO_EXTENSION;

PROXY_POLICY *PROXY_POLICY_new(void); void PROXY_POLICY_free(PROXY_POLICY *a); PROXY_POLICY *d2i_PROXY_POLICY(PROXY_POLICY **a, const unsigned char **in, long len); int i2d_PROXY_POLICY(PROXY_POLICY *a, unsigned char **out); extern const ASN1_ITEM PROXY_POLICY_it;
PROXY_CERT_INFO_EXTENSION *PROXY_CERT_INFO_EXTENSION_new(void); void PROXY_CERT_INFO_EXTENSION_free(PROXY_CERT_INFO_EXTENSION *a); PROXY_CERT_INFO_EXTENSION *d2i_PROXY_CERT_INFO_EXTENSION(PROXY_CERT_INFO_EXTENSION **a, const unsigned char **in, long len); int i2d_PROXY_CERT_INFO_EXTENSION(PROXY_CERT_INFO_EXTENSION *a, unsigned char **out); extern const ASN1_ITEM PROXY_CERT_INFO_EXTENSION_it;
# 410 "/usr/include/openssl/x509v3.h" 3 4
typedef struct x509_purpose_st {
 int purpose;
 int trust;
 int flags;
 int (*check_purpose)(const struct x509_purpose_st *,
    const X509 *, int);
 char *name;
 char *sname;
 void *usr_data;
} X509_PURPOSE;
# 456 "/usr/include/openssl/x509v3.h" 3 4


BASIC_CONSTRAINTS *BASIC_CONSTRAINTS_new(void); void BASIC_CONSTRAINTS_free(BASIC_CONSTRAINTS *a); BASIC_CONSTRAINTS *d2i_BASIC_CONSTRAINTS(BASIC_CONSTRAINTS **a, const unsigned char **in, long len); int i2d_BASIC_CONSTRAINTS(BASIC_CONSTRAINTS *a, unsigned char **out); extern const ASN1_ITEM BASIC_CONSTRAINTS_it;

SXNET *SXNET_new(void); void SXNET_free(SXNET *a); SXNET *d2i_SXNET(SXNET **a, const unsigned char **in, long len); int i2d_SXNET(SXNET *a, unsigned char **out); extern const ASN1_ITEM SXNET_it;
SXNETID *SXNETID_new(void); void SXNETID_free(SXNETID *a); SXNETID *d2i_SXNETID(SXNETID **a, const unsigned char **in, long len); int i2d_SXNETID(SXNETID *a, unsigned char **out); extern const ASN1_ITEM SXNETID_it;

int SXNET_add_id_asc(SXNET **psx, char *zone, char *user, int userlen) __attribute__((deprecated));
int SXNET_add_id_ulong(SXNET **psx, unsigned long lzone, char *user, int userlen) __attribute__((deprecated));
int SXNET_add_id_INTEGER(SXNET **psx, ASN1_INTEGER *izone, char *user, int userlen) __attribute__((deprecated));

ASN1_OCTET_STRING *SXNET_get_id_asc(SXNET *sx, char *zone) __attribute__((deprecated));
ASN1_OCTET_STRING *SXNET_get_id_ulong(SXNET *sx, unsigned long lzone) __attribute__((deprecated));
ASN1_OCTET_STRING *SXNET_get_id_INTEGER(SXNET *sx, ASN1_INTEGER *zone) __attribute__((deprecated));

AUTHORITY_KEYID *AUTHORITY_KEYID_new(void); void AUTHORITY_KEYID_free(AUTHORITY_KEYID *a); AUTHORITY_KEYID *d2i_AUTHORITY_KEYID(AUTHORITY_KEYID **a, const unsigned char **in, long len); int i2d_AUTHORITY_KEYID(AUTHORITY_KEYID *a, unsigned char **out); extern const ASN1_ITEM AUTHORITY_KEYID_it;

PKEY_USAGE_PERIOD *PKEY_USAGE_PERIOD_new(void); void PKEY_USAGE_PERIOD_free(PKEY_USAGE_PERIOD *a); PKEY_USAGE_PERIOD *d2i_PKEY_USAGE_PERIOD(PKEY_USAGE_PERIOD **a, const unsigned char **in, long len); int i2d_PKEY_USAGE_PERIOD(PKEY_USAGE_PERIOD *a, unsigned char **out); extern const ASN1_ITEM PKEY_USAGE_PERIOD_it;

GENERAL_NAME *GENERAL_NAME_new(void); void GENERAL_NAME_free(GENERAL_NAME *a); GENERAL_NAME *d2i_GENERAL_NAME(GENERAL_NAME **a, const unsigned char **in, long len); int i2d_GENERAL_NAME(GENERAL_NAME *a, unsigned char **out); extern const ASN1_ITEM GENERAL_NAME_it;


ASN1_BIT_STRING *v2i_ASN1_BIT_STRING(X509V3_EXT_METHOD *method,
    X509V3_CTX *ctx, STACK *nval) __attribute__((deprecated));
STACK *i2v_ASN1_BIT_STRING(X509V3_EXT_METHOD *method,
    ASN1_BIT_STRING *bits,
    STACK *extlist) __attribute__((deprecated));

STACK *i2v_GENERAL_NAME(X509V3_EXT_METHOD *method, GENERAL_NAME *gen, STACK *ret) __attribute__((deprecated));
int GENERAL_NAME_print(BIO *out, GENERAL_NAME *gen) __attribute__((deprecated));

GENERAL_NAMES *GENERAL_NAMES_new(void); void GENERAL_NAMES_free(GENERAL_NAMES *a); GENERAL_NAMES *d2i_GENERAL_NAMES(GENERAL_NAMES **a, const unsigned char **in, long len); int i2d_GENERAL_NAMES(GENERAL_NAMES *a, unsigned char **out); extern const ASN1_ITEM GENERAL_NAMES_it;

STACK *i2v_GENERAL_NAMES(X509V3_EXT_METHOD *method,
  GENERAL_NAMES *gen, STACK *extlist) __attribute__((deprecated));
GENERAL_NAMES *v2i_GENERAL_NAMES(X509V3_EXT_METHOD *method,
    X509V3_CTX *ctx, STACK *nval) __attribute__((deprecated));

OTHERNAME *OTHERNAME_new(void); void OTHERNAME_free(OTHERNAME *a); OTHERNAME *d2i_OTHERNAME(OTHERNAME **a, const unsigned char **in, long len); int i2d_OTHERNAME(OTHERNAME *a, unsigned char **out); extern const ASN1_ITEM OTHERNAME_it;
EDIPARTYNAME *EDIPARTYNAME_new(void); void EDIPARTYNAME_free(EDIPARTYNAME *a); EDIPARTYNAME *d2i_EDIPARTYNAME(EDIPARTYNAME **a, const unsigned char **in, long len); int i2d_EDIPARTYNAME(EDIPARTYNAME *a, unsigned char **out); extern const ASN1_ITEM EDIPARTYNAME_it;

char *i2s_ASN1_OCTET_STRING(X509V3_EXT_METHOD *method, ASN1_OCTET_STRING *ia5) __attribute__((deprecated));
ASN1_OCTET_STRING *s2i_ASN1_OCTET_STRING(X509V3_EXT_METHOD *method, X509V3_CTX *ctx, char *str) __attribute__((deprecated));

EXTENDED_KEY_USAGE *EXTENDED_KEY_USAGE_new(void); void EXTENDED_KEY_USAGE_free(EXTENDED_KEY_USAGE *a); EXTENDED_KEY_USAGE *d2i_EXTENDED_KEY_USAGE(EXTENDED_KEY_USAGE **a, const unsigned char **in, long len); int i2d_EXTENDED_KEY_USAGE(EXTENDED_KEY_USAGE *a, unsigned char **out); extern const ASN1_ITEM EXTENDED_KEY_USAGE_it;
int i2a_ACCESS_DESCRIPTION(BIO *bp, ACCESS_DESCRIPTION* a) __attribute__((deprecated));

CERTIFICATEPOLICIES *CERTIFICATEPOLICIES_new(void); void CERTIFICATEPOLICIES_free(CERTIFICATEPOLICIES *a); CERTIFICATEPOLICIES *d2i_CERTIFICATEPOLICIES(CERTIFICATEPOLICIES **a, const unsigned char **in, long len); int i2d_CERTIFICATEPOLICIES(CERTIFICATEPOLICIES *a, unsigned char **out); extern const ASN1_ITEM CERTIFICATEPOLICIES_it;
POLICYINFO *POLICYINFO_new(void); void POLICYINFO_free(POLICYINFO *a); POLICYINFO *d2i_POLICYINFO(POLICYINFO **a, const unsigned char **in, long len); int i2d_POLICYINFO(POLICYINFO *a, unsigned char **out); extern const ASN1_ITEM POLICYINFO_it;
POLICYQUALINFO *POLICYQUALINFO_new(void); void POLICYQUALINFO_free(POLICYQUALINFO *a); POLICYQUALINFO *d2i_POLICYQUALINFO(POLICYQUALINFO **a, const unsigned char **in, long len); int i2d_POLICYQUALINFO(POLICYQUALINFO *a, unsigned char **out); extern const ASN1_ITEM POLICYQUALINFO_it;
USERNOTICE *USERNOTICE_new(void); void USERNOTICE_free(USERNOTICE *a); USERNOTICE *d2i_USERNOTICE(USERNOTICE **a, const unsigned char **in, long len); int i2d_USERNOTICE(USERNOTICE *a, unsigned char **out); extern const ASN1_ITEM USERNOTICE_it;
NOTICEREF *NOTICEREF_new(void); void NOTICEREF_free(NOTICEREF *a); NOTICEREF *d2i_NOTICEREF(NOTICEREF **a, const unsigned char **in, long len); int i2d_NOTICEREF(NOTICEREF *a, unsigned char **out); extern const ASN1_ITEM NOTICEREF_it;

CRL_DIST_POINTS *CRL_DIST_POINTS_new(void); void CRL_DIST_POINTS_free(CRL_DIST_POINTS *a); CRL_DIST_POINTS *d2i_CRL_DIST_POINTS(CRL_DIST_POINTS **a, const unsigned char **in, long len); int i2d_CRL_DIST_POINTS(CRL_DIST_POINTS *a, unsigned char **out); extern const ASN1_ITEM CRL_DIST_POINTS_it;
DIST_POINT *DIST_POINT_new(void); void DIST_POINT_free(DIST_POINT *a); DIST_POINT *d2i_DIST_POINT(DIST_POINT **a, const unsigned char **in, long len); int i2d_DIST_POINT(DIST_POINT *a, unsigned char **out); extern const ASN1_ITEM DIST_POINT_it;
DIST_POINT_NAME *DIST_POINT_NAME_new(void); void DIST_POINT_NAME_free(DIST_POINT_NAME *a); DIST_POINT_NAME *d2i_DIST_POINT_NAME(DIST_POINT_NAME **a, const unsigned char **in, long len); int i2d_DIST_POINT_NAME(DIST_POINT_NAME *a, unsigned char **out); extern const ASN1_ITEM DIST_POINT_NAME_it;

ACCESS_DESCRIPTION *ACCESS_DESCRIPTION_new(void); void ACCESS_DESCRIPTION_free(ACCESS_DESCRIPTION *a); ACCESS_DESCRIPTION *d2i_ACCESS_DESCRIPTION(ACCESS_DESCRIPTION **a, const unsigned char **in, long len); int i2d_ACCESS_DESCRIPTION(ACCESS_DESCRIPTION *a, unsigned char **out); extern const ASN1_ITEM ACCESS_DESCRIPTION_it;
AUTHORITY_INFO_ACCESS *AUTHORITY_INFO_ACCESS_new(void); void AUTHORITY_INFO_ACCESS_free(AUTHORITY_INFO_ACCESS *a); AUTHORITY_INFO_ACCESS *d2i_AUTHORITY_INFO_ACCESS(AUTHORITY_INFO_ACCESS **a, const unsigned char **in, long len); int i2d_AUTHORITY_INFO_ACCESS(AUTHORITY_INFO_ACCESS *a, unsigned char **out); extern const ASN1_ITEM AUTHORITY_INFO_ACCESS_it;

extern const ASN1_ITEM POLICY_MAPPING_it;
POLICY_MAPPING *POLICY_MAPPING_new(void); void POLICY_MAPPING_free(POLICY_MAPPING *a);
extern const ASN1_ITEM POLICY_MAPPINGS_it;

extern const ASN1_ITEM GENERAL_SUBTREE_it;
GENERAL_SUBTREE *GENERAL_SUBTREE_new(void); void GENERAL_SUBTREE_free(GENERAL_SUBTREE *a);

extern const ASN1_ITEM NAME_CONSTRAINTS_it;
NAME_CONSTRAINTS *NAME_CONSTRAINTS_new(void); void NAME_CONSTRAINTS_free(NAME_CONSTRAINTS *a);

POLICY_CONSTRAINTS *POLICY_CONSTRAINTS_new(void); void POLICY_CONSTRAINTS_free(POLICY_CONSTRAINTS *a);
extern const ASN1_ITEM POLICY_CONSTRAINTS_it;


GENERAL_NAME *v2i_GENERAL_NAME(X509V3_EXT_METHOD *method, X509V3_CTX *ctx,
       CONF_VALUE *cnf) __attribute__((deprecated));
GENERAL_NAME *v2i_GENERAL_NAME_ex(GENERAL_NAME *out, X509V3_EXT_METHOD *method,
    X509V3_CTX *ctx, CONF_VALUE *cnf, int is_nc) __attribute__((deprecated));
void X509V3_conf_free(CONF_VALUE *val) __attribute__((deprecated));

X509_EXTENSION *X509V3_EXT_nconf_nid(CONF *conf, X509V3_CTX *ctx, int ext_nid, char *value) __attribute__((deprecated));
X509_EXTENSION *X509V3_EXT_nconf(CONF *conf, X509V3_CTX *ctx, char *name, char *value) __attribute__((deprecated));
int X509V3_EXT_add_nconf_sk(CONF *conf, X509V3_CTX *ctx, char *section, STACK **sk) __attribute__((deprecated));
int X509V3_EXT_add_nconf(CONF *conf, X509V3_CTX *ctx, char *section, X509 *cert) __attribute__((deprecated));
int X509V3_EXT_REQ_add_nconf(CONF *conf, X509V3_CTX *ctx, char *section, X509_REQ *req) __attribute__((deprecated));
int X509V3_EXT_CRL_add_nconf(CONF *conf, X509V3_CTX *ctx, char *section, X509_CRL *crl) __attribute__((deprecated));

X509_EXTENSION *X509V3_EXT_conf_nid(LHASH *conf, X509V3_CTX *ctx, int ext_nid, char *value) __attribute__((deprecated));
X509_EXTENSION *X509V3_EXT_conf(LHASH *conf, X509V3_CTX *ctx, char *name, char *value) __attribute__((deprecated));
int X509V3_EXT_add_conf(LHASH *conf, X509V3_CTX *ctx, char *section, X509 *cert) __attribute__((deprecated));
int X509V3_EXT_REQ_add_conf(LHASH *conf, X509V3_CTX *ctx, char *section, X509_REQ *req) __attribute__((deprecated));
int X509V3_EXT_CRL_add_conf(LHASH *conf, X509V3_CTX *ctx, char *section, X509_CRL *crl) __attribute__((deprecated));

int X509V3_add_value_bool_nf(char *name, int asn1_bool,
      STACK **extlist) __attribute__((deprecated));
int X509V3_get_value_bool(CONF_VALUE *value, int *asn1_bool) __attribute__((deprecated));
int X509V3_get_value_int(CONF_VALUE *value, ASN1_INTEGER **aint) __attribute__((deprecated));
void X509V3_set_nconf(X509V3_CTX *ctx, CONF *conf) __attribute__((deprecated));
void X509V3_set_conf_lhash(X509V3_CTX *ctx, LHASH *lhash) __attribute__((deprecated));


char * X509V3_get_string(X509V3_CTX *ctx, char *name, char *section) __attribute__((deprecated));
STACK * X509V3_get_section(X509V3_CTX *ctx, char *section) __attribute__((deprecated));
void X509V3_string_free(X509V3_CTX *ctx, char *str) __attribute__((deprecated));
void X509V3_section_free( X509V3_CTX *ctx, STACK *section) __attribute__((deprecated));
void X509V3_set_ctx(X509V3_CTX *ctx, X509 *issuer, X509 *subject,
     X509_REQ *req, X509_CRL *crl, int flags) __attribute__((deprecated));

int X509V3_add_value(const char *name, const char *value,
      STACK **extlist) __attribute__((deprecated));
int X509V3_add_value_uchar(const char *name, const unsigned char *value,
      STACK **extlist) __attribute__((deprecated));
int X509V3_add_value_bool(const char *name, int asn1_bool,
      STACK **extlist) __attribute__((deprecated));
int X509V3_add_value_int(const char *name, ASN1_INTEGER *aint,
      STACK **extlist) __attribute__((deprecated));
char * i2s_ASN1_INTEGER(X509V3_EXT_METHOD *meth, ASN1_INTEGER *aint) __attribute__((deprecated));
ASN1_INTEGER * s2i_ASN1_INTEGER(X509V3_EXT_METHOD *meth, char *value) __attribute__((deprecated));
char * i2s_ASN1_ENUMERATED(X509V3_EXT_METHOD *meth, ASN1_ENUMERATED *aint) __attribute__((deprecated));
char * i2s_ASN1_ENUMERATED_TABLE(X509V3_EXT_METHOD *meth, ASN1_ENUMERATED *aint) __attribute__((deprecated));
int X509V3_EXT_add(X509V3_EXT_METHOD *ext) __attribute__((deprecated));
int X509V3_EXT_add_list(X509V3_EXT_METHOD *extlist) __attribute__((deprecated));
int X509V3_EXT_add_alias(int nid_to, int nid_from) __attribute__((deprecated));
void X509V3_EXT_cleanup(void) __attribute__((deprecated));

X509V3_EXT_METHOD *X509V3_EXT_get(X509_EXTENSION *ext) __attribute__((deprecated));
X509V3_EXT_METHOD *X509V3_EXT_get_nid(int nid) __attribute__((deprecated));
int X509V3_add_standard_extensions(void) __attribute__((deprecated));
STACK *X509V3_parse_list(const char *line) __attribute__((deprecated));
void *X509V3_EXT_d2i(X509_EXTENSION *ext) __attribute__((deprecated));
void *X509V3_get_d2i(STACK *x, int nid, int *crit, int *idx) __attribute__((deprecated));


X509_EXTENSION *X509V3_EXT_i2d(int ext_nid, int crit, void *ext_struc) __attribute__((deprecated));
int X509V3_add1_i2d(STACK **x, int nid, void *value, int crit, unsigned long flags) __attribute__((deprecated));

char *hex_to_string(unsigned char *buffer, long len) __attribute__((deprecated));
unsigned char *string_to_hex(char *str, long *len) __attribute__((deprecated));
int name_cmp(const char *name, const char *cmp) __attribute__((deprecated));

void X509V3_EXT_val_prn(BIO *out, STACK *val, int indent,
         int ml) __attribute__((deprecated));
int X509V3_EXT_print(BIO *out, X509_EXTENSION *ext, unsigned long flag, int indent) __attribute__((deprecated));
int X509V3_EXT_print_fp(FILE *out, X509_EXTENSION *ext, int flag, int indent) __attribute__((deprecated));

int X509V3_extensions_print(BIO *out, char *title, STACK *exts, unsigned long flag, int indent) __attribute__((deprecated));

int X509_check_ca(X509 *x) __attribute__((deprecated));
int X509_check_purpose(X509 *x, int id, int ca) __attribute__((deprecated));
int X509_supported_extension(X509_EXTENSION *ex) __attribute__((deprecated));
int X509_PURPOSE_set(int *p, int purpose) __attribute__((deprecated));
int X509_check_issued(X509 *issuer, X509 *subject) __attribute__((deprecated));
int X509_PURPOSE_get_count(void) __attribute__((deprecated));
X509_PURPOSE * X509_PURPOSE_get0(int idx) __attribute__((deprecated));
int X509_PURPOSE_get_by_sname(char *sname) __attribute__((deprecated));
int X509_PURPOSE_get_by_id(int id) __attribute__((deprecated));
int X509_PURPOSE_add(int id, int trust, int flags,
   int (*ck)(const X509_PURPOSE *, const X509 *, int),
    char *name, char *sname, void *arg) __attribute__((deprecated));
char *X509_PURPOSE_get0_name(X509_PURPOSE *xp) __attribute__((deprecated));
char *X509_PURPOSE_get0_sname(X509_PURPOSE *xp) __attribute__((deprecated));
int X509_PURPOSE_get_trust(X509_PURPOSE *xp) __attribute__((deprecated));
void X509_PURPOSE_cleanup(void) __attribute__((deprecated));
int X509_PURPOSE_get_id(X509_PURPOSE *) __attribute__((deprecated));

STACK *X509_get1_email(X509 *x) __attribute__((deprecated));
STACK *X509_REQ_get1_email(X509_REQ *x) __attribute__((deprecated));
void X509_email_free(STACK *sk) __attribute__((deprecated));
STACK *X509_get1_ocsp(X509 *x) __attribute__((deprecated));

ASN1_OCTET_STRING *a2i_IPADDRESS(const char *ipasc) __attribute__((deprecated));
ASN1_OCTET_STRING *a2i_IPADDRESS_NC(const char *ipasc) __attribute__((deprecated));
int a2i_ipadd(unsigned char *ipout, const char *ipasc) __attribute__((deprecated));
int X509V3_NAME_from_section(X509_NAME *nm, STACK*dn_sk,
      unsigned long chtype) __attribute__((deprecated));

void X509_POLICY_NODE_print(BIO *out, X509_POLICY_NODE *node, int indent) __attribute__((deprecated));
# 787 "/usr/include/openssl/x509v3.h" 3 4
void ERR_load_X509V3_strings(void) __attribute__((deprecated));
# 105 "_ssl.c" 2
# 1 "/usr/include/openssl/pem.h" 1 3 4
# 64 "/usr/include/openssl/pem.h" 3 4
# 1 "/usr/include/openssl/e_os2.h" 1 3 4
# 56 "/usr/include/openssl/e_os2.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 57 "/usr/include/openssl/e_os2.h" 2 3 4
# 65 "/usr/include/openssl/pem.h" 2 3 4
# 73 "/usr/include/openssl/pem.h" 3 4
# 1 "/usr/include/openssl/pem2.h" 1 3 4
# 74 "/usr/include/openssl/pem.h" 2 3 4
# 143 "/usr/include/openssl/pem.h" 3 4
typedef struct PEM_Encode_Seal_st
 {
 EVP_ENCODE_CTX encode;
 EVP_MD_CTX md;
 EVP_CIPHER_CTX cipher;
 } PEM_ENCODE_SEAL_CTX;







typedef struct pem_recip_st
 {
 char *name;
 X509_NAME *dn;

 int cipher;
 int key_enc;

 } PEM_USER;

typedef struct pem_ctx_st
 {
 int type;

 struct {
  int version;
  int mode;
  } proc_type;

 char *domain;

 struct {
  int cipher;


  } DEK_info;

 PEM_USER *originator;

 int num_recipient;
 PEM_USER **recipient;


 STACK *x509_chain;



 EVP_MD *md;

 int md_enc;
 int md_len;
 char *md_data;

 EVP_CIPHER *dec;
 int key_len;
 unsigned char *key;




 int data_enc;
 int data_len;
 unsigned char *data;
 } PEM_CTX;
# 567 "/usr/include/openssl/pem.h" 3 4
typedef int pem_password_cb(char *buf, int size, int rwflag, void *userdata);





int PEM_get_EVP_CIPHER_INFO(char *header, EVP_CIPHER_INFO *cipher) __attribute__((deprecated));
int PEM_do_header (EVP_CIPHER_INFO *cipher, unsigned char *data,long *len,
 pem_password_cb *callback,void *u) __attribute__((deprecated));


int PEM_read_bio(BIO *bp, char **name, char **header,
  unsigned char **data,long *len) __attribute__((deprecated));
int PEM_write_bio(BIO *bp,const char *name,char *hdr,unsigned char *data,
  long len) __attribute__((deprecated));
int PEM_bytes_read_bio(unsigned char **pdata, long *plen, char **pnm, const char *name, BIO *bp,
      pem_password_cb *cb, void *u) __attribute__((deprecated));
void * PEM_ASN1_read_bio(d2i_of_void *d2i, const char *name, BIO *bp,
     void **x, pem_password_cb *cb, void *u) __attribute__((deprecated));







int PEM_ASN1_write_bio(i2d_of_void *i2d,const char *name,BIO *bp,char *x,
      const EVP_CIPHER *enc,unsigned char *kstr,int klen,
      pem_password_cb *cb, void *u) __attribute__((deprecated));







STACK * PEM_X509_INFO_read_bio(BIO *bp, STACK *sk, pem_password_cb *cb, void *u) __attribute__((deprecated));
int PEM_X509_INFO_write_bio(BIO *bp,X509_INFO *xi, EVP_CIPHER *enc,
  unsigned char *kstr, int klen, pem_password_cb *cd, void *u) __attribute__((deprecated));



int PEM_read(FILE *fp, char **name, char **header,
  unsigned char **data,long *len) __attribute__((deprecated));
int PEM_write(FILE *fp,char *name,char *hdr,unsigned char *data,long len) __attribute__((deprecated));
void * PEM_ASN1_read(d2i_of_void *d2i, const char *name, FILE *fp, void **x,
        pem_password_cb *cb, void *u) __attribute__((deprecated));
int PEM_ASN1_write(i2d_of_void *i2d,const char *name,FILE *fp,
         char *x,const EVP_CIPHER *enc,unsigned char *kstr,
         int klen,pem_password_cb *callback, void *u) __attribute__((deprecated));
STACK * PEM_X509_INFO_read(FILE *fp, STACK *sk,
 pem_password_cb *cb, void *u) __attribute__((deprecated));


int PEM_SealInit(PEM_ENCODE_SEAL_CTX *ctx, EVP_CIPHER *type,
  EVP_MD *md_type, unsigned char **ek, int *ekl,
  unsigned char *iv, EVP_PKEY **pubk, int npubk) __attribute__((deprecated));
void PEM_SealUpdate(PEM_ENCODE_SEAL_CTX *ctx, unsigned char *out, int *outl,
  unsigned char *in, int inl) __attribute__((deprecated));
int PEM_SealFinal(PEM_ENCODE_SEAL_CTX *ctx, unsigned char *sig,int *sigl,
  unsigned char *out, int *outl, EVP_PKEY *priv) __attribute__((deprecated));

void PEM_SignInit(EVP_MD_CTX *ctx, EVP_MD *type) __attribute__((deprecated));
void PEM_SignUpdate(EVP_MD_CTX *ctx,unsigned char *d,unsigned int cnt) __attribute__((deprecated));
int PEM_SignFinal(EVP_MD_CTX *ctx, unsigned char *sigret,
  unsigned int *siglen, EVP_PKEY *pkey) __attribute__((deprecated));

int PEM_def_callback(char *buf, int num, int w, void *key) __attribute__((deprecated));
void PEM_proc_type(char *buf, int type) __attribute__((deprecated));
void PEM_dek_info(char *buf, const char *type, int len, char *str) __attribute__((deprecated));



# 1 "/usr/include/openssl/symhacks.h" 1 3 4
# 641 "/usr/include/openssl/pem.h" 2 3 4

X509 *PEM_read_bio_X509(BIO *bp, X509 **x, pem_password_cb *cb, void *u); X509 *PEM_read_X509(FILE *fp, X509 **x, pem_password_cb *cb, void *u); int PEM_write_bio_X509(BIO *bp, X509 *x); int PEM_write_X509(FILE *fp, X509 *x);

X509 *PEM_read_bio_X509_AUX(BIO *bp, X509 **x, pem_password_cb *cb, void *u); X509 *PEM_read_X509_AUX(FILE *fp, X509 **x, pem_password_cb *cb, void *u); int PEM_write_bio_X509_AUX(BIO *bp, X509 *x); int PEM_write_X509_AUX(FILE *fp, X509 *x);

X509_CERT_PAIR *PEM_read_bio_X509_CERT_PAIR(BIO *bp, X509_CERT_PAIR **x, pem_password_cb *cb, void *u); X509_CERT_PAIR *PEM_read_X509_CERT_PAIR(FILE *fp, X509_CERT_PAIR **x, pem_password_cb *cb, void *u); int PEM_write_bio_X509_CERT_PAIR(BIO *bp, X509_CERT_PAIR *x); int PEM_write_X509_CERT_PAIR(FILE *fp, X509_CERT_PAIR *x);

X509_REQ *PEM_read_bio_X509_REQ(BIO *bp, X509_REQ **x, pem_password_cb *cb, void *u); X509_REQ *PEM_read_X509_REQ(FILE *fp, X509_REQ **x, pem_password_cb *cb, void *u); int PEM_write_bio_X509_REQ(BIO *bp, X509_REQ *x); int PEM_write_X509_REQ(FILE *fp, X509_REQ *x);
int PEM_write_bio_X509_REQ_NEW(BIO *bp, X509_REQ *x); int PEM_write_X509_REQ_NEW(FILE *fp, X509_REQ *x);

X509_CRL *PEM_read_bio_X509_CRL(BIO *bp, X509_CRL **x, pem_password_cb *cb, void *u); X509_CRL *PEM_read_X509_CRL(FILE *fp, X509_CRL **x, pem_password_cb *cb, void *u); int PEM_write_bio_X509_CRL(BIO *bp, X509_CRL *x); int PEM_write_X509_CRL(FILE *fp, X509_CRL *x);

PKCS7 *PEM_read_bio_PKCS7(BIO *bp, PKCS7 **x, pem_password_cb *cb, void *u); PKCS7 *PEM_read_PKCS7(FILE *fp, PKCS7 **x, pem_password_cb *cb, void *u); int PEM_write_bio_PKCS7(BIO *bp, PKCS7 *x); int PEM_write_PKCS7(FILE *fp, PKCS7 *x);

NETSCAPE_CERT_SEQUENCE *PEM_read_bio_NETSCAPE_CERT_SEQUENCE(BIO *bp, NETSCAPE_CERT_SEQUENCE **x, pem_password_cb *cb, void *u); NETSCAPE_CERT_SEQUENCE *PEM_read_NETSCAPE_CERT_SEQUENCE(FILE *fp, NETSCAPE_CERT_SEQUENCE **x, pem_password_cb *cb, void *u); int PEM_write_bio_NETSCAPE_CERT_SEQUENCE(BIO *bp, NETSCAPE_CERT_SEQUENCE *x); int PEM_write_NETSCAPE_CERT_SEQUENCE(FILE *fp, NETSCAPE_CERT_SEQUENCE *x);

X509_SIG *PEM_read_bio_PKCS8(BIO *bp, X509_SIG **x, pem_password_cb *cb, void *u); X509_SIG *PEM_read_PKCS8(FILE *fp, X509_SIG **x, pem_password_cb *cb, void *u); int PEM_write_bio_PKCS8(BIO *bp, X509_SIG *x); int PEM_write_PKCS8(FILE *fp, X509_SIG *x);

PKCS8_PRIV_KEY_INFO *PEM_read_bio_PKCS8_PRIV_KEY_INFO(BIO *bp, PKCS8_PRIV_KEY_INFO **x, pem_password_cb *cb, void *u); PKCS8_PRIV_KEY_INFO *PEM_read_PKCS8_PRIV_KEY_INFO(FILE *fp, PKCS8_PRIV_KEY_INFO **x, pem_password_cb *cb, void *u); int PEM_write_bio_PKCS8_PRIV_KEY_INFO(BIO *bp, PKCS8_PRIV_KEY_INFO *x); int PEM_write_PKCS8_PRIV_KEY_INFO(FILE *fp, PKCS8_PRIV_KEY_INFO *x);



RSA *PEM_read_bio_RSAPrivateKey(BIO *bp, RSA **x, pem_password_cb *cb, void *u); RSA *PEM_read_RSAPrivateKey(FILE *fp, RSA **x, pem_password_cb *cb, void *u); int PEM_write_bio_RSAPrivateKey(BIO *bp, RSA *x, const EVP_CIPHER *enc, unsigned char *kstr, int klen, pem_password_cb *cb, void *u); int PEM_write_RSAPrivateKey(FILE *fp, RSA *x, const EVP_CIPHER *enc, unsigned char *kstr, int klen, pem_password_cb *cb, void *u);

RSA *PEM_read_bio_RSAPublicKey(BIO *bp, RSA **x, pem_password_cb *cb, void *u); RSA *PEM_read_RSAPublicKey(FILE *fp, RSA **x, pem_password_cb *cb, void *u); int PEM_write_bio_RSAPublicKey(BIO *bp, const RSA *x); int PEM_write_RSAPublicKey(FILE *fp, const RSA *x);
RSA *PEM_read_bio_RSA_PUBKEY(BIO *bp, RSA **x, pem_password_cb *cb, void *u); RSA *PEM_read_RSA_PUBKEY(FILE *fp, RSA **x, pem_password_cb *cb, void *u); int PEM_write_bio_RSA_PUBKEY(BIO *bp, RSA *x); int PEM_write_RSA_PUBKEY(FILE *fp, RSA *x);





DSA *PEM_read_bio_DSAPrivateKey(BIO *bp, DSA **x, pem_password_cb *cb, void *u); DSA *PEM_read_DSAPrivateKey(FILE *fp, DSA **x, pem_password_cb *cb, void *u); int PEM_write_bio_DSAPrivateKey(BIO *bp, DSA *x, const EVP_CIPHER *enc, unsigned char *kstr, int klen, pem_password_cb *cb, void *u); int PEM_write_DSAPrivateKey(FILE *fp, DSA *x, const EVP_CIPHER *enc, unsigned char *kstr, int klen, pem_password_cb *cb, void *u);

DSA *PEM_read_bio_DSA_PUBKEY(BIO *bp, DSA **x, pem_password_cb *cb, void *u); DSA *PEM_read_DSA_PUBKEY(FILE *fp, DSA **x, pem_password_cb *cb, void *u); int PEM_write_bio_DSA_PUBKEY(BIO *bp, DSA *x); int PEM_write_DSA_PUBKEY(FILE *fp, DSA *x);

DSA *PEM_read_bio_DSAparams(BIO *bp, DSA **x, pem_password_cb *cb, void *u); DSA *PEM_read_DSAparams(FILE *fp, DSA **x, pem_password_cb *cb, void *u); int PEM_write_bio_DSAparams(BIO *bp, const DSA *x); int PEM_write_DSAparams(FILE *fp, const DSA *x);




EC_GROUP *PEM_read_bio_ECPKParameters(BIO *bp, EC_GROUP **x, pem_password_cb *cb, void *u); EC_GROUP *PEM_read_ECPKParameters(FILE *fp, EC_GROUP **x, pem_password_cb *cb, void *u); int PEM_write_bio_ECPKParameters(BIO *bp, const EC_GROUP *x); int PEM_write_ECPKParameters(FILE *fp, const EC_GROUP *x);
EC_KEY *PEM_read_bio_ECPrivateKey(BIO *bp, EC_KEY **x, pem_password_cb *cb, void *u); EC_KEY *PEM_read_ECPrivateKey(FILE *fp, EC_KEY **x, pem_password_cb *cb, void *u); int PEM_write_bio_ECPrivateKey(BIO *bp, EC_KEY *x, const EVP_CIPHER *enc, unsigned char *kstr, int klen, pem_password_cb *cb, void *u); int PEM_write_ECPrivateKey(FILE *fp, EC_KEY *x, const EVP_CIPHER *enc, unsigned char *kstr, int klen, pem_password_cb *cb, void *u);
EC_KEY *PEM_read_bio_EC_PUBKEY(BIO *bp, EC_KEY **x, pem_password_cb *cb, void *u); EC_KEY *PEM_read_EC_PUBKEY(FILE *fp, EC_KEY **x, pem_password_cb *cb, void *u); int PEM_write_bio_EC_PUBKEY(BIO *bp, EC_KEY *x); int PEM_write_EC_PUBKEY(FILE *fp, EC_KEY *x);




DH *PEM_read_bio_DHparams(BIO *bp, DH **x, pem_password_cb *cb, void *u); DH *PEM_read_DHparams(FILE *fp, DH **x, pem_password_cb *cb, void *u); int PEM_write_bio_DHparams(BIO *bp, const DH *x); int PEM_write_DHparams(FILE *fp, const DH *x);



EVP_PKEY *PEM_read_bio_PrivateKey(BIO *bp, EVP_PKEY **x, pem_password_cb *cb, void *u); EVP_PKEY *PEM_read_PrivateKey(FILE *fp, EVP_PKEY **x, pem_password_cb *cb, void *u); int PEM_write_bio_PrivateKey(BIO *bp, EVP_PKEY *x, const EVP_CIPHER *enc, unsigned char *kstr, int klen, pem_password_cb *cb, void *u); int PEM_write_PrivateKey(FILE *fp, EVP_PKEY *x, const EVP_CIPHER *enc, unsigned char *kstr, int klen, pem_password_cb *cb, void *u);

EVP_PKEY *PEM_read_bio_PUBKEY(BIO *bp, EVP_PKEY **x, pem_password_cb *cb, void *u); EVP_PKEY *PEM_read_PUBKEY(FILE *fp, EVP_PKEY **x, pem_password_cb *cb, void *u); int PEM_write_bio_PUBKEY(BIO *bp, EVP_PKEY *x); int PEM_write_PUBKEY(FILE *fp, EVP_PKEY *x);

int PEM_write_bio_PKCS8PrivateKey_nid(BIO *bp, EVP_PKEY *x, int nid,
      char *kstr, int klen,
      pem_password_cb *cb, void *u) __attribute__((deprecated));
int PEM_write_bio_PKCS8PrivateKey(BIO *, EVP_PKEY *, const EVP_CIPHER *,
                                  char *, int, pem_password_cb *, void *) __attribute__((deprecated));
int i2d_PKCS8PrivateKey_bio(BIO *bp, EVP_PKEY *x, const EVP_CIPHER *enc,
      char *kstr, int klen,
      pem_password_cb *cb, void *u) __attribute__((deprecated));
int i2d_PKCS8PrivateKey_nid_bio(BIO *bp, EVP_PKEY *x, int nid,
      char *kstr, int klen,
      pem_password_cb *cb, void *u) __attribute__((deprecated));
EVP_PKEY *d2i_PKCS8PrivateKey_bio(BIO *bp, EVP_PKEY **x, pem_password_cb *cb, void *u) __attribute__((deprecated));

int i2d_PKCS8PrivateKey_fp(FILE *fp, EVP_PKEY *x, const EVP_CIPHER *enc,
      char *kstr, int klen,
      pem_password_cb *cb, void *u) __attribute__((deprecated));
int i2d_PKCS8PrivateKey_nid_fp(FILE *fp, EVP_PKEY *x, int nid,
      char *kstr, int klen,
      pem_password_cb *cb, void *u) __attribute__((deprecated));
int PEM_write_PKCS8PrivateKey_nid(FILE *fp, EVP_PKEY *x, int nid,
      char *kstr, int klen,
      pem_password_cb *cb, void *u) __attribute__((deprecated));

EVP_PKEY *d2i_PKCS8PrivateKey_fp(FILE *fp, EVP_PKEY **x, pem_password_cb *cb, void *u) __attribute__((deprecated));

int PEM_write_PKCS8PrivateKey(FILE *fp,EVP_PKEY *x,const EVP_CIPHER *enc,
         char *kstr,int klen, pem_password_cb *cd, void *u) __attribute__((deprecated));
# 731 "/usr/include/openssl/pem.h" 3 4
void ERR_load_PEM_strings(void) __attribute__((deprecated));
# 106 "_ssl.c" 2
# 1 "/usr/include/openssl/ssl.h" 1 3 4
# 175 "/usr/include/openssl/ssl.h" 3 4
# 1 "/usr/include/openssl/e_os2.h" 1 3 4
# 56 "/usr/include/openssl/e_os2.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 57 "/usr/include/openssl/e_os2.h" 2 3 4
# 176 "/usr/include/openssl/ssl.h" 2 3 4


# 1 "/usr/include/openssl/comp.h" 1 3 4
# 13 "/usr/include/openssl/comp.h" 3 4
typedef struct comp_ctx_st COMP_CTX;

typedef struct comp_method_st
 {
 int type;
 const char *name;
 int (*init)(COMP_CTX *ctx);
 void (*finish)(COMP_CTX *ctx);
 int (*compress)(COMP_CTX *ctx,
   unsigned char *out, unsigned int olen,
   unsigned char *in, unsigned int ilen);
 int (*expand)(COMP_CTX *ctx,
        unsigned char *out, unsigned int olen,
        unsigned char *in, unsigned int ilen);

 long (*ctrl)(void);
 long (*callback_ctrl)(void);
 } COMP_METHOD;

struct comp_ctx_st
 {
 COMP_METHOD *meth;
 unsigned long compress_in;
 unsigned long compress_out;
 unsigned long expand_in;
 unsigned long expand_out;

 CRYPTO_EX_DATA ex_data;
 };


COMP_CTX *COMP_CTX_new(COMP_METHOD *meth) __attribute__((deprecated));
void COMP_CTX_free(COMP_CTX *ctx) __attribute__((deprecated));
int COMP_compress_block(COMP_CTX *ctx, unsigned char *out, int olen,
 unsigned char *in, int ilen) __attribute__((deprecated));
int COMP_expand_block(COMP_CTX *ctx, unsigned char *out, int olen,
 unsigned char *in, int ilen) __attribute__((deprecated));
COMP_METHOD *COMP_rle(void ) __attribute__((deprecated));
COMP_METHOD *COMP_zlib(void ) __attribute__((deprecated));
void COMP_zlib_cleanup(void) __attribute__((deprecated));
# 64 "/usr/include/openssl/comp.h" 3 4
void ERR_load_COMP_strings(void) __attribute__((deprecated));
# 179 "/usr/include/openssl/ssl.h" 2 3 4
# 191 "/usr/include/openssl/ssl.h" 3 4
# 1 "/usr/include/openssl/pem.h" 1 3 4
# 192 "/usr/include/openssl/ssl.h" 2 3 4
# 1 "/usr/include/openssl/hmac.h" 1 3 4
# 63 "/usr/include/openssl/hmac.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 64 "/usr/include/openssl/hmac.h" 2 3 4
# 77 "/usr/include/openssl/hmac.h" 3 4
typedef struct hmac_ctx_st
 {
 const EVP_MD *md;
 EVP_MD_CTX md_ctx;
 EVP_MD_CTX i_ctx;
 EVP_MD_CTX o_ctx;
 unsigned int key_length;
 unsigned char key[128];
 } HMAC_CTX;




void HMAC_CTX_init(HMAC_CTX *ctx) __attribute__((deprecated));
void HMAC_CTX_cleanup(HMAC_CTX *ctx) __attribute__((deprecated));



void HMAC_Init(HMAC_CTX *ctx, const void *key, int len,
        const EVP_MD *md) __attribute__((deprecated));
void HMAC_Init_ex(HMAC_CTX *ctx, const void *key, int len,
    const EVP_MD *md, ENGINE *impl) __attribute__((deprecated));
void HMAC_Update(HMAC_CTX *ctx, const unsigned char *data, size_t len) __attribute__((deprecated));
void HMAC_Final(HMAC_CTX *ctx, unsigned char *md, unsigned int *len) __attribute__((deprecated));
unsigned char *HMAC(const EVP_MD *evp_md, const void *key, int key_len,
      const unsigned char *d, size_t n, unsigned char *md,
      unsigned int *md_len) __attribute__((deprecated));

void HMAC_CTX_set_flags(HMAC_CTX *ctx, unsigned long flags) __attribute__((deprecated));
# 193 "/usr/include/openssl/ssl.h" 2 3 4

# 1 "/usr/include/openssl/kssl.h" 1 3 4
# 68 "/usr/include/openssl/kssl.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 69 "/usr/include/openssl/kssl.h" 2 3 4
# 195 "/usr/include/openssl/ssl.h" 2 3 4

# 1 "/usr/include/openssl/symhacks.h" 1 3 4
# 197 "/usr/include/openssl/ssl.h" 2 3 4
# 348 "/usr/include/openssl/ssl.h" 3 4
typedef struct ssl_st *ssl_crock_st;


typedef struct ssl_cipher_st
 {
 int valid;
 const char *name;
 unsigned long id;
 unsigned long algorithms;
 unsigned long algo_strength;
 unsigned long algorithm2;
 int strength_bits;
 int alg_bits;
 unsigned long mask;
 unsigned long mask_strength;
 } SSL_CIPHER;




typedef struct ssl_method_st
 {
 int version;
 int (*ssl_new)(SSL *s);
 void (*ssl_clear)(SSL *s);
 void (*ssl_free)(SSL *s);
 int (*ssl_accept)(SSL *s);
 int (*ssl_connect)(SSL *s);
 int (*ssl_read)(SSL *s,void *buf,int len);
 int (*ssl_peek)(SSL *s,void *buf,int len);
 int (*ssl_write)(SSL *s,const void *buf,int len);
 int (*ssl_shutdown)(SSL *s);
 int (*ssl_renegotiate)(SSL *s);
 int (*ssl_renegotiate_check)(SSL *s);
 long (*ssl_get_message)(SSL *s, int st1, int stn, int mt, long
  max, int *ok);
 int (*ssl_read_bytes)(SSL *s, int type, unsigned char *buf, int len,
  int peek);
 int (*ssl_write_bytes)(SSL *s, int type, const void *buf_, int len);
 int (*ssl_dispatch_alert)(SSL *s);
 long (*ssl_ctrl)(SSL *s,int cmd,long larg,void *parg);
 long (*ssl_ctx_ctrl)(SSL_CTX *ctx,int cmd,long larg,void *parg);
 SSL_CIPHER *(*get_cipher_by_char)(const unsigned char *ptr);
 int (*put_cipher_by_char)(const SSL_CIPHER *cipher,unsigned char *ptr);
 int (*ssl_pending)(const SSL *s);
 int (*num_ciphers)(void);
 SSL_CIPHER *(*get_cipher)(unsigned ncipher);
 struct ssl_method_st *(*get_ssl_method)(int version);
 long (*get_timeout)(void);
 struct ssl3_enc_method *ssl3_enc;
 int (*ssl_version)(void);
 long (*ssl_callback_ctrl)(SSL *s, int cb_id, void (*fp)(void));
 long (*ssl_ctx_callback_ctrl)(SSL_CTX *s, int cb_id, void (*fp)(void));
 } SSL_METHOD;
# 422 "/usr/include/openssl/ssl.h" 3 4
typedef struct ssl_session_st
 {
 int ssl_version;



 unsigned int key_arg_length;
 unsigned char key_arg[8];
 int master_key_length;
 unsigned char master_key[48];

 unsigned int session_id_length;
 unsigned char session_id[32];



 unsigned int sid_ctx_length;
 unsigned char sid_ctx[32];






 int not_resumable;


 struct sess_cert_st *sess_cert;





 X509 *peer;


 long verify_result;

 int references;
 long timeout;
 long time;

 int compress_meth;

 SSL_CIPHER *cipher;
 unsigned long cipher_id;



 STACK *ciphers;

 CRYPTO_EX_DATA ex_data;



 struct ssl_session_st *prev,*next;

 char *tlsext_hostname;

 unsigned char *tlsext_tick;
 size_t tlsext_ticklen;
 long tlsext_tick_lifetime_hint;

 } SSL_SESSION;
# 601 "/usr/include/openssl/ssl.h" 3 4
void SSL_CTX_set_msg_callback(SSL_CTX *ctx, void (*cb)(int write_p, int version, int content_type, const void *buf, size_t len, SSL *ssl, void *arg)) __attribute__((deprecated));
void SSL_set_msg_callback(SSL *ssl, void (*cb)(int write_p, int version, int content_type, const void *buf, size_t len, SSL *ssl, void *arg)) __attribute__((deprecated));
# 629 "/usr/include/openssl/ssl.h" 3 4
typedef int (*GEN_SESSION_CB)(const SSL *ssl, unsigned char *id,
    unsigned int *id_len);

typedef struct ssl_comp_st
 {
 int id;
 const char *name;

 COMP_METHOD *method;



 } SSL_COMP;



struct ssl_ctx_st
 {
 SSL_METHOD *method;

 STACK *cipher_list;

 STACK *cipher_list_by_id;

 struct x509_store_st *cert_store;
 struct lhash_st *sessions;


 unsigned long session_cache_size;
 struct ssl_session_st *session_cache_head;
 struct ssl_session_st *session_cache_tail;






 int session_cache_mode;




 long session_timeout;
# 681 "/usr/include/openssl/ssl.h" 3 4
 int (*new_session_cb)(struct ssl_st *ssl,SSL_SESSION *sess);
 void (*remove_session_cb)(struct ssl_ctx_st *ctx,SSL_SESSION *sess);
 SSL_SESSION *(*get_session_cb)(struct ssl_st *ssl,
  unsigned char *data,int len,int *copy);

 struct
  {
  int sess_connect;
  int sess_connect_renegotiate;
  int sess_connect_good;
  int sess_accept;
  int sess_accept_renegotiate;
  int sess_accept_good;
  int sess_miss;
  int sess_timeout;
  int sess_cache_full;
  int sess_hit;
  int sess_cb_hit;





  } stats;

 int references;


 int (*app_verify_callback)(X509_STORE_CTX *, void *);
 void *app_verify_arg;




 pem_password_cb *default_passwd_callback;


 void *default_passwd_callback_userdata;


 int (*client_cert_cb)(SSL *ssl, X509 **x509, EVP_PKEY **pkey);


    int (*app_gen_cookie_cb)(SSL *ssl, unsigned char *cookie,
        unsigned int *cookie_len);


    int (*app_verify_cookie_cb)(SSL *ssl, unsigned char *cookie,
        unsigned int cookie_len);

 CRYPTO_EX_DATA ex_data;

 const EVP_MD *rsa_md5;
 const EVP_MD *md5;
 const EVP_MD *sha1;

 STACK *extra_certs;
 STACK *comp_methods;




 void (*info_callback)(const SSL *ssl,int type,int val);


 STACK *client_CA;




 unsigned long options;
 unsigned long mode;
 long max_cert_list;

 struct cert_st *cert;
 int read_ahead;


 void (*msg_callback)(int write_p, int version, int content_type, const void *buf, size_t len, SSL *ssl, void *arg);
 void *msg_callback_arg;

 int verify_mode;
 unsigned int sid_ctx_length;
 unsigned char sid_ctx[32];
 int (*default_verify_callback)(int ok,X509_STORE_CTX *ctx);


 GEN_SESSION_CB generate_session_id;

 X509_VERIFY_PARAM *param;






 int quiet_shutdown;




 ENGINE *client_cert_engine;




 int (*tlsext_servername_callback)(SSL*, int *, void *);
 void *tlsext_servername_arg;

 unsigned char tlsext_tick_key_name[16];
 unsigned char tlsext_tick_hmac_key[16];
 unsigned char tlsext_tick_aes_key[16];

 int (*tlsext_ticket_key_cb)(SSL *ssl,
     unsigned char *name, unsigned char *iv,
     EVP_CIPHER_CTX *ectx,
     HMAC_CTX *hctx, int enc);



 int (*tlsext_status_cb)(SSL *ssl, void *arg);
 void *tlsext_status_arg;


 };
# 818 "/usr/include/openssl/ssl.h" 3 4
  struct lhash_st *SSL_CTX_sessions(SSL_CTX *ctx);
# 844 "/usr/include/openssl/ssl.h" 3 4
void SSL_CTX_sess_set_new_cb(SSL_CTX *ctx, int (*new_session_cb)(struct ssl_st *ssl,SSL_SESSION *sess)) __attribute__((deprecated));
int (*SSL_CTX_sess_get_new_cb(SSL_CTX *ctx))(struct ssl_st *ssl, SSL_SESSION *sess) __attribute__((deprecated));
void SSL_CTX_sess_set_remove_cb(SSL_CTX *ctx, void (*remove_session_cb)(struct ssl_ctx_st *ctx,SSL_SESSION *sess)) __attribute__((deprecated));
void (*SSL_CTX_sess_get_remove_cb(SSL_CTX *ctx))(struct ssl_ctx_st *ctx, SSL_SESSION *sess) __attribute__((deprecated));
void SSL_CTX_sess_set_get_cb(SSL_CTX *ctx, SSL_SESSION *(*get_session_cb)(struct ssl_st *ssl, unsigned char *data,int len,int *copy)) __attribute__((deprecated));
SSL_SESSION *(*SSL_CTX_sess_get_get_cb(SSL_CTX *ctx))(struct ssl_st *ssl, unsigned char *Data, int len, int *copy) __attribute__((deprecated));
void SSL_CTX_set_info_callback(SSL_CTX *ctx, void (*cb)(const SSL *ssl,int type,int val)) __attribute__((deprecated));
void (*SSL_CTX_get_info_callback(SSL_CTX *ctx))(const SSL *ssl,int type,int val) __attribute__((deprecated));
void SSL_CTX_set_client_cert_cb(SSL_CTX *ctx, int (*client_cert_cb)(SSL *ssl, X509 **x509, EVP_PKEY **pkey)) __attribute__((deprecated));
int (*SSL_CTX_get_client_cert_cb(SSL_CTX *ctx))(SSL *ssl, X509 **x509, EVP_PKEY **pkey) __attribute__((deprecated));

int SSL_CTX_set_client_cert_engine(SSL_CTX *ctx, ENGINE *e) __attribute__((deprecated));

void SSL_CTX_set_cookie_generate_cb(SSL_CTX *ctx, int (*app_gen_cookie_cb)(SSL *ssl, unsigned char *cookie, unsigned int *cookie_len)) __attribute__((deprecated));
void SSL_CTX_set_cookie_verify_cb(SSL_CTX *ctx, int (*app_verify_cookie_cb)(SSL *ssl, unsigned char *cookie, unsigned int cookie_len)) __attribute__((deprecated));
# 871 "/usr/include/openssl/ssl.h" 3 4
struct ssl_st
 {



 int version;
 int type;

 SSL_METHOD *method;






 BIO *rbio;
 BIO *wbio;
 BIO *bbio;
# 899 "/usr/include/openssl/ssl.h" 3 4
 int rwstate;


 int in_handshake;
 int (*handshake_func)(SSL *);
# 913 "/usr/include/openssl/ssl.h" 3 4
 int server;

 int new_session;





 int quiet_shutdown;
 int shutdown;

 int state;
 int rstate;

 BUF_MEM *init_buf;
 void *init_msg;
 int init_num;
 int init_off;


 unsigned char *packet;
 unsigned int packet_length;

 struct ssl2_state_st *s2;
 struct ssl3_state_st *s3;
 struct dtls1_state_st *d1;

 int read_ahead;



 void (*msg_callback)(int write_p, int version, int content_type, const void *buf, size_t len, SSL *ssl, void *arg);
 void *msg_callback_arg;

 int hit;

 X509_VERIFY_PARAM *param;







 STACK *cipher_list;
 STACK *cipher_list_by_id;




 EVP_CIPHER_CTX *enc_read_ctx;
 const EVP_MD *read_hash;

 COMP_CTX *expand;




 EVP_CIPHER_CTX *enc_write_ctx;
 const EVP_MD *write_hash;

 COMP_CTX *compress;
# 983 "/usr/include/openssl/ssl.h" 3 4
 struct cert_st *cert;



 unsigned int sid_ctx_length;
 unsigned char sid_ctx[32];


 SSL_SESSION *session;


 GEN_SESSION_CB generate_session_id;


 int verify_mode;

 int (*verify_callback)(int ok,X509_STORE_CTX *ctx);

 void (*info_callback)(const SSL *ssl,int type,int val);

 int error;
 int error_code;





 SSL_CTX *ctx;


 int debug;


 long verify_result;
 CRYPTO_EX_DATA ex_data;


 STACK *client_CA;

 int references;
 unsigned long options;
 unsigned long mode;
 long max_cert_list;
 int first_packet;
 int client_version;



 void (*tlsext_debug_cb)(SSL *s, int client_server, int type,
     unsigned char *data, int len,
     void *arg);
 void *tlsext_debug_arg;
 char *tlsext_hostname;
 int servername_done;






 int tlsext_status_type;

 int tlsext_status_expected;

 STACK *tlsext_ocsp_ids;
 X509_EXTENSIONS *tlsext_ocsp_exts;

 unsigned char *tlsext_ocsp_resp;
 int tlsext_ocsp_resplen;


 int tlsext_ticket_expected;
 SSL_CTX * initial_ctx;




 };





# 1 "/usr/include/openssl/ssl2.h" 1 3 4
# 158 "/usr/include/openssl/ssl2.h" 3 4
typedef struct ssl2_state_st
 {
 int three_byte_header;
 int clear_text;
 int escape;
 int ssl2_rollback;



 unsigned int wnum;
 int wpend_tot;
 const unsigned char *wpend_buf;

 int wpend_off;
 int wpend_len;
 int wpend_ret;


 int rbuf_left;
 int rbuf_offs;
 unsigned char *rbuf;
 unsigned char *wbuf;

 unsigned char *write_ptr;


 unsigned int padding;
 unsigned int rlength;
 int ract_data_length;
 unsigned int wlength;
 int wact_data_length;
 unsigned char *ract_data;
 unsigned char *wact_data;
 unsigned char *mac_data;

 unsigned char *read_key;
 unsigned char *write_key;


 unsigned int challenge_length;
 unsigned char challenge[32];
 unsigned int conn_id_length;
 unsigned char conn_id[16];
 unsigned int key_material_length;
 unsigned char key_material[24*2];

 unsigned long read_sequence;
 unsigned long write_sequence;

 struct {
  unsigned int conn_id_length;
  unsigned int cert_type;
  unsigned int cert_length;
  unsigned int csl;
  unsigned int clear;
  unsigned int enc;
  unsigned char ccl[32];
  unsigned int cipher_spec_length;
  unsigned int session_id_length;
  unsigned int clen;
  unsigned int rlen;
  } tmp;
 } SSL2_STATE;
# 1067 "/usr/include/openssl/ssl.h" 2 3 4
# 1 "/usr/include/openssl/ssl3.h" 1 3 4
# 125 "/usr/include/openssl/ssl3.h" 3 4
# 1 "/usr/include/openssl/ssl.h" 1 3 4
# 126 "/usr/include/openssl/ssl3.h" 2 3 4
# 1 "/usr/include/openssl/pq_compat.h" 1 3 4
# 63 "/usr/include/openssl/pq_compat.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 64 "/usr/include/openssl/pq_compat.h" 2 3 4
# 127 "/usr/include/openssl/ssl3.h" 2 3 4
# 297 "/usr/include/openssl/ssl3.h" 3 4
typedef struct ssl3_record_st
 {
       int type;
       unsigned int length;
       unsigned int off;
       unsigned char *data;
       unsigned char *input;
       unsigned char *comp;
        unsigned long epoch;
        unsigned long long seq_num;
 } SSL3_RECORD;

typedef struct ssl3_buffer_st
 {
 unsigned char *buf;

 size_t len;
 int offset;
 int left;
 } SSL3_BUFFER;
# 337 "/usr/include/openssl/ssl3.h" 3 4
typedef struct ssl3_state_st
 {
 long flags;
 int delay_buf_pop_ret;

 unsigned char read_sequence[8];
 unsigned char read_mac_secret[64];
 unsigned char write_sequence[8];
 unsigned char write_mac_secret[64];

 unsigned char server_random[32];
 unsigned char client_random[32];


 int need_empty_fragments;
 int empty_fragment_done;

 SSL3_BUFFER rbuf;
 SSL3_BUFFER wbuf;

 SSL3_RECORD rrec;
 SSL3_RECORD wrec;



 unsigned char alert_fragment[2];
 unsigned int alert_fragment_len;
 unsigned char handshake_fragment[4];
 unsigned int handshake_fragment_len;


 unsigned int wnum;
 int wpend_tot;
 int wpend_type;
 int wpend_ret;
 const unsigned char *wpend_buf;


 EVP_MD_CTX finish_dgst1;
 EVP_MD_CTX finish_dgst2;



 int change_cipher_spec;

 int warn_alert;
 int fatal_alert;


 int alert_dispatch;
 unsigned char send_alert[2];



 int renegotiate;
 int total_renegotiations;
 int num_renegotiations;

 int in_read_app_data;

 struct {

  unsigned char cert_verify_md[64*2];


  unsigned char finish_md[64*2];
  int finish_md_len;
  unsigned char peer_finish_md[64*2];
  int peer_finish_md_len;

  unsigned long message_size;
  int message_type;


  SSL_CIPHER *new_cipher;

  DH *dh;



  EC_KEY *ecdh;



  int next_state;

  int reuse_message;


  int cert_req;
  int ctype_num;
  char ctype[7];
  STACK *ca_names;

  int use_rsa_tmp;

  int key_block_length;
  unsigned char *key_block;

  const EVP_CIPHER *new_sym_enc;
  const EVP_MD *new_hash;

  const SSL_COMP *new_compression;



  int cert_request;
  } tmp;


        unsigned char previous_client_finished[64];
        unsigned char previous_client_finished_len;
        unsigned char previous_server_finished[64];
        unsigned char previous_server_finished_len;
        int send_connection_binding;
 } SSL3_STATE;
# 1068 "/usr/include/openssl/ssl.h" 2 3 4
# 1 "/usr/include/openssl/tls1.h" 1 3 4
# 130 "/usr/include/openssl/tls1.h" 3 4
const char *SSL_get_servername(const SSL *s, const int type) ;
int SSL_get_servername_type(const SSL *s) ;
# 1069 "/usr/include/openssl/ssl.h" 2 3 4
# 1 "/usr/include/openssl/dtls1.h" 1 3 4
# 64 "/usr/include/openssl/dtls1.h" 3 4
# 1 "/usr/include/openssl/pqueue.h" 1 3 4
# 71 "/usr/include/openssl/pqueue.h" 3 4
typedef struct _pqueue *pqueue;

typedef struct _pitem
 {
 unsigned long long priority;
 void *data;
 struct _pitem *next;
 } pitem;

typedef struct _pitem *piterator;

pitem *pitem_new(unsigned long long priority, void *data) __attribute__((deprecated));
void pitem_free(pitem *item) __attribute__((deprecated));

pqueue pqueue_new(void) __attribute__((deprecated));
void pqueue_free(pqueue pq) __attribute__((deprecated));

pitem *pqueue_insert(pqueue pq, pitem *item) __attribute__((deprecated));
pitem *pqueue_peek(pqueue pq) __attribute__((deprecated));
pitem *pqueue_pop(pqueue pq) __attribute__((deprecated));
pitem *pqueue_find(pqueue pq, unsigned long long priority) __attribute__((deprecated));
pitem *pqueue_iterator(pqueue pq) __attribute__((deprecated));
pitem *pqueue_next(piterator *iter) __attribute__((deprecated));

void pqueue_print(pqueue pq) __attribute__((deprecated));
int pqueue_size(pqueue pq) __attribute__((deprecated));
# 65 "/usr/include/openssl/dtls1.h" 2 3 4
# 109 "/usr/include/openssl/dtls1.h" 3 4
typedef struct dtls1_bitmap_st
 {
 unsigned long long map;
 unsigned long length;
 unsigned long long max_seq_num;
 } DTLS1_BITMAP;

struct dtls1_retransmit_state
 {
 EVP_CIPHER_CTX *enc_write_ctx;
 const EVP_MD *write_hash;

 COMP_CTX *compress;



 SSL_SESSION *session;
 unsigned short epoch;
 };

struct hm_header_st
 {
 unsigned char type;
 unsigned long msg_len;
 unsigned short seq;
 unsigned long frag_off;
 unsigned long frag_len;
 unsigned int is_ccs;
 struct dtls1_retransmit_state saved_retransmit_state;
 };

struct ccs_header_st
 {
 unsigned char type;
 unsigned short seq;
 };

struct dtls1_timeout_st
 {

 unsigned int read_timeouts;


 unsigned int write_timeouts;


 unsigned int num_alerts;
 };

typedef struct record_pqueue_st
 {
 unsigned short epoch;
 pqueue q;
 } record_pqueue;

typedef struct hm_fragment_st
 {
 struct hm_header_st msg_header;
 unsigned char *fragment;
 unsigned char *reassembly;
 } hm_fragment;

typedef struct dtls1_state_st
 {
 unsigned int send_cookie;
 unsigned char cookie[256];
 unsigned char rcvd_cookie[256];
 unsigned int cookie_len;






 unsigned short r_epoch;
 unsigned short w_epoch;


 DTLS1_BITMAP bitmap;


 DTLS1_BITMAP next_bitmap;


 unsigned short handshake_write_seq;
 unsigned short next_handshake_write_seq;

 unsigned short handshake_read_seq;


 unsigned char last_write_sequence[8];


 record_pqueue unprocessed_rcds;
 record_pqueue processed_rcds;


 pqueue buffered_messages;


 pqueue sent_messages;






 record_pqueue buffered_app_data;


 unsigned int listen;

 unsigned int mtu;

 struct hm_header_st w_msg_hdr;
 struct hm_header_st r_msg_hdr;

 struct dtls1_timeout_st timeout;


 struct timeval next_timeout;


 unsigned short timeout_duration;



 unsigned char alert_fragment[2];
 unsigned int alert_fragment_len;
 unsigned char handshake_fragment[12];
 unsigned int handshake_fragment_len;

 unsigned int retransmitting;
 unsigned int change_cipher_spec_ok;

 } DTLS1_STATE;

typedef struct dtls1_record_data_st
 {
 unsigned char *packet;
 unsigned int packet_length;
 SSL3_BUFFER rbuf;
 SSL3_RECORD rrec;
 } DTLS1_RECORD_DATA;
# 1070 "/usr/include/openssl/ssl.h" 2 3 4
# 1 "/usr/include/openssl/ssl23.h" 1 3 4
# 1071 "/usr/include/openssl/ssl.h" 2 3 4
# 1131 "/usr/include/openssl/ssl.h" 3 4
size_t SSL_get_finished(const SSL *s, void *buf, size_t count) __attribute__((deprecated));
size_t SSL_get_peer_finished(const SSL *s, void *buf, size_t count) __attribute__((deprecated));
# 1336 "/usr/include/openssl/ssl.h" 3 4
BIO_METHOD *BIO_f_ssl(void);
BIO *BIO_new_ssl(SSL_CTX *ctx,int client) __attribute__((deprecated));
BIO *BIO_new_ssl_connect(SSL_CTX *ctx) __attribute__((deprecated));
BIO *BIO_new_buffer_ssl_connect(SSL_CTX *ctx) __attribute__((deprecated));
int BIO_ssl_copy_session_id(BIO *to,BIO *from);
void BIO_ssl_shutdown(BIO *ssl_bio);



int SSL_CTX_set_cipher_list(SSL_CTX *,const char *str) __attribute__((deprecated));
SSL_CTX *SSL_CTX_new(SSL_METHOD *meth) __attribute__((deprecated));
void SSL_CTX_free(SSL_CTX *) __attribute__((deprecated));
long SSL_CTX_set_timeout(SSL_CTX *ctx,long t) __attribute__((deprecated));
long SSL_CTX_get_timeout(const SSL_CTX *ctx) __attribute__((deprecated));
X509_STORE *SSL_CTX_get_cert_store(const SSL_CTX *) __attribute__((deprecated));
void SSL_CTX_set_cert_store(SSL_CTX *,X509_STORE *) __attribute__((deprecated));
int SSL_want(const SSL *s) __attribute__((deprecated));
int SSL_clear(SSL *s) __attribute__((deprecated));

void SSL_CTX_flush_sessions(SSL_CTX *ctx,long tm) __attribute__((deprecated));

SSL_CIPHER *SSL_get_current_cipher(const SSL *s) __attribute__((deprecated));
int SSL_CIPHER_get_bits(const SSL_CIPHER *c,int *alg_bits) __attribute__((deprecated));
char * SSL_CIPHER_get_version(const SSL_CIPHER *c) __attribute__((deprecated));
const char * SSL_CIPHER_get_name(const SSL_CIPHER *c) __attribute__((deprecated));

int SSL_get_fd(const SSL *s) __attribute__((deprecated));
int SSL_get_rfd(const SSL *s) __attribute__((deprecated));
int SSL_get_wfd(const SSL *s) __attribute__((deprecated));
const char * SSL_get_cipher_list(const SSL *s,int n) __attribute__((deprecated));
char * SSL_get_shared_ciphers(const SSL *s, char *buf, int len) __attribute__((deprecated));
int SSL_get_read_ahead(const SSL * s) __attribute__((deprecated));
int SSL_pending(const SSL *s) __attribute__((deprecated));

int SSL_set_fd(SSL *s, int fd) __attribute__((deprecated));
int SSL_set_rfd(SSL *s, int fd) __attribute__((deprecated));
int SSL_set_wfd(SSL *s, int fd) __attribute__((deprecated));


void SSL_set_bio(SSL *s, BIO *rbio,BIO *wbio) __attribute__((deprecated));
BIO * SSL_get_rbio(const SSL *s) __attribute__((deprecated));
BIO * SSL_get_wbio(const SSL *s) __attribute__((deprecated));

int SSL_set_cipher_list(SSL *s, const char *str) __attribute__((deprecated));
void SSL_set_read_ahead(SSL *s, int yes) __attribute__((deprecated));
int SSL_get_verify_mode(const SSL *s) __attribute__((deprecated));
int SSL_get_verify_depth(const SSL *s) __attribute__((deprecated));
int (*SSL_get_verify_callback(const SSL *s))(int,X509_STORE_CTX *) __attribute__((deprecated));
void SSL_set_verify(SSL *s, int mode,
         int (*callback)(int ok,X509_STORE_CTX *ctx)) __attribute__((deprecated));
void SSL_set_verify_depth(SSL *s, int depth) __attribute__((deprecated));

int SSL_use_RSAPrivateKey(SSL *ssl, RSA *rsa) __attribute__((deprecated));

int SSL_use_RSAPrivateKey_ASN1(SSL *ssl, unsigned char *d, long len) __attribute__((deprecated));
int SSL_use_PrivateKey(SSL *ssl, EVP_PKEY *pkey) __attribute__((deprecated));
int SSL_use_PrivateKey_ASN1(int pk,SSL *ssl, const unsigned char *d, long len) __attribute__((deprecated));
int SSL_use_certificate(SSL *ssl, X509 *x) __attribute__((deprecated));
int SSL_use_certificate_ASN1(SSL *ssl, const unsigned char *d, int len) __attribute__((deprecated));


int SSL_use_RSAPrivateKey_file(SSL *ssl, const char *file, int type) __attribute__((deprecated));
int SSL_use_PrivateKey_file(SSL *ssl, const char *file, int type) __attribute__((deprecated));
int SSL_use_certificate_file(SSL *ssl, const char *file, int type) __attribute__((deprecated));
int SSL_CTX_use_RSAPrivateKey_file(SSL_CTX *ctx, const char *file, int type) __attribute__((deprecated));
int SSL_CTX_use_PrivateKey_file(SSL_CTX *ctx, const char *file, int type) __attribute__((deprecated));
int SSL_CTX_use_certificate_file(SSL_CTX *ctx, const char *file, int type) __attribute__((deprecated));
int SSL_CTX_use_certificate_chain_file(SSL_CTX *ctx, const char *file) __attribute__((deprecated));
STACK *SSL_load_client_CA_file(const char *file) __attribute__((deprecated));
int SSL_add_file_cert_subjects_to_stack(STACK *stackCAs,
         const char *file) __attribute__((deprecated));


int SSL_add_dir_cert_subjects_to_stack(STACK *stackCAs,
        const char *dir) __attribute__((deprecated));





void SSL_load_error_strings(void ) __attribute__((deprecated));
const char *SSL_state_string(const SSL *s) __attribute__((deprecated));
const char *SSL_rstate_string(const SSL *s) __attribute__((deprecated));
const char *SSL_state_string_long(const SSL *s) __attribute__((deprecated));
const char *SSL_rstate_string_long(const SSL *s) __attribute__((deprecated));
long SSL_SESSION_get_time(const SSL_SESSION *s) __attribute__((deprecated));
long SSL_SESSION_set_time(SSL_SESSION *s, long t) __attribute__((deprecated));
long SSL_SESSION_get_timeout(const SSL_SESSION *s) __attribute__((deprecated));
long SSL_SESSION_set_timeout(SSL_SESSION *s, long t) __attribute__((deprecated));
void SSL_copy_session_id(SSL *to,const SSL *from) __attribute__((deprecated));

SSL_SESSION *SSL_SESSION_new(void) __attribute__((deprecated));
unsigned long SSL_SESSION_hash(const SSL_SESSION *a) __attribute__((deprecated));
int SSL_SESSION_cmp(const SSL_SESSION *a,const SSL_SESSION *b) __attribute__((deprecated));
const unsigned char *SSL_SESSION_get_id(const SSL_SESSION *s, unsigned int *len) __attribute__((deprecated));

int SSL_SESSION_print_fp(FILE *fp,const SSL_SESSION *ses) __attribute__((deprecated));


int SSL_SESSION_print(BIO *fp,const SSL_SESSION *ses) __attribute__((deprecated));

void SSL_SESSION_free(SSL_SESSION *ses) __attribute__((deprecated));
int i2d_SSL_SESSION(SSL_SESSION *in,unsigned char **pp) __attribute__((deprecated));
int SSL_set_session(SSL *to, SSL_SESSION *session) __attribute__((deprecated));
int SSL_CTX_add_session(SSL_CTX *s, SSL_SESSION *c) __attribute__((deprecated));
int SSL_CTX_remove_session(SSL_CTX *,SSL_SESSION *c) __attribute__((deprecated));
int SSL_CTX_set_generate_session_id(SSL_CTX *, GEN_SESSION_CB) __attribute__((deprecated));
int SSL_set_generate_session_id(SSL *, GEN_SESSION_CB) __attribute__((deprecated));
int SSL_has_matching_session_id(const SSL *ssl, const unsigned char *id,
     unsigned int id_len) __attribute__((deprecated));
SSL_SESSION *d2i_SSL_SESSION(SSL_SESSION **a,const unsigned char **pp,
        long length) __attribute__((deprecated));


X509 * SSL_get_peer_certificate(const SSL *s) __attribute__((deprecated));


STACK *SSL_get_peer_cert_chain(const SSL *s);

int SSL_CTX_get_verify_mode(const SSL_CTX *ctx) __attribute__((deprecated));
int SSL_CTX_get_verify_depth(const SSL_CTX *ctx) __attribute__((deprecated));
int (*SSL_CTX_get_verify_callback(const SSL_CTX *ctx))(int,X509_STORE_CTX *) __attribute__((deprecated));
void SSL_CTX_set_verify(SSL_CTX *ctx,int mode,
   int (*callback)(int, X509_STORE_CTX *)) __attribute__((deprecated));
void SSL_CTX_set_verify_depth(SSL_CTX *ctx,int depth) __attribute__((deprecated));
void SSL_CTX_set_cert_verify_callback(SSL_CTX *ctx, int (*cb)(X509_STORE_CTX *,void *), void *arg) __attribute__((deprecated));

int SSL_CTX_use_RSAPrivateKey(SSL_CTX *ctx, RSA *rsa) __attribute__((deprecated));

int SSL_CTX_use_RSAPrivateKey_ASN1(SSL_CTX *ctx, const unsigned char *d, long len) __attribute__((deprecated));
int SSL_CTX_use_PrivateKey(SSL_CTX *ctx, EVP_PKEY *pkey) __attribute__((deprecated));
int SSL_CTX_use_PrivateKey_ASN1(int pk,SSL_CTX *ctx,
 const unsigned char *d, long len) __attribute__((deprecated));
int SSL_CTX_use_certificate(SSL_CTX *ctx, X509 *x) __attribute__((deprecated));
int SSL_CTX_use_certificate_ASN1(SSL_CTX *ctx, int len, const unsigned char *d) __attribute__((deprecated));

void SSL_CTX_set_default_passwd_cb(SSL_CTX *ctx, pem_password_cb *cb) __attribute__((deprecated));
void SSL_CTX_set_default_passwd_cb_userdata(SSL_CTX *ctx, void *u) __attribute__((deprecated));

int SSL_CTX_check_private_key(const SSL_CTX *ctx) __attribute__((deprecated));
int SSL_check_private_key(const SSL *ctx) __attribute__((deprecated));

int SSL_CTX_set_session_id_context(SSL_CTX *ctx,const unsigned char *sid_ctx,
           unsigned int sid_ctx_len) __attribute__((deprecated));

SSL * SSL_new(SSL_CTX *ctx) __attribute__((deprecated));
int SSL_set_session_id_context(SSL *ssl,const unsigned char *sid_ctx,
       unsigned int sid_ctx_len) __attribute__((deprecated));

int SSL_CTX_set_purpose(SSL_CTX *s, int purpose) __attribute__((deprecated));
int SSL_set_purpose(SSL *s, int purpose) __attribute__((deprecated));
int SSL_CTX_set_trust(SSL_CTX *s, int trust) __attribute__((deprecated));
int SSL_set_trust(SSL *s, int trust) __attribute__((deprecated));

void SSL_free(SSL *ssl) __attribute__((deprecated));
int SSL_accept(SSL *ssl) __attribute__((deprecated));
int SSL_connect(SSL *ssl) __attribute__((deprecated));
int SSL_read(SSL *ssl,void *buf,int num) __attribute__((deprecated));
int SSL_peek(SSL *ssl,void *buf,int num) __attribute__((deprecated));
int SSL_write(SSL *ssl,const void *buf,int num) __attribute__((deprecated));
long SSL_ctrl(SSL *ssl,int cmd, long larg, void *parg) __attribute__((deprecated));
long SSL_callback_ctrl(SSL *, int, void (*)(void)) __attribute__((deprecated));
long SSL_CTX_ctrl(SSL_CTX *ctx,int cmd, long larg, void *parg) __attribute__((deprecated));
long SSL_CTX_callback_ctrl(SSL_CTX *, int, void (*)(void)) __attribute__((deprecated));

int SSL_get_error(const SSL *s,int ret_code) __attribute__((deprecated));
const char *SSL_get_version(const SSL *s) __attribute__((deprecated));


int SSL_CTX_set_ssl_version(SSL_CTX *ctx,SSL_METHOD *meth) __attribute__((deprecated));

SSL_METHOD *SSLv2_method(void) __attribute__((deprecated));
SSL_METHOD *SSLv2_server_method(void) __attribute__((deprecated));
SSL_METHOD *SSLv2_client_method(void) __attribute__((deprecated));

SSL_METHOD *SSLv3_method(void) __attribute__((deprecated));
SSL_METHOD *SSLv3_server_method(void) __attribute__((deprecated));
SSL_METHOD *SSLv3_client_method(void) __attribute__((deprecated));

SSL_METHOD *SSLv23_method(void) __attribute__((deprecated));
SSL_METHOD *SSLv23_server_method(void) __attribute__((deprecated));
SSL_METHOD *SSLv23_client_method(void) __attribute__((deprecated));

SSL_METHOD *TLSv1_method(void) __attribute__((deprecated));
SSL_METHOD *TLSv1_server_method(void) __attribute__((deprecated));
SSL_METHOD *TLSv1_client_method(void) __attribute__((deprecated));

SSL_METHOD *DTLSv1_method(void) __attribute__((deprecated));
SSL_METHOD *DTLSv1_server_method(void) __attribute__((deprecated));
SSL_METHOD *DTLSv1_client_method(void) __attribute__((deprecated));

STACK *SSL_get_ciphers(const SSL *s) __attribute__((deprecated));

int SSL_do_handshake(SSL *s) __attribute__((deprecated));
int SSL_renegotiate(SSL *s) __attribute__((deprecated));
int SSL_renegotiate_pending(SSL *s) __attribute__((deprecated));
int SSL_shutdown(SSL *s) __attribute__((deprecated));

SSL_METHOD *SSL_get_ssl_method(SSL *s) __attribute__((deprecated));
int SSL_set_ssl_method(SSL *s,SSL_METHOD *method) __attribute__((deprecated));
const char *SSL_alert_type_string_long(int value) __attribute__((deprecated));
const char *SSL_alert_type_string(int value) __attribute__((deprecated));
const char *SSL_alert_desc_string_long(int value) __attribute__((deprecated));
const char *SSL_alert_desc_string(int value) __attribute__((deprecated));

void SSL_set_client_CA_list(SSL *s, STACK *name_list) __attribute__((deprecated));
void SSL_CTX_set_client_CA_list(SSL_CTX *ctx, STACK *name_list) __attribute__((deprecated));
STACK *SSL_get_client_CA_list(const SSL *s) __attribute__((deprecated));
STACK *SSL_CTX_get_client_CA_list(const SSL_CTX *s) __attribute__((deprecated));
int SSL_add_client_CA(SSL *ssl,X509 *x) __attribute__((deprecated));
int SSL_CTX_add_client_CA(SSL_CTX *ctx,X509 *x) __attribute__((deprecated));

void SSL_set_connect_state(SSL *s) __attribute__((deprecated));
void SSL_set_accept_state(SSL *s) __attribute__((deprecated));

long SSL_get_default_timeout(const SSL *s) __attribute__((deprecated));

int SSL_library_init(void ) __attribute__((deprecated));

char *SSL_CIPHER_description(const SSL_CIPHER *,char *buf,int size) __attribute__((deprecated));
STACK *SSL_dup_CA_list(STACK *sk) __attribute__((deprecated));

SSL *SSL_dup(SSL *ssl) __attribute__((deprecated));

X509 *SSL_get_certificate(const SSL *ssl) __attribute__((deprecated));
               struct evp_pkey_st *SSL_get_privatekey(SSL *ssl);

void SSL_CTX_set_quiet_shutdown(SSL_CTX *ctx,int mode) __attribute__((deprecated));
int SSL_CTX_get_quiet_shutdown(const SSL_CTX *ctx) __attribute__((deprecated));
void SSL_set_quiet_shutdown(SSL *ssl,int mode) __attribute__((deprecated));
int SSL_get_quiet_shutdown(const SSL *ssl) __attribute__((deprecated));
void SSL_set_shutdown(SSL *ssl,int mode) __attribute__((deprecated));
int SSL_get_shutdown(const SSL *ssl) __attribute__((deprecated));
int SSL_version(const SSL *ssl) __attribute__((deprecated));
int SSL_CTX_set_default_verify_paths(SSL_CTX *ctx) __attribute__((deprecated));
int SSL_CTX_load_verify_locations(SSL_CTX *ctx, const char *CAfile,
 const char *CApath) __attribute__((deprecated));

SSL_SESSION *SSL_get_session(const SSL *ssl) __attribute__((deprecated));
SSL_SESSION *SSL_get1_session(SSL *ssl) __attribute__((deprecated));
SSL_CTX *SSL_get_SSL_CTX(const SSL *ssl) __attribute__((deprecated));
SSL_CTX *SSL_set_SSL_CTX(SSL *ssl, SSL_CTX* ctx) __attribute__((deprecated));
void SSL_set_info_callback(SSL *ssl,
      void (*cb)(const SSL *ssl,int type,int val)) __attribute__((deprecated));
void (*SSL_get_info_callback(const SSL *ssl))(const SSL *ssl,int type,int val) __attribute__((deprecated));
int SSL_state(const SSL *ssl) __attribute__((deprecated));

void SSL_set_verify_result(SSL *ssl,long v) __attribute__((deprecated));
long SSL_get_verify_result(const SSL *ssl) __attribute__((deprecated));

int SSL_set_ex_data(SSL *ssl,int idx,void *data) __attribute__((deprecated));
void *SSL_get_ex_data(const SSL *ssl,int idx) __attribute__((deprecated));
int SSL_get_ex_new_index(long argl, void *argp, CRYPTO_EX_new *new_func,
 CRYPTO_EX_dup *dup_func, CRYPTO_EX_free *free_func) __attribute__((deprecated));

int SSL_SESSION_set_ex_data(SSL_SESSION *ss,int idx,void *data) __attribute__((deprecated));
void *SSL_SESSION_get_ex_data(const SSL_SESSION *ss,int idx) __attribute__((deprecated));
int SSL_SESSION_get_ex_new_index(long argl, void *argp, CRYPTO_EX_new *new_func,
 CRYPTO_EX_dup *dup_func, CRYPTO_EX_free *free_func) __attribute__((deprecated));

int SSL_CTX_set_ex_data(SSL_CTX *ssl,int idx,void *data) __attribute__((deprecated));
void *SSL_CTX_get_ex_data(const SSL_CTX *ssl,int idx) __attribute__((deprecated));
int SSL_CTX_get_ex_new_index(long argl, void *argp, CRYPTO_EX_new *new_func,
 CRYPTO_EX_dup *dup_func, CRYPTO_EX_free *free_func) __attribute__((deprecated));

int SSL_get_ex_data_X509_STORE_CTX_idx(void ) __attribute__((deprecated));
# 1629 "/usr/include/openssl/ssl.h" 3 4
void SSL_CTX_set_tmp_rsa_callback(SSL_CTX *ctx,
      RSA *(*cb)(SSL *ssl,int is_export,
          int keylength)) __attribute__((deprecated));

void SSL_set_tmp_rsa_callback(SSL *ssl,
      RSA *(*cb)(SSL *ssl,int is_export,
          int keylength)) __attribute__((deprecated));


void SSL_CTX_set_tmp_dh_callback(SSL_CTX *ctx,
     DH *(*dh)(SSL *ssl,int is_export,
        int keylength)) __attribute__((deprecated));
void SSL_set_tmp_dh_callback(SSL *ssl,
     DH *(*dh)(SSL *ssl,int is_export,
        int keylength)) __attribute__((deprecated));


void SSL_CTX_set_tmp_ecdh_callback(SSL_CTX *ctx,
     EC_KEY *(*ecdh)(SSL *ssl,int is_export,
        int keylength)) __attribute__((deprecated));
void SSL_set_tmp_ecdh_callback(SSL *ssl,
     EC_KEY *(*ecdh)(SSL *ssl,int is_export,
        int keylength)) __attribute__((deprecated));



const COMP_METHOD *SSL_get_current_compression(SSL *s) __attribute__((deprecated));
const COMP_METHOD *SSL_get_current_expansion(SSL *s) __attribute__((deprecated));
const char *SSL_COMP_get_name(const COMP_METHOD *comp) __attribute__((deprecated));
STACK *SSL_COMP_get_compression_methods(void) __attribute__((deprecated));
int SSL_COMP_add_compression_method(int id,COMP_METHOD *cm) __attribute__((deprecated));
# 1672 "/usr/include/openssl/ssl.h" 3 4
void ERR_load_SSL_strings(void) __attribute__((deprecated));
# 107 "_ssl.c" 2
# 1 "/usr/include/openssl/err.h" 1 3 4
# 64 "/usr/include/openssl/err.h" 3 4
# 1 "/usr/include/openssl/e_os2.h" 1 3 4
# 56 "/usr/include/openssl/e_os2.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 57 "/usr/include/openssl/e_os2.h" 2 3 4
# 65 "/usr/include/openssl/err.h" 2 3 4
# 89 "/usr/include/openssl/err.h" 3 4
# 1 "/usr/include/errno.h" 1 3 4
# 90 "/usr/include/openssl/err.h" 2 3 4







typedef struct err_state_st
 {
 unsigned long pid;
 int err_flags[16];
 unsigned long err_buffer[16];
 char *err_data[16];
 int err_data_flags[16];
 const char *err_file[16];
 int err_line[16];
 int top,bottom;
 } ERR_STATE;
# 257 "/usr/include/openssl/err.h" 3 4
typedef struct ERR_string_data_st
 {
 unsigned long error;
 const char *string;
 } ERR_STRING_DATA;

void ERR_put_error(int lib, int func,int reason,const char *file,int line) __attribute__((deprecated));
void ERR_set_error_data(char *data,int flags) __attribute__((deprecated));

unsigned long ERR_get_error(void) __attribute__((deprecated));
unsigned long ERR_get_error_line(const char **file,int *line) __attribute__((deprecated));
unsigned long ERR_get_error_line_data(const char **file,int *line,
          const char **data, int *flags) __attribute__((deprecated));
unsigned long ERR_peek_error(void) __attribute__((deprecated));
unsigned long ERR_peek_error_line(const char **file,int *line) __attribute__((deprecated));
unsigned long ERR_peek_error_line_data(const char **file,int *line,
           const char **data,int *flags) __attribute__((deprecated));
unsigned long ERR_peek_last_error(void) __attribute__((deprecated));
unsigned long ERR_peek_last_error_line(const char **file,int *line) __attribute__((deprecated));
unsigned long ERR_peek_last_error_line_data(const char **file,int *line,
           const char **data,int *flags) __attribute__((deprecated));
void ERR_clear_error(void ) __attribute__((deprecated));
char *ERR_error_string(unsigned long e,char *buf) __attribute__((deprecated));
void ERR_error_string_n(unsigned long e, char *buf, size_t len) __attribute__((deprecated));
const char *ERR_lib_error_string(unsigned long e) __attribute__((deprecated));
const char *ERR_func_error_string(unsigned long e) __attribute__((deprecated));
const char *ERR_reason_error_string(unsigned long e) __attribute__((deprecated));
void ERR_print_errors_cb(int (*cb)(const char *str, size_t len, void *u),
    void *u) __attribute__((deprecated));

void ERR_print_errors_fp(FILE *fp) __attribute__((deprecated));


void ERR_print_errors(BIO *bp) __attribute__((deprecated));
void ERR_add_error_data(int num, ...) __attribute__((deprecated));

void ERR_load_strings(int lib,ERR_STRING_DATA str[]) __attribute__((deprecated));
void ERR_unload_strings(int lib,ERR_STRING_DATA str[]) __attribute__((deprecated));
void ERR_load_ERR_strings(void) __attribute__((deprecated));
void ERR_load_crypto_strings(void) __attribute__((deprecated));
void ERR_free_strings(void) __attribute__((deprecated));

void ERR_remove_state(unsigned long pid) __attribute__((deprecated));
ERR_STATE *ERR_get_state(void) __attribute__((deprecated));


LHASH *ERR_get_string_table(void) __attribute__((deprecated));
LHASH *ERR_get_err_state_table(void) __attribute__((deprecated));
void ERR_release_err_state_table(LHASH **hash) __attribute__((deprecated));


int ERR_get_next_error_library(void) __attribute__((deprecated));

int ERR_set_mark(void) __attribute__((deprecated));
int ERR_pop_to_mark(void) __attribute__((deprecated));
# 323 "/usr/include/openssl/err.h" 3 4
const ERR_FNS *ERR_get_implementation(void) __attribute__((deprecated));


int ERR_set_implementation(const ERR_FNS *fns) __attribute__((deprecated));
# 108 "_ssl.c" 2
# 1 "/usr/include/openssl/rand.h" 1 3 4
# 66 "/usr/include/openssl/rand.h" 3 4
# 1 "/usr/include/openssl/e_os2.h" 1 3 4
# 56 "/usr/include/openssl/e_os2.h" 3 4
# 1 "/usr/include/openssl/opensslconf.h" 1 3 4
# 57 "/usr/include/openssl/e_os2.h" 2 3 4
# 67 "/usr/include/openssl/rand.h" 2 3 4
# 83 "/usr/include/openssl/rand.h" 3 4
struct rand_meth_st
 {
 void (*seed)(const void *buf, int num);
 int (*bytes)(unsigned char *buf, int num);
 void (*cleanup)(void);
 void (*add)(const void *buf, int num, double entropy);
 int (*pseudorand)(unsigned char *buf, int num);
 int (*status)(void);
 };





int RAND_set_rand_method(const RAND_METHOD *meth) __attribute__((deprecated));
const RAND_METHOD *RAND_get_rand_method(void) __attribute__((deprecated));

int RAND_set_rand_engine(ENGINE *engine) __attribute__((deprecated));

RAND_METHOD *RAND_SSLeay(void) __attribute__((deprecated));
void RAND_cleanup(void ) __attribute__((deprecated));
int RAND_bytes(unsigned char *buf,int num) __attribute__((deprecated));
int RAND_pseudo_bytes(unsigned char *buf,int num) __attribute__((deprecated));
void RAND_seed(const void *buf,int num) __attribute__((deprecated));
void RAND_add(const void *buf,int num,double entropy) __attribute__((deprecated));
int RAND_load_file(const char *file,long max_bytes) __attribute__((deprecated));
int RAND_write_file(const char *file) __attribute__((deprecated));
const char *RAND_file_name(char *file,size_t num) __attribute__((deprecated));
int RAND_status(void) __attribute__((deprecated));
int RAND_query_egd_bytes(const char *path, unsigned char *buf, int bytes) __attribute__((deprecated));
int RAND_egd(const char *path) __attribute__((deprecated));
int RAND_egd_bytes(const char *path,int bytes) __attribute__((deprecated));
int RAND_poll(void) __attribute__((deprecated));
# 137 "/usr/include/openssl/rand.h" 3 4
void ERR_load_RAND_strings(void) __attribute__((deprecated));
# 109 "_ssl.c" 2


# 1 "_ssl_data.h" 1



static struct py_ssl_library_code library_codes[] = {
    {"PEM", 9},
    {"SSL", 20},
    {"X509", 11},
    { ((void *)0) }
};

static struct py_ssl_error_code error_codes[] = {

    {"BAD_BASE64_DECODE", 9, 100},




    {"BAD_DECRYPT", 9, 101},




    {"BAD_END_LINE", 9, 102},




    {"BAD_IV_CHARS", 9, 103},






    {"BAD_MAGIC_NUMBER", 9, 116},


    {"BAD_PASSWORD_READ", 9, 104},






    {"BAD_VERSION_NUMBER", 9, 117},




    {"BIO_WRITE_FAILURE", 9, 118},




    {"CIPHER_IS_NULL", 9, 127},


    {"ERROR_CONVERTING_PRIVATE_KEY", 9, 115},






    {"EXPECTING_PRIVATE_KEY_BLOB", 9, 119},




    {"EXPECTING_PUBLIC_KEY_BLOB", 9, 120},




    {"INCONSISTENT_HEADER", 9, 121},




    {"KEYBLOB_HEADER_PARSE_ERROR", 9, 122},




    {"KEYBLOB_TOO_SHORT", 9, 123},


    {"NOT_DEK_INFO", 9, 105},




    {"NOT_ENCRYPTED", 9, 106},




    {"NOT_PROC_TYPE", 9, 107},




    {"NO_START_LINE", 9, 108},




    {"PROBLEMS_GETTING_PASSWORD", 9, 109},




    {"PUBLIC_KEY_NO_RSA", 9, 110},






    {"PVK_DATA_TOO_SHORT", 9, 124},




    {"PVK_TOO_SHORT", 9, 125},


    {"READ_KEY", 9, 111},




    {"SHORT_HEADER", 9, 112},




    {"UNSUPPORTED_CIPHER", 9, 113},




    {"UNSUPPORTED_ENCRYPTION", 9, 114},






    {"UNSUPPORTED_KEY_COMPONENTS", 9, 126},


    {"APP_DATA_IN_HANDSHAKE", 20, 100},




    {"ATTEMPT_TO_REUSE_SESSION_IN_DIFFERENT_CONTEXT", 20, 272},




    {"BAD_ALERT_RECORD", 20, 101},




    {"BAD_AUTHENTICATION_TYPE", 20, 102},




    {"BAD_CHANGE_CIPHER_SPEC", 20, 103},




    {"BAD_CHECKSUM", 20, 104},




    {"BAD_DATA_RETURNED_BY_CALLBACK", 20, 106},




    {"BAD_DECOMPRESSION", 20, 107},




    {"BAD_DH_G_LENGTH", 20, 108},




    {"BAD_DH_PUB_KEY_LENGTH", 20, 109},




    {"BAD_DH_P_LENGTH", 20, 110},




    {"BAD_DIGEST_LENGTH", 20, 111},




    {"BAD_DSA_SIGNATURE", 20, 112},




    {"BAD_ECC_CERT", 20, 304},




    {"BAD_ECDSA_SIGNATURE", 20, 305},




    {"BAD_ECPOINT", 20, 306},






    {"BAD_HANDSHAKE_LENGTH", 20, 332},


    {"BAD_HELLO_REQUEST", 20, 105},




    {"BAD_LENGTH", 20, 271},




    {"BAD_MAC_DECODE", 20, 113},






    {"BAD_MAC_LENGTH", 20, 333},


    {"BAD_MESSAGE_TYPE", 20, 114},




    {"BAD_PACKET_LENGTH", 20, 115},




    {"BAD_PROTOCOL_VERSION_NUMBER", 20, 116},






    {"BAD_PSK_IDENTITY_HINT_LENGTH", 20, 316},


    {"BAD_RESPONSE_ARGUMENT", 20, 117},




    {"BAD_RSA_DECRYPT", 20, 118},




    {"BAD_RSA_ENCRYPT", 20, 119},




    {"BAD_RSA_E_LENGTH", 20, 120},




    {"BAD_RSA_MODULUS_LENGTH", 20, 121},




    {"BAD_RSA_SIGNATURE", 20, 122},




    {"BAD_SIGNATURE", 20, 123},




    {"BAD_SSL_FILETYPE", 20, 124},




    {"BAD_SSL_SESSION_ID_LENGTH", 20, 125},




    {"BAD_STATE", 20, 126},




    {"BAD_WRITE_RETRY", 20, 127},




    {"BIO_NOT_SET", 20, 128},




    {"BLOCK_CIPHER_PAD_IS_WRONG", 20, 129},




    {"BN_LIB", 20, 130},




    {"CA_DN_LENGTH_MISMATCH", 20, 131},




    {"CA_DN_TOO_LONG", 20, 132},




    {"CCS_RECEIVED_EARLY", 20, 133},




    {"CERTIFICATE_VERIFY_FAILED", 20, 134},




    {"CERT_LENGTH_MISMATCH", 20, 135},




    {"CHALLENGE_IS_DIFFERENT", 20, 136},




    {"CIPHER_CODE_WRONG_LENGTH", 20, 137},




    {"CIPHER_OR_HASH_UNAVAILABLE", 20, 138},




    {"CIPHER_TABLE_SRC_ERROR", 20, 139},




    {"CLIENTHELLO_TLSEXT", 20, 157},




    {"COMPRESSED_LENGTH_TOO_LONG", 20, 140},






    {"COMPRESSION_DISABLED", 20, 343},


    {"COMPRESSION_FAILURE", 20, 141},




    {"COMPRESSION_ID_NOT_WITHIN_PRIVATE_RANGE", 20, 307},




    {"COMPRESSION_LIBRARY_ERROR", 20, 142},




    {"CONNECTION_ID_IS_DIFFERENT", 20, 143},




    {"CONNECTION_TYPE_NOT_SET", 20, 144},




    {"COOKIE_MISMATCH", 20, 308},




    {"DATA_BETWEEN_CCS_AND_FINISHED", 20, 145},




    {"DATA_LENGTH_TOO_LONG", 20, 146},




    {"DECRYPTION_FAILED", 20, 147},




    {"DECRYPTION_FAILED_OR_BAD_RECORD_MAC", 20, 281},




    {"DH_PUBLIC_VALUE_LENGTH_IS_WRONG", 20, 148},




    {"DIGEST_CHECK_FAILED", 20, 149},




    {"DTLS_MESSAGE_TOO_BIG", 20, 318},




    {"DUPLICATE_COMPRESSION_ID", 20, 309},






    {"ECC_CERT_NOT_FOR_KEY_AGREEMENT", 20, 317},




    {"ECC_CERT_NOT_FOR_SIGNING", 20, 318},




    {"ECC_CERT_SHOULD_HAVE_RSA_SIGNATURE", 20, 322},




    {"ECC_CERT_SHOULD_HAVE_SHA1_SIGNATURE", 20, 323},


    {"ECGROUP_TOO_LARGE_FOR_CIPHER", 20, 310},




    {"ENCRYPTED_LENGTH_TOO_LONG", 20, 150},




    {"ERROR_GENERATING_TMP_RSA_KEY", 20, 282},




    {"ERROR_IN_RECEIVED_CIPHER_LIST", 20, 151},




    {"EXCESSIVE_MESSAGE_SIZE", 20, 152},




    {"EXTRA_DATA_IN_MESSAGE", 20, 153},




    {"GOT_A_FIN_BEFORE_A_CCS", 20, 154},




    {"HTTPS_PROXY_REQUEST", 20, 155},




    {"HTTP_REQUEST", 20, 156},




    {"ILLEGAL_PADDING", 20, 283},






    {"INCONSISTENT_COMPRESSION", 20, 340},


    {"INVALID_CHALLENGE_LENGTH", 20, 158},




    {"INVALID_COMMAND", 20, 280},






    {"INVALID_COMPRESSION_ALGORITHM", 20, 341},


    {"INVALID_PURPOSE", 20, 278},




    {"INVALID_STATUS_RESPONSE", 20, 316},




    {"INVALID_TICKET_KEYS_LENGTH", 20, 275},




    {"INVALID_TRUST", 20, 279},




    {"KEY_ARG_TOO_LONG", 20, 284},




    {"KRB5", 20, 285},




    {"KRB5_C_CC_PRINC", 20, 286},




    {"KRB5_C_GET_CRED", 20, 287},




    {"KRB5_C_INIT", 20, 288},




    {"KRB5_C_MK_REQ", 20, 289},




    {"KRB5_S_BAD_TICKET", 20, 290},




    {"KRB5_S_INIT", 20, 291},




    {"KRB5_S_RD_REQ", 20, 292},




    {"KRB5_S_TKT_EXPIRED", 20, 293},




    {"KRB5_S_TKT_NYV", 20, 294},




    {"KRB5_S_TKT_SKEW", 20, 295},




    {"LENGTH_MISMATCH", 20, 159},




    {"LENGTH_TOO_SHORT", 20, 160},




    {"LIBRARY_BUG", 20, 274},




    {"LIBRARY_HAS_NO_CIPHERS", 20, 161},




    {"MESSAGE_TOO_LONG", 20, 296},




    {"MISSING_DH_DSA_CERT", 20, 162},




    {"MISSING_DH_KEY", 20, 163},




    {"MISSING_DH_RSA_CERT", 20, 164},




    {"MISSING_DSA_SIGNING_CERT", 20, 165},




    {"MISSING_EXPORT_TMP_DH_KEY", 20, 166},




    {"MISSING_EXPORT_TMP_RSA_KEY", 20, 167},




    {"MISSING_RSA_CERTIFICATE", 20, 168},




    {"MISSING_RSA_ENCRYPTING_CERT", 20, 169},




    {"MISSING_RSA_SIGNING_CERT", 20, 170},




    {"MISSING_TMP_DH_KEY", 20, 171},




    {"MISSING_TMP_ECDH_KEY", 20, 311},




    {"MISSING_TMP_RSA_KEY", 20, 172},




    {"MISSING_TMP_RSA_PKEY", 20, 173},




    {"MISSING_VERIFY_MESSAGE", 20, 174},




    {"NON_SSLV2_INITIAL_PACKET", 20, 175},




    {"NO_CERTIFICATES_RETURNED", 20, 176},




    {"NO_CERTIFICATE_ASSIGNED", 20, 177},




    {"NO_CERTIFICATE_RETURNED", 20, 178},




    {"NO_CERTIFICATE_SET", 20, 179},




    {"NO_CERTIFICATE_SPECIFIED", 20, 180},




    {"NO_CIPHERS_AVAILABLE", 20, 181},




    {"NO_CIPHERS_PASSED", 20, 182},




    {"NO_CIPHERS_SPECIFIED", 20, 183},




    {"NO_CIPHER_LIST", 20, 184},




    {"NO_CIPHER_MATCH", 20, 185},




    {"NO_CLIENT_CERT_METHOD", 20, 317},




    {"NO_CLIENT_CERT_RECEIVED", 20, 186},




    {"NO_COMPRESSION_SPECIFIED", 20, 187},






    {"NO_GOST_CERTIFICATE_SENT_BY_PEER", 20, 330},


    {"NO_METHOD_SPECIFIED", 20, 188},




    {"NO_PRIVATEKEY", 20, 189},




    {"NO_PRIVATE_KEY_ASSIGNED", 20, 190},




    {"NO_PROTOCOLS_AVAILABLE", 20, 191},




    {"NO_PUBLICKEY", 20, 192},




    {"NO_RENEGOTIATION", 20, 319},






    {"NO_REQUIRED_DIGEST", 20, 324},


    {"NO_SHARED_CIPHER", 20, 193},




    {"NO_VERIFY_CALLBACK", 20, 194},




    {"NULL_SSL_CTX", 20, 195},




    {"NULL_SSL_METHOD_PASSED", 20, 196},




    {"OLD_SESSION_CIPHER_NOT_RETURNED", 20, 197},






    {"OLD_SESSION_COMPRESSION_ALGORITHM_NOT_RETURNED", 20, 344},


    {"ONLY_TLS_ALLOWED_IN_FIPS_MODE", 20, 297},






    {"OPAQUE_PRF_INPUT_TOO_LONG", 20, 327},


    {"PACKET_LENGTH_TOO_LONG", 20, 198},




    {"PARSE_TLSEXT", 20, 223},




    {"PATH_TOO_LONG", 20, 270},




    {"PEER_DID_NOT_RETURN_A_CERTIFICATE", 20, 199},




    {"PEER_ERROR", 20, 200},




    {"PEER_ERROR_CERTIFICATE", 20, 201},




    {"PEER_ERROR_NO_CERTIFICATE", 20, 202},




    {"PEER_ERROR_NO_CIPHER", 20, 203},




    {"PEER_ERROR_UNSUPPORTED_CERTIFICATE_TYPE", 20, 204},




    {"PRE_MAC_LENGTH_TOO_LONG", 20, 205},




    {"PROBLEMS_MAPPING_CIPHER_FUNCTIONS", 20, 206},




    {"PROTOCOL_IS_SHUTDOWN", 20, 207},






    {"PSK_IDENTITY_NOT_FOUND", 20, 223},




    {"PSK_NO_CLIENT_CB", 20, 224},




    {"PSK_NO_SERVER_CB", 20, 225},


    {"PUBLIC_KEY_ENCRYPT_ERROR", 20, 208},




    {"PUBLIC_KEY_IS_NOT_RSA", 20, 209},




    {"PUBLIC_KEY_NOT_RSA", 20, 210},




    {"READ_BIO_NOT_SET", 20, 211},




    {"READ_TIMEOUT_EXPIRED", 20, 312},




    {"READ_WRONG_PACKET_TYPE", 20, 212},




    {"RECORD_LENGTH_MISMATCH", 20, 213},




    {"RECORD_TOO_LARGE", 20, 214},




    {"RECORD_TOO_SMALL", 20, 298},




    {"RENEGOTIATE_EXT_TOO_LONG", 20, 320},




    {"RENEGOTIATION_ENCODING_ERR", 20, 321},




    {"RENEGOTIATION_MISMATCH", 20, 322},




    {"REQUIRED_CIPHER_MISSING", 20, 215},






    {"REQUIRED_COMPRESSSION_ALGORITHM_MISSING", 20, 342},


    {"REUSE_CERT_LENGTH_NOT_ZERO", 20, 216},




    {"REUSE_CERT_TYPE_NOT_ZERO", 20, 217},




    {"REUSE_CIPHER_LIST_NOT_ZERO", 20, 218},




    {"SCSV_RECEIVED_WHEN_RENEGOTIATING", 20, 324},




    {"SERVERHELLO_TLSEXT", 20, 224},




    {"SESSION_ID_CONTEXT_UNINITIALIZED", 20, 277},




    {"SHORT_READ", 20, 219},




    {"SIGNATURE_FOR_NON_SIGNING_CERTIFICATE", 20, 220},




    {"SSL23_DOING_SESSION_ID_REUSE", 20, 221},




    {"SSL2_CONNECTION_ID_TOO_LONG", 20, 299},






    {"SSL3_EXT_INVALID_ECPOINTFORMAT", 20, 321},


    {"SSL3_EXT_INVALID_SERVERNAME", 20, 225},




    {"SSL3_EXT_INVALID_SERVERNAME_TYPE", 20, 226},




    {"SSL3_SESSION_ID_TOO_LONG", 20, 300},




    {"SSL3_SESSION_ID_TOO_SHORT", 20, 222},




    {"SSLV3_ALERT_BAD_CERTIFICATE", 20, 1042},




    {"SSLV3_ALERT_BAD_RECORD_MAC", 20, 1020},




    {"SSLV3_ALERT_CERTIFICATE_EXPIRED", 20, 1045},




    {"SSLV3_ALERT_CERTIFICATE_REVOKED", 20, 1044},




    {"SSLV3_ALERT_CERTIFICATE_UNKNOWN", 20, 1046},




    {"SSLV3_ALERT_DECOMPRESSION_FAILURE", 20, 1030},




    {"SSLV3_ALERT_HANDSHAKE_FAILURE", 20, 1040},




    {"SSLV3_ALERT_ILLEGAL_PARAMETER", 20, 1047},




    {"SSLV3_ALERT_NO_CERTIFICATE", 20, 1041},




    {"SSLV3_ALERT_UNEXPECTED_MESSAGE", 20, 1010},




    {"SSLV3_ALERT_UNSUPPORTED_CERTIFICATE", 20, 1043},




    {"SSL_CTX_HAS_NO_DEFAULT_SSL_VERSION", 20, 228},




    {"SSL_HANDSHAKE_FAILURE", 20, 229},




    {"SSL_LIBRARY_HAS_NO_CIPHERS", 20, 230},




    {"SSL_SESSION_ID_CALLBACK_FAILED", 20, 301},




    {"SSL_SESSION_ID_CONFLICT", 20, 302},




    {"SSL_SESSION_ID_CONTEXT_TOO_LONG", 20, 273},




    {"SSL_SESSION_ID_HAS_BAD_LENGTH", 20, 303},




    {"SSL_SESSION_ID_IS_DIFFERENT", 20, 231},




    {"TLSV1_ALERT_ACCESS_DENIED", 20, 1049},




    {"TLSV1_ALERT_DECODE_ERROR", 20, 1050},




    {"TLSV1_ALERT_DECRYPTION_FAILED", 20, 1021},




    {"TLSV1_ALERT_DECRYPT_ERROR", 20, 1051},




    {"TLSV1_ALERT_EXPORT_RESTRICTION", 20, 1060},




    {"TLSV1_ALERT_INSUFFICIENT_SECURITY", 20, 1071},




    {"TLSV1_ALERT_INTERNAL_ERROR", 20, 1080},




    {"TLSV1_ALERT_NO_RENEGOTIATION", 20, 1100},




    {"TLSV1_ALERT_PROTOCOL_VERSION", 20, 1070},




    {"TLSV1_ALERT_RECORD_OVERFLOW", 20, 1022},




    {"TLSV1_ALERT_UNKNOWN_CA", 20, 1048},




    {"TLSV1_ALERT_USER_CANCELLED", 20, 1090},






    {"TLSV1_BAD_CERTIFICATE_HASH_VALUE", 20, 1114},




    {"TLSV1_BAD_CERTIFICATE_STATUS_RESPONSE", 20, 1113},




    {"TLSV1_CERTIFICATE_UNOBTAINABLE", 20, 1111},




    {"TLSV1_UNRECOGNIZED_NAME", 20, 1112},




    {"TLSV1_UNSUPPORTED_EXTENSION", 20, 1110},


    {"TLS_CLIENT_CERT_REQ_WITH_ANON_CIPHER", 20, 232},




    {"TLS_INVALID_ECPOINTFORMAT_LIST", 20, 227},




    {"TLS_PEER_DID_NOT_RESPOND_WITH_CERTIFICATE_LIST", 20, 233},




    {"TLS_RSA_ENCRYPTED_VALUE_LENGTH_IS_WRONG", 20, 234},




    {"TRIED_TO_USE_UNSUPPORTED_CIPHER", 20, 235},




    {"UNABLE_TO_DECODE_DH_CERTS", 20, 236},




    {"UNABLE_TO_DECODE_ECDH_CERTS", 20, 313},




    {"UNABLE_TO_EXTRACT_PUBLIC_KEY", 20, 237},




    {"UNABLE_TO_FIND_DH_PARAMETERS", 20, 238},




    {"UNABLE_TO_FIND_ECDH_PARAMETERS", 20, 314},




    {"UNABLE_TO_FIND_PUBLIC_KEY_PARAMETERS", 20, 239},




    {"UNABLE_TO_FIND_SSL_METHOD", 20, 240},




    {"UNABLE_TO_LOAD_SSL2_MD5_ROUTINES", 20, 241},




    {"UNABLE_TO_LOAD_SSL3_MD5_ROUTINES", 20, 242},




    {"UNABLE_TO_LOAD_SSL3_SHA1_ROUTINES", 20, 243},




    {"UNEXPECTED_MESSAGE", 20, 244},




    {"UNEXPECTED_RECORD", 20, 245},




    {"UNINITIALIZED", 20, 276},




    {"UNKNOWN_ALERT_TYPE", 20, 246},




    {"UNKNOWN_CERTIFICATE_TYPE", 20, 247},




    {"UNKNOWN_CIPHER_RETURNED", 20, 248},




    {"UNKNOWN_CIPHER_TYPE", 20, 249},




    {"UNKNOWN_KEY_EXCHANGE_TYPE", 20, 250},




    {"UNKNOWN_PKEY_TYPE", 20, 251},




    {"UNKNOWN_PROTOCOL", 20, 252},




    {"UNKNOWN_REMOTE_ERROR_TYPE", 20, 253},




    {"UNKNOWN_SSL_VERSION", 20, 254},




    {"UNKNOWN_STATE", 20, 255},




    {"UNSAFE_LEGACY_RENEGOTIATION_DISABLED", 20, 323},




    {"UNSUPPORTED_CIPHER", 20, 256},




    {"UNSUPPORTED_COMPRESSION_ALGORITHM", 20, 257},






    {"UNSUPPORTED_DIGEST_TYPE", 20, 326},


    {"UNSUPPORTED_ELLIPTIC_CURVE", 20, 315},




    {"UNSUPPORTED_PROTOCOL", 20, 258},




    {"UNSUPPORTED_SSL_VERSION", 20, 259},




    {"UNSUPPORTED_STATUS_TYPE", 20, 329},




    {"WRITE_BIO_NOT_SET", 20, 260},




    {"WRONG_CIPHER_RETURNED", 20, 261},




    {"WRONG_MESSAGE_TYPE", 20, 262},




    {"WRONG_NUMBER_OF_KEY_BITS", 20, 263},




    {"WRONG_SIGNATURE_LENGTH", 20, 264},




    {"WRONG_SIGNATURE_SIZE", 20, 265},




    {"WRONG_SSL_VERSION", 20, 266},




    {"WRONG_VERSION_NUMBER", 20, 267},




    {"X509_LIB", 20, 268},




    {"X509_VERIFICATION_SETUP_PROBLEMS", 20, 269},




    {"BAD_X509_FILETYPE", 11, 100},




    {"BASE64_DECODE_ERROR", 11, 118},




    {"CANT_CHECK_DH_KEY", 11, 114},




    {"CERT_ALREADY_IN_HASH_TABLE", 11, 101},




    {"ERR_ASN1_LIB", 11, 102},




    {"INVALID_DIRECTORY", 11, 113},




    {"INVALID_FIELD_NAME", 11, 119},




    {"INVALID_TRUST", 11, 123},




    {"KEY_TYPE_MISMATCH", 11, 115},




    {"KEY_VALUES_MISMATCH", 11, 116},




    {"LOADING_CERT_DIR", 11, 103},




    {"LOADING_DEFAULTS", 11, 104},






    {"METHOD_NOT_SUPPORTED", 11, 124},


    {"NO_CERT_SET_FOR_US_TO_VERIFY", 11, 105},






    {"PUBLIC_KEY_DECODE_ERROR", 11, 125},




    {"PUBLIC_KEY_ENCODE_ERROR", 11, 126},


    {"SHOULD_RETRY", 11, 106},




    {"UNABLE_TO_FIND_PARAMETERS_IN_CHAIN", 11, 107},




    {"UNABLE_TO_GET_CERTS_PUBLIC_KEY", 11, 108},




    {"UNKNOWN_KEY_TYPE", 11, 117},




    {"UNKNOWN_NID", 11, 109},




    {"UNKNOWN_PURPOSE_ID", 11, 121},




    {"UNKNOWN_TRUST_ID", 11, 120},




    {"UNSUPPORTED_ALGORITHM", 11, 111},




    {"WRONG_LOOKUP_TYPE", 11, 112},




    {"WRONG_TYPE", 11, 122},



    { ((void *)0) }
};
# 112 "_ssl.c" 2


static PyObject *PySSLErrorObject;
static PyObject *PySSLZeroReturnErrorObject;
static PyObject *PySSLWantReadErrorObject;
static PyObject *PySSLWantWriteErrorObject;
static PyObject *PySSLSyscallErrorObject;
static PyObject *PySSLEOFErrorObject;


static PyObject *err_codes_to_names;
static PyObject *err_names_to_codes;
static PyObject *lib_codes_to_names;






static unsigned int _ssl_locks_count = 0;
# 177 "_ssl.c"
typedef struct {
    PyObject ob_base;
    SSL_CTX *ctx;




} PySSLContext;

typedef struct {
    PyObject ob_base;
    PyObject *Socket;
    SSL *ssl;
    X509 *peer_cert;
    int shutdown_seen_zero;
    enum py_ssl_server_or_client socket_type;
} PySSLSocket;

static PyTypeObject PySSLContext_Type;
static PyTypeObject PySSLSocket_Type;

static PyObject *PySSL_SSLwrite(PySSLSocket *self, PyObject *args);
static PyObject *PySSL_SSLread(PySSLSocket *self, PyObject *args);
static int check_socket_and_wait_for_timeout(PySocketSockObject *s,
                                             int writing);
static PyObject *PySSL_peercert(PySSLSocket *self, PyObject *args);
static PyObject *PySSL_cipher(PySSLSocket *self);




typedef enum {
    SOCKET_IS_NONBLOCKING,
    SOCKET_IS_BLOCKING,
    SOCKET_HAS_TIMED_OUT,
    SOCKET_HAS_BEEN_CLOSED,
    SOCKET_TOO_LARGE_FOR_SELECT,
    SOCKET_OPERATION_OK
} timeout_state;
# 228 "_ssl.c"
static char SSLError_doc[] = "An error occurred in the SSL implementation.";


static char SSLZeroReturnError_doc[] = "SSL/TLS session closed cleanly.";


static char SSLWantReadError_doc[] = "Non-blocking SSL socket needs to read more data\n" "before the requested operation can be completed.";



static char SSLWantWriteError_doc[] = "Non-blocking SSL socket needs to write more data\n" "before the requested operation can be completed.";



static char SSLSyscallError_doc[] = "System error when attempting SSL operation.";


static char SSLEOFError_doc[] = "SSL/TLS connection terminated abruptly.";


static PyObject *
SSLError_str(PyOSErrorObject *self)
{
    if (self->strerror != ((void *)0) && ((((((PyObject*)(self->strerror))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        ( ((PyObject*)(self->strerror))->ob_refcnt++);
        return self->strerror;
    }
    else
        return PyObject_Str(self->args);
}

static PyType_Slot sslerror_type_slots[] = {
    {48, ((void *)0)},
    {56, SSLError_doc},
    {70, SSLError_str},
    {0, 0},
};

static PyType_Spec sslerror_type_spec = {
    "ssl.SSLError",
    sizeof(PyOSErrorObject),
    0,
    ( 0 | (1L<<18) | 0) | (1L<<10),
    sslerror_type_slots
};

static void
fill_and_set_sslerror(PyObject *type, int ssl_errno, const char *errstr,
                      int lineno, unsigned long errcode)
{
    PyObject *err_value = ((void *)0), *reason_obj = ((void *)0), *lib_obj = ((void *)0);
    PyObject *init_value, *msg, *key;
    static _Py_Identifier PyId_reason = { 0, "reason", 0 };
    static _Py_Identifier PyId_library = { 0, "library", 0 };

    if (errcode != 0) {
        int lib, reason;

        lib = (int)((((unsigned long)errcode)>>24L)&0xffL);
        reason = (int)((errcode)&0xfffL);
        key = Py_BuildValue("ii", lib, reason);
        if (key == ((void *)0))
            goto fail;
        reason_obj = PyDict_GetItem(err_codes_to_names, key);
        do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
        if (reason_obj == ((void *)0)) {

            PyErr_Clear();
        }
        key = PyLong_FromLong(lib);
        if (key == ((void *)0))
            goto fail;
        lib_obj = PyDict_GetItem(lib_codes_to_names, key);
        do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
        if (lib_obj == ((void *)0)) {
            PyErr_Clear();
        }
        if (errstr == ((void *)0))
            errstr = ERR_reason_error_string(errcode);
    }
    if (errstr == ((void *)0))
        errstr = "unknown error";

    if (reason_obj && lib_obj)
        msg = PyUnicode_FromFormat("[%S: %S] %s (_ssl.c:%d)",
                                   lib_obj, reason_obj, errstr, lineno);
    else if (lib_obj)
        msg = PyUnicode_FromFormat("[%S] %s (_ssl.c:%d)",
                                   lib_obj, errstr, lineno);
    else
        msg = PyUnicode_FromFormat("%s (_ssl.c:%d)", errstr, lineno);

    if (msg == ((void *)0))
        goto fail;
    init_value = Py_BuildValue("iN", ssl_errno, msg);
    err_value = PyObject_CallObject(type, init_value);
    do { if ( --((PyObject*)(init_value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(init_value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(init_value)))); } while (0);
    if (err_value == ((void *)0))
        goto fail;
    if (reason_obj == ((void *)0))
        reason_obj = (&_Py_NoneStruct);
    if (_PyObject_SetAttrId(err_value, &PyId_reason, reason_obj))
        goto fail;
    if (lib_obj == ((void *)0))
        lib_obj = (&_Py_NoneStruct);
    if (_PyObject_SetAttrId(err_value, &PyId_library, lib_obj))
        goto fail;
    PyErr_SetObject(type, err_value);
fail:
    do { if ((err_value) == ((void *)0)) ; else do { if ( --((PyObject*)(err_value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(err_value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(err_value)))); } while (0); } while (0);
}

static PyObject *
PySSL_SetError(PySSLSocket *obj, int ret, char *filename, int lineno)
{
    PyObject *type = PySSLErrorObject;
    char *errstr = ((void *)0);
    int err;
    enum py_ssl_error p = PY_SSL_ERROR_NONE;
    unsigned long e = 0;

    (__builtin_expect(!(ret <= 0), 0) ? __assert_rtn(__func__, "_ssl.c", 349, "ret <= 0") : (void)0);
    e = ERR_peek_last_error();

    if (obj->ssl != ((void *)0)) {
        err = SSL_get_error(obj->ssl, ret);

        switch (err) {
        case 6:
            errstr = "TLS/SSL connection has been closed (EOF)";
            type = PySSLZeroReturnErrorObject;
            p = PY_SSL_ERROR_ZERO_RETURN;
            break;
        case 2:
            errstr = "The operation did not complete (read)";
            type = PySSLWantReadErrorObject;
            p = PY_SSL_ERROR_WANT_READ;
            break;
        case 3:
            p = PY_SSL_ERROR_WANT_WRITE;
            type = PySSLWantWriteErrorObject;
            errstr = "The operation did not complete (write)";
            break;
        case 4:
            p = PY_SSL_ERROR_WANT_X509_LOOKUP;
            errstr = "The operation did not complete (X509 lookup)";
            break;
        case 7:
            p = PY_SSL_ERROR_WANT_CONNECT;
            errstr = "The operation did not complete (connect)";
            break;
        case 5:
        {
            if (e == 0) {
                PySocketSockObject *s
                  = (PySocketSockObject *) PyWeakref_GetObject(obj->Socket);
                if (ret == 0 || (((PyObject *)s) == (&_Py_NoneStruct))) {
                    p = PY_SSL_ERROR_EOF;
                    type = PySSLEOFErrorObject;
                    errstr = "EOF occurred in violation of protocol";
                } else if (ret == -1) {

                    ( ((PyObject*)(s))->ob_refcnt++);
                    ERR_clear_error();
                    s->errorhandler();
                    do { if ( --((PyObject*)(s))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(s)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(s)))); } while (0);
                    return ((void *)0);
                } else {
                    p = PY_SSL_ERROR_SYSCALL;
                    type = PySSLSyscallErrorObject;
                    errstr = "Some I/O error occurred";
                }
            } else {
                p = PY_SSL_ERROR_SYSCALL;
            }
            break;
        }
        case 1:
        {
            p = PY_SSL_ERROR_SSL;
            if (e == 0)

                errstr = "A failure in the SSL library occurred";
            break;
        }
        default:
            p = PY_SSL_ERROR_INVALID_ERROR_CODE;
            errstr = "Invalid error code";
        }
    }
    fill_and_set_sslerror(type, p, errstr, lineno, e);
    ERR_clear_error();
    return ((void *)0);
}

static PyObject *
_setSSLError (char *errstr, int errcode, char *filename, int lineno) {

    if (errstr == ((void *)0))
        errcode = ERR_peek_last_error();
    else
        errcode = 0;
    fill_and_set_sslerror(PySSLErrorObject, errcode, errstr, lineno, errcode);
    ERR_clear_error();
    return ((void *)0);
}





static PySSLSocket *
newPySSLSocket(SSL_CTX *ctx, PySocketSockObject *sock,
               enum py_ssl_server_or_client socket_type,
               char *server_hostname)
{
    PySSLSocket *self;

    self = ( (PySSLSocket *) _PyObject_New(&PySSLSocket_Type) );
    if (self == ((void *)0))
        return ((void *)0);

    self->peer_cert = ((void *)0);
    self->ssl = ((void *)0);
    self->Socket = ((void *)0);


    (void) ERR_get_state();
    ERR_clear_error();

    { PyThreadState *_save = ((void *)0); do { if (_ssl_locks_count>0) { (_save) = PyEval_SaveThread(); } } while (0);
    self->ssl = SSL_new(ctx);
    do { if (_ssl_locks_count>0) { PyEval_RestoreThread(_save); } } while (0); }
    SSL_set_fd(self->ssl, sock->sock_fd);

    SSL_ctrl((self->ssl),33,(0x00000004L),((void *)0));



    if (server_hostname != ((void *)0))
        SSL_ctrl(self->ssl,55,0,(char *)server_hostname);





    if (sock->sock_timeout >= 0.0) {
        BIO_ctrl(SSL_get_rbio(self->ssl),102,(1),((void *)0));
        BIO_ctrl(SSL_get_wbio(self->ssl),102,(1),((void *)0));
    }

    { PyThreadState *_save = ((void *)0); do { if (_ssl_locks_count>0) { (_save) = PyEval_SaveThread(); } } while (0);
    if (socket_type == PY_SSL_CLIENT)
        SSL_set_connect_state(self->ssl);
    else
        SSL_set_accept_state(self->ssl);
    do { if (_ssl_locks_count>0) { PyEval_RestoreThread(_save); } } while (0); }

    self->socket_type = socket_type;
    self->Socket = PyWeakref_NewRef((PyObject *) sock, ((void *)0));
    return self;
}



static PyObject *PySSL_SSLdo_handshake(PySSLSocket *self)
{
    int ret;
    int err;
    int sockstate, nonblocking;
    PySocketSockObject *sock
      = (PySocketSockObject *) PyWeakref_GetObject(self->Socket);

    if (((PyObject*)sock) == (&_Py_NoneStruct)) {
        _setSSLError("Underlying socket connection gone",
                     PY_SSL_ERROR_NO_SOCKET, "_ssl.c", 503);
        return ((void *)0);
    }
    ( ((PyObject*)(sock))->ob_refcnt++);


    nonblocking = (sock->sock_timeout >= 0.0);
    BIO_ctrl(SSL_get_rbio(self->ssl),102,(nonblocking),((void *)0));
    BIO_ctrl(SSL_get_wbio(self->ssl),102,(nonblocking),((void *)0));



    do {
        { PyThreadState *_save = ((void *)0); do { if (_ssl_locks_count>0) { (_save) = PyEval_SaveThread(); } } while (0);
        ret = SSL_do_handshake(self->ssl);
        err = SSL_get_error(self->ssl, ret);
        do { if (_ssl_locks_count>0) { PyEval_RestoreThread(_save); } } while (0); }
        if (PyErr_CheckSignals())
            goto error;
        if (err == 2) {
            sockstate = check_socket_and_wait_for_timeout(sock, 0);
        } else if (err == 3) {
            sockstate = check_socket_and_wait_for_timeout(sock, 1);
        } else {
            sockstate = SOCKET_OPERATION_OK;
        }
        if (sockstate == SOCKET_HAS_TIMED_OUT) {
            PyErr_SetString(PySocketModule.timeout_error,
                            ("_ssl.c" ":" "531" ": " "The handshake operation timed out"));
            goto error;
        } else if (sockstate == SOCKET_HAS_BEEN_CLOSED) {
            PyErr_SetString(PySSLErrorObject,
                            ("_ssl.c" ":" "535" ": " "Underlying socket has been closed."));
            goto error;
        } else if (sockstate == SOCKET_TOO_LARGE_FOR_SELECT) {
            PyErr_SetString(PySSLErrorObject,
                            ("_ssl.c" ":" "539" ": " "Underlying socket too large for select()."));
            goto error;
        } else if (sockstate == SOCKET_IS_NONBLOCKING) {
            break;
        }
    } while (err == 2 || err == 3);
    do { if ( --((PyObject*)(sock))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sock)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sock)))); } while (0);
    if (ret < 1)
        return PySSL_SetError(self, ret, "_ssl.c", 547);

    if (self->peer_cert)
        X509_free (self->peer_cert);
    { PyThreadState *_save = ((void *)0); do { if (_ssl_locks_count>0) { (_save) = PyEval_SaveThread(); } } while (0);
    self->peer_cert = SSL_get_peer_certificate(self->ssl);
    do { if (_ssl_locks_count>0) { PyEval_RestoreThread(_save); } } while (0); }

    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);

error:
    do { if ( --((PyObject*)(sock))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sock)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sock)))); } while (0);
    return ((void *)0);
}

static PyObject *
_create_tuple_for_attribute (ASN1_OBJECT *name, ASN1_STRING *value) {

    char namebuf[256];
    int buflen;
    PyObject *name_obj;
    PyObject *value_obj;
    PyObject *attr;
    unsigned char *valuebuf = ((void *)0);

    buflen = OBJ_obj2txt(namebuf, sizeof(namebuf), name, 0);
    if (buflen < 0) {
        _setSSLError(((void *)0), 0, "_ssl.c", 575);
        goto fail;
    }
    name_obj = PyUnicode_FromStringAndSize(namebuf, buflen);
    if (name_obj == ((void *)0))
        goto fail;

    buflen = ASN1_STRING_to_UTF8(&valuebuf, value);
    if (buflen < 0) {
        _setSSLError(((void *)0), 0, "_ssl.c", 584);
        do { if ( --((PyObject*)(name_obj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(name_obj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(name_obj)))); } while (0);
        goto fail;
    }
    value_obj = PyUnicode_DecodeUTF8((char *) valuebuf,
                                     buflen, "strict");
    CRYPTO_free(valuebuf);
    if (value_obj == ((void *)0)) {
        do { if ( --((PyObject*)(name_obj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(name_obj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(name_obj)))); } while (0);
        goto fail;
    }
    attr = PyTuple_New(2);
    if (attr == ((void *)0)) {
        do { if ( --((PyObject*)(name_obj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(name_obj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(name_obj)))); } while (0);
        do { if ( --((PyObject*)(value_obj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value_obj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value_obj)))); } while (0);
        goto fail;
    }
    (((PyTupleObject *)(attr))->ob_item[0] = name_obj);
    (((PyTupleObject *)(attr))->ob_item[1] = value_obj);
    return attr;

  fail:
    return ((void *)0);
}

static PyObject *
_create_tuple_for_X509_NAME (X509_NAME *xname)
{
    PyObject *dn = ((void *)0);
    PyObject *rdn = ((void *)0);
    PyObject *rdnt;
    PyObject *attr = ((void *)0);
    int entry_count = X509_NAME_entry_count(xname);
    X509_NAME_ENTRY *entry;
    ASN1_OBJECT *name;
    ASN1_STRING *value;
    int index_counter;
    int rdn_level = -1;
    int retcode;

    dn = PyList_New(0);
    if (dn == ((void *)0))
        return ((void *)0);

    rdn = PyList_New(0);
    if (rdn == ((void *)0))
        goto fail0;

    for (index_counter = 0;
         index_counter < entry_count;
         index_counter++)
    {
        entry = X509_NAME_get_entry(xname, index_counter);


        if (rdn_level >= 0) {
            if (rdn_level != entry->set) {


                rdnt = PyList_AsTuple(rdn);
                do { if ( --((PyObject*)(rdn))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(rdn)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(rdn)))); } while (0);
                if (rdnt == ((void *)0))
                    goto fail0;
                retcode = PyList_Append(dn, rdnt);
                do { if ( --((PyObject*)(rdnt))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(rdnt)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(rdnt)))); } while (0);
                if (retcode < 0)
                    goto fail0;

                rdn = PyList_New(0);
                if (rdn == ((void *)0))
                    goto fail0;
            }
        }
        rdn_level = entry->set;


        name = X509_NAME_ENTRY_get_object(entry);
        value = X509_NAME_ENTRY_get_data(entry);
        attr = _create_tuple_for_attribute(name, value);






        if (attr == ((void *)0))
            goto fail1;
        retcode = PyList_Append(rdn, attr);
        do { if ( --((PyObject*)(attr))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(attr)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(attr)))); } while (0);
        if (retcode < 0)
            goto fail1;
    }

    if (rdn != ((void *)0)) {
        if ((((PyVarObject*)(rdn))->ob_size) > 0) {
            rdnt = PyList_AsTuple(rdn);
            do { if ( --((PyObject*)(rdn))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(rdn)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(rdn)))); } while (0);
            if (rdnt == ((void *)0))
                goto fail0;
            retcode = PyList_Append(dn, rdnt);
            do { if ( --((PyObject*)(rdnt))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(rdnt)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(rdnt)))); } while (0);
            if (retcode < 0)
                goto fail0;
        }
        else {
            do { if ( --((PyObject*)(rdn))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(rdn)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(rdn)))); } while (0);
        }
    }


    rdnt = PyList_AsTuple(dn);
    do { if ( --((PyObject*)(dn))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dn)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dn)))); } while (0);
    if (rdnt == ((void *)0))
        return ((void *)0);
    return rdnt;

  fail1:
    do { if ((rdn) == ((void *)0)) ; else do { if ( --((PyObject*)(rdn))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(rdn)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(rdn)))); } while (0); } while (0);

  fail0:
    do { if ((dn) == ((void *)0)) ; else do { if ( --((PyObject*)(dn))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dn)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dn)))); } while (0); } while (0);
    return ((void *)0);
}

static PyObject *
_get_peer_alt_names (X509 *certificate) {







    int i, j;
    PyObject *peer_alt_names = (&_Py_NoneStruct);
    PyObject *v, *t;
    X509_EXTENSION *ext = ((void *)0);
    GENERAL_NAMES *names = ((void *)0);
    GENERAL_NAME *name;
    const X509V3_EXT_METHOD *method;
    BIO *biobuf = ((void *)0);
    char buf[2048];
    char *vptr;
    int len;


    const unsigned char *p;




    if (certificate == ((void *)0))
        return peer_alt_names;


    biobuf = BIO_new(BIO_s_mem());

    i = -1;
    while ((i = X509_get_ext_by_NID(
                    certificate, 85, i)) >= 0) {

        if (peer_alt_names == (&_Py_NoneStruct)) {
            peer_alt_names = PyList_New(0);
            if (peer_alt_names == ((void *)0))
                goto fail;
        }


        ext = X509_get_ext(certificate, i);
        if(!(method = X509V3_EXT_get(ext))) {
            PyErr_SetString
              (PySSLErrorObject,
               ("_ssl.c" ":" "756" ": " "No method for internalizing subjectAltName!"));
            goto fail;
        }

        p = ext->value->data;
        if (method->it)
            names = (GENERAL_NAMES*)
              (ASN1_item_d2i(((void *)0),
                             &p,
                             ext->value->length,
                             (method->it)));
        else
            names = (GENERAL_NAMES*)
              (method->d2i(((void *)0),
                           &p,
                           ext->value->length));

        for(j = 0; j < sk_num((names)); j++) {



            name = ((GENERAL_NAME *)sk_value((names), (j)));
            if (name->type == 4) {




                t = PyTuple_New(2);
                if (t == ((void *)0)) {
                    goto fail;
                }

                v = PyUnicode_FromString("DirName");
                if (v == ((void *)0)) {
                    do { if ( --((PyObject*)(t))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(t)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(t)))); } while (0);
                    goto fail;
                }
                (((PyTupleObject *)(t))->ob_item[0] = v);

                v = _create_tuple_for_X509_NAME (name->d.dirn);
                if (v == ((void *)0)) {
                    do { if ( --((PyObject*)(t))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(t)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(t)))); } while (0);
                    goto fail;
                }
                (((PyTupleObject *)(t))->ob_item[1] = v);

            } else {



                (void) (int)BIO_ctrl(biobuf,1,0,((void *)0));
                GENERAL_NAME_print(biobuf, name);
                len = BIO_gets(biobuf, buf, sizeof(buf)-1);
                if (len < 0) {
                    _setSSLError(((void *)0), 0, "_ssl.c", 810);
                    goto fail;
                }
                vptr = strchr(buf, ':');
                if (vptr == ((void *)0))
                    goto fail;
                t = PyTuple_New(2);
                if (t == ((void *)0))
                    goto fail;
                v = PyUnicode_FromStringAndSize(buf, (vptr - buf));
                if (v == ((void *)0)) {
                    do { if ( --((PyObject*)(t))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(t)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(t)))); } while (0);
                    goto fail;
                }
                (((PyTupleObject *)(t))->ob_item[0] = v);
                v = PyUnicode_FromStringAndSize((vptr + 1),
                                                (len - (vptr - buf + 1)));
                if (v == ((void *)0)) {
                    do { if ( --((PyObject*)(t))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(t)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(t)))); } while (0);
                    goto fail;
                }
                (((PyTupleObject *)(t))->ob_item[1] = v);
            }



            if (PyList_Append(peer_alt_names, t) < 0) {
                do { if ( --((PyObject*)(t))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(t)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(t)))); } while (0);
                goto fail;
            }
            do { if ( --((PyObject*)(t))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(t)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(t)))); } while (0);
        }
        sk_pop_free((names), (void (*)(void *))(GENERAL_NAME_free));
    }
    BIO_free(biobuf);
    if (peer_alt_names != (&_Py_NoneStruct)) {
        v = PyList_AsTuple(peer_alt_names);
        do { if ( --((PyObject*)(peer_alt_names))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(peer_alt_names)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(peer_alt_names)))); } while (0);
        return v;
    } else {
        return peer_alt_names;
    }


  fail:
    if (biobuf != ((void *)0))
        BIO_free(biobuf);

    if (peer_alt_names != (&_Py_NoneStruct)) {
        do { if ((peer_alt_names) == ((void *)0)) ; else do { if ( --((PyObject*)(peer_alt_names))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(peer_alt_names)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(peer_alt_names)))); } while (0); } while (0);
    }

    return ((void *)0);
}

static PyObject *
_decode_certificate(X509 *certificate) {

    PyObject *retval = ((void *)0);
    BIO *biobuf = ((void *)0);
    PyObject *peer;
    PyObject *peer_alt_names = ((void *)0);
    PyObject *issuer;
    PyObject *version;
    PyObject *sn_obj;
    ASN1_INTEGER *serialNumber;
    char buf[2048];
    int len;
    ASN1_TIME *notBefore, *notAfter;
    PyObject *pnotBefore, *pnotAfter;

    retval = PyDict_New();
    if (retval == ((void *)0))
        return ((void *)0);

    peer = _create_tuple_for_X509_NAME(
        X509_get_subject_name(certificate));
    if (peer == ((void *)0))
        goto fail0;
    if (PyDict_SetItemString(retval, (const char *) "subject", peer) < 0) {
        do { if ( --((PyObject*)(peer))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(peer)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(peer)))); } while (0);
        goto fail0;
    }
    do { if ( --((PyObject*)(peer))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(peer)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(peer)))); } while (0);

    issuer = _create_tuple_for_X509_NAME(
        X509_get_issuer_name(certificate));
    if (issuer == ((void *)0))
        goto fail0;
    if (PyDict_SetItemString(retval, (const char *)"issuer", issuer) < 0) {
        do { if ( --((PyObject*)(issuer))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(issuer)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(issuer)))); } while (0);
        goto fail0;
    }
    do { if ( --((PyObject*)(issuer))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(issuer)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(issuer)))); } while (0);

    version = PyLong_FromLong(ASN1_INTEGER_get((certificate)->cert_info->version) + 1);
    if (PyDict_SetItemString(retval, "version", version) < 0) {
        do { if ( --((PyObject*)(version))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(version)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(version)))); } while (0);
        goto fail0;
    }
    do { if ( --((PyObject*)(version))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(version)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(version)))); } while (0);


    biobuf = BIO_new(BIO_s_mem());

    (void) (int)BIO_ctrl(biobuf,1,0,((void *)0));
    serialNumber = X509_get_serialNumber(certificate);

    i2a_ASN1_INTEGER(biobuf, serialNumber);
    len = BIO_gets(biobuf, buf, sizeof(buf)-1);
    if (len < 0) {
        _setSSLError(((void *)0), 0, "_ssl.c", 921);
        goto fail1;
    }
    sn_obj = PyUnicode_FromStringAndSize(buf, len);
    if (sn_obj == ((void *)0))
        goto fail1;
    if (PyDict_SetItemString(retval, "serialNumber", sn_obj) < 0) {
        do { if ( --((PyObject*)(sn_obj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sn_obj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sn_obj)))); } while (0);
        goto fail1;
    }
    do { if ( --((PyObject*)(sn_obj))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sn_obj)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sn_obj)))); } while (0);

    (void) (int)BIO_ctrl(biobuf,1,0,((void *)0));
    notBefore = ((certificate)->cert_info->validity->notBefore);
    ASN1_TIME_print(biobuf, notBefore);
    len = BIO_gets(biobuf, buf, sizeof(buf)-1);
    if (len < 0) {
        _setSSLError(((void *)0), 0, "_ssl.c", 938);
        goto fail1;
    }
    pnotBefore = PyUnicode_FromStringAndSize(buf, len);
    if (pnotBefore == ((void *)0))
        goto fail1;
    if (PyDict_SetItemString(retval, "notBefore", pnotBefore) < 0) {
        do { if ( --((PyObject*)(pnotBefore))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pnotBefore)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pnotBefore)))); } while (0);
        goto fail1;
    }
    do { if ( --((PyObject*)(pnotBefore))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pnotBefore)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pnotBefore)))); } while (0);

    (void) (int)BIO_ctrl(biobuf,1,0,((void *)0));
    notAfter = ((certificate)->cert_info->validity->notAfter);
    ASN1_TIME_print(biobuf, notAfter);
    len = BIO_gets(biobuf, buf, sizeof(buf)-1);
    if (len < 0) {
        _setSSLError(((void *)0), 0, "_ssl.c", 955);
        goto fail1;
    }
    pnotAfter = PyUnicode_FromStringAndSize(buf, len);
    if (pnotAfter == ((void *)0))
        goto fail1;
    if (PyDict_SetItemString(retval, "notAfter", pnotAfter) < 0) {
        do { if ( --((PyObject*)(pnotAfter))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pnotAfter)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pnotAfter)))); } while (0);
        goto fail1;
    }
    do { if ( --((PyObject*)(pnotAfter))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(pnotAfter)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(pnotAfter)))); } while (0);



    peer_alt_names = _get_peer_alt_names(certificate);
    if (peer_alt_names == ((void *)0))
        goto fail1;
    else if (peer_alt_names != (&_Py_NoneStruct)) {
        if (PyDict_SetItemString(retval, "subjectAltName",
                                 peer_alt_names) < 0) {
            do { if ( --((PyObject*)(peer_alt_names))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(peer_alt_names)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(peer_alt_names)))); } while (0);
            goto fail1;
        }
        do { if ( --((PyObject*)(peer_alt_names))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(peer_alt_names)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(peer_alt_names)))); } while (0);
    }

    BIO_free(biobuf);
    return retval;

  fail1:
    if (biobuf != ((void *)0))
        BIO_free(biobuf);
  fail0:
    do { if ((retval) == ((void *)0)) ; else do { if ( --((PyObject*)(retval))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(retval)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(retval)))); } while (0); } while (0);
    return ((void *)0);
}


static PyObject *
PySSL_test_decode_certificate (PyObject *mod, PyObject *args) {

    PyObject *retval = ((void *)0);
    PyObject *filename;
    X509 *x=((void *)0);
    BIO *cert;

    if (!PyArg_ParseTuple(args, "O&:test_decode_certificate",
                          PyUnicode_FSConverter, &filename))
        return ((void *)0);

    if ((cert=BIO_new(BIO_s_file())) == ((void *)0)) {
        PyErr_SetString(PySSLErrorObject,
                        "Can't malloc memory to read file");
        goto fail0;
    }

    if (BIO_ctrl(cert,108, 0x01|0x02,(char *)PyBytes_AsString(filename)) <= 0) {
        PyErr_SetString(PySSLErrorObject,
                        "Can't open file");
        goto fail0;
    }

    x = PEM_read_bio_X509_AUX(cert,((void *)0), ((void *)0), ((void *)0));
    if (x == ((void *)0)) {
        PyErr_SetString(PySSLErrorObject,
                        "Error decoding PEM-encoded file");
        goto fail0;
    }

    retval = _decode_certificate(x);
    X509_free(x);

  fail0:
    do { if ( --((PyObject*)(filename))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(filename)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(filename)))); } while (0);
    if (cert != ((void *)0)) BIO_free(cert);
    return retval;
}


static PyObject *
PySSL_peercert(PySSLSocket *self, PyObject *args)
{
    PyObject *retval = ((void *)0);
    int len;
    int verification;
    int binary_mode = 0;

    if (!PyArg_ParseTuple(args, "|p:peer_certificate", &binary_mode))
        return ((void *)0);

    if (!self->peer_cert)
        return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);

    if (binary_mode) {


        unsigned char *bytes_buf = ((void *)0);

        bytes_buf = ((void *)0);
        len = i2d_X509(self->peer_cert, &bytes_buf);
        if (len < 0) {
            PySSL_SetError(self, len, "_ssl.c", 1056);
            return ((void *)0);
        }

        retval = PyBytes_FromStringAndSize
          ((const char *) bytes_buf, len);
        CRYPTO_free(bytes_buf);
        return retval;

    } else {
        verification = SSL_CTX_get_verify_mode(SSL_get_SSL_CTX(self->ssl));
        if ((verification & 0x01) == 0)
            return PyDict_New();
        else
            return _decode_certificate(self->peer_cert);
    }
}

static char PySSL_peercert_doc[] = "peer_certificate([der=False]) -> certificate\n\nReturns the certificate for the peer.  If no certificate was provided,\nreturns None.  If a certificate was provided, but not validated, returns\nan empty dictionary.  Otherwise returns a dict containing information\nabout the peer certificate.\n\nIf the optional argument is True, returns a DER-encoded copy of the\npeer certificate, or None if no certificate was provided.  This will\nreturn the certificate even if it wasn't validated.";
# 1086 "_ssl.c"
static PyObject *PySSL_cipher (PySSLSocket *self) {

    PyObject *retval, *v;
    const SSL_CIPHER *current;
    char *cipher_name;
    char *cipher_protocol;

    if (self->ssl == ((void *)0))
        return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
    current = SSL_get_current_cipher(self->ssl);
    if (current == ((void *)0))
        return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);

    retval = PyTuple_New(3);
    if (retval == ((void *)0))
        return ((void *)0);

    cipher_name = (char *) SSL_CIPHER_get_name(current);
    if (cipher_name == ((void *)0)) {
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        (((PyTupleObject *)(retval))->ob_item[0] = (&_Py_NoneStruct));
    } else {
        v = PyUnicode_FromString(cipher_name);
        if (v == ((void *)0))
            goto fail0;
        (((PyTupleObject *)(retval))->ob_item[0] = v);
    }
    cipher_protocol = SSL_CIPHER_get_version(current);
    if (cipher_protocol == ((void *)0)) {
        ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
        (((PyTupleObject *)(retval))->ob_item[1] = (&_Py_NoneStruct));
    } else {
        v = PyUnicode_FromString(cipher_protocol);
        if (v == ((void *)0))
            goto fail0;
        (((PyTupleObject *)(retval))->ob_item[1] = v);
    }
    v = PyLong_FromLong(SSL_CIPHER_get_bits(current, ((void *)0)));
    if (v == ((void *)0))
        goto fail0;
    (((PyTupleObject *)(retval))->ob_item[2] = v);
    return retval;

  fail0:
    do { if ( --((PyObject*)(retval))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(retval)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(retval)))); } while (0);
    return ((void *)0);
}
# 1148 "_ssl.c"
static PyObject *PySSL_compression(PySSLSocket *self) {



    const COMP_METHOD *comp_method;
    const char *short_name;

    if (self->ssl == ((void *)0))
        return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
    comp_method = SSL_get_current_compression(self->ssl);
    if (comp_method == ((void *)0) || comp_method->type == 0)
        return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
    short_name = OBJ_nid2sn(comp_method->type);
    if (short_name == ((void *)0))
        return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
    return PyUnicode_DecodeFSDefault(short_name);

}

static void PySSL_dealloc(PySSLSocket *self)
{
    if (self->peer_cert)
        X509_free (self->peer_cert);
    if (self->ssl)
        SSL_free(self->ssl);
    do { if ((self->Socket) == ((void *)0)) ; else do { if ( --((PyObject*)(self->Socket))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(self->Socket)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(self->Socket)))); } while (0); } while (0);
    PyObject_Free(self);
}






static int
check_socket_and_wait_for_timeout(PySocketSockObject *s, int writing)
{
    fd_set fds;
    struct timeval tv;
    int rc;


    if (s->sock_timeout < 0.0)
        return SOCKET_IS_BLOCKING;
    else if (s->sock_timeout == 0.0)
        return SOCKET_IS_NONBLOCKING;


    if (s->sock_fd < 0)
        return SOCKET_HAS_BEEN_CLOSED;




    {
        struct pollfd pollfd;
        int timeout;

        pollfd.fd = s->sock_fd;
        pollfd.events = writing ? 0x0004 : 0x0001;


        timeout = (int)(s->sock_timeout * 1000 + 0.5);
        { PyThreadState *_save = ((void *)0); do { if (_ssl_locks_count>0) { (_save) = PyEval_SaveThread(); } } while (0);
        rc = poll(&pollfd, 1, timeout);
        do { if (_ssl_locks_count>0) { PyEval_RestoreThread(_save); } } while (0); }

        goto normal_return;
    }



    if (!(((s->sock_fd) >= 0) && ((s->sock_fd) < 1024)))
        return SOCKET_TOO_LARGE_FOR_SELECT;


    tv.tv_sec = (int)s->sock_timeout;
    tv.tv_usec = (int)((s->sock_timeout - tv.tv_sec) * 1e6);
    __builtin_bzero(&fds, sizeof(*(&fds)));
    do { int __fd = (s->sock_fd); ((&fds)->fds_bits[__fd/(sizeof(__int32_t) * 8)] |= (1<<(__fd % (sizeof(__int32_t) * 8)))); } while(0);


    { PyThreadState *_save = ((void *)0); do { if (_ssl_locks_count>0) { (_save) = PyEval_SaveThread(); } } while (0);
    if (writing)
        rc = select(s->sock_fd+1, ((void *)0), &fds, ((void *)0), &tv);
    else
        rc = select(s->sock_fd+1, &fds, ((void *)0), ((void *)0), &tv);
    do { if (_ssl_locks_count>0) { PyEval_RestoreThread(_save); } } while (0); }


normal_return:



    return rc == 0 ? SOCKET_HAS_TIMED_OUT : SOCKET_OPERATION_OK;
}

static PyObject *PySSL_SSLwrite(PySSLSocket *self, PyObject *args)
{
    Py_buffer buf;
    int len;
    int sockstate;
    int err;
    int nonblocking;
    PySocketSockObject *sock
      = (PySocketSockObject *) PyWeakref_GetObject(self->Socket);

    if (((PyObject*)sock) == (&_Py_NoneStruct)) {
        _setSSLError("Underlying socket connection gone",
                     PY_SSL_ERROR_NO_SOCKET, "_ssl.c", 1257);
        return ((void *)0);
    }
    ( ((PyObject*)(sock))->ob_refcnt++);

    if (!PyArg_ParseTuple(args, "y*:write", &buf)) {
        do { if ( --((PyObject*)(sock))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sock)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sock)))); } while (0);
        return ((void *)0);
    }


    nonblocking = (sock->sock_timeout >= 0.0);
    BIO_ctrl(SSL_get_rbio(self->ssl),102,(nonblocking),((void *)0));
    BIO_ctrl(SSL_get_wbio(self->ssl),102,(nonblocking),((void *)0));

    sockstate = check_socket_and_wait_for_timeout(sock, 1);
    if (sockstate == SOCKET_HAS_TIMED_OUT) {
        PyErr_SetString(PySocketModule.timeout_error,
                        "The write operation timed out");
        goto error;
    } else if (sockstate == SOCKET_HAS_BEEN_CLOSED) {
        PyErr_SetString(PySSLErrorObject,
                        "Underlying socket has been closed.");
        goto error;
    } else if (sockstate == SOCKET_TOO_LARGE_FOR_SELECT) {
        PyErr_SetString(PySSLErrorObject,
                        "Underlying socket too large for select().");
        goto error;
    }
    do {
        { PyThreadState *_save = ((void *)0); do { if (_ssl_locks_count>0) { (_save) = PyEval_SaveThread(); } } while (0);
        len = SSL_write(self->ssl, buf.buf, buf.len);
        err = SSL_get_error(self->ssl, len);
        do { if (_ssl_locks_count>0) { PyEval_RestoreThread(_save); } } while (0); }
        if (PyErr_CheckSignals()) {
            goto error;
        }
        if (err == 2) {
            sockstate = check_socket_and_wait_for_timeout(sock, 0);
        } else if (err == 3) {
            sockstate = check_socket_and_wait_for_timeout(sock, 1);
        } else {
            sockstate = SOCKET_OPERATION_OK;
        }
        if (sockstate == SOCKET_HAS_TIMED_OUT) {
            PyErr_SetString(PySocketModule.timeout_error,
                            "The write operation timed out");
            goto error;
        } else if (sockstate == SOCKET_HAS_BEEN_CLOSED) {
            PyErr_SetString(PySSLErrorObject,
                            "Underlying socket has been closed.");
            goto error;
        } else if (sockstate == SOCKET_IS_NONBLOCKING) {
            break;
        }
    } while (err == 2 || err == 3);

    do { if ( --((PyObject*)(sock))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sock)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sock)))); } while (0);
    PyBuffer_Release(&buf);
    if (len > 0)
        return PyLong_FromLong(len);
    else
        return PySSL_SetError(self, len, "_ssl.c", 1319);

error:
    do { if ( --((PyObject*)(sock))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sock)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sock)))); } while (0);
    PyBuffer_Release(&buf);
    return ((void *)0);
}

static char PySSL_SSLwrite_doc[] = "write(s) -> len\n\nWrites the string s into the SSL object.  Returns the number\nof bytes written.";





static PyObject *PySSL_SSLpending(PySSLSocket *self)
{
    int count = 0;

    { PyThreadState *_save = ((void *)0); do { if (_ssl_locks_count>0) { (_save) = PyEval_SaveThread(); } } while (0);
    count = SSL_pending(self->ssl);
    do { if (_ssl_locks_count>0) { PyEval_RestoreThread(_save); } } while (0); }
    if (count < 0)
        return PySSL_SetError(self, count, "_ssl.c", 1341);
    else
        return PyLong_FromLong(count);
}

static char PySSL_SSLpending_doc[] = "pending() -> count\n\nReturns the number of already decrypted bytes available for read,\npending on the connection.\n";





static PyObject *PySSL_SSLread(PySSLSocket *self, PyObject *args)
{
    PyObject *dest = ((void *)0);
    Py_buffer buf;
    char *mem;
    int len, count;
    int buf_passed = 0;
    int sockstate;
    int err;
    int nonblocking;
    PySocketSockObject *sock
      = (PySocketSockObject *) PyWeakref_GetObject(self->Socket);

    if (((PyObject*)sock) == (&_Py_NoneStruct)) {
        _setSSLError("Underlying socket connection gone",
                     PY_SSL_ERROR_NO_SOCKET, "_ssl.c", 1367);
        return ((void *)0);
    }
    ( ((PyObject*)(sock))->ob_refcnt++);

    buf.obj = ((void *)0);
    buf.buf = ((void *)0);
    if (!PyArg_ParseTuple(args, "i|w*:read", &len, &buf))
        goto error;

    if ((buf.buf == ((void *)0)) && (buf.obj == ((void *)0))) {
        dest = PyBytes_FromStringAndSize(((void *)0), len);
        if (dest == ((void *)0))
            goto error;
        mem = ((__builtin_expect(!(((((((PyObject*)(dest))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_ssl.c", 1381, "PyBytes_Check(dest)") : (void)0), (((PyBytesObject *)(dest))->ob_sval));
    }
    else {
        buf_passed = 1;
        mem = buf.buf;
        if (len <= 0 || len > buf.len) {
            len = (int) buf.len;
            if (buf.len != len) {
                PyErr_SetString(PyExc_OverflowError,
                                "maximum length can't fit in a C 'int'");
                goto error;
            }
        }
    }


    nonblocking = (sock->sock_timeout >= 0.0);
    BIO_ctrl(SSL_get_rbio(self->ssl),102,(nonblocking),((void *)0));
    BIO_ctrl(SSL_get_wbio(self->ssl),102,(nonblocking),((void *)0));


    { PyThreadState *_save = ((void *)0); do { if (_ssl_locks_count>0) { (_save) = PyEval_SaveThread(); } } while (0);
    count = SSL_pending(self->ssl);
    do { if (_ssl_locks_count>0) { PyEval_RestoreThread(_save); } } while (0); }

    if (!count) {
        sockstate = check_socket_and_wait_for_timeout(sock, 0);
        if (sockstate == SOCKET_HAS_TIMED_OUT) {
            PyErr_SetString(PySocketModule.timeout_error,
                            "The read operation timed out");
            goto error;
        } else if (sockstate == SOCKET_TOO_LARGE_FOR_SELECT) {
            PyErr_SetString(PySSLErrorObject,
                            "Underlying socket too large for select().");
            goto error;
        } else if (sockstate == SOCKET_HAS_BEEN_CLOSED) {
            count = 0;
            goto done;
        }
    }
    do {
        { PyThreadState *_save = ((void *)0); do { if (_ssl_locks_count>0) { (_save) = PyEval_SaveThread(); } } while (0);
        count = SSL_read(self->ssl, mem, len);
        err = SSL_get_error(self->ssl, count);
        do { if (_ssl_locks_count>0) { PyEval_RestoreThread(_save); } } while (0); }
        if (PyErr_CheckSignals())
            goto error;
        if (err == 2) {
            sockstate = check_socket_and_wait_for_timeout(sock, 0);
        } else if (err == 3) {
            sockstate = check_socket_and_wait_for_timeout(sock, 1);
        } else if ((err == 6) &&
                   (SSL_get_shutdown(self->ssl) ==
                    2))
        {
            count = 0;
            goto done;
        } else {
            sockstate = SOCKET_OPERATION_OK;
        }
        if (sockstate == SOCKET_HAS_TIMED_OUT) {
            PyErr_SetString(PySocketModule.timeout_error,
                            "The read operation timed out");
            goto error;
        } else if (sockstate == SOCKET_IS_NONBLOCKING) {
            break;
        }
    } while (err == 2 || err == 3);
    if (count <= 0) {
        PySSL_SetError(self, count, "_ssl.c", 1450);
        goto error;
    }

done:
    do { if ( --((PyObject*)(sock))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sock)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sock)))); } while (0);
    if (!buf_passed) {
        _PyBytes_Resize(&dest, count);
        return dest;
    }
    else {
        PyBuffer_Release(&buf);
        return PyLong_FromLong(count);
    }

error:
    do { if ( --((PyObject*)(sock))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sock)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sock)))); } while (0);
    if (!buf_passed)
        do { if ((dest) == ((void *)0)) ; else do { if ( --((PyObject*)(dest))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(dest)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(dest)))); } while (0); } while (0);
    else
        PyBuffer_Release(&buf);
    return ((void *)0);
}

static char PySSL_SSLread_doc[] = "read([len]) -> string\n\nRead up to len bytes from the SSL socket.";




static PyObject *PySSL_SSLshutdown(PySSLSocket *self)
{
    int err, ssl_err, sockstate, nonblocking;
    int zeros = 0;
    PySocketSockObject *sock
      = (PySocketSockObject *) PyWeakref_GetObject(self->Socket);


    if ((((PyObject*)sock) == (&_Py_NoneStruct)) || (sock->sock_fd < 0)) {
        _setSSLError("Underlying socket connection gone",
                     PY_SSL_ERROR_NO_SOCKET, "_ssl.c", 1489);
        return ((void *)0);
    }
    ( ((PyObject*)(sock))->ob_refcnt++);


    nonblocking = (sock->sock_timeout >= 0.0);
    BIO_ctrl(SSL_get_rbio(self->ssl),102,(nonblocking),((void *)0));
    BIO_ctrl(SSL_get_wbio(self->ssl),102,(nonblocking),((void *)0));

    while (1) {
        { PyThreadState *_save = ((void *)0); do { if (_ssl_locks_count>0) { (_save) = PyEval_SaveThread(); } } while (0);
# 1509 "_ssl.c"
        if (self->shutdown_seen_zero)
            SSL_set_read_ahead(self->ssl, 0);
        err = SSL_shutdown(self->ssl);
        do { if (_ssl_locks_count>0) { PyEval_RestoreThread(_save); } } while (0); }

        if (err > 0)
            break;
        if (err == 0) {



            if (++zeros > 1)
                break;

            self->shutdown_seen_zero = 1;
            continue;
        }


        ssl_err = SSL_get_error(self->ssl, err);
        if (ssl_err == 2)
            sockstate = check_socket_and_wait_for_timeout(sock, 0);
        else if (ssl_err == 3)
            sockstate = check_socket_and_wait_for_timeout(sock, 1);
        else
            break;
        if (sockstate == SOCKET_HAS_TIMED_OUT) {
            if (ssl_err == 2)
                PyErr_SetString(PySocketModule.timeout_error,
                                "The read operation timed out");
            else
                PyErr_SetString(PySocketModule.timeout_error,
                                "The write operation timed out");
            goto error;
        }
        else if (sockstate == SOCKET_TOO_LARGE_FOR_SELECT) {
            PyErr_SetString(PySSLErrorObject,
                            "Underlying socket too large for select().");
            goto error;
        }
        else if (sockstate != SOCKET_OPERATION_OK)

            break;
    }

    if (err < 0) {
        do { if ( --((PyObject*)(sock))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sock)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sock)))); } while (0);
        return PySSL_SetError(self, err, "_ssl.c", 1556);
    }
    else

        return (PyObject *) sock;

error:
    do { if ( --((PyObject*)(sock))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(sock)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(sock)))); } while (0);
    return ((void *)0);
}

static char PySSL_SSLshutdown_doc[] = "shutdown(s) -> socket\n\nDoes the SSL shutdown handshake with the remote end, and returns\nthe underlying socket object.";






static PyObject *
PySSL_tls_unique_cb(PySSLSocket *self)
{
    PyObject *retval = ((void *)0);
    char buf[128];
    int len;

    if (SSL_ctrl((self->ssl),8,0,((void *)0)) ^ !self->socket_type) {

        len = SSL_get_finished(self->ssl, buf, 128);
    }
    else {

        len = SSL_get_peer_finished(self->ssl, buf, 128);
    }


    (__builtin_expect(!(len >= 0), 0) ? __assert_rtn(__func__, "_ssl.c", 1591, "len >= 0") : (void)0);
    if (len == 0)
        return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);

    retval = PyBytes_FromStringAndSize(buf, len);

    return retval;
}

static char PySSL_tls_unique_cb_doc[] = "tls_unique_cb() -> bytes\n\nReturns the 'tls-unique' channel binding data, as defined by RFC 5929.\n\nIf the TLS handshake is not yet complete, None is returned";
# 1609 "_ssl.c"
static PyMethodDef PySSLMethods[] = {
    {"do_handshake", (PyCFunction)PySSL_SSLdo_handshake, 0x0004},
    {"write", (PyCFunction)PySSL_SSLwrite, 0x0001,
     PySSL_SSLwrite_doc},
    {"read", (PyCFunction)PySSL_SSLread, 0x0001,
     PySSL_SSLread_doc},
    {"pending", (PyCFunction)PySSL_SSLpending, 0x0004,
     PySSL_SSLpending_doc},
    {"peer_certificate", (PyCFunction)PySSL_peercert, 0x0001,
     PySSL_peercert_doc},
    {"cipher", (PyCFunction)PySSL_cipher, 0x0004},



    {"compression", (PyCFunction)PySSL_compression, 0x0004},
    {"shutdown", (PyCFunction)PySSL_SSLshutdown, 0x0004,
     PySSL_SSLshutdown_doc},

    {"tls_unique_cb", (PyCFunction)PySSL_tls_unique_cb, 0x0004,
     PySSL_tls_unique_cb_doc},

    {((void *)0), ((void *)0)}
};

static PyTypeObject PySSLSocket_Type = {
    { { 1, ((void *)0) }, 0 },
    "_ssl._SSLSocket",
    sizeof(PySSLSocket),
    0,

    (destructor)PySSL_dealloc,
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
    PySSLMethods,
};






static PyObject *
context_new(PyTypeObject *type, PyObject *args, PyObject *kwds)
{
    char *kwlist[] = {"protocol", ((void *)0)};
    PySSLContext *self;
    int proto_version = PY_SSL_VERSION_SSL23;
    SSL_CTX *ctx = ((void *)0);

    if (!PyArg_ParseTupleAndKeywords(
        args, kwds, "i:_SSLContext", kwlist,
        &proto_version))
        return ((void *)0);

    { PyThreadState *_save = ((void *)0); do { if (_ssl_locks_count>0) { (_save) = PyEval_SaveThread(); } } while (0);
    if (proto_version == PY_SSL_VERSION_TLS1)
        ctx = SSL_CTX_new(TLSv1_method());
    else if (proto_version == PY_SSL_VERSION_SSL3)
        ctx = SSL_CTX_new(SSLv3_method());

    else if (proto_version == PY_SSL_VERSION_SSL2)
        ctx = SSL_CTX_new(SSLv2_method());

    else if (proto_version == PY_SSL_VERSION_SSL23)
        ctx = SSL_CTX_new(SSLv23_method());
    else
        proto_version = -1;
    do { if (_ssl_locks_count>0) { PyEval_RestoreThread(_save); } } while (0); }

    if (proto_version == -1) {
        PyErr_SetString(PyExc_ValueError,
                        "invalid protocol version");
        return ((void *)0);
    }
    if (ctx == ((void *)0)) {
        PyErr_SetString(PySSLErrorObject,
                        "failed to allocate SSL context");
        return ((void *)0);
    }

    (__builtin_expect(!(type != ((void *)0) && type->tp_alloc != ((void *)0)), 0) ? __assert_rtn(__func__, "_ssl.c", 1709, "type != NULL && type->tp_alloc != NULL") : (void)0);
    self = (PySSLContext *) type->tp_alloc(type, 0);
    if (self == ((void *)0)) {
        SSL_CTX_free(ctx);
        return ((void *)0);
    }
    self->ctx = ctx;




    SSL_CTX_set_verify(self->ctx, 0x00, ((void *)0));
    SSL_CTX_ctrl((self->ctx),32,(0x00000FFFL & ~0x00000800L),((void *)0));



    SSL_CTX_set_session_id_context(self->ctx, (const unsigned char *) "Python",
                                   sizeof("Python"));


    return (PyObject *)self;
}

static void
context_dealloc(PySSLContext *self)
{
    SSL_CTX_free(self->ctx);



    (((PyObject*)(self))->ob_type)->tp_free(self);
}

static PyObject *
set_ciphers(PySSLContext *self, PyObject *args)
{
    int ret;
    const char *cipherlist;

    if (!PyArg_ParseTuple(args, "s:set_ciphers", &cipherlist))
        return ((void *)0);
    ret = SSL_CTX_set_cipher_list(self->ctx, cipherlist);
    if (ret == 0) {



        ERR_clear_error();
        PyErr_SetString(PySSLErrorObject,
                        "No cipher can be selected.");
        return ((void *)0);
    }
    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}
# 1809 "_ssl.c"
static PyObject *
_set_npn_protocols(PySSLContext *self, PyObject *args)
{
# 1842 "_ssl.c"
    PyErr_SetString(PyExc_NotImplementedError,
                    "The NPN extension requires OpenSSL 1.0.1 or later.");
    return ((void *)0);

}

static PyObject *
get_verify_mode(PySSLContext *self, void *c)
{
    switch (SSL_CTX_get_verify_mode(self->ctx)) {
    case 0x00:
        return PyLong_FromLong(PY_SSL_CERT_NONE);
    case 0x01:
        return PyLong_FromLong(PY_SSL_CERT_OPTIONAL);
    case 0x01 | 0x02:
        return PyLong_FromLong(PY_SSL_CERT_REQUIRED);
    }
    PyErr_SetString(PySSLErrorObject,
                    "invalid return value from SSL_CTX_get_verify_mode");
    return ((void *)0);
}

static int
set_verify_mode(PySSLContext *self, PyObject *arg, void *c)
{
    int n, mode;
    if (!PyArg_Parse(arg, "i", &n))
        return -1;
    if (n == PY_SSL_CERT_NONE)
        mode = 0x00;
    else if (n == PY_SSL_CERT_OPTIONAL)
        mode = 0x01;
    else if (n == PY_SSL_CERT_REQUIRED)
        mode = 0x01 | 0x02;
    else {
        PyErr_SetString(PyExc_ValueError,
                        "invalid value for verify_mode");
        return -1;
    }
    SSL_CTX_set_verify(self->ctx, mode, ((void *)0));
    return 0;
}

static PyObject *
get_options(PySSLContext *self, void *c)
{
    return PyLong_FromLong(SSL_CTX_ctrl((self->ctx),32,0,((void *)0)));
}

static int
set_options(PySSLContext *self, PyObject *arg, void *c)
{
    long new_opts, opts, set, clear;
    if (!PyArg_Parse(arg, "l", &new_opts))
        return -1;
    opts = SSL_CTX_ctrl((self->ctx),32,0,((void *)0));
    clear = opts & ~new_opts;
    set = ~opts & new_opts;
    if (clear) {

        SSL_CTX_ctrl((self->ctx),77,(clear),((void *)0));





    }
    if (set)
        SSL_CTX_ctrl((self->ctx),32,(set),((void *)0));
    return 0;
}

typedef struct {
    PyThreadState *thread_state;
    PyObject *callable;
    char *password;
    Py_ssize_t size;
    int error;
} _PySSLPasswordInfo;

static int
_pwinfo_set(_PySSLPasswordInfo *pw_info, PyObject* password,
            const char *bad_type_error)
{




    PyObject *password_bytes = ((void *)0);
    const char *data = ((void *)0);
    Py_ssize_t size;

    if (((((((PyObject*)(password))->ob_type))->tp_flags & ((1L<<28))) != 0)) {
        password_bytes = PyUnicode_AsEncodedString(password, ((void *)0), ((void *)0));
        if (!password_bytes) {
            goto error;
        }
        data = ((__builtin_expect(!(((((((PyObject*)(password_bytes))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_ssl.c", 1939, "PyBytes_Check(password_bytes)") : (void)0), (((PyBytesObject *)(password_bytes))->ob_sval));
        size = ((__builtin_expect(!(((((((PyObject*)(password_bytes))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_ssl.c", 1940, "PyBytes_Check(password_bytes)") : (void)0),(((PyVarObject*)(password_bytes))->ob_size));
    } else if (((((((PyObject*)(password))->ob_type))->tp_flags & ((1L<<27))) != 0)) {
        data = ((__builtin_expect(!(((((((PyObject*)(password))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_ssl.c", 1942, "PyBytes_Check(password)") : (void)0), (((PyBytesObject *)(password))->ob_sval));
        size = ((__builtin_expect(!(((((((PyObject*)(password))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_ssl.c", 1943, "PyBytes_Check(password)") : (void)0),(((PyVarObject*)(password))->ob_size));
    } else if (((((PyObject*)(password))->ob_type) == (&PyByteArray_Type) || PyType_IsSubtype((((PyObject*)(password))->ob_type), (&PyByteArray_Type)))) {
        data = ((__builtin_expect(!(((((PyObject*)(password))->ob_type) == (&PyByteArray_Type) || PyType_IsSubtype((((PyObject*)(password))->ob_type), (&PyByteArray_Type)))), 0) ? __assert_rtn(__func__, "_ssl.c", 1945, "PyByteArray_Check(password)") : (void)0), (((PyVarObject*)(password))->ob_size) ? ((PyByteArrayObject *)(password))->ob_bytes : _PyByteArray_empty_string);
        size = ((__builtin_expect(!(((((PyObject*)(password))->ob_type) == (&PyByteArray_Type) || PyType_IsSubtype((((PyObject*)(password))->ob_type), (&PyByteArray_Type)))), 0) ? __assert_rtn(__func__, "_ssl.c", 1946, "PyByteArray_Check(password)") : (void)0),(((PyVarObject*)(password))->ob_size));
    } else {
        PyErr_SetString(PyExc_TypeError, bad_type_error);
        goto error;
    }

    free(pw_info->password);
    pw_info->password = malloc(size);
    if (!pw_info->password) {
        PyErr_SetString(PyExc_MemoryError,
                        "unable to allocate password buffer");
        goto error;
    }
    ((__builtin_object_size (pw_info->password, 0) != (size_t) -1) ? __builtin___memcpy_chk (pw_info->password, data, size, __builtin_object_size (pw_info->password, 0)) : __inline_memcpy_chk (pw_info->password, data, size));
    pw_info->size = size;

    do { if ((password_bytes) == ((void *)0)) ; else do { if ( --((PyObject*)(password_bytes))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(password_bytes)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(password_bytes)))); } while (0); } while (0);
    return 1;

error:
    do { if ((password_bytes) == ((void *)0)) ; else do { if ( --((PyObject*)(password_bytes))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(password_bytes)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(password_bytes)))); } while (0); } while (0);
    return 0;
}

static int
_password_callback(char *buf, int size, int rwflag, void *userdata)
{
    _PySSLPasswordInfo *pw_info = (_PySSLPasswordInfo*) userdata;
    PyObject *fn_ret = ((void *)0);

    do { if (_ssl_locks_count>0) { PyEval_RestoreThread(pw_info->thread_state); } } while (0);

    if (pw_info->callable) {
        fn_ret = PyObject_CallFunctionObjArgs(pw_info->callable, ((void *)0));
        if (!fn_ret) {


            goto error;
        }

        if (!_pwinfo_set(pw_info, fn_ret,
                         "password callback must return a string")) {
            goto error;
        }
        do { if (fn_ret) { PyObject *_py_tmp = (PyObject *)(fn_ret); (fn_ret) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    }

    if (pw_info->size > size) {
        PyErr_Format(PyExc_ValueError,
                     "password cannot be longer than %d bytes", size);
        goto error;
    }

    do { if (_ssl_locks_count>0) { (pw_info->thread_state) = PyEval_SaveThread(); } } while (0);
    ((__builtin_object_size (buf, 0) != (size_t) -1) ? __builtin___memcpy_chk (buf, pw_info->password, pw_info->size, __builtin_object_size (buf, 0)) : __inline_memcpy_chk (buf, pw_info->password, pw_info->size));
    return pw_info->size;

error:
    do { if ((fn_ret) == ((void *)0)) ; else do { if ( --((PyObject*)(fn_ret))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(fn_ret)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(fn_ret)))); } while (0); } while (0);
    do { if (_ssl_locks_count>0) { (pw_info->thread_state) = PyEval_SaveThread(); } } while (0);
    pw_info->error = 1;
    return -1;
}

static PyObject *
load_cert_chain(PySSLContext *self, PyObject *args, PyObject *kwds)
{
    char *kwlist[] = {"certfile", "keyfile", "password", ((void *)0)};
    PyObject *certfile, *keyfile = ((void *)0), *password = ((void *)0);
    PyObject *certfile_bytes = ((void *)0), *keyfile_bytes = ((void *)0);
    pem_password_cb *orig_passwd_cb = self->ctx->default_passwd_callback;
    void *orig_passwd_userdata = self->ctx->default_passwd_callback_userdata;
    _PySSLPasswordInfo pw_info = { ((void *)0), ((void *)0), ((void *)0), 0, 0 };
    int r;

    (*__error()) = 0;
    ERR_clear_error();
    if (!PyArg_ParseTupleAndKeywords(args, kwds,
        "O|OO:load_cert_chain", kwlist,
        &certfile, &keyfile, &password))
        return ((void *)0);
    if (keyfile == (&_Py_NoneStruct))
        keyfile = ((void *)0);
    if (!PyUnicode_FSConverter(certfile, &certfile_bytes)) {
        PyErr_SetString(PyExc_TypeError,
                        "certfile should be a valid filesystem path");
        return ((void *)0);
    }
    if (keyfile && !PyUnicode_FSConverter(keyfile, &keyfile_bytes)) {
        PyErr_SetString(PyExc_TypeError,
                        "keyfile should be a valid filesystem path");
        goto error;
    }
    if (password && password != (&_Py_NoneStruct)) {
        if (PyCallable_Check(password)) {
            pw_info.callable = password;
        } else if (!_pwinfo_set(&pw_info, password,
                                "password should be a string or callable")) {
            goto error;
        }
        SSL_CTX_set_default_passwd_cb(self->ctx, _password_callback);
        SSL_CTX_set_default_passwd_cb_userdata(self->ctx, &pw_info);
    }
    do { if (_ssl_locks_count>0) { (pw_info.thread_state) = PyEval_SaveThread(); } } while (0);
    r = SSL_CTX_use_certificate_chain_file(self->ctx,
        ((__builtin_expect(!(((((((PyObject*)(certfile_bytes))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_ssl.c", 2051, "PyBytes_Check(certfile_bytes)") : (void)0), (((PyBytesObject *)(certfile_bytes))->ob_sval)));
    do { if (_ssl_locks_count>0) { PyEval_RestoreThread(pw_info.thread_state); } } while (0);
    if (r != 1) {
        if (pw_info.error) {
            ERR_clear_error();

        }
        else if ((*__error()) != 0) {
            ERR_clear_error();
            PyErr_SetFromErrno(PyExc_IOError);
        }
        else {
            _setSSLError(((void *)0), 0, "_ssl.c", 2063);
        }
        goto error;
    }
    do { if (_ssl_locks_count>0) { (pw_info.thread_state) = PyEval_SaveThread(); } } while (0);
    r = SSL_CTX_use_PrivateKey_file(self->ctx,
        ((__builtin_expect(!(((((((PyObject*)(keyfile ? keyfile_bytes : certfile_bytes))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_ssl.c", 2069, "PyBytes_Check(keyfile ? keyfile_bytes : certfile_bytes)") : (void)0), (((PyBytesObject *)(keyfile ? keyfile_bytes : certfile_bytes))->ob_sval)),
        1);
    do { if (_ssl_locks_count>0) { PyEval_RestoreThread(pw_info.thread_state); } } while (0);
    do { if (keyfile_bytes) { PyObject *_py_tmp = (PyObject *)(keyfile_bytes); (keyfile_bytes) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    do { if (certfile_bytes) { PyObject *_py_tmp = (PyObject *)(certfile_bytes); (certfile_bytes) = ((void *)0); do { if ( --((PyObject*)(_py_tmp))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(_py_tmp)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(_py_tmp)))); } while (0); } } while (0);
    if (r != 1) {
        if (pw_info.error) {
            ERR_clear_error();

        }
        else if ((*__error()) != 0) {
            ERR_clear_error();
            PyErr_SetFromErrno(PyExc_IOError);
        }
        else {
            _setSSLError(((void *)0), 0, "_ssl.c", 2084);
        }
        goto error;
    }
    do { if (_ssl_locks_count>0) { (pw_info.thread_state) = PyEval_SaveThread(); } } while (0);
    r = SSL_CTX_check_private_key(self->ctx);
    do { if (_ssl_locks_count>0) { PyEval_RestoreThread(pw_info.thread_state); } } while (0);
    if (r != 1) {
        _setSSLError(((void *)0), 0, "_ssl.c", 2092);
        goto error;
    }
    SSL_CTX_set_default_passwd_cb(self->ctx, orig_passwd_cb);
    SSL_CTX_set_default_passwd_cb_userdata(self->ctx, orig_passwd_userdata);
    free(pw_info.password);
    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);

error:
    SSL_CTX_set_default_passwd_cb(self->ctx, orig_passwd_cb);
    SSL_CTX_set_default_passwd_cb_userdata(self->ctx, orig_passwd_userdata);
    free(pw_info.password);
    do { if ((keyfile_bytes) == ((void *)0)) ; else do { if ( --((PyObject*)(keyfile_bytes))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(keyfile_bytes)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(keyfile_bytes)))); } while (0); } while (0);
    do { if ((certfile_bytes) == ((void *)0)) ; else do { if ( --((PyObject*)(certfile_bytes))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(certfile_bytes)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(certfile_bytes)))); } while (0); } while (0);
    return ((void *)0);
}

static PyObject *
load_verify_locations(PySSLContext *self, PyObject *args, PyObject *kwds)
{
    char *kwlist[] = {"cafile", "capath", ((void *)0)};
    PyObject *cafile = ((void *)0), *capath = ((void *)0);
    PyObject *cafile_bytes = ((void *)0), *capath_bytes = ((void *)0);
    const char *cafile_buf = ((void *)0), *capath_buf = ((void *)0);
    int r;

    (*__error()) = 0;
    if (!PyArg_ParseTupleAndKeywords(args, kwds,
        "|OO:load_verify_locations", kwlist,
        &cafile, &capath))
        return ((void *)0);
    if (cafile == (&_Py_NoneStruct))
        cafile = ((void *)0);
    if (capath == (&_Py_NoneStruct))
        capath = ((void *)0);
    if (cafile == ((void *)0) && capath == ((void *)0)) {
        PyErr_SetString(PyExc_TypeError,
                        "cafile and capath cannot be both omitted");
        return ((void *)0);
    }
    if (cafile && !PyUnicode_FSConverter(cafile, &cafile_bytes)) {
        PyErr_SetString(PyExc_TypeError,
                        "cafile should be a valid filesystem path");
        return ((void *)0);
    }
    if (capath && !PyUnicode_FSConverter(capath, &capath_bytes)) {
        do { if ((cafile_bytes) == ((void *)0)) ; else do { if ( --((PyObject*)(cafile_bytes))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(cafile_bytes)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(cafile_bytes)))); } while (0); } while (0);
        PyErr_SetString(PyExc_TypeError,
                        "capath should be a valid filesystem path");
        return ((void *)0);
    }
    if (cafile)
        cafile_buf = ((__builtin_expect(!(((((((PyObject*)(cafile_bytes))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_ssl.c", 2144, "PyBytes_Check(cafile_bytes)") : (void)0), (((PyBytesObject *)(cafile_bytes))->ob_sval));
    if (capath)
        capath_buf = ((__builtin_expect(!(((((((PyObject*)(capath_bytes))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_ssl.c", 2146, "PyBytes_Check(capath_bytes)") : (void)0), (((PyBytesObject *)(capath_bytes))->ob_sval));
    { PyThreadState *_save = ((void *)0); do { if (_ssl_locks_count>0) { (_save) = PyEval_SaveThread(); } } while (0);
    r = SSL_CTX_load_verify_locations(self->ctx, cafile_buf, capath_buf);
    do { if (_ssl_locks_count>0) { PyEval_RestoreThread(_save); } } while (0); }
    do { if ((cafile_bytes) == ((void *)0)) ; else do { if ( --((PyObject*)(cafile_bytes))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(cafile_bytes)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(cafile_bytes)))); } while (0); } while (0);
    do { if ((capath_bytes) == ((void *)0)) ; else do { if ( --((PyObject*)(capath_bytes))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(capath_bytes)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(capath_bytes)))); } while (0); } while (0);
    if (r != 1) {
        if ((*__error()) != 0) {
            ERR_clear_error();
            PyErr_SetFromErrno(PyExc_IOError);
        }
        else {
            _setSSLError(((void *)0), 0, "_ssl.c", 2158);
        }
        return ((void *)0);
    }
    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}

static PyObject *
load_dh_params(PySSLContext *self, PyObject *filepath)
{
    FILE *f;
    DH *dh;

    f = _Py_fopen(filepath, "rb");
    if (f == ((void *)0)) {
        if (!PyErr_Occurred())
            PyErr_SetFromErrnoWithFilenameObject(PyExc_OSError, filepath);
        return ((void *)0);
    }
    (*__error()) = 0;
    { PyThreadState *_save = ((void *)0); do { if (_ssl_locks_count>0) { (_save) = PyEval_SaveThread(); } } while (0);
    dh = PEM_read_DHparams(f, ((void *)0), ((void *)0), ((void *)0));
    fclose(f);
    do { if (_ssl_locks_count>0) { PyEval_RestoreThread(_save); } } while (0); }
    if (dh == ((void *)0)) {
        if ((*__error()) != 0) {
            ERR_clear_error();
            PyErr_SetFromErrnoWithFilenameObject(PyExc_OSError, filepath);
        }
        else {
            _setSSLError(((void *)0), 0, "_ssl.c", 2188);
        }
        return ((void *)0);
    }
    if (SSL_CTX_ctrl(self->ctx,3,0,(char *)dh) == 0)
        _setSSLError(((void *)0), 0, "_ssl.c", 2193);
    DH_free(dh);
    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}

static PyObject *
context_wrap_socket(PySSLContext *self, PyObject *args, PyObject *kwds)
{
    char *kwlist[] = {"sock", "server_side", "server_hostname", ((void *)0)};
    PySocketSockObject *sock;
    int server_side = 0;
    char *hostname = ((void *)0);
    PyObject *hostname_obj, *res;



    if (!PyArg_ParseTupleAndKeywords(args, kwds, "O!i|O!:_wrap_socket", kwlist,
                                     PySocketModule.Sock_Type,
                                     &sock, &server_side,
                                     (((PyObject*)((&_Py_NoneStruct)))->ob_type), &hostname_obj)) {
        PyErr_Clear();
        if (!PyArg_ParseTupleAndKeywords(args, kwds, "O!iet:_wrap_socket", kwlist,
            PySocketModule.Sock_Type,
            &sock, &server_side,
            "idna", &hostname))
            return ((void *)0);






    }

    res = (PyObject *) newPySSLSocket(self->ctx, sock, server_side,
                                      hostname);
    if (hostname != ((void *)0))
        PyMem_Free(hostname);
    return res;
}

static PyObject *
session_stats(PySSLContext *self, PyObject *unused)
{
    int r;
    PyObject *value, *stats = PyDict_New();
    if (!stats)
        return ((void *)0);
# 2251 "_ssl.c"
    value = PyLong_FromLong(SSL_CTX_ctrl(self->ctx,20,0,((void *)0))); if (value == ((void *)0)) goto error; r = PyDict_SetItemString(stats, "number", value); do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); if (r < 0) goto error;;
    value = PyLong_FromLong(SSL_CTX_ctrl(self->ctx,21,0,((void *)0))); if (value == ((void *)0)) goto error; r = PyDict_SetItemString(stats, "connect", value); do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); if (r < 0) goto error;;
    value = PyLong_FromLong(SSL_CTX_ctrl(self->ctx,22,0,((void *)0))); if (value == ((void *)0)) goto error; r = PyDict_SetItemString(stats, "connect_good", value); do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); if (r < 0) goto error;;
    value = PyLong_FromLong(SSL_CTX_ctrl(self->ctx,23,0,((void *)0))); if (value == ((void *)0)) goto error; r = PyDict_SetItemString(stats, "connect_renegotiate", value); do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); if (r < 0) goto error;;
    value = PyLong_FromLong(SSL_CTX_ctrl(self->ctx,24,0,((void *)0))); if (value == ((void *)0)) goto error; r = PyDict_SetItemString(stats, "accept", value); do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); if (r < 0) goto error;;
    value = PyLong_FromLong(SSL_CTX_ctrl(self->ctx,25,0,((void *)0))); if (value == ((void *)0)) goto error; r = PyDict_SetItemString(stats, "accept_good", value); do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); if (r < 0) goto error;;
    value = PyLong_FromLong(SSL_CTX_ctrl(self->ctx,26,0,((void *)0))); if (value == ((void *)0)) goto error; r = PyDict_SetItemString(stats, "accept_renegotiate", value); do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); if (r < 0) goto error;;
    value = PyLong_FromLong(SSL_CTX_ctrl(self->ctx,24,0,((void *)0))); if (value == ((void *)0)) goto error; r = PyDict_SetItemString(stats, "accept", value); do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); if (r < 0) goto error;;
    value = PyLong_FromLong(SSL_CTX_ctrl(self->ctx,27,0,((void *)0))); if (value == ((void *)0)) goto error; r = PyDict_SetItemString(stats, "hits", value); do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); if (r < 0) goto error;;
    value = PyLong_FromLong(SSL_CTX_ctrl(self->ctx,29,0,((void *)0))); if (value == ((void *)0)) goto error; r = PyDict_SetItemString(stats, "misses", value); do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); if (r < 0) goto error;;
    value = PyLong_FromLong(SSL_CTX_ctrl(self->ctx,30,0,((void *)0))); if (value == ((void *)0)) goto error; r = PyDict_SetItemString(stats, "timeouts", value); do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); if (r < 0) goto error;;
    value = PyLong_FromLong(SSL_CTX_ctrl(self->ctx,31,0,((void *)0))); if (value == ((void *)0)) goto error; r = PyDict_SetItemString(stats, "cache_full", value); do { if ( --((PyObject*)(value))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(value)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(value)))); } while (0); if (r < 0) goto error;;



    return stats;

error:
    do { if ( --((PyObject*)(stats))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(stats)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(stats)))); } while (0);
    return ((void *)0);
}

static PyObject *
set_default_verify_paths(PySSLContext *self, PyObject *unused)
{
    if (!SSL_CTX_set_default_verify_paths(self->ctx)) {
        _setSSLError(((void *)0), 0, "_ssl.c", 2277);
        return ((void *)0);
    }
    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}


static PyObject *
set_ecdh_curve(PySSLContext *self, PyObject *name)
{
    PyObject *name_bytes;
    int nid;
    EC_KEY *key;

    if (!PyUnicode_FSConverter(name, &name_bytes))
        return ((void *)0);
    (__builtin_expect(!(((((((PyObject*)(name_bytes))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_ssl.c", 2293, "PyBytes_Check(name_bytes)") : (void)0);
    nid = OBJ_sn2nid(((__builtin_expect(!(((((((PyObject*)(name_bytes))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_ssl.c", 2294, "PyBytes_Check(name_bytes)") : (void)0), (((PyBytesObject *)(name_bytes))->ob_sval)));
    do { if ( --((PyObject*)(name_bytes))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(name_bytes)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(name_bytes)))); } while (0);
    if (nid == 0) {
        PyErr_Format(PyExc_ValueError,
                     "unknown elliptic curve name %R", name);
        return ((void *)0);
    }
    key = EC_KEY_new_by_curve_name(nid);
    if (key == ((void *)0)) {
        _setSSLError(((void *)0), 0, "_ssl.c", 2303);
        return ((void *)0);
    }
    SSL_CTX_ctrl(self->ctx,4,0,(char *)key);
    EC_KEY_free(key);
    return ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++), (&_Py_NoneStruct);
}


static PyGetSetDef context_getsetlist[] = {
    {"options", (getter) get_options,
                (setter) set_options, ((void *)0)},
    {"verify_mode", (getter) get_verify_mode,
                    (setter) set_verify_mode, ((void *)0)},
    {((void *)0)},
};

static struct PyMethodDef context_methods[] = {
    {"_wrap_socket", (PyCFunction) context_wrap_socket,
                       0x0001 | 0x0002, ((void *)0)},
    {"set_ciphers", (PyCFunction) set_ciphers,
                    0x0001, ((void *)0)},
    {"_set_npn_protocols", (PyCFunction) _set_npn_protocols,
                           0x0001, ((void *)0)},
    {"load_cert_chain", (PyCFunction) load_cert_chain,
                        0x0001 | 0x0002, ((void *)0)},
    {"load_dh_params", (PyCFunction) load_dh_params,
                       0x0008, ((void *)0)},
    {"load_verify_locations", (PyCFunction) load_verify_locations,
                              0x0001 | 0x0002, ((void *)0)},
    {"session_stats", (PyCFunction) session_stats,
                      0x0004, ((void *)0)},
    {"set_default_verify_paths", (PyCFunction) set_default_verify_paths,
                                 0x0004, ((void *)0)},

    {"set_ecdh_curve", (PyCFunction) set_ecdh_curve,
                       0x0008, ((void *)0)},

    {((void *)0), ((void *)0)}
};

static PyTypeObject PySSLContext_Type = {
    { { 1, ((void *)0) }, 0 },
    "_ssl._SSLContext",
    sizeof(PySSLContext),
    0,
    (destructor)context_dealloc,
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
    ( 0 | (1L<<18) | 0) | (1L<<10),
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    context_methods,
    0,
    context_getsetlist,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    context_new,
};






static PyObject *
PySSL_RAND_add(PyObject *self, PyObject *args)
{
    char *buf;
    int len;
    double entropy;

    if (!PyArg_ParseTuple(args, "s#d:RAND_add", &buf, &len, &entropy))
        return ((void *)0);
    RAND_add(buf, len, entropy);
    ( ((PyObject*)((&_Py_NoneStruct)))->ob_refcnt++);
    return (&_Py_NoneStruct);
}

static char PySSL_RAND_add_doc[] = "RAND_add(string, entropy)\n\nMix string into the OpenSSL PRNG state.  entropy (a float) is a lower\nbound on the entropy contained in string.  See RFC 1750.";





static PyObject *
PySSL_RAND(int len, int pseudo)
{
    int ok;
    PyObject *bytes;
    unsigned long err;
    const char *errstr;
    PyObject *v;

    bytes = PyBytes_FromStringAndSize(((void *)0), len);
    if (bytes == ((void *)0))
        return ((void *)0);
    if (pseudo) {
        ok = RAND_pseudo_bytes((unsigned char*)((__builtin_expect(!(((((((PyObject*)(bytes))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_ssl.c", 2423, "PyBytes_Check(bytes)") : (void)0), (((PyBytesObject *)(bytes))->ob_sval)), len);
        if (ok == 0 || ok == 1)
            return Py_BuildValue("NO", bytes, ok == 1 ? ((PyObject *) &_Py_TrueStruct) : ((PyObject *) &_Py_FalseStruct));
    }
    else {
        ok = RAND_bytes((unsigned char*)((__builtin_expect(!(((((((PyObject*)(bytes))->ob_type))->tp_flags & ((1L<<27))) != 0)), 0) ? __assert_rtn(__func__, "_ssl.c", 2428, "PyBytes_Check(bytes)") : (void)0), (((PyBytesObject *)(bytes))->ob_sval)), len);
        if (ok == 1)
            return bytes;
    }
    do { if ( --((PyObject*)(bytes))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(bytes)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(bytes)))); } while (0);

    err = ERR_get_error();
    errstr = ERR_reason_error_string(err);
    v = Py_BuildValue("(ks)", err, errstr);
    if (v != ((void *)0)) {
        PyErr_SetObject(PySSLErrorObject, v);
        do { if ( --((PyObject*)(v))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(v)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(v)))); } while (0);
    }
    return ((void *)0);
}

static PyObject *
PySSL_RAND_bytes(PyObject *self, PyObject *args)
{
    int len;
    if (!PyArg_ParseTuple(args, "i:RAND_bytes", &len))
        return ((void *)0);
    return PySSL_RAND(len, 0);
}

static char PySSL_RAND_bytes_doc[] = "RAND_bytes(n) -> bytes\n\nGenerate n cryptographically strong pseudo-random bytes.";




static PyObject *
PySSL_RAND_pseudo_bytes(PyObject *self, PyObject *args)
{
    int len;
    if (!PyArg_ParseTuple(args, "i:RAND_pseudo_bytes", &len))
        return ((void *)0);
    return PySSL_RAND(len, 1);
}

static char PySSL_RAND_pseudo_bytes_doc[] = "RAND_pseudo_bytes(n) -> (bytes, is_cryptographic)\n\nGenerate n pseudo-random bytes. is_cryptographic is True if the bytesgenerated are cryptographically strong.";





static PyObject *
PySSL_RAND_status(PyObject *self)
{
    return PyLong_FromLong(RAND_status());
}

static char PySSL_RAND_status_doc[] = "RAND_status() -> 0 or 1\n\nReturns 1 if the OpenSSL PRNG has been seeded with enough data and 0 if not.\nIt is necessary to seed the PRNG with RAND_add() on some platforms before\nusing the ssl() function.";






static PyObject *
PySSL_RAND_egd(PyObject *self, PyObject *args)
{
    PyObject *path;
    int bytes;

    if (!PyArg_ParseTuple(args, "O&:RAND_egd",
                          PyUnicode_FSConverter, &path))
        return ((void *)0);

    bytes = RAND_egd(PyBytes_AsString(path));
    do { if ( --((PyObject*)(path))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(path)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(path)))); } while (0);
    if (bytes == -1) {
        PyErr_SetString(PySSLErrorObject,
                        "EGD connection failed or EGD did not return "
                        "enough data to seed the PRNG");
        return ((void *)0);
    }
    return PyLong_FromLong(bytes);
}

static char PySSL_RAND_egd_doc[] = "RAND_egd(path) -> bytes\n\nQueries the entropy gather daemon (EGD) on the socket named by 'path'.\nReturns number of bytes read.  Raises SSLError if connection to EGD\nfails or if it does provide enough data to seed PRNG.";
# 2520 "_ssl.c"
static PyMethodDef PySSL_methods[] = {
    {"_test_decode_cert", PySSL_test_decode_certificate,
     0x0001},

    {"RAND_add", PySSL_RAND_add, 0x0001,
     PySSL_RAND_add_doc},
    {"RAND_bytes", PySSL_RAND_bytes, 0x0001,
     PySSL_RAND_bytes_doc},
    {"RAND_pseudo_bytes", PySSL_RAND_pseudo_bytes, 0x0001,
     PySSL_RAND_pseudo_bytes_doc},
    {"RAND_egd", PySSL_RAND_egd, 0x0001,
     PySSL_RAND_egd_doc},
    {"RAND_status", (PyCFunction)PySSL_RAND_status, 0x0004,
     PySSL_RAND_status_doc},

    {((void *)0), ((void *)0)}
};







static PyThread_type_lock *_ssl_locks = ((void *)0);

static unsigned long _ssl_thread_id_function (void) {
    return PyThread_get_thread_ident();
}

static void _ssl_thread_locking_function
    (int mode, int n, const char *file, int line) {
# 2566 "_ssl.c"
    if ((_ssl_locks == ((void *)0)) ||
        (n < 0) || ((unsigned)n >= _ssl_locks_count))
        return;

    if (mode & 1) {
        PyThread_acquire_lock(_ssl_locks[n], 1);
    } else {
        PyThread_release_lock(_ssl_locks[n]);
    }
}

static int _setup_ssl_threads(void) {

    unsigned int i;

    if (_ssl_locks == ((void *)0)) {
        _ssl_locks_count = CRYPTO_num_locks();
        _ssl_locks = (PyThread_type_lock *)
            malloc(sizeof(PyThread_type_lock) * _ssl_locks_count);
        if (_ssl_locks == ((void *)0))
            return 0;
        ((__builtin_object_size (_ssl_locks, 0) != (size_t) -1) ? __builtin___memset_chk (_ssl_locks, 0, sizeof(PyThread_type_lock) * _ssl_locks_count, __builtin_object_size (_ssl_locks, 0)) : __inline_memset_chk (_ssl_locks, 0, sizeof(PyThread_type_lock) * _ssl_locks_count));

        for (i = 0; i < _ssl_locks_count; i++) {
            _ssl_locks[i] = PyThread_allocate_lock();
            if (_ssl_locks[i] == ((void *)0)) {
                unsigned int j;
                for (j = 0; j < i; j++) {
                    PyThread_free_lock(_ssl_locks[j]);
                }
                free(_ssl_locks);
                return 0;
            }
        }
        CRYPTO_set_locking_callback(_ssl_thread_locking_function);
        CRYPTO_set_id_callback(_ssl_thread_id_function);
    }
    return 1;
}



static char module_doc[] = "Implementation module for SSL socket operations.  See the socket module\nfor documentation.";




static struct PyModuleDef _sslmodule = {
    { { 1, ((void *)0) }, ((void *)0), 0, ((void *)0), },
    "_ssl",
    module_doc,
    -1,
    PySSL_methods,
    ((void *)0),
    ((void *)0),
    ((void *)0),
    ((void *)0)
};


static void
parse_openssl_version(unsigned long libver,
                      unsigned int *major, unsigned int *minor,
                      unsigned int *fix, unsigned int *patch,
                      unsigned int *status)
{
    *status = libver & 0xF;
    libver >>= 4;
    *patch = libver & 0xFF;
    libver >>= 8;
    *fix = libver & 0xFF;
    libver >>= 8;
    *minor = libver & 0xFF;
    libver >>= 8;
    *major = libver & 0xFF;
}

PyObject*
PyInit__ssl(void)
{
    PyObject *m, *d, *r;
    unsigned long libver;
    unsigned int major, minor, fix, patch, status;
    PySocketModule_APIObject *socket_api;
    struct py_ssl_error_code *errcode;
    struct py_ssl_library_code *libcode;

    if (PyType_Ready(&PySSLContext_Type) < 0)
        return ((void *)0);
    if (PyType_Ready(&PySSLSocket_Type) < 0)
        return ((void *)0);

    m = PyModule_Create2(&_sslmodule, 1013);
    if (m == ((void *)0))
        return ((void *)0);
    d = PyModule_GetDict(m);


    socket_api = PyCapsule_Import("_socket" "." "CAPI", 1);
    if (!socket_api)
        return ((void *)0);
    PySocketModule = *socket_api;


    SSL_load_error_strings();
    SSL_library_init();


    if (!_setup_ssl_threads()) {
        return ((void *)0);
    }

    OPENSSL_add_all_algorithms_noconf();


    sslerror_type_slots[0].pfunc = PyExc_OSError;
    PySSLErrorObject = PyType_FromSpec(&sslerror_type_spec);
    if (PySSLErrorObject == ((void *)0))
        return ((void *)0);

    PySSLZeroReturnErrorObject = PyErr_NewExceptionWithDoc(
        "ssl.SSLZeroReturnError", SSLZeroReturnError_doc,
        PySSLErrorObject, ((void *)0));
    PySSLWantReadErrorObject = PyErr_NewExceptionWithDoc(
        "ssl.SSLWantReadError", SSLWantReadError_doc,
        PySSLErrorObject, ((void *)0));
    PySSLWantWriteErrorObject = PyErr_NewExceptionWithDoc(
        "ssl.SSLWantWriteError", SSLWantWriteError_doc,
        PySSLErrorObject, ((void *)0));
    PySSLSyscallErrorObject = PyErr_NewExceptionWithDoc(
        "ssl.SSLSyscallError", SSLSyscallError_doc,
        PySSLErrorObject, ((void *)0));
    PySSLEOFErrorObject = PyErr_NewExceptionWithDoc(
        "ssl.SSLEOFError", SSLEOFError_doc,
        PySSLErrorObject, ((void *)0));
    if (PySSLZeroReturnErrorObject == ((void *)0)
        || PySSLWantReadErrorObject == ((void *)0)
        || PySSLWantWriteErrorObject == ((void *)0)
        || PySSLSyscallErrorObject == ((void *)0)
        || PySSLEOFErrorObject == ((void *)0))
        return ((void *)0);
    if (PyDict_SetItemString(d, "SSLError", PySSLErrorObject) != 0
        || PyDict_SetItemString(d, "SSLZeroReturnError", PySSLZeroReturnErrorObject) != 0
        || PyDict_SetItemString(d, "SSLWantReadError", PySSLWantReadErrorObject) != 0
        || PyDict_SetItemString(d, "SSLWantWriteError", PySSLWantWriteErrorObject) != 0
        || PyDict_SetItemString(d, "SSLSyscallError", PySSLSyscallErrorObject) != 0
        || PyDict_SetItemString(d, "SSLEOFError", PySSLEOFErrorObject) != 0)
        return ((void *)0);
    if (PyDict_SetItemString(d, "_SSLContext",
                             (PyObject *)&PySSLContext_Type) != 0)
        return ((void *)0);
    if (PyDict_SetItemString(d, "_SSLSocket",
                             (PyObject *)&PySSLSocket_Type) != 0)
        return ((void *)0);
    PyModule_AddIntConstant(m, "SSL_ERROR_ZERO_RETURN",
                            PY_SSL_ERROR_ZERO_RETURN);
    PyModule_AddIntConstant(m, "SSL_ERROR_WANT_READ",
                            PY_SSL_ERROR_WANT_READ);
    PyModule_AddIntConstant(m, "SSL_ERROR_WANT_WRITE",
                            PY_SSL_ERROR_WANT_WRITE);
    PyModule_AddIntConstant(m, "SSL_ERROR_WANT_X509_LOOKUP",
                            PY_SSL_ERROR_WANT_X509_LOOKUP);
    PyModule_AddIntConstant(m, "SSL_ERROR_SYSCALL",
                            PY_SSL_ERROR_SYSCALL);
    PyModule_AddIntConstant(m, "SSL_ERROR_SSL",
                            PY_SSL_ERROR_SSL);
    PyModule_AddIntConstant(m, "SSL_ERROR_WANT_CONNECT",
                            PY_SSL_ERROR_WANT_CONNECT);

    PyModule_AddIntConstant(m, "SSL_ERROR_EOF",
                            PY_SSL_ERROR_EOF);
    PyModule_AddIntConstant(m, "SSL_ERROR_INVALID_ERROR_CODE",
                            PY_SSL_ERROR_INVALID_ERROR_CODE);

    PyModule_AddIntConstant(m, "CERT_NONE",
                            PY_SSL_CERT_NONE);
    PyModule_AddIntConstant(m, "CERT_OPTIONAL",
                            PY_SSL_CERT_OPTIONAL);
    PyModule_AddIntConstant(m, "CERT_REQUIRED",
                            PY_SSL_CERT_REQUIRED);



    PyModule_AddIntConstant(m, "PROTOCOL_SSLv2",
                            PY_SSL_VERSION_SSL2);

    PyModule_AddIntConstant(m, "PROTOCOL_SSLv3",
                            PY_SSL_VERSION_SSL3);
    PyModule_AddIntConstant(m, "PROTOCOL_SSLv23",
                            PY_SSL_VERSION_SSL23);
    PyModule_AddIntConstant(m, "PROTOCOL_TLSv1",
                            PY_SSL_VERSION_TLS1);


    PyModule_AddIntConstant(m, "OP_ALL",
                            0x00000FFFL & ~0x00000800L);
    PyModule_AddIntConstant(m, "OP_NO_SSLv2", 0x01000000L);
    PyModule_AddIntConstant(m, "OP_NO_SSLv3", 0x02000000L);
    PyModule_AddIntConstant(m, "OP_NO_TLSv1", 0x04000000L);
    PyModule_AddIntConstant(m, "OP_CIPHER_SERVER_PREFERENCE",
                            0x00400000L);
    PyModule_AddIntConstant(m, "OP_SINGLE_DH_USE", 0x00100000L);

    PyModule_AddIntConstant(m, "OP_SINGLE_ECDH_USE", 0x00080000L);







    r = ((PyObject *) &_Py_TrueStruct);



    ( ((PyObject*)(r))->ob_refcnt++);
    PyModule_AddObject(m, "HAS_SNI", r);


    r = ((PyObject *) &_Py_TrueStruct);



    ( ((PyObject*)(r))->ob_refcnt++);
    PyModule_AddObject(m, "HAS_TLS_UNIQUE", r);




    r = ((PyObject *) &_Py_TrueStruct);

    ( ((PyObject*)(r))->ob_refcnt++);
    PyModule_AddObject(m, "HAS_ECDH", r);




    r = ((PyObject *) &_Py_FalseStruct);

    ( ((PyObject*)(r))->ob_refcnt++);
    PyModule_AddObject(m, "HAS_NPN", r);


    err_codes_to_names = PyDict_New();
    err_names_to_codes = PyDict_New();
    if (err_codes_to_names == ((void *)0) || err_names_to_codes == ((void *)0))
        return ((void *)0);
    errcode = error_codes;
    while (errcode->mnemonic != ((void *)0)) {
        PyObject *mnemo, *key;
        mnemo = PyUnicode_FromString(errcode->mnemonic);
        key = Py_BuildValue("ii", errcode->library, errcode->reason);
        if (mnemo == ((void *)0) || key == ((void *)0))
            return ((void *)0);
        if (PyDict_SetItem(err_codes_to_names, key, mnemo))
            return ((void *)0);
        if (PyDict_SetItem(err_names_to_codes, mnemo, key))
            return ((void *)0);
        do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
        do { if ( --((PyObject*)(mnemo))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(mnemo)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(mnemo)))); } while (0);
        errcode++;
    }
    if (PyModule_AddObject(m, "err_codes_to_names", err_codes_to_names))
        return ((void *)0);
    if (PyModule_AddObject(m, "err_names_to_codes", err_names_to_codes))
        return ((void *)0);

    lib_codes_to_names = PyDict_New();
    if (lib_codes_to_names == ((void *)0))
        return ((void *)0);
    libcode = library_codes;
    while (libcode->library != ((void *)0)) {
        PyObject *mnemo, *key;
        key = PyLong_FromLong(libcode->code);
        mnemo = PyUnicode_FromString(libcode->library);
        if (key == ((void *)0) || mnemo == ((void *)0))
            return ((void *)0);
        if (PyDict_SetItem(lib_codes_to_names, key, mnemo))
            return ((void *)0);
        do { if ( --((PyObject*)(key))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(key)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(key)))); } while (0);
        do { if ( --((PyObject*)(mnemo))->ob_refcnt != 0) ; else ( (*(((PyObject*)((PyObject *)(mnemo)))->ob_type)->tp_dealloc)((PyObject *)((PyObject *)(mnemo)))); } while (0);
        libcode++;
    }
    if (PyModule_AddObject(m, "lib_codes_to_names", lib_codes_to_names))
        return ((void *)0);





    libver = SSLeay();
    r = PyLong_FromUnsignedLong(libver);
    if (r == ((void *)0))
        return ((void *)0);
    if (PyModule_AddObject(m, "OPENSSL_VERSION_NUMBER", r))
        return ((void *)0);
    parse_openssl_version(libver, &major, &minor, &fix, &patch, &status);
    r = Py_BuildValue("IIIII", major, minor, fix, patch, status);
    if (r == ((void *)0) || PyModule_AddObject(m, "OPENSSL_VERSION_INFO", r))
        return ((void *)0);
    r = PyUnicode_FromString(SSLeay_version(0));
    if (r == ((void *)0) || PyModule_AddObject(m, "OPENSSL_VERSION", r))
        return ((void *)0);

    libver = 0x0090812fL;
    parse_openssl_version(libver, &major, &minor, &fix, &patch, &status);
    r = Py_BuildValue("IIIII", major, minor, fix, patch, status);
    if (r == ((void *)0) || PyModule_AddObject(m, "_OPENSSL_API_VERSION", r))
        return ((void *)0);

    return m;
}
