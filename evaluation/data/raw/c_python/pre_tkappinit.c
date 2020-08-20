# 1 "tkappinit.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "tkappinit.c"
# 15 "tkappinit.c"
# 1 "/usr/include/string.h" 1 3 4
# 61 "/usr/include/string.h" 3 4
# 1 "/usr/include/_types.h" 1 3 4
# 27 "/usr/include/_types.h" 3 4
# 1 "/usr/include/sys/_types.h" 1 3 4
# 32 "/usr/include/sys/_types.h" 3 4
# 1 "/usr/include/sys/cdefs.h" 1 3 4
# 417 "/usr/include/sys/cdefs.h" 3 4
# 1 "/usr/include/sys/_symbol_aliasing.h" 1 3 4
# 418 "/usr/include/sys/cdefs.h" 2 3 4
# 494 "/usr/include/sys/cdefs.h" 3 4
# 1 "/usr/include/sys/_posix_availability.h" 1 3 4
# 495 "/usr/include/sys/cdefs.h" 2 3 4
# 33 "/usr/include/sys/_types.h" 2 3 4
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
# 62 "/usr/include/string.h" 2 3 4


# 1 "/usr/include/Availability.h" 1 3 4
# 141 "/usr/include/Availability.h" 3 4
# 1 "/usr/include/AvailabilityInternal.h" 1 3 4
# 142 "/usr/include/Availability.h" 2 3 4
# 65 "/usr/include/string.h" 2 3 4



typedef __darwin_size_t size_t;
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

# 155 "/usr/include/string.h" 3 4
typedef __darwin_ssize_t ssize_t;



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
# 32 "/usr/include/secure/_string.h" 3 4
# 1 "/usr/include/secure/_common.h" 1 3 4
# 33 "/usr/include/secure/_string.h" 2 3 4
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
# 16 "tkappinit.c" 2
# 1 "/usr/include/tcl.h" 1 3 4
# 141 "/usr/include/tcl.h" 3 4
# 1 "/usr/include/stdio.h" 1 3 4
# 73 "/usr/include/stdio.h" 3 4
typedef __darwin_va_list va_list;
# 85 "/usr/include/stdio.h" 3 4
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



FILE *fopen(const char * , const char * ) __asm("_" "fopen" );

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





FILE *fdopen(int, const char *) __asm("_" "fdopen" );

int fileno(FILE *);

# 318 "/usr/include/stdio.h" 3 4

int pclose(FILE *);



FILE *popen(const char *, const char *) __asm("_" "popen" );


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

# 445 "/usr/include/stdio.h" 3 4

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
# 142 "/usr/include/tcl.h" 2 3 4
# 153 "/usr/include/tcl.h" 3 4
# 1 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stdarg.h" 1 3 4
# 43 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stdarg.h" 3 4
typedef __builtin_va_list __gnuc_va_list;
# 154 "/usr/include/tcl.h" 2 3 4
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
typedef int (Tcl_CmdProc) (ClientData clientData, Tcl_Interp *interp, int argc, const char *argv[]);

typedef void (Tcl_CmdTraceProc) (ClientData clientData, Tcl_Interp *interp, int level, char *command, Tcl_CmdProc *proc, ClientData cmdClientData, int argc, const char *argv[]);


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
typedef char *(Tcl_VarTraceProc) (ClientData clientData, Tcl_Interp *interp, const char *part1, const char *part2, int flags);


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

typedef int (Tcl_DriverOutputProc) (ClientData instanceData, const char *buf, int toWrite, int *errorCodePtr);

typedef int (Tcl_DriverSeekProc) (ClientData instanceData, long offset, int mode, int *errorCodePtr);

typedef int (Tcl_DriverSetOptionProc) ( ClientData instanceData, Tcl_Interp *interp, const char *optionName, const char *value);


typedef int (Tcl_DriverGetOptionProc) ( ClientData instanceData, Tcl_Interp *interp, const char *optionName, Tcl_DString *dsPtr);


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
    Tcl_Obj *objPtr, const char **tablePtr,
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




extern char * Tcl_Concat(int argc, const char *const *argv);




extern int Tcl_ConvertElement(const char *src, char *dst,
    int flags);




extern int Tcl_ConvertCountedElement(const char *src,
    int length, char *dst, int flags);




extern int Tcl_CreateAlias(Tcl_Interp *slave,
    const char *slaveCmd, Tcl_Interp *target,
    const char *targetCmd, int argc,
    const char *const *argv);




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
    const char **targetCmdPtr, int *argcPtr,
    const char ***argvPtr);




extern int Tcl_GetAliasObj(Tcl_Interp *interp,
    const char *slaveCmd,
    Tcl_Interp **targetInterpPtr,
    const char **targetCmdPtr, int *objcPtr,
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




extern char * Tcl_JoinPath(int argc, const char *const *argv,
    Tcl_DString *resultPtr);




extern int Tcl_LinkVar(Tcl_Interp *interp, const char *varName,
    char *addr, int type);





extern Tcl_Channel Tcl_MakeFileChannel(ClientData handle, int mode);




extern int Tcl_MakeSafe(Tcl_Interp *interp);




extern Tcl_Channel Tcl_MakeTcpClientChannel(ClientData tcpSocket);




extern char * Tcl_Merge(int argc, const char *const *argv);




extern Tcl_HashEntry * Tcl_NextHashEntry(Tcl_HashSearch *searchPtr);




extern void Tcl_NotifyChannel(Tcl_Channel channel, int mask);




extern Tcl_Obj * Tcl_ObjGetVar2(Tcl_Interp *interp, Tcl_Obj *part1Ptr,
    Tcl_Obj *part2Ptr, int flags);




extern Tcl_Obj * Tcl_ObjSetVar2(Tcl_Interp *interp, Tcl_Obj *part1Ptr,
    Tcl_Obj *part2Ptr, Tcl_Obj *newValuePtr,
    int flags);




extern Tcl_Channel Tcl_OpenCommandChannel(Tcl_Interp *interp, int argc,
    const char **argv, int flags);




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
    const char **startPtr,
    const char **endPtr);




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
    const char ***argvPtr);




extern void Tcl_SplitPath(const char *path, int *argcPtr,
    const char ***argvPtr);




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
    const char *start, const char **termPtr);




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
    const char **termPtr);




extern int Tcl_ParseCommand(Tcl_Interp *interp,
    const char *start, int numBytes, int nested,
    Tcl_Parse *parsePtr);




extern int Tcl_ParseExpr(Tcl_Interp *interp, const char *start,
    int numBytes, Tcl_Parse *parsePtr);




extern int Tcl_ParseQuotedString(Tcl_Interp *interp,
    const char *start, int numBytes,
    Tcl_Parse *parsePtr, int append,
    const char **termPtr);




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
    int (*tcl_GetIndexFromObj) (Tcl_Interp *interp, Tcl_Obj *objPtr, const char **tablePtr, const char *msg, int flags, int *indexPtr);
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
    char * (*tcl_Concat) (int argc, const char *const *argv);
    int (*tcl_ConvertElement) (const char *src, char *dst, int flags);
    int (*tcl_ConvertCountedElement) (const char *src, int length, char *dst, int flags);
    int (*tcl_CreateAlias) (Tcl_Interp *slave, const char *slaveCmd, Tcl_Interp *target, const char *targetCmd, int argc, const char *const *argv);
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
    int (*tcl_GetAlias) (Tcl_Interp *interp, const char *slaveCmd, Tcl_Interp **targetInterpPtr, const char **targetCmdPtr, int *argcPtr, const char ***argvPtr);
    int (*tcl_GetAliasObj) (Tcl_Interp *interp, const char *slaveCmd, Tcl_Interp **targetInterpPtr, const char **targetCmdPtr, int *objcPtr, Tcl_Obj ***objv);
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
    char * (*tcl_JoinPath) (int argc, const char *const *argv, Tcl_DString *resultPtr);
    int (*tcl_LinkVar) (Tcl_Interp *interp, const char *varName, char *addr, int type);
    void *reserved188;
    Tcl_Channel (*tcl_MakeFileChannel) (ClientData handle, int mode);
    int (*tcl_MakeSafe) (Tcl_Interp *interp);
    Tcl_Channel (*tcl_MakeTcpClientChannel) (ClientData tcpSocket);
    char * (*tcl_Merge) (int argc, const char *const *argv);
    Tcl_HashEntry * (*tcl_NextHashEntry) (Tcl_HashSearch *searchPtr);
    void (*tcl_NotifyChannel) (Tcl_Channel channel, int mask);
    Tcl_Obj * (*tcl_ObjGetVar2) (Tcl_Interp *interp, Tcl_Obj *part1Ptr, Tcl_Obj *part2Ptr, int flags);
    Tcl_Obj * (*tcl_ObjSetVar2) (Tcl_Interp *interp, Tcl_Obj *part1Ptr, Tcl_Obj *part2Ptr, Tcl_Obj *newValuePtr, int flags);
    Tcl_Channel (*tcl_OpenCommandChannel) (Tcl_Interp *interp, int argc, const char **argv, int flags);
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
    void (*tcl_RegExpRange) (Tcl_RegExp regexp, int index, const char **startPtr, const char **endPtr);
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
    int (*tcl_SplitList) (Tcl_Interp *interp, const char *listStr, int *argcPtr, const char ***argvPtr);
    void (*tcl_SplitPath) (const char *path, int *argcPtr, const char ***argvPtr);
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
    const char * (*tcl_ParseVar) (Tcl_Interp *interp, const char *start, const char **termPtr);
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
    int (*tcl_ParseBraces) (Tcl_Interp *interp, const char *start, int numBytes, Tcl_Parse *parsePtr, int append, const char **termPtr);
    int (*tcl_ParseCommand) (Tcl_Interp *interp, const char *start, int numBytes, int nested, Tcl_Parse *parsePtr);
    int (*tcl_ParseExpr) (Tcl_Interp *interp, const char *start, int numBytes, Tcl_Parse *parsePtr);
    int (*tcl_ParseQuotedString) (Tcl_Interp *interp, const char *start, int numBytes, Tcl_Parse *parsePtr, int append, const char **termPtr);
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
# 17 "tkappinit.c" 2
# 1 "/usr/include/tk.h" 1 3 4
# 78 "/usr/include/tk.h" 3 4
# 1 "/usr/include/X11/Xlib.h" 1 3 4
# 38 "/usr/include/X11/Xlib.h" 3 4
# 1 "/usr/include/sys/types.h" 1 3 4
# 72 "/usr/include/sys/types.h" 3 4
# 1 "/usr/include/sys/appleapiopts.h" 1 3 4
# 73 "/usr/include/sys/types.h" 2 3 4





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
# 79 "/usr/include/sys/types.h" 2 3 4


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
# 82 "/usr/include/sys/types.h" 2 3 4


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


typedef __darwin_dev_t dev_t;



typedef u_int32_t fixpt_t;


typedef __darwin_blkcnt_t blkcnt_t;




typedef __darwin_blksize_t blksize_t;




typedef __darwin_gid_t gid_t;





typedef __uint32_t in_addr_t;




typedef __uint16_t in_port_t;



typedef __darwin_ino_t ino_t;





typedef __darwin_ino64_t ino64_t;






typedef __int32_t key_t;



typedef __darwin_mode_t mode_t;




typedef __uint16_t nlink_t;





typedef __darwin_id_t id_t;



typedef __darwin_pid_t pid_t;
# 176 "/usr/include/sys/types.h" 3 4
typedef int32_t segsz_t;
typedef int32_t swblk_t;


typedef __darwin_uid_t uid_t;
# 223 "/usr/include/sys/types.h" 3 4
typedef __darwin_clock_t clock_t;
# 240 "/usr/include/sys/types.h" 3 4
typedef __darwin_time_t time_t;




typedef __darwin_useconds_t useconds_t;




typedef __darwin_suseconds_t suseconds_t;
# 260 "/usr/include/sys/types.h" 3 4
# 1 "/usr/include/sys/_structs.h" 1 3 4
# 183 "/usr/include/sys/_structs.h" 3 4

typedef struct fd_set {
 __int32_t fds_bits[((((1024) % ((sizeof(__int32_t) * 8))) == 0) ? ((1024) / ((sizeof(__int32_t) * 8))) : (((1024) / ((sizeof(__int32_t) * 8))) + 1))];
} fd_set;



static __inline int
__darwin_fd_isset(int _n, const struct fd_set *_p)
{
 return (_p->fds_bits[_n/(sizeof(__int32_t) * 8)] & (1<<(_n % (sizeof(__int32_t) * 8))));
}
# 261 "/usr/include/sys/types.h" 2 3 4




typedef __int32_t fd_mask;
# 318 "/usr/include/sys/types.h" 3 4
typedef __darwin_pthread_attr_t pthread_attr_t;



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
# 326 "/Developer/usr/llvm-gcc-4.2/lib/gcc/i686-apple-darwin11/4.2.1/include/stddef.h" 3 4
typedef int wchar_t;
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
typedef int (Tk_OptionParseProc) (ClientData clientData, Tcl_Interp *interp, Tk_Window tkwin, const char *value, char *widgRec, int offset);


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
    int argc, const char **argv, char *widgRec,
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
    const char **argv, double *dblPtr,
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
    int *argcPtr, const char **argv,
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
    int (*tk_ConfigureWidget) (Tcl_Interp *interp, Tk_Window tkwin, Tk_ConfigSpec *specs, int argc, const char **argv, char *widgRec, int flags);
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
    int (*tk_GetScrollInfo) (Tcl_Interp *interp, int argc, const char **argv, double *dblPtr, int *intPtr);
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
    int (*tk_ParseArgv) (Tcl_Interp *interp, Tk_Window tkwin, int *argcPtr, const char **argv, Tk_ArgvInfo *argTable, int flags);
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
# 18 "tkappinit.c" 2

# 1 "tkinter.h" 1
# 20 "tkappinit.c" 2






int
Tcl_AppInit(Tcl_Interp *interp)
{



    const char *_tkinter_skip_tk_init;
# 60 "tkappinit.c"
    if (Tcl_Init (interp) == 1)
        return 1;
# 89 "tkappinit.c"
    _tkinter_skip_tk_init = Tcl_GetVar(interp,
                    "_tkinter_skip_tk_init", 1);
    if (_tkinter_skip_tk_init != ((void *)0) &&
                    strcmp(_tkinter_skip_tk_init, "1") == 0) {
        return 0;
    }
# 108 "tkappinit.c"
    if (Tk_Init(interp) == 1) {




        return 1;
    }




    Tk_MainWindow(interp);
# 184 "tkappinit.c"
    return 0;
}
