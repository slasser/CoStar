# 1 "getaddrinfo.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "getaddrinfo.c"
# 74 "getaddrinfo.c"
static const char in_addrany[] = { 0, 0, 0, 0 };
static const char in6_addrany[] = {
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
};
static const char in_loopback[] = { 127, 0, 0, 1 };
static const char in6_loopback[] = {
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1
};

struct sockinet {
    u_char si_len;
    u_char si_family;
    u_short si_port;
};

static struct gai_afd {
    int a_af;
    int a_addrlen;
    int a_socklen;
    int a_off;
    const char *a_addrany;
    const char *a_loopback;
} gai_afdl [] = {
# 107 "getaddrinfo.c"
    {PF_INET, sizeof(struct in_addr),
     sizeof(struct sockaddr_in),
     __builtin_offsetof(struct sockaddr_in, sin_addr),
     in_addrany, in_loopback},
    {0, 0, 0, 0, NULL, NULL},
};
# 132 "getaddrinfo.c"
static int get_name(const char *, struct gai_afd *,
                          struct addrinfo **, char *, struct addrinfo *,
                          int);
static int get_addr(const char *, int, struct addrinfo **,
                        struct addrinfo *, int);
static int str_isnumber(const char *);

static char *ai_errlist[] = {
    "success.",
    "address family for hostname not supported.",
    "temporary failure in name resolution.",
    "invalid value for ai_flags.",
    "non-recoverable failure in name resolution.",
    "ai_family not supported.",
    "memory allocation failure.",
    "no address associated with hostname.",
    "hostname nor servname provided, or not known.",
    "servname not supported for ai_socktype.",
    "ai_socktype not supported.",
    "system error returned in errno.",
    "invalid value for hints.",
    "resolved protocol is unknown.",
    "unknown error.",
};
# 201 "getaddrinfo.c"
char *
gai_strerror(int ecode)
{
    if (ecode < 0 || ecode > EAI_MAX)
        ecode = EAI_MAX;
    return ai_errlist[ecode];
}

void
freeaddrinfo(struct addrinfo *ai)
{
    struct addrinfo *next;

    do {
        next = ai->ai_next;
        if (ai->ai_canonname)
            free(ai->ai_canonname);

        free(ai);
    } while ((ai = next) != NULL);
}

static int
str_isnumber(const char *p)
{
    unsigned char *q = (unsigned char *)p;
    while (*q) {
        if (! isdigit(*q))
            return 0;
        q++;
    }
    return 1;
}

int
getaddrinfo(const char*hostname, const char*servname,
            const struct addrinfo *hints, struct addrinfo **res)
{
    struct addrinfo sentinel;
    struct addrinfo *top = NULL;
    struct addrinfo *cur;
    int i, error = 0;
    char pton[4];
    struct addrinfo ai;
    struct addrinfo *pai;
    u_short port;
# 263 "getaddrinfo.c"
    sentinel.ai_next = NULL;
    cur = &sentinel;
    pai = &ai;
    pai->ai_flags = 0;
    pai->ai_family = PF_UNSPEC;
    pai->ai_socktype = 0;
    pai->ai_protocol = 0;
    pai->ai_addrlen = 0;
    pai->ai_canonname = NULL;
    pai->ai_addr = NULL;
    pai->ai_next = NULL;
    port = 0;

    if (hostname == NULL && servname == NULL)
        return EAI_NONAME;
    if (hints) {

        if (hints->ai_addrlen || hints->ai_canonname ||
            hints->ai_addr || hints->ai_next)
            { error = (EAI_BADHINTS); goto bad; };
        if (hints->ai_flags & ~AI_MASK)
            { error = (EAI_BADFLAGS); goto bad; };
        switch (hints->ai_family) {
        case PF_UNSPEC:
        case PF_INET:



            break;
        default:
            { error = (EAI_FAMILY); goto bad; };
        }
        memcpy(pai, hints, sizeof(*pai));
        switch (pai->ai_socktype) {
        case 0:
            switch (pai->ai_protocol) {
            case 0:
                break;
            case IPPROTO_UDP:
                pai->ai_socktype = SOCK_DGRAM;
                break;
            case IPPROTO_TCP:
                pai->ai_socktype = SOCK_STREAM;
                break;
            default:
                pai->ai_socktype = SOCK_RAW;
                break;
            }
            break;
        case SOCK_RAW:
            break;
        case SOCK_DGRAM:
            if (pai->ai_protocol != IPPROTO_UDP &&
                pai->ai_protocol != 0)
                { error = (EAI_BADHINTS); goto bad; };
            pai->ai_protocol = IPPROTO_UDP;
            break;
        case SOCK_STREAM:
            if (pai->ai_protocol != IPPROTO_TCP &&
                pai->ai_protocol != 0)
                { error = (EAI_BADHINTS); goto bad; };
            pai->ai_protocol = IPPROTO_TCP;
            break;
        default:
            { error = (EAI_SOCKTYPE); goto bad; };

        }
    }




    if (servname) {
        if (str_isnumber(servname)) {
            if (pai->ai_socktype == 0) {

                pai->ai_socktype = SOCK_DGRAM;
                pai->ai_protocol = IPPROTO_UDP;
            }
            port = htons((u_short)atoi(servname));
        } else {
            struct servent *sp;
            char *proto;

            proto = NULL;
            switch (pai->ai_socktype) {
            case 0:
                proto = NULL;
                break;
            case SOCK_DGRAM:
                proto = "udp";
                break;
            case SOCK_STREAM:
                proto = "tcp";
                break;
            default:
                fprintf(stderr, "panic!\n");
                break;
            }
            if ((sp = getservbyname(servname, proto)) == NULL)
                { error = (EAI_SERVICE); goto bad; };
            port = sp->s_port;
            if (pai->ai_socktype == 0) {
                if (strcmp(sp->s_proto, "udp") == 0) {
                    pai->ai_socktype = SOCK_DGRAM;
                    pai->ai_protocol = IPPROTO_UDP;
                } else if (strcmp(sp->s_proto, "tcp") == 0) {
                    pai->ai_socktype = SOCK_STREAM;
                    pai->ai_protocol = IPPROTO_TCP;
                } else
                    { error = (EAI_PROTOCOL); goto bad; };
            }
        }
    }






    if (hostname == NULL) {
        struct gai_afd *gai_afd;

        for (gai_afd = &gai_afdl[0]; gai_afd->a_af; gai_afd++) {
            if (!(pai->ai_family == PF_UNSPEC
               || pai->ai_family == gai_afd->a_af)) {
                continue;
            }

            if (pai->ai_flags & AI_PASSIVE) {
                { char *p; if (((cur->ai_next) = (struct addrinfo *)malloc(sizeof(struct addrinfo) + ((gai_afd)->a_socklen))) == NULL) goto free; memcpy(cur->ai_next, pai, sizeof(struct addrinfo)); (cur->ai_next)->ai_addr = (struct sockaddr *)((cur->ai_next) + 1); memset((cur->ai_next)->ai_addr, 0, (gai_afd)->a_socklen); (cur->ai_next)->ai_addrlen = (gai_afd)->a_socklen; (cur->ai_next)->ai_addr->sa_family = (cur->ai_next)->ai_family = (gai_afd)->a_af; ((struct sockinet *)(cur->ai_next)->ai_addr)->si_port = port; p = (char *)((cur->ai_next)->ai_addr); memcpy(p + (gai_afd)->a_off, (gai_afd->a_addrany), (gai_afd)->a_addrlen);};



            } else {
                { char *p; if (((cur->ai_next) = (struct addrinfo *)malloc(sizeof(struct addrinfo) + ((gai_afd)->a_socklen))) == NULL) goto free; memcpy(cur->ai_next, pai, sizeof(struct addrinfo)); (cur->ai_next)->ai_addr = (struct sockaddr *)((cur->ai_next) + 1); memset((cur->ai_next)->ai_addr, 0, (gai_afd)->a_socklen); (cur->ai_next)->ai_addrlen = (gai_afd)->a_socklen; (cur->ai_next)->ai_addr->sa_family = (cur->ai_next)->ai_family = (gai_afd)->a_af; ((struct sockinet *)(cur->ai_next)->ai_addr)->si_port = port; p = (char *)((cur->ai_next)->ai_addr); memcpy(p + (gai_afd)->a_off, (gai_afd->a_loopback), (gai_afd)->a_addrlen);};




            }
            cur = cur->ai_next;
        }
        top = sentinel.ai_next;
        if (top)
            goto good;
        else
            { error = (EAI_FAMILY); goto bad; };
    }


    for (i = 0; gai_afdl[i].a_af; i++) {
        if (inet_pton(gai_afdl[i].a_af, hostname, pton)) {
            u_long v4a;




            switch (gai_afdl[i].a_af) {
            case AF_INET:
                v4a = ((struct in_addr *)pton)->s_addr;
                v4a = ntohl(v4a);
                if ((((v4a) & 0xf0000000U) == 0xe0000000U) || (((v4a) & 0xe0000000U) == 0xe0000000U))
                    pai->ai_flags &= ~AI_CANONNAME;
                v4a >>= IN_CLASSA_NSHIFT;
                if (v4a == 0 || v4a == 127)
                    pai->ai_flags &= ~AI_CANONNAME;
                break;







            }

            if (pai->ai_family == gai_afdl[i].a_af ||
                pai->ai_family == PF_UNSPEC) {
                if (! (pai->ai_flags & AI_CANONNAME)) {
                    { char *p; if (((top) = (struct addrinfo *)malloc(sizeof(struct addrinfo) + ((&gai_afdl[i])->a_socklen))) == NULL) goto free; memcpy(top, pai, sizeof(struct addrinfo)); (top)->ai_addr = (struct sockaddr *)((top) + 1); memset((top)->ai_addr, 0, (&gai_afdl[i])->a_socklen); (top)->ai_addrlen = (&gai_afdl[i])->a_socklen; (top)->ai_addr->sa_family = (top)->ai_family = (&gai_afdl[i])->a_af; ((struct sockinet *)(top)->ai_addr)->si_port = port; p = (char *)((top)->ai_addr); memcpy(p + (&gai_afdl[i])->a_off, (pton), (&gai_afdl[i])->a_addrlen);};
                    goto good;
                }
# 455 "getaddrinfo.c"
                get_name(pton, &gai_afdl[i], &top, pton, pai, port);
                goto good;
            } else
                { error = (EAI_FAMILY); goto bad; };
        }
    }

    if (pai->ai_flags & AI_NUMERICHOST)
        { error = (EAI_NONAME); goto bad; };


    error = get_addr(hostname, pai->ai_family, &top, pai, port);
    if (error == 0) {
        if (top) {
 good:
            *res = top;
            return 0;
        } else
            error = EAI_FAIL;
    }
 free:
    if (top)
        freeaddrinfo(top);
 bad:
    *res = NULL;
    return error;
}

static int
get_name(addr, gai_afd, res, numaddr, pai, port0)
    const char *addr;
    struct gai_afd *gai_afd;
    struct addrinfo **res;
    char *numaddr;
    struct addrinfo *pai;
    int port0;
{
    u_short port = port0 & 0xffff;
    struct hostent *hp;
    struct addrinfo *cur;
    int error = 0;







    hp = gethostbyaddr(addr, gai_afd->a_addrlen, AF_INET);

    if (hp && hp->h_name && hp->h_name[0] && hp->h_addr_list[0]) {
        { char *p; if (((cur) = (struct addrinfo *)malloc(sizeof(struct addrinfo) + ((gai_afd)->a_socklen))) == NULL) goto free; memcpy(cur, pai, sizeof(struct addrinfo)); (cur)->ai_addr = (struct sockaddr *)((cur) + 1); memset((cur)->ai_addr, 0, (gai_afd)->a_socklen); (cur)->ai_addrlen = (gai_afd)->a_socklen; (cur)->ai_addr->sa_family = (cur)->ai_family = (gai_afd)->a_af; ((struct sockinet *)(cur)->ai_addr)->si_port = port; p = (char *)((cur)->ai_addr); memcpy(p + (gai_afd)->a_off, (hp->h_addr_list[0]), (gai_afd)->a_addrlen);};
        if (pai->ai_flags & AI_CANONNAME) { if (((cur)->ai_canonname = (char *)malloc(strlen(hp->h_name) + 1)) != NULL) { strcpy((cur)->ai_canonname, (hp->h_name)); } else { error = EAI_MEMORY; goto free; }};
    } else
        { char *p; if (((cur) = (struct addrinfo *)malloc(sizeof(struct addrinfo) + ((gai_afd)->a_socklen))) == NULL) goto free; memcpy(cur, pai, sizeof(struct addrinfo)); (cur)->ai_addr = (struct sockaddr *)((cur) + 1); memset((cur)->ai_addr, 0, (gai_afd)->a_socklen); (cur)->ai_addrlen = (gai_afd)->a_socklen; (cur)->ai_addr->sa_family = (cur)->ai_family = (gai_afd)->a_af; ((struct sockinet *)(cur)->ai_addr)->si_port = port; p = (char *)((cur)->ai_addr); memcpy(p + (gai_afd)->a_off, (numaddr), (gai_afd)->a_addrlen);};





    *res = cur;
    return 0;
 free:
    if (cur)
        freeaddrinfo(cur);





    *res = NULL;
    return error;
}

static int
get_addr(hostname, af, res, pai, port0)
    const char *hostname;
    int af;
    struct addrinfo **res;
    struct addrinfo *pai;
    int port0;
{
    u_short port = port0 & 0xffff;
    struct addrinfo sentinel;
    struct hostent *hp;
    struct addrinfo *top, *cur;
    struct gai_afd *gai_afd;
    int i, error = 0, h_error;
    char *ap;

    top = NULL;
    sentinel.ai_next = NULL;
    cur = &sentinel;







    hp = gethostbyname(hostname);
    h_error = h_errno;

    if (hp == NULL) {
        switch (h_error) {
        case HOST_NOT_FOUND:
        case NO_DATA:
            error = EAI_NODATA;
            break;
        case TRY_AGAIN:
            error = EAI_AGAIN;
            break;
        case NO_RECOVERY:
        default:
            error = EAI_FAIL;
            break;
        }
        goto free;
    }

    if ((hp->h_name == NULL) || (hp->h_name[0] == 0) ||
        (hp->h_addr_list[0] == NULL)) {
        error = EAI_FAIL;
        goto free;
    }

    for (i = 0; (ap = hp->h_addr_list[i]) != NULL; i++) {
        switch (af) {






        default:

        case AF_INET:
            gai_afd = &gai_afdl[0];
            break;
# 604 "getaddrinfo.c"
        }
# 616 "getaddrinfo.c"
        { char *p; if (((cur->ai_next) = (struct addrinfo *)malloc(sizeof(struct addrinfo) + ((gai_afd)->a_socklen))) == NULL) goto free; memcpy(cur->ai_next, pai, sizeof(struct addrinfo)); (cur->ai_next)->ai_addr = (struct sockaddr *)((cur->ai_next) + 1); memset((cur->ai_next)->ai_addr, 0, (gai_afd)->a_socklen); (cur->ai_next)->ai_addrlen = (gai_afd)->a_socklen; (cur->ai_next)->ai_addr->sa_family = (cur->ai_next)->ai_family = (gai_afd)->a_af; ((struct sockinet *)(cur->ai_next)->ai_addr)->si_port = port; p = (char *)((cur->ai_next)->ai_addr); memcpy(p + (gai_afd)->a_off, (ap), (gai_afd)->a_addrlen);};
        if (cur == &sentinel) {
            top = cur->ai_next;
            if (pai->ai_flags & AI_CANONNAME) { if (((top)->ai_canonname = (char *)malloc(strlen(hp->h_name) + 1)) != NULL) { strcpy((top)->ai_canonname, (hp->h_name)); } else { error = EAI_MEMORY; goto free; }};
        }
        cur = cur->ai_next;
    }



    *res = top;
    return 0;
 free:
    if (top)
        freeaddrinfo(top);





    *res = NULL;
    return error;
}
