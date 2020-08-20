# 1 "getnameinfo.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "getnameinfo.c"
# 55 "getnameinfo.c"
static struct gni_afd {
    int a_af;
    int a_addrlen;
    int a_socklen;
    int a_off;
} gni_afdl [] = {




    {PF_INET, sizeof(struct in_addr), sizeof(struct sockaddr_in),
        __builtin_offsetof(struct sockaddr_in, sin_addr)},
    {0, 0, 0},
};

struct gni_sockinet {
    u_char si_len;
    u_char si_family;
    u_short si_port;
};
# 85 "getnameinfo.c"
int getnameinfo(const struct sockaddr *, size_t, char *, size_t,
                          char *, size_t, int);

int
getnameinfo(sa, salen, host, hostlen, serv, servlen, flags)
    const struct sockaddr *sa;
    size_t salen;
    char *host;
    size_t hostlen;
    char *serv;
    size_t servlen;
    int flags;
{
    struct gni_afd *gni_afd;
    struct servent *sp;
    struct hostent *hp;
    u_short port;
    int family, len, i;
    char *addr, *p;
    u_long v4a;



    int h_error;
    char numserv[512];
    char numaddr[512];

    if (sa == NULL)
        return 0;





    len = salen;


    family = sa->sa_family;
    for (i = 0; gni_afdl[i].a_af; i++)
        if (gni_afdl[i].a_af == family) {
            gni_afd = &gni_afdl[i];
            goto found;
        }
    return 5;

 found:
    if (len != gni_afd->a_socklen) return 6;

    port = ((struct gni_sockinet *)sa)->si_port;
    addr = (char *)sa + gni_afd->a_off;

    if (serv == NULL || servlen == 0) {

    } else if (flags & NI_NUMERICSERV) {
        sprintf(numserv, "%d", ntohs(port));
        if (strlen(numserv) > servlen)
            return 3;
        strcpy(serv, numserv);
    } else {
        sp = getservbyport(port, (flags & NI_DGRAM) ? "udp" : "tcp");
        if (sp) {
            if (strlen(sp->s_name) > servlen)
                return 3;
            strcpy(serv, sp->s_name);
        } else
            return 1;
    }

    switch (sa->sa_family) {
    case AF_INET:
        v4a = ((struct sockaddr_in *)sa)->sin_addr.s_addr;
        if (IN_MULTICAST(v4a) || IN_EXPERIMENTAL(v4a))
            flags |= NI_NUMERICHOST;
        v4a >>= IN_CLASSA_NSHIFT;
        if (v4a == 0 || v4a == IN_LOOPBACKNET)
            flags |= NI_NUMERICHOST;
        break;







    }
    if (host == NULL || hostlen == 0) {

    } else if (flags & NI_NUMERICHOST) {
        if (inet_ntop(gni_afd->a_af, addr, numaddr, sizeof(numaddr))
            == NULL)
            return 4;
        if (strlen(numaddr) > hostlen)
            return 3;
        strcpy(host, numaddr);
    } else {



        hp = gethostbyaddr(addr, gni_afd->a_addrlen, gni_afd->a_af);
        h_error = h_errno;


        if (hp) {
            if (flags & NI_NOFQDN) {
                p = strchr(hp->h_name, '.');
                if (p) *p = '\0';
            }
            if (strlen(hp->h_name) > hostlen) {



                return 3;
            }
            strcpy(host, hp->h_name);



        } else {
            if (flags & NI_NAMEREQD)
                return 2;
            if (inet_ntop(gni_afd->a_af, addr, numaddr, sizeof(numaddr))
                == NULL)
                return 2;
            if (strlen(numaddr) > hostlen)
                return 3;
            strcpy(host, numaddr);
        }
    }
    return 0;
}
