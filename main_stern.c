#include <malloc.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <unistd.h>
#include <time.h>
#include <assert.h>
#include <inttypes.h>
#include <limits.h>
#include <errno.h>

#define _GNU_SOURCE
#include <getopt.h>

#include "KeccakDuplex.h"
#include "KeccakSponge.h"
#include "KeccakF-1600-interface.h"
#include "pi.h"

#define BPW (8 * sizeof (unsigned long))
#define BILLION  1000000000L

enum { RANDOM, QUASI_CYCLIC, QUASI_DYADIC } matrix_type;

#if __WORDSIZE==64
#define LOG2 6 
#else
#error "Source written for 64-bit machine"
#endif

/*
    buf
     | 
     V
     +----------------------+----------+--------------+------------+
     |     permutation      |  yH^T    |       e      |   s = eH^T |
     +----------------------+----------+--------------+------------+
*/ typedef struct {     /* data structure of commitment                     */
    unsigned char *buf; /* buf contains all data. Their layout is:          */
    unsigned long *__restrict__ y;   /* the random vector y: n bits         */
    int *p;             /* p is the random permutation: n integers          */
    unsigned long *__restrict__ yH;  /* the value yH^T                      */
    unsigned long *__restrict__ e; /* the private error vector of weight w  */
    unsigned long *__restrict__ s; /* the public syndrome: eH^T = s         */
} *com_t;

typedef struct matrix {
    int type;                                 /*  matrix_type               */
    int rown;                                 /*  number of rows            */
    int coln;                                 /*  number of columns         */
    int rwdcnt;                               /*  number of words in a row  */
    int alloc_size;                           /*  number of allocated bytes */
    unsigned long *el;                        /*  memory of the matrix      */
    unsigned long *aux;                       /*  aux. memory for mult.     */
    unsigned long *sig_aux;                   /*  aux. memory for mult.     */
} *binmat_t;

binmat_t binmat_ini (int rown, int coln, int type) {
    
    binmat_t A = malloc (sizeof (*A));
   
    A->type       = type; 
    A->coln       = coln;
    A->rown       = rown;  
    A->rwdcnt     = (1 + (coln - 1) / BPW);
    A->alloc_size = rown * A->rwdcnt * sizeof (*A->el);
    A->el         = malloc(A->alloc_size);             /* data of the matrix */
    A->aux        = malloc(coln/8);
    A->sig_aux    = malloc(coln/8);
  
    return A;
}

void binmat_free(binmat_t H) {                  /* free the matrix resources */
    free(H->el);
    free(H->aux);
    free(H->sig_aux);
    free(H);
}

#define ADD_LINE_RND(sh) {\
        register unsigned long mask = 0UL - ((ec >> (sh)) & 1);\
        res = s;\
        for (k = 0; k < rwdcnt; ++k) {\
            *res = *res ^ (*word & mask);\
            ++res; ++word;\
        }}

static unsigned long *vm_aux_rnd(unsigned long const *e
                               , unsigned long const *H
                               , int rows, int rwdcnt 
                               , unsigned long *s) {
    int i,j,k;
    unsigned long const *__restrict__ word = H;
    unsigned long *__restrict__ res = s;

    for(i=0;i<rows>>LOG2;++i) {
        register unsigned long const ec = *e++;
        for(j=sizeof(*e);j>0;--j) {
            register const int bit = j<<3;
            register int b = bit-1; 
            ADD_LINE_RND(b); b = bit-2;
            ADD_LINE_RND(b); b = bit-3;
            ADD_LINE_RND(b); b = bit-4;
            ADD_LINE_RND(b); b = bit-5;
            ADD_LINE_RND(b); b = bit-6;
            ADD_LINE_RND(b); b = bit-7;
            ADD_LINE_RND(b); b = bit-8;
            ADD_LINE_RND(b);
        }
    }
    return s;
}

static unsigned long *vm_aux_cyc(unsigned long const *e
                               , unsigned long const *__restrict__ H
                               , int rows, int rwdcnt 
                               , unsigned long *s) {
    int i,j,k;

    for(i=0;i<rows;i+=64) {                 /* rows must be a multiple of 64 */
        unsigned long *__restrict__ res = s;
        register unsigned long const mc = *e++;
        register unsigned long const *__restrict__ g = &H[i*rwdcnt];

        for(k=0;k<rwdcnt;++k) {
            register unsigned long const el = *g++;

            for(j=63;j>=0;) {
                register unsigned long mask = 0UL - ((mc >> j) & 1UL);
                *res ^= (((el >> j) ^ (el << (64-j))) & mask);
                --j; /* 0 */
                mask = 0UL - ((mc >> j) & 1UL);
                *res ^= (((el >> j) ^ (el << (64-j))) & mask);
                --j; /* 1 */
                mask = 0UL - ((mc >> j) & 1UL);
                *res ^= (((el >> j) ^ (el << (64-j))) & mask);
                --j; /* 2 */
                mask = 0UL - ((mc >> j) & 1UL);
                *res ^= (((el >> j) ^ (el << (64-j))) & mask);
                --j; /* 3 */
                mask = 0UL - ((mc >> j) & 1UL);
                *res ^= (((el >> j) ^ (el << (64-j))) & mask);
                --j; /* 4 */
                mask = 0UL - ((mc >> j) & 1UL);
                *res ^= (((el >> j) ^ (el << (64-j))) & mask);
                --j; /* 5 */
                mask = 0UL - ((mc >> j) & 1UL);
                *res ^= (((el >> j) ^ (el << (64-j))) & mask);
                --j; /* 6 */
                mask = 0UL - ((mc >> j) & 1UL);
                *res ^= (((el >> j) ^ (el << (64-j))) & mask);
                --j; /* 7 */
            }
            ++res;
        }
    }

    return s;
}

uint64_t vm64(uint64_t v, uint64_t m) {/* multiply a 64-bit vector from the  */
    register int i;                    /* left onto a binary dyadic matrix H */
    register uint64_t res = 0UL;
                        /* the strategy is to (re-)calculate each row of the */
    for(i=0;i<64;++i) { /* matrix on the fly                                 */
        int n = i;
        register uint64_t row = m;

        if(n >= 32) {
            row = (((row & 0x00000000FFFFFFFFUL) << 32)      /* swap 4-bytes */
                 | ((row & 0xFFFFFFFF00000000UL) >> 32));
            n = n - 32;
        }
        if(n >= 16) {
            row = (((row & 0x0000FFFF0000FFFFUL) << 16)      /* swap 2-bytes */
                 | ((row & 0xFFFF0000FFFF0000UL) >> 16));
            n = n - 16;
        }
        if(n >= 8) {
            row = (((row & 0x00FF00FF00FF00FFUL) <<  8)        /* swap bytes */
                 | ((row & 0xFF00FF00FF00FF00UL) >>  8));
            n = n - 8;
        }
        if(n >= 4) {
            row = (((row & 0x0F0F0F0F0F0F0F0FUL) <<  4)      /* swap nybbles */
                 | ((row & 0xF0F0F0F0F0F0F0F0UL) >>  4));
            n = n - 4;
        }
        if(n >= 2) {
            row = (((row & 0x3333333333333333UL) <<  2)         /* swap nyps */
                 | ((row & 0xCCCCCCCCCCCCCCCCUL) >>  2));
            n = n - 2;
        }
        if(n == 1) {
            row = (((row & 0x5555555555555555UL) <<  1)         /* swap bits */ 
                 | ((row & 0xAAAAAAAAAAAAAAAAUL) >>  1));
        }

        if((v >> (63-i)) & 1UL) { /**/
            res = res ^ row;
        }
    }
    return res;
}

static unsigned long *vm_aux_dya(unsigned long const *e
                               , unsigned long const *__restrict__ H
                               , int rows, int rwdcnt 
                               , unsigned long *s) {
    int i,j;
    unsigned long *__restrict__ res = s;

    for(i=0;i<rows;i+=64) {                 /* rows must be a multiple of 64 */
        register unsigned long const ec = *e++;
        register unsigned long const *__restrict__ h = &H[i*rwdcnt];

        for(j=0;j<rwdcnt;++j) {
            register unsigned long const m = *h++;
            res[j] ^= vm64(ec, m);
        }
    }

    return s;
}

/* matrix vector product: s = eH^T. NOTE: H is an (n \times r) matrix!    */
unsigned long *binmv_product(binmat_t const H 
                           , unsigned long const *e
                           , unsigned long *s) { 

    register int const i = H->coln>>LOG2; /* init at the beginning */
    register int const j = H->coln*H->rwdcnt;
     
    memcpy(s, e, H->coln>>3);

    switch (H->type) {
        case RANDOM: /* improve interface !*/
            s = vm_aux_rnd(&e[i], &H->el[j], H->coln, H->rwdcnt, s);
            break;
        case QUASI_CYCLIC:
            s = vm_aux_cyc(&e[i], &H->el[j], H->coln, H->rwdcnt, s);
            break;
        case QUASI_DYADIC:
            s = vm_aux_dya(&e[i], &H->el[j], H->coln, H->rwdcnt, s);
            break;
        default:;
    }
    return s;
}

void init_binmat_from_pi(binmat_t H) { /* init the binary matrix H. note     */
    int i,j,k;                         /* the matrix is save transposedly.   */
    int const c = H->coln;             /* Multiplication has to be done by   */
    int const r = H->rown;             /* the left then: He -> eH^T          */

    memset(H->el, 0x00, (H->coln*H->coln)/8);

    for(i=0;i<c;++i)           /* write the identity matrix into the first   */
        for(j=0;j<c;++j)       /* half of H                                  */
            if(i==j) {
                k = i*c+j;
                H->el[(k>>LOG2)] |= (1UL << ((BPW-1) - (k & (BPW-1))));
            }

    switch (H->type) {
        case RANDOM:   /* just copy some random data to the second half of H */
            memcpy(&H->el[c*H->rwdcnt], Pi, ((r-c)*c)/8);
            break;
        case QUASI_CYCLIC:
        case QUASI_DYADIC:  /* copy some random data to the 'signature' rows */
            for(i=c;i<r;i+=BPW) {       /* of H                              */
                memcpy(&H->el[i*H->rwdcnt], &Pi[i/BPW], c/8);
            }
            break;
        default:;
    }
}

inline static unsigned long rdtsc() {     /* read the cycle count of the CPU */
    union {
        unsigned int x[2];
        unsigned long y;
    } u;
    __asm__ volatile("rdtsc" : "=a"(u.x[0]), "=d"(u.x[1]));
    return u.y;
}

inline static unsigned long cb(unsigned long x) {    /* count the number of  */
                                                     /* bits contained in x  */
    x = (x & 0x5555555555555555) + ((x >> 1) & 0x5555555555555555);
    x = (x & 0x3333333333333333) + ((x >> 2) & 0x3333333333333333);
    x = (x & 0x0F0F0F0F0F0F0F0F) + ((x >> 4) & 0x0F0F0F0F0F0F0F0F);
    x = (x & 0x00FF00FF00FF00FF) + ((x >> 8) & 0x00FF00FF00FF00FF);
    x = (x & 0x0000FFFF0000FFFF) + ((x >>16) & 0x0000FFFF0000FFFF);
    x = (x & 0x00000000FFFFFFFF) + ((x >>32) & 0x00000000FFFFFFFF);

    return x;
}

void next_perm(int *__restrict__ src, int *__restrict__ perm
             , int n, int const *__restrict__ r) {
    int i;

    perm[0] = src[0];
    for(i=1;i<n;++i) {
        register int j = r[i-1];
        perm[i] = perm[j];
        perm[j] = src[i];
    }
    for(i=0;i<n;++i)/* Update source vector for next round */
        *src++ = *perm++;
}

void generate_perm(int *src, int *r
                 , int *__restrict__ perm, int n/*, unsigned long const* yrnd*/) {
    int i; /* note: use Keccak here as well ? */

    for(i=0;i<n;++i)
        src[i] = i;
    srand((unsigned) rdtsc());
    r[0] = 0;
    for(i=1;i<n;++i)
        r[i] = rand() % (i+1);

    next_perm(src, perm, n, r); 
}

void permute_v(unsigned long *__restrict__ u /* permute the bits contained   */
             , unsigned long *__restrict__ v /* contained in v and save the  */
             , int const *__restrict__ perm, int n) { /* result in u         */

    register int i, j, iLOG2, pi;
    unsigned long *__restrict__ uiLOG2;
    int const     *__restrict__ p = perm;

    assert((n % 8) == 0);

    for(i=0;i<n;) {        /* Note: we know that (n % 8) == 0. Therefore     */
        iLOG2  = i>>LOG2;  /* i>>LOG2 does not change in 8 steps aligned on  */
        uiLOG2 = &u[iLOG2];/* an 8-boundary                                  */
        pi = *p++;
        /* 0 */
        j = ((BPW-1) - (i & (BPW-1)));
        *uiLOG2 |= ((v[pi>>LOG2] >> ((BPW-1) - (pi & (BPW-1)))) & 1) << j;
        ++i; pi = *p++;
        /* 1 */
        j = ((BPW-1) - (i & (BPW-1)));
        *uiLOG2 |= ((v[pi>>LOG2] >> ((BPW-1) - (pi & (BPW-1)))) & 1) << j;
        ++i; pi = *p++;
        /* 2 */
        j = ((BPW-1) - (i & (BPW-1)));
        *uiLOG2 |= ((v[pi>>LOG2] >> ((BPW-1) - (pi & (BPW-1)))) & 1) << j;
        ++i; pi = *p++;
        /* 3 */
        j = ((BPW-1) - (i & (BPW-1)));
        *uiLOG2 |= ((v[pi>>LOG2] >> ((BPW-1) - (pi & (BPW-1)))) & 1) << j;
        ++i; pi = *p++;
        /* 4 */
        j = ((BPW-1) - (i & (BPW-1)));
        *uiLOG2 |= ((v[pi>>LOG2] >> ((BPW-1) - (pi & (BPW-1)))) & 1) << j;
        ++i; pi = *p++;
        /* 5 */
        j = ((BPW-1) - (i & (BPW-1)));
        *uiLOG2 |= ((v[pi>>LOG2] >> ((BPW-1) - (pi & (BPW-1)))) & 1) << j;
        ++i; pi = *p++;
        /* 6 */
        j = ((BPW-1) - (i & (BPW-1)));
        *uiLOG2 |= ((v[pi>>LOG2] >> ((BPW-1) - (pi & (BPW-1)))) & 1) << j;
        ++i; pi = *p++;
        /* 7 */
        j = ((BPW-1) - (i & (BPW-1)));
        *uiLOG2 |= ((v[pi>>LOG2] >> ((BPW-1) - (pi & (BPW-1)))) & 1) << j;
        ++i;
    }
}

/* HASH: call Keccak: 'dest' will contain the digest, 'src' is the data to   */
/* hash, 'hlen' is the size of 'dest' in bits, and 'srcl' is the size of src */
/* in bits.                                                                  */
#define HASH(dest,src,hlen,srcl) \
    InitSponge(&state, rate, capacity);\
    Absorb(&state, (unsigned char *)src, srcl);\
    Squeeze(&state, (unsigned char *)dest, hlen);

#define WEIGHT (76) 
#define ROUNDS (1) 

/* 2^80 security level                                         */
/* Stern + Veron (n = 768, k = r= 384, wt(s) = 76)             */
/* CVE ( q= 256; n = 144 ; k=r = 72 ; w := 55)                 */
/* NOTE: n should be a multiple of 64 for Stern and Veron, for */
/* for CVE a multiple of 8.                                    */

int main(int argc, char *argv[]) {

    extern char *optarg;
    extern int optind, optopt;

	struct timespec start, stop;
	double accum;
    int i,k,C2,round;
    unsigned long b;
    //int n = 1024;                     /* bit length of a row of H           */
    //int n = 896;
    int n = 768;
    //int n = 640;
    int r = n/2;                      /* bit length of a column of H        */
    //unsigned w            = WEIGHT;   /* weight of the priv. error vector e */
    unsigned w            = 76;   /* weight of the priv. error vector e */
    int rounds            = ROUNDS;   /* rounds to perform the stern scheme */
    int const j           = n/BPW;    /* number of words per column         */
    unsigned int hbl      = 160;      /* hashbitlen                         */
    int const hbl8        = hbl/8;    /* hasbitlen in bytes                 */
    unsigned int rate     = 1024;     /* bitrate of Keccak                  */
    unsigned int capacity = 576;      /* capacity of Keccak                 */
    spongeState state;                /* state of Keccak                    */
    binmat_t H;                       /* the parity check matrix            */
    com_t c;                          /* commitment                         */

    int C1 = RANDOM;
    //int C1 = QUASI_CYCLIC;
    //int C1 = QUASI_DYADIC;
    while ((i = getopt(argc, argv, ":hrcdm:s:w:")) != -1) {
        errno = 0;
        switch(i) {
            case 's':
                rounds = (int)strtoul(optarg, NULL, 10); 
                break;
            case 'r':
                C1 = RANDOM;
                break;
            case 'c':
                C1 = QUASI_CYCLIC;
                break;
            case 'd':
                C1 = QUASI_DYADIC;
                break;
            case ':':
                fprintf(stderr,"Option -%c requires an operand\n",optopt); 
                exit(0); 
            case '?':
                fprintf(stderr, "Unrecognized option: -%c\n", optopt);
                exit(0); 
            case 'h':
                printf("Available options:\n");
                printf("-h\tprint this help\n");
                printf("-c\tquasi cyclic matrix\n");
                printf("-d\tquasi dyadic matrix\n");
                printf("-r\trandom matrix\n");
                printf("-s\trounds\n");
                exit(0); 
            default:;
        }
    }

    int           *src         = malloc(n*sizeof(*src)); /* used for perm.  */
    int           *rnd         = malloc(n*sizeof(*rnd)); /* used for perm.  */
    unsigned long *yrnd        = malloc(n/8*rounds);     /* rdm vectors     */
    unsigned long *y           = malloc(n/8);   /* one rdm vector per round */
    unsigned long *y_chck      = malloc(n/8);   /* aux.var.: contains y + e */
    unsigned long *u           = malloc(n/8);   /* auxiliary variable       */
    unsigned char *c1_prover   = malloc(hbl/8); /* commitment c1 (prover)   */
    unsigned char *c2_prover   = malloc(hbl/8); /* commitment c2 (prover)   */
    unsigned char *c3_prover   = malloc(hbl/8); /* commitment c3 (prover)   */
    unsigned char *c1_verifier = malloc(hbl/8); /* commitment c1 (verifier) */
    unsigned char *c2_verifier = malloc(hbl/8); /* commitment c2 (verifier) */
    unsigned char *c3_verifier = malloc(hbl/8); /* commitment c3 (verifier) */

    c      = malloc(sizeof(*c));
    c->buf = malloc(n*sizeof(*c->p) + r/8 + n/8 + r/8);

    //c->y   = (unsigned long *)&(c->buf)[0];
    c->p   = (int *)&(c->buf)[0];
    c->yH  = (unsigned long *)&(c->buf)[n*sizeof(*c->p)];
    c->e   = (unsigned long *)&(c->buf)[n*sizeof(*c->p) + r/8];
    c->s   = (unsigned long *)&(c->buf)[n*sizeof(*c->p) + r/8 + n/8];

    H = binmat_ini(n, r, C1);             /* init H                          */
    init_binmat_from_pi(H);

    generate_perm(src, rnd, c->p, n);     /* comp. rnd. perm.                */
    memset(y, 0x00, n/8);                 /* init the private error vector e */
    y[0] = (1UL<<32)-1;
//#if WEIGHT==128
#if WEIGHT==76
    y[1] = (1UL<<32)-1;
    y[2] = (1UL<<12)-1;
    //y[2] = (1UL<<32)-1;
    //y[3] = (1UL<<32)-1;
#endif
    permute_v(c->e, y, c->p, n);

    memset(c->s, 0x00, r/8);              /* init s = eH^T                   */
    c->s = binmv_product(H, c->e, c->s);

    if(clock_gettime( CLOCK_REALTIME, &start) == -1 )
        perror( "clock gettime" );

    unsigned long long rd = rdtsc(); /* get (n*rounds-bit) random bits. n    */ 
    HASH(yrnd, &rd, n*rounds, sizeof(rd)*8); /* bits will be used per round. */

    for(k=0,round=0;round<rounds;++round,k+=j) {             /* stern scheme */

        c->y = &yrnd[k];                    /* save n/8 bytes in c->y        */
        memset(c->yH, 0x00, (H->coln)>>3);  /* compute yH^T                  */
        c->yH = binmv_product(H, c->y, c->yH);
        next_perm(src, c->p, n, rnd);       /* fetch next random permutation */
        HASH(c1_prover, c->p, hbl, n*(sizeof(*c->p)*8) + r);/* c1 = h(p||yH) */

        memset(y, 0x00, n>>3);
        permute_v(y, c->y, c->p, n);
        HASH(c2_prover, y, hbl, n);                         /* c2 = h(yP)    */

        memset(u, 0x00, n>>3);
        for(i=0;i<j;++i)
            y_chck[i] = c->y[i] ^ c->e[i];
        permute_v(u, y_chck, c->p, n);
        HASH(c3_prover, u, hbl, n);                         /* c3 = (y+e)P   */

        b = (*c->y) % 3;     /* bad idea ? but for tests it seems to be  ok. */
        //b = ((b & 1UL) + ((b >> 1) & 1UL)); // + ((b >> 2) & 1UL));
        switch (b) {
        case 0:    /* reveal y and the permutation sigma --> check c1 and c2 */
            memset(c->yH, 0x00, r>>3);       /* compute yH^T and hash to get */
            c->yH = binmv_product(H, c->y, c->yH); /* c1_verifier = h(p||yH) */
            HASH(c1_verifier, c->p, hbl, n*(sizeof(*c->p)*8) + r);
           
            memset(y, 0x00, n>>3);            /* permute c->y and store      */
            permute_v(y, c->y, c->p, n);      /* the result in y             */
            HASH(c2_verifier, y, hbl, n);     /* compute c2_verifier = h(yP) */
            
            C1 = C2 = 0;
            for(i=0;i<hbl8;++i) {  /* check c1_prover == c1_verifier and     */
                                   /*       c2_prover == c2_verifier         */
                C1 += c1_prover[i] ^ c1_verifier[i];
                C2 += c2_prover[i] ^ c2_verifier[i];
            }
            if(C1 || C2)
                fprintf(stderr,"b=%lu:C1=%d,C2=%d\n",b,C1,C2);
            
            break;
        case 1:                      /* reveal y+e and the permutation sigma */
            memset(c->yH, 0x00, r>>3);          /* y_chck still contains y+e */ 
            c->yH = binmv_product(H, y_chck, c->yH);/* compute s0 = (y+e)H^T */
            for(i=0;i<(int)(r>>LOG2);++i)       /* compute s1 = s0 + s       */ 
                c->yH[i] ^= c->s[i];/* s1 = yH^T --> c1_verifier = h(p||s1)  */
            HASH(c1_verifier, c->p, hbl, n*(sizeof(*c->p)*8) + r);
        
            memset(u, 0x00, n>>3);
            permute_v(u, y_chck, c->p, n);
            HASH(c3_verifier, u, hbl, n);

            C1 = C2 = 0;
            for(i=0;i<hbl8;++i) {  /* check c1_prover == c1_verifier and     */
                                   /*       c3_prover == c3_verifier         */
                C1 += c1_prover[i] ^ c1_verifier[i];
                C2 += c3_prover[i] ^ c3_verifier[i];
            }
            if(C1 || C2)
                fprintf(stderr,"b=%lu:C1=%d,C2=%d\n",b,C1,C2);

            break;
        case 2:                                       /* reveal yP and eP    */
            HASH(c2_verifier, y, hbl, n);             /* y still contains yP */

            memset(u, 0x00, n>>3);
            permute_v(u, c->e, c->p, n);       /* permute e and save eP in u */

            b = 0;
            for(i=0;i<j;++i)
                b += cb(u[i]);                     /* check the weight of eP */           
            if(b != w)
                fprintf(stderr,"b(%lu) != w(%d)\n",b,w);
                
            for(i=0;i<j;++i)                              /* compute eP + yP */
                u[i] = u[i] ^ y[i];
            HASH(c3_verifier, u, hbl, n);

            C1 = C2 = 0;
            for(i=0;i<hbl8;++i) {  /* check c2_prover == c2_verifier and     */
                                   /*       c3_prover == c3_verifier         */
                C1 += c2_prover[i] ^ c2_verifier[i];
                C2 += c3_prover[i] ^ c3_verifier[i];
            }
            if(C1 || C2)
                fprintf(stderr,"b=%lu:C1=%d,C2=%d\n",b,C1,C2);

            break;
        default:;
        }
    }

    if( clock_gettime(CLOCK_REALTIME, &stop)== -1 ) {
        perror( "clock gettime" );
    } else {
        accum = (stop.tv_sec - start.tv_sec) +
		(double)(stop.tv_nsec - start.tv_nsec)/(double)BILLION;
        switch(H->type) {
        case RANDOM:
		    printf("(RANDOM      :rnds=%d,w=%d: %lf secs --> %lf sec/rnd)\n"
                 , rounds, w, accum, accum/round);
            break;
        case QUASI_CYCLIC:
		    printf("(QUASI_CYCLIC:rnds=%d,w=%d: %lf secs --> %lf sec/rnd)\n"
                 , rounds, w, accum, accum/round);
            break;
        case QUASI_DYADIC:
		    printf("(QUASI_DYADIC:rnds=%d,w=%d: %lf secs --> %lf sec/rnd)\n"
                 , rounds, w, accum, accum/round);
            break;
        default:;
        }
    }

    free(c->buf);
    free(c);
    free(src);
    free(rnd);
    free(yrnd);
    free(y);
    free(u);
    free(c1_prover);
    free(c2_prover);
    free(c3_prover);
    free(c1_verifier);
    free(c2_verifier);
    free(c3_verifier);
    free(y_chck);
    binmat_free(H);

    return 0;
}

