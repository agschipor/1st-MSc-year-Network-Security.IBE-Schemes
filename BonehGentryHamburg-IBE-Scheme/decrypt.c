#include <stdio.h>
#include <gmp.h>
#include <time.h>
#include <string.h>
#include <malloc.h>
#include <openssl/sha.h>
#include <errno.h>
#include <limits.h>

#define ERR_FILE_OPEN "file open failed"
#define ERR_FILE_READ "file read failed"
#define ERR_MALLOC "malloc"
#define ERR_BAD_PARAMETERS "bad parameters: r^2 isn't congruent with a/-a modulo n"
#define ERR_SQURE_ROOT_MODULO " calculate square root modulo"
#define ERR_IDENTITY_LENGTH_GREATHER_THAN_BUFSIZ "identity length greather than BUFSIZ"
#define SUCCESS "success"


void PrintError(char* error)
{
    fprintf(stderr, "<<ERROR>>\t%s:\t%s", error, strerror(errno));
}


void GetHash(unsigned char* identity, unsigned char** hash, unsigned char index, char** error)
{
    int i;
    size_t length;
    unsigned char buffer[BUFSIZ];
    SHA256_CTX ctx;
    
    SHA256_Init(&ctx);
 
    length = strlen(identity);

    if (length > BUFSIZ) 
    {
        *error = ERR_IDENTITY_LENGTH_GREATHER_THAN_BUFSIZ;
        return;
    }

    for (i = 0; i < length; i++)
        buffer[i] = identity[i];

    buffer[i++] = 48 + index;
    buffer[i] = '\0';

    SHA256_Update(&ctx, buffer, length + 1);
    SHA256_Final(buffer, &ctx);

    *hash = (unsigned char*)malloc(SHA256_DIGEST_LENGTH * sizeof(unsigned char) + 1);

    if (*hash == NULL)
    {
        *error = ERR_MALLOC;
        return;
    }

    for (i = 0; i < SHA256_DIGEST_LENGTH; i++)
        (*hash)[i] = buffer[i];

    hash[SHA256_DIGEST_LENGTH] = '\0';

    *error = SUCCESS;
}


void GetHexHash(unsigned char* hash, unsigned char** hex_hash, char** error)
{
    int i, j;

    *hex_hash = (unsigned char*)malloc(65*sizeof(unsigned char));

    if (hex_hash == NULL)
    {
        *error = ERR_MALLOC;
        return;
    }

    for (i = 0, j = 0; i < 32; i++, j+=2)
        sprintf((*hex_hash+j), "%02X", hash[i]);

    *error = SUCCESS;
}


void GetJnHash(mpz_t n, mpz_t jn_hash)
{
    while (mpz_jacobi(jn_hash, n) != 1)
    {
        mpz_add_ui(jn_hash, jn_hash, 1);
        mpz_mod(jn_hash, jn_hash, n);
    }
}


void f(mpz_t res, mpz_t s, mpz_t x, mpz_t n)
{
    mpz_mul(res, x, s);
    mpz_mod(res, res, n);
    mpz_add_ui(res, res, 1);
    mpz_mod(res, res, n);
}


//########################## nu este folosit aici #######################################
void g(mpz_t res, mpz_t s, mpz_t y, mpz_t n)
{
    mpz_mul(res, y, s);
    mpz_mod(res, res, n);
    mpz_add_ui(res, res, 1);
    mpz_mod(res, res, n);
    mpz_mul_ui(res, res, 2);
    mpz_mod(res, res, n);
}
//#######################################################################################


void Q(mpz_t a, mpz_t S, mpz_t s, mpz_t n, mpz_t x, mpz_t y, gmp_randstate_t r_state)
{  
    mpz_t t, tmp, inv_tmp, rgcd;

    mpz_init(t);
    mpz_init(tmp);
    mpz_init(inv_tmp);
    mpz_init(rgcd);

    mpz_set_si(t, 0);
    do 
    {
        do 
        {
            mpz_add_ui(t, t, 1);
            mpz_gcd(rgcd, t, n);
        }
        while (mpz_cmp_si(rgcd, 1) != 0);

        mpz_mod(t, t, n);

        mpz_mul(tmp, t, t);
        mpz_mul(tmp, tmp, S);
        mpz_add(tmp, tmp, a);
        mpz_gcd(rgcd, tmp, n);
    }
    while(mpz_cmp_si(rgcd, 1) != 0);

    mpz_mod(tmp, tmp, n);

    mpz_invert(inv_tmp, tmp, n);

    mpz_mul(x, inv_tmp, t);
    mpz_mod(x, x, n);
    mpz_mul(x, x, s);
    mpz_mod(x, x, n);
    mpz_mul_si(x, x, -2);
    mpz_mod(x, x, n);

    mpz_mul(inv_tmp, tmp, s);
    mpz_mod(inv_tmp, inv_tmp, n);

    mpz_invert(inv_tmp, inv_tmp, n);
    //y = t^2
    mpz_mul(y, t, t);
    mpz_mod(y, y, n);
    //y *= S
    mpz_mul(y, y, S);
    mpz_mod(y, y, n);
    //y = R- y
    mpz_sub(y, a, y);
    mpz_mod(y, y, n);
    //y = y * inv_tmp
    mpz_mul(y, y, inv_tmp);
    mpz_mod(y, y, n);
    /////////////////////////////////
    mpz_t cx;
    mpz_init(cx);

    mpz_mul(cx, t, t);
    mpz_mod(cx, cx, n);

    mpz_mul(cx, cx, S);
    mpz_mod(cx, cx, n);

    mpz_sub(cx, a, cx);
    mpz_mod(cx, cx, n);

    mpz_invert(inv_tmp, tmp, n);
    
    mpz_mul(cx, cx, inv_tmp);
    mpz_mod(cx, cx, n);

    mpz_mul_ui(cx, cx, 2);
    mpz_mod(cx, cx, n);
    mpz_add_ui(cx, cx, 2);
    mpz_mod(cx, cx, n);
    gmp_printf("\nt=%Zd\n", cx);

    mpz_clear(cx);
    ////////////////////////////////

    mpz_clear(rgcd);
    mpz_clear(inv_tmp);
    mpz_clear(tmp);
    mpz_clear(t);

}


//####################################################################################################
int TonelliShanks(mpz_t res, mpz_t a, mpz_t p)
{
    mpz_t Q, c, t, b, tmp;
    int i;
    unsigned long int S, M;

    mpz_init(Q);
    mpz_init(c);
    mpz_init(t);
    mpz_init(b);
    mpz_init(tmp);

    // p trebuie sa fie numar prim impar
    if (mpz_tstbit(p, 0) != 1)
        return 1; 
    // daca simbolul legendre nu e 1, atunci a nu e reziduu patratic, iar ecuatia nu are solutii
    if (mpz_legendre(a, p) != 1)
        return 1; 

    if (mpz_divisible_p(a, p) == 1)
    {
        mpz_set_ui(res, 0);
        return 0;
    }   

    // daca p e congruent cu 3 modulo 4, putem calcula radacina mai usor
    if (mpz_tstbit(p, 1) == 1)
    {
        mpz_set(res, p);
        mpz_add_ui(res, res, 1);
        mpz_tdiv_q_2exp(res, res, 2);
        mpz_powm(res, a, res, p); // a^res mod p | res = (p+1)/4
        return 0;
    }

    // caut S, o putere de-a lui 2 si un Q astfel incat p-1=Q*2^S
    mpz_set(Q, p);
    mpz_sub_ui(Q, Q, 1);

    // aflu S
    S = mpz_scan1(Q, 0);

    if (S == ULONG_MAX)
        return 1;

    // aflu Q
    mpz_tdiv_q_2exp(Q, Q, S);

    // caut un element non reziduu modulo p
    mpz_set_ui(c, 2);

    while(mpz_legendre(c, p) != -1)
        mpz_add_ui(c, c, 1);

    // setez c = non reziduu ^ Q
    mpz_powm(c, c, Q, p);

    mpz_powm(t, a, Q, p);

    mpz_add_ui(Q, Q, 1);
    mpz_mod(Q, Q, p);
    mpz_tdiv_q_2exp(Q, Q, 1);

    mpz_powm(res, a, Q, p);

    M = S;

    while (mpz_cmp_ui(t, 1) != 0)
    {   
        for (i = 1; i < M; i++)
        {
            mpz_powm_ui(tmp, t, 1 << i, p);
            if (mpz_cmp_ui(tmp, 1) == 0)
                break;
        }

        mpz_powm_ui(b, c, 1 << (M - i - 1), p);
        
        mpz_mul(res, res, b);
        mpz_mod(res, res, p);
        
        mpz_mul(c, b, b);
        mpz_mod(c, c, p);

        mpz_mul(t, t, c);
        mpz_mod(t, t, p);

        M = i;
    }

    mpz_clear(b);
    mpz_clear(t);
    mpz_clear(c);
    mpz_clear(Q);
    mpz_clear(tmp);

    return 0;
}


void CRTTwo(mpz_t res, mpz_t s1, mpz_t p, mpz_t s2, mpz_t q, mpz_t n)
{
    mpz_t p_inv, q_inv, tmp;
    
    mpz_init(p_inv);
    mpz_init(q_inv);
    mpz_init(tmp);

    mpz_invert(p_inv, p, q);
    mpz_invert(q_inv, q, p);

    mpz_set(res, s1);
    mpz_mul(res, res, q);
    mpz_mul(res, res, q_inv);

    mpz_set(tmp, s2);
    mpz_mul(tmp, tmp, p);
    mpz_mul(tmp, tmp, p_inv);

    mpz_add(res, res, tmp);
    mpz_mod(res, res, n);

    mpz_clear(tmp);
    mpz_clear(p_inv);
    mpz_clear(q_inv);
}
//####################################################################################################



void Decrypt(char* filename, unsigned char* identity, int l, mpz_t p, mpz_t q, mpz_t n, mpz_t u, mpz_t *r, char** error)
{
    int j, i, read_length, bit, m, mrev;
    mpz_t rp, S, *R, *uR, cR, x, y, s, tmp1, tmp2;
    gmp_randstate_t r_state;
    FILE *fd, *fd_write;
    unsigned char *hash, *hex_hash, c1, c2, decrypted_character;

    mpz_init(rp);
    mpz_init(S);
    mpz_init(cR);
    mpz_init(x);
    mpz_init(y);
    mpz_init(s);
    mpz_init(tmp1);
    mpz_init(tmp2);

    fd = fopen(filename, "r");

    if (fd == NULL)
    {
        *error = ERR_FILE_OPEN;
        return;
    }

    fd_write = fopen("decrypted_text", "w");

    if (fd_write == NULL)
    {
        *error = ERR_FILE_OPEN;
        return;
    }

    R = (mpz_t*)malloc(l * sizeof(mpz_t));

    if (R == NULL)
    {
        *error = ERR_MALLOC;
        return;
    }

    uR = (mpz_t*)malloc(l * sizeof(mpz_t));

    if (uR == NULL)
    {
        *error = ERR_MALLOC;
        return;
    }

    for (i = 0; i < l; i++)
    {
        mpz_init(R[i]);
        mpz_init(uR[i]);

        GetHash(identity, &hash, i, error);

        if (strcmp(*error, SUCCESS) != 0)
            return;

        GetHexHash(hash, &hex_hash, error);    

        if (strcmp(*error, SUCCESS) != 0)
            return;

        mpz_set_str(R[i], hex_hash, 16);
        mpz_mod(R[i], R[i], n);

        GetJnHash(n, R[i]);

        mpz_mul(uR[i], R[i], u);
        mpz_mod(uR[i], uR[i], n);
    }

    gmp_randinit_mt(r_state);
    gmp_randseed_ui(r_state, time(NULL));
        
    i = 0;    
    while (1)
    {  
        if (i % l == 0)
        {
            i = 0;
            read_length = mpz_inp_str(S, fd, 10);
            if (read_length == 0)
                break;  

            if (TonelliShanks(tmp1, S, p) == 1)
            {
                *error = ERR_SQURE_ROOT_MODULO;
                return;
            }

            if (TonelliShanks(tmp2, S, q) == 1)
            {
                *error = ERR_SQURE_ROOT_MODULO;
                return;
            }

            CRTTwo(s, tmp1, p, tmp2, q, n);

            gmp_printf("%Zd\n", s);
        }
        
        decrypted_character ^= decrypted_character;

        fgetc(fd);
        c1 = (unsigned char)fgetc(fd);
        c2 = (unsigned char)fgetc(fd);
        fgetc(fd);
        //printf("%X, %X\n", c1, c2);

        for (j = 0; j < 8; j++, i++)
        {   int xa;
            mpz_powm_ui(rp, r[i], 2, n);

            //daca r[j]^2 = R[j], aleg R[j] si c1, altfel aleg uR[j] si c2
            if (mpz_cmp(rp, R[i]) == 0)
            {
                bit = ((1 << (7 - j)) & c1) == 0 ? 1 : -1;
                mpz_set(cR, R[i]);
                xa = 1;
            }
            else
            {
                bit = ((1 << (7 - j)) & c2) == 0 ? 1 : -1; 
                mpz_set(cR, uR[i]);
                xa = 2;
            }

            Q(cR, S, s, n, x, y, r_state);
     //       gmp_printf("%d.(%d)\tx=%Zd\n\ty=%Zd\n", i, xa, x, y);    

            g(tmp1, s, y, n);
            gmp_printf("\ng=%Zd\n\n", tmp1);

            f(tmp1, r[i], x, n);
            m = bit * mpz_jacobi(tmp1, n);

            mrev = (m == -1) ? 1 : 0 ;
            decrypted_character |= (mrev << (7 - j));    
        }

        fprintf(fd_write, "%c", decrypted_character);
    }

    for (i = 0; i < l; i++)
        mpz_clear(R[i]);

    for (i = 0; i < l; i++)
        mpz_clear(uR[i]);

    free(R);
    free(uR);

    mpz_clear(tmp1);
    mpz_clear(tmp2);
    mpz_clear(s);
    mpz_clear(x);
    mpz_clear(y);
    mpz_clear(cR);
    mpz_clear(S);
    mpz_clear(rp);

    fclose(fd);
    fclose(fd_write);
}


void ReadPublicParameters(mpz_t n, mpz_t u, int l, char** error)
{
    FILE *fd;

    fd = fopen("public_params", "r");

    if (fd == NULL)
    {
        *error = ERR_FILE_OPEN;
        return;
    }

    if (mpz_inp_str(n, fd, 10) == 0)
    {
        *error = ERR_FILE_READ;
        return;   
    }

    if (mpz_inp_str(u, fd, 10) == 0)
    {
        *error = ERR_FILE_READ;
        return;   
    }

    fclose(fd);

    *error = SUCCESS;
}


void ReadPrivateParameters(mpz_t p, mpz_t q, mpz_t *r, int l, char** error)
{
    int i;
    FILE *fd;
    
    fd = fopen("private_per_user_param", "r");

    if (fd == NULL)
    {
        *error = ERR_FILE_OPEN;
        return;
    }

    for (i = 0; i < l; i++)
    {
        mpz_init(r[i]);
        if (mpz_inp_str(r[i], fd, 10) == 0)
        {
            *error = ERR_FILE_READ;
            return;   
        }
    }

    fclose(fd);

  fd = fopen("private_params", "r");

    if (fd == NULL)
    {
        *error = ERR_FILE_OPEN;
        return;
    }

    if (mpz_inp_str(p, fd, 10) == 0)
    {
        *error = ERR_FILE_READ;
        return;   
    }

    if (mpz_inp_str(q, fd, 10) == 0)
    {
        *error = ERR_FILE_READ;
        return;   
    }

    fclose(fd);

    *error = SUCCESS;

    *error = SUCCESS;
}


int main(int argc, char *argv[])
{
    if (argc < 4) 
    {
        fprintf(stderr, "Usage: %s <identity> <l> <plaintext_file>\n", argv[0]);
        return 1;
    }

    int l = atoi(argv[2]), i;
    char *error;
    mpz_t *r, n, u, p, q;

    mpz_init(n);
    mpz_init(u);
    mpz_init(p);
    mpz_init(q);

    ReadPublicParameters(n, u, l, &error);

    if (strcmp(error, SUCCESS) != 0)
    {
        PrintError(error);
        return 1;
    }

    r = (mpz_t*)malloc(l * sizeof(mpz_t));

    if (r == NULL)
    {
        PrintError(ERR_MALLOC);
        return 1;
    }

    ReadPrivateParameters(p, q, r, l, &error);

    if (strcmp(error, SUCCESS) != 0)
    {
        PrintError(error);
        return 1;
    }

    Decrypt(argv[3], argv[1], l, p, q, n, u, r, &error);

    if (strcmp(error, SUCCESS) != 0)
    {
        PrintError(error);
        return 1;
    }

    for (i = 0; i < l; i++)
        mpz_clear(r[i]);

    free(r);

    mpz_clear(n);
    mpz_clear(u);
    mpz_clear(p);
    mpz_clear(q);
}