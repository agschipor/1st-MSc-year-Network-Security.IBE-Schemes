#include <stdio.h>
#include <stdlib.h>     
#include <gmp.h>
#include <time.h>
#include <string.h>
#include <malloc.h>
#include <openssl/sha.h>
#include <errno.h>
#include <limits.h>

#define ERR_FILE_OPEN "file open failed"
#define ERR_FILE_WRITE "file write failed"
#define ERR_FILE_READ "file read failed"
#define ERR_MALLOC "malloc error"
#define ERR_SQURE_ROOT_MODULO "cannot calculate square root modulo"
#define ERR_IDENTITY_LENGTH_GREATHER_THAN_BUFSIZ "identity length greather than BUFSIZ"
#define SUCCESS "success"



void PrintError(char* error)
{
    fprintf(stderr, "<<ERROR>>\t%s:\t%s", error, strerror(errno));
}


unsigned char* GetHash(unsigned char* identity, char** error)
{
    int i;
    size_t length;
    unsigned char buffer[BUFSIZ], *hash;
    SHA256_CTX ctx;
    
    SHA256_Init(&ctx);
 
    length = strlen(identity);
    if (length > BUFSIZ) 
    {
        *error = ERR_IDENTITY_LENGTH_GREATHER_THAN_BUFSIZ;
        return NULL;
    }

    for (i = 0; i < length; i++)
        buffer[i] = identity[i];

    buffer[i] = '\0';

    SHA256_Update(&ctx, buffer, length);
    SHA256_Final(buffer, &ctx);

    hash = (unsigned char*)malloc(SHA256_DIGEST_LENGTH * sizeof(unsigned char) + 1);

    if (hash == NULL)
    {
        *error = ERR_MALLOC;
        return NULL;
    }

    for (i = 0; i < SHA256_DIGEST_LENGTH; i++)
        hash[i] = buffer[i];

    hash[SHA256_DIGEST_LENGTH] = '\0';

    *error = SUCCESS;

    return hash;
}


unsigned char* GetHexHash(unsigned char* hash, char** error)
{
    int i, j;
    unsigned char* hex_hash;

    hex_hash = (unsigned char*)malloc(65*sizeof(unsigned char));

    if (hex_hash == NULL)
    {
        *error = ERR_MALLOC;
        return NULL;
    }

    for (i = 0, j = 0; i < 32; i++, j+=2)
        sprintf((hex_hash+j), "%02X", hash[i]);

    *error = SUCCESS;

    return hex_hash;
}


void GetJnHash(mpz_t n, mpz_t jn_hash)
{
    while (mpz_jacobi(jn_hash, n) != 1)
    {
        mpz_add_ui(jn_hash, jn_hash, 1);
        mpz_mod(jn_hash, jn_hash, n);
    }
}


void ReadPublicParameters(mpz_t n, mpz_t u, char** error)
{
    FILE *fd;
    int i;

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


//################################################
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
//################################################################


void GetSquareRootsModulo(mpz_t *z, mpz_t a, mpz_t p, mpz_t q, mpz_t n, char** error)
{
    mpz_t tmp1, tmp2;

    mpz_init(tmp1);
    mpz_init(tmp2);

    if (TonelliShanks(tmp1, a, p) == 1)
    {
        *error = ERR_SQURE_ROOT_MODULO;
        return;
    }

    if (TonelliShanks(tmp2, a, q) == 1)
    {
        *error = ERR_SQURE_ROOT_MODULO;
        return;   
    }

    CRTTwo(z[0], tmp1, p, tmp2, q, n);

    mpz_mul_si(tmp1, tmp1, -1);
    mpz_mod(tmp1, tmp1, p);

    mpz_mul_si(z[1], z[0], -1);
    mpz_mod(z[1], z[1], n);

    CRTTwo(z[2], tmp1, p, tmp2, q, n);    

    mpz_mul_si(z[3], z[2], -1);
    mpz_mod(z[3], z[3], n);

    mpz_clear(tmp1);
    mpz_clear(tmp2);

    *error = SUCCESS;
}



void ReadPrivateParameters(mpz_t p, mpz_t q, char** error)
{
    FILE *fd;
    int i;

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
}

//---------------------------------------------------------------------------------
void KeyGen(unsigned char* identity, mpz_t rj, mpz_t n, mpz_t u, mpz_t p, mpz_t q, char** error)
{
    int i, w;
    mpz_t uRj, z[4];
    unsigned char *hash, *hex_hash;

    mpz_init(uRj);

    srand(time(NULL));

    for (i = 0; i < 4; i++)
        mpz_init(z[i]);

    hash = GetHash(identity, error);

    if (strcmp(*error, SUCCESS) != 0)
        return;

    hex_hash = GetHexHash(hash, error);    

    if (strcmp(*error, SUCCESS) != 0)
        return;

    mpz_set_str(uRj, hex_hash, 16);
    mpz_mod(uRj, uRj, n);

    GetJnHash(n, uRj);

    w = rand() % 4;

    if (mpz_legendre(uRj, p) == -1 || mpz_legendre(uRj, q) == -1)
    {
        mpz_mul(uRj, u, uRj);
        mpz_mod(uRj, uRj, n);
    }

    GetSquareRootsModulo(z, uRj, p, q, n, error);

    if (strcmp(*error, SUCCESS) != 0)
        return;

    mpz_set(rj, z[w]);
    
    free(hash);
    free(hex_hash);


    for (i = 0; i < 4; i++)
        mpz_clear(z[i]);

    mpz_clear(uRj);
}
//---------------------------------------------------------------------------------

void WritePrivateParametersToFile(mpz_t rj, char** error)
{   
    int i;
    FILE *fd = fopen("private_per_user_param", "w");

    if (fd == NULL)
    {
        *error = ERR_FILE_OPEN;
        return;
    }

    if (mpz_out_str(fd, 10, rj) == 0)
    {
        *error = ERR_FILE_WRITE;
        return;
    }

    fclose(fd);

    *error = SUCCESS;
}


int main(int argc, char *argv[])
{
    if (argc < 2) 
    {
        fprintf(stderr, "Usage: %s <identity>\n", argv[0]);
        return 1;
    }

    int i;
    char *error;
    mpz_t n, u, p, q, rj;

    mpz_init(n);
    mpz_init(u);
    mpz_init(p);
    mpz_init(q);
    mpz_init(rj);

    ReadPublicParameters(n, u, &error);

    if (strcmp(error, SUCCESS) != 0)
    {
        PrintError(error);
        return 1;
    }

    ReadPrivateParameters(p, q, &error);

    if (strcmp(error, SUCCESS) != 0)
    {
        PrintError(error);
        return 1;
    }

    KeyGen((unsigned char*)argv[1], rj, n, u, p, q, &error);

    if (strcmp(error, SUCCESS) != 0)
    {
        PrintError(error);
        return 1;
    }

    WritePrivateParametersToFile(rj, &error);

    if (strcmp(error, SUCCESS) != 0)
    {
        PrintError(error);
        return 1;
    }

    mpz_clear(rj);
    mpz_clear(n);
    mpz_clear(u);
    mpz_clear(p);
    mpz_clear(q);

    return 0;
}