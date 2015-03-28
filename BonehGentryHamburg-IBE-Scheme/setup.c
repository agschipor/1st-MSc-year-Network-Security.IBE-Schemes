#include <stdio.h>
#include <gmp.h>
#include <time.h>
#include <string.h>
#include <malloc.h>
#include <openssl/sha.h>
#include <errno.h>

#define ERR_FILE_OPEN "file open failed"
#define ERR_FILE_WRITE "file write failed"
#define SUCCESS "success"



void PrintError(char* error)
{
    fprintf(stderr, "<<ERROR>>\t%s:\t%s", error, strerror(errno));
}


void GetU(mpz_t u, mpz_t n, mpz_t p, mpz_t q, gmp_randstate_t r_state) 
{
    int jacobi_value, legendre_value_p, legendre_value_q;

    do 
    {
        mpz_urandomm(u, r_state, n);

        jacobi_value = mpz_jacobi(u, n);
        legendre_value_p = mpz_legendre(u, p);
        legendre_value_q = mpz_legendre(u, q);
    }
    while (jacobi_value != 1 || legendre_value_p != -1 || legendre_value_q != -1);
}


void GetPrime(mpz_t prime, gmp_randstate_t r_state)
{
    mpz_t random;

    mpz_init(random);

    mpz_urandomb(random, r_state, 512);
    mpz_nextprime(prime, random);    

    mpz_clear(random);
}


void GetParameters(mpz_t p, mpz_t q, mpz_t n, mpz_t u)
{
    gmp_randstate_t r_state;

    gmp_randinit_mt(r_state);
    gmp_randseed_ui(r_state, time(NULL));

    GetPrime(p, r_state);

    do
    {
        GetPrime(q, r_state);
    }   
    while (mpz_cmp(p, q) == 0);

    mpz_mul(n, p, q);

    GetU(u, n, p, q, r_state);
}

 
void WritePrivateParametersToFile(mpz_t p, mpz_t q, char** error)
{
    FILE *fd = fopen("private_params", "w");

    if (fd == NULL)
    {
        *error = ERR_FILE_OPEN;
        return;
    }

    if (mpz_out_str(fd, 10, p) == 0)
    {
        *error = ERR_FILE_WRITE;
        return;
    }

    fprintf(fd, "\n");

    if (mpz_out_str(fd, 10, q) == 0)
    {
        *error = ERR_FILE_WRITE;
        return;
    }

    fclose(fd);

    *error = SUCCESS;
}


void WritePublicParametersToFile(mpz_t n, mpz_t u, char** error)
{   
    FILE *fd = fopen("public_params", "w");

    if (fd == NULL)
    {
        *error = ERR_FILE_OPEN;
        return;
    }

    if (mpz_out_str(fd, 10, n) == 0)
    {
        *error = ERR_FILE_WRITE;
        return;
    }

    fprintf(fd, "\n");

    if (mpz_out_str(fd, 10, u) == 0)
    {
        *error = ERR_FILE_WRITE;
        return;
    }

    fclose(fd);

    *error = SUCCESS;
}


int main(int argc, char *argv[])
{
    mpz_t p, q, n, u;
    char* error;

    mpz_init(p);
    mpz_init(q);
    mpz_init(n);
    mpz_init(u);

    GetParameters(p, q, n, u);    

    WritePrivateParametersToFile(p, q, &error);

    if (strcmp(error, SUCCESS) != 0)
    {
        PrintError(error);
        return 1;
    }

    WritePublicParametersToFile(n, u, &error);

    if (strcmp(error, SUCCESS) != 0)
    {
        PrintError(error);
        return 1;
    }

    mpz_clear(p);
    mpz_clear(q);
    mpz_clear(n);
    mpz_clear(u);

    return 0;
}