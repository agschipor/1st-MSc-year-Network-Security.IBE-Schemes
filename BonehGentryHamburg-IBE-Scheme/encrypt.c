#include <stdio.h>
#include <stdlib.h>
#include <gmp.h>
#include <time.h>
#include <string.h>
#include <malloc.h>
#include <openssl/sha.h>
#include <errno.h>

#define ERR_FILE_OPEN "file open failed"
#define ERR_FILE_READ "file read failed"
#define ERR_CALLOC "calloc failed"
#define ERR_MALLOC "malloc failed"
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


//########################## nu este folosit aici #######################################
void f(mpz_t res, mpz_t r, mpz_t x, mpz_t n)
{
    mpz_mul(res, x, r);
    mpz_mod(res, res, n);
    mpz_add_ui(res, res, 1);
    mpz_mod(res, res, n);
}
//#######################################################################################


void g(mpz_t res, mpz_t s, mpz_t y, mpz_t n)
{
    mpz_mul(res, y, s);
    mpz_mod(res, res, n);
    mpz_add_ui(res, res, 1);
    mpz_mod(res, res, n);
    mpz_mul_ui(res, res, 2);
    mpz_mod(res, res, n);
}


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


void Encrypt(char* filename, unsigned char* identity, int l, mpz_t n, mpz_t u, char** error)
{
    int i, j, bit, ascii_code, c1, c2, crev;
    mpz_t *R, *uR, x, y, s, S, tmp;
    gmp_randstate_t r_state;
    FILE *fd, *fd_write;
    unsigned char *hash, *hex_hash, character, encrypted_character1, encrypted_character2;

    mpz_init(x);
    mpz_init(y);
    mpz_init(s);
    mpz_init(S);
    mpz_init(tmp);

    fd = fopen(filename, "r");

    if (fd == NULL)
    {
        *error = ERR_FILE_OPEN;
        return;
    }

    fd_write = fopen("encrypted_text", "w");

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
    do
    {   
        encrypted_character1 ^= encrypted_character1;
        encrypted_character2 ^= encrypted_character2;

        ascii_code = fgetc(fd);
        character = (unsigned char)ascii_code;

        if (ascii_code == EOF && i % l != 0)
            ascii_code = character = 0x20;

        if (ascii_code == EOF)
            break;

        if (i % l == 0)
        {
            i = 0;
            mpz_urandomm(s, r_state, n);
            mpz_powm_ui(S, s, 2, n);
            mpz_out_str(fd_write, 10, S);
            //gmp_printf("%Zd\n", s);
        }

        for (j = 0; j < 8; j++, i++)
        {
            bit = ((1 << (7 - j)) & character) == 0 ? 1 : -1;

            Q(R[i], S, s, n, x, y, r_state);
            g(tmp, s, y, n);
            c1 = bit * mpz_jacobi(tmp, n);
            //gmp_printf("%d.(1)\tx=%Zd\n\ty=%Zd\n", i, x, y);    
            gmp_printf("\ng=%Zd\n\n", tmp);


            Q(uR[i], S, s, n, x, y, r_state);
            g(tmp, s, y, n);
            c2 = bit * mpz_jacobi(tmp, n);
            gmp_printf("\ng=%Zd\n\n", tmp);
            //gmp_printf("%d.(2)\tx=%Zd\n\ty=%Zd\n\n", i, x, y);    
            crev = (c1 == -1) ? 1 : 0;
            encrypted_character1 |= (crev << (7 - j));
            crev = (c2 == -1) ? 1 : 0;
            encrypted_character2 |= (crev << (7 - j));
        }    

        fprintf(fd_write, " %c%c ", encrypted_character1, encrypted_character2);
    }
    while (ascii_code != EOF);

    for (i = 0; i < l; i++)
        mpz_clear(R[i]);

    for (i = 0; i < l; i++)
        mpz_clear(uR[i]);


    mpz_clear(x);
    mpz_clear(y);
    mpz_init(s);
    mpz_init(S);
    mpz_clear(tmp);

    free(R);
    free(uR);

    fclose(fd);
    fclose(fd_write);   
}


void ReadPublicParameters(mpz_t n, mpz_t u, int l, char** error)
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


int main(int argc, char *argv[])
{
    if (argc < 4) 
    {
        fprintf(stderr, "Usage: %s <identity> <l> <plaintext_file>\n", argv[0]);
        return 1;
    }

    int l = atoi(argv[2]);
    char *error;
    mpz_t n, u;

    mpz_init(n);
    mpz_init(u);

    ReadPublicParameters(n, u, l, &error);

    if (strcmp(error, SUCCESS) != 0)
    {
        PrintError(error);
        return 1;
    }

    Encrypt(argv[3], (unsigned char*)argv[1], l, n, u, &error);
   
    if (strcmp(error, SUCCESS) != 0)
    {
        PrintError(error);
        return 1;
    }

    mpz_clear(n);
    mpz_clear(u);

    return 0;
}