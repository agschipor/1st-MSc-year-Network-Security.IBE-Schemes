#include <stdio.h>
#include <math.h>
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

//, unsigned char** hash
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

    do 
    {
        do 
        {
            mpz_urandomm(t, r_state, n);
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
    /*gmp_printf("\nt=%Zd\n", cx);*/

    mpz_clear(cx);
    ////////////////////////////////

    mpz_clear(rgcd);
    mpz_clear(inv_tmp);
    mpz_clear(tmp);
    mpz_clear(t);
}


void Encrypt(char* filename, unsigned char* identity, int l, mpz_t n, mpz_t u, char** error)
{
    FILE *fd, *fd_write;
    gmp_randstate_t r_state;
    mpz_t R, uR, x, y, s, S, tmp, *xs, *ys, *xbs, *ybs, *ss;
    int i, bit, ascii_code, c1, c2, crev, k, alpha, beta;
    unsigned char *hash, *hex_hash, character, encrypted_character1, encrypted_character2;

    mpz_init(x);
    mpz_init(y);
    mpz_init(s);
    mpz_init(S);
    mpz_init(R);
    mpz_init(uR);
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

    k = ceil(sqrt(l));

    xs = (mpz_t*)malloc(k * sizeof(mpz_t));

    if (xs == NULL)
    {
        *error = ERR_MALLOC;
        return;
    }

    ys = (mpz_t*)malloc(k * sizeof(mpz_t));

    if (ys == NULL)
    {
        *error = ERR_MALLOC;
        return;
    }

    xbs = (mpz_t*)malloc(k * sizeof(mpz_t));

    if (xbs == NULL)
    {
        *error = ERR_MALLOC;
        return;
    }

    ybs = (mpz_t*)malloc(k * sizeof(mpz_t));

    if (ybs == NULL)
    {
        *error = ERR_MALLOC;
        return;
    }

    ss = (mpz_t*)malloc(k * sizeof(mpz_t));

    if (ss == NULL)
    {
        *error = ERR_MALLOC;
        return;
    }

    hash = GetHash(identity, error);

    if (strcmp(*error, SUCCESS) != 0)
        return;

    hex_hash = GetHexHash(hash, error);    

    if (strcmp(*error, SUCCESS) != 0)
        return;

    mpz_set_str(R, hex_hash, 16);
    mpz_mod(R, R, n);

    
    GetJnHash(n, R);

    mpz_mul(uR, R, u);
    mpz_mod(uR, uR, n);

    gmp_randinit_mt(r_state);
    gmp_randseed_ui(r_state, time(NULL)); 

    for (i = 0; i < k; i++)
    {
        mpz_init(xs[i]);
        mpz_init(ys[i]);

        mpz_init(xbs[i]);
        mpz_init(ybs[i]);

        mpz_init(ss[i]);
    }

    while (1)
    {
        i = 0;
        alpha = 1;
        beta = 0;
        
        while (i < l) 
        {
            if (i % 8 == 0)
            {
                encrypted_character1 ^= encrypted_character1;
                encrypted_character2 ^= encrypted_character2;

                ascii_code = fgetc(fd);
                character = (unsigned char)ascii_code;

                if (ascii_code == EOF && i != 0)
                    ascii_code = character = 0x20;

                if (ascii_code == EOF)
                    break;
            }

            bit = ((1 << 7) & character) == 0 ? 1 : -1;
            character <<= 1;

            if (i < k)
            {
                mpz_urandomm(ss[i], r_state, n);
                mpz_powm_ui(S, ss[i], 2, n);

                Q(R, S, ss[i], n, xs[i], ys[i], r_state);
                g(tmp, ss[i], ys[i], n);
                c1 = bit * mpz_jacobi(tmp, n);     

                Q(uR, S, ss[i], n, xbs[i], ybs[i], r_state);
                g(tmp, ss[i], ybs[i], n);
                c2 = bit * mpz_jacobi(tmp, n);

                crev = (c1 == -1) ? 1 : 0;
                encrypted_character1 |= crev;
                
                crev = (c2 == -1) ? 1 : 0;
                encrypted_character2 |= crev;
            }
            else
            {
                mpz_mul(s, ss[alpha], ss[beta]);
                mpz_mod(s, s, n);

                mpz_mul(tmp, R, xs[alpha]);
                mpz_mod(tmp, tmp, n);
                mpz_mul(tmp, tmp, xs[beta]);
                mpz_mod(tmp, tmp, n);
                mpz_add_ui(tmp, tmp, 1);
                mpz_mod(tmp, tmp, n);
                mpz_invert(tmp, tmp, n);

                mpz_add(x, xs[alpha], xs[beta]);
                mpz_mod(x, x, n);

                mpz_mul(x, x, tmp);
                mpz_mod(x, x, n);

                mpz_mul(y, ys[alpha], ys[beta]);
                mpz_mod(y, y, n);
                mpz_mul(y, y, tmp);
                mpz_mod(y, y, n);

                g(tmp, s, y, n);
                c1 = bit * mpz_jacobi(tmp, n);

                mpz_mul(tmp, uR, xbs[alpha]);
                mpz_mod(tmp, tmp, n);
                mpz_mul(tmp, tmp, xbs[beta]);
                mpz_mod(tmp, tmp, n);
                mpz_add_ui(tmp, tmp, 1);
                mpz_mod(tmp, tmp, n);
                mpz_invert(tmp, tmp, n);

                mpz_add(x, xbs[alpha], xbs[beta]);
                mpz_mod(x, x, n);

                mpz_mul(x, x, tmp);
                mpz_mod(x, x, n);

                mpz_mul(y, ybs[alpha], ybs[beta]);
                mpz_mod(y, y, n);
                mpz_mul(y, y, tmp);
                mpz_mod(y, y, n);
                
                g(tmp, s, y, n);
                c2 = bit * mpz_jacobi(tmp, n);

                crev = (c1 == -1) ? 1 : 0;
                encrypted_character1 |= crev;

                crev = (c2 == -1) ? 1 : 0;
                encrypted_character2 |= crev;

                beta++;
                if (beta == k)
                {
                    alpha++;
                    beta = 0;
                }
            }

            i++;

            if (i % 8 == 0)
                fprintf(fd_write, " %c%c ", encrypted_character1, encrypted_character2);
            else
            {
                encrypted_character1 <<= 1;
                encrypted_character2 <<= 1;
            }
        }

        if (ascii_code == EOF)
            break;

        for (i = 0; i < k; i++)
        {
            fprintf(fd_write, " ");
            mpz_out_str(fd_write, 10, xs[i]);
            fprintf(fd_write, " ");
            mpz_out_str(fd_write, 10, xbs[i]);
        }
    }

    for (i = 0; i < k; i++)
    {
        mpz_clear(xs[i]);
        mpz_clear(ys[i]);
        mpz_clear(xbs[i]);
        mpz_clear(ybs[i]);
        mpz_clear(ss[i]);
    }

    free(ss);
    free(xs);
    free(ys);
    free(xbs);
    free(ybs);

    mpz_clear(x);
    mpz_clear(y);
    mpz_clear(s);
    mpz_clear(S);
    mpz_clear(tmp);
    mpz_clear(R);
    mpz_clear(uR);

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