#include <stdio.h>
#include <gmp.h>
#include <time.h>
#include <string.h>
#include <malloc.h>
#include <openssl/sha.h>
#include <errno.h>
#include <limits.h>
#include <math.h>

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


void f(mpz_t res, mpz_t r, mpz_t x, mpz_t n)
{
    mpz_mul(res, x, r);
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


void Decrypt(char* filename, unsigned char* identity, int l, mpz_t p, mpz_t q, mpz_t n, mpz_t u, mpz_t r, char** error)
{
    int k, i, alpha, beta, read_length, bit, m, mrev, bytes_no, choice;
    mpz_t rp, S, R, uR, cR, x, s, tmp, *xs;
    FILE *fd, *fd_write;
    unsigned char *hash, *hex_hash, *cs, c, decrypted_character;

    mpz_init(R);
    mpz_init(uR);
    mpz_init(rp);
    mpz_init(S);
    mpz_init(cR);
    mpz_init(x);
    mpz_init(s);
    mpz_init(tmp);
    
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

    bytes_no = l/8;

    k = ceil(sqrt(l));

    xs = (mpz_t*)malloc(k * sizeof(mpz_t));

    if (xs == NULL)
    {
        *error = ERR_MALLOC;
        return;
    }

    cs = (char*)malloc(bytes_no * sizeof(char));

    if (cs == NULL)
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
    
    mpz_powm_ui(rp, r, 2, n);

    choice = 2;
    mpz_set(cR, uR);
    if (mpz_cmp(rp, R) == 0)
    {
        choice = 1;
        mpz_set(cR, R);
    }

    while (!feof(fd))
    {    
        for (i = 0; i < bytes_no; i++)
        {
            fgetc(fd);
            cs[i] = (unsigned char)fgetc(fd);
            if (choice == 2)
                cs[i] = (unsigned char)fgetc(fd);
            else
                fgetc(fd);
            fgetc(fd);
        }

        for (i = 0; i < k; i++)
        {
            mpz_init(xs[i]);
            mpz_inp_str(xs[i], fd, 10);

            if (choice == 2)
                mpz_inp_str(xs[i], fd, 10);
            else
                mpz_inp_str(tmp, fd, 10);
        }

        i = 0;
        alpha = 1;
        beta = 0;

        while (i < l)
        {
            if (i % 8 == 0)
            {
                decrypted_character ^= decrypted_character;
                c = cs[i/8];
            }

            bit = ((1 << 7) & c) == 0 ? 1 : -1;
            c <<= 1;

            if (i < k)
            {
                f(tmp, r, xs[i], n);
                m = bit * mpz_jacobi(tmp, n);

                mrev = (m == -1) ? 1 : 0 ;
                decrypted_character |= mrev;
            }
            else
            {
                mpz_mul(tmp, cR, xs[alpha]);
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
                
                f(tmp, r, x, n);

                m = bit * mpz_jacobi(tmp, n);

                mrev = (m == -1) ? 1 : 0 ;
                decrypted_character |= mrev;

                beta++;
                if (beta == k)
                {
                    alpha++;
                    beta = 0;
                }
            }

            i++;

            if (i % 8 == 0)
                fprintf(fd_write, "%c", decrypted_character);
            else
                decrypted_character <<= 1;   
        }
    }

    for (i = 0; i < k; i++)
        mpz_clear(xs[i]);

    free(xs);
    free(cs);

    mpz_clear(R);
    mpz_clear(uR);
    mpz_clear(tmp);
    mpz_clear(s);
    mpz_clear(x);
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


void ReadPrivateParameters(mpz_t p, mpz_t q, mpz_t r, char** error)
{
    int i;
    FILE *fd;
    
    fd = fopen("private_per_user_param", "r");

    if (fd == NULL)
    {
        *error = ERR_FILE_OPEN;
        return;
    }

    if (mpz_inp_str(r, fd, 10) == 0)
    {
        *error = ERR_FILE_READ;
        return;   
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
    mpz_t r, n, u, p, q;

    mpz_init(n);
    mpz_init(u);
    mpz_init(p);
    mpz_init(q);
    mpz_init(r);

    ReadPublicParameters(n, u, l, &error);

    if (strcmp(error, SUCCESS) != 0)
    {
        PrintError(error);
        return 1;
    }

    ReadPrivateParameters(p, q, r, &error);

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

    mpz_clear(n);
    mpz_clear(u);
    mpz_clear(p);
    mpz_clear(q);
    mpz_clear(r);
}