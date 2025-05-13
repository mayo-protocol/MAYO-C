// SPDX-#define F_TAIL_LEN 4    /* Length of the field extension defining polynomial tail */

/**
 * Field defining polynomial tails for each parameter set
 * Format: coefficients of the polynomial after the highest degree term
 */
#define F_TAIL_64                                                              \
  { 8, 0, 2, 8 } /* f(z) =  z^64 + x^3*z^3 + x*z^2 + x^3 */
#define F_TAIL_78                                                              \
  { 8, 1, 1, 0 } /* f(z) =  z^78 + z^2 + z + x^3 */
#define F_TAIL_108                                                             \
  { 8, 0, 1, 7 } /* f(z) =  z^108 + (x^2 + x + 1)*z^3 + z^2 + x^3 */
#define F_TAIL_142                                                             \
  { 4, 0, 8, 1 } /* f(z) =  z^142 + z^3 + x^3*z^2 + x^2 */dentifier: Apache-2.0

#ifndef MAYO_H
#define MAYO_H

#include <stdint.h>
#include <stdlib.h>

/**
 * MAYO parameter sets macros - These define the polynomial to use for each MAYO variant
 * For example, MAYO_1 uses a field extension with polynomial z^78 + z^2 + z + x^3
 */
#define F_TAIL_LEN 4
#define F_TAIL_64                                                              \
  { 8, 0, 2, 8 } /* f(z) =  z^64 + x^3*z^3 + x*z^2 + x^3 */
#define F_TAIL_78                                                              \
  { 8, 1, 1, 0 } /* f(z) =  z^78 + z^2 + z + x^3 */
#define F_TAIL_108                                                             \
  { 8, 0, 1, 7 } /* f(z) =  z^108 + (x^2 + x + 1)*z^3 + z^2 + x^3 */
#define F_TAIL_142                                                             \
  { 4, 0, 8, 1 } /* f(z) =  z^142 + z^3 + x^3*z^2 + x^2 */

#define MAYO_1_name "MAYO_1"
#define MAYO_1_n 86
#define MAYO_1_m 78
#define MAYO_1_m_vec_limbs 5
#define MAYO_1_o 8
#define MAYO_1_v (MAYO_1_n - MAYO_1_o)
#define MAYO_1_A_cols (MAYO_1_k * MAYO_1_o + 1)
#define MAYO_1_k 10
#define MAYO_1_q 16
#define MAYO_1_m_bytes 39
#define MAYO_1_O_bytes 312
#define MAYO_1_v_bytes 39
#define MAYO_1_r_bytes 40
#define MAYO_1_P1_bytes 120159
#define MAYO_1_P2_bytes 24336
#define MAYO_1_P3_bytes 1404
#define MAYO_1_csk_bytes 24
#define MAYO_1_cpk_bytes 1420
#define MAYO_1_sig_bytes 454
#define MAYO_1_f_tail F_TAIL_78
#define MAYO_1_f_tail_arr f_tail_78
#define MAYO_1_salt_bytes 24
#define MAYO_1_digest_bytes 32
#define MAYO_1_pk_seed_bytes 16
#define MAYO_1_sk_seed_bytes 24

#define MAYO_2_name "MAYO_2"
#define MAYO_2_n 81
#define MAYO_2_m 64
#define MAYO_2_m_vec_limbs 4
#define MAYO_2_o 17
#define MAYO_2_v (MAYO_2_n - MAYO_2_o)
#define MAYO_2_A_cols (MAYO_2_k * MAYO_2_o + 1)
#define MAYO_2_k 4
#define MAYO_2_q 16
#define MAYO_2_m_bytes 32
#define MAYO_2_O_bytes 544
#define MAYO_2_v_bytes 32
#define MAYO_2_r_bytes 34
#define MAYO_2_P1_bytes 66560
#define MAYO_2_P2_bytes 34816
#define MAYO_2_P3_bytes 4896
#define MAYO_2_csk_bytes 24
#define MAYO_2_cpk_bytes 4912
#define MAYO_2_sig_bytes 186
#define MAYO_2_f_tail F_TAIL_64
#define MAYO_2_f_tail_arr f_tail_64
#define MAYO_2_salt_bytes 24
#define MAYO_2_digest_bytes 32
#define MAYO_2_pk_seed_bytes 16
#define MAYO_2_sk_seed_bytes 24

#define MAYO_3_name "MAYO_3"
#define MAYO_3_n 118
#define MAYO_3_m 108
#define MAYO_3_m_vec_limbs 7
#define MAYO_3_o 10
#define MAYO_3_v (MAYO_3_n - MAYO_3_o)
#define MAYO_3_A_cols (MAYO_3_k * MAYO_3_o + 1)
#define MAYO_3_k 11
#define MAYO_3_q 16
#define MAYO_3_m_bytes 54
#define MAYO_3_O_bytes 540
#define MAYO_3_v_bytes 54
#define MAYO_3_r_bytes 55
#define MAYO_3_P1_bytes 317844
#define MAYO_3_P2_bytes 58320
#define MAYO_3_P3_bytes 2970
#define MAYO_3_csk_bytes 32
#define MAYO_3_cpk_bytes 2986
#define MAYO_3_sig_bytes 681
#define MAYO_3_f_tail F_TAIL_108
#define MAYO_3_f_tail_arr f_tail_108
#define MAYO_3_salt_bytes 32
#define MAYO_3_digest_bytes 48
#define MAYO_3_pk_seed_bytes 16
#define MAYO_3_sk_seed_bytes 32

#define MAYO_5_name "MAYO_5"
#define MAYO_5_n 154
#define MAYO_5_m 142
#define MAYO_5_m_vec_limbs 9
#define MAYO_5_o 12
#define MAYO_5_v (MAYO_5_n - MAYO_5_o)
#define MAYO_5_A_cols (MAYO_5_k * MAYO_5_o + 1)
#define MAYO_5_k 12
#define MAYO_5_q 16
#define MAYO_5_m_bytes 71
#define MAYO_5_O_bytes 852
#define MAYO_5_v_bytes 71
#define MAYO_5_r_bytes 72
#define MAYO_5_P1_bytes 720863
#define MAYO_5_P2_bytes 120984
#define MAYO_5_P3_bytes 5538
#define MAYO_5_csk_bytes 40
#define MAYO_5_cpk_bytes 5554
#define MAYO_5_sig_bytes 964
#define MAYO_5_f_tail F_TAIL_142
#define MAYO_5_f_tail_arr f_tail_142
#define MAYO_5_salt_bytes 40
#define MAYO_5_digest_bytes 64
#define MAYO_5_pk_seed_bytes 16
#define MAYO_5_sk_seed_bytes 40

#define PARAM_JOIN2_(a, b) a##_##b
#define PARAM_JOIN2(a, b) PARAM_JOIN2_(a, b)
/* Get a specific parameter value for the current MAYO variant by appending the suffix */
#define PARAM_NAME(end) PARAM_JOIN2(MAYO_VARIANT, end)

#if defined(MAYO_VARIANT)
#define PARAM_JOIN3_(a, b, c) pqmayo_##a##_##b##_##c
#define PARAM_JOIN3(a, b, c) PARAM_JOIN3_(a, b, c)
#define PARAM_NAME3(end, s) PARAM_JOIN3(MAYO_VARIANT, end, s)

#if defined(MAYO_BUILD_TYPE_REF)
#define MAYO_NAMESPACE(s) PARAM_NAME3(ref, s)
#elif defined(MAYO_BUILD_TYPE_OPT)
#define MAYO_NAMESPACE(s) PARAM_NAME3(opt, s)
#elif defined(MAYO_BUILD_TYPE_AVX2)
#define MAYO_NAMESPACE(s) PARAM_NAME3(avx2, s)
#elif defined(MAYO_BUILD_TYPE_NEON)
#define MAYO_NAMESPACE(s) PARAM_NAME3(neon, s)
#else
#error "Build type not known"
#endif

#else
#define MAYO_NAMESPACE(s) s
#endif

#ifdef ENABLE_PARAMS_DYNAMIC
#define NAME_MAX mayo5
#define N_MAX 154
#define M_MAX 142
#define O_MAX 17
#define K_MAX 12
#define Q_MAX 16
#define PK_SEED_BYTES_MAX 16
#define SK_SEED_BYTES_MAX 40
#define SALT_BYTES_MAX 40
#define DIGEST_BYTES_MAX 64
#define V_MAX 142
#define O_BYTES_MAX 852
#define V_BYTES_MAX 71
#define R_BYTES_MAX 72
#define P1_BYTES_MAX 720863
#define P2_BYTES_MAX 120984
#define P3_BYTES_MAX 5538
#define SIG_BYTES_MAX 964
#define CPK_BYTES_MAX 5554
#define CSK_BYTES_MAX 40
#define M_BYTES_MAX 71
#define M_VEC_LIMBS_MAX 9
#elif defined(MAYO_VARIANT)
#define M_MAX PARAM_NAME(m)
#define M_VEC_LIMBS_MAX PARAM_NAME(m_vec_limbs)
#define N_MAX PARAM_NAME(n)
#define O_MAX PARAM_NAME(o)
#define V_MAX PARAM_NAME(v)
#define K_MAX PARAM_NAME(k)
#define Q_MAX PARAM_NAME(q)
#define M_BYTES_MAX PARAM_NAME(m_bytes)
#define O_BYTES_MAX PARAM_NAME(O_bytes)
#define V_BYTES_MAX PARAM_NAME(v_bytes)
#define R_BYTES_MAX PARAM_NAME(r_bytes)
#define P1_BYTES_MAX PARAM_NAME(P1_bytes)
#define P2_BYTES_MAX PARAM_NAME(P2_bytes)
#define P3_BYTES_MAX PARAM_NAME(P3_bytes)
#define SIG_BYTES_MAX PARAM_NAME(sig_bytes)
#define CSK_BYTES_MAX PARAM_NAME(csk_bytes)
#define CPK_BYTES_MAX PARAM_NAME(cpk_bytes)
#define SALT_BYTES_MAX PARAM_NAME(salt_bytes)
#define DIGEST_BYTES_MAX PARAM_NAME(digest_bytes)
#define PK_SEED_BYTES_MAX PARAM_NAME(pk_seed_bytes)
#define SK_SEED_BYTES_MAX SALT_BYTES_MAX
#else
#error "Parameter not specified"
#endif

#define P1_LIMBS_MAX (V_MAX*(V_MAX+1)/2*M_VEC_LIMBS_MAX)
#define P2_LIMBS_MAX (V_MAX*O_MAX*M_VEC_LIMBS_MAX)
#define P3_LIMBS_MAX (O_MAX*(O_MAX+1)/2*M_VEC_LIMBS_MAX)

#ifdef ENABLE_PARAMS_DYNAMIC
#define PARAM_name(p) (p->name)
#define PARAM_m(p) (p->m)
#define PARAM_m_vec_limbs(p) (p->m_vec_limbs)
#define PARAM_n(p) (p->n)
#define PARAM_o(p) (p->o)
#define PARAM_v(p) (p->n - p->o)
#define PARAM_A_cols(p) (p->k * p->o + 1)
#define PARAM_k(p) (p->k)
#define PARAM_q(p) (p->q)
#define PARAM_m_bytes(p) (p->m_bytes)
#define PARAM_O_bytes(p) (p->O_bytes)
#define PARAM_v_bytes(p) (p->v_bytes)
#define PARAM_r_bytes(p) (p->r_bytes)
#define PARAM_P1_bytes(p) (p->P1_bytes)
#define PARAM_P2_bytes(p) (p->P2_bytes)
#define PARAM_P3_bytes(p) (p->P3_bytes)
#define PARAM_csk_bytes(p) (p->csk_bytes)
#define PARAM_cpk_bytes(p) (p->cpk_bytes)
#define PARAM_sig_bytes(p) (p->sig_bytes)
#define PARAM_f_tail(p) (p->f_tail)
#define PARAM_salt_bytes(p) (p->salt_bytes)
#define PARAM_sk_seed_bytes(p) (p->sk_seed_bytes)
#define PARAM_digest_bytes(p) (p->digest_bytes)
#define PARAM_pk_seed_bytes(p) (p->pk_seed_bytes)
#elif defined(MAYO_VARIANT)
#define PARAM_name(p) PARAM_NAME(name)
#define PARAM_m(p) PARAM_NAME(m)
#define PARAM_m_vec_limbs(p) PARAM_NAME(m_vec_limbs)
#define PARAM_n(p) PARAM_NAME(n)
#define PARAM_o(p) PARAM_NAME(o)
#define PARAM_v(p) PARAM_NAME(v)
#define PARAM_A_cols(p) PARAM_NAME(A_cols)
#define PARAM_k(p) PARAM_NAME(k)
#define PARAM_q(p) PARAM_NAME(q)
#define PARAM_m_bytes(p) PARAM_NAME(m_bytes)
#define PARAM_O_bytes(p) PARAM_NAME(O_bytes)
#define PARAM_v_bytes(p) PARAM_NAME(v_bytes)
#define PARAM_r_bytes(p) PARAM_NAME(r_bytes)
#define PARAM_P1_bytes(p) PARAM_NAME(P1_bytes)
#define PARAM_P2_bytes(p) PARAM_NAME(P2_bytes)
#define PARAM_P3_bytes(p) PARAM_NAME(P3_bytes)
#define PARAM_csk_bytes(p) PARAM_NAME(csk_bytes)
#define PARAM_cpk_bytes(p) PARAM_NAME(cpk_bytes)
#define PARAM_epk_bytes(p) PARAM_NAME(epk_bytes)
#define PARAM_sig_bytes(p) PARAM_NAME(sig_bytes)
static const unsigned char f_tail[] = PARAM_NAME(f_tail);
#define PARAM_salt_bytes(p) PARAM_NAME(salt_bytes)
#define PARAM_sk_seed_bytes(p) PARAM_NAME(sk_seed_bytes)
#define PARAM_digest_bytes(p) PARAM_NAME(digest_bytes)
#define PARAM_pk_seed_bytes(p) PARAM_NAME(pk_seed_bytes)
#define PARAM_f_tail(p) f_tail
#else
#error "Parameter not specified"
#endif

#define PARAM_P1_limbs(p) (PARAM_v(p)*(PARAM_v(p)+1)/2*PARAM_m_vec_limbs(p))
#define PARAM_P2_limbs(p) (PARAM_v(p)*PARAM_o(p)*PARAM_m_vec_limbs(p))
#define PARAM_P3_limbs(p) (PARAM_o(p)*(PARAM_o(p)+1)/2*PARAM_m_vec_limbs(p))
#define PARAM_EPK_limbs(p) (PARAM_P1_limbs(p) + PARAM_P2_limbs(p) + PARAM_P3_limbs(p))

/**
 * Struct defining MAYO parameters
 * This structure contains all the parameter values needed to define a specific MAYO variant
 */
typedef struct {
    int m;                      /* Number of equations in the system (size of public matrix) */
    int n;                      /* Total number of variables */
    int o;                      /* Number of Oil variables */
    int k;                      /* Number of field extensions in the oil space */
    int q;                      /* Field size (always 16 for MAYO) */
    const unsigned char *f_tail; /* Field extension defining polynomial tail */
    int m_bytes;                /* Number of bytes needed to represent m field elements */
    int O_bytes;                /* Number of bytes for oil submatrix */
    int v_bytes;                /* Number of bytes for vinegar variables */
    int r_bytes;                /* Number of bytes for r value */
    int R_bytes;                /* Number of bytes for R value */
    int P1_bytes;               /* Number of bytes for P1 matrix */
    int P2_bytes;               /* Number of bytes for P2 matrix */
    int P3_bytes;               /* Number of bytes for P3 matrix */
    int csk_bytes;              /* Size of compact secret key in bytes */
    int cpk_bytes;              /* Size of compact public key in bytes */
    int sig_bytes;              /* Size of signature in bytes */
    int salt_bytes;             /* Size of salt in bytes */
    int sk_seed_bytes;          /* Size of secret key seed in bytes */
    int digest_bytes;           /* Size of hash digest in bytes */
    int pk_seed_bytes;          /* Size of public key seed in bytes */
    int m_vec_limbs;            /* Number of 64-bit limbs for vectors of size m */
    const char *name;           /* String identifier of the parameter set */
} mayo_params_t;

typedef struct sk_t {
    uint64_t p[P1_LIMBS_MAX + P2_LIMBS_MAX];  /* Matrices P1 and P2 of the expanded secret key */
    uint8_t O[V_MAX*O_MAX];                   /* Oil subspace matrix for the expanded secret key */
} sk_t;

typedef struct pk_t {
    uint64_t p[P1_LIMBS_MAX + P2_LIMBS_MAX + P3_LIMBS_MAX]; /* All matrices P1, P2, P3 of the expanded public key */
} pk_t;

/**
 * MAYO parameter sets
 */
#ifdef ENABLE_PARAMS_DYNAMIC
extern const mayo_params_t MAYO_1;
extern const mayo_params_t MAYO_2;
extern const mayo_params_t MAYO_3;
extern const mayo_params_t MAYO_5;
#endif

/**
 * Status codes
 */
#define MAYO_OK 0     /* Operation completed successfully */
#define MAYO_ERR 1    /* Operation failed (e.g., verification failure) */

/**
 * Mayo keypair generation.
 *
 * The implementation corresponds to Mayo.CompactKeyGen() in the Mayo spec.
 * Generates a new keypair for the Mayo signature scheme with the specified parameter set.
 * The caller is responsible to allocate sufficient memory to hold pk and sk.
 *
 * The public key can be used for signature verification (mayo_verify, mayo_open).
 * The secret key can be used for signature generation (mayo_sign).
 *
 * @param[in] p Mayo parameter set (MAYO_1, MAYO_2, MAYO_3, or MAYO_5)
 * @param[out] pk Buffer to store the generated public key (size: PARAM_cpk_bytes(p))
 * @param[out] sk Buffer to store the generated secret key (size: PARAM_csk_bytes(p))
 * @return int MAYO_OK on success, or an error code
 */
#define mayo_keypair MAYO_NAMESPACE(mayo_keypair)
int mayo_keypair(const mayo_params_t *p, unsigned char *pk, unsigned char *sk);

#define mayo_sign_signature MAYO_NAMESPACE(mayo_sign_signature)
/**
 * MAYO signature generation without message concatenation.
 * 
 * This generates only the signature without appending the message.
 * The signature can then be verified using mayo_verify.
 *
 * @param[in] p Mayo parameter set
 * @param[out] sig Signature buffer (should be at least PARAM_sig_bytes bytes)
 * @param[out] siglen Pointer to the length of the signature
 * @param[in] m Message to be signed
 * @param[in] mlen Message length
 * @param[in] csk Compacted secret key
 * @return int status code (MAYO_OK on success)
 */
int mayo_sign_signature(const mayo_params_t *p, unsigned char *sig,
              size_t *siglen, const unsigned char *m,
              size_t mlen, const unsigned char *csk);

/**
 * MAYO signature generation.
 *
 * The implementation performs Mayo.expandSK() + Mayo.sign() in the Mayo spec.
 * This function signs a message using the provided secret key, generating a signature
 * that is concatenated with the original message.
 * 
 * The process involves:
 * 1. Expanding the compact secret key into its internal representation
 * 2. Generating a cryptographic signature for the message
 * 3. Appending the signature to the message in the output buffer
 *
 * Keys provided is a compacted secret key.
 * The caller is responsible to allocate sufficient memory to hold sm.
 *
 * @param[in] p Mayo parameter set
 * @param[out] sm Buffer to store signature concatenated with message (size: PARAM_sig_bytes(p) + mlen)
 * @param[out] smlen Pointer to receive the total length of signature and message
 * @param[in] m Message to be signed
 * @param[in] mlen Message length
 * @param[in] sk Compacted secret key
 * @return int MAYO_OK on success, or an error code
 */
#define mayo_sign MAYO_NAMESPACE(mayo_sign)
int mayo_sign(const mayo_params_t *p, unsigned char *sm,
              size_t *smlen, const unsigned char *m,
              size_t mlen, const unsigned char *sk);

/**
 * Mayo open signature.
 *
 * The implementation performs Mayo.verify(). 
 * If the signature verification succeeded, the recovered message is stored in m.
 * Keys provided is a compact public key.
 * The caller is responsible to allocate sufficient memory to hold m.
 *
 * This function is useful when the message is embedded within the signature+message
 * structure and needs to be verified and extracted in one operation.
 *
 * @param[in] p Mayo parameter set
 * @param[out] m Buffer to store the recovered message if verification succeeds
 * @param[out] mlen Pointer to receive the length of the recovered message
 * @param[in] sm Buffer containing signature concatenated with message
 * @param[in] smlen Length of the signature+message buffer
 * @param[in] pk Compacted public key
 * @return int MAYO_OK on successful verification, MAYO_ERR on failure
 */
#define mayo_open MAYO_NAMESPACE(mayo_open)
int mayo_open(const mayo_params_t *p, unsigned char *m,
              size_t *mlen, const unsigned char *sm,
              size_t smlen, const unsigned char *pk);

/**
 * Mayo compact keypair generation.
 *
 * The implementation corresponds to Mayo.CompactKeyGen() in the Mayo spec.
 * The caller is responsible to allocate sufficient memory to hold pk and sk.
 *
 * outputs a pair (csk, cpk) \in B^{csk_bytes} x B^{cpk_bytes}, where csk and
 * cpk are compact representations of a Mayo secret key and public key
 *
 * @param[in] p Mayo parameter set
 * @param[out] cpk Mayo compacted public key
 * @param[out] csk Mayo compacted secret key
 * @return int status code
 */
#define mayo_keypair_compact MAYO_NAMESPACE(mayo_keypair_compact)
int mayo_keypair_compact(const mayo_params_t *p, unsigned char *cpk,
                         unsigned char *csk);

/**
 * Mayo expand public key.
 *
 * The implementation corresponds to Mayo.expandPK() in the Mayo spec.
 * The caller is responsible to allocate sufficient memory to hold epk.
 *
 * @param[in] p Mayo parameter set
 * @param[in] cpk Compacted public key.
 * @param[out] epk Expanded public key.
 * @return int return code
 */
#define mayo_expand_pk MAYO_NAMESPACE(mayo_expand_pk)
int mayo_expand_pk(const mayo_params_t *p, const unsigned char *cpk,
                   uint64_t *epk);

/**
 * Mayo expand secret key.
 *
 * The implementation corresponds to Mayo.expandSK() in the Mayo spec.
 * The caller is responsible to allocate sufficient memory to hold esk.
 *
 * @param[in] p Mayo parameter set
 * @param[in] csk Compacted secret key.
 * @param[out] esk Expanded secret key.
 * @return int return code
 */
#define mayo_expand_sk MAYO_NAMESPACE(mayo_expand_sk)
int mayo_expand_sk(const mayo_params_t *p, const unsigned char *csk,
                   sk_t *esk);

/**
 * Mayo verify signature.
 *
 * The implementation performs Mayo.verify(). If the signature verification succeeded, returns 0, otherwise 1.
 * Keys provided is a compact public key.
 *
 * @param[in] p Mayo parameter set
 * @param[in] m Message to be verified against the signature
 * @param[in] mlen Length of the message
 * @param[in] sig Signature to verify (without the message)
 * @param[in] pk Compacted public key
 * @return int MAYO_OK (0) if verification succeeded, MAYO_ERR (1) otherwise
 */
#define mayo_verify MAYO_NAMESPACE(mayo_verify)
int mayo_verify(const mayo_params_t *p, const unsigned char *m,
                size_t mlen, const unsigned char *sig,
                const unsigned char *pk);

#endif

