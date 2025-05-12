// SPDX-License-Identifier: Apache-2.0

/**
 * An example to demonstrate how to use the MAYO API.
 */

#include <mayo.h>
#include <mem.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/**
 * Example for MAYO variant:
 * - mayo_keypair
 * - mayo_expand_pk
 * - mayo_expand_sk
 * - mayo_sign
 * - mayo_verify
 * - mayo_open
 * 
 * @param[in] p MAYO parameter
 * @return int return code
 */
static int example_mayo(const mayo_params_t* p) {

    size_t msglen = 32;
    size_t smlen = PARAM_sig_bytes(p) + msglen;//something(p) gives the specific parameter from the parameter set

    unsigned char *pk  = calloc(PARAM_cpk_bytes(p), 1);//public key
    unsigned char *sk  = calloc(PARAM_csk_bytes(p), 1);//secret key

    uint64_t *epk = calloc(1, sizeof(pk_t));//[DOUBT] : why not use pk_t defined in mayo.h, doesn't matter tho
    sk_t *esk = calloc(1, sizeof(sk_t));//sk_t is a struct defined in mayo.h
    // an internal representation optimized for fast signing

    unsigned char *sig = calloc(PARAM_sig_bytes(p) + msglen, 1);//buffer for signature + message

    unsigned char msg[32] = { 0xe };//initial message
    unsigned char msg2[32] = { 0 };//buffer for the recovered message in 

    printf("Example with %s\n", PARAM_name(p));//name of the parameter set

    printf("mayo_keypair -> ");
    int res = mayo_keypair(p, pk, sk);
    if (res != MAYO_OK) {//MAYO_OK is 0
        printf("FAIL\n");
        res = -1;
        goto err;
    } else {
        printf("OK\n");
    }

    //expands the compacted secret key (sk) to the expanded secret key (esk)
    printf("mayo_expand_sk -> ");
    res = mayo_expand_sk(p, sk, esk);
    if (res != MAYO_OK) {
        printf("FAIL\n");
        res = -1;
        goto err;
    } else {
        printf("OK\n");
    }

    //expands the compacted public key (pk) to the expanded public key (epk)
    printf("mayo_expand_pk -> ");
    res = mayo_expand_pk(p, pk, epk);
    if (res != MAYO_OK) {
        printf("FAIL\n");
        res = -1;
        goto err;
    } else {
        printf("OK\n");
    }

    printf("mayo_sign -> ");
    res = mayo_sign(p, sig, &smlen, msg, msglen, sk);
    if (res != MAYO_OK) {
        printf("FAIL\n");
        res = -1;
        goto err;
    } else {
        printf("OK\n");
    }
    //MAYO_OPEN
    //The implementation performs Mayo.verify().
    //If the signature verification succeeded, the recovered message is stored in msg2
    //&msglen is pointer to the length of message
    //Keys provided is a compact public key.
    //The caller is responsible to allocate sufficient memory to hold m.
    printf("mayo_open (with correct signature) -> ");
    res = mayo_open(p, msg2, &msglen, sig, smlen, pk);
    if (res != MAYO_OK || memcmp(msg, msg2, msglen)) {
        printf("FAIL\n");
        res = -1;
        goto err;
    } else {
        res = MAYO_OK;
        printf("OK\n");
    }
    //MAYO_VERIFY
    //If the signature verification succeeded, returns 0, otherwise 1.
    //Key provided is a compact public key.
    printf("mayo_verify (with correct signature) -> ");
    res = mayo_verify(p, msg, msglen, sig, pk);
    if (res != MAYO_OK) {
        printf("FAIL\n");
        res = -1;
        goto err;
    } else {
        res = MAYO_OK;
        printf("OK\n");
    }

    printf("mayo_open (with altered signature) -> ");
    sig[0] = ~sig[0];//alter one bit to simulate corruption
    memset(msg2, 0, msglen);//reset the buffer in order to be used for new recovered message
    res = mayo_open(p, msg2, &msglen, sig, smlen, pk);
    if (res != MAYO_ERR || !memcmp(msg, msg2, msglen)) {
        printf("FAIL\n");
        res = -1;
        goto err;
    } else {
        res = MAYO_OK;
        printf("OK\n");
    }

    printf("mayo_verify (with altered signature) -> ");
    res = mayo_verify(p, msg, msglen, sig, pk);
    if (res == MAYO_OK) {
        printf("FAIL\n");
        res = -1;
        goto err;
    } else {
        res = MAYO_OK;
        printf("OK\n");
    }

err:
    free(pk);
    free(epk);
    //secure_free is likely a zeroing + free, to avoid leaking sensitive data
    mayo_secure_free(sk, PARAM_csk_bytes(p));
    mayo_secure_free(esk, sizeof(sk_t));
    free(sig);
    return res;
}

int main(void) {
#ifdef ENABLE_PARAMS_DYNAMIC
    const mayo_params_t* params[] = {&MAYO_1, &MAYO_2, &MAYO_3, &MAYO_5};
    int paramslen = sizeof(params) / sizeof(params[0]);
    for (int i = 0; i < paramslen; ++i) {
        if (example_mayo(params[i]) != MAYO_OK) {
            return -1;
        }
    }
#else
    return example_mayo(0);
#endif
}

