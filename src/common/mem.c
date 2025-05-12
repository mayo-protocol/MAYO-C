// SPDX-License-Identifier: Apache-2.0

#include <string.h>
#include <stdlib.h>
#include <stdint.h>

void mayo_secure_free(void *mem, size_t size) {
    if (mem) {
        typedef void *(*memset_t)(void *, int, size_t);
        // function pointer definition, any function with the same signature can be set to memset_t
        static volatile memset_t memset_func = memset;
        // static restricts scope to the current file
        // volatile prevents compiler optimization
        // tells the compiler not to optimize away accesses to memset_func, since its value might change externally or has side effects.
        // "optimize away" means:
        // The compiler removes or skips code during optimization because it thinks the code has no effect on the program's outcome
        // usually done for sensitive data
        memset_func(mem, 0, size);
        free(mem);
    }
}
void mayo_secure_clear(void *mem, size_t size) {
    typedef void *(*memset_t)(void *, int, size_t);
    static volatile memset_t memset_func = memset;
    memset_func(mem, 0, size);
}
