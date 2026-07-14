/* Differential-test CLI wrapper around the UNMODIFIED cJSON oracle.
 *
 * Contract (shared verbatim with the Lean port):
 *   stdin  : arbitrary bytes (the candidate JSON document)
 *   stdout : on success, cJSON_PrintUnformatted() of the parsed value, no trailing newline
 *   exit 0 : parse succeeded (and printing succeeded)
 *   exit 1 : parse failed
 *   exit 2 : parse succeeded but printing failed (allocation / internal)
 *   exit 3 : harness error (could not read stdin / out of memory)
 *
 * Entry point: cJSON_ParseWithLength(buf, len + 1) over a NUL-appended copy.
 * That is byte-for-byte the buffer cJSON_Parse() would build for any input
 * containing no embedded NUL, and is well-defined (rather than truncating) when
 * one is present. See SPEC.md S0.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "cJSON.h"

int main(void) {
    size_t cap = 1 << 16, len = 0;
    unsigned char *buf = (unsigned char *)malloc(cap);
    if (!buf) return 3;

    for (;;) {
        if (len == cap) {
            size_t ncap = cap * 2;
            unsigned char *nbuf = (unsigned char *)realloc(buf, ncap);
            if (!nbuf) { free(buf); return 3; }
            buf = nbuf; cap = ncap;
        }
        size_t got = fread(buf + len, 1, cap - len, stdin);
        len += got;
        if (got == 0) {
            if (ferror(stdin)) { free(buf); return 3; }
            break;
        }
    }

    /* append the NUL that cJSON_Parse() would have included in its length */
    if (len == cap) {
        unsigned char *nbuf = (unsigned char *)realloc(buf, cap + 1);
        if (!nbuf) { free(buf); return 3; }
        buf = nbuf; cap = cap + 1;
    }
    buf[len] = '\0';

    cJSON *item = cJSON_ParseWithLength((const char *)buf, len + 1);
    if (!item) { free(buf); return 1; }

    char *out = cJSON_PrintUnformatted(item);
    if (!out) { cJSON_Delete(item); free(buf); return 2; }

    fwrite(out, 1, strlen(out), stdout);
    fflush(stdout);

    free(out);
    cJSON_Delete(item);
    free(buf);
    return 0;
}
