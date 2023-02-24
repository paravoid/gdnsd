
#line 1 "./libgdnsd/vscf.rl"
/* Copyright © 2012 Brandon L Black <blblack@gmail.com>
 *
 * This file is part of gdnsd.
 *
 * vscf is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * vscf is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with vscf.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

#include <config.h>
#include <gdnsd/vscf.h>

#include <gdnsd/alloc.h>
#include <gdnsd/file.h>
#include <gdnsd/misc.h>
#include <gdnsd/mm3.h>

#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <inttypes.h>
#include <glob.h>

#define parse_error(_fmt, ...) do {\
    if (!scnr->err_emitted) {\
        scnr->err_emitted = true;\
        log_err("Parse error at %s line %u: " _fmt, scnr->desc, scnr->lcount, __VA_ARGS__);\
    }\
} while (0)

#define parse_error_noargs(_fmt) do {\
    if (!scnr->err_emitted) {\
        scnr->err_emitted = true;\
        log_err("Parse error at %s line %u: " _fmt, scnr->desc, scnr->lcount);\
    }\
} while (0)

/*************************************/
/*** Private data type definitions ***/
/*************************************/

typedef struct {
    vscf_data_t* parent;
    vscf_type_t  type;
    char*        rval;
    char*        val;
    unsigned     rlen;
    unsigned     len;
} vscf_simple_t;

typedef struct {
    vscf_data_t*  parent;
    vscf_type_t   type;
    unsigned      len;
    vscf_data_t** vals;
} vscf_array_t;

typedef struct _vscf_hentry_t vscf_hentry_t;
struct _vscf_hentry_t {
    unsigned       klen;
    char*          key;
    unsigned       index;
    bool           marked;
    vscf_data_t*   val;
    vscf_hentry_t* next;
};

typedef struct {
    vscf_data_t*    parent;
    vscf_type_t     type;
    unsigned        child_count;
    vscf_hentry_t** children;
    vscf_hentry_t** ordered;
} vscf_hash_t;

union vscf_data_t {
    struct {
        vscf_data_t*    parent;
        vscf_type_t     type;
    };
    vscf_simple_t   simple;
    vscf_array_t    array;
    vscf_hash_t     hash;
};

typedef struct {
    int           cs;
    unsigned      top;
    unsigned      cont_stack_top;
    unsigned      cont_stack_alloc;
    unsigned      cs_stack_alloc;
    unsigned      lcount;
    unsigned      cur_klen;
    vscf_data_t** cont_stack;
    int*          cs_stack;
    const char*   p;
    const char*   pe;
    const char*   eof;
    char*         cur_key;
    const char*   fn;
    const char*   desc;
    const char*   tstart;
    bool          err_emitted;
} vscf_scnr_t;

/*************************/
/*** Private functions ***/
/*************************/

F_NONNULL F_PURE
static unsigned key_hash(const char* k, unsigned klen, const unsigned hash_mask)
{
    return hash_mm3_u32((const uint8_t*)k, klen) & hash_mask;
}

F_WUNUSED
static vscf_hash_t* hash_new(void)
{
    vscf_hash_t* h = xcalloc(sizeof(*h));
    h->type = VSCF_HASH_T;
    return h;
}

F_NONNULL
static void hash_grow(vscf_hash_t* h)
{
    const unsigned old_hash_mask = count2mask(h->child_count);
    const unsigned new_hash_mask = (old_hash_mask << 1) | 1;
    vscf_hentry_t** new_table = xcalloc_n(new_hash_mask + 1, sizeof(*new_table));
    for (unsigned i = 0; i <= old_hash_mask; i++) {
        vscf_hentry_t* entry = h->children[i];
        while (entry) {
            const unsigned child_hash = key_hash(entry->key, entry->klen, new_hash_mask);
            vscf_hentry_t* slot = new_table[child_hash];
            vscf_hentry_t* next_entry = entry->next;
            entry->next = NULL;

            if (slot) {
                while (slot->next)
                    slot = slot->next;
                slot->next = entry;
            } else {
                new_table[child_hash] = entry;
            }

            entry = next_entry;
        }
    }

    free(h->children);

    h->children = new_table;
    h->ordered = xrealloc_n(h->ordered, new_hash_mask + 1, sizeof(*h->ordered));
}

F_NONNULL F_WUNUSED
static bool hash_add_val(const char* key, const unsigned klen, vscf_hash_t* h, vscf_data_t* v)
{
    v->parent = (vscf_data_t*)h;

    if (!h->children) {
        h->children = xcalloc_n(2, sizeof(*h->children));
        h->ordered = xmalloc_n(2, sizeof(*h->ordered));
    }

    const unsigned child_mask = count2mask(h->child_count);
    const unsigned child_hash = key_hash(key, klen, child_mask);

    vscf_hentry_t** store_at = &(h->children[child_hash]);
    while (*store_at) {
        if ((klen == (*store_at)->klen)
                && !memcmp(key, (*store_at)->key, klen)) {
            return false;
        }
        store_at = &((*store_at)->next);
    }

    vscf_hentry_t* new_hentry = *store_at = xcalloc(sizeof(*new_hentry));
    new_hentry->klen = klen;
    new_hentry->key = xmalloc(klen + 1);
    memcpy(new_hentry->key, key, klen + 1);
    new_hentry->index = h->child_count;
    new_hentry->val = v;

    if (h->child_count == child_mask)
        hash_grow(h);

    h->ordered[h->child_count++] = new_hentry;

    return true;
}

F_NONNULL F_WUNUSED
static bool scnr_hash_add_val(vscf_scnr_t* scnr, vscf_hash_t* h, vscf_data_t* v)
{
    gdnsd_assert(scnr->cur_key);

    bool rv = hash_add_val(scnr->cur_key, scnr->cur_klen, h, v);
    if (rv) {
        free(scnr->cur_key);
        scnr->cur_key = NULL;
        scnr->cur_klen = 0;
    } else {
        parse_error("Duplicate hash key '%s'", scnr->cur_key);
    }
    return rv;
}

F_WUNUSED
static vscf_array_t* array_new(void)
{
    vscf_array_t* a = xcalloc(sizeof(*a));
    a->type   = VSCF_ARRAY_T;
    return a;
}

F_NONNULL
static void array_add_val(vscf_array_t* a, vscf_data_t* v)
{
    v->parent = (vscf_data_t*)a;
    unsigned idx = a->len++;
    a->vals = xrealloc_n(a->vals, a->len, sizeof(*a->vals));
    a->vals[idx] = v;
}

/*
 * Takes a pointer to a constant simple key/value with len
 * Allocates necessary storage and stores the unescaped version
 *  in *out, returning the new length, which will be <= the original length
 * Note also that the returned storage is one byte longer than indicated and
 *  terminated with a NUL in that extra byte.  It serves two purposes:
 * (1) Ensuring that the data pointer of a zero-length string/key is not NULL
 *   (it points to one byte of NUL)
 * (2) Allowing the treatment of vscf strings as NUL-terminated in cases where
 *   embedded NULs are irrelevant (such as our own numeric conversions, and
 *   probably many user-code cases too).
 */
F_NONNULLX(2, 3, 4) F_WUNUSED
static bool unescape_string(vscf_scnr_t* scnr, char** outp, unsigned* outlenp, const char* in, unsigned len)
{
    char* out = xmalloc(len + 1);
    unsigned newlen = len;
    if (len) {
        newlen = dns_unescape(out, in, len);
        gdnsd_assert(newlen <= len);
        if (!newlen) {
            if (scnr)
                parse_error_noargs("Cannot unescape string by DNS escaping rules");
            free(out);
            return false;
        }
        if (newlen != len)
            out = xrealloc(out, newlen + 1); // downsize
    }
    out[newlen] = 0;
    *outp = out;
    *outlenp = newlen;
    return true;
}

F_NONNULLX(2) F_WUNUSED
static vscf_simple_t* simple_new(vscf_scnr_t* scnr, const char* rval, const unsigned rlen)
{
    vscf_simple_t* s = xcalloc(sizeof(*s));
    char* storage = xmalloc(rlen + 1U);
    memcpy(storage, rval, rlen);
    storage[rlen] = '\0';
    s->type   = VSCF_SIMPLE_T;
    s->rlen   = rlen;
    s->rval   = storage;
    if (!unescape_string(scnr, &s->val, &s->len, storage, rlen)) {
        free(storage);
        free(s);
        return NULL;
    }
    return s;
}

F_NONNULL F_WUNUSED F_RETNN
static vscf_data_t* val_clone(const vscf_data_t* d, const bool ignore_marked);

F_NONNULL F_RETNN
static vscf_hash_t* hash_clone(const vscf_hash_t* h, const bool ignore_marked)
{
    vscf_hash_t* nh = hash_new();
    for (unsigned i = 0; i < h->child_count; i++) {
        const vscf_hentry_t* hentry = h->ordered[i];
        if (!ignore_marked || !hentry->marked) {
            vscf_data_t* new_child = val_clone(hentry->val, ignore_marked);
            const bool add_ok V_UNUSED
                = hash_add_val(hentry->key, hentry->klen, nh, new_child);
            gdnsd_assert(add_ok);
        }
    }
    return nh;
}

F_NONNULL F_WUNUSED F_RETNN
static vscf_array_t* array_clone(const vscf_array_t* a, const bool ignore_marked)
{
    vscf_array_t* na = array_new();
    for (unsigned i = 0; i < a->len; i++) {
        array_add_val(na, val_clone(a->vals[i], ignore_marked));
    }
    return na;
}

F_NONNULL F_WUNUSED F_RETNN
static vscf_simple_t* simple_clone(const vscf_simple_t* s)
{
    vscf_simple_t* new_s = xcalloc(sizeof(*new_s));
    new_s->type = VSCF_SIMPLE_T;
    new_s->rval = xmalloc(s->rlen + 1U);
    new_s->val = xmalloc(s->len + 1U);
    new_s->rlen = s->rlen;
    new_s->len = s->len;
    memcpy(new_s->rval, s->rval, s->rlen + 1U);
    memcpy(new_s->val, s->val, s->len + 1U);
    return new_s;
}

F_WUNUSED F_RETNN
static vscf_data_t* val_clone(const vscf_data_t* d, const bool ignore_marked)
{
    vscf_data_t* rv = NULL;
    switch (d->type) {
    case VSCF_HASH_T:
        rv = (vscf_data_t*)hash_clone(&d->hash, ignore_marked);
        break;
    case VSCF_ARRAY_T:
        rv = (vscf_data_t*)array_clone(&d->array, ignore_marked);
        break;
    case VSCF_SIMPLE_T:
        rv = (vscf_data_t*)simple_clone(&d->simple);
        break;
    default:
        gdnsd_assert(0);
    }
    return rv;
}

F_NONNULL F_WUNUSED
static bool set_key(vscf_scnr_t* scnr, const char* end)
{
    gdnsd_assert(scnr->tstart);
    if (!unescape_string(scnr, &scnr->cur_key, &scnr->cur_klen, scnr->tstart, end - scnr->tstart))
        return false;
    scnr->tstart = NULL;
    return true;
}

F_NONNULL F_WUNUSED
static bool add_to_cur_container(vscf_scnr_t* scnr, vscf_data_t* v)
{
    vscf_data_t* cont = scnr->cont_stack[scnr->cont_stack_top];
    gdnsd_assert(cont);

    if (cont->type == VSCF_HASH_T) {
        vscf_hash_t* h = &cont->hash;
        return scnr_hash_add_val(scnr, h, v);
    } else {
        gdnsd_assert(cont->type == VSCF_ARRAY_T);
        vscf_array_t* a = &cont->array;
        array_add_val(a, v);
        return true;
    }
}

F_NONNULL F_WUNUSED
static bool scnr_set_simple(vscf_scnr_t* scnr, const char* end)
{
    gdnsd_assert(scnr->tstart);
    const unsigned rlen = end - scnr->tstart;
    vscf_simple_t* s = simple_new(scnr, scnr->tstart, rlen);
    if (!s)
        return false;
    scnr->tstart = NULL;
    return add_to_cur_container(scnr, (vscf_data_t*)s);
}

static void val_destroy(vscf_data_t* d);

F_NONNULL F_WUNUSED
static bool vscf_include_file(vscf_scnr_t* scnr, const char* fn)
{
    vscf_data_t* inc_data = vscf_scan_filename(fn);

    if (!inc_data) {
        parse_error("Failed to load included file %s", fn);
        return false;
    }

    vscf_data_t* cont = scnr->cont_stack[scnr->cont_stack_top];
    if (vscf_is_hash(cont) && !scnr->cur_key) { // this is hash-merge context
        if (vscf_is_array(inc_data)) {
            parse_error("Included file '%s' cannot be an array in this context", fn);
            return false;
        }
        gdnsd_assert(vscf_is_hash(inc_data));

        // destructively merge include stuff into parent, stealing values
        for (unsigned i = 0; i < inc_data->hash.child_count; i++) {
            vscf_hentry_t* inc_he = inc_data->hash.ordered[i];
            if (!hash_add_val(inc_he->key, inc_he->klen, (vscf_hash_t*)cont, inc_he->val)) {
                parse_error("Include file '%s' has duplicate key '%s' when merging into parent hash", fn, inc_he->key);
                val_destroy(inc_data);
                return false;
            }
            inc_he->val = NULL;
        }
        val_destroy(inc_data);
    } else { // value context
        return add_to_cur_container(scnr, inc_data);
    }

    return true;
}

F_NONNULL F_WUNUSED
static bool vscf_include_glob(vscf_scnr_t* scnr, const char* inc_glob, const int extraflags)
{
    int globflags = GLOB_ERR | extraflags;
    glob_t globbuf;
    const int globrv = glob(inc_glob, globflags, NULL, &globbuf);
    if (globrv && globrv != GLOB_NOMATCH) {
        parse_error("Include path '%s' failed glob(): %i", inc_glob, globrv);
        globfree(&globbuf);
        return false;
    }

    if (globrv != GLOB_NOMATCH) {
        vscf_data_t* cont = scnr->cont_stack[scnr->cont_stack_top];
        if (!vscf_is_hash(cont) || scnr->cur_key) { // value-context
            if (globbuf.gl_pathc > 1U) {
                parse_error("Including '%s': cannot include multiple files in value context", inc_glob);
                globfree(&globbuf);
                return false;
            }
        }

        for (size_t i = 0; i < globbuf.gl_pathc; i++) {
            if (!vscf_include_file(scnr, globbuf.gl_pathv[i])) {
                globfree(&globbuf);
                return false;
            }
        }
    }

    globfree(&globbuf);
    return true;
}

F_NONNULL F_WUNUSED
static bool vscf_include_glob_or_dir(vscf_scnr_t* scnr, const char* glob_or_dir)
{
    struct stat st;
    if (!stat(glob_or_dir, &st) && S_ISDIR(st.st_mode)) {
        // we handle the directory case by transforming it into a
        // glob, but allowing GLOB_NOMATCH
        const size_t inc_dir_len = strlen(glob_or_dir);
        char* inc_dir_glob = xmalloc(inc_dir_len + 3);
        memcpy(inc_dir_glob, glob_or_dir, inc_dir_len);
        size_t pos = inc_dir_len;
        if (inc_dir_len > 0 && inc_dir_glob[inc_dir_len - 1] != '/')
            inc_dir_glob[pos++] = '/';
        inc_dir_glob[pos++] = '*';
        inc_dir_glob[pos] = '\0';
        bool rv = vscf_include_glob(scnr, inc_dir_glob, 0);
        free(inc_dir_glob);
        return rv;
    }

    // handle as a user-specified glob
    return vscf_include_glob(scnr, glob_or_dir, GLOB_NOCHECK);
}

F_NONNULL F_WUNUSED
static bool scnr_proc_include(vscf_scnr_t* scnr, const char* end)
{
    gdnsd_assert(scnr->tstart);

    // raw scanner storage isn't NUL-terminated, so we copy to input_fn to terminate
    const unsigned infn_len = end - scnr->tstart;
    char* input_fn = xmalloc(infn_len + 1);
    memcpy(input_fn, scnr->tstart, infn_len);
    input_fn[infn_len] = '\0';
    scnr->tstart = NULL;

    log_debug("found an include statement for '%s' within '%s'!", input_fn, scnr->desc);

    // absolute path, easy
    if (input_fn[0] == '/') {
        bool rv = vscf_include_glob_or_dir(scnr, input_fn);
        free(input_fn);
        return rv;
    }

    // relative path, make relative to including file if possible
    if (!scnr->fn) {
        parse_error("Relative include path '%s' not allowed here because scanner does not know the filesystem path of including data '%s'", input_fn, scnr->desc);
        free(input_fn);
        return false;
    }

    const unsigned cur_fn_len = strlen(scnr->fn);
    char* abs_path = xmalloc(cur_fn_len + infn_len + 2); // slightly oversized, who cares

    // copy outer filename to temp storage
    memcpy(abs_path, scnr->fn, cur_fn_len);
    abs_path[cur_fn_len] = '\0';

    // locate final slash to append input_fn after, or use start of string
    //   This will break on literal slashes in filenames, but I think
    //   I've made this assumption before and I could kinda care less about
    //   people who do dumb things like that.
    char* final_slash = strrchr(abs_path, '/');
    char* copy_to = final_slash ? final_slash + 1 : abs_path;
    memcpy(copy_to, input_fn, infn_len);
    copy_to[infn_len] = '\0';
    bool rv = vscf_include_glob_or_dir(scnr, abs_path);
    free(abs_path);
    free(input_fn);
    return rv;
}

F_NONNULL F_WUNUSED
static bool cont_stack_push(vscf_scnr_t* scnr, vscf_data_t* c)
{
    if (!add_to_cur_container(scnr, c))
        return false;

    if (++scnr->cont_stack_top == scnr->cont_stack_alloc)
        scnr->cont_stack = xrealloc_n(scnr->cont_stack, ++scnr->cont_stack_alloc, sizeof(*scnr->cont_stack));
    scnr->cont_stack[scnr->cont_stack_top] = c;

    return true;
}

F_NONNULL
static void cont_stack_pop(vscf_scnr_t* scnr)
{
    gdnsd_assert(scnr->cont_stack_top > 0);
    --scnr->cont_stack_top;
}

/*** Destructors ***/

F_NONNULL
static void simple_destroy(vscf_simple_t* s)
{
    free(s->rval);
    if (s->val)
        free(s->val);
    free(s);
}

F_NONNULL
static void array_destroy(vscf_array_t* a)
{
    for (unsigned i = 0; i < a->len; i++)
        val_destroy(a->vals[i]);
    free(a->vals);
    free(a);
}

F_NONNULL
static void hash_destroy(vscf_hash_t* h)
{
    for (unsigned i = 0; i < h->child_count; i++) {
        vscf_hentry_t* hentry = h->ordered[i];
        val_destroy(hentry->val);
        free(hentry->key);
        free(hentry);
    }
    free(h->children);
    free(h->ordered);
    free(h);
}

static void val_destroy(vscf_data_t* d)
{
    if (d) {
        switch (d->type) {
        case VSCF_HASH_T:
            hash_destroy(&d->hash);
            break;
        case VSCF_ARRAY_T:
            array_destroy(&d->array);
            break;
        case VSCF_SIMPLE_T:
            simple_destroy(&d->simple);
            break;
        default:
            gdnsd_assert(0);
        }
    }
}

/************************************/
/*** The Ragel machine definition ***/
/************************************/

// *INDENT-OFF*
// start-sonar-exclude

#line 620 "libgdnsd/vscf.c"
static const char _vscf_actions[] = {
	0, 1, 0, 1, 1, 1, 2, 1, 
	3, 1, 4, 1, 5, 1, 6, 1, 
	7, 1, 8, 1, 9, 1, 10, 1, 
	11, 1, 12, 2, 3, 0, 2, 3, 
	6, 2, 3, 7, 2, 3, 8, 2, 
	3, 9, 2, 4, 0, 2, 4, 6, 
	2, 4, 7, 2, 4, 8, 2, 4, 
	9, 2, 5, 0, 2, 5, 1, 2, 
	5, 3, 2, 5, 6, 2, 5, 7, 
	2, 5, 8, 2, 5, 9, 2, 5, 
	10, 2, 5, 11, 3, 5, 3, 0, 
	3, 5, 3, 6, 3, 5, 3, 7, 
	3, 5, 3, 8, 3, 5, 3, 9
	
};

static const short _vscf_key_offsets[] = {
	0, 0, 13, 19, 25, 26, 41, 44, 
	47, 53, 58, 60, 62, 63, 64, 65, 
	66, 67, 68, 69, 70, 71, 85, 98, 
	104, 110, 111, 116, 129, 131, 133, 147, 
	150, 153, 159, 164, 166, 168, 169, 170, 
	175, 188, 190, 192, 197, 199, 201, 215, 
	229, 232, 235, 240, 242, 244, 245, 246, 
	260, 273, 287, 301, 304, 307, 321, 322, 
	323, 324, 325, 326, 327, 328, 329, 330, 
	344, 357, 363, 369, 370, 375, 388, 390, 
	392, 406, 409, 412, 418, 423, 425, 427, 
	428, 433, 446, 447, 449, 451, 456, 458, 
	460, 474, 475, 489, 502, 516, 530, 533, 
	536, 550, 551, 552, 553, 554, 555, 556, 
	557, 558, 559, 573, 586, 592, 598, 599, 
	604, 617, 619, 621, 635, 638, 641, 647, 
	652, 654, 656, 657, 662, 675, 677, 679, 
	684, 686, 688, 702, 703, 717, 730, 736, 
	742, 743, 758, 771, 785, 799, 802, 805, 
	811, 816, 818, 820, 821, 822, 823, 824, 
	825, 826, 827, 828, 829, 843, 856, 862, 
	868, 869, 874, 887, 889, 891, 905, 908, 
	911, 917, 922, 924, 926, 927, 932, 945, 
	947, 949, 954, 967, 969, 971, 985, 999, 
	1002, 1005, 1019, 1024, 1026, 1028, 1029, 1043, 
	1044, 1058, 1071, 1085, 1099, 1113, 1127, 1140, 
	1154, 1168, 1173, 1178, 1178
};

static const char _vscf_trans_keys[] = {
	9, 10, 32, 34, 35, 44, 59, 61, 
	92, 123, 125, 91, 93, 9, 10, 32, 
	35, 59, 61, 9, 10, 32, 35, 59, 
	61, 10, 9, 10, 32, 34, 35, 36, 
	44, 59, 61, 62, 91, 92, 93, 123, 
	125, 10, 34, 92, 10, 34, 92, 9, 
	10, 32, 35, 59, 61, 10, 48, 49, 
	50, 57, 48, 57, 48, 57, 10, 105, 
	110, 99, 108, 117, 100, 101, 123, 9, 
	10, 32, 34, 35, 36, 44, 59, 61, 
	92, 123, 125, 91, 93, 9, 10, 32, 
	34, 35, 44, 59, 61, 92, 123, 125, 
	91, 93, 9, 10, 32, 35, 59, 125, 
	9, 10, 32, 35, 59, 125, 10, 10, 
	48, 49, 50, 57, 9, 10, 32, 34, 
	35, 44, 59, 61, 92, 123, 125, 91, 
	93, 48, 57, 48, 57, 9, 10, 32, 
	34, 35, 36, 44, 59, 61, 92, 123, 
	125, 91, 93, 10, 34, 92, 10, 34, 
	92, 9, 10, 32, 35, 59, 125, 10, 
	48, 49, 50, 57, 48, 57, 48, 57, 
	10, 10, 10, 48, 49, 50, 57, 9, 
	10, 32, 34, 35, 44, 59, 61, 92, 
	123, 125, 91, 93, 48, 57, 48, 57, 
	10, 48, 49, 50, 57, 48, 57, 48, 
	57, 9, 10, 32, 34, 35, 36, 44, 
	59, 61, 91, 92, 93, 123, 125, 9, 
	10, 32, 34, 35, 36, 44, 59, 61, 
	91, 92, 93, 123, 125, 10, 34, 92, 
	10, 34, 92, 10, 48, 49, 50, 57, 
	48, 57, 48, 57, 10, 10, 9, 10, 
	32, 34, 35, 36, 44, 59, 61, 91, 
	92, 93, 123, 125, 9, 10, 32, 34, 
	35, 44, 59, 61, 91, 92, 93, 123, 
	125, 9, 10, 32, 34, 35, 36, 44, 
	59, 61, 91, 92, 93, 123, 125, 9, 
	10, 32, 34, 35, 36, 44, 59, 61, 
	91, 92, 93, 123, 125, 10, 34, 92, 
	10, 34, 92, 9, 10, 32, 34, 35, 
	36, 44, 59, 61, 91, 92, 93, 123, 
	125, 10, 105, 110, 99, 108, 117, 100, 
	101, 123, 9, 10, 32, 34, 35, 36, 
	44, 59, 61, 92, 123, 125, 91, 93, 
	9, 10, 32, 34, 35, 44, 59, 61, 
	92, 123, 125, 91, 93, 9, 10, 32, 
	35, 59, 125, 9, 10, 32, 35, 59, 
	125, 10, 10, 48, 49, 50, 57, 9, 
	10, 32, 34, 35, 44, 59, 61, 92, 
	123, 125, 91, 93, 48, 57, 48, 57, 
	9, 10, 32, 34, 35, 36, 44, 59, 
	61, 92, 123, 125, 91, 93, 10, 34, 
	92, 10, 34, 92, 9, 10, 32, 35, 
	59, 125, 10, 48, 49, 50, 57, 48, 
	57, 48, 57, 10, 10, 48, 49, 50, 
	57, 9, 10, 32, 34, 35, 44, 59, 
	61, 91, 92, 93, 123, 125, 10, 48, 
	57, 48, 57, 10, 48, 49, 50, 57, 
	48, 57, 48, 57, 9, 10, 32, 34, 
	35, 36, 44, 59, 61, 91, 92, 93, 
	123, 125, 10, 9, 10, 32, 34, 35, 
	36, 44, 59, 61, 91, 92, 93, 123, 
	125, 9, 10, 32, 34, 35, 44, 59, 
	61, 91, 92, 93, 123, 125, 9, 10, 
	32, 34, 35, 36, 44, 59, 61, 91, 
	92, 93, 123, 125, 9, 10, 32, 34, 
	35, 36, 44, 59, 61, 91, 92, 93, 
	123, 125, 10, 34, 92, 10, 34, 92, 
	9, 10, 32, 34, 35, 36, 44, 59, 
	61, 91, 92, 93, 123, 125, 10, 105, 
	110, 99, 108, 117, 100, 101, 123, 9, 
	10, 32, 34, 35, 36, 44, 59, 61, 
	92, 123, 125, 91, 93, 9, 10, 32, 
	34, 35, 44, 59, 61, 92, 123, 125, 
	91, 93, 9, 10, 32, 35, 59, 125, 
	9, 10, 32, 35, 59, 125, 10, 10, 
	48, 49, 50, 57, 9, 10, 32, 34, 
	35, 44, 59, 61, 92, 123, 125, 91, 
	93, 48, 57, 48, 57, 9, 10, 32, 
	34, 35, 36, 44, 59, 61, 92, 123, 
	125, 91, 93, 10, 34, 92, 10, 34, 
	92, 9, 10, 32, 35, 59, 125, 10, 
	48, 49, 50, 57, 48, 57, 48, 57, 
	10, 10, 48, 49, 50, 57, 9, 10, 
	32, 34, 35, 44, 59, 61, 91, 92, 
	93, 123, 125, 48, 57, 48, 57, 10, 
	48, 49, 50, 57, 48, 57, 48, 57, 
	9, 10, 32, 34, 35, 36, 44, 59, 
	61, 91, 92, 93, 123, 125, 10, 9, 
	10, 32, 34, 35, 36, 44, 59, 61, 
	92, 123, 125, 91, 93, 9, 10, 32, 
	34, 35, 44, 59, 61, 92, 123, 125, 
	91, 93, 9, 10, 32, 35, 59, 61, 
	9, 10, 32, 35, 59, 61, 10, 9, 
	10, 32, 34, 35, 36, 44, 59, 61, 
	62, 91, 92, 93, 123, 125, 9, 10, 
	32, 34, 35, 44, 59, 61, 92, 123, 
	125, 91, 93, 9, 10, 32, 34, 35, 
	36, 44, 59, 61, 92, 123, 125, 91, 
	93, 9, 10, 32, 34, 35, 36, 44, 
	59, 61, 92, 123, 125, 91, 93, 10, 
	34, 92, 10, 34, 92, 9, 10, 32, 
	35, 59, 61, 10, 48, 49, 50, 57, 
	48, 57, 48, 57, 10, 105, 110, 99, 
	108, 117, 100, 101, 123, 9, 10, 32, 
	34, 35, 36, 44, 59, 61, 92, 123, 
	125, 91, 93, 9, 10, 32, 34, 35, 
	44, 59, 61, 92, 123, 125, 91, 93, 
	9, 10, 32, 35, 59, 125, 9, 10, 
	32, 35, 59, 125, 10, 10, 48, 49, 
	50, 57, 9, 10, 32, 34, 35, 44, 
	59, 61, 92, 123, 125, 91, 93, 48, 
	57, 48, 57, 9, 10, 32, 34, 35, 
	36, 44, 59, 61, 92, 123, 125, 91, 
	93, 10, 34, 92, 10, 34, 92, 9, 
	10, 32, 35, 59, 125, 10, 48, 49, 
	50, 57, 48, 57, 48, 57, 10, 10, 
	48, 49, 50, 57, 9, 10, 32, 34, 
	35, 44, 59, 61, 92, 123, 125, 91, 
	93, 48, 57, 48, 57, 10, 48, 49, 
	50, 57, 9, 10, 32, 34, 35, 44, 
	59, 61, 92, 123, 125, 91, 93, 48, 
	57, 48, 57, 9, 10, 32, 34, 35, 
	36, 44, 59, 61, 91, 92, 93, 123, 
	125, 9, 10, 32, 34, 35, 36, 44, 
	59, 61, 91, 92, 93, 123, 125, 10, 
	34, 92, 10, 34, 92, 9, 10, 32, 
	34, 35, 36, 44, 59, 61, 92, 123, 
	125, 91, 93, 10, 48, 49, 50, 57, 
	48, 57, 48, 57, 10, 9, 10, 32, 
	34, 35, 36, 44, 59, 61, 92, 123, 
	125, 91, 93, 10, 9, 10, 32, 34, 
	35, 36, 44, 59, 61, 91, 92, 93, 
	123, 125, 9, 10, 32, 34, 35, 44, 
	59, 61, 92, 123, 125, 91, 93, 9, 
	10, 32, 34, 35, 36, 44, 59, 61, 
	92, 123, 125, 91, 93, 9, 10, 32, 
	34, 35, 36, 44, 59, 61, 92, 123, 
	125, 91, 93, 9, 10, 32, 34, 35, 
	36, 44, 59, 61, 92, 123, 125, 91, 
	93, 9, 10, 32, 34, 35, 36, 44, 
	59, 61, 92, 123, 125, 91, 93, 9, 
	10, 32, 34, 35, 44, 59, 61, 92, 
	123, 125, 91, 93, 9, 10, 32, 34, 
	35, 36, 44, 59, 61, 92, 123, 125, 
	91, 93, 9, 10, 32, 34, 35, 36, 
	44, 59, 61, 91, 92, 93, 123, 125, 
	9, 10, 32, 35, 59, 9, 10, 32, 
	35, 59, 0
};

static const char _vscf_single_lengths[] = {
	0, 11, 6, 6, 1, 15, 3, 3, 
	6, 1, 0, 0, 1, 1, 1, 1, 
	1, 1, 1, 1, 1, 12, 11, 6, 
	6, 1, 1, 11, 0, 0, 12, 3, 
	3, 6, 1, 0, 0, 1, 1, 1, 
	11, 0, 0, 1, 0, 0, 14, 14, 
	3, 3, 1, 0, 0, 1, 1, 14, 
	13, 14, 14, 3, 3, 14, 1, 1, 
	1, 1, 1, 1, 1, 1, 1, 12, 
	11, 6, 6, 1, 1, 11, 0, 0, 
	12, 3, 3, 6, 1, 0, 0, 1, 
	1, 13, 1, 0, 0, 1, 0, 0, 
	14, 1, 14, 13, 14, 14, 3, 3, 
	14, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 12, 11, 6, 6, 1, 1, 
	11, 0, 0, 12, 3, 3, 6, 1, 
	0, 0, 1, 1, 13, 0, 0, 1, 
	0, 0, 14, 1, 12, 11, 6, 6, 
	1, 15, 11, 12, 12, 3, 3, 6, 
	1, 0, 0, 1, 1, 1, 1, 1, 
	1, 1, 1, 1, 12, 11, 6, 6, 
	1, 1, 11, 0, 0, 12, 3, 3, 
	6, 1, 0, 0, 1, 1, 11, 0, 
	0, 1, 11, 0, 0, 14, 14, 3, 
	3, 12, 1, 0, 0, 1, 12, 1, 
	14, 11, 12, 12, 12, 12, 11, 12, 
	14, 5, 5, 0, 0
};

static const char _vscf_range_lengths[] = {
	0, 1, 0, 0, 0, 0, 0, 0, 
	0, 2, 1, 1, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 1, 1, 0, 
	0, 0, 2, 1, 1, 1, 1, 0, 
	0, 0, 2, 1, 1, 0, 0, 2, 
	1, 1, 1, 2, 1, 1, 0, 0, 
	0, 0, 2, 1, 1, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 1, 
	1, 0, 0, 0, 2, 1, 1, 1, 
	1, 0, 0, 0, 2, 1, 1, 0, 
	2, 0, 0, 1, 1, 2, 1, 1, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 1, 1, 0, 0, 0, 2, 
	1, 1, 1, 1, 0, 0, 0, 2, 
	1, 1, 0, 2, 0, 1, 1, 2, 
	1, 1, 0, 0, 1, 1, 0, 0, 
	0, 0, 1, 1, 1, 0, 0, 0, 
	2, 1, 1, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 1, 1, 0, 0, 
	0, 2, 1, 1, 1, 1, 0, 0, 
	0, 2, 1, 1, 0, 2, 1, 1, 
	1, 2, 1, 1, 1, 0, 0, 0, 
	0, 1, 2, 1, 1, 0, 1, 0, 
	0, 1, 1, 1, 1, 1, 1, 1, 
	0, 0, 0, 0, 0
};

static const short _vscf_index_offsets[] = {
	0, 0, 13, 20, 27, 29, 45, 49, 
	53, 60, 64, 66, 68, 70, 72, 74, 
	76, 78, 80, 82, 84, 86, 100, 113, 
	120, 127, 129, 133, 146, 148, 150, 164, 
	168, 172, 179, 183, 185, 187, 189, 191, 
	195, 208, 210, 212, 216, 218, 220, 235, 
	250, 254, 258, 262, 264, 266, 268, 270, 
	285, 299, 314, 329, 333, 337, 352, 354, 
	356, 358, 360, 362, 364, 366, 368, 370, 
	384, 397, 404, 411, 413, 417, 430, 432, 
	434, 448, 452, 456, 463, 467, 469, 471, 
	473, 477, 491, 493, 495, 497, 501, 503, 
	505, 520, 522, 537, 551, 566, 581, 585, 
	589, 604, 606, 608, 610, 612, 614, 616, 
	618, 620, 622, 636, 649, 656, 663, 665, 
	669, 682, 684, 686, 700, 704, 708, 715, 
	719, 721, 723, 725, 729, 743, 745, 747, 
	751, 753, 755, 770, 772, 786, 799, 806, 
	813, 815, 831, 844, 858, 872, 876, 880, 
	887, 891, 893, 895, 897, 899, 901, 903, 
	905, 907, 909, 911, 913, 927, 940, 947, 
	954, 956, 960, 973, 975, 977, 991, 995, 
	999, 1006, 1010, 1012, 1014, 1016, 1020, 1033, 
	1035, 1037, 1041, 1054, 1056, 1058, 1073, 1088, 
	1092, 1096, 1110, 1114, 1116, 1118, 1120, 1134, 
	1136, 1151, 1164, 1178, 1192, 1206, 1220, 1233, 
	1247, 1262, 1268, 1274, 1275
};

static const unsigned char _vscf_trans_targs[] = {
	2, 3, 2, 0, 4, 0, 4, 5, 
	39, 0, 0, 0, 1, 2, 3, 2, 
	4, 4, 5, 0, 2, 3, 2, 4, 
	4, 5, 0, 3, 4, 46, 47, 46, 
	48, 53, 13, 0, 53, 0, 46, 202, 
	43, 0, 202, 0, 201, 7, 8, 9, 
	6, 7, 8, 9, 6, 2, 3, 2, 
	4, 4, 5, 0, 7, 10, 0, 6, 
	11, 0, 6, 0, 203, 12, 14, 0, 
	15, 0, 16, 0, 17, 0, 18, 0, 
	19, 0, 20, 0, 21, 0, 21, 30, 
	21, 31, 37, 0, 0, 37, 0, 26, 
	0, 0, 0, 22, 23, 24, 23, 0, 
	25, 0, 25, 0, 26, 0, 202, 0, 
	22, 23, 24, 23, 25, 25, 202, 0, 
	23, 24, 23, 25, 25, 202, 0, 24, 
	25, 27, 28, 0, 22, 23, 24, 23, 
	0, 25, 0, 25, 0, 26, 0, 202, 
	0, 22, 29, 0, 22, 0, 21, 30, 
	21, 31, 37, 0, 0, 37, 0, 26, 
	0, 0, 0, 22, 32, 33, 34, 31, 
	32, 33, 34, 31, 23, 24, 23, 25, 
	25, 202, 0, 32, 35, 0, 31, 36, 
	0, 31, 0, 30, 37, 205, 38, 40, 
	41, 0, 1, 2, 3, 2, 0, 4, 
	0, 4, 5, 39, 0, 0, 0, 1, 
	42, 0, 1, 0, 206, 44, 0, 201, 
	45, 0, 201, 0, 46, 47, 46, 48, 
	53, 13, 0, 53, 0, 202, 43, 0, 
	202, 0, 201, 46, 47, 46, 48, 53, 
	13, 0, 53, 0, 202, 43, 0, 202, 
	0, 201, 49, 207, 50, 48, 49, 207, 
	50, 48, 49, 51, 0, 48, 52, 0, 
	48, 0, 47, 53, 208, 54, 55, 96, 
	55, 59, 97, 63, 0, 97, 0, 57, 
	88, 209, 57, 0, 56, 57, 58, 57, 
	59, 62, 55, 62, 0, 57, 88, 209, 
	57, 0, 56, 57, 58, 57, 59, 62, 
	63, 55, 62, 0, 57, 88, 209, 57, 
	0, 56, 57, 58, 57, 59, 62, 63, 
	55, 62, 0, 57, 88, 209, 57, 0, 
	56, 60, 61, 93, 59, 60, 61, 93, 
	59, 57, 58, 57, 59, 62, 63, 55, 
	62, 0, 57, 88, 209, 57, 0, 56, 
	58, 62, 64, 0, 65, 0, 66, 0, 
	67, 0, 68, 0, 69, 0, 70, 0, 
	71, 0, 71, 80, 71, 81, 87, 0, 
	0, 87, 0, 76, 0, 0, 0, 72, 
	73, 74, 73, 0, 75, 0, 75, 0, 
	76, 0, 57, 0, 72, 73, 74, 73, 
	75, 75, 57, 0, 73, 74, 73, 75, 
	75, 57, 0, 74, 75, 77, 78, 0, 
	72, 73, 74, 73, 0, 75, 0, 75, 
	0, 76, 0, 57, 0, 72, 79, 0, 
	72, 0, 71, 80, 71, 81, 87, 0, 
	0, 87, 0, 76, 0, 0, 0, 72, 
	82, 83, 84, 81, 82, 83, 84, 81, 
	73, 74, 73, 75, 75, 57, 0, 82, 
	85, 0, 81, 86, 0, 81, 0, 80, 
	87, 89, 91, 0, 56, 57, 58, 57, 
	59, 62, 55, 62, 0, 57, 88, 209, 
	57, 0, 56, 210, 90, 92, 0, 56, 
	0, 60, 94, 0, 59, 95, 0, 59, 
	0, 55, 96, 55, 59, 97, 63, 0, 
	97, 0, 57, 88, 209, 57, 0, 56, 
	96, 97, 98, 138, 98, 102, 139, 106, 
	0, 139, 0, 100, 131, 211, 100, 0, 
	99, 100, 101, 100, 102, 105, 98, 105, 
	0, 100, 131, 211, 100, 0, 99, 100, 
	101, 100, 102, 105, 106, 98, 105, 0, 
	100, 131, 211, 100, 0, 99, 100, 101, 
	100, 102, 105, 106, 98, 105, 0, 100, 
	131, 211, 100, 0, 99, 103, 104, 135, 
	102, 103, 104, 135, 102, 100, 101, 100, 
	102, 105, 106, 98, 105, 0, 100, 131, 
	211, 100, 0, 99, 101, 105, 107, 0, 
	108, 0, 109, 0, 110, 0, 111, 0, 
	112, 0, 113, 0, 114, 0, 114, 123, 
	114, 124, 130, 0, 0, 130, 0, 119, 
	0, 0, 0, 115, 116, 117, 116, 0, 
	118, 0, 118, 0, 119, 0, 100, 0, 
	115, 116, 117, 116, 118, 118, 100, 0, 
	116, 117, 116, 118, 118, 100, 0, 117, 
	118, 120, 121, 0, 115, 116, 117, 116, 
	0, 118, 0, 118, 0, 119, 0, 100, 
	0, 115, 122, 0, 115, 0, 114, 123, 
	114, 124, 130, 0, 0, 130, 0, 119, 
	0, 0, 0, 115, 125, 126, 127, 124, 
	125, 126, 127, 124, 116, 117, 116, 118, 
	118, 100, 0, 125, 128, 0, 124, 129, 
	0, 124, 0, 123, 130, 132, 133, 0, 
	99, 100, 101, 100, 102, 105, 98, 105, 
	0, 100, 131, 211, 100, 0, 99, 134, 
	0, 99, 0, 103, 136, 0, 102, 137, 
	0, 102, 0, 98, 138, 98, 102, 139, 
	106, 0, 139, 0, 100, 131, 211, 100, 
	0, 99, 138, 139, 140, 198, 140, 149, 
	199, 156, 0, 199, 0, 181, 0, 212, 
	0, 141, 142, 143, 142, 0, 144, 0, 
	144, 145, 181, 0, 0, 0, 141, 142, 
	143, 142, 144, 144, 145, 0, 142, 143, 
	142, 144, 144, 145, 0, 143, 144, 189, 
	190, 189, 191, 197, 156, 0, 197, 0, 
	189, 147, 185, 0, 147, 0, 146, 147, 
	148, 147, 149, 155, 140, 155, 0, 185, 
	0, 212, 0, 146, 147, 148, 147, 149, 
	155, 156, 140, 155, 0, 181, 0, 212, 
	0, 141, 147, 148, 147, 149, 155, 156, 
	140, 155, 0, 181, 0, 212, 0, 141, 
	150, 151, 152, 149, 150, 151, 152, 149, 
	142, 143, 142, 144, 144, 145, 0, 150, 
	153, 0, 149, 154, 0, 149, 0, 148, 
	155, 157, 0, 158, 0, 159, 0, 160, 
	0, 161, 0, 162, 0, 163, 0, 164, 
	0, 164, 173, 164, 174, 180, 0, 0, 
	180, 0, 169, 0, 0, 0, 165, 166, 
	167, 166, 0, 168, 0, 168, 0, 169, 
	0, 147, 0, 165, 166, 167, 166, 168, 
	168, 147, 0, 166, 167, 166, 168, 168, 
	147, 0, 167, 168, 170, 171, 0, 165, 
	166, 167, 166, 0, 168, 0, 168, 0, 
	169, 0, 147, 0, 165, 172, 0, 165, 
	0, 164, 173, 164, 174, 180, 0, 0, 
	180, 0, 169, 0, 0, 0, 165, 175, 
	176, 177, 174, 175, 176, 177, 174, 166, 
	167, 166, 168, 168, 147, 0, 175, 178, 
	0, 174, 179, 0, 174, 0, 173, 180, 
	182, 183, 0, 141, 142, 143, 142, 0, 
	144, 0, 144, 145, 181, 0, 0, 0, 
	141, 184, 0, 141, 0, 186, 187, 0, 
	146, 147, 148, 147, 149, 155, 140, 155, 
	0, 185, 0, 212, 0, 146, 188, 0, 
	146, 0, 189, 190, 189, 191, 197, 156, 
	0, 197, 0, 147, 185, 0, 147, 0, 
	146, 189, 190, 189, 191, 197, 156, 0, 
	197, 0, 147, 185, 0, 147, 0, 146, 
	192, 193, 194, 191, 192, 193, 194, 191, 
	147, 148, 147, 149, 155, 156, 140, 155, 
	0, 181, 0, 212, 0, 141, 192, 195, 
	0, 191, 196, 0, 191, 0, 190, 197, 
	140, 198, 140, 149, 199, 156, 0, 199, 
	0, 181, 0, 212, 0, 141, 198, 199, 
	200, 208, 200, 6, 54, 13, 0, 54, 
	0, 55, 39, 0, 0, 0, 1, 202, 
	203, 202, 6, 12, 204, 12, 0, 43, 
	0, 0, 0, 201, 202, 203, 202, 6, 
	12, 13, 204, 12, 0, 39, 0, 0, 
	0, 1, 202, 203, 202, 6, 12, 13, 
	204, 12, 0, 39, 0, 0, 0, 1, 
	204, 205, 204, 6, 38, 13, 0, 38, 
	0, 39, 0, 0, 0, 1, 204, 205, 
	204, 6, 38, 13, 0, 38, 0, 39, 
	0, 0, 0, 1, 202, 203, 202, 6, 
	12, 204, 12, 0, 43, 0, 0, 0, 
	201, 202, 203, 202, 6, 12, 13, 204, 
	12, 0, 39, 0, 0, 0, 1, 200, 
	208, 200, 6, 54, 13, 0, 54, 0, 
	55, 39, 0, 0, 0, 1, 209, 210, 
	209, 90, 90, 0, 209, 210, 209, 90, 
	90, 0, 0, 0, 0
};

static const char _vscf_trans_actions[] = {
	3, 3, 3, 0, 3, 0, 3, 3, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 11, 11, 11, 11, 
	11, 11, 0, 0, 0, 0, 0, 0, 
	1, 0, 0, 0, 0, 0, 0, 13, 
	1, 0, 15, 0, 1, 0, 0, 0, 
	0, 11, 11, 11, 11, 5, 5, 5, 
	5, 5, 5, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 1, 0, 0, 0, 0, 0, 1, 
	0, 0, 0, 1, 23, 23, 23, 0, 
	23, 0, 23, 0, 0, 0, 23, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	11, 11, 11, 11, 11, 11, 0, 0, 
	0, 0, 0, 0, 0, 81, 81, 81, 
	0, 81, 0, 81, 0, 11, 0, 81, 
	0, 11, 0, 0, 0, 0, 11, 11, 
	11, 57, 11, 0, 0, 11, 0, 57, 
	0, 0, 0, 57, 0, 0, 0, 0, 
	11, 11, 11, 11, 25, 25, 25, 25, 
	25, 25, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 60, 60, 60, 0, 60, 
	0, 60, 60, 11, 0, 0, 0, 11, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 1, 
	0, 0, 0, 0, 0, 13, 1, 0, 
	15, 0, 1, 11, 11, 11, 57, 11, 
	11, 0, 11, 0, 66, 57, 0, 69, 
	0, 57, 0, 0, 0, 0, 11, 11, 
	11, 11, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 1, 0, 0, 0, 0, 0, 13, 
	1, 0, 15, 0, 1, 7, 7, 7, 
	27, 7, 7, 7, 0, 30, 0, 7, 
	33, 0, 0, 0, 0, 0, 1, 0, 
	0, 0, 0, 0, 13, 1, 0, 15, 
	0, 1, 11, 11, 11, 57, 11, 11, 
	11, 11, 0, 66, 57, 11, 69, 0, 
	57, 0, 0, 0, 0, 11, 11, 11, 
	11, 9, 9, 9, 42, 9, 9, 9, 
	9, 0, 45, 42, 9, 48, 0, 42, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 1, 0, 0, 
	0, 0, 0, 1, 0, 0, 0, 1, 
	23, 23, 23, 0, 23, 0, 23, 0, 
	0, 0, 23, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 11, 11, 11, 11, 
	11, 11, 0, 0, 0, 0, 0, 0, 
	0, 81, 81, 81, 0, 81, 0, 81, 
	0, 11, 0, 81, 0, 11, 0, 0, 
	0, 0, 11, 11, 11, 57, 11, 0, 
	0, 11, 0, 57, 0, 0, 0, 57, 
	0, 0, 0, 0, 11, 11, 11, 11, 
	25, 25, 25, 25, 25, 25, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 63, 63, 63, 
	84, 63, 63, 63, 0, 88, 11, 63, 
	92, 0, 11, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 11, 11, 11, 57, 11, 11, 0, 
	11, 0, 66, 57, 11, 69, 0, 57, 
	0, 0, 0, 0, 0, 1, 0, 0, 
	0, 0, 0, 13, 1, 17, 15, 0, 
	1, 7, 7, 7, 27, 7, 7, 7, 
	0, 30, 0, 36, 33, 0, 0, 0, 
	0, 0, 1, 0, 0, 0, 0, 0, 
	13, 1, 17, 15, 0, 1, 11, 11, 
	11, 57, 11, 11, 11, 11, 0, 66, 
	57, 72, 69, 0, 57, 0, 0, 0, 
	0, 11, 11, 11, 11, 9, 9, 9, 
	42, 9, 9, 9, 9, 0, 45, 42, 
	51, 48, 0, 42, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 1, 0, 0, 0, 0, 0, 1, 
	0, 0, 0, 1, 23, 23, 23, 0, 
	23, 0, 23, 0, 0, 0, 23, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	11, 11, 11, 11, 11, 11, 0, 0, 
	0, 0, 0, 0, 0, 81, 81, 81, 
	0, 81, 0, 81, 0, 11, 0, 81, 
	0, 11, 0, 0, 0, 0, 11, 11, 
	11, 57, 11, 0, 0, 11, 0, 57, 
	0, 0, 0, 57, 0, 0, 0, 0, 
	11, 11, 11, 11, 25, 25, 25, 25, 
	25, 25, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 63, 63, 63, 84, 63, 63, 63, 
	0, 88, 11, 96, 92, 0, 11, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 11, 11, 11, 57, 11, 
	11, 0, 11, 0, 66, 57, 72, 69, 
	0, 57, 0, 0, 0, 0, 0, 1, 
	0, 0, 0, 0, 0, 1, 0, 19, 
	0, 1, 3, 3, 3, 0, 3, 0, 
	3, 3, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 11, 11, 
	11, 11, 11, 11, 0, 0, 0, 0, 
	0, 0, 1, 0, 0, 0, 0, 0, 
	0, 13, 1, 0, 15, 0, 1, 7, 
	7, 7, 27, 7, 7, 7, 0, 0, 
	0, 39, 0, 0, 0, 0, 0, 1, 
	0, 0, 0, 0, 0, 1, 0, 19, 
	0, 1, 11, 11, 11, 57, 11, 11, 
	11, 11, 0, 57, 0, 75, 0, 57, 
	0, 0, 0, 0, 11, 11, 11, 11, 
	5, 5, 5, 5, 5, 5, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 1, 0, 0, 0, 
	0, 0, 1, 0, 0, 0, 1, 23, 
	23, 23, 0, 23, 0, 23, 0, 0, 
	0, 23, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 11, 11, 11, 11, 11, 
	11, 0, 0, 0, 0, 0, 0, 0, 
	81, 81, 81, 0, 81, 0, 81, 0, 
	11, 0, 81, 0, 11, 0, 0, 0, 
	0, 11, 11, 11, 57, 11, 0, 0, 
	11, 0, 57, 0, 0, 0, 57, 0, 
	0, 0, 0, 11, 11, 11, 11, 25, 
	25, 25, 25, 25, 25, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 60, 60, 60, 0, 
	60, 0, 60, 60, 11, 0, 0, 0, 
	11, 0, 0, 0, 0, 0, 0, 0, 
	0, 63, 63, 63, 84, 63, 63, 63, 
	0, 11, 0, 100, 0, 11, 0, 0, 
	0, 0, 0, 0, 0, 1, 0, 0, 
	0, 0, 0, 13, 1, 0, 15, 0, 
	1, 11, 11, 11, 57, 11, 11, 0, 
	11, 0, 66, 57, 0, 69, 0, 57, 
	0, 0, 0, 0, 11, 11, 11, 11, 
	9, 9, 9, 42, 9, 9, 9, 9, 
	0, 42, 0, 54, 0, 42, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	11, 11, 11, 57, 11, 11, 0, 11, 
	0, 57, 0, 75, 0, 57, 0, 0, 
	0, 0, 0, 1, 0, 0, 0, 0, 
	0, 21, 1, 0, 0, 0, 1, 7, 
	7, 7, 27, 7, 7, 7, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 1, 
	0, 0, 0, 0, 0, 1, 0, 0, 
	0, 1, 11, 11, 11, 57, 11, 11, 
	11, 11, 0, 57, 0, 0, 0, 57, 
	0, 0, 0, 1, 0, 0, 0, 0, 
	0, 1, 0, 0, 0, 1, 11, 11, 
	11, 57, 11, 11, 0, 11, 0, 57, 
	0, 0, 0, 57, 63, 63, 63, 84, 
	63, 63, 63, 0, 11, 0, 0, 0, 
	11, 9, 9, 9, 42, 9, 9, 9, 
	9, 0, 42, 0, 0, 0, 42, 11, 
	11, 11, 57, 11, 11, 0, 11, 0, 
	78, 57, 0, 0, 0, 57, 0, 0, 
	0, 0, 0, 0, 11, 11, 11, 11, 
	11, 0, 0, 0, 0
};

static const char _vscf_eof_actions[] = {
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 7, 0, 11, 0, 11, 63, 9, 
	11, 0, 11, 0, 0
};

static const int vscf_start = 200;
static const int vscf_first_final = 200;
static const int vscf_error = 0;

static const int vscf_en_array = 98;
static const int vscf_en_hash = 140;
static const int vscf_en_main = 200;


#line 767 "./libgdnsd/vscf.rl"

// end-sonar-exclude
// *INDENT-ON*

/****************************/
/*** Public API functions ***/
/****************************/

vscf_data_t* vscf_scan_buf(const size_t len, const char* buf, const char* source, bool source_is_fn)
{
    (void)vscf_en_main; // silence unused var warning from generated code

    vscf_scnr_t* scnr = xcalloc(sizeof(*scnr));
    scnr->lcount = 1;
    if (source_is_fn)
        scnr->fn = source;
    scnr->desc = source;
    scnr->cs = vscf_start;
    scnr->cont_stack_alloc = 2;
    scnr->cont_stack = xmalloc_n(scnr->cont_stack_alloc, sizeof(*scnr->cont_stack));

    // default container is hash, will be replaced if array
    scnr->cont_stack[0] = (vscf_data_t*)hash_new();

    // Whole input in one chunk
    scnr->tstart = scnr->p = buf;
    scnr->eof = scnr->pe = buf + len;

    // *INDENT-OFF*
    // start-sonar-exclude
    
#line 808 "./libgdnsd/vscf.rl"


GDNSD_DIAG_PUSH_IGNORED("-Wswitch-default")
GDNSD_DIAG_PUSH_IGNORED("-Wsign-conversion")
    
#line 1306 "libgdnsd/vscf.c"
	{
	int _klen;
	unsigned int _trans;
	const char *_acts;
	unsigned int _nacts;
	const char *_keys;

	if ( (     scnr->p) == (    scnr->pe) )
		goto _test_eof;
	if ( (    scnr->cs) == 0 )
		goto _out;
_resume:
	_keys = _vscf_trans_keys + _vscf_key_offsets[(    scnr->cs)];
	_trans = _vscf_index_offsets[(    scnr->cs)];

	_klen = _vscf_single_lengths[(    scnr->cs)];
	if ( _klen > 0 ) {
		const char *_lower = _keys;
		const char *_mid;
		const char *_upper = _keys + _klen - 1;
		while (1) {
			if ( _upper < _lower )
				break;

			_mid = _lower + ((_upper-_lower) >> 1);
			if ( (*(     scnr->p)) < *_mid )
				_upper = _mid - 1;
			else if ( (*(     scnr->p)) > *_mid )
				_lower = _mid + 1;
			else {
				_trans += (unsigned int)(_mid - _keys);
				goto _match;
			}
		}
		_keys += _klen;
		_trans += _klen;
	}

	_klen = _vscf_range_lengths[(    scnr->cs)];
	if ( _klen > 0 ) {
		const char *_lower = _keys;
		const char *_mid;
		const char *_upper = _keys + (_klen<<1) - 2;
		while (1) {
			if ( _upper < _lower )
				break;

			_mid = _lower + (((_upper-_lower) >> 1) & ~1);
			if ( (*(     scnr->p)) < _mid[0] )
				_upper = _mid - 2;
			else if ( (*(     scnr->p)) > _mid[1] )
				_lower = _mid + 2;
			else {
				_trans += (unsigned int)((_mid - _keys)>>1);
				goto _match;
			}
		}
		_trans += _klen;
	}

_match:
	(    scnr->cs) = _vscf_trans_targs[_trans];

	if ( _vscf_trans_actions[_trans] == 0 )
		goto _again;

	_acts = _vscf_actions + _vscf_trans_actions[_trans];
	_nacts = (unsigned int) *_acts++;
	while ( _nacts-- > 0 )
	{
		switch ( *_acts++ )
		{
	case 0:
#line 626 "./libgdnsd/vscf.rl"
	{ scnr->tstart = (     scnr->p); }
	break;
	case 1:
#line 628 "./libgdnsd/vscf.rl"
	{
        if (!set_key(scnr, (     scnr->p)))
            {(     scnr->p)++; goto _out; }
    }
	break;
	case 2:
#line 633 "./libgdnsd/vscf.rl"
	{
        scnr->tstart++;
        if (!set_key(scnr, (     scnr->p) - 1))
            {(     scnr->p)++; goto _out; }
    }
	break;
	case 3:
#line 639 "./libgdnsd/vscf.rl"
	{
        if (!scnr_set_simple(scnr, (     scnr->p)))
            {(     scnr->p)++; goto _out; }
    }
	break;
	case 4:
#line 644 "./libgdnsd/vscf.rl"
	{
        scnr->tstart++;
        if (!scnr_set_simple(scnr, (     scnr->p) - 1))
            {(     scnr->p)++; goto _out; }
    }
	break;
	case 5:
#line 651 "./libgdnsd/vscf.rl"
	{ scnr->lcount++; }
	break;
	case 6:
#line 689 "./libgdnsd/vscf.rl"
	{
        if (!cont_stack_push(scnr, (vscf_data_t*)array_new()))
            {(     scnr->p)++; goto _out; }
        {
            if (scnr->top == scnr->cs_stack_alloc)
                scnr->cs_stack = xrealloc_n(scnr->cs_stack, ++scnr->cs_stack_alloc, sizeof(*scnr->cs_stack));
        {( scnr->cs_stack)[(   scnr->top)++] = (    scnr->cs); (    scnr->cs) = 98;goto _again;}}
    }
	break;
	case 7:
#line 695 "./libgdnsd/vscf.rl"
	{
        if (!cont_stack_push(scnr, (vscf_data_t*)hash_new()))
            {(     scnr->p)++; goto _out; }
        {
            if (scnr->top == scnr->cs_stack_alloc)
                scnr->cs_stack = xrealloc_n(scnr->cs_stack, ++scnr->cs_stack_alloc, sizeof(*scnr->cs_stack));
        {( scnr->cs_stack)[(   scnr->top)++] = (    scnr->cs); (    scnr->cs) = 140;goto _again;}}
    }
	break;
	case 8:
#line 701 "./libgdnsd/vscf.rl"
	{
        cont_stack_pop(scnr);
        {(    scnr->cs) = ( scnr->cs_stack)[--(   scnr->top)]; goto _again;}
    }
	break;
	case 9:
#line 706 "./libgdnsd/vscf.rl"
	{
        cont_stack_pop(scnr);
        {(    scnr->cs) = ( scnr->cs_stack)[--(   scnr->top)]; goto _again;}
    }
	break;
	case 10:
#line 711 "./libgdnsd/vscf.rl"
	{
        gdnsd_assert(scnr->cont_stack_top == 0); // outermost
        gdnsd_assert(vscf_is_hash(scnr->cont_stack[0])); // default hash
        hash_destroy((vscf_hash_t*)scnr->cont_stack[0]);
        scnr->cont_stack[0] = (vscf_data_t*)array_new();
    }
	break;
	case 11:
#line 718 "./libgdnsd/vscf.rl"
	{
        if (!scnr_proc_include(scnr, (     scnr->p)))
            {(     scnr->p)++; goto _out; }
    }
	break;
	case 12:
#line 723 "./libgdnsd/vscf.rl"
	{
        scnr->tstart++;
        if (!scnr_proc_include(scnr, (     scnr->p) - 1))
            {(     scnr->p)++; goto _out; }
    }
	break;
#line 1463 "libgdnsd/vscf.c"
		}
	}

_again:
	if ( (    scnr->cs) == 0 )
		goto _out;
	if ( ++(     scnr->p) != (    scnr->pe) )
		goto _resume;
	_test_eof: {}
	if ( (     scnr->p) == (   scnr->eof) )
	{
	const char *__acts = _vscf_actions + _vscf_eof_actions[(    scnr->cs)];
	unsigned int __nacts = (unsigned int) *__acts++;
	while ( __nacts-- > 0 ) {
		switch ( *__acts++ ) {
	case 3:
#line 639 "./libgdnsd/vscf.rl"
	{
        if (!scnr_set_simple(scnr, (     scnr->p)))
            {(     scnr->p)++; goto _out; }
    }
	break;
	case 4:
#line 644 "./libgdnsd/vscf.rl"
	{
        scnr->tstart++;
        if (!scnr_set_simple(scnr, (     scnr->p) - 1))
            {(     scnr->p)++; goto _out; }
    }
	break;
	case 5:
#line 651 "./libgdnsd/vscf.rl"
	{ scnr->lcount++; }
	break;
#line 1494 "libgdnsd/vscf.c"
		}
	}
	}

	_out: {}
	}

#line 813 "./libgdnsd/vscf.rl"
GDNSD_DIAG_POP
GDNSD_DIAG_POP
    // end-sonar-exclude
    // *INDENT-ON*

    // Error/incomplete states
    if (scnr->cs == vscf_error) {
        parse_error_noargs("Syntax error");
    } else if (scnr->cs < vscf_first_final) {
        if (scnr->cs == vscf_en_hash)
            parse_error_noargs("Unterminated hash at end of file");
        else if (scnr->cs == vscf_en_array)
            parse_error_noargs("Unterminated array at end of file");
        else if (*(scnr->eof - 1) != '\n')
            parse_error_noargs("Trailing incomplete or unparseable record at end of file (missing newline at end of file?)");
        else
            parse_error_noargs("Trailing incomplete or unparseable record at end of file");
    }

    if (scnr->cs_stack)
        free(scnr->cs_stack);

    vscf_data_t* retval;

    if (scnr->err_emitted) {
        val_destroy(scnr->cont_stack[0]);
        retval = NULL;
    } else {
        gdnsd_assert(scnr->cont_stack_top == 0);
        retval = scnr->cont_stack[0];
    }

    free(scnr->cont_stack);
    free(scnr);
    return retval;
}

vscf_data_t* vscf_scan_filename(const char* fn)
{
    vscf_data_t* rv = NULL;
    gdnsd_fmap_t* fmap = gdnsd_fmap_new(fn, true, false);
    if (fmap) {
        const size_t len = gdnsd_fmap_get_len(fmap);
        const char* buf = gdnsd_fmap_get_buf(fmap);
        rv = vscf_scan_buf(len, buf, fn, true);
        if (gdnsd_fmap_delete(fmap) && rv) {
            vscf_destroy(rv);
            rv = NULL;
        }
    }

    return rv;
}

void vscf_destroy(vscf_data_t* d)
{
    val_destroy(d);
}

vscf_type_t vscf_get_type(const vscf_data_t* d)
{
    return d->type;
}

bool vscf_is_simple(const vscf_data_t* d)
{
    return d->type == VSCF_SIMPLE_T;
}

bool vscf_is_array(const vscf_data_t* d)
{
    return d->type == VSCF_ARRAY_T;
}

bool vscf_is_hash(const vscf_data_t* d)
{
    return d->type == VSCF_HASH_T;
}

bool vscf_is_root(const vscf_data_t* d)
{
    return d->parent == NULL;
}

vscf_data_t* vscf_get_parent(const vscf_data_t* d)
{
    return d->parent;
}

unsigned vscf_simple_get_len(vscf_data_t* d)
{
    gdnsd_assert(vscf_is_simple(d));
    return d->simple.len;
}

const char* vscf_simple_get_data(vscf_data_t* d)
{
    gdnsd_assert(vscf_is_simple(d));
    return d->simple.val;
}

unsigned vscf_array_get_len(const vscf_data_t* d)
{
    if (d->type != VSCF_ARRAY_T)
        return 1;
    return d->array.len;
}

vscf_data_t* vscf_array_get_data(vscf_data_t* d, unsigned idx)
{
    if (d->type != VSCF_ARRAY_T) {
        if (idx)
            return NULL;
        return d;
    }
    if (idx >= d->array.len)
        return NULL;
    return d->array.vals[idx];
}

unsigned vscf_hash_get_len(const vscf_data_t* d)
{
    gdnsd_assert(vscf_is_hash(d));
    return d->hash.child_count;
}

vscf_data_t* vscf_hash_get_data_bykey(const vscf_data_t* d, const char* key, unsigned klen, bool set_mark)
{
    gdnsd_assert(vscf_is_hash(d));
    if (d->hash.child_count) {
        unsigned child_mask = count2mask(d->hash.child_count);
        unsigned child_hash = key_hash(key, klen, child_mask);
        vscf_hentry_t* he = d->hash.children[child_hash];
        while (he) {
            if ((klen == he->klen) && !memcmp(key, he->key, klen)) {
                if (set_mark)
                    he->marked = true;
                return he->val;
            }
            he = he->next;
        }
    }

    return NULL;
}

const char* vscf_hash_get_key_byindex(const vscf_data_t* d, unsigned idx, unsigned* klen_ptr)
{
    gdnsd_assert(vscf_is_hash(d));
    if (idx >= d->hash.child_count)
        return NULL;
    if (klen_ptr)
        *klen_ptr = d->hash.ordered[idx]->klen;
    const char* rv = d->hash.ordered[idx]->key;
    gdnsd_assert(rv);
    return rv;
}

vscf_data_t* vscf_hash_get_data_byindex(const vscf_data_t* d, unsigned idx)
{
    gdnsd_assert(vscf_is_hash(d));
    if (idx >= d->hash.child_count)
        return NULL;
    vscf_data_t* rv = d->hash.ordered[idx]->val;
    gdnsd_assert(rv);
    return rv;
}

int vscf_hash_get_index_bykey(const vscf_data_t* d, const char* key, unsigned klen)
{
    gdnsd_assert(vscf_is_hash(d));
    if (d->hash.child_count) {
        unsigned child_mask = count2mask(d->hash.child_count);
        unsigned child_hash = key_hash(key, klen, child_mask);
        vscf_hentry_t* he = d->hash.children[child_hash];
        while (he) {
            if ((klen == he->klen) && !memcmp(key, he->key, klen))
                return (int)he->index;
            he = he->next;
        }
    }

    return -1;
}

void vscf_hash_iterate(const vscf_data_t* d, bool ignore_mark, vscf_hash_iter_cb_t f, void* data)
{
    gdnsd_assert(vscf_is_hash(d));
    for (unsigned i = 0; i < d->hash.child_count; i++) {
        const vscf_hentry_t* hentry = d->hash.ordered[i];
        if (!ignore_mark || !hentry->marked)
            if (!f(hentry->key, hentry->klen, hentry->val, data))
                return;
    }
}

void vscf_hash_iterate_const(const vscf_data_t* d, bool ignore_mark, vscf_hash_iter_const_cb_t f, const void* data)
{
    gdnsd_assert(vscf_is_hash(d));
    for (unsigned i = 0; i < d->hash.child_count; i++) {
        const vscf_hentry_t* hentry = d->hash.ordered[i];
        if (!ignore_mark || !hentry->marked)
            if (!f(hentry->key, hentry->klen, hentry->val, data))
                return;
    }
}

void vscf_hash_sort(const vscf_data_t* d, vscf_key_cmp_cb_t f)
{
    gdnsd_assert(vscf_is_hash(d));
    qsort(d->hash.ordered, d->hash.child_count, sizeof(*d->hash.ordered),
          (int(*)(const void*, const void*))f
         );
    for (unsigned i = 0; i < d->hash.child_count; i++)
        d->hash.ordered[i]->index = i;
}

bool vscf_simple_get_as_ulong(vscf_data_t* d, unsigned long* out)
{
    gdnsd_assert(vscf_is_simple(d));
    if (!d->simple.len)
        return false;
    char* eptr;
    char* real_eptr = d->simple.val + d->simple.len;
    errno = 0;
    unsigned long retval = strtoul(d->simple.val, &eptr, 0);
    if (errno || eptr != real_eptr) {
        errno = 0;
        return false;
    }

    *out = retval;
    return true;
}

bool vscf_simple_get_as_long(vscf_data_t* d, long* out)
{
    gdnsd_assert(vscf_is_simple(d));
    if (!d->simple.len)
        return false;
    char* eptr;
    char* real_eptr = d->simple.val + d->simple.len;
    errno = 0;
    long retval = strtol(d->simple.val, &eptr, 0);
    if (errno || eptr != real_eptr) {
        errno = 0;
        return false;
    }

    *out = retval;
    return true;
}

bool vscf_simple_get_as_double(vscf_data_t* d, double* out)
{
    gdnsd_assert(vscf_is_simple(d));
    if (!d->simple.len)
        return false;
    char* eptr;
    char* real_eptr = d->simple.val + d->simple.len;
    errno = 0;
    double retval = strtod(d->simple.val, &eptr);
    if (errno || eptr != real_eptr) {
        errno = 0;
        return false;
    }

    *out = retval;
    return true;
}

bool vscf_simple_get_as_bool(vscf_data_t* d, bool* out)
{
    gdnsd_assert(vscf_is_simple(d));
    if (d->simple.len == 4
            && (d->simple.val[0] == 'T' || d->simple.val[0] == 't')
            && (d->simple.val[1] == 'R' || d->simple.val[1] == 'r')
            && (d->simple.val[2] == 'U' || d->simple.val[2] == 'u')
            && (d->simple.val[3] == 'E' || d->simple.val[3] == 'e')) {
        *out = true;
        return true;
    }

    if (d->simple.len == 5
            && (d->simple.val[0] == 'F' || d->simple.val[0] == 'f')
            && (d->simple.val[1] == 'A' || d->simple.val[1] == 'a')
            && (d->simple.val[2] == 'L' || d->simple.val[2] == 'l')
            && (d->simple.val[3] == 'S' || d->simple.val[3] == 's')
            && (d->simple.val[4] == 'E' || d->simple.val[4] == 'e')) {
        *out = false;
        return true;
    }

    return false;
}

dname_status_t vscf_simple_get_as_dname(const vscf_data_t* d, uint8_t* dname)
{
    gdnsd_assert(vscf_is_simple(d));
    return dname_from_string(dname, d->simple.rval, d->simple.rlen);
}

vscf_data_t* vscf_hash_new(void)
{
    return (vscf_data_t*)hash_new();
}

vscf_data_t* vscf_array_new(void)
{
    return (vscf_data_t*)array_new();
}

vscf_data_t* vscf_simple_new(const char* rval, const unsigned rlen)
{
    return (vscf_data_t*)simple_new(NULL, rval, rlen);
}

void vscf_array_add_val(vscf_data_t* a, vscf_data_t* v)
{
    gdnsd_assert(vscf_is_array(a));
    array_add_val(&a->array, v);
}

bool vscf_hash_add_val(const char* key, const unsigned klen, vscf_data_t* h, vscf_data_t* v)
{
    gdnsd_assert(vscf_is_hash(h));
    return hash_add_val(key, klen, &h->hash, v);
}

vscf_data_t* vscf_clone(const vscf_data_t* d, const bool ignore_marked)
{
    return val_clone(d, ignore_marked);
}

void vscf_hash_inherit(const vscf_data_t* src, vscf_data_t* dest, const char* k, const bool mark_src)
{
    gdnsd_assert(vscf_is_hash(src));
    gdnsd_assert(vscf_is_hash(dest));

    const vscf_data_t* src_val = vscf_hash_get_data_bystringkey(src, k, mark_src);
    if (src_val && !vscf_hash_get_data_bystringkey(dest, k, false))
        vscf_hash_add_val(k, strlen(k), dest, vscf_clone(src_val, false));
}

void vscf_hash_inherit_all(const vscf_data_t* src, vscf_data_t* dest, const bool skip_marked)
{
    gdnsd_assert(vscf_is_hash(src));
    gdnsd_assert(vscf_is_hash(dest));

    const unsigned src_len = vscf_hash_get_len(src);
    for (unsigned i = 0; i < src_len; i++)
        if (!skip_marked || !src->hash.ordered[i]->marked)
            vscf_hash_inherit(src, dest, vscf_hash_get_key_byindex(src, i, NULL), false);
}

bool vscf_hash_bequeath_all(const vscf_data_t* src, const char* k, const bool mark_src, const bool skip_marked)
{
    gdnsd_assert(vscf_is_hash(src));

    bool rv = false;

    const vscf_data_t* src_val = vscf_hash_get_data_bystringkey(src, k, mark_src);
    if (src_val) {
        const unsigned src_len = vscf_hash_get_len(src);
        for (unsigned i = 0; i < src_len; i++) {
            vscf_data_t* child_val = vscf_hash_get_data_byindex(src, i);
            gdnsd_assert(child_val);
            if (vscf_is_hash(child_val) && (!skip_marked || !src->hash.ordered[i]->marked))
                if (!vscf_hash_get_data_bystringkey(child_val, k, false))
                    vscf_hash_add_val(k, strlen(k), child_val, vscf_clone(src_val, false));
        }
        rv = true;
    }

    return rv;
}
