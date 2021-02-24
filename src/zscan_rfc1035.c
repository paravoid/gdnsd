
#line 1 "./src/zscan_rfc1035.rl"
/* Copyright © 2012 Brandon L Black <blblack@gmail.com> and Jay Reitz <jreitz@gmail.com>
 *
 * This file is part of gdnsd.
 *
 * gdnsd is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * gdnsd is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with gdnsd.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

#include <config.h>
#include "zscan_rfc1035.h"

#include "conf.h"
#include "ltree.h"

#include <gdnsd/alloc.h>
#include <gdnsd/log.h>
#include <gdnsd/misc.h>
#include <gdnsd/file.h>

#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <setjmp.h>
#include <errno.h>

#ifndef INET6_ADDRSTRLEN
#define INET6_ADDRSTRLEN 46
#endif

#define parse_error(_fmt, ...) \
    do {\
        log_err("rfc1035: Zone %s: Zonefile parse error at file %s line %u: " _fmt, logf_dname(z->zone->dname), z->curfn, z->lcount, __VA_ARGS__);\
        siglongjmp(z->jbuf, 1);\
    } while (0)

#define parse_error_noargs(_fmt) \
    do {\
        log_err("rfc1035: Zone %s: Zonefile parse error at file %s line %u: " _fmt, logf_dname(z->zone->dname), z->curfn, z->lcount);\
        siglongjmp(z->jbuf, 1);\
    } while (0)

typedef struct {
    uint8_t  ipv6[16];
    uint32_t ipv4;
    bool     zn_err_detect;
    bool     lhs_is_ooz;
    unsigned lcount;
    unsigned text_len;
    unsigned def_ttl;
    unsigned uval;
    unsigned ttl;
    unsigned ttl_min;
    unsigned uv_1;
    unsigned uv_2;
    unsigned uv_3;
    unsigned uv_4;
    unsigned uv_5;
    unsigned rfc3597_data_len;
    unsigned rfc3597_data_written;
    uint8_t* rfc3597_data;
    zone_t* zone;
    const char* tstart;
    const char* curfn;
    char* include_filename;
    uint8_t  origin[256];
    uint8_t  file_origin[256];
    uint8_t  lhs_dname[256];
    uint8_t  rhs_dname[256];
    union {
        uint8_t eml_dname[256];
        char    rhs_dyn[256];
        char    caa_prop[256];
    };
    uint8_t* text;
    sigjmp_buf jbuf;
} zscan_t;

F_NONNULL
static void scanner(zscan_t* z, char* buf, const size_t bufsize);

/******** IP Addresses ********/

F_NONNULL
static void set_ipv4(zscan_t* z, const char* end)
{
    char txt[16];
    unsigned len = end - z->tstart;
    if (len > 15)
        parse_error_noargs("IPv4 address unparseable (too long)");
    memcpy(txt, z->tstart, len);
    txt[len] = 0;
    z->tstart = NULL;
    struct in_addr addr;
    int status = inet_pton(AF_INET, txt, &addr);
    if (status > 0)
        z->ipv4 = addr.s_addr;
    else
        parse_error("IPv4 address '%s' invalid", txt);
}

F_NONNULL
static void set_ipv6(zscan_t* z, const char* end)
{
    char txt[INET6_ADDRSTRLEN + 1];
    unsigned len = end - z->tstart;
    if (len > INET6_ADDRSTRLEN)
        parse_error_noargs("IPv6 address unparseable (too long)");
    memcpy(txt, z->tstart, len);
    txt[len] = 0;
    z->tstart = NULL;
    struct in6_addr v6a;
    int status = inet_pton(AF_INET6, txt, &v6a);
    if (status > 0)
        memcpy(z->ipv6, v6a.s6_addr, 16);
    else
        parse_error("IPv6 address '%s' invalid", txt);
}

F_NONNULL
static void set_uval(zscan_t* z)
{
    errno = 0;
    z->uval = strtoul(z->tstart, NULL, 10);
    z->tstart = NULL;
    if (errno)
        parse_error("Integer conversion error: %s", logf_errno());
}

F_NONNULL
static void validate_origin_in_zone(zscan_t* z, const uint8_t* origin)
{
    gdnsd_assert(z->zone->dname);
    if (!dname_isinzone(z->zone->dname, origin))
        parse_error("Origin '%s' is not within this zonefile's zone (%s)", logf_dname(origin), logf_dname(z->zone->dname));
}

F_NONNULL
static void validate_lhs_not_ooz(zscan_t* z)
{
    if (z->lhs_is_ooz)
        parse_error("Domainname '%s' is not within this zonefile's zone (%s)", logf_dname(z->lhs_dname), logf_dname(z->zone->dname));
}

F_NONNULL F_PURE
static unsigned dn_find_final_label_offset(const uint8_t* dname)
{
    gdnsd_assert(dname_status(dname) == DNAME_PARTIAL);

    // Since we assert DNAME_PARTIAL, we just have to search forward until the
    // next potential label len is the partial terminator 0xff.
    const uint8_t* dnptr = dname + 1;
    unsigned next_llen_pos = *dnptr + 1U;
    while (dnptr[next_llen_pos] != 0xff) {
        dnptr += next_llen_pos;
        next_llen_pos = *dnptr + 1U;
    }

    return (unsigned)(dnptr - dname);
}

// This converts an unqualified name to a qualified one.  Normal behavior is to
// append the current $ORIGIN, but we also plug in support for '@' here (as a
// lone character meaning $ORIGIN) and also these extensions:
//--
// * If the final label is "@Z", we replace that with the original zone-level
// origin (the name of the actual zone) rather than the current $ORIGIN
// * If the final label is "@F", we replace that with the original file-level
// origin (the origin when a zonefile or includefile was first loaded, before
// any $ORIGIN statement within it) rather than the current $ORIGIN
//--
// @Z and @F are equivalent when not processing an included file.
// @Z and @F can also, like @, be the first (only) label; there doesn't have to
// be any prefix label before them.

F_NONNULL
static dname_status_t dn_qualify(uint8_t* dname, const uint8_t* origin, uint8_t* const file_origin, const uint8_t* zone_origin)
{
    gdnsd_assert(dname_status(dname) == DNAME_PARTIAL);

    // Lone "@" case:
    if (dname[0] == 3U && dname[2] == '@') {
        gdnsd_assert(dname[1] == 1U && dname[3] == 0xff);
        dname_copy(dname, origin);
        return DNAME_VALID;
    }

    // @Z/@F handling (note @X for any other char is illegal for now):
    const unsigned final_label_offset = dn_find_final_label_offset(dname);
    const unsigned final_label_len = dname[final_label_offset];
    gdnsd_assert(final_label_len != 0);

    if (final_label_len == 2U && dname[final_label_offset + 1] == '@') {
        const uint8_t which = dname[final_label_offset + 2];
        // adjust dname to strip the final @X label off
        dname[final_label_offset] = 0xff;
        *dname -= 3U;
        // note lowercase z/f here, because earlier dname processing
        // normalizes all alpha chars to lowercase
        if (which == 'z')
            return dname_cat(dname, zone_origin);
        else if (which == 'f')
            return dname_cat(dname, file_origin);
        else
            return DNAME_INVALID;
    }

    // default qualification with no @ involvement
    return dname_cat(dname, origin);
}

F_NONNULL
static void dname_set(zscan_t* z, uint8_t* dname, unsigned len, bool lhs)
{
    gdnsd_assert(z->zone->dname);
    dname_status_t catstat;
    dname_status_t status;

    if (len) {
        status = dname_from_string(dname, z->tstart, len);
    } else {
        gdnsd_assert(lhs);
        dname_copy(dname, z->origin);
        status = DNAME_VALID;
    }

    switch (status) {
    case DNAME_INVALID:
        parse_error_noargs("unparseable domainname");
        break;
    case DNAME_VALID:
        if (lhs) {
            const bool inzone = dname_isinzone(z->zone->dname, dname);
            z->lhs_is_ooz = !inzone;
            // in-zone LHS dnames are made relative to zroot
            if (inzone)
                gdnsd_dname_drop_zone(dname, z->zone->dname);
        }
        break;
    case DNAME_PARTIAL:
        // even though in the lhs case we commonly trim
        //   back most or all of z->origin from dname, we
        //   still have to construct it just for validity checks
        catstat = dn_qualify(dname, z->origin, z->file_origin, z->zone->dname);
        if (catstat == DNAME_INVALID)
            parse_error_noargs("illegal domainname");
        gdnsd_assert(catstat == DNAME_VALID);
        if (lhs) {
            z->lhs_is_ooz = false;
            gdnsd_dname_drop_zone(dname, z->zone->dname);
        }
        break;
    default:
        gdnsd_assert(0);
    }
}

// This is broken out into a separate function (called via
//   function pointer to eliminate the possibility of
//   inlining on non-gcc compilers, I hope) to avoid issues with
//   setjmp and all of the local auto variables in zscan_rfc1035() below.
typedef bool (*sij_func_t)(zscan_t*, char*, const unsigned);
F_NONNULL F_NOINLINE
static bool _scan_isolate_jmp(zscan_t* z, char* buf, const unsigned bufsize)
{
    if (!sigsetjmp(z->jbuf, 0)) {
        scanner(z, buf, bufsize);
        return false;
    }
    return true;
}

F_NONNULL
static bool zscan_do(zone_t* zone, const uint8_t* origin, const char* fn, const unsigned def_ttl_arg)
{
    log_debug("rfc1035: Scanning file '%s' for zone '%s'", fn, logf_dname(zone->dname));

    bool failed = false;

    gdnsd_fmap_t* fmap = gdnsd_fmap_new(fn, true, true);
    if (!fmap) {
        failed = true;
        return failed;
    }

    const size_t bufsize = gdnsd_fmap_get_len(fmap);
    char* buf = gdnsd_fmap_get_buf(fmap);

    zscan_t* z = xcalloc(sizeof(*z));
    z->lcount = 1;
    z->def_ttl = def_ttl_arg;
    z->zone = zone;
    z->curfn = fn;
    dname_copy(z->origin, origin);
    dname_copy(z->file_origin, origin);
    z->lhs_dname[0] = 1; // set lhs to relative origin initially

    sij_func_t sij = &_scan_isolate_jmp;
    if (sij(z, buf, bufsize))
        failed = true;

    if (gdnsd_fmap_delete(fmap))
        failed = true;

    if (z->text)
        free(z->text);
    if (z->rfc3597_data)
        free(z->rfc3597_data);
    if (z->include_filename)
        free(z->include_filename);
    free(z);

    return failed;
}

/********** TXT ******************/

F_NONNULL
static void text_start(zscan_t* z V_UNUSED)
{
    gdnsd_assert(z->text == NULL);
    gdnsd_assert(z->text_len == 0);
}

F_NONNULL
static void text_add_tok(zscan_t* z, const unsigned len, const bool big_ok)
{
    char* text_temp = xmalloc(len ? len : 1);
    unsigned newlen = len;
    if (len) {
        newlen = dns_unescape(text_temp, z->tstart, len);
        if (!newlen) {
            free(text_temp);
            parse_error_noargs("Text chunk has bad escape sequence");
        }
        gdnsd_assert(newlen <= len);
    }

    if (newlen > 255U) {
        if (!big_ok || gcfg->disable_text_autosplit) {
            free(text_temp);
            parse_error_noargs("Text chunk too long (>255 unescaped)");
        }
        if (newlen > 16000U) {
            free(text_temp);
            parse_error_noargs("Text chunk too long (>16000 unescaped)");
        }
        const unsigned remainder = newlen % 255;
        const unsigned num_whole_chunks = (newlen - remainder) / 255;
        unsigned new_alloc = newlen + num_whole_chunks + (remainder ? 1 : 0);
        if (new_alloc + z->text_len > 16000U) {
            free(text_temp);
            parse_error_noargs("Text record too long (>16000 in rdata form)");
        }

        z->text = xrealloc(z->text, z->text_len + new_alloc);
        unsigned write_offset = z->text_len;
        z->text_len += new_alloc;
        const char* readptr = text_temp;
        for (unsigned i = 0; i < num_whole_chunks; i++) {
            z->text[write_offset++] = 255;
            memcpy(&z->text[write_offset], readptr, 255);
            write_offset += 255;
            readptr += 255;
        }
        if (remainder) {
            z->text[write_offset++] = remainder;
            memcpy(&z->text[write_offset], readptr, remainder);
        }
        gdnsd_assert(write_offset + remainder == z->text_len);
    } else { // 0-255 bytes, one chunk
        const unsigned new_alloc = newlen + 1;
        if (new_alloc + z->text_len > 16000U) {
            free(text_temp);
            parse_error_noargs("Text record too long (>16000 in rdata form)");
        }
        z->text = xrealloc(z->text, z->text_len + new_alloc);
        unsigned write_offset = z->text_len;
        z->text_len += new_alloc;
        z->text[write_offset++] = newlen;
        memcpy(&z->text[write_offset], text_temp, newlen);
    }

    free(text_temp);
    z->tstart = NULL;
}

F_NONNULL
static void text_add_tok_huge(zscan_t* z, const unsigned len)
{
    char* storage = xmalloc(len ? len : 1);
    unsigned newlen = len;
    if (len) {
        newlen = dns_unescape(storage, z->tstart, len);
        if (!newlen) {
            free(storage);
            parse_error_noargs("Text chunk has bad escape sequence");
        }
        gdnsd_assert(newlen <= len);
    }

    if (newlen > 16000U) {
        free(storage);
        parse_error_noargs("Text chunk too long (>16000 unescaped)");
    }

    // _huge is only used alone, not in a set
    gdnsd_assert(!z->text_len);
    gdnsd_assert(!z->text);

    z->text = (uint8_t*)storage;
    z->text_len = newlen;
    z->tstart = NULL;
}

F_NONNULL
static void set_filename(zscan_t* z, const unsigned len)
{
    char* fn = xmalloc(len + 1);
    const unsigned newlen = dns_unescape(fn, z->tstart, len);
    if (!newlen) {
        free(fn);
        parse_error_noargs("Filename has bad escape sequence");
    }
    gdnsd_assert(newlen <= len);
    z->include_filename = fn = xrealloc(fn, newlen + 1);
    fn[newlen] = 0;
    z->tstart = NULL;
}

F_NONNULL
static char* _make_zfn(const char* curfn, const char* include_fn)
{
    if (include_fn[0] == '/')
        return xstrdup(include_fn);

    const char* slashpos = strrchr(curfn, '/');
    const unsigned cur_copy = (slashpos - curfn) + 1;
    const unsigned include_len = strlen(include_fn);
    char* rv = xmalloc(cur_copy + include_len + 1);
    memcpy(rv, curfn, cur_copy);
    memcpy(rv + cur_copy, include_fn, include_len);
    rv[cur_copy + include_len] = 0;

    return rv;
}

F_NONNULL
static void process_include(zscan_t* z)
{
    gdnsd_assert(z->include_filename);

    validate_origin_in_zone(z, z->rhs_dname);
    char* zfn = _make_zfn(z->curfn, z->include_filename);
    free(z->include_filename);
    z->include_filename = NULL;
    bool subfailed = zscan_do(z->zone, z->rhs_dname, zfn, z->def_ttl);
    free(zfn);
    if (subfailed)
        siglongjmp(z->jbuf, 1);
}

// Input must have two bytes of text constrained to [0-9A-Fa-f]
F_NONNULL
static unsigned hexbyte(const char* intxt)
{
    gdnsd_assert(
        (intxt[0] >= '0' && intxt[0] <= '9')
        || (intxt[0] >= 'A' && intxt[0] <= 'F')
        || (intxt[0] >= 'a' && intxt[0] <= 'f')
    );
    gdnsd_assert(
        (intxt[1] >= '0' && intxt[1] <= '9')
        || (intxt[1] >= 'A' && intxt[1] <= 'F')
        || (intxt[1] >= 'a' && intxt[1] <= 'f')
    );

    int out;

    if (intxt[0] <= '9')
        out = (intxt[0] - '0') << 4;
    else
        out = ((intxt[0] | 0x20) - ('a' - 10)) << 4;

    if (intxt[1] <= '9')
        out |= (intxt[1] - '0');
    else
        out |= ((intxt[1] | 0x20) - ('a' - 10));

    gdnsd_assert(out >= 0 && out < 256);
    return (unsigned)out;
}

F_NONNULL
static void mult_uval(zscan_t* z, int fc)
{
    fc |= 0x20;
    switch (fc) {
    case 'm':
        z->uval *= 60;
        break;
    case 'h':
        z->uval *= 3600;
        break;
    case 'd':
        z->uval *= 86400;
        break;
    case 'w':
        z->uval *= 604800;
        break;
    default:
        gdnsd_assert(0);
    }
}

F_NONNULL
static void set_dyna(zscan_t* z, const char* fpc)
{
    unsigned dlen = fpc - z->tstart;
    if (dlen > 255)
        parse_error_noargs("DYNA/DYNC plugin!resource string cannot exceed 255 chars");
    memcpy(z->rhs_dyn, z->tstart, dlen);
    z->rhs_dyn[dlen] = 0;
    z->tstart = NULL;
}

F_NONNULL
static void set_caa_prop(zscan_t* z, const char* fpc)
{
    unsigned dlen = fpc - z->tstart;
    if (dlen > 255)
        parse_error_noargs("CAA property string cannot exceed 255 chars");
    memcpy(z->caa_prop, z->tstart, dlen);
    z->caa_prop[dlen] = 0;
    z->tstart = NULL;
}

F_NONNULL
static void rec_soa(zscan_t* z)
{
    validate_lhs_not_ooz(z);
    if (z->lhs_dname[0] != 1)
        parse_error_noargs("SOA record can only be defined for the root of the zone");
    if (ltree_add_rec_soa(
                z->zone,
                z->lhs_dname,
                .master = z->rhs_dname,
                .email = z->eml_dname,
                .ttl = z->ttl,
                .serial = z->uv_1,
                .refresh = z->uv_2,
                .retry = z->uv_3,
                .expire = z->uv_4,
                .ncache = z->uv_5)
       )
        siglongjmp(z->jbuf, 1);
}

F_NONNULL
static void rec_a(zscan_t* z)
{
    if (ltree_add_rec_a(z->zone, z->lhs_dname, z->ipv4, z->ttl, z->lhs_is_ooz))
        siglongjmp(z->jbuf, 1);
}

F_NONNULL
static void rec_aaaa(zscan_t* z)
{
    if (ltree_add_rec_aaaa(z->zone, z->lhs_dname, z->ipv6, z->ttl, z->lhs_is_ooz))
        siglongjmp(z->jbuf, 1);
}

F_NONNULL
static void rec_ns(zscan_t* z)
{
    validate_lhs_not_ooz(z);
    if (ltree_add_rec_ns(z->zone, z->lhs_dname, z->rhs_dname, z->ttl))
        siglongjmp(z->jbuf, 1);
}

F_NONNULL
static void rec_cname(zscan_t* z)
{
    validate_lhs_not_ooz(z);
    if (ltree_add_rec_cname(z->zone, z->lhs_dname, z->rhs_dname, z->ttl))
        siglongjmp(z->jbuf, 1);
}

F_NONNULL
static void rec_ptr(zscan_t* z)
{
    validate_lhs_not_ooz(z);
    if (ltree_add_rec_ptr(z->zone, z->lhs_dname, z->rhs_dname, z->ttl))
        siglongjmp(z->jbuf, 1);
}

F_NONNULL
static void rec_mx(zscan_t* z)
{
    validate_lhs_not_ooz(z);
    if (ltree_add_rec_mx(z->zone, z->lhs_dname, z->rhs_dname, z->ttl, z->uval))
        siglongjmp(z->jbuf, 1);
}

F_NONNULL
static void rec_srv(zscan_t* z)
{
    validate_lhs_not_ooz(z);
    if (ltree_add_rec_srv(
                z->zone,
                z->lhs_dname,
                .rhs = z->rhs_dname,
                .ttl = z->ttl,
                .priority = z->uv_1,
                .weight = z->uv_2,
                .port = z->uv_3)
       )
        siglongjmp(z->jbuf, 1);
}

F_NONNULL
static void text_cleanup(zscan_t* z)
{
    if (z->text)
        free(z->text);
    z->text = NULL;
    z->text_len = 0;
}

F_NONNULL
static void rec_naptr(zscan_t* z)
{
    validate_lhs_not_ooz(z);
    if (ltree_add_rec_naptr(
                z->zone,
                z->lhs_dname,
                .rhs = z->rhs_dname,
                .ttl = z->ttl,
                .order = z->uv_1,
                .pref = z->uv_2,
                .text_len = z->text_len,
                .text = z->text)
       )
        siglongjmp(z->jbuf, 1);
    z->text = NULL; // storage handed off to ltree
    text_cleanup(z);
}

F_NONNULL
static void rec_txt(zscan_t* z)
{
    validate_lhs_not_ooz(z);
    if (ltree_add_rec_txt(z->zone, z->lhs_dname, z->text_len, z->text, z->ttl))
        siglongjmp(z->jbuf, 1);
    z->text = NULL; // storage handed off to ltree
    text_cleanup(z);
}

F_NONNULL
static void rec_dyna(zscan_t* z)
{
    validate_lhs_not_ooz(z);
    if (ltree_add_rec_dynaddr(z->zone, z->lhs_dname, z->rhs_dyn, z->ttl, z->ttl_min))
        siglongjmp(z->jbuf, 1);
}

F_NONNULL
static void rec_dync(zscan_t* z)
{
    validate_lhs_not_ooz(z);
    if (ltree_add_rec_dync(z->zone, z->lhs_dname, z->rhs_dyn, z->ttl, z->ttl_min))
        siglongjmp(z->jbuf, 1);
}

F_NONNULL
static void rec_rfc3597(zscan_t* z)
{
    if (z->rfc3597_data_written < z->rfc3597_data_len)
        parse_error("RFC3597 generic RR claimed rdata length of %u, but only %u bytes of data present", z->rfc3597_data_len, z->rfc3597_data_written);
    validate_lhs_not_ooz(z);
    if (ltree_add_rec_rfc3597(z->zone, z->lhs_dname, z->uv_1, z->ttl, z->rfc3597_data_len, z->rfc3597_data))
        siglongjmp(z->jbuf, 1);
    z->rfc3597_data = NULL;
}

F_NONNULL
static void rec_caa(zscan_t* z)
{
    if (z->uval > 255)
        parse_error("CAA flags byte value %u is >255", z->uval);

    validate_lhs_not_ooz(z);

    const unsigned prop_len = strlen(z->caa_prop);
    gdnsd_assert(prop_len < 256); // parser-enforced
    const unsigned value_len = z->text_len;
    const unsigned total_len = 2 + prop_len + value_len;

    uint8_t* caa_rdata = xmalloc(total_len);
    uint8_t* caa_write = caa_rdata;
    *caa_write++ = z->uval;
    *caa_write++ = prop_len;
    memcpy(caa_write, z->caa_prop, prop_len);
    caa_write += prop_len;
    memcpy(caa_write, z->text, value_len);

    if (ltree_add_rec_rfc3597(z->zone, z->lhs_dname, 257, z->ttl, total_len, caa_rdata)) {
        free(caa_rdata);
        siglongjmp(z->jbuf, 1);
    }
    text_cleanup(z);
}

F_NONNULL
static void rfc3597_data_setup(zscan_t* z)
{
    z->rfc3597_data_len = z->uval;
    z->rfc3597_data_written = 0;
    z->rfc3597_data = xmalloc(z->uval);
}

F_NONNULL
static void rfc3597_octet(zscan_t* z)
{
    if (z->rfc3597_data_written == z->rfc3597_data_len)
        parse_error_noargs("RFC3597 generic RR: more rdata is present than the indicated length");
    z->rfc3597_data[z->rfc3597_data_written++] = hexbyte(z->tstart);
}

// The external entrypoint to the parser
bool zscan_rfc1035(zone_t* zone, const char* fn)
{
    gdnsd_assert(zone->dname);
    return zscan_do(zone, zone->dname, fn, gcfg->zones_default_ttl);
}

// This pre-processor does two important things that vastly simplify the real
// ragel parser:
// 1) Gets rid of all comments, replacing their characters with spaces so that
//    they're just seen as excessive whitespace.  Technically we only needed
//    to strip comments for the () case below, which is the complicated one
//    for ragel, but since we're doing it anyways it seemed simpler to do
//    universally and take comment-handling out of ragel as well.
// 2) Gets rid of all awful rfc1035 () line continuation, replacing the
//    parentheses themselves with spaces, and replacing any embedded newlines
//    with the formfeed character \f (which the ragel parser treats as
//    whitespace, but also knows to increment linecount on these so that error
//    reporting still shows the correct line number).

#define preproc_err(_msg) \
    do {\
        log_err("rfc1035: Zone %s: Zonefile preprocessing error at file %s line %zu: " _msg, logf_dname(z->zone->dname), z->curfn, line_num);\
        siglongjmp(z->jbuf, 1);\
    } while (0)

F_NONNULL
static void preprocess_buf(zscan_t* z, char* buf, const size_t buflen)
{
    // This is validated with a user-facing error before calling this function!
    gdnsd_assert(buf[buflen - 1] == '\n');

    bool in_quotes = false;
    bool in_parens = false;
    size_t line_num = 1;
    for (size_t i = 0; i < buflen; i++) {
        switch (buf[i]) {
        case '\n':
            line_num++;
            // In parens, replace \n with \f.  The ragel parser treats \f as
            // whitespace but knows to increment the line count so that error
            // reports are sane, while true unescaped \n terminates records.
            if (in_parens && !in_quotes)
                buf[i] = '\f';
            break;
        case ';':
            if (!in_quotes) {
                // Note we don't check i < buflen while advancing here, because
                // there's a check that the final character of the buffer must
                // be '\n' before the preprocessor is even invoked, which is
                // re-asserted at the top of this function.
                do {
                    buf[i++] = ' ';
                } while (buf[i] != '\n');
                line_num++;
                if (in_parens)
                    buf[i] = '\f';
            }
            break;
        case '"':
            in_quotes = !in_quotes;
            break;
        case '(':
            if (!in_quotes) {
                if (in_parens)
                    preproc_err("Parentheses double-opened");
                in_parens = true;
                buf[i] = ' ';
            }
            break;
        case ')':
            if (!in_quotes) {
                if (!in_parens)
                    preproc_err("Parentheses double-closed");
                in_parens = false;
                buf[i] = ' ';
            }
            break;
        case '\\':
            // Skip one escaped char.  Note 3-digit escapes exist as well, but
            // we're only concerned here with escaping of metachars, so it
            // turns out we don't have to track for the 3-digit escapes here.
            // We do have to keep the line count accurate in the case of an
            // escaped newline, though.
            if (buf[++i] == '\n')
                line_num++;
            break;
        case '\f':
            // Because \f is a special metachar for our ()-handling
            if (!in_quotes)
                preproc_err("Literal formfeed character not allowed in unquoted text: please escape it!");
            break;
        default:
            break;
        }
    }

    if (in_quotes)
        preproc_err("Unterminated open double-quote at EOF");
    if (in_parens)
        preproc_err("Unterminated open parentheses at EOF");
}

// *INDENT-OFF*
// start-sonar-exclude

#line 849 "src/zscan_rfc1035.c"
static const int zone_start = 405;
static const int zone_first_final = 405;
static const int zone_error = 0;

static const int zone_en_main = 405;


#line 1051 "./src/zscan_rfc1035.rl"

// end-sonar-exclude

F_NONNULL
static void scanner(zscan_t* z, char* buf, const size_t bufsize)
{
    gdnsd_assert(bufsize);

    // This avoids the unfortunately common case of files with final lines
    //   that are unterminated by bailing out early.  This also incidentally
    //   but importantly protects from set_uval()'s strtoul running off the
    //   end of the buffer if we were parsing an integer at that point.
    if (buf[bufsize - 1] != '\n') {
        parse_error_noargs("No newline at end of file");
        return;
    }

    // Undo parentheses braindamage before real parsing
    preprocess_buf(z, buf, bufsize);

    (void)zone_en_main; // silence unused var warning from generated code

    int cs = zone_start;

    GDNSD_DIAG_PUSH_IGNORED("-Wswitch-default")
    GDNSD_DIAG_PUSH_IGNORED("-Wimplicit-fallthrough")
// start-sonar-exclude
#ifndef __clang_analyzer__
    // ^ ... because the ragel-generated code for the zonefile parser is
    //   so huge that it makes analyzer runs take forever.
    const char* p = buf;
    const char* pe = buf + bufsize;
    const char* eof = pe;
    
#line 892 "src/zscan_rfc1035.c"
	{
	if ( p == pe )
		goto _test_eof;
	switch ( cs )
	{
case 405:
	switch( (*p) ) {
		case 9: goto st12;
		case 10: goto st406;
		case 12: goto st13;
		case 32: goto st12;
		case 34: goto tr1027;
		case 36: goto st325;
		case 59: goto st0;
		case 92: goto tr1029;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr1026;
tr1026:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st1;
tr991:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st1;
tr1030:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st1;
st1:
	if ( ++p == pe )
		goto _test_eof1;
case 1:
#line 930 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr1;
		case 10: goto st0;
		case 12: goto tr3;
		case 32: goto tr1;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto st385;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto st1;
tr1:
#line 851 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->lhs_dname, p - z->tstart, true); }
	goto st2;
tr17:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st2;
tr845:
#line 852 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->lhs_dname, p - z->tstart - 1, true); }
	goto st2;
tr992:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 851 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->lhs_dname, p - z->tstart, true); }
	goto st2;
st2:
	if ( ++p == pe )
		goto _test_eof2;
case 2:
#line 965 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st2;
		case 12: goto st3;
		case 32: goto st2;
		case 65: goto tr8;
		case 67: goto tr9;
		case 68: goto tr10;
		case 73: goto tr11;
		case 77: goto tr12;
		case 78: goto tr13;
		case 80: goto tr14;
		case 83: goto tr15;
		case 84: goto tr16;
		case 97: goto tr8;
		case 99: goto tr9;
		case 100: goto tr10;
		case 105: goto tr11;
		case 109: goto tr12;
		case 110: goto tr13;
		case 112: goto tr14;
		case 115: goto tr15;
		case 116: goto tr16;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr7;
	goto st0;
st0:
cs = 0;
	goto _out;
tr3:
#line 851 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->lhs_dname, p - z->tstart, true); }
	goto st3;
tr18:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st3;
tr846:
#line 852 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->lhs_dname, p - z->tstart - 1, true); }
	goto st3;
tr993:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 851 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->lhs_dname, p - z->tstart, true); }
	goto st3;
st3:
	if ( ++p == pe )
		goto _test_eof3;
case 3:
#line 1017 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr17;
		case 12: goto tr18;
		case 32: goto tr17;
		case 65: goto tr20;
		case 67: goto tr21;
		case 68: goto tr22;
		case 73: goto tr23;
		case 77: goto tr24;
		case 78: goto tr25;
		case 80: goto tr26;
		case 83: goto tr27;
		case 84: goto tr28;
		case 97: goto tr20;
		case 99: goto tr21;
		case 100: goto tr22;
		case 105: goto tr23;
		case 109: goto tr24;
		case 110: goto tr25;
		case 112: goto tr26;
		case 115: goto tr27;
		case 116: goto tr28;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr19;
	goto st0;
tr7:
#line 885 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
#line 886 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; z->ttl_min = z->def_ttl >> 1; z->uv_2 = 0; }
	goto st4;
tr19:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 885 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
#line 886 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; z->ttl_min = z->def_ttl >> 1; z->uv_2 = 0; }
	goto st4;
st4:
	if ( ++p == pe )
		goto _test_eof4;
case 4:
#line 1066 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr29;
		case 12: goto tr30;
		case 32: goto tr29;
		case 47: goto tr31;
		case 68: goto tr33;
		case 72: goto tr33;
		case 77: goto tr33;
		case 87: goto tr33;
		case 100: goto tr33;
		case 104: goto tr33;
		case 109: goto tr33;
		case 119: goto tr33;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st4;
	goto st0;
tr45:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st5;
tr29:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 882 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uval; }
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
#line 883 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uv_1; z->ttl_min = z->uv_2 ? z->uv_2 : z->uv_1 >> 1; }
	goto st5;
tr1023:
#line 882 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uval; }
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
#line 883 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uv_1; z->ttl_min = z->uv_2 ? z->uv_2 : z->uv_1 >> 1; }
	goto st5;
st5:
	if ( ++p == pe )
		goto _test_eof5;
case 5:
#line 1110 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st5;
		case 12: goto st6;
		case 32: goto st5;
		case 65: goto st7;
		case 67: goto st14;
		case 68: goto st54;
		case 73: goto st395;
		case 77: goto st92;
		case 78: goto st110;
		case 80: goto st187;
		case 83: goto st203;
		case 84: goto st276;
		case 97: goto st7;
		case 99: goto st14;
		case 100: goto st54;
		case 105: goto st395;
		case 109: goto st92;
		case 110: goto st110;
		case 112: goto st187;
		case 115: goto st203;
		case 116: goto st276;
	}
	goto st0;
tr46:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st6;
tr30:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 882 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uval; }
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
#line 883 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uv_1; z->ttl_min = z->uv_2 ? z->uv_2 : z->uv_1 >> 1; }
	goto st6;
tr1024:
#line 882 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uval; }
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
#line 883 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uv_1; z->ttl_min = z->uv_2 ? z->uv_2 : z->uv_1 >> 1; }
	goto st6;
st6:
	if ( ++p == pe )
		goto _test_eof6;
case 6:
#line 1161 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr45;
		case 12: goto tr46;
		case 32: goto tr45;
		case 65: goto tr47;
		case 67: goto tr48;
		case 68: goto tr49;
		case 73: goto tr50;
		case 77: goto tr51;
		case 78: goto tr52;
		case 80: goto tr53;
		case 83: goto tr54;
		case 84: goto tr55;
		case 97: goto tr47;
		case 99: goto tr48;
		case 100: goto tr49;
		case 105: goto tr50;
		case 109: goto tr51;
		case 110: goto tr52;
		case 112: goto tr53;
		case 115: goto tr54;
		case 116: goto tr55;
	}
	goto st0;
tr8:
#line 885 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; }
	goto st7;
tr47:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st7;
tr20:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 885 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; }
	goto st7;
st7:
	if ( ++p == pe )
		goto _test_eof7;
case 7:
#line 1204 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st8;
		case 12: goto st9;
		case 32: goto st8;
		case 65: goto st389;
		case 97: goto st389;
	}
	goto st0;
tr60:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st8;
st8:
	if ( ++p == pe )
		goto _test_eof8;
case 8:
#line 1221 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st8;
		case 12: goto st9;
		case 32: goto st8;
		case 46: goto tr59;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr59;
	goto st0;
tr61:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st9;
st9:
	if ( ++p == pe )
		goto _test_eof9;
case 9:
#line 1239 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr60;
		case 12: goto tr61;
		case 32: goto tr60;
		case 46: goto tr62;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr62;
	goto st0;
tr59:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st10;
tr62:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st10;
st10:
	if ( ++p == pe )
		goto _test_eof10;
case 10:
#line 1263 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr63;
		case 10: goto tr64;
		case 12: goto tr65;
		case 32: goto tr63;
		case 46: goto st10;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st10;
	goto st0;
tr106:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st11;
tr63:
#line 877 "./src/zscan_rfc1035.rl"
	{ set_ipv4(z, p); }
#line 897 "./src/zscan_rfc1035.rl"
	{ rec_a(z); }
	goto st11;
tr102:
#line 874 "./src/zscan_rfc1035.rl"
	{ text_add_tok_huge(z, p - z->tstart); }
#line 909 "./src/zscan_rfc1035.rl"
	{ rec_caa(z); }
	goto st11;
tr111:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 874 "./src/zscan_rfc1035.rl"
	{ text_add_tok_huge(z, p - z->tstart); }
#line 909 "./src/zscan_rfc1035.rl"
	{ rec_caa(z); }
	goto st11;
tr129:
#line 875 "./src/zscan_rfc1035.rl"
	{ z->tstart++; text_add_tok_huge(z, p - z->tstart - 1); }
#line 909 "./src/zscan_rfc1035.rl"
	{ rec_caa(z); }
	goto st11;
tr143:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 900 "./src/zscan_rfc1035.rl"
	{ rec_cname(z); }
	goto st11;
tr150:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 900 "./src/zscan_rfc1035.rl"
	{ rec_cname(z); }
	goto st11;
tr168:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 900 "./src/zscan_rfc1035.rl"
	{ rec_cname(z); }
	goto st11;
tr182:
#line 893 "./src/zscan_rfc1035.rl"
	{ set_dyna(z, p); }
#line 906 "./src/zscan_rfc1035.rl"
	{ rec_dyna(z); }
	goto st11;
tr192:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 893 "./src/zscan_rfc1035.rl"
	{ set_dyna(z, p); }
#line 906 "./src/zscan_rfc1035.rl"
	{ rec_dyna(z); }
	goto st11;
tr212:
#line 893 "./src/zscan_rfc1035.rl"
	{ set_dyna(z, p); }
#line 907 "./src/zscan_rfc1035.rl"
	{ rec_dync(z); }
	goto st11;
tr222:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 893 "./src/zscan_rfc1035.rl"
	{ set_dyna(z, p); }
#line 907 "./src/zscan_rfc1035.rl"
	{ rec_dync(z); }
	goto st11;
tr269:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 902 "./src/zscan_rfc1035.rl"
	{ rec_mx(z); }
	goto st11;
tr276:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 902 "./src/zscan_rfc1035.rl"
	{ rec_mx(z); }
	goto st11;
tr294:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 902 "./src/zscan_rfc1035.rl"
	{ rec_mx(z); }
	goto st11;
tr355:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 904 "./src/zscan_rfc1035.rl"
	{ rec_naptr(z); }
	goto st11;
tr362:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 904 "./src/zscan_rfc1035.rl"
	{ rec_naptr(z); }
	goto st11;
tr380:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 904 "./src/zscan_rfc1035.rl"
	{ rec_naptr(z); }
	goto st11;
tr463:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 899 "./src/zscan_rfc1035.rl"
	{ rec_ns(z); }
	goto st11;
tr470:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 899 "./src/zscan_rfc1035.rl"
	{ rec_ns(z); }
	goto st11;
tr488:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 899 "./src/zscan_rfc1035.rl"
	{ rec_ns(z); }
	goto st11;
tr501:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 901 "./src/zscan_rfc1035.rl"
	{ rec_ptr(z); }
	goto st11;
tr508:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 901 "./src/zscan_rfc1035.rl"
	{ rec_ptr(z); }
	goto st11;
tr526:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 901 "./src/zscan_rfc1035.rl"
	{ rec_ptr(z); }
	goto st11;
tr598:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 891 "./src/zscan_rfc1035.rl"
	{ z->uv_5 = z->uval; }
#line 896 "./src/zscan_rfc1035.rl"
	{ rec_soa(z); }
	goto st11;
tr603:
#line 891 "./src/zscan_rfc1035.rl"
	{ z->uv_5 = z->uval; }
#line 896 "./src/zscan_rfc1035.rl"
	{ rec_soa(z); }
	goto st11;
tr696:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 903 "./src/zscan_rfc1035.rl"
	{ rec_srv(z); }
	goto st11;
tr703:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 903 "./src/zscan_rfc1035.rl"
	{ rec_srv(z); }
	goto st11;
tr721:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 903 "./src/zscan_rfc1035.rl"
	{ rec_srv(z); }
	goto st11;
tr876:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 867 "./src/zscan_rfc1035.rl"
	{ process_include(z); }
	goto st11;
tr883:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 867 "./src/zscan_rfc1035.rl"
	{ process_include(z); }
	goto st11;
tr901:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 867 "./src/zscan_rfc1035.rl"
	{ process_include(z); }
	goto st11;
tr943:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 860 "./src/zscan_rfc1035.rl"
	{
        validate_origin_in_zone(z, z->rhs_dname);
        dname_copy(z->origin, z->rhs_dname);
    }
	goto st11;
tr950:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 860 "./src/zscan_rfc1035.rl"
	{
        validate_origin_in_zone(z, z->rhs_dname);
        dname_copy(z->origin, z->rhs_dname);
    }
	goto st11;
tr968:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 860 "./src/zscan_rfc1035.rl"
	{
        validate_origin_in_zone(z, z->rhs_dname);
        dname_copy(z->origin, z->rhs_dname);
    }
	goto st11;
tr981:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 884 "./src/zscan_rfc1035.rl"
	{ z->def_ttl = z->uval; }
	goto st11;
tr986:
#line 884 "./src/zscan_rfc1035.rl"
	{ z->def_ttl = z->uval; }
	goto st11;
tr1004:
#line 878 "./src/zscan_rfc1035.rl"
	{ set_ipv6(z, p); }
#line 898 "./src/zscan_rfc1035.rl"
	{ rec_aaaa(z); }
	goto st11;
st11:
	if ( ++p == pe )
		goto _test_eof11;
case 11:
#line 1535 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st11;
		case 10: goto st406;
		case 12: goto st25;
		case 32: goto st11;
	}
	goto st0;
tr73:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st406;
tr64:
#line 877 "./src/zscan_rfc1035.rl"
	{ set_ipv4(z, p); }
#line 897 "./src/zscan_rfc1035.rl"
	{ rec_a(z); }
	goto st406;
tr103:
#line 874 "./src/zscan_rfc1035.rl"
	{ text_add_tok_huge(z, p - z->tstart); }
#line 909 "./src/zscan_rfc1035.rl"
	{ rec_caa(z); }
	goto st406;
tr1032:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st406;
tr112:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 874 "./src/zscan_rfc1035.rl"
	{ text_add_tok_huge(z, p - z->tstart); }
#line 909 "./src/zscan_rfc1035.rl"
	{ rec_caa(z); }
	goto st406;
tr130:
#line 875 "./src/zscan_rfc1035.rl"
	{ z->tstart++; text_add_tok_huge(z, p - z->tstart - 1); }
#line 909 "./src/zscan_rfc1035.rl"
	{ rec_caa(z); }
	goto st406;
tr144:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 900 "./src/zscan_rfc1035.rl"
	{ rec_cname(z); }
	goto st406;
tr151:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 900 "./src/zscan_rfc1035.rl"
	{ rec_cname(z); }
	goto st406;
tr169:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 900 "./src/zscan_rfc1035.rl"
	{ rec_cname(z); }
	goto st406;
tr183:
#line 893 "./src/zscan_rfc1035.rl"
	{ set_dyna(z, p); }
#line 906 "./src/zscan_rfc1035.rl"
	{ rec_dyna(z); }
	goto st406;
tr193:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 893 "./src/zscan_rfc1035.rl"
	{ set_dyna(z, p); }
#line 906 "./src/zscan_rfc1035.rl"
	{ rec_dyna(z); }
	goto st406;
tr213:
#line 893 "./src/zscan_rfc1035.rl"
	{ set_dyna(z, p); }
#line 907 "./src/zscan_rfc1035.rl"
	{ rec_dync(z); }
	goto st406;
tr223:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 893 "./src/zscan_rfc1035.rl"
	{ set_dyna(z, p); }
#line 907 "./src/zscan_rfc1035.rl"
	{ rec_dync(z); }
	goto st406;
tr270:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 902 "./src/zscan_rfc1035.rl"
	{ rec_mx(z); }
	goto st406;
tr277:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 902 "./src/zscan_rfc1035.rl"
	{ rec_mx(z); }
	goto st406;
tr295:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 902 "./src/zscan_rfc1035.rl"
	{ rec_mx(z); }
	goto st406;
tr356:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 904 "./src/zscan_rfc1035.rl"
	{ rec_naptr(z); }
	goto st406;
tr363:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 904 "./src/zscan_rfc1035.rl"
	{ rec_naptr(z); }
	goto st406;
tr381:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 904 "./src/zscan_rfc1035.rl"
	{ rec_naptr(z); }
	goto st406;
tr464:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 899 "./src/zscan_rfc1035.rl"
	{ rec_ns(z); }
	goto st406;
tr471:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 899 "./src/zscan_rfc1035.rl"
	{ rec_ns(z); }
	goto st406;
tr489:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 899 "./src/zscan_rfc1035.rl"
	{ rec_ns(z); }
	goto st406;
tr502:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 901 "./src/zscan_rfc1035.rl"
	{ rec_ptr(z); }
	goto st406;
tr509:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 901 "./src/zscan_rfc1035.rl"
	{ rec_ptr(z); }
	goto st406;
tr527:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 901 "./src/zscan_rfc1035.rl"
	{ rec_ptr(z); }
	goto st406;
tr599:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 891 "./src/zscan_rfc1035.rl"
	{ z->uv_5 = z->uval; }
#line 896 "./src/zscan_rfc1035.rl"
	{ rec_soa(z); }
	goto st406;
tr604:
#line 891 "./src/zscan_rfc1035.rl"
	{ z->uv_5 = z->uval; }
#line 896 "./src/zscan_rfc1035.rl"
	{ rec_soa(z); }
	goto st406;
tr697:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 903 "./src/zscan_rfc1035.rl"
	{ rec_srv(z); }
	goto st406;
tr704:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 903 "./src/zscan_rfc1035.rl"
	{ rec_srv(z); }
	goto st406;
tr722:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 903 "./src/zscan_rfc1035.rl"
	{ rec_srv(z); }
	goto st406;
tr738:
#line 870 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, true); }
#line 905 "./src/zscan_rfc1035.rl"
	{ rec_txt(z); }
	goto st406;
tr744:
#line 905 "./src/zscan_rfc1035.rl"
	{ rec_txt(z); }
	goto st406;
tr750:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 905 "./src/zscan_rfc1035.rl"
	{ rec_txt(z); }
	goto st406;
tr764:
#line 871 "./src/zscan_rfc1035.rl"
	{ z->tstart++; text_add_tok(z, p - z->tstart - 1, true); }
#line 905 "./src/zscan_rfc1035.rl"
	{ rec_txt(z); }
	goto st406;
tr772:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 870 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, true); }
#line 905 "./src/zscan_rfc1035.rl"
	{ rec_txt(z); }
	goto st406;
tr807:
#line 908 "./src/zscan_rfc1035.rl"
	{ rec_rfc3597(z); }
	goto st406;
tr811:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 908 "./src/zscan_rfc1035.rl"
	{ rec_rfc3597(z); }
	goto st406;
tr816:
#line 912 "./src/zscan_rfc1035.rl"
	{ rfc3597_octet(z); }
#line 908 "./src/zscan_rfc1035.rl"
	{ rec_rfc3597(z); }
	goto st406;
tr867:
#line 865 "./src/zscan_rfc1035.rl"
	{ set_filename(z, p - z->tstart); }
#line 867 "./src/zscan_rfc1035.rl"
	{ process_include(z); }
	goto st406;
tr877:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 867 "./src/zscan_rfc1035.rl"
	{ process_include(z); }
	goto st406;
tr884:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 867 "./src/zscan_rfc1035.rl"
	{ process_include(z); }
	goto st406;
tr902:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 867 "./src/zscan_rfc1035.rl"
	{ process_include(z); }
	goto st406;
tr910:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 865 "./src/zscan_rfc1035.rl"
	{ set_filename(z, p - z->tstart); }
#line 867 "./src/zscan_rfc1035.rl"
	{ process_include(z); }
	goto st406;
tr928:
#line 866 "./src/zscan_rfc1035.rl"
	{ z->tstart++; set_filename(z, p - z->tstart - 1); }
#line 867 "./src/zscan_rfc1035.rl"
	{ process_include(z); }
	goto st406;
tr944:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 860 "./src/zscan_rfc1035.rl"
	{
        validate_origin_in_zone(z, z->rhs_dname);
        dname_copy(z->origin, z->rhs_dname);
    }
	goto st406;
tr951:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 860 "./src/zscan_rfc1035.rl"
	{
        validate_origin_in_zone(z, z->rhs_dname);
        dname_copy(z->origin, z->rhs_dname);
    }
	goto st406;
tr969:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 860 "./src/zscan_rfc1035.rl"
	{
        validate_origin_in_zone(z, z->rhs_dname);
        dname_copy(z->origin, z->rhs_dname);
    }
	goto st406;
tr982:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 884 "./src/zscan_rfc1035.rl"
	{ z->def_ttl = z->uval; }
	goto st406;
tr987:
#line 884 "./src/zscan_rfc1035.rl"
	{ z->def_ttl = z->uval; }
	goto st406;
tr1005:
#line 878 "./src/zscan_rfc1035.rl"
	{ set_ipv6(z, p); }
#line 898 "./src/zscan_rfc1035.rl"
	{ rec_aaaa(z); }
	goto st406;
st406:
	if ( ++p == pe )
		goto _test_eof406;
case 406:
#line 1874 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr1031;
		case 10: goto tr1032;
		case 12: goto tr1033;
		case 32: goto tr1031;
		case 34: goto tr1034;
		case 36: goto tr1035;
		case 59: goto st0;
		case 92: goto tr1036;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr1030;
tr72:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st12;
tr1031:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st12;
st12:
	if ( ++p == pe )
		goto _test_eof12;
case 12:
#line 1900 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st12;
		case 10: goto st406;
		case 12: goto st13;
		case 32: goto st12;
		case 65: goto tr8;
		case 67: goto tr9;
		case 68: goto tr10;
		case 73: goto tr11;
		case 77: goto tr12;
		case 78: goto tr13;
		case 80: goto tr14;
		case 83: goto tr15;
		case 84: goto tr16;
		case 97: goto tr8;
		case 99: goto tr9;
		case 100: goto tr10;
		case 105: goto tr11;
		case 109: goto tr12;
		case 110: goto tr13;
		case 112: goto tr14;
		case 115: goto tr15;
		case 116: goto tr16;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr7;
	goto st0;
tr74:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st13;
tr1033:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st13;
st13:
	if ( ++p == pe )
		goto _test_eof13;
case 13:
#line 1940 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr72;
		case 10: goto tr73;
		case 12: goto tr74;
		case 32: goto tr72;
		case 65: goto tr20;
		case 67: goto tr21;
		case 68: goto tr22;
		case 73: goto tr23;
		case 77: goto tr24;
		case 78: goto tr25;
		case 80: goto tr26;
		case 83: goto tr27;
		case 84: goto tr28;
		case 97: goto tr20;
		case 99: goto tr21;
		case 100: goto tr22;
		case 105: goto tr23;
		case 109: goto tr24;
		case 110: goto tr25;
		case 112: goto tr26;
		case 115: goto tr27;
		case 116: goto tr28;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr19;
	goto st0;
tr9:
#line 885 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; }
	goto st14;
tr48:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st14;
tr21:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 885 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; }
	goto st14;
st14:
	if ( ++p == pe )
		goto _test_eof14;
case 14:
#line 1986 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 65: goto st15;
		case 78: goto st37;
		case 97: goto st15;
		case 110: goto st37;
	}
	goto st0;
st15:
	if ( ++p == pe )
		goto _test_eof15;
case 15:
	switch( (*p) ) {
		case 65: goto st16;
		case 97: goto st16;
	}
	goto st0;
st16:
	if ( ++p == pe )
		goto _test_eof16;
case 16:
	switch( (*p) ) {
		case 9: goto st17;
		case 12: goto st18;
		case 32: goto st17;
	}
	goto st0;
tr81:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st17;
st17:
	if ( ++p == pe )
		goto _test_eof17;
case 17:
#line 2021 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st17;
		case 12: goto st18;
		case 32: goto st17;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr80;
	goto st0;
tr82:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st18;
st18:
	if ( ++p == pe )
		goto _test_eof18;
case 18:
#line 2038 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr81;
		case 12: goto tr82;
		case 32: goto tr81;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr83;
	goto st0;
tr80:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st19;
tr83:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st19;
st19:
	if ( ++p == pe )
		goto _test_eof19;
case 19:
#line 2061 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr84;
		case 12: goto tr85;
		case 32: goto tr84;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st19;
	goto st0;
tr90:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st20;
tr84:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
	goto st20;
st20:
	if ( ++p == pe )
		goto _test_eof20;
case 20:
#line 2082 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st20;
		case 12: goto st21;
		case 32: goto st20;
	}
	if ( (*p) < 65 ) {
		if ( 48 <= (*p) && (*p) <= 57 )
			goto tr89;
	} else if ( (*p) > 90 ) {
		if ( 97 <= (*p) && (*p) <= 122 )
			goto tr89;
	} else
		goto tr89;
	goto st0;
tr91:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st21;
tr85:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
	goto st21;
st21:
	if ( ++p == pe )
		goto _test_eof21;
case 21:
#line 2109 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr90;
		case 12: goto tr91;
		case 32: goto tr90;
	}
	if ( (*p) < 65 ) {
		if ( 48 <= (*p) && (*p) <= 57 )
			goto tr92;
	} else if ( (*p) > 90 ) {
		if ( 97 <= (*p) && (*p) <= 122 )
			goto tr92;
	} else
		goto tr92;
	goto st0;
tr89:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st22;
tr92:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st22;
st22:
	if ( ++p == pe )
		goto _test_eof22;
case 22:
#line 2138 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr93;
		case 12: goto tr94;
		case 32: goto tr93;
	}
	if ( (*p) < 65 ) {
		if ( 48 <= (*p) && (*p) <= 57 )
			goto st22;
	} else if ( (*p) > 90 ) {
		if ( 97 <= (*p) && (*p) <= 122 )
			goto st22;
	} else
		goto st22;
	goto st0;
tr117:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st23;
tr93:
#line 894 "./src/zscan_rfc1035.rl"
	{ set_caa_prop(z, p); }
	goto st23;
st23:
	if ( ++p == pe )
		goto _test_eof23;
case 23:
#line 2165 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st23;
		case 10: goto st0;
		case 12: goto st30;
		case 32: goto st23;
		case 34: goto tr99;
		case 59: goto st0;
		case 92: goto tr100;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr96;
tr96:
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st24;
tr110:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st24;
tr116:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st24;
st24:
	if ( ++p == pe )
		goto _test_eof24;
case 24:
#line 2200 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr102;
		case 10: goto tr103;
		case 12: goto tr104;
		case 32: goto tr102;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto st26;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto st24;
tr107:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st25;
tr65:
#line 877 "./src/zscan_rfc1035.rl"
	{ set_ipv4(z, p); }
#line 897 "./src/zscan_rfc1035.rl"
	{ rec_a(z); }
	goto st25;
tr104:
#line 874 "./src/zscan_rfc1035.rl"
	{ text_add_tok_huge(z, p - z->tstart); }
#line 909 "./src/zscan_rfc1035.rl"
	{ rec_caa(z); }
	goto st25;
tr113:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 874 "./src/zscan_rfc1035.rl"
	{ text_add_tok_huge(z, p - z->tstart); }
#line 909 "./src/zscan_rfc1035.rl"
	{ rec_caa(z); }
	goto st25;
tr131:
#line 875 "./src/zscan_rfc1035.rl"
	{ z->tstart++; text_add_tok_huge(z, p - z->tstart - 1); }
#line 909 "./src/zscan_rfc1035.rl"
	{ rec_caa(z); }
	goto st25;
tr145:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 900 "./src/zscan_rfc1035.rl"
	{ rec_cname(z); }
	goto st25;
tr152:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 900 "./src/zscan_rfc1035.rl"
	{ rec_cname(z); }
	goto st25;
tr170:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 900 "./src/zscan_rfc1035.rl"
	{ rec_cname(z); }
	goto st25;
tr184:
#line 893 "./src/zscan_rfc1035.rl"
	{ set_dyna(z, p); }
#line 906 "./src/zscan_rfc1035.rl"
	{ rec_dyna(z); }
	goto st25;
tr194:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 893 "./src/zscan_rfc1035.rl"
	{ set_dyna(z, p); }
#line 906 "./src/zscan_rfc1035.rl"
	{ rec_dyna(z); }
	goto st25;
tr214:
#line 893 "./src/zscan_rfc1035.rl"
	{ set_dyna(z, p); }
#line 907 "./src/zscan_rfc1035.rl"
	{ rec_dync(z); }
	goto st25;
tr224:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 893 "./src/zscan_rfc1035.rl"
	{ set_dyna(z, p); }
#line 907 "./src/zscan_rfc1035.rl"
	{ rec_dync(z); }
	goto st25;
tr271:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 902 "./src/zscan_rfc1035.rl"
	{ rec_mx(z); }
	goto st25;
tr278:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 902 "./src/zscan_rfc1035.rl"
	{ rec_mx(z); }
	goto st25;
tr296:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 902 "./src/zscan_rfc1035.rl"
	{ rec_mx(z); }
	goto st25;
tr357:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 904 "./src/zscan_rfc1035.rl"
	{ rec_naptr(z); }
	goto st25;
tr364:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 904 "./src/zscan_rfc1035.rl"
	{ rec_naptr(z); }
	goto st25;
tr382:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 904 "./src/zscan_rfc1035.rl"
	{ rec_naptr(z); }
	goto st25;
tr465:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 899 "./src/zscan_rfc1035.rl"
	{ rec_ns(z); }
	goto st25;
tr472:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 899 "./src/zscan_rfc1035.rl"
	{ rec_ns(z); }
	goto st25;
tr490:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 899 "./src/zscan_rfc1035.rl"
	{ rec_ns(z); }
	goto st25;
tr503:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 901 "./src/zscan_rfc1035.rl"
	{ rec_ptr(z); }
	goto st25;
tr510:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 901 "./src/zscan_rfc1035.rl"
	{ rec_ptr(z); }
	goto st25;
tr528:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 901 "./src/zscan_rfc1035.rl"
	{ rec_ptr(z); }
	goto st25;
tr600:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 891 "./src/zscan_rfc1035.rl"
	{ z->uv_5 = z->uval; }
#line 896 "./src/zscan_rfc1035.rl"
	{ rec_soa(z); }
	goto st25;
tr605:
#line 891 "./src/zscan_rfc1035.rl"
	{ z->uv_5 = z->uval; }
#line 896 "./src/zscan_rfc1035.rl"
	{ rec_soa(z); }
	goto st25;
tr698:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 903 "./src/zscan_rfc1035.rl"
	{ rec_srv(z); }
	goto st25;
tr705:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 903 "./src/zscan_rfc1035.rl"
	{ rec_srv(z); }
	goto st25;
tr723:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 903 "./src/zscan_rfc1035.rl"
	{ rec_srv(z); }
	goto st25;
tr878:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 867 "./src/zscan_rfc1035.rl"
	{ process_include(z); }
	goto st25;
tr885:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 867 "./src/zscan_rfc1035.rl"
	{ process_include(z); }
	goto st25;
tr903:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 867 "./src/zscan_rfc1035.rl"
	{ process_include(z); }
	goto st25;
tr945:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 860 "./src/zscan_rfc1035.rl"
	{
        validate_origin_in_zone(z, z->rhs_dname);
        dname_copy(z->origin, z->rhs_dname);
    }
	goto st25;
tr952:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
#line 860 "./src/zscan_rfc1035.rl"
	{
        validate_origin_in_zone(z, z->rhs_dname);
        dname_copy(z->origin, z->rhs_dname);
    }
	goto st25;
tr970:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
#line 860 "./src/zscan_rfc1035.rl"
	{
        validate_origin_in_zone(z, z->rhs_dname);
        dname_copy(z->origin, z->rhs_dname);
    }
	goto st25;
tr983:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 884 "./src/zscan_rfc1035.rl"
	{ z->def_ttl = z->uval; }
	goto st25;
tr988:
#line 884 "./src/zscan_rfc1035.rl"
	{ z->def_ttl = z->uval; }
	goto st25;
tr1006:
#line 878 "./src/zscan_rfc1035.rl"
	{ set_ipv6(z, p); }
#line 898 "./src/zscan_rfc1035.rl"
	{ rec_aaaa(z); }
	goto st25;
st25:
	if ( ++p == pe )
		goto _test_eof25;
case 25:
#line 2474 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr106;
		case 10: goto tr73;
		case 12: goto tr107;
		case 32: goto tr106;
	}
	goto st0;
tr100:
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st26;
tr114:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st26;
tr120:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st26;
st26:
	if ( ++p == pe )
		goto _test_eof26;
case 26:
#line 2504 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st27;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st28;
	goto st24;
st27:
	if ( ++p == pe )
		goto _test_eof27;
case 27:
	switch( (*p) ) {
		case 9: goto tr111;
		case 10: goto tr112;
		case 12: goto tr113;
		case 32: goto tr111;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto tr114;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr110;
st28:
	if ( ++p == pe )
		goto _test_eof28;
case 28:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st29;
	goto st0;
st29:
	if ( ++p == pe )
		goto _test_eof29;
case 29:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st24;
	goto st0;
tr118:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st30;
tr94:
#line 894 "./src/zscan_rfc1035.rl"
	{ set_caa_prop(z, p); }
	goto st30;
st30:
	if ( ++p == pe )
		goto _test_eof30;
case 30:
#line 2552 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr117;
		case 10: goto st0;
		case 12: goto tr118;
		case 32: goto tr117;
		case 34: goto tr119;
		case 59: goto st0;
		case 92: goto tr120;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr116;
tr99:
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st31;
tr125:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st31;
tr119:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st31;
st31:
	if ( ++p == pe )
		goto _test_eof31;
case 31:
#line 2587 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto st32;
		case 34: goto st33;
		case 92: goto st34;
	}
	goto st31;
tr126:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st32;
st32:
	if ( ++p == pe )
		goto _test_eof32;
case 32:
#line 2602 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto tr126;
		case 34: goto tr127;
		case 92: goto tr128;
	}
	goto tr125;
tr127:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st33;
st33:
	if ( ++p == pe )
		goto _test_eof33;
case 33:
#line 2617 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr129;
		case 10: goto tr130;
		case 12: goto tr131;
		case 32: goto tr129;
	}
	goto st0;
tr128:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st34;
st34:
	if ( ++p == pe )
		goto _test_eof34;
case 34:
#line 2633 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st32;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st35;
	goto st31;
st35:
	if ( ++p == pe )
		goto _test_eof35;
case 35:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st36;
	goto st0;
st36:
	if ( ++p == pe )
		goto _test_eof36;
case 36:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st31;
	goto st0;
st37:
	if ( ++p == pe )
		goto _test_eof37;
case 37:
	switch( (*p) ) {
		case 65: goto st38;
		case 97: goto st38;
	}
	goto st0;
st38:
	if ( ++p == pe )
		goto _test_eof38;
case 38:
	switch( (*p) ) {
		case 77: goto st39;
		case 109: goto st39;
	}
	goto st0;
st39:
	if ( ++p == pe )
		goto _test_eof39;
case 39:
	switch( (*p) ) {
		case 69: goto st40;
		case 101: goto st40;
	}
	goto st0;
st40:
	if ( ++p == pe )
		goto _test_eof40;
case 40:
	switch( (*p) ) {
		case 9: goto st41;
		case 12: goto st47;
		case 32: goto st41;
	}
	goto st0;
tr156:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st41;
st41:
	if ( ++p == pe )
		goto _test_eof41;
case 41:
#line 2698 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st41;
		case 10: goto st0;
		case 12: goto st47;
		case 32: goto st41;
		case 34: goto tr140;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr141;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr139;
tr139:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st42;
tr155:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st42;
tr149:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st42;
st42:
	if ( ++p == pe )
		goto _test_eof42;
case 42:
#line 2730 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr143;
		case 10: goto tr144;
		case 12: goto tr145;
		case 32: goto tr143;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto st43;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto st42;
tr141:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st43;
tr159:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st43;
tr153:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st43;
st43:
	if ( ++p == pe )
		goto _test_eof43;
case 43:
#line 2761 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st44;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st45;
	goto st42;
st44:
	if ( ++p == pe )
		goto _test_eof44;
case 44:
	switch( (*p) ) {
		case 9: goto tr150;
		case 10: goto tr151;
		case 12: goto tr152;
		case 32: goto tr150;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto tr153;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr149;
st45:
	if ( ++p == pe )
		goto _test_eof45;
case 45:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st46;
	goto st0;
st46:
	if ( ++p == pe )
		goto _test_eof46;
case 46:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st42;
	goto st0;
tr157:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st47;
st47:
	if ( ++p == pe )
		goto _test_eof47;
case 47:
#line 2805 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr156;
		case 10: goto st0;
		case 12: goto tr157;
		case 32: goto tr156;
		case 34: goto tr158;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr159;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr155;
tr140:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st48;
tr158:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st48;
tr164:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st48;
st48:
	if ( ++p == pe )
		goto _test_eof48;
case 48:
#line 2837 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto st49;
		case 34: goto st50;
		case 92: goto st51;
	}
	goto st48;
tr165:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st49;
st49:
	if ( ++p == pe )
		goto _test_eof49;
case 49:
#line 2852 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto tr165;
		case 34: goto tr166;
		case 92: goto tr167;
	}
	goto tr164;
tr166:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st50;
st50:
	if ( ++p == pe )
		goto _test_eof50;
case 50:
#line 2867 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr168;
		case 10: goto tr169;
		case 12: goto tr170;
		case 32: goto tr168;
	}
	goto st0;
tr167:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st51;
st51:
	if ( ++p == pe )
		goto _test_eof51;
case 51:
#line 2883 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st49;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st52;
	goto st48;
st52:
	if ( ++p == pe )
		goto _test_eof52;
case 52:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st53;
	goto st0;
st53:
	if ( ++p == pe )
		goto _test_eof53;
case 53:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st48;
	goto st0;
tr10:
#line 886 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; z->ttl_min = z->def_ttl >> 1; z->uv_2 = 0; }
	goto st54;
tr49:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st54;
tr22:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 886 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; z->ttl_min = z->def_ttl >> 1; z->uv_2 = 0; }
	goto st54;
st54:
	if ( ++p == pe )
		goto _test_eof54;
case 54:
#line 2921 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 89: goto st55;
		case 121: goto st55;
	}
	goto st0;
st55:
	if ( ++p == pe )
		goto _test_eof55;
case 55:
	switch( (*p) ) {
		case 78: goto st56;
		case 110: goto st56;
	}
	goto st0;
st56:
	if ( ++p == pe )
		goto _test_eof56;
case 56:
	switch( (*p) ) {
		case 65: goto st57;
		case 67: goto st71;
		case 97: goto st57;
		case 99: goto st71;
	}
	goto st0;
st57:
	if ( ++p == pe )
		goto _test_eof57;
case 57:
	switch( (*p) ) {
		case 9: goto st58;
		case 12: goto st70;
		case 32: goto st58;
	}
	goto st0;
tr204:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st58;
st58:
	if ( ++p == pe )
		goto _test_eof58;
case 58:
#line 2965 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st58;
		case 10: goto st0;
		case 12: goto st70;
		case 32: goto st58;
		case 59: goto st0;
		case 92: goto tr180;
	}
	if ( (*p) > 34 ) {
		if ( 40 <= (*p) && (*p) <= 41 )
			goto st0;
	} else if ( (*p) >= 33 )
		goto st0;
	goto tr179;
tr179:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st59;
tr203:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st59;
tr199:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st59;
st59:
	if ( ++p == pe )
		goto _test_eof59;
case 59:
#line 2998 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr182;
		case 10: goto tr183;
		case 12: goto tr184;
		case 32: goto tr182;
		case 33: goto st60;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto st66;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto st59;
tr200:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st60;
st60:
	if ( ++p == pe )
		goto _test_eof60;
case 60:
#line 3020 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 12: goto st0;
		case 59: goto st0;
		case 92: goto st62;
	}
	if ( (*p) < 32 ) {
		if ( 9 <= (*p) && (*p) <= 10 )
			goto st0;
	} else if ( (*p) > 34 ) {
		if ( 40 <= (*p) && (*p) <= 41 )
			goto st0;
	} else
		goto st0;
	goto st61;
tr191:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st61;
st61:
	if ( ++p == pe )
		goto _test_eof61;
case 61:
#line 3043 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr182;
		case 10: goto tr183;
		case 12: goto tr184;
		case 32: goto tr182;
		case 59: goto st0;
		case 92: goto st62;
	}
	if ( (*p) > 34 ) {
		if ( 40 <= (*p) && (*p) <= 41 )
			goto st0;
	} else if ( (*p) >= 33 )
		goto st0;
	goto st61;
tr195:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st62;
st62:
	if ( ++p == pe )
		goto _test_eof62;
case 62:
#line 3066 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st63;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st64;
	goto st61;
st63:
	if ( ++p == pe )
		goto _test_eof63;
case 63:
	switch( (*p) ) {
		case 9: goto tr192;
		case 10: goto tr193;
		case 12: goto tr194;
		case 32: goto tr192;
		case 59: goto st0;
		case 92: goto tr195;
	}
	if ( (*p) > 34 ) {
		if ( 40 <= (*p) && (*p) <= 41 )
			goto st0;
	} else if ( (*p) >= 33 )
		goto st0;
	goto tr191;
st64:
	if ( ++p == pe )
		goto _test_eof64;
case 64:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st65;
	goto st0;
st65:
	if ( ++p == pe )
		goto _test_eof65;
case 65:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st61;
	goto st0;
tr180:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st66;
tr206:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st66;
tr201:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st66;
st66:
	if ( ++p == pe )
		goto _test_eof66;
case 66:
#line 3122 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st67;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st68;
	goto st59;
st67:
	if ( ++p == pe )
		goto _test_eof67;
case 67:
	switch( (*p) ) {
		case 9: goto tr192;
		case 10: goto tr193;
		case 12: goto tr194;
		case 32: goto tr192;
		case 33: goto tr200;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto tr201;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr199;
st68:
	if ( ++p == pe )
		goto _test_eof68;
case 68:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st69;
	goto st0;
st69:
	if ( ++p == pe )
		goto _test_eof69;
case 69:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st59;
	goto st0;
tr205:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st70;
st70:
	if ( ++p == pe )
		goto _test_eof70;
case 70:
#line 3167 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr204;
		case 10: goto st0;
		case 12: goto tr205;
		case 32: goto tr204;
		case 59: goto st0;
		case 92: goto tr206;
	}
	if ( (*p) > 34 ) {
		if ( 40 <= (*p) && (*p) <= 41 )
			goto st0;
	} else if ( (*p) >= 33 )
		goto st0;
	goto tr203;
st71:
	if ( ++p == pe )
		goto _test_eof71;
case 71:
	switch( (*p) ) {
		case 9: goto st72;
		case 12: goto st84;
		case 32: goto st72;
	}
	goto st0;
tr234:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st72;
st72:
	if ( ++p == pe )
		goto _test_eof72;
case 72:
#line 3200 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st72;
		case 10: goto st0;
		case 12: goto st84;
		case 32: goto st72;
		case 59: goto st0;
		case 92: goto tr210;
	}
	if ( (*p) > 34 ) {
		if ( 40 <= (*p) && (*p) <= 41 )
			goto st0;
	} else if ( (*p) >= 33 )
		goto st0;
	goto tr209;
tr209:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st73;
tr233:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st73;
tr229:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st73;
st73:
	if ( ++p == pe )
		goto _test_eof73;
case 73:
#line 3233 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr212;
		case 10: goto tr213;
		case 12: goto tr214;
		case 32: goto tr212;
		case 33: goto st74;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto st80;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto st73;
tr230:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st74;
st74:
	if ( ++p == pe )
		goto _test_eof74;
case 74:
#line 3255 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 12: goto st0;
		case 59: goto st0;
		case 92: goto st76;
	}
	if ( (*p) < 32 ) {
		if ( 9 <= (*p) && (*p) <= 10 )
			goto st0;
	} else if ( (*p) > 34 ) {
		if ( 40 <= (*p) && (*p) <= 41 )
			goto st0;
	} else
		goto st0;
	goto st75;
tr221:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st75;
st75:
	if ( ++p == pe )
		goto _test_eof75;
case 75:
#line 3278 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr212;
		case 10: goto tr213;
		case 12: goto tr214;
		case 32: goto tr212;
		case 59: goto st0;
		case 92: goto st76;
	}
	if ( (*p) > 34 ) {
		if ( 40 <= (*p) && (*p) <= 41 )
			goto st0;
	} else if ( (*p) >= 33 )
		goto st0;
	goto st75;
tr225:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st76;
st76:
	if ( ++p == pe )
		goto _test_eof76;
case 76:
#line 3301 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st77;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st78;
	goto st75;
st77:
	if ( ++p == pe )
		goto _test_eof77;
case 77:
	switch( (*p) ) {
		case 9: goto tr222;
		case 10: goto tr223;
		case 12: goto tr224;
		case 32: goto tr222;
		case 59: goto st0;
		case 92: goto tr225;
	}
	if ( (*p) > 34 ) {
		if ( 40 <= (*p) && (*p) <= 41 )
			goto st0;
	} else if ( (*p) >= 33 )
		goto st0;
	goto tr221;
st78:
	if ( ++p == pe )
		goto _test_eof78;
case 78:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st79;
	goto st0;
st79:
	if ( ++p == pe )
		goto _test_eof79;
case 79:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st75;
	goto st0;
tr210:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st80;
tr236:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st80;
tr231:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st80;
st80:
	if ( ++p == pe )
		goto _test_eof80;
case 80:
#line 3357 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st81;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st82;
	goto st73;
st81:
	if ( ++p == pe )
		goto _test_eof81;
case 81:
	switch( (*p) ) {
		case 9: goto tr222;
		case 10: goto tr223;
		case 12: goto tr224;
		case 32: goto tr222;
		case 33: goto tr230;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto tr231;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr229;
st82:
	if ( ++p == pe )
		goto _test_eof82;
case 82:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st83;
	goto st0;
st83:
	if ( ++p == pe )
		goto _test_eof83;
case 83:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st73;
	goto st0;
tr235:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st84;
st84:
	if ( ++p == pe )
		goto _test_eof84;
case 84:
#line 3402 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr234;
		case 10: goto st0;
		case 12: goto tr235;
		case 32: goto tr234;
		case 59: goto st0;
		case 92: goto tr236;
	}
	if ( (*p) > 34 ) {
		if ( 40 <= (*p) && (*p) <= 41 )
			goto st0;
	} else if ( (*p) >= 33 )
		goto st0;
	goto tr233;
tr11:
#line 885 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; }
#line 886 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; z->ttl_min = z->def_ttl >> 1; z->uv_2 = 0; }
	goto st85;
tr23:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 885 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; }
#line 886 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; z->ttl_min = z->def_ttl >> 1; z->uv_2 = 0; }
	goto st85;
st85:
	if ( ++p == pe )
		goto _test_eof85;
case 85:
#line 3435 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 78: goto st86;
		case 110: goto st86;
	}
	goto st0;
st86:
	if ( ++p == pe )
		goto _test_eof86;
case 86:
	switch( (*p) ) {
		case 9: goto st87;
		case 12: goto st88;
		case 32: goto st87;
	}
	goto st0;
tr241:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st87;
st87:
	if ( ++p == pe )
		goto _test_eof87;
case 87:
#line 3459 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st87;
		case 12: goto st88;
		case 32: goto st87;
		case 65: goto st7;
		case 67: goto st14;
		case 68: goto st54;
		case 77: goto st92;
		case 78: goto st110;
		case 80: goto st187;
		case 83: goto st203;
		case 84: goto st276;
		case 97: goto st7;
		case 99: goto st14;
		case 100: goto st54;
		case 109: goto st92;
		case 110: goto st110;
		case 112: goto st187;
		case 115: goto st203;
		case 116: goto st276;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr240;
	goto st0;
tr242:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st88;
st88:
	if ( ++p == pe )
		goto _test_eof88;
case 88:
#line 3492 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr241;
		case 12: goto tr242;
		case 32: goto tr241;
		case 65: goto tr47;
		case 67: goto tr48;
		case 68: goto tr49;
		case 77: goto tr51;
		case 78: goto tr52;
		case 80: goto tr53;
		case 83: goto tr54;
		case 84: goto tr55;
		case 97: goto tr47;
		case 99: goto tr48;
		case 100: goto tr49;
		case 109: goto tr51;
		case 110: goto tr52;
		case 112: goto tr53;
		case 115: goto tr54;
		case 116: goto tr55;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr243;
	goto st0;
tr240:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st89;
tr243:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st89;
st89:
	if ( ++p == pe )
		goto _test_eof89;
case 89:
#line 3531 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr244;
		case 12: goto tr245;
		case 32: goto tr244;
		case 47: goto tr246;
		case 68: goto tr248;
		case 72: goto tr248;
		case 77: goto tr248;
		case 87: goto tr248;
		case 100: goto tr248;
		case 104: goto tr248;
		case 109: goto tr248;
		case 119: goto tr248;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st89;
	goto st0;
tr251:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st90;
tr244:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 882 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uval; }
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
#line 883 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uv_1; z->ttl_min = z->uv_2 ? z->uv_2 : z->uv_1 >> 1; }
	goto st90;
tr834:
#line 882 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uval; }
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
#line 883 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uv_1; z->ttl_min = z->uv_2 ? z->uv_2 : z->uv_1 >> 1; }
	goto st90;
st90:
	if ( ++p == pe )
		goto _test_eof90;
case 90:
#line 3575 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st90;
		case 12: goto st91;
		case 32: goto st90;
		case 65: goto st7;
		case 67: goto st14;
		case 68: goto st54;
		case 77: goto st92;
		case 78: goto st110;
		case 80: goto st187;
		case 83: goto st203;
		case 84: goto st276;
		case 97: goto st7;
		case 99: goto st14;
		case 100: goto st54;
		case 109: goto st92;
		case 110: goto st110;
		case 112: goto st187;
		case 115: goto st203;
		case 116: goto st276;
	}
	goto st0;
tr252:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st91;
tr245:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 882 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uval; }
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
#line 883 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uv_1; z->ttl_min = z->uv_2 ? z->uv_2 : z->uv_1 >> 1; }
	goto st91;
tr835:
#line 882 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uval; }
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
#line 883 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uv_1; z->ttl_min = z->uv_2 ? z->uv_2 : z->uv_1 >> 1; }
	goto st91;
st91:
	if ( ++p == pe )
		goto _test_eof91;
case 91:
#line 3624 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr251;
		case 12: goto tr252;
		case 32: goto tr251;
		case 65: goto tr47;
		case 67: goto tr48;
		case 68: goto tr49;
		case 77: goto tr51;
		case 78: goto tr52;
		case 80: goto tr53;
		case 83: goto tr54;
		case 84: goto tr55;
		case 97: goto tr47;
		case 99: goto tr48;
		case 100: goto tr49;
		case 109: goto tr51;
		case 110: goto tr52;
		case 112: goto tr53;
		case 115: goto tr54;
		case 116: goto tr55;
	}
	goto st0;
tr12:
#line 885 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; }
	goto st92;
tr51:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st92;
tr24:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 885 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; }
	goto st92;
st92:
	if ( ++p == pe )
		goto _test_eof92;
case 92:
#line 3665 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 88: goto st93;
		case 120: goto st93;
	}
	goto st0;
st93:
	if ( ++p == pe )
		goto _test_eof93;
case 93:
	switch( (*p) ) {
		case 9: goto st94;
		case 12: goto st95;
		case 32: goto st94;
	}
	goto st0;
tr257:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st94;
st94:
	if ( ++p == pe )
		goto _test_eof94;
case 94:
#line 3689 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st94;
		case 12: goto st95;
		case 32: goto st94;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr256;
	goto st0;
tr258:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st95;
st95:
	if ( ++p == pe )
		goto _test_eof95;
case 95:
#line 3706 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr257;
		case 12: goto tr258;
		case 32: goto tr257;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr259;
	goto st0;
tr256:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st96;
tr259:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st96;
st96:
	if ( ++p == pe )
		goto _test_eof96;
case 96:
#line 3729 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr260;
		case 12: goto tr261;
		case 32: goto tr260;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st96;
	goto st0;
tr282:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st97;
tr260:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
	goto st97;
st97:
	if ( ++p == pe )
		goto _test_eof97;
case 97:
#line 3750 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st97;
		case 10: goto st0;
		case 12: goto st103;
		case 32: goto st97;
		case 34: goto tr266;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr267;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr263;
tr263:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st98;
tr281:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st98;
tr275:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st98;
st98:
	if ( ++p == pe )
		goto _test_eof98;
case 98:
#line 3782 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr269;
		case 10: goto tr270;
		case 12: goto tr271;
		case 32: goto tr269;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto st99;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto st98;
tr267:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st99;
tr285:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st99;
tr279:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st99;
st99:
	if ( ++p == pe )
		goto _test_eof99;
case 99:
#line 3813 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st100;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st101;
	goto st98;
st100:
	if ( ++p == pe )
		goto _test_eof100;
case 100:
	switch( (*p) ) {
		case 9: goto tr276;
		case 10: goto tr277;
		case 12: goto tr278;
		case 32: goto tr276;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto tr279;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr275;
st101:
	if ( ++p == pe )
		goto _test_eof101;
case 101:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st102;
	goto st0;
st102:
	if ( ++p == pe )
		goto _test_eof102;
case 102:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st98;
	goto st0;
tr283:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st103;
tr261:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
	goto st103;
st103:
	if ( ++p == pe )
		goto _test_eof103;
case 103:
#line 3861 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr282;
		case 10: goto st0;
		case 12: goto tr283;
		case 32: goto tr282;
		case 34: goto tr284;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr285;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr281;
tr266:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st104;
tr284:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st104;
tr290:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st104;
st104:
	if ( ++p == pe )
		goto _test_eof104;
case 104:
#line 3893 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto st105;
		case 34: goto st106;
		case 92: goto st107;
	}
	goto st104;
tr291:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st105;
st105:
	if ( ++p == pe )
		goto _test_eof105;
case 105:
#line 3908 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto tr291;
		case 34: goto tr292;
		case 92: goto tr293;
	}
	goto tr290;
tr292:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st106;
st106:
	if ( ++p == pe )
		goto _test_eof106;
case 106:
#line 3923 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr294;
		case 10: goto tr295;
		case 12: goto tr296;
		case 32: goto tr294;
	}
	goto st0;
tr293:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st107;
st107:
	if ( ++p == pe )
		goto _test_eof107;
case 107:
#line 3939 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st105;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st108;
	goto st104;
st108:
	if ( ++p == pe )
		goto _test_eof108;
case 108:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st109;
	goto st0;
st109:
	if ( ++p == pe )
		goto _test_eof109;
case 109:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st104;
	goto st0;
tr13:
#line 885 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; }
	goto st110;
tr52:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st110;
tr25:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 885 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; }
	goto st110;
st110:
	if ( ++p == pe )
		goto _test_eof110;
case 110:
#line 3977 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 65: goto st111;
		case 83: goto st173;
		case 97: goto st111;
		case 115: goto st173;
	}
	goto st0;
st111:
	if ( ++p == pe )
		goto _test_eof111;
case 111:
	switch( (*p) ) {
		case 80: goto st112;
		case 112: goto st112;
	}
	goto st0;
st112:
	if ( ++p == pe )
		goto _test_eof112;
case 112:
	switch( (*p) ) {
		case 84: goto st113;
		case 116: goto st113;
	}
	goto st0;
st113:
	if ( ++p == pe )
		goto _test_eof113;
case 113:
	switch( (*p) ) {
		case 82: goto st114;
		case 114: goto st114;
	}
	goto st0;
st114:
	if ( ++p == pe )
		goto _test_eof114;
case 114:
	switch( (*p) ) {
		case 9: goto st115;
		case 12: goto st116;
		case 32: goto st115;
	}
	goto st0;
tr307:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st115;
st115:
	if ( ++p == pe )
		goto _test_eof115;
case 115:
#line 4030 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st115;
		case 12: goto st116;
		case 32: goto st115;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr306;
	goto st0;
tr308:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st116;
st116:
	if ( ++p == pe )
		goto _test_eof116;
case 116:
#line 4047 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr307;
		case 12: goto tr308;
		case 32: goto tr307;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr309;
	goto st0;
tr306:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st117;
tr309:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st117;
st117:
	if ( ++p == pe )
		goto _test_eof117;
case 117:
#line 4070 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr310;
		case 12: goto tr311;
		case 32: goto tr310;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st117;
	goto st0;
tr316:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st118;
tr310:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
	goto st118;
st118:
	if ( ++p == pe )
		goto _test_eof118;
case 118:
#line 4093 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st118;
		case 12: goto st119;
		case 32: goto st118;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr315;
	goto st0;
tr317:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st119;
tr311:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
	goto st119;
st119:
	if ( ++p == pe )
		goto _test_eof119;
case 119:
#line 4116 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr316;
		case 12: goto tr317;
		case 32: goto tr316;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr318;
	goto st0;
tr315:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st120;
tr318:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st120;
st120:
	if ( ++p == pe )
		goto _test_eof120;
case 120:
#line 4139 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr319;
		case 12: goto tr320;
		case 32: goto tr319;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st120;
	goto st0;
tr441:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st121;
tr319:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 888 "./src/zscan_rfc1035.rl"
	{ z->uv_2 = z->uval; }
	goto st121;
st121:
	if ( ++p == pe )
		goto _test_eof121;
case 121:
#line 4162 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st121;
		case 10: goto st0;
		case 12: goto st166;
		case 32: goto st121;
		case 34: goto tr325;
		case 59: goto st0;
		case 92: goto tr326;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr322;
tr322:
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st122;
tr435:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st122;
tr440:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st122;
st122:
	if ( ++p == pe )
		goto _test_eof122;
case 122:
#line 4197 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr328;
		case 10: goto st0;
		case 12: goto tr329;
		case 32: goto tr328;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto st162;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto st122;
tr417:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st123;
tr328:
#line 872 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, false); }
	goto st123;
tr436:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 872 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, false); }
	goto st123;
tr453:
#line 873 "./src/zscan_rfc1035.rl"
	{ z->tstart++; text_add_tok(z, p - z->tstart - 1, false); }
	goto st123;
st123:
	if ( ++p == pe )
		goto _test_eof123;
case 123:
#line 4232 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st123;
		case 10: goto st0;
		case 12: goto st155;
		case 32: goto st123;
		case 34: goto tr334;
		case 59: goto st0;
		case 92: goto tr335;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr331;
tr331:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st124;
tr416:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st124;
tr411:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st124;
st124:
	if ( ++p == pe )
		goto _test_eof124;
case 124:
#line 4263 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr337;
		case 10: goto st0;
		case 12: goto tr338;
		case 32: goto tr337;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto st151;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto st124;
tr393:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st125;
tr337:
#line 872 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, false); }
	goto st125;
tr412:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 872 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, false); }
	goto st125;
tr429:
#line 873 "./src/zscan_rfc1035.rl"
	{ z->tstart++; text_add_tok(z, p - z->tstart - 1, false); }
	goto st125;
st125:
	if ( ++p == pe )
		goto _test_eof125;
case 125:
#line 4298 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st125;
		case 10: goto st0;
		case 12: goto st144;
		case 32: goto st125;
		case 34: goto tr343;
		case 59: goto st0;
		case 92: goto tr344;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr340;
tr340:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st126;
tr392:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st126;
tr387:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st126;
st126:
	if ( ++p == pe )
		goto _test_eof126;
case 126:
#line 4329 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr346;
		case 10: goto st0;
		case 12: goto tr347;
		case 32: goto tr346;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto st140;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto st126;
tr368:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st127;
tr346:
#line 872 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, false); }
	goto st127;
tr388:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 872 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, false); }
	goto st127;
tr405:
#line 873 "./src/zscan_rfc1035.rl"
	{ z->tstart++; text_add_tok(z, p - z->tstart - 1, false); }
	goto st127;
st127:
	if ( ++p == pe )
		goto _test_eof127;
case 127:
#line 4364 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st127;
		case 10: goto st0;
		case 12: goto st133;
		case 32: goto st127;
		case 34: goto tr352;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr353;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr349;
tr349:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st128;
tr367:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st128;
tr361:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st128;
st128:
	if ( ++p == pe )
		goto _test_eof128;
case 128:
#line 4396 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr355;
		case 10: goto tr356;
		case 12: goto tr357;
		case 32: goto tr355;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto st129;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto st128;
tr353:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st129;
tr371:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st129;
tr365:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st129;
st129:
	if ( ++p == pe )
		goto _test_eof129;
case 129:
#line 4427 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st130;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st131;
	goto st128;
st130:
	if ( ++p == pe )
		goto _test_eof130;
case 130:
	switch( (*p) ) {
		case 9: goto tr362;
		case 10: goto tr363;
		case 12: goto tr364;
		case 32: goto tr362;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto tr365;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr361;
st131:
	if ( ++p == pe )
		goto _test_eof131;
case 131:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st132;
	goto st0;
st132:
	if ( ++p == pe )
		goto _test_eof132;
case 132:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st128;
	goto st0;
tr369:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st133;
tr347:
#line 872 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, false); }
	goto st133;
tr389:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 872 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, false); }
	goto st133;
tr406:
#line 873 "./src/zscan_rfc1035.rl"
	{ z->tstart++; text_add_tok(z, p - z->tstart - 1, false); }
	goto st133;
st133:
	if ( ++p == pe )
		goto _test_eof133;
case 133:
#line 4485 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr368;
		case 10: goto st0;
		case 12: goto tr369;
		case 32: goto tr368;
		case 34: goto tr370;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr371;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr367;
tr352:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st134;
tr370:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st134;
tr376:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st134;
st134:
	if ( ++p == pe )
		goto _test_eof134;
case 134:
#line 4517 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto st135;
		case 34: goto st136;
		case 92: goto st137;
	}
	goto st134;
tr377:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st135;
st135:
	if ( ++p == pe )
		goto _test_eof135;
case 135:
#line 4532 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto tr377;
		case 34: goto tr378;
		case 92: goto tr379;
	}
	goto tr376;
tr378:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st136;
st136:
	if ( ++p == pe )
		goto _test_eof136;
case 136:
#line 4547 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr380;
		case 10: goto tr381;
		case 12: goto tr382;
		case 32: goto tr380;
	}
	goto st0;
tr379:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st137;
st137:
	if ( ++p == pe )
		goto _test_eof137;
case 137:
#line 4563 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st135;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st138;
	goto st134;
st138:
	if ( ++p == pe )
		goto _test_eof138;
case 138:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st139;
	goto st0;
st139:
	if ( ++p == pe )
		goto _test_eof139;
case 139:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st134;
	goto st0;
tr344:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st140;
tr396:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st140;
tr390:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st140;
st140:
	if ( ++p == pe )
		goto _test_eof140;
case 140:
#line 4601 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st141;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st142;
	goto st126;
st141:
	if ( ++p == pe )
		goto _test_eof141;
case 141:
	switch( (*p) ) {
		case 9: goto tr388;
		case 10: goto st0;
		case 12: goto tr389;
		case 32: goto tr388;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto tr390;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr387;
st142:
	if ( ++p == pe )
		goto _test_eof142;
case 142:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st143;
	goto st0;
st143:
	if ( ++p == pe )
		goto _test_eof143;
case 143:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st126;
	goto st0;
tr394:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st144;
tr338:
#line 872 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, false); }
	goto st144;
tr413:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 872 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, false); }
	goto st144;
tr430:
#line 873 "./src/zscan_rfc1035.rl"
	{ z->tstart++; text_add_tok(z, p - z->tstart - 1, false); }
	goto st144;
st144:
	if ( ++p == pe )
		goto _test_eof144;
case 144:
#line 4659 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr393;
		case 10: goto st0;
		case 12: goto tr394;
		case 32: goto tr393;
		case 34: goto tr395;
		case 59: goto st0;
		case 92: goto tr396;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr392;
tr343:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st145;
tr395:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st145;
tr401:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st145;
st145:
	if ( ++p == pe )
		goto _test_eof145;
case 145:
#line 4690 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto st146;
		case 34: goto st147;
		case 92: goto st148;
	}
	goto st145;
tr402:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st146;
st146:
	if ( ++p == pe )
		goto _test_eof146;
case 146:
#line 4705 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto tr402;
		case 34: goto tr403;
		case 92: goto tr404;
	}
	goto tr401;
tr403:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st147;
st147:
	if ( ++p == pe )
		goto _test_eof147;
case 147:
#line 4720 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr405;
		case 12: goto tr406;
		case 32: goto tr405;
	}
	goto st0;
tr404:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st148;
st148:
	if ( ++p == pe )
		goto _test_eof148;
case 148:
#line 4735 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st146;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st149;
	goto st145;
st149:
	if ( ++p == pe )
		goto _test_eof149;
case 149:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st150;
	goto st0;
st150:
	if ( ++p == pe )
		goto _test_eof150;
case 150:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st145;
	goto st0;
tr335:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st151;
tr420:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st151;
tr414:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st151;
st151:
	if ( ++p == pe )
		goto _test_eof151;
case 151:
#line 4773 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st152;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st153;
	goto st124;
st152:
	if ( ++p == pe )
		goto _test_eof152;
case 152:
	switch( (*p) ) {
		case 9: goto tr412;
		case 10: goto st0;
		case 12: goto tr413;
		case 32: goto tr412;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto tr414;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr411;
st153:
	if ( ++p == pe )
		goto _test_eof153;
case 153:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st154;
	goto st0;
st154:
	if ( ++p == pe )
		goto _test_eof154;
case 154:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st124;
	goto st0;
tr418:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st155;
tr329:
#line 872 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, false); }
	goto st155;
tr437:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 872 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, false); }
	goto st155;
tr454:
#line 873 "./src/zscan_rfc1035.rl"
	{ z->tstart++; text_add_tok(z, p - z->tstart - 1, false); }
	goto st155;
st155:
	if ( ++p == pe )
		goto _test_eof155;
case 155:
#line 4831 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr417;
		case 10: goto st0;
		case 12: goto tr418;
		case 32: goto tr417;
		case 34: goto tr419;
		case 59: goto st0;
		case 92: goto tr420;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr416;
tr334:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st156;
tr419:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st156;
tr425:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st156;
st156:
	if ( ++p == pe )
		goto _test_eof156;
case 156:
#line 4862 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto st157;
		case 34: goto st158;
		case 92: goto st159;
	}
	goto st156;
tr426:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st157;
st157:
	if ( ++p == pe )
		goto _test_eof157;
case 157:
#line 4877 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto tr426;
		case 34: goto tr427;
		case 92: goto tr428;
	}
	goto tr425;
tr427:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st158;
st158:
	if ( ++p == pe )
		goto _test_eof158;
case 158:
#line 4892 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr429;
		case 12: goto tr430;
		case 32: goto tr429;
	}
	goto st0;
tr428:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st159;
st159:
	if ( ++p == pe )
		goto _test_eof159;
case 159:
#line 4907 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st157;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st160;
	goto st156;
st160:
	if ( ++p == pe )
		goto _test_eof160;
case 160:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st161;
	goto st0;
st161:
	if ( ++p == pe )
		goto _test_eof161;
case 161:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st156;
	goto st0;
tr326:
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st162;
tr438:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st162;
tr444:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st162;
st162:
	if ( ++p == pe )
		goto _test_eof162;
case 162:
#line 4949 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st163;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st164;
	goto st122;
st163:
	if ( ++p == pe )
		goto _test_eof163;
case 163:
	switch( (*p) ) {
		case 9: goto tr436;
		case 10: goto st0;
		case 12: goto tr437;
		case 32: goto tr436;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto tr438;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr435;
st164:
	if ( ++p == pe )
		goto _test_eof164;
case 164:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st165;
	goto st0;
st165:
	if ( ++p == pe )
		goto _test_eof165;
case 165:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st122;
	goto st0;
tr442:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st166;
tr320:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 888 "./src/zscan_rfc1035.rl"
	{ z->uv_2 = z->uval; }
	goto st166;
st166:
	if ( ++p == pe )
		goto _test_eof166;
case 166:
#line 4999 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr441;
		case 10: goto st0;
		case 12: goto tr442;
		case 32: goto tr441;
		case 34: goto tr443;
		case 59: goto st0;
		case 92: goto tr444;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr440;
tr325:
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st167;
tr449:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st167;
tr443:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st167;
st167:
	if ( ++p == pe )
		goto _test_eof167;
case 167:
#line 5034 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto st168;
		case 34: goto st169;
		case 92: goto st170;
	}
	goto st167;
tr450:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st168;
st168:
	if ( ++p == pe )
		goto _test_eof168;
case 168:
#line 5049 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto tr450;
		case 34: goto tr451;
		case 92: goto tr452;
	}
	goto tr449;
tr451:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st169;
st169:
	if ( ++p == pe )
		goto _test_eof169;
case 169:
#line 5064 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr453;
		case 12: goto tr454;
		case 32: goto tr453;
	}
	goto st0;
tr452:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st170;
st170:
	if ( ++p == pe )
		goto _test_eof170;
case 170:
#line 5079 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st168;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st171;
	goto st167;
st171:
	if ( ++p == pe )
		goto _test_eof171;
case 171:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st172;
	goto st0;
st172:
	if ( ++p == pe )
		goto _test_eof172;
case 172:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st167;
	goto st0;
st173:
	if ( ++p == pe )
		goto _test_eof173;
case 173:
	switch( (*p) ) {
		case 9: goto st174;
		case 12: goto st180;
		case 32: goto st174;
	}
	goto st0;
tr476:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st174;
st174:
	if ( ++p == pe )
		goto _test_eof174;
case 174:
#line 5117 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st174;
		case 10: goto st0;
		case 12: goto st180;
		case 32: goto st174;
		case 34: goto tr460;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr461;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr459;
tr459:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st175;
tr475:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st175;
tr469:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st175;
st175:
	if ( ++p == pe )
		goto _test_eof175;
case 175:
#line 5149 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr463;
		case 10: goto tr464;
		case 12: goto tr465;
		case 32: goto tr463;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto st176;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto st175;
tr461:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st176;
tr479:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st176;
tr473:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st176;
st176:
	if ( ++p == pe )
		goto _test_eof176;
case 176:
#line 5180 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st177;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st178;
	goto st175;
st177:
	if ( ++p == pe )
		goto _test_eof177;
case 177:
	switch( (*p) ) {
		case 9: goto tr470;
		case 10: goto tr471;
		case 12: goto tr472;
		case 32: goto tr470;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto tr473;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr469;
st178:
	if ( ++p == pe )
		goto _test_eof178;
case 178:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st179;
	goto st0;
st179:
	if ( ++p == pe )
		goto _test_eof179;
case 179:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st175;
	goto st0;
tr477:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st180;
st180:
	if ( ++p == pe )
		goto _test_eof180;
case 180:
#line 5224 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr476;
		case 10: goto st0;
		case 12: goto tr477;
		case 32: goto tr476;
		case 34: goto tr478;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr479;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr475;
tr460:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st181;
tr478:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st181;
tr484:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st181;
st181:
	if ( ++p == pe )
		goto _test_eof181;
case 181:
#line 5256 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto st182;
		case 34: goto st183;
		case 92: goto st184;
	}
	goto st181;
tr485:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st182;
st182:
	if ( ++p == pe )
		goto _test_eof182;
case 182:
#line 5271 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto tr485;
		case 34: goto tr486;
		case 92: goto tr487;
	}
	goto tr484;
tr486:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st183;
st183:
	if ( ++p == pe )
		goto _test_eof183;
case 183:
#line 5286 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr488;
		case 10: goto tr489;
		case 12: goto tr490;
		case 32: goto tr488;
	}
	goto st0;
tr487:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st184;
st184:
	if ( ++p == pe )
		goto _test_eof184;
case 184:
#line 5302 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st182;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st185;
	goto st181;
st185:
	if ( ++p == pe )
		goto _test_eof185;
case 185:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st186;
	goto st0;
st186:
	if ( ++p == pe )
		goto _test_eof186;
case 186:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st181;
	goto st0;
tr14:
#line 885 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; }
	goto st187;
tr53:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st187;
tr26:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 885 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; }
	goto st187;
st187:
	if ( ++p == pe )
		goto _test_eof187;
case 187:
#line 5340 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 84: goto st188;
		case 116: goto st188;
	}
	goto st0;
st188:
	if ( ++p == pe )
		goto _test_eof188;
case 188:
	switch( (*p) ) {
		case 82: goto st189;
		case 114: goto st189;
	}
	goto st0;
st189:
	if ( ++p == pe )
		goto _test_eof189;
case 189:
	switch( (*p) ) {
		case 9: goto st190;
		case 12: goto st196;
		case 32: goto st190;
	}
	goto st0;
tr514:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st190;
st190:
	if ( ++p == pe )
		goto _test_eof190;
case 190:
#line 5373 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st190;
		case 10: goto st0;
		case 12: goto st196;
		case 32: goto st190;
		case 34: goto tr498;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr499;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr497;
tr497:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st191;
tr513:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st191;
tr507:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st191;
st191:
	if ( ++p == pe )
		goto _test_eof191;
case 191:
#line 5405 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr501;
		case 10: goto tr502;
		case 12: goto tr503;
		case 32: goto tr501;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto st192;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto st191;
tr499:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st192;
tr517:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st192;
tr511:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st192;
st192:
	if ( ++p == pe )
		goto _test_eof192;
case 192:
#line 5436 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st193;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st194;
	goto st191;
st193:
	if ( ++p == pe )
		goto _test_eof193;
case 193:
	switch( (*p) ) {
		case 9: goto tr508;
		case 10: goto tr509;
		case 12: goto tr510;
		case 32: goto tr508;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto tr511;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr507;
st194:
	if ( ++p == pe )
		goto _test_eof194;
case 194:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st195;
	goto st0;
st195:
	if ( ++p == pe )
		goto _test_eof195;
case 195:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st191;
	goto st0;
tr515:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st196;
st196:
	if ( ++p == pe )
		goto _test_eof196;
case 196:
#line 5480 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr514;
		case 10: goto st0;
		case 12: goto tr515;
		case 32: goto tr514;
		case 34: goto tr516;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr517;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr513;
tr498:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st197;
tr516:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st197;
tr522:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st197;
st197:
	if ( ++p == pe )
		goto _test_eof197;
case 197:
#line 5512 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto st198;
		case 34: goto st199;
		case 92: goto st200;
	}
	goto st197;
tr523:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st198;
st198:
	if ( ++p == pe )
		goto _test_eof198;
case 198:
#line 5527 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto tr523;
		case 34: goto tr524;
		case 92: goto tr525;
	}
	goto tr522;
tr524:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st199;
st199:
	if ( ++p == pe )
		goto _test_eof199;
case 199:
#line 5542 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr526;
		case 10: goto tr527;
		case 12: goto tr528;
		case 32: goto tr526;
	}
	goto st0;
tr525:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st200;
st200:
	if ( ++p == pe )
		goto _test_eof200;
case 200:
#line 5558 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st198;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st201;
	goto st197;
st201:
	if ( ++p == pe )
		goto _test_eof201;
case 201:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st202;
	goto st0;
st202:
	if ( ++p == pe )
		goto _test_eof202;
case 202:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st197;
	goto st0;
tr15:
#line 885 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; }
	goto st203;
tr54:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st203;
tr27:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 885 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; }
	goto st203;
st203:
	if ( ++p == pe )
		goto _test_eof203;
case 203:
#line 5596 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 79: goto st204;
		case 82: goto st252;
		case 111: goto st204;
		case 114: goto st252;
	}
	goto st0;
st204:
	if ( ++p == pe )
		goto _test_eof204;
case 204:
	switch( (*p) ) {
		case 65: goto st205;
		case 97: goto st205;
	}
	goto st0;
st205:
	if ( ++p == pe )
		goto _test_eof205;
case 205:
	switch( (*p) ) {
		case 9: goto st206;
		case 12: goto st245;
		case 32: goto st206;
	}
	goto st0;
tr646:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st206;
st206:
	if ( ++p == pe )
		goto _test_eof206;
case 206:
#line 5631 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st206;
		case 10: goto st0;
		case 12: goto st245;
		case 32: goto st206;
		case 34: goto tr537;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr538;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr536;
tr536:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st207;
tr645:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st207;
tr640:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st207;
st207:
	if ( ++p == pe )
		goto _test_eof207;
case 207:
#line 5663 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr540;
		case 10: goto st0;
		case 12: goto tr541;
		case 32: goto tr540;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto st241;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto st207;
tr622:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st208;
tr540:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
	goto st208;
tr641:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
	goto st208;
tr658:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
	goto st208;
st208:
	if ( ++p == pe )
		goto _test_eof208;
case 208:
#line 5698 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st208;
		case 10: goto st0;
		case 12: goto st234;
		case 32: goto st208;
		case 34: goto tr546;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr547;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr543;
tr543:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st209;
tr621:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st209;
tr616:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st209;
st209:
	if ( ++p == pe )
		goto _test_eof209;
case 209:
#line 5730 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr549;
		case 10: goto st0;
		case 12: goto tr550;
		case 32: goto tr549;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto st230;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto st209;
tr555:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st210;
tr549:
#line 855 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->eml_dname, p - z->tstart, false); }
	goto st210;
tr617:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 855 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->eml_dname, p - z->tstart, false); }
	goto st210;
tr634:
#line 856 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->eml_dname, p - z->tstart - 1, false); }
	goto st210;
st210:
	if ( ++p == pe )
		goto _test_eof210;
case 210:
#line 5765 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st210;
		case 12: goto st211;
		case 32: goto st210;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr554;
	goto st0;
tr556:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st211;
tr550:
#line 855 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->eml_dname, p - z->tstart, false); }
	goto st211;
tr618:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 855 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->eml_dname, p - z->tstart, false); }
	goto st211;
tr635:
#line 856 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->eml_dname, p - z->tstart - 1, false); }
	goto st211;
st211:
	if ( ++p == pe )
		goto _test_eof211;
case 211:
#line 5796 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr555;
		case 12: goto tr556;
		case 32: goto tr555;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr557;
	goto st0;
tr554:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st212;
tr557:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st212;
st212:
	if ( ++p == pe )
		goto _test_eof212;
case 212:
#line 5819 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr558;
		case 12: goto tr559;
		case 32: goto tr558;
		case 68: goto tr561;
		case 72: goto tr561;
		case 77: goto tr561;
		case 87: goto tr561;
		case 100: goto tr561;
		case 104: goto tr561;
		case 109: goto tr561;
		case 119: goto tr561;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st212;
	goto st0;
tr565:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st213;
tr558:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
	goto st213;
tr612:
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
	goto st213;
st213:
	if ( ++p == pe )
		goto _test_eof213;
case 213:
#line 5854 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st213;
		case 12: goto st214;
		case 32: goto st213;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr564;
	goto st0;
tr566:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st214;
tr559:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
	goto st214;
tr613:
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
	goto st214;
st214:
	if ( ++p == pe )
		goto _test_eof214;
case 214:
#line 5881 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr565;
		case 12: goto tr566;
		case 32: goto tr565;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr567;
	goto st0;
tr564:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st215;
tr567:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st215;
st215:
	if ( ++p == pe )
		goto _test_eof215;
case 215:
#line 5904 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr568;
		case 12: goto tr569;
		case 32: goto tr568;
		case 68: goto tr571;
		case 72: goto tr571;
		case 77: goto tr571;
		case 87: goto tr571;
		case 100: goto tr571;
		case 104: goto tr571;
		case 109: goto tr571;
		case 119: goto tr571;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st215;
	goto st0;
tr575:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st216;
tr568:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 888 "./src/zscan_rfc1035.rl"
	{ z->uv_2 = z->uval; }
	goto st216;
tr610:
#line 888 "./src/zscan_rfc1035.rl"
	{ z->uv_2 = z->uval; }
	goto st216;
st216:
	if ( ++p == pe )
		goto _test_eof216;
case 216:
#line 5939 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st216;
		case 12: goto st217;
		case 32: goto st216;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr574;
	goto st0;
tr576:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st217;
tr569:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 888 "./src/zscan_rfc1035.rl"
	{ z->uv_2 = z->uval; }
	goto st217;
tr611:
#line 888 "./src/zscan_rfc1035.rl"
	{ z->uv_2 = z->uval; }
	goto st217;
st217:
	if ( ++p == pe )
		goto _test_eof217;
case 217:
#line 5966 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr575;
		case 12: goto tr576;
		case 32: goto tr575;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr577;
	goto st0;
tr574:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st218;
tr577:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st218;
st218:
	if ( ++p == pe )
		goto _test_eof218;
case 218:
#line 5989 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr578;
		case 12: goto tr579;
		case 32: goto tr578;
		case 68: goto tr581;
		case 72: goto tr581;
		case 77: goto tr581;
		case 87: goto tr581;
		case 100: goto tr581;
		case 104: goto tr581;
		case 109: goto tr581;
		case 119: goto tr581;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st218;
	goto st0;
tr585:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st219;
tr578:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 889 "./src/zscan_rfc1035.rl"
	{ z->uv_3 = z->uval; }
	goto st219;
tr608:
#line 889 "./src/zscan_rfc1035.rl"
	{ z->uv_3 = z->uval; }
	goto st219;
st219:
	if ( ++p == pe )
		goto _test_eof219;
case 219:
#line 6024 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st219;
		case 12: goto st220;
		case 32: goto st219;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr584;
	goto st0;
tr586:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st220;
tr579:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 889 "./src/zscan_rfc1035.rl"
	{ z->uv_3 = z->uval; }
	goto st220;
tr609:
#line 889 "./src/zscan_rfc1035.rl"
	{ z->uv_3 = z->uval; }
	goto st220;
st220:
	if ( ++p == pe )
		goto _test_eof220;
case 220:
#line 6051 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr585;
		case 12: goto tr586;
		case 32: goto tr585;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr587;
	goto st0;
tr584:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st221;
tr587:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st221;
st221:
	if ( ++p == pe )
		goto _test_eof221;
case 221:
#line 6074 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr588;
		case 12: goto tr589;
		case 32: goto tr588;
		case 68: goto tr591;
		case 72: goto tr591;
		case 77: goto tr591;
		case 87: goto tr591;
		case 100: goto tr591;
		case 104: goto tr591;
		case 109: goto tr591;
		case 119: goto tr591;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st221;
	goto st0;
tr595:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st222;
tr588:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 890 "./src/zscan_rfc1035.rl"
	{ z->uv_4 = z->uval; }
	goto st222;
tr606:
#line 890 "./src/zscan_rfc1035.rl"
	{ z->uv_4 = z->uval; }
	goto st222;
st222:
	if ( ++p == pe )
		goto _test_eof222;
case 222:
#line 6109 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st222;
		case 12: goto st223;
		case 32: goto st222;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr594;
	goto st0;
tr596:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st223;
tr589:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 890 "./src/zscan_rfc1035.rl"
	{ z->uv_4 = z->uval; }
	goto st223;
tr607:
#line 890 "./src/zscan_rfc1035.rl"
	{ z->uv_4 = z->uval; }
	goto st223;
st223:
	if ( ++p == pe )
		goto _test_eof223;
case 223:
#line 6136 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr595;
		case 12: goto tr596;
		case 32: goto tr595;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr597;
	goto st0;
tr594:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st224;
tr597:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st224;
st224:
	if ( ++p == pe )
		goto _test_eof224;
case 224:
#line 6159 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr598;
		case 10: goto tr599;
		case 12: goto tr600;
		case 32: goto tr598;
		case 68: goto tr602;
		case 72: goto tr602;
		case 77: goto tr602;
		case 87: goto tr602;
		case 100: goto tr602;
		case 104: goto tr602;
		case 109: goto tr602;
		case 119: goto tr602;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st224;
	goto st0;
tr602:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 880 "./src/zscan_rfc1035.rl"
	{ mult_uval(z, (*p)); }
	goto st225;
st225:
	if ( ++p == pe )
		goto _test_eof225;
case 225:
#line 6187 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr603;
		case 10: goto tr604;
		case 12: goto tr605;
		case 32: goto tr603;
	}
	goto st0;
tr591:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 880 "./src/zscan_rfc1035.rl"
	{ mult_uval(z, (*p)); }
	goto st226;
st226:
	if ( ++p == pe )
		goto _test_eof226;
case 226:
#line 6205 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr606;
		case 12: goto tr607;
		case 32: goto tr606;
	}
	goto st0;
tr581:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 880 "./src/zscan_rfc1035.rl"
	{ mult_uval(z, (*p)); }
	goto st227;
st227:
	if ( ++p == pe )
		goto _test_eof227;
case 227:
#line 6222 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr608;
		case 12: goto tr609;
		case 32: goto tr608;
	}
	goto st0;
tr571:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 880 "./src/zscan_rfc1035.rl"
	{ mult_uval(z, (*p)); }
	goto st228;
st228:
	if ( ++p == pe )
		goto _test_eof228;
case 228:
#line 6239 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr610;
		case 12: goto tr611;
		case 32: goto tr610;
	}
	goto st0;
tr561:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 880 "./src/zscan_rfc1035.rl"
	{ mult_uval(z, (*p)); }
	goto st229;
st229:
	if ( ++p == pe )
		goto _test_eof229;
case 229:
#line 6256 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr612;
		case 12: goto tr613;
		case 32: goto tr612;
	}
	goto st0;
tr547:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st230;
tr625:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st230;
tr619:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st230;
st230:
	if ( ++p == pe )
		goto _test_eof230;
case 230:
#line 6281 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st231;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st232;
	goto st209;
st231:
	if ( ++p == pe )
		goto _test_eof231;
case 231:
	switch( (*p) ) {
		case 9: goto tr617;
		case 10: goto st0;
		case 12: goto tr618;
		case 32: goto tr617;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto tr619;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr616;
st232:
	if ( ++p == pe )
		goto _test_eof232;
case 232:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st233;
	goto st0;
st233:
	if ( ++p == pe )
		goto _test_eof233;
case 233:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st209;
	goto st0;
tr623:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st234;
tr541:
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
	goto st234;
tr642:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 853 "./src/zscan_rfc1035.rl"
	{ dname_set(z, z->rhs_dname, p - z->tstart, false); }
	goto st234;
tr659:
#line 854 "./src/zscan_rfc1035.rl"
	{ z->tstart++; dname_set(z, z->rhs_dname, p - z->tstart - 1, false); }
	goto st234;
st234:
	if ( ++p == pe )
		goto _test_eof234;
case 234:
#line 6339 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr622;
		case 10: goto st0;
		case 12: goto tr623;
		case 32: goto tr622;
		case 34: goto tr624;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr625;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr621;
tr546:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st235;
tr624:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st235;
tr630:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st235;
st235:
	if ( ++p == pe )
		goto _test_eof235;
case 235:
#line 6371 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto st236;
		case 34: goto st237;
		case 92: goto st238;
	}
	goto st235;
tr631:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st236;
st236:
	if ( ++p == pe )
		goto _test_eof236;
case 236:
#line 6386 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto tr631;
		case 34: goto tr632;
		case 92: goto tr633;
	}
	goto tr630;
tr632:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st237;
st237:
	if ( ++p == pe )
		goto _test_eof237;
case 237:
#line 6401 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr634;
		case 12: goto tr635;
		case 32: goto tr634;
	}
	goto st0;
tr633:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st238;
st238:
	if ( ++p == pe )
		goto _test_eof238;
case 238:
#line 6416 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st236;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st239;
	goto st235;
st239:
	if ( ++p == pe )
		goto _test_eof239;
case 239:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st240;
	goto st0;
st240:
	if ( ++p == pe )
		goto _test_eof240;
case 240:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st235;
	goto st0;
tr538:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st241;
tr649:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st241;
tr643:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st241;
st241:
	if ( ++p == pe )
		goto _test_eof241;
case 241:
#line 6454 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st242;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st243;
	goto st207;
st242:
	if ( ++p == pe )
		goto _test_eof242;
case 242:
	switch( (*p) ) {
		case 9: goto tr641;
		case 10: goto st0;
		case 12: goto tr642;
		case 32: goto tr641;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto tr643;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr640;
st243:
	if ( ++p == pe )
		goto _test_eof243;
case 243:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st244;
	goto st0;
st244:
	if ( ++p == pe )
		goto _test_eof244;
case 244:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st207;
	goto st0;
tr647:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st245;
st245:
	if ( ++p == pe )
		goto _test_eof245;
case 245:
#line 6498 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr646;
		case 10: goto st0;
		case 12: goto tr647;
		case 32: goto tr646;
		case 34: goto tr648;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr649;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr645;
tr537:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st246;
tr648:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st246;
tr654:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st246;
st246:
	if ( ++p == pe )
		goto _test_eof246;
case 246:
#line 6530 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto st247;
		case 34: goto st248;
		case 92: goto st249;
	}
	goto st246;
tr655:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st247;
st247:
	if ( ++p == pe )
		goto _test_eof247;
case 247:
#line 6545 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto tr655;
		case 34: goto tr656;
		case 92: goto tr657;
	}
	goto tr654;
tr656:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st248;
st248:
	if ( ++p == pe )
		goto _test_eof248;
case 248:
#line 6560 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr658;
		case 12: goto tr659;
		case 32: goto tr658;
	}
	goto st0;
tr657:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st249;
st249:
	if ( ++p == pe )
		goto _test_eof249;
case 249:
#line 6575 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st247;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st250;
	goto st246;
st250:
	if ( ++p == pe )
		goto _test_eof250;
case 250:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st251;
	goto st0;
st251:
	if ( ++p == pe )
		goto _test_eof251;
case 251:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st246;
	goto st0;
st252:
	if ( ++p == pe )
		goto _test_eof252;
case 252:
	switch( (*p) ) {
		case 86: goto st253;
		case 118: goto st253;
	}
	goto st0;
st253:
	if ( ++p == pe )
		goto _test_eof253;
case 253:
	switch( (*p) ) {
		case 9: goto st254;
		case 12: goto st255;
		case 32: goto st254;
	}
	goto st0;
tr666:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st254;
st254:
	if ( ++p == pe )
		goto _test_eof254;
case 254:
#line 6622 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st254;
		case 12: goto st255;
		case 32: goto st254;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr665;
	goto st0;
tr667:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st255;
st255:
	if ( ++p == pe )
		goto _test_eof255;
case 255:
#line 6639 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr666;
		case 12: goto tr667;
		case 32: goto tr666;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr668;
	goto st0;
tr665:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st256;
tr668:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st256;
st256:
	if ( ++p == pe )
		goto _test_eof256;
case 256:
#line 6662 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr669;
		case 12: goto tr670;
		case 32: goto tr669;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st256;
	goto st0;
tr675:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st257;
tr669:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
	goto st257;
st257:
	if ( ++p == pe )
		goto _test_eof257;
case 257:
#line 6685 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st257;
		case 12: goto st258;
		case 32: goto st257;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr674;
	goto st0;
tr676:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st258;
tr670:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
	goto st258;
st258:
	if ( ++p == pe )
		goto _test_eof258;
case 258:
#line 6708 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr675;
		case 12: goto tr676;
		case 32: goto tr675;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr677;
	goto st0;
tr674:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st259;
tr677:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st259;
st259:
	if ( ++p == pe )
		goto _test_eof259;
case 259:
#line 6731 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr678;
		case 12: goto tr679;
		case 32: goto tr678;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st259;
	goto st0;
tr684:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st260;
tr678:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 888 "./src/zscan_rfc1035.rl"
	{ z->uv_2 = z->uval; }
	goto st260;
st260:
	if ( ++p == pe )
		goto _test_eof260;
case 260:
#line 6754 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st260;
		case 12: goto st261;
		case 32: goto st260;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr683;
	goto st0;
tr685:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st261;
tr679:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 888 "./src/zscan_rfc1035.rl"
	{ z->uv_2 = z->uval; }
	goto st261;
st261:
	if ( ++p == pe )
		goto _test_eof261;
case 261:
#line 6777 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr684;
		case 12: goto tr685;
		case 32: goto tr684;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr686;
	goto st0;
tr683:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st262;
tr686:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st262;
st262:
	if ( ++p == pe )
		goto _test_eof262;
case 262:
#line 6800 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr687;
		case 12: goto tr688;
		case 32: goto tr687;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st262;
	goto st0;
tr709:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st263;
tr687:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 889 "./src/zscan_rfc1035.rl"
	{ z->uv_3 = z->uval; }
	goto st263;
st263:
	if ( ++p == pe )
		goto _test_eof263;
case 263:
#line 6823 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st263;
		case 10: goto st0;
		case 12: goto st269;
		case 32: goto st263;
		case 34: goto tr693;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr694;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr690;
tr690:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st264;
tr708:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st264;
tr702:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st264;
st264:
	if ( ++p == pe )
		goto _test_eof264;
case 264:
#line 6855 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr696;
		case 10: goto tr697;
		case 12: goto tr698;
		case 32: goto tr696;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto st265;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto st264;
tr694:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st265;
tr712:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st265;
tr706:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st265;
st265:
	if ( ++p == pe )
		goto _test_eof265;
case 265:
#line 6886 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st266;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st267;
	goto st264;
st266:
	if ( ++p == pe )
		goto _test_eof266;
case 266:
	switch( (*p) ) {
		case 9: goto tr703;
		case 10: goto tr704;
		case 12: goto tr705;
		case 32: goto tr703;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto tr706;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr702;
st267:
	if ( ++p == pe )
		goto _test_eof267;
case 267:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st268;
	goto st0;
st268:
	if ( ++p == pe )
		goto _test_eof268;
case 268:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st264;
	goto st0;
tr710:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st269;
tr688:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 889 "./src/zscan_rfc1035.rl"
	{ z->uv_3 = z->uval; }
	goto st269;
st269:
	if ( ++p == pe )
		goto _test_eof269;
case 269:
#line 6936 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr709;
		case 10: goto st0;
		case 12: goto tr710;
		case 32: goto tr709;
		case 34: goto tr711;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr712;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr708;
tr693:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st270;
tr711:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st270;
tr717:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st270;
st270:
	if ( ++p == pe )
		goto _test_eof270;
case 270:
#line 6968 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto st271;
		case 34: goto st272;
		case 92: goto st273;
	}
	goto st270;
tr718:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st271;
st271:
	if ( ++p == pe )
		goto _test_eof271;
case 271:
#line 6983 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto tr718;
		case 34: goto tr719;
		case 92: goto tr720;
	}
	goto tr717;
tr719:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st272;
st272:
	if ( ++p == pe )
		goto _test_eof272;
case 272:
#line 6998 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr721;
		case 10: goto tr722;
		case 12: goto tr723;
		case 32: goto tr721;
	}
	goto st0;
tr720:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st273;
st273:
	if ( ++p == pe )
		goto _test_eof273;
case 273:
#line 7014 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st271;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st274;
	goto st270;
st274:
	if ( ++p == pe )
		goto _test_eof274;
case 274:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st275;
	goto st0;
st275:
	if ( ++p == pe )
		goto _test_eof275;
case 275:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st270;
	goto st0;
tr16:
#line 885 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; }
	goto st276;
tr55:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st276;
tr28:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 885 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->def_ttl; }
	goto st276;
st276:
	if ( ++p == pe )
		goto _test_eof276;
case 276:
#line 7052 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 88: goto st277;
		case 89: goto st296;
		case 120: goto st277;
		case 121: goto st296;
	}
	goto st0;
st277:
	if ( ++p == pe )
		goto _test_eof277;
case 277:
	switch( (*p) ) {
		case 84: goto st278;
		case 116: goto st278;
	}
	goto st0;
st278:
	if ( ++p == pe )
		goto _test_eof278;
case 278:
	switch( (*p) ) {
		case 9: goto st279;
		case 12: goto st295;
		case 32: goto st279;
	}
	goto st0;
st279:
	if ( ++p == pe )
		goto _test_eof279;
case 279:
	switch( (*p) ) {
		case 9: goto tr732;
		case 10: goto st0;
		case 12: goto tr733;
		case 32: goto tr732;
		case 34: goto tr734;
		case 59: goto st0;
		case 92: goto tr735;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr731;
tr742:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st280;
tr748:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st280;
tr731:
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st280;
tr770:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st280;
tr779:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st280;
tr762:
#line 871 "./src/zscan_rfc1035.rl"
	{ z->tstart++; text_add_tok(z, p - z->tstart - 1, true); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st280;
st280:
	if ( ++p == pe )
		goto _test_eof280;
case 280:
#line 7133 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr737;
		case 10: goto tr738;
		case 12: goto tr739;
		case 32: goto tr737;
		case 34: goto tr740;
		case 59: goto st0;
		case 92: goto st286;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto st280;
tr749:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st281;
tr737:
#line 870 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, true); }
	goto st281;
tr763:
#line 871 "./src/zscan_rfc1035.rl"
	{ z->tstart++; text_add_tok(z, p - z->tstart - 1, true); }
	goto st281;
tr771:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 870 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, true); }
	goto st281;
st281:
	if ( ++p == pe )
		goto _test_eof281;
case 281:
#line 7168 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st281;
		case 10: goto tr744;
		case 12: goto st282;
		case 32: goto st281;
		case 34: goto tr746;
		case 59: goto st0;
		case 92: goto tr747;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr742;
tr751:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st282;
tr739:
#line 870 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, true); }
	goto st282;
tr765:
#line 871 "./src/zscan_rfc1035.rl"
	{ z->tstart++; text_add_tok(z, p - z->tstart - 1, true); }
	goto st282;
tr773:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 870 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, true); }
	goto st282;
st282:
	if ( ++p == pe )
		goto _test_eof282;
case 282:
#line 7203 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr749;
		case 10: goto tr750;
		case 12: goto tr751;
		case 32: goto tr749;
		case 34: goto tr752;
		case 59: goto st0;
		case 92: goto tr753;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr748;
tr746:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st283;
tr752:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st283;
tr734:
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st283;
tr758:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st283;
tr782:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st283;
tr740:
#line 870 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, true); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st283;
tr766:
#line 871 "./src/zscan_rfc1035.rl"
	{ z->tstart++; text_add_tok(z, p - z->tstart - 1, true); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st283;
tr774:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 870 "./src/zscan_rfc1035.rl"
	{ text_add_tok(z, p - z->tstart, true); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st283;
st283:
	if ( ++p == pe )
		goto _test_eof283;
case 283:
#line 7268 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto st284;
		case 34: goto st285;
		case 92: goto st290;
	}
	goto st283;
tr759:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st284;
st284:
	if ( ++p == pe )
		goto _test_eof284;
case 284:
#line 7283 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto tr759;
		case 34: goto tr760;
		case 92: goto tr761;
	}
	goto tr758;
tr760:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st285;
st285:
	if ( ++p == pe )
		goto _test_eof285;
case 285:
#line 7298 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr763;
		case 10: goto tr764;
		case 12: goto tr765;
		case 32: goto tr763;
		case 34: goto tr766;
		case 59: goto st0;
		case 92: goto tr767;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr762;
tr747:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st286;
tr753:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st286;
tr735:
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st286;
tr775:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st286;
tr783:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st286;
tr767:
#line 871 "./src/zscan_rfc1035.rl"
	{ z->tstart++; text_add_tok(z, p - z->tstart - 1, true); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st286;
st286:
	if ( ++p == pe )
		goto _test_eof286;
case 286:
#line 7349 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st287;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st288;
	goto st280;
st287:
	if ( ++p == pe )
		goto _test_eof287;
case 287:
	switch( (*p) ) {
		case 9: goto tr771;
		case 10: goto tr772;
		case 12: goto tr773;
		case 32: goto tr771;
		case 34: goto tr774;
		case 59: goto st0;
		case 92: goto tr775;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr770;
st288:
	if ( ++p == pe )
		goto _test_eof288;
case 288:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st289;
	goto st0;
st289:
	if ( ++p == pe )
		goto _test_eof289;
case 289:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st280;
	goto st0;
tr761:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st290;
st290:
	if ( ++p == pe )
		goto _test_eof290;
case 290:
#line 7393 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st284;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st291;
	goto st283;
st291:
	if ( ++p == pe )
		goto _test_eof291;
case 291:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st292;
	goto st0;
st292:
	if ( ++p == pe )
		goto _test_eof292;
case 292:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st283;
	goto st0;
tr732:
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
	goto st293;
tr780:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
	goto st293;
st293:
	if ( ++p == pe )
		goto _test_eof293;
case 293:
#line 7427 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr732;
		case 10: goto tr744;
		case 12: goto tr733;
		case 32: goto tr732;
		case 34: goto tr734;
		case 59: goto st0;
		case 92: goto tr735;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr731;
tr733:
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
	goto st294;
tr781:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 869 "./src/zscan_rfc1035.rl"
	{ text_start(z); }
	goto st294;
st294:
	if ( ++p == pe )
		goto _test_eof294;
case 294:
#line 7454 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr780;
		case 10: goto tr750;
		case 12: goto tr781;
		case 32: goto tr780;
		case 34: goto tr782;
		case 59: goto st0;
		case 92: goto tr783;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr779;
st295:
	if ( ++p == pe )
		goto _test_eof295;
case 295:
	switch( (*p) ) {
		case 9: goto tr780;
		case 10: goto st0;
		case 12: goto tr781;
		case 32: goto tr780;
		case 34: goto tr782;
		case 59: goto st0;
		case 92: goto tr783;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr779;
st296:
	if ( ++p == pe )
		goto _test_eof296;
case 296:
	switch( (*p) ) {
		case 80: goto st297;
		case 112: goto st297;
	}
	goto st0;
st297:
	if ( ++p == pe )
		goto _test_eof297;
case 297:
	switch( (*p) ) {
		case 69: goto st298;
		case 101: goto st298;
	}
	goto st0;
st298:
	if ( ++p == pe )
		goto _test_eof298;
case 298:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr786;
	goto st0;
tr786:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st299;
st299:
	if ( ++p == pe )
		goto _test_eof299;
case 299:
#line 7516 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr787;
		case 12: goto tr788;
		case 32: goto tr787;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st299;
	goto st0;
tr793:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st300;
tr787:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
	goto st300;
st300:
	if ( ++p == pe )
		goto _test_eof300;
case 300:
#line 7539 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st300;
		case 12: goto st301;
		case 32: goto st300;
		case 92: goto st302;
	}
	goto st0;
tr794:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st301;
tr788:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
	goto st301;
st301:
	if ( ++p == pe )
		goto _test_eof301;
case 301:
#line 7561 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr793;
		case 12: goto tr794;
		case 32: goto tr793;
		case 92: goto tr795;
	}
	goto st0;
tr795:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st302;
st302:
	if ( ++p == pe )
		goto _test_eof302;
case 302:
#line 7577 "src/zscan_rfc1035.c"
	if ( (*p) == 35 )
		goto st303;
	goto st0;
st303:
	if ( ++p == pe )
		goto _test_eof303;
case 303:
	switch( (*p) ) {
		case 9: goto st304;
		case 12: goto st305;
		case 32: goto st304;
	}
	goto st0;
tr800:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st304;
st304:
	if ( ++p == pe )
		goto _test_eof304;
case 304:
#line 7599 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st304;
		case 12: goto st305;
		case 32: goto st304;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr799;
	goto st0;
tr801:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st305;
st305:
	if ( ++p == pe )
		goto _test_eof305;
case 305:
#line 7616 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr800;
		case 12: goto tr801;
		case 32: goto tr800;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr802;
	goto st0;
tr799:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st306;
tr802:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st306;
st306:
	if ( ++p == pe )
		goto _test_eof306;
case 306:
#line 7639 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr803;
		case 12: goto tr804;
		case 32: goto tr803;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st306;
	goto st0;
tr803:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 911 "./src/zscan_rfc1035.rl"
	{ rfc3597_data_setup(z); }
	goto st307;
tr806:
#line 908 "./src/zscan_rfc1035.rl"
	{ rec_rfc3597(z); }
	goto st307;
tr810:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 908 "./src/zscan_rfc1035.rl"
	{ rec_rfc3597(z); }
	goto st307;
st307:
	if ( ++p == pe )
		goto _test_eof307;
case 307:
#line 7668 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr806;
		case 10: goto tr807;
		case 12: goto tr808;
		case 32: goto tr806;
	}
	if ( (*p) < 65 ) {
		if ( 48 <= (*p) && (*p) <= 57 )
			goto tr809;
	} else if ( (*p) > 70 ) {
		if ( 97 <= (*p) && (*p) <= 102 )
			goto tr809;
	} else
		goto tr809;
	goto st0;
tr804:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 911 "./src/zscan_rfc1035.rl"
	{ rfc3597_data_setup(z); }
	goto st308;
tr808:
#line 908 "./src/zscan_rfc1035.rl"
	{ rec_rfc3597(z); }
	goto st308;
tr812:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 908 "./src/zscan_rfc1035.rl"
	{ rec_rfc3597(z); }
	goto st308;
st308:
	if ( ++p == pe )
		goto _test_eof308;
case 308:
#line 7704 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr810;
		case 10: goto tr811;
		case 12: goto tr812;
		case 32: goto tr810;
	}
	if ( (*p) < 65 ) {
		if ( 48 <= (*p) && (*p) <= 57 )
			goto tr813;
	} else if ( (*p) > 70 ) {
		if ( 97 <= (*p) && (*p) <= 102 )
			goto tr813;
	} else
		goto tr813;
	goto st0;
tr809:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st309;
tr813:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st309;
tr818:
#line 912 "./src/zscan_rfc1035.rl"
	{ rfc3597_octet(z); }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st309;
st309:
	if ( ++p == pe )
		goto _test_eof309;
case 309:
#line 7740 "src/zscan_rfc1035.c"
	if ( (*p) < 65 ) {
		if ( 48 <= (*p) && (*p) <= 57 )
			goto st310;
	} else if ( (*p) > 70 ) {
		if ( 97 <= (*p) && (*p) <= 102 )
			goto st310;
	} else
		goto st310;
	goto st0;
st310:
	if ( ++p == pe )
		goto _test_eof310;
case 310:
	switch( (*p) ) {
		case 9: goto tr815;
		case 10: goto tr816;
		case 12: goto tr817;
		case 32: goto tr815;
	}
	if ( (*p) < 65 ) {
		if ( 48 <= (*p) && (*p) <= 57 )
			goto tr818;
	} else if ( (*p) > 70 ) {
		if ( 97 <= (*p) && (*p) <= 102 )
			goto tr818;
	} else
		goto tr818;
	goto st0;
tr821:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st311;
tr815:
#line 912 "./src/zscan_rfc1035.rl"
	{ rfc3597_octet(z); }
	goto st311;
st311:
	if ( ++p == pe )
		goto _test_eof311;
case 311:
#line 7781 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st311;
		case 10: goto tr807;
		case 12: goto st312;
		case 32: goto st311;
	}
	if ( (*p) < 65 ) {
		if ( 48 <= (*p) && (*p) <= 57 )
			goto tr809;
	} else if ( (*p) > 70 ) {
		if ( 97 <= (*p) && (*p) <= 102 )
			goto tr809;
	} else
		goto tr809;
	goto st0;
tr822:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st312;
tr817:
#line 912 "./src/zscan_rfc1035.rl"
	{ rfc3597_octet(z); }
	goto st312;
st312:
	if ( ++p == pe )
		goto _test_eof312;
case 312:
#line 7809 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr821;
		case 10: goto tr811;
		case 12: goto tr822;
		case 32: goto tr821;
	}
	if ( (*p) < 65 ) {
		if ( 48 <= (*p) && (*p) <= 57 )
			goto tr813;
	} else if ( (*p) > 70 ) {
		if ( 97 <= (*p) && (*p) <= 102 )
			goto tr813;
	} else
		goto tr813;
	goto st0;
tr246:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
	goto st313;
tr836:
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
	goto st313;
st313:
	if ( ++p == pe )
		goto _test_eof313;
case 313:
#line 7839 "src/zscan_rfc1035.c"
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr823;
	goto st0;
tr823:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st314;
st314:
	if ( ++p == pe )
		goto _test_eof314;
case 314:
#line 7851 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr824;
		case 12: goto tr825;
		case 32: goto tr824;
		case 68: goto tr827;
		case 72: goto tr827;
		case 77: goto tr827;
		case 87: goto tr827;
		case 100: goto tr827;
		case 104: goto tr827;
		case 109: goto tr827;
		case 119: goto tr827;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st314;
	goto st0;
tr830:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st315;
tr824:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 888 "./src/zscan_rfc1035.rl"
	{ z->uv_2 = z->uval; }
#line 883 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uv_1; z->ttl_min = z->uv_2 ? z->uv_2 : z->uv_1 >> 1; }
	goto st315;
tr832:
#line 888 "./src/zscan_rfc1035.rl"
	{ z->uv_2 = z->uval; }
#line 883 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uv_1; z->ttl_min = z->uv_2 ? z->uv_2 : z->uv_1 >> 1; }
	goto st315;
st315:
	if ( ++p == pe )
		goto _test_eof315;
case 315:
#line 7890 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st315;
		case 12: goto st316;
		case 32: goto st315;
		case 68: goto st54;
		case 100: goto st54;
	}
	goto st0;
tr831:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st316;
tr825:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 888 "./src/zscan_rfc1035.rl"
	{ z->uv_2 = z->uval; }
#line 883 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uv_1; z->ttl_min = z->uv_2 ? z->uv_2 : z->uv_1 >> 1; }
	goto st316;
tr833:
#line 888 "./src/zscan_rfc1035.rl"
	{ z->uv_2 = z->uval; }
#line 883 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uv_1; z->ttl_min = z->uv_2 ? z->uv_2 : z->uv_1 >> 1; }
	goto st316;
st316:
	if ( ++p == pe )
		goto _test_eof316;
case 316:
#line 7921 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr830;
		case 12: goto tr831;
		case 32: goto tr830;
		case 68: goto tr49;
		case 100: goto tr49;
	}
	goto st0;
tr827:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 880 "./src/zscan_rfc1035.rl"
	{ mult_uval(z, (*p)); }
	goto st317;
st317:
	if ( ++p == pe )
		goto _test_eof317;
case 317:
#line 7940 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr832;
		case 12: goto tr833;
		case 32: goto tr832;
	}
	goto st0;
tr248:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 880 "./src/zscan_rfc1035.rl"
	{ mult_uval(z, (*p)); }
	goto st318;
st318:
	if ( ++p == pe )
		goto _test_eof318;
case 318:
#line 7957 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr834;
		case 12: goto tr835;
		case 32: goto tr834;
		case 47: goto tr836;
	}
	goto st0;
tr1027:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st319;
tr841:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st319;
tr1034:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st319;
st319:
	if ( ++p == pe )
		goto _test_eof319;
case 319:
#line 7983 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto st320;
		case 34: goto st321;
		case 92: goto st322;
	}
	goto st319;
tr842:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st320;
st320:
	if ( ++p == pe )
		goto _test_eof320;
case 320:
#line 7998 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto tr842;
		case 34: goto tr843;
		case 92: goto tr844;
	}
	goto tr841;
tr843:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st321;
st321:
	if ( ++p == pe )
		goto _test_eof321;
case 321:
#line 8013 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr845;
		case 12: goto tr846;
		case 32: goto tr845;
	}
	goto st0;
tr844:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st322;
st322:
	if ( ++p == pe )
		goto _test_eof322;
case 322:
#line 8028 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st320;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st323;
	goto st319;
st323:
	if ( ++p == pe )
		goto _test_eof323;
case 323:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st324;
	goto st0;
st324:
	if ( ++p == pe )
		goto _test_eof324;
case 324:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st319;
	goto st0;
tr1035:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st325;
st325:
	if ( ++p == pe )
		goto _test_eof325;
case 325:
#line 8056 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 73: goto st326;
		case 79: goto st359;
		case 84: goto st378;
		case 105: goto st326;
		case 111: goto st359;
		case 116: goto st378;
	}
	goto st0;
st326:
	if ( ++p == pe )
		goto _test_eof326;
case 326:
	switch( (*p) ) {
		case 78: goto st327;
		case 110: goto st327;
	}
	goto st0;
st327:
	if ( ++p == pe )
		goto _test_eof327;
case 327:
	switch( (*p) ) {
		case 67: goto st328;
		case 99: goto st328;
	}
	goto st0;
st328:
	if ( ++p == pe )
		goto _test_eof328;
case 328:
	switch( (*p) ) {
		case 76: goto st329;
		case 108: goto st329;
	}
	goto st0;
st329:
	if ( ++p == pe )
		goto _test_eof329;
case 329:
	switch( (*p) ) {
		case 85: goto st330;
		case 117: goto st330;
	}
	goto st0;
st330:
	if ( ++p == pe )
		goto _test_eof330;
case 330:
	switch( (*p) ) {
		case 68: goto st331;
		case 100: goto st331;
	}
	goto st0;
st331:
	if ( ++p == pe )
		goto _test_eof331;
case 331:
	switch( (*p) ) {
		case 69: goto st332;
		case 101: goto st332;
	}
	goto st0;
st332:
	if ( ++p == pe )
		goto _test_eof332;
case 332:
	switch( (*p) ) {
		case 9: goto tr858;
		case 12: goto tr859;
		case 32: goto tr858;
	}
	goto st0;
tr915:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st333;
tr858:
#line 858 "./src/zscan_rfc1035.rl"
	{ dname_copy(z->rhs_dname, z->origin); }
	goto st333;
st333:
	if ( ++p == pe )
		goto _test_eof333;
case 333:
#line 8142 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st333;
		case 10: goto st0;
		case 12: goto st352;
		case 32: goto st333;
		case 34: goto tr863;
		case 59: goto st0;
		case 92: goto tr864;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr860;
tr860:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st334;
tr914:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st334;
tr908:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st334;
st334:
	if ( ++p == pe )
		goto _test_eof334;
case 334:
#line 8173 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr866;
		case 10: goto tr867;
		case 12: goto tr868;
		case 32: goto tr866;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto st348;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto st334;
tr889:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st335;
tr866:
#line 865 "./src/zscan_rfc1035.rl"
	{ set_filename(z, p - z->tstart); }
	goto st335;
tr909:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 865 "./src/zscan_rfc1035.rl"
	{ set_filename(z, p - z->tstart); }
	goto st335;
tr927:
#line 866 "./src/zscan_rfc1035.rl"
	{ z->tstart++; set_filename(z, p - z->tstart - 1); }
	goto st335;
st335:
	if ( ++p == pe )
		goto _test_eof335;
case 335:
#line 8208 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st335;
		case 10: goto st0;
		case 12: goto st341;
		case 32: goto st335;
		case 34: goto tr873;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr874;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr870;
tr870:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st336;
tr888:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st336;
tr882:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st336;
st336:
	if ( ++p == pe )
		goto _test_eof336;
case 336:
#line 8240 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr876;
		case 10: goto tr877;
		case 12: goto tr878;
		case 32: goto tr876;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto st337;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto st336;
tr874:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st337;
tr892:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st337;
tr886:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st337;
st337:
	if ( ++p == pe )
		goto _test_eof337;
case 337:
#line 8271 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st338;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st339;
	goto st336;
st338:
	if ( ++p == pe )
		goto _test_eof338;
case 338:
	switch( (*p) ) {
		case 9: goto tr883;
		case 10: goto tr884;
		case 12: goto tr885;
		case 32: goto tr883;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto tr886;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr882;
st339:
	if ( ++p == pe )
		goto _test_eof339;
case 339:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st340;
	goto st0;
st340:
	if ( ++p == pe )
		goto _test_eof340;
case 340:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st336;
	goto st0;
tr890:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st341;
tr868:
#line 865 "./src/zscan_rfc1035.rl"
	{ set_filename(z, p - z->tstart); }
	goto st341;
tr911:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 865 "./src/zscan_rfc1035.rl"
	{ set_filename(z, p - z->tstart); }
	goto st341;
tr929:
#line 866 "./src/zscan_rfc1035.rl"
	{ z->tstart++; set_filename(z, p - z->tstart - 1); }
	goto st341;
st341:
	if ( ++p == pe )
		goto _test_eof341;
case 341:
#line 8329 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr889;
		case 10: goto st0;
		case 12: goto tr890;
		case 32: goto tr889;
		case 34: goto tr891;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr892;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr888;
tr873:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st342;
tr891:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st342;
tr897:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st342;
st342:
	if ( ++p == pe )
		goto _test_eof342;
case 342:
#line 8361 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto st343;
		case 34: goto st344;
		case 92: goto st345;
	}
	goto st342;
tr898:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st343;
st343:
	if ( ++p == pe )
		goto _test_eof343;
case 343:
#line 8376 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto tr898;
		case 34: goto tr899;
		case 92: goto tr900;
	}
	goto tr897;
tr899:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st344;
st344:
	if ( ++p == pe )
		goto _test_eof344;
case 344:
#line 8391 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr901;
		case 10: goto tr902;
		case 12: goto tr903;
		case 32: goto tr901;
	}
	goto st0;
tr900:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st345;
st345:
	if ( ++p == pe )
		goto _test_eof345;
case 345:
#line 8407 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st343;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st346;
	goto st342;
st346:
	if ( ++p == pe )
		goto _test_eof346;
case 346:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st347;
	goto st0;
st347:
	if ( ++p == pe )
		goto _test_eof347;
case 347:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st342;
	goto st0;
tr864:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st348;
tr918:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st348;
tr912:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st348;
st348:
	if ( ++p == pe )
		goto _test_eof348;
case 348:
#line 8445 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st349;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st350;
	goto st334;
st349:
	if ( ++p == pe )
		goto _test_eof349;
case 349:
	switch( (*p) ) {
		case 9: goto tr909;
		case 10: goto tr910;
		case 12: goto tr911;
		case 32: goto tr909;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto tr912;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr908;
st350:
	if ( ++p == pe )
		goto _test_eof350;
case 350:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st351;
	goto st0;
st351:
	if ( ++p == pe )
		goto _test_eof351;
case 351:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st334;
	goto st0;
tr916:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st352;
tr859:
#line 858 "./src/zscan_rfc1035.rl"
	{ dname_copy(z->rhs_dname, z->origin); }
	goto st352;
st352:
	if ( ++p == pe )
		goto _test_eof352;
case 352:
#line 8493 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr915;
		case 10: goto st0;
		case 12: goto tr916;
		case 32: goto tr915;
		case 34: goto tr917;
		case 59: goto st0;
		case 92: goto tr918;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr914;
tr863:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st353;
tr917:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st353;
tr923:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st353;
st353:
	if ( ++p == pe )
		goto _test_eof353;
case 353:
#line 8524 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto st354;
		case 34: goto st355;
		case 92: goto st356;
	}
	goto st353;
tr924:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st354;
st354:
	if ( ++p == pe )
		goto _test_eof354;
case 354:
#line 8539 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto tr924;
		case 34: goto tr925;
		case 92: goto tr926;
	}
	goto tr923;
tr925:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st355;
st355:
	if ( ++p == pe )
		goto _test_eof355;
case 355:
#line 8554 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr927;
		case 10: goto tr928;
		case 12: goto tr929;
		case 32: goto tr927;
	}
	goto st0;
tr926:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st356;
st356:
	if ( ++p == pe )
		goto _test_eof356;
case 356:
#line 8570 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st354;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st357;
	goto st353;
st357:
	if ( ++p == pe )
		goto _test_eof357;
case 357:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st358;
	goto st0;
st358:
	if ( ++p == pe )
		goto _test_eof358;
case 358:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st353;
	goto st0;
st359:
	if ( ++p == pe )
		goto _test_eof359;
case 359:
	switch( (*p) ) {
		case 82: goto st360;
		case 114: goto st360;
	}
	goto st0;
st360:
	if ( ++p == pe )
		goto _test_eof360;
case 360:
	switch( (*p) ) {
		case 73: goto st361;
		case 105: goto st361;
	}
	goto st0;
st361:
	if ( ++p == pe )
		goto _test_eof361;
case 361:
	switch( (*p) ) {
		case 71: goto st362;
		case 103: goto st362;
	}
	goto st0;
st362:
	if ( ++p == pe )
		goto _test_eof362;
case 362:
	switch( (*p) ) {
		case 73: goto st363;
		case 105: goto st363;
	}
	goto st0;
st363:
	if ( ++p == pe )
		goto _test_eof363;
case 363:
	switch( (*p) ) {
		case 78: goto st364;
		case 110: goto st364;
	}
	goto st0;
st364:
	if ( ++p == pe )
		goto _test_eof364;
case 364:
	switch( (*p) ) {
		case 9: goto st365;
		case 12: goto st371;
		case 32: goto st365;
	}
	goto st0;
tr956:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st365;
st365:
	if ( ++p == pe )
		goto _test_eof365;
case 365:
#line 8653 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st365;
		case 10: goto st0;
		case 12: goto st371;
		case 32: goto st365;
		case 34: goto tr940;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr941;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr939;
tr939:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st366;
tr955:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st366;
tr949:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st366;
st366:
	if ( ++p == pe )
		goto _test_eof366;
case 366:
#line 8685 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr943;
		case 10: goto tr944;
		case 12: goto tr945;
		case 32: goto tr943;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto st367;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto st366;
tr941:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st367;
tr959:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st367;
tr953:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st367;
st367:
	if ( ++p == pe )
		goto _test_eof367;
case 367:
#line 8716 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st368;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st369;
	goto st366;
st368:
	if ( ++p == pe )
		goto _test_eof368;
case 368:
	switch( (*p) ) {
		case 9: goto tr950;
		case 10: goto tr951;
		case 12: goto tr952;
		case 32: goto tr950;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto tr953;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr949;
st369:
	if ( ++p == pe )
		goto _test_eof369;
case 369:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st370;
	goto st0;
st370:
	if ( ++p == pe )
		goto _test_eof370;
case 370:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st366;
	goto st0;
tr957:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st371;
st371:
	if ( ++p == pe )
		goto _test_eof371;
case 371:
#line 8760 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr956;
		case 10: goto st0;
		case 12: goto tr957;
		case 32: goto tr956;
		case 34: goto tr958;
		case 36: goto st0;
		case 59: goto st0;
		case 92: goto tr959;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr955;
tr940:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st372;
tr958:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st372;
tr964:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st372;
st372:
	if ( ++p == pe )
		goto _test_eof372;
case 372:
#line 8792 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto st373;
		case 34: goto st374;
		case 92: goto st375;
	}
	goto st372;
tr965:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st373;
st373:
	if ( ++p == pe )
		goto _test_eof373;
case 373:
#line 8807 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 10: goto tr965;
		case 34: goto tr966;
		case 92: goto tr967;
	}
	goto tr964;
tr966:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st374;
st374:
	if ( ++p == pe )
		goto _test_eof374;
case 374:
#line 8822 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr968;
		case 10: goto tr969;
		case 12: goto tr970;
		case 32: goto tr968;
	}
	goto st0;
tr967:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st375;
st375:
	if ( ++p == pe )
		goto _test_eof375;
case 375:
#line 8838 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st373;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st376;
	goto st372;
st376:
	if ( ++p == pe )
		goto _test_eof376;
case 376:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st377;
	goto st0;
st377:
	if ( ++p == pe )
		goto _test_eof377;
case 377:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st372;
	goto st0;
st378:
	if ( ++p == pe )
		goto _test_eof378;
case 378:
	switch( (*p) ) {
		case 84: goto st379;
		case 116: goto st379;
	}
	goto st0;
st379:
	if ( ++p == pe )
		goto _test_eof379;
case 379:
	switch( (*p) ) {
		case 76: goto st380;
		case 108: goto st380;
	}
	goto st0;
st380:
	if ( ++p == pe )
		goto _test_eof380;
case 380:
	switch( (*p) ) {
		case 9: goto st381;
		case 12: goto st382;
		case 32: goto st381;
	}
	goto st0;
tr978:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st381;
st381:
	if ( ++p == pe )
		goto _test_eof381;
case 381:
#line 8894 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st381;
		case 12: goto st382;
		case 32: goto st381;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr977;
	goto st0;
tr979:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st382;
st382:
	if ( ++p == pe )
		goto _test_eof382;
case 382:
#line 8911 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr978;
		case 12: goto tr979;
		case 32: goto tr978;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr980;
	goto st0;
tr977:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st383;
tr980:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st383;
st383:
	if ( ++p == pe )
		goto _test_eof383;
case 383:
#line 8934 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr981;
		case 10: goto tr982;
		case 12: goto tr983;
		case 32: goto tr981;
		case 68: goto tr985;
		case 72: goto tr985;
		case 77: goto tr985;
		case 87: goto tr985;
		case 100: goto tr985;
		case 104: goto tr985;
		case 109: goto tr985;
		case 119: goto tr985;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st383;
	goto st0;
tr985:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 880 "./src/zscan_rfc1035.rl"
	{ mult_uval(z, (*p)); }
	goto st384;
st384:
	if ( ++p == pe )
		goto _test_eof384;
case 384:
#line 8962 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr986;
		case 10: goto tr987;
		case 12: goto tr988;
		case 32: goto tr986;
	}
	goto st0;
tr1029:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st385;
tr994:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st385;
tr1036:
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st385;
st385:
	if ( ++p == pe )
		goto _test_eof385;
case 385:
#line 8988 "src/zscan_rfc1035.c"
	if ( (*p) == 10 )
		goto st386;
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st387;
	goto st1;
st386:
	if ( ++p == pe )
		goto _test_eof386;
case 386:
	switch( (*p) ) {
		case 9: goto tr992;
		case 10: goto st0;
		case 12: goto tr993;
		case 32: goto tr992;
		case 34: goto st0;
		case 59: goto st0;
		case 92: goto tr994;
	}
	if ( 40 <= (*p) && (*p) <= 41 )
		goto st0;
	goto tr991;
st387:
	if ( ++p == pe )
		goto _test_eof387;
case 387:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st388;
	goto st0;
st388:
	if ( ++p == pe )
		goto _test_eof388;
case 388:
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st1;
	goto st0;
st389:
	if ( ++p == pe )
		goto _test_eof389;
case 389:
	switch( (*p) ) {
		case 65: goto st390;
		case 97: goto st390;
	}
	goto st0;
st390:
	if ( ++p == pe )
		goto _test_eof390;
case 390:
	switch( (*p) ) {
		case 65: goto st391;
		case 97: goto st391;
	}
	goto st0;
st391:
	if ( ++p == pe )
		goto _test_eof391;
case 391:
	switch( (*p) ) {
		case 9: goto st392;
		case 12: goto st393;
		case 32: goto st392;
	}
	goto st0;
tr1001:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st392;
st392:
	if ( ++p == pe )
		goto _test_eof392;
case 392:
#line 9060 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st392;
		case 12: goto st393;
		case 32: goto st392;
		case 46: goto tr1000;
	}
	if ( (*p) < 65 ) {
		if ( 48 <= (*p) && (*p) <= 58 )
			goto tr1000;
	} else if ( (*p) > 70 ) {
		if ( 97 <= (*p) && (*p) <= 102 )
			goto tr1000;
	} else
		goto tr1000;
	goto st0;
tr1002:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st393;
st393:
	if ( ++p == pe )
		goto _test_eof393;
case 393:
#line 9084 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr1001;
		case 12: goto tr1002;
		case 32: goto tr1001;
		case 46: goto tr1003;
	}
	if ( (*p) < 65 ) {
		if ( 48 <= (*p) && (*p) <= 58 )
			goto tr1003;
	} else if ( (*p) > 70 ) {
		if ( 97 <= (*p) && (*p) <= 102 )
			goto tr1003;
	} else
		goto tr1003;
	goto st0;
tr1000:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st394;
tr1003:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st394;
st394:
	if ( ++p == pe )
		goto _test_eof394;
case 394:
#line 9114 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr1004;
		case 10: goto tr1005;
		case 12: goto tr1006;
		case 32: goto tr1004;
		case 46: goto st394;
	}
	if ( (*p) < 65 ) {
		if ( 48 <= (*p) && (*p) <= 58 )
			goto st394;
	} else if ( (*p) > 70 ) {
		if ( 97 <= (*p) && (*p) <= 102 )
			goto st394;
	} else
		goto st394;
	goto st0;
tr50:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st395;
st395:
	if ( ++p == pe )
		goto _test_eof395;
case 395:
#line 9139 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 78: goto st396;
		case 110: goto st396;
	}
	goto st0;
st396:
	if ( ++p == pe )
		goto _test_eof396;
case 396:
	switch( (*p) ) {
		case 9: goto st90;
		case 12: goto st91;
		case 32: goto st90;
	}
	goto st0;
tr31:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
	goto st397;
tr1025:
#line 887 "./src/zscan_rfc1035.rl"
	{ z->uv_1 = z->uval; }
	goto st397;
st397:
	if ( ++p == pe )
		goto _test_eof397;
case 397:
#line 9169 "src/zscan_rfc1035.c"
	if ( 48 <= (*p) && (*p) <= 57 )
		goto tr1009;
	goto st0;
tr1009:
#line 848 "./src/zscan_rfc1035.rl"
	{ z->tstart = p; }
	goto st398;
st398:
	if ( ++p == pe )
		goto _test_eof398;
case 398:
#line 9181 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr1010;
		case 12: goto tr1011;
		case 32: goto tr1010;
		case 68: goto tr1013;
		case 72: goto tr1013;
		case 77: goto tr1013;
		case 87: goto tr1013;
		case 100: goto tr1013;
		case 104: goto tr1013;
		case 109: goto tr1013;
		case 119: goto tr1013;
	}
	if ( 48 <= (*p) && (*p) <= 57 )
		goto st398;
	goto st0;
tr1017:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st399;
tr1010:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 888 "./src/zscan_rfc1035.rl"
	{ z->uv_2 = z->uval; }
#line 883 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uv_1; z->ttl_min = z->uv_2 ? z->uv_2 : z->uv_1 >> 1; }
	goto st399;
tr1021:
#line 888 "./src/zscan_rfc1035.rl"
	{ z->uv_2 = z->uval; }
#line 883 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uv_1; z->ttl_min = z->uv_2 ? z->uv_2 : z->uv_1 >> 1; }
	goto st399;
st399:
	if ( ++p == pe )
		goto _test_eof399;
case 399:
#line 9220 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto st399;
		case 12: goto st400;
		case 32: goto st399;
		case 68: goto st54;
		case 73: goto st401;
		case 100: goto st54;
		case 105: goto st401;
	}
	goto st0;
tr1018:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st400;
tr1011:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 888 "./src/zscan_rfc1035.rl"
	{ z->uv_2 = z->uval; }
#line 883 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uv_1; z->ttl_min = z->uv_2 ? z->uv_2 : z->uv_1 >> 1; }
	goto st400;
tr1022:
#line 888 "./src/zscan_rfc1035.rl"
	{ z->uv_2 = z->uval; }
#line 883 "./src/zscan_rfc1035.rl"
	{ z->ttl  = z->uv_1; z->ttl_min = z->uv_2 ? z->uv_2 : z->uv_1 >> 1; }
	goto st400;
st400:
	if ( ++p == pe )
		goto _test_eof400;
case 400:
#line 9253 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr1017;
		case 12: goto tr1018;
		case 32: goto tr1017;
		case 68: goto tr49;
		case 73: goto tr1019;
		case 100: goto tr49;
		case 105: goto tr1019;
	}
	goto st0;
tr1019:
#line 920 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	goto st401;
st401:
	if ( ++p == pe )
		goto _test_eof401;
case 401:
#line 9272 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 78: goto st402;
		case 110: goto st402;
	}
	goto st0;
st402:
	if ( ++p == pe )
		goto _test_eof402;
case 402:
	switch( (*p) ) {
		case 9: goto st315;
		case 12: goto st316;
		case 32: goto st315;
	}
	goto st0;
tr1013:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 880 "./src/zscan_rfc1035.rl"
	{ mult_uval(z, (*p)); }
	goto st403;
st403:
	if ( ++p == pe )
		goto _test_eof403;
case 403:
#line 9298 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr1021;
		case 12: goto tr1022;
		case 32: goto tr1021;
	}
	goto st0;
tr33:
#line 879 "./src/zscan_rfc1035.rl"
	{ set_uval(z); }
#line 880 "./src/zscan_rfc1035.rl"
	{ mult_uval(z, (*p)); }
	goto st404;
st404:
	if ( ++p == pe )
		goto _test_eof404;
case 404:
#line 9315 "src/zscan_rfc1035.c"
	switch( (*p) ) {
		case 9: goto tr1023;
		case 12: goto tr1024;
		case 32: goto tr1023;
		case 47: goto tr1025;
	}
	goto st0;
	}
	_test_eof1: cs = 1; goto _test_eof; 
	_test_eof2: cs = 2; goto _test_eof; 
	_test_eof3: cs = 3; goto _test_eof; 
	_test_eof4: cs = 4; goto _test_eof; 
	_test_eof5: cs = 5; goto _test_eof; 
	_test_eof6: cs = 6; goto _test_eof; 
	_test_eof7: cs = 7; goto _test_eof; 
	_test_eof8: cs = 8; goto _test_eof; 
	_test_eof9: cs = 9; goto _test_eof; 
	_test_eof10: cs = 10; goto _test_eof; 
	_test_eof11: cs = 11; goto _test_eof; 
	_test_eof406: cs = 406; goto _test_eof; 
	_test_eof12: cs = 12; goto _test_eof; 
	_test_eof13: cs = 13; goto _test_eof; 
	_test_eof14: cs = 14; goto _test_eof; 
	_test_eof15: cs = 15; goto _test_eof; 
	_test_eof16: cs = 16; goto _test_eof; 
	_test_eof17: cs = 17; goto _test_eof; 
	_test_eof18: cs = 18; goto _test_eof; 
	_test_eof19: cs = 19; goto _test_eof; 
	_test_eof20: cs = 20; goto _test_eof; 
	_test_eof21: cs = 21; goto _test_eof; 
	_test_eof22: cs = 22; goto _test_eof; 
	_test_eof23: cs = 23; goto _test_eof; 
	_test_eof24: cs = 24; goto _test_eof; 
	_test_eof25: cs = 25; goto _test_eof; 
	_test_eof26: cs = 26; goto _test_eof; 
	_test_eof27: cs = 27; goto _test_eof; 
	_test_eof28: cs = 28; goto _test_eof; 
	_test_eof29: cs = 29; goto _test_eof; 
	_test_eof30: cs = 30; goto _test_eof; 
	_test_eof31: cs = 31; goto _test_eof; 
	_test_eof32: cs = 32; goto _test_eof; 
	_test_eof33: cs = 33; goto _test_eof; 
	_test_eof34: cs = 34; goto _test_eof; 
	_test_eof35: cs = 35; goto _test_eof; 
	_test_eof36: cs = 36; goto _test_eof; 
	_test_eof37: cs = 37; goto _test_eof; 
	_test_eof38: cs = 38; goto _test_eof; 
	_test_eof39: cs = 39; goto _test_eof; 
	_test_eof40: cs = 40; goto _test_eof; 
	_test_eof41: cs = 41; goto _test_eof; 
	_test_eof42: cs = 42; goto _test_eof; 
	_test_eof43: cs = 43; goto _test_eof; 
	_test_eof44: cs = 44; goto _test_eof; 
	_test_eof45: cs = 45; goto _test_eof; 
	_test_eof46: cs = 46; goto _test_eof; 
	_test_eof47: cs = 47; goto _test_eof; 
	_test_eof48: cs = 48; goto _test_eof; 
	_test_eof49: cs = 49; goto _test_eof; 
	_test_eof50: cs = 50; goto _test_eof; 
	_test_eof51: cs = 51; goto _test_eof; 
	_test_eof52: cs = 52; goto _test_eof; 
	_test_eof53: cs = 53; goto _test_eof; 
	_test_eof54: cs = 54; goto _test_eof; 
	_test_eof55: cs = 55; goto _test_eof; 
	_test_eof56: cs = 56; goto _test_eof; 
	_test_eof57: cs = 57; goto _test_eof; 
	_test_eof58: cs = 58; goto _test_eof; 
	_test_eof59: cs = 59; goto _test_eof; 
	_test_eof60: cs = 60; goto _test_eof; 
	_test_eof61: cs = 61; goto _test_eof; 
	_test_eof62: cs = 62; goto _test_eof; 
	_test_eof63: cs = 63; goto _test_eof; 
	_test_eof64: cs = 64; goto _test_eof; 
	_test_eof65: cs = 65; goto _test_eof; 
	_test_eof66: cs = 66; goto _test_eof; 
	_test_eof67: cs = 67; goto _test_eof; 
	_test_eof68: cs = 68; goto _test_eof; 
	_test_eof69: cs = 69; goto _test_eof; 
	_test_eof70: cs = 70; goto _test_eof; 
	_test_eof71: cs = 71; goto _test_eof; 
	_test_eof72: cs = 72; goto _test_eof; 
	_test_eof73: cs = 73; goto _test_eof; 
	_test_eof74: cs = 74; goto _test_eof; 
	_test_eof75: cs = 75; goto _test_eof; 
	_test_eof76: cs = 76; goto _test_eof; 
	_test_eof77: cs = 77; goto _test_eof; 
	_test_eof78: cs = 78; goto _test_eof; 
	_test_eof79: cs = 79; goto _test_eof; 
	_test_eof80: cs = 80; goto _test_eof; 
	_test_eof81: cs = 81; goto _test_eof; 
	_test_eof82: cs = 82; goto _test_eof; 
	_test_eof83: cs = 83; goto _test_eof; 
	_test_eof84: cs = 84; goto _test_eof; 
	_test_eof85: cs = 85; goto _test_eof; 
	_test_eof86: cs = 86; goto _test_eof; 
	_test_eof87: cs = 87; goto _test_eof; 
	_test_eof88: cs = 88; goto _test_eof; 
	_test_eof89: cs = 89; goto _test_eof; 
	_test_eof90: cs = 90; goto _test_eof; 
	_test_eof91: cs = 91; goto _test_eof; 
	_test_eof92: cs = 92; goto _test_eof; 
	_test_eof93: cs = 93; goto _test_eof; 
	_test_eof94: cs = 94; goto _test_eof; 
	_test_eof95: cs = 95; goto _test_eof; 
	_test_eof96: cs = 96; goto _test_eof; 
	_test_eof97: cs = 97; goto _test_eof; 
	_test_eof98: cs = 98; goto _test_eof; 
	_test_eof99: cs = 99; goto _test_eof; 
	_test_eof100: cs = 100; goto _test_eof; 
	_test_eof101: cs = 101; goto _test_eof; 
	_test_eof102: cs = 102; goto _test_eof; 
	_test_eof103: cs = 103; goto _test_eof; 
	_test_eof104: cs = 104; goto _test_eof; 
	_test_eof105: cs = 105; goto _test_eof; 
	_test_eof106: cs = 106; goto _test_eof; 
	_test_eof107: cs = 107; goto _test_eof; 
	_test_eof108: cs = 108; goto _test_eof; 
	_test_eof109: cs = 109; goto _test_eof; 
	_test_eof110: cs = 110; goto _test_eof; 
	_test_eof111: cs = 111; goto _test_eof; 
	_test_eof112: cs = 112; goto _test_eof; 
	_test_eof113: cs = 113; goto _test_eof; 
	_test_eof114: cs = 114; goto _test_eof; 
	_test_eof115: cs = 115; goto _test_eof; 
	_test_eof116: cs = 116; goto _test_eof; 
	_test_eof117: cs = 117; goto _test_eof; 
	_test_eof118: cs = 118; goto _test_eof; 
	_test_eof119: cs = 119; goto _test_eof; 
	_test_eof120: cs = 120; goto _test_eof; 
	_test_eof121: cs = 121; goto _test_eof; 
	_test_eof122: cs = 122; goto _test_eof; 
	_test_eof123: cs = 123; goto _test_eof; 
	_test_eof124: cs = 124; goto _test_eof; 
	_test_eof125: cs = 125; goto _test_eof; 
	_test_eof126: cs = 126; goto _test_eof; 
	_test_eof127: cs = 127; goto _test_eof; 
	_test_eof128: cs = 128; goto _test_eof; 
	_test_eof129: cs = 129; goto _test_eof; 
	_test_eof130: cs = 130; goto _test_eof; 
	_test_eof131: cs = 131; goto _test_eof; 
	_test_eof132: cs = 132; goto _test_eof; 
	_test_eof133: cs = 133; goto _test_eof; 
	_test_eof134: cs = 134; goto _test_eof; 
	_test_eof135: cs = 135; goto _test_eof; 
	_test_eof136: cs = 136; goto _test_eof; 
	_test_eof137: cs = 137; goto _test_eof; 
	_test_eof138: cs = 138; goto _test_eof; 
	_test_eof139: cs = 139; goto _test_eof; 
	_test_eof140: cs = 140; goto _test_eof; 
	_test_eof141: cs = 141; goto _test_eof; 
	_test_eof142: cs = 142; goto _test_eof; 
	_test_eof143: cs = 143; goto _test_eof; 
	_test_eof144: cs = 144; goto _test_eof; 
	_test_eof145: cs = 145; goto _test_eof; 
	_test_eof146: cs = 146; goto _test_eof; 
	_test_eof147: cs = 147; goto _test_eof; 
	_test_eof148: cs = 148; goto _test_eof; 
	_test_eof149: cs = 149; goto _test_eof; 
	_test_eof150: cs = 150; goto _test_eof; 
	_test_eof151: cs = 151; goto _test_eof; 
	_test_eof152: cs = 152; goto _test_eof; 
	_test_eof153: cs = 153; goto _test_eof; 
	_test_eof154: cs = 154; goto _test_eof; 
	_test_eof155: cs = 155; goto _test_eof; 
	_test_eof156: cs = 156; goto _test_eof; 
	_test_eof157: cs = 157; goto _test_eof; 
	_test_eof158: cs = 158; goto _test_eof; 
	_test_eof159: cs = 159; goto _test_eof; 
	_test_eof160: cs = 160; goto _test_eof; 
	_test_eof161: cs = 161; goto _test_eof; 
	_test_eof162: cs = 162; goto _test_eof; 
	_test_eof163: cs = 163; goto _test_eof; 
	_test_eof164: cs = 164; goto _test_eof; 
	_test_eof165: cs = 165; goto _test_eof; 
	_test_eof166: cs = 166; goto _test_eof; 
	_test_eof167: cs = 167; goto _test_eof; 
	_test_eof168: cs = 168; goto _test_eof; 
	_test_eof169: cs = 169; goto _test_eof; 
	_test_eof170: cs = 170; goto _test_eof; 
	_test_eof171: cs = 171; goto _test_eof; 
	_test_eof172: cs = 172; goto _test_eof; 
	_test_eof173: cs = 173; goto _test_eof; 
	_test_eof174: cs = 174; goto _test_eof; 
	_test_eof175: cs = 175; goto _test_eof; 
	_test_eof176: cs = 176; goto _test_eof; 
	_test_eof177: cs = 177; goto _test_eof; 
	_test_eof178: cs = 178; goto _test_eof; 
	_test_eof179: cs = 179; goto _test_eof; 
	_test_eof180: cs = 180; goto _test_eof; 
	_test_eof181: cs = 181; goto _test_eof; 
	_test_eof182: cs = 182; goto _test_eof; 
	_test_eof183: cs = 183; goto _test_eof; 
	_test_eof184: cs = 184; goto _test_eof; 
	_test_eof185: cs = 185; goto _test_eof; 
	_test_eof186: cs = 186; goto _test_eof; 
	_test_eof187: cs = 187; goto _test_eof; 
	_test_eof188: cs = 188; goto _test_eof; 
	_test_eof189: cs = 189; goto _test_eof; 
	_test_eof190: cs = 190; goto _test_eof; 
	_test_eof191: cs = 191; goto _test_eof; 
	_test_eof192: cs = 192; goto _test_eof; 
	_test_eof193: cs = 193; goto _test_eof; 
	_test_eof194: cs = 194; goto _test_eof; 
	_test_eof195: cs = 195; goto _test_eof; 
	_test_eof196: cs = 196; goto _test_eof; 
	_test_eof197: cs = 197; goto _test_eof; 
	_test_eof198: cs = 198; goto _test_eof; 
	_test_eof199: cs = 199; goto _test_eof; 
	_test_eof200: cs = 200; goto _test_eof; 
	_test_eof201: cs = 201; goto _test_eof; 
	_test_eof202: cs = 202; goto _test_eof; 
	_test_eof203: cs = 203; goto _test_eof; 
	_test_eof204: cs = 204; goto _test_eof; 
	_test_eof205: cs = 205; goto _test_eof; 
	_test_eof206: cs = 206; goto _test_eof; 
	_test_eof207: cs = 207; goto _test_eof; 
	_test_eof208: cs = 208; goto _test_eof; 
	_test_eof209: cs = 209; goto _test_eof; 
	_test_eof210: cs = 210; goto _test_eof; 
	_test_eof211: cs = 211; goto _test_eof; 
	_test_eof212: cs = 212; goto _test_eof; 
	_test_eof213: cs = 213; goto _test_eof; 
	_test_eof214: cs = 214; goto _test_eof; 
	_test_eof215: cs = 215; goto _test_eof; 
	_test_eof216: cs = 216; goto _test_eof; 
	_test_eof217: cs = 217; goto _test_eof; 
	_test_eof218: cs = 218; goto _test_eof; 
	_test_eof219: cs = 219; goto _test_eof; 
	_test_eof220: cs = 220; goto _test_eof; 
	_test_eof221: cs = 221; goto _test_eof; 
	_test_eof222: cs = 222; goto _test_eof; 
	_test_eof223: cs = 223; goto _test_eof; 
	_test_eof224: cs = 224; goto _test_eof; 
	_test_eof225: cs = 225; goto _test_eof; 
	_test_eof226: cs = 226; goto _test_eof; 
	_test_eof227: cs = 227; goto _test_eof; 
	_test_eof228: cs = 228; goto _test_eof; 
	_test_eof229: cs = 229; goto _test_eof; 
	_test_eof230: cs = 230; goto _test_eof; 
	_test_eof231: cs = 231; goto _test_eof; 
	_test_eof232: cs = 232; goto _test_eof; 
	_test_eof233: cs = 233; goto _test_eof; 
	_test_eof234: cs = 234; goto _test_eof; 
	_test_eof235: cs = 235; goto _test_eof; 
	_test_eof236: cs = 236; goto _test_eof; 
	_test_eof237: cs = 237; goto _test_eof; 
	_test_eof238: cs = 238; goto _test_eof; 
	_test_eof239: cs = 239; goto _test_eof; 
	_test_eof240: cs = 240; goto _test_eof; 
	_test_eof241: cs = 241; goto _test_eof; 
	_test_eof242: cs = 242; goto _test_eof; 
	_test_eof243: cs = 243; goto _test_eof; 
	_test_eof244: cs = 244; goto _test_eof; 
	_test_eof245: cs = 245; goto _test_eof; 
	_test_eof246: cs = 246; goto _test_eof; 
	_test_eof247: cs = 247; goto _test_eof; 
	_test_eof248: cs = 248; goto _test_eof; 
	_test_eof249: cs = 249; goto _test_eof; 
	_test_eof250: cs = 250; goto _test_eof; 
	_test_eof251: cs = 251; goto _test_eof; 
	_test_eof252: cs = 252; goto _test_eof; 
	_test_eof253: cs = 253; goto _test_eof; 
	_test_eof254: cs = 254; goto _test_eof; 
	_test_eof255: cs = 255; goto _test_eof; 
	_test_eof256: cs = 256; goto _test_eof; 
	_test_eof257: cs = 257; goto _test_eof; 
	_test_eof258: cs = 258; goto _test_eof; 
	_test_eof259: cs = 259; goto _test_eof; 
	_test_eof260: cs = 260; goto _test_eof; 
	_test_eof261: cs = 261; goto _test_eof; 
	_test_eof262: cs = 262; goto _test_eof; 
	_test_eof263: cs = 263; goto _test_eof; 
	_test_eof264: cs = 264; goto _test_eof; 
	_test_eof265: cs = 265; goto _test_eof; 
	_test_eof266: cs = 266; goto _test_eof; 
	_test_eof267: cs = 267; goto _test_eof; 
	_test_eof268: cs = 268; goto _test_eof; 
	_test_eof269: cs = 269; goto _test_eof; 
	_test_eof270: cs = 270; goto _test_eof; 
	_test_eof271: cs = 271; goto _test_eof; 
	_test_eof272: cs = 272; goto _test_eof; 
	_test_eof273: cs = 273; goto _test_eof; 
	_test_eof274: cs = 274; goto _test_eof; 
	_test_eof275: cs = 275; goto _test_eof; 
	_test_eof276: cs = 276; goto _test_eof; 
	_test_eof277: cs = 277; goto _test_eof; 
	_test_eof278: cs = 278; goto _test_eof; 
	_test_eof279: cs = 279; goto _test_eof; 
	_test_eof280: cs = 280; goto _test_eof; 
	_test_eof281: cs = 281; goto _test_eof; 
	_test_eof282: cs = 282; goto _test_eof; 
	_test_eof283: cs = 283; goto _test_eof; 
	_test_eof284: cs = 284; goto _test_eof; 
	_test_eof285: cs = 285; goto _test_eof; 
	_test_eof286: cs = 286; goto _test_eof; 
	_test_eof287: cs = 287; goto _test_eof; 
	_test_eof288: cs = 288; goto _test_eof; 
	_test_eof289: cs = 289; goto _test_eof; 
	_test_eof290: cs = 290; goto _test_eof; 
	_test_eof291: cs = 291; goto _test_eof; 
	_test_eof292: cs = 292; goto _test_eof; 
	_test_eof293: cs = 293; goto _test_eof; 
	_test_eof294: cs = 294; goto _test_eof; 
	_test_eof295: cs = 295; goto _test_eof; 
	_test_eof296: cs = 296; goto _test_eof; 
	_test_eof297: cs = 297; goto _test_eof; 
	_test_eof298: cs = 298; goto _test_eof; 
	_test_eof299: cs = 299; goto _test_eof; 
	_test_eof300: cs = 300; goto _test_eof; 
	_test_eof301: cs = 301; goto _test_eof; 
	_test_eof302: cs = 302; goto _test_eof; 
	_test_eof303: cs = 303; goto _test_eof; 
	_test_eof304: cs = 304; goto _test_eof; 
	_test_eof305: cs = 305; goto _test_eof; 
	_test_eof306: cs = 306; goto _test_eof; 
	_test_eof307: cs = 307; goto _test_eof; 
	_test_eof308: cs = 308; goto _test_eof; 
	_test_eof309: cs = 309; goto _test_eof; 
	_test_eof310: cs = 310; goto _test_eof; 
	_test_eof311: cs = 311; goto _test_eof; 
	_test_eof312: cs = 312; goto _test_eof; 
	_test_eof313: cs = 313; goto _test_eof; 
	_test_eof314: cs = 314; goto _test_eof; 
	_test_eof315: cs = 315; goto _test_eof; 
	_test_eof316: cs = 316; goto _test_eof; 
	_test_eof317: cs = 317; goto _test_eof; 
	_test_eof318: cs = 318; goto _test_eof; 
	_test_eof319: cs = 319; goto _test_eof; 
	_test_eof320: cs = 320; goto _test_eof; 
	_test_eof321: cs = 321; goto _test_eof; 
	_test_eof322: cs = 322; goto _test_eof; 
	_test_eof323: cs = 323; goto _test_eof; 
	_test_eof324: cs = 324; goto _test_eof; 
	_test_eof325: cs = 325; goto _test_eof; 
	_test_eof326: cs = 326; goto _test_eof; 
	_test_eof327: cs = 327; goto _test_eof; 
	_test_eof328: cs = 328; goto _test_eof; 
	_test_eof329: cs = 329; goto _test_eof; 
	_test_eof330: cs = 330; goto _test_eof; 
	_test_eof331: cs = 331; goto _test_eof; 
	_test_eof332: cs = 332; goto _test_eof; 
	_test_eof333: cs = 333; goto _test_eof; 
	_test_eof334: cs = 334; goto _test_eof; 
	_test_eof335: cs = 335; goto _test_eof; 
	_test_eof336: cs = 336; goto _test_eof; 
	_test_eof337: cs = 337; goto _test_eof; 
	_test_eof338: cs = 338; goto _test_eof; 
	_test_eof339: cs = 339; goto _test_eof; 
	_test_eof340: cs = 340; goto _test_eof; 
	_test_eof341: cs = 341; goto _test_eof; 
	_test_eof342: cs = 342; goto _test_eof; 
	_test_eof343: cs = 343; goto _test_eof; 
	_test_eof344: cs = 344; goto _test_eof; 
	_test_eof345: cs = 345; goto _test_eof; 
	_test_eof346: cs = 346; goto _test_eof; 
	_test_eof347: cs = 347; goto _test_eof; 
	_test_eof348: cs = 348; goto _test_eof; 
	_test_eof349: cs = 349; goto _test_eof; 
	_test_eof350: cs = 350; goto _test_eof; 
	_test_eof351: cs = 351; goto _test_eof; 
	_test_eof352: cs = 352; goto _test_eof; 
	_test_eof353: cs = 353; goto _test_eof; 
	_test_eof354: cs = 354; goto _test_eof; 
	_test_eof355: cs = 355; goto _test_eof; 
	_test_eof356: cs = 356; goto _test_eof; 
	_test_eof357: cs = 357; goto _test_eof; 
	_test_eof358: cs = 358; goto _test_eof; 
	_test_eof359: cs = 359; goto _test_eof; 
	_test_eof360: cs = 360; goto _test_eof; 
	_test_eof361: cs = 361; goto _test_eof; 
	_test_eof362: cs = 362; goto _test_eof; 
	_test_eof363: cs = 363; goto _test_eof; 
	_test_eof364: cs = 364; goto _test_eof; 
	_test_eof365: cs = 365; goto _test_eof; 
	_test_eof366: cs = 366; goto _test_eof; 
	_test_eof367: cs = 367; goto _test_eof; 
	_test_eof368: cs = 368; goto _test_eof; 
	_test_eof369: cs = 369; goto _test_eof; 
	_test_eof370: cs = 370; goto _test_eof; 
	_test_eof371: cs = 371; goto _test_eof; 
	_test_eof372: cs = 372; goto _test_eof; 
	_test_eof373: cs = 373; goto _test_eof; 
	_test_eof374: cs = 374; goto _test_eof; 
	_test_eof375: cs = 375; goto _test_eof; 
	_test_eof376: cs = 376; goto _test_eof; 
	_test_eof377: cs = 377; goto _test_eof; 
	_test_eof378: cs = 378; goto _test_eof; 
	_test_eof379: cs = 379; goto _test_eof; 
	_test_eof380: cs = 380; goto _test_eof; 
	_test_eof381: cs = 381; goto _test_eof; 
	_test_eof382: cs = 382; goto _test_eof; 
	_test_eof383: cs = 383; goto _test_eof; 
	_test_eof384: cs = 384; goto _test_eof; 
	_test_eof385: cs = 385; goto _test_eof; 
	_test_eof386: cs = 386; goto _test_eof; 
	_test_eof387: cs = 387; goto _test_eof; 
	_test_eof388: cs = 388; goto _test_eof; 
	_test_eof389: cs = 389; goto _test_eof; 
	_test_eof390: cs = 390; goto _test_eof; 
	_test_eof391: cs = 391; goto _test_eof; 
	_test_eof392: cs = 392; goto _test_eof; 
	_test_eof393: cs = 393; goto _test_eof; 
	_test_eof394: cs = 394; goto _test_eof; 
	_test_eof395: cs = 395; goto _test_eof; 
	_test_eof396: cs = 396; goto _test_eof; 
	_test_eof397: cs = 397; goto _test_eof; 
	_test_eof398: cs = 398; goto _test_eof; 
	_test_eof399: cs = 399; goto _test_eof; 
	_test_eof400: cs = 400; goto _test_eof; 
	_test_eof401: cs = 401; goto _test_eof; 
	_test_eof402: cs = 402; goto _test_eof; 
	_test_eof403: cs = 403; goto _test_eof; 
	_test_eof404: cs = 404; goto _test_eof; 

	_test_eof: {}
	if ( p == eof )
	{
	switch ( cs ) {
	case 406: 
#line 915 "./src/zscan_rfc1035.rl"
	{ z->lcount++; }
	break;
#line 9738 "src/zscan_rfc1035.c"
	}
	}

	_out: {}
	}

#line 1085 "./src/zscan_rfc1035.rl"
#endif // __clang_analyzer__
// end-sonar-exclude
    GDNSD_DIAG_POP
    GDNSD_DIAG_POP

    if (cs == zone_error)
        parse_error_noargs("General parse error");
    else if (cs < zone_first_final)
        parse_error_noargs("Trailing incomplete or unparseable record at end of file");
}
