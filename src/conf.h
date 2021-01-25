/* Copyright © 2012 Brandon L Black <blblack@gmail.com>
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

#ifndef GDNSD_CONF_H
#define GDNSD_CONF_H

#include "socks.h"

#include <gdnsd/compiler.h>
#include <gdnsd/vscf.h>

#include <stdbool.h>
#include <inttypes.h>

struct binstr {
    const uint8_t* data;
    unsigned len;
};

struct cfg {
    struct binstr chaos;
    struct binstr nsid;
    const char* cookie_key_file;
    bool     lock_mem;
    bool     disable_text_autosplit;
    bool     edns_client_subnet;
    bool     zones_strict_data;
    bool     disable_cookies;
    bool     disable_tcp_dso;
    bool     dnssec_enabled;
    bool     dnssec_deterministic_ecdsa;
    unsigned dnssec_max_active_zsks;
    unsigned dnssec_nxd_cache_scale;
    unsigned dnssec_nxd_sign_rate;
    unsigned max_nocookie_response;
    unsigned zones_default_ttl;
    unsigned max_ncache_ttl;
    unsigned max_ttl;
    unsigned min_ttl;
    unsigned max_edns_response;
    unsigned max_edns_response_v6;
    unsigned acme_challenge_ttl;
    unsigned acme_challenge_dns_ttl;
    unsigned zones_rfc1035_threads;
};

extern const struct cfg* gcfg;

F_RETNN
struct cfg* conf_load(const vscf_data_t* cfg_root, const bool force_zsd);

#endif // GDNSD_CONF_H
