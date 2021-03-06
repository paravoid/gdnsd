# CNAME torture testing

use _GDT ();
use Test::More tests => 12;

my $neg_soa = 'example.com 900 SOA ns1.example.com hmaster.example.net 1 7200 1800 259200 900';

my $pid = _GDT->test_spawn_daemon();

# this belongs in another testset I guess, but it was convenient to stuff here for now
_GDT->test_dns(
    qname => 'mxinorg.example.com', qtype => 'MX',
    answer => 'mxinorg.example.com 21600 MX 0 foo.example.org',
);

_GDT->test_dns(
    qname => 'ct1.example.com', qtype => 'CNAME',
    answer => 'ct1.example.com 21600 CNAME ct2.example.com',
);

_GDT->test_dns(
    qname => 'ct1.example.com', qtype => 'A',
    answer => 'ct1.example.com 21600 CNAME ct2.example.com',
);

_GDT->test_dns(
    qname => 'ct1.example.com', qtype => 'MX',
    answer => 'ct1.example.com 21600 CNAME ct2.example.com',
);

_GDT->test_dns(
    qname => 'ctx1.example.com', qtype => 'CNAME',
    answer => 'ctx1.example.com 21600 CNAME ctx2.example.com',
);

# NXDOMAIN above a CNAME, because it's a bit of a strange case for the code
_GDT->test_dns(
    qname => 'www.ctx1.example.com', qtype => 'A',
    header => { rcode => 'NXDOMAIN' },
    auth => $neg_soa,
    stats => [qw/udp_reqs nxdomain/],
);

_GDT->test_dns(
    qname => 'ctx1.example.com', qtype => 'A',
    answer => 'ctx1.example.com 21600 CNAME ctx2.example.com',
);

_GDT->test_dns(
    qname => 'ct21.example.com', qtype => 'A',
    answer => 'ct21.example.com 21600 CNAME ct22.example.org',
);

_GDT->test_dns(
    qname => 'ctinside.example.com', qtype => 'A',
    answer => 'ctinside.example.com 21600 CNAME www.subfubar.x.y.z.example.com',
);

# -> local NXDOMAIN several layers deep, with unprintable label char on LHS
#   (this exercises a few previously-uncovered blocks of code in ltree.c)
_GDT->test_dns(
    qname => 'asdf\003.example.org', qtype => 'A',
    answer => 'asdf\003.example.org 43201 CNAME deep.layers.of.nxd.subdomain.*.example.org',
);

_GDT->test_kill_daemon($pid);
