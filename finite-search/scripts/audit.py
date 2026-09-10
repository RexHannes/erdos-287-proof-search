#!/usr/bin/env python3
"""Adversarial audit of the Erdos #287 finite verification.

Everything checked here is read back out of the *Lean sources* (not out of chain.json), so it
audits what is actually compiled:

  * every `Nat.Prime N` claimed in RequestProject/Certificates/*.lean is verified independently
    (strong deterministic Miller-Rabin plus trial division for small N), and, where a Lucas
    certificate is used, the certificate data itself is re-checked;
  * the prime pairs satisfy P_i = 2 q_i - 1, q_i > 11;
  * the chain overlaps P_i < P_{i+1} <= 2 P_i hold;
  * the covering intervals used in RequestProject/Chain.lean tile [8, 10^60] with no gap, and
    join up with the finite base M <= 7;
  * the final interval reaches beyond 10^60.
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
CERTDIR = os.path.join(ROOT, "RequestProject", "Certificates")

errors = []


def check(cond, msg):
    if not cond:
        errors.append(msg)
        print("FAIL:", msg)


# ------------------------------------------------------------------ primality


def _sieve(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    i = 2
    while i * i <= n:
        if s[i]:
            s[i * i:: i] = bytearray(len(s[i * i:: i]))
        i += 1
    return [i for i in range(n + 1) if s[i]]


SMALL = _sieve(200000)


def is_prime(n):
    """Deterministic for n < 3.3e24; strong probable prime to 30 bases otherwise."""
    if n < 2:
        return False
    for p in SMALL:
        if p * p > n:
            return True
        if n % p == 0:
            return n == p
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in SMALL[:30]:
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


# ------------------------------------------------------------------ parse certificates

norm_re = re.compile(r"theorem\s+prime_([qP])(\d{3})\s*:\s*Nat\.Prime\s+(\d+)\s*:=\s*by norm_num")
cert_re = re.compile(
    r"theorem\s+prime_([qP])(\d{3})\s*:\s*Nat\.Prime\s+(\d+)\s*:=\s*\n"
    r"\s*prime_of_cert'\s*\(c := (\d+)\)\s*\(t := (\d+)\)\s*\(a := (\d+)\)\s*\(ps := \[([0-9, ]*)\]\)"
)

primes = {}  # (kind, idx) -> N
ncert = 0
nnorm = 0
for fn in sorted(os.listdir(CERTDIR)):
    src = open(os.path.join(CERTDIR, fn)).read()
    for m in norm_re.finditer(src):
        kind, idx, N = m.group(1), int(m.group(2)), int(m.group(3))
        check(is_prime(N), "norm_num prime claim is false: %d" % N)
        check(N < 10 ** 7, "norm_num used for a large number: %d" % N)
        primes[(kind, idx)] = N
        nnorm += 1
    for m in cert_re.finditer(src):
        kind, idx = m.group(1), int(m.group(2))
        N, c, t, a = int(m.group(3)), int(m.group(4)), int(m.group(5)), int(m.group(6))
        ps = [int(x) for x in m.group(7).split(",") if x.strip()]
        check(N == c * 2 ** t + 1, "certificate shape mismatch for %d" % N)
        check(c * 2 ** t < 2 ** 256, "size hypothesis violated for %d" % N)
        prod = 1
        for p in ps:
            prod *= p
        check(prod == c, "ps does not multiply to c for %d" % N)
        for p in ps:
            check(is_prime(p), "claimed prime factor %d is not prime" % p)
        # re-check the Lucas data itself
        check(pow(a, N - 1, N) == 1, "witness fails Fermat test for %d" % N)
        check(pow(a, (N - 1) // 2, N) != 1, "witness fails at q=2 for %d" % N)
        for p in set(ps):
            check(pow(a, (N - 1) // p, N) != 1, "witness fails at q=%d for %d" % (p, N))
        # and an independent primality test
        check(is_prime(N), "certified number is composite: %d" % N)
        primes[(kind, idx)] = N
        ncert += 1

print("parsed %d Lucas certificates and %d norm_num primality facts" % (ncert, nnorm))
check(ncert + nnorm == 2 * 192, "unexpected number of primality facts: %d" % (ncert + nnorm))

# ------------------------------------------------------------------ pair / chain structure

n = len(primes) // 2
for i in range(n):
    q, P = primes[("q", i)], primes[("P", i)]
    check(P == 2 * q - 1, "pair %d: P != 2q-1" % i)
    check(q > 11, "pair %d: q <= 11" % i)
for i in range(n - 1):
    check(primes[("P", i)] < primes[("P", i + 1)], "chain not increasing at %d" % i)
    check(primes[("P", i + 1)] <= 2 * primes[("P", i)], "chain overlap fails at %d" % i)
print("prime-pair and chain-overlap structure OK for %d pairs" % n)

# ------------------------------------------------------------------ intervals used in Chain.lean

chain_src = open(os.path.join(ROOT, "RequestProject", "Chain.lean")).read()
iv_re = re.compile(
    r"theorem wps_chain(\d{3}) \{M : ℕ\} \(h1 : (\d+) ≤ M\) \(h2 : M ≤ (\d+)\)")
chain_iv = {}
for m in iv_re.finditer(chain_src):
    i, lo, hi = int(m.group(1)), int(m.group(2)), int(m.group(3))
    chain_iv[i] = (lo, hi)
    check(lo == primes[("P", i)] + 1, "wps_chain%03d lower endpoint wrong" % i)
    check(hi == 2 * primes[("P", i)], "wps_chain%03d upper endpoint wrong" % i)
check(len(chain_iv) == n, "missing chain interval lemmas")

small_src = open(os.path.join(ROOT, "RequestProject", "Small.lean")).read()
sm_re = re.compile(r"theorem (windowPairSupply_\w+) \{M : ℕ\} \(h1 : (\d+) ≤ M\) \(h2 : M ≤ (\d+)\)")
small_iv = [(m.group(1), int(m.group(2)), int(m.group(3))) for m in sm_re.finditer(small_src)]
print("small window pairs:", [(a, b, c) for a, b, c in small_iv])

# the total collection of intervals actually invoked, in the order Chain.lean uses them
intervals = [(lo, hi) for (_, lo, hi) in small_iv]
intervals += [chain_iv[i] for i in range(n)]
intervals.sort()

cur = 7  # everything up to 7 is handled by the finite base `no_counterexample_le_seven`
for (lo, hi) in intervals:
    if lo <= cur + 1:
        cur = max(cur, hi)
check(cur >= 10 ** 60, "intervals do not reach 10^60 (reach %d)" % cur)
print("intervals cover [2, %d]  (>= 10^60 : %s)" % (cur, cur >= 10 ** 60))
print("final interval upper endpoint / 10^60 = %.6f" % (intervals[-1][1] / 10.0 ** 60))

# ------------------------------------------------------------------ hygiene

def strip_comments(src):
    src = re.sub(r"/-.*?-/", " ", src, flags=re.S)
    src = re.sub(r"--[^\n]*", " ", src)
    return src


bad = []
pats = [r"\bsorry\b", r"\badmit\b", r"\bnative_decide\b", r"^\s*axiom\s",
        r"implemented_by", r"\bunsafe\b"]
for dirpath, _, files in os.walk(os.path.join(ROOT, "RequestProject")):
    for f in files:
        if not f.endswith(".lean"):
            continue
        src = strip_comments(open(os.path.join(dirpath, f)).read())
        for pat in pats:
            if re.search(pat, src, flags=re.M):
                bad.append((os.path.join(dirpath, f), pat))
check(not bad, "forbidden constructs found: %s" % bad)
print("hygiene scan OK")

print()
if errors:
    print("AUDIT FAILED with %d problem(s)" % len(errors))
    sys.exit(1)
print("AUDIT PASSED")
