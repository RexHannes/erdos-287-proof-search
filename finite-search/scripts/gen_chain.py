#!/usr/bin/env python3
"""Search for the certified chain of prime pairs used in the Erdos #287 finite verification.

For each step we need a pair (q, P) with

    P = 2*q - 1,   q prime,   P prime,
    P_prev < P <= 2*P_prev,

and additionally we insist that  q - 1 = c * 2^t  with  c  small (so that  q - 1  and
P - 1 = c * 2^(t+1)  are both completely factored, which is what Lucas' primality criterion
needs).  For each of q and P we also find a primitive root witness.

Output: chain.json
"""

import json
import math
import sys

# ---------------------------------------------------------------- primality (search only)


def _sieve(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    i = 2
    while i * i <= n:
        if s[i]:
            s[i * i:: i] = bytearray(len(s[i * i:: i]))
        i += 1
    return [i for i in range(n + 1) if s[i]]


_SMALL_PRIMES = _sieve(100000)


def is_probable_prime(n):
    if n < 2:
        return False
    for p in _SMALL_PRIMES[:300]:
        if n % p == 0:
            return n == p
    d = n - 1
    r = 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if a % n == 0:
            continue
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


def factor_small(c):
    """Complete factorisation (with multiplicity) of a small number."""
    fs = []
    m = c
    for p in _SMALL_PRIMES:
        if p * p > m:
            break
        while m % p == 0:
            fs.append(p)
            m //= p
    if m > 1:
        assert is_probable_prime(m), ("unfactored cofactor", m)
        fs.append(m)
    return sorted(fs)


def find_witness(N, prime_factors):
    """Find a primitive root mod N (N prime), i.e. a Lucas witness."""
    for a in range(2, 20000):
        if pow(a, N - 1, N) != 1:
            continue
        if all(pow(a, (N - 1) // p, N) != 1 for p in prime_factors):
            return a
    raise RuntimeError("no witness found for %d" % N)


# ---------------------------------------------------------------- chain search

CMAX = 1 << 22


def next_pair(P_prev):
    """Find the largest usable pair (c, t, q, P) with P_prev < P <= 2*P_prev."""
    q_lo = (P_prev + 1) // 2 + 1
    q_hi = P_prev
    if P_prev < (1 << 26):
        for q in range(q_hi if q_hi % 2 else q_hi - 1, q_lo - 1, -2):
            if not is_probable_prime(q):
                continue
            P = 2 * q - 1
            if not is_probable_prime(P):
                continue
            m = q - 1
            t = 0
            while m % 2 == 0:
                m //= 2
                t += 1
            if m > CMAX:
                continue
            assert P_prev < P <= 2 * P_prev
            return (m, t, q, P)
        raise RuntimeError("no small pair found above %d" % P_prev)
    t0 = max(1, (q_hi - 1).bit_length() - CMAX.bit_length() + 1)
    for t in range(t0, t0 + 4):
        step = 1 << t
        c_hi = (q_hi - 1) >> t
        c_lo = max(1, ((q_lo - 1) + step - 1) >> t)
        for c in range(c_hi, c_lo - 1, -1):
            q = c * step + 1
            if q < q_lo or q > q_hi:
                continue
            if not is_probable_prime(q):
                continue
            P = 2 * q - 1
            if not is_probable_prime(P):
                continue
            assert P_prev < P <= 2 * P_prev
            return (c, t, q, P)
    raise RuntimeError("no pair found above %d" % P_prev)


def main():
    target = 10 ** 60
    chain = [dict(c=39, t=2, q=157, P=313)]
    P = 313
    while 2 * P < target:
        c, t, q, Pn = next_pair(P)
        chain.append(dict(c=c, t=t, q=q, P=Pn))
        P = Pn
        print("step %3d  P ~ 10^%.2f" % (len(chain), math.log10(P)), file=sys.stderr)
    out = []
    for e in chain:
        c, t, q, P = e["c"], e["t"], e["q"], e["P"]
        assert q == c * 2 ** t + 1
        assert P == c * 2 ** (t + 1) + 1
        ps = factor_small(c)
        prod = 1
        for p in ps:
            prod *= p
        assert prod == c, (c, ps)
        pf = sorted(set(ps + [2]))
        aq = find_witness(q, pf)
        aP = find_witness(P, pf)
        out.append(dict(c=c, t=t, q=q, P=P, ps=ps, aq=aq, aP=aP))
    json.dump(out, open("chain.json", "w"), indent=1)
    print("chain length", len(out))
    print("final P", out[-1]["P"])
    print("2*P >= 10^60:", 2 * out[-1]["P"] >= target)


if __name__ == "__main__":
    main()
