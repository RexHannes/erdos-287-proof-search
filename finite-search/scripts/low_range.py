#!/usr/bin/env python3
"""Search for window pairs (x, x+1) covering small maxima M.

A number n is *forbidden* at maximum M0 if there is a prime power p^a dividing n with
w = M0 // p^a  satisfying  w < p  and  p does not divide any nonempty subset sum of
{ L/1, ..., L/w }  where  L = lcm(1..w).

A window pair at x covers all M with x+1 <= M <= 2x, provided x and x+1 are both forbidden
at M0 = 2x.
"""

from functools import lru_cache
from math import gcd
from itertools import combinations


def lcm_upto(w):
    L = 1
    for j in range(1, w + 1):
        L = L * j // gcd(L, j)
    return L


@lru_cache(maxsize=None)
def subset_sums(w):
    L = lcm_upto(w)
    vals = [L // j for j in range(1, w + 1)]
    sums = set()
    for r in range(1, w + 1):
        for comb in combinations(vals, r):
            sums.add(sum(comb))
    return L, frozenset(sums)


def window_ok(p, w):
    if w == 0:
        return True
    if w >= p:
        return False
    L, sums = subset_sums(w)
    if L % p == 0:
        return False
    return all(s % p != 0 for s in sums)


def prime_powers_dividing(n):
    res = []
    m = n
    d = 2
    while d * d <= m:
        if m % d == 0:
            e = 0
            while m % d == 0:
                m //= d
                e += 1
            for a in range(1, e + 1):
                res.append((d, a))
        d += 1
    if m > 1:
        res.append((m, 1))
    return res


def forbidden_cert(n, M0):
    """Return (p, a, w, L) certifying that n is forbidden at maximum M0, or None."""
    best = None
    for (p, a) in prime_powers_dividing(n):
        w = M0 // (p ** a)
        if window_ok(p, w):
            L = lcm_upto(w) if w > 0 else 1
            cand = (p, a, w, L)
            if best is None or p ** a > best[0] ** best[1]:
                best = cand
    return best


def pair_cert(x):
    M0 = 2 * x
    cu = forbidden_cert(x, M0)
    cv = forbidden_cert(x + 1, M0)
    if cu and cv:
        return cu, cv
    return None


def cover(lo, hi):
    """Greedily cover [lo, hi] by window pairs; return list of (x, certs)."""
    out = []
    cur = lo
    while cur <= hi:
        # need x with x+1 <= cur and 2x >= cur ; take x as large as possible
        found = None
        for x in range(cur - 1, (cur + 1) // 2 - 1, -1):
            c = pair_cert(x)
            if c:
                found = (x, c)
                break
        if not found:
            raise RuntimeError("no window pair covering M = %d" % cur)
        out.append(found)
        cur = 2 * found[0] + 1
    return out


if __name__ == "__main__":
    res = cover(8, 400)
    for x, (cu, cv) in res:
        print("x=%-6d covers [%d,%d]  x: p^a=%d^%d w=%d L=%d   x+1: p^a=%d^%d w=%d L=%d"
              % (x, x + 1, 2 * x, cu[0], cu[1], cu[2], cu[3], cv[0], cv[1], cv[2], cv[3]))
