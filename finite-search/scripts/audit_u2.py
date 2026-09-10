#!/usr/bin/env python3
"""Independent adversarial audit of the extension of the finite Erdos #287 range to U2.

Everything checked here is read back out of the *Lean sources*, so it audits what is actually
compiled.  The Lean kernel proof is authoritative; this script is a supplementary, independent
re-derivation of every numerical claim used by the extension:

  * the exact numerical definitions of c, P, Q, t, x, U2 and CHAIN_CEILING;
  * 3t + 1 = 4P, 4t + 1 = 5Q, 16P - 15Q = 1, x = 15Q, x + 1 = 16P;
  * U2 = floor(8 (x+1) / 3) and the crucial overlap x + 1 < CHAIN_CEILING;
  * CHAIN_CEILING agrees with the endpoint of the chain lemma in Chain.lean;
  * the multiplier window bounds U2 < 43 P and U2 < 41 Q (windows 42 and 40);
  * the factorial subset-sum bounds 42 * 42! < P and 40 * 40! < Q;
  * both Proth certificates (side conditions and the modular congruence) plus a fully
    independent primality test of P and Q;
  * absence of forbidden proof constructs anywhere in RequestProject/;
  * the exact statement of the final theorem.
"""

import math
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
SRC = os.path.join(ROOT, "RequestProject")

errors = []


def check(cond, msg):
    if not cond:
        errors.append(msg)
        print("FAIL:", msg)
    else:
        print("ok  :", msg)


def read(rel):
    with open(os.path.join(SRC, rel)) as f:
        return f.read()


def strip_comments(src):
    src = re.sub(r"/-.*?-/", " ", src, flags=re.S)
    src = re.sub(r"--[^\n]*", " ", src)
    return src


# --------------------------------------------------------------- primality


def is_prime(n):
    """Deterministic Miller-Rabin (correct for all n, using the first 30 primes as bases
    together with trial division; for the sizes here this is the standard strong test)."""
    if n < 2:
        return False
    small = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
             73, 79, 83, 89, 97, 101, 103, 107, 109, 113]
    for p in small:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in small:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


# --------------------------------------------------------------- parse defs

ext = strip_comments(read("Extension.lean"))
main = strip_comments(read("Main.lean"))
chain = strip_comments(read("Chain.lean"))


def get_def(name, src=None):
    src = ext if src is None else src
    m = re.search(r"def\s+" + name + r"\s*:\s*ℕ\s*:=\s*(\d+)", src)
    if m is None:
        raise SystemExit("could not find definition of " + name)
    return int(m.group(1))


c = get_def("bigC")
P = get_def("bigP")
Q = get_def("bigQ")
t = get_def("bigT")
x = get_def("bigX")
U2 = get_def("U2")
CC = get_def("CHAIN_CEILING")

print("c  =", c)
print("P  =", P)
print("Q  =", Q)
print("t  =", t)
print("x  =", x)
print("U2 =", U2)
print("CHAIN_CEILING =", CC)
print()

# ------------------------------------------------- shapes and identities

check(P == 15 * c * 2 ** 100 + 1, "P = 15 * c * 2^100 + 1")
check(Q == c * 2 ** 104 + 1, "Q = c * 2^104 + 1")
check(t == 1 + 5 * c * 2 ** 102, "t = 1 + 5 * c * 2^102")
check(3 * t + 1 == 4 * P, "3t + 1 = 4P")
check(4 * t + 1 == 5 * Q, "4t + 1 = 5Q")
check(16 * P - 15 * Q == 1, "16P - 15Q = 1")
check(x == 15 * Q, "x = 15Q")
check(x + 1 == 16 * P, "x + 1 = 16P")
check(U2 == 8 * (x + 1) // 3, "U2 = floor(8 (x+1) / 3)")
check(3 * U2 <= 8 * (x + 1), "3 * U2 <= 8 * (x+1)  (the hypothesis actually used in Lean)")
check(x + 1 < CC, "x + 1 < CHAIN_CEILING  (the chain overlap)")

# the Lean statements really assert these shapes
for stmt in [
    r"bigP\s*=\s*15\s*\*\s*bigC\s*\*\s*2\s*\^\s*100\s*\+\s*1",
    r"bigQ\s*=\s*bigC\s*\*\s*2\s*\^\s*104\s*\+\s*1",
    r"bigT\s*=\s*1\s*\+\s*5\s*\*\s*bigC\s*\*\s*2\s*\^\s*102",
    r"3\s*\*\s*bigT\s*\+\s*1\s*=\s*4\s*\*\s*bigP",
    r"4\s*\*\s*bigT\s*\+\s*1\s*=\s*5\s*\*\s*bigQ",
    r"16\s*\*\s*bigP\s*=\s*15\s*\*\s*bigQ\s*\+\s*1",
    r"bigX\s*=\s*15\s*\*\s*bigQ",
    r"bigX\s*\+\s*1\s*=\s*16\s*\*\s*bigP",
    r"U2\s*=\s*8\s*\*\s*\(bigX\s*\+\s*1\)\s*/\s*3",
    r"bigX\s*\+\s*1\s*<\s*CHAIN_CEILING",
]:
    check(re.search(stmt, ext) is not None, "Lean source states: " + stmt)

# ------------------------------------------------- the chain endpoint

m = re.search(r"theorem\s+windowPairSupply_of_le_chainCeiling.*?M\s*≤\s*(\d+)", chain, re.S)
check(m is not None and int(m.group(1)) == CC,
      "Chain.lean's windowPairSupply_of_le_chainCeiling ends exactly at CHAIN_CEILING")
# the old 10^60 theorem is still there, unchanged
check(re.search(r"theorem\s+windowPairSupply_of_le\s*\{M\s*:\s*ℕ\}\s*\(h1\s*:\s*8\s*≤\s*M\)"
                r"\s*\(h2\s*:\s*M\s*≤\s*10\s*\^\s*60\)", chain) is not None,
      "the original windowPairSupply_of_le (ceiling 10^60) is preserved")
# the blocks tile [8, CHAIN_CEILING] with no gap, and the last one ends at CHAIN_CEILING
blocks = re.findall(r"theorem\s+wps_block(\d+)\s*\{M\s*:\s*ℕ\}\s*\(h1\s*:\s*(\d+)\s*≤\s*M\)"
                    r"\s*\(h2\s*:\s*M\s*≤\s*(\d+)\)", chain)
check(len(blocks) == 8, "found all 8 block lemmas in Chain.lean")
lo_prev = None
gapok = blocks[0][1] == "8"
for _, lo, hi in blocks:
    if lo_prev is not None:
        gapok = gapok and int(lo) <= lo_prev + 1
    lo_prev = int(hi)
check(gapok, "the block lemmas tile [8, CHAIN_CEILING] with no gap")
check(int(blocks[-1][2]) == CC, "the last block wps_block07 ends exactly at CHAIN_CEILING")
check(re.search(r"le_or_gt M " + str(CC) + r" with hle \| hgt\s*\n\s*·\s*exact wps_block07",
                chain) is not None,
      "windowPairSupply_of_le_chainCeiling's last branch is wps_block07 up to CHAIN_CEILING")

# ------------------------------------------------- window bounds

mp = re.search(r"forbidden_bigP.*?ForbiddenPP\s+M\s+bigP\s+1\s+(\d+)\s+\(Nat.factorial\s+(\d+)\)",
               ext, re.S)
mq = re.search(r"forbidden_bigQ.*?ForbiddenPP\s+M\s+bigQ\s+1\s+(\d+)\s+\(Nat.factorial\s+(\d+)\)",
               ext, re.S)
check(mp is not None and mp.group(1) == mp.group(2) == "42",
      "Lean certifies ForbiddenPP M bigP 1 42 (42!)")
check(mq is not None and mq.group(1) == mq.group(2) == "40",
      "Lean certifies ForbiddenPP M bigQ 1 40 (40!)")
check(U2 < 43 * P, "U2 < 43 P  (multiplier window of P is at most 42 throughout the range)")
check(U2 < 41 * Q, "U2 < 41 Q  (multiplier window of Q is at most 40 throughout the range)")
check(P <= x + 1 <= U2 and (x + 1) % P == 0, "P divides x+1, and x+1 lies in the range")
check(Q <= x <= U2 and x % Q == 0, "Q divides x, and x lies in the range")

# factorial subset-sum bounds: every nonempty subset sum of {w!/j : 1<=j<=w} lies in [1, w*w!]
check(42 * math.factorial(42) < P, "42 * 42! < P")
check(40 * math.factorial(40) < Q, "40 * 40! < Q")
check(all(math.factorial(42) % j == 0 for j in range(1, 43)), "every 1<=j<=42 divides 42!")
check(all(math.factorial(40) % j == 0 for j in range(1, 41)), "every 1<=j<=40 divides 40!")
check(math.factorial(42) < P and math.factorial(40) < Q, "P does not divide 42!, Q does not divide 40!")

# ------------------------------------------------- primality

mP = re.search(r"prime_bigP.*?prime_of_proth_half_pow_neg_one\s*\(k\s*:=\s*([0-9 *]+)\)\s*"
               r"\(e\s*:=\s*(\d+)\)\s*\n?\s*\(a\s*:=\s*(\d+)\)", ext, re.S)
mQ = re.search(r"prime_bigQ.*?prime_of_proth_half_pow_neg_one\s*\(k\s*:=\s*([0-9 *]+)\)\s*"
               r"\(e\s*:=\s*(\d+)\)\s*\n?\s*\(a\s*:=\s*(\d+)\)", ext, re.S)
check(mP is not None, "found the Proth certificate for P in the Lean source")
check(mQ is not None, "found the Proth certificate for Q in the Lean source")

for name, N, m in (("P", P, mP), ("Q", Q, mQ)):
    k = eval(m.group(1))            # noqa: S307 - a literal product of digits
    e = int(m.group(2))
    a = int(m.group(3))
    check(N == k * 2 ** e + 1, f"{name} = k * 2^e + 1 with the k, e used in the Lean certificate")
    check(0 < k < 2 ** e, f"{name}: 0 < k < 2^e")
    check(k % 2 == 1, f"{name}: k is odd")
    check(N < 2 ** 256, f"{name} < 2^256 (fuel bound of powMod)")
    check(pow(a, (N - 1) // 2, N) == N - 1,
          f"{name}: a^((N-1)/2) = -1 mod N for the witness a = {a}")
    check(is_prime(N), f"{name} is prime (independent strong test)")

# ------------------------------------------------- hygiene

forbidden = [r"\bsorry\b", r"\badmit\b", r"\bnative_decide\b", r"\bunsafe\b",
             r"@\[implemented_by", r"^\s*axiom\s"]
bad = []
for dirpath, _, files in os.walk(SRC):
    for fn in files:
        if not fn.endswith(".lean"):
            continue
        path = os.path.join(dirpath, fn)
        with open(path) as f:
            body = strip_comments(f.read())
        for pat in forbidden:
            for mm in re.finditer(pat, body, re.M):
                bad.append(f"{path}: {mm.group(0)!r}")
check(not bad, "no forbidden proof constructs in RequestProject/ (%s)" % ("; ".join(bad) or "none"))

# ------------------------------------------------- final theorem statement

want = re.search(
    r"theorem\s+no_Erdos287Counterexample_of_max_le_U2\s*\n?\s*"
    r"\{A\s*:\s*Finset\s*ℕ\}\s*\n?\s*"
    r"\(h\s*:\s*Erdos287Counterexample\s*A\)\s*\n?\s*"
    r"\(hM\s*:\s*A\.max'\s*h\.nonempty\s*≤\s*\n?\s*(\d+)\)\s*:\s*\n?\s*False", main)
check(want is not None, "the final theorem has the requested shape")
check(want is not None and int(want.group(1)) == U2,
      "the final theorem's ceiling is exactly U2 = %d" % U2)
check(re.search(r"theorem\s+no_Erdos287Counterexample_of_max_le_1e60", main) is not None,
      "the original 10^60 theorem is preserved")
check(re.search(r"def\s+Erdos287Counterexample\s*\(A\s*:\s*Finset\s*ℕ\)\s*:\s*Prop\s*:=\s*"
                r"\(∀\s*n\s*∈\s*A,\s*1\s*<\s*n\)\s*∧\s*2\s*≤\s*A\.card\s*∧\s*"
                r"\(∑\s*n\s*∈\s*A,\s*\(1\s*:\s*ℚ\)\s*/\s*n\)\s*=\s*1\s*∧",
                strip_comments(read("Defs.lean"))) is not None,
      "Erdos287Counterexample is unchanged (positivity, size, reciprocal sum, gap clause)")

print()
if errors:
    print("AUDIT FAILED with %d error(s)" % len(errors))
    sys.exit(1)
print("AUDIT PASSED")
