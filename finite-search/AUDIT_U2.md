# Adversarial audit report — extension of the finite Erdős #287 range to `U2`

Date of run: see git history.  The **Lean kernel proof is authoritative**; the checks below are a
supplementary, independent re-derivation performed by `scripts/audit_u2.py`, which reads the
committed Lean sources back (never the JSON data or any intermediate script output).

## Summary

| item | result |
|---|---|
| `lake build` (clean tree) | PASS |
| `sorry` / `admit` / `axiom` / `native_decide` / `unsafe` / `@[implemented_by]` | none |
| `#print axioms Erdos287.no_Erdos287Counterexample_of_max_le_1e60` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms Erdos287.no_Erdos287Counterexample_of_max_le_U2` | `[propext, Classical.choice, Quot.sound]` |
| `scripts/audit.py` (original chain audit) | PASS |
| `scripts/audit_u2.py` (extension audit) | PASS |

## What was audited

* **Interval endpoints.**  The eight block lemmas of `RequestProject/Chain.lean` tile
  `[8, CHAIN_CEILING]` with no gap, the first starting at `8` (joined to the exhaustive check for
  `M ≤ 7`), the last ending exactly at
  `CHAIN_CEILING = 1516965997302524373612172717550681525506538629288954643349506`.
  The original theorem `windowPairSupply_of_le` (ceiling `10 ^ 60`) is preserved verbatim; the new
  `windowPairSupply_of_le_chainCeiling` reuses exactly the same block lemmas.
* **The first interval after the previously formalized finite range.**  The new interval is
  `(CHAIN_CEILING, U2]`, and the blocker satisfies `x + 1 < CHAIN_CEILING`, i.e. the blocker lies
  strictly inside the range already covered — so there is no gap, and in the new interval the
  blocker really lies strictly below the maximum.
* **Chain overlaps.**  Re-checked by `scripts/audit.py` for all 192 pairs
  (`P_i = 2 q_i − 1`, `q_i > 11`, `P_i < P_{i+1} ≤ 2 P_i`).
* **The final inequality.**  `U2 = ⌊8 (x+1) / 3⌋`, and the hypothesis actually used in Lean,
  `3 · U2 ≤ 8 · (x + 1)`, holds.  `U2 = 3739298103962937078961175187719640178760086558841160733818922`
  is exactly the ceiling appearing in the final theorem.
* **Numerical definitions and identities.**  `c, P, Q, t, x, U2, CHAIN_CEILING` are parsed out of
  `RequestProject/Extension.lean` and satisfy `P = 15c·2^100 + 1`, `Q = c·2^104 + 1`,
  `t = 1 + 5c·2^102`, `3t + 1 = 4P`, `4t + 1 = 5Q`, `16P − 15Q = 1`, `x = 15Q`, `x + 1 = 16P`.
  The corresponding Lean theorem statements are matched textually as well.
* **Window bounds.**  `U2 < 43 P` and `U2 < 41 Q`, so the multiplier windows throughout the new
  interval are at most `42` and `40`, matching the `ForbiddenPP … 42 (42!)` and
  `ForbiddenPP … 40 (40!)` certificates that Lean proves.
* **Factorial subset-sum bounds.**  `42 · 42! < P`, `40 · 40! < Q`, and every `1 ≤ j ≤ w` divides
  `w!`.  Together these give `0 < ∑_{j∈J} w!/j ≤ w·w! < p` for every nonempty `J ⊆ {1,…,w}`, which
  is exactly what `Erdos287.forbiddenPP_of_factorial_bound` proves in Lean — no powerset is
  enumerated anywhere.
* **Primality certificates.**  For both `P` (witness `11`) and `Q` (witness `3`): the Proth side
  conditions `N = k·2^e + 1`, `0 < k < 2^e`, `k` odd, `N < 2^256`, and the congruence
  `a^((N−1)/2) ≡ −1 (mod N)` are recomputed independently, and `P`, `Q` are additionally
  confirmed prime by a 30-base strong test with trial division.  Inside Lean **no** probable-prime
  test is used: the congruence is evaluated by the kernel via `Erdos287.powMod` (proved correct in
  `RequestProject/PowMod.lean`), and primality is deduced from the proved theorem
  `Erdos287.prime_of_proth_half_pow_neg_one`.
* **The bridge to the problem statement.**  `Erdos287Counterexample` is unchanged (all four
  clauses: elements `> 1`, at least two elements, reciprocal sum exactly `1`, all gaps `≤ 2`).
  The new consumer `not_counterexample_of_harmonic_forbidden_pair` uses only these clauses, and
  the old `WindowPairSupply` bridge is untouched.
* **Hygiene.**  A textual scan of every `.lean` file under `RequestProject/` (with comments
  stripped) finds no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, or `@[implemented_by]`.

## Caveats

* The theorem is **finite**: it says only that no counterexample has maximum denominator at most
  `U2`.  Unrestricted Erdős Problem #287 remains open, and nothing stronger is claimed.
* Proth's criterion as proved here (`prime_of_proth_half_pow_neg_one`) does not need `k` to be
  odd; oddness of both `k`'s is nevertheless checked by the audit.

## Raw output of `scripts/audit_u2.py`

```
c  = 4609040761224086961713861467
P  = 87639799311631337788152543462179066689689528722839704698881
Q  = 93482452599073426974029379692991004469002163971029018345473
t  = 116853065748841783717536724616238755586252704963786272931841
x  = 1402236788986101404610440695394865067035032459565435275182095
U2 = 3739298103962937078961175187719640178760086558841160733818922
CHAIN_CEILING = 1516965997302524373612172717550681525506538629288954643349506

ok  : P = 15 * c * 2^100 + 1
ok  : Q = c * 2^104 + 1
ok  : t = 1 + 5 * c * 2^102
ok  : 3t + 1 = 4P
ok  : 4t + 1 = 5Q
ok  : 16P - 15Q = 1
ok  : x = 15Q
ok  : x + 1 = 16P
ok  : U2 = floor(8 (x+1) / 3)
ok  : 3 * U2 <= 8 * (x+1)  (the hypothesis actually used in Lean)
ok  : x + 1 < CHAIN_CEILING  (the chain overlap)
ok  : Lean source states: bigP\s*=\s*15\s*\*\s*bigC\s*\*\s*2\s*\^\s*100\s*\+\s*1
ok  : Lean source states: bigQ\s*=\s*bigC\s*\*\s*2\s*\^\s*104\s*\+\s*1
ok  : Lean source states: bigT\s*=\s*1\s*\+\s*5\s*\*\s*bigC\s*\*\s*2\s*\^\s*102
ok  : Lean source states: 3\s*\*\s*bigT\s*\+\s*1\s*=\s*4\s*\*\s*bigP
ok  : Lean source states: 4\s*\*\s*bigT\s*\+\s*1\s*=\s*5\s*\*\s*bigQ
ok  : Lean source states: 16\s*\*\s*bigP\s*=\s*15\s*\*\s*bigQ\s*\+\s*1
ok  : Lean source states: bigX\s*=\s*15\s*\*\s*bigQ
ok  : Lean source states: bigX\s*\+\s*1\s*=\s*16\s*\*\s*bigP
ok  : Lean source states: U2\s*=\s*8\s*\*\s*\(bigX\s*\+\s*1\)\s*/\s*3
ok  : Lean source states: bigX\s*\+\s*1\s*<\s*CHAIN_CEILING
ok  : Chain.lean's windowPairSupply_of_le_chainCeiling ends exactly at CHAIN_CEILING
ok  : the original windowPairSupply_of_le (ceiling 10^60) is preserved
ok  : found all 8 block lemmas in Chain.lean
ok  : the block lemmas tile [8, CHAIN_CEILING] with no gap
ok  : the last block wps_block07 ends exactly at CHAIN_CEILING
ok  : windowPairSupply_of_le_chainCeiling's last branch is wps_block07 up to CHAIN_CEILING
ok  : Lean certifies ForbiddenPP M bigP 1 42 (42!)
ok  : Lean certifies ForbiddenPP M bigQ 1 40 (40!)
ok  : U2 < 43 P  (multiplier window of P is at most 42 throughout the range)
ok  : U2 < 41 Q  (multiplier window of Q is at most 40 throughout the range)
ok  : P divides x+1, and x+1 lies in the range
ok  : Q divides x, and x lies in the range
ok  : 42 * 42! < P
ok  : 40 * 40! < Q
ok  : every 1<=j<=42 divides 42!
ok  : every 1<=j<=40 divides 40!
ok  : P does not divide 42!, Q does not divide 40!
ok  : found the Proth certificate for P in the Lean source
ok  : found the Proth certificate for Q in the Lean source
ok  : P = k * 2^e + 1 with the k, e used in the Lean certificate
ok  : P: 0 < k < 2^e
ok  : P: k is odd
ok  : P < 2^256 (fuel bound of powMod)
ok  : P: a^((N-1)/2) = -1 mod N for the witness a = 11
ok  : P is prime (independent strong test)
ok  : Q = k * 2^e + 1 with the k, e used in the Lean certificate
ok  : Q: 0 < k < 2^e
ok  : Q: k is odd
ok  : Q < 2^256 (fuel bound of powMod)
ok  : Q: a^((N-1)/2) = -1 mod N for the witness a = 3
ok  : Q is prime (independent strong test)
ok  : no forbidden proof constructs in RequestProject/ (none)
ok  : the final theorem has the requested shape
ok  : the final theorem's ceiling is exactly U2 = 3739298103962937078961175187719640178760086558841160733818922
ok  : the original 10^60 theorem is preserved
ok  : Erdos287Counterexample is unchanged (positivity, size, reciprocal sum, gap clause)

AUDIT PASSED
```

## Raw output of `scripts/audit.py`

```
parsed 351 Lucas certificates and 33 norm_num primality facts
prime-pair and chain-overlap structure OK for 192 pairs
small window pairs: [('windowPairSupply_seven', 8, 14), ('windowPairSupply_thirteen', 14, 26), ('windowPairSupply_twentyfive', 26, 50), ('windowPairSupply_46', 47, 92), ('windowPairSupply_82', 83, 164), ('windowPairSupply_158', 159, 316)]
intervals cover [2, 1516965997302524373612172717550681525506538629288954643349506]  (>= 10^60 : True)
final interval upper endpoint / 10^60 = 1.516966
hygiene scan OK

AUDIT PASSED
```
