# Summary of changes for run 5a9f2336-f3ae-4d8b-85f9-8b80ee344888
## Result

The finite theorem is now proved through the exact requested ceiling.

```lean
theorem Erdos287.no_Erdos287Counterexample_of_max_le_U2
    {A : Finset ℕ}
    (h : Erdos287Counterexample A)
    (hM : A.max' h.nonempty ≤
      3739298103962937078961175187719640178760086558841160733818922) :
    False
```

`lake build` passes from a clean build tree (`.lake/build` was deleted and everything rebuilt), and

```
'Erdos287.no_Erdos287Counterexample_of_max_le_1e60' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.no_Erdos287Counterexample_of_max_le_U2'   depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, or `@[implemented_by]` anywhere in `RequestProject/`. The problem statement `Erdos287Counterexample`, the old chain, the certificate blocks and `no_Erdos287Counterexample_of_max_le_1e60` are untouched (verified by diff against the starting commit); nothing was rebuilt from scratch and no ceiling was weakened. Only the finite statement is claimed — unrestricted Erdős Problem #287 remains open.

## New / modified files

* `RequestProject/Harmonic.lean` (new) — `∑_{n=a+1}^{M} 1/n ≤ log M − log a` by an integral-comparison induction, hence `< 1` when `3M ≤ 8a` (since `8/3 < e`), and the reusable consumer `not_counterexample_of_harmonic_forbidden_pair`.
* `RequestProject/Proth.lean` (new) — `prime_of_proth_half_pow_neg_one`: `N = k·2^e + 1`, `0 < k < 2^e`, `a^((N−1)/2) ≡ −1 (mod N)` ⟹ `N` prime, proved from the order/2-adic-valuation argument plus `minFac_sq_le_self`. It needs no factorization of `k` (unlike the existing Lucas interface). The congruence is discharged by kernel evaluation of the existing `powMod`. The classical "`k` odd" hypothesis turned out to be unnecessary for sufficiency and is omitted; both `k`s used are odd anyway (checked by the audit).
* `RequestProject/Factorial.lean` (new) — `forbiddenPP_of_factorial_bound`: with `L = w!`, every nonempty subset sum lies in `[1, w·w!]`, so `w·w! < p` gives the window certificate with no powerset enumeration.
* `RequestProject/Extension.lean` (new) — the constants `bigC, bigP, bigQ, bigT, bigX, U2, CHAIN_CEILING`, all requested identities (`3t+1 = 4P`, `4t+1 = 5Q`, `16P − 15Q = 1`, `x = 15Q`, `x+1 = 16P`, `U2 = ⌊8(x+1)/3⌋`, `x+1 < CHAIN_CEILING`), the two Proth primality proofs (witnesses `11` and `3`), the certificates `ForbiddenPP M P 1 42 (42!)` and `ForbiddenPP M Q 1 40 (40!)` valid for all `M ≤ U2` (using `U2 < 43P`, `U2 < 41Q`, `42·42! < P`, `40·40! < Q`), and `no_counterexample_of_chainCeiling_lt_max_le_U2`.
* `RequestProject/Chain.lean` — added `windowPairSupply_of_le_chainCeiling` (same block lemmas, ceiling `CHAIN_CEILING`); the original `windowPairSupply_of_le` is preserved verbatim.
* `RequestProject/Main.lean` — added `no_Erdos287Counterexample_of_max_le_chainCeiling`, the final theorem, and both `#print axioms` lines.
* `scripts/audit_u2.py`, `AUDIT_U2.md`, `scripts/make_archive.sh`, README section (new/updated).

## Audit

`scripts/audit_u2.py` (independent, reads the Lean sources back) and the pre-existing `scripts/audit.py` both PASS; the full report is `AUDIT_U2.md`. It re-derives `c, P, Q, t, x, U2, CHAIN_CEILING` from the Lean source and checks all the identities, the overlap `x+1 < CHAIN_CEILING`, `3·U2 ≤ 8(x+1)`, the tiling of `[8, CHAIN_CEILING]` by the eight block lemmas, the window bounds `U2 < 43P` / `U2 < 41Q`, the factorial subset-sum bounds, both Proth side conditions and congruences plus an independent 30-base strong primality test of `P` and `Q`, the hygiene scan, and the exact final theorem statement and unchanged problem statement.

An archive suitable for independent replay is produced by `sh scripts/make_archive.sh` (it writes `../erdos287-U2.tar.gz`; archives are excluded by the project's `.gitignore`, so the script rather than a binary blob is checked in).


# Summary of changes for run bf475d4f-3bd0-4258-9719-f0d13bc1f422
## Result

`lake build` passes from a clean tree, and

```
#print axioms Erdos287.no_Erdos287Counterexample_of_max_le_1e60
```

reports **exactly**:

```
'Erdos287.no_Erdos287Counterexample_of_max_le_1e60' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

No `sorry`, no `admit`, no new axioms, no `native_decide`, no `unsafe`, no `@[implemented_by]`. The problem statement was not weakened and the `10^60` ceiling was not lowered. Only the finite statement is claimed; Erdős Problem #287 itself remains open.

## Important note on the supplied inputs

The project as received contained **only** an empty `RequestProject/Main.lean` (a header of `set_option`s), `lakefile.toml`, `lean-toolchain` and the Mathlib manifest. There was no `Erdos287Counterexample` predicate, no `Gap2CE`/`WindowPairSupply` machinery, no formally verified finite base, no pinned `PrimeCert` dependency, and no `PRIME_PAIR_COVER.json`. Everything below was therefore written from scratch, and the finite certificate data was regenerated (`PRIME_PAIR_COVER.json`, produced by `scripts/gen_chain.py`). This is documented in `README.md`.

Consequences of that: the problem statement was formalised directly from the official statement of #287 (`{2,3,6}` sanity checks are included in `RequestProject/Defs.lean` to show the definition is not vacuous); primality certificates are implemented in-project on top of Mathlib's `lucas_primality`; and the regenerated chain has **192** pairs, not 327 — it satisfies exactly the requested conditions (`P_i = 2q_i − 1`, both prime, `q_i > 11`, `P_i < P_{i+1} ≤ 2P_i`, last interval past `10^60`), and is simply a denser choice.

## What was built

- `RequestProject/Window.lean` — the window lemma `no_dvd_of_window`: a `p`-adic valuation argument proving that a reciprocal representation of `1` with all parts `≤ M` contains no multiple of a prime power whose multiplier window is short enough. Proved independently, not transcribed from any verifier.
- `RequestProject/Defs.lean` — `Erdos287Counterexample`, `ForbiddenPP`, `WindowPairSupply`, and the bridge `not_counterexample_of_windowPairSupply`.
- `RequestProject/Pairs.lean` — the requested generic lemma: `q > 11` prime, `P = 2q − 1` prime, `P + 1 ≤ M ≤ 2P` ⟹ `WindowPairSupply M`, with `x = P`, `pu = P, au = 1` (window 2) and `pv = q, av = 1` (window 3).
- `RequestProject/Small.lean` — six hand-made window pairs (`x = 7, 13, 25, 46, 82, 158`) covering `8 ≤ M ≤ 316`, plus an exhaustive finite check for `M ≤ 7`.
- `RequestProject/PowMod.lean` — kernel-reducible binary modular exponentiation, proved correct, and `prime_of_cert` (Lucas certificates of Proth shape `N = c·2^t + 1` with `c` fully factored).
- `RequestProject/Certificates/Block00–07.lean` — 351 kernel-checked Lucas certificates and 33 `norm_num` primality facts.
- `RequestProject/Chain.lean` — interval lemmas and the covering theorem `windowPairSupply_of_le`.
- `RequestProject/Main.lean` — the target theorem and `#print axioms`.

Note: the hypothesis "`p^(a+1)` divides no element" turned out to be derivable from the other window hypotheses, so it is not part of the window lemma.

## Adversarial audit (`scripts/audit.py`, passes)

The audit reads the **Lean sources back** (not the JSON) and re-checks, independently of Lean:

- every claimed prime, by trial division plus a 30-base strong test — no probable-prime test enters the Lean proof, which uses only kernel-evaluated Lucas certificates;
- every Lucas certificate's own data (`a^(N−1) ≡ 1`, `a^((N−1)/p) ≢ 1` for `p = 2` and every `p` in the factor list), the shape `N = c·2^t + 1`, that the factor list multiplies to `c`, and that each listed factor is prime;
- `P_i = 2q_i − 1`, `q_i > 11` for all 192 pairs;
- every chain overlap `P_i < P_{i+1} ≤ 2P_i`;
- the endpoints of every interval lemma against `[P_i + 1, 2P_i]`;
- that the intervals tile `[2, 10^60]` with no gap, joining the finite base `M ≤ 7` to the first window pair at `M = 8`;
- the final interval: `2·P_191 = 1.516965997… × 10^60 ≥ 10^60`;
- a hygiene scan for forbidden constructs.

Negative controls were also run during development: a wrong Lucas witness and a composite `c·2^t+1` are both rejected by the kernel check, confirming the certificates are genuinely computed.

The bridge from `Erdos287Counterexample` to `WindowPairSupply` is fully machine-checked: if `x`, `x+1` are both forbidden and `x + 1 ≤ M ≤ 2x`, then some element of `A` is `≤ x` (a counting bound on reciprocals), and the largest such element violates the gap-at-most-two clause.
