This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Erdős Problem #287 — finite verification up to `U2 ≈ 3.739 · 10 ^ 60`

## What is proved

Erdős Problem #287 asks:

> Let `k ≥ 2`.  Is it true that, for any distinct integers `1 < n₁ < ⋯ < n_k` with
> `1 = 1/n₁ + ⋯ + 1/n_k`, we must have `max (n_{i+1} − n_i) ≥ 3`?

The problem is **open**.  This project proves the *finite* statement

```lean
theorem Erdos287.no_Erdos287Counterexample_of_max_le_1e60
    {A : Finset ℕ}
    (h : Erdos287Counterexample A)
    (hM : A.max' h.nonempty ≤ 10 ^ 60) :
    False
```

and its extension

```lean
theorem Erdos287.no_Erdos287Counterexample_of_max_le_U2
    {A : Finset ℕ}
    (h : Erdos287Counterexample A)
    (hM : A.max' h.nonempty ≤
      3739298103962937078961175187719640178760086558841160733818922) :
    False
```

i.e. **no counterexample has maximum denominator `≤ U2 = 3739298103962937078961175187719640178760086558841160733818922`**.
Nothing stronger is claimed: unrestricted Erdős Problem #287 remains **open**.

`#print axioms` reports, for both theorems,

```
'Erdos287.no_Erdos287Counterexample_of_max_le_1e60' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'Erdos287.no_Erdos287Counterexample_of_max_le_U2' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

No `sorry`, no `admit`, no new axioms, no `native_decide`, no `unsafe`, no `@[implemented_by]`.

## Note on the supplied inputs

The project as received contained only an empty `RequestProject/Main.lean` (a header of
`set_option`s) together with `lakefile.toml`, `lean-toolchain` and the Mathlib manifest.  It did
**not** contain a predicate `Erdos287Counterexample`, a `Gap2CE`/`WindowPairSupply` bridge, a
finite base, a `PrimeCert` dependency, or `PRIME_PAIR_COVER.json`.  Consequently every part of
the development below was written from scratch, and the finite certificate data was regenerated
here (`PRIME_PAIR_COVER.json`, produced by `scripts/gen_chain.py`).  The regenerated chain has
192 prime pairs rather than the 327 mentioned in the request; it satisfies exactly the stated
conditions (`P_i = 2 q_i − 1`, both prime, `P_i < P_{i+1} ≤ 2 P_i`, last interval beyond
`10 ^ 60`).

Because no `PrimeCert` package was pinned in the manifest, kernel-checkable primality
certificates are implemented directly in this project (`RequestProject/PowMod.lean`) on top of
Mathlib's `lucas_primality`.

## Structure

| file | contents |
|---|---|
| `RequestProject/Window.lean` | the window lemma `no_dvd_of_window`: a `p`-adic valuation argument showing a reciprocal representation of `1` with parts `≤ M` contains no multiple of a prime power with a short multiplier window |
| `RequestProject/Defs.lean` | the problem statement `Erdos287Counterexample`, the certificates `ForbiddenPP` / `WindowPairSupply`, and the bridge `not_counterexample_of_windowPairSupply` |
| `RequestProject/Pairs.lean` | `windowPairSupply_of_prime_pair`: `q > 11` prime, `P = 2q − 1` prime ⟹ `WindowPairSupply M` for `P + 1 ≤ M ≤ 2P` |
| `RequestProject/Small.lean` | hand-made window pairs covering `8 ≤ M ≤ 316`, and an exhaustive finite check for `M ≤ 7` |
| `RequestProject/PowMod.lean` | kernel-reducible binary modular exponentiation, proved correct, and `prime_of_cert` (Lucas certificates of Proth shape `N = c · 2^t + 1`) |
| `RequestProject/Certificates/Block*.lean` | 351 Lucas certificates and 33 `norm_num` primality facts for the 192 pairs |
| `RequestProject/Chain.lean` | interval lemmas for each pair and the covering theorem `windowPairSupply_of_le` |
| `RequestProject/Harmonic.lean` | the harmonic blocker: `∑_{n=a+1}^{M} 1/n ≤ log M − log a < 1` when `3M ≤ 8a`, and the consumer `not_counterexample_of_harmonic_forbidden_pair` |
| `RequestProject/Proth.lean` | Proth's criterion `prime_of_proth_half_pow_neg_one`: `N = k·2^e + 1`, `k < 2^e`, `a^((N−1)/2) ≡ −1 (mod N)` ⟹ `N` prime |
| `RequestProject/Factorial.lean` | `forbiddenPP_of_factorial_bound`: window certificates with `L = w!` when `w·w! < p`, avoiding any powerset enumeration |
| `RequestProject/Extension.lean` | the constants `c, P, Q, t, x, U2, CHAIN_CEILING`, their arithmetic, the two Proth primality proofs, and the interval `(CHAIN_CEILING, U2]` |
| `RequestProject/Main.lean` | the target theorems and `#print axioms` |

## Mathematical argument

Let `A` be a counterexample with maximum `M`.

1. **Window lemma.**  Fix a prime `p` and `a ≥ 1`.  Multiplying `∑_{n ∈ A} 1/n = 1` by `p^a` and
   splitting `A` according to divisibility by `p^a`, every term coming from an `n` *not* divisible
   by `p^a` has positive `p`-adic valuation, and so does `p^a` itself.  Hence the remaining part
   `∑_{j ∈ J} 1/j` (where `J = {n / p^a : n ∈ A, p^a ∣ n} ⊆ {1, …, w}`, `w = ⌊M / p^a⌋`) has
   positive valuation too.  Writing it as `m / L` with `L` a common multiple of `1, …, w` prime to
   `p`, this forces `p ∣ m`.  If `p` divides no nonempty subset sum `∑_{j ∈ J} L/j`, then `J = ∅`:
   `A` contains **no multiple of `p^a`**.

2. **Window pairs.**  Suppose `x` and `x + 1` are both forbidden in this sense and
   `x + 1 ≤ M ≤ 2x`.  Since the elements of `A` above `x` number at most `M − x ≤ x` and are each
   `≥ x + 1`, their reciprocals sum to less than `1`; so some element of `A` is `≤ x`.  Take the
   largest such element `y`.  It is `< x`, it is not the maximum of `A`, and neither `y + 1` nor
   `y + 2` can lie in `A` (they would be `≤ x + 1` and larger than `y`, and `x`, `x + 1 ∉ A`).
   This contradicts the gap-at-most-two hypothesis.

3. **Prime pairs.**  For `q > 11` prime with `P = 2q − 1` prime and `P + 1 ≤ M ≤ 2P`:
   `P` has multiplier window `2` (subset sums `2, 1, 3`, all `< P`), and `q` divides
   `x + 1 = 2q` with multiplier window `3` (subset sums at most `11 < q`).  So `(P, P+1)` is a
   window pair, killing all `M ∈ [P + 1, 2P]`.

4. **Covering.**  `M ≤ 7` is settled by enumerating the `64` subsets of `{2, …, 7}`.  Six
   hand-made window pairs (`x = 7, 13, 25, 46, 82, 158`) cover `8 ≤ M ≤ 316`, and the certified
   chain of 192 prime pairs, starting at `(q, P) = (157, 313)` and satisfying
   `P_i < P_{i+1} ≤ 2 P_i`, covers `314 ≤ M ≤ 2 P_{191} ≈ 1.517 · 10^60`.

## The extension from `CHAIN_CEILING` to `U2`

The prime-pair chain covers every maximum up to

```
CHAIN_CEILING = 1516965997302524373612172717550681525506538629288954643349506.
```

Above it a **single** blocker suffices, because the crude counting bound behind
`WindowPairSupply` (which needs `M ≤ 2x`) is replaced by a harmonic bound.  With

```
c = 4609040761224086961713861467
P = 15·c·2^100 + 1 = 87639799311631337788152543462179066689689528722839704698881   (prime)
Q =    c·2^104 + 1 = 93482452599073426974029379692991004469002163971029018345473   (prime)
t = 1 + 5·c·2^102,   3t + 1 = 4P,   4t + 1 = 5Q,   16P − 15Q = 1
x = 15Q,   x + 1 = 16P,   U2 = ⌊8(x+1)/3⌋
```

one has `x + 1 < CHAIN_CEILING`, so the new interval overlaps the range already covered.

* `P` and `Q` are proved prime by Proth's criterion (witnesses `11` and `3`), the modular power
  being evaluated by the kernel through `powMod`; no probable-prime test enters the proof.
* For every `M ≤ U2` one has `M < 43P` and `M < 41Q`, so the multiplier windows are `42` and
  `40`; since `42·42! < P` and `40·40! < Q`, the certificates `ForbiddenPP M P 1 42 (42!)` and
  `ForbiddenPP M Q 1 40 (40!)` hold — every nonempty subset sum `∑ w!/j` lies strictly between
  `0` and the prime, so no powerset is ever enumerated.
* Hence `x` and `x + 1` are absent from any counterexample with maximum `M ≤ U2`.  If moreover
  `x + 1 < M`, the gap-at-most-two condition pushes all of `A` above `x + 1`, so
  `1 = ∑_{n∈A} 1/n ≤ ∑_{n=x+2}^{M} 1/n ≤ log(M/(x+1)) ≤ log(8/3) < 1`, a contradiction.

## Reproducing / auditing the certificate data

```
python3 scripts/gen_chain.py    # searches for the chain -> scripts/chain.json
python3 scripts/gen_lean.py     # emits Certificates/Block*.lean, Chain.lean, PRIME_PAIR_COVER.json
python3 scripts/audit.py        # independent audit, reading the emitted Lean sources back
python3 scripts/low_range.py    # search that produced the small window pairs
python3 scripts/audit_u2.py     # independent audit of the extension to U2
sh scripts/make_archive.sh      # source archive for independent replay (../erdos287-U2.tar.gz)
```

The full audit report is `AUDIT_U2.md`.

`python3 scripts/audit_u2.py` is an independent audit of the extension: it re-derives `c, P, Q,
t, x, U2, CHAIN_CEILING` from `RequestProject/Extension.lean`, checks `3t+1 = 4P`, `4t+1 = 5Q`,
`16P − 15Q = 1`, `x = 15Q`, `x+1 = 16P`, `U2 = ⌊8(x+1)/3⌋`, the overlap `x+1 < CHAIN_CEILING`,
the window bounds `U2 < 43P`, `U2 < 41Q`, the factorial subset-sum bounds, both Proth
certificates (plus an independent primality test of `P` and `Q`), the tiling of
`[8, CHAIN_CEILING]` by the block lemmas, the absence of forbidden constructs, and the exact
statement of the final theorem.

`scripts/audit.py` parses the Lean sources (not the JSON) and re-checks, independently of Lean:
every claimed prime (Miller–Rabin plus trial division), every Lucas certificate's own data,
`P_i = 2 q_i − 1` and `q_i > 11`, every chain overlap `P_i < P_{i+1} ≤ 2 P_i`, the endpoints of
every interval lemma, that the intervals tile `[2, 10^60]` with no gap starting from the finite
base `M ≤ 7`, and that no forbidden construct occurs in any Lean file.
