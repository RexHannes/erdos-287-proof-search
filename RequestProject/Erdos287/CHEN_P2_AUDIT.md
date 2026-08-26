# Audit: the Chen / P₂ relaxation of the blocker pair (Erdős #287 kernel)

Audit only. No claim that #287 is solved. Every machine-checked claim below is a theorem
in `RequestProject/Erdos287/ChenP2Audit.lean`; the file builds and contains no `sorry`,
`axiom`, `unsafe`, or `native_decide`, and every cited theorem reduces to the allowed
axioms `propext`, `Classical.choice`, `Quot.sound`.

## The question

In the certified kernel, the blocker-pair contradiction (`Gap2CE.excludedPP_blockerPair`)
forces two adjacent holes `x, x+1 ∈ [N, M]` from two **excluded prime powers** `q₁ ∣ x`,
`q₂ ∣ x+1`. Exclusion is delivered by `primePower_window_exclusion`. Can **one** side be
relaxed from a prime power `q` to a `P₂ = q₁·q₂` (semiprime) while still forcing its hole?

## Task 1 — the exact relaxed statements

* `IsP2 q` — `q` is a product of two primes.
* `ExcludedP2Naive M q` — the literal analogue of `ExcludedPP`, in its **most favourable**
  form: `q = p₁·p₂` (`p₁ ≤ p₂`), window `⌊M/q⌋`, threshold `C(⌊M/q⌋) < p₁`. (Smallest
  possible window ⇒ smallest `C`; only the smaller factor must beat it. If this cannot
  force exclusion, no weaker P₂ rule can.)
* `P2ForcesExclusion` — the relaxed exclusion primitive: a naively-excluded `P₂` avoids
  every reciprocal-sum-`1` set `A ⊆ [1,M]` (analogue of `ExcludedPP.not_dvd_mem`).
* `RelaxedBlockerPair` — the relaxed blocker-pair theorem: one side `ExcludedP2Naive`, the
  other `ExcludedPP`, forcing `False` on a `Gap2CE`.

## Task 2 — attempt to prove it

The proof of `primePower_window_exclusion` is intrinsically single-prime: divisibility by
`p^e` places the element in the **top `p`-adic layer**, whose reciprocal-sum numerator is
`≤ C(⌊M/p^e⌋)` yet `≡ 0 (mod p)` (`topLayer_congruence`), forcing it to vanish once
`p > C(⌊M/p^e⌋)`. A semiprime supplies **no single modulus** with a dominant valuation, so
there is nothing to run the top-layer congruence against. The relaxation cannot be proved.

## Task 3 — it is false, with a concrete local configuration

`not_P2ForcesExclusion : ¬ P2ForcesExclusion`.

Concrete configuration: `A = {2, 3, 6}`, `∑ 1/a = 1` (`p2_witness_sum`), `M = 6`, semiprime
`q = 6 = 2·3`.

* `p2_six_excludedNaive : ExcludedP2Naive 6 6` — the *product* window is `⌊6/6⌋ = 1`, and
  `C 1 = 1 < 2`, so the naive P₂ rule **predicts a hole at 6**.
* But `6 ∈ A`, so **no hole is forced** — the prediction is wrong.

`p2_window_illegitimate` explains why: the top-layer argument only ever provides the window
of an *individual* prime factor `pᵢ`, `⌊M/pᵢ⌋`, never the smaller product window `⌊M/q⌋`.
For both factors of `6` the legitimate window fails to exclude:

* factor `2`: `⌊6/2⌋ = 3`, `C 3 = 11 ≥ 2`;
* factor `3`: `⌊6/3⌋ = 2`, `C 2 = 3 ≥ 3`.

The fallacy of the relaxation is exactly the illegitimate replacement `⌊M/pᵢ⌋ ↝ ⌊M/q⌋`.

## Salvage (not a genuine relaxation)

`P2_excluded_via_prime_factor`: if one prime factor `p₀ ∣ q` is *itself* an excluded prime
power (`ExcludedPP M p₀`), then `q` forces a hole — but only because `p₀ ∣ x` already does,
via `ExcludedPP.not_dvd_mem`. This is the prime-power blocker in disguise and gains nothing:
it needs the *larger* factor to be a near-`M` prime, i.e. it is not a P₂ relaxation at all.

## Task 4 — Chen-type input gives no usable infinite tail

A Chen-type theorem (infinitely many primes `p` with `p+2` a `P₂`) supplies infinitely many
`(prime, P₂)` neighbours. Turning them into a tail of blocker pairs needs each `P₂` to force
its hole, i.e. it needs `RelaxedBlockerPair` / `P2ForcesExclusion`. Since these are false
(`chen_no_usable_tail = not_P2ForcesExclusion`), the prime side gives one hole and the `P₂`
side gives none: no adjacent double hole is produced, so **no usable infinite tail** follows
through this mechanism.

Because the P₂ relaxation fails, the sound blocker inputs remain the genuine prime-power
pairs already certified (`Gap2CE.excludedPP_blockerPair`, and the good-prime / safe-prime
blockers `Gap2CE.goodPrime_blocker_{sub,add}`, `Gap2CE.safePrime_blocker`, which do require
a genuinely large prime factor rather than a mere almost-prime).

## Required output

* **Can one side be relaxed to P₂?** No — not by the top-layer / prime-power exclusion
  theorem. The relaxation is false.
* **First point of failure.** The exclusion primitive `P2ForcesExclusion`
  (`not_P2ForcesExclusion`), i.e. the illegitimate window replacement `⌊M/pᵢ⌋ ↝ ⌊M/q⌋`
  (`p2_window_illegitimate`).
* **Concrete counterexample.** `A = {2,3,6}`, `M = 6`, `q = 6 = 2·3`.
* **Theorems (in `ChenP2Audit.lean`).** `IsP2`, `ExcludedP2Naive`, `P2ForcesExclusion`,
  `RelaxedBlockerPair`, `p2_witness_sum`, `p2_six_excludedNaive`, `not_P2ForcesExclusion`,
  `p2_window_illegitimate`, `P2_excluded_via_prime_factor`, `chen_no_usable_tail`.
* **Build.** Succeeds (`RequestProject.Main`, 8040 jobs).
* **Placeholders.** None; only `propext`, `Classical.choice`, `Quot.sound` are used.
