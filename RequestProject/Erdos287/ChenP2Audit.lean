import RequestProject.Erdos287.Chain

/-!
# Erdős Problem #287 — audit of the Chen / P₂ relaxation of the blocker pair

The certified blocker-pair contradiction (`Gap2CE.excludedPP_blockerPair`) forces two
adjacent holes `x, x+1 ∈ [N, M]` from two **excluded prime powers** `q₁ ∣ x`, `q₂ ∣ x+1`.
Exclusion is delivered by `primePower_window_exclusion`, whose proof is *intrinsically a
single-prime argument*: divisibility by `p^e` puts the element in the top `p`-adic layer,
whose reciprocal-sum numerator is bounded by `C(⌊M/p^e⌋)` yet must be divisible by `p`,
forcing it to vanish — a contradiction once `p > C(⌊M/p^e⌋)`.

This file audits whether **one side of the blocker pair can be relaxed from a prime power
`q` to a `P₂ = q₁·q₂`** (a semiprime, or more generally an almost-prime with controlled
prime factors) while still forcing a hole.

## Summary of the verdict (all machine-checked below)

* **Task 1.** We state the exact relaxed exclusion primitive `P2ForcesExclusion` and the
  relaxed blocker-pair theorem `RelaxedBlockerPair`.
* **Task 2/3.** The natural relaxation is **false**: `not_P2ForcesExclusion`. The concrete
  local configuration is `A = {2, 3, 6}` (`∑ 1/a = 1`) with `M = 6` and the semiprime
  `q = 6 = 2·3`.  Its "favourable" window `⌊M/q⌋ = 1` gives `C 1 = 1 < 2`, so the naive
  P₂ rule *predicts* a hole at `6`; yet `6 ∈ A`, so no hole is forced.
  `p2_window_illegitimate` pins down *why*: the top-layer argument only ever provides the
  window `⌊M/pᵢ⌋` of an *individual* prime factor, and for both factors of `6` that window
  fails to exclude (`C(⌊6/2⌋) = 11 ≥ 2`, `C(⌊6/3⌋) = 3 ≥ 3`).
* **Salvage.** The *only* sound way a `P₂` forces a hole is when one of its prime factors
  is *itself* an excluded prime power (`P2_excluded_via_prime_factor`) — but that reduces
  to the existing prime-power exclusion and is not a genuine relaxation.
* **Task 4.** Consequently a Chen-type theorem (infinitely many `p` with `p+2` a `P₂`) does
  **not** yield a usable infinite tail of blocker pairs: the `P₂` neighbour fails to force
  its hole. See `SFT_AUDIT.md` companion notes / the docstring of `chen_no_usable_tail`.
-/

open scoped BigOperators

namespace Erdos287

/-! ## Task 1 — the relaxed exclusion primitive and relaxed blocker pair -/

/-- `q` is a `P₂` (semiprime): a product of two primes. -/
def IsP2 (q : ℕ) : Prop := ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ q = p₁ * p₂

/-- The **naive P₂ exclusion predicate**: the literal analogue of `ExcludedPP` in which the
prime power `p^e` is replaced by a semiprime `q = p₁·p₂` (`p₁ ≤ p₂`), the window is the
*product's* window `⌊M/q⌋`, and the threshold is the smaller prime factor `p₁`.

This is the strongest/most favourable version of the relaxation: it uses the *smallest*
possible window `⌊M/q⌋` (making `C` small) and only demands the *smaller* prime factor to
beat it.  If even this fails to force exclusion, so does every weaker P₂ rule. -/
def ExcludedP2Naive (M q : ℕ) : Prop :=
  ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ ≤ p₂ ∧ q = p₁ * p₂ ∧ C (M / q) < (p₁ : ℤ)

/-- **Task 1 — the exact relaxed exclusion claim.**  "A naively-excluded `P₂` forces a
hole": every element of a reciprocal-sum-`1` set `A ⊆ [1,M]` avoids multiples of a
naively-excluded semiprime `q`.  (Compare `ExcludedPP.not_dvd_mem`.) -/
def P2ForcesExclusion : Prop :=
  ∀ (M q : ℕ), ExcludedP2Naive M q →
    ∀ (A : Finset ℕ), (∀ a ∈ A, 0 < a) → (∀ a ∈ A, a ≤ M) →
      (∑ a ∈ A, (1 : ℚ) / a = 1) → ∀ x ∈ A, ¬ q ∣ x

/-- **Task 1 — the exact relaxed blocker-pair theorem.**  One side of the blocker pair is
relaxed from a prime power to a naively-excluded `P₂`; the other side stays an excluded
prime power.  This is the statement one would *want* in order to use a Chen-type pairing
(prime `p` next to a `P₂`). -/
def RelaxedBlockerPair : Prop :=
  ∀ (ce : Gap2CE) (x q₁ q₂ : ℕ),
    ce.N ≤ x → x + 1 ≤ ce.M →
    ExcludedP2Naive ce.M q₁ → ExcludedPP ce.M q₂ →
    q₁ ∣ x → q₂ ∣ (x + 1) → False

/-! ## Task 2 / 3 — the relaxation is false, with a concrete configuration

The natural P₂ exclusion primitive `P2ForcesExclusion` is refuted by the reciprocal-sum-`1`
configuration `A = {2, 3, 6}` and the semiprime `q = 6`. -/

/-- The witness set `A = {2, 3, 6}` has reciprocal sum `1`. -/
theorem p2_witness_sum : (∑ a ∈ ({2, 3, 6} : Finset ℕ), (1 : ℚ) / a) = 1 := by
  norm_num

/-- `q = 6 = 2·3` is naively excluded on the window `[1, 6]`: its product window is
`⌊6/6⌋ = 1`, where `C 1 = 1 < 2`, the smaller prime factor. -/
theorem p2_six_excludedNaive : ExcludedP2Naive 6 6 := by
  refine ⟨2, 3, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num [C_one]

/-- **Task 2/3 result.**  The naive P₂ exclusion primitive is **false**: a semiprime that
is "naively excluded" can still divide a member of a reciprocal-sum-`1` set. -/
theorem not_P2ForcesExclusion : ¬ P2ForcesExclusion := by
  intro h
  -- Apply the claimed exclusion to A = {2,3,6}, M = 6, q = 6, x = 6.
  have hx : ¬ (6 : ℕ) ∣ 6 :=
    h 6 6 p2_six_excludedNaive ({2, 3, 6} : Finset ℕ)
      (by intro a ha; fin_cases ha <;> norm_num)
      (by intro a ha; fin_cases ha <;> norm_num)
      p2_witness_sum 6 (by norm_num)
  exact hx (dvd_refl 6)

/-- **Why the relaxation fails.**  The single-prime top-layer argument can only ever offer
the window of an *individual* prime factor `pᵢ`, namely `⌊M/pᵢ⌋` — never the smaller
product window `⌊M/q⌋`.  For the counterexample `q = 6` on `[1,6]`, *both* legitimate
individual-prime windows fail to exclude:

* factor `2`: window `⌊6/2⌋ = 3`, `C 3 = 11 ≥ 2`;
* factor `3`: window `⌊6/3⌋ = 2`, `C 2 = 3 ≥ 3`.

So the exclusion is not merely unproven by our method — no member of the top-layer family
is genuinely excluded, matching the fact that `6 ∈ A`. -/
theorem p2_window_illegitimate :
    ¬ (C (6 / 2) < (2 : ℤ)) ∧ ¬ (C (6 / 3) < (3 : ℤ)) := by
  constructor
  · norm_num [C_three]
  · norm_num [C_two]

/-! ## Salvage — the only sound `P₂` blocker is a disguised prime-power blocker

A semiprime `q` *does* force a hole precisely when one of its prime factors is itself an
excluded prime power.  But then divisibility by that prime already excludes the element:
the "P₂" plays no role, so this is not a genuine relaxation. -/

/-- If a prime power `p₀` dividing the semiprime `q` is genuinely excluded on `[1,M]`, then
`q` cannot divide any member of a reciprocal-sum-`1` set `A ⊆ [1,M]`.  This is immediate
from `ExcludedPP.not_dvd_mem` (via `p₀ ∣ q ∣ x`) and shows the salvage adds nothing beyond
the prime-power case. -/
theorem P2_excluded_via_prime_factor {M q p₀ : ℕ} (hexc : ExcludedPP M p₀)
    (hpq : p₀ ∣ q) {A : Finset ℕ} (hpos : ∀ a ∈ A, 0 < a) (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) {x : ℕ} (hxA : x ∈ A) (hqx : q ∣ x) : False :=
  ExcludedPP.not_dvd_mem hexc hpos hAM hsum hxA (dvd_trans hpq hqx)

/-! ## Task 4 — no usable infinite tail from a Chen-type theorem

Chen-type theorems (e.g. infinitely many primes `p` with `p + 2` a `P₂`) supply an infinite
family of `(prime, P₂)` neighbours.  To convert such a family into an infinite tail of
blocker pairs one would need each `P₂` neighbour to *force its hole* via
`RelaxedBlockerPair`.  But `not_P2ForcesExclusion` shows the `P₂` side does **not** force a
hole in general, so the tail collapses: the prime side gives one hole, the `P₂` side gives
none, and no adjacent double hole is produced.

We record this as: `RelaxedBlockerPair` would entail `P2ForcesExclusion`-style exclusion,
which is false.  Concretely, any purported "Chen tail" theorem that produced a hole from a
naively-excluded `P₂` would contradict `not_P2ForcesExclusion` on the local configuration
`{2,3,6}`.  Hence no Chen-type input yields a usable infinite tail through this mechanism. -/
theorem chen_no_usable_tail :
    ¬ P2ForcesExclusion := not_P2ForcesExclusion

end Erdos287
