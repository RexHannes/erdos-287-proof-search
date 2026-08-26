import Mathlib
import RequestProject.Erdos287.Blocker
import RequestProject.Erdos287.PrimeFree

/-!
# Erdős #287 — good-prime exclusion, the adjacent blocker, and the finite
log-cofactor blocker

Everything here is finite and elementary; **Erdős #287 remains OPEN** and no theorem in
this file claims otherwise.  All statements are conditional on a hypothetical
representation `∑_{a ∈ A} 1/a = 1` (respectively on a hypothetical gap-`≤2`
counterexample `Gap2CE`).

* `GoodPrime M q` — `q` is prime, `q² > M` and `q > C(⌊M/q⌋)`.
* `goodPrimeExclusion` — no denominator of a reciprocal representation with maximum `≤ M`
  is divisible by a good prime.  (Via the maximal `q`-adic fibre congruence, i.e. the
  banked `primePower_window_exclusion` at exponent `1`.)
* `Gap2CE.goodPrime_adjacent_holes` / `goodPrime_adjacent_blocker` — if `q₀ ∣ x` and
  `q₁ ∣ (x+1)` are good primes and `x, x+1` lie in the denominator span, then `x` and
  `x+1` are adjacent holes, contradicting the gap-`≤2` hypothesis.
* `Gap2CE.logCofactor_finite_blocker` — the finite (abstract-`J`) log-cofactor blocker:
  from `qᵢ ≥ M/(2J)`, `qᵢ² > M` and `qᵢ > C(2J)` the same contradiction follows.  The
  asymptotic statement `J ≤ η log M / log log M` is *not* proved here; it is recorded as
  an external elementary-asymptotic interface (`Challenges/Delta6Interfaces.lean`).
-/

open scoped BigOperators

namespace TrustedBank
namespace Erdos287Good

open Erdos287

/-- **Good prime.**  `q` is prime, `q² > M`, and `q` exceeds the maximum reciprocal-sum
numerator over the window `{1, …, ⌊M/q⌋}`. -/
def GoodPrime (M q : ℕ) : Prop :=
  q.Prime ∧ M < q ^ 2 ∧ C (M / q) < (q : ℤ)

/-- A good prime is an excluded prime power (with exponent `1`). -/
theorem GoodPrime.excludedPP {M q : ℕ} (h : GoodPrime M q) : ExcludedPP M q :=
  ⟨q, 1, h.1, le_refl 1, (pow_one q).symm, h.2.2⟩

/-- **Good Prime Exclusion.**  If `A` is a finite set of positive integers, bounded by
`M`, with `∑_{a ∈ A} 1/a = 1`, and `q` is a good prime for `M`, then no element of `A`
is divisible by `q`.

The hypothesis `M < q²` is part of the stated criterion; the proof itself only uses
primality and the window bound `C(⌊M/q⌋) < q`. -/
theorem goodPrimeExclusion (A : Finset ℕ) (M q : ℕ) (hq : GoodPrime M q)
    (hpos : ∀ a ∈ A, 0 < a) (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) :
    ∀ a ∈ A, ¬ q ∣ a := by
  intro a ha hdvd
  exact ExcludedPP.not_dvd_mem hq.excludedPP hpos hAM hsum ha hdvd

/-- The same statement in "empty top fibre" form: the set of denominators divisible by a
good prime is empty. -/
theorem goodPrime_fibre_empty (A : Finset ℕ) (M q : ℕ) (hq : GoodPrime M q)
    (hpos : ∀ a ∈ A, 0 < a) (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) :
    A.filter (fun a => q ∣ a) = ∅ := by
  refine Finset.filter_eq_empty_iff.mpr ?_
  intro a ha
  exact goodPrimeExclusion A M q hq hpos hAM hsum a ha

/-! ## Small synthetic hostile tests for `GoodPrime` -/

/-- `q = 5` is a good prime for `M = 6`: `⌊6/5⌋ = 1`, `C 1 = 1 < 5`, and `25 > 6`. -/
theorem goodPrime_six_five : GoodPrime 6 5 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [show (6 : ℕ) / 5 = 1 from rfl, C_one]
  norm_num

/-- Consistency of the exclusion on a genuine representation: `A = {2,3,6}` has
reciprocal sum `1`, and indeed no element is divisible by the good prime `5`. -/
theorem goodPrime_six_five_excludes :
    ∀ a ∈ ({2, 3, 6} : Finset ℕ), ¬ (5 : ℕ) ∣ a := by
  decide

/-- `q = 2` is **not** a good prime for `M = 6` (`C 3 = 11 ≥ 2`), which is exactly why
`2 ∣ 2 ∈ A` is not excluded: the criterion does not misfire. -/
theorem not_goodPrime_six_two : ¬ GoodPrime 6 2 := by
  rintro ⟨-, -, h⟩
  rw [show (6 : ℕ) / 2 = 3 from rfl, C_three] at h
  norm_num at h

namespace Gap2CE

open Erdos287.Gap2CE

variable (ce : Erdos287.Gap2CE)

/-- **Adjacent good-factor holes.**  If `q₀ ∣ x` and `q₁ ∣ (x+1)` are good primes for
`M`, then both `x` and `x+1` are holes of the counterexample. -/
theorem goodPrime_adjacent_holes {x q₀ q₁ : ℕ}
    (h0 : GoodPrime ce.M q₀) (h1 : GoodPrime ce.M q₁)
    (hd0 : q₀ ∣ x) (hd1 : q₁ ∣ x + 1) :
    x ∉ ce.A ∧ x + 1 ∉ ce.A :=
  ⟨ce.notMem_of_excludedPP h0.excludedPP hd0, ce.notMem_of_excludedPP h1.excludedPP hd1⟩

/-- **Adjacent good-factor blocker.**  Two adjacent integers in the denominator span,
each divisible by a good prime, contradict the gap-`≤2` hypothesis. -/
theorem goodPrime_adjacent_blocker {x q₀ q₁ : ℕ}
    (hxN : ce.N ≤ x) (hxM : x + 1 ≤ ce.M)
    (h0 : GoodPrime ce.M q₀) (h1 : GoodPrime ce.M q₁)
    (hd0 : q₀ ∣ x) (hd1 : q₁ ∣ x + 1) : False := by
  obtain ⟨hx, hx1⟩ := goodPrime_adjacent_holes ce h0 h1 hd0 hd1
  exact ce.blockerPair_contradiction hxN hxM hx hx1

/-- The literal form requested in the task statement, with `M/2 < x < x+1 ≤ M`.

The hypothesis `hhalf : ce.M < 2 * x` is stated because the task states it; the proof
does not use it (the blocker only needs `x, x+1` inside the denominator span). -/
theorem goodPrime_adjacent_blocker_upper_half {x q₀ q₁ : ℕ}
    (hhalf : ce.M < 2 * x) (hxN : ce.N ≤ x) (hxM : x + 1 ≤ ce.M)
    (h0 : GoodPrime ce.M q₀) (h1 : GoodPrime ce.M q₁)
    (hd0 : q₀ ∣ x) (hd1 : q₁ ∣ x + 1) : False :=
  goodPrime_adjacent_blocker ce hxN hxM h0 h1 hd0 hd1

/-! ### The finite log-cofactor blocker (abstract `J`) -/

/-- A prime `q` with `M ≤ 2J·q`, `q² > M` and `q > C(2J)` is a good prime.
This is the finite half of the log-cofactor reduction: the window `⌊M/q⌋` is at most
`2J`, so monotonicity of `C` applies. -/
theorem goodPrime_of_window_bound {M J q : ℕ} (hq : q.Prime)
    (hlow : M ≤ 2 * J * q) (hsq : M < q ^ 2) (hC : C (2 * J) < (q : ℤ)) :
    GoodPrime M q := by
  refine ⟨hq, hsq, lt_of_le_of_lt (C_mono ?_) hC⟩
  calc M / q ≤ (2 * J * q) / q := Nat.div_le_div_right hlow
    _ = 2 * J := Nat.mul_div_cancel _ hq.pos

/-- **Finite log-cofactor blocker.**  For an abstract cutoff `J`, if `x` and `x+1` lie
in the denominator span and each has a prime factor `qᵢ` with `qᵢ ≥ M/(2J)` (in the
integral form `M ≤ 2J·qᵢ`), `qᵢ² > M` and `qᵢ > C(2J)`, then no gap-`≤2` counterexample
exists.

The asymptotic input `J ≤ η log M / log log M` is deliberately *not* formalized here;
it is recorded as an open external interface. -/
theorem logCofactor_finite_blocker {J x q₀ q₁ : ℕ}
    (hxN : ce.N ≤ x) (hxM : x + 1 ≤ ce.M)
    (hq0 : q₀.Prime) (hq1 : q₁.Prime)
    (hlow0 : ce.M ≤ 2 * J * q₀) (hlow1 : ce.M ≤ 2 * J * q₁)
    (hsq0 : ce.M < q₀ ^ 2) (hsq1 : ce.M < q₁ ^ 2)
    (hC0 : C (2 * J) < (q₀ : ℤ)) (hC1 : C (2 * J) < (q₁ : ℤ))
    (hd0 : q₀ ∣ x) (hd1 : q₁ ∣ x + 1) : False :=
  goodPrime_adjacent_blocker ce hxN hxM
    (goodPrime_of_window_bound hq0 hlow0 hsq0 hC0)
    (goodPrime_of_window_bound hq1 hlow1 hsq1 hC1) hd0 hd1

end Gap2CE

end Erdos287Good
end TrustedBank
