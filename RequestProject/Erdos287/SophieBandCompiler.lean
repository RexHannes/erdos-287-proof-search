import RequestProject.Erdos287.SophieOptimal

/-!
# Erdős Problem #287 — the fixed interior band compiler

This file converts "a prime `q` lies in a fixed rational band around `X = ⌊M/2⌋`" into the
exact hypotheses of the plus/minus Sophie blockers of `SophieOptimal.lean`, and packages the
resulting conditional refutation.

The constants are **not** `(3/4, 4/5)`.  The literal requirements of the blockers are

* `M < 3q`     (so that the window `⌊M/q⌋` is `≤ 2`), i.e. `q > M/3`;
* `2q + 1 ≤ M` (so that `2q` and `2q ± 1` fit in the window), i.e. `q ≤ (M-1)/2`;

so the *exact* admissible interval is `M/3 < q ≤ (M-1)/2` (`Erdos287.band_exact`), which in
terms of `X = ⌊M/2⌋` is essentially `(2/3)·X < q < 1·X`.  Any pair `1/2 < α < β < 1` with
`α > 2/3` and `β < 1` works with enough slack; `(3/4, 4/5)` is admissible but wastes most of
the band.  We prove the clean, near-maximal pair

  `α = 7/10`,  `β = 24/25`,  `M_min = 25`,

i.e. `7·X < 10·q` and `25·q < 24·X`, with all floor/parity endpoints handled by `omega`
(no real arithmetic, no rounding hand-waving).
-/

open scoped BigOperators

namespace Erdos287

/-- The fixed rational band `7·⌊M/2⌋ < 10·q` and `25·q < 24·⌊M/2⌋`
(i.e. `α = 7/10 < β = 24/25` applied to `X = ⌊M/2⌋`). -/
def InBand (M q : ℕ) : Prop := 7 * (M / 2) < 10 * q ∧ 25 * q < 24 * (M / 2)

instance (M q : ℕ) : Decidable (InBand M q) := by unfold InBand; infer_instance

/-- **Exact band.**  The two blocker hypotheses `M < 3q` and `2q + 1 ≤ M` say exactly that
`q` lies in the half-open interval `(M/3, (M-1)/2]`. -/
theorem band_exact {M q : ℕ} :
    (M < 3 * q ∧ 2 * q + 1 ≤ M) ↔ (M / 3 < q ∧ 2 * q < M) := by
  omega

/-- **Band compiler.**  For `M ≥ 25`, membership in the fixed band forces every numerical
hypothesis of the plus/minus Sophie blockers: `q > 3`, `M < 3q`, and `2q + 1 ≤ M`. -/
theorem band_hypotheses {M q : ℕ} (hM : 25 ≤ M) (hb : InBand M q) :
    3 < q ∧ M < 3 * q ∧ 2 * q + 1 ≤ M := by
  obtain ⟨h1, h2⟩ := hb
  refine ⟨by omega, by omega, by omega⟩

/-- The banded pair `(3/4, 4/5)` is admissible too, but only from `M ≥ 10` onwards and on a
much narrower band; recorded for comparison with the prose formulation. -/
theorem band_hypotheses_three_quarters {M q : ℕ} (hM : 20 ≤ M)
    (h1 : 3 * (M / 2) < 4 * q) (h2 : 5 * q < 4 * (M / 2)) :
    3 < q ∧ M < 3 * q ∧ 2 * q + 1 ≤ M :=
  ⟨by omega, by omega, by omega⟩

namespace Gap2CE

variable (ce : Gap2CE)

/-- **Banded plus blocker.**  A prime `q` in the fixed band with `2q + 1` prime refutes any
gap-`≤2` counterexample with `M ≥ 25`. -/
theorem band_plus_blocker {q : ℕ} (hM : 25 ≤ ce.M) (hq : q.Prime) (hb : InBand ce.M q)
    (hp : (2 * q + 1).Prime) : False := by
  obtain ⟨hq3, hM3, hfit⟩ := band_hypotheses hM hb
  exact ce.plus_sophie_blocker hq hq3 hp rfl (by omega) hM3

/-- **Banded minus blocker.**  A prime `q` in the fixed band with `2q - 1` prime refutes any
gap-`≤2` counterexample with `M ≥ 25`. -/
theorem band_minus_blocker {q : ℕ} (hM : 25 ≤ ce.M) (hq : q.Prime) (hb : InBand ce.M q)
    (hp : (2 * q - 1).Prime) : False := by
  obtain ⟨hq3, hM3, hfit⟩ := band_hypotheses hM hb
  exact ce.minus_sophie_blocker hq hq3 hp (by omega) (by omega) hM3

end Gap2CE

/-! ## The surviving analytic interface

Everything above is finite and kernel-checked.  The single remaining input is the
*existence* of a Sophie-Germain-type prime in the fixed band; it is stated here as an
explicit hypothesis (never as an axiom), so that the compiler below is a genuine
conditional theorem. -/

/-- **Sophie band supply** (the open analytic input): for every `M ≥ Mmin` there is a prime
`q` in the fixed band `(7/10)⌊M/2⌋ < q < (24/25)⌊M/2⌋` such that `2q + 1` or `2q - 1` is
prime. -/
def SophieBandSupply (Mmin : ℕ) : Prop :=
  ∀ M : ℕ, Mmin ≤ M → ∃ q : ℕ, q.Prime ∧ InBand M q ∧ ((2 * q + 1).Prime ∨ (2 * q - 1).Prime)

/-- **Conditional compiler.**  Granted the band supply from `Mmin ≥ 25` on, no gap-`≤2`
counterexample with `M ≥ Mmin` exists.  (The hypothesis is an assumption of the theorem, not
an axiom of the development.) -/
theorem no_Gap2CE_of_sophieBandSupply {Mmin : ℕ} (hMmin : 25 ≤ Mmin)
    (hsupply : SophieBandSupply Mmin) (ce : Gap2CE) (hM : Mmin ≤ ce.M) : False := by
  obtain ⟨q, hq, hb, hcase⟩ := hsupply ce.M hM
  rcases hcase with hp | hp
  · exact ce.band_plus_blocker (by omega) hq hb hp
  · exact ce.band_minus_blocker (by omega) hq hb hp

end Erdos287
