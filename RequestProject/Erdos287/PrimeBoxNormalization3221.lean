import Mathlib
import RequestProject.Erdos287.BadCharacterCount3221

/-!
# V21, Phase 4 — prime-box normalisation: the source audit, the interface, the phase lemma

`BALANCED7-PRIMEBOX-L1-NORMALIZATION45 : SOURCE_OPEN`

## Source audit (recorded honestly)

The repository was searched for a *physical* Balanced7 definition of the seven coefficient
slots `ω_i(p)`.  What exists is the **abstract** polarisation apparatus:

* `Erdos287.FactorialEulerPolarization.linForm / Fdiv / azForm / Fz7` and
  `factorialEulerPolarization_seven`, which take an arbitrary coefficient family
  `om : ℕ → Fin 7 → K` as *input*;
* `Erdos287.BalancedSevenPolarization.labelledPolynomial` and
  `coeff_balancedSeven_eq_perm_sum`, which extract the balanced monomial coefficient of an
  arbitrary labelled linear form.

There is **no** declaration in the repository fixing a physical `ω_i(p)` (no
`Λ(p)`-normalisation, no `log p · ω_i(p)` convention, no normalised prime indicator, and no
prime-box support statement).  Consequently:

* the physical pointwise law `|ω_i(p)| ≤ C` is **not** available, and in particular it is
  *not* inferred from the factorial coefficient-extraction theorem — that inference is
  exactly the circular provenance this V21 layer repairs;
* the prime-box `L¹` interface below is **left uninhabited** and the programme label stays
  `SOURCE_OPEN`.

## What *is* proved here

* `primeBoxL1_of_pointwise_and_count` — the conditional compiler: a pointwise coefficient
  law together with a prime-box **cardinality** input gives the `L¹` bound.  The
  cardinality input is a separate (external) datum; no prime-counting theorem is proved.
* `phaseUniformBound_implies_sum_abs_omega_le_seven` and
  `phaseUniformBound_implies_each_abs_omega_le_seven` — the abstract finite phase-alignment
  lemma.  Its *antecedent* is a physical statement about independent phases and is **not**
  claimed here (`phaseUniformBound_not_automatic`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace Erdos287
namespace V21PrimeBox

/-! ## §1. The physical prime-box datum -/

/-- Pure data for the seven physical coefficient slots and their prime boxes.  (No field is
a free `Prop`; the analytic/source content is in the interface below.) -/
structure PrimeBoxData where
  /-- The seven coefficient slots `ω_i(·)`. -/
  omega : Fin 7 → ℕ → ℂ
  /-- The seven physical prime boxes. -/
  box : Fin 7 → Finset ℕ

/-- **`BalancedSevenPrimeBoxNormalization3221`** — `SOURCE_OPEN / UNINHABITED`.

The literal prime-box normalisation package: prime support, the pointwise coefficient law
with an explicit constant, and the `L¹` bound `∑_{p ∈ box_i} |ω_i(p)| ≤ C₁ · Y / log Y`.

**No inhabitant is constructed in this repository**, because the physical `ω_i` are not
defined in the source; see the audit in the module docstring. -/
structure BalancedSevenPrimeBoxNormalization3221 (Dat : PrimeBoxData) (Cptw C1 Y : ℝ) :
    Prop where
  /-- Each box is literally supported on primes. -/
  prime_support : ∀ i : Fin 7, ∀ p ∈ Dat.box i, Nat.Prime p
  /-- The pointwise coefficient law. -/
  pointwise_bound : ∀ (i : Fin 7) (p : ℕ), ‖Dat.omega i p‖ ≤ Cptw
  /-- The prime-box `L¹` bound. -/
  l1_bound : ∀ i : Fin 7, ∑ p ∈ Dat.box i, ‖Dat.omega i p‖ ≤ C1 * (Y / Real.log Y)

/-- **`primeBoxNormalization_not_automatic`.**  `LEAN_PROVED`.

The prime-box normalisation is a genuine restriction: explicit data refute it. -/
theorem primeBoxNormalization_not_automatic :
    ∃ (Dat : PrimeBoxData) (Cptw C1 Y : ℝ),
      ¬ BalancedSevenPrimeBoxNormalization3221 Dat Cptw C1 Y := by
  refine ⟨⟨fun _ _ => 0, fun _ => ∅⟩, -1, 0, 1, ?_⟩
  intro h
  have h1 := h.pointwise_bound 0 0
  simp only [norm_zero] at h1
  linarith

/-! ## §2. The conditional `L¹` compiler -/

/-- **`primeBoxL1_of_pointwise_and_count`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

Pointwise coefficient law **+** prime-box cardinality input ⇒ prime-box `L¹` bound.

The three ingredients are kept strictly separate:

* **A.** the pointwise `1`-bounded coefficient law (`hptw`);
* **B.** the prime support (recorded in the datum, not used by the inequality);
* **C.** the prime-box cardinality (`hcard`), an *external* prime-counting input.

No prime number theory is proved or assumed inside this theorem. -/
theorem primeBoxL1_of_pointwise_and_count {om : ℕ → ℂ} {P : Finset ℕ} {Cptw K : ℝ}
    (hC : 0 ≤ Cptw) (hptw : ∀ p ∈ P, ‖om p‖ ≤ Cptw) (hcard : (P.card : ℝ) ≤ K) :
    ∑ p ∈ P, ‖om p‖ ≤ Cptw * K := by
  have h1 : ∑ p ∈ P, ‖om p‖ ≤ ∑ _p ∈ P, Cptw := Finset.sum_le_sum hptw
  have h2 : ∑ _p ∈ P, (Cptw : ℝ) = (P.card : ℝ) * Cptw := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h3 : (P.card : ℝ) * Cptw ≤ K * Cptw := by
    exact mul_le_mul_of_nonneg_right hcard hC
  calc ∑ p ∈ P, ‖om p‖ ≤ (P.card : ℝ) * Cptw := by rw [← h2]; exact h1
    _ ≤ K * Cptw := h3
    _ = Cptw * K := by ring

/-! ## §3. The phase-alignment lemma (abstract, finite, conditional) -/

/-- The aligning phase vector: `z_i = conj(ω_i)/|ω_i|` off the zero set. -/
noncomputable def aligningPhase (om : Fin 7 → ℂ) (i : Fin 7) : ℂ :=
  if om i = 0 then 1 else (starRingEnd ℂ) (om i) / (‖om i‖ : ℂ)

theorem aligningPhase_norm (om : Fin 7 → ℂ) (i : Fin 7) : ‖aligningPhase om i‖ = 1 := by
  unfold aligningPhase
  by_cases h : om i = 0
  · rw [if_pos h, norm_one]
  · rw [if_neg h, norm_div, RCLike.norm_conj, Complex.norm_real, norm_norm,
      div_self (by simpa using h)]

theorem aligningPhase_mul (om : Fin 7 → ℂ) (i : Fin 7) :
    aligningPhase om i * om i = (‖om i‖ : ℂ) := by
  unfold aligningPhase
  by_cases h : om i = 0
  · rw [if_pos h, h]; simp
  · have hn : (‖om i‖ : ℂ) ≠ 0 := by simpa using h
    rw [if_neg h, div_mul_eq_mul_div, Complex.conj_mul', sq, mul_div_assoc,
      div_self hn, mul_one]

/-- **`phaseUniformBound_implies_sum_abs_omega_le_seven`.**  `LEAN_PROVED`.

If the normalised phase average is bounded by `1` for **every** unit phase vector, then
`∑_i |ω_i| ≤ 7`.  This is the abstract implication only: its antecedent is a physical
statement and is not asserted here. -/
theorem phaseUniformBound_implies_sum_abs_omega_le_seven (om : Fin 7 → ℂ)
    (h : ∀ z : Fin 7 → ℂ, (∀ i, ‖z i‖ = 1) →
      ‖(1 / 7 : ℂ) * ∑ i : Fin 7, z i * om i‖ ≤ 1) :
    ∑ i : Fin 7, ‖om i‖ ≤ 7 := by
  have hz := h (aligningPhase om) (aligningPhase_norm om)
  have hsum : ∑ i : Fin 7, aligningPhase om i * om i = ((∑ i : Fin 7, ‖om i‖ : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun i _ => aligningPhase_mul om i
  rw [hsum, norm_mul] at hz
  have hnorm : ‖((∑ i : Fin 7, ‖om i‖ : ℝ) : ℂ)‖ = ∑ i : Fin 7, ‖om i‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (Finset.sum_nonneg fun i _ => norm_nonneg _)]
  rw [hnorm] at hz
  have h17 : ‖(1 / 7 : ℂ)‖ = 1 / 7 := by
    rw [norm_div, norm_one]
    norm_num
  rw [h17] at hz
  linarith

/-- **`phaseUniformBound_implies_each_abs_omega_le_seven`.**  `LEAN_PROVED`. -/
theorem phaseUniformBound_implies_each_abs_omega_le_seven (om : Fin 7 → ℂ)
    (h : ∀ z : Fin 7 → ℂ, (∀ i, ‖z i‖ = 1) →
      ‖(1 / 7 : ℂ) * ∑ i : Fin 7, z i * om i‖ ≤ 1) (j : Fin 7) :
    ‖om j‖ ≤ 7 := by
  have hsum := phaseUniformBound_implies_sum_abs_omega_le_seven om h
  have hle : ‖om j‖ ≤ ∑ i : Fin 7, ‖om i‖ :=
    Finset.single_le_sum (f := fun i => ‖om i‖) (fun i _ => norm_nonneg _) (Finset.mem_univ j)
  linarith

/-- **`phaseUniformBound_not_automatic`.**  `LEAN_PROVED` (anti-circularity).

The phase antecedent is a genuine physical restriction: it fails for explicit data, so the
lemma above never manufactures its own hypothesis. -/
theorem phaseUniformBound_not_automatic :
    ∃ om : Fin 7 → ℂ, ¬ (∀ z : Fin 7 → ℂ, (∀ i, ‖z i‖ = 1) →
      ‖(1 / 7 : ℂ) * ∑ i : Fin 7, z i * om i‖ ≤ 1) := by
  refine ⟨fun _ => 100, ?_⟩
  intro h
  have hsum := phaseUniformBound_implies_sum_abs_omega_le_seven _ h
  norm_num at hsum

end V21PrimeBox
end Erdos287
