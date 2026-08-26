import Mathlib
import RequestProject.TrustedBank.FixedAffine.UnitTransport

/-!
# Trusted bank — Bank C: abstract SB fixed-unit portability

This file contains **only** the source-independent statement:  multiplying two families
of values by fixed units does not change their simultaneous zero set, nor its
cardinality, nor the weighted count over it.

It deliberately does *not* say anything about any particular analytic source; in
particular it does **not** state that "SB-ν for twins implies SB-ν for all fixed affine
sources".  That implication needs a source-glue theorem (see
`RequestProject/Challenges/AffineSourceGlue.lean`) establishing that the affine source
really does change the fibre functions by exactly such unit multiples.
-/

open scoped BigOperators

namespace TrustedBank
namespace ZeroSetTransport

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {R₁ R₂ : Type*} [MonoidWithZero R₁] [MonoidWithZero R₂]
variable (F₁ : I → R₁) (F₂ : I → R₂) (κ₁ : R₁ˣ) (κ₂ : R₂ˣ)

/-- The unit-twisted family `F' i = κ * F i`. -/
def twist {R : Type*} [MonoidWithZero R] (κ : Rˣ) (F : I → R) : I → R :=
  fun i => (κ : R) * F i

omit [Fintype I] [DecidableEq I] in
/-- **Bank C.1 — pointwise vanishing is unchanged by a fixed unit.** -/
theorem twist_eq_zero_iff {R : Type*} [MonoidWithZero R] (κ : Rˣ) (F : I → R) (i : I) :
    twist κ F i = 0 ↔ F i = 0 :=
  UnitTransport.unitMul_eq_zero_iff κ (F i)

/-- The simultaneous zero set of two families. -/
def zeroSet [DecidablePred fun i => F₁ i = 0 ∧ F₂ i = 0] : Finset I :=
  Finset.univ.filter (fun i => F₁ i = 0 ∧ F₂ i = 0)

omit [Fintype I] [DecidableEq I] in
/-- **Bank C.2 — the simultaneous zero sets coincide exactly.** -/
theorem twist_simultaneous_zero_iff (i : I) :
    (twist κ₁ F₁ i = 0 ∧ twist κ₂ F₂ i = 0) ↔ (F₁ i = 0 ∧ F₂ i = 0) := by
  rw [twist_eq_zero_iff, twist_eq_zero_iff]

omit [DecidableEq I] in
/-- **Bank C.3 — equality of the simultaneous zero sets as finite sets.** -/
theorem twist_zeroSet_eq
    [DecidablePred fun i => F₁ i = 0 ∧ F₂ i = 0]
    [DecidablePred fun i => twist κ₁ F₁ i = 0 ∧ twist κ₂ F₂ i = 0] :
    zeroSet (twist κ₁ F₁) (twist κ₂ F₂) = zeroSet F₁ F₂ := by
  ext i
  simp only [zeroSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact twist_simultaneous_zero_iff F₁ F₂ κ₁ κ₂ i

omit [DecidableEq I] in
/-- **Bank C.4 — equality of the fibre counts.** -/
theorem twist_zeroSet_card_eq
    [DecidablePred fun i => F₁ i = 0 ∧ F₂ i = 0]
    [DecidablePred fun i => twist κ₁ F₁ i = 0 ∧ twist κ₂ F₂ i = 0] :
    (zeroSet (twist κ₁ F₁) (twist κ₂ F₂)).card = (zeroSet F₁ F₂).card := by
  rw [twist_zeroSet_eq]

omit [DecidableEq I] in
/-- **Bank C.5 — the weighted count over the simultaneous zero set is unchanged**
(the weight function being literally the same function). -/
theorem twist_zeroSet_weighted_sum_eq {M : Type*} [AddCommMonoid M] (w : I → M)
    [DecidablePred fun i => F₁ i = 0 ∧ F₂ i = 0]
    [DecidablePred fun i => twist κ₁ F₁ i = 0 ∧ twist κ₂ F₂ i = 0] :
    ∑ i ∈ zeroSet (twist κ₁ F₁) (twist κ₂ F₂), w i = ∑ i ∈ zeroSet F₁ F₂, w i := by
  rw [twist_zeroSet_eq]

end ZeroSetTransport
end TrustedBank
