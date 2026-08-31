import Mathlib
import RequestProject.CurrentProgramme.Erdos287A0C0SourceLift

/-!
# Raw → reduced projective pair — Erdős #287 (append-only)

This module is **append-only** and sits strictly after `Erdos287A0C0SourceLift`.  All results
are unconditional integer algebra.

Contents.

* §1  **Raw and reduced pairs.**  `Praw = k b · A0row`, `Rraw = d₂ · C0 · u u'`, the common row
  factor `F = b u'`, and the reduced pair
  `Pnat = 2 s k Δ₀ e' r₁' r₂' z' b' ℓ₀'`, `Rnat = 2 s' d₂ Δ₀' e r₁ r₂ z r m`.
* §2  **Factorisation.**  `Praw = F · Pnat` and `Rraw = F · Rnat`, unconditionally, together
  with `F ≠ 0` derived from the positivity slots of the row (the cancellation below never
  assumes `F ≠ 0` silently).
* §3  **Projective collision equivalence.**  For two rows with *different* row factors
  `F₁, F₂`, both nonzero, `Praw₁ Rraw₂ = Praw₂ Rraw₁ ↔ Pnat₁ Rnat₂ = Pnat₂ Rnat₁`.  The proof
  is integral-domain cancellation of `F₁F₂`; no division is used, and no relation between the
  two rows (`b₁ = b₂`, `u₁' = u₂'`, `F₁ = F₂`, …) is assumed.
* §4  **Gauge-scaling algebra.**  The same cancellation stated abstractly: rowwise rescaling by
  nonzero `g₁, g₂` preserves projective collision.  This is an algebraic sanity lemma, *not* a
  claim that arbitrary gauge transformations are physical.
* §5  **Fixed factorisation depth.**  The purely arithmetic record that `Pnat` and `Rnat` each
  carry eight slots, and the derived integer `(8+8)^2 - 2 = 254`.  No analytic divisor-moment
  estimate is stated or assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace ReducedProjective

open Erdos287.SourceLift

/-! ## §1  Raw and reduced projective pairs -/

variable (R : SourceRow)

/-- Raw projective numerator `Praw = k b · A0row`. -/
def Praw : ℤ := (R.k : ℤ) * (R.b : ℤ) * R.A0row

/-- Raw projective denominator `Rraw = d₂ · C0 · u u'`. -/
def Rraw : ℤ := (R.d2 : ℤ) * R.C0 * R.u * R.u'

/-- Common row factor `F = b u'`. -/
def F : ℤ := (R.b : ℤ) * R.u'

/-- Reduced numerator `Pnat = 2 s k Δ₀ e' r₁' r₂' z' b' ℓ₀'`. -/
def Pnat : ℤ :=
  2 * R.s * (R.k : ℤ) * R.Delta0 * (R.e' : ℤ) * (R.r1' : ℤ) * (R.r2' : ℤ) * (R.z' : ℤ)
    * (R.b' : ℤ) * (R.ell0' : ℤ)

/-- Reduced denominator `Rnat = 2 s' d₂ Δ₀' e r₁ r₂ z r m`. -/
def Rnat : ℤ :=
  2 * R.s' * (R.d2 : ℤ) * R.Delta0' * (R.e : ℤ) * (R.r1 : ℤ) * (R.r2 : ℤ) * (R.z : ℤ)
    * (R.r : ℤ) * (R.m : ℤ)

/-! ## §2  Factorisation of the raw pair -/

/-- **`erdos287_F_pos`.**  `LEAN_PROVED`.  The common row factor is positive, hence nonzero;
this is what licenses the cancellation in §3. -/
theorem erdos287_F_pos : 0 < F R :=
  mul_pos (SourceRow.erdos287_b_pos R) (SourceRow.erdos287_u'_pos R)

/-- **`erdos287_F_ne_zero`.**  `LEAN_PROVED`.  `F ≠ 0`. -/
theorem erdos287_F_ne_zero : F R ≠ 0 := ne_of_gt (erdos287_F_pos R)

/-- **`erdos287_Praw_factor`.**  `LEAN_PROVED`.  `Praw = F · Pnat`, unconditionally. -/
theorem erdos287_Praw_factor : Praw R = F R * Pnat R := by
  simp only [Praw, Pnat, F, SourceRow.A0row, SourceRow.Gamma2, SourceRow.beta2]
  ring

/-- **`erdos287_Rraw_factor`.**  `LEAN_PROVED`.  `Rraw = F · Rnat`, unconditionally. -/
theorem erdos287_Rraw_factor : Rraw R = F R * Rnat R := by
  simp only [Rraw, Rnat, F, SourceRow.C0, SourceRow.Gamma1, SourceRow.u]
  ring

/-! ## §3  Projective collision equivalence

The abstract cancellation lemma comes first; it is stated in an arbitrary integral domain and
uses `mul_left_cancel₀`, never division. -/

/-- **`projective_collision_iff_of_row_factor`.**  `LEAN_PROVED`.  Abstract raw/reduced
equivalence: if `Praw i = F i * Pnat i` and `Rraw i = F i * Rnat i` for `i = 1, 2` with
`F₁ ≠ 0 ≠ F₂` (the two row factors need not be equal), then the raw and reduced projective
collisions are equivalent. -/
theorem projective_collision_iff_of_row_factor {α : Type*} [CommRing α] [IsDomain α]
    {F1 F2 Praw1 Rraw1 Praw2 Rraw2 Pnat1 Rnat1 Pnat2 Rnat2 : α}
    (hF1 : F1 ≠ 0) (hF2 : F2 ≠ 0)
    (hP1 : Praw1 = F1 * Pnat1) (hR1 : Rraw1 = F1 * Rnat1)
    (hP2 : Praw2 = F2 * Pnat2) (hR2 : Rraw2 = F2 * Rnat2) :
    Praw1 * Rraw2 = Praw2 * Rraw1 ↔ Pnat1 * Rnat2 = Pnat2 * Rnat1 := by
  have hFF : F1 * F2 ≠ 0 := mul_ne_zero hF1 hF2
  constructor
  · intro h
    refine mul_left_cancel₀ hFF ?_
    calc (F1 * F2) * (Pnat1 * Rnat2)
        = Praw1 * Rraw2 := by rw [hP1, hR2]; ring
      _ = Praw2 * Rraw1 := h
      _ = (F1 * F2) * (Pnat2 * Rnat1) := by rw [hP2, hR1]; ring
  · intro h
    calc Praw1 * Rraw2 = (F1 * F2) * (Pnat1 * Rnat2) := by rw [hP1, hR2]; ring
      _ = (F1 * F2) * (Pnat2 * Rnat1) := by rw [h]
      _ = Praw2 * Rraw1 := by rw [hP2, hR1]; ring

/-- **`erdos287_raw_projective_collision_iff_reduced`.**  `LEAN_PROVED`.  For two arbitrary
source rows `R₁`, `R₂` — with no assumption whatsoever relating their slots, in particular not
`b₁ = b₂`, not `u₁' = u₂'` and not `F₁ = F₂` — the raw projective collision is equivalent to
the reduced projective collision. -/
theorem erdos287_raw_projective_collision_iff_reduced (R1 R2 : SourceRow) :
    Praw R1 * Rraw R2 = Praw R2 * Rraw R1 ↔ Pnat R1 * Rnat R2 = Pnat R2 * Rnat R1 :=
  projective_collision_iff_of_row_factor
    (erdos287_F_ne_zero R1) (erdos287_F_ne_zero R2)
    (erdos287_Praw_factor R1) (erdos287_Rraw_factor R1)
    (erdos287_Praw_factor R2) (erdos287_Rraw_factor R2)

/-! ## §4  Gauge-scaling algebra -/

/-- **`projective_collision_invariant_under_row_scaling`.**  `LEAN_PROVED`.  Algebraic sanity
lemma: rescaling both entries of each row by a nonzero rowwise factor does not change the
projective collision relation.  This asserts nothing about which rescalings are physical. -/
theorem projective_collision_invariant_under_row_scaling {α : Type*} [CommRing α] [IsDomain α]
    {g1 g2 P1 R1 P2 R2 : α} (hg1 : g1 ≠ 0) (hg2 : g2 ≠ 0) :
    (g1 * P1) * (g2 * R2) = (g2 * P2) * (g1 * R1) ↔ P1 * R2 = P2 * R1 :=
  projective_collision_iff_of_row_factor hg1 hg2 rfl rfl rfl rfl

/-! ## §5  Fixed factorisation depth — arithmetic record only

The two lists below are the literal slot lists of `Pnat` and `Rnat`; the identities show that
the definitions really are the product of `2 * sign` with those eight slots.  Only the depth is
recorded: **no** divisor-moment or analytic estimate is stated here. -/

/-- The eight numerator slots of `Pnat`. -/
def numeratorSlots : List ℤ :=
  [(R.k : ℤ), R.Delta0, (R.e' : ℤ), (R.r1' : ℤ), (R.r2' : ℤ), (R.z' : ℤ), (R.b' : ℤ),
    (R.ell0' : ℤ)]

/-- The eight denominator slots of `Rnat`. -/
def denominatorSlots : List ℤ :=
  [(R.d2 : ℤ), R.Delta0', (R.e : ℤ), (R.r1 : ℤ), (R.r2 : ℤ), (R.z : ℤ), (R.r : ℤ), (R.m : ℤ)]

/-- **`erdos287_Pnat_slot_product`.**  `LEAN_PROVED`.  `Pnat = 2 s · ∏ (numerator slots)`. -/
theorem erdos287_Pnat_slot_product : Pnat R = 2 * R.s * (numeratorSlots R).prod := by
  simp only [Pnat, numeratorSlots, List.prod_cons, List.prod_nil]
  ring

/-- **`erdos287_Rnat_slot_product`.**  `LEAN_PROVED`.  `Rnat = 2 s' · ∏ (denominator slots)`. -/
theorem erdos287_Rnat_slot_product : Rnat R = 2 * R.s' * (denominatorSlots R).prod := by
  simp only [Rnat, denominatorSlots, List.prod_cons, List.prod_nil]
  ring

/-- Depth of the reduced numerator: eight slots. -/
def reducedNumeratorDepth : ℕ := 8

/-- Depth of the reduced denominator: eight slots. -/
def reducedDenominatorDepth : ℕ := 8

/-- **`erdos287_numerator_depth`.**  `LEAN_PROVED`.  The numerator slot list has length
`reducedNumeratorDepth = 8`. -/
theorem erdos287_numerator_depth : (numeratorSlots R).length = reducedNumeratorDepth := rfl

/-- **`erdos287_denominator_depth`.**  `LEAN_PROVED`.  The denominator slot list has length
`reducedDenominatorDepth = 8`. -/
theorem erdos287_denominator_depth : (denominatorSlots R).length = reducedDenominatorDepth := rfl

/-- The arithmetic exponent attached to the fixed depth pair `(8, 8)`, namely
`(8 + 8)^2 - 2`.  This is a *number*, recorded for bookkeeping; it is not asserted to be the
exponent of any analytic estimate. -/
def fixedDepthExponent : ℕ := (reducedNumeratorDepth + reducedDenominatorDepth) ^ 2 - 2

/-- **`erdos287_fixed_depth_exponent`.**  `LEAN_PROVED`.  `(8+8)^2 - 2 = 254`. -/
theorem erdos287_fixed_depth_exponent : fixedDepthExponent = 254 := by decide +kernel

/-! ## §6  Hostile check: the two row factors really may differ

The collision equivalence of §3 quantifies over two independent rows.  The witness below shows
that the family of rows does contain pairs with `F₁ ≠ F₂`, so the equivalence is not secretly a
statement about a single common factor. -/

/-- A sample row with prescribed `b`, `r'`, `m'` and all other slots equal to `1` (signed slots
included).  Used only as a witness. -/
def sampleRow (bb rr' mm' : ℕ) (hbb : 0 < bb) (hrr' : 0 < rr') (hmm' : 0 < mm') : SourceRow where
  s := 1
  s' := 1
  Delta0 := 1
  Delta0' := 1
  e := 1
  e' := 1
  r1 := 1
  r2 := 1
  r1' := 1
  r2' := 1
  z := 1
  z' := 1
  b := bb
  b' := 1
  r := 1
  m := 1
  r' := rr'
  m' := mm'
  ell0' := 1
  d2 := 1
  k := 1
  hb := hbb
  hb' := Nat.one_pos
  hr := Nat.one_pos
  hm := Nat.one_pos
  hr' := hrr'
  hm' := hmm'
  hell0' := Nat.one_pos

/-- **`row_factors_may_differ`.**  `LEAN_PROVED`.  There exist two rows whose common factors
`F` differ, so §3 is genuinely a two-factor statement. -/
theorem row_factors_may_differ : ∃ R1 R2 : SourceRow, F R1 ≠ F R2 := by
  refine ⟨sampleRow 1 1 1 Nat.one_pos Nat.one_pos Nat.one_pos,
    sampleRow 2 1 1 (by norm_num) Nat.one_pos Nat.one_pos, ?_⟩
  simp [F, SourceRow.u', sampleRow]

end ReducedProjective
end Erdos287
