import Mathlib
import RequestProject.Erdos287.HighConductorVariance3221
import RequestProject.Erdos287.FiveBoxCharacterFactorization3221
import RequestProject.Erdos287.OuterTwoPrimeBlock3221
import RequestProject.CurrentProgramme.Erdos287CenteredQCellPhysical

/-!
# Semantic repair layer §16–§19 — the literal `2 + 5` split, the inverse-sampled `3221`
dictionary, the five-box dictionary and the outer two-prime finite norms

All statements here are **exact finite algebra**; no analytic estimate is proved or assumed.

* §1 the literal `2 + 5` split: `m = p_{i₁} p_{i₂}`, `w = ∏_{other five}`, `m·w = P`;
* §2 `SP2-SUPERSQRT-TO-INVERSESAMPLED3221-PHYSICAL-DICTIONARY45`: `q ∣ 2 m w + s` iff
  `w ≡ −s(2m)⁻¹ (mod q)`, obtained by literally reusing the banked
  `InverseSampledHighCond3221Data.samplePoint_iff_affineSampled`;
* §3 the five-box dictionary: the seven-slot physical character product is exactly the
  labelled outer pair block times the labelled five-box transform;
* §4 the outer two-prime finite `L¹`/`L∞`/`L²` norms of the physical coefficient, with the
  external prime-density normalisation explicitly isolated (still uninhabited).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace Supersqrt3221

open Finset
open Erdos287.SP2Source
open Erdos287.StrictCellSingleton
open Erdos287.WeightedSP2
open Erdos287.CenteredQCell
open Erdos287.HighCond3221
open Erdos287.V20FiveBox
open Erdos287.V21Outer

/-! ## §1.  The literal `2 + 5` split -/

/-- The two chosen physical labels of the outer block. -/
def outerLabels : Finset (Fin 7) := ({1, 2} : Finset (Fin 7))

/-- The five remaining labelled slots. -/
def innerLabels : Finset (Fin 7) := ({0, 3, 4, 5, 6} : Finset (Fin 7))

theorem outerLabels_eq_outerBoxes : outerLabels = outerBoxes := rfl

theorem innerLabels_eq_innerBoxes : innerLabels = innerBoxes := by decide

theorem outer_inner_disjoint : Disjoint outerLabels innerLabels := by decide

theorem outer_union_inner : outerLabels ∪ innerLabels = Finset.univ := by decide

/-- The outer two-prime block `m = p_{i₁} p_{i₂}`. -/
def outerPart (v : Fin 7 → ℕ) : ℕ := v 1 * v 2

/-- The five-prime complement `w = ∏_{j ∈ innerLabels} p_j`. -/
def innerPart (v : Fin 7 → ℕ) : ℕ := ∏ j ∈ innerLabels, v j

/-- **`outer_mul_inner_eq_pushforward`.**  `LEAN_PROVED`.

The literal `2 + 5` factorisation `m · w = P`. -/
theorem outer_mul_inner_eq_pushforward (v : Fin 7 → ℕ) :
    outerPart v * innerPart v = pushforward v := by
  rw [outerPart, innerPart, pushforward, innerLabels, Fin.prod_univ_seven]
  simp [Finset.prod_insert, Finset.mem_insert]
  ring

/-! ## §2.  The inverse-sampled `3221` physical dictionary -/

/-- **`supersqrt_inverseSampled_dictionary`.**  `LEAN_PROVED` (literal reuse).

`SP2-SUPERSQRT-TO-INVERSESAMPLED3221-PHYSICAL-DICTIONARY45`:

```
    q ∣ 2·m·w + s   ↔   w ≡ −s(2m)⁻¹  (mod q),
```

under the coprimality hypotheses already carried by the banked inverse-sampled datum.  The
proof is literally `samplePoint_iff_affineSampled`, not a re-derivation. -/
theorem supersqrt_inverseSampled_dictionary (D : InverseSampledHighCond3221Data)
    {q m : ℕ} (hq : q ∈ D.Qbox) (hm : m ∈ D.Mbox) (w : ℤ) :
    ((q : ℤ) ∣ 2 * (m : ℤ) * w + D.sign) ↔ ((w : ZMod q) = D.samplePoint q m) := by
  rw [D.samplePoint_iff_affineSampled hq hm w, Erdos287.PrePoisson3221.AffineSampled,
    show 2 * ((m : ℤ) * w) = 2 * (m : ℤ) * w by ring]

/-- The dictionary in the `m·w = P` form of the `2 + 5` split. -/
theorem supersqrt_split_dictionary (D : InverseSampledHighCond3221Data)
    {q : ℕ} (hq : q ∈ D.Qbox) {v : Fin 7 → ℕ} (hm : outerPart v ∈ D.Mbox) :
    ((q : ℤ) ∣ 2 * (pushforward v : ℤ) + D.sign)
      ↔ (((innerPart v : ℕ) : ℤ) : ZMod q) = D.samplePoint q (outerPart v) := by
  have hsplit : ((pushforward v : ℕ) : ℤ) = (outerPart v : ℤ) * (innerPart v : ℤ) := by
    rw [← outer_mul_inner_eq_pushforward v]; push_cast; ring
  rw [hsplit, show 2 * ((outerPart v : ℤ) * (innerPart v : ℤ))
      = 2 * (outerPart v : ℤ) * (innerPart v : ℤ) by ring]
  exact supersqrt_inverseSampled_dictionary D hq hm _

/-! ## §3.  The five-box dictionary -/

/-- The physical slot transform is literally the banked labelled box transform. -/
theorem slotTransform_eq_blockSum (C : SP2FixedCertificateData) (S : PhysicalSlotData)
    (q : ℕ) (chi : DirichletCharacter ℂ q) (j : Fin 7) :
    slotTransform C S q chi j = blockSum q (C.lam j) (omegaPhysical C S j) chi := rfl

/-- **`sevenSlot_eq_outerPair_mul_fiveBox`.**  `LEAN_PROVED`.

The `2 + 5` dictionary at the level of character transforms: the seven-slot physical
product is exactly the labelled outer pair block times the labelled five-box transform, with
each of the five inner slots mapped to its own source box and physical weight. -/
theorem sevenSlot_eq_outerPair_mul_fiveBox (C : SP2FixedCertificateData)
    (S : PhysicalSlotData) (q : ℕ) (chi : DirichletCharacter ℂ q) :
    (∏ j, slotTransform C S q chi j)
      = pairBlockSum q (C.lam 1) (C.lam 2) (omegaPhysical C S 1) (omegaPhysical C S 2) chi *
        fiveBoxCHat q (C.lam 0) (C.lam 3) (C.lam 4) (C.lam 5) (C.lam 6)
          (omegaPhysical C S 0) (omegaPhysical C S 3) (omegaPhysical C S 4)
          (omegaPhysical C S 5) (omegaPhysical C S 6) chi := by
  rw [pairBlockSum_eq_mul, fiveBox_characterTransform_eq_prod_five, Fin.prod_univ_seven]
  simp only [slotTransform_eq_blockSum]
  ring

/-- **`physical_sevenSlot_source_factorisation`.**  `LEAN_PROVED`.

The full chain: the direct physical cell sum, transformed by `χ`, equals the outer pair
block times the five-box transform. -/
theorem physical_sevenSlot_source_factorisation (C : SP2FixedCertificateData)
    (S : PhysicalSlotData) (q : ℕ) (chi : DirichletCharacter ℂ q) :
    ∑ v ∈ cellVectors C,
        (∏ j, omegaPhysical C S j (v j)) * chi ((pushforward v : ℕ) : ZMod q)
      = pairBlockSum q (C.lam 1) (C.lam 2) (omegaPhysical C S 1) (omegaPhysical C S 2) chi *
        fiveBoxCHat q (C.lam 0) (C.lam 3) (C.lam 4) (C.lam 5) (C.lam 6)
          (omegaPhysical C S 0) (omegaPhysical C S 3) (omegaPhysical C S 4)
          (omegaPhysical C S 5) (omegaPhysical C S 6) chi := by
  rw [sevenSlot_character_product C S q chi, sevenSlot_eq_outerPair_mul_fiveBox]

/-! ## §4.  The outer two-prime block: finite norms -/

/-- The physical outer two-prime coefficient, built directly from the two chosen slot
weights. -/
noncomputable def alphaPhysical (C : SP2FixedCertificateData) (S : PhysicalSlotData)
    (m : ℕ) : ℂ :=
  alphaOuter (C.lam 1) (C.lam 2) (omegaPhysical C S 1) (omegaPhysical C S 2) m

/-- **`alphaOuter_sup_le`.**  `LEAN_PROVED_FINITE`.

The literal `L^∞` bound from the pointwise normalisation of the slot weights. -/
theorem alphaOuter_sup_le (P1 P2 : Finset ℕ) (w1 w2 : ℕ → ℂ)
    (h1 : ∀ p, ‖w1 p‖ ≤ 1) (h2 : ∀ p, ‖w2 p‖ ≤ 1) (m : ℕ) :
    ‖alphaOuter P1 P2 w1 w2 m‖ ≤ (P1.card : ℝ) * (P2.card : ℝ) := by
  classical
  refine le_trans (norm_sum_le _ _) ?_
  have hinner : ∀ p ∈ P1,
      ‖∑ r ∈ P2, (if p * r = m then w1 p * w2 r else 0)‖ ≤ (P2.card : ℝ) := by
    intro p _
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ r ∈ P2, ‖(if p * r = m then w1 p * w2 r else 0)‖ ≤ 1 := by
      intro r _
      by_cases h : p * r = m
      · rw [if_pos h, norm_mul]
        exact le_trans (mul_le_mul (h1 p) (h2 r) (norm_nonneg _) zero_le_one)
          (by norm_num)
      · rw [if_neg h, norm_zero]; norm_num
    refine le_trans (Finset.sum_le_sum hterm) ?_
    simp
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-- **`alphaPhysical_sup_le`.**  `LEAN_PROVED_FINITE`. -/
theorem alphaPhysical_sup_le (C : SP2FixedCertificateData) (S : PhysicalSlotData) (m : ℕ) :
    ‖alphaPhysical C S m‖ ≤ ((C.lam 1).card : ℝ) * ((C.lam 2).card : ℝ) :=
  alphaOuter_sup_le _ _ _ _ (fun p => norm_omegaPhysical_le_one C S 1 p)
    (fun p => norm_omegaPhysical_le_one C S 2 p) m

/-- **`alphaPhysical_l1_le`.**  `LEAN_PROVED_FINITE`. -/
theorem alphaPhysical_l1_le (C : SP2FixedCertificateData) (S : PhysicalSlotData)
    (Mbox : Finset ℕ) :
    ∑ m ∈ Mbox, ‖alphaPhysical C S m‖
      ≤ ((C.lam 1).card : ℝ) * ((C.lam 2).card : ℝ) := by
  refine le_trans (alphaOuter_l1_le (C.lam 1) (C.lam 2) Mbox _ _) ?_
  have h1 : ∑ p ∈ C.lam 1, ‖omegaPhysical C S 1 p‖ ≤ ((C.lam 1).card : ℝ) := by
    refine le_trans (Finset.sum_le_sum (fun p _ => norm_omegaPhysical_le_one C S 1 p)) ?_
    simp
  have h2 : ∑ r ∈ C.lam 2, ‖omegaPhysical C S 2 r‖ ≤ ((C.lam 2).card : ℝ) := by
    refine le_trans (Finset.sum_le_sum (fun p _ => norm_omegaPhysical_le_one C S 2 p)) ?_
    simp
  exact mul_le_mul h1 h2 (Finset.sum_nonneg fun _ _ => norm_nonneg _) (by positivity)

/-- **`alphaPhysical_l2_le`.**  `LEAN_PROVED_FINITE`.

The deterministic finite `L²` bound of the physical outer coefficient.  It is *purely*
finite: no prime count and no `X`-dependence enter. -/
theorem alphaPhysical_l2_le (C : SP2FixedCertificateData) (S : PhysicalSlotData)
    (Mbox : Finset ℕ) :
    ∑ m ∈ Mbox, ‖alphaPhysical C S m‖ ^ 2
      ≤ (((C.lam 1).card : ℝ) * ((C.lam 2).card : ℝ)) *
        (((C.lam 1).card : ℝ) * ((C.lam 2).card : ℝ)) :=
  outerL2_of_sup_and_l1 Mbox _ (by positivity)
    (fun m _ => alphaPhysical_sup_le C S m) (alphaPhysical_l1_le C S Mbox)

/-- **`outerL2_physical_needs_prime_density`.**  `LEAN_PROVED` (isolation statement).

The finite bound above is *not* the physical `L²` normalisation `≪ M/log²X`: the banked
interface `OuterTwoPrimeL2Normalization3221Input` is refuted at explicit data, so it carries
genuine external prime-density content and stays uninhabited.  What the finite algebra
supplies is exactly the budget hypothesis of `outerL2_input_of_sup_and_l1`. -/
theorem outerL2_physical_needs_prime_density
    (C : SP2FixedCertificateData) (S : PhysicalSlotData) (Mbox : Finset ℕ)
    {M X Couter : ℝ}
    (hbudget : (((C.lam 1).card : ℝ) * ((C.lam 2).card : ℝ)) *
        (((C.lam 1).card : ℝ) * ((C.lam 2).card : ℝ))
        ≤ Couter * M / (Real.log X) ^ 2) :
    OuterTwoPrimeL2Normalization3221Input (C.lam 1) (C.lam 2) Mbox
      (omegaPhysical C S 1) (omegaPhysical C S 2) M X Couter :=
  outerL2_input_of_sup_and_l1 _ _ _ _ _ (by positivity)
    (fun m _ => alphaPhysical_sup_le C S m) (alphaPhysical_l1_le C S Mbox) hbudget

end Supersqrt3221
end Erdos287
