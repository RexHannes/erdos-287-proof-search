import Mathlib

/-!
# Erdős #287 — September-4 signed-floor bank, §1: the physical weight `W`

```
PHYSICAL W (exact definition)            : KERNEL-PROVED
W SUPPORT ⊆ [7/10, 9/10]                 : KERNEL-PROVED
W(7/10) = W(9/10) = 0, W(4/5) = 1        : KERNEL-PROVED
0 ≤ W ≤ 1                                : KERNEL-PROVED
W strictly increasing on [7/10, 4/5]     : KERNEL-PROVED
W strictly decreasing on [4/5, 9/10]     : KERNEL-PROVED
SUP NORM  IsGreatest (range W) 1         : KERNEL-PROVED
TOTAL VARIATION  eVariationOn W univ = 2 : KERNEL-PROVED  (Mathlib `eVariationOn`)
C_W = 2‖W‖_∞ + Var(W) = 4                : KERNEL-PROVED
ANALYTIC PRIME DISTRIBUTION              : NOT ASSERTED ANYWHERE IN THIS FILE
```

This module is **append-only**.  It changes no earlier statement and imports no earlier
Erdős-287 module.  It contains no analytic number theory: `W` is an explicit real bump
function with exact rational break points `7/10`, `4/5`, `9/10`.

## The exact weight

    W(x) = exp (1 - 1 / (1 - (10x - 8)²))     if |10x - 8| < 1,
    W(x) = 0                                  otherwise.

The condition `|10x-8| < 1` is coded as `(10x-8)^2 < 1`, which is equivalent and avoids an
absolute value in the defining `if`.

## Total variation

The variation notion used is the Mathlib notion `eVariationOn : (α → E) → Set α → ℝ≥0∞`
(the supremum of `∑ edist (f (u (i+1))) (f (u i))` over finite monotone samples in the set).
No bespoke "variation" definition is introduced for this file, so the row

    PHYSICAL-W-VARIATION45

is discharged against the project's ambient (Mathlib) notion, not against a private one.

## Firewall

`C_W = 4` is a statement about this explicit weight only.  It is **not** an estimate for any
arithmetic sum, it does not inhabit any analytic socket, and it does not bear on Erdős #287.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

namespace Erdos287
namespace September4PhysicalW

/-! ## §1.1  The exact weight and its two basic branches -/

/-- The affine physical coordinate `u(x) = 10x - 8`; `u = 0` at the centre `x = 4/5` and
`u = ∓1` at the exact rational endpoints `x = 7/10`, `x = 9/10`. -/
noncomputable def uCoord (x : ℝ) : ℝ := 10 * x - 8

/-- The exponent `1 - 1/(1 - u²)` of the physical bump, as a function of the affine
coordinate `u`. -/
noncomputable def bumpExponent (u : ℝ) : ℝ := 1 - (1 - u ^ 2)⁻¹

/-- **The physical weight.**

    W(x) = exp (1 - 1/(1 - (10x-8)²))   for |10x-8| < 1,   W(x) = 0 otherwise. -/
noncomputable def W (x : ℝ) : ℝ :=
  if (uCoord x) ^ 2 < 1 then Real.exp (bumpExponent (uCoord x)) else 0

theorem W_of_mem {x : ℝ} (h : (uCoord x) ^ 2 < 1) :
    W x = Real.exp (bumpExponent (uCoord x)) := if_pos h

theorem W_of_not_mem {x : ℝ} (h : ¬ (uCoord x) ^ 2 < 1) : W x = 0 := if_neg h

theorem uCoord_lt_one_iff (x : ℝ) : (uCoord x) ^ 2 < 1 ↔ 7 / 10 < x ∧ x < 9 / 10 := by
  constructor
  · intro h
    have h' : (10 * x - 8) ^ 2 < 1 := h
    constructor <;> nlinarith [h']
  · rintro ⟨h1, h2⟩
    have : (10 * x - 8) ^ 2 < 1 := by nlinarith
    exact this

/-! ## §1.2  Support, endpoint and centre values -/

/-- **`W_support_subset`.**  `KERNEL-PROVED`.  `support W ⊆ [7/10, 9/10]`. -/
theorem W_support_subset : Function.support W ⊆ Icc (7 / 10 : ℝ) (9 / 10) := by
  intro x hx
  by_cases h : (uCoord x) ^ 2 < 1
  · have := (uCoord_lt_one_iff x).1 h
    exact ⟨le_of_lt this.1, le_of_lt this.2⟩
  · exact absurd (W_of_not_mem h) hx

/-- The sharper open-support statement. -/
theorem W_support_subset_Ioo : Function.support W ⊆ Ioo (7 / 10 : ℝ) (9 / 10) := by
  intro x hx
  by_cases h : (uCoord x) ^ 2 < 1
  · exact (uCoord_lt_one_iff x).1 h
  · exact absurd (W_of_not_mem h) hx

theorem W_eq_zero_of_le {x : ℝ} (hx : x ≤ 7 / 10) : W x = 0 := by
  refine W_of_not_mem ?_
  intro h
  exact absurd ((uCoord_lt_one_iff x).1 h).1 (not_lt.2 hx)

theorem W_eq_zero_of_ge {x : ℝ} (hx : 9 / 10 ≤ x) : W x = 0 := by
  refine W_of_not_mem ?_
  intro h
  exact absurd ((uCoord_lt_one_iff x).1 h).2 (not_lt.2 hx)

/-- **`W_seven_tenths`.**  `KERNEL-PROVED`.  `W(7/10) = 0`. -/
theorem W_seven_tenths : W (7 / 10 : ℝ) = 0 := W_eq_zero_of_le le_rfl

/-- **`W_nine_tenths`.**  `KERNEL-PROVED`.  `W(9/10) = 0`. -/
theorem W_nine_tenths : W (9 / 10 : ℝ) = 0 := W_eq_zero_of_ge le_rfl

/-- **`W_four_fifths`.**  `KERNEL-PROVED`.  `W(4/5) = 1`: the centre value. -/
theorem W_four_fifths : W (4 / 5 : ℝ) = 1 := by
  have hu : uCoord (4 / 5 : ℝ) = 0 := by simp [uCoord]; ring
  have h : (uCoord (4 / 5 : ℝ)) ^ 2 < 1 := by rw [hu]; norm_num
  rw [W_of_mem h, hu]
  simp [bumpExponent]

/-! ## §1.3  The two-sided bound `0 ≤ W ≤ 1` -/

/-- **`W_nonneg`.**  `KERNEL-PROVED`. -/
theorem W_nonneg (x : ℝ) : 0 ≤ W x := by
  by_cases h : (uCoord x) ^ 2 < 1
  · rw [W_of_mem h]; exact (Real.exp_pos _).le
  · rw [W_of_not_mem h]

theorem bumpExponent_nonpos {u : ℝ} (h : u ^ 2 < 1) : bumpExponent u ≤ 0 := by
  have hpos : 0 < 1 - u ^ 2 := by linarith
  have hle : 1 - u ^ 2 ≤ 1 := by nlinarith [sq_nonneg u]
  have : (1 : ℝ) ≤ (1 - u ^ 2)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hpos]; simpa using hle
  simp only [bumpExponent]
  linarith

/-- **`W_le_one`.**  `KERNEL-PROVED`. -/
theorem W_le_one (x : ℝ) : W x ≤ 1 := by
  by_cases h : (uCoord x) ^ 2 < 1
  · rw [W_of_mem h, Real.exp_le_one_iff]
    exact bumpExponent_nonpos h
  · rw [W_of_not_mem h]; norm_num

theorem W_pos_of_mem {x : ℝ} (h : (uCoord x) ^ 2 < 1) : 0 < W x := by
  rw [W_of_mem h]; exact Real.exp_pos _

/-! ## §1.4  Monotonicity on the two halves -/

/-- The exponent is strictly larger at the *smaller* squared coordinate: this is the exact
monotonicity that drives both halves of the bump. -/
theorem bumpExponent_lt {u v : ℝ} (hu : u ^ 2 < 1) (h : v ^ 2 < u ^ 2) :
    bumpExponent u < bumpExponent v := by
  have hv : v ^ 2 < 1 := lt_trans h hu
  have hupos : 0 < 1 - u ^ 2 := by linarith
  have hvpos : 0 < 1 - v ^ 2 := by linarith
  have hinv : (1 - v ^ 2)⁻¹ < (1 - u ^ 2)⁻¹ := (inv_lt_inv₀ hvpos hupos).mpr (by linarith)
  simp only [bumpExponent]
  linarith

/-- **`W_strictMonoOn_left`.**  `KERNEL-PROVED`.  `W` is strictly increasing on the closed
left half `[7/10, 4/5]` (hence in particular on the open interval `(7/10, 4/5)`). -/
theorem W_strictMonoOn_left : StrictMonoOn W (Icc (7 / 10 : ℝ) (4 / 5)) := by
  intro x hx y hy hxy
  have hy' : (uCoord y) ^ 2 < 1 := by
    have h1 : 7 / 10 < y := lt_of_le_of_lt hx.1 hxy
    have h2 : y < 9 / 10 := lt_of_le_of_lt hy.2 (by norm_num)
    exact (uCoord_lt_one_iff y).2 ⟨h1, h2⟩
  by_cases hx' : (uCoord x) ^ 2 < 1
  · rw [W_of_mem hx', W_of_mem hy', Real.exp_lt_exp]
    refine bumpExponent_lt hx' ?_
    have hux : uCoord x ≤ 0 := by
      have := hx.2; simp only [uCoord]; linarith
    have huy : uCoord y ≤ 0 := by
      have := hy.2; simp only [uCoord]; linarith
    have hlt : uCoord x < uCoord y := by simp only [uCoord]; linarith
    have hprod : (uCoord y - uCoord x) * (uCoord y + uCoord x) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    nlinarith
  · rw [W_of_not_mem hx']
    exact W_pos_of_mem hy'

/-- The exact reflection symmetry about the centre `4/5`: `W(8/5 - x) = W(x)`. -/
theorem W_symm (x : ℝ) : W (8 / 5 - x) = W x := by
  have hu : uCoord (8 / 5 - x) = - uCoord x := by simp only [uCoord]; ring
  by_cases h : (uCoord x) ^ 2 < 1
  · have h' : (uCoord (8 / 5 - x)) ^ 2 < 1 := by rw [hu]; simpa using h
    rw [W_of_mem h', W_of_mem h, hu]
    congr 1
    simp only [bumpExponent]
    ring_nf
  · have h' : ¬ (uCoord (8 / 5 - x)) ^ 2 < 1 := by rw [hu]; simpa using h
    rw [W_of_not_mem h', W_of_not_mem h]

/-- **`W_strictAntiOn_right`.**  `KERNEL-PROVED`.  `W` is strictly decreasing on the closed
right half `[4/5, 9/10]`. -/
theorem W_strictAntiOn_right : StrictAntiOn W (Icc (4 / 5 : ℝ) (9 / 10)) := by
  intro x hx y hy hxy
  have hx' : (8 / 5 - x) ∈ Icc (7 / 10 : ℝ) (4 / 5) := by
    constructor <;> [linarith [hx.2]; linarith [hx.1]]
  have hy' : (8 / 5 - y) ∈ Icc (7 / 10 : ℝ) (4 / 5) := by
    constructor <;> [linarith [hy.2]; linarith [hy.1]]
  have := W_strictMonoOn_left hy' hx' (by linarith)
  rwa [W_symm, W_symm] at this

/-! ## §1.5  The sup norm -/

/-- **`W_isGreatest_one`.**  `KERNEL-PROVED`.  `1` is the greatest value of `W`: this is the
statement `‖W‖_∞ = 1` in the ambient (unbundled) representation. -/
theorem W_isGreatest_one : IsGreatest (Set.range W) 1 :=
  ⟨⟨4 / 5, W_four_fifths⟩, by rintro y ⟨x, rfl⟩; exact W_le_one x⟩

/-- **`W_sSup_range`.**  `KERNEL-PROVED`.  `sSup (range W) = 1`. -/
theorem W_sSup_range : sSup (Set.range W) = 1 := W_isGreatest_one.csSup_eq

/-- **`W_iSup`.**  `KERNEL-PROVED`.  `⨆ x, W x = 1`. -/
theorem W_iSup : (⨆ x : ℝ, W x) = 1 := by
  rw [iSup, W_sSup_range]

/-! ## §1.6  The total variation, in the Mathlib sense -/

/-- **`W_variation_left`.**  `KERNEL-PROVED`.  The variation of `W` over the rising half is
exactly `1`. -/
theorem W_variation_left : eVariationOn W (Icc (7 / 10 : ℝ) (4 / 5)) = 1 := by
  have hmemA : (7 / 10 : ℝ) ∈ Icc (7 / 10 : ℝ) (4 / 5) := by constructor <;> norm_num
  have hmemB : (4 / 5 : ℝ) ∈ Icc (7 / 10 : ℝ) (4 / 5) := by constructor <;> norm_num
  have hmono : MonotoneOn W (Icc (7 / 10 : ℝ) (4 / 5)) := W_strictMonoOn_left.monotoneOn
  have hle : eVariationOn W (Icc (7 / 10 : ℝ) (4 / 5))
      ≤ ENNReal.ofReal (W (4 / 5) - W (7 / 10)) := by
    have h := hmono.eVariationOn_le hmemA hmemB
    rwa [Set.inter_self] at h
  have hge : ENNReal.ofReal (W (4 / 5) - W (7 / 10))
      ≤ eVariationOn W (Icc (7 / 10 : ℝ) (4 / 5)) := by
    have h := eVariationOn.edist_le W hmemB hmemA
    refine le_trans ?_ h
    rw [edist_dist, Real.dist_eq, abs_of_nonneg (by
      rw [W_four_fifths, W_seven_tenths]; norm_num : (0 : ℝ) ≤ W (4 / 5) - W (7 / 10))]
  have heq := le_antisymm hle hge
  rw [heq, W_four_fifths, W_seven_tenths]
  simp

/-- **`W_variation_right`.**  `KERNEL-PROVED`.  The variation of `W` over the falling half is
exactly `1`; it is obtained from the rising half by the exact reflection `x ↦ 8/5 − x`. -/
theorem W_variation_right : eVariationOn W (Icc (4 / 5 : ℝ) (9 / 10)) = 1 := by
  have hphi : AntitoneOn (fun x : ℝ => 8 / 5 - x) (Icc (4 / 5 : ℝ) (9 / 10)) := by
    intro a _ b _ hab; simpa using by linarith
  have himg : (fun x : ℝ => 8 / 5 - x) '' Icc (4 / 5 : ℝ) (9 / 10) = Icc (7 / 10 : ℝ) (4 / 5) := by
    rw [Set.image_const_sub_Icc]; norm_num
  have hcomp : eVariationOn (W ∘ fun x : ℝ => 8 / 5 - x) (Icc (4 / 5 : ℝ) (9 / 10))
      = eVariationOn W ((fun x : ℝ => 8 / 5 - x) '' Icc (4 / 5 : ℝ) (9 / 10)) :=
    eVariationOn.comp_eq_of_antitoneOn W _ hphi
  have heqOn : Set.EqOn W (W ∘ fun x : ℝ => 8 / 5 - x) (Icc (4 / 5 : ℝ) (9 / 10)) := by
    intro x _; simpa using (W_symm x).symm
  rw [eVariationOn.eq_of_eqOn heqOn, hcomp, himg, W_variation_left]

/-- **`W_variation_Icc`.**  `KERNEL-PROVED`.  `Var_{[7/10,9/10]}(W) = 2`. -/
theorem W_variation_Icc : eVariationOn W (Icc (7 / 10 : ℝ) (9 / 10)) = 2 := by
  have h := eVariationOn.Icc_add_Icc W (s := Set.univ) (a := (7 / 10 : ℝ)) (b := 4 / 5)
    (c := 9 / 10) (by norm_num) (by norm_num) (Set.mem_univ _)
  simp only [Set.univ_inter] at h
  rw [W_variation_left, W_variation_right] at h
  rw [← h]
  norm_num

/-- The variation over the whole line: `W` vanishes outside its support, so the tails
contribute nothing.  `KERNEL-PROVED`. -/
theorem W_variation_Iic : eVariationOn W (Iic (4 / 5 : ℝ)) = 1 := by
  have hphi : MonotoneOn (fun x : ℝ => max x (7 / 10)) (Iic (4 / 5 : ℝ)) := by
    intro a _ b _ hab; exact max_le_max hab le_rfl
  have himg : (fun x : ℝ => max x (7 / 10)) '' Iic (4 / 5 : ℝ) = Icc (7 / 10 : ℝ) (4 / 5) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨le_max_right _ _, max_le (by simpa using hx) (by norm_num)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨y, by simpa using h2, max_eq_left h1⟩
  have heqOn : Set.EqOn W (W ∘ fun x : ℝ => max x (7 / 10)) (Iic (4 / 5 : ℝ)) := by
    intro x _
    rcases le_or_gt x (7 / 10) with h | h
    · simp only [Function.comp_apply, max_eq_right h, W_seven_tenths, W_eq_zero_of_le h]
    · simp [max_eq_left h.le]
  rw [eVariationOn.eq_of_eqOn heqOn, eVariationOn.comp_eq_of_monotoneOn W _ hphi, himg,
    W_variation_left]

theorem W_variation_Ici : eVariationOn W (Ici (4 / 5 : ℝ)) = 1 := by
  have hphi : MonotoneOn (fun x : ℝ => min x (9 / 10)) (Ici (4 / 5 : ℝ)) := by
    intro a _ b _ hab; exact min_le_min hab le_rfl
  have himg : (fun x : ℝ => min x (9 / 10)) '' Ici (4 / 5 : ℝ) = Icc (4 / 5 : ℝ) (9 / 10) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨le_min (by simpa using hx) (by norm_num), min_le_right _ _⟩
    · rintro ⟨h1, h2⟩
      exact ⟨y, by simpa using h1, min_eq_left h2⟩
  have heqOn : Set.EqOn W (W ∘ fun x : ℝ => min x (9 / 10)) (Ici (4 / 5 : ℝ)) := by
    intro x _
    rcases le_or_gt (9 / 10) x with h | h
    · simp only [Function.comp_apply, min_eq_right h, W_nine_tenths, W_eq_zero_of_ge h]
    · simp [min_eq_left h.le]
  rw [eVariationOn.eq_of_eqOn heqOn, eVariationOn.comp_eq_of_monotoneOn W _ hphi, himg,
    W_variation_right]

/-- **`physicalW_variation`** (row `PHYSICAL-W-VARIATION45`).  `KERNEL-PROVED`.

    Var(W) = eVariationOn W univ = 2,

in the ambient Mathlib variation notion. -/
theorem physicalW_variation : eVariationOn W Set.univ = 2 := by
  have hU : Iic (4 / 5 : ℝ) ∪ Ici (4 / 5 : ℝ) = Set.univ := Set.Iic_union_Ici
  have h := eVariationOn.union W (x := (4 / 5 : ℝ)) (s := Iic (4 / 5 : ℝ)) (t := Ici (4 / 5 : ℝ))
    isGreatest_Iic isLeast_Ici
  rw [hU, W_variation_Iic, W_variation_Ici] at h
  rw [h]
  norm_num

/-! ## §1.7  The compiler constant `C_W = 2‖W‖_∞ + Var(W)` -/

/-- The compiler constant of the physical weight, in the representation actually used here:
twice the supremum of `W` plus its (Mathlib) total variation. -/
noncomputable def C_W : ℝ := 2 * sSup (Set.range W) + (eVariationOn W Set.univ).toReal

/-- **`physicalW_CW_eq_four`** (row `ERDOS287-PHYSICAL-W-CW4`).  `KERNEL-PROVED`.

    C_W = 2‖W‖_∞ + Var(W) = 2·1 + 2 = 4.

Every term of the *actual* definition is kernel-proved: `sSup (range W) = 1`
(`W_sSup_range`) and `eVariationOn W univ = 2` (`physicalW_variation`). -/
theorem physicalW_CW_eq_four : C_W = 4 := by
  show 2 * sSup (Set.range W) + (eVariationOn W Set.univ).toReal = 4
  rw [W_sSup_range, physicalW_variation]
  norm_num

/-! ## §1.8  The derivative inside the support (optional row) -/

/-- **`W_hasDerivAt`.**  `KERNEL-PROVED`.  Inside the support,

    W'(x) = -20 u v² exp(1 - v),   u = 10x - 8,  v = (1 - u²)⁻¹. -/
theorem W_hasDerivAt {x : ℝ} (h : (uCoord x) ^ 2 < 1) :
    HasDerivAt W
      (-20 * uCoord x * ((1 - (uCoord x) ^ 2)⁻¹) ^ 2 *
        Real.exp (1 - (1 - (uCoord x) ^ 2)⁻¹)) x := by
  have hpos : 0 < 1 - (uCoord x) ^ 2 := by linarith
  have hne : (1 - (uCoord x) ^ 2) ≠ 0 := ne_of_gt hpos
  have hu : HasDerivAt uCoord 10 x := by
    have h0 : HasDerivAt (fun y : ℝ => 10 * y - 8) 10 x := by
      simpa using ((hasDerivAt_id x).const_mul (10 : ℝ)).sub_const 8
    exact h0
  have hden : HasDerivAt (fun y => 1 - (uCoord y) ^ 2) (-(20 * uCoord x)) x := by
    have h1 := (hu.pow 2).const_sub 1
    convert h1 using 1
    ring
  have hinv : HasDerivAt (fun y => (1 - (uCoord y) ^ 2)⁻¹)
      (20 * uCoord x * ((1 - (uCoord x) ^ 2)⁻¹) ^ 2) x := by
    have h2 := hden.inv hne
    convert h2 using 1
    field_simp
  have hexp : HasDerivAt (fun y => Real.exp (1 - (1 - (uCoord y) ^ 2)⁻¹))
      (Real.exp (1 - (1 - (uCoord x) ^ 2)⁻¹) *
        (-(20 * uCoord x * ((1 - (uCoord x) ^ 2)⁻¹) ^ 2))) x := by
    have h3 := (hinv.const_sub 1).exp
    convert h3 using 1
  have hloc : W =ᶠ[nhds x] fun y => Real.exp (1 - (1 - (uCoord y) ^ 2)⁻¹) := by
    have hopen : IsOpen {y : ℝ | (uCoord y) ^ 2 < 1} := by
      have hc : Continuous fun y : ℝ => (uCoord y) ^ 2 := by
        unfold uCoord; fun_prop
      exact isOpen_lt hc continuous_const
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds h) ?_
    intro y hy
    simpa [bumpExponent] using W_of_mem hy
  have h4 := hexp.congr_of_eventuallyEq hloc
  convert h4 using 1
  ring

end September4PhysicalW
end Erdos287
