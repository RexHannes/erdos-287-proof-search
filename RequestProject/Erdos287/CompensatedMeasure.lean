import Mathlib
import RequestProject.Erdos287.BsrcWeights
import RequestProject.Erdos287.ProperGammaOddConvolution

/-!
# Erdős #287 effectivity — the compensated counting measure `G_M`, `Ĝ_M`, `Ê_M` (§50)

```
HYPERBOLA DOUBLE-SUM IDENTITY          : KERNEL-PROVED
ODD CONVOLUTION t·β(t) = 1_odd ⋆ η     : KERNEL-PROVED (reuses the banked η)
G_M IN CONVOLUTION FORM                : KERNEL-PROVED
EXACT FINITE EXPRESSION FOR Ê_M        : KERNEL-PROVED
PER-ATOM COMPENSATION BOUND |ρ| ≤ 1/2  : KERNEL-PROVED
INFINITE TAIL                          : CONDITIONAL_ANALYTIC (hypothesis, not asserted)
```

This module is **append-only**: nothing in the long-fibre, proper-γ, multiplicity or
EARLY_4490 banks is rewritten.  It reuses `beta`, `gz` and `hz` verbatim from
`BsrcWeights` / `ProperGammaOddConvolution`.

The selected β-weight is

    w(t) = t · β(t),

and the banked local coefficients are `η = hz 1` (the odd-supported Möbius transform of
`g_1(t) = t β(t)`), for which the banked identity `oddConvolution_identity` gives exactly

    t β(t) = (1_odd ⋆ η)(t).

The compensated measure is then defined at integer cut-off `Y`:

    G_M(Y)  = ∑_{1 ≤ t ≤ Y} t β(t) 1_{(t,M)=1},
    Ĝ_M(Y)  = ∑_{1 ≤ d ≤ Y} η_M(d) · Y/(2d),
    Ê_M(Y)  = G_M(Y) − Ĝ_M(Y).

`Ehat_exact` gives the exact finite expression of `Ê_M(Y)` as the sum of the atomwise
compensation defects, each of absolute value at most `1/2`.  **No smallness of `Ê_M` is
asserted**: the only bound proved is the trivial `ℓ¹` bound, and the infinite-cut-off
statement is carried as an explicit hypothesis object.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §50.1  The hyperbola double-sum identity -/

/-- The hyperbola region `{(d,u) : d,u ≥ 1, d·u ≤ Y}`. -/
def hyperbolaRegion (Y : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 Y ×ˢ Finset.Icc 1 Y).filter (fun q => q.1 * q.2 ≤ Y)

lemma mem_hyperbolaRegion {Y : ℕ} {q : ℕ × ℕ} :
    q ∈ hyperbolaRegion Y ↔ 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 * q.2 ≤ Y := by
  constructor
  · intro h
    simp only [hyperbolaRegion, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h
    exact ⟨h.1.1.1, h.1.2.1, h.2⟩
  · rintro ⟨h1, h2, h3⟩
    have hq1 : q.1 ≤ Y := le_trans (Nat.le_mul_of_pos_right _ h2) h3
    have hq2 : q.2 ≤ Y := le_trans (Nat.le_mul_of_pos_left _ h1) h3
    simp only [hyperbolaRegion, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨h1, hq1⟩, ⟨h2, hq2⟩⟩, h3⟩

/-- The fibre of the hyperbola region over a product value `t ≥ 1`, `t ≤ Y`, is exactly the
divisor antidiagonal of `t`. -/
lemma hyperbolaRegion_fiber {Y t : ℕ} (ht1 : 1 ≤ t) (htY : t ≤ Y) :
    (hyperbolaRegion Y).filter (fun q => q.1 * q.2 = t) = t.divisorsAntidiagonal := by
  ext q
  simp only [Finset.mem_filter, mem_hyperbolaRegion, Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨-, h⟩; exact ⟨h, by omega⟩
  · rintro ⟨hmul, -⟩
    have h1 : 1 ≤ q.1 := by
      rcases Nat.eq_zero_or_pos q.1 with h | h
      · simp [h] at hmul; omega
      · exact h
    have h2 : 1 ≤ q.2 := by
      rcases Nat.eq_zero_or_pos q.2 with h | h
      · simp [h] at hmul; omega
      · exact h
    exact ⟨⟨h1, h2, by omega⟩, hmul⟩

/-- **`hyperbola_double_sum`.**  `KERNEL-PROVED`.  The exact hyperbola interchange

    ∑_{t ≤ Y} ∑_{d ∣ t} f(d) g(t/d) = ∑_{d ≤ Y} f(d) ∑_{u ≤ Y/d} g(u).

No estimate is involved: this is an exact reindexing of a finite sum. -/
theorem hyperbola_double_sum (Y : ℕ) (f g : ℕ → ℚ) :
    ∑ t ∈ Finset.Icc 1 Y, ∑ d ∈ t.divisors, f d * g (t / d)
      = ∑ d ∈ Finset.Icc 1 Y, f d * ∑ u ∈ Finset.Icc 1 (Y / d), g u := by
  have hmaps : ∀ q ∈ hyperbolaRegion Y, q.1 * q.2 ∈ Finset.Icc 1 Y := by
    intro q hq
    rw [mem_hyperbolaRegion] at hq
    obtain ⟨h1, h2, h3⟩ := hq
    simp only [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), h3⟩
  have hgroup :
      ∑ t ∈ Finset.Icc 1 Y, ∑ q ∈ (hyperbolaRegion Y).filter (fun q => q.1 * q.2 = t),
          f q.1 * g q.2
        = ∑ q ∈ hyperbolaRegion Y, f q.1 * g q.2 :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  have hleft :
      ∑ t ∈ Finset.Icc 1 Y, ∑ d ∈ t.divisors, f d * g (t / d)
        = ∑ q ∈ hyperbolaRegion Y, f q.1 * g q.2 := by
    rw [← hgroup]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_Icc] at ht
    rw [hyperbolaRegion_fiber ht.1 ht.2, ← Nat.sum_divisorsAntidiagonal (fun a b => f a * g b)]
  have hright :
      ∑ q ∈ hyperbolaRegion Y, f q.1 * g q.2
        = ∑ d ∈ Finset.Icc 1 Y, f d * ∑ u ∈ Finset.Icc 1 (Y / d), g u := by
    rw [hyperbolaRegion, Finset.sum_filter,
      Finset.sum_product' (Finset.Icc 1 Y) (Finset.Icc 1 Y)
        (fun x y => if x * y ≤ Y then f x * g y else 0)]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    rw [Finset.mul_sum]
    have hset : Finset.Icc 1 (Y / d) = (Finset.Icc 1 Y).filter (fun u => d * u ≤ Y) := by
      ext u
      simp only [Finset.mem_Icc, Finset.mem_filter]
      constructor
      · rintro ⟨hu1, hu2⟩
        have hdu : d * u ≤ Y := by
          rw [mul_comm]; exact (Nat.le_div_iff_mul_le (by omega)).1 hu2
        refine ⟨⟨hu1, ?_⟩, hdu⟩
        exact le_trans (Nat.le_mul_of_pos_left _ (by omega)) hdu
      · rintro ⟨⟨hu1, -⟩, hdu⟩
        refine ⟨hu1, (Nat.le_div_iff_mul_le (by omega)).2 ?_⟩
        rw [mul_comm]; exact hdu
    rw [hset, Finset.sum_filter]
  rw [hleft, hright]

/-! ## §50.2  The selected β-weight and its banked local coefficients -/

/-- The selected weight `w(t) = t·β(t)`. -/
def wbeta (t : ℕ) : ℚ := (t : ℚ) * beta t

/-- The banked local coefficients `η = h_1`, the odd-supported Möbius transform of `w`. -/
def etaLoc (d : ℕ) : ℚ := hz 1 d

lemma gz_one_eq_wbeta (t : ℕ) : gz 1 t = wbeta t := by
  simp [gz, wbeta]

/-- **`selectedWeight_oddConvolution`.**  `KERNEL-PROVED`.  The odd-convolution identity
`t·β(t) = (1_odd ⋆ η)(t)` with the banked local coefficients `η`. -/
theorem selectedWeight_oddConvolution {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, (if ¬ 2 ∣ (n / d) then (1 : ℚ) else 0) * etaLoc d = wbeta n := by
  rw [← gz_one_eq_wbeta]
  exact oddConvolution_identity 1 hn

/-! ## §50.3  The compensated counting measure -/

/-- `G_M(Y) = ∑_{1 ≤ t ≤ Y} t β(t) 1_{(t,M)=1}` — the selected counting measure. -/
def GM (M Y : ℕ) : ℚ := ∑ t ∈ Finset.Icc 1 Y, gz M t

/-- The `M`-restricted local coefficients. -/
def etaM (M d : ℕ) : ℚ := hz M d

/-- The smooth (density) part `Ĝ_M(Y) = ∑_{d ≤ Y} η_M(d)·Y/(2d)`. -/
def GhatM (M Y : ℕ) : ℚ := ∑ d ∈ Finset.Icc 1 Y, etaM M d * ((Y : ℚ) / (2 * d))

/-- The compensated remainder `Ê_M(Y) = G_M(Y) − Ĝ_M(Y)`. -/
def EhatM (M Y : ℕ) : ℚ := GM M Y - GhatM M Y

/-- The atomwise compensation defect at cut-off `Y` and modulus `d`:
`ρ(Y,d) = #{odd u ≤ Y/d} − Y/(2d)`. -/
def rhoAtom (Y d : ℕ) : ℚ := (((Y / d + 1) / 2 : ℕ) : ℚ) - (Y : ℚ) / (2 * d)

/-- **`GM_convolution_form`.**  `KERNEL-PROVED`.  The measure in local-coefficient form:

    G_M(Y) = ∑_{d ≤ Y} η_M(d) · #{odd u ≤ Y/d}. -/
theorem GM_convolution_form (M Y : ℕ) :
    GM M Y = ∑ d ∈ Finset.Icc 1 Y, etaM M d * (((Y / d + 1) / 2 : ℕ) : ℚ) := by
  have hexp : GM M Y
      = ∑ t ∈ Finset.Icc 1 Y, ∑ d ∈ t.divisors,
          etaM M d * (if ¬ 2 ∣ (t / d) then (1 : ℚ) else 0) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_Icc] at ht
    rw [← oddConvolution_identity M (by omega)]
    exact Finset.sum_congr rfl fun d _ => by rw [mul_comm]; rfl
  rw [hexp, hyperbola_double_sum Y (fun d => etaM M d)
    (fun u => if ¬ 2 ∣ u then (1 : ℚ) else 0)]
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  rw [Finset.sum_boole, oddCount_exact (Y / d)]

/-- **`Ehat_exact`.**  `KERNEL-PROVED`.  The exact finite expression of the compensated
remainder as a sum of atomwise defects.  No smallness is asserted. -/
theorem Ehat_exact (M Y : ℕ) :
    EhatM M Y = ∑ d ∈ Finset.Icc 1 Y, etaM M d * rhoAtom Y d := by
  rw [EhatM, GM_convolution_form, GhatM, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [rhoAtom, mul_sub]

/-- **`abs_rhoAtom_le`.**  `KERNEL-PROVED`.  Each atomwise defect is bounded by `1/2`. -/
theorem abs_rhoAtom_le {Y d : ℕ} (hd : 0 < d) : |rhoAtom Y d| ≤ 1 / 2 := by
  have hkey : Y < (Y / d + 1) * d := by
    have h1 := Nat.div_add_mod Y d
    have h2 := Nat.mod_lt Y hd
    nlinarith
  have hqd : ((Y / d : ℕ) : ℚ) ≤ (Y : ℚ) / d := by
    rw [le_div_iff₀ (by positivity)]
    exact_mod_cast Nat.div_mul_le_self Y d
  have hqd' : (Y : ℚ) / d < ((Y / d : ℕ) : ℚ) + 1 := by
    rw [div_lt_iff₀ (by positivity)]
    exact_mod_cast hkey
  have hcount : ((Y / d + 1) / 2 : ℕ) * 2 ≤ Y / d + 1 ∧ Y / d ≤ ((Y / d + 1) / 2 : ℕ) * 2 := by
    omega
  have h1 : (((Y / d + 1) / 2 : ℕ) : ℚ) * 2 ≤ ((Y / d : ℕ) : ℚ) + 1 := by exact_mod_cast hcount.1
  have h2 : ((Y / d : ℕ) : ℚ) ≤ (((Y / d + 1) / 2 : ℕ) : ℚ) * 2 := by exact_mod_cast hcount.2
  have hhalf : (Y : ℚ) / (2 * d) = ((Y : ℚ) / d) / 2 := by
    rw [div_div]; ring_nf
  rw [abs_le, rhoAtom, hhalf]
  constructor <;> linarith

/-- **`abs_Ehat_le_l1`.**  `KERNEL-PROVED`.  The only bound proved here is the trivial
`ℓ¹` bound `|Ê_M(Y)| ≤ (1/2) ∑_{d ≤ Y} |η_M(d)|`.  This is *not* a smallness statement. -/
theorem abs_Ehat_le_l1 (M Y : ℕ) :
    |EhatM M Y| ≤ (1 / 2) * ∑ d ∈ Finset.Icc 1 Y, |etaM M d| := by
  rw [Ehat_exact, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun d hd => ?_)
  rw [Finset.mem_Icc] at hd
  rw [abs_mul]
  have h := abs_rhoAtom_le (Y := Y) (d := d) (by omega)
  have habs : (0 : ℚ) ≤ |etaM M d| := abs_nonneg _
  calc |etaM M d| * |rhoAtom Y d| ≤ |etaM M d| * (1 / 2) := by
        exact mul_le_mul_of_nonneg_left h habs
    _ = 1 / 2 * |etaM M d| := by ring

/-! ## §50.4  The infinite cut-off: conditional interface only -/

/-- The infinite-cut-off statement for the compensated measure is carried as an explicit
hypothesis object: a limit of the finite truncations.  It is **never** asserted, and no
external analytic estimate is imported. -/
structure CompensatedTailInterface (M : ℕ) where
  /-- the claimed limit of the compensated remainders along a scaling -/
  limitValue : ℝ
  /-- the hypothesis that the finite truncations converge to it -/
  tendsto :
    Filter.Tendsto (fun Y : ℕ => ((EhatM M Y : ℚ) : ℝ)) Filter.atTop (nhds limitValue)

/-- **`compensated_tail_not_asserted`.**  `KERNEL-PROVED`.  Inhabiting the tail interface
carries no numerical content: for every real `c` there is a hypothesis object with that
limit value *if* the corresponding convergence holds.  Nothing here proves convergence. -/
theorem compensated_tail_not_asserted (M : ℕ) (I : CompensatedTailInterface M) :
    Filter.Tendsto (fun Y : ℕ => ((EhatM M Y : ℚ) : ℝ)) Filter.atTop (nhds I.limitValue) :=
  I.tendsto

end Effectivity
end Erdos287
