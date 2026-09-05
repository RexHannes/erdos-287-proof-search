import Mathlib

/-!
# Erdős #287 effectivity — the `c = 1 / c = 2` splice (§10, §11)

```
c1/c2 DISCRETE SPLICE   : KERNEL-PROVED
c1/c2 CONTINUOUS SPLICE : KERNEL-PROVED (integrability as an explicit hypothesis)
```

## Conventions

The two lanes are, with `T d n = A_d(n)·W(dn/X)` an arbitrary real weight,

    D₁ = ∑_d μ(d) ∑_{d < n ≤ Nb}       T d n,
    D₂ = ∑_d μ(d) ∑_{2d < m ≤ Nb/2}    T d (2m)      (the `n ↦ 2n` substituted lane),

so that the `c = 2` lane sees exactly the **even** `n > 4d`.  Then

    D₁ − D₂ = ∑_d μ(d) [ ∑_{n > d, n odd} T d n + ∑_{d < n ≤ 4d, n even} T d n ],

and the upper endpoint `4d` is *derived* from the substitution `n ↦ 2n`
(`discrete_splice`).  The continuous lane is the exact mirror,

    C₁ = ∑_d μ(d) M_d ∫_d^∞ W(dt/X) dt,
    C₂ = ∑_d μ(d) M_d ∫_{2d}^∞ W(2dt/X) dt,

and the two factors `1/2` in

    C₁ − C₂ = ∑_d μ(d) M_d [ ½∫_d^∞ W(dt/X)dt + ½∫_d^{4d} W(dt/X)dt ]

come from the substitution `∫_{Ioi 2d} g(2t)dt = ½∫_{Ioi 4d} g`, not from an
assumption (`continuous_splice_pointwise`, `continuous_splice`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction MeasureTheory

namespace Erdos287
namespace Effectivity

/-! ## §10  The discrete splice -/

/-- The `c = 1` discrete lane, truncated at `Nb`. -/
def Ddisc1 (T : ℕ → ℕ → ℝ) (Dset : Finset ℕ) (Nb : ℕ) : ℝ :=
  ∑ d ∈ Dset, (moebius d : ℝ) * ∑ n ∈ Finset.Ioc d Nb, T d n

/-- The `c = 2` discrete lane after the substitution `n ↦ 2n`. -/
def Ddisc2 (T : ℕ → ℕ → ℝ) (Dset : Finset ℕ) (Nb : ℕ) : ℝ :=
  ∑ d ∈ Dset, (moebius d : ℝ) * ∑ m ∈ Finset.Ioc (2 * d) (Nb / 2), T d (2 * m)

/-- The image of `Ioc (2d) B` under doubling is the set of even elements of `Ioc (4d) (2B)`. -/
lemma image_two_mul_Ioc (d B : ℕ) :
    (Finset.Ioc (2 * d) B).image (fun m => 2 * m)
      = (Finset.Ioc (4 * d) (2 * B)).filter (fun n => 2 ∣ n) := by
  ext n
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨m, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨by omega, by omega⟩, ⟨m, rfl⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨m, rfl⟩⟩
    exact ⟨m, ⟨by omega, by omega⟩, rfl⟩

/-- The per-`d` discrete splice: the `c = 2` lane removes exactly the even `n > 4d`. -/
lemma discrete_splice_pointwise (T : ℕ → ℕ → ℝ) {d Nb B : ℕ} (hNb : Nb = 2 * B)
    (h4d : 4 * d ≤ Nb) :
    (∑ n ∈ Finset.Ioc d Nb, T d n) - ∑ m ∈ Finset.Ioc (2 * d) (Nb / 2), T d (2 * m)
      = (∑ n ∈ Finset.Ioc d Nb with ¬ (2 ∣ n), T d n)
        + ∑ n ∈ Finset.Ioc d (4 * d) with (2 ∣ n), T d n := by
  classical
  have hB : Nb / 2 = B := by omega
  -- the substituted lane is the even part beyond `4d`
  have hsub : (∑ m ∈ Finset.Ioc (2 * d) (Nb / 2), T d (2 * m))
      = ∑ n ∈ Finset.Ioc (4 * d) Nb with (2 ∣ n), T d n := by
    rw [hB]
    conv_rhs => rw [hNb]
    rw [← image_two_mul_Ioc d B,
      Finset.sum_image (by intro x _ y _ h; simp only [] at h; omega)]
  -- split the `c = 1` lane into odd and even parts
  have hsplit : (∑ n ∈ Finset.Ioc d Nb, T d n)
      = (∑ n ∈ Finset.Ioc d Nb with ¬ (2 ∣ n), T d n)
        + ∑ n ∈ Finset.Ioc d Nb with (2 ∣ n), T d n := by
    rw [add_comm]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- split the even part at `4d`
  have hIoc : Finset.Ioc d Nb = Finset.Ioc d (4 * d) ∪ Finset.Ioc (4 * d) Nb :=
    (Finset.Ioc_union_Ioc_eq_Ioc (by omega) h4d).symm
  have hdisj : Disjoint (Finset.Ioc d (4 * d)) (Finset.Ioc (4 * d) Nb) := by
    refine Finset.disjoint_left.2 fun x hx hx' => ?_
    simp only [Finset.mem_Ioc] at hx hx'
    omega
  have heven : (∑ n ∈ Finset.Ioc d Nb with (2 ∣ n), T d n)
      = (∑ n ∈ Finset.Ioc d (4 * d) with (2 ∣ n), T d n)
        + ∑ n ∈ Finset.Ioc (4 * d) Nb with (2 ∣ n), T d n := by
    rw [hIoc, Finset.filter_union, Finset.sum_union]
    exact Finset.disjoint_filter_filter hdisj
  rw [hsub, hsplit, heven]
  ring

/-- **`discrete_splice`.**  `KERNEL-PROVED`.  The exact finite-sum `c = 1 / c = 2` splice,

    D₁ − D₂ = ∑_d μ(d) [ ∑_{d < n ≤ Nb, n odd} T d n + ∑_{d < n ≤ 4d, n even} T d n ].

The upper endpoint `4d` is derived from the substitution `n ↦ 2n`. -/
theorem discrete_splice (T : ℕ → ℕ → ℝ) (Dset : Finset ℕ) {Nb B : ℕ} (hNb : Nb = 2 * B)
    (h4d : ∀ d ∈ Dset, 4 * d ≤ Nb) :
    Ddisc1 T Dset Nb - Ddisc2 T Dset Nb
      = ∑ d ∈ Dset, (moebius d : ℝ) *
          ((∑ n ∈ Finset.Ioc d Nb with ¬ (2 ∣ n), T d n)
            + ∑ n ∈ Finset.Ioc d (4 * d) with (2 ∣ n), T d n) := by
  rw [Ddisc1, Ddisc2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [← mul_sub, discrete_splice_pointwise T hNb (h4d d hd)]

/-! ## §11  The continuous splice -/

/-- **`continuous_splice_pointwise`.**  `KERNEL-PROVED`.  The per-`d` continuous splice.
Both factors `1/2` come from the substitution `∫_{Ioi 2d} g(2t) dt = ½ ∫_{Ioi 4d} g`. -/
theorem continuous_splice_pointwise (W : ℝ → ℝ) (X : ℝ) {d : ℝ} (hd : 0 < d)
    (hint : IntegrableOn (fun t => W (d * t / X)) (Set.Ioi d)) :
    (∫ t in Set.Ioi d, W (d * t / X)) - ∫ t in Set.Ioi (2 * d), W (2 * d * t / X)
      = (1 / 2) * (∫ t in Set.Ioi d, W (d * t / X))
        + (1 / 2) * ∫ t in Set.Ioc d (4 * d), W (d * t / X) := by
  set g : ℝ → ℝ := fun y => W (d * y / X) with hg
  -- the `c = 2` integral is a scaled copy
  have hscale : (∫ t in Set.Ioi (2 * d), W (2 * d * t / X))
      = (2 : ℝ)⁻¹ * ∫ s in Set.Ioi (4 * d), g s := by
    have h1 : (∫ t in Set.Ioi (2 * d), W (2 * d * t / X)) = ∫ t in Set.Ioi (2 * d), g (2 * t) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp only [hg]
      ring_nf
    rw [h1, integral_comp_mul_left_Ioi g (2 * d) (by norm_num : (0:ℝ) < 2)]
    simp only [smul_eq_mul]
    norm_num
    ring_nf
  -- split the `c = 1` integral at `4d`
  have hsplit : (∫ t in Set.Ioi d, g t)
      = (∫ t in Set.Ioc d (4 * d), g t) + ∫ t in Set.Ioi (4 * d), g t := by
    have hunion : Set.Ioc d (4 * d) ∪ Set.Ioi (4 * d) = Set.Ioi d :=
      Set.Ioc_union_Ioi_eq_Ioi (by linarith)
    have hdisj : Disjoint (Set.Ioc d (4 * d)) (Set.Ioi (4 * d)) :=
      Set.Ioc_disjoint_Ioi le_rfl
    rw [← hunion] at hint ⊢
    rw [setIntegral_union hdisj measurableSet_Ioi
      (hint.mono_set Set.subset_union_left) (hint.mono_set Set.subset_union_right)]
  rw [hscale]
  have : (∫ s in Set.Ioi (4 * d), g s)
      = (∫ t in Set.Ioi d, g t) - ∫ t in Set.Ioc d (4 * d), g t := by rw [hsplit]; ring
  rw [this]
  simp only [hg]
  ring

/-- The `c = 1` continuous lane. -/
noncomputable def Ccont1 (W : ℝ → ℝ) (X : ℝ) (M : ℕ → ℝ) (Dset : Finset ℕ) : ℝ :=
  ∑ d ∈ Dset, (moebius d : ℝ) * M d * ∫ t in Set.Ioi (d : ℝ), W ((d : ℝ) * t / X)

/-- The `c = 2` continuous lane. -/
noncomputable def Ccont2 (W : ℝ → ℝ) (X : ℝ) (M : ℕ → ℝ) (Dset : Finset ℕ) : ℝ :=
  ∑ d ∈ Dset, (moebius d : ℝ) * M d * ∫ t in Set.Ioi (2 * (d : ℝ)), W (2 * (d : ℝ) * t / X)

/-- **`continuous_splice`.**  `KERNEL-PROVED` (given integrability of each lane).

    C₁ − C₂ = ∑_d μ(d) M_d [ ½ ∫_d^∞ W(dt/X)dt + ½ ∫_d^{4d} W(dt/X)dt ]. -/
theorem continuous_splice (W : ℝ → ℝ) (X : ℝ) (M : ℕ → ℝ) (Dset : Finset ℕ)
    (hpos : ∀ d ∈ Dset, 0 < d)
    (hint : ∀ d ∈ Dset, IntegrableOn (fun t => W ((d : ℝ) * t / X)) (Set.Ioi (d : ℝ))) :
    Ccont1 W X M Dset - Ccont2 W X M Dset
      = ∑ d ∈ Dset, (moebius d : ℝ) * M d *
          ((1 / 2) * (∫ t in Set.Ioi (d : ℝ), W ((d : ℝ) * t / X))
            + (1 / 2) * ∫ t in Set.Ioc (d : ℝ) (4 * (d : ℝ)), W ((d : ℝ) * t / X)) := by
  rw [Ccont1, Ccont2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hpos d hd
  rw [← mul_sub, continuous_splice_pointwise W X hd0 (hint d hd)]

end Effectivity
end Erdos287
