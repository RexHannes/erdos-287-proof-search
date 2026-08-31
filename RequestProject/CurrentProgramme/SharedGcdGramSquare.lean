import Mathlib
import RequestProject.CurrentProgramme.LevelPairPrimeAssignment

/-!
# Shared-gcd projector / Gram-as-square — Erdős #287, ONE-LEVEL MÖBIUS Δ, §§9–10

**Exact finite algebra only.**  No analytic statement is made here.

Let `Ω_H` be the (finite) shared-gcd projector on the divisor lattice and set

```
λ_H = μ ∗ Ω_H,        λ_H(d) = ∑_{ke = d} μ(k) Ω_H(e).
```

Banked in §9:

* `sum_lambdaH_divisors` — Möbius inversion `Ω_H(m) = ∑_{d ∣ m} λ_H(d)`;
* `omega_gcd_eq_indicator_sum` — `Ω_H(gcd(g₁,g₂)) = ∑_{d ∣ g₁, d ∣ g₂} λ_H(d)` over the finite
  divisor support of the level set;
* `sharedGcd_gram_square` — **`DET1-SHAREDGCD-GRAM-SQUARE45`**: the exact Gram identity

  ```
  Q_H = ∑_d λ_H(d) ∑_a ρ(a) | ∑_{d ∣ g} w(g) V_g(a) |².
  ```

* `moebius_split_clean_sector` — on the squarefree sector `g = dm`, `gcd(d,m) = 1`,
  `μ(g) = μ(d)μ(m)`;
* `sharedGcd_oneLevel_gram` — the one-level form obtained by pulling out `μ(d)/d`, whose square
  modulus is `1/d²` on the active squarefree support:

  ```
  Q_H = ∑_d λ_H(d)/d² ∑_a ρ(a) | ∑_m μ(m)/m V_{dm}(a) |².
  ```

Banked in §10:

* `abs_lambdaH_le` — `|λ_H(d)| ≤ ∑_{e ∣ d} |μ(d/e)| |Ω_H(e)|`;
* `lambdaH_harmonic_mass_le` — the exact finite convolution inequality

  ```
  ∑_{d ≤ X} |λ_H(d)|/d² ≤ (∑_{e ≤ X} |Ω_H(e)|/e²)(∑_{k ≤ X} |μ(k)|/k²);
  ```

* `omega_support_mass_le` — if `Ω_H` is supported on `e ≥ H` then
  `∑_{e ≤ X} |Ω_H(e)|/e² ≤ (1/H)·∑_{e ≤ X} |Ω_H(e)|/e`, the exact finite avatar of the `1/H`
  saving.  The asymptotic form `∑_d |λ_H(d)|/d² ≪ C/H` is **research metadata only** and is not
  formalised.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset ArithmeticFunction
open scoped BigOperators ComplexConjugate

namespace Erdos287
namespace SharedGcdGram

variable {ι : Type*}

/-! ## §9.1  The projector and its Möbius transform -/

/-- `λ_H = μ ∗ Ω_H` on the divisor lattice. -/
noncomputable def lambdaH (Om : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ x ∈ d.divisorsAntidiagonal, (moebius x.1 : ℝ) * Om x.2

/-- **Möbius inversion.**  `LEAN_PROVED`.  `Ω_H(m) = ∑_{d ∣ m} λ_H(d)` for `m > 0`. -/
theorem sum_lambdaH_divisors (Om : ℕ → ℝ) {m : ℕ} (hm : 0 < m) :
    ∑ d ∈ m.divisors, lambdaH Om d = Om m := by
  refine (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
    (f := lambdaH Om) (g := Om)).2 ?_ m hm
  intro k _
  simp [lambdaH, zsmul_eq_mul]

/-- The finite divisor support of a level set. -/
def divisorSupport (G : Finset ℕ) : Finset ℕ := G.biUnion (fun g => g.divisors)

/-- The `d`-th level slice `{g ∈ G : d ∣ g}`. -/
def levelSlice (G : Finset ℕ) (d : ℕ) : Finset ℕ := G.filter (fun g => d ∣ g)

/-- The cofactors `{g/d : g ∈ G, d ∣ g}`. -/
def cofactorSlice (G : Finset ℕ) (d : ℕ) : Finset ℕ := (levelSlice G d).image (fun g => g / d)

/-- The divisors of `gcd(g₁,g₂)` are exactly the common divisors inside the divisor support. -/
theorem gcd_divisors_eq_filter {G : Finset ℕ} (hG : ∀ g ∈ G, 0 < g) {g1 g2 : ℕ} (h1 : g1 ∈ G) :
    (Nat.gcd g1 g2).divisors = (divisorSupport G).filter (fun d => d ∣ g1 ∧ d ∣ g2) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, divisorSupport, Finset.mem_biUnion,
    Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨hd, -⟩
    exact ⟨⟨g1, h1, hd.1, (hG g1 h1).ne'⟩, hd⟩
  · rintro ⟨-, hd⟩
    exact ⟨hd, Nat.gcd_ne_zero_left (hG g1 h1).ne'⟩

/-- **`Ω_H(gcd(g₁,g₂)) = ∑_{d ∣ g₁, d ∣ g₂} λ_H(d)`.**  `LEAN_PROVED`. -/
theorem omega_gcd_eq_indicator_sum (Om : ℕ → ℝ) {G : Finset ℕ} (hG : ∀ g ∈ G, 0 < g)
    {g1 g2 : ℕ} (h1 : g1 ∈ G) :
    ((Om (Nat.gcd g1 g2) : ℝ) : ℂ)
      = ∑ d ∈ divisorSupport G, (if d ∣ g1 ∧ d ∣ g2 then ((lambdaH Om d : ℝ) : ℂ) else 0) := by
  rw [← Finset.sum_filter, ← gcd_divisors_eq_filter hG h1, ← Complex.ofReal_sum,
    sum_lambdaH_divisors Om (Nat.gcd_pos_of_pos_left _ (hG g1 h1))]

/-! ## §9.2  The Gram functional and the exact square identity -/

/-- The shared-gcd Gram functional

```
Q_H = ∑_{g₁,g₂} w(g₁) conj(w(g₂)) Ω_H(gcd(g₁,g₂)) ∑_a ρ(a) V_{g₁}(a) conj(V_{g₂}(a)).
``` -/
noncomputable def gramSharedGcd (Om : ℕ → ℝ) (G : Finset ℕ) (A : Finset ι) (rho : ι → ℝ)
    (V : ℕ → ι → ℂ) (w : ℕ → ℂ) : ℂ :=
  ∑ g1 ∈ G, ∑ g2 ∈ G, w g1 * conj (w g2) * ((Om (Nat.gcd g1 g2) : ℝ) : ℂ) *
    ∑ a ∈ A, (rho a : ℂ) * V g1 a * conj (V g2 a)

/-- A single level slice assembles into a genuine square. -/
theorem slice_sum_eq_square (A : Finset ι) (rho : ι → ℝ) (V : ℕ → ι → ℂ) (w : ℕ → ℂ)
    (Gd : Finset ℕ) :
    ∑ g1 ∈ Gd, ∑ g2 ∈ Gd, (w g1 * conj (w g2) * ∑ a ∈ A, (rho a : ℂ) * V g1 a * conj (V g2 a))
      = ∑ a ∈ A, (rho a : ℂ) * ((‖∑ g ∈ Gd, w g * V g a‖ : ℝ) : ℂ) ^ 2 := by
  symm
  have hsq : ∀ a : ι, (rho a : ℂ) * ((‖∑ g ∈ Gd, w g * V g a‖ : ℝ) : ℂ) ^ 2
      = ∑ g1 ∈ Gd, ∑ g2 ∈ Gd, (rho a : ℂ) * (w g1 * V g1 a) * conj (w g2 * V g2 a) := by
    intro a
    have h1 : ((‖∑ g ∈ Gd, w g * V g a‖ : ℝ) : ℂ) ^ 2
        = (∑ g ∈ Gd, w g * V g a) * conj (∑ g ∈ Gd, w g * V g a) := by
      rw [Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq]
    rw [h1, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun g1 _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun g2 _ => by ring)
  rw [Finset.sum_congr rfl (fun a _ => hsq a), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun g1 _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun g2 _ => ?_)
  rw [Finset.mul_sum]
  exact (Finset.sum_congr rfl (fun a _ => by simp only [map_mul]; ring)).symm

/-- Restriction of a double sum to a level slice. -/
theorem double_sum_indicator (G : Finset ℕ) (d : ℕ) (c : ℂ) (T : ℕ → ℕ → ℂ) :
    ∑ g1 ∈ G, ∑ g2 ∈ G, (if d ∣ g1 ∧ d ∣ g2 then c else 0) * T g1 g2
      = c * ∑ g1 ∈ levelSlice G d, ∑ g2 ∈ levelSlice G d, T g1 g2 := by
  classical
  rw [Finset.mul_sum, levelSlice, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun g1 _ => ?_)
  rw [Finset.mul_sum, Finset.sum_filter]
  by_cases h1 : d ∣ g1
  · simp only [h1, true_and, if_true]
    refine Finset.sum_congr rfl (fun g2 _ => ?_)
    by_cases h2 : d ∣ g2 <;> simp [h2]
  · simp only [h1, false_and, if_false, zero_mul]
    simp

/-- The shared-gcd weight expands over the level slices: for an arbitrary kernel `T`,

```
∑_{g₁,g₂} Ω_H(gcd(g₁,g₂)) T(g₁,g₂) = ∑_d λ_H(d) ∑_{d ∣ g₁} ∑_{d ∣ g₂} T(g₁,g₂).
``` -/
theorem gram_expand (Om : ℕ → ℝ) {G : Finset ℕ} (hG : ∀ g ∈ G, 0 < g) (T : ℕ → ℕ → ℂ) :
    ∑ g1 ∈ G, ∑ g2 ∈ G, ((Om (Nat.gcd g1 g2) : ℝ) : ℂ) * T g1 g2
      = ∑ d ∈ divisorSupport G, ((lambdaH Om d : ℝ) : ℂ) *
          ∑ g1 ∈ levelSlice G d, ∑ g2 ∈ levelSlice G d, T g1 g2 := by
  classical
  have step1 : ∀ g1 ∈ G, ∀ g2 ∈ G,
      ((Om (Nat.gcd g1 g2) : ℝ) : ℂ) * T g1 g2
        = ∑ d ∈ divisorSupport G,
            (if d ∣ g1 ∧ d ∣ g2 then ((lambdaH Om d : ℝ) : ℂ) else 0) * T g1 g2 := by
    intro g1 h1 g2 _
    rw [← Finset.sum_mul, ← omega_gcd_eq_indicator_sum Om hG h1]
  rw [Finset.sum_congr rfl (fun g1 h1 => Finset.sum_congr rfl (fun g2 h2 => step1 g1 h1 g2 h2))]
  have swap : ∀ g1 ∈ G, ∑ g2 ∈ G, ∑ d ∈ divisorSupport G,
      (if d ∣ g1 ∧ d ∣ g2 then ((lambdaH Om d : ℝ) : ℂ) else 0) * T g1 g2
      = ∑ d ∈ divisorSupport G, ∑ g2 ∈ G,
        (if d ∣ g1 ∧ d ∣ g2 then ((lambdaH Om d : ℝ) : ℂ) else 0) * T g1 g2 :=
    fun _ _ => Finset.sum_comm
  rw [Finset.sum_congr rfl swap, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun d _ => double_sum_indicator G d _ T)

/-- **`DET1-SHAREDGCD-GRAM-SQUARE45`.**  `LEAN_PROVED` (exact).

The shared-gcd Gram functional is an exact `λ_H`-weighted sum of squares:

```
Q_H = ∑_d λ_H(d) ∑_a ρ(a) | ∑_{d ∣ g} w(g) V_g(a) |².
``` -/
theorem sharedGcd_gram_square (Om : ℕ → ℝ) {G : Finset ℕ} (hG : ∀ g ∈ G, 0 < g) (A : Finset ι)
    (rho : ι → ℝ) (V : ℕ → ι → ℂ) (w : ℕ → ℂ) :
    gramSharedGcd Om G A rho V w
      = ∑ d ∈ divisorSupport G, ((lambdaH Om d : ℝ) : ℂ) *
          ∑ a ∈ A, (rho a : ℂ) *
            ((‖∑ g ∈ levelSlice G d, w g * V g a‖ : ℝ) : ℂ) ^ 2 := by
  classical
  have hcomm : gramSharedGcd Om G A rho V w
      = ∑ g1 ∈ G, ∑ g2 ∈ G, ((Om (Nat.gcd g1 g2) : ℝ) : ℂ) *
          (w g1 * conj (w g2) * ∑ a ∈ A, (rho a : ℂ) * V g1 a * conj (V g2 a)) := by
    unfold gramSharedGcd
    exact Finset.sum_congr rfl (fun g1 _ => Finset.sum_congr rfl (fun g2 _ => by ring))
  rw [hcomm, gram_expand Om hG]
  exact Finset.sum_congr rfl
    (fun d _ => by rw [slice_sum_eq_square A rho V w (levelSlice G d)])

/-! ## §9.3  The clean squarefree sector and the one-level form -/

/-- On the clean squarefree sector, `μ(dm) = μ(d)μ(m)`. -/
theorem moebius_split_clean_sector {d m : ℕ} (h : Nat.Coprime d m) :
    (moebius (d * m) : ℤ) = (moebius d : ℤ) * (moebius m : ℤ) := by
  rw [isMultiplicative_moebius.map_mul_of_coprime h]

/-- The level slice, reindexed by cofactors: `μ(d)/d` factors out. -/
theorem levelSlice_sum_factor {G : Finset ℕ} (hG : ∀ g ∈ G, 0 < g)
    (hsq : ∀ g ∈ G, Squarefree g) {d : ℕ} (hd : 0 < d) (V : ℕ → ι → ℂ) (a : ι) :
    ∑ g ∈ levelSlice G d, ((moebius g : ℤ) : ℂ) / (g : ℂ) * V g a
      = ((moebius d : ℤ) : ℂ) / (d : ℂ) *
          ∑ m ∈ cofactorSlice G d, ((moebius m : ℤ) : ℂ) / (m : ℂ) * V (d * m) a := by
  classical
  have hinj : ∀ x ∈ levelSlice G d, ∀ y ∈ levelSlice G d, x / d = y / d → x = y := by
    intro x hx y hy hxy
    simp only [levelSlice, Finset.mem_filter] at hx hy
    calc x = d * (x / d) := (Nat.mul_div_cancel' hx.2).symm
      _ = d * (y / d) := by rw [hxy]
      _ = y := Nat.mul_div_cancel' hy.2
  rw [cofactorSlice, Finset.sum_image (fun x hx y hy h => hinj x hx y hy h), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  simp only [levelSlice, Finset.mem_filter] at hg
  obtain ⟨hgG, hdg⟩ := hg
  have hgpos : 0 < g := hG g hgG
  have hgeq : d * (g / d) = g := Nat.mul_div_cancel' hdg
  have hcop : Nat.Coprime d (g / d) := by
    have hsqg := hsq g hgG
    rw [← hgeq] at hsqg
    exact (Nat.squarefree_mul_iff.1 hsqg).1
  have hmu : (moebius g : ℤ) = (moebius d : ℤ) * (moebius (g / d) : ℤ) := by
    conv_lhs => rw [← hgeq]
    exact moebius_split_clean_sector hcop
  have hdC : ((d : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hqC : (((g / d : ℕ) : ℂ)) ≠ 0 := by
    have : 0 < g / d := Nat.div_pos (Nat.le_of_dvd hgpos hdg) hd
    exact Nat.cast_ne_zero.2 this.ne'
  have hgC : ((g : ℂ)) = (d : ℂ) * ((g / d : ℕ) : ℂ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℂ)) hgeq.symm
  rw [hgeq, hgC]
  rw [show ((moebius g : ℤ) : ℂ) = ((moebius d : ℤ) : ℂ) * ((moebius (g / d) : ℤ) : ℂ) by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hmu]
  field_simp

/-- On the squarefree support, `|μ(d)/d|² = 1/d²`. -/
theorem norm_sq_moebius_div {d : ℕ} (hd : 0 < d) (hsq : Squarefree d) (S : ℂ) :
    ((‖((moebius d : ℤ) : ℂ) / (d : ℂ) * S‖ : ℝ) : ℂ) ^ 2
      = (1 / (d : ℂ) ^ 2) * ((‖S‖ : ℝ) : ℂ) ^ 2 := by
  have habs : ‖((moebius d : ℤ) : ℂ)‖ = 1 := by
    rw [moebius_apply_of_squarefree hsq]
    push_cast
    simp [norm_pow]
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have : ‖((moebius d : ℤ) : ℂ) / (d : ℂ) * S‖ = (1 / (d : ℝ)) * ‖S‖ := by
    rw [norm_mul, norm_div, habs]
    simp
  rw [this]
  push_cast
  rw [mul_pow]
  congr 1
  field_simp

/-- **One-level Gram form.**  `LEAN_PROVED` (exact).

With `w(g) = μ(g)/g` on a squarefree level set,

```
Q_H = ∑_d λ_H(d)/d² ∑_a ρ(a) | ∑_m μ(m)/m V_{dm}(a) |².
``` -/
theorem sharedGcd_oneLevel_gram (Om : ℕ → ℝ) {G : Finset ℕ} (hG : ∀ g ∈ G, 0 < g)
    (hsq : ∀ g ∈ G, Squarefree g) (A : Finset ι) (rho : ι → ℝ) (V : ℕ → ι → ℂ) :
    gramSharedGcd Om G A rho V (fun g => ((moebius g : ℤ) : ℂ) / (g : ℂ))
      = ∑ d ∈ divisorSupport G, ((lambdaH Om d : ℝ) : ℂ) / (d : ℂ) ^ 2 *
          ∑ a ∈ A, (rho a : ℂ) *
            ((‖∑ m ∈ cofactorSlice G d, ((moebius m : ℤ) : ℂ) / (m : ℂ) * V (d * m) a‖ : ℝ) : ℂ)
              ^ 2 := by
  classical
  rw [sharedGcd_gram_square Om hG A rho V _]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  -- `d` divides some element of `G`, hence is positive and squarefree
  obtain ⟨g, hgG, hgd⟩ := Finset.mem_biUnion.1 hd
  rw [Nat.mem_divisors] at hgd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hgd.1 (hG g hgG)
  have hdsq : Squarefree d := (hsq g hgG).squarefree_of_dvd hgd.1
  have hdC : ((d : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hdpos.ne'
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [levelSlice_sum_factor hG hsq hdpos V a, norm_sq_moebius_div hdpos hdsq]
  field_simp

/-! ## §10  The harmonic mass of `λ_H` -/

/-- **`|λ_H(d)| ≤ ∑_{e ∣ d} |μ(d/e)||Ω_H(e)|`.**  `LEAN_PROVED`. -/
theorem abs_lambdaH_le (Om : ℕ → ℝ) (d : ℕ) :
    |lambdaH Om d| ≤ ∑ x ∈ d.divisorsAntidiagonal, |(moebius x.1 : ℝ)| * |Om x.2| := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun x _ => abs_mul _ _)

/-- The divisor antidiagonals of `1,…,X` assemble into the product box cut by `ek ≤ X`. -/
theorem biUnion_divisorsAntidiagonal (X : ℕ) :
    (Finset.Icc 1 X).biUnion (fun d => d.divisorsAntidiagonal)
      = ((Finset.Icc 1 X) ×ˢ (Finset.Icc 1 X)).filter (fun p => p.1 * p.2 ≤ X) := by
  ext p
  obtain ⟨u, v⟩ := p
  simp only [Finset.mem_biUnion, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal, Finset.mem_filter,
    Finset.mem_product]
  constructor
  · rintro ⟨d, ⟨hd1, hdX⟩, hprod, -⟩
    have hu : 1 ≤ u := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hv : 1 ≤ v := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have huv : u * v ≤ X := by omega
    exact ⟨⟨⟨hu, le_trans (Nat.le_mul_of_pos_right _ hv) huv⟩,
      ⟨hv, le_trans (Nat.le_mul_of_pos_left _ hu) huv⟩⟩, huv⟩
  · rintro ⟨⟨⟨hu, -⟩, ⟨hv, -⟩⟩, hle⟩
    have hpos : 0 < u * v := Nat.mul_pos hu hv
    exact ⟨u * v, ⟨hpos, hle⟩, rfl, hpos.ne'⟩

/-- **`DET1-SHAREDGCD-GRAM-SQUARE45`, harmonic mass.**  `LEAN_PROVED` (exact finite form).

```
∑_{d ≤ X} |λ_H(d)|/d² ≤ (∑_{e ≤ X} |Ω_H(e)|/e²) · (∑_{k ≤ X} |μ(k)|/k²).
``` -/
theorem lambdaH_harmonic_mass_le (Om : ℕ → ℝ) (X : ℕ) :
    ∑ d ∈ Finset.Icc 1 X, |lambdaH Om d| / (d : ℝ) ^ 2
      ≤ (∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ) ^ 2) *
        (∑ k ∈ Finset.Icc 1 X, |(moebius k : ℝ)| / (k : ℝ) ^ 2) := by
  classical
  have hpt : ∀ d ∈ Finset.Icc 1 X, |lambdaH Om d| / (d : ℝ) ^ 2
      ≤ ∑ x ∈ d.divisorsAntidiagonal,
          (|(moebius x.1 : ℝ)| / (x.1 : ℝ) ^ 2) * (|Om x.2| / (x.2 : ℝ) ^ 2) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd.1
    have h1 := abs_lambdaH_le Om d
    have h2 : |lambdaH Om d| / (d : ℝ) ^ 2
        ≤ (∑ x ∈ d.divisorsAntidiagonal, |(moebius x.1 : ℝ)| * |Om x.2|) / (d : ℝ) ^ 2 := by
      gcongr
    refine le_trans h2 (le_of_eq ?_)
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Nat.mem_divisorsAntidiagonal] at hx
    have hx1 : (0 : ℝ) < (x.1 : ℝ) := by
      have hne : x.1 ≠ 0 := by rintro h; rw [h] at hx; simp at hx; omega
      exact_mod_cast Nat.pos_of_ne_zero hne
    have hx2 : (0 : ℝ) < (x.2 : ℝ) := by
      have hne : x.2 ≠ 0 := by rintro h; rw [h] at hx; simp at hx; omega
      exact_mod_cast Nat.pos_of_ne_zero hne
    have hdd : (d : ℝ) = (x.1 : ℝ) * (x.2 : ℝ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hx.1.symm
    rw [hdd]
    field_simp
  refine le_trans (Finset.sum_le_sum hpt) ?_
  have hdisj : (↑(Finset.Icc 1 X) : Set ℕ).PairwiseDisjoint
      (fun d => d.divisorsAntidiagonal) := by
    intro a _ b _ hab
    simp only [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    rw [Nat.mem_divisorsAntidiagonal] at hp hp'
    exact hab (hp.1.symm.trans hp'.1)
  rw [← Finset.sum_biUnion hdisj, biUnion_divisorsAntidiagonal X]
  have hsub : ((Finset.Icc 1 X) ×ˢ (Finset.Icc 1 X)).filter (fun p => p.1 * p.2 ≤ X)
      ⊆ (Finset.Icc 1 X) ×ˢ (Finset.Icc 1 X) := Finset.filter_subset _ _
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)) ?_
  rw [Finset.sum_product]
  refine le_of_eq ?_
  rw [mul_comm, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun k _ => by simp only [Finset.mul_sum])

/-- **Support form of the `1/H` saving.**  `LEAN_PROVED` (exact finite form).

If `Ω_H` vanishes below `H`, then its harmonic mass at weight `e⁻²` is at most `1/H` times its
mass at weight `e⁻¹`.  The asymptotic statement `∑_d |λ_H(d)|/d² ≪ C/H` is research metadata
only. -/
theorem omega_support_mass_le (Om : ℕ → ℝ) {H : ℕ} (hH : 0 < H)
    (hsupp : ∀ e, e < H → Om e = 0) (X : ℕ) :
    ∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ) ^ 2
      ≤ (1 / (H : ℝ)) * ∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun e he => ?_)
  rw [Finset.mem_Icc] at he
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he.1
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  by_cases hlt : e < H
  · rw [hsupp e hlt]
    simp
  · have hHe : (H : ℝ) ≤ (e : ℝ) := by exact_mod_cast Nat.le_of_not_lt hlt
    have h1 : |Om e| / (e : ℝ) ^ 2 = (|Om e| / (e : ℝ)) * (1 / (e : ℝ)) := by
      field_simp
    have h2 : (1 / (H : ℝ)) * (|Om e| / (e : ℝ)) = (|Om e| / (e : ℝ)) * (1 / (H : ℝ)) := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hHpos hHe)
      (by positivity)

end SharedGcdGram
end Erdos287
