import RequestProject.Erdos287.ResearchBankV9.GcdClique

/-!
# Erdős #287 — Research Bank V9 §4F: the small-overlap zero-mode kernel

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For moduli `m₁, m₂ ≥ 1`, `g = gcd(m₁, m₂)`, `L = lcm(m₁, m₂)`, and `n₁, n₂` units modulo
`m₁, m₂` respectively, kernel-proved (`zeroMode_card`, `zeroMode_density`): the number of
`x ∈ [0, L)` with `x n₁ ≡ c₁ (mod m₁)` and `x n₂ ≡ c₂ (mod m₂)` is exactly
`1_{c₁ n₂ ≡ c₂ n₁ (mod g)}`, so

  `D₁₁(n₁, n₂) = (1/L) · 1_{c₁ n₂ ≡ c₂ n₁ (mod g)}`.

With inverses guarded by unit hypotheses, the indicator is the ratio indicator
`1_{n₁ n₂⁻¹ ≡ c₁ c₂⁻¹ (mod g)}` (`compat_iff_ratio`).  The principal density is `(1/L)(1/φ(g))`,
the average of the ratio indicator over the unit classes (`ratio_indicator_average`), and the
centred kernel is `(1/L)[1_{ratio} − 1/φ(g)]` (`centred_kernel_eq`), which sums to zero over unit
classes (`centred_kernel_sum_zero`).

The external interface `ZhengRatioBVInput` (Zheng's ratio-form generalized Bombieri–Vinogradov
estimate) is never inhabited; `smallOverlap_zeroFrequency_bound` proves
interface ⟹ small-overlap zero-frequency bound.
-/

open scoped BigOperators

namespace Erdos287
namespace ResearchBankV9
namespace AsraZeroMode

/-- The solution set in `[0, L)` of the two linear congruences. -/
def solSet (m₁ m₂ : ℕ) (n₁ n₂ c₁ c₂ : ℤ) : Finset ℤ :=
  (Finset.Ico 0 (Nat.lcm m₁ m₂ : ℤ)).filter fun x =>
    (m₁ : ℤ) ∣ x * n₁ - c₁ ∧ (m₂ : ℤ) ∣ x * n₂ - c₂

/-- The compatibility condition `c₁ n₂ ≡ c₂ n₁ (mod g)`. -/
def Compat (m₁ m₂ : ℕ) (n₁ n₂ c₁ c₂ : ℤ) : Prop :=
  ((Nat.gcd m₁ m₂ : ℕ) : ℤ) ∣ c₁ * n₂ - c₂ * n₁

theorem lcm_dvd_int {m₁ m₂ : ℕ} {z : ℤ} (h₁ : (m₁ : ℤ) ∣ z) (h₂ : (m₂ : ℤ) ∣ z) :
    ((Nat.lcm m₁ m₂ : ℕ) : ℤ) ∣ z := by
  rw [Int.natCast_dvd] at h₁ h₂ ⊢
  exact Nat.lcm_dvd h₁ h₂

section
variable {m₁ m₂ : ℕ} {n₁ n₂ c₁ c₂ : ℤ}

theorem sol_unique (hu₁ : IsCoprime n₁ m₁) (hu₂ : IsCoprime n₂ m₂)
    {x y : ℤ} (hx : x ∈ solSet m₁ m₂ n₁ n₂ c₁ c₂) (hy : y ∈ solSet m₁ m₂ n₁ n₂ c₁ c₂) :
    x = y := by
  simp only [solSet, Finset.mem_filter, Finset.mem_Ico] at hx hy
  have h₁ : (m₁ : ℤ) ∣ x - y := by
    have := dvd_sub hx.2.1 hy.2.1
    rw [show x * n₁ - c₁ - (y * n₁ - c₁) = (x - y) * n₁ by ring] at this
    exact hu₁.symm.dvd_of_dvd_mul_right this
  have h₂ : (m₂ : ℤ) ∣ x - y := by
    have := dvd_sub hx.2.2 hy.2.2
    rw [show x * n₂ - c₂ - (y * n₂ - c₂) = (x - y) * n₂ by ring] at this
    exact hu₂.symm.dvd_of_dvd_mul_right this
  have := Int.eq_zero_of_abs_lt_dvd (lcm_dvd_int h₁ h₂)
    (by rw [abs_lt]; constructor <;> linarith)
  linarith

theorem compat_of_sol {x : ℤ} (hx : x ∈ solSet m₁ m₂ n₁ n₂ c₁ c₂) : Compat m₁ m₂ n₁ n₂ c₁ c₂ := by
  simp only [solSet, Finset.mem_filter] at hx
  have g₁ : ((Nat.gcd m₁ m₂ : ℕ) : ℤ) ∣ x * n₁ - c₁ :=
    (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)).trans hx.2.1
  have g₂ : ((Nat.gcd m₁ m₂ : ℕ) : ℤ) ∣ x * n₂ - c₂ :=
    (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)).trans hx.2.2
  have := dvd_sub (dvd_mul_of_dvd_left g₂ n₁) (dvd_mul_of_dvd_left g₁ n₂)
  unfold Compat
  rwa [show (x * n₂ - c₂) * n₁ - (x * n₁ - c₁) * n₂ = c₁ * n₂ - c₂ * n₁ by ring] at this

theorem sol_exists (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hu₁ : IsCoprime n₁ m₁) (hu₂ : IsCoprime n₂ m₂)
    (hc : Compat m₁ m₂ n₁ n₂ c₁ c₂) : ∃ x, x ∈ solSet m₁ m₂ n₁ n₂ c₁ c₂ := by
  obtain ⟨u₁, v₁, e₁⟩ := hu₁
  obtain ⟨u₂, v₂, e₂⟩ := hu₂
  have hcomp : ((Nat.gcd m₁ m₂ : ℕ) : ℤ) ∣ c₁ * u₁ - c₂ * u₂ := by
    have g₁ : ((Nat.gcd m₁ m₂ : ℕ) : ℤ) ∣ (m₁ : ℤ) := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)
    have g₂ : ((Nat.gcd m₁ m₂ : ℕ) : ℤ) ∣ (m₂ : ℤ) := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)
    have := dvd_add (dvd_add (dvd_mul_of_dvd_right hc (u₁ * u₂))
      (dvd_mul_of_dvd_right g₂ (c₁ * u₁ * v₂))) (dvd_mul_of_dvd_right g₁ (-(c₂ * u₂ * v₁)))
    have e : u₁ * u₂ * (c₁ * n₂ - c₂ * n₁) + c₁ * u₁ * v₂ * m₂ + -(c₂ * u₂ * v₁) * m₁ =
        c₁ * u₁ - c₂ * u₂ := by
      linear_combination (c₁ * u₁) * e₂ - (c₂ * u₂) * e₁
    rwa [e] at this
  obtain ⟨y, hy₁, hy₂⟩ := GcdClique.two_crt (c₁ * u₁) (c₂ * u₂) m₁ m₂ hcomp
  have hL : (0 : ℤ) < (Nat.lcm m₁ m₂ : ℕ) := by
    exact_mod_cast Nat.lcm_pos hm₁ hm₂
  set x := y % ((Nat.lcm m₁ m₂ : ℕ) : ℤ)
  have hxy : ((Nat.lcm m₁ m₂ : ℕ) : ℤ) ∣ x - y := by
    refine ⟨-(y / ((Nat.lcm m₁ m₂ : ℕ) : ℤ)), ?_⟩
    have := Int.emod_add_mul_ediv y ((Nat.lcm m₁ m₂ : ℕ) : ℤ); linarith
  have hx₁ : (m₁ : ℤ) ∣ x - y := (Int.natCast_dvd_natCast.2 (Nat.dvd_lcm_left _ _)).trans hxy
  have hx₂ : (m₂ : ℤ) ∣ x - y := (Int.natCast_dvd_natCast.2 (Nat.dvd_lcm_right _ _)).trans hxy
  refine ⟨x, ?_⟩
  simp only [solSet, Finset.mem_filter, Finset.mem_Ico]
  refine ⟨⟨Int.emod_nonneg _ hL.ne', Int.emod_lt_of_pos _ hL⟩, ?_, ?_⟩
  · have := dvd_add (dvd_add (dvd_mul_of_dvd_left hx₁ n₁) (dvd_mul_of_dvd_left hy₁ n₁))
      (dvd_mul_of_dvd_left (dvd_refl (m₁ : ℤ)) (-(c₁ * v₁)))
    rwa [show (x - y) * n₁ + (y - c₁ * u₁) * n₁ + (m₁ : ℤ) * (-(c₁ * v₁)) = x * n₁ - c₁ by
      linear_combination (-c₁) * e₁] at this
  · have := dvd_add (dvd_add (dvd_mul_of_dvd_left hx₂ n₂) (dvd_mul_of_dvd_left hy₂ n₂))
      (dvd_mul_of_dvd_left (dvd_refl (m₂ : ℤ)) (-(c₂ * v₂)))
    rwa [show (x - y) * n₂ + (y - c₂ * u₂) * n₂ + (m₂ : ℤ) * (-(c₂ * v₂)) = x * n₂ - c₂ by
      linear_combination (-c₂) * e₂] at this

/-- **The zero-mode count** `#{x ∈ [0, L) : …} = 1_{c₁ n₂ ≡ c₂ n₁ (mod g)}`. -/
theorem zeroMode_card (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hu₁ : IsCoprime n₁ m₁)
    (hu₂ : IsCoprime n₂ m₂) [Decidable (Compat m₁ m₂ n₁ n₂ c₁ c₂)] :
    (solSet m₁ m₂ n₁ n₂ c₁ c₂).card = if Compat m₁ m₂ n₁ n₂ c₁ c₂ then 1 else 0 := by
  split_ifs with hc
  · obtain ⟨x, hx⟩ := sol_exists hm₁ hm₂ hu₁ hu₂ hc
    rw [Finset.card_eq_one]
    exact ⟨x, Finset.eq_singleton_iff_unique_mem.2
      ⟨hx, fun y hy => sol_unique hu₁ hu₂ hy hx⟩⟩
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    exact fun x hx => hc (compat_of_sol hx)

/-- **The zero-mode compatibility density** `D₁₁ = (1/L) · 1_{c₁ n₂ ≡ c₂ n₁ (mod g)}`. -/
theorem zeroMode_density (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hu₁ : IsCoprime n₁ m₁)
    (hu₂ : IsCoprime n₂ m₂) [Decidable (Compat m₁ m₂ n₁ n₂ c₁ c₂)] :
    ((solSet m₁ m₂ n₁ n₂ c₁ c₂).card : ℚ) / (Nat.lcm m₁ m₂ : ℕ) =
      (1 / (Nat.lcm m₁ m₂ : ℕ)) * (if Compat m₁ m₂ n₁ n₂ c₁ c₂ then 1 else 0) := by
  rw [zeroMode_card hm₁ hm₂ hu₁ hu₂]
  split_ifs <;> simp

end

/-- **Ratio form (inverses guarded by unit hypotheses).**  In `ZMod g`, with `n₂ ↦ v₂` and
`c₂ ↦ w₂` units: `c₁ n₂ ≡ c₂ n₁ (mod g)` iff `n₁ n₂⁻¹ = c₁ c₂⁻¹`. -/
theorem compat_iff_ratio {g : ℕ} {n₁ n₂ c₁ c₂ : ℤ} (v₂ w₂ : (ZMod g)ˣ)
    (hv : ((n₂ : ZMod g)) = v₂) (hw : ((c₂ : ZMod g)) = w₂) :
    ((g : ℤ) ∣ c₁ * n₂ - c₂ * n₁) ↔
      (n₁ : ZMod g) * (v₂⁻¹ : (ZMod g)ˣ) = (c₁ : ZMod g) * (w₂⁻¹ : (ZMod g)ˣ) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [hv, hw, sub_eq_zero]
  constructor
  · intro h
    calc (n₁ : ZMod g) * ↑v₂⁻¹ = (n₁ : ZMod g) * ↑v₂⁻¹ * (↑w₂ * ↑w₂⁻¹) := by simp
      _ = (↑w₂ * n₁) * ↑v₂⁻¹ * ↑w₂⁻¹ := by ring
      _ = (c₁ * ↑v₂) * ↑v₂⁻¹ * ↑w₂⁻¹ := by rw [← h]
      _ = c₁ * ↑w₂⁻¹ := by simp [mul_assoc]
  · intro h
    calc (c₁ : ZMod g) * ↑v₂ = (c₁ * ↑w₂⁻¹) * ↑w₂ * ↑v₂ := by simp [mul_assoc]
      _ = ((n₁ : ZMod g) * ↑v₂⁻¹) * ↑w₂ * ↑v₂ := by rw [h]
      _ = ↑w₂ * n₁ := by
        rw [mul_assoc, mul_assoc, mul_comm (↑w₂ : ZMod g) ↑v₂, ← mul_assoc (↑v₂⁻¹ : ZMod g)]
        simp [mul_comm]

/-- The principal density `(1/L)(1/φ(g))`. -/
def principal (L g : ℕ) : ℚ := (1 / L) * (1 / Nat.totient g)

/-- The centred kernel `(1/L)[1_{ratio} − 1/φ(g)]`. -/
def centredKernel (L g : ℕ) (ind : ℚ) : ℚ := (1 / L) * (ind - 1 / Nat.totient g)

/-- **The centred kernel** is `D₁₁` minus the principal density. -/
theorem centred_kernel_eq (L g : ℕ) (ind : ℚ) :
    (1 / (L : ℚ)) * ind - principal L g = centredKernel L g ind := by
  unfold principal centredKernel; ring

/-- **The principal density is the unit-class average** of the ratio indicator. -/
theorem ratio_indicator_average (g : ℕ) [NeZero g] (w : (ZMod g)ˣ) :
    (∑ v : (ZMod g)ˣ, (if v = w then (1 : ℚ) else 0)) / Nat.totient g = 1 / Nat.totient g := by
  simp

/-- **The centred kernel sums to zero over the unit classes.** -/
theorem centred_kernel_sum_zero (L g : ℕ) [NeZero g] (w : (ZMod g)ˣ) :
    ∑ v : (ZMod g)ˣ, centredKernel L g (if v = w then 1 else 0) = 0 := by
  unfold centredKernel
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    ZMod.card_units_eq_totient, nsmul_eq_mul]
  have hg : 0 < Nat.totient g := Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne g))
  have : (Nat.totient g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  field_simp
  ring

/-- **External interface (Zheng's ratio-form generalized Bombieri–Vinogradov estimate) — never
inhabited here.**  The weighted sum of centred kernels over a small-overlap family is `≤ E`. -/
structure ZhengRatioBVInput {ι : Type*} (Q : Finset ι) (coef : ι → ℚ) (L g : ι → ℕ)
    (ind : ι → ℚ) (E : ℚ) : Prop where
  /-- The ratio-form generalized BV bound. -/
  bound : |∑ q ∈ Q, coef q * centredKernel (L q) (g q) (ind q)| ≤ E

/-- The small-overlap zero-frequency ASRA term: `∑ coef · (D₁₁ − principal)`. -/
def zeroFrequencyTerm {ι : Type*} (Q : Finset ι) (coef : ι → ℚ) (L g : ι → ℕ) (ind : ι → ℚ) :
    ℚ := ∑ q ∈ Q, coef q * ((1 / (L q : ℚ)) * ind q - principal (L q) (g q))

/-- **Interface ⟹ small-overlap zero-frequency ASRA bound** (internal proof). -/
theorem smallOverlap_zeroFrequency_bound {ι : Type*} (Q : Finset ι) (coef : ι → ℚ)
    (L g : ι → ℕ) (ind : ι → ℚ) (E : ℚ) (hin : ZhengRatioBVInput Q coef L g ind E) :
    |zeroFrequencyTerm Q coef L g ind| ≤ E := by
  unfold zeroFrequencyTerm
  simp only [centred_kernel_eq]
  exact hin.bound

end AsraZeroMode
end ResearchBankV9
end Erdos287
