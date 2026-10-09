import RequestProject.Erdos287.SourceChain.Physical.Scalar.Majorant

/-!
# Erdős #287 — scalar sieve: total-variation bound

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

`abs_ellX_le` — `|ℓ_X(d)| ≤ ε₀^{-2} + 1 = T² + 1` for every `d`: in each parity sector the
low/high split `d = b·a` is unique (`b` = product of the low prime factors), so each sector
contributes at most one term of size `≤ 1`.  The bound is independent of `X` (§17: "the total
variation is independent of `X` after fixing the scalar parameters").
-/

open scoped BigOperators
open Finset

namespace Erdos287.Physical.Sieve

theorem abs_sum_le_one_of_unique {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (huniq : ∀ x ∈ s, ∀ y ∈ s, f x ≠ 0 → f y ≠ 0 → x = y) (hle : ∀ x ∈ s, |f x| ≤ 1) :
    |∑ x ∈ s, f x| ≤ 1 := by
  by_cases h : ∃ x ∈ s, f x ≠ 0
  · obtain ⟨x, hx, hfx⟩ := h
    rw [Finset.sum_eq_single x (fun y hy hyx => by
      by_contra hne; exact hyx (huniq y hy x hx hne hfx)) (fun h => absurd hx h)]
    exact hle x hx
  · push_neg at h
    rw [Finset.sum_eq_zero h]; simp

namespace ScalarParams

variable {S : ScalarParams}

theorem abs_kappa_le (J b : ℕ) : |S.kappa J b| ≤ 1 := by
  have hμ : |(ArithmeticFunction.moebius b : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  unfold kappa
  split_ifs
  · unfold lamLowPlus; split_ifs
    · exact hμ
    · simp
  · unfold lamLowMinus; split_ifs
    · exact hμ
    · simp

theorem hw_le_one (J a : ℕ) : S.hw J a ≤ 1 := by
  classical
  unfold hw; split_ifs <;> norm_num

/-- The low part of a support element is determined by `d`. -/
theorem low_part_unique (hS : S.Good) {J d : ℕ} {x y : ℕ × ℕ}
    (hx : x ∈ d.divisorsAntidiagonal) (hy : y ∈ d.divisorsAntidiagonal)
    (hfx : S.kappa J x.1 * S.hw J x.2 ≠ 0) (hfy : S.kappa J y.1 * S.hw J y.2 ≠ 0) : x = y := by
  classical
  obtain ⟨hxm, hd0⟩ := Nat.mem_divisorsAntidiagonal.1 hx
  obtain ⟨hym, -⟩ := Nat.mem_divisorsAntidiagonal.1 hy
  have key : ∀ z : ℕ × ℕ, z.1 * z.2 = d → S.kappa J z.1 * S.hw J z.2 ≠ 0 →
      z.1 = ∏ p ∈ d.primeFactors.filter (fun p : ℕ => (p : ℝ) < S.u0), p := by
    intro z hz hf
    have hk : S.kappa J z.1 ≠ 0 := fun h0 => hf (by rw [h0, zero_mul])
    have hh : S.hw J z.2 ≠ 0 := fun h0 => hf (by rw [h0, mul_zero])
    obtain ⟨hsq, hlow⟩ := kappa_support hk
    obtain ⟨⟨hsqa, hhigh, -⟩, -⟩ := hw_support hh
    have hz1 : z.1 ≠ 0 := hsq.ne_zero
    have hz2 : z.2 ≠ 0 := hsqa.ne_zero
    have hpf : z.1.primeFactors = d.primeFactors.filter (fun p : ℕ => (p : ℝ) < S.u0) := by
      rw [← hz, Nat.primeFactors_mul hz1 hz2]
      ext p
      simp only [mem_filter, mem_union]
      constructor
      · intro hp; exact ⟨Or.inl hp, hlow p hp⟩
      · rintro ⟨hp | hp, hlt⟩
        · exact hp
        · exact absurd hlt (not_low_of_high hS (hhigh p hp))
    rw [← hpf, Nat.prod_primeFactors_of_squarefree hsq]
  have h1 := key x hxm hfx
  have h2 := key y hym hfy
  have hx1 : x.1 ≠ 0 := by
    intro h; rw [h, zero_mul] at hxm; exact hd0 hxm.symm
  have heq1 : x.1 = y.1 := h1.trans h2.symm
  have heq2 : x.2 = y.2 := by
    have : x.1 * x.2 = x.1 * y.2 := by rw [hxm, heq1, hym]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hx1) this
  exact Prod.ext heq1 heq2

/-- **Total variation**: `|ℓ_X(d)| ≤ T² + 1`, independent of `X`. -/
theorem abs_ellX_le (hS : S.Good) (d : ℕ) : |S.ellX d| ≤ (S.T : ℝ) ^ 2 + 1 := by
  rw [ellX_eq_setForm hS]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ J ∈ range (S.T ^ 2 + 1), |(-1 : ℝ) ^ J *
      ∑ x ∈ d.divisorsAntidiagonal, S.kappa J x.1 * S.hw J x.2| ≤ 1 := by
    intro J _
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    apply abs_sum_le_one_of_unique
    · intro x hx y hy hfx hfy; exact low_part_unique hS hx hy hfx hfy
    · intro x _
      rw [abs_mul, abs_of_nonneg (hw_nonneg J x.2)]
      have h1 := abs_kappa_le (S := S) J x.1
      have h2 := hw_le_one (S := S) J x.2
      have h3 := hw_nonneg (S := S) J x.2
      nlinarith [abs_nonneg (S.kappa J x.1)]
  refine (Finset.sum_le_sum this).trans ?_
  simp

end ScalarParams

end Erdos287.Physical.Sieve
