import RequestProject.Erdos287.SourceChain.Physical.Scalar.Bound
import RequestProject.Erdos287.SourceChain.Physical.TypeII.OrderingB

/-!
# Erdős #287 — Type-II source: the physical coefficient `c_{ξ,l,r}`

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

The Type-II coefficient is generated from the *actual* scalar coefficient `ℓ_X`
(`Sieve.ScalarParams.ellX`) through a factorization rule `d ↦ (l, r)`:

`c_{ξ,l,r} = Γ_ξ · ℓ_X(l r) · 1[σ(l r) = (l, r)] · 1[(f_ξ, l r) = 1]`.

* `SplitRule` — a map `σ : ℕ → ℕ × ℕ` with `σ(d) = (l, r) ⇒ l r = d`, `(l, r) = 1`.
  The physical source (Pascadi Prop. 5.2) only asserts the *existence* of an
  anatomy-dependent well-factorable split; its precise choice is **not** pinned down by the
  source, so it is kept as an explicit parameter here (this is the BLOCKED item of the report).
* `physCoef_abs_le` — `|c_{ξ,l,r}| ≤ |Γ_ξ| (T² + 1)`.
* `physCoef_coprime` — every nonzero coefficient has `(l, r) = 1`, so `typeII_split_Z`
  applies to it.
* `physCoef_reassemble` — **lossless reassembly**: for any test function `g`,
  `∑_{l,r} c_{ξ,l,r} g(l r) 1[l r < K] = Γ_ξ ∑_{1 ≤ d < K} 1[(f_ξ,d)=1] ℓ_X(d) g(d)`:
  each scalar term `ℓ_X(d)` is counted exactly once, with no new weights introduced.
-/

open scoped BigOperators
open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII

/-- A factorization rule `d ↦ (l, r)` with `l r = d` and `(l, r) = 1`. -/
structure SplitRule where
  σ : ℕ → ℕ × ℕ
  mul_eq : ∀ d, (σ d).1 * (σ d).2 = d
  coprime : ∀ d, Nat.Coprime (σ d).1 (σ d).2

open Classical in
/-- **The physical Type-II coefficient**
`c_{ξ,l,r} = Γ_ξ ℓ_X(l r) 1[σ(l r) = (l,r)] 1[(f_ξ, l r) = 1]`. -/
noncomputable def physCoef (S : Sieve.ScalarParams) (σ : SplitRule) (Γ : ℝ) (f : ℕ)
    (l r : ℕ) : ℝ :=
  if σ.σ (l * r) = (l, r) ∧ Nat.Coprime f (l * r) then Γ * S.ellX (l * r) else 0

theorem physCoef_abs_le {S : Sieve.ScalarParams} (hS : S.Good) (σ : SplitRule) (Γ : ℝ)
    (f l r : ℕ) : |physCoef S σ Γ f l r| ≤ |Γ| * ((S.T : ℝ) ^ 2 + 1) := by
  unfold physCoef
  split_ifs
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (Sieve.ScalarParams.abs_ellX_le hS _) (abs_nonneg _)
  · simp only [abs_zero]; positivity

theorem physCoef_coprime {S : Sieve.ScalarParams} {σ : SplitRule} {Γ : ℝ} {f l r : ℕ}
    (h : physCoef S σ Γ f l r ≠ 0) : Nat.Coprime l r ∧ Nat.Coprime f (l * r) := by
  unfold physCoef at h
  split_ifs at h with hc
  · refine ⟨?_, hc.2⟩
    have := σ.coprime (l * r)
    rwa [hc.1] at this
  · exact absurd rfl h

/-- **Lossless reassembly** of the scalar coefficient from the Type-II coefficients. -/
theorem physCoef_reassemble (S : Sieve.ScalarParams) (σ : SplitRule) (Γ : ℝ) (f K : ℕ)
    (g : ℕ → ℝ) :
    ∑ l ∈ Ico 1 K, ∑ r ∈ Ico 1 K,
        (if l * r < K then physCoef S σ Γ f l r * g (l * r) else 0) =
      Γ * ∑ d ∈ Ico 1 K, if Nat.Coprime f d then S.ellX d * g d else 0 := by
  classical
  set G : ℕ → ℝ := fun d => if Nat.Coprime f d then Γ * S.ellX d * g d else 0 with hG
  have hσmem : ∀ d ∈ Ico 1 K, σ.σ d ∈ Ico 1 K ×ˢ Ico 1 K := by
    intro d hd
    rw [mem_Ico] at hd
    have hm := σ.mul_eq d
    have h1 : (σ.σ d).1 ≠ 0 := by intro h; rw [h, zero_mul] at hm; omega
    have h2 : (σ.σ d).2 ≠ 0 := by intro h; rw [h, mul_zero] at hm; omega
    have hl := Nat.le_mul_of_pos_right (σ.σ d).1 (Nat.pos_of_ne_zero h2)
    have hr := Nat.le_mul_of_pos_left (σ.σ d).2 (Nat.pos_of_ne_zero h1)
    simp only [mem_product, mem_Ico]
    omega
  have hR : Γ * ∑ d ∈ Ico 1 K, (if Nat.Coprime f d then S.ellX d * g d else 0) =
      ∑ d ∈ Ico 1 K, ∑ x ∈ Ico 1 K ×ˢ Ico 1 K, if σ.σ d = x then G (x.1 * x.2) else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [Finset.sum_ite_eq, if_pos (hσmem d hd), σ.mul_eq d, hG]
    simp only
    split_ifs <;> ring
  rw [hR]
  conv_rhs => rw [Finset.sum_comm, Finset.sum_product]
  refine Finset.sum_congr rfl (fun l hl => Finset.sum_congr rfl (fun r hr => ?_))
  rw [mem_Ico] at hl hr
  have hfib : ∀ d ∈ Ico 1 K, (if σ.σ d = (l, r) then G ((l, r).1 * (l, r).2) else 0) =
      if d = l * r then (if σ.σ (l * r) = (l, r) then G (l * r) else 0) else 0 := by
    intro d _
    by_cases h : σ.σ d = (l, r)
    · have hd : d = l * r := by rw [← σ.mul_eq d, h]
      subst hd; simp [h]
    · rw [if_neg h]
      by_cases hd : d = l * r
      · subst hd; simp [h]
      · simp [hd]
  rw [Finset.sum_congr rfl hfib, Finset.sum_ite_eq']
  have hpos : 1 ≤ l * r := Nat.mul_pos (by omega) (by omega)
  by_cases hK : l * r < K
  · rw [if_pos hK, if_pos (mem_Ico.2 ⟨hpos, hK⟩)]
    unfold physCoef
    simp only [hG]
    by_cases h1 : σ.σ (l * r) = (l, r) <;> by_cases h2 : Nat.Coprime f (l * r) <;> simp [h1, h2]
  · rw [if_neg hK, if_neg (by rw [mem_Ico]; omega)]

end Erdos287.Physical.TypeII
