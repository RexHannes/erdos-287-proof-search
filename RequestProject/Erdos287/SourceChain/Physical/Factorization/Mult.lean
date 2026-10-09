import RequestProject.Erdos287.SourceChain.Physical.Factorization.Prop52

/-!
# Erdős #287 — Pascadi's Proposition 5.2, multiplicative form

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

`prop52_real`: for a decreasing sequence of reals `P₀ ≥ P₁ ≥ ⋯ ≥ 1` (primes, or box upper
endpoints, padded by `1`) in Pascadi's `𝒟⁺_r(D)` with `D = x^{3/5-50δ}`, and every published
parameter condition `0 < δ < 10⁻⁵`, `x^{2δ} ≤ N ≤ x^{1/3+δ}`, the greedy colouring gives

`d₁ ≤ N x^{-δ}`, `N² d₂ d₃² ≤ x^{1-δ}`, `N² d₂⁵ d₃² ≤ x^{2-δ}` (Pascadi (5.3)),

where `d_k` is the product of the `P_i` of colour `k`.  It is obtained from `prop52_additive`
by passing to `t_i = log_x P_i`.
-/

open Finset Real

set_option autoImplicit false

namespace Erdos287.Physical.Factor

/-- The colour-`k` factor `d_k = ∏_{i < R, c i = k} P_i`. -/
noncomputable def cprod (P : ℕ → ℝ) (c : ℕ → Fin 3) (k : Fin 3) (R : ℕ) : ℝ :=
  ∏ i ∈ (range R).filter (fun i => c i = k), P i

/-- Pascadi's hypotheses of Prop. 5.2, multiplicatively (`𝒟⁺_r(D)` for a real vector). -/
structure MultHyp (x δ N : ℝ) (P : ℕ → ℝ) : Prop where
  x_gt : 1 < x
  δ_pos : 0 < δ
  δ_small : δ < 1 / 100000
  N_lo : x ^ (2 * δ) ≤ N
  N_hi : N ≤ x ^ (1 / 3 + δ)
  one_le : ∀ i, 1 ≤ P i
  anti : Antitone P
  plus : ∀ j, Even j → (∏ i ∈ range j, P i) * P j ^ 3 ≤ x ^ (3 / 5 - 50 * δ)

/-- Pascadi's system (5.3). -/
def Sys53 (x δ N d₁ d₂ d₃ : ℝ) : Prop :=
  d₁ ≤ N * x ^ (-δ) ∧ N ^ 2 * d₂ * d₃ ^ 2 ≤ x ^ (1 - δ) ∧ N ^ 2 * d₂ ^ 5 * d₃ ^ 2 ≤ x ^ (2 - δ)

/-- **Pascadi, Proposition 5.2** (real-vector form, constructive greedy proof). -/
theorem prop52_real {x δ N : ℝ} {P : ℕ → ℝ} (h : MultHyp x δ N P) (R : ℕ) :
    ∃ c : ℕ → Fin 3, Sys53 x δ N (cprod P c 0 R) (cprod P c 1 R) (cprod P c 2 R) := by
  have hx := h.x_gt
  have hx0 : 0 < x := by linarith
  have hx1 : x ≠ 1 := ne_of_gt hx
  have hP0 : ∀ i, 0 < P i := fun i => lt_of_lt_of_le one_pos (h.one_le i)
  have hN0 : 0 < N := lt_of_lt_of_le (rpow_pos_of_pos hx0 _) h.N_lo
  set t : ℕ → ℝ := fun i => logb x (P i) with ht
  set n : ℝ := logb x N with hn
  have hlogb : ∀ a, logb x (x ^ a) = a := fun a => logb_rpow hx0 hx1
  have hA : AddHyp δ n t := by
    refine ⟨h.δ_pos, h.δ_small, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hlogb (2 * δ)]
      exact (logb_le_logb hx (rpow_pos_of_pos hx0 _) hN0).2 h.N_lo
    · rw [← hlogb (1 / 3 + δ)]
      exact (logb_le_logb hx hN0 (rpow_pos_of_pos hx0 _)).2 h.N_hi
    · intro i; exact logb_nonneg hx (h.one_le i)
    · intro i j hij; exact (logb_le_logb hx (hP0 j) (hP0 i)).2 (h.anti hij)
    · intro j hj
      have hpj := h.plus j hj
      have hprod : 0 < ∏ i ∈ range j, P i := prod_pos (fun i _ => hP0 i)
      have hL := (logb_le_logb hx (mul_pos hprod (pow_pos (hP0 j) 3))
        (rpow_pos_of_pos hx0 _)).2 hpj
      rw [hlogb, logb_mul hprod.ne' (pow_pos (hP0 j) 3).ne', logb_pow,
        logb_prod _ _ (fun i _ => (hP0 i).ne')] at hL
      push_cast at hL
      exact hL
  obtain ⟨c, h1, h2, h3⟩ := prop52_additive hA R
  have hcp : ∀ k, cprod P c k R = x ^ csumS t c k (range R) := by
    intro k
    unfold cprod csumS
    rw [rpow_sum_of_pos hx0]
    exact prod_congr rfl (fun i _ => (rpow_logb hx0 hx1 (hP0 i)).symm)
  have hN : N = x ^ n := (rpow_logb hx0 hx1 hN0).symm
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [hcp, hN, ← rpow_add hx0]
    exact (rpow_le_rpow_left_iff hx).2 (by linarith)
  · rw [hcp, hcp, hN]
    set a2 := csumS t c 1 (range R)
    set a3 := csumS t c 2 (range R)
    have e : (x ^ n) ^ 2 * x ^ a2 * (x ^ a3) ^ 2 = x ^ (n + n + a2 + a3 + a3) := by
      rw [rpow_add hx0, rpow_add hx0, rpow_add hx0, rpow_add hx0]; ring
    rw [e]
    exact (rpow_le_rpow_left_iff hx).2 (by linarith)
  · rw [hcp, hcp, hN]
    set a2 := csumS t c 1 (range R)
    set a3 := csumS t c 2 (range R)
    have e : (x ^ n) ^ 2 * (x ^ a2) ^ 5 * (x ^ a3) ^ 2 =
        x ^ (n + n + a2 + a2 + a2 + a2 + a2 + a3 + a3) := by
      simp only [rpow_add hx0]; ring
    rw [e]
    exact (rpow_le_rpow_left_iff hx).2 (by linarith)

end Erdos287.Physical.Factor
