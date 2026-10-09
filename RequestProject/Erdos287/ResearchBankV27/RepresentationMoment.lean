import RequestProject.Erdos287.ResearchBankV27.GroupedCoefficient

/-!
# Erdős #287 — Research Bank V27 §5.7–5.8: diagonal count and representation moment

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`A_z = #{(i,i') : grp(i,i') = z}` is the representation count with coefficient `1`.

**LEAN BANK.**
* `bPsi_norm_le` — `|b_Ψ(z)| ≤ A_z` for one-bounded `Ψ`;
* `bPsi_L2_le` — `Σ_z |b_Ψ(z)|² ≤ Σ_z A_z²`;
* `same_rep_relation` — two representations with the same `(z, y)` and the same `(s, t)` satisfy
  `(h − h') t = (k − k') s` (when `a f ≠ 0`);
* `antidiagonal_card` — `#{(k,s) : k s = n} = τ(n)`;
* **`diagonal_count_le`** — for a box of positive `(h,t)` and ANY finite boxes of `k`, `s`:
  `#{(h,t,k,s) : h t = k s} ≤ Σ_{(h,t)} τ(h t)`.  This is the precise arithmetic content of the
  diagonal `ht = ks`; the analytic divisor-moment estimate of `Σ τ(ht)` is NOT claimed here (it
  is the `RepresentationMomentProvider`, `DecoratedLemma.lean`).
-/

namespace Erdos287
namespace ResearchBankV27
namespace RepresentationMoment

open Finset GroupedCoefficient

variable {I Z : Type*} [Fintype I] [DecidableEq Z]

/-- The representation count `A_z` (coefficient `1`). -/
noncomputable def repCount (grp : I → I → Z) (z : Z) : ℝ :=
  (((univ : Finset (I × I)).filter (fun p => grp p.1 p.2 = z)).card : ℝ)

theorem repCount_nonneg (grp : I → I → Z) (z : Z) : 0 ≤ repCount grp z := Nat.cast_nonneg _

/-- **`|b_Ψ(z)| ≤ A_z`** (LEAN BANK). -/
theorem bPsi_norm_le (grp : I → I → Z) (Ψ : I → ℂ) (hΨ : ∀ i, ‖Ψ i‖ ≤ 1) (z : Z) :
    ‖bPsi grp Ψ z‖ ≤ repCount grp z := by
  unfold bPsi repCount
  refine (norm_sum_le _ _).trans ?_
  calc ∑ p ∈ (univ : Finset (I × I)).filter (fun p => grp p.1 p.2 = z),
        ‖Ψ p.1 * starRingEnd ℂ (Ψ p.2)‖
      ≤ ∑ p ∈ (univ : Finset (I × I)).filter (fun p => grp p.1 p.2 = z), (1 : ℝ) :=
        Finset.sum_le_sum fun p _ => by
          rw [norm_mul, Complex.norm_conj]
          exact mul_le_one₀ (hΨ _) (norm_nonneg _) (hΨ _)
    _ = _ := by simp

/-- **`Σ_z |b_Ψ(z)|² ≤ Σ_z A_z²`** (LEAN BANK). -/
theorem bPsi_L2_le (grp : I → I → Z) (Ψ : I → ℂ) (hΨ : ∀ i, ‖Ψ i‖ ≤ 1) (T : Finset Z) :
    ∑ z ∈ T, ‖bPsi grp Ψ z‖ ^ 2 ≤ ∑ z ∈ T, repCount grp z ^ 2 :=
  Finset.sum_le_sum fun z _ =>
    pow_le_pow_left₀ (norm_nonneg _) (bPsi_norm_le grp Ψ hΨ z) 2

/-- **Same `(z, y)`, same `(s, t)` ⟹ `(h − h') t = (k − k') s`** (LEAN BANK). -/
theorem same_rep_relation {a f s t h k h' k' : ℤ} (haf : a * f ≠ 0)
    (heq : GroupedCoefficient.grpConcrete a f (s, h) (t, k) =
      GroupedCoefficient.grpConcrete a f (s, h') (t, k')) :
    (h - h') * t = (k - k') * s := by
  unfold GroupedCoefficient.grpConcrete at heq
  simp only [Prod.mk.injEq] at heq
  have := mul_left_cancel₀ haf heq.2
  linarith

theorem antidiagonal_card (n : ℕ) : n.divisorsAntidiagonal.card = n.divisors.card := by
  rw [← Nat.map_div_right_divisors, Finset.card_map]

/-- **Diagonal representation count** (LEAN BANK). -/
theorem diagonal_count_le (D : Finset (ℕ × ℕ)) (hD : ∀ p ∈ D, 0 < p.1 ∧ 0 < p.2)
    (Kb Sb : Finset ℕ) :
    ∑ p ∈ D, ((Kb ×ˢ Sb).filter (fun q => q.1 * q.2 = p.1 * p.2)).card ≤
      ∑ p ∈ D, (p.1 * p.2).divisors.card := by
  refine Finset.sum_le_sum fun p hp => ?_
  have hn : p.1 * p.2 ≠ 0 := Nat.mul_ne_zero (hD p hp).1.ne' (hD p hp).2.ne'
  rw [← antidiagonal_card]
  refine Finset.card_le_card fun q hq => ?_
  rw [Finset.mem_filter] at hq
  exact Nat.mem_divisorsAntidiagonal.2 ⟨hq.2, hn⟩

end RepresentationMoment
end ResearchBankV27
end Erdos287
