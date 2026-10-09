import RequestProject.Erdos287.CurrentTail.SpectatorNorm

/-!
# Erdős #287 — current tail consolidation: near-diagonal counting under `n₁ ≡ n₂ (mod f)`

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.  Deterministic counting only.**

Kernel-proved:

* `count_congr_le` — `#{n₂ ≤ N : n₂ ≡ n₁ (f)} ≤ N/f + 1`;
* `count_congr_window_le` — `#{n₂ ≤ N : n₂ ≡ n₁ (f), |n₁ - n₂| ≤ H} ≤ 2H/f + 2`;
* `pairs_congr_window_le` — `#{(n₁,n₂) ∈ [1,N]² : n₁ ≡ n₂ (f), |n₁-n₂| ≤ H} ≤ N (2H/f + 2)`;
* `pairs_congr_window_real` — in real form `≤ 2NH/f + 2N`; with `H = N/L^{C₀}` this is the
  shape `N²/(f L^{C₀}) + N`;
* `nearDiagonal_to_reciprocalDensity` — summing over packets,
  `∑_ξ |Γ_ξ| (A/f_ξ + B) ≤ A ∑_ξ |Γ_ξ|/φ(f_ξ) + B ∑_ξ |Γ_ξ|` (uses `φ(f) ≤ f`).

The remaining asymptotic comparison of `N ∑_ξ |Γ_ξ|` with the target size is **not** proved
here; it is isolated as the hypothesis `NearDiagonalRangeComparison` and consumed explicitly.
-/

open scoped BigOperators
open Finset

namespace Erdos287.CurrentTail

theorem div_add_le (a b f : ℕ) (hf : 0 < f) : (a + b) / f ≤ a / f + b / f + 1 := by
  have h1 := Nat.lt_mul_div_succ a hf
  have h2 := Nat.lt_mul_div_succ b hf
  have : (a + b) / f < a / f + b / f + 2 := by
    rw [Nat.div_lt_iff_lt_mul hf]
    nlinarith
  omega

/-- `#{n₂ ∈ [1,N] : n₂ ≡ n₁ (mod f)} ≤ N/f + 1`. -/
theorem count_congr_le (N f n1 : ℕ) :
    ((Icc 1 N).filter (fun n2 => n2 ≡ n1 [MOD f])).card ≤ N / f + 1 := by
  have : ((Icc 1 N).filter (fun n2 => n2 ≡ n1 [MOD f])).card ≤ (range (N / f + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun n => n / f) ?_ ?_
    · intro n hn
      have hn' := Finset.mem_filter.1 (Finset.mem_coe.1 hn)
      simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_Icc.1 hn'.1).2)
    · intro n hn n' hn' h
      have e1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hn)).2
      have e2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hn')).2
      have hmod : n % f = n' % f := (e1.trans e2.symm)
      have h' : n / f = n' / f := h
      rw [← Nat.div_add_mod n f, ← Nat.div_add_mod n' f, h', hmod]
  simpa using this

/-- Windowed count: `#{n₂ ∈ [1,N] : n₂ ≡ n₁ (f), n₁ ≤ n₂ + H, n₂ ≤ n₁ + H} ≤ 2H/f + 2`. -/
theorem count_congr_window_le (N f n1 H : ℕ) (hf : 0 < f) :
    ((Icc 1 N).filter (fun n2 => n2 ≡ n1 [MOD f] ∧ n1 ≤ n2 + H ∧ n2 ≤ n1 + H)).card ≤
      2 * H / f + 2 := by
  have hsub : ((Icc 1 N).filter (fun n2 => n2 ≡ n1 [MOD f] ∧ n1 ≤ n2 + H ∧ n2 ≤ n1 + H)).card
      ≤ (Icc ((n1 - H) / f) ((n1 + H) / f)).card := by
    refine Finset.card_le_card_of_injOn (fun n => n / f) ?_ ?_
    · intro n hn
      have hn' := (Finset.mem_filter.1 (Finset.mem_coe.1 hn)).2
      simp only [Finset.coe_Icc, Set.mem_Icc]
      exact ⟨Nat.div_le_div_right (by omega), Nat.div_le_div_right hn'.2.2⟩
    · intro n hn n' hn' h
      have e1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hn)).2.1
      have e2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hn')).2.1
      have hmod : n % f = n' % f := (e1.trans e2.symm)
      have h' : n / f = n' / f := h
      rw [← Nat.div_add_mod n f, ← Nat.div_add_mod n' f, h', hmod]
  refine hsub.trans ?_
  rw [Nat.card_Icc]
  rcases le_or_gt H n1 with hle | hlt
  · have := div_add_le (n1 - H) (2 * H) f hf
    rw [show n1 - H + 2 * H = n1 + H by omega] at this
    generalize (n1 + H) / f = x at this ⊢
    generalize (n1 - H) / f = y at this ⊢
    generalize 2 * H / f = z at this ⊢
    omega
  · have : (n1 + H) / f ≤ 2 * H / f := Nat.div_le_div_right (by omega)
    generalize (n1 + H) / f = x at this ⊢
    generalize (n1 - H) / f = y at this ⊢
    generalize 2 * H / f = z at this ⊢
    omega

/-- Near-diagonal pair count:
`#{(n₁,n₂) ∈ [1,N]² : n₁ ≡ n₂ (f), |n₁ - n₂| ≤ H} ≤ N (2H/f + 2)`. -/
theorem pairs_congr_window_le (N f H : ℕ) (hf : 0 < f) :
    ((Icc 1 N ×ˢ Icc 1 N).filter
      (fun p => p.2 ≡ p.1 [MOD f] ∧ p.1 ≤ p.2 + H ∧ p.2 ≤ p.1 + H)).card ≤
      N * (2 * H / f + 2) := by
  rw [Finset.card_filter, Finset.sum_product]
  calc ∑ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N,
        (if y ≡ x [MOD f] ∧ x ≤ y + H ∧ y ≤ x + H then 1 else 0)
      = ∑ x ∈ Icc 1 N,
          ((Icc 1 N).filter (fun y => y ≡ x [MOD f] ∧ x ≤ y + H ∧ y ≤ x + H)).card := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.card_filter]
    _ ≤ ∑ _x ∈ Icc 1 N, (2 * H / f + 2) :=
        Finset.sum_le_sum (fun x _ => count_congr_window_le N f x H hf)
    _ = N * (2 * H / f + 2) := by simp

/-- Real form: `#near-diagonal pairs ≤ 2NH/f + 2N`. -/
theorem pairs_congr_window_real (N f H : ℕ) (hf : 0 < f) :
    (((Icc 1 N ×ˢ Icc 1 N).filter
      (fun p => p.2 ≡ p.1 [MOD f] ∧ p.1 ≤ p.2 + H ∧ p.2 ≤ p.1 + H)).card : ℝ) ≤
      2 * N * H / f + 2 * N := by
  have h := pairs_congr_window_le N f H hf
  have hdiv : ((2 * H / f : ℕ) : ℝ) ≤ (2 * H : ℝ) / f := by
    rw [le_div_iff₀ (by exact_mod_cast hf)]
    exact_mod_cast Nat.div_mul_le_self (2 * H) f
  calc _ ≤ ((N * (2 * H / f + 2) : ℕ) : ℝ) := by exact_mod_cast h
    _ = (N : ℝ) * (((2 * H / f : ℕ) : ℝ) + 2) := by push_cast; ring
    _ ≤ (N : ℝ) * ((2 * H : ℝ) / f + 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    _ = 2 * N * H / f + 2 * N := by ring

/-- **Deterministic conversion to the reciprocal-density norm.**
`∑_ξ |Γ_ξ| (A/f_ξ + B) ≤ A ∑_ξ |Γ_ξ|/φ(f_ξ) + B ∑_ξ |Γ_ξ|` for `A ≥ 0`. -/
theorem nearDiagonal_to_reciprocalDensity {ι : Type*} (Xi : Finset ι) (Γ : ι → ℝ)
    (f : ι → ℕ) (hf : ∀ ξ, 0 < f ξ) {A B : ℝ} (hA : 0 ≤ A) :
    ∑ ξ ∈ Xi, |Γ ξ| * (A / f ξ + B) ≤
      A * ∑ ξ ∈ Xi, |Γ ξ| / (Nat.totient (f ξ) : ℝ) + B * ∑ ξ ∈ Xi, |Γ ξ| := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun ξ _ => ?_)
  have hφ := totient_cast_pos (hf ξ)
  have hle : (Nat.totient (f ξ) : ℝ) ≤ f ξ := by exact_mod_cast Nat.totient_le _
  have : A / f ξ ≤ A / (Nat.totient (f ξ) : ℝ) := div_le_div_of_nonneg_left hA hφ hle
  have e : |Γ ξ| * (A / f ξ + B) = |Γ ξ| * (A / f ξ) + B * |Γ ξ| := by ring
  rw [e]
  have : |Γ ξ| * (A / f ξ) ≤ A * (|Γ ξ| / (Nat.totient (f ξ) : ℝ)) := by
    have h2 := mul_le_mul_of_nonneg_left this (abs_nonneg (Γ ξ))
    calc |Γ ξ| * (A / f ξ) ≤ |Γ ξ| * (A / (Nat.totient (f ξ) : ℝ)) := h2
      _ = A * (|Γ ξ| / (Nat.totient (f ξ) : ℝ)) := by ring
  linarith

/-- **Isolated asymptotic range comparison** for the near-diagonal: the `B`-part
`N ∑_ξ |Γ_ξ|` is at most `ε` times the target size.  Not proved; consumed explicitly. -/
def NearDiagonalRangeComparison (Nsum target ε : ℝ) : Prop := Nsum ≤ ε * target

end Erdos287.CurrentTail
