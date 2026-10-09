import RequestProject.Erdos287.CurrentTail.EffectivityBoundary

/-!
# Erdős #287 — current tail consolidation: regression controls

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Ten negative controls, each a kernel-checked theorem:

1. `reg1_dilation_changes_discrepancy` — (reconstructed form of the V96 bad dilation; the V96
   text itself is UNFORMALISED_SOURCE) dilating a support by `2` changes the discrepancy modulo
   `2`: it is not an admissible symmetry of the source;
2. `reg2_fixedResidue_breaks_SW` — fixed-residue restriction does **not** preserve ordinary SW:
   all discrepancies modulo `3` vanish, but after restricting to odd `n` they do not;
3. `reg3_characterBeforeCauchy` — Ordering A loses the `1/f` density (factor `√f ≥ 2`);
4. `reg4_packetwise_population` — packetwise multiplication of a logarithmic error by a packet
   population `P ≥ s` destroys an `s`-saving;
5. `reg5_provider_outside_hypotheses` — the `E₁` provider cannot be applied to coefficients
   violating its divisor-power bound (its hypothesis record is then false);
6. `reg6_forgetting_fourier_enlargement` — the dual length for modulus `fq` is not that of `q`;
7. `reg7_TH_printed_not_quantitative` — a toy error satisfying the printed `T_H ≤ x^ε` shape but
   violating every `C · T_H^{7/128}` bound;
8. `reg8_abs_before_recombination` — absolute values before main-term recombination lose exact
   cancellation;
9. `reg9_existential_onset` — an existential onset carries no computable numeral;
10. `reg10_tail_alone_no_splice` — the tail shape does not give the global shape.
-/

open scoped BigOperators
open Finset

namespace Erdos287.CurrentTail

/-! ### 1. Dilation -/

theorem reg1_dilation_changes_discrepancy :
    Delta {1, 2, 3} (fun _ => 1) 2 0 = -1 ∧ Delta {2, 4, 6} (fun _ => 1) 2 0 = 3 := by
  have h2 : Nat.totient 2 = 1 := by decide
  constructor <;>
  · simp only [Delta, ind, h2]
    norm_num [Finset.sum_insert, Nat.ModEq, Nat.coprime_iff_gcd_eq_one, Finset.filter_insert,
      Finset.filter_singleton, Nat.odd_iff]

/-! ### 2. Fixed-residue restriction vs ordinary SW -/

theorem reg2_fixedResidue_breaks_SW :
    Delta {1, 2} (fun _ => 1) 3 1 = 0 ∧ Delta {1, 2} (fun _ => 1) 3 2 = 0 ∧
      DeltaRel {1, 2} (fun _ => 1) 2 1 3 1 = 1 / 2 := by
  have h3 : Nat.totient 3 = 2 := by decide
  refine ⟨?_, ?_, ?_⟩
  · simp only [Delta, ind, h3]
    norm_num [Finset.sum_insert, Nat.ModEq, Nat.coprime_iff_gcd_eq_one, Finset.filter_insert,
      Finset.filter_singleton, Nat.odd_iff]
  · simp only [Delta, ind, h3]
    norm_num [Finset.sum_insert, Nat.ModEq, Nat.coprime_iff_gcd_eq_one, Finset.filter_insert,
      Finset.filter_singleton, Nat.odd_iff]
  · simp only [DeltaRel, ind, h3]
    have : ({1, 2} : Finset ℕ).filter (fun n => n ≡ 1 [MOD 2]) = {1} := by decide
    rw [this]
    norm_num [Nat.ModEq, Nat.coprime_iff_gcd_eq_one, Finset.filter_singleton]

/-! ### 3. Character before Cauchy -/

theorem reg3_characterBeforeCauchy {f : ℕ} (K : ℕ) (hf : 4 ≤ f) :
    2 * orderingBBound K K ≤ orderingABound (f * K) K :=
  orderingA_loss_ge_two K hf

/-! ### 4. Packetwise population -/

theorem reg4_packetwise_population {N s P : ℝ} (hN : 0 ≤ N) (hs : 0 < s) (hP : s ≤ P) :
    N ≤ P * (N / s) := by
  rw [mul_div_assoc', le_div_iff₀ hs]
  nlinarith

/-! ### 5. Provider outside its coefficient hypotheses -/

theorem reg5_provider_outside_hypotheses {x : ℝ} {Mset Nset Qset : Finset ℕ} {β γ : ℕ → ℝ}
    {a : ℕ} {θ σlo σhi δ A0 : ℝ} {B : ℕ} {n : ℕ} (hn : n ∈ Nset)
    (hbad : (tau n : ℝ) ^ B < |γ n|) :
    ¬ E1Hypotheses x Mset Nset Qset β γ a θ σlo σhi δ B A0 :=
  fun h => absurd (h.coeff_gamma n hn) (not_le.2 hbad)

/-! ### 6. Fourier enlargement -/

theorem reg6_forgetting_fourier_enlargement {f q N : ℚ} (hf : f ≠ 1) (hq : q ≠ 0)
    (hN : N ≠ 0) : dualLength (f * q) N ≠ dualLength q N :=
  forgetting_enlargement_wrong hf hq hN

/-! ### 7. Printed `T_H` shape versus the quantitative `T_H^{7/128}` loss -/

/-- Toy error with linear `T_H` dependence. -/
noncomputable def toyErr (δ x T : ℝ) : ℝ := T * x ^ (-δ)

theorem toyErr_printed (δ : ℝ) {ε x T : ℝ} (hx : 1 ≤ x) (hTx : T ≤ x ^ ε) :
    toyErr δ x T ≤ x ^ (-δ + ε) := by
  unfold toyErr
  have hx0 : 0 < x := by linarith
  rw [Real.rpow_add hx0, mul_comm (x ^ (-δ))]
  exact mul_le_mul_of_nonneg_right hTx (Real.rpow_nonneg hx0.le _)

theorem toyErr_not_quantitative (δ : ℝ) :
    ¬ ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
      toyErr δ 1 T ≤ C * T ^ ((THLossExponent : ℚ) : ℝ) * (1 : ℝ) ^ (-δ) := by
  rintro ⟨C, hC⟩
  set T : ℝ := (|C| + 1) ^ 2 with hTdef
  have hT1 : 1 ≤ T := by
    have : 1 ≤ |C| + 1 := by linarith [abs_nonneg C]
    nlinarith
  have hT0 : 0 < T := by linarith
  have h := hC T hT1
  simp only [toyErr, Real.one_rpow, mul_one, THLossExponent] at h
  push_cast at h
  have hsplit : T = T ^ ((7 : ℝ) / 128) * T ^ ((121 : ℝ) / 128) := by
    rw [← Real.rpow_add hT0]; norm_num
  have hpos : 0 < T ^ ((7 : ℝ) / 128) := Real.rpow_pos_of_pos hT0 _
  have h121 : T ^ ((121 : ℝ) / 128) ≤ C := by
    have : T ^ ((7 : ℝ) / 128) * T ^ ((121 : ℝ) / 128) ≤ T ^ ((7 : ℝ) / 128) * C := by
      rw [← hsplit, mul_comm]; exact h
    exact le_of_mul_le_mul_left this hpos
  have hhalf : T ^ ((1 : ℝ) / 2) ≤ T ^ ((121 : ℝ) / 128) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have hsqrt : T ^ ((1 : ℝ) / 2) = |C| + 1 := by
    rw [← Real.sqrt_eq_rpow, hTdef, Real.sqrt_sq (by linarith [abs_nonneg C])]
  linarith [le_abs_self C]

theorem reg7_TH_printed_not_quantitative (δ : ℝ) :
    (∀ ε x T : ℝ, 1 ≤ x → T ≤ x ^ ε → toyErr δ x T ≤ x ^ (-δ + ε)) ∧
    ¬ ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
      toyErr δ 1 T ≤ C * T ^ ((THLossExponent : ℚ) : ℝ) * (1 : ℝ) ^ (-δ) :=
  ⟨fun _ _ _ hx hTx => toyErr_printed δ hx hTx, toyErr_not_quantitative δ⟩

/-! ### 8. Absolute values before recombination -/

theorem reg8_abs_before_recombination : |(1 : ℝ) + (-1)| < |(1 : ℝ)| + |(-1 : ℝ)| := by
  norm_num

/-! ### 9. Existential onset -/

theorem reg9_existential_onset (P : Prop) : ∃ n : ℕ, (P → n = 0) ∧ (¬ P → n = 1) :=
  existential_witness_classical P

/-! ### 10. Tail alone gives no splice -/

theorem reg10_tail_alone_no_splice :
    ∃ P : Finset ℕ → Prop, (∃ M0 : ℕ, ∀ A, P A → A.sum id < M0) ∧ ¬ (∀ A, ¬ P A) :=
  tail_does_not_give_global

end Erdos287.CurrentTail
