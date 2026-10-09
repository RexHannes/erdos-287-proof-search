import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilyMaynard
import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilyMultiplicity

/-!
# Erdős #287 — the family Urem estimate on the literal physical packets

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

`actual_family_urem_maynard` instantiates `physical_family_urem_maynard` with the literal
packets `ξ ∈ Ξ ⊆ XiAll` of a `PhysData` satisfying the presieve hypotheses `WGood` and a bounded
Maynard tensor (`|f'_{i,v}| ≤ B_f`).  The following source conditions are **proved** rather than
assumed:

* `(c_ξ, f_ξ) = 1` (`PhysData.cRes_unit`);
* every prime of `A_ξ |B_ξ|` divides `f_ξ` (`physData_affinePrimesDivideBase`, from `j < ℓ`);
* `0 < f_ξ`;
* the packet multiplicity `∑_{ξ : f_ξ = f} |Γ_ξ| ≤ (V B_f^k)² k² τ(f)^{2k}` (`packet_multiplicity`).

The remaining hypotheses are exactly the published-theorem input (`MaynardLemma13_8`), the
Siegel–Walfisz condition (6.1) and divisor bound for the actual common sequence `α`, the
`β` energy bound, the base cap `f_ξ ≤ F`, the band cap `l < 2^{n₀}` for nonzero coefficients and the
modulus cutoff `2 F 2^{n₀} ≤ N'/(log N')^C`.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII.UremFamily

open Erdos287.Physical Erdos287.Physical.TypeII Erdos287.Physical.Sieve
  Erdos287.Physical.Sieve.ScalarParams Erdos287.Physical.Factor

lemma physData_f_pos (P : PhysData) (hP : P.WGood) {ξ : Packet P.k} (hξ : P.Admissible ξ) :
    0 < P.f ξ := by
  unfold PhysData.f PhysData.q0
  refine Nat.pos_of_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (hP.a_pos _).ne' hP.W_pos.ne') ?_)
  rw [prod_ne_zero_iff]
  intro i _
  exact (Nat.lcm_pos (hξ.2.2.2.2.2.1 i).1 (hξ.2.2.2.2.2.1 i).2).ne'

/-- **The family Urem estimate on the literal physical packets, from Maynard I, Lemma 13.8.** -/
theorem actual_family_urem_maynard (hM : MaynardLemma13_8) {B0 : ℝ} (hB0 : 0 < B0)
    (cSW : ℝ → ℝ) {Aexp : ℝ} (hAexp : 0 < Aexp) :
    ∃ C Cimp : ℝ, ∀ (P : PhysData), P.WGood → ∀ (Bf : ℝ), (∀ v i t, |P.fp v i t| ≤ Bf) →
    (2 * P.k : ℝ) + 1 ≤ B0 →
    ∀ (Ξ : Finset (Packet P.k)), Ξ ⊆ P.XiAll → ∀ (S : ScalarParams), S.Good →
    ∀ (δ N : ℝ) (K n n0 Nn M K' F : ℕ), K ≤ 2 ^ n →
    ∀ (α : ArithmeticFunction ℝ) (β : Packet P.k → ArithmeticFunction ℝ),
    (∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn) →
    (∀ ξ ∈ Ξ, ∀ m, β ξ m ≠ 0 → M ≤ m ∧ m < 2 * M) → 4 * Nn * M ≤ K' →
    (∀ ξ ∈ Ξ, P.f ξ ≤ F) → ∀ (Bβ : ℝ),
    (∀ ξ ∈ Ξ, ∑ m ∈ Ico M (2 * M), β ξ m ^ 2 ≤ Bβ) →
    (∀ ξ ∈ Ξ, ∀ J (Pb : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3) l r,
      physCoefCut S δ N (P.Gamma ξ) (P.f ξ) K J Pb χ l r ≠ 0 → l < 2 ^ n0) →
    2 ≤ (Nn : ℝ) - 1 / 2 → SWCondition α ((Nn : ℝ) - 1 / 2) B0 cSW →
    (∀ m, |α m| ≤ tau m ^ B0) →
    ((2 * F * 2 ^ n0 : ℕ) : ℝ) ≤ ((Nn : ℝ) - 1 / 2) / Real.log ((Nn : ℝ) - 1 / 2) ^ C →
    ∑ ξ ∈ Ξ, |physUrem S δ N (P.Gamma ξ) (P.f ξ) (P.cRes ξ) (P.A ξ) (P.B ξ) K K' α (β ξ)| ≤
      ∑ J ∈ range (S.T ^ 2 + 1), ∑ Pb : Fin J → Fin S.H, ∑ _χ : Fin S.Kc → Fin 3,
        ∑ r ∈ Ico 1 K, (1 / (Nat.totient r : ℝ)) * ∑ i ∈ range n0,
          S.atomWeight J Pb (S.atomColour δ N J Pb) * Real.sqrt Bβ *
            Real.sqrt (∑ ξ ∈ Ξ, |P.Gamma ξ| * ((M : ℝ) / P.f ξ + (2 ^ i : ℕ))) *
            Real.sqrt (((P.V * Bf ^ P.k) ^ 2 * (P.k : ℝ) ^ 2) * ((tau r ^ B0) ^ 2 *
              (Cimp * ((Nn : ℝ) - 1 / 2) ^ 2 / Real.log ((Nn : ℝ) - 1 / 2) ^ Aexp))) := by
  obtain ⟨C, Cimp, hC⟩ := physical_family_urem_maynard hM hB0 cSW hAexp
  refine ⟨C, Cimp, ?_⟩
  intro P hP Bf hBf hkB0 Ξ hΞ S hS δ N K n n0 Nn M K' F hKn α β hα hβ hK' hF Bβ hβ2 hl0 hN hsw
    hdiv hcut
  have hadm : ∀ ξ ∈ Ξ, P.Admissible ξ := fun ξ hξ => PhysData.mem_XiAll (hΞ hξ)
  refine hC Ξ S hS δ N P.Gamma P.f P.cRes P.A P.B K n n0 Nn M K' F (2 * P.k) hKn α β hα hβ hK'
    (fun ξ hξ => ⟨physData_f_pos P hP (hadm ξ hξ), hF ξ hξ⟩)
    (fun ξ hξ => PhysData.cRes_unit hP (hadm ξ hξ))
    (fun ξ hξ => physData_affinePrimesDivideBase P hP ξ (ne_of_lt (hadm ξ hξ).1))
    Bβ _ (by positivity) hβ2 ?_ hl0 hN hsw hdiv (by push_cast; linarith) hcut
  intro f0
  refine le_trans ?_ (packet_multiplicity P hP hBf f0)
  exact sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ hΞ) (fun _ _ _ => abs_nonneg _)

/-- **Reconnection to the exact Type-II identity.**  For a group `Ξ` of literal packets sharing
the sequence `α`, `scalarTypeII_eq_cells` gives, packet by packet,
`scalarTypeII_ξ = (Ordering-B cells)_ξ + physUrem_ξ`; hence any bound `E` on the family sum
`∑_ξ |physUrem_ξ|` (for instance the one of `actual_family_urem_maynard`) bounds the difference
between the group's scalar Type-II source and its cell sum. -/
theorem group_typeII_sub_cells_le (P : PhysData) {S : ScalarParams} (hS : S.Good)
    (Ξ : Finset (Packet P.k)) (δ N : ℝ) {K n : ℕ} (hKn : K ≤ 2 ^ n) {Nn M K' : ℕ}
    (α : ArithmeticFunction ℝ) (β : Packet P.k → ArithmeticFunction ℝ)
    (hα : ∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn)
    (hβ : ∀ ξ ∈ Ξ, ∀ m, β ξ m ≠ 0 → M ≤ m ∧ m < 2 * M) (hK' : 4 * Nn * M ≤ K') {E : ℝ}
    (hE : ∑ ξ ∈ Ξ, |physUrem S δ N (P.Gamma ξ) (P.f ξ) (P.cRes ξ) (P.A ξ) (P.B ξ) K K' α (β ξ)| ≤
      E) :
    |∑ ξ ∈ Ξ, scalarTypeII S (P.Gamma ξ) (P.f ξ) (P.cRes ξ) (P.A ξ) (P.B ξ) K K' α (β ξ) -
      ∑ ξ ∈ Ξ, ∑ J ∈ range (S.T ^ 2 + 1), ∑ Pb : Fin J → Fin S.H, ∑ χ : Fin S.Kc → Fin 3,
        ∑ i ∈ range n, ∑ i' ∈ range n,
          (physCell S δ N (P.Gamma ξ) (P.f ξ) (P.cRes ξ) (P.A ξ) (P.B ξ) K (2 ^ i) (2 ^ i') Nn M J
            Pb χ α (β ξ)).T| ≤ E := by
  rw [sum_congr rfl (fun ξ hξ => scalarTypeII_eq_cells hS δ N (P.Gamma ξ) (P.f ξ) (P.cRes ξ)
    (P.A ξ) (P.B ξ) hKn α (β ξ) hα (hβ ξ hξ) hK'), sum_add_distrib, add_sub_cancel_left]
  exact (abs_sum_le_sum_abs _ _).trans hE

end Erdos287.Physical.TypeII.UremFamily
