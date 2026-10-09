import RequestProject.Erdos287.ResearchBankV13.PrimeLayer

/-!
# Erdős #287 — Research Bank V14 §A8: the row-rigidity lemma

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For fixed `H` put `D_H = lcm(1, …, H)` and `N_H = ∑_{j=1}^{H} D_H / j`.

* `clearing_bounds` — denominator clearing: for nonempty `S ⊆ {1..H}`,
  `∑_{j∈S} D_H/j` is a positive integer `≤ N_H`, equal to `D_H · ∑_{j∈S} 1/j`;
* `clearing_contradiction` — hence a prime `p > N_H` cannot divide it;
* `row_rigidity` — **the row-rigidity lemma**: if `p` is prime, `⌊M/p⌋ ≤ H` and `p > max(H, N_H)`,
  then under the reciprocal-sum-one hypothesis (exact representation with maximum `M`) every
  positive `p`-multiple `≤ M` is omitted.  The modular core (the top `p`-adic layer congruence,
  which forces `p` to divide a cleared layer numerator) is the already kernel-checked
  `topLayer_congruence` route used by V13 `primeLayer_exclusion`; no analytic provider enters.
-/

namespace Erdos287
namespace ResearchBankV14
namespace RowRigidity

open ResearchBankV13.PrimeLayer ResearchBankV13.FiniteRepresentationModel

/-- `D_H = lcm(1, …, H)`. -/
def D (H : ℕ) : ℕ := L H

/-- `N_H = ∑_{j=1}^{H} D_H / j`. -/
def NH (H : ℕ) : ℕ := A H

theorem D_pos (H : ℕ) : 0 < D H := by
  unfold D L; exact lcmUpto_pos H

/-- **Denominator clearing.** -/
theorem clearing_bounds {H : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 H) (hne : S.Nonempty) :
    0 < ∑ j ∈ S, D H / j ∧ ∑ j ∈ S, D H / j ≤ NH H ∧
      ((∑ j ∈ S, D H / j : ℕ) : ℚ) = D H * ∑ j ∈ S, (1 : ℚ) / j := by
  have hdiv : ∀ j ∈ S, j ∣ D H ∧ 1 ≤ j := fun j hj =>
    ⟨dvd_lcmUpto (hS hj), (Finset.mem_Icc.1 (hS hj)).1⟩
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := hne
    have hpos : 0 < D H / j := Nat.div_pos (Nat.le_of_dvd (D_pos H) (hdiv j hj).1)
      (hdiv j hj).2
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun j => D H / j)
      (fun _ _ => Nat.zero_le _) hj)
  · exact Finset.sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => Nat.zero_le _
  · rw [Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨hd, h1⟩ := hdiv j hj
    rw [Nat.cast_div hd (by exact_mod_cast (show j ≠ 0 by omega))]
    field_simp

/-- **Modular contradiction**: a prime `p > N_H` cannot divide a cleared layer numerator. -/
theorem clearing_contradiction {H p : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 H)
    (hne : S.Nonempty) (hp : NH H < p) (hdvd : p ∣ ∑ j ∈ S, D H / j) : False := by
  obtain ⟨h1, h2, -⟩ := clearing_bounds hS hne
  have := Nat.le_of_dvd h1 hdvd
  omega

/-- `⌊M/p⌋ ≤ H` iff `M < (H+1) p` (for `p > 0`). -/
theorem floor_le_iff {M p H : ℕ} (hp : 0 < p) : M / p ≤ H ↔ M < (H + 1) * p := by
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hp]

/-- **The row-rigidity lemma.** -/
theorem row_rigidity {Aset : Finset ℕ} (hA : Erdos287Counterexample Aset) {p H : ℕ}
    (hp : p.Prime) (hfloor : Aset.max' hA.nonempty / p ≤ H) (hbig : max H (NH H) < p) :
    ∀ a ∈ Aset, ¬ p ∣ a := by
  have hM := (floor_le_iff hp.pos).1 hfloor
  exact primeLayer_exclusion hA hp hM (lt_of_le_of_lt (le_max_right _ _) hbig)

/-- The same, in the form "every positive `p`-multiple `≤ M` is omitted". -/
theorem multiples_omitted {Aset : Finset ℕ} (hA : Erdos287Counterexample Aset) {p H : ℕ}
    (hp : p.Prime) (hfloor : Aset.max' hA.nonempty / p ≤ H) (hbig : max H (NH H) < p)
    {m : ℕ} (_hm : 0 < m) (_hmM : m ≤ Aset.max' hA.nonempty) (hpm : p ∣ m) : m ∉ Aset :=
  fun hmA => row_rigidity hA hp hfloor hbig m hmA hpm

theorem NH_values : NH 2 = 3 ∧ NH 5 = 137 ∧ NH 10 = 7381 := ⟨A_2, A_5, A_10⟩

end RowRigidity
end ResearchBankV14
end Erdos287
