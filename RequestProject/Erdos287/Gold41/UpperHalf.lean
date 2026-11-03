import RequestProject.Erdos287.Gold41.Defs
import RequestProject.Erdos287.Blocker
import RequestProject.Erdos287.Counterexample

namespace Erdos287
namespace Gold41

open Erdos287

/-- Upper-half prime exclusion in literal selected-set form. -/
theorem upperHalfPrime_not_mem (S : SelectedSet) {p : ℕ}
    (hp : p.Prime) (hhalf : S.M < 2 * p) (hpM : p < S.M) :
    p ∉ S.A := by
  have hexc : ExcludedPP S.M p :=
    excludedPP_self_of_large hp (Nat.le_of_lt hpM) hhalf
  intro hpA
  exact ExcludedPP.not_dvd_mem hexc
    (fun a ha => S.pos_of_mem ha)
    (fun a ha => S.le_max ha)
    S.reciprocal_sum_one hpA dvd_rfl

/-- Indicator form of upper-half prime exclusion (`x_p = 0`). -/
theorem upperHalfPrime_natIndicator_zero (S : SelectedSet) {p : ℕ}
    (hp : p.Prime) (hhalf : S.M < 2 * p) (hpM : p < S.M) :
    natIndicator S.A p = 0 := by
  simp [natIndicator, upperHalfPrime_not_mem S hp hhalf hpM]

namespace Gap2CE

variable (ce : Erdos287.Gap2CE)

/-- In a hypothetical gap-two counterexample, an upper-half prime `p` is excluded. -/
theorem upperHalfPrime_not_mem {p : ℕ}
    (hp : p.Prime) (hhalf : ce.M < 2 * p) (hpM : p ≤ ce.M) :
    p ∉ ce.A := by
  have hexc : ExcludedPP ce.M p := excludedPP_self_of_large hp hpM hhalf
  exact ce.notMem_of_excludedPP hexc dvd_rfl

/-- Internal forced neighbors for an excluded upper-half prime (`x_{p-1}=x_{p+1}=1`). -/
theorem forced_neighbors_of_upperHalfPrime {p : ℕ}
    (hp : p.Prime)
    (hpN : ce.N + 1 ≤ p)
    (hpM : p + 1 ≤ ce.M)
    (hhalf : ce.M < 2 * p) :
    p - 1 ∈ ce.A ∧ p + 1 ∈ ce.A := by
  have hhole : p ∉ ce.A :=
    Gap2CE.upperHalfPrime_not_mem (ce := ce) hp hhalf
      (by omega)
  have hpred_eq : p - 1 + 1 = p := by omega
  have hleft : p - 1 ∈ ce.A := by
    refine ce.forced_left ?_ ?_ ?_
    · omega
    · omega
    · simpa [hpred_eq] using hhole
  have hright : p + 1 ∈ ce.A :=
    ce.forced_right (n := p) (by omega) hpM hhole
  exact ⟨hleft, hright⟩

/-- Indicator form of internal forced neighbors under the same hypotheses. -/
theorem forced_neighbors_natIndicator {p : ℕ}
    (hp : p.Prime)
    (hpN : ce.N + 1 ≤ p)
    (hpM : p + 1 ≤ ce.M)
    (hhalf : ce.M < 2 * p) :
    natIndicator ce.A (p - 1) = 1 ∧ natIndicator ce.A (p + 1) = 1 := by
  rcases Gap2CE.forced_neighbors_of_upperHalfPrime (ce := ce) hp hpN hpM hhalf with
      ⟨hleft, hright⟩
  exact ⟨by simp [natIndicator, hleft], by simp [natIndicator, hright]⟩

end Gap2CE

end Gold41
end Erdos287
