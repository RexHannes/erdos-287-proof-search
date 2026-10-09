import RequestProject.Erdos287.Window
import RequestProject.Erdos287.ResearchBankV6.SupportDisjointness

/-!
# Erdős #287 — Research Bank V6: FULL-FROZEN prime-power precision as denominator entry

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The small-prime denominator-entry mechanism of the canonical frontier is the FULL-FROZEN
prime-power precision already banked in this project: `Erdos287.primePower_window_exclusion`
(itself resting on `Erdos287.topLayer_congruence` and the certified constants `C(1..8)`).

This module contains the single new kernel statement needed to plug that mechanism into the V6
row language: under the window-exclusion hypotheses, the denominator set of a hypothetical
counterexample is **disjoint from the whole physical `q`-row** `q = p^e`, i.e. the prime power
never enters any denominator.  Nothing here is re-proved or weakened; the earlier theorem is used
as an import.
-/

namespace Erdos287
namespace ResearchBankV6
namespace FullFrozen

open Finset

/-- **FULL-FROZEN denominator entry (kernel).**  If `A ⊆ [1, M]` has `∑_{a ∈ A} 1/a = 1`,
`q = p^e ≤ M` and `p > C(⌊M/q⌋)`, then `A` is disjoint from the physical `q`-row: no denominator
of `A` is a multiple of `q`. -/
theorem row_disjoint_of_window_exclusion
    (A : Finset ℕ) (M p e : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a) (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) (he : 1 ≤ e) (hqM : p ^ e ≤ M)
    (hpC : Erdos287.C (M / p ^ e) < (p : ℤ)) :
    Disjoint A (UpperGap.rowSupport M (p ^ e)) := by
  rw [Finset.disjoint_right]
  intro n hn hnA
  exact Erdos287.primePower_window_exclusion A M p e hp hpos hAM hsum he hqM hpC n hnA
    (UpperGap.mem_rowSupport.1 hn).2

/-- Equivalently: the number of denominators in the excluded row is zero. -/
theorem row_card_zero_of_window_exclusion
    (A : Finset ℕ) (M p e : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a) (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) (he : 1 ≤ e) (hqM : p ^ e ≤ M)
    (hpC : Erdos287.C (M / p ^ e) < (p : ℤ)) :
    (A ∩ UpperGap.rowSupport M (p ^ e)).card = 0 := by
  rw [Finset.card_eq_zero, ← Finset.disjoint_iff_inter_eq_empty]
  exact row_disjoint_of_window_exclusion A M p e hp hpos hAM hsum he hqM hpC

end FullFrozen
end ResearchBankV6
end Erdos287
