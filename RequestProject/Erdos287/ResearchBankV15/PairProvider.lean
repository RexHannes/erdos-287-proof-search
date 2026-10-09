import Mathlib.Tactic
import RequestProject.Erdos287.ResearchBankV15.ZerothMomentContract

/-!
# Erdős #287 — Research Bank V15 §B11: the sole analytic owner

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`ActualWeightedColouredPairProvider src WF` means precisely: for the **same** fixed tuple
(`FixedAffineSource.tuple`), the **same** nonnegative physical weight (`weightSystem src`), the
**same** proportional window (`window tuple M`) and the **same** normalization
`N_X = C_X S_W0(a) I`, eventually `P_actual / N_X ≤ A0 · W_F + 2/5 + η` for every `η > 0`.

Because `P_actual` is the *physical* count (`pair_expansion`), the contract automatically
preserves the actual collision-weighted local densities, the root-dependent CRT residue and the
complete lcm modulus (both inside `Hit`), the large-core sectors (nothing is truncated), the
signed spectator coefficients `λ_d λ_e` (no absolute values), and the `W_F` normalization shared
with the score margin.

* `toV14` / `ofV14` — it is *exactly* the V14 provider at this tuple / weight / normalization;
* `pair_expansion` — the physical square expansion of `P_actual`.

**The provider is never constructed in the bank.**
-/

namespace Erdos287
namespace ResearchBankV15
namespace PairProvider

open ResearchBankV14 ResearchBankV14.BalancedKernelParameters
open ResearchBankV14.ConditionalAsymptoticImplication
open FixedAffineSource Normalization ZerothMomentContract

variable (src : SourceData)

/-- **The actual weighted coloured pair provider** (sole remaining new analytic owner; never
constructed). -/
structure ActualWeightedColouredPairProvider (WF : ℝ) : Prop where
  eventual : ∀ η > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀,
    Pair tuple (weightSystem src) M / NX src M ≤ ((A0 : ℚ) : ℝ) * WF + 2 / 5 + η

theorem toV14 {WF : ℝ} (h : ActualWeightedColouredPairProvider src WF) :
    ConditionalAsymptoticImplication.ActualWeightedColouredPairProvider tuple (weightSystem src)
      (NX src) WF := ⟨h.eventual⟩

theorem ofV14 {WF : ℝ}
    (h : ConditionalAsymptoticImplication.ActualWeightedColouredPairProvider tuple
      (weightSystem src) (NX src) WF) : ActualWeightedColouredPairProvider src WF := ⟨h.eventual⟩

open Classical in
/-- **Physical square expansion of `P_actual`**: signed coefficients `λ_d λ_e`, the joint
residue / complete-modulus condition `Hit`, and the actual coloured pair counts. -/
theorem pair_expansion (M : ℕ) :
    Pair tuple (weightSystem src) M =
      ∑ d ∈ src.D M, ∑ e ∈ src.D M, lamM src M d * lamM src M e *
        ∑ t ∈ (window tuple M).filter (Hit src d e),
          ∑ r, (((occ tuple t r).choose 2 : ℕ) : ℝ) := by
  unfold Pair
  convert weighted_expansion src M (fun t => ∑ r, (((occ tuple t r).choose 2 : ℕ) : ℝ)) using 1

end PairProvider
end ResearchBankV15
end Erdos287
