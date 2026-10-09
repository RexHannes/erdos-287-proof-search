import RequestProject.Erdos287.ResearchBankV19.ActualBranchData

/-!
# Erdős #287 — Research Bank V19 §9: the sole remaining provider

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`ActualCenteredSourceCompositionProvider branches N mainConst` asserts EXACTLY the still-unproved
source-level facts, for the list of actual branches:

1. `zeroMode` — every packet is coherent (zero-mode domain) or uses the root-class Gram;
2. `e1` — every E1 branch supplies a valid period `V` satisfying the periodic-provider hypotheses;
3. `e2` — every E2 branch lies in the proved outer/own-variable scope;
4. `localControl`, `outerControl` — the local error bounds and the outer conductor/root sums are
   globally controlled in the SAME normalization `N`, eventually, for every `η > 0`;
5. `principalRecombination` — the signed principal terms recombine legally (their sum is at
   most `mainConst`).

**OPEN — DEFINED, NEVER CONSTRUCTED.**  No instance is built anywhere in the bank.

`LocalTransportBounds branches` records the LOCAL transport output (from the V18/V19 local
providers): `|err_b(M)| ≤ localBound_b(M)` for every branch.

* `provider_falsifiable` — the provider is a genuine proposition: a branch with joint E2
  dependence refutes it.
-/

namespace Erdos287
namespace ResearchBankV19
namespace ActualCenteredCompositionProvider

open BranchData

/-- **The sole remaining provider** (OPEN; never constructed). -/
structure ActualCenteredSourceCompositionProvider (branches : List ActualBranchData)
    (N : ℕ → ℝ) (mainConst : ℝ) : Prop where
  zeroMode : ∀ b ∈ branches, CoherentPacket b ∨ b.usesRootClassGram = true
  e1 : ∀ b ∈ branches, b.isE1 = true → E1Valid b
  e2 : ∀ b ∈ branches, b.isE2 = true → E2InScope b
  localControl : ∀ η > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀,
    0 < N M ∧ (branches.map fun b => b.localBound M).sum ≤ η * N M
  outerControl : ∀ η > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, (branches.map fun b => b.outerWeight M).sum ≤ η * N M
  principalRecombination : (branches.map fun b => b.principal).sum ≤ mainConst

/-- **Local transport bounds** (output of the V18/V19 local providers). -/
structure LocalTransportBounds (branches : List ActualBranchData) : Prop where
  local_bound : ∀ b ∈ branches, ∀ M, |b.err M| ≤ b.localBound M

/-- **The provider is falsifiable** (not vacuous). -/
theorem provider_falsifiable (N : ℕ → ℝ) (c : ℝ) :
    ¬ ActualCenteredSourceCompositionProvider [jointSample] N c := fun h =>
  jointSample_not_in_scope (h.e2 jointSample (List.mem_singleton_self _) rfl)

end ActualCenteredCompositionProvider
end ResearchBankV19
end Erdos287
