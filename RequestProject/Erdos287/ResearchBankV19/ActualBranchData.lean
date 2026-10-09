import RequestProject.Erdos287.ResearchBankV19.HBBranchTaxonomy
import RequestProject.Erdos287.ResearchBankV19.CoherentRoots

/-!
# Erdős #287 — Research Bank V19 §8: actual branch data

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`ActualBranchData` is the explicit data record every coloured branch must carry:

    actual coefficient; full CRT modulus; root packet (moduli + root assignment);
    SW / centering stage; Q, D₀, R, S, N, M, H; E1 period V if relevant;
    E2 outer/inner dependency classification; outer conductor/root weights;
    signed principal contribution; error contribution and its local bound.

Predicates (definitions only):
* `CoherentPacket b` — the root assignment is coherent on every pair of packet moduli;
* `E1Valid b` — the branch supplies a period `V > 0`, coprime to the full modulus, for which the
  actual coefficient is `V`-periodic (the periodic-provider hypotheses);
* `E2InScope b` — the E2 dependency is outer-only or own-variable (not joint).

Nothing here asserts that any actual branch satisfies these predicates.
-/

namespace Erdos287
namespace ResearchBankV19
namespace BranchData

open HBBranchTaxonomy

/-- Siegel–Walfisz / centering stage. -/
inductive SWStage
  | preCentering
  | centered
  | siegelWalfisz
  deriving DecidableEq, Repr

/-- E2 outer/inner dependency classification. -/
inductive E2Dependency
  /-- depends on outer variables only -/
  | outerOnly
  /-- independent one-bounded own-variable (`h`) multiplier -/
  | ownVariable
  /-- joint `q/h` dependence (NOT covered by the proved scope theorem) -/
  | joint
  deriving DecidableEq, Repr

/-- **The actual branch data record.** -/
structure ActualBranchData where
  branch : HBBranch
  coeff : ℤ → ℂ
  fullModulus : ℕ
  packetModuli : Finset ℕ
  rootPacket : ℕ → ℤ
  usesRootClassGram : Bool
  swStage : SWStage
  Q : ℝ
  D0 : ℝ
  R : ℝ
  S : ℝ
  N : ℝ
  M : ℝ
  H : ℝ
  isE1 : Bool
  e1Period : Option ℕ
  isE2 : Bool
  e2Dependency : E2Dependency
  outerWeight : ℕ → ℝ
  principal : ℝ
  err : ℕ → ℝ
  localBound : ℕ → ℝ

/-- Coherent root packet. -/
def CoherentPacket (b : ActualBranchData) : Prop :=
  ∀ q₁ ∈ b.packetModuli, ∀ q₂ ∈ b.packetModuli, CoherentRoots.Coherent b.rootPacket q₁ q₂

/-- Valid E1 period data. -/
def E1Valid (b : ActualBranchData) : Prop :=
  ∃ V : ℕ, b.e1Period = some V ∧ 0 < V ∧ Nat.Coprime b.fullModulus V ∧
    ∀ u : ℤ, b.coeff (u + V) = b.coeff u

/-- E2 branch inside the proved outer/own-variable scope. -/
def E2InScope (b : ActualBranchData) : Prop := b.e2Dependency ≠ .joint

/-- A sample record (used only by negative controls): an E2 branch with JOINT dependence. -/
def jointSample : ActualBranchData where
  branch := .twoLarge
  coeff := fun _ => 1
  fullModulus := 1
  packetModuli := ∅
  rootPacket := fun _ => 0
  usesRootClassGram := false
  swStage := .centered
  Q := 1
  D0 := 1
  R := 1
  S := 1
  N := 1
  M := 1
  H := 1
  isE1 := false
  e1Period := none
  isE2 := true
  e2Dependency := .joint
  outerWeight := fun _ => 0
  principal := 0
  err := fun _ => 0
  localBound := fun _ => 0

theorem jointSample_not_in_scope : ¬ E2InScope jointSample := fun h => h rfl

end BranchData
end ResearchBankV19
end Erdos287
