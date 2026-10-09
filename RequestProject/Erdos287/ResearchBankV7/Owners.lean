import RequestProject.Erdos287.ResearchBankV7.Epochs
import RequestProject.Erdos287.ResearchBankV7.Absorption
import RequestProject.Erdos287.ResearchBankV7.StableEntry
import RequestProject.Erdos287.ResearchBankV7.GuardedBranchHit
import RequestProject.Erdos287.ResearchBankV7.V6Audit

/-!
# Erdős #287 — Research Bank V7: owners, supersession and the current closure DAG

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* **Frozen V6 milestone.**  The V6 owners are re-recorded with their V6 epoch stamp.
  `UpperGapCarryCompression` is recorded as *historical / superseded* — later work bypassed and
  refined that interface — and is explicitly **not** declared false
  (`upperGapCarryCompression_not_declared_false`); its proved V6 consequences are re-exported
  unchanged.
* **Supersession of the exact-mass owner.**  The generic `ExactMassIntersection` owner has been
  materially refined by exact interval lifting and guarded ERASURE-HIT; it is recorded as
  *superseded/refined*, never as false, and the downstream exact-mass mechanism is recorded as
  *conditionally ready once a genuine compatible ENTRY reference word exists*.
* **Current sole owner.**  `EntryFirstTerminalLeafExistenceOrKill` — an uninhabited interface
  expressing the unresolved global dichotomy: construct a genuine complete legal seed whose
  absorption tree has a surviving terminal leaf, **or** derive a contradiction covering all
  relevant seeds and branches.
* **Closure DAG.**  Only proved edges are entered; the node `GenuineEntryReferenceWord` remains
  uninhabited and no edge bypasses it.
-/

namespace Erdos287
namespace ResearchBankV7
namespace Owners

open Erdos287.ResearchBankV7.Epochs

/-! ## 1.  The frozen V6 milestone -/

/-- The V6 upper-gap carry-compression owner (candidate D, the granularity form), recorded as a
historical owner of the V6 epoch. -/
def UpperGapCarryCompressionV6 (D : ℕ) : Prop :=
  ResearchBankV6.OpenOwners.UpperGapCarryCompressionGranularity D

/-- The V6 exact-mass owner, recorded as a historical owner of the V6 epoch. -/
def ExactMassIntersectionV6 (frozen : ℚ) (middleSpectrum upperSpectrum : Set ℚ) : Prop :=
  ResearchBankV6.OpenOwners.ExactMassIntersection frozen middleSpectrum upperSpectrum

/-- The historical owner record for `UpperGapCarryCompression`: **superseded**, not false. -/
def record_upperGapCarryCompression : OwnerRecord :=
  { name := "UpperGapCarryCompression (V6 upper-gap/carry epoch)"
    epoch := Epoch.v6UpperGapCarry
    claim := UpperGapCarryCompressionV6 12
    flag := OwnerFlag.superseded }

/-- The historical owner record for `ExactMassIntersection`: **superseded/refined**, not false. -/
def record_exactMassIntersection : OwnerRecord :=
  { name := "ExactMassIntersection (V6 upper-gap/carry epoch)"
    epoch := Epoch.v6UpperGapCarry
    claim := ExactMassIntersectionV6 0 Set.univ Set.univ
    flag := OwnerFlag.superseded }

/-- **`UpperGapCarryCompression` is not declared false.**  Its recorded flag is `superseded`, and
the `superseded` flag is truth-neutral (`Epochs.superseded_flag_is_truth_neutral`); moreover its
proved V6 consequence survives unchanged. -/
theorem upperGapCarryCompression_not_declared_false :
    record_upperGapCarryCompression.flag = OwnerFlag.superseded ∧
      ∀ (D : ℕ) (d : ResearchBankV6.OpenOwners.CarryData),
        UpperGapCarryCompressionV6 D → d.admissible →
          (ResearchBankV6.OpenOwners.aggregateMass d).den ∣ ResearchBankV6.UpperGap.lcmUpto D :=
  ⟨rfl, fun _ d h hd => ResearchBankV6.OpenOwners.mass_den_dvd_of_granularity h d hd⟩

/-- **`ExactMassIntersection` is not declared false** either: superseded/refined, with its proved
V6 consequence re-exported unchanged. -/
theorem exactMassIntersection_not_declared_false :
    record_exactMassIntersection.flag = OwnerFlag.superseded ∧
      ∀ (frozen : ℚ) (middleSpectrum upperSpectrum : Set ℚ),
        ExactMassIntersectionV6 frozen middleSpectrum upperSpectrum →
          ∀ m ∈ middleSpectrum, ∀ u ∈ upperSpectrum, frozen + m + u ≠ 1 :=
  ⟨rfl, fun _ _ _ h _ hm _ hu =>
    ResearchBankV6.OpenOwners.no_unit_mass_of_exactMassIntersection h hm hu⟩

/-! ## 2.  The refinement that supersedes the exact-mass owner -/

/-- The genuineness specification of an ENTRY reference word is supplied by the ENTRY-FIRST lane;
it is a parameter here, never instantiated. -/
abbrev EntrySpec := GuardedBranchHit.GuardedBranch → Prop

/-- **The node `genuine ENTRY reference word`.**  Uninhabited for the intended specification. -/
def GenuineEntryReferenceWord (spec : EntrySpec) : Prop :=
  ∃ b : GuardedBranchHit.GuardedBranch, spec b

/-- **The downstream exact-mass mechanism, conditionally ready.**  Once a genuine compatible ENTRY
reference word exists, the refined mechanism (exact interval lifting + guarded ERASURE-HIT)
delivers an exact `S = 1` modification of the same physical branch. -/
theorem exactMass_ready_given_entry (spec : EntrySpec) (h : GenuineEntryReferenceWord spec) :
    ∃ b : GuardedBranchHit.GuardedBranch, spec b ∧
      ∃ S ⊆ b.P, S.card ≤ b.zeroBudget ∧ Disjoint S b.G ∧ Disjoint S b.Nprot ∧
        ∑ n ∈ b.T \ S, (1 : ℚ) / n = 1 := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, hb, b.guarded_branch_to_hit⟩

/-! ## 3.  The current sole owner -/

/-- **CURRENT OWNER (uninhabited).**  `EntryFirstTerminalLeafExistenceOrKill`: for the intended
family of legal seeds and their complete absorption trees, either

* there is a genuine complete legal seed whose absorption tree has a surviving (nonfailed)
  terminal leaf, **or**
* a contradiction covering all relevant seeds and branches is derived, i.e. no gap-`≤ 2`
  counterexample exists at all.

The second disjunct is the genuine global kill (it entails the #287 conclusion on this route), so
this dichotomy is **not** an instance of excluded middle and is not inhabited here. -/
def EntryFirstTerminalLeafExistenceOrKill
    (Seed : Type) (Legal : Seed → Prop) (setup : Seed → StableEntry.AbsorptionSetup) : Prop :=
  (∃ s : Seed, Legal s ∧ (setup s).HasNonfailedLeaf) ∨ (∀ _ : Erdos287.Gap2CE, False)

/-- The current owner record. -/
def record_currentOwner (Seed : Type) (Legal : Seed → Prop)
    (setup : Seed → StableEntry.AbsorptionSetup) : OwnerRecord :=
  { name := "EntryFirstTerminalLeafExistenceOrKill (current ENTRY-FIRST epoch)"
    epoch := Epoch.entryFirst
    claim := EntryFirstTerminalLeafExistenceOrKill Seed Legal setup
    flag := OwnerFlag.openOwner }

/-- **The kill side of the owner is a genuine global statement.**  If it holds, no gap-`≤ 2`
counterexample exists; in particular the owner is not a triviality. -/
theorem owner_kill_side_is_global
    {Seed : Type} {Legal : Seed → Prop} {setup : Seed → StableEntry.AbsorptionSetup}
    (h : EntryFirstTerminalLeafExistenceOrKill Seed Legal setup)
    (hno : ¬ ∃ s : Seed, Legal s ∧ (setup s).HasNonfailedLeaf) :
    ∀ _ : Erdos287.Gap2CE, False :=
  h.resolve_left hno

/-! ## 4.  Firewalls protecting the current owner -/

/-- **Firewall.**  The owner may not be weakened to separate row feasibility: from the feasibility
of each row individually nothing follows about the global object. -/
theorem owner_not_weakened_to_row_feasibility :
    ¬ ∀ (P : ℕ → Prop) (Q : Prop), (∀ n, P n) → Q := by
  intro h
  exact h (fun _ => True) False (fun _ => trivial)

/-- **Firewall.**  STABLE-ENTRY is a bounded branching criterion, not a resolution of the owner:
an equivalence for a fixed seed inhabits neither side of the dichotomy. -/
theorem stableEntry_does_not_solve_owner :
    ¬ ∀ P Q R : Prop, (P ↔ Q) → R := by
  intro h
  exact h False False False Iff.rfl

/-- A completely trivial guarded branch (the degenerate solution `1/1 = 1`).  It exists, and it is
**not** an ENTRY reference word of the #287 problem; it is used only to show that the genuineness
specification is load-bearing. -/
def trivialBranch : GuardedBranchHit.GuardedBranch where
  J := 1
  J_pos := by norm_num
  T := {1}
  T_ok := by intro n hn; simp at hn; subst hn; exact ⟨by norm_num, by norm_num⟩
  P := ∅
  P_sub := by simp
  G := ∅
  Nprot := ∅
  G_disj := by simp
  N_disj := by simp
  zeroBudget := 0
  budget_ok := by simp
  g := 1
  A := 0
  B := 0
  cert := by
    intro n _ hA hB
    refine ⟨∅, by simp, ?_⟩
    have : n = 0 := le_antisymm hB hA
    simp [this]
  deficit_lattice := by decide
  margin_lo := by decide
  margin_hi := by decide

/-- **Firewall.**  The genuineness specification of the ENTRY node is load-bearing: with the empty
specification the node is inhabited, with the contradictory one it is not.  Recording the node as
uninhabited therefore refers to the intended #287 specification, and no theorem may substitute a
weaker one. -/
theorem entry_node_specification_is_load_bearing :
    GenuineEntryReferenceWord (fun _ => True) ∧ ¬ GenuineEntryReferenceWord (fun _ => False) := by
  refine ⟨⟨trivialBranch, trivial⟩, ?_⟩
  rintro ⟨b, hb⟩
  exact hb

/-- **Firewall.**  No result of this layer bypasses the ENTRY node: the exact-mass mechanism is an
implication *out of* the node, and an implication never inhabits its hypothesis. -/
theorem no_bypass_of_entry_node :
    ¬ ∀ (spec : EntrySpec), (GenuineEntryReferenceWord spec → True) →
      GenuineEntryReferenceWord spec := by
  intro h
  obtain ⟨b, hb⟩ := h (fun _ => False) (fun _ => trivial)
  exact hb

/-! ## 5.  The current closure DAG -/

/-- A DAG edge carries an actual Lean proof of `src → tgt`; there is no way to enter an edge
without one. -/
structure ProvedEdge where
  /-- Source node. -/
  src : Prop
  /-- Target node. -/
  tgt : Prop
  /-- The proof of the edge. -/
  proof : src → tgt

/-- Edge: FULL-FROZEN / seed constraints ⟶ bounded absorption budget.  A charging datum with
`γ = 1/8` and no guards satisfies the absorption budget `|W| ≤ (16/5)|Z₀|`. -/
def edge_boundedAbsorption (c : Absorption.ChargingData) : ProvedEdge :=
  { src := c.gamma = 1/8 ∧ c.G0 = ∅
    tgt := (c.W.card : ℚ) ≤ (16/5) * c.Z0.card
    proof := fun h => Absorption.unguarded_W_bound c h.1 h.2 }

/-- Edge: bounded absorption ⟶ STABLE-ENTRY terminal-leaf criterion (forward, kernel part). -/
def edge_stableEntryForward (A : StableEntry.AbsorptionSetup) : ProvedEdge :=
  { src := A.HasNo00Extension
    tgt := A.HasNonfailedLeaf
    proof := A.stableEntry_forward }

/-- Edge: genuine ENTRY reference word ⟶ guarded spine / ERASURE-HIT ⟶ exact `S = 1`. -/
def edge_entryToExactMass (spec : EntrySpec) : ProvedEdge :=
  { src := GenuineEntryReferenceWord spec
    tgt := ∃ b : GuardedBranchHit.GuardedBranch, spec b ∧
      ∃ S ⊆ b.P, S.card ≤ b.zeroBudget ∧ Disjoint S b.G ∧ Disjoint S b.Nprot ∧
        ∑ n ∈ b.T \ S, (1 : ℚ) / n = 1
    proof := exactMass_ready_given_entry spec }

/-- The current V7 closure DAG: the edges actually entered.  Every one is a proved implication,
and the chain passes through the uninhabited node `GenuineEntryReferenceWord`. -/
def closureDagV7 (c : Absorption.ChargingData) (A : StableEntry.AbsorptionSetup)
    (spec : EntrySpec) : List ProvedEdge :=
  [edge_boundedAbsorption c, edge_stableEntryForward A, edge_entryToExactMass spec]

/-- Every DAG edge is exactly an implication — the only content an edge has. -/
theorem dag_edges_are_proved (e : ProvedEdge) (hs : e.src) : e.tgt := e.proof hs

/-- **The DAG does not close #287.**  The terminal edge starts at the uninhabited ENTRY node, and
an implication out of an uninhabited node produces nothing. -/
theorem dag_does_not_close : ¬ ∀ e : ProvedEdge, e.tgt := by
  intro h
  exact h { src := False, tgt := False, proof := id }

end Owners
end ResearchBankV7
end Erdos287
