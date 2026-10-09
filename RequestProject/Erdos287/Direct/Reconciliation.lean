import RequestProject.Erdos287.Direct.CurrentStatus
import RequestProject.Erdos287.Direct.TargetTuningFinite
import RequestProject.Erdos287.CurrentStatusLatest

/-!
# Route S / Route D reconciliation, finite-frontier integrity and hostile audit

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Two distinct research programmes are tracked:

* **Route S** — the existing Source / FivePrime / Directed-Selberg / Physical-`k=1` /
  Ω / `S_live` / final-splice programme, whose ledger is
  `Erdos287.Effectivity.latestEvidence` with cut set `Erdos287.Effectivity.latestCutSet`;
* **Route D** — the Direct Reciprocal programme of this namespace, with ledger
  `Erdos287.Direct.directEvidence` and cut `Erdos287.Direct.directCutSet`.

The ledgers are **not merged**.  This file proves that

* the Route-S ledger and cut set are bit-for-bit unchanged (`routeS_ledger_preserved`,
  `routeS_cutSet_unchanged`);
* no node of either route is discharged by the other (`routes_do_not_discharge_each_other`);
* the only cross-route formal dependencies are the *proved* bridges to the shared problem
  predicate and to the elementary top-layer package (`cross_route_bridges_proved`);
* the certified finite frontier is exactly the existing ceiling, with `U2` still pending
  (`finite_frontier_integrity`).

§20 (hostile audit) is discharged by explicit refutations of four tempting steps.
-/

open scoped BigOperators

namespace Erdos287
namespace Direct

/-! ## D.43  Route-S ledger preservation -/

/-- **`routeS_ledger_preserved`.**  `KERNEL-PROVED`.  The Route-S evidence classes are exactly
as banked; this file adds nodes to a *separate* ledger and rewrites none of them. -/
theorem routeS_ledger_preserved :
    Effectivity.latestEvidence .finiteCeilingHere = Effectivity.EvidenceLatest.kernelProved ∧
    Effectivity.latestEvidence .finiteCeilingU2 =
      Effectivity.EvidenceLatest.pendingExternalImport ∧
    Effectivity.latestEvidence .fivePrimeSourceGeometry =
      Effectivity.EvidenceLatest.kernelProved ∧
    Effectivity.latestEvidence .selbergFiniteAlgebra = Effectivity.EvidenceLatest.kernelProved ∧
    Effectivity.latestEvidence .tBoxCapacityBound =
      Effectivity.EvidenceLatest.conditionalAnalytic ∧
    Effectivity.latestEvidence .fixedConductorCharacterBound =
      Effectivity.EvidenceLatest.falseClaim ∧
    Effectivity.latestEvidence .pointwiseK1Target = Effectivity.EvidenceLatest.falseClaim ∧
    Effectivity.latestEvidence .centredK1Qualitative =
      Effectivity.EvidenceLatest.retiredNonclosing ∧
    Effectivity.latestEvidence .erdos287 = Effectivity.EvidenceLatest.openNode :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`routeS_cutSet_unchanged`.**  `KERNEL-PROVED`.  The Route-S cut set is the supplied
ten-node list, in the supplied order. -/
theorem routeS_cutSet_unchanged :
    Effectivity.latestCutSet =
      [Effectivity.LatestNode.physicalK1Quantitative,
        Effectivity.LatestNode.boxAllocationAffordability,
        Effectivity.LatestNode.omegaTwo, Effectivity.LatestNode.omegaOne,
        Effectivity.LatestNode.early4490Residual, Effectivity.LatestNode.properGamma,
        Effectivity.LatestNode.sLive, Effectivity.LatestNode.r012,
        Effectivity.LatestNode.signedFloor, Effectivity.LatestNode.finalSplice] := rfl

/-! ## D.44  No cross-route discharge -/

/-- **`routes_do_not_discharge_each_other`.**  `KERNEL-PROVED`.  Every node of each route's cut
is still open in its own ledger: nothing proved in one route has been used to tag a node of the
other closed. -/
theorem routes_do_not_discharge_each_other :
    (∀ n ∈ Effectivity.latestCutSet,
        Effectivity.latestEvidence n = Effectivity.EvidenceLatest.openNode) ∧
      (∀ n ∈ directCutSet, directEvidence n = EvidenceDirect.openNode) :=
  ⟨Effectivity.cutSet_all_open, directCut_all_open⟩

/-- **`cross_route_bridges_proved`.**  `KERNEL-PROVED`.  The cross-route bridges that exist are
exactly these two, and both are theorems: Route D's source compiles into the shared exact #287
predicate, and the elementary top-layer congruence applies to Route-D counterexamples. -/
theorem cross_route_bridges_proved :
    (∀ (a M : ℕ) (eps : ℕ → Bool), DirectCounterexample a M eps →
      Erdos287Counterexample (selected a M eps)) ∧
    (∀ (a M : ℕ) (eps : ℕ → Bool), DirectCounterexample a M eps → ∀ p : ℕ, p.Prime →
      1 ≤ topExp (selected a M eps) p →
      (∑ x ∈ topLayer (selected a M eps) p, (((ordCompl[p] x : ℕ) : ZMod p))⁻¹) = 0) :=
  ⟨fun _ _ _ h => directCounterexample_to_exact h,
    fun _ _ _ h _ hp he => direct_topLayer_congruence h hp he⟩

/-! ## D.45  Finite-frontier integrity -/

/-- **`finite_frontier_integrity`.**  `KERNEL-PROVED`.  The only finite exclusion certified in
this repository is the existing ceiling `67108856338751594`; the announced `U2` range is not
supplied, is strictly larger, and no theorem here asserts it.  Route D adds **no** finite
exclusion claim. -/
theorem finite_frontier_integrity :
    (∀ {A : Finset ℕ} (h : Erdos287Counterexample A),
        A.max' h.nonempty ≤ extendedCeiling → False) ∧
      extendedCeiling = 67108856338751594 ∧
      extendedCeiling < Effectivity.U2 ∧
      Effectivity.latestEvidence .finiteCeilingU2 =
        Effectivity.EvidenceLatest.pendingExternalImport := by
  refine ⟨fun h hM => Effectivity.finite_ceiling_here h hM, rfl, ?_, rfl⟩
  exact Effectivity.u2_reconciliation_pending.2.2

/-! ## D.46  Hostile audit (§20) -/

/-- **Audit 1 — conditional survivor ⇏ actual survivor.**  `KERNEL-PROVED`.  The
kernel-extension interface is a genuine hypothesis: it is *false* for an explicit feasible
kernel (window `[2,3]` with both positions pinned selected, whose only realisation has
reciprocal sum `5/6`).  So a survivor conditional on the interface is not an actual survivor. -/
theorem kernelExtension_can_fail :
    ¬ KernelExtensionInterface ⟨{2, 3}, ∅, {2, 3}⟩ 2 3 := by
  intro hext
  obtain ⟨eps', hreal, -, hsum⟩ :=
    hext (fun _ => true) ⟨by simp, by simp, by intro n _ _; simp⟩
  have h2 : eps' 2 = true := hreal.2.1 2 (by decide)
  have h3 : eps' 3 = true := hreal.2.1 3 (by decide)
  have hsel : selected 2 3 eps' = {2, 3} := by
    ext x
    simp only [mem_selected, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, -⟩; omega
    · rintro (rfl | rfl)
      · exact ⟨⟨le_refl _, by omega⟩, h2⟩
      · exact ⟨⟨by omega, le_refl _⟩, h3⟩
  rw [hsel] at hsum
  norm_num [recipSum] at hsum

/-- **Audit 2 — independent feasibility ⇏ common feasibility.**  `KERNEL-PROVED`.  Two kernels
that are individually feasible on the same window can have no common realisation. -/
theorem independent_feasibility_not_common :
    Feasible ⟨{3}, ∅, {3}⟩ 2 10 ∧ Feasible ⟨{3}, {3}, ∅⟩ 2 10 ∧
      ¬ Feasible ⟨{3}, {3}, {3}⟩ 2 10 := by
  refine ⟨⟨fun _ => true, by simp, by simp, by intro n _ _; simp⟩, ?_, ?_⟩
  · refine ⟨fun n => decide (n ≠ 3), ?_, by simp, ?_⟩
    · intro n hn
      have : n = 3 := by simpa using hn
      simp [this]
    · intro n _ _
      by_cases h : n = 3
      · right; simp [h]
      · left; simp [h]
  · intro hfeas
    have hdisj := feasible_pins_disjoint hfeas
    rw [Finset.disjoint_left] at hdisj
    have h3 : (3 : ℕ) ∈ ({3} : Finset ℕ) := by decide
    exact hdisj h3 h3

/-- **Audit 3 — approximate straddling ⇏ exact equality.**  `KERNEL-PROVED` (re-exported). -/
theorem straddling_not_exact :
    (1 : ℚ) - 1 / 2 ≤ 1 / 2 ∧ (1 : ℚ) / 2 ≤ 1 ∧ (1 : ℚ) ≤ 3 / 2 ∧ (3 : ℚ) / 2 ≤ 1 + 1 / 2 ∧
      (1 : ℚ) / 2 ≠ 1 ∧ (3 : ℚ) / 2 ≠ 1 :=
  targetStraddling_is_not_exactness

/-- **Audit 4 — a value-moving switch is *not* automatically tracked-component neutral.**
`KERNEL-PROVED`.  The switch `4 ↦ 7` on the window `[2,8]` satisfies every local condition of
`ProtectedSwitch`, yet the additive statistic `n ↦ n` changes from `28` to `31`; neutrality
therefore genuinely needs the agreement hypothesis of `tracked_sum_invariant`. -/
theorem trackedNeutrality_needs_agreement :
    ProtectedSwitch 2 8 (fun n => decide (n ≠ 7)) 4 7 ∧
      (∑ n ∈ selected 2 8 (fun n => decide (n ≠ 7)), (n : ℤ)) = 28 ∧
      (∑ n ∈ selected 2 8 (toggle (fun n => decide (n ≠ 7)) 4 7), (n : ℤ)) = 31 := by
  refine ⟨⟨by decide, by decide, by omega, by omega, by omega, by decide, by decide⟩, ?_, ?_⟩
  · decide
  · decide

/-- **Audit 5 — no finite claim beyond the certified ceiling.**  `KERNEL-PROVED` bookkeeping.
Route D introduces no finite exclusion node at all, so no report-level frontier can leak into
the formal ledger through it. -/
theorem routeD_adds_no_finite_claim :
    (∀ n : DirectNode, directEvidence n ≠ EvidenceDirect.finiteCertificatePending) := by
  intro n
  cases n <;> decide

/-! ## D.47  The final status -/

/-- **`erdos287_open_in_both_routes`.**  `KERNEL-PROVED`.  Erdős #287 is recorded open in both
ledgers, and neither route's cut is empty. -/
theorem erdos287_open_in_both_routes :
    Effectivity.latestEvidence .erdos287 = Effectivity.EvidenceLatest.openNode ∧
      directEvidence .erdos287 = EvidenceDirect.openNode ∧
      Effectivity.latestCutSet ≠ [] ∧ directCutSet ≠ [] :=
  ⟨rfl, rfl, by decide, by decide⟩

/-! ## D.48  Axiom audit -/

#print axioms Erdos287.Direct.directCounterexample_to_exact
#print axioms Erdos287.Direct.exact_to_directCounterexample
#print axioms Erdos287.Direct.compiler_ambient
#print axioms Erdos287.Direct.largePrime_factorisation_unique
#print axioms Erdos287.Direct.prime_pow_dvd_LN
#print axioms Erdos287.Direct.LN_succ_eq
#print axioms Erdos287.Direct.carry_aggregate
#print axioms Erdos287.Direct.descending_recurrence
#print axioms Erdos287.Direct.pathPoly_coeff
#print axioms Erdos287.Direct.exact_reciprocal_target
#print axioms Erdos287.Direct.pathPoly_recurrence
#print axioms Erdos287.Direct.pathPoly_mul_of_separated
#print axioms Erdos287.Direct.char_sum_identity
#print axioms Erdos287.Direct.subsetSumCount_pos_of_bound
#print axioms Erdos287.Direct.allTargets_of_expSumInterface
#print axioms Erdos287.Direct.card_ge_of_attainsAllTargets
#print axioms Erdos287.Direct.sixSwitch_identity
#print axioms Erdos287.Direct.recipSum_toggle
#print axioms Erdos287.Direct.toggle_preserves_isolation
#print axioms Erdos287.Direct.greedy_crossing
#print axioms Erdos287.Direct.targetTuning_of
#print axioms Erdos287.Direct.absorber_lattice_necessary
#print axioms Erdos287.Direct.direct_topLayer_congruence
#print axioms Erdos287.Direct.kernelExtension_can_fail
#print axioms Erdos287.Direct.independent_feasibility_not_common
#print axioms Erdos287.Direct.trackedNeutrality_needs_agreement
#print axioms Erdos287.Direct.routeS_ledger_preserved
#print axioms Erdos287.Direct.finite_frontier_integrity
#print axioms Erdos287.Direct.erdos287_open_in_both_routes

end Direct
end Erdos287
