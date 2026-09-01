import RequestProject.Erdos287.OrderedSequenceBridge
import RequestProject.Status.SemanticFirewallsErdos287

/-!
# Erdős #287 — public-tree reconciliation layer (2026-09-01), append-only

This module is a **new status layer**: it describes the *current public tree* only, and it
does not rewrite, weaken or contradict any earlier status file.  Where an earlier layer and
this one disagree about a *label*, the rule recorded in
`RequestProject/Status/CurrentAuthoritativeStatusErdos287.lean` continues to apply: later
layers govern labels, never mathematical content.

Contents.

* §1 Node classification of the current public tree
  (`kernelProved`, `analyticBankMetadataOnly`, `conditionalSourceInterface`, `open_`,
  `superseded`, `retracted`), with node *kinds* (finite theorem, local analytic interface,
  source-normalisation interface, `WindowPairSupply`, end-to-end compiler, public
  statement).
* §2 The dependency DAG with terminal node `Erdos287Statement`, proved acyclic by an
  explicit rank function, plus the guard that *no node is labelled closed merely because an
  implication theorem exists*.
* §3 The end-to-end firewall: the exact compiler is reconfirmed, and the closure input is
  proved to have genuine arithmetic content (it is **not** vacuously inhabitable, and every
  inhabitant supplies two large prime powers at consecutive positions).
* §4 A metadata ledger recording that no banked local analytic interface constructs an
  `Erdos287ClosureInputs` inhabitant.
* §5 Additional machine-checkable semantic guards (Ω-norm weighting, packet vs aggregate,
  interface-vs-theorem separation) completing the hygiene audit.

Erdős #287 is **not** claimed to be solved anywhere in this file or in this repository.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace PublicTree20260901

/-! ## §1  Node classification of the current public tree -/

/-- The only admissible classifications of a node of the current public tree. -/
inductive NodeStatus
  /-- A literal Lean theorem, kernel-checked, with no undischarged mathematical hypothesis. -/
  | kernelProved
  /-- Metadata only: a label, ledger row or bookkeeping structure — *not* a mathematical
  theorem about the objects it names. -/
  | analyticBankMetadataOnly
  /-- A conditional interface: a Lean statement whose analytic hypotheses are explicit and
  undischarged in this repository. -/
  | conditionalSourceInterface
  /-- Open: neither proved nor reduced to anything proved here. -/
  | open_
  /-- Superseded by a later formulation (superseded ≠ false). -/
  | superseded
  /-- Retracted: withdrawn as a claim. -/
  | retracted
  deriving DecidableEq, Fintype, Repr

/-- The kind of object a node is, independently of its status. -/
inductive NodeKind
  /-- A finite, fully verified arithmetic theorem. -/
  | finiteTheorem
  /-- A local analytic interface (hypothesis shell). -/
  | localAnalyticInterface
  /-- A source-normalisation interface. -/
  | sourceNormalisationInterface
  /-- The `WindowPairSupply` arithmetic supply statement. -/
  | windowPairSupplyKind
  /-- The final end-to-end compiler. -/
  | endToEndCompiler
  /-- The public statement of the problem. -/
  | publicStatement
  deriving DecidableEq, Fintype, Repr

/-- The nodes of the current public tree that this layer classifies. -/
inductive Node
  /-- `Erdos287Statement`: the exact public statement (set form). -/
  | erdos287Statement
  /-- `Erdos287SeqStatement`: the published ordered-sequence form. -/
  | erdos287SeqStatement
  /-- The equivalence of the two public formulations. -/
  | statementEquivalence
  /-- `no_Erdos287Counterexample_of_closure`: the end-to-end compiler. -/
  | endToEndCompiler
  /-- `WindowPairSupply` above an explicit threshold (the single closure input). -/
  | windowPairSupply
  /-- The kernel-verified finite range `3 ≤ M ≤ 4·10⁹`. -/
  | finiteRange
  /-- The window-certificate engine (`CVal`, `excludedPP_of_window_le`, `blocker_window`). -/
  | windowCertificateEngine
  /-- The top-layer congruence package and its corollaries. -/
  | topLayerPackage
  /-- The prime-free / prime-maximum blockers. -/
  | primeBlockers
  /-- The sign-sensitive Sophie interface. -/
  | sophieInterface
  /-- Banked local analytic interfaces (product energy, Ξ-gcd tail, affine product energy,
  Ω weighted divisor moment, simultaneous-critical packet, …). -/
  | localAnalyticInterfaces
  /-- Source-normalisation interfaces (Perron / nuclear normalisation, source length). -/
  | sourceNormalisationInterfaces
  /-- The naive full-CRT signless-pair DFT route. -/
  | naiveFullCRTRoute
  /-- The old local scalar route. -/
  | oldLocalScalarRoute
  deriving DecidableEq, Fintype, Repr

/-- Authoritative status of each node of the current public tree. -/
def nodeStatus : Node → NodeStatus
  | .erdos287Statement => .open_
  | .erdos287SeqStatement => .open_
  | .statementEquivalence => .kernelProved
  | .endToEndCompiler => .kernelProved
  | .windowPairSupply => .open_
  | .finiteRange => .kernelProved
  | .windowCertificateEngine => .kernelProved
  | .topLayerPackage => .kernelProved
  | .primeBlockers => .kernelProved
  | .sophieInterface => .kernelProved
  | .localAnalyticInterfaces => .conditionalSourceInterface
  | .sourceNormalisationInterfaces => .conditionalSourceInterface
  | .naiveFullCRTRoute => .retracted
  | .oldLocalScalarRoute => .superseded

/-- The kind of each node. -/
def nodeKind : Node → NodeKind
  | .erdos287Statement => .publicStatement
  | .erdos287SeqStatement => .publicStatement
  | .statementEquivalence => .finiteTheorem
  | .endToEndCompiler => .endToEndCompiler
  | .windowPairSupply => .windowPairSupplyKind
  | .finiteRange => .finiteTheorem
  | .windowCertificateEngine => .finiteTheorem
  | .topLayerPackage => .finiteTheorem
  | .primeBlockers => .finiteTheorem
  | .sophieInterface => .finiteTheorem
  | .localAnalyticInterfaces => .localAnalyticInterface
  | .sourceNormalisationInterfaces => .sourceNormalisationInterface
  | .naiveFullCRTRoute => .localAnalyticInterface
  | .oldLocalScalarRoute => .localAnalyticInterface

/-- **Classification firewall.**  The public statement, its ordered form and the supply
input are all `open_`; the analytic interfaces are conditional; nothing analytic is
`kernelProved`. -/
theorem classification_of_open_nodes :
    nodeStatus .erdos287Statement = .open_ ∧
      nodeStatus .erdos287SeqStatement = .open_ ∧
      nodeStatus .windowPairSupply = .open_ ∧
      nodeStatus .localAnalyticInterfaces = .conditionalSourceInterface ∧
      nodeStatus .sourceNormalisationInterfaces = .conditionalSourceInterface := by
  decide +kernel

/-- **No analytic node is kernel-proved.**  Every node whose kind is a local analytic or
source-normalisation interface carries a non-`kernelProved` status. -/
theorem analytic_nodes_not_kernelProved :
    ∀ n : Node,
      (nodeKind n = .localAnalyticInterface ∨
        nodeKind n = .sourceNormalisationInterface) →
      nodeStatus n ≠ .kernelProved := by
  decide +kernel

/-- Exactly seven nodes of the current public tree are kernel-proved finite/compiler nodes. -/
theorem kernelProved_node_count :
    (Finset.univ.filter (fun n : Node => nodeStatus n = .kernelProved)).card = 7 := by
  decide +kernel

/-! ## §2  The dependency DAG, terminal at `Erdos287Statement` -/

/-- `dependsOn a b = true` means: closing `a` requires `b`. -/
def dependsOn : Node → Node → Bool
  | .erdos287Statement, .endToEndCompiler => true
  | .erdos287Statement, .windowPairSupply => true
  | .erdos287SeqStatement, .erdos287Statement => true
  | .endToEndCompiler, .finiteRange => true
  | .endToEndCompiler, .windowCertificateEngine => true
  | .finiteRange, .windowCertificateEngine => true
  | .windowCertificateEngine, .topLayerPackage => true
  | .primeBlockers, .topLayerPackage => true
  | .sophieInterface, .windowCertificateEngine => true
  | .windowPairSupply, .localAnalyticInterfaces => true
  | .localAnalyticInterfaces, .sourceNormalisationInterfaces => true
  | _, _ => false

/-- A rank witnessing acyclicity: every dependency strictly decreases the rank. -/
def rank : Node → ℕ
  | .erdos287SeqStatement => 7
  | .erdos287Statement => 6
  | .endToEndCompiler => 5
  | .windowPairSupply => 5
  | .finiteRange => 4
  | .sophieInterface => 4
  | .primeBlockers => 4
  | .windowCertificateEngine => 3
  | .topLayerPackage => 2
  | .localAnalyticInterfaces => 3
  | .sourceNormalisationInterfaces => 2
  | .naiveFullCRTRoute => 0
  | .oldLocalScalarRoute => 0
  | .statementEquivalence => 1

/-- **The dependency graph is a DAG**: every edge strictly decreases the rank. -/
theorem dependsOn_rank_decreasing :
    ∀ a b : Node, dependsOn a b = true → rank b < rank a := by
  decide +kernel

/-- In particular the graph is irreflexive. -/
theorem dependsOn_irrefl : ∀ n : Node, dependsOn n n = false := by decide +kernel

/-- **`Erdos287Statement` is the terminal node.**  Except for the ordered-sequence
restatement — which is *equivalent* to it, not below it — no node of the tree is required
in order to close the public statement from above: nothing else depends on it. -/
theorem erdos287Statement_terminal :
    ∀ n : Node, n ≠ .erdos287SeqStatement → dependsOn n .erdos287Statement = false := by
  decide +kernel

/-- **Closed-by-implication guard.**  The end-to-end compiler node is `kernelProved`, yet the
statement node it feeds is still `open_`, and the supply node is still `open_`.  Proving an
implication therefore never closes its target. -/
theorem implication_does_not_close_target :
    nodeStatus .endToEndCompiler = .kernelProved ∧
      dependsOn .erdos287Statement .endToEndCompiler = true ∧
      nodeStatus .erdos287Statement = .open_ ∧
      nodeStatus .windowPairSupply = .open_ := by
  decide +kernel

/-! ## §3  End-to-end firewall: the closure input has real arithmetic content -/

/-- **Reconfirmation of the exact end-to-end theorem** `Erdos287ClosureInputs →
Erdos287Statement`.  (Definitional repackaging of `no_Erdos287Counterexample_of_closure`; no
new mathematics.) -/
theorem reconfirm_endToEnd (I : Erdos287ClosureInputs) : Erdos287Statement :=
  no_Erdos287Counterexample_of_closure I

/-- The same compiler in the published ordered form, via the new statement equivalence. -/
theorem reconfirm_endToEnd_seq (I : Erdos287ClosureInputs) : Erdos287SeqStatement :=
  erdos287SeqStatement_of_statement (no_Erdos287Counterexample_of_closure I)

/-- **The `supply` field stays visible.**  Every inhabitant of the closure inputs is exactly
a supply statement above its own threshold. -/
theorem closureInputs_supply_visible (I : Erdos287ClosureInputs) :
    ∀ M : ℕ, I.M0 ≤ M → WindowPairSupply M := I.supply

/-- `WindowPairSupply` fails at `M = 0`: the position constraints are unsatisfiable. -/
theorem not_windowPairSupply_zero : ¬ WindowPairSupply 0 := by
  rintro ⟨x, pu, au, pv, av, -, -, -, -, -, -, -, -, -, -, -, hxL⟩
  omega

/-- `WindowPairSupply` fails at `M = 1`. -/
theorem not_windowPairSupply_one : ¬ WindowPairSupply 1 := by
  rintro ⟨x, pu, au, pv, av, -, -, -, -, -, -, -, -, -, -, hUx, hxL⟩
  omega

/-- `WindowPairSupply` fails at `M = 2`: the only admissible position is `x = 1`, which
carries no prime power. -/
theorem not_windowPairSupply_two : ¬ WindowPairSupply 2 := by
  rintro ⟨x, pu, au, pv, av, hpu, -, hau, -, hdu, -, -, -, -, -, hUx, hxL⟩
  have hx : x = 1 := by omega
  subst hx
  have h1 : pu ^ au = 1 := Nat.dvd_one.mp hdu
  have : pu = 1 := by
    rcases Nat.pow_eq_one.1 h1 with h | h
    · exact h
    · omega
  exact absurd this hpu.ne_one

/-- **The closure input is not vacuously inhabitable.**  Every `Erdos287ClosureInputs` has a
threshold at least `3`, because the supply statement is false below it. -/
theorem closureInputs_threshold_ge_three (I : Erdos287ClosureInputs) : 3 ≤ I.M0 := by
  by_contra h
  push_neg at h
  interval_cases hM : I.M0
  · exact not_windowPairSupply_zero (I.supply 0 (by omega))
  · exact not_windowPairSupply_one (I.supply 1 (by omega))
  · exact not_windowPairSupply_two (I.supply 2 (by omega))

/-- **The supply statement has genuine arithmetic content.**  A window pair at `M` produces
two consecutive positions in the top half of `[1, M]`, each divisible by a prime power
exceeding `M/10`. -/
theorem windowPairSupply_forces_large_primePowers {M : ℕ} (h : WindowPairSupply M) :
    ∃ x qu qv : ℕ,
      M ≤ 2 * x ∧ x + 1 ≤ M ∧ qu ∣ x ∧ qv ∣ (x + 1) ∧ M < 10 * qu ∧ M < 10 * qv := by
  obtain ⟨x, pu, au, pv, av, hpu, hpv, hau, hav, hdu, hdv, hwu, -, hwv, -, hUx, hxL⟩ := h
  have hqu : 0 < pu ^ au := pow_pos hpu.pos _
  have hqv : 0 < pv ^ av := pow_pos hpv.pos _
  refine ⟨x, pu ^ au, pv ^ av, hUx, hxL, hdu, hdv, ?_, ?_⟩
  · have : M / pu ^ au < 10 := by omega
    exact (Nat.div_lt_iff_lt_mul hqu).1 this |>.trans_le (by omega)
  · have : M / pv ^ av < 10 := by omega
    exact (Nat.div_lt_iff_lt_mul hqv).1 this |>.trans_le (by omega)

/-! ## §4  Metadata ledger: no banked interface constructs the closure input -/

/-- The banked local analytic / source interfaces of the current public tree. -/
inductive BankedInterface
  /-- Grouped-`q` product energy. -/
  | groupedProductEnergy
  /-- The Ξ-gcd tail bound. -/
  | xiGcdTailBound
  /-- The affine product energy (Cochrane–Shi type) bound. -/
  | affineProductEnergyBound
  /-- The Ω weighted divisor moment bound. -/
  | omegaWeightedDivisorMoment
  /-- The simultaneous-critical packet. -/
  | simultaneousCriticalPacket
  /-- The dense `q_C` admissibility interface. -/
  | denseQCAdmissible
  /-- The C0 physical normalisation interface. -/
  | c0PhysicalNormalisation
  /-- The transverse carrier interface. -/
  | transverseCarrier
  deriving DecidableEq, Fintype, Repr

/-- **Metadata.**  No banked interface is recorded as constructing an
`Erdos287ClosureInputs` inhabitant.  This is a bookkeeping field, deliberately labelled as
metadata: the mathematical guards live in §3. -/
def constructsClosureInputs : BankedInterface → Bool := fun _ => false

/-- **Uninhabited-inputs ledger.**  All eight banked interfaces are recorded as *not*
constructing a closure-inputs inhabitant. -/
theorem no_banked_interface_constructs_closureInputs :
    (∀ i : BankedInterface, constructsClosureInputs i = false) ∧
      Fintype.card BankedInterface = 8 := by
  refine ⟨fun _ => rfl, by decide +kernel⟩

/-- **Interface ≠ theorem.**  The metadata status `analyticBankMetadataOnly` and the
conditional status `conditionalSourceInterface` are both distinct from `kernelProved`. -/
theorem interface_status_not_theorem :
    NodeStatus.analyticBankMetadataOnly ≠ NodeStatus.kernelProved ∧
      NodeStatus.conditionalSourceInterface ≠ NodeStatus.kernelProved ∧
      NodeStatus.superseded ≠ NodeStatus.retracted := by
  decide +kernel

/-! ## §5  Additional machine-checkable semantic guards -/

/-- **Ω-norm firewall (quantitative form).**  A plain `ℓ²` mass and a divisor-weighted `ℓ²`
mass are genuinely different functionals: they disagree on an explicit vector, so a bound
proved for one may never be quoted for the other. -/
theorem plain_l2_ne_weighted_l2 :
    ∃ (f w : Fin 2 → ℝ), (∀ i, 0 < w i) ∧ ∑ i, (f i) ^ 2 ≠ ∑ i, w i * (f i) ^ 2 := by
  refine ⟨![1, 1], ![1, 2], ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num
  · simp [Fin.sum_univ_two]

/-- **Packet versus aggregate firewall.**  Three packet-level bounds of size `1` do not give
an aggregate bound of size `1`. -/
theorem packetwise_not_aggregate :
    ∃ g : Fin 3 → ℝ, (∀ i, g i ≤ 1) ∧ 1 < ∑ i, g i := by
  refine ⟨fun _ => 1, fun _ => le_refl 1, ?_⟩
  simp

/-- **Supply-is-an-input firewall.**  A proof of the compiler together with the *absence* of
a supply proof yields nothing about the statement: formally, the compiler is a function on
inhabitants, and this layer records `windowPairSupply` as `open_`. -/
theorem supply_is_input_not_output :
    nodeStatus .windowPairSupply = .open_ ∧ nodeKind .windowPairSupply = .windowPairSupplyKind := by
  decide +kernel

end PublicTree20260901
end Erdos287
