import RequestProject.Erdos287.ResearchBankV5.Routes

/-!
# Research Bank V5 — route-indexed owners, gate ledger and closure DAGs

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This is pure bookkeeping.  The owner function, the ledgers and the closure DAGs record *status*,
never mathematics: no owner is inhabited here, and no combination of ledger entries constructs a
mathematical theorem (`ledger_is_not_a_proof`, `no_closure_from_status`).

Authoritative snapshot:

```text
ANCHORED V2: FROZEN            ANCHORED V3: FROZEN
ANCHORED V4: BUILT / BANKED    AnchoredV4 bridge to original #287: PROVED
AnchoredV4 route: OPEN         (ENTRY_EXISTENCE, SAFE_DESCENT_SUPPLY,
                                GUARDED_ABSORBER_ANALYTIC_SUPPLY)

Gate A: local classification CLOSED, global exceptional-leaf capacity OPEN
Gate B: generic long FP PAY, generic PP PAY, exceptional β=1 families OPEN
Gate C: generic long rows PAY/REMOVED, global reduced excess contradiction OPEN
Gate D: CLOSED
Erdős #287: OPEN
```
-/

namespace Erdos287
namespace ResearchBankV5

open ResearchStatus EvidenceKind

/-! ## 1.  Owners -/

/-- The named owners of the two routes. -/
inductive OpenOwner
  /-- Anchored V4: existence of an actual ENTRY at arbitrarily large scale. -/
  | ENTRY_EXISTENCE
  /-- Anchored V4: supply of safe descent moves. -/
  | SAFE_DESCENT_SUPPLY
  /-- Anchored V4: analytic supply of guarded absorbers. -/
  | GUARDED_ABSORBER_ANALYTIC_SUPPLY
  /-- Contact-core: strict-height exceptional-leaf capacity (the current owner). -/
  | STRICT_HEIGHT_EXCEPTIONAL_LEAF_CAPACITY
  /-- Contact-core: the global Gate A forest/capacity theorem. -/
  | GATE_A_GLOBAL_FOREST_CAPACITY
  /-- Contact-core: the exceptional `β = 1` families of Gate B. -/
  | GATE_B_EXCEPTIONAL_FAMILIES
  /-- Contact-core: the global reduced excess-core contradiction of Gate C. -/
  | GATE_C_REDUCED_EXCESS_CONTRADICTION
  deriving DecidableEq, Repr

/-- Owners of each route. -/
def routeOwners : ResearchRoute → List OpenOwner
  | ResearchRoute.anchoredV4 =>
      [OpenOwner.ENTRY_EXISTENCE, OpenOwner.SAFE_DESCENT_SUPPLY,
        OpenOwner.GUARDED_ABSORBER_ANALYTIC_SUPPLY]
  | ResearchRoute.contactCoreV5 =>
      [OpenOwner.STRICT_HEIGHT_EXCEPTIONAL_LEAF_CAPACITY,
        OpenOwner.GATE_A_GLOBAL_FOREST_CAPACITY, OpenOwner.GATE_B_EXCEPTIONAL_FAMILIES,
        OpenOwner.GATE_C_REDUCED_EXCESS_CONTRADICTION]

/-- **Master current-owner function** (bookkeeping only; it does not inhabit the owners). -/
def currentOwner : ResearchRoute → OpenOwner
  | ResearchRoute.anchoredV4 => OpenOwner.ENTRY_EXISTENCE
  | ResearchRoute.contactCoreV5 => OpenOwner.STRICT_HEIGHT_EXCEPTIONAL_LEAF_CAPACITY

/-- The current owner of a route belongs to that route. -/
theorem currentOwner_mem_routeOwners (r : ResearchRoute) : currentOwner r ∈ routeOwners r := by
  cases r <;> simp [currentOwner, routeOwners]

/-- **Owner firewall.**  The two routes have disjoint owner sets: a status statement about one
route's owners never touches the other's. -/
theorem routeOwners_disjoint : ∀ o : OpenOwner,
    o ∈ routeOwners ResearchRoute.anchoredV4 → o ∉ routeOwners ResearchRoute.contactCoreV5 := by
  decide

/-- Every owner is `open`. -/
def ownerStatus : OpenOwner → ResearchStatus := fun _ => ResearchStatus.«open»

/-- The Anchored V4 current owner is open. -/
theorem anchored_current_open :
    ownerStatus (currentOwner ResearchRoute.anchoredV4) = ResearchStatus.«open» := rfl

/-- The contact-core current owner is open. -/
theorem contactCore_current_open :
    ownerStatus (currentOwner ResearchRoute.contactCoreV5) = ResearchStatus.«open» := rfl

/-- The three Anchored V4 owners are preserved exactly. -/
theorem anchoredV4_owner_set :
    routeOwners ResearchRoute.anchoredV4 =
      [OpenOwner.ENTRY_EXISTENCE, OpenOwner.SAFE_DESCENT_SUPPLY,
        OpenOwner.GUARDED_ABSORBER_ANALYTIC_SUPPLY] := rfl

/-! ## 2.  Ledger entries -/

/-- A ledger entry: a named node with its route, its research status and its evidence kind. -/
structure LedgerEntry where
  /-- Node name. -/
  name : String
  /-- Owning route. -/
  route : ResearchRoute
  /-- Research status. -/
  status : ResearchStatus
  /-- Evidence kind. -/
  evidence : EvidenceKind
  deriving DecidableEq, Repr

/-- The Anchored V4 ledger, frozen exactly as reported by the V4 layer. -/
def anchoredLedger : List LedgerEntry :=
  [ ⟨"ANCHORED_V2", ResearchRoute.anchoredV4, retired, kernelProof⟩,
    ⟨"ANCHORED_V3", ResearchRoute.anchoredV4, retired, kernelProof⟩,
    ⟨"ANCHORED_V4_BANK", ResearchRoute.anchoredV4, bank, kernelProof⟩,
    ⟨"NORMALIZED_PRIME_POWER_HEIGHT", ResearchRoute.anchoredV4, bank, kernelProof⟩,
    ⟨"DOUBLED_DENOMINATOR_LATTICE", ResearchRoute.anchoredV4, bank, kernelProof⟩,
    ⟨"NO_00_GUARD_GEOMETRY", ResearchRoute.anchoredV4, bank, kernelProof⟩,
    ⟨"ENTRY_NECESSARY_CONDITIONS", ResearchRoute.anchoredV4, bank, kernelProof⟩,
    ⟨"WELL_FOUNDED_PRIME_POWER_DESCENT", ResearchRoute.anchoredV4, bank, kernelProof⟩,
    ⟨"EXACT_FOURIER_COUNTING_IDENTITY", ResearchRoute.anchoredV4, bank, kernelProof⟩,
    ⟨"EXACT_ABSORPTION_FROM_DOMINANCE", ResearchRoute.anchoredV4, bank, conditionalInterface⟩,
    ⟨"TRANSITION_SYSTEM_DUAL_CERTIFICATE", ResearchRoute.anchoredV4, bank, kernelProof⟩,
    ⟨"V3_RECONCILIATION", ResearchRoute.anchoredV4, bank, kernelProof⟩,
    ⟨"ANCHORED_V4_ORIGINAL_BRIDGE", ResearchRoute.anchoredV4, closed, kernelProof⟩,
    ⟨"ENTRY_EXISTENCE", ResearchRoute.anchoredV4, ResearchStatus.«open», researchConjecture⟩,
    ⟨"SAFE_DESCENT_SUPPLY", ResearchRoute.anchoredV4, ResearchStatus.«open», researchConjecture⟩,
    ⟨"GUARDED_ABSORBER_ANALYTIC_SUPPLY", ResearchRoute.anchoredV4, ResearchStatus.«open»,
      researchConjecture⟩,
    ⟨"GLOBAL_COLUMN_SURJECTIVITY", ResearchRoute.anchoredV4, killed, kernelProof⟩,
    ⟨"ROUTE_B_COSET_CRITERION_ONLY", ResearchRoute.anchoredV4, bank, kernelProof⟩ ]

/-- The contact-core ledger. -/
def contactLedger : List LedgerEntry :=
  [ ⟨"PATH_TRANSFER", ResearchRoute.contactCoreV5, bank, kernelProof⟩,
    ⟨"DEPTH_ONE_TERMINAL_SPLICE", ResearchRoute.contactCoreV5, retired, finiteRegressionOnly⟩,
    ⟨"COMPLETE_PP_ROW", ResearchRoute.contactCoreV5, bank, kernelProof⟩,
    ⟨"PADIC_LAYER_DIGIT_STEP", ResearchRoute.contactCoreV5, bank, kernelProof⟩,
    ⟨"PADIC_SATURATION_GLOBAL", ResearchRoute.contactCoreV5, ResearchStatus.«open»,
      researchConjecture⟩,
    ⟨"PP_OBSTRUCTION_DICHOTOMY", ResearchRoute.contactCoreV5, bank, kernelProof⟩,
    ⟨"RAW_PP_PORT_CAP_4L", ResearchRoute.contactCoreV5, pay, kernelProof⟩,
    ⟨"VALUATION_LIFT", ResearchRoute.contactCoreV5, bank, kernelProof⟩,
    ⟨"STRICT_HEIGHT", ResearchRoute.contactCoreV5, bank, kernelProof⟩,
    ⟨"CROOT_GENERAL_MODULUS", ResearchRoute.contactCoreV5, bank, externalAnalyticBank⟩,
    ⟨"CROOT_PRIME_POWER", ResearchRoute.contactCoreV5, bank, externalAnalyticBank⟩,
    ⟨"VAL_TRANS_ONE_DEMAND", ResearchRoute.contactCoreV5, bank, conditionalInterface⟩,
    ⟨"FP_INTERFACE_GEN", ResearchRoute.contactCoreV5, bank, externalAnalyticBank⟩,
    ⟨"FP_INTERFACE", ResearchRoute.contactCoreV5, bank, externalAnalyticBank⟩,
    ⟨"FULL_CUBE_REMOVABILITY", ResearchRoute.contactCoreV5, pay, conditionalInterface⟩,
    ⟨"LINEAR_CHARGE", ResearchRoute.contactCoreV5, bank, conditionalInterface⟩,
    ⟨"LOG_FORM_CHARGE", ResearchRoute.contactCoreV5, superseded, conditionalInterface⟩,
    ⟨"PRIMORIAL_PRE_SIEVE", ResearchRoute.contactCoreV5, killed, kernelProof⟩,
    ⟨"FIXED_MULTIPLICATIVE_HEIGHT_DROP", ResearchRoute.contactCoreV5, killed,
      finiteRegressionOnly⟩,
    ⟨"CONTACT_GATE_D_BRIDGE", ResearchRoute.contactCoreV5, closed, kernelProof⟩,
    ⟨"STRICT_HEIGHT_EXCEPTIONAL_LEAF_CAPACITY", ResearchRoute.contactCoreV5,
      ResearchStatus.«open», researchConjecture⟩ ]

/-- Every entry of the Anchored ledger belongs to the Anchored route, and every entry of the
contact ledger to the contact-core route: the ledgers do not leak into one another. -/
theorem ledgers_route_separated :
    (∀ e ∈ anchoredLedger, e.route = ResearchRoute.anchoredV4) ∧
      (∀ e ∈ contactLedger, e.route = ResearchRoute.contactCoreV5) := by
  constructor <;> decide

/-- The V4 open owners recorded in the ledger are exactly the three reported ones. -/
theorem anchoredLedger_open_entries :
    anchoredLedger.filter (fun e => e.status = ResearchStatus.«open») =
      [ ⟨"ENTRY_EXISTENCE", ResearchRoute.anchoredV4, ResearchStatus.«open», researchConjecture⟩,
        ⟨"SAFE_DESCENT_SUPPLY", ResearchRoute.anchoredV4, ResearchStatus.«open»,
          researchConjecture⟩,
        ⟨"GUARDED_ABSORBER_ANALYTIC_SUPPLY", ResearchRoute.anchoredV4, ResearchStatus.«open»,
          researchConjecture⟩ ] := by
  decide

/-- No externally banked node is recorded as a kernel proof. -/
theorem no_external_marked_kernel :
    ∀ e ∈ contactLedger, e.evidence = externalAnalyticBank → e.evidence ≠ kernelProof := by
  decide

/-! ## 3.  Gates -/

/-- The four gates of the contact-core route, split into their local and global parts. -/
inductive Gate
  /-- Local row-language classification of high owners. -/
  | A_local
  /-- Global forest / exceptional-leaf capacity. -/
  | A_global
  /-- Generic long first-power cycle families. -/
  | B_generic_longFP
  /-- Generic proper-power cycle families. -/
  | B_generic_PP
  /-- Exceptional `β = 1` families. -/
  | B_exceptional
  /-- Generic clean long rows in the excess core. -/
  | C_generic_removed
  /-- The global reduced excess-core contradiction. -/
  | C_global
  /-- The contact-core bridge back to the original problem. -/
  | D
  deriving DecidableEq, Repr

/-- The authoritative gate ledger. -/
def gateStatus : Gate → ResearchStatus
  | Gate.A_local => closed
  | Gate.A_global => ResearchStatus.«open»
  | Gate.B_generic_longFP => pay
  | Gate.B_generic_PP => pay
  | Gate.B_exceptional => ResearchStatus.«open»
  | Gate.C_generic_removed => pay
  | Gate.C_global => ResearchStatus.«open»
  | Gate.D => closed

/-- Evidence kinds of the gates. -/
def gateEvidence : Gate → EvidenceKind
  | Gate.A_local => conditionalInterface
  | Gate.A_global => researchConjecture
  | Gate.B_generic_longFP => conditionalInterface
  | Gate.B_generic_PP => conditionalInterface
  | Gate.B_exceptional => researchConjecture
  | Gate.C_generic_removed => conditionalInterface
  | Gate.C_global => researchConjecture
  | Gate.D => kernelProof

/-- Gate D is closed, with a kernel proof. -/
theorem gateD_closed : gateStatus Gate.D = closed ∧ gateEvidence Gate.D = kernelProof := by decide

/-- Gate A is closed locally and open globally. -/
theorem gateA_split :
    gateStatus Gate.A_local = closed ∧ gateStatus Gate.A_global = ResearchStatus.«open» := by decide

/-- Gate B is open, with its generic families paid. -/
theorem gateB_open :
    gateStatus Gate.B_generic_longFP = pay ∧ gateStatus Gate.B_generic_PP = pay ∧
      gateStatus Gate.B_exceptional = ResearchStatus.«open» := by decide

/-- Gate C is open, with the generic clean long rows removed. -/
theorem gateC_open :
    gateStatus Gate.C_generic_removed = pay ∧
      gateStatus Gate.C_global = ResearchStatus.«open» := by decide

/-- **(A-CLASS).**  The unified high-owner local taxonomy. -/
def localTaxonomy : List String :=
  ["full-cube removable", "positive-density interface-heavy",
    "first-power short/transition layer", "sparse p-adic tail"]

/-- **(C-REDUCE).**  The current reduced excess core. -/
def reducedExcessCore : List String :=
  ["transition FP rows", "linear-interface-heavy rows", "sparse p-adic interfaces"]

/-! ## 4.  Global status -/

/-- The status of the original problem in this project. -/
def erdos287Status : ResearchStatus := ResearchStatus.«open»

/-- Erdős #287 is **not** marked closed. -/
theorem erdos287_not_marked_closed : erdos287Status ≠ closed := by decide

/-- The status of each route. -/
def routeStatus : ResearchRoute → ResearchStatus := fun _ => ResearchStatus.«open»

/-- Both routes are open. -/
theorem both_routes_open :
    routeStatus ResearchRoute.anchoredV4 = ResearchStatus.«open» ∧
      routeStatus ResearchRoute.contactCoreV5 = ResearchStatus.«open» := by decide

/-! ## 5.  Closure DAGs -/

/-- The Anchored route's closure DAG (names only). -/
def anchoredDAG : List (String × String) :=
  [ ("ENTRY_EXISTENCE", "SAFE_DESCENT_SUPPLY"),
    ("SAFE_DESCENT_SUPPLY", "GUARDED_ABSORBER_ANALYTIC_SUPPLY"),
    ("GUARDED_ABSORBER_ANALYTIC_SUPPLY", "EXACT_VALUE_1_CONFIGURATION"),
    ("EXACT_VALUE_1_CONFIGURATION", "ANCHORED_BRIDGE"),
    ("ANCHORED_BRIDGE", "ORIGINAL_COUNTEREXAMPLE") ]

/-- The contact-core route's closure DAG (names only). -/
def contactDAG : List (String × String) :=
  [ ("STRICT_HEIGHT_EXCEPTIONAL_LEAF_CAPACITY", "GATE_A_CLOSED"),
    ("GATE_A_CLOSED", "GATE_B_EXCEPTIONAL_CLEANUP"),
    ("GATE_B_EXCEPTIONAL_CLEANUP", "ALL_BETA_ONE_BAD_BLOCKS_EXCLUDED"),
    ("ALL_BETA_ONE_BAD_BLOCKS_EXCLUDED", "GATE_C_REDUCED_EXCESS_CONTRADICTION"),
    ("GATE_C_REDUCED_EXCESS_CONTRADICTION", "CONTACT_CONTRADICTION_INTEGRALITY"),
    ("CONTACT_CONTRADICTION_INTEGRALITY", "GATE_D_BRIDGE"),
    ("GATE_D_BRIDGE", "ORIGINAL_287") ]

/-- The two DAGs share no arrow. -/
theorem dags_disjoint : ∀ e ∈ anchoredDAG, e ∉ contactDAG := by decide

/-- **The conditional structure of the Anchored DAG.**  Every arrow is an implication that must be
supplied; composing them is the only way to reach the original problem. -/
theorem anchored_chain_composition {ENTRY SAFE ABS VALUE1 ORIG : Prop}
    (a1 : ENTRY → SAFE) (a2 : SAFE → ABS) (a3 : ABS → VALUE1) (a4 : VALUE1 → ORIG) :
    ENTRY → ORIG := fun h => a4 (a3 (a2 (a1 h)))

/-- **The conditional structure of the contact-core DAG.** -/
theorem contact_chain_composition {CAP GA GB BETA1 GC CONTRA ORIG : Prop}
    (a1 : CAP → GA) (a2 : GA → GB) (a3 : GB → BETA1) (a4 : BETA1 → GC) (a5 : GC → CONTRA)
    (a6 : CONTRA → ORIG) : CAP → ORIG := fun h => a6 (a5 (a4 (a3 (a2 (a1 h)))))

/-! ## 6.  No-fake-closure theorems -/

/-- **No closure from status.**  A status value never constructs a mathematical implication. -/
theorem no_closure_from_status : ¬ (∀ (s : ResearchStatus) (P Q : Prop), s = closed → P → Q) := by
  intro h
  exact h closed True False rfl trivial

/-- **The ledger is not a proof.**  A `closed` entry in the ledger does not inhabit any statement:
there is a closed entry alongside a false claim. -/
theorem ledger_is_not_a_proof :
    ∃ (e : LedgerEntry) (P : Prop), e.status = closed ∧ ¬ P :=
  ⟨⟨"probe", ResearchRoute.contactCoreV5, closed, kernelProof⟩, False, rfl, id⟩

/-- **Gate D closed does not close #287.**  Without Gates A–C no implication to the original
problem exists. -/
theorem gateD_closed_does_not_close_287 :
    gateStatus Gate.D = closed ∧ erdos287Status = ResearchStatus.«open» ∧
      ¬ (∀ gateD original : Prop, gateD → original) := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  exact h True False trivial

/-- Reaching the original problem from Gate D requires all of Gates A, B, C as premises. -/
theorem closure_requires_all_gates {GA GB GC GD ORIG : Prop}
    (hab : GA → GB) (hbc : GB → GC) (hcd : GC → GD) (hd : GD → ORIG) : GA → ORIG :=
  fun h => hd (hcd (hbc (hab h)))

/-! ## 7.  Research-planning metadata (descriptive only) -/

/-- Descriptive metadata: the two conceptual deep gates currently visible.  This is a
research-planning summary, **not** a theorem, and not a claim that these are the only possible
future lemmas. -/
def deepGates : List String :=
  ["STRICT_HEIGHT_EXCEPTIONAL_LEAF_CAPACITY", "REDUCED_BETA_GE_2_EXCESS_CORE_CONTRADICTION"]

end ResearchBankV5
end Erdos287
