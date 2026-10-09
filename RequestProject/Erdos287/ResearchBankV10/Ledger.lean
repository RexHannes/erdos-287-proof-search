import RequestProject.Erdos287.ResearchBankV9.Ledger

/-!
# Erdős #287 — Research Bank V10 §P: epoch-aware ledger and status firewall

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Bookkeeping plus *proved* meta-statements only.  Rows are data; they never inhabit a mathematical
proposition.

* `StatusV10` extends the V8/V9 scale injectively (`ofV8_injective`) with the V10 labels
  `FROZEN BANK`, `REPAIRED (conditional on visible providers)`, `EXACT PASS`, `NONE`;
* `v10Ledger = (V9 ledger, embedded verbatim) ++ v10New`;
* `v10_preserves_v9_ledger` — every V9 row appears in V10 with the **same** name, status, evidence
  and epoch, and the V9 ledger is literally a prefix;
* `v10_no_reclassification` — no V10 row re-lists a V9 row name with a different status (so no
  V8/V9 `KILL` becomes `PAY` and no `OPEN` becomes `CLOSED` by reclassification);
* `v10_no_closed`, `v10_erdos287_open`, `v10_frontier` — the required frontier statuses;
* `no_ledger_path_closes_erdos287_v10` — along the V10 closure DAG, propagation from the rows with
  status `PROVED` / `EXACT PASS` / `FROZEN BANK` reaches a fixpoint that does not contain
  `Erdős #287` (nor the asymptotic composition, `M_an`, the finite architecture or the splice).
-/

namespace Erdos287
namespace ResearchBankV10
namespace Ledger

open Erdos287.ResearchBankV8.Ledger

/-- The V10 status scale. -/
inductive StatusV10
  | old (s : StatusV8)
  | frozenBank
  | repairedConditional
  | exactPass
  | none
  deriving DecidableEq, Repr

/-- Embedding of the V8/V9 scale. -/
def ofV8 : StatusV8 → StatusV10 := StatusV10.old

theorem ofV8_injective : Function.Injective ofV8 := fun _ _ h => by cases h; rfl

/-- V10 epochs. -/
inductive EpochV10
  | old (e : EpochV8)
  | astraRepair
  | effectiveHandoff
  deriving DecidableEq, Repr

/-- A V10 ledger row. -/
structure RowV10 where
  name : String
  epoch : EpochV10
  status : StatusV10
  evidence : EvidenceV8
  deriving DecidableEq, Repr

/-- Verbatim embedding of a V8/V9 row. -/
def embed (r : RowV8) : RowV10 := ⟨r.name, .old r.epoch, .old r.status, r.evidence⟩

/-- The frozen V9 ledger, embedded verbatim. -/
def v9Frozen : List RowV10 := ResearchBankV9.Ledger.v9Ledger.map embed

/-- The new V10 rows. -/
def v10New : List RowV10 :=
  [ ⟨"paired zero-mode algebra", .astraRepair, .frozenBank, .kernelProof⟩
  , ⟨"zero/raw-cut composition", .astraRepair, .frozenBank, .researchRecord⟩
  , ⟨"physical pruning interfaces", .astraRepair, .frozenBank, .researchRecord⟩
  , ⟨"R10/R00 elementary payment", .astraRepair, .frozenBank, .researchRecord⟩
  , ⟨"rough gcd/lcm algebra", .astraRepair, .frozenBank, .kernelProof⟩
  , ⟨"small-total-modulus BV interface", .astraRepair, .frozenBank, .externalInterface⟩
  , ⟨"Type-I e-rescaling (exact change of variables, lattice identity)", .astraRepair,
      .old .proved, .kernelProof⟩
  , ⟨"forgetting e | rho in the rescaling (density 1/10 -> 1/5)", .astraRepair,
      .old .falseStatement, .finiteFixture⟩
  , ⟨"common Bonferroni roughness layer (sandwich, shell, s0^J/J!)", .astraRepair,
      .old .proved, .kernelProof⟩
  , ⟨"Type-I grouped coefficient dependency contract", .astraRepair, .old .proved, .kernelProof⟩
  , ⟨"smooth Type-I incl. e-rescaling and sum_e T_e", .astraRepair, .repairedConditional,
      .conditionalOnInterfaces⟩
  , ⟨"compatible-alpha count = d (not |k| d)", .astraRepair, .old .proved, .kernelProof⟩
  , ⟨"old |k| d compatible-cell count", .astraRepair, .old .falseStatement, .finiteFixture⟩
  , ⟨"Type-II grouped coefficient on (u,v,w); reciprocal phase", .astraRepair, .old .proved,
      .kernelProof⟩
  , ⟨"restored Type-II compatible-cell estimate", .astraRepair, .repairedConditional,
      .conditionalOnInterfaces⟩
  , ⟨"high-H / low-H counting identities and cost comparison", .astraRepair, .old .proved,
      .kernelProof⟩
  , ⟨"high-H / low-H composition", .astraRepair, .repairedConditional, .conditionalOnInterfaces⟩
  , ⟨"endpoint-only HB coverage argument", .astraRepair, .old .killedMethod, .finiteFixture⟩
  , ⟨"HB selection trichotomy (I / II / III)", .astraRepair, .old .proved, .kernelProof⟩
  , ⟨"full actual-support HB routing", .astraRepair, .repairedConditional,
      .conditionalOnInterfaces⟩
  , ⟨"level-D well-factorable => truncated well-factorable", .astraRepair,
      .old .falseStatement, .finiteFixture⟩
  , ⟨"rough seed convolution identities", .astraRepair, .old .proved, .kernelProof⟩
  , ⟨"Zheng Kloosterman input", .astraRepair, .old .conditional, .externalInterface⟩
  , ⟨"ordinary BV input", .astraRepair, .old .conditional, .externalInterface⟩
  , ⟨"rough-seed SW input", .astraRepair, .old .conditional, .externalInterface⟩
  , ⟨"asymptotic composition", .astraRepair, .repairedConditional, .conditionalOnInterfaces⟩
  , ⟨"exponent gate > 78/145", .astraRepair, .exactPass, .kernelProof⟩
  , ⟨"explicit numerical M_an", .astraRepair, .none, .researchRecord⟩
  , ⟨"viable finite architecture / overlapping finite certificate", .astraRepair, .old .open,
      .researchRecord⟩
  , ⟨"effective finite splice", .astraRepair, .old .blocked, .researchRecord⟩
  , ⟨"Erdős #287", .astraRepair, .old .open, .researchRecord⟩ ]

/-- The complete V10 ledger. -/
def v10Ledger : List RowV10 := v9Frozen ++ v10New

set_option maxRecDepth 100000

/-- **V10 preserves every V9 status**: the embedded V9 ledger is a prefix of the V10 ledger, and
every V9 row appears with the same name, status, evidence and epoch. -/
theorem v10_preserves_v9_ledger :
    v10Ledger.take ResearchBankV9.Ledger.v9Ledger.length = v9Frozen ∧
    ∀ r ∈ ResearchBankV9.Ledger.v9Ledger, ∃ r' ∈ v10Ledger,
      r'.name = r.name ∧ r'.status = .old r.status ∧ r'.evidence = r.evidence ∧
        r'.epoch = .old r.epoch := by
  refine ⟨?_, fun r hr => ⟨embed r, List.mem_append_left _ (List.mem_map_of_mem hr), rfl, rfl,
    rfl, rfl⟩⟩
  unfold v10Ledger
  rw [List.take_append_of_le_length (by simp [v9Frozen])]
  simp [v9Frozen]

/-- No V10 row is `CLOSED`. -/
theorem v10New_no_closed : ∀ r ∈ v10New, r.status ≠ .old .closed := by decide

/-- **No `CLOSED` row anywhere in V10.** -/
theorem v10_no_closed : ∀ r ∈ v10Ledger, r.status ≠ .old .closed := by
  intro r hr
  rcases List.mem_append.1 hr with h | h
  · obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 h
    intro hc
    exact ResearchBankV9.Ledger.v9_no_closed r₀ hr₀ (by simpa [embed] using hc)
  · exact v10New_no_closed r h

/-- **No reclassification**: a V10 row re-listing a V9 row name has the same status. -/
theorem v10_no_reclassification :
    ∀ r ∈ ResearchBankV9.Ledger.v9Ledger, ∀ r' ∈ v10New, r'.name = r.name →
      r'.status = .old r.status := by decide

/-- **Erdős #287 is `OPEN`**, never `CLOSED`. -/
theorem v10_erdos287_open :
    (∀ r ∈ v10New, r.name = "Erdős #287" → r.status = .old .open) ∧
    (∃ r ∈ v10New, r.name = "Erdős #287" ∧ r.status = .old .open) ∧
    (∀ r ∈ v10Ledger, r.status ≠ .old .closed) :=
  ⟨by decide, by decide, v10_no_closed⟩

/-- **The frontier** required by the Astra repair. -/
theorem v10_frontier :
    (∃ r ∈ v10New, r.name = "zero/raw-cut composition" ∧ r.status = .frozenBank) ∧
    (∃ r ∈ v10New, r.name = "R10/R00 elementary payment" ∧ r.status = .frozenBank) ∧
    (∃ r ∈ v10New, r.name = "smooth Type-I incl. e-rescaling and sum_e T_e" ∧
      r.status = .repairedConditional) ∧
    (∃ r ∈ v10New, r.name = "restored Type-II compatible-cell estimate" ∧
      r.status = .repairedConditional) ∧
    (∃ r ∈ v10New, r.name = "high-H / low-H composition" ∧ r.status = .repairedConditional) ∧
    (∃ r ∈ v10New, r.name = "full actual-support HB routing" ∧ r.status = .repairedConditional) ∧
    (∃ r ∈ v10New, r.name = "exponent gate > 78/145" ∧ r.status = .exactPass) ∧
    (∃ r ∈ v10New, r.name = "explicit numerical M_an" ∧ r.status = .none) ∧
    (∃ r ∈ v10New, r.name = "viable finite architecture / overlapping finite certificate" ∧
      r.status = .old .open) ∧
    (∃ r ∈ v10New, r.name = "asymptotic composition" ∧ r.status = .repairedConditional) ∧
    (∃ r ∈ v10New, r.name = "effective finite splice" ∧ r.status = .old .blocked) ∧
    (∃ r ∈ v10New, r.name = "endpoint-only HB coverage argument" ∧
      r.status = .old .killedMethod) := by
  decide

/-- `PROVED` / `EXACT PASS` require a kernel proof; research-record / external rows are never
`PROVED`. -/
theorem v10_proved_implies_kernel :
    ∀ r ∈ v10New, (r.status = .old .proved ∨ r.status = .exactPass) →
      r.evidence = .kernelProof := by decide

theorem v10_record_external_not_proved :
    ∀ r ∈ v10New, (r.evidence = .researchRecord ∨ r.evidence = .externalInterface) →
      r.status ≠ .old .proved ∧ r.status ≠ .exactPass := by decide

/-! ## The V10 closure DAG -/

/-- The V10 closure DAG (schematic research DAG). -/
def closureDAG : List ResearchBankV9.Ledger.Edge :=
  [ ⟨["smooth Type-I incl. e-rescaling and sum_e T_e", "restored Type-II compatible-cell estimate",
      "ordinary BV input", "rough-seed SW input", "Zheng Kloosterman input",
      "full actual-support HB routing"], "asymptotic composition"⟩
  , ⟨["asymptotic composition", "explicit numerical M_an"], "effective analytic threshold"⟩
  , ⟨["effective analytic threshold", "viable finite architecture / overlapping finite certificate"],
      "effective finite splice"⟩
  , ⟨["effective finite splice"], "Erdős #287"⟩ ]

/-- The base nodes: `PROVED`, `EXACT PASS`, `FROZEN BANK`. -/
def baseNodes : List String :=
  (v10New.filter fun r => r.status = .old .proved ∨ r.status = .exactPass ∨
    r.status = .frozenBank).map (·.name)

/-- One propagation step. -/
def step (S : List String) : List String :=
  S ++ (closureDAG.filter fun e => e.premises.all fun p => p ∈ S).map (·.conclusion)

/-- `n` propagation steps. -/
def derivable : ℕ → List String
  | 0 => baseNodes
  | n + 1 => step (derivable n)

theorem step_baseNodes : step baseNodes = baseNodes := by decide

theorem derivable_eq (n : ℕ) : derivable n = baseNodes := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [derivable, ih, step_baseNodes]

/-- **No V10 ledger path closes Erdős #287** (nor the composition, `M_an` or the splice). -/
theorem no_ledger_path_closes_erdos287_v10 (n : ℕ) :
    "Erdős #287" ∉ derivable n ∧ "asymptotic composition" ∉ derivable n ∧
    "effective analytic threshold" ∉ derivable n ∧ "effective finite splice" ∉ derivable n := by
  rw [derivable_eq]; decide

/-- Every DAG edge has a premise outside the base nodes. -/
theorem every_edge_has_open_premise :
    ∀ e ∈ closureDAG, ∃ p ∈ e.premises, p ∉ baseNodes := by decide

end Ledger
end ResearchBankV10
end Erdos287
