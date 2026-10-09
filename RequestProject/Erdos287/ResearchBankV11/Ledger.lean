import RequestProject.Erdos287.ResearchBankV10.Ledger

/-!
# Erdős #287 — Research Bank V11: effective-handoff ledger and closure firewall

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `v11Ledger = v10Ledger ++ v11New`;
* `v11_preserves_v10_ledger` — the V10 ledger is a prefix of the V11 ledger (every V10 row, hence
  every V9 row, keeps its name, status, evidence and epoch);
* `v11_no_reclassification` — no V11 row re-lists a V10 row name with a different status;
* `v11_frontier` — `M_an`: NONE; finite architecture: OPEN; finite splice: BLOCKED;
  asymptotic composition: CONDITIONAL; Erdős #287: OPEN; no `CLOSED` row anywhere;
* `no_ledger_path_closes_erdos287_v11` — the closure DAG fixpoint from the proved rows does not
  contain Erdős #287.
-/

namespace Erdos287
namespace ResearchBankV11
namespace Ledger

open Erdos287.ResearchBankV8.Ledger Erdos287.ResearchBankV10.Ledger

/-- The new V11 rows. -/
def v11New : List RowV10 :=
  [ ⟨"numerical external constant bundle (structure, no instance)", .effectiveHandoff,
      .old .proved, .kernelProof⟩
  , ⟨"generic power-to-log conversion", .effectiveHandoff, .old .proved, .kernelProof⟩
  , ⟨"analytic activation threshold is sufficient (given numerical constants)",
      .effectiveHandoff, .old .proved, .kernelProof⟩
  , ⟨"numerical external constants", .effectiveHandoff, .old .open, .researchRecord⟩
  , ⟨"unknown external constants as numerical activation data", .effectiveHandoff,
      .old .falseStatement, .researchRecord⟩
  , ⟨"explicit numerical M_an", .effectiveHandoff, .none, .researchRecord⟩
  , ⟨"exceptional prime into W as a full solution", .effectiveHandoff, .old .falseStatement,
      .finiteFixture⟩
  , ⟨"exceptional-safe full modulus input", .effectiveHandoff, .old .conditional,
      .externalInterface⟩
  , ⟨"old prescribed CRT architecture (in its stated scope)", .effectiveHandoff,
      .old .killedMethod, .researchRecord⟩
  , ⟨"old small-graph / narrow-simplex positive-score route (in its stated scope)",
      .effectiveHandoff, .old .killedMethod, .researchRecord⟩
  , ⟨"finite architecture contract => eventual exclusion", .effectiveHandoff, .old .proved,
      .kernelProof⟩
  , ⟨"viable finite architecture / overlapping finite certificate", .effectiveHandoff,
      .old .open, .researchRecord⟩
  , ⟨"asymptotic composition", .effectiveHandoff, .repairedConditional,
      .conditionalOnInterfaces⟩
  , ⟨"effective finite splice", .effectiveHandoff, .old .blocked, .researchRecord⟩
  , ⟨"Erdős #287", .effectiveHandoff, .old .open, .researchRecord⟩ ]

/-- The complete V11 ledger. -/
def v11Ledger : List RowV10 := v10Ledger ++ v11New

set_option maxRecDepth 100000

/-- **V11 preserves the V10 ledger** (prefix; every row unchanged). -/
theorem v11_preserves_v10_ledger :
    v11Ledger.take v10Ledger.length = v10Ledger ∧ ∀ r ∈ v10Ledger, r ∈ v11Ledger :=
  ⟨List.take_left, fun _ hr => List.mem_append_left _ hr⟩

/-- Consequently every V9 row is preserved in V11. -/
theorem v11_preserves_v9_ledger :
    ∀ r ∈ ResearchBankV9.Ledger.v9Ledger, ∃ r' ∈ v11Ledger,
      r'.name = r.name ∧ r'.status = .old r.status ∧ r'.evidence = r.evidence := by
  intro r hr
  obtain ⟨r', hr', h1, h2, h3, -⟩ := v10_preserves_v9_ledger.2 r hr
  exact ⟨r', List.mem_append_left _ hr', h1, h2, h3⟩

/-- **No reclassification** of V10 rows by V11. -/
theorem v11_no_reclassification :
    ∀ r ∈ v10Ledger, ∀ r' ∈ v11New, r'.name = r.name → r'.status = r.status := by decide

theorem v11New_no_closed : ∀ r ∈ v11New, r.status ≠ .old .closed := by decide

/-- **No `CLOSED` row anywhere in V11.** -/
theorem v11_no_closed : ∀ r ∈ v11Ledger, r.status ≠ .old .closed := by
  intro r hr
  rcases List.mem_append.1 hr with h | h
  · exact v10_no_closed r h
  · exact v11New_no_closed r h

/-- **The V11 frontier.** -/
theorem v11_frontier :
    (∃ r ∈ v11New, r.name = "explicit numerical M_an" ∧ r.status = .none) ∧
    (∃ r ∈ v11New, r.name = "viable finite architecture / overlapping finite certificate" ∧
      r.status = .old .open) ∧
    (∃ r ∈ v11New, r.name = "effective finite splice" ∧ r.status = .old .blocked) ∧
    (∃ r ∈ v11New, r.name = "asymptotic composition" ∧ r.status = .repairedConditional) ∧
    (∃ r ∈ v11New, r.name = "Erdős #287" ∧ r.status = .old .open) ∧
    (∀ r ∈ v11New, r.name = "Erdős #287" → r.status = .old .open) := by
  decide

theorem v11_proved_implies_kernel :
    ∀ r ∈ v11New, r.status = .old .proved → r.evidence = .kernelProof := by decide

/-- The V11 closure DAG. -/
def closureDAG : List ResearchBankV9.Ledger.Edge :=
  [ ⟨["asymptotic composition", "numerical external constants",
      "exceptional-safe full modulus input"], "explicit numerical M_an"⟩
  , ⟨["explicit numerical M_an", "viable finite architecture / overlapping finite certificate",
      "finite verification through M0-1"], "effective finite splice"⟩
  , ⟨["effective finite splice"], "Erdős #287"⟩ ]

/-- Base nodes: `PROVED`, `EXACT PASS`, `FROZEN BANK` rows of V10 and V11. -/
def baseNodes : List String :=
  ((v10New ++ v11New).filter fun r => r.status = .old .proved ∨ r.status = .exactPass ∨
    r.status = .frozenBank).map (·.name)

def step (S : List String) : List String :=
  S ++ (closureDAG.filter fun e => e.premises.all fun p => p ∈ S).map (·.conclusion)

def derivable : ℕ → List String
  | 0 => baseNodes
  | n + 1 => step (derivable n)

theorem step_baseNodes : step baseNodes = baseNodes := by decide

theorem derivable_eq (n : ℕ) : derivable n = baseNodes := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [derivable, ih, step_baseNodes]

/-- **No V11 ledger path closes Erdős #287** (nor `M_an`, nor the splice). -/
theorem no_ledger_path_closes_erdos287_v11 (n : ℕ) :
    "Erdős #287" ∉ derivable n ∧ "explicit numerical M_an" ∉ derivable n ∧
    "effective finite splice" ∉ derivable n := by
  rw [derivable_eq]; decide

end Ledger
end ResearchBankV11
end Erdos287
