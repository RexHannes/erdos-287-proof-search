import RequestProject.Erdos287.CurrentTail.Regressions

/-!
# Erdős #287 — current tail consolidation: the closure DAG

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Statuses: `Exact` (kernel-proved, no open input), `KernelConditional` (kernel-proved implication
from named inputs), `ExternalAnalytic` (named analytic provider, never constructed), `Banked`
(previously audited layer, preserved unchanged), `Candidate` (written paper-level argument not
yet independently passed / not formalised), `Open`, `Retired`.

Kernel-checked (`decide`):

* `dag_acyclic` — every edge strictly increases an explicit rank (so the graph is acyclic);
* `orderingA_feeds_nothing` — the retired Ordering A has no outgoing edge;
* `retired_feeds_nothing` — no retired node feeds anything;
* `global_preds` — the only inputs of global #287 are the effective onset and the finite splice;
  in particular the asymptotic tail does **not** feed global #287 directly;
* `tail_status`, `global_open`, `splice_open`, `onset_open` — current statuses.

The statement-level check "no provider contains its downstream conclusion" is performed at build
time in `AxiomAudit.lean`.
-/

set_option maxRecDepth 20000

namespace Erdos287.CurrentTail

/-- Closure statuses. -/
inductive DAGStatus
  | Exact
  | KernelConditional
  | ExternalAnalytic
  | Banked
  | Candidate
  | Open
  | Retired
  deriving DecidableEq, Repr

/-- Nodes of the current programme. -/
inductive Node
  | exactModel            -- 1
  | reciprocalMass        -- 2
  | W3                    -- 3
  | W2984                 -- 4
  | sevenBlockConsumer    -- 5
  | v99Centering          -- 6
  | baseFluctuation       -- 7
  | largeSmoothDeletion   -- 8
  | rbdhReduction         -- 9
  | ordinaryBDH           -- 10
  | spectatorNorm         -- 11
  | orderingA             -- 12
  | orderingB             -- 13
  | nearDiagonal          -- 14
  | e1Dictionary          -- 15
  | e1Estimate            -- 16
  | e2Dictionary          -- 17
  | quantitativeTH        -- 18
  | e2Estimate            -- 19
  | recombination         -- 20
  | asymptoticTail        -- 21
  | effectiveOnset        -- 22
  | finiteSplice          -- 23
  | globalErdos287        -- 24
  | sevenBlockFramework   -- 25 (structural framework input of the tail theorem)
  deriving DecidableEq, Repr, Fintype

open Node

/-- Current statuses. -/
def status : Node → DAGStatus
  | exactModel => .Exact
  | reciprocalMass => .Exact
  | W3 => .Banked
  | W2984 => .Banked
  | sevenBlockConsumer => .Exact
  | v99Centering => .Exact
  | baseFluctuation => .KernelConditional
  | largeSmoothDeletion => .ExternalAnalytic
  | rbdhReduction => .Exact
  | ordinaryBDH => .ExternalAnalytic
  | spectatorNorm => .KernelConditional
  | orderingA => .Retired
  | orderingB => .Candidate
  | nearDiagonal => .KernelConditional
  | e1Dictionary => .Candidate
  | e1Estimate => .ExternalAnalytic
  | e2Dictionary => .Candidate
  | quantitativeTH => .ExternalAnalytic
  | e2Estimate => .ExternalAnalytic
  | recombination => .KernelConditional
  | asymptoticTail => .KernelConditional
  | effectiveOnset => .Open
  | finiteSplice => .Open
  | globalErdos287 => .Open
  | sevenBlockFramework => .Candidate

/-- Dependency edges `(a, b)`: `a` feeds `b`. -/
def edges : List (Node × Node) :=
  [(exactModel, reciprocalMass), (exactModel, W3), (exactModel, W2984), (W3, W2984),
   (exactModel, sevenBlockConsumer), (reciprocalMass, sevenBlockConsumer),
   (reciprocalMass, v99Centering), (v99Centering, orderingB), (v99Centering, baseFluctuation),
   (v99Centering, recombination), (baseFluctuation, recombination),
   (largeSmoothDeletion, recombination), (ordinaryBDH, rbdhReduction),
   (rbdhReduction, recombination), (spectatorNorm, recombination),
   (orderingB, nearDiagonal), (orderingB, e1Dictionary), (orderingB, e2Dictionary),
   (nearDiagonal, recombination), (e1Dictionary, recombination), (e1Estimate, recombination),
   (e2Dictionary, recombination), (quantitativeTH, recombination), (e2Estimate, recombination),
   (recombination, asymptoticTail), (sevenBlockConsumer, asymptoticTail),
   (sevenBlockFramework, asymptoticTail), (asymptoticTail, effectiveOnset),
   (effectiveOnset, globalErdos287), (finiteSplice, globalErdos287)]

/-- An explicit topological rank. -/
def rank : Node → ℕ
  | exactModel => 0
  | reciprocalMass => 1
  | W3 => 1
  | W2984 => 2
  | sevenBlockConsumer => 2
  | v99Centering => 2
  | baseFluctuation => 3
  | largeSmoothDeletion => 0
  | rbdhReduction => 1
  | ordinaryBDH => 0
  | spectatorNorm => 0
  | orderingA => 0
  | orderingB => 3
  | nearDiagonal => 4
  | e1Dictionary => 4
  | e1Estimate => 0
  | e2Dictionary => 4
  | quantitativeTH => 0
  | e2Estimate => 0
  | recombination => 5
  | asymptoticTail => 6
  | effectiveOnset => 7
  | finiteSplice => 0
  | globalErdos287 => 8
  | sevenBlockFramework => 0

/-- **Acyclicity**: every edge strictly increases the rank. -/
theorem dag_acyclic : ∀ e ∈ edges, rank e.1 < rank e.2 := by decide

/-- Consequence: there is no edge-path from a node back to itself (rank argument). -/
theorem no_self_loop : ∀ e ∈ edges, e.1 ≠ e.2 := by decide

/-- The retired Ordering A feeds nothing (in particular, not the tail theorem). -/
theorem orderingA_feeds_nothing : ∀ e ∈ edges, e.1 ≠ orderingA := by decide

theorem retired_feeds_nothing : ∀ e ∈ edges, status e.1 ≠ .Retired := by decide

/-- The inputs of global #287 are exactly the effective onset and the finite splice. -/
theorem global_preds : ∀ e ∈ edges, e.2 = globalErdos287 →
    e.1 = effectiveOnset ∨ e.1 = finiteSplice := by decide

theorem tail_not_direct_to_global : (asymptoticTail, globalErdos287) ∉ edges := by decide

theorem splice_feeds_global : (finiteSplice, globalErdos287) ∈ edges := by decide

theorem tail_status : status asymptoticTail = .KernelConditional := rfl
theorem global_open : status globalErdos287 = .Open := rfl
theorem splice_open : status finiteSplice = .Open := rfl
theorem onset_open : status effectiveOnset = .Open := rfl
theorem orderingA_retired : status orderingA = .Retired := rfl

/-- Every analytic node is an external provider (none is marked proved). -/
theorem analytic_nodes_external :
    ∀ n ∈ [ordinaryBDH, e1Estimate, quantitativeTH, e2Estimate, largeSmoothDeletion],
      status n = .ExternalAnalytic := by decide

end Erdos287.CurrentTail
