/-!
# Erdős #287 — source chain: the updated closure DAG (V99–V100R4 message-level source)

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Statuses:
* `Exact` — kernel-proved, no open input;
* `KernelConditional` — kernel-proved implication from named inputs;
* `ExternalAnalytic` — named analytic provider (never constructed);
* `RefereePending` — source membership inherited from an author package, independent audit pending;
* `Banked` — previously audited layer, preserved unchanged;
* `Open` — not established;
* `Retired` — superseded (Ordering A);
* `Metadata` — author/referee status record; carries no mathematics.

Kernel-checked by `decide`:
* `scDag_acyclic` — every edge strictly increases an explicit rank;
* `scOrderingA_feeds_nothing`, `scOrderingA_no_path_to_tail` — retired Ordering A has no path to
  either tail node;
* `scMetadata_feeds_nothing` — author/referee metadata instantiates no mathematical node;
* `scGlobal_preds` — global #287 has exactly the inputs *effective onset* and *finite splice*;
  `scTail_reaches_global`, `scSplice_reaches_global` — both the tail and the splice lie upstream;
  `scConditionalTail_not_global_pred` — the conditional tail does not feed global #287 directly;
* `scTerminal_statuses` — no unconditional tail exists.
-/

namespace Erdos287.SourceChain

/-- Closure statuses for the source-chain DAG. -/
inductive SCStatus
  | Exact
  | KernelConditional
  | ExternalAnalytic
  | RefereePending
  | Banked
  | Open
  | Retired
  | Metadata
  deriving DecidableEq, Repr

/-- Nodes of the consolidated programme (23 mathematical nodes + retired Ordering A + two
metadata records). -/
inductive SCNode
  | exactModel            -- 1
  | finiteBank            -- 2
  | W3                    -- 3
  | W2984                 -- 4
  | sevenBlockConsumer    -- 5
  | v99Centering          -- 6
  | rbdhAlgebra           -- 7
  | orderingBSource       -- 8
  | auxErrorPayment       -- 9
  | fab                   -- 10
  | noncleanFAA           -- 11
  | cleanFAAsharp         -- 12
  | scalarWeight          -- 13
  | rangeExport           -- 14
  | affinePhase           -- 15
  | kernelMembership      -- 16
  | spectralEstimate      -- 17
  | finalRemainder        -- 18
  | conditionalTail       -- 19
  | unconditionalTail     -- 20
  | effectiveOnset        -- 21
  | finiteSplice          -- 22
  | globalErdos287        -- 23
  | orderingA             -- retired
  | authorCandidate       -- metadata: `V100R4_AuthorCandidate`
  | refereePending        -- metadata: `IndependentTailAuditPending`
  deriving DecidableEq, Repr

open SCNode

/-- All nodes. -/
def scNodes : List SCNode :=
  [exactModel, finiteBank, W3, W2984, sevenBlockConsumer, v99Centering, rbdhAlgebra,
   orderingBSource, auxErrorPayment, fab, noncleanFAA, cleanFAAsharp, scalarWeight, rangeExport,
   affinePhase, kernelMembership, spectralEstimate, finalRemainder, conditionalTail,
   unconditionalTail, effectiveOnset, finiteSplice, globalErdos287, orderingA, authorCandidate,
   refereePending]

/-- Current statuses. -/
def scStatus : SCNode → SCStatus
  | exactModel => .Exact
  | finiteBank => .Banked
  | W3 => .Banked
  | W2984 => .Banked
  | sevenBlockConsumer => .Exact
  | v99Centering => .Exact
  | rbdhAlgebra => .Exact
  | orderingBSource => .KernelConditional
  | auxErrorPayment => .KernelConditional
  | fab => .KernelConditional
  | noncleanFAA => .KernelConditional
  | cleanFAAsharp => .KernelConditional
  | scalarWeight => .Exact
  | rangeExport => .KernelConditional
  | affinePhase => .Exact
  | kernelMembership => .RefereePending
  | spectralEstimate => .ExternalAnalytic
  | finalRemainder => .KernelConditional
  | conditionalTail => .KernelConditional
  | unconditionalTail => .Open
  | effectiveOnset => .Open
  | finiteSplice => .Open
  | globalErdos287 => .Open
  | orderingA => .Retired
  | authorCandidate => .Metadata
  | refereePending => .Metadata

/-- Dependency edges `(a, b)`: `a` feeds `b`. -/
def scEdges : List (SCNode × SCNode) :=
  [(exactModel, finiteBank), (exactModel, W3), (exactModel, W2984), (W3, W2984),
   (exactModel, sevenBlockConsumer), (sevenBlockConsumer, conditionalTail),
   (exactModel, v99Centering), (v99Centering, orderingBSource), (v99Centering, finalRemainder),
   (rbdhAlgebra, auxErrorPayment), (rbdhAlgebra, finalRemainder),
   (orderingBSource, fab), (orderingBSource, noncleanFAA), (orderingBSource, auxErrorPayment),
   (noncleanFAA, cleanFAAsharp),
   (scalarWeight, rangeExport), (rangeExport, kernelMembership),
   (affinePhase, kernelMembership), (cleanFAAsharp, kernelMembership),
   (kernelMembership, finalRemainder), (spectralEstimate, finalRemainder),
   (fab, finalRemainder), (auxErrorPayment, finalRemainder), (noncleanFAA, finalRemainder),
   (finalRemainder, conditionalTail), (conditionalTail, unconditionalTail),
   (unconditionalTail, effectiveOnset), (effectiveOnset, globalErdos287),
   (finiteBank, finiteSplice), (finiteSplice, globalErdos287)]

/-- An explicit topological rank. -/
def scRank : SCNode → Nat
  | exactModel => 0
  | finiteBank => 1
  | W3 => 1
  | W2984 => 2
  | sevenBlockConsumer => 1
  | v99Centering => 1
  | rbdhAlgebra => 0
  | orderingBSource => 2
  | auxErrorPayment => 3
  | fab => 3
  | noncleanFAA => 3
  | cleanFAAsharp => 4
  | scalarWeight => 0
  | rangeExport => 1
  | affinePhase => 0
  | kernelMembership => 5
  | spectralEstimate => 0
  | finalRemainder => 6
  | conditionalTail => 7
  | unconditionalTail => 8
  | effectiveOnset => 9
  | finiteSplice => 2
  | globalErdos287 => 10
  | orderingA => 0
  | authorCandidate => 0
  | refereePending => 0

/-- Successors of a node. -/
def scSucc (a : SCNode) : List SCNode := (scEdges.filter (fun e => e.1 == a)).map (·.2)

/-- Nodes reachable from `a` in at most `fuel` steps (including `a`). -/
def scReach : Nat → SCNode → List SCNode
  | 0, a => [a]
  | n + 1, a => a :: (scSucc a).flatMap (scReach n)

/-- Reachability with fuel = number of nodes (sufficient for any simple path). -/
def scReachable (a b : SCNode) : Bool := (scReach scNodes.length a).contains b

/-- **Acyclicity**: every edge strictly increases the rank. -/
theorem scDag_acyclic : ∀ e ∈ scEdges, scRank e.1 < scRank e.2 := by decide

/-- The retired Ordering A has no outgoing edge. -/
theorem scOrderingA_feeds_nothing : ∀ e ∈ scEdges, e.1 ≠ orderingA := by decide

/-- The retired Ordering A has no path to either tail node. -/
theorem scOrderingA_no_path_to_tail :
    scReachable orderingA conditionalTail = false ∧
      scReachable orderingA unconditionalTail = false := by decide

/-- Author / referee metadata instantiates no mathematical node. -/
theorem scMetadata_feeds_nothing :
    ∀ e ∈ scEdges, e.1 ≠ authorCandidate ∧ e.1 ≠ refereePending := by decide

/-- Every retired or metadata node feeds nothing. -/
theorem scInert_feeds_nothing :
    ∀ e ∈ scEdges, scStatus e.1 ≠ .Retired ∧ scStatus e.1 ≠ .Metadata := by decide

/-- The direct inputs of global #287 are exactly the effective onset and the finite splice. -/
theorem scGlobal_preds :
    (scEdges.filter (fun e => e.2 == globalErdos287)).map (·.1) =
      [effectiveOnset, finiteSplice] := by decide

/-- The conditional tail does not feed global #287 directly. -/
theorem scConditionalTail_not_global_pred : (conditionalTail, globalErdos287) ∉ scEdges := by
  decide

/-- The tail lies upstream of global #287. -/
theorem scTail_reaches_global :
    scReachable conditionalTail globalErdos287 = true ∧
      scReachable unconditionalTail globalErdos287 = true := by decide

/-- The finite splice lies upstream of global #287. -/
theorem scSplice_reaches_global : scReachable finiteSplice globalErdos287 = true := by decide

/-- The spectral estimate reaches the tail only through the final remainder. -/
theorem scSpectral_routing :
    (scEdges.filter (fun e => e.1 == spectralEstimate)).map (·.2) = [finalRemainder] := by
  decide

/-- Current terminal statuses. -/
theorem scTerminal_statuses :
    scStatus unconditionalTail = .Open ∧ scStatus conditionalTail = .KernelConditional ∧
      scStatus globalErdos287 = .Open ∧ scStatus finiteSplice = .Open ∧
      scStatus effectiveOnset = .Open := by decide

/-- No node with status `Open`, `ExternalAnalytic` or `RefereePending` is upstream of a node
labelled `Exact` (exact nodes depend only on exact/banked nodes). -/
theorem scExact_inputs_exact :
    ∀ e ∈ scEdges, scStatus e.2 = .Exact →
      scStatus e.1 = .Exact ∨ scStatus e.1 = .Banked := by decide

end Erdos287.SourceChain
