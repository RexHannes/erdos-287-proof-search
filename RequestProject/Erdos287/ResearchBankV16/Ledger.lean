import RequestProject.Erdos287.ResearchBankV15.Ledger
import RequestProject.Erdos287.ResearchBankV16.ScopeFirewalls

/-!
# Erdős #287 — Research Bank V16: ledger (append-only)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

From V16 on, every new row carries exactly one of the six semantic classes

    LEAN BANK | LEAN CONDITIONAL | EXTERNAL PROVIDER | FINITE REGRESSION | OPEN | REPAIRED / RETIRED

(`SemClass`).  The complete V15 ledger is embedded verbatim (`RowV16.old`) as a prefix, so no
V2–V15 row is re-interpreted.  `v16_erdos287_open` — #287 stays OPEN.
-/

namespace Erdos287
namespace ResearchBankV16
namespace Ledger

open ResearchBankV14.Ledger

/-- The six semantic classes used by V16–V20. -/
inductive SemClass
  /-- Proved in Lean from existing formal definitions/theorems. -/
  | leanBank
  /-- Proved in Lean from an explicit Provider argument. -/
  | leanConditional
  /-- Theorem from the literature, not formalized here. -/
  | externalProvider
  /-- Checked finite instance / fixture only. -/
  | finiteRegression
  /-- Research obligation not constructed. -/
  | open
  /-- Earlier claim shown too strong and replaced. -/
  | repairedRetired
  deriving DecidableEq, Repr

/-- A V16+ ledger row: a verbatim earlier (V2–V15) row, or a new classified row. -/
inductive RowV16
  | old (r : RowV14)
  | new (name : String) (cls : SemClass)
  deriving DecidableEq, Repr

def RowV16.nm : RowV16 → String
  | .old r => r.nm
  | .new n _ => n

def RowV16.cls? : RowV16 → Option SemClass
  | .old _ => none
  | .new _ c => some c

/-- The new V16 rows. -/
def v16New : List RowV16 :=
  [ .new "V14/V15 infrastructure (frozen)" .leanBank
  , .new "G(26,7): alpha = 7 (general proof), proper 4-colouring" .leanBank
  , .new "symbolic balanced 26-group blow-up" .leanBank
  , .new "Route-C score f(v) = v - binom(v,2)/99, 50 - f = (v-99)(v-100)/198" .leanBank
  , .new "Route-C parameters (K = 2^82650, a = 57384, A_C = 2/theta_d + xi)" .finiteRegression
  , .new "Route-C functional certificate (mu_F, W_F bounds)" .externalProvider
  , .new "Route-C contact localization c_C = 46/125, c_C R_C < 1" .leanBank
  , .new "harmonic two-hole contradiction at c_C" .leanBank
  , .new "Route-B constants imported into Route C" .repairedRetired
  , .new "relaxed pair budget A_C W_F + 90 + err" .leanBank
  , .new "Route-C deterministic consumer" .leanBank
  , .new "Route-C conditional implication" .leanConditional
  , .new "RouteCBaselineProvider" .open
  , .new "explicit analytic threshold" .open
  , .new "finite splice" .open
  , .new "Erdős #287" .open ]

/-- The complete V16 ledger. -/
def v16Ledger : List RowV16 := (ResearchBankV15.Ledger.v15Ledger.map RowV16.old) ++ v16New

theorem old_injective : Function.Injective RowV16.old := fun _ _ h => by cases h; rfl

/-- **V16 preserves the V15 ledger verbatim** (prefix, injective embedding). -/
theorem v16_preserves_v15_ledger :
    v16Ledger.take ResearchBankV15.Ledger.v15Ledger.length =
      ResearchBankV15.Ledger.v15Ledger.map RowV16.old ∧
    ∀ r ∈ ResearchBankV15.Ledger.v15Ledger, RowV16.old r ∈ v16Ledger := by
  refine ⟨?_, fun r hr => List.mem_append_left _ (List.mem_map_of_mem hr)⟩
  unfold v16Ledger
  rw [← List.length_map (f := RowV16.old)]
  exact List.take_left

/-- **Erdős #287 stays OPEN.** -/
theorem v16_erdos287_open : ∀ r ∈ v16New, r.nm = "Erdős #287" → r.cls? = some .open := by
  decide

/-- The Route-C baseline provider is OPEN, not promoted. -/
theorem v16_provider_open :
    ∀ r ∈ v16New, r.nm ∈ ["RouteCBaselineProvider", "explicit analytic threshold",
      "finite splice", "Erdős #287"] → r.cls? = some .open := by decide

end Ledger
end ResearchBankV16
end Erdos287
