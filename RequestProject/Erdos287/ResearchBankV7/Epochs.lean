import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V7: research epochs and meta-firewalls

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

V7 is a strictly **append-only** layer: nothing of `AnchoredV2/V3/V4`, `ResearchBankV5` or
`ResearchBankV6` is edited, renamed, moved, weakened or reinterpreted.  This module introduces the
*chronology* that makes the older ledgers and the current ledger simultaneously readable:

* `Epoch` — the four research epochs (V6 upper-gap/carry, STABLE-ENTRY, exact-HIT / arithmetic
  spine, current ENTRY-FIRST);
* `OwnerRecord` — an epoch-stamped owner row carrying an actual `Prop` claim;
* meta-firewalls (all machine-checked):
  - `superseded_does_not_mean_false`,
  - `historical_open_does_not_determine_current_owner`,
  - `later_reduction_does_not_inhabit_earlier_owner`,
  - `no_closure_propagation_through_ledger_edges`.

None of these is a mathematical statement about #287: they are exact statements about the
bookkeeping calculus, proved so that "current owner" talk cannot silently contradict an earlier
historical ledger.
-/

namespace Erdos287
namespace ResearchBankV7
namespace Epochs

/-! ## 1.  The epochs -/

/-- The research epochs of the #287 programme after V6. -/
inductive Epoch
  /-- The V6 upper-gap / carry epoch (row mass, carry identity, height aggregation). -/
  | v6UpperGapCarry
  /-- The STABLE-ENTRY epoch (seed traces, bounded adaptive absorption trees). -/
  | stableEntry
  /-- The exact-HIT / arithmetic-spine epoch (interval lifting, spine certificates, erasure). -/
  | exactHitSpine
  /-- The current ENTRY-FIRST epoch. -/
  | entryFirst
  deriving DecidableEq, Repr

/-- Chronological index of an epoch. -/
def Epoch.index : Epoch → ℕ
  | .v6UpperGapCarry => 0
  | .stableEntry => 1
  | .exactHitSpine => 2
  | .entryFirst => 3

/-- The chronology is injective: epochs are pairwise distinct stages. -/
theorem epoch_index_injective : Function.Injective Epoch.index := by
  intro a b h; cases a <;> cases b <;> simp_all [Epoch.index]

/-- The four epochs occur in the recorded order. -/
theorem epoch_chronology :
    Epoch.v6UpperGapCarry.index < Epoch.stableEntry.index ∧
    Epoch.stableEntry.index < Epoch.exactHitSpine.index ∧
    Epoch.exactHitSpine.index < Epoch.entryFirst.index := by decide

/-- The current epoch. -/
def currentEpoch : Epoch := Epoch.entryFirst

/-- Every epoch is at most the current one. -/
theorem le_currentEpoch (e : Epoch) : e.index ≤ currentEpoch.index := by
  cases e <;> decide

/-! ## 2.  Epoch-stamped owner records -/

/-- The lifecycle flag of an owner *inside its own epoch*. -/
inductive OwnerFlag
  /-- Unresolved in its epoch and still unresolved now. -/
  | openOwner
  /-- Bypassed or refined by later work.  **Never** means "false". -/
  | superseded
  /-- Discharged at its stated scope. -/
  | discharged
  deriving DecidableEq, Repr

/-- An epoch-stamped owner row.  The `claim` field is an actual `Prop`; a row is *data*, so
creating a row never inhabits `claim`. -/
structure OwnerRecord where
  /-- Human-readable owner name. -/
  name : String
  /-- The epoch in which this owner was the current one. -/
  epoch : Epoch
  /-- The mathematical claim of the owner. -/
  claim : Prop
  /-- Its lifecycle flag. -/
  flag : OwnerFlag

/-! ## 3.  Meta-firewalls -/

/-- **Firewall: `superseded` does not mean `false`.**  There is a `superseded` owner record whose
claim is true; being bypassed by later work is a statement about the *architecture*, never a
refutation of the statement. -/
theorem superseded_does_not_mean_false :
    ∃ r : OwnerRecord, r.flag = OwnerFlag.superseded ∧ r.claim :=
  ⟨{ name := "superseded probe", epoch := Epoch.v6UpperGapCarry, claim := True,
     flag := OwnerFlag.superseded }, rfl, trivial⟩

/-- **Firewall: the `superseded` flag is truth-neutral.**  Both a true and a false claim can carry
it, so the flag transports no truth value in either direction. -/
theorem superseded_flag_is_truth_neutral :
    (∃ r : OwnerRecord, r.flag = OwnerFlag.superseded ∧ r.claim) ∧
    (∃ r : OwnerRecord, r.flag = OwnerFlag.superseded ∧ ¬ r.claim) :=
  ⟨superseded_does_not_mean_false,
   ⟨{ name := "superseded false probe", epoch := Epoch.v6UpperGapCarry, claim := False,
      flag := OwnerFlag.superseded }, rfl, not_false⟩⟩

/-- **Firewall: a historical owner being open does not say that the current owner is the same
statement.**  Openness of one proposition transports nothing to another proposition. -/
theorem historical_open_does_not_determine_current_owner :
    ¬ ∀ P Q : Prop, ¬ P → ¬ Q := by
  intro h
  exact (h False True not_false) trivial

/-- The same, in record form: two owners of different epochs may carry genuinely different
claims, one unprovable and one provable. -/
theorem owners_of_distinct_epochs_may_differ :
    ∃ r s : OwnerRecord, r.epoch ≠ s.epoch ∧ ¬ r.claim ∧ s.claim :=
  ⟨{ name := "historical owner", epoch := Epoch.v6UpperGapCarry, claim := False,
     flag := OwnerFlag.superseded },
   { name := "current owner probe", epoch := Epoch.entryFirst, claim := True,
     flag := OwnerFlag.openOwner },
   by decide, not_false, trivial⟩

/-- **Firewall: a later reduction does not retroactively inhabit an earlier open proposition.**
From `Q → P` (a later statement reducing to the earlier owner `P`) one may not conclude `P`. -/
theorem later_reduction_does_not_inhabit_earlier_owner :
    ¬ ∀ P Q : Prop, (Q → P) → P := by
  intro h
  exact h False False id

/-- **Firewall: no closure status propagates merely through ledger edges.**  An edge `P → Q`
together with a proof of `Q` never yields `P`. -/
theorem no_closure_propagation_through_ledger_edges :
    ¬ ∀ P Q : Prop, (P → Q) → Q → P := by
  intro h
  exact h False True (fun x => x.elim) trivial

/-- **Firewall: edges compose, statuses do not.**  Composing two proved edges is legitimate
(kernel), but that is the *only* thing an edge does. -/
theorem edges_compose {P Q R : Prop} (h₁ : P → Q) (h₂ : Q → R) : P → R := fun p => h₂ (h₁ p)

end Epochs
end ResearchBankV7
end Erdos287
