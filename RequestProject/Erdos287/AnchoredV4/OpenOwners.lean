import RequestProject.Erdos287.AnchoredV4.OriginalBridge

/-!
# Anchored V4 — machine-readable open owners

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Every unresolved dependency of the V4 layer is a named `Prop` together with a machine-readable
status, so that a later run cannot forget which premises are still unproved.  There is no `axiom`,
`sorry`, `native_decide`, `opaque` or `@[implemented_by]` anywhere in this layer, and none of the
`OPEN` owners below is inhabited.
-/

namespace Erdos287
namespace AnchoredV4
namespace OpenOwners

/-- The audited status of an owner. -/
inductive OwnerStatus
  | PROVED
  | CONDITIONAL_INTERFACE
  | OPEN
  | FALSE
  | NOT_NEEDED
  deriving DecidableEq, Repr

open OwnerStatus

/-! ## The four principal owners -/

/-- **OPEN.**  Existence of an actual ENTRY at arbitrarily large scale, with the interval and the
paid height both a bounded fraction of `M`.  Never inhabited in this project. -/
def ENTRY_EXISTENCE : Prop :=
  ∀ M₀ : ℕ, ∃ M aM Q Y : ℕ, M₀ ≤ M ∧ 2 * aM ≤ M ∧ 2 * Q ≤ M ∧ EntryExists M aM Q Y

/-- **OPEN.**  Existence of a valid descent move at every state above the floor height, for the
ENTRY data at hand.  Never inhabited in this project. -/
def SAFE_DESCENT_SUPPLY : Prop :=
  ∀ (aM M Q Y : ℕ) (mask : Finset ℕ), DescentSupply aM M Q Y mask

/-- **OPEN.**  The analytic supply of guarded reservoirs which absorb the residual exactly.  Never
inhabited in this project; the deterministic part of the absorber is proved in
`FourierAbsorber.lean` and consumes only the visible dominance and no-wraparound hypotheses. -/
def GUARDED_ABSORBER_ANALYTIC_SUPPLY : Prop :=
  ∀ (aM M Q Y : ℕ) (mask : Finset ℕ), AbsorberSupply aM M Q Y mask

/-- **PROVED.**  The bridge from a final V4 configuration to the original Erdős #287 counterexample
statement.  This owner is discharged by `final_configuration_is_counterexample`. -/
def ENTRY_TO_ORIGINAL_287_BRIDGE : Prop :=
  ∀ (aM M : ℕ) (Zf : Finset ℕ), 1 < aM → Zf ⊆ Finset.Ioo aM M → NoAdjacent Zf →
    wordSum (Finset.Icc aM M) Zf = 1 → Erdos287Counterexample

/-- The bridge owner is discharged. -/
theorem entry_to_original_287_bridge : ENTRY_TO_ORIGINAL_287_BRIDGE :=
  fun _ _ _ haM hsub hna hval => final_configuration_is_counterexample haM hsub hna hval

/-! ## The audited ledger -/

/-- The machine-readable ledger of V4 owners. -/
def ownerLedger : List (String × OwnerStatus) :=
  [ ("ENTRY_EXISTENCE", OPEN),
    ("SAFE_DESCENT_SUPPLY", OPEN),
    ("GUARDED_ABSORBER_ANALYTIC_SUPPLY", OPEN),
    ("ENTRY_TO_ORIGINAL_287_BRIDGE", PROVED),
    ("NORMALIZED_PRIME_POWER_HEIGHT", PROVED),
    ("DOUBLED_DENOMINATOR_LATTICE", PROVED),
    ("GUARD_GEOMETRY", PROVED),
    ("WELL_FOUNDED_PRIME_POWER_DESCENT", PROVED),
    ("EXACT_FOURIER_COUNTING_IDENTITY", PROVED),
    ("EXACT_ABSORPTION_FROM_DOMINANCE", CONDITIONAL_INTERFACE),
    ("CONDITIONAL_ENTRY_TO_EXACT_ONE", CONDITIONAL_INTERFACE),
    ("GLOBAL_COLUMN_SURJECTIVITY", FALSE),
    ("ROWWISE_NEUTRALITY_NECESSARY", FALSE),
    ("POSITIVE_MASS_IMPLIES_COVERAGE", FALSE),
    ("MANY_TARGETS_IMPLY_HIT", FALSE) ]

/-- The exact list of owners that remain `OPEN`. -/
theorem open_owners :
    ownerLedger.filter (fun e => e.2 = OwnerStatus.OPEN) =
      [ ("ENTRY_EXISTENCE", OPEN),
        ("SAFE_DESCENT_SUPPLY", OPEN),
        ("GUARDED_ABSORBER_ANALYTIC_SUPPLY", OPEN) ] := by
  decide

/-- The exact list of shortcuts that are formally `FALSE` and must never be revived. -/
theorem false_shortcuts :
    ownerLedger.filter (fun e => e.2 = OwnerStatus.FALSE) =
      [ ("GLOBAL_COLUMN_SURJECTIVITY", FALSE),
        ("ROWWISE_NEUTRALITY_NECESSARY", FALSE),
        ("POSITIVE_MASS_IMPLIES_COVERAGE", FALSE),
        ("MANY_TARGETS_IMPLY_HIT", FALSE) ] := by
  decide

/-! ## Unmatched V3 ↔ V4 interfaces

These are *not* claimed as bridges: the V3 objects exist and are frozen, but their types do not
line up with the V4 objects without additional data, so no bridge lemma is stated.

* the V3 `AlignedBank` alignment coefficient is a statement about a fixed terminal bank with a
  reserved mobility family; the V4 absorber is a statement about a guarded even reservoir inside
  the word interval.  `absorber_is_sumset_membership` shows the two have the same *shape*
  (subset-sum membership), but no data-level identification is proved;
* the V3 packet theorems give many disjoint zero-sum packets; converting them into V4 descent
  moves would additionally require the parity and neighbour-height conditions of
  `DescentStep`, which the V3 statements do not provide. -/

end OpenOwners
end AnchoredV4
end Erdos287
