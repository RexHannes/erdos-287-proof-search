import Mathlib

/-!
# Erdős #287 — September-2 bank, §1–§2: the tagged two-lane source and the selected-`E`
type firewall

```
TAGGED DISJOINT-UNION ALGEBRA      : KERNEL-PROVED
SELECTED-E TYPE FIREWALL           : KERNEL-PROVED (typing guard, not a predicate)
PHYSICAL RECONSTRUCTION SEMANTICS  : PAPER / SOURCE EXTERNAL (recorded, not proved)
source-tag ≠ physical n-support    : KERNEL-PROVED (explicit witness)
```

This module is **append-only**.  It proves *only* the tagged disjoint-union algebra of the
two lanes; it asserts nothing analytic and nothing about Erdős #287.

**§1 — the tagged source.**  With the neutral lane tags `tot`, `u` and the two *discrete*
occurrence types `TotDiscIndex`, `UDiscIndex`,

```
    RawIndex := ({tot} × TotDiscIndex)  ⊎  ({u} × UDiscIndex).
```

The tag components are singleton subtypes, so the tag of a row is fixed by its summand.
Kernel-proved: the lane dichotomy, fibre disjointness, the census split of any `Finset` of
rows, and the equivalence `RawIndex ≃ TotDiscIndex ⊕ UDiscIndex`.

*Intended semantics* (recorded, not proved here): `tot` reconstructs `T_X` and `u`
reconstructs `L_X`.  The purely algebraic split identity `∑ = T + L` is kernel-proved for
supplied weights; the *physical* identification of those numbers with `T_X`, `L_X` stays
`PAPER / SOURCE EXTERNAL`.

Recorded explicitly and machine-checked: **source-tag disjointness is not physical
`n`-support disjointness** (`tag_disjointness_is_not_support_disjointness`).

**§2 — the selected-`E` firewall.**  `TotDiscIndex` has *no* selected-`E` field, while
`UDiscIndex` has one.  Hence no constructor can attach selected-`E` metadata to a `Tot` row:
`no_tot_constructor_carries_selectedE` says that any row-producing map landing in the `Tot`
lane loses the datum, whatever it does with it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace September2TaggedSource

/-! ## §1.1  Lane tags and the two discrete occurrence types -/

/-- The neutral lane tag. -/
inductive LaneTag
  /-- The `Tot` lane. -/
  | tot
  /-- The `U` lane. -/
  | u
  deriving DecidableEq, Fintype, Repr

/-- **`TotDiscIndex`** — a discrete `Tot`-lane source occurrence.  It has **no**
selected-`E` field; this absence is the typing guard of §2. -/
structure TotDiscIndex where
  /-- Contour label (a label, never an ordinate value). -/
  contour : ℕ
  /-- Dissection depth. -/
  depth : ℕ
  /-- Block label. -/
  block : ℕ
  /-- Source sign. -/
  sign : Bool
  deriving DecidableEq, Repr

/-- **`UDiscIndex`** — a discrete `U`-lane source occurrence.  Only this type carries
selected-`E` data. -/
structure UDiscIndex where
  /-- Contour label. -/
  contour : ℕ
  /-- Dissection depth. -/
  depth : ℕ
  /-- Block label. -/
  block : ℕ
  /-- Source sign. -/
  sign : Bool
  /-- The selected-`E` leaf set. -/
  selectedE : Finset ℕ
  deriving DecidableEq

/-- A `Tot`-tagged row: the tag is pinned to `tot` by the subtype. -/
abbrev TotTagged := {t : LaneTag // t = LaneTag.tot} × TotDiscIndex

/-- A `U`-tagged row: the tag is pinned to `u` by the subtype. -/
abbrev UTagged := {t : LaneTag // t = LaneTag.u} × UDiscIndex

/-- **`RawIndex`** — the tagged disjoint union of the two lanes. -/
abbrev RawIndex := TotTagged ⊕ UTagged

/-- The lane of a row. -/
def laneOf : RawIndex → LaneTag
  | Sum.inl r => r.1.1
  | Sum.inr r => r.1.1

@[simp] theorem laneOf_inl (r : TotTagged) : laneOf (Sum.inl r) = LaneTag.tot := r.1.2

@[simp] theorem laneOf_inr (r : UTagged) : laneOf (Sum.inr r) = LaneTag.u := r.1.2

/-- **`lane_dichotomy`.**  `KERNEL-PROVED`. -/
theorem lane_dichotomy (i : RawIndex) : laneOf i = LaneTag.tot ∨ laneOf i = LaneTag.u := by
  cases i with
  | inl r => exact Or.inl (laneOf_inl r)
  | inr r => exact Or.inr (laneOf_inr r)

/-- **`lanes_are_disjoint`.**  `KERNEL-PROVED`.  No row lies in both lanes. -/
theorem lanes_are_disjoint (i : RawIndex) :
    ¬ (laneOf i = LaneTag.tot ∧ laneOf i = LaneTag.u) := by
  rintro ⟨h1, h2⟩
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- **`rawIndexEquiv`.**  `KERNEL-PROVED`.  The tagged union is equivalent to the plain
disjoint union of the two occurrence types: the tags carry no extra information. -/
def rawIndexEquiv : RawIndex ≃ TotDiscIndex ⊕ UDiscIndex where
  toFun := fun i => match i with
    | Sum.inl r => Sum.inl r.2
    | Sum.inr r => Sum.inr r.2
  invFun := fun i => match i with
    | Sum.inl a => Sum.inl (⟨LaneTag.tot, rfl⟩, a)
    | Sum.inr b => Sum.inr (⟨LaneTag.u, rfl⟩, b)
  left_inv := by
    rintro (⟨⟨t, ht⟩, a⟩ | ⟨⟨t, ht⟩, b⟩) <;> subst ht <;> rfl
  right_inv := by
    rintro (a | b) <;> rfl

/-- The `Tot` sub-census. -/
def totCells (S : Finset RawIndex) : Finset RawIndex :=
  S.filter (fun i => laneOf i = LaneTag.tot)

/-- The `U` sub-census. -/
def uCells (S : Finset RawIndex) : Finset RawIndex :=
  S.filter (fun i => laneOf i = LaneTag.u)

/-- **`census_union`.**  `KERNEL-PROVED`. -/
theorem census_union (S : Finset RawIndex) : totCells S ∪ uCells S = S := by
  ext i
  simp only [totCells, uCells, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    rcases lane_dichotomy i with hl | hl
    · exact Or.inl ⟨h, hl⟩
    · exact Or.inr ⟨h, hl⟩

/-- **`census_disjoint`.**  `KERNEL-PROVED`. -/
theorem census_disjoint (S : Finset RawIndex) : Disjoint (totCells S) (uCells S) := by
  rw [Finset.disjoint_left]
  intro i hi hj
  simp only [totCells, uCells, Finset.mem_filter] at hi hj
  exact lanes_are_disjoint i ⟨hi.2, hj.2⟩

/-- **`census_card_split`.**  `KERNEL-PROVED`.  The tagged census splits additively. -/
theorem census_card_split (S : Finset RawIndex) :
    (totCells S).card + (uCells S).card = S.card := by
  rw [← Finset.card_union_of_disjoint (census_disjoint S), census_union]

/-! ## §1.2  Intended semantics (recorded) and the algebraic split identity -/

/-- The object a lane is *intended* to reconstruct.  This is recorded metadata. -/
inductive ReconstructionTarget
  /-- The full correlation `T_X`. -/
  | TX
  /-- The leakage term `L_X`. -/
  | LX
  deriving DecidableEq, Fintype, Repr

/-- The intended reconstruction map: `tot ↦ T_X`, `u ↦ L_X`. -/
def intendedTarget : LaneTag → ReconstructionTarget
  | LaneTag.tot => ReconstructionTarget.TX
  | LaneTag.u => ReconstructionTarget.LX

/-- **`intendedTarget_injective`.**  `KERNEL-PROVED`.  The two lanes are intended for two
different objects. -/
theorem intendedTarget_injective : Function.Injective intendedTarget := by decide

/-- Supplied weights together with the two lane totals.  Inhabiting this record with the
*physical* source weights is `PAPER / SOURCE EXTERNAL`; only its algebra is proved here. -/
structure LaneWeights (S : Finset RawIndex) where
  /-- The supplied weight of a row. -/
  weight : RawIndex → ℝ
  /-- The supplied `Tot`-lane total. -/
  totTotal : ℝ
  /-- The supplied `U`-lane total. -/
  uTotal : ℝ
  /-- The `Tot` lane sums to `totTotal`. -/
  tot_sum : ∑ i ∈ totCells S, weight i = totTotal
  /-- The `U` lane sums to `uTotal`. -/
  u_sum : ∑ i ∈ uCells S, weight i = uTotal

/-- **`source_split_identity`.**  `KERNEL-PROVED`.  The tagged algebra: the full source sum
is the sum of the two lane totals. -/
theorem source_split_identity {S : Finset RawIndex} (w : LaneWeights S) :
    ∑ i ∈ S, w.weight i = w.totTotal + w.uTotal := by
  rw [← w.tot_sum, ← w.u_sum, ← Finset.sum_union (census_disjoint S), census_union]

/-! ## §1.3  Tag disjointness is not physical support disjointness -/

/-- A sample `Tot` row. -/
def sampleTot : RawIndex := Sum.inl (⟨LaneTag.tot, rfl⟩, ⟨0, 0, 0, false⟩)

/-- A sample `U` row. -/
def sampleU : RawIndex := Sum.inr (⟨LaneTag.u, rfl⟩, ⟨0, 0, 0, false, ∅⟩)

/-- **`tag_disjointness_is_not_support_disjointness`.**  `KERNEL-PROVED`.  Two rows may carry
different lane tags and still have overlapping physical `n`-support: tag disjointness is a
bookkeeping statement, never a support statement. -/
theorem tag_disjointness_is_not_support_disjointness :
    ∃ (supp : RawIndex → Finset ℕ) (i j : RawIndex),
      laneOf i ≠ laneOf j ∧ ¬ Disjoint (supp i) (supp j) := by
  refine ⟨fun _ => {0}, sampleTot, sampleU, ?_, ?_⟩
  · simp [sampleTot, sampleU, laneOf]
  · simp

/-! ## §2  The selected-`E` type firewall -/

/-- The selected-`E` datum of a row.  It is `none` on the `Tot` lane **by typing**: the type
`TotDiscIndex` has no such field to read. -/
def selectedE : RawIndex → Option (Finset ℕ)
  | Sum.inl _ => none
  | Sum.inr r => some r.2.selectedE

/-- **`tot_rows_carry_no_selectedE`.**  `KERNEL-PROVED`. -/
theorem tot_rows_carry_no_selectedE {i : RawIndex} (h : laneOf i = LaneTag.tot) :
    selectedE i = none := by
  cases i with
  | inl r => rfl
  | inr r => exact absurd (h.symm.trans (laneOf_inr r)) (by decide)

/-- **`selectedE_isSome_iff_u`.**  `KERNEL-PROVED`.  Exactly the `U` rows carry selected-`E`
data. -/
theorem selectedE_isSome_iff_u (i : RawIndex) :
    (selectedE i).isSome ↔ laneOf i = LaneTag.u := by
  cases i with
  | inl r => simp [selectedE, laneOf_inl]
  | inr r => simp [selectedE, laneOf_inr]

/-- **`no_tot_constructor_carries_selectedE`.**  `KERNEL-PROVED`.  The typing guard: any
constructor that builds `Tot` rows out of a base row **and** a selected-`E` set produces rows
carrying no selected-`E` datum — the metadata cannot be smuggled into the `Tot` lane. -/
theorem no_tot_constructor_carries_selectedE
    (attach : TotDiscIndex → Finset ℕ → RawIndex)
    (hlane : ∀ r E, laneOf (attach r E) = LaneTag.tot)
    (r : TotDiscIndex) (E : Finset ℕ) :
    selectedE (attach r E) = none :=
  tot_rows_carry_no_selectedE (hlane r E)

/-- **`selectedE_not_recoverable_from_tot_lane`.**  `KERNEL-PROVED`.  Stronger form: no
recovery map can read back two different selected-`E` sets from `Tot` rows produced by a
constructor that ignores the datum. -/
theorem selectedE_not_recoverable_from_tot_lane
    (attach : TotDiscIndex → Finset ℕ → RawIndex)
    (hconst : ∀ r E₁ E₂, attach r E₁ = attach r E₂)
    (recover : RawIndex → Finset ℕ) (r : TotDiscIndex) (E₁ E₂ : Finset ℕ) :
    recover (attach r E₁) = recover (attach r E₂) := by
  rw [hconst r E₁ E₂]

end September2TaggedSource
end Erdos287
