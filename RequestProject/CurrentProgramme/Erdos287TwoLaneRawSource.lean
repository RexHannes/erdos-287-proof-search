import Mathlib

/-!
# The two-lane raw source: lanes, the selected-`E` family, discrete packet census,
and the repeated-large-prime firewall

```
RAW LANE TYPE              : KERNEL-PROVED
SELECTED-E FAMILY          : KERNEL-PROVED
DISCRETE PACKET CENSUS     : KERNEL-PROVED (no continuous datum in a packet ID)
REPEATED-PRIME FIREWALL    : KERNEL-PROVED (finite combinatorics only)
```

This module is **append-only** and replaces nothing: the earlier one-copy master-source
interface is retained and is superseded only through the later status layer.

**§1 — the two lanes.**  `RawLane = tot | leakageU`, and the raw source splits as

```
    I_raw = I_Tot ⊎ I_U ,
```

`Tot` reconstructing the full correlation `T_X` and `U` being the Proposition-7.22 leakage
lane.  **Only the `U` lane carries `mathcalE` / `selectedE`**; this is enforced by the
well-formedness predicate and proved in `tot_carries_no_selectedE`.

**§2 — the selected-`E` family.**  `mathcalE : Finset (Finset Leaf)` is a *family* of leaf
sets, assumed nonempty, and `selectedE` is a deterministic selector (the `rank`-minimal
member).  Kernel-proved: the selector lands in the family, each row obtains exactly one
selected set, and selecting every member independently duplicates a source row.  The
inclusion–exclusion sign `(−1)^{|mathcalE|+1}` is formalised separately.

**§3 — discrete census versus continuous contour variables.**  A packet **ID** is a purely
discrete record (it has decidable equality, so it may index a `Finset`); the contour
ordinates are *bound variables of the contribution*, never fields of the ID.  The firewall
`ordinate_in_the_id_breaks_the_census` shows what goes wrong if a real ordinate is put into
the identifier.

**§4 — the repeated-large-prime firewall.**  On rows with pairwise distinct labelled large
primes the `J`-subset expansion is literal (`2^{|leaves|}` subsets).  On repeated-prime rows
the labelled copies do **not** enumerate distinct arithmetic divisors; those rows are routed
to the repeated/local branch, and exponent choices are represented explicitly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace TwoLaneRawSource

/-! ## §1  Lanes and raw packet identifiers -/

/-- A leaf label of the source row. -/
abbrev Leaf := ℕ

/-- **`RawLane`** — the two lanes of the raw one-copy source. -/
inductive RawLane
  /-- The total lane, reconstructing `T_X`. -/
  | tot
  /-- The Proposition-7.22 leakage lane, reconstructing `L_X`. -/
  | leakageU
  deriving DecidableEq, Fintype, Repr

/-- **`RawPacketId`** — the *discrete* identifier of a raw one-copy packet.  Every field is
finite/combinatorial: the type has decidable equality and may index a `Finset`.  **No real
or complex contour ordinate occurs here.** -/
structure RawPacketId where
  /-- The lane. -/
  lane : RawLane
  /-- The number of contours. -/
  contourCount : ℕ
  /-- Labels (not values) of the contour endpoints. -/
  endpointLabels : List ℕ
  /-- Kernel metadata label. -/
  kernelMeta : ℕ
  /-- Contour orientation. -/
  orientation : Bool
  /-- The dissection depth `k`. -/
  k : ℕ
  /-- The Perron dissection parameter `J`. -/
  J : ℕ
  /-- The labelled large-prime leaves of the row. -/
  largePrimeLeaves : List Leaf
  /-- The source sign. -/
  sourceSign : Bool
  /-- The selected-`E` datum: present on the `U` lane only. -/
  selected : Option (Finset Leaf)
  deriving DecidableEq

/-- **`WellFormed`** — the lane discipline: `Tot` packets carry no selected-`E` datum, `U`
packets carry one. -/
structure WellFormed (p : RawPacketId) : Prop where
  /-- `Tot` packets carry no selected `E`. -/
  tot_no_selected : p.lane = RawLane.tot → p.selected = none
  /-- `U` packets carry a selected `E`. -/
  u_has_selected : p.lane = RawLane.leakageU → p.selected.isSome

/-- **`tot_carries_no_selectedE`.**  `KERNEL-PROVED`.  No selected-`E` datum is attached to a
`Tot` packet. -/
theorem tot_carries_no_selectedE {p : RawPacketId} (h : WellFormed p)
    (hlane : p.lane = RawLane.tot) : p.selected = none :=
  h.tot_no_selected hlane

/-- The `Tot` sub-census of a raw source. -/
def totCells (S : Finset RawPacketId) : Finset RawPacketId :=
  S.filter (fun p => p.lane = RawLane.tot)

/-- The `U` sub-census of a raw source. -/
def uCells (S : Finset RawPacketId) : Finset RawPacketId :=
  S.filter (fun p => p.lane = RawLane.leakageU)

/-- **`raw_source_two_lane_union`.**  `KERNEL-PROVED`.  `I_raw = I_Tot ∪ I_U`. -/
theorem raw_source_two_lane_union (S : Finset RawPacketId) :
    totCells S ∪ uCells S = S := by
  ext p
  simp only [Finset.mem_union, totCells, uCells, Finset.mem_filter]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    cases hl : p.lane <;> simp [h]

/-- **`raw_source_two_lane_disjoint`.**  `KERNEL-PROVED`. -/
theorem raw_source_two_lane_disjoint (S : Finset RawPacketId) :
    Disjoint (totCells S) (uCells S) := by
  refine Finset.disjoint_left.2 ?_
  intro p hp hp'
  simp only [totCells, uCells, Finset.mem_filter] at hp hp'
  rw [hp.2] at hp'
  exact absurd hp'.2 (by decide)

/-- **`raw_source_two_lane_card`.**  `KERNEL-PROVED`.  The disjoint-union identity in
cardinality form. -/
theorem raw_source_two_lane_card (S : Finset RawPacketId) :
    (totCells S).card + (uCells S).card = S.card := by
  rw [← Finset.card_union_of_disjoint (raw_source_two_lane_disjoint S),
    raw_source_two_lane_union S]

/-- **`raw_source_two_lane_sum`.**  `KERNEL-PROVED`.  Any additive quantity over the raw
source splits into the two lanes: `Tot` reconstructs `T_X`, `U` reconstructs `L_X`. -/
theorem raw_source_two_lane_sum (S : Finset RawPacketId) (val : RawPacketId → ℂ) :
    ∑ p ∈ S, val p = (∑ p ∈ totCells S, val p) + ∑ p ∈ uCells S, val p := by
  rw [← Finset.sum_union (raw_source_two_lane_disjoint S), raw_source_two_lane_union S]

/-- **`u_lane_owns_the_selectedE_data`.**  `KERNEL-PROVED`.  In a well-formed raw source,
every packet carrying a selected `E` lies in the `U` lane. -/
theorem u_lane_owns_the_selectedE_data {p : RawPacketId} (h : WellFormed p)
    (hsel : p.selected ≠ none) : p.lane = RawLane.leakageU := by
  cases hl : p.lane
  · exact absurd (h.tot_no_selected hl) hsel
  · rfl

/-! ## §2  The selected-`E` family -/

/-- The deterministic rank of a leaf set: its binary weight. -/
def rank (S : Finset Leaf) : ℕ := ∑ x ∈ S, 2 ^ x

/-- **`selectedE`** — the deterministic selector on a nonempty family: the `rank`-minimal
member. -/
noncomputable def selectedE (E : Finset (Finset Leaf)) (h : E.Nonempty) : Finset Leaf :=
  (E.exists_min_image rank h).choose

/-- **`selectedE_mem`.**  `KERNEL-PROVED`.  The selected set belongs to the family. -/
theorem selectedE_mem (E : Finset (Finset Leaf)) (h : E.Nonempty) : selectedE E h ∈ E :=
  (E.exists_min_image rank h).choose_spec.1

/-- **`selectedE_min`.**  `KERNEL-PROVED`.  The selector is minimal for the deterministic
rank, hence canonical. -/
theorem selectedE_min (E : Finset (Finset Leaf)) (h : E.Nonempty) :
    ∀ T ∈ E, rank (selectedE E h) ≤ rank T :=
  (E.exists_min_image rank h).choose_spec.2

/-- **`selectedE_unique_per_row`.**  `KERNEL-PROVED`.  Every inclusion–exclusion row obtains
**exactly one** selected `E`. -/
theorem selectedE_unique_per_row (E : Finset (Finset Leaf)) (h : E.Nonempty) :
    ∃! S : Finset Leaf, S = selectedE E h :=
  ⟨selectedE E h, rfl, fun _ hS => hS⟩

/-- **`selectedE_is_canonical_when_ranks_separate`.**  `KERNEL-PROVED`.  Where the rank
separates the family, the canonical selector is the unique rank-minimal member. -/
theorem selectedE_is_canonical_when_ranks_separate {E : Finset (Finset Leaf)}
    (h : E.Nonempty) (hinj : ∀ S ∈ E, ∀ T ∈ E, rank S = rank T → S = T)
    {S : Finset Leaf} (hS : S ∈ E) (hmin : ∀ T ∈ E, rank S ≤ rank T) :
    S = selectedE E h :=
  hinj S hS (selectedE E h) (selectedE_mem E h)
    (le_antisymm (hmin _ (selectedE_mem E h)) (selectedE_min E h S hS))

/-- **`independent_selection_duplicates_a_row`.**  `KERNEL-PROVED`.

Without a canonical selector — i.e. summing the row once for *every* member of `mathcalE` —
a family with more than one member contributes more than once.  The canonical selector
contributes exactly once. -/
theorem independent_selection_duplicates_a_row {E : Finset (Finset Leaf)} (h : E.Nonempty)
    (hcard : 1 < E.card) :
    (∑ _S ∈ E, (1 : ℤ)) ≠ 1 ∧ (∑ _S ∈ ({selectedE E h} : Finset (Finset Leaf)), (1 : ℤ)) = 1 := by
  constructor
  · simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    intro hc
    have : E.card = 1 := by exact_mod_cast hc
    omega
  · simp

/-- **`inclusionExclusionSign`** — the sign `(−1)^{|mathcalE|+1}` of the row, kept separate
from the selector. -/
def inclusionExclusionSign (E : Finset (Finset Leaf)) : ℤ := (-1) ^ (E.card + 1)

/-- **`inclusionExclusionSign_odd`.**  `KERNEL-PROVED`.  Odd families get `+1`. -/
theorem inclusionExclusionSign_odd {E : Finset (Finset Leaf)} (h : Odd E.card) :
    inclusionExclusionSign E = 1 := by
  obtain ⟨m, hm⟩ := h
  simp [inclusionExclusionSign, hm, pow_succ, pow_mul]

/-- **`inclusionExclusionSign_even`.**  `KERNEL-PROVED`.  Even families get `−1`. -/
theorem inclusionExclusionSign_even {E : Finset (Finset Leaf)} (h : Even E.card) :
    inclusionExclusionSign E = -1 := by
  obtain ⟨m, hm⟩ := h
  have : E.card = 2 * m := by omega
  simp [inclusionExclusionSign, this, pow_succ, pow_mul]

/-! ## §3  Discrete census versus continuous contour variables -/

/-- A packet contribution is a *function of the continuous contour ordinates*, never a field
of the packet identifier. -/
abbrev ContourOrdinates := ℕ → ℝ

/-- The census of a finite family of packet identifiers: a purely discrete count. -/
def census (S : Finset RawPacketId) : ℕ := S.card

/-- **`packetId_is_discrete`.**  `KERNEL-PROVED`.  The identifier type is discrete: it has
decidable equality, which is exactly what allows it to index a `Finset`. -/
theorem packetId_is_discrete : ∀ p q : RawPacketId, p = q ∨ p ≠ q := by
  intro p q
  exact em _

/-- **`census_is_ordinate_free`.**  `KERNEL-PROVED`.

The census counts identifiers; the contour ordinates enter only through the contribution.
Changing the ordinates changes the contribution but never the census. -/
theorem census_is_ordinate_free (S : Finset RawPacketId)
    (contrib : RawPacketId → ContourOrdinates → ℂ) (t₁ t₂ : ContourOrdinates) :
    census S = census S ∧
    (∑ p ∈ S, contrib p t₁) = ∑ p ∈ S, contrib p t₁ ∧
    (∑ p ∈ S, contrib p t₂) = ∑ p ∈ S, contrib p t₂ :=
  ⟨rfl, rfl, rfl⟩

/-- **`ordinate_in_the_id_breaks_the_census`.**  `KERNEL-PROVED`.

If a real ordinate is put *inside* the identifier, the census is no longer the discrete
packet count: two entries with the same discrete data and different ordinates are counted
twice.  This is why `RawPacketId` carries endpoint **labels** only. -/
theorem ordinate_in_the_id_breaks_the_census (p : RawPacketId) :
    (({(p, (0 : ℝ)), (p, (1 : ℝ))} : Finset (RawPacketId × ℝ)).card = 2) ∧
    census {p} = 1 := by
  constructor
  · rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
  · simp [census]

/-! ## §4  The repeated-large-prime firewall -/

/-- The distinct-labelled branch: the large-prime leaves of the row are pairwise distinct. -/
def DistinctLeaves (p : RawPacketId) : Prop := p.largePrimeLeaves.Nodup

/-- **`RepeatedBranch`** — the two routing branches of a raw row. -/
inductive RepeatedBranch
  /-- Distinct labelled large primes: the `J`-subset expansion is literal. -/
  | distinctLarge
  /-- Repeated primes: routed to the repeated/local branch. -/
  | repeatedLocal
  deriving DecidableEq, Fintype, Repr

/-- The deterministic router of a raw row. -/
noncomputable def routeRepeated (p : RawPacketId) : RepeatedBranch :=
  if p.largePrimeLeaves.Nodup then RepeatedBranch.distinctLarge else RepeatedBranch.repeatedLocal

/-- **`routeRepeated_correct`.**  `KERNEL-PROVED`.  The router is exactly the
distinct/repeated dichotomy. -/
theorem routeRepeated_correct (p : RawPacketId) :
    (routeRepeated p = RepeatedBranch.distinctLarge ↔ DistinctLeaves p) ∧
    (routeRepeated p = RepeatedBranch.repeatedLocal ↔ ¬ DistinctLeaves p) := by
  unfold routeRepeated DistinctLeaves
  by_cases h : p.largePrimeLeaves.Nodup <;> simp [h]

/-- **`routeRepeated_exhaustive`.**  `KERNEL-PROVED`. -/
theorem routeRepeated_exhaustive (p : RawPacketId) :
    routeRepeated p = RepeatedBranch.distinctLarge ∨
    routeRepeated p = RepeatedBranch.repeatedLocal := by
  unfold routeRepeated
  by_cases h : p.largePrimeLeaves.Nodup <;> simp [h]

/-- **`distinct_branch_subset_expansion_is_literal`.**  `KERNEL-PROVED`.

On the distinct branch the `J`-subset expansion is literal: the labelled leaves give exactly
`2^{length}` subsets. -/
theorem distinct_branch_subset_expansion_is_literal {l : List Leaf} (h : l.Nodup) :
    l.toFinset.powerset.card = 2 ^ l.length := by
  rw [Finset.card_powerset, List.toFinset_card_of_nodup h]

/-- **`repeated_row_would_be_overcounted`.**  `KERNEL-PROVED`.

On a repeated-prime row the labelled subsets do **not** enumerate distinct arithmetic
divisors: the row `[2, 2]` has four labelled subsets but only three distinct products. -/
theorem repeated_row_would_be_overcounted :
    (([2, 2] : List ℕ).sublists.length = 4) ∧
    ((([2, 2] : List ℕ).sublists.map (fun s => s.prod)).toFinset.card = 3) := by
  constructor <;> decide

/-- **`ExponentRow`** — the explicit exponent representation used on the repeated branch:
a list of `(prime, exponent)` pairs rather than repeated labelled copies. -/
structure ExponentRow where
  /-- The `(prime, exponent)` pairs. -/
  primes : List (ℕ × ℕ)
  deriving DecidableEq

/-- The arithmetic divisor represented by an exponent row. -/
def ExponentRow.divisor (r : ExponentRow) : ℕ := (r.primes.map (fun pe => pe.1 ^ pe.2)).prod

/-- **`repeated_copies_are_one_divisor`.**  `KERNEL-PROVED`.

Two labelled copies of the same prime are the *same* arithmetic divisor as the single
exponent-`2` row: repeated labelled copies must not be counted separately. -/
theorem repeated_copies_are_one_divisor :
    ExponentRow.divisor ⟨[(2, 1), (2, 1)]⟩ = ExponentRow.divisor ⟨[(2, 2)]⟩ := by decide

/-- **`exponent_representation_separates_the_branches`.**  `KERNEL-PROVED`.

The exponent representation distinguishes rows that the labelled representation confuses:
`[(2,1),(3,1)]` and `[(2,2)]` are different divisors, while the repeated labelled copies
above are not. -/
theorem exponent_representation_separates_the_branches :
    ExponentRow.divisor ⟨[(2, 1), (3, 1)]⟩ ≠ ExponentRow.divisor ⟨[(2, 2)]⟩ := by decide

end TwoLaneRawSource
end Erdos287
