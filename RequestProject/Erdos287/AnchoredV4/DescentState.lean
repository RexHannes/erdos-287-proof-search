import RequestProject.Erdos287.AnchoredV4.Entry

/-!
# Anchored V4 — exact finite descent data

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A `DescentState` is the exact state of the word during the prime-power descent: the current
omission set `Z`, the guard, the mask discipline, and the current normalized height bound
`den (word value) ∣ 2 * L height`.

A `DescentStep` is one valid descent move.  Every requirement is an explicit proposition, not a
Boolean flag:

* `centers_fresh`  — the new omitted positions are **not** already omitted (no denominator reuse);
* `centers_even`   — every newly omitted position is even (parity discipline);
* `centers_nb_low` — both neighbours of a new center have normalized height `≤ Q`, hence are
  outside the odd-zero mask, hence the `no-00` guard survives;
* `component_hit`  — the new word value satisfies the **doubled** denominator condition at the
  strictly smaller height `newHeight < height`.

`DescentStep.next` builds the successor state; `next_wordSum`, `next_fresh` and
`next_height_lt` record the exact bookkeeping.
-/

namespace Erdos287
namespace AnchoredV4

/-- The exact state of the descent. -/
structure DescentState (aM M Q : ℕ) (mask : Finset ℕ) where
  /-- current normalized-height bound -/
  height : ℕ
  /-- current omission set -/
  Z : Finset ℕ
  /-- omissions live in the interior of the interval (the endpoints stay selected) -/
  Z_subset : Z ⊆ Finset.Ioo aM M
  /-- `no-00` guard -/
  Z_noAdjacent : NoAdjacent Z
  /-- odd omissions are confined to the mask -/
  Z_odd_mask : ∀ z ∈ Z, ¬ Even z → z ∈ mask
  /-- the doubled denominator condition at the current height -/
  den_ok : (wordSum (Finset.Icc aM M) Z).den ∣ 2 * L height

namespace DescentState

variable {aM M Q : ℕ} {mask : Finset ℕ}

/-- The word value of a state. -/
def value (s : DescentState aM M Q mask) : ℚ := wordSum (Finset.Icc aM M) s.Z

/-- Height form of the state invariant. -/
theorem normHeight_value_den_le (s : DescentState aM M Q mask) (h : 1 ≤ s.height) :
    normHeight s.value.den ≤ s.height :=
  (normalizedHeight_le_iff_dvd_two_lcm s.value.den_nz h).1 s.den_ok

end DescentState

/-- One valid descent move at the current height. -/
structure DescentStep (aM M Q : ℕ) (mask : Finset ℕ) (s : DescentState aM M Q mask) where
  /-- the fresh even positions omitted by this move -/
  centers : Finset ℕ
  /-- the height reached after the move -/
  newHeight : ℕ
  /-- the centers are interior to the interval (the endpoints stay selected) -/
  centers_subset : centers ⊆ Finset.Ioo aM M
  /-- **no reuse**: the centers are not already omitted -/
  centers_fresh : Disjoint centers s.Z
  /-- **parity**: all newly omitted positions are even -/
  centers_even : ∀ c ∈ centers, Even c
  /-- **guard**: both neighbours of a center have low normalized height -/
  centers_nb_low : ∀ c ∈ centers, ∀ j, (j = c + 1 ∨ j + 1 = c) → normHeight j ≤ Q
  /-- **strict descent** of the normalized prime-power height -/
  newHeight_lt : newHeight < s.height
  /-- **component hit**: the corrected word value lies in the `2 L newHeight` lattice -/
  component_hit : (wordSum (Finset.Icc aM M) (s.Z ∪ centers)).den ∣ 2 * L newHeight

namespace DescentStep

variable {aM M Q : ℕ} {mask : Finset ℕ} {s : DescentState aM M Q mask}

/-- The successor state produced by a descent move.  The mask hypothesis is exactly the ENTRY
condition `mask_high`. -/
def next (hmask : ∀ n ∈ mask, Q < normHeight n) (d : DescentStep aM M Q mask s) :
    DescentState aM M Q mask where
  height := d.newHeight
  Z := s.Z ∪ d.centers
  Z_subset := Finset.union_subset s.Z_subset d.centers_subset
  Z_noAdjacent :=
    noAdjacent_union_even_of_mask s.Z_noAdjacent s.Z_odd_mask d.centers_even
      (fun c hc j hj hmem => absurd (hmask j hmem) (not_lt.2 (d.centers_nb_low c hc j hj)))
  Z_odd_mask := by
    intro z hz hodd
    rcases Finset.mem_union.1 hz with h | h
    · exact s.Z_odd_mask z h hodd
    · exact absurd (d.centers_even z h) hodd
  den_ok := d.component_hit

@[simp] lemma next_height (hmask : ∀ n ∈ mask, Q < normHeight n) (d : DescentStep aM M Q mask s) :
    (d.next hmask).height = d.newHeight := rfl

@[simp] lemma next_Z (hmask : ∀ n ∈ mask, Q < normHeight n) (d : DescentStep aM M Q mask s) :
    (d.next hmask).Z = s.Z ∪ d.centers := rfl

/-- **Strict height descent.** -/
theorem next_height_lt (hmask : ∀ n ∈ mask, Q < normHeight n) (d : DescentStep aM M Q mask s) :
    (d.next hmask).height < s.height := d.newHeight_lt

/-- **No denominator is consumed twice**: the positions omitted by the move were selected before
the move. -/
theorem next_fresh (d : DescentStep aM M Q mask s) :
    ∀ c ∈ d.centers, c ∉ s.Z := fun _ hc => Finset.disjoint_left.1 d.centers_fresh hc

/-- **Exact value bookkeeping**: the word value drops by exactly the reciprocal sum of the fresh
centers. -/
theorem next_value (hmask : ∀ n ∈ mask, Q < normHeight n) (d : DescentStep aM M Q mask s) :
    (d.next hmask).value = s.value - recipSum d.centers :=
  wordSum_union (d.centers_subset.trans Finset.Ioo_subset_Icc_self) d.centers_fresh

/-- **Every new component is strictly lower.**  After the move, the normalized height of the
denominator of the word value is `< s.height`. -/
theorem next_component_lower (hmask : ∀ n ∈ mask, Q < normHeight n)
    (d : DescentStep aM M Q mask s) (h1 : 1 ≤ d.newHeight) :
    normHeight (d.next hmask).value.den < s.height :=
  lt_of_le_of_lt ((d.next hmask).normHeight_value_den_le h1) d.newHeight_lt

/-- All positions omitted after the move but not before are even. -/
theorem next_new_even (hmask : ∀ n ∈ mask, Q < normHeight n) (d : DescentStep aM M Q mask s) :
    ∀ z ∈ (d.next hmask).Z, z ∉ s.Z → Even z := by
  intro z hz hzs
  rcases Finset.mem_union.1 hz with h | h
  · exact absurd h hzs
  · exact d.centers_even z h

end DescentStep

end AnchoredV4
end Erdos287
