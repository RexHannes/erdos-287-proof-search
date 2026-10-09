import RequestProject.Erdos287.AnchoredV4.FourierAbsorber

/-!
# Anchored V4 — the conditional exact endgame

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This module assembles the exact chain

`ENTRY + DescentSupply + AbsorberSupply ⟹ ∃ final same-word configuration with S_final = 1`.

Every premise is an explicit `Prop` about data:

* `Entry M aM Q Y` — the exact entrance datum (`Entry.lean`);
* `DescentSupply aM M Q Y mask` — a valid descent move exists above the floor height `Y`;
* `AbsorberSupply aM M Q Y mask` — a guarded reservoir exactly absorbs the residual `S − 1`.

`DescentSupply` and `AbsorberSupply` are **not** inhabited anywhere in this project.  The theorem
below is therefore an implication, never an unconditional payment; the conclusion is exact rational
equality `S_final = 1`, not an approximation, and it preserves:

* the original interval and the selected endpoints (`Zf ⊆ Ioo aM M`);
* the `no-00` guard;
* the mask discipline (odd omissions only inside the declared mask);
* freshness: every position omitted after ENTRY is even and was previously selected.
-/

namespace Erdos287
namespace AnchoredV4

variable {M aM Q Y : ℕ} {mask : Finset ℕ}

/-- **Absorber supply** (explicit hypothesis, never inhabited here): at any state already inside
the `2 L Y` lattice, a guarded reservoir absorbs the residual `value − 1` exactly. -/
def AbsorberSupply (aM M Q Y : ℕ) (mask : Finset ℕ) : Prop :=
  ∀ t : DescentState aM M Q mask, t.value.den ∣ 2 * L Y →
    ∃ (R : GuardedReservoir aM M Q t.Z) (E : Finset ℕ), E ⊆ R.positions ∧
      recipSum E = t.value - 1

/-- **Stage 1: ENTRY to low height.**  Under the descent supply, the entry configuration descends
to a configuration whose word value lies in the `2 L Y` lattice, with all invariants intact. -/
theorem entry_to_low_height (e : Entry M aM Q Y) (hdesc : DescentSupply aM M Q Y e.mask) :
    ∃ t : DescentState aM M Q e.mask,
      e.Z ⊆ t.Z ∧ (∀ z ∈ t.Z, z ∉ e.Z → Even z) ∧ t.Z ⊆ Finset.Ioo aM M ∧
      NoAdjacent t.Z ∧ (∀ z ∈ t.Z, ¬ Even z → z ∈ e.mask) ∧ t.value.den ∣ 2 * L Y := by
  obtain ⟨t, -, h2, h3, h4, h5, h6, h7⟩ :=
    descent_terminates e.mask_high hdesc e.toDescentState
  exact ⟨t, h2, h3, h4, h5, h6, h7⟩

/-- **Stage 2: low height to exact absorption.**  A state inside the `2 L Y` lattice together with
an exact guarded absorption of its residual yields a final configuration with word value exactly
`1`. -/
theorem low_height_to_exact_absorb (hmask_high : ∀ n ∈ mask, Q < normHeight n)
    (t : DescentState aM M Q mask) {R : GuardedReservoir aM M Q t.Z} {E : Finset ℕ}
    (hE : E ⊆ R.positions) (habs : recipSum E = t.value - 1) :
    ∃ Zf : Finset ℕ, t.Z ⊆ Zf ∧ Zf ⊆ Finset.Ioo aM M ∧ NoAdjacent Zf ∧
      (∀ z ∈ Zf, ¬ Even z → z ∈ mask) ∧ (∀ z ∈ Zf, z ∉ t.Z → Even z) ∧
      wordSum (Finset.Icc aM M) Zf = 1 := by
  refine ⟨t.Z ∪ E, Finset.subset_union_left, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.union_subset t.Z_subset (hE.trans R.positions_subset)
  · exact R.noAdjacent_absorb hmask_high t.Z_noAdjacent t.Z_odd_mask hE
  · exact R.mask_absorb t.Z_odd_mask hE
  · intro z hz hzt
    rcases Finset.mem_union.1 hz with h | h
    · exact absurd h hzt
    · exact R.positions_even z (hE h)
  · rw [R.wordSum_absorb hE, habs]
    have : wordSum (Finset.Icc aM M) t.Z = t.value := rfl
    rw [this]
    ring

/-- **The conditional exact endgame.**  `ENTRY + DescentSupply + AbsorberSupply` produce a final
same-word configuration of exact value `1`, on the same interval, with selected endpoints, the
`no-00` guard, the mask discipline, and only fresh even new omissions.

This is an implication.  Neither `DescentSupply` nor `AbsorberSupply` is proved here, and nothing
below claims a #287 counterexample: the bridge from a value-`1` configuration to the original
Erdős #287 sequence statement is a separate, still open, obligation
(`ENTRY_TO_ORIGINAL_287_BRIDGE` in `OpenOwners.lean`). -/
theorem conditional_entry_to_exact_one (e : Entry M aM Q Y)
    (hdesc : DescentSupply aM M Q Y e.mask) (habs : AbsorberSupply aM M Q Y e.mask) :
    ∃ Zf : Finset ℕ, e.Z ⊆ Zf ∧ Zf ⊆ Finset.Ioo aM M ∧ NoAdjacent Zf ∧
      (∀ z ∈ Zf, ¬ Even z → z ∈ e.mask) ∧ (∀ z ∈ Zf, z ∉ e.Z → Even z) ∧
      wordSum (Finset.Icc aM M) Zf = 1 := by
  obtain ⟨t, hsub, hnew, -, -, -, hden⟩ := entry_to_low_height e hdesc
  obtain ⟨R, E, hE, habsE⟩ := habs t hden
  obtain ⟨Zf, h1, h2, h3, h4, h5, h6⟩ :=
    low_height_to_exact_absorb e.mask_high t hE habsE
  refine ⟨Zf, hsub.trans h1, h2, h3, h4, ?_, h6⟩
  intro z hz hze
  by_cases hzt : z ∈ t.Z
  · exact hnew z hzt hze
  · exact h5 z hz hzt

end AnchoredV4
end Erdos287
