import RequestProject.Erdos287.AnchoredV4.DescentState

/-!
# Anchored V4 — well-founded prime-power descent

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`DescentSupply aM M Q y mask` is the **explicit hypothesis** that a valid descent move exists at
every state whose height exceeds `y`.  It is a `Prop` about data, not an axiom, and it is the
honest owner `SAFE_DESCENT_SUPPLY`: nothing in this layer inhabits it.

Given that supply, `descent_terminates` proves — by genuine `Nat` descent on the height, not by
appeal to intuition — that iterated descent reaches a state of height `≤ y`, and that the reached
state still satisfies **all** exact invariants:

* the interval and the `no-00` guard;
* the mask discipline (odd omissions only inside the mask);
* every newly omitted position is even and was previously selected (no reuse);
* the doubled denominator condition `den (word value) ∣ 2 * L y`.
-/

namespace Erdos287
namespace AnchoredV4

variable {aM M Q y : ℕ} {mask : Finset ℕ}

/-- **Descent supply** (explicit hypothesis, never inhabited here): a valid descent move exists at
every state above the floor height `y`. -/
def DescentSupply (aM M Q y : ℕ) (mask : Finset ℕ) : Prop :=
  ∀ s : DescentState aM M Q mask, y < s.height → Nonempty (DescentStep aM M Q mask s)

private theorem descent_aux (hmask : ∀ n ∈ mask, Q < normHeight n)
    (hsupply : DescentSupply aM M Q y mask) :
    ∀ (n : ℕ) (s : DescentState aM M Q mask), s.height ≤ n →
      ∃ t : DescentState aM M Q mask, t.height ≤ y ∧ s.Z ⊆ t.Z ∧
        (∀ z ∈ t.Z, z ∉ s.Z → Even z) := by
  intro n
  induction n with
  | zero =>
      intro s hs
      exact ⟨s, le_trans hs (Nat.zero_le y), Finset.Subset.refl _, by intro z hz hz'; exact absurd hz hz'⟩
  | succ n ih =>
      intro s hs
      by_cases hy : s.height ≤ y
      · exact ⟨s, hy, Finset.Subset.refl _, by intro z hz hz'; exact absurd hz hz'⟩
      · obtain ⟨d⟩ := hsupply s (not_le.1 hy)
        have hlt : d.newHeight < s.height := d.newHeight_lt
        have hle : (d.next hmask).height ≤ n := by
          simp only [DescentStep.next_height]
          omega
        obtain ⟨t, ht1, ht2, ht3⟩ := ih (d.next hmask) hle
        refine ⟨t, ht1, ?_, ?_⟩
        · exact Finset.Subset.trans (by simp [DescentStep.next_Z]) ht2
        · intro z hz hzs
          by_cases hmem : z ∈ (d.next hmask).Z
          · exact d.next_new_even hmask z hmem hzs
          · exact ht3 z hz hmem

/-- **Well-founded prime-power descent.**  If a valid descent move exists at every height above
`y`, iterated descent terminates at a state of height `≤ y`, preserving every exact invariant of
the descent state, and the terminal word value lies in the `2 * L y` lattice. -/
theorem descent_terminates (hmask : ∀ n ∈ mask, Q < normHeight n)
    (hsupply : DescentSupply aM M Q y mask) (s : DescentState aM M Q mask) :
    ∃ t : DescentState aM M Q mask,
      t.height ≤ y ∧ s.Z ⊆ t.Z ∧ (∀ z ∈ t.Z, z ∉ s.Z → Even z) ∧
      t.Z ⊆ Finset.Ioo aM M ∧ NoAdjacent t.Z ∧
      (∀ z ∈ t.Z, ¬ Even z → z ∈ mask) ∧ t.value.den ∣ 2 * L y := by
  obtain ⟨t, ht1, ht2, ht3⟩ := descent_aux hmask hsupply s.height s le_rfl
  exact ⟨t, ht1, ht2, ht3, t.Z_subset, t.Z_noAdjacent, t.Z_odd_mask,
    dvd_two_L_mono ht1 t.den_ok⟩

/-- Height form of the descent conclusion: the terminal normalized prime-power height is at most
the floor `y`. -/
theorem descent_normHeight_le (hmask : ∀ n ∈ mask, Q < normHeight n)
    (hsupply : DescentSupply aM M Q y mask) (hy : 1 ≤ y) (s : DescentState aM M Q mask) :
    ∃ t : DescentState aM M Q mask, s.Z ⊆ t.Z ∧ normHeight t.value.den ≤ y := by
  obtain ⟨t, ht1, ht2, -, -, -, -, hden⟩ := descent_terminates hmask hsupply s
  exact ⟨t, ht2, (normalizedHeight_le_iff_dvd_two_lcm t.value.den_nz hy).1 hden⟩

/-- The `ENTRY` datum is a descent state at height `Q`. -/
def Entry.toDescentState {M aM Q Y : ℕ} (e : Entry M aM Q Y) :
    DescentState aM M Q e.mask where
  height := Q
  Z := e.Z
  Z_subset := e.Z_subset
  Z_noAdjacent := e.Z_noAdjacent
  Z_odd_mask := e.Z_odd_mask
  den_ok := e.den_init

@[simp] lemma Entry.toDescentState_height {M aM Q Y : ℕ} (e : Entry M aM Q Y) :
    e.toDescentState.height = Q := rfl

@[simp] lemma Entry.toDescentState_Z {M aM Q Y : ℕ} (e : Entry M aM Q Y) :
    e.toDescentState.Z = e.Z := rfl

lemma Entry.toDescentState_value {M aM Q Y : ℕ} (e : Entry M aM Q Y) :
    e.toDescentState.value = e.Sinit := rfl

end AnchoredV4
end Erdos287
