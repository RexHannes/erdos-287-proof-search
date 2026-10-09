import RequestProject.Erdos287.AnchoredV4.GuardGeometry

/-!
# Anchored V4 — the exact `ENTRY` proposition

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`ENTRY` is the exact entrance datum of the conditional endgame.  It is *not* the vague statement
"all large-prime rows have been handled": every condition below is an explicit proposition about
the finite omission set `Z ⊂ (aM, M)`:

* `Z` has no two adjacent positions (`NoAdjacent`);
* every `z ∈ Z` fails `z ∣ 2 * L Q`, i.e. every omitted position has normalized prime-power
  height `> Q` (`Entry.height_gt`);
* every **odd** omitted position lies in the declared high-height mask, and the mask itself only
  contains positions of height `> Q`: transition heights in the window `[Y, Q]` can therefore only
  be corrected by *even* omissions;
* the entry word value `S_init = ∑_{n ∈ [aM, M] \ Z} 1/n` satisfies the **doubled** denominator
  condition `den S_init ∣ 2 * L Q`.

`Entry` is a structure, so a proof of `∃ e : Entry M aM Q Y, …` is exactly the ENTRY-existence
owner.  `entryDegenerate` shows the axioms are consistent (a degenerate witness with `Z = ∅`);
it is **not** an ENTRY for large `M` and proves nothing about the actual owner.
-/

namespace Erdos287
namespace AnchoredV4

/-- **The exact ENTRY datum** on the interval `[aM, M]` with transition window `[Y, Q]`. -/
structure Entry (M aM Q Y : ℕ) where
  /-- the omitted (zero) positions -/
  Z : Finset ℕ
  /-- the declared high-height odd-zero mask -/
  mask : Finset ℕ
  /-- the low end of the transition window is a legitimate height -/
  one_le_Y : 1 ≤ Y
  /-- the transition window `[Y, Q]` is nonempty -/
  Y_le_Q : Y ≤ Q
  /-- all omitted positions are interior to the interval -/
  Z_subset : Z ⊆ Finset.Ioo aM M
  /-- the `no-00` guard -/
  Z_noAdjacent : NoAdjacent Z
  /-- every omitted position is outside the `2 L Q` lattice -/
  Z_not_dvd : ∀ z ∈ Z, ¬ (z ∣ 2 * L Q)
  /-- odd omissions are confined to the declared mask -/
  Z_odd_mask : ∀ z ∈ Z, ¬ Even z → z ∈ mask
  /-- the mask only contains genuinely high-height positions -/
  mask_high : ∀ n ∈ mask, Q < normHeight n
  /-- the **doubled** denominator condition on the entry word value -/
  den_init : (wordSum (Finset.Icc aM M) Z).den ∣ 2 * L Q

namespace Entry

variable {M aM Q Y : ℕ}

/-- The entry word value. -/
def Sinit (e : Entry M aM Q Y) : ℚ := wordSum (Finset.Icc aM M) e.Z

lemma one_le_Q (e : Entry M aM Q Y) : 1 ≤ Q := le_trans e.one_le_Y e.Y_le_Q

lemma Z_pos (e : Entry M aM Q Y) {z : ℕ} (hz : z ∈ e.Z) : 0 < z := by
  have := e.Z_subset hz
  simp only [Finset.mem_Ioo] at this
  omega

/-- **Height form of the entry condition**: every omitted position has normalized prime-power
height strictly above the top of the transition window. -/
theorem height_gt (e : Entry M aM Q Y) {z : ℕ} (hz : z ∈ e.Z) : Q < normHeight z := by
  by_contra h
  exact e.Z_not_dvd z hz
    ((normalizedHeight_le_iff_dvd_two_lcm (e.Z_pos hz).ne' e.one_le_Q).2
      (not_lt.1 h))

/-- Positions of height `≤ Q` are never in the odd-zero mask; this is the exact reason a fresh
even center with low-height neighbours is safe. -/
theorem not_mem_mask_of_height_le (e : Entry M aM Q Y) {j : ℕ} (hj : normHeight j ≤ Q) : j ∉ e.mask := by
  intro hmem
  exact absurd (e.mask_high j hmem) (not_lt.2 hj)

/-- **Safe even center.**  Omitting a fresh even position whose two neighbours have height `≤ Q`
preserves the `no-00` guard. -/
theorem noAdjacent_insert_safe (e : Entry M aM Q Y) {c : ℕ} (hc : Even c)
    (hnb : ∀ j, (j = c + 1 ∨ j + 1 = c) → normHeight j ≤ Q) :
    NoAdjacent (insert c e.Z) :=
  noAdjacent_insert_even_of_mask e.Z_noAdjacent e.Z_odd_mask hc
    (fun j hj => e.not_mem_mask_of_height_le (hnb j hj))

/-- **Safe even reservoir.**  Omitting a whole fresh block of even positions with low-height
neighbours preserves the `no-00` guard. -/
theorem noAdjacent_union_safe (e : Entry M aM Q Y) {E : Finset ℕ} (hE : ∀ c ∈ E, Even c)
    (hnb : ∀ c ∈ E, ∀ j, (j = c + 1 ∨ j + 1 = c) → normHeight j ≤ Q) :
    NoAdjacent (e.Z ∪ E) :=
  noAdjacent_union_even_of_mask e.Z_noAdjacent e.Z_odd_mask hE
    (fun c hc j hj => e.not_mem_mask_of_height_le (hnb c hc j hj))

/-- The entry denominator condition in normalized-height form. -/
theorem normHeight_den_init_le (e : Entry M aM Q Y) : normHeight e.Sinit.den ≤ Q :=
  (normalizedHeight_le_iff_dvd_two_lcm e.Sinit.den_nz e.one_le_Q).1 e.den_init

end Entry

/-- **Consistency witness** (degenerate).  The `Entry` conditions are satisfiable, so every
conditional theorem with an `Entry` hypothesis is non-vacuous.  This witness has an empty omission
set on the one-point interval `[1,1]` and says nothing about ENTRY existence for large `M`. -/
def entryDegenerate : Entry 1 0 1 1 where
  Z := ∅
  mask := ∅
  one_le_Y := le_rfl
  Y_le_Q := le_rfl
  Z_subset := by simp
  Z_noAdjacent := noAdjacent_empty
  Z_not_dvd := by simp
  Z_odd_mask := by simp
  mask_high := by simp
  den_init := by
    have h : wordSum (Finset.Icc 0 1) (∅ : Finset ℕ) = 1 := by
      decide +kernel
    rw [h]
    simp

end AnchoredV4
end Erdos287
