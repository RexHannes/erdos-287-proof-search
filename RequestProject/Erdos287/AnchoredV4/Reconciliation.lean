import RequestProject.Erdos287.AnchoredV4.EntryObstructions
import RequestProject.Erdos287.AnchoredV3

/-!
# Anchored V4 — reconciliation with the frozen Anchored V3 bank

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Anchored V2 and Anchored V3 are frozen: this module only *uses* them.  It answers the
reconciliation questions with theorems whose types line up exactly, and records the questions
whose interfaces do **not** line up as open items (`OpenOwners.lean`) rather than pretending a
bridge exists.

Established bridges:

* `mobility_preserves_doubled_lattice` — every V3 target-mobility state satisfies the V4
  normalized-height condition as soon as the V3 core modulus lies in the `2 L Y` lattice
  (reconciliation question 2);
* `absorber_is_sumset_membership` — V4 exact absorption is membership of the target numerator in
  the subset-sum set of the reservoir weights, the same shape as the V3 alignment sumset
  (reconciliation question 3);
* `noAdjacent_to_V3_no00` — the V4 `no-00` guard implies the frozen V3 `No00` predicate with the
  successor guard (reconciliation question 1);
* `dvd_iff_forall_component` — the exact prime-power component splitting, which is what reduces a
  global ENTRY congruence to one constraint per active component (reconciliation question 4);
* the V3 firewalls are re-checked below and remain in force (reconciliation question 5).
-/

namespace Erdos287
namespace AnchoredV4

/-- **Reconciliation 2.**  A V3 mobility state keeps the V4 doubled-denominator condition: if the
V3 core modulus is inside the `2 L Y` lattice, then every moved baseline has normalized
prime-power height at most `Y`. -/
theorem mobility_preserves_doubled_lattice {H : ℕ} (M : AnchoredV3.MobilityData H) {Y : ℕ}
    (hY : 1 ≤ Y) (hcore : M.Dcore ∣ 2 * L Y) (y : Finset (Fin H)) :
    normHeight (M.S y).den ≤ Y :=
  (normalizedHeight_le_iff_dvd_two_lcm (M.S y).den_nz hY).1 ((M.den_dvd_Dcore y).trans hcore)

/-- **Reconciliation 3.**  Exact absorption by a guarded reservoir is exactly membership of the
target numerator in the subset-sum set of the reservoir weights — the finite coefficient shape
used by the V3 alignment sumset. -/
theorem absorber_is_sumset_membership {aM M Q : ℕ} {Zcur : Finset ℕ}
    (R : GuardedReservoir aM M Q Zcur) {P k : ℕ} (hP : P ≠ 0)
    (hdvd : ∀ n ∈ R.positions, n ≠ 0 ∧ n ∣ P) {Δ : ℚ} (hΔ : Δ * P = k) :
    R.AbsorbsExactly Δ ↔ ∃ E ⊆ R.positions, ∑ n ∈ E, weight P n = k :=
  exact_absorption_iff_weight_subsetSum hP hdvd hΔ

/-- **Reconciliation 1.**  The V4 guard implies the frozen V3 `No00` predicate for the successor
guard on any set of positions whose successors stay inside the interval. -/
theorem noAdjacent_to_V3_no00 {aM M : ℕ} {Z positions : Finset ℕ}
    (hZ : NoAdjacent Z) (hpos : ∀ p ∈ positions, p ∈ Finset.Icc aM M ∧ p + 1 ∈ Finset.Icc aM M) :
    AnchoredV3.No00 (fun p => p + 1) positions (Finset.Icc aM M \ Z) := by
  intro p hp
  by_cases hpZ : p ∈ Z
  · exact Or.inr (Finset.mem_sdiff.2 ⟨(hpos p hp).2, hZ p hpZ⟩)
  · exact Or.inl (Finset.mem_sdiff.2 ⟨(hpos p hp).1, hpZ⟩)

/-- **Reconciliation 4.**  A divisibility by the transition modulus is exactly the conjunction of
its prime-power component constraints: the number of independent ENTRY constraints is the number
of active prime-power components, no more. -/
theorem dvd_iff_forall_component {r x : ℕ} (hr : r ≠ 0) (hx : x ≠ 0) :
    r ∣ x ↔ ∀ p ∈ r.primeFactors, p ^ r.factorization p ∣ x := by
  constructor
  · intro h p _
    exact (Nat.ordProj_dvd r p).trans h
  · intro h
    rw [← Nat.factorization_le_iff_dvd hr hx, Finsupp.le_iff]
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
    have := h p (by simpa using hp)
    exact (Nat.Prime.pow_dvd_iff_le_factorization hpp hx).1 this

/-! ## The frozen V3 firewalls remain in force

These are referenced, never re-proved, re-stated or weakened. -/

#check @Erdos287.AnchoredV3.rowwise_sufficient_not_necessary
#check @Erdos287.AnchoredV3.ColumnPackets.manyNeutralPackets_not_exactTarget
#check @Erdos287.AnchoredV3.OldEmptyNewHit.same_bank_old_empty_new_global_hit
#check @Erdos287.AnchoredV3.ColumnLattice.sharpness_witness_two
#check @Erdos287.AnchoredV3.AlignedBank.alignment_coefficient

/-- The V4 firewalls added on top of the frozen V3 ones. -/
theorem v4_firewalls_in_force :
    (¬ (∀ (q : ℚ) (P : ℕ), (2 * q).den ∣ P → q.den ∣ P)) ∧
      (¬ singletonReservoir.AbsorbsExactly (1 / 8)) ∧
      (¬ gcdWitnessSystem.Solvable) ∧
      (Disjoint mobilityTargets columnImage) :=
  ⟨den_dvd_not_iff_den_two_mul_dvd, positive_mass_not_exact_coverage.2.2,
    gcdWitnessSystem_unsolvable, mobility_targets_not_hit.2⟩

end AnchoredV4
end Erdos287
