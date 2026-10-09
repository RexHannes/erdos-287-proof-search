import RequestProject.Erdos287.ResearchBankV6.UpperGapCarry

/-!
# Erdős #287 — Research Bank V6: the two new open owners

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Two owners are introduced here, both **uninhabited**:

* `UpperGapCarryCompression*` — the quantitatively explicit compression/lattice statement for
  admissible aggregate carries `K_N`, conditioned on the same physical no-00 trace.  Because the
  current mathematics does not yet single out the strongest useful quantitative form, **four**
  clearly labelled candidate interfaces are recorded (support, window, size, granularity).  All
  four are uninhabited; only their exact logical consequences are proved.
* `ExactMassIntersection` — the unresolved step from denominator-entry / aggregate-carry
  information plus the available middle mass spectrum to the exact equation `S = 1`.

The firewall `den_dvd_does_not_close` is machine-checked: knowing `den(S) ∣ J` is **not** closure.
-/

namespace Erdos287
namespace ResearchBankV6
namespace OpenOwners

open Finset
open Erdos287.ResearchBankV6.UpperGap

/-! ## 1.  Admissible carry data -/

/-- The data consumed by the compression owner: a finite set of heights, the aggregate carries
`K_N`, and the physical `no-00` trace admissibility predicate (kept abstract, since it is a
property of the *physical* selection, not of the numbers `K_N`). -/
structure CarryData where
  /-- The finite set of heights occurring in the current upper gap. -/
  heights : Finset ℕ
  /-- The aggregate carry at each height. -/
  K : ℕ → ℕ
  /-- The physical `no-00` trace admissibility of the underlying selection. -/
  admissible : Prop

/-- The set of *active* heights, i.e. those carrying a nonzero aggregate carry. -/
def activeHeights (d : CarryData) : Finset ℕ := d.heights.filter (fun N => d.K N ≠ 0)

/-- The aggregate upper-gap mass `∑_N K_N / L_N`. -/
def aggregateMass (d : CarryData) : ℚ := ∑ N ∈ d.heights, (d.K N : ℚ) / lcmUpto N

/-- Only active heights contribute to the aggregate mass (kernel). -/
theorem aggregateMass_eq_active (d : CarryData) :
    aggregateMass d = ∑ N ∈ activeHeights d, (d.K N : ℚ) / lcmUpto N := by
  rw [aggregateMass, activeHeights]
  refine (Finset.sum_filter_of_ne ?_).symm
  intro N _ hne hK
  apply hne
  rw [hK]
  simp

/-! ## 2.  Candidate interfaces for UPPER-GAP CARRY COMPRESSION (all uninhabited) -/

/-- **Candidate A — support compression.**  Every admissible carry configuration has at most `c`
active heights.  Quantitative target of the next consumer: `c` absolute (independent of `M`). -/
def UpperGapCarryCompressionSupport (c : ℕ) : Prop :=
  ∀ d : CarryData, d.admissible → (activeHeights d).card ≤ c

/-- **Candidate B — window compression.**  All active heights of an admissible configuration lie
in a window of explicit width `w` above the smallest active height. -/
def UpperGapCarryCompressionWindow (w : ℕ) : Prop :=
  ∀ d : CarryData, d.admissible → ∀ N ∈ activeHeights d, ∀ N' ∈ activeHeights d, N ≤ N' + w

/-- **Candidate C — size compression.**  The aggregate carry at each height is bounded by
`c · L_N / N`: the carry cannot use the whole residue range of its height. -/
def UpperGapCarryCompressionSize (c : ℕ) : Prop :=
  ∀ d : CarryData, d.admissible → ∀ N ∈ d.heights, 1 ≤ N → N * d.K N ≤ c * lcmUpto N

/-- **Candidate D — granularity / lattice compression.**  The aggregate upper-gap mass of an
admissible configuration lies in the lattice `(1 / L_D) ℤ` for the explicit modulus `D`; this is
the exact form the mass-intersection consumer asks for. -/
def UpperGapCarryCompressionGranularity (D : ℕ) : Prop :=
  ∀ d : CarryData, d.admissible → ∃ k : ℤ, aggregateMass d = (k : ℚ) / lcmUpto D

/-- The four candidates are recorded as *distinct* interfaces; no reduction between them is
claimed here. -/
theorem compression_candidates_not_reduced :
    (UpperGapCarryCompressionSupport 1 → UpperGapCarryCompressionSupport 1) ∧
    (UpperGapCarryCompressionWindow 1 → UpperGapCarryCompressionWindow 1) ∧
    (UpperGapCarryCompressionSize 1 → UpperGapCarryCompressionSize 1) ∧
    (UpperGapCarryCompressionGranularity 1 → UpperGapCarryCompressionGranularity 1) :=
  ⟨id, id, id, id⟩

/-! ## 3.  Exact consequences of the candidates (conditional, kernel-proved implications) -/

/-- **CONDITIONAL.**  Under support compression with `c = 1`, an admissible aggregate mass is a
single carry fraction `K_N / L_N`, or zero. -/
theorem mass_single_term_of_support_one (h : UpperGapCarryCompressionSupport 1)
    (d : CarryData) (hd : d.admissible) :
    aggregateMass d = 0 ∨ ∃ N, aggregateMass d = (d.K N : ℚ) / lcmUpto N := by
  have hcard := h d hd
  rw [aggregateMass_eq_active]
  rcases Finset.card_le_one.1 hcard with hone
  rcases Finset.eq_empty_or_nonempty (activeHeights d) with hempty | ⟨N, hN⟩
  · left; rw [hempty]; simp
  · right
    refine ⟨N, ?_⟩
    have : activeHeights d = {N} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨hN, fun x hx => hone x hx N hN⟩
    rw [this, Finset.sum_singleton]

/-- **CONDITIONAL.**  Under granularity compression at modulus `D`, the admissible upper-gap mass
has reduced denominator dividing `L_D`; this is exactly the input format requested by the
mass-intersection consumer. -/
theorem mass_den_dvd_of_granularity {D : ℕ} (h : UpperGapCarryCompressionGranularity D)
    (d : CarryData) (hd : d.admissible) : (aggregateMass d).den ∣ lcmUpto D :=
  (den_dvd_iff (lcmUpto_pos D)).2 (h d hd)

/-- **Kernel.**  Aggregating several carries that already live in the lattice `(1/L)ℤ` stays in
that lattice — the exact granularity algebra that the compression owner must supply externally
only for the *admissibility* part. -/
theorem sum_in_lattice {L : ℕ} (S : Finset ℕ) (k : ℕ → ℤ) :
    ∃ m : ℤ, ∑ N ∈ S, (k N : ℚ) / L = (m : ℚ) / L := by
  refine ⟨∑ N ∈ S, k N, ?_⟩
  rw [← Finset.sum_div]
  push_cast
  ring

/-! ## 4.  The final owner: exact mass intersection -/

/-- **`ExactMassIntersection`, OWNER-OPEN.**  Given the frozen core/top mass `frozen`, the set
`middleSpectrum` of masses realizable by the completed middle band, and the set `upperSpectrum` of
masses realizable by admissible upper-gap carries, the unresolved step is the exact equation
`S = 1`: no admissible combination sums to `1`.

This is **uninhabited**: it is the open final owner, not a theorem of this layer. -/
def ExactMassIntersection (frozen : ℚ) (middleSpectrum upperSpectrum : Set ℚ) : Prop :=
  ∀ m ∈ middleSpectrum, ∀ u ∈ upperSpectrum, frozen + m + u ≠ 1

/-- The exact logical consequence of the final owner: an admissible configuration cannot have
total mass `1`. -/
theorem no_unit_mass_of_exactMassIntersection {frozen : ℚ} {middleSpectrum upperSpectrum : Set ℚ}
    (h : ExactMassIntersection frozen middleSpectrum upperSpectrum)
    {m u : ℚ} (hm : m ∈ middleSpectrum) (hu : u ∈ upperSpectrum) : frozen + m + u ≠ 1 :=
  h m hm u hu

/-! ## 5.  Firewall: denominator information is not closure -/

/-- **FIREWALL (machine-checked).**  `den(S) ∣ J` does **not** close Erdős #287: for every
modulus `J ≥ 2` there is a rational `S` with `den(S) ∣ J`, `0 < S < 1` (so `S ≠ 1`).  Knowing the
denominator of the total mass therefore never yields the exact equation `S = 1`. -/
theorem den_dvd_does_not_close (J : ℕ) (hJ : 2 ≤ J) :
    ∃ S : ℚ, S.den ∣ J ∧ 0 < S ∧ S < 1 ∧ S ≠ 1 := by
  refine ⟨((J : ℚ) - 1) / J, ?_, ?_, ?_, ?_⟩
  · have h : ((J : ℚ) - 1) / J = (((J : ℤ) - 1 : ℤ) : ℚ) / ((J : ℤ) : ℚ) := by push_cast; ring
    rw [h]
    exact (den_dvd_iff (by omega : 0 < J)).2 ⟨(J : ℤ) - 1, rfl⟩
  · have hJ' : (0:ℚ) < (J:ℚ) := by positivity
    have : (1:ℚ) ≤ (J:ℚ) - 1 := by
      have : (2:ℚ) ≤ (J:ℚ) := by exact_mod_cast hJ
      linarith
    positivity
  · have hJ' : (0:ℚ) < (J:ℚ) := by
      have : (2:ℚ) ≤ (J:ℚ) := by exact_mod_cast hJ
      linarith
    rw [div_lt_one hJ']
    linarith
  · intro hcon
    have hJ' : (0:ℚ) < (J:ℚ) := by
      have : (2:ℚ) ≤ (J:ℚ) := by exact_mod_cast hJ
      linarith
    rw [div_eq_one_iff_eq (ne_of_gt hJ')] at hcon
    linarith

/-- The same firewall in non-implication form: denominator divisibility never implies `S = 1`. -/
theorem den_dvd_not_sufficient : ¬ (∀ (S : ℚ) (J : ℕ), 0 < J → S.den ∣ J → S = 1) := by
  intro h
  have := h 0 1 (by norm_num) (by simp)
  norm_num at this

end OpenOwners
end ResearchBankV6
end Erdos287
