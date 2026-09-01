import RequestProject.CurrentProgramme.Erdos287PhysicalDictionaryInterfaces

/-!
# Erdős #287 — physical source coverage: abstract owner map and its firewall

An **abstract** owner map assigns to every packet in a finite domain a unique owner.  From
that alone one gets exact, deterministic bookkeeping (no double spending, exhaustive
accounting) — **but only over the domain**.

This module proves both halves:

* `ownerMap_no_double_spending` / `ownerMap_exhaustive` — exact accounting over the domain;
* `coverage_of_domain` — if every physical packet lies in the domain, the physical total is
  exactly the owner-wise total;
* `abstractOwnerMap_does_not_imply_physicalSourceCoverage100` — the firewall: an owner map
  whose domain misses physical packets undercounts, with an explicit finite countermodel;
  and `physicalSourceCoverage100` requires the (missing) master physical source realisation,
  so it is uninhabited for the countermodel spec.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace SourceCoverage

open Erdos287.PhysicalDictionary

/-! ## §1  The abstract owner map -/

/-- **An abstract finite owner map.**  A finite domain of packets, an owner for each packet,
and a non-negative mass. -/
structure PhysicalOwnerMap where
  /-- The finite domain of packets the map actually covers. -/
  domain : Finset ℕ
  /-- The owner of each packet. -/
  owner : ℕ → Owner
  /-- The mass of each packet. -/
  mass : ℕ → ℝ
  /-- Masses are non-negative. -/
  mass_nonneg : ∀ p, 0 ≤ mass p

namespace PhysicalOwnerMap

variable (O : PhysicalOwnerMap)

/-- The packets of the domain owned by a given owner. -/
def fibre (o : Owner) : Finset ℕ := O.domain.filter (fun p => O.owner p = o)

/-- **`ownerMap_no_double_spending`.**  `LEAN_PROVED`.  The owner fibres are pairwise
disjoint: a packet is never spent twice. -/
theorem no_double_spending {o o' : Owner} (h : o ≠ o') :
    Disjoint (O.fibre o) (O.fibre o') := by
  classical
  refine Finset.disjoint_left.2 fun p hp hp' => ?_
  simp only [fibre, Finset.mem_filter] at hp hp'
  exact h (hp.2 ▸ hp'.2 ▸ rfl)

/-- **`ownerMap_exhaustive`.**  `LEAN_PROVED`.  Summing the owner fibres reproduces the
total mass over the domain exactly: nothing is lost and nothing is counted twice. -/
theorem exhaustive : ∑ o : Owner, ∑ p ∈ O.fibre o, O.mass p = ∑ p ∈ O.domain, O.mass p := by
  classical
  simpa [fibre] using Finset.sum_fiberwise O.domain O.owner O.mass

/-- **`coverage_of_domain`.**  `LEAN_PROVED`.  *If* every physical packet is in the domain
(and the domain contains nothing else), the owner-wise total is exactly the physical total.
This is the only situation in which the abstract bookkeeping is a coverage statement. -/
theorem coverage_of_domain (physical : Finset ℕ) (hcover : physical = O.domain) :
    ∑ o : Owner, ∑ p ∈ O.fibre o, O.mass p = ∑ p ∈ physical, O.mass p := by
  rw [hcover]; exact O.exhaustive

end PhysicalOwnerMap

/-! ## §2  The coverage firewall -/

/-- The countermodel owner map: it covers the single packet `0`, while the physical packet
set is `{0, 1}`; every packet has mass `1`. -/
def partialOwnerMap : PhysicalOwnerMap where
  domain := {0}
  owner := fun _ => Owner.c0
  mass := fun _ => 1
  mass_nonneg := fun _ => zero_le_one

/-- **`abstractOwnerMap_does_not_imply_physicalSourceCoverage100`.**  `LEAN_PROVED`.  An
abstract owner map with exact internal bookkeeping can still undercount the physical source:
here the owner-wise total is `1` while the physical total is `2`. -/
theorem abstractOwnerMap_does_not_imply_physicalSourceCoverage100 :
    (∑ o : Owner, ∑ p ∈ partialOwnerMap.fibre o, partialOwnerMap.mass p) = 1 ∧
      (∑ p ∈ ({0, 1} : Finset ℕ), partialOwnerMap.mass p) = 2 ∧
      (∑ o : Owner, ∑ p ∈ partialOwnerMap.fibre o, partialOwnerMap.mass p)
        ≠ ∑ p ∈ ({0, 1} : Finset ℕ), partialOwnerMap.mass p := by
  have h1 : (∑ o : Owner, ∑ p ∈ partialOwnerMap.fibre o, partialOwnerMap.mass p) = 1 := by
    rw [partialOwnerMap.exhaustive]
    simp [partialOwnerMap]
  have h2 : (∑ p ∈ ({0, 1} : Finset ℕ), partialOwnerMap.mass p) = 2 := by
    simp [partialOwnerMap]
  exact ⟨h1, h2, by rw [h1, h2]; norm_num⟩

/-- **`physicalSourceCoverage100`.**  A genuine 100% coverage claim: an owner map together
with the (missing) master physical source realisation whose index family is *exactly* the
domain, and whose weights are the masses.  **Left uninhabited.** -/
structure PhysicalSourceCoverage100 (spec : MasterSource.SourceSpec) where
  /-- The missing master physical source realisation. -/
  source : MasterSource.MasterPhysicalSourceRealisation spec
  /-- The abstract owner map. -/
  ownerMap : PhysicalOwnerMap
  /-- The domain is exactly the physical index family: this is the coverage claim. -/
  domain_eq : ownerMap.domain = source.index
  /-- The masses are the physical weight masses. -/
  mass_eq : ∀ p ∈ ownerMap.domain, ownerMap.mass p = ‖spec.requiredWeight p‖

/-- Given a coverage claim, the owner-wise total is exactly the physical weight mass. -/
theorem coverage100_total {spec : MasterSource.SourceSpec}
    (C : PhysicalSourceCoverage100 spec) :
    ∑ o : Owner, ∑ p ∈ C.ownerMap.fibre o, C.ownerMap.mass p
      = ∑ p ∈ C.source.index, ‖spec.requiredWeight p‖ := by
  rw [C.ownerMap.exhaustive, ← C.domain_eq]
  exact Finset.sum_congr rfl fun p hp => C.mass_eq p hp

/-- **`physicalSourceCoverage100_open`.**  Coverage is not established: for the countermodel
spec the coverage type is empty, because it requires the master physical source
realisation. -/
theorem physicalSourceCoverage100_open :
    ¬ Nonempty (PhysicalSourceCoverage100 MasterSource.vanishingWeightSpec) := by
  rintro ⟨C⟩
  exact MasterSource.no_realisation_vanishingWeightSpec ⟨C.source⟩

/-- **Combined verdict.**  Abstract owner bookkeeping is available and exact; physical
100% source coverage is not. -/
theorem ownerBookkeeping_available_coverage_open (O : PhysicalOwnerMap) :
    (∑ o : Owner, ∑ p ∈ O.fibre o, O.mass p = ∑ p ∈ O.domain, O.mass p) ∧
      ¬ Nonempty (PhysicalSourceCoverage100 MasterSource.vanishingWeightSpec) :=
  ⟨O.exhaustive, physicalSourceCoverage100_open⟩

end SourceCoverage
end Erdos287
