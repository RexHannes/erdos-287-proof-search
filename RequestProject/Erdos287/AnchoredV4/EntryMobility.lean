import RequestProject.Erdos287.AnchoredV4.TransitionSystem

/-!
# Anchored V4 — mobility versus the column image (Route B)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Route B asks whether target mobility can move a transition target into the image of the global
column compiler.  The honest content of that question is an **exact intersection statement**, not
a counting statement: a coset of the mobility subgroup meets the column subgroup exactly when the
target lies in their sum.

* `coset_meets_subgroup_iff` — the exact intersection theorem (any abelian group);
* `mobility_targets_not_hit` — a finite witness with four distinct mobility targets which are all
  disjoint from the column image.  Many distinct targets do **not** imply a hit.
-/

namespace Erdos287
namespace AnchoredV4

/-- **Exact coset/subgroup intersection.**  For subgroups `H` (mobility) and `K` (column image) of
an abelian group, the mobility coset of a target `t` meets the column image iff `t ∈ H ⊔ K`. -/
theorem coset_meets_subgroup_iff {G : Type*} [AddCommGroup G] (H K : AddSubgroup G) (t : G) :
    (∃ h ∈ H, t + h ∈ K) ↔ t ∈ H ⊔ K := by
  constructor
  · rintro ⟨h, hh, hk⟩
    have : t = (-h) + (t + h) := by abel
    rw [this]
    exact AddSubgroup.mem_sup.2 ⟨-h, H.neg_mem hh, t + h, hk, rfl⟩
  · intro ht
    obtain ⟨y, hy, z, hz, hyz⟩ := AddSubgroup.mem_sup.1 ht
    refine ⟨-y, H.neg_mem hy, ?_⟩
    have : t + (-y) = z := by rw [← hyz]; abel
    rw [this]
    exact hz

/-- Four distinct mobility targets modulo `8`. -/
def mobilityTargets : Finset (ZMod 8) := {1, 3, 5, 7}

/-- The column image modulo `8` of this witness. -/
def columnImage : Finset (ZMod 8) := {0, 4}

/-- **Firewall (mobility fallacy).**  A mobility family with many distinct targets can be entirely
disjoint from the column image: target abundance is not an intersection theorem. -/
theorem mobility_targets_not_hit :
    mobilityTargets.card = 4 ∧ Disjoint mobilityTargets columnImage := by
  constructor
  · decide
  · decide

/-- Route B in its only legitimate form: mobility solves the transition target exactly when the
target lies in the sum of the mobility subgroup and the column subgroup. -/
theorem mobility_route_B {G : Type*} [AddCommGroup G] (H K : AddSubgroup G) (t : G) :
    (∃ h ∈ H, t + h ∈ K) ↔ t ∈ H ⊔ K := coset_meets_subgroup_iff H K t

end AnchoredV4
end Erdos287
