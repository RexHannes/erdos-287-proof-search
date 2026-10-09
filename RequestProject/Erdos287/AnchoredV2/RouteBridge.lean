import RequestProject.Erdos287.AnchoredV2.CapacityGap
import RequestProject.Erdos287.AnchoredV2.Level2
import RequestProject.Erdos287.AnchoredV2.TrackedKernel
import RequestProject.Erdos287.Anchored.BicyclicInterface

/-!
# Anchored V2 — bridges to the actual anchored kernels

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Every anchored contact instance (in particular every leafless branching kernel produced by the
Anchored V1 peeling) canonically determines a port system: its blocks are the contact
positions, its contact edges are the anchored contact edges, and the complete local relation of
a position is `{incident edges}` when the position may be selected and `{∅}` when it may be
omitted.  Capacity data and Level-2 data are then the data of that port system.

Consequently a negative capacity certificate, or Level-2 fractional infeasibility, rejects the
actual anchored kernel.  Neither certificate is claimed to exist for any particular kernel: the
corresponding *uniform* statements are recorded as explicit open owners, and they are shown to
**refine** the Anchored V1 open owner `BranchingKernelRejection`.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV2

open Erdos287.Anchored
open Erdos287.Anchored.ContactCSP

/-- The contact edges incident to a position. -/
def incidentEdges (I : ContactCSP) (v : ℕ) : Finset (ℕ × ℕ) :=
  I.Edges.filter (fun e => e.1 = v ∨ e.2 = v)

/-- The port system canonically determined by an anchored contact instance. -/
def portOfContact (I : ContactCSP) : PortSystem (ℕ × ℕ) where
  Blocks := I.V
  Edges := I.Edges
  ep := id
  L := fun v =>
    (if I.dom v true then {incidentEdges I v} else ∅) ∪
      (if I.dom v false then {(∅ : Finset (ℕ × ℕ))} else ∅)

theorem portOfContact_wellFormed {I : ContactCSP} (hwf : I.WellFormed) :
    (portOfContact I).WellFormed := by
  intro e he
  exact hwf e he

/-- **`feasible_of_sat`.**  `KERNEL-PROVED`.  A satisfying assignment of an anchored contact
instance with contact (OR) relations gives an integral solution of its port system. -/
theorem feasible_of_sat {I : ContactCSP}
    (hOR : ∀ e ∈ I.Edges, ∀ a b : Bool, I.rel e.1 e.2 a b = (a || b)) (hsat : I.Sat) :
    (portOfContact I).Feasible := by
  classical
  obtain ⟨f, hdom, hrel⟩ := hsat
  refine ⟨fun v => if f v then incidentEdges I v else ∅, ?_, ?_⟩
  · intro v hv
    have hd := hdom v hv
    by_cases hfv : f v = true
    · rw [hfv] at hd
      simp only [portOfContact, hfv, if_true, if_pos hd]
      exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
    · have hfv' : f v = false := by
        cases hc : f v with
        | false => rfl
        | true => exact absurd hc hfv
      rw [hfv'] at hd
      simp only [portOfContact, hfv', if_pos hd]
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  · intro e he
    have hor := hrel e he
    rw [hOR e he] at hor
    rcases Bool.or_eq_true_iff.1 hor with h | h
    · left
      simp only [portOfContact, id_eq, h, if_true]
      exact Finset.mem_filter.2 ⟨he, Or.inl rfl⟩
    · right
      simp only [portOfContact, id_eq, h, if_true]
      exact Finset.mem_filter.2 ⟨he, Or.inr rfl⟩

/-- **`negativeCapacity_rejects_anchored`.**  `KERNEL-PROVED`.  A negative capacity certificate
for the port system of an actual anchored kernel rejects that kernel. -/
theorem negativeCapacity_rejects_anchored {I : ContactCSP} (hwf : I.WellFormed)
    (hOR : ∀ e ∈ I.Edges, ∀ a b : Bool, I.rel e.1 e.2 a b = (a || b))
    (cert : NegativeCapacityCertificate (portOfContact I)) : ¬ I.Sat := by
  intro hsat
  exact (NegativeCapacityCertificate.not_feasible (portOfContact_wellFormed hwf) cert)
    (feasible_of_sat hOR hsat)

/-- **`level2_rejects_anchored`.**  Level-2 fractional infeasibility of the port system of an
actual anchored kernel rejects that kernel. -/
theorem level2_rejects_anchored {I : ContactCSP} (hwf : I.WellFormed)
    (hOR : ∀ e ∈ I.Edges, ∀ a b : Bool, I.rel e.1 e.2 a b = (a || b))
    (h : ¬ (portOfContact I).Level2FractionalFeasible) : ¬ I.Sat := by
  intro hsat
  exact PortSystem.not_feasible_of_not_level2 (portOfContact_wellFormed hwf) h
    (feasible_of_sat hOR hsat)

/-! ## Bridges to the tracked-prime kernel -/

theorem trackedKernel_contact_isOR (K : TrackedPrimeKernel) :
    ∀ e ∈ K.contact.Edges, ∀ a b : Bool, K.contact.rel e.1 e.2 a b = (a || b) := by
  intro e _ a b; rfl

/-- **`negativeCapacity_rejects_trackedKernel`.**  `KERNEL-PROVED`.  A negative capacity
certificate for the contact relaxation of a tracked-prime kernel rejects the kernel. -/
theorem negativeCapacity_rejects_trackedKernel {K : TrackedPrimeKernel}
    (cert : NegativeCapacityCertificate (portOfContact K.contact)) : ¬ K.Feasible := by
  refine TrackedPrimeKernel.not_feasible_of_contact_unsat ?_
  exact negativeCapacity_rejects_anchored K.contact_wellFormed
    (trackedKernel_contact_isOR K) cert

/-- **`level2_rejects_trackedKernel`.**  Level-2 fractional infeasibility of the contact
relaxation of a tracked-prime kernel rejects the kernel. -/
theorem level2_rejects_trackedKernel {K : TrackedPrimeKernel}
    (h : ¬ (portOfContact K.contact).Level2FractionalFeasible) : ¬ K.Feasible := by
  refine TrackedPrimeKernel.not_feasible_of_contact_unsat ?_
  exact level2_rejects_anchored K.contact_wellFormed (trackedKernel_contact_isOR K) h

/-! ## The new explicit open owners -/

/-- **Open owner.**  Every arising leafless branching kernel of excess at least `2` admits a
negative capacity certificate.  This is *not* inhabited anywhere. -/
def UniformNegativeCapacity (Arises : ContactCSP → Prop) : Prop :=
  ∀ I : ContactCSP, Arises I → Leafless I → 2 ≤ I.excess →
    Nonempty (NegativeCapacityCertificate (portOfContact I))

/-- **Open owner.**  Every arising leafless branching kernel of excess at least `2` is Level-2
fractionally infeasible.  This is *not* inhabited anywhere. -/
def UniformLevel2Rejection (Arises : ContactCSP → Prop) : Prop :=
  ∀ I : ContactCSP, Arises I → Leafless I → 2 ≤ I.excess →
    ¬ (portOfContact I).Level2FractionalFeasible

/-- **`branchingKernelRejection_of_uniformNegativeCapacity`.**  `KERNEL-PROVED`.  The capacity
owner refines the Anchored V1 open owner: uniform negative capacity implies the global
rejection of branching kernels. -/
theorem branchingKernelRejection_of_uniformNegativeCapacity {Arises : ContactCSP → Prop}
    (hwf : ∀ I, Arises I → I.WellFormed)
    (hOR : ∀ I, Arises I → ∀ e ∈ I.Edges, ∀ a b : Bool, I.rel e.1 e.2 a b = (a || b))
    (h : UniformNegativeCapacity Arises) : BranchingKernelRejection Arises := by
  intro I hI hleaf hex
  obtain ⟨cert⟩ := h I hI hleaf hex
  exact negativeCapacity_rejects_anchored (hwf I hI) (hOR I hI) cert

/-- **`branchingKernelRejection_of_uniformLevel2Rejection`.**  The Level-2 owner refines the
Anchored V1 open owner: uniform Level-2 rejection implies the global rejection of branching
kernels. -/
theorem branchingKernelRejection_of_uniformLevel2Rejection {Arises : ContactCSP → Prop}
    (hwf : ∀ I, Arises I → I.WellFormed)
    (hOR : ∀ I, Arises I → ∀ e ∈ I.Edges, ∀ a b : Bool, I.rel e.1 e.2 a b = (a || b))
    (h : UniformLevel2Rejection Arises) : BranchingKernelRejection Arises := by
  intro I hI hleaf hex
  exact level2_rejects_anchored (hwf I hI) (hOR I hI) (h I hI hleaf hex)

end AnchoredV2
end Erdos287
