import RequestProject.Erdos287.Anchored.CycleRank

/-!
# Anchored V2 — the tracked-prime kernel

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A `TrackedPrimeKernel` is the finite exact record of everything a partially completed anchored
search retains:

* the retained physical Boolean positions;
* shared-position equalities (two physical positions carrying the same cofactor);
* endpoint pins (positions permanently selected) and forced zeros;
* the no-`00` adjacency pairs (every adjacent pair must contain a selected position);
* inherited high-power equations, given as exact Boolean side conditions;
* one exact truncated prime-power equation per tracked prime.

`TrackedKernelFeasible` is the (finite, exact) existence of a Boolean word satisfying all of
these.  The only structural theorem proved here is **monotonicity in the tracked-prime set**:
a kernel that tracks more primes and carries more constraints is harder to satisfy.  No
cardinality or asymptotic claim is made.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV2

/-- The finite exact tracked-prime kernel record. -/
structure TrackedPrimeKernel where
  /-- retained physical Boolean positions -/
  positions : Finset ℕ
  /-- shared-position equalities -/
  shared : Finset (ℕ × ℕ)
  /-- endpoint pins: positions permanently selected -/
  pins : Finset ℕ
  /-- forced zeros: positions permanently omitted -/
  zeros : Finset ℕ
  /-- no-`00` adjacency pairs -/
  adjacency : Finset (ℕ × ℕ)
  /-- inherited high-power equations, as exact Boolean side conditions -/
  highPower : Finset ((ℕ → Bool) → Bool)
  /-- the tracked primes -/
  tracked : Finset ℕ
  /-- one exact truncated prime-power equation per tracked prime -/
  layerEq : ℕ → (ℕ → Bool) → Bool

namespace TrackedPrimeKernel

/-- A Boolean word satisfies the kernel. -/
def Satisfies (K : TrackedPrimeKernel) (w : ℕ → Bool) : Prop :=
  (∀ e ∈ K.shared, w e.1 = w e.2) ∧
  (∀ x ∈ K.pins, w x = true) ∧
  (∀ x ∈ K.zeros, w x = false) ∧
  (∀ e ∈ K.adjacency, (w e.1 || w e.2) = true) ∧
  (∀ g ∈ K.highPower, g w = true) ∧
  (∀ p ∈ K.tracked, K.layerEq p w = true)

/-- **Tracked kernel feasibility**: some Boolean word satisfies every retained constraint. -/
def Feasible (K : TrackedPrimeKernel) : Prop := ∃ w : ℕ → Bool, K.Satisfies w

/-- `K'` refines `K`: it tracks at least the same primes with literally the same truncated
prime-power equations, and carries at least all of `K`'s other constraints. -/
structure Refines (K' K : TrackedPrimeKernel) : Prop where
  /-- the shared-position equalities are inherited -/
  shared : K.shared ⊆ K'.shared
  /-- the pins are inherited -/
  pins : K.pins ⊆ K'.pins
  /-- the forced zeros are inherited -/
  zeros : K.zeros ⊆ K'.zeros
  /-- the no-`00` adjacency constraints are inherited -/
  adjacency : K.adjacency ⊆ K'.adjacency
  /-- the inherited high-power equations are inherited -/
  highPower : K.highPower ⊆ K'.highPower
  /-- the tracked-prime set only grows -/
  tracked : K.tracked ⊆ K'.tracked
  /-- on the old tracked primes the truncated prime-power equation is literally the same -/
  layerEq : ∀ p ∈ K.tracked, K'.layerEq p = K.layerEq p

/-- **`feasible_of_refines`.**  `KERNEL-PROVED`.  Monotonicity of tracked kernel feasibility:
if `K'` tracks the primes of `K` with the same equations and all of `K`'s other constraints,
then feasibility of `K'` implies feasibility of `K`. -/
theorem feasible_of_refines {K' K : TrackedPrimeKernel} (h : Refines K' K) (hK' : K'.Feasible) :
    K.Feasible := by
  obtain ⟨w, hshared, hpins, hzeros, hadj, hhigh, hlayer⟩ := hK'
  refine ⟨w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun e he => hshared e (h.shared he)
  · exact fun x hx => hpins x (h.pins hx)
  · exact fun x hx => hzeros x (h.zeros hx)
  · exact fun e he => hadj e (h.adjacency he)
  · exact fun g hg => hhigh g (h.highPower hg)
  · intro p hp
    have := hlayer p (h.tracked hp)
    rwa [h.layerEq p hp] at this

/-- The kernel is *localised*: all of its pins, forced zeros, shared-position equalities and
no-`00` adjacency constraints only mention retained positions. -/
def Localised (K : TrackedPrimeKernel) : Prop :=
  (∀ x ∈ K.pins, x ∈ K.positions) ∧ (∀ x ∈ K.zeros, x ∈ K.positions) ∧
    (∀ e ∈ K.shared, e.1 ∈ K.positions ∧ e.2 ∈ K.positions) ∧
    (∀ e ∈ K.adjacency, e.1 ∈ K.positions ∧ e.2 ∈ K.positions)

/-- The anchored contact instance carried by the no-`00` adjacency constraints of a tracked
kernel: positions are contact positions, adjacency pairs are contact (OR) edges, and the unary
domain records the pins and the forced zeros. -/
def contact (K : TrackedPrimeKernel) : Erdos287.Anchored.ContactCSP :=
  { V := K.positions
    dom := fun v b => (!decide (v ∈ K.pins) || b) && (!decide (v ∈ K.zeros) || !b)
    Edges := K.adjacency.filter (fun e => e.1 ∈ K.positions ∧ e.2 ∈ K.positions)
    rel := fun _ _ a b => a || b }

theorem contact_wellFormed (K : TrackedPrimeKernel) : K.contact.WellFormed := by
  intro e he
  simp only [contact, Finset.mem_filter] at he
  exact ⟨he.2.1, he.2.2⟩

/-- **`contact_sat_of_feasible`.**  `KERNEL-PROVED`.  The contact relaxation is sound: a
feasible tracked kernel yields a satisfying assignment of its contact instance. -/
theorem contact_sat_of_feasible {K : TrackedPrimeKernel} (h : K.Feasible) : K.contact.Sat := by
  obtain ⟨w, -, hpins, hzeros, hadj, -, -⟩ := h
  refine ⟨w, ?_, ?_⟩
  · intro v hv
    simp only [contact, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not]
    constructor
    · by_cases hp : v ∈ K.pins
      · exact Or.inr (hpins v hp)
      · exact Or.inl (by simpa using hp)
    · by_cases hz : v ∈ K.zeros
      · exact Or.inr (by simp [hzeros v hz])
      · exact Or.inl (by simpa using hz)
  · intro e he
    simp only [contact, Finset.mem_filter] at he
    exact hadj e he.1

/-- **`not_feasible_of_contact_unsat`.**  `KERNEL-PROVED`.  Any rejection of the contact
relaxation rejects the tracked kernel itself. -/
theorem not_feasible_of_contact_unsat {K : TrackedPrimeKernel} (h : ¬ K.contact.Sat) :
    ¬ K.Feasible := fun hf => h (contact_sat_of_feasible hf)

end TrackedPrimeKernel

end AnchoredV2
end Erdos287
