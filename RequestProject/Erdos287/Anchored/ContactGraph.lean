import RequestProject.Erdos287.Anchored.PrimePowerLayer

/-!
# Local contact relations and the finite contact graph

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Each arithmetic layer exposes a finite set of *contact positions* `J ⊆ C`.  Its allowed
Boolean signatures

`R_p ⊆ {0,1}^J`

are obtained by existentially quantifying all noncontact cofactors and requiring the **full**
anchored prime-power equation — not a leading-digit surrogate.  This file proves

* `layerAllows_iff`: the signature relation is exactly "there is a subset of `C` agreeing
  with the signature on the contact positions and satisfying the full local condition";
* `layerRel_spec`: the Boolean two-contact relation is exact and *computable*, through the
  fingerprint criterion;

and sets up the finite contact-graph constraint system (`ContactCSP`) with its exact decision
procedure `satB` (`sat_iff_satB`).  Everything is finite; no asymptotic notion occurs.
-/

open scoped BigOperators

namespace Erdos287
namespace Anchored

/-! ## A.11  Signatures on the contact positions -/

/-- The contact positions selected by the signature `σ`. -/
def selNodes (contact : Finset ℕ) (σ : ℕ → Bool) : Finset ℕ :=
  contact.filter (fun c => σ c = true)

/-- The contact positions omitted by the signature `σ`. -/
def omitNodes (contact : Finset ℕ) (σ : ℕ → Bool) : Finset ℕ :=
  contact.filter (fun c => σ c = false)

theorem anchor_of_signature {C contact : Finset ℕ} (hsub : contact ⊆ C) (σ : ℕ → Bool) :
    Anchor C (selNodes contact σ) (omitNodes contact σ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (Finset.filter_subset _ _).trans hsub
  · exact (Finset.filter_subset _ _).trans hsub
  · refine Finset.disjoint_left.2 ?_
    intro a ha ha'
    simp only [selNodes, omitNodes, Finset.mem_filter] at ha ha'
    exact absurd (ha.2.symm.trans ha'.2) (by simp)

/-- **The local contact relation.**  A signature `σ` on the contact positions of the layer
`(p, C, contact)` is allowed when the anchored state it pins down is locally feasible. -/
def LayerAllows (p : ℕ) (C contact : Finset ℕ) (σ : ℕ → Bool) : Prop :=
  AnchoredFeasible p C (selNodes contact σ) (omitNodes contact σ)

/-- **`layerAllows_iff`.**  `KERNEL-PROVED`.  The contact relation is exactly the existential
quantification over the noncontact cofactors of the full local prime-power condition. -/
theorem layerAllows_iff (p : ℕ) {C contact : Finset ℕ} (σ : ℕ → Bool) :
    LayerAllows p C contact σ ↔
      ∃ E, E ⊆ C ∧ (∀ c ∈ contact, (c ∈ E ↔ σ c = true)) ∧
        (recipSum E = 0 ∨ 1 ≤ padicValRat p (recipSum E)) := by
  unfold LayerAllows AnchoredFeasible
  constructor
  · rintro ⟨E, hE, h⟩
    rw [mem_allowed] at hE
    refine ⟨E, hE.2.1, ?_, h⟩
    intro c hc
    constructor
    · intro hcE
      by_contra hσ
      have hcN : c ∈ omitNodes contact σ := by
        simp only [omitNodes, Finset.mem_filter]
        exact ⟨hc, by simpa using hσ⟩
      exact (Finset.disjoint_left.1 hE.2.2 hcE) hcN
    · intro hσ
      exact hE.1 (by simp only [selNodes, Finset.mem_filter]; exact ⟨hc, hσ⟩)
  · rintro ⟨E, hEC, hagree, h⟩
    refine ⟨E, mem_allowed.2 ⟨?_, hEC, ?_⟩, h⟩
    · intro c hc
      simp only [selNodes, Finset.mem_filter] at hc
      exact (hagree c hc.1).2 hc.2
    · refine Finset.disjoint_left.2 ?_
      intro c hcE hcN
      simp only [omitNodes, Finset.mem_filter] at hcN
      have := (hagree c hcN.1).1 hcE
      simp [hcN.2] at this

/-! ## A.12  The computable two-contact relation -/

/-- The signature with value `a` at `x` and `b` elsewhere. -/
def sigPair (x : ℕ) (a b : Bool) : ℕ → Bool := fun z => if z = x then a else b

@[simp] theorem sigPair_left (x : ℕ) (a b : Bool) : sigPair x a b x = a := by simp [sigPair]

theorem sigPair_right {x y : ℕ} (h : y ≠ x) (a b : Bool) : sigPair x a b y = b := by
  simp [sigPair, h]

/-- The **Boolean** two-contact relation of a layer, computable through the fingerprint
criterion. -/
def layerRel (p : ℕ) [Fact p.Prime] (C : Finset ℕ) (x : ℕ) (a b : Bool) : Bool :=
  decide (AnchoredFeasible p C (selNodes C (sigPair x a b)) (omitNodes C (sigPair x a b)))

/-- **`layerRel_spec`.**  `KERNEL-PROVED`.  The Boolean relation decides the contact relation
exactly. -/
theorem layerRel_spec (p : ℕ) [Fact p.Prime] (C : Finset ℕ) (x : ℕ) (a b : Bool) :
    layerRel p C x a b = true ↔ LayerAllows p C C (sigPair x a b) := by
  simp [layerRel, LayerAllows]

/-! ## A.13  The finite contact-graph constraint system -/

/-- A finite binary constraint system on contact positions: vertices `V`, unary domains
`dom`, contact edges `Edges` and a Boolean binary relation `rel` for each edge. -/
structure ContactCSP where
  /-- the contact positions -/
  V : Finset ℕ
  /-- the unary domain indicator at each position -/
  dom : ℕ → Bool → Bool
  /-- the contact edges -/
  Edges : Finset (ℕ × ℕ)
  /-- the binary relation carried by each edge -/
  rel : ℕ → ℕ → Bool → Bool → Bool

namespace ContactCSP

/-- A global Boolean assignment satisfies the instance. -/
def Sat (I : ContactCSP) : Prop :=
  ∃ f : ℕ → Bool, (∀ v ∈ I.V, I.dom v (f v) = true) ∧
    ∀ e ∈ I.Edges, I.rel e.1 e.2 (f e.1) (f e.2) = true

/-- Endpoints of every edge are positions of the instance. -/
def WellFormed (I : ContactCSP) : Prop := ∀ e ∈ I.Edges, e.1 ∈ I.V ∧ e.2 ∈ I.V

/-- The exact finite search over the powerset of `V`. -/
def SatSearch (I : ContactCSP) : Prop :=
  ∃ S ∈ I.V.powerset, (∀ v ∈ I.V, I.dom v (decide (v ∈ S)) = true) ∧
    (∀ e ∈ I.Edges, I.rel e.1 e.2 (decide (e.1 ∈ S)) (decide (e.2 ∈ S)) = true)

instance decidableSatSearch (I : ContactCSP) : Decidable I.SatSearch := by
  unfold ContactCSP.SatSearch
  infer_instance

/-- The exact finite decision procedure. -/
def satB (I : ContactCSP) : Bool := decide I.SatSearch

/-- **`sat_iff_satSearch`.**  `KERNEL-PROVED`.  Satisfiability of a finite contact instance
is exactly the finite powerset search. -/
theorem sat_iff_satSearch (I : ContactCSP) (hwf : I.WellFormed) : I.Sat ↔ I.SatSearch := by
  classical
  constructor
  · rintro ⟨f, hdom, hrel⟩
    refine ⟨I.V.filter (fun v => f v = true), Finset.mem_powerset.2 (Finset.filter_subset _ _),
      ?_, ?_⟩
    · have hval : ∀ v ∈ I.V, (decide (v ∈ I.V.filter (fun w => f w = true))) = f v := by
        intro v hv
        by_cases hfv : f v = true <;> simp [Finset.mem_filter, hv, hfv]
      intro v hv
      rw [hval v hv]
      exact hdom v hv
    · have hval : ∀ v ∈ I.V, (decide (v ∈ I.V.filter (fun w => f w = true))) = f v := by
        intro v hv
        by_cases hfv : f v = true <;> simp [Finset.mem_filter, hv, hfv]
      intro e he
      obtain ⟨h1, h2⟩ := hwf e he
      rw [hval e.1 h1, hval e.2 h2]
      exact hrel e he
  · rintro ⟨S, -, hd, hr⟩
    exact ⟨fun v => decide (v ∈ S), hd, hr⟩

/-- **`sat_iff_satB`.**  `KERNEL-PROVED`.  The Boolean procedure `satB` decides
satisfiability exactly. -/
theorem sat_iff_satB (I : ContactCSP) (hwf : I.WellFormed) : I.Sat ↔ I.satB = true := by
  rw [sat_iff_satSearch I hwf, satB, decide_eq_true_iff]

/-- Consequently satisfiability of a well-formed finite contact instance is decidable. -/
def decidableSat (I : ContactCSP) (hwf : I.WellFormed) : Decidable I.Sat :=
  decidable_of_iff _ (I.sat_iff_satSearch hwf).symm

/-- With no contact edges, satisfiability is exactly nonemptiness of every unary domain. -/
theorem sat_iff_domains_nonempty_of_no_edges (I : ContactCSP) (hE : I.Edges = ∅) :
    I.Sat ↔ ∀ v ∈ I.V, ∃ b : Bool, I.dom v b = true := by
  classical
  constructor
  · rintro ⟨f, hdom, -⟩ v hv
    exact ⟨f v, hdom v hv⟩
  · intro h
    refine ⟨fun v => if hv : ∃ b : Bool, I.dom v b = true then hv.choose else false, ?_, ?_⟩
    · intro v hv
      have hex := h v hv
      simp only [dif_pos hex]
      exact hex.choose_spec
    · intro e he
      rw [hE] at he
      exact absurd he (by simp)

end ContactCSP

end Anchored
end Erdos287
