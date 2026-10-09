import RequestProject.Erdos287.AnchoredV2.BlockCut
import RequestProject.Erdos287.Anchored.PathTransfer

/-!
# Anchored V2 — the cactus / block-cut message solver

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A certified cactus decomposition is supplied as data: a list of child blocks meeting pairwise
only in one articulation position `a`, each carrying the ambient local relations.  A bridge
child sends the one-contact message `MsgAt`, a cycle child sends the two-contact relation
`Msg2At`; because contact positions *are* the Boolean variables, two contacts referring to the
same physical cofactor are literally the same variable.

At the articulation, all incoming child relations, all pins and all local OR clauses are
combined and intersected with the full local arithmetic relation carried by the child's own
unary domains; the resulting decision is **exact in both directions**
(`cactus_star_sat_iff`).
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV2

open Erdos287.Anchored
open Erdos287.Anchored.ContactCSP

/-- The union of a certified list of child blocks, carrying the ambient contact relations. -/
def unionCSP (rel : ℕ → ℕ → Bool → Bool → Bool) (Cs : List ContactCSP) : ContactCSP where
  V := (Cs.map ContactCSP.V).foldr (· ∪ ·) ∅
  dom := fun v b => Cs.all (fun J => J.dom v b)
  Edges := (Cs.map ContactCSP.Edges).foldr (· ∪ ·) ∅
  rel := rel

theorem mem_unionCSP_V (rel : ℕ → ℕ → Bool → Bool → Bool) (Cs : List ContactCSP) (v : ℕ) :
    v ∈ (unionCSP rel Cs).V ↔ ∃ J ∈ Cs, v ∈ J.V := by
  induction Cs with
  | nil => simp [unionCSP]
  | cons J t ih =>
      have ih' : v ∈ (List.map ContactCSP.V t).foldr (· ∪ ·) ∅ ↔ ∃ J ∈ t, v ∈ J.V := ih
      simp only [unionCSP, List.map_cons, List.foldr_cons, Finset.mem_union, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact ⟨J, Or.inl rfl, h⟩
        · obtain ⟨J', hJ', hv⟩ := ih'.1 h
          exact ⟨J', Or.inr hJ', hv⟩
      · rintro ⟨J', (rfl | hJ'), hv⟩
        · exact Or.inl hv
        · exact Or.inr (ih'.2 ⟨J', hJ', hv⟩)

theorem mem_unionCSP_Edges (rel : ℕ → ℕ → Bool → Bool → Bool) (Cs : List ContactCSP)
    (e : ℕ × ℕ) : e ∈ (unionCSP rel Cs).Edges ↔ ∃ J ∈ Cs, e ∈ J.Edges := by
  induction Cs with
  | nil => simp [unionCSP]
  | cons J t ih =>
      have ih' : e ∈ (List.map ContactCSP.Edges t).foldr (· ∪ ·) ∅ ↔ ∃ J ∈ t, e ∈ J.Edges := ih
      simp only [unionCSP, List.map_cons, List.foldr_cons, Finset.mem_union, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact ⟨J, Or.inl rfl, h⟩
        · obtain ⟨J', hJ', hv⟩ := ih'.1 h
          exact ⟨J', Or.inr hJ', hv⟩
      · rintro ⟨J', (rfl | hJ'), hv⟩
        · exact Or.inl hv
        · exact Or.inr (ih'.2 ⟨J', hJ', hv⟩)

/-- The certified data of a cactus decomposition at one articulation position `a`. -/
structure CactusData (rel : ℕ → ℕ → Bool → Bool → Bool) (Cs : List ContactCSP) (a : ℕ) :
    Prop where
  /-- each child carries the ambient local relations -/
  rel_eq : ∀ J ∈ Cs, ∀ e ∈ J.Edges, ∀ x y, J.rel e.1 e.2 x y = rel e.1 e.2 x y
  /-- each child's contact edges stay inside it -/
  edges_in : ∀ J ∈ Cs, ∀ e ∈ J.Edges, e.1 ∈ J.V ∧ e.2 ∈ J.V
  /-- each child's unary domain is vacuous outside it -/
  dom_out : ∀ J ∈ Cs, ∀ v, v ∉ J.V → ∀ b, J.dom v b = true
  /-- distinct children meet only in the articulation position -/
  meet : Cs.Pairwise (fun J J' => ∀ v, v ∈ J.V → v ∈ J'.V → v = a)

/-- **`cactus_star_sat_iff`.**  `KERNEL-PROVED`.  The exact cactus decision at one articulation
position: the glued instance is satisfiable exactly when all children admit a common Boolean
value at the articulation. -/
theorem cactus_star_sat_iff {rel : ℕ → ℕ → Bool → Bool → Bool} {Cs : List ContactCSP} {a : ℕ}
    (h : CactusData rel Cs a) :
    (unionCSP rel Cs).Sat ↔ ∃ x : Bool, ∀ J ∈ Cs, MsgAt J a x := by
  classical
  constructor
  · rintro ⟨f, hdom, hrel⟩
    refine ⟨f a, ?_⟩
    intro J hJ
    refine ⟨f, rfl, ?_, ?_⟩
    · intro v hv
      have hvu : v ∈ (unionCSP rel Cs).V := (mem_unionCSP_V rel Cs v).2 ⟨J, hJ, hv⟩
      have hd := hdom v hvu
      simp only [unionCSP, List.all_eq_true] at hd
      exact hd J hJ
    · intro e he
      have heu : e ∈ (unionCSP rel Cs).Edges := (mem_unionCSP_Edges rel Cs e).2 ⟨J, hJ, he⟩
      have hr := hrel e heu
      rw [h.rel_eq J hJ e he]
      exact hr
  · rintro ⟨x, hx⟩
    choose F hFa hFdom hFrel using hx
    set G : ContactCSP → (ℕ → Bool) :=
      fun J => if hJ : J ∈ Cs then F J hJ else fun _ => x with hG
    have hGa : ∀ J ∈ Cs, G J a = x := by
      intro J hJ
      simp only [hG, dif_pos hJ]
      exact hFa J hJ
    have hGdom : ∀ J ∈ Cs, ∀ v ∈ J.V, J.dom v (G J v) = true := by
      intro J hJ v hv
      simp only [hG, dif_pos hJ]
      exact hFdom J hJ v hv
    have hGrel : ∀ J ∈ Cs, ∀ e ∈ J.Edges, J.rel e.1 e.2 (G J e.1) (G J e.2) = true := by
      intro J hJ e he
      simp only [hG, dif_pos hJ]
      exact hFrel J hJ e he
    set f : ℕ → Bool :=
      fun v => match Cs.find? (fun J => decide (v ∈ J.V)) with
        | some J => G J v
        | none => x with hf
    have hsymm : Symmetric (fun J J' : ContactCSP => ∀ v, v ∈ J.V → v ∈ J'.V → v = a) := by
      intro J J' hJJ' v hv1 hv2
      exact hJJ' v hv2 hv1
    have hkey : ∀ J ∈ Cs, ∀ v ∈ J.V, f v = G J v := by
      intro J hJ v hv
      have hfind : ∃ J₀, Cs.find? (fun J' => decide (v ∈ J'.V)) = some J₀ := by
        rcases hfo : Cs.find? (fun J' => decide (v ∈ J'.V)) with _ | J₀
        · exfalso
          have := List.find?_eq_none.1 hfo J hJ
          simp [hv] at this
        · exact ⟨J₀, hfo⟩
      obtain ⟨J₀, hJ₀⟩ := hfind
      have hJ₀mem : J₀ ∈ Cs := List.mem_of_find?_eq_some hJ₀
      have hJ₀v : v ∈ J₀.V := by
        have := List.find?_some hJ₀
        simpa using this
      simp only [hf, hJ₀]
      by_cases heq : J₀ = J
      · rw [heq]
      · have hva : v = a := by
          have := List.Pairwise.forall hsymm h.meet hJ₀mem hJ heq
          exact this v hJ₀v hv
        rw [hva, hGa J₀ hJ₀mem, hGa J hJ]
    refine ⟨f, ?_, ?_⟩
    · intro v hv
      simp only [unionCSP, List.all_eq_true]
      intro J hJ
      by_cases hvJ : v ∈ J.V
      · rw [hkey J hJ v hvJ]
        exact hGdom J hJ v hvJ
      · exact h.dom_out J hJ v hvJ _
    · intro e he
      obtain ⟨J, hJ, heJ⟩ := (mem_unionCSP_Edges rel Cs e).1 he
      have h1 : e.1 ∈ J.V := (h.edges_in J hJ e heJ).1
      have h2 : e.2 ∈ J.V := (h.edges_in J hJ e heJ).2
      show rel e.1 e.2 (f e.1) (f e.2) = true
      rw [hkey J hJ _ h1, hkey J hJ _ h2, ← h.rel_eq J hJ e heJ]
      exact hGrel J hJ e heJ

/-- **`msg2_pathChild`.**  `KERNEL-PROVED`.  The two-contact message of a path child is exactly
the anchored V1 transfer between its endpoints. -/
theorem msg2_pathChild (dom : ℕ → Bool → Bool) (rel : ℕ → ℕ → Bool → Bool → Bool)
    (x : ℕ) (l : List ℕ) (hnd : (x :: l).Nodup) (u v : Bool) :
    Msg2At (pathCSP dom rel x l) x (lastOf x l) u v ↔ transfer dom rel x l u v = true := by
  rw [transfer_spec dom rel x l hnd u v]
  constructor
  · rintro ⟨f, hfx, hfl, hd, hr⟩
    refine ⟨f, hfx, hfl, (chainOk_iff dom rel x l f).2 ⟨?_, ?_⟩⟩
    · intro w hw
      exact hd w (by simpa [pathCSP, List.mem_toFinset] using hw)
    · intro e he
      exact hr e (by simpa [pathCSP, List.mem_toFinset] using he)
  · rintro ⟨f, hfx, hfl, hok⟩
    obtain ⟨h1, h2⟩ := (chainOk_iff dom rel x l f).1 hok
    refine ⟨f, hfx, hfl, ?_, ?_⟩
    · intro w hw
      exact h1 w (by simpa [pathCSP, List.mem_toFinset] using hw)
    · intro e he
      exact h2 e (by simpa [pathCSP, List.mem_toFinset] using he)

end AnchoredV2
end Erdos287
