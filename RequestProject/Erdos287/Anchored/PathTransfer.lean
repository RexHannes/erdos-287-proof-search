import RequestProject.Erdos287.Anchored.ContactGraph

/-!
# Exact transfer along a contact path

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A *contact path* is a repetition-free list of contact positions `x :: l`, carrying the unary
domains `dom` and the binary contact relations `rel` of the contact graph.  This file defines
the exact Boolean transfer `transfer dom rel x l a b` (composition of the local relations
along the path) and proves

* `transfer_spec`: `transfer … a b = true` iff there is a global assignment with the two
  prescribed endpoint values satisfying every local condition along the path;
* `pathCSP_sat_iff`: satisfiability of the path instance is exactly
  `∃ a b, transfer … a b = true`, a check over four Boolean pairs.

Everything is exact and finite; no approximation of any kind is used.
-/

open scoped BigOperators

namespace Erdos287
namespace Anchored

/-- The last vertex of the path `x :: l`. -/
def lastOf : ℕ → List ℕ → ℕ
  | x, [] => x
  | _, (y :: t) => lastOf y t

theorem lastOf_mem (x : ℕ) (l : List ℕ) : lastOf x l ∈ x :: l := by
  induction l generalizing x with
  | nil => simp [lastOf]
  | cons y t ih =>
      have := ih y
      simp [lastOf] at *
      tauto

/-- The assignment `f` satisfies every local condition along the path `x :: l`. -/
def chainOk (dom : ℕ → Bool → Bool) (rel : ℕ → ℕ → Bool → Bool → Bool) :
    ℕ → List ℕ → (ℕ → Bool) → Prop
  | x, [], f => dom x (f x) = true
  | x, (y :: t), f => dom x (f x) = true ∧ rel x y (f x) (f y) = true ∧ chainOk dom rel y t f

/-- The exact Boolean transfer along the path `x :: l`. -/
def transfer (dom : ℕ → Bool → Bool) (rel : ℕ → ℕ → Bool → Bool → Bool) :
    ℕ → List ℕ → Bool → Bool → Bool
  | x, [], a, b => dom x a && (a == b)
  | x, (y :: t), a, b =>
      dom x a && ((rel x y a false && transfer dom rel y t false b) ||
        (rel x y a true && transfer dom rel y t true b))

variable (dom : ℕ → Bool → Bool) (rel : ℕ → ℕ → Bool → Bool → Bool)

theorem chainOk_congr {f g : ℕ → Bool} (x : ℕ) (l : List ℕ)
    (h : ∀ z ∈ x :: l, f z = g z) : chainOk dom rel x l f ↔ chainOk dom rel x l g := by
  induction l generalizing x with
  | nil => simp [chainOk, h x (by simp)]
  | cons y t ih =>
      have hx : f x = g x := h x (by simp)
      have hy : f y = g y := h y (by simp)
      have ht : ∀ z ∈ y :: t, f z = g z := by
        intro z hz
        exact h z (by simp at hz ⊢; tauto)
      simp [chainOk, hx, hy, ih y ht]

/-- Local path conditions, unpacked as vertex conditions and edge conditions. -/
theorem chainOk_iff (x : ℕ) (l : List ℕ) (f : ℕ → Bool) :
    chainOk dom rel x l f ↔
      ((∀ v ∈ x :: l, dom v (f v) = true) ∧
        (∀ e ∈ (x :: l).zip l, rel e.1 e.2 (f e.1) (f e.2) = true)) := by
  induction l generalizing x with
  | nil => simp [chainOk]
  | cons y t ih =>
      simp only [chainOk, ih y, List.zip_cons_cons, List.mem_cons]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨?_, ?_⟩
        · rintro v (rfl | hv)
          · exact h1
          · exact h3 v hv
        · rintro e (rfl | he)
          · exact h2
          · exact h4 e he
      · rintro ⟨h1, h2⟩
        exact ⟨h1 x (Or.inl rfl), h2 (x, y) (Or.inl rfl),
          fun v hv => h1 v (Or.inr hv), fun e he => h2 e (Or.inr he)⟩

/-- **`transfer_spec`.**  `KERNEL-PROVED`.  The Boolean transfer is exactly the existence of a
path assignment with the prescribed endpoint values. -/
theorem transfer_spec (x : ℕ) (l : List ℕ) (hnd : (x :: l).Nodup) (a b : Bool) :
    transfer dom rel x l a b = true ↔
      ∃ f : ℕ → Bool, f x = a ∧ f (lastOf x l) = b ∧ chainOk dom rel x l f := by
  induction l generalizing x a with
  | nil =>
      simp only [transfer, lastOf, Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨hd, hab⟩
        exact ⟨fun _ => a, rfl, hab ▸ rfl, by simpa [chainOk] using hd⟩
      · rintro ⟨f, hfx, hfb, hok⟩
        refine ⟨by rw [← hfx]; simpa [chainOk] using hok, by rw [← hfx, hfb]⟩
  | cons y t ih =>
      have hxnotin : x ∉ y :: t := by
        simpa using (List.nodup_cons.1 hnd).1
      have hndt : (y :: t).Nodup := (List.nodup_cons.1 hnd).2
      simp only [transfer, lastOf, Bool.and_eq_true, Bool.or_eq_true]
      constructor
      · rintro ⟨hd, hc⟩
        have hex : ∃ c : Bool, rel x y a c = true ∧ transfer dom rel y t c b = true := by
          rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨false, h1, h2⟩
          · exact ⟨true, h1, h2⟩
        obtain ⟨c, hrel, htr⟩ := hex
        obtain ⟨g, hgy, hgb, hgok⟩ := (ih y hndt c).1 htr
        refine ⟨Function.update g x a, by simp, ?_, ?_⟩
        · have hne : lastOf y t ≠ x := by
            intro h
            exact hxnotin (h ▸ lastOf_mem y t)
          simpa [Function.update_of_ne hne] using hgb
        · have hupd : ∀ z ∈ y :: t, Function.update g x a z = g z := by
            intro z hz
            have : z ≠ x := by rintro rfl; exact hxnotin hz
            simp [Function.update_of_ne this]
          refine ⟨by simpa using hd, ?_, ?_⟩
          · have h1 : Function.update g x a y = g y := hupd y (by simp)
            simp [h1, hgy, hrel]
          · exact (chainOk_congr dom rel y t (fun z hz => (hupd z hz).symm)).1 hgok
      · rintro ⟨f, hfx, hfb, hok⟩
        obtain ⟨hd, hrel, hrest⟩ := hok
        have htr : transfer dom rel y t (f y) b = true :=
          (ih y hndt (f y)).2 ⟨f, rfl, hfb, hrest⟩
        refine ⟨by rw [← hfx]; exact hd, ?_⟩
        rcases hfy : f y with _ | _
        · rw [hfy] at hrel htr
          exact Or.inl ⟨by rw [← hfx]; exact hrel, htr⟩
        · rw [hfy] at hrel htr
          exact Or.inr ⟨by rw [← hfx]; exact hrel, htr⟩

/-! ## A.15  The path instance of the contact graph -/

/-- The contact instance carried by the path `x :: l`. -/
def pathCSP (dom : ℕ → Bool → Bool) (rel : ℕ → ℕ → Bool → Bool → Bool)
    (x : ℕ) (l : List ℕ) : ContactCSP :=
  { V := (x :: l).toFinset
    dom := dom
    Edges := ((x :: l).zip l).toFinset
    rel := rel }

theorem pathCSP_wellFormed (x : ℕ) (l : List ℕ) : (pathCSP dom rel x l).WellFormed := by
  intro e he
  simp only [pathCSP, List.mem_toFinset] at he ⊢
  have hz := List.of_mem_zip he
  exact ⟨hz.1, List.mem_cons_of_mem _ hz.2⟩

/-- **`pathCSP_sat_iff`.**  `KERNEL-PROVED`.  A contact path component is satisfiable exactly
when the composed transfer admits a pair of endpoint values — a check over four Boolean
pairs, hence exactly decidable. -/
theorem pathCSP_sat_iff (x : ℕ) (l : List ℕ) (hnd : (x :: l).Nodup) :
    (pathCSP dom rel x l).Sat ↔ ∃ a b : Bool, transfer dom rel x l a b = true := by
  constructor
  · rintro ⟨f, hdom, hrel⟩
    have hok : chainOk dom rel x l f := by
      refine (chainOk_iff dom rel x l f).2 ⟨?_, ?_⟩
      · intro v hv
        exact hdom v (by simpa [pathCSP, List.mem_toFinset] using hv)
      · intro e he
        exact hrel e (by simpa [pathCSP, List.mem_toFinset] using he)
    exact ⟨f x, f (lastOf x l), (transfer_spec dom rel x l hnd _ _).2 ⟨f, rfl, rfl, hok⟩⟩
  · rintro ⟨a, b, htr⟩
    obtain ⟨f, -, -, hok⟩ := (transfer_spec dom rel x l hnd a b).1 htr
    obtain ⟨h1, h2⟩ := (chainOk_iff dom rel x l f).1 hok
    refine ⟨f, ?_, ?_⟩
    · intro v hv
      exact h1 v (by simpa [pathCSP, List.mem_toFinset] using hv)
    · intro e he
      exact h2 e (by simpa [pathCSP, List.mem_toFinset] using he)

end Anchored
end Erdos287
