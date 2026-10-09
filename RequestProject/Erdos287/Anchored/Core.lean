import RequestProject.Erdos287.Direct.Core

/-!
# Erdős #287 — Anchored / contact-graph route, core conventions

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This namespace (`Erdos287.Anchored`) is a *new, append-only, proof-side* development.  It is
deliberately kept disjoint from

* **Route S** — the Source / FivePrime / Directed-Selberg / physical-`k = 1` programme, and
* **Route D** — the Direct Reciprocal programme of `Erdos287.Direct`,

and it must not be conflated with either.  No node of this route discharges a node of another
route unless an explicit bridge theorem is proved; see `Anchored/Reconciliation.lean`.

This file fixes the exact finite conventions of the anchored route:

* the reciprocal sum of a finite set of cofactors (reusing `Erdos287.Direct.recipSum`, so
  that the two routes speak about literally the same rational number);
* the ambient lcm `lcmOf C` of a finite cofactor set, its positivity and divisibility;
* the *integral* cofactor numerator `cofactorNum C E = ∑_{c ∈ E} lcmOf C / c`;
* the exact identity `recipSum E = cofactorNum C E / lcmOf C`.

Everything is finite and exact: sums are rational, no real number and no asymptotic notion
occurs anywhere in this namespace.
-/

open scoped BigOperators

namespace Erdos287
namespace Anchored

/-- The reciprocal sum of a finite set of cofactors.  This is *literally* the Route-D
reciprocal sum, reused so that no second convention is introduced. -/
abbrev recipSum (A : Finset ℕ) : ℚ := Erdos287.Direct.recipSum A

theorem recipSum_def (A : Finset ℕ) : recipSum A = ∑ n ∈ A, (1 : ℚ) / n := rfl

@[simp] theorem recipSum_empty : recipSum ∅ = 0 := Erdos287.Direct.recipSum_empty

/-- Reciprocal sums are never negative (the convention `1 / (0 : ℚ) = 0` is harmless here). -/
theorem recipSum_nonneg (A : Finset ℕ) : 0 ≤ recipSum A := by
  refine Finset.sum_nonneg ?_
  intro n _
  positivity

/-- On a set of positive cofactors a nonempty subset has a strictly positive reciprocal sum. -/
theorem recipSum_pos {A : Finset ℕ} (hne : A.Nonempty) (hpos : ∀ c ∈ A, 0 < c) :
    0 < recipSum A := by
  obtain ⟨a, ha⟩ := hne
  have hlt : (0 : ℚ) < 1 / (a : ℚ) := by
    have : (0 : ℚ) < (a : ℚ) := by exact_mod_cast hpos a ha
    positivity
  refine lt_of_lt_of_le hlt ?_
  refine Finset.single_le_sum (f := fun n : ℕ => (1 : ℚ) / n) ?_ ha
  intro n _
  positivity

/-! ## A.2  The ambient lcm of a finite cofactor set -/

/-- The ambient lcm of a finite set of cofactors. -/
def lcmOf (C : Finset ℕ) : ℕ := C.lcm id

@[simp] theorem lcmOf_empty : lcmOf ∅ = 1 := by simp [lcmOf]

theorem dvd_lcmOf {C : Finset ℕ} {c : ℕ} (hc : c ∈ C) : c ∣ lcmOf C :=
  Finset.dvd_lcm (f := id) hc

/-- The ambient lcm of a set of positive cofactors is positive. -/
theorem lcmOf_pos {C : Finset ℕ} (hpos : ∀ c ∈ C, 0 < c) : 0 < lcmOf C := by
  classical
  induction C using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have h1 : 0 < a := hpos a (Finset.mem_insert_self a s)
      have h2 : 0 < s.lcm id := ih (fun c hc => hpos c (Finset.mem_insert_of_mem hc))
      have hne : Nat.lcm a (s.lcm id) ≠ 0 := Nat.lcm_ne_zero h1.ne' h2.ne'
      have : lcmOf (insert a s) = Nat.lcm a (s.lcm id) := by
        simp [lcmOf, Finset.lcm_insert, lcm]
      rw [this]
      exact Nat.pos_of_ne_zero hne

/-! ## A.3  The integral cofactor numerator -/

/-- The integral numerator of the reciprocal sum of `E` over the ambient lcm of `C`:
`cofactorNum C E = ∑_{c ∈ E} lcmOf C / c`, a natural number whenever `E ⊆ C`. -/
def cofactorNum (C E : Finset ℕ) : ℕ := ∑ c ∈ E, lcmOf C / c

@[simp] theorem cofactorNum_empty (C : Finset ℕ) : cofactorNum C ∅ = 0 := by
  simp [cofactorNum]

/-- **The exact compiler identity.**  For `E ⊆ C` with all cofactors positive,
`recipSum E = cofactorNum C E / lcmOf C` in `ℚ`. -/
theorem recipSum_eq_cofactorNum_div {C E : Finset ℕ} (hEC : E ⊆ C)
    (hpos : ∀ c ∈ C, 0 < c) :
    recipSum E = ((cofactorNum C E : ℕ) : ℚ) / ((lcmOf C : ℕ) : ℚ) := by
  have hL : 0 < lcmOf C := lcmOf_pos hpos
  have hL' : ((lcmOf C : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast hL.ne'
  rw [eq_div_iff hL', cofactorNum]
  push_cast
  rw [recipSum_def, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro c hc
  have hcC : c ∈ C := hEC hc
  have hc0 : (c : ℚ) ≠ 0 := by
    have := hpos c hcC
    exact_mod_cast this.ne'
  have hcast : ((lcmOf C / c : ℕ) : ℚ) = ((lcmOf C : ℕ) : ℚ) / (c : ℚ) :=
    Nat.cast_div (dvd_lcmOf hcC) hc0
  rw [hcast]
  field_simp

/-- On positive cofactors, a nonempty `E ⊆ C` has a nonzero integral numerator. -/
theorem cofactorNum_ne_zero {C E : Finset ℕ} (hEC : E ⊆ C) (hpos : ∀ c ∈ C, 0 < c)
    (hne : E.Nonempty) : cofactorNum C E ≠ 0 := by
  have hL : 0 < lcmOf C := lcmOf_pos hpos
  obtain ⟨a, ha⟩ := hne
  have haC : a ∈ C := hEC ha
  have hdvd : a ∣ lcmOf C := dvd_lcmOf haC
  have hpa : 0 < a := hpos a haC
  have : 0 < lcmOf C / a := Nat.div_pos (Nat.le_of_dvd hL hdvd) hpa
  have hle : lcmOf C / a ≤ cofactorNum C E :=
    Finset.single_le_sum (f := fun c : ℕ => lcmOf C / c) (fun _ _ => Nat.zero_le _) ha
  omega

end Anchored
end Erdos287
