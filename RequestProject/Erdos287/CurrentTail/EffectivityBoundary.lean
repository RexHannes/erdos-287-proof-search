import RequestProject.Erdos287.CurrentTail.TailBoundary

/-!
# Erdős #287 — current tail consolidation: the effectivity firewall

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Five separate layers, never identified:

1. `Tail287Statement` — asymptotic tail `∃ M₀ ∀ A, max A < M₀` (no numeral);
2. `EffectiveOnset M₀` — the same with an **explicit numeral** `M₀`;
3. `FiniteBank B` — a verified finite exclusion `max A < B ⟹ False` (computational bank);
4. `IntermediateRange B M₀` — exclusion of counterexamples with `B ≤ max A < M₀`;
5. `Erdos287Global` — no counterexample at all.

Kernel-proved:

* `global_of_layers` — onset + finite bank + intermediate range ⟹ global;
* `tail_of_effectiveOnset` — an explicit onset gives the asymptotic tail (one direction only);
* `existential_witness_classical` — negative control: a classically provable `∃ n` whose
  witness encodes an arbitrary proposition (an existential onset carries no computable numeral);
* `tail_does_not_give_global` — negative control: an abstract predicate satisfying the tail shape
  but not the global shape, so the finite splice is genuinely needed.

Open optimisation issue (recorded, not formalised): the **dimension-floor obstruction** of the
current tiny-support / huge-first-moment design (`OpenIssue.dimensionFloor`).
-/

open scoped BigOperators
open Finset

namespace Erdos287.CurrentTail

open Erdos287 Erdos287.PostV71V87 Erdos287.PostV87V90R

/-- Effective onset: an explicit numeral `M₀`. -/
def EffectiveOnset (M0 : ℕ) : Prop :=
  ∀ A : Finset ℕ, ∀ hA : Erdos287Counterexample A, A.max' hA.nonempty < M0

/-- Finite bank up to `B`. -/
def FiniteBank (B : ℕ) : Prop :=
  ∀ A : Finset ℕ, ∀ hA : Erdos287Counterexample A, A.max' hA.nonempty < B → False

/-- Intermediate range `[B, M₀)`. -/
def IntermediateRange (B M0 : ℕ) : Prop :=
  ∀ A : Finset ℕ, ∀ hA : Erdos287Counterexample A,
    B ≤ A.max' hA.nonempty → A.max' hA.nonempty < M0 → False

/-- Global Erdős #287 (in counterexample form). -/
def Erdos287Global : Prop := ∀ A : Finset ℕ, ¬ Erdos287Counterexample A

theorem tail_of_effectiveOnset {M0 : ℕ} (h : EffectiveOnset M0) : Tail287Statement :=
  ⟨M0, h⟩

/-- **Global from the three layers** (the splice itself is *not* claimed). -/
theorem global_of_layers {B M0 : ℕ} (hon : EffectiveOnset M0) (hbank : FiniteBank B)
    (hmid : IntermediateRange B M0) : Erdos287Global := by
  intro A hA
  rcases lt_or_ge (A.max' hA.nonempty) B with h | h
  · exact hbank A hA h
  · exact hmid A hA h (hon A hA)

/-- Negative control: classical existence of a witness that encodes an arbitrary proposition. -/
theorem existential_witness_classical (P : Prop) :
    ∃ n : ℕ, (P → n = 0) ∧ (¬ P → n = 1) := by
  by_cases hP : P
  · exact ⟨0, fun _ => rfl, fun h => absurd hP h⟩
  · exact ⟨1, fun h => absurd h hP, fun _ => rfl⟩

/-- Negative control: the tail shape does not imply the global shape. -/
theorem tail_does_not_give_global :
    ∃ P : Finset ℕ → Prop, (∃ M0 : ℕ, ∀ A, P A → A.sum id < M0) ∧ ¬ (∀ A, ¬ P A) := by
  refine ⟨fun A => A = {1}, ⟨2, fun A hA => by subst hA; decide⟩, fun h => h {1} rfl⟩

/-- Recorded open optimisation issues. -/
inductive OpenIssue
  | dimensionFloor
  | effectiveOnsetComputation
  | finiteSplice
  deriving DecidableEq, Repr

/-- Descriptions of the open issues. -/
def OpenIssue.description : OpenIssue → String
  | .dimensionFloor =>
      "Known dimension-floor obstruction of the current tiny-support / huge-first-moment " ++
      "design (first moment mu = 999999 over seven blocks), as recorded by the programme; " ++
      "open optimisation issue, not analysed in Lean."
  | .effectiveOnsetComputation =>
      "No computable numerical onset is extracted from the existential tail."
  | .finiteSplice =>
      "The finite bank does not reach any onset; the splice is not routine and is open."

end Erdos287.CurrentTail
