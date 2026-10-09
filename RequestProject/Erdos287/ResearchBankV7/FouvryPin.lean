import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V7: Fouvry-pin localization at its true evidence level

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The Fouvry lane rests on analytic ingredients that are **not** formalized in this project.  They
are recorded here as explicit, *uninhabited* external interfaces:

* `FouvryShiftedPrimeInput` (Fouvry / Luca–Young shifted-prime divisor input);
* `SelbergUpperBoundSieve`;
* `BrunTitchmarsh`;
* `PrimeCountingEstimate`.

Everything derived from them is stated as an implication with the external premise visible
(`CONDITIONAL-BANKED`), and the finite/arithmetic consequences are kernel-proved:

* `pin_capture_conditional` — the pin-capture inequality
  `Φ(𝓡) ≤ c·M·log(2H)/(log M)² + W(𝓡)/log(2H)`;
* `sublinear_support_cannot_capture_positive_proportion` — a sublinear-support residual family
  cannot contain a positive proportion of the pin population;
* `branch_budget_pin_localization` — the pin bound under the bounded-absorption branch budget.

Interpretation banked: Fouvry bulk is **no longer a separate completion owner** on a surviving
terminal leaf.  Firewall: none of this infers that a surviving terminal leaf exists
(`fouvry_bound_does_not_give_terminal_leaf`).
-/

namespace Erdos287
namespace ResearchBankV7
namespace FouvryPin

open Finset

/-! ## 1.  External analytic interfaces (uninhabited here) -/

/-- **EXTERNAL (uninhabited here).**  The Fouvry / Luca–Young shifted-prime input: for a positive
proportion of primes `p ≤ x`, the shifted prime `p − 1` has a divisor in a prescribed dyadic
range.  Not formalized in this project. -/
def FouvryShiftedPrimeInput : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℕ, 100 ≤ x → ∃ P : Finset ℕ,
    (∀ p ∈ P, p.Prime ∧ p ≤ x) ∧ δ * (x / Real.log x) ≤ (P.card : ℝ)

/-- **EXTERNAL (uninhabited here).**  A Selberg upper-bound sieve estimate for the sifted
quantities used in the pin lane.  Not formalized in this project. -/
def SelbergUpperBoundSieve (S : ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x z : ℕ, 2 ≤ z → z ≤ x → S x z ≤ c * (x / Real.log z)

/-- **EXTERNAL (uninhabited here).**  Brun–Titchmarsh: an upper bound for primes in an arithmetic
progression.  Not formalized in this project. -/
def BrunTitchmarsh (piAP : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x q a : ℕ, 1 ≤ q → q < x →
    piAP x q a ≤ c * (x / ((q : ℝ) * Real.log (x / q)))

/-- **EXTERNAL (uninhabited here).**  The prime-counting estimate used for the pin population.
Not formalized in this project. -/
def PrimeCountingEstimate (pinPop : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ M : ℕ, 100 ≤ M → δ * (M / Real.log M) ≤ pinPop M

/-! ## 2.  The pin-capture inequality (conditional) -/

/-- The pin-capture inequality for a residual family `𝓡`, with pin count `Φ` and weight `W`:
`Φ(𝓡) ≤ c·M·log(2H)/(log M)² + W(𝓡)/log(2H)`. -/
def PinCaptureInequality (Phi W : Finset ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (M H : ℕ) (R : Finset ℕ), 100 ≤ M → 1 ≤ H →
    Phi R ≤ c * ((M : ℝ) * Real.log (2 * H) / (Real.log M) ^ 2)
      + W R / Real.log (2 * H)

/-- The adapter consuming the analytic inputs.  It is itself **external**: no Lean proof of it
exists in this project. -/
def PinCaptureAdapter (Phi W : Finset ℕ → ℝ) (S : ℕ → ℕ → ℝ) (piAP : ℕ → ℕ → ℕ → ℝ) : Prop :=
  FouvryShiftedPrimeInput ∧ SelbergUpperBoundSieve S ∧ BrunTitchmarsh piAP →
    PinCaptureInequality Phi W

/-- **CONDITIONAL-BANKED.**  The pin-capture inequality follows from the shifted-prime input, the
Selberg sieve and Brun–Titchmarsh through the adapter — and only that way. -/
theorem pin_capture_conditional {Phi W : Finset ℕ → ℝ} {S : ℕ → ℕ → ℝ} {piAP : ℕ → ℕ → ℕ → ℝ}
    (hadapt : PinCaptureAdapter Phi W S piAP)
    (hF : FouvryShiftedPrimeInput) (hS : SelbergUpperBoundSieve S) (hBT : BrunTitchmarsh piAP) :
    PinCaptureInequality Phi W :=
  hadapt ⟨hF, hS, hBT⟩

/-- **CONDITIONAL-BANKED.**  The short-cofactor pin bound: the pin count of a residual family with
short cofactors is bounded by the capture inequality specialized at the family's own weight. -/
theorem short_cofactor_pin_bound {Phi W : Finset ℕ → ℝ} (h : PinCaptureInequality Phi W)
    (M H : ℕ) (R : Finset ℕ) (hM : 100 ≤ M) (hH : 1 ≤ H) :
    ∃ c : ℝ, 0 < c ∧ Phi R ≤ c * ((M : ℝ) * Real.log (2 * H) / (Real.log M) ^ 2)
      + W R / Real.log (2 * H) := by
  obtain ⟨c, hc, hineq⟩ := h
  exact ⟨c, hc, hineq M H R hM hH⟩

/-! ## 3.  Exact consequences of the inequality (kernel, given the inputs) -/

/-- **Kernel (given the numerical inputs).**  A residual family whose support weight is
sublinear cannot contain a positive proportion of the pin population: if the capture bound plus
the sublinear weight term stays below `ρ·pinPop`, the family's pin count does. -/
theorem sublinear_support_cannot_capture_positive_proportion
    {Phi : ℝ} {mainTerm weightTerm rho pinPop : ℝ}
    (hcap : Phi ≤ mainTerm + weightTerm)
    (hsub : mainTerm + weightTerm < rho * pinPop) :
    Phi < rho * pinPop :=
  lt_of_le_of_lt hcap hsub

/-- **Kernel (given the numerical inputs).**  Branch-budget pin localization: under the bounded
adaptive-absorption budget `W(𝓡) ≤ (16/5)z₀ + (8/5)g₀`, the pin-capture inequality localizes the
pin count in terms of the zero and guard budgets. -/
theorem branch_budget_pin_localization
    {Phi mainTerm weight L z0 g0 : ℝ} (hL : 0 < L)
    (hcap : Phi ≤ mainTerm + weight / L)
    (hbudget : weight ≤ (16/5) * z0 + (8/5) * g0) :
    Phi ≤ mainTerm + ((16/5) * z0 + (8/5) * g0) / L := by
  have hdiv : weight / L ≤ ((16/5) * z0 + (8/5) * g0) / L := by gcongr
  linarith

/-! ## 4.  Interpretation and firewalls -/

/-- **Interpretation (bookkeeping).**  On a surviving terminal leaf the Fouvry bulk is no longer a
separate completion owner: the pin bound is consumed inside the branch budget, which is what the
localization theorem above expresses.  This is recorded, not used as a mathematical premise. -/
def fouvryBulkNotSeparateOwner : String :=
  "Fouvry bulk is consumed by the branch budget; it is not a separate completion owner."

/-- **Firewall.**  No bound of this module infers the existence of a surviving terminal leaf: a
bound valid *on* a leaf never produces a leaf. -/
theorem fouvry_bound_does_not_give_terminal_leaf :
    ¬ ∀ (Leaf : Type) (H C : Leaf → Prop), (∀ l, H l → C l) → Nonempty Leaf := by
  intro h
  exact (h Empty (fun _ => True) (fun _ => True) (fun _ _ => trivial)).elim (fun e => e.elim)

/-- **Firewall.**  Conditional analytic records never become kernel theorems: an implication from
an uninhabited premise carries no conclusion. -/
theorem external_premise_does_not_upgrade :
    ¬ ∀ P Q : Prop, (P → Q) → Q := by
  intro h
  exact h False False id

end FouvryPin
end ResearchBankV7
end Erdos287
