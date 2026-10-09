import RequestProject.Erdos287.PostV87V90R.WidthThree

/-!
# Erdős #287 — post-V87 → V90R: the narrow-width owner and `E287_11_4` (CONDITIONAL)

**ERDŐS #287 REMAINS OPEN.**

## The current owner

After W3 (all fixed widths `s > 3`) and the harmonic bound `e(a-1) < M`, the remaining
sufficiently large sources live in the chamber `e(a-1) < M < s·a` (approximately
`e ≤ M/a ≤ 3`).  `NarrowWidth287 s onset W` is membership of an exact word in this chamber
(no `o(1)` anywhere: `s` is a fixed real `> 3`).  `narrowWidth_bounds` proves the exact
harmonic two-sided restriction.

`NarrowWidthClosureProvider s` (OPEN, never constructed) is precisely the exclusion of the
chamber beyond an explicit onset.

## Splices (all CONDITIONAL)

* `tail_of_W3_narrow` : W3 provider → narrow closure → tail exclusion;
* `tail_of_W3family_narrow` : W3 provider family → narrow closure → tail exclusion;
* `erdos287_of_W3_narrow_finite` : W3 provider → narrow closure →
  `FiniteExclusionBelow (max onsets)` → no Erdős #287 counterexample.

## `E287_11_4`

`E287_11_4_Provider s` (OPEN, never constructed) asserts, for every residual window beyond a
uniform onset: a fixed 11-macroblock compiler for `ContactCycle 11 3 = G(11,2)`, one parameter
with window control (source window, adjacency orientation, row bound, big prime) and **four
distinct occupied macroblocks** whose occupancy *is* primality of actual form values.
Then `4 > α(G(11,2)) = 3` (`E287_11_4_geometry`) yields a useful occupied edge, hence adjacent
compulsory omissions, hence a contradiction:

* `E287_11_4` : `E287_11_4_Provider s → NarrowWidthClosureProvider s`;
* `tail_of_E287_11_4` : W3 provider → `E287_11_4_Provider` → tail exclusion.

*Audit note.*  Parity / endpoint / mask information is not needed by the consumer (only exact
mass and gap-two enter, via row rigidity), so it is not demanded of the provider.
-/

open scoped BigOperators
open Classical

namespace Erdos287.PostV87V90R

open Erdos287 Erdos287.PostV71V87

/-- **The narrow-width chamber** (current owner): an exact word with `a > 1`, `M ≥ onset` and
`M < s a`. -/
def NarrowWidth287 (s : ℝ) (onset : ℕ) (W : ExactWord) : Prop :=
  1 < W.a ∧ onset ≤ W.M ∧ (W.M : ℝ) < s * W.a

/-- Exact harmonic restriction of the chamber: `e (a - 1) < M < s a`. -/
theorem narrowWidth_bounds {s : ℝ} {onset : ℕ} {W : ExactWord} (h : NarrowWidth287 s onset W) :
    Real.exp 1 * ((W.a : ℝ) - 1) < W.M ∧ (W.M : ℝ) < s * W.a :=
  ⟨ExactWord.exp_lower W h.1, h.2.2⟩

/-- **(OPEN provider)** Exclusion of the narrow chamber beyond an explicit onset. -/
structure NarrowWidthClosureProvider (s : ℝ) where
  hs : 3 < s
  onset : ℕ
  exclude : ∀ W : ExactWord, NarrowWidth287 s onset W → False

/-- Tail exclusion beyond `M0`. -/
def TailExclusion (M0 : ℕ) : Prop := ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M → False

/-- **Splice (CONDITIONAL).**  W3 at width `s' ≤ s` plus narrow closure at `s` give tail
exclusion. -/
theorem tail_of_W3Statement_narrow {s s' : ℝ} (hss : s' ≤ s) {Ms : ℕ}
    (h3 : ∀ W : ExactWord, 1 < W.a → Ms ≤ W.M → s' * W.a ≤ W.M → False)
    (N : NarrowWidthClosureProvider s) : TailExclusion (max Ms N.onset) := by
  intro W ha hM
  by_cases hw : s' * W.a ≤ W.M
  · exact h3 W ha (le_trans (le_max_left _ _) hM) hw
  · push_neg at hw
    exact N.exclude W ⟨ha, le_trans (le_max_right _ _) hM, by
      have : (0 : ℝ) ≤ W.a := by positivity
      nlinarith⟩

/-- **W3 provider → narrow closure → tail exclusion (CONDITIONAL).** -/
theorem tail_of_W3_narrow {s : ℝ} (P : WidthThreeMomentProvider s)
    (N : NarrowWidthClosureProvider s) : TailExclusion (max P.onset N.onset) :=
  tail_of_W3Statement_narrow le_rfl (W3_of_provider P) N

/-- **W3 provider family → narrow closure → tail exclusion (CONDITIONAL).** -/
theorem tail_of_W3family_narrow
    (Pfam : ∀ s : ℝ, 3 < s → s ≤ 7 → WidthThreeMomentProvider s) {s : ℝ}
    (N : NarrowWidthClosureProvider s) : ∃ M0, TailExclusion M0 := by
  have hs' : 3 < min s 7 := lt_min N.hs (by norm_num)
  let P := Pfam (min s 7) hs' (min_le_right _ _)
  exact ⟨_, tail_of_W3Statement_narrow (min_le_left s 7) (W3_of_provider P) N⟩

/-- **Global splice (CONDITIONAL).**  W3 provider, narrow closure and finite exclusion below the
explicit combined onset give: no Erdős #287 counterexample exists. -/
theorem erdos287_of_W3_narrow_finite {s : ℝ} (P : WidthThreeMomentProvider s)
    (N : NarrowWidthClosureProvider s) (hfin : FiniteExclusionBelow (max P.onset N.onset)) :
    ∀ A : Finset ℕ, ¬ Erdos287Counterexample A := by
  intro A hA
  by_cases hlt : A.max' hA.nonempty < max P.onset N.onset
  · exact hfin A hA hlt
  · push_neg at hlt
    exact tail_of_W3_narrow P N (ofCounterexample hA) (ofCounterexample_one_lt_a hA) hlt

/-! ## `E287_11_4` -/

/-- Residual windows: `1 < a`, `onset ≤ M`, `M < s a`, `e(a-1) < M`. -/
def ResidualWindow (s : ℝ) (onset a M : ℕ) : Prop :=
  1 < a ∧ onset ≤ M ∧ (M : ℝ) < s * a ∧ Real.exp 1 * ((a : ℝ) - 1) < M

/-- **(OPEN provider) `E287_11_4`.**  A fixed 11-macroblock compiler for `G(11,2)`, a uniform
onset, and for every residual window a single parameter with window control at which at least
four distinct macroblocks are occupied by prime form values. -/
structure E287_11_4_Provider (s : ℝ) where
  hs : 3 < s
  K : ℕ
  compiler : AffineContactCompiler 11 3 K
  H : ℕ
  onset : ℕ
  occupancy : ∀ a M : ℕ, ResidualWindow s onset a M →
    ∃ t, WindowControl compiler a M H t ∧ 4 ≤ (occupied compiler t).card

/-- The consumer geometry: `α(G(11,2)) = 3 < 4`. -/
theorem E287_11_4_geometry : alpha (G 11 2) < 4 := by rw [alpha_G_11_2]; norm_num

/-- **`E287_11_4` (CONDITIONAL).**  The provider closes the narrow chamber. -/
def E287_11_4 {s : ℝ} (P : E287_11_4_Provider s) : NarrowWidthClosureProvider s where
  hs := P.hs
  onset := P.onset
  exclude := fun W ⟨ha, hM, hs⟩ => by
    obtain ⟨t, hW, hocc⟩ := P.occupancy W.a W.M ⟨ha, hM, hs, ExactWord.exp_lower W ha⟩
    exact occupancy_contact_false (m := 3) (r := 11) W P.compiler (by norm_num) (by norm_num)
      hW hocc

/-- **`E287_11_4` + W3 → tail exclusion (CONDITIONAL).** -/
theorem tail_of_E287_11_4 {s : ℝ} (P3 : WidthThreeMomentProvider s) (P : E287_11_4_Provider s) :
    TailExclusion (max P3.onset P.onset) :=
  tail_of_W3_narrow P3 (E287_11_4 P)

/-- **Non-vacuity:** residual windows exist beyond every onset, for every `s > 3`. -/
theorem residualWindow_exists {s : ℝ} (hs : 3 < s) (onset : ℕ) :
    ∃ a M : ℕ, ResidualWindow s onset a M := by
  refine ⟨onset + 2, 3 * (onset + 2), by omega, by omega, ?_, ?_⟩
  · push_cast
    have : (0 : ℝ) < (onset : ℝ) + 2 := by positivity
    nlinarith
  · have he := Real.exp_one_lt_d9
    push_cast
    have : (0 : ℝ) ≤ (onset : ℝ) := by positivity
    nlinarith [Real.exp_pos 1]

end Erdos287.PostV87V90R
