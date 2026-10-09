import RequestProject.Erdos287.PostV87V90R

/-!
# Erdős #287 — W3 publication package: checkpoint

**ERDŐS #287 REMAINS OPEN.**  This module freezes the W3 publication interface that the
W2.984 package (`Erdos287.W2984Publication`) imports.  It adds **no new mathematics**: every
name below is an alias of an already-built declaration of `Erdos287.PostV87V90R`, which remains
the single source of truth (exact #287 model, moment Cauchy consumer, cyclic contact graph,
affine gcd compiler, fixed-relative window geometry, bounded-cofactor row rigidity, harmonic
width bounds, conditional W3).

Status of W3 at this checkpoint (unchanged from `ERDOS287_POSTV87_V90R_REPORT.md`):
`W3_of_provider : WidthThreeMomentProvider s → (no wide exact word beyond the onset)` is
kernel-proved; the provider itself (the width-`> 3` analytic moment theorem) is an explicit,
never-constructed input.  The referee verdict `W3: PASS` concerns the written analytic proof
of that input; it is not a Lean fact.
-/

namespace Erdos287.W3Publication

open Erdos287 Erdos287.PostV71V87 Erdos287.PostV87V90R

/-- The W3-type width statement at width `s` (alias). -/
abbrev WidthStatement (s : ℝ) : Prop := PostV87V90R.W3Statement s

/-- Wide windows (alias). -/
abbrev Wide (s : ℝ) (onset a M : ℕ) : Prop := PostV87V90R.WideWindow s onset a M

theorem WidthStatement.mono {s s' : ℝ} (h : WidthStatement s) (hss : s ≤ s') :
    WidthStatement s' := PostV87V90R.W3Statement.mono h hss

/-- W3 (conditional), re-exported. -/
theorem W3_of_provider {s : ℝ} (P : WidthThreeMomentProvider s) : WidthStatement s :=
  W3Statement_of_provider P

/-- Wide windows of an exact word. -/
theorem wide_of_exactWord {s : ℝ} {onset : ℕ} (W : ExactWord) (ha : 1 < W.a)
    (hM : onset ≤ W.M) (hs : s * W.a ≤ W.M) : Wide s onset W.a W.M :=
  ⟨ha, hM, hs, ExactWord.exp_lower W ha, ExactWord.exp_upper W ha⟩

/-- Width statement in counterexample language: `M ≥ M_s` and `s · min A ≤ max A` is impossible. -/
theorem counterexample_form {s : ℝ} (h : WidthStatement s) :
    ∃ Ms : ℕ, ∀ A : Finset ℕ, ∀ hA : Erdos287Counterexample A, Ms ≤ A.max' hA.nonempty →
      s * (A.min' hA.nonempty : ℝ) ≤ A.max' hA.nonempty → False := by
  obtain ⟨Ms, hMs⟩ := h
  refine ⟨Ms, fun A hA hM hs => ?_⟩
  have ha := ofCounterexample_one_lt_a hA
  refine hMs (ofCounterexample hA) ha (by rwa [ofCounterexample_M]) ?_
  rw [ofCounterexample_a, ofCounterexample_M]; exact hs

end Erdos287.W3Publication
