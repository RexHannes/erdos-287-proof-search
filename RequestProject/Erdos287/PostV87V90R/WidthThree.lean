import RequestProject.Erdos287.PostV87V90R.OccupancyContact

/-!
# Erdős #287 — post-V87 → V90R: the width-`> 3` theorem W3 (CONDITIONAL)

**ERDŐS #287 REMAINS OPEN.  W3 is proved here only from an explicit, never-constructed
analytic provider.**

## Factoring

1. **Finite compiler** — `AffineContactCompiler (4m+1) m K` (data with proved fields).
2. **Analytic moment provider** — `WindowMomentData C H a M`: for the *window* `[a, M]` only
   (no reference to any hypothetical counterexample), a finite weighted parameter set with
   * first moment `𝔼P ≥ μ > 0`,
   * pair moment `𝔼Q ≤ C μ²/(2r)`,
   * pair constant `C < r/m` (`= 4 + 1/m` for `r = 4m+1`: the classical `4 + η` constant
     with `η < 1/m`, see `pairConstant_iff`),
   * first-moment size `μ > m r/(r - mC)`,
   * window control (source window, row bound, big prime) on the support.
3. **Moment-to-occupancy consumer** — `occupancy_of_normalized_moments` (unconditional).
4. **Occupancy-to-contact consumer** — `occupancy_contact_false` (unconditional).

`WidthThreeMomentProvider s` bundles `m` with `3 + 1/m < s` (`width`), the compiler, `H`, an
**explicit onset** and window-level moment data for every *wide window*
(`WideWindow s onset a M`: `1 < a`, `onset ≤ M`, `s a ≤ M`, `e(a-1) < M ≤ e²(a+1)`).

*Semantic audit.*  The moment field is quantified over windows `(a, M)`, which provably exist
for every `3 < s ≤ 7` and every onset (`wideWindow_exists`); it is a genuine prime-distribution
statement.  Quantifying it over hypothetical exact words instead would make it trivially
inhabitable from tail exclusion (`RegressionSuite.wordQuantified_provider_trivial`).

## Results

* `W3_of_provider` : `WidthThreeMomentProvider s → W3Statement s` (**conditional**);
* `W3_counterexample_form` — the same in the language of `Erdos287Counterexample`, with
  `M / min A ≥ s`;
* `W3_family_of_providers` — a uniform provider family for `3 < s ≤ 7` gives `W3Statement s`
  for *every* `s > 3` (monotonicity, `W3Statement.mono`).

No inhabitant of `WidthThreeMomentProvider` is constructed anywhere: **W3 is CONDITIONAL**.
-/

open scoped BigOperators
open Classical

namespace Erdos287.PostV87V90R

open Erdos287 Erdos287.PostV71V87

section Window

variable {r m K : ℕ} [NeZero r]

/-- **Window-level analytic moment data** for a compiler on the window `[a, M]`.  Every field
is a concrete numerical inequality; nothing refers to a hypothetical counterexample. -/
structure WindowMomentData (C : AffineContactCompiler r m K) (H a M : ℕ) where
  /-- Finite weighted parameter set. -/
  F : FiniteWeights
  /-- First-moment lower bound. -/
  μ : ℝ
  /-- Normalised pair constant. -/
  Cpair : ℝ
  hμ : 0 < μ
  firstMoment : μ ≤ F.E (fun t => (Pcount (blockCount C) t : ℝ))
  pairMoment : F.E (fun t => (Qcount (blockCount C) t : ℝ)) ≤ Cpair * μ ^ 2 / (2 * r)
  pairConstant : Cpair < r / m
  firstMomentLarge : (m : ℝ) * r / (r - m * Cpair) < μ
  scaleControl : ∀ t ∈ F.T, 0 < F.w t → WindowControl C a M H t

/-- Window moment data at the window of an exact word is contradictory. -/
theorem WindowMomentData.false {C : AffineContactCompiler r m K} {H : ℕ} {W : ExactWord}
    (D : WindowMomentData C H W.a W.M) (hm : 1 ≤ m) (hr : 2 * m ≤ r) : False :=
  moment_contact_false W C hm hr D.F D.hμ D.firstMoment D.pairMoment D.pairConstant
    D.firstMomentLarge D.scaleControl

end Window

/-- Admissible wide windows. -/
def WideWindow (s : ℝ) (onset a M : ℕ) : Prop :=
  1 < a ∧ onset ≤ M ∧ s * a ≤ M ∧ Real.exp 1 * ((a : ℝ) - 1) < M ∧
    (M : ℝ) ≤ Real.exp 1 ^ 2 * ((a : ℝ) + 1)

/-- **Explicit analytic provider for W3 at width `s`** (never constructed here). -/
structure WidthThreeMomentProvider (s : ℝ) where
  hs : 3 < s
  hs7 : s ≤ 7
  m : ℕ
  hm : 1 ≤ m
  /-- Graph width `((4m+1) - m)/m = 3 + 1/m < s`. -/
  width : (((4 * m + 1 : ℕ) : ℝ) - m) / m < s
  K : ℕ
  compiler : AffineContactCompiler (4 * m + 1) m K
  H : ℕ
  /-- Explicit, uniform onset. -/
  onset : ℕ
  moments : ∀ a M : ℕ, WideWindow s onset a M → WindowMomentData compiler H a M

/-- The block number `r = 4m + 1` of a W3 provider. -/
def WidthThreeMomentProvider.blocks {s : ℝ} (P : WidthThreeMomentProvider s) : ℕ := 4 * P.m + 1

/-- For `r = 4m+1` the pair-constant condition `C < r/m` is `C < 4 + 1/m`. -/
theorem pairConstant_iff {m : ℕ} (hm : 1 ≤ m) (C : ℝ) :
    C < ((4 * m + 1 : ℕ) : ℝ) / m ↔ C < 4 + 1 / m := by
  have : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have e : ((4 * m + 1 : ℕ) : ℝ) / m = 4 + 1 / m := by push_cast; field_simp
  rw [e]

/-- The W3 conclusion at width `s`: beyond some `M_s`, no exact word has `M ≥ s a`. -/
def W3Statement (s : ℝ) : Prop :=
  ∃ Ms : ℕ, ∀ W : ExactWord, 1 < W.a → Ms ≤ W.M → s * W.a ≤ W.M → False

theorem W3Statement.mono {s s' : ℝ} (h : W3Statement s) (hss : s ≤ s') : W3Statement s' := by
  obtain ⟨Ms, hMs⟩ := h
  refine ⟨Ms, fun W ha hM hs => hMs W ha hM ?_⟩
  have : (0 : ℝ) ≤ W.a := by positivity
  nlinarith

/-- **W3 (CONDITIONAL).**  `WidthThreeMomentProvider s → W3Statement s`, with `M_s` the
provider's explicit onset. -/
theorem W3_of_provider {s : ℝ} (P : WidthThreeMomentProvider s) :
    ∀ W : ExactWord, 1 < W.a → P.onset ≤ W.M → s * W.a ≤ W.M → False := by
  intro W ha hM hs
  exact (P.moments W.a W.M ⟨ha, hM, hs, ExactWord.exp_lower W ha, ExactWord.exp_upper W ha⟩).false
    P.hm (by omega)

theorem W3Statement_of_provider {s : ℝ} (P : WidthThreeMomentProvider s) : W3Statement s :=
  ⟨P.onset, W3_of_provider P⟩

/-- **W3 in counterexample language (CONDITIONAL).**  For every Erdős #287 counterexample `A`
with `max A ≥ M_s`, the width satisfies `max A / min A < s`. -/
theorem W3_counterexample_form {s : ℝ} (P : WidthThreeMomentProvider s) :
    ∃ Ms : ℕ, ∀ A : Finset ℕ, ∀ h : Erdos287Counterexample A, Ms ≤ A.max' h.nonempty →
      s ≤ (A.max' h.nonempty : ℝ) / A.min' h.nonempty → False := by
  refine ⟨P.onset, fun A h hM hs => ?_⟩
  have ha := ofCounterexample_one_lt_a h
  have hapos : (0 : ℝ) < (ofCounterexample h).a := by positivity
  refine W3_of_provider P (ofCounterexample h) ha hM ?_
  rw [ofCounterexample_a] at hapos ⊢
  rw [ofCounterexample_M]
  rwa [le_div_iff₀ hapos] at hs

/-- **W3 family (CONDITIONAL).**  A uniform provider family on `3 < s ≤ 7` yields W3 at every
width `s > 3`. -/
theorem W3_family_of_providers
    (Pfam : ∀ s : ℝ, 3 < s → s ≤ 7 → WidthThreeMomentProvider s) :
    ∀ s : ℝ, 3 < s → W3Statement s := by
  intro s hs
  rcases le_total s 7 with h7 | h7
  · exact W3Statement_of_provider (Pfam s hs h7)
  · exact (W3Statement_of_provider (Pfam 7 (by norm_num) le_rfl)).mono h7

/-- `e² > 7`. -/
theorem seven_lt_exp_sq : (7 : ℝ) < Real.exp 1 ^ 2 := by
  have := Real.exp_one_gt_d9
  nlinarith

/-- **Non-vacuity of the provider's moment field:** wide windows exist for every
`3 < s ≤ 7` and every onset. -/
theorem wideWindow_exists {s : ℝ} (hs : 3 < s) (hs7 : s ≤ 7) (onset : ℕ) :
    ∃ a M : ℕ, WideWindow s onset a M := by
  set a := onset + 2 with ha
  refine ⟨a, ⌈s * a⌉₊, by omega, ?_, Nat.le_ceil _, ?_, ?_⟩
  · have h1 : (onset : ℝ) ≤ s * a := by
      have : (onset : ℝ) ≤ a := by rw [ha]; push_cast; linarith
      have : (0 : ℝ) ≤ a := by positivity
      nlinarith
    exact_mod_cast le_trans h1 (Nat.le_ceil _)
  · have he := Real.exp_one_lt_d9
    have h1 : (a : ℝ) ≥ 2 := by rw [ha]; push_cast; linarith
    have : Real.exp 1 * ((a : ℝ) - 1) < s * a := by nlinarith [Real.exp_pos 1]
    exact lt_of_lt_of_le this (Nat.le_ceil _)
  · have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ s * a by positivity)
    have h7 := seven_lt_exp_sq
    have h1 : (a : ℝ) ≥ 2 := by rw [ha]; push_cast; linarith
    have : s * a + 1 ≤ Real.exp 1 ^ 2 * ((a : ℝ) + 1) := by nlinarith
    linarith

end Erdos287.PostV87V90R
