import RequestProject.Erdos287.PostV87V90R.NarrowWidth
import RequestProject.Erdos287.PostV87V90R.RetiredRoutes

/-!
# Erdős #287 — post-V87 → V90R: semantic regression suite

**ERDŐS #287 REMAINS OPEN.**  Each item is a kernel-checked negative control.

1. `C_lt_11_3_alone_insufficient` — `C < 11/3` without the first-moment size condition does
   **not** yield occupancy (explicit one-point fixture).
2. `obsolete_11_6_not_threshold` — a pair constant `C = 3 ≥ 11/6` still satisfies the repaired
   `r = 11, m = 3` hypotheses; `11/6` is not a threshold and occurs nowhere downstream (also
   grep-checked by `audit.sh`).
3. `crossScale_not_reduction` — `CrossScaleSynchronization287` is equivalent to tail exclusion.
4. `width_exclusion_not_global` — width exclusion at every `s > 3` does not imply emptiness.
5. `fixed_s_not_pointwise_three` — excluding every fixed `s > 3` does not give `M ≤ 3a` at any
   finite `M`.
6. `wideWindow_exists`, `residualWindow_exists` (non-vacuity of the providers' domains) and
   `wordQuantified_provider_trivial` (why the providers are window-quantified); the build-time
   `#audit_providers_v90` additionally rejects `True`/`False.elim`/`IsEmpty` constructions.
7. `predicate_provider_trivial` — a provider storing only a predicate is trivially inhabited;
   `windowMomentData_exposes` — the real provider exposes the numerical inequalities.
8. `finite_verifier_not_asymptotic` — a finite verification (`n² + n + 41` prime for
   `n < 40`) is not the asymptotic statement (fails at `n = 40`).
9. `three_blocks_no_contact` — the `G(11,2)` geometry proves only the consumer: three occupied
   blocks force nothing.
10. `finite_bank_gap` — finite exclusion below a smaller bound does not fill the onset gap.
-/

open scoped BigOperators
open Classical

namespace Erdos287.PostV87V90R

open Erdos287 Erdos287.PostV71V87

/-! ## 1. `C < 11/3` alone is not the theorem -/

/-- The one-point weight space. -/
noncomputable def pointWeights : FiniteWeights where
  T := {0}
  w := fun _ => 1
  w_nonneg := fun _ _ => zero_le_one
  w_sum := by simp

theorem pointWeights_E (f : ℕ → ℝ) : pointWeights.E f = f 0 := by
  simp [FiniteWeights.E, pointWeights]

/-- One count in block `0`, nothing elsewhere. -/
def singleCount : ℕ → ZMod 11 → ℕ := fun _ j => if j = 0 then 1 else 0

theorem singleCount_P : Pcount singleCount 0 = 1 := by decide
theorem singleCount_Q : Qcount singleCount 0 = 0 := by decide
theorem singleCount_Z : Zcount singleCount 0 = 1 := by decide

/-- **Regression 1.**  `𝔼P ≥ μ > 0`, `𝔼Q ≤ C μ²/22` and `C < 11/3` do **not** force four
occupied blocks: the first-moment size condition `μ > 33/(11 - 3C)` is indispensable. -/
theorem C_lt_11_3_alone_insufficient :
    ¬ ∀ (F : FiniteWeights) (Y : ℕ → ZMod 11 → ℕ) (μ C : ℝ), 0 < μ →
      μ ≤ F.E (fun t => (Pcount Y t : ℝ)) →
      F.E (fun t => (Qcount Y t : ℝ)) ≤ C * μ ^ 2 / (2 * 11) → C < 11 / 3 →
      ∃ t ∈ F.T, 0 < F.w t ∧ 4 ≤ Zcount Y t := by
  intro h
  obtain ⟨t, ht, -, hZ⟩ := h pointWeights singleCount 1 0 one_pos
    (by rw [pointWeights_E, singleCount_P]; norm_num)
    (by rw [pointWeights_E, singleCount_Q]; norm_num) (by norm_num)
  have : t = 0 := by simpa [pointWeights] using ht
  subst this
  rw [singleCount_Z] at hZ
  omega

/-- The same fixture violates the first-moment size condition, as it must. -/
theorem singleCount_violates_first_moment : ¬ ((33 : ℝ) / (11 - 3 * 0) < 1) := by norm_num

/-! ## 2. `11/6` is obsolete -/

/-- **Regression 2.**  `C = 3` is above the obsolete `11/6`, yet satisfies the repaired
condition `C < 11/3`, with first-moment size requirement `33/(11 - 9) = 16.5`. -/
theorem obsolete_11_6_not_threshold :
    (11 : ℝ) / 6 < 3 ∧ (3 : ℝ) < 11 / 3 ∧ (33 : ℝ) / (11 - 3 * 3) < 17 := by norm_num

/-! ## 3. Cross-scale synchronisation is overstrong -/

/-- **Regression 3.** -/
theorem crossScale_not_reduction (M0 : ℕ) :
    CrossScaleSynchronization287 M0 ↔ TailExclusion M0 :=
  crossScale_retired_equiv_tail M0

/-! ## 4–5. Width exclusion versus global / pointwise statements -/

/-- Width exclusion at width `s` for an abstract predicate on windows. -/
def WidthExcluded (Bad : ℕ → ℕ → Prop) (s : ℝ) : Prop :=
  ∃ Ms : ℕ, ∀ a M : ℕ, Bad a M → Ms ≤ M → s * a ≤ M → False

/-- **Regression 4.**  Exclusion at every width `s > 3` does not imply emptiness: the windows
`M = 3a` survive every fixed `s > 3` (the narrow-width owner is indispensable). -/
theorem width_exclusion_not_global :
    ∃ Bad : ℕ → ℕ → Prop, (∀ s : ℝ, 3 < s → WidthExcluded Bad s) ∧
      ∀ M0 : ℕ, ∃ a M, M0 ≤ M ∧ Bad a M := by
  refine ⟨fun a M => M = 3 * a ∧ 1 < a, fun s hs => ⟨0, fun a M ⟨hM, ha⟩ _ hle => ?_⟩,
    fun M0 => ⟨M0 + 2, 3 * (M0 + 2), by omega, rfl, by omega⟩⟩
  subst hM
  have : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  push_cast at hle
  nlinarith

/-- **Regression 5.**  The windows `(a, 3a + 1)` are excluded at every fixed width `s > 3`
beyond an onset, yet *every* one of them has `M > 3a`: the W3 family does not give a pointwise
`M/a ≤ 3` at finite `M`. -/
theorem fixed_s_not_pointwise_three :
    (∀ s : ℝ, 3 < s → ∃ Ms : ℕ, ∀ a : ℕ, Ms ≤ 3 * a + 1 → ((3 * a + 1 : ℕ) : ℝ) < s * a) ∧
      ∀ a : ℕ, 3 * a < 3 * a + 1 := by
  refine ⟨fun s hs => ⟨3 * (⌊1 / (s - 3)⌋₊ + 1) + 1, fun a ha => ?_⟩, fun a => by omega⟩
  have hpos : 0 < s - 3 := by linarith
  have ha' : ⌊1 / (s - 3)⌋₊ + 1 ≤ a := by omega
  have h1 : 1 / (s - 3) < (a : ℝ) := by
    have := Nat.lt_floor_add_one (1 / (s - 3))
    have : ((⌊1 / (s - 3)⌋₊ + 1 : ℕ) : ℝ) ≤ a := by exact_mod_cast ha'
    push_cast at this
    linarith
  rw [div_lt_iff₀ hpos] at h1
  push_cast
  nlinarith

/-! ## 6. Providers are window-quantified and non-vacuous -/

/-- **Regression 6 (semantic audit).**  A moment field quantified over hypothetical exact words
(instead of windows) would be trivially inhabited from tail exclusion itself — circular.  This
is why `WidthThreeMomentProvider` quantifies over windows (`WideWindow`, provably inhabited by
`wideWindow_exists`). -/
theorem wordQuantified_provider_trivial {r m K : ℕ} [NeZero r] (C : AffineContactCompiler r m K)
    (H M0 : ℕ) (htail : TailExclusion M0) :
    ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M → Nonempty (WindowMomentData C H W.a W.M) :=
  fun W ha hM => (htail W ha hM).elim

/-- Wide windows exist beyond every onset (`3 < s ≤ 7`): the W3 provider's moment field is not
vacuous. -/
theorem w3_domain_nonempty {s : ℝ} (hs : 3 < s) (hs7 : s ≤ 7) (onset : ℕ) :
    ∃ a M : ℕ, WideWindow s onset a M :=
  wideWindow_exists hs hs7 onset

/-- Residual windows exist beyond every onset: the `E287_11_4` occupancy field is not vacuous. -/
theorem e287_domain_nonempty {s : ℝ} (hs : 3 < s) (onset : ℕ) :
    ∃ a M : ℕ, ResidualWindow s onset a M :=
  residualWindow_exists hs onset

/-! ## 7. Predicate-only providers are worthless -/

/-- A "provider" that only stores a proposition and its proof. -/
structure PredicateOnlyProvider where
  claim : Prop
  proof : claim

/-- **Regression 7.**  Such a record is inhabited by `True`; it carries no information. -/
theorem predicate_provider_trivial : Nonempty PredicateOnlyProvider := ⟨⟨True, trivial⟩⟩

/-- The real window moment data exposes the numerical inequalities actually consumed. -/
theorem windowMomentData_exposes {r m K : ℕ} [NeZero r] {C : AffineContactCompiler r m K}
    {H a M : ℕ} (D : WindowMomentData C H a M) :
    0 < D.μ ∧ D.μ ≤ D.F.E (fun t => (Pcount (blockCount C) t : ℝ)) ∧
      D.F.E (fun t => (Qcount (blockCount C) t : ℝ)) ≤ D.Cpair * D.μ ^ 2 / (2 * r) ∧
      D.Cpair < r / m ∧ (m : ℝ) * r / (r - m * D.Cpair) < D.μ :=
  ⟨D.hμ, D.firstMoment, D.pairMoment, D.pairConstant, D.firstMomentLarge⟩

/-! ## 8. Finite verification is not asymptotic prime supply -/

/-- **Regression 8.**  `n² + n + 41` is prime for every `n < 40` (a finite verification) but
not for `n = 40`: no finite check implies the corresponding asymptotic prime-supply statement. -/
theorem finite_verifier_not_asymptotic :
    (∀ n < 40, (n ^ 2 + n + 41).Prime) ∧ ¬ (40 ^ 2 + 40 + 41).Prime := by
  refine ⟨fun n hn => ?_, by norm_num⟩
  interval_cases n <;> norm_num

/-! ## 9. The 11-block geometry proves only the consumer -/

/-- **Regression 9.**  Three occupied blocks (`{0,1,2}`) contain no useful edge of `G(11,2)`:
the graph theorem supplies the consumer geometry, never occupancy. -/
theorem three_blocks_no_contact :
    ∃ O : Finset (ZMod 11), O.card = 3 ∧ IndepFinset (G 11 2) O :=
  ⟨arc 11 3, arc_card (by norm_num), arc_indep (by norm_num)⟩

/-! ## 10. Finite-bank exclusion does not fill the onset gap -/

/-- **Regression 10.**  Tail exclusion beyond `10` and finite exclusion below `3` leave the
value `5` uncovered: a finite bank below a smaller bound than the (unknown) W3 onset proves
nothing about the gap. -/
theorem finite_bank_gap :
    ∃ Bad : ℕ → Prop, (∀ M, 10 ≤ M → ¬ Bad M) ∧ (∀ M, M < 3 → ¬ Bad M) ∧ ∃ M, Bad M :=
  ⟨fun M => M = 5, fun M h h5 => by omega, fun M h h5 => by omega, 5, rfl⟩

end Erdos287.PostV87V90R
