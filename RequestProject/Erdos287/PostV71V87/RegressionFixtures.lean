import RequestProject.Erdos287.PostV71V87.Firewalls
import RequestProject.Erdos287.PostV71V87.MinorRepair

/-!
# Erdős #287 (post-V71 → V87) — negative / hostile regression fixtures

Each fixture is a kernel-checked witness that a tempting but invalid upgrade fails.

* `reg_dvd_ne_zero`             — `D ∣ X` must not be confused with `X = 0`.
* `reg_actual_ne_target`        — an actual principal minor `C_R = B_R·S + K_R` is not the
                                  target-one quantity `D_R = B_R + K_R` when `S ≠ 1`.
* `reg_surrogate_not_exact`     — fixed-depth minor / valuation surrogates do not imply exact
                                  mass one (`{1,2,3,6}` has mass `2`).
* `reg_pointwise_not_uniform`   — a pointwise ("for each fixed prime, eventually") statement
                                  does not upgrade to a uniform one without a provider.
* `reg_endpoint_second_branch`  — the second V86 alternative `M - a < de < 2a` really occurs
                                  (gap-two word `{10,11,13,14}`, `d = 3`, `e = 4`), so the CRT
                                  theorem cannot be strengthened to `de > M`.
* `reg_active_above_qstar`      — for the same word, `q_* = 3` but the prime `5 ∈ (q_*, 2q_*]`
                                  has an active row: an active/empty transition at `q_*` is not
                                  a structural consequence of the definitions.
* `reg_superlog_not_polylog`    — superlogarithmic recurrence holds automatically in every
                                  polylogarithmic window (re-export of
                                  `polylog_window_not_excluded`).
-/

open scoped BigOperators

namespace Erdos287.PostV71V87

/-- `D ∣ X` is not `X = 0`: with `D = 2`, `X = 2`. -/
theorem reg_dvd_ne_zero : ∃ D X : ℤ, D ∣ X ∧ X ≠ 0 ∧ D ≠ 1 :=
  ⟨2, 2, dvd_refl _, by norm_num, by norm_num⟩

/-- The actual minor and its target-one substitute differ as soon as `B ≠ 0`, `S ≠ 1`:
`B = 1, K = 0, S = 2` gives `C = 2`, `D = 1`. -/
theorem reg_actual_ne_target :
    (MinorData.mk 1 0).actual 2 ≠ (MinorData.mk 1 0).target := by
  simp [MinorData.actual, MinorData.target]

/-- Valuation surrogates (at every prime set) and all fixed-depth minor tests hold for
`{1,2,3,6}`, whose mass is `2 ≠ 1`. -/
theorem reg_surrogate_not_exact :
    (∀ S : Finset ℕ, (∀ p ∈ S, p ≠ 1) → ValuationSurrogate {1, 2, 3, 6} S) ∧
      (∀ m : MinorData, (m.actual (∑ n ∈ ({1, 2, 3, 6} : Finset ℕ), (1 : ℚ) / n)).den = 1) ∧
      ∑ n ∈ ({1, 2, 3, 6} : Finset ℕ), (1 : ℚ) / n ≠ 1 := by
  refine ⟨fun S hS p hp => ?_, fun m => ?_, ?_⟩
  · rw [mass_one_two_three_six]
    simpa using hS p hp
  · rw [mass_one_two_three_six]; exact fixed_depth_tests_pass_at_two m
  · rw [mass_one_two_three_six]; norm_num

/-- Quantifier-swap fixture: "for every fixed `q`, eventually `q < X`" holds, while the
uniform statement "eventually, for every `q`, `q < X`" is false. -/
theorem reg_pointwise_not_uniform :
    (∀ q : ℕ, ∃ X0 : ℕ, ∀ X, X0 ≤ X → q < X) ∧
      ¬ (∃ X0 : ℕ, ∀ q X : ℕ, X0 ≤ X → q < X) := by
  refine ⟨fun q => ⟨q + 1, fun X hX => by omega⟩, ?_⟩
  rintro ⟨X0, h⟩
  exact lt_irrefl _ (h X0 X0 le_rfl)

/-- The gap-two word `{10, 11, 13, 14}` on `[10, 14]`. -/
def fixtureWord : Word where
  A := {10, 11, 13, 14}
  a := 10
  M := 14
  a_pos := by norm_num
  sub := by decide
  a_mem := by decide
  M_mem := by decide
  gap := by
    intro x h1 h2
    have hx : x = 10 ∨ x = 11 ∨ x = 12 ∨ x = 13 := by
      have h1' : 10 ≤ x := h1
      have h2' : x + 1 ≤ 14 := h2
      omega
    rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem fixtureWord_absent_three : fixtureWord.Absent 3 := by
  intro n hn
  simp only [fixtureWord, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> decide

theorem fixtureWord_absent_four : fixtureWord.Absent 4 := by
  intro n hn
  simp only [fixtureWord, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> decide

/-- **The second endpoint branch is realised.**  For coprime absent moduli `3, 4` of the
gap-two word `{10,11,13,14}`: `de = 12 ≤ M = 14`, while `M - a = 4 < 12 < 20 = 2a`. -/
theorem reg_endpoint_second_branch :
    Nat.Coprime 3 4 ∧ fixtureWord.Absent 3 ∧ fixtureWord.Absent 4 ∧
      ¬ fixtureWord.M < 3 * 4 ∧
      (fixtureWord.M - fixtureWord.a < 3 * 4 ∧ 3 * 4 < 2 * fixtureWord.a) :=
  ⟨by decide, fixtureWord_absent_three, fixtureWord_absent_four, by decide, by decide, by decide⟩

theorem fixtureWord_not_active_three : ¬ fixtureWord.Active 3 := by
  intro h
  obtain ⟨n, hn, hv⟩ := fixtureWord.exists_mem_v_eq_maxVal 3
  have h0 : Word.v 3 n = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fixtureWord_absent_three n hn)
  unfold Word.Active at h
  omega

theorem fixtureWord_active_two : fixtureWord.Active 2 := by
  have h := fixtureWord.v_le_maxVal (n := 10) (by decide) 2
  have h10 : Word.v 2 10 = 1 := by
    have : (10 : ℕ) = 2 ^ 1 * 5 := by norm_num
    rw [Word.v, this, Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 5 by decide)]
  unfold Word.Active
  omega

theorem fixtureWord_active_five : fixtureWord.Active 5 := by
  have h := fixtureWord.v_le_maxVal (n := 10) (by decide) 5
  have h10 : Word.v 5 10 = 1 := by
    have : (10 : ℕ) = 5 ^ 1 * 2 := by norm_num
    rw [Word.v, this, Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow Nat.prime_five]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 5 ∣ 2 by decide)]
  unfold Word.Active
  omega

/-- For the fixture word the minimal ceiling is `q_* = 3`. -/
theorem fixtureWord_qstar : fixtureWord.qstar = 3 := by
  have hle : fixtureWord.qstar ≤ 3 := by
    have := fixtureWord.qstar_le Nat.prime_three
    rwa [fixtureWord.Q_eq_self_of_not_active fixtureWord_not_active_three] at this
  have hgt := fixtureWord.one_lt_qstar
  have hne : fixtureWord.qstar ≠ 2 := by
    intro h2
    obtain ⟨p, hp, hQ⟩ := fixtureWord.qstar_spec
    rw [h2] at hQ
    have hpd : p ∣ 2 := by
      rw [← hQ, Word.Q]; exact dvd_pow_self p (by omega)
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hpd
    subst hp2
    have h1 := fixtureWord_active_two
    unfold Word.Active at h1
    have : 2 ^ 2 ≤ 2 ^ (1 + fixtureWord.maxVal 2) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Word.Q] at hQ
    omega
  omega

/-- **High-shell extinction is not adjacent to `q_*`.**  In the fixture word, the prime
`5 ∈ (q_*, 2 q_*]` has an active row although `q_* = 3`. -/
theorem reg_active_above_qstar :
    fixtureWord.qstar = 3 ∧ (5 : ℕ).Prime ∧ fixtureWord.qstar < 5 ∧
      5 ≤ 2 * fixtureWord.qstar ∧ fixtureWord.Active 5 := by
  refine ⟨fixtureWord_qstar, Nat.prime_five, ?_, ?_, fixtureWord_active_five⟩ <;>
    rw [fixtureWord_qstar] <;> norm_num

/-- **Superlogarithmic recurrence ≠ closure of polylogarithmic terminal windows.** -/
theorem reg_superlog_not_polylog (c : ℝ) (hc : 0 < c) (B : ℕ) (hB : 2 ≤ B) :
    ∃ D0 : ℝ, ∀ D : ℝ, D0 ≤ D → ∀ q : ℝ, 0 < q → q ≤ D / Real.log D ^ B →
      c * gRec (Real.log D) ≤ D / q :=
  polylog_window_not_excluded c hc B hB

/-- **Non-vacuity of the exact-word model.**  The trivial exact word `{1}` exists (with
`a = 1`, so it is not an Erdős #287 counterexample). -/
def trivialExactWord : ExactWord where
  A := {1}
  a := 1
  M := 1
  a_pos := by norm_num
  sub := by decide
  a_mem := by decide
  M_mem := by decide
  gap := by intro x h1 h2; omega
  mass := by norm_num

end Erdos287.PostV71V87
