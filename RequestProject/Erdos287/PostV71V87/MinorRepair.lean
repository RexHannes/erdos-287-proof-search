import RequestProject.Erdos287.PostV71V87.Model

/-!
# Erdős #287 — V83 repair: actual principal minors vs target-one substitutes (RETIRED route)

The V83 audit separated two quantities attached to a complement block `R`:

* the **actual** quantity `C_R`, computed with the true reciprocal mass `S = ∑ 1/n`; it is
  affine in `S` with integer slope `B_R` and integer offset `K_R`:  `C_R = B_R·S + K_R`;
* the **target-one substitute** `D_R = B_R + K_R`, obtained by substituting `S := 1`.

We prove

* `actual_sub_target`  — `C_R − D_R = B_R (S − 1)`;
* `den_intCast_mul`    — `den(B·S) = den(S) / gcd(den S, |B|)`;
* `den_actual`         — `den(C_R) = den(S) / gcd(den S, |B_R|)`;
* `actual_integral_iff` — `C_R ∈ ℤ ↔ den(S) ∣ B_R`;
* `fixed_depth_compression` — a whole family of fixed-depth complement-minor integrality
  tests is equivalent to the single condition `den(S) ∣ gcd_R B_R`;
* `fixed_depth_tests_pass_at_two` / `fixed_depth_not_exact_mass` — every such test passes at
  `S = 2`, realised by the reciprocal set `{1,2,3,6}`; fixed depths **never** imply exact
  mass one.  The hierarchy is therefore **RETIRED** as a closure route.
* `target_integral` — the target-one substitute is always integral, and
  `integer_det_integral` — the determinant of an actual integer matrix is automatically
  integral; so no "non-integral principal minor" claim may be made about an integer matrix.
-/

open scoped BigOperators

namespace Erdos287.PostV71V87

/-- Integer data of an affine minor `C = B·S + K`. -/
structure MinorData where
  /-- Slope (coefficient of the mass `S`). -/
  B : ℤ
  /-- Integer offset. -/
  K : ℤ

namespace MinorData

variable (m : MinorData)

/-- The actual quantity `C_R = B_R·S + K_R`. -/
def actual (S : ℚ) : ℚ := m.B * S + m.K

/-- The target-one substitute `D_R = B_R + K_R`. -/
def target : ℚ := m.B + m.K

/-- **`C_R − D_R = B_R (S − 1)`.** -/
theorem actual_sub_target (S : ℚ) : m.actual S - m.target = m.B * (S - 1) := by
  unfold actual target; ring

/-- The actual quantity agrees with the substitute exactly at `S = 1`, and in general
only when `B_R = 0` or `S = 1`. -/
theorem actual_eq_target_iff (S : ℚ) : m.actual S = m.target ↔ m.B = 0 ∨ S = 1 := by
  rw [← sub_eq_zero, actual_sub_target]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · simp [h]
    · simp [h]

end MinorData

/-- **Reduced denominator of an integer multiple.** `den(B·S) = den(S) / gcd(den S, |B|)`. -/
theorem den_intCast_mul (B : ℤ) (S : ℚ) :
    ((B : ℚ) * S).den = S.den / Nat.gcd S.den B.natAbs := by
  rw [Rat.mul_den]
  simp only [Rat.den_intCast, Rat.num_intCast, one_mul, Int.natAbs_mul]
  rw [Nat.Coprime.gcd_mul_right_cancel _ S.reduced, Nat.gcd_comm]

namespace MinorData

variable (m : MinorData)

/-- **`den(C_R) = den(S) / gcd(den(S), B_R)`.** -/
theorem den_actual (S : ℚ) : (m.actual S).den = S.den / Nat.gcd S.den m.B.natAbs := by
  unfold actual
  rw [Rat.add_intCast_den, den_intCast_mul]

/-- `d / gcd(d, b) = 1 ↔ d ∣ b` for `d > 0`. -/
theorem div_gcd_eq_one_iff {d b : ℕ} (hd : 0 < d) : d / Nat.gcd d b = 1 ↔ d ∣ b := by
  have hg : 0 < Nat.gcd d b := Nat.gcd_pos_of_pos_left _ hd
  constructor
  · intro h
    have h2 := Nat.div_mul_cancel (Nat.gcd_dvd_left d b)
    rw [h, one_mul] at h2
    rw [← Nat.gcd_eq_left_iff_dvd]
    exact h2
  · intro h
    rw [Nat.gcd_eq_left h, Nat.div_self hd]

/-- **Integrality of the actual quantity:** `C_R ∈ ℤ ↔ den(S) ∣ B_R`. -/
theorem actual_integral_iff (S : ℚ) : (m.actual S).den = 1 ↔ (S.den : ℤ) ∣ m.B := by
  rw [den_actual, div_gcd_eq_one_iff S.den_pos, Int.natCast_dvd]

/-- The target-one substitute is always integral (so it carries no information). -/
theorem target_integral : m.target.den = 1 := by
  unfold target
  rw [Rat.add_intCast_den]; simp

end MinorData

/-- **Fixed-depth compression.**  A finite family of complement-minor integrality tests is
equivalent to the single denominator condition `den(S) ∣ gcd_R B_R`. -/
theorem fixed_depth_compression {ι : Type*} (F : Finset ι) (m : ι → MinorData) (S : ℚ) :
    (∀ i ∈ F, ((m i).actual S).den = 1) ↔ (S.den : ℤ) ∣ F.gcd (fun i => (m i).B) := by
  simp_rw [MinorData.actual_integral_iff]
  exact Finset.dvd_gcd_iff.symm

/-- Every fixed-depth integrality test passes at `S = 2`. -/
theorem fixed_depth_tests_pass_at_two (m : MinorData) : (m.actual 2).den = 1 := by
  rw [MinorData.actual_integral_iff]
  simp

/-- The reciprocal set `{1,2,3,6}` has mass `2`. -/
theorem mass_one_two_three_six : ∑ n ∈ ({1, 2, 3, 6} : Finset ℕ), (1 : ℚ) / n = 2 := by
  norm_num

/-- **Fixed depths do not imply exact mass one.**  The genuine reciprocal set `{1,2,3,6}`
passes every complement-minor integrality test, at every depth, yet its mass is `2 ≠ 1`. -/
theorem fixed_depth_not_exact_mass :
    ∃ A : Finset ℕ, (∀ n ∈ A, 0 < n) ∧
      (∀ m : MinorData, (m.actual (∑ n ∈ A, (1 : ℚ) / n)).den = 1) ∧
      ∑ n ∈ A, (1 : ℚ) / n ≠ 1 := by
  refine ⟨{1, 2, 3, 6}, by decide, ?_, ?_⟩
  · intro m; rw [mass_one_two_three_six]; exact fixed_depth_tests_pass_at_two m
  · rw [mass_one_two_three_six]; norm_num

/-- **Actual integer-matrix determinants are automatically integral.**  For an integer
matrix, the determinant of its image in `ℚ` is the cast of an integer: a principal minor of
an integer matrix can never be "non-integral". -/
theorem integer_det_integral {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℤ) :
    ((Int.castRingHom ℚ).mapMatrix X).det = ((X.det : ℤ) : ℚ) ∧
      (((Int.castRingHom ℚ).mapMatrix X).det).den = 1 := by
  have h : ((Int.castRingHom ℚ).mapMatrix X).det = ((X.det : ℤ) : ℚ) :=
    (RingHom.map_det (Int.castRingHom ℚ) X).symm
  exact ⟨h, by rw [h]; simp⟩

end Erdos287.PostV71V87
