import RequestProject.Erdos287.ClosureInputs

/-!
# Erdős #287 — core lemma for the finite `10^60` certificate

This file contains only the generic mathematics.  The long prime-pair certificate is kept in a
separate generated file so that the proof mechanism can be audited independently of the data.
-/

open scoped BigOperators

namespace Erdos287

/-- `CVal` is at most `11` on multiplier windows of size at most three. -/
theorem CVal_le_eleven_of_le_three {j : ℕ} (hj : j ≤ 3) : CVal j ≤ 11 := by
  interval_cases j <;> norm_num [CVal]

/-- A certified pair of primes `P = 2q - 1`, `q > 11`, supplies the two adjacent blocker
positions `P` and `P+1` for every maximum `M` in `[P+1, 2P]`.

This packages the elementary prime-pair interval argument directly into the already
kernel-checked `WindowPairSupply` interface. -/
theorem windowPairSupply_of_safePrimePair
    {q P M : ℕ}
    (hq : q.Prime) (hP : P.Prime) (hq11 : 11 < q)
    (hrel : P = 2 * q - 1)
    (hlo : P + 1 ≤ M) (hhi : M ≤ 2 * P) :
    WindowPairSupply M := by
  have hqpos : 0 < q := hq.pos
  have hPpos : 0 < P := hP.pos
  have hwu : M / P ^ 1 ≤ 2 := by
    rw [pow_one]
    exact div_le_of_lt_mul hPpos (by omega)
  have hwv : M / q ^ 1 ≤ 3 := by
    rw [pow_one]
    exact div_le_of_lt_mul hqpos (by omega)
  have hwu9 : M / P ^ 1 ≤ 9 := le_trans hwu (by omega)
  have hwv9 : M / q ^ 1 ≤ 9 := le_trans hwv (by omega)
  have hcu : CVal (M / P ^ 1) < P := by
    have hc := CVal_le_three_of_le_two hwu
    omega
  have hcv : CVal (M / q ^ 1) < q := by
    have hc := CVal_le_eleven_of_le_three hwv
    omega
  refine ⟨P, P, 1, q, 1, hP, hq, by omega, by omega, ?_, ?_, hwu9, hcu, hwv9, hcv, hhi, hlo⟩
  · simp
  · rw [pow_one]
    refine ⟨2, ?_⟩
    omega

/-- The same prime pair directly refutes a gap-at-most-two counterexample whose maximum
lies in its certified interval. -/
theorem Gap2CE.no_of_safePrimePair
    (ce : Gap2CE) {q P : ℕ}
    (hq : q.Prime) (hP : P.Prime) (hq11 : 11 < q)
    (hrel : P = 2 * q - 1)
    (hlo : P + 1 ≤ ce.M) (hhi : ce.M ≤ 2 * P) : False := by
  exact ce.no_of_windowPairSupply
    (windowPairSupply_of_safePrimePair hq hP hq11 hrel hlo hhi)

end Erdos287
