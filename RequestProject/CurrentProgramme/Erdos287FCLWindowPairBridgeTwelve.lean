import RequestProject.CurrentProgramme.Erdos287FCLWindowPairBridge

/-!
# The `FCL_W(M/2) → WindowPairSupply M` bridge at the sharp threshold `M ≥ 12`

```
FCL → WINDOWPAIR (threshold 12) : KERNEL-PROVED CONDITIONAL
```

This module is **append-only**: the banked threshold-`20` bridge
`Erdos287.FCLWindowPair.windowPairSupply_of_positiveFCLMass` is left untouched, and the
same, unchanged conditional input `PositiveFCLPrimeMassWitness` is reused.  What is added
is the sharper elementary threshold:

```
    for M ≥ 12,   FCL_W(M/2)  →  WindowPairSupply M .
```

The witness at the scale `X = M/2` supplies a prime `q` with `7M ≤ 20q ≤ 9M` (i.e.
`q ∈ [(7/10)X, (9/10)X]`) and a sign `s = ±1` with `2q + s = r^a`, `r` prime, `a ≥ 1`.
Both cases are treated:

```
    PLUS  : x = 2q,      p_u = q, a_u = 1,  p_v = r, a_v = a ;
    MINUS : x = 2q − 1,  p_u = r, a_u = a,  p_v = q, a_v = 1 .
```

Every literal field of `Erdos287.WindowPairSupply M` is discharged: primality of both
bases, positivity of both exponents, both divisibilities, both windows `M/q^e ≤ 9`, both
`CVal` inequalities, `M ≤ 2x` and `x + 1 ≤ M`.

At `M ≥ 12` the support condition already forces `q ≥ 5`, hence `CVal(M/q) ≤ 3 < q`; this
is exactly what makes the threshold `12` admissible.  The bridge remains **strictly
conditional**: nothing constructs the witness for general `M`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace FCLWindowPair

/-! ## §1  The sharp elementary facts at `M ≥ 12` -/

namespace PositiveFCLPrimeMassWitness

variable {M : ℕ} (h : PositiveFCLPrimeMassWitness M)

/-- At `M ≥ 12` the support condition forces `q ≥ 5`. -/
theorem q_ge_five (hM : 12 ≤ M) : 5 ≤ h.q := by
  have := h.q_lower
  omega

/-- At `M ≥ 12` the window of `q` is at most `2`. -/
theorem window_q_twelve (hM : 12 ≤ M) : M / h.q ≤ 2 := by
  have hq5 := h.q_ge_five hM
  refine Erdos287.div_le_of_lt_mul (by omega) ?_
  have := h.q_lower
  omega

end PositiveFCLPrimeMassWitness

/-! ## §2  The bridge at threshold `12` -/

/-- **`windowPairSupply_of_positiveFCLMass_twelve`.**  `KERNEL-PROVED CONDITIONAL`.

For every `M ≥ 12`, a positive-FCL-prime-mass witness at the scale `X = M/2` produces the
literal `Erdos287.WindowPairSupply M`, in both the plus and the minus case. -/
theorem windowPairSupply_of_positiveFCLMass_twelve {M : ℕ} (hM : 12 ≤ M)
    (h : PositiveFCLPrimeMassWitness M) : WindowPairSupply M := by
  have hq5 : 5 ≤ h.q := h.q_ge_five hM
  have hlo := h.q_lower
  have hhi := h.q_upper
  have hwq : M / h.q ^ 1 ≤ 2 := by
    rw [pow_one]; exact h.window_q_twelve hM
  have hcq : CVal (M / h.q ^ 1) < h.q := by
    have := Erdos287.CVal_le_three_of_le_two hwq
    omega
  have hwq9 : M / h.q ^ 1 ≤ 9 := by omega
  cases hs : h.s with
  | true =>
      -- PLUS case: `x = 2q`, `x + 1 = 2q + 1 = r^a`
      have hra : 2 * h.q + 1 = h.r ^ h.a := by
        have := h.lambda_pos; rwa [hs, if_pos rfl] at this
      have hwr : M / h.r ^ h.a ≤ 1 := by
        rw [← hra]
        exact Erdos287.div_le_of_lt_mul (by omega) (by omega)
      have hcr : CVal (M / h.r ^ h.a) < h.r := by
        have h1 := Erdos287.CVal_eq_one_of_le_one hwr
        have h2 := h.r_prime.two_le
        omega
      have hwr9 : M / h.r ^ h.a ≤ 9 := by omega
      refine ⟨2 * h.q, h.q, 1, h.r, h.a, h.q_prime, h.r_prime, le_rfl, h.a_pos,
        ⟨2, by rw [pow_one]; ring⟩, ⟨1, by rw [← hra, mul_one]⟩,
        hwq9, hcq, hwr9, hcr, by omega, by omega⟩
  | false =>
      -- MINUS case: `x = 2q − 1 = r^a`, `x + 1 = 2q`
      have hra : 2 * h.q - 1 = h.r ^ h.a := by
        have := h.lambda_pos; rwa [hs, if_neg (by simp)] at this
      have hrval : h.r ^ h.a + 1 = 2 * h.q := by omega
      have hwr : M / h.r ^ h.a ≤ 1 := by
        rw [← hra]
        exact Erdos287.div_le_of_lt_mul (by omega) (by omega)
      have hcr : CVal (M / h.r ^ h.a) < h.r := by
        have h1 := Erdos287.CVal_eq_one_of_le_one hwr
        have h2 := h.r_prime.two_le
        omega
      have hwr9 : M / h.r ^ h.a ≤ 9 := by omega
      refine ⟨2 * h.q - 1, h.r, h.a, h.q, 1, h.r_prime, h.q_prime, h.a_pos, le_rfl,
        ⟨1, by rw [← hra, mul_one]⟩, ⟨2, by rw [pow_one]; omega⟩,
        hwr9, hcr, hwq9, hcq, by omega, by omega⟩

/-- **Non-vacuity at the threshold.**  At `M = 12` the support condition forces `q = 5`,
and `2·5 + 1 = 11` is prime, so the plus case of the bridge fires at the threshold. -/
def witnessTwelve : PositiveFCLPrimeMassWitness 12 where
  q := 5
  q_prime := by decide
  q_lower := by norm_num
  q_upper := by norm_num
  s := true
  r := 11
  r_prime := by decide
  a := 1
  a_pos := le_rfl
  lambda_pos := by norm_num

/-- The threshold-`12` bridge really fires at `M = 12`. -/
theorem windowPairSupply_twelve : WindowPairSupply 12 :=
  windowPairSupply_of_positiveFCLMass_twelve le_rfl witnessTwelve

/-- **`bridge_threshold_is_twelve`.**  `KERNEL-PROVED`.

The threshold recorded by this layer is `12`, and it strictly improves the banked
threshold `20` while proving the same conclusion from the same input. -/
theorem bridge_threshold_is_twelve :
    (12 : ℕ) < 20 ∧
    ∀ M : ℕ, 12 ≤ M → PositiveFCLPrimeMassWitness M → WindowPairSupply M :=
  ⟨by norm_num, fun _ hM h => windowPairSupply_of_positiveFCLMass_twelve hM h⟩

/-- **`threshold_twelve_subsumes_threshold_twenty`.**  `KERNEL-PROVED`.

Every input accepted by the banked threshold-`20` bridge is accepted here, with the same
conclusion; the older statement is retained, not replaced. -/
theorem threshold_twelve_subsumes_threshold_twenty {M : ℕ} (hM : 20 ≤ M)
    (h : PositiveFCLPrimeMassWitness M) :
    WindowPairSupply M ∧ WindowPairSupply M :=
  ⟨windowPairSupply_of_positiveFCLMass hM h,
    windowPairSupply_of_positiveFCLMass_twelve (by omega) h⟩

/-- **`bridge_needs_the_support_condition`.**  `KERNEL-PROVED`.

The bridge is genuinely conditional on the FCL support data: at `M = 12` no witness can
carry `q = 3`, since `7·12 ≤ 20·3` fails. -/
theorem bridge_needs_the_support_condition :
    ¬ ∃ h : PositiveFCLPrimeMassWitness 12, h.q = 3 := by
  rintro ⟨h, hq⟩
  have := h.q_lower
  omega

end FCLWindowPair
end Erdos287
