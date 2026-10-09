import Mathlib
import RequestProject.Erdos287.BsrcWeights

/-!
# Erdős #287 effectivity — the γ parameters and the high-prime admission set (§42)

```
EXACT RATIONAL PARAMETERS            : KERNEL-PROVED
gamma = a0 + nu/2                    : KERNEL-PROVED
4 nu > gamma                         : KERNEL-PROVED
|H(z)| ≤ 3                           : KERNEL-PROVED (under the exact threshold hypotheses)
e(z) = 1 − C2(z) + 2 C3(z)           : KERNEL-PROVED (all cases j = 0,1,2,3)
COEFFICIENT +2 IS FORCED             : KERNEL-PROVED
NO j ≥ 4 CASE                        : KERNEL-PROVED
C3 SOURCE TYPING                     : KERNEL-PROVED
|2 R[C3]| / B_X < 1.1e-10            : CERTIFICATE-BACKED (never a theorem here)
ERDŐS #287                           : OPEN
```

The exact rational parameters of the current chart are

    ε  = 1/(2·10²¹),      ν = 16623/100000 − 2ε,
    γ  = 1/2 − ε,         a₀ = 83377/200000,

with the two structural identities `γ = a₀ + ν/2` and `4ν > γ` kernel-proved in exact
rational arithmetic; **no floating point occurs in any statement**.

The high-prime admission set is

    H(z) = { p prime : p > 2, p ∣ z, p ≥ N_z^ν },      N_z = z^{1/γ}.

Following the instruction to separate the *arithmetic* finite prime set from the
*threshold order* hypotheses, `HighPrimeData` carries the finite set `H`, an abstract real
threshold `T` (the physical value is `T = N_z^ν`), and the two order hypotheses
`T ≤ p` for `p ∈ H` and `z < T⁴`.  `highPrimeCount_le_three` then proves `|H| ≤ 3`, and
`admission_threshold_pow` supplies the physical instance of `z < T⁴` from `4ν > γ`.
**`ν` is never replaced by `ν/2`.**

The inclusion–exclusion layer is combinatorial and exact: `C2` counts the qualifying
*unordered* high-prime pairs (2-element subsets of `H`), `C3` is the indicator of the exact
three-high-prime exceptional case (all three pairs qualifying), and

    e(z) = 1 − C2(z) + 2 C3(z)

is verified in each of the four admissible cases `|H| = 0,1,2,3`; `admissionE_coeff_two_forced`
shows the coefficient `+2` is the unique one annihilating the exceptional case, and
`admission_no_four_case` shows no `j ≥ 4` case is source-admissible.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §42.1  The exact rational parameters -/

/-- `ε = 1/(2·10²¹)`, exact rational. -/
def epsPar : ℚ := 1 / (2 * 10 ^ 21)

/-- `ν = 16623/100000 − 2ε`, exact rational. -/
def nuPar : ℚ := 16623 / 100000 - 2 * epsPar

/-- `γ = 1/2 − ε`, exact rational. -/
def gammaPar : ℚ := 1 / 2 - epsPar

/-- `a₀ = 83377/200000`, exact rational. -/
def a0Par : ℚ := 83377 / 200000

/-- **`gammaPar_eq_a0_add_half_nu`.**  `KERNEL-PROVED`.  `γ = a₀ + ν/2`. -/
theorem gammaPar_eq_a0_add_half_nu : gammaPar = a0Par + nuPar / 2 := by
  unfold gammaPar a0Par nuPar epsPar; norm_num

/-- **`four_nuPar_gt_gammaPar`.**  `KERNEL-PROVED`.  `4ν > γ`. -/
theorem four_nuPar_gt_gammaPar : gammaPar < 4 * nuPar := by
  unfold gammaPar nuPar epsPar; norm_num

/-- **`gammaPar_pos`.**  `KERNEL-PROVED`. -/
theorem gammaPar_pos : 0 < gammaPar := by unfold gammaPar epsPar; norm_num

/-- **`nuPar_pos`.**  `KERNEL-PROVED`. -/
theorem nuPar_pos : 0 < nuPar := by unfold nuPar epsPar; norm_num

/-- **`nuPar_lt_gammaPar`.**  `KERNEL-PROVED`.  A qualifying high prime is a genuine
restriction: `ν < γ`, so `N_z^ν < N_z^γ = z`. -/
theorem nuPar_lt_gammaPar : nuPar < gammaPar := by unfold nuPar gammaPar epsPar; norm_num

/-! ## §42.2  The real threshold `N_z^ν` -/

/-- The real exponent `γ`. -/
noncomputable def gammaR : ℝ := (gammaPar : ℝ)

/-- The real exponent `ν`. -/
noncomputable def nuR : ℝ := (nuPar : ℝ)

theorem gammaR_pos : 0 < gammaR := by
  have : (0 : ℚ) < gammaPar := gammaPar_pos
  simpa [gammaR] using (by exact_mod_cast this : (0 : ℝ) < (gammaPar : ℝ))

theorem four_nuR_gt_gammaR : gammaR < 4 * nuR := by
  have : (gammaPar : ℚ) < 4 * nuPar := four_nuPar_gt_gammaPar
  have := (by exact_mod_cast this : ((gammaPar : ℝ)) < 4 * (nuPar : ℝ))
  simpa [gammaR, nuR] using this

/-- `N_z = z^{1/γ}`. -/
noncomputable def Nz (z : ℝ) : ℝ := z ^ (1 / gammaR)

/-- **`admission_threshold_pow`.**  `KERNEL-PROVED`.  The exact reason four qualifying high
primes are impossible: with `T = N_z^ν` one has `z < T⁴`, because `4ν/γ > 1`.  This is where
`4ν > γ` is used, and `ν` is **not** replaced by `ν/2`. -/
theorem admission_threshold_pow {z : ℝ} (hz : 1 < z) : z < (Nz z ^ nuR) ^ (4 : ℕ) := by
  have hz0 : (0 : ℝ) < z := lt_trans zero_lt_one hz
  have hpow : Nz z ^ nuR = z ^ (nuR / gammaR) := by
    rw [Nz, ← Real.rpow_mul hz0.le]
    congr 1
    ring
  have h4 : (z ^ (nuR / gammaR)) ^ (4 : ℕ) = z ^ (4 * nuR / gammaR) := by
    rw [← Real.rpow_natCast (z ^ (nuR / gammaR)) 4, ← Real.rpow_mul hz0.le]
    ring_nf
  have hexp : (1 : ℝ) < 4 * nuR / gammaR := by
    rw [lt_div_iff₀ gammaR_pos, one_mul]
    exact four_nuR_gt_gammaR
  calc z = z ^ (1 : ℝ) := (Real.rpow_one z).symm
    _ < z ^ (4 * nuR / gammaR) := by
        exact Real.rpow_lt_rpow_left_iff hz |>.2 hexp
    _ = (Nz z ^ nuR) ^ (4 : ℕ) := by rw [hpow, h4]

/-! ## §42.3  The high-prime admission set and `|H(z)| ≤ 3` -/

/-- The arithmetic/threshold data of the high-prime admission set at a fixed `z`.  The finite
prime set `H` is *arithmetic*; the threshold `T` (physically `N_z^ν`) enters only through the
two explicit order hypotheses. -/
structure HighPrimeData where
  /-- The modulus `z`. -/
  z : ℕ
  /-- The real threshold; physically `T = N_z^ν`. -/
  T : ℝ
  /-- The finite set of qualifying high primes. -/
  H : Finset ℕ
  /-- `z` is positive. -/
  hz : 0 < z
  /-- The threshold is positive. -/
  hT : 0 < T
  /-- Each member is an odd prime dividing `z` and at least the threshold. -/
  hmem : ∀ p ∈ H, p.Prime ∧ 2 < p ∧ p ∣ z ∧ T ≤ (p : ℝ)
  /-- The threshold order hypothesis `z < T⁴` (supplied physically by `admission_threshold_pow`). -/
  hT4 : (z : ℝ) < T ^ (4 : ℕ)

/-- **`highPrimeCount_le_three`.**  `KERNEL-PROVED`.  At most three primes qualify: four
distinct qualifying primes would have product `≥ T⁴ > z`, contradicting that their product
divides `z`. -/
theorem highPrimeCount_le_three (D : HighPrimeData) : D.H.card ≤ 3 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (show 4 ≤ D.H.card by omega)
  have hprime : ∀ p ∈ S, Prime p := fun p hp =>
    Nat.Prime.prime (D.hmem p (hSsub hp)).1
  have hdvd : ∀ p ∈ S, p ∣ D.z := fun p hp => (D.hmem p (hSsub hp)).2.2.1
  have hprod_dvd : (∏ p ∈ S, p) ∣ D.z := Finset.prod_primes_dvd _ hprime hdvd
  have hprod_le : (∏ p ∈ S, p) ≤ D.z := Nat.le_of_dvd D.hz hprod_dvd
  have hprodR : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (D.z : ℝ) := by exact_mod_cast hprod_le
  have hTle : D.T ^ (4 : ℕ) ≤ ((∏ p ∈ S, p : ℕ) : ℝ) := by
    have hcast : ((∏ p ∈ S, p : ℕ) : ℝ) = ∏ p ∈ S, (p : ℝ) := by push_cast; ring
    rw [hcast]
    have hconst : ∏ _p ∈ S, D.T = D.T ^ (4 : ℕ) := by
      rw [Finset.prod_const, hScard]
    rw [← hconst]
    refine Finset.prod_le_prod (fun p _ => D.hT.le) (fun p hp => ?_)
    exact (D.hmem p (hSsub hp)).2.2.2
  linarith [D.hT4]

/-- **`highPrime_four_impossible`.**  `KERNEL-PROVED`.  Restated: no four distinct qualifying
high primes exist. -/
theorem highPrime_four_impossible (D : HighPrimeData) : ¬ (4 ≤ D.H.card) := by
  have := highPrimeCount_le_three D; omega

/-! ## §42.4  Admission inclusion–exclusion -/

/-- The qualifying *unordered* high-prime pairs: 2-element subsets of `H` satisfying the
source's pair condition. -/
def qualPairs (H : Finset ℕ) (pc : Finset ℕ → Bool) : Finset (Finset ℕ) :=
  (H.powersetCard 2).filter (fun s => pc s = true)

/-- `C2(z)`: the number of qualifying unordered high-prime pairs. -/
def admC2 (H : Finset ℕ) (pc : Finset ℕ → Bool) : ℤ := (qualPairs H pc).card

/-- `C3(z)`: the indicator of the exact three-high-prime exceptional case (three high primes,
all three pairs qualifying). -/
def admC3 (H : Finset ℕ) (pc : Finset ℕ → Bool) : ℤ :=
  if H.card = 3 ∧ (qualPairs H pc).card = 3 then 1 else 0

/-- The admission `e(z) = 1 − C2(z) + 2 C3(z)`. -/
def admissionE (H : Finset ℕ) (pc : Finset ℕ → Bool) : ℤ :=
  1 - admC2 H pc + 2 * admC3 H pc

/-- **`gammaAdmission_inclusion_exclusion`.**  `KERNEL-PROVED`.  The admission is exactly the
inclusion–exclusion combination `1 − C2 + 2 C3`, and its value in each of the four admissible
cases `j = |H| ∈ {0,1,2,3}` is determined:

* `j = 0` and `j = 1`: no pairs at all, so `e = 1`;
* `j = 2`: `C3 = 0` and `e = 1 − C2` with `C2 ≤ 1`;
* `j = 3`: `C2 ≤ 3` and `e = 1 − C2 + 2 C3`, with `e = 0` exactly in the exceptional case. -/
theorem gammaAdmission_inclusion_exclusion (H : Finset ℕ) (pc : Finset ℕ → Bool) :
    admissionE H pc = 1 - admC2 H pc + 2 * admC3 H pc ∧
      (H.card = 0 → admC2 H pc = 0 ∧ admC3 H pc = 0 ∧ admissionE H pc = 1) ∧
      (H.card = 1 → admC2 H pc = 0 ∧ admC3 H pc = 0 ∧ admissionE H pc = 1) ∧
      (H.card = 2 → admC2 H pc ≤ 1 ∧ admC3 H pc = 0 ∧ admissionE H pc = 1 - admC2 H pc) ∧
      (H.card = 3 → admC2 H pc ≤ 3 ∧
        admissionE H pc = 1 - admC2 H pc + 2 * admC3 H pc) := by
  have hcard : (qualPairs H pc).card ≤ H.card.choose 2 := by
    refine le_trans (Finset.card_filter_le _ _) ?_
    rw [Finset.card_powersetCard]
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro h
    have h0 : (qualPairs H pc).card = 0 := by
      have := hcard; rw [h] at this; simpa using this
    refine ⟨by simp [admC2, h0], by simp [admC3, h, h0], by simp [admissionE, admC2, admC3, h, h0]⟩
  · intro h
    have h0 : (qualPairs H pc).card = 0 := by
      have := hcard; rw [h] at this; simpa using this
    refine ⟨by simp [admC2, h0], by simp [admC3, h, h0], by simp [admissionE, admC2, admC3, h, h0]⟩
  · intro h
    have h1 : (qualPairs H pc).card ≤ 1 := by
      have := hcard; rw [h] at this; simpa using this
    refine ⟨by simpa [admC2] using (by exact_mod_cast h1 : ((qualPairs H pc).card : ℤ) ≤ 1), ?_, ?_⟩
    · simp [admC3, h]
    · simp [admissionE, admC3, h]
  · intro h
    have h3 : (qualPairs H pc).card ≤ 3 := by
      have := hcard; rw [h] at this; simpa using this
    exact ⟨by simpa [admC2] using (by exact_mod_cast h3 : ((qualPairs H pc).card : ℤ) ≤ 3), rfl⟩

/-- **`admissionE_exceptional_case`.**  `KERNEL-PROVED`.  In the exceptional three-high-prime
case (three qualifying pairs) the admission vanishes: `1 − 3 + 2·1 = 0`. -/
theorem admissionE_exceptional_case {H : Finset ℕ} {pc : Finset ℕ → Bool}
    (h3 : H.card = 3) (hp : (qualPairs H pc).card = 3) : admissionE H pc = 0 := by
  simp [admissionE, admC2, admC3, h3, hp]

/-- **`admissionE_coeff_two_forced`.**  `KERNEL-PROVED`.  The coefficient `+2` in the `j = 3`
term is forced: `1 − 3 + c = 0` holds precisely for `c = 2`, so no other correction
annihilates the exceptional case. -/
theorem admissionE_coeff_two_forced (c : ℤ) :
    ((1 : ℤ) - 3 + c * 1 = 0) ↔ c = 2 := by omega

/-- **`admission_no_four_case`.**  `KERNEL-PROVED`.  No `j ≥ 4` case is source-admissible,
because the qualifying high-prime count is at most three. -/
theorem admission_no_four_case (D : HighPrimeData) (pc : Finset ℕ → Bool) :
    ¬ (4 ≤ D.H.card) ∧
      (D.H.card = 0 ∨ D.H.card = 1 ∨ D.H.card = 2 ∨ D.H.card = 3) ∧
      admissionE D.H pc = 1 - admC2 D.H pc + 2 * admC3 D.H pc := by
  have h := highPrimeCount_le_three D
  exact ⟨by omega, by omega, rfl⟩

/-- **`admC3_endpoint_firewall`.**  `KERNEL-PROVED`.  Endpoint firewalls: `C3` can only fire
in the exact three-high-prime case with all three pairs qualifying, and it never fires when
fewer than three high primes are present. -/
theorem admC3_endpoint_firewall (H : Finset ℕ) (pc : Finset ℕ → Bool) :
    (admC3 H pc = 1 → H.card = 3 ∧ (qualPairs H pc).card = 3) ∧
      (H.card ≤ 2 → admC3 H pc = 0) ∧
      (admC3 H pc = 0 ∨ admC3 H pc = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    by_cases hc : H.card = 3 ∧ (qualPairs H pc).card = 3
    · exact hc
    · rw [admC3, if_neg hc] at h; exact absurd h (by norm_num)
  · intro h
    have : ¬ (H.card = 3 ∧ (qualPairs H pc).card = 3) := by omega
    simp [admC3, this]
  · by_cases hc : H.card = 3 ∧ (qualPairs H pc).card = 3 <;> simp [admC3, hc]

/-- **`admissionE_no_high_primes`.**  `KERNEL-PROVED`.  With no qualifying high prime the
admission is the trivial `1`: the correction layer is genuinely a correction. -/
theorem admissionE_no_high_primes (pc : Finset ℕ → Bool) : admissionE ∅ pc = 1 :=
  ((gammaAdmission_inclusion_exclusion ∅ pc).2.1 (by simp)).2.2

/-! ## §42.5  `C3` source typing -/

/-- Named owners in the admission layer.  The auxiliary `C3` inclusion–exclusion correction is
a **separate** object from any historical physical "three-high" owner. -/
inductive AdmissionOwner
  | c3InclusionExclusionCorrection
  | historicalThreeHighPhysical
  | pairCorrectionC2
  deriving DecidableEq, Repr

/-- **`c3_source_typing`.**  `KERNEL-PROVED`.  The auxiliary `C3` correction is not the
historical three-high owner, and not the pair correction either: the three owners are
pairwise distinct names, so no charge may be transferred between them by name alone. -/
theorem c3_source_typing :
    AdmissionOwner.c3InclusionExclusionCorrection ≠ AdmissionOwner.historicalThreeHighPhysical ∧
      AdmissionOwner.c3InclusionExclusionCorrection ≠ AdmissionOwner.pairCorrectionC2 ∧
      AdmissionOwner.historicalThreeHighPhysical ≠ AdmissionOwner.pairCorrectionC2 := by
  refine ⟨by decide, by decide, by decide⟩

/-- A typed numerical certificate for the `C3` remainder allocation. -/
structure C3Certificate where
  /-- The claimed ratio `|2 R[C3]| / B_X`. -/
  ratio : ℚ
  /-- The certified strict upper bound (`1.1e-10`). -/
  bound : ℚ
  /-- The certificate hypothesis, supplied externally. -/
  certified : ratio < bound

/-- The declared `C3` allocation `1.1e-10`, as an exact rational. -/
def c3Allocation : ℚ := 11 / 10 ^ 11

/-- **`c3Allocation_value`.**  `KERNEL-PROVED`.  Only the exact rational value is kernel
content. -/
theorem c3Allocation_value : c3Allocation = 11 / 10 ^ 11 := rfl

/-- **`c3Certificate_not_proved`.**  `KERNEL-PROVED`.  Inhabiting a `C3Certificate` carries no
analytic content: the structure is satisfiable by data unrelated to the physical `R[C3]`, so
it never proves the physical bound. -/
theorem c3Certificate_not_proved : ∃ C : C3Certificate, C.bound = c3Allocation ∧ C.ratio = 0 :=
  ⟨⟨0, c3Allocation, by unfold c3Allocation; norm_num⟩, rfl, rfl⟩

end Effectivity
end Erdos287
