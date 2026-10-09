import RequestProject.Erdos287.PostV64V71.CircleIdentity
import RequestProject.Erdos287.PostV64V71.FingerprintLogBudget
import RequestProject.Erdos287.PostV64V71.LocalAdmissibility

/-!
# Erdős #287 — V71 analytic frontier: providers, effectivity firewall, minor-arc route

**Every proposition defined in this file is a named interface.  None is proved, asserted,
or instantiated anywhere in the repository.**

| interface | mathematical status | formal status |
|---|---|---|
| `SiegelWalfiszLogModuli287` | known theorem (constants ineffective) | EXTERNAL / UNINHABITED |
| `AverageSingularSeries287 C₂` | paper proof | PAPER-LEVEL / UNINHABITED |
| `EventualMajorArc287` | PAY (paper proof via Siegel–Walfisz) | PAPER-LEVEL / UNINHABITED |
| `EffectiveMajorArc287 onset c` | **not established** (needs effective SW) | UNINHABITED |
| `MinorArcLowerBound287` | **OPEN** (proposed route) | OPEN |
| `D2LogBound287` | paper estimate | PAPER-LEVEL / UNINHABITED |
| `HuangFiniteExclusion287` | external certificate, **absent** | EXTERNAL / UNINHABITED |

Proved here:

* `Hcan_ge_twelve` — `Hcan M ≥ 12` for `M ≥ 2^1500` (so `K = ⌊H/4⌋ ≥ 3`, `log K ≥ 1`);
* `minor_plus_effective_major_implies_supply` — an *effective* major-arc lower bound
  `C_major ≥ c M (log K)²` (`c ≥ 1/4 + 1/1000`) with onset `≤ 2^1500`, together with
  `MinorArcLowerBound287`, implies `DeterminantSupply287`;
* `effectivity_firewall` — an eventual statement `∃ M₀, ∀ M ≥ M₀, P M` does **not** in general
  imply the fixed-onset statement `∀ M ≥ 2^1500, P M` (explicit counter-predicate);
* `splice_requires_explicit_onset` — a tail exclusion above `M₀` splices with a finite exclusion
  up to `U` only under the explicit overlap `M₀ ≤ U + 1`.
-/

open scoped BigOperators

namespace Erdos287.PostV64V71

open Erdos287 Erdos287.PostQSigma

/-- `ψ(x; q, a) = ∑_{n ≤ x, n ≡ a (mod q)} Λ(n)`. -/
noncomputable def psiAP (x : ℝ) (q a : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q), LambdaW n

/-- **Siegel–Walfisz for logarithmic moduli** (KNOWN EXTERNAL MATHEMATICS, NOT FORMALISED; the
constants `C(A)` are ineffective). -/
def SiegelWalfiszLogModuli287 : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → ∀ q a : ℕ, 1 ≤ q →
    (q : ℝ) ≤ Real.log x ^ A → Nat.Coprime a q →
    |psiAP x q a - x / (Nat.totient q)| ≤ C * x / Real.log x ^ A

/-- **Average of the singular series** (PAPER-LEVEL / UNINHABITED):
`∑_{k,t ≤ K} S(k,t)/(kt) = (log K)² + O(log K)` and `≥ (3/8) log(K/2) log K`. -/
def AverageSingularSeries287 (C2 : ℝ) : Prop :=
  (∃ C : ℝ, ∀ K : ℕ, 2 ≤ K →
    |∑ k ∈ Finset.Icc 1 K, ∑ t ∈ Finset.Icc 1 K, singularSeries C2 k t / ((k : ℝ) * t) -
      Real.log K ^ 2| ≤ C * Real.log K) ∧
  (∀ K : ℕ, 2 ≤ K →
    3 / 8 * Real.log ((K : ℝ) / 2) * Real.log K ≤
      ∑ k ∈ Finset.Icc 1 K, ∑ t ∈ Finset.Icc 1 K, singularSeries C2 k t / ((k : ℝ) * t))

/-- `K(M) = ⌊Hcan M / 4⌋`. -/
noncomputable def Kcan (M : ℕ) : ℕ := Hcan M / 4

/-- **Eventual major-arc asymptotic** `C_major = (1/2 + o(1)) M (log K)²` (PAPER-LEVEL; the proof
uses Siegel–Walfisz and is *ineffective*). -/
def EventualMajorArc287 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    |Cmajor M (Kcan M) (majorArcsV71 M) - (M : ℝ) * Real.log (Kcan M) ^ 2 / 2| ≤
      δ * M * Real.log (Kcan M) ^ 2

/-- **Effective major-arc lower bound with explicit onset** (NOT ESTABLISHED; must not be
inferred from `EventualMajorArc287`). -/
def EffectiveMajorArc287 (onset : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, onset ≤ M → c * M * Real.log (Kcan M) ^ 2 ≤ Cmajor M (Kcan M) (majorArcsV71 M)

/-- **Signed minor-arc lower bound** (OPEN; proposed route to `DeterminantSupply287`). -/
def MinorArcLowerBound287 : Prop :=
  ∀ M : ℕ, 2 ^ 1500 ≤ M →
    -(1 / 4 : ℝ) * M * Real.log (Kcan M) ^ 2 ≤ Cminor M (Kcan M) (majorArcsV71 M)

/-- **V68/V69 residual-denominator size** (PAPER-LEVEL / UNINHABITED):
`log D₂(M) < 0.872 M / log M` for `M ≥ 2^1500`. -/
def D2LogBound287 : Prop :=
  ∀ M : ℕ, 2 ^ 1500 ≤ M → Real.log (D2 M (Hcan M)) < 872 / 1000 * M / Real.log M

/-- **Huang finite certificate interface** (EXTERNAL / UNINHABITED; the ≈502-digit certificate
is not in the repository). -/
def HuangFiniteExclusion287 : Prop := ∃ U : ℕ, 2 ^ 1500 ≤ U + 1 ∧ FiniteExclusionUpTo U

/-! ## Proved bridges -/

/-- `Hcan M ≥ 12` for `M ≥ 2^1500`. -/
theorem Hcan_ge_twelve {M : ℕ} (hM : 2 ^ 1500 ≤ M) : 12 ≤ Hcan M := by
  have hL := log_ge_of_large hM
  have h6 := log_le_div_twelve hL
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  unfold Hcan
  apply Nat.le_floor
  rw [le_div_iff₀ (by linarith)]
  push_cast
  nlinarith

/-- `log K ≥ 1` for `M ≥ 2^1500`. -/
theorem one_le_log_Kcan {M : ℕ} (hM : 2 ^ 1500 ≤ M) : 1 ≤ Real.log (Kcan M) := by
  have h12 := Hcan_ge_twelve hM
  have hK : 3 ≤ Kcan M := by unfold Kcan; omega
  have hK' : (3 : ℝ) ≤ Kcan M := by exact_mod_cast hK
  have he := Real.exp_one_lt_d9
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith

/-- **Effective major arc + signed minor arc ⇒ `DeterminantSupply287`.**  Requires an explicit
onset `≤ 2^1500` and constant `c ≥ 1/4 + 1/1000`. -/
theorem minor_plus_effective_major_implies_supply {onset : ℕ} {c : ℝ}
    (hmaj : EffectiveMajorArc287 onset c) (honset : onset ≤ 2 ^ 1500)
    (hc : 1 / 4 + 1 / 1000 ≤ c) (hmin : MinorArcLowerBound287) : DeterminantSupply287 := by
  intro M hM
  have hL := log_ge_of_large hM
  have hlogK := one_le_log_Kcan hM
  have hM1 : 1 ≤ M := le_trans Nat.one_le_two_pow hM
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have hdec := major_minor_exact_decomposition_V71 M (Kcan M)
  have hCK : CK M (Kcan M) ≤ DLambda M (Hcan M) := weighted_subbox_le_full_supply_quarter M _
  have h1 := hmaj M (Nat.le_trans honset hM)
  have h2 := hmin M hM
  clear hmaj hmin honset hM hM1
  set LK := Real.log (Kcan M)
  set L := Real.log M
  have hLK2 : 1 ≤ LK ^ 2 := one_le_pow₀ hlogK
  have hlow : (1 / 1000 : ℝ) * M ≤ DLambda M (Hcan M) := by
    have : (c - 1 / 4) * M * LK ^ 2 ≤ DLambda M (Hcan M) := by nlinarith
    have h3 : (1 / 1000 : ℝ) * M ≤ (c - 1 / 4) * M * LK ^ 2 := by
      have : (1 / 1000 : ℝ) * M * 1 ≤ (c - 1 / 4) * M * LK ^ 2 := by
        apply mul_le_mul _ hLK2 (by norm_num) (by nlinarith)
        exact mul_le_mul_of_nonneg_right (by linarith) hM0.le
      linarith
    linarith
  have hL3 : (13000 : ℝ) < L ^ 3 := by
    have : (1039 : ℝ) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL.le 3
    norm_num at this; linarith
  have : 13 * (M : ℝ) / L ^ 3 < 1 / 1000 * M := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Effectivity firewall.**  The eventual form does not imply the fixed-onset form in general:
the predicate `P M := 2^1500 < M` holds eventually but fails at `M = 2^1500`. -/
theorem effectivity_firewall_general (B : ℕ) :
    ¬ ∀ P : ℕ → Prop, (∃ M₀ : ℕ, ∀ M, M₀ ≤ M → P M) → ∀ M : ℕ, B ≤ M → P M := by
  intro h
  exact lt_irrefl B (h (fun M => B < M) ⟨B + 1, fun M hM => hM⟩ B le_rfl)

theorem effectivity_firewall :
    ¬ ∀ P : ℕ → Prop, (∃ M₀ : ℕ, ∀ M, M₀ ≤ M → P M) → ∀ M : ℕ, 2 ^ 1500 ≤ M → P M :=
  effectivity_firewall_general (2 ^ 1500)

/-- **Splice requires an explicit onset.**  A tail exclusion above `M₀` and a finite exclusion up
to `U` combine to the full statement only under the explicit overlap condition `M₀ ≤ U + 1`. -/
theorem splice_requires_explicit_onset {U M₀ : ℕ} (hfin : FiniteExclusionUpTo U)
    (htail : NoCounterexampleAbove M₀) (hov : M₀ ≤ U + 1) :
    ∀ A : Finset ℕ, ¬ Erdos287Counterexample A := by
  intro A hA
  have := hfin A hA
  exact htail A hA (by omega)

/-- The conditional global theorem along the proposed analytic route (every hypothesis is an
open or external interface). -/
theorem erdos287_of_analytic_route (hfin : HuangFiniteExclusion287) {onset : ℕ} {c : ℝ}
    (hmaj : EffectiveMajorArc287 onset c) (honset : onset ≤ 2 ^ 1500)
    (hc : 1 / 4 + 1 / 1000 ≤ c) (hmin : MinorArcLowerBound287) (hlcm : LcmUpperBound12) :
    ∀ A : Finset ℕ, ¬ Erdos287Counterexample A := by
  obtain ⟨U, hU, hfinU⟩ := hfin
  exact splice_requires_explicit_onset hfinU
    (determinant_supply_implies_no_tail'
      (minor_plus_effective_major_implies_supply hmaj honset hc hmin) hlcm) hU

end Erdos287.PostV64V71
