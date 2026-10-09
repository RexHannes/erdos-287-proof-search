import RequestProject.Erdos287.ResearchBankV23.SameWeightPrincipal
import RequestProject.Erdos287.ResearchBankV23.SingularFactors
import RequestProject.Erdos287.ResearchBankV23.GoodPrimeEulerFactor
import RequestProject.Erdos287.ResearchBankV22.PositiveSieveParameters
import RequestProject.Erdos287.ResearchBankV16.RouteCConsumer
import RequestProject.Erdos287.ResearchBankV14.ConditionalAsymptoticImplication
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Erdős #287 — Research Bank V23 §6: the principal Euler/Mellin provider and the SAME
# normalization theorem

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## Finite principal models (definitions)

`PrincipalModel h` bundles ONE finite principal CRT model: spectator / root-collision states
`Ys` with nonnegative weights `μ`, the sieve-prime universe `U`, conditional densities
`qY y p ∈ [0, min(1, h p)]` and a complex amplitude `B`.  `PrincipalModel.Mnew` and
`PrincipalModel.sifted` are the V23 functionals `M_new` and
`Li/(φ(A_i W0) N) · E[|B|² 1(L_j sifted)]` of that model; `pref Li phiW N M = Li(M)/(φ·N(M))`
is the principal prefactor with the frozen normalization `N`.

## EXTERNAL PROVIDER (interface only; never constructed)

`PrincipalEulerProvider` contains, with explicit fields:
* `euler_product` — the EXACT Euler product: generating function = exact exceptional local
  factor × `∏_{good p} E_p(s,t)` with the V23 good-prime factor `eulerFactor`;
* `zeta_simple_pole` — the simple pole of `ζ` at `1` with residue `1`
  (this field is DISCHARGED from Mathlib: `zeta_simple_pole_available`);
* `mellin_truncation` — Fourier/Mellin truncation error `o((log x)^{-r})`, in ε/eventual form;
* `mixed_derivative` — the mixed-derivative integral: truncated Mellin term
  `= (S_all/S_ij + o(1)) (log x)^{-r} L_ij(F)`;
* `normalization_agreement` — the provider's normalization `N` satisfies the frozen V14/V15
  `S0Contract` for the frozen `S0` (i.e. it IS the S0/S1 normalization);
* `sifted_main` — the sifted principal term tends to
  `S_i·(S_ij/S_i)·(S_all/S_ij)/S_all · e^{-γ}/b_z · L_ij(F)/I`, uniformly in the family index.

## LEAN CONDITIONAL / LEAN BANK consequences

* `zeta_simple_pole_available` (LEAN BANK, Mathlib) — the pole field is provable;
* `euler_product_at_zero` (LEAN BANK given the product field) — at zero parameters every good
  local factor is `(p-2-r)/(p-2)`;
* **`principal_euler_asymptotic`** (LEAN CONDITIONAL) —
  `|E_ij|A|² (log x)^r - S_all/S_ij · L_ij(F)| ≤ ε` eventually;
* **`same_normalization_sifted_main`** (LEAN CONDITIONAL) — with `N` the SAME frozen
  normalization used by S0/S1 (the statement carries `S0Contract (S0 τ W) N` for the frozen
  Route-C `S0`),

      Li/(φ(A_i W0) N) · E[|B|² 1(L_j sifted to z)] = e^{-γ}/b_z · L_ij(F)/I + o(1),

  the singular chain cancelling by `singular_cancellation` (no informal cancellation).
-/

namespace Erdos287
namespace ResearchBankV23
namespace PrincipalEuler

open Finset Filter
open ResearchBankV21.QuadraticDomination
open SameWeightPrincipal SingularFactors GoodPrimeEulerFactor
open ResearchBankV14.ConditionalAsymptoticImplication (S0Contract S1Contract)

/-- **One finite principal CRT model** (states, universe, conditional densities, amplitude). -/
structure PrincipalModel (h : ℕ → ℝ) where
  Ys : Type
  fin : Fintype Ys
  U : Finset ℕ
  μ : Ys → ℝ
  μ_nonneg : ∀ y, 0 ≤ μ y
  qY : Ys → U → ℝ
  q_nonneg : ∀ y p, 0 ≤ qY y p
  q_le_h : ∀ y p, qY y p ≤ h p
  q_le_one : ∀ y p, qY y p ≤ 1
  B : Ys → ℂ

attribute [instance] PrincipalModel.fin

namespace PrincipalModel

variable {h : ℕ → ℝ} (m : PrincipalModel h)

/-- `M_new` of the model for the weight `Λ`, with prefactor `pref`. -/
noncomputable def Mnew (pref : ℝ) (Λ : Finset ℕ → ℝ) : ℝ :=
  SameWeightPrincipal.Mnew m.U pref Λ m.μ m.qY m.B

/-- The sifted principal term of the model, with prefactor `pref`. -/
noncomputable def sifted (pref : ℝ) : ℝ :=
  SameWeightPrincipal.principalSifted m.U pref m.μ m.qY m.B

theorem sifted_nonneg {pref : ℝ} (hpref : 0 ≤ pref) : 0 ≤ m.sifted pref :=
  principalSifted_nonneg hpref m.μ_nonneg m.q_nonneg m.q_le_one m.B

end PrincipalModel

/-- The principal prefactor `Li(M) / (φ(A_i W0) · N(M))` with the frozen normalization `N`. -/
noncomputable def pref (Li : ℕ → ℝ) (phiW : ℝ) (N : ℕ → ℝ) (M : ℕ) : ℝ := Li M / (phiW * N M)

/-- The principal main-term constant `e^{-γ}/b_z`. -/
noncomputable def gConst : ℝ :=
  Real.exp (-Real.eulerMascheroniConstant) / (ResearchBankV22.PositiveSieveParameters.b_z : ℝ)

/-- **The principal Euler/Mellin provider** (EXTERNAL PROVIDER; never constructed). -/
structure PrincipalEulerProvider (h : ℕ → ℝ) (r : ℕ) (Sd : SingularData) (LF I : ℝ)
    (S0 N Li : ℕ → ℝ) (phiW : ℝ) (model : ℕ → ℕ → PrincipalModel h) where
  /-- generating Dirichlet series of the principal second moment (truncated at scale `M`) -/
  Zgen : ℕ → (Fin r → ℝ) → (Fin r → ℝ) → ℝ
  /-- the good primes at scale `M` -/
  good : ℕ → Finset ℕ
  /-- the exact local factor of the finitely many exceptional primes -/
  excLocal : ℕ → (Fin r → ℝ) → (Fin r → ℝ) → ℝ
  good_gt : ∀ M p, p ∈ good M → r + 2 < p
  euler_product : ∀ M s t, Zgen M s t = excLocal M s t * ∏ p ∈ good M, eulerFactor p r s t
  zeta_simple_pole :
    Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (nhdsWithin 1 {1}ᶜ) (nhds 1)
  /-- `E_ij |A_{e,x}|²` -/
  EA : ℕ → ℝ
  /-- the truncated Mellin integral -/
  mellin : ℕ → ℝ
  mellin_truncation : ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀,
    |EA M - mellin M| * Real.log M ^ r ≤ ε
  mixed_derivative : ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀,
    |mellin M * Real.log M ^ r - Sd.Sall / Sd.Sij * LF| ≤ ε
  Sall_ne : Sd.Sall ≠ 0
  normalization_agreement : S0Contract S0 N
  sifted_main : ∀ S : ℕ, ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀,
    |(model S M).sifted (pref Li phiW N M) -
      Sd.Si * (Sd.Sij / Sd.Si) * (Sd.Sall / Sd.Sij) / Sd.Sall * gConst * (LF / I)| ≤ ε

/-- **The zeta simple-pole field is provable** (LEAN BANK, from Mathlib). -/
theorem zeta_simple_pole_available :
    Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (nhdsWithin 1 {1}ᶜ) (nhds 1) :=
  riemannZeta_residue_one

/-- At zero parameters a good local factor is `(p - 2 - r)/(p - 2)`. -/
theorem eulerFactor_zero_value {p r : ℕ} (hp : 2 < p) :
    eulerFactor p r 0 0 = ((p : ℝ) - 2 - r) / ((p : ℝ) - 2) := by
  unfold eulerFactor
  simp only [Pi.zero_apply, add_zero, neg_zero, Real.rpow_zero, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : (p : ℝ) - 2 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp
    linarith
  field_simp
  ring

/-- **The exact Euler product at zero parameters** (LEAN BANK given the product field). -/
theorem euler_product_at_zero {h : ℕ → ℝ} {r : ℕ} {Sd : SingularData} {LF I : ℝ}
    {S0 N Li : ℕ → ℝ} {phiW : ℝ} {model : ℕ → ℕ → PrincipalModel h}
    (P : PrincipalEulerProvider h r Sd LF I S0 N Li phiW model) (M : ℕ) :
    P.Zgen M 0 0 = P.excLocal M 0 0 * ∏ p ∈ P.good M, (((p : ℝ) - 2 - r) / ((p : ℝ) - 2)) := by
  rw [P.euler_product]
  congr 1
  exact prod_congr rfl fun p hp => eulerFactor_zero_value (by have := P.good_gt M p hp; omega)

/-- **Principal Euler asymptotic** (LEAN CONDITIONAL):
`|E_ij|A_{e,x}|² (log x)^r - S_all/S_ij · L_ij(F)| ≤ ε` eventually. -/
theorem principal_euler_asymptotic {h : ℕ → ℝ} {r : ℕ} {Sd : SingularData} {LF I : ℝ}
    {S0 N Li : ℕ → ℝ} {phiW : ℝ} {model : ℕ → ℕ → PrincipalModel h}
    (P : PrincipalEulerProvider h r Sd LF I S0 N Li phiW model) :
    ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, |P.EA M * Real.log M ^ r - Sd.Sall / Sd.Sij * LF| ≤ ε := by
  intro ε hε
  obtain ⟨M1, h1⟩ := P.mellin_truncation (ε / 2) (by positivity)
  obtain ⟨M2, h2⟩ := P.mixed_derivative (ε / 2) (by positivity)
  refine ⟨max M1 M2, fun M hM => ?_⟩
  have a := h1 M (le_trans (le_max_left _ _) hM)
  have b := h2 M (le_trans (le_max_right _ _) hM)
  have e : P.EA M * Real.log M ^ r - Sd.Sall / Sd.Sij * LF =
      (P.EA M - P.mellin M) * Real.log M ^ r +
        (P.mellin M * Real.log M ^ r - Sd.Sall / Sd.Sij * LF) := by ring
  rw [e]
  have hlog : |(P.EA M - P.mellin M) * Real.log M ^ r| ≤ |P.EA M - P.mellin M| * Real.log M ^ r := by
    rw [abs_mul]
    gcongr
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by
      rcases M with _ | M
      · simp
      · rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast Nat.succ_pos M))]) r
  calc _ ≤ |(P.EA M - P.mellin M) * Real.log M ^ r| +
        |P.mellin M * Real.log M ^ r - Sd.Sall / Sd.Sij * LF| := abs_add_le _ _
    _ ≤ ε := by linarith

/-- The main-term constant after the exact singular cancellation. -/
theorem singular_chain_normalized (Sd : SingularData) (hSall : Sd.Sall ≠ 0) :
    Sd.Si * (Sd.Sij / Sd.Si) * (Sd.Sall / Sd.Sij) / Sd.Sall = 1 := by
  rw [singular_cancellation, div_self hSall]

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The SAME normalization theorem** (LEAN CONDITIONAL).  The normalization `N` in the
principal prefactor is the SAME frozen normalization used by the S0/S1 contracts: the
hypothesis `h0 : S0Contract (S0 τ W) N` is carried in the statement for the frozen Route-C
zeroth moment, and the provider is required to use the very same `S0`, `N`.  Then

    Li/(φ(A_i W0) N) · E[|B|² 1(L_j sifted to z)] = e^{-γ}/b_z · L_ij(F)/I + o(1)

(in ε/eventual form, uniformly for every family index `S`). -/
theorem same_normalization_sifted_main {h : ℕ → ℝ} {r : ℕ} {Sd : SingularData} {LF I : ℝ}
    (τ : ResearchBankV16.RouteCConsumer.FixedTupleC V)
    (W : ResearchBankV16.RouteCConsumer.WeightSystem τ) {N Li : ℕ → ℝ} {phiW : ℝ}
    {model : ℕ → ℕ → PrincipalModel h}
    (P : PrincipalEulerProvider h r Sd LF I (ResearchBankV16.RouteCConsumer.S0 τ W) N Li phiW
      model) :
    S0Contract (ResearchBankV16.RouteCConsumer.S0 τ W) N ∧
      ∀ S : ℕ, ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀,
        |(model S M).sifted (pref Li phiW N M) - gConst * (LF / I)| ≤ ε := by
  refine ⟨P.normalization_agreement, fun S ε hε => ?_⟩
  obtain ⟨M₀, hM⟩ := P.sifted_main S ε hε
  refine ⟨M₀, fun M hM' => ?_⟩
  have := hM M hM'
  rwa [singular_chain_normalized Sd P.Sall_ne, one_mul] at this

/-- `e^{-γ}/b_z ≤ 2` (used for the principal budget). -/
theorem gConst_pos_le_two : 0 < gConst ∧ gConst ≤ 2 := by
  have hb : (ResearchBankV22.PositiveSieveParameters.b_z : ℝ) = 501 / 1000 := by
    unfold ResearchBankV22.PositiveSieveParameters.b_z; push_cast; ring
  unfold gConst
  rw [hb]
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have he : Real.exp (-Real.eulerMascheroniConstant) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by norm_num)]
  linarith

end PrincipalEuler
end ResearchBankV23
end Erdos287
