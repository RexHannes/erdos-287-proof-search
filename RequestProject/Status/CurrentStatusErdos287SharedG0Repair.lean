import Mathlib
import RequestProject.Status.CurrentStatusErdos287PrimitiveLocalProfile
import RequestProject.CurrentProgramme.LocalProfileHarmonicTwists
import RequestProject.CurrentProgramme.SharedG0PrimitiveUParam
import RequestProject.CurrentProgramme.SharedG0PrimitiveURouter
import RequestProject.CurrentProgramme.SharedG0UnitSectorGcd
import RequestProject.CurrentProgramme.SharedG0BPairAveraged
import RequestProject.CurrentProgramme.PrimitiveReducedDenominator
import RequestProject.CurrentProgramme.PrimitiveNearFreqCount
import RequestProject.CurrentProgramme.SharedG0CauchyConfigurationSocket

/-!
# Append-only status layer — Erdős #287, SHARED-`g₀` CAUCHY REPAIR Δ

This module is **append-only**.  The PRIMITIVE-LOCALPROFILE ledger
(`Erdos287.PrimitiveLocalProfileStatus.ledger`) and, through it, the BLOCK20 ledger are
imported and left untouched; `historical_localProfile_status_preserved` re-checks a sample of
their rows.  No historical file is edited.

Frontier movement of this delta:

```
before : 287-K0-SP2-DET1-PRIMITIVE-LOCALPROFILE-GRAM45
after  : 287-K0-SP2-DET1-SHAREDG0-CAUCHY-CONFIGURATION45   (controlling repair)
```

`PRIMITIVE-LOCALPROFILE-GRAM45` is recorded as `strictlyReducedBlocked`: strictly reduced in
research, but its promotion is blocked by the repair child above.  It is **not** closed and
**not** marked false.

The two analytic children returned `REPAIR` by the hostile NANC audit,

* `DET1-LARGESHAREDG0-CELLS45`,
* `DET1-PRIMITIVE-NEARFREQ45`,

carry the label `repairPending`; neither is `closed`.

`DET1-SHORTLIFT-EULER-COLLAPSE45` is upgraded to `nancVerifiedPass` (§11): the previous NANC
objection and the one-full-log budget charge are SUPERSEDED / WITHDRAWN.  The corresponding
Lean analytic input remains **uninhabited** — nothing analytic is proved here.

The later hard-denominator child
`287-K0-SP2-DET1-PRIMITIVE-SMALLGCD-FAR-HARDDEN-GRAM45` is `pendingChild`: conditional on both
repair children closing, and not inhabited.

`FCL` is `notReached`, `UNIFORM k = 0` and `ERDOS287` are `open_`; there is no `closed` row.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace SharedG0RepairStatus

open Erdos287.LocalProfileHarmonic
open Erdos287.SharedG0Param
open Erdos287.SharedG0Router
open Erdos287.SharedG0UnitSector
open Erdos287.SharedG0BPair
open Erdos287.ReducedDenominator
open Erdos287.NearFreqCount
open Erdos287.SharedG0Cauchy

/-! ## §12.1  The ledger -/

/-- The nodes of the SHARED-`g₀` CAUCHY REPAIR Δ pass. -/
inductive Node
  | primitiveRamanujanAlgebra
  | shortLiftLocalProfileAlgebra
  | shortLiftEulerAnalytic45
  | localProfileHarmonicTwists45
  | sharedG0PrimitiveUParam45
  | sharedG0PrimitiveURouter45
  | sharedG0BPairAveraged45
  | primitiveReducedDenominator45
  | primitiveNearFreqCount45
  | largeSharedG0Cells45
  | primitiveNearFreq45
  | sharedG0CauchyConfiguration45
  | primitiveLocalProfileGram45
  | primitiveSmallGcdFarHardDenGram45
  | uniformK0
  | fcl
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-- The status labels.  `closed` exists only so that "no closed row" is a statement about this
ledger; it is never used. -/
inductive Label
  | closed
  | formallyBanked
  | formalCorePass
  | formalFinitePass
  | formalPrecursorPass
  | nancVerifiedPassUninhabited
  | repairPending
  | analyticRepairOpen
  | strictlyReducedBlocked
  | pendingChild
  | notReached
  | open_
  deriving DecidableEq, Fintype, Repr

open Node Label

/-- The SHARED-`g₀` CAUCHY REPAIR Δ ledger, exactly the §12 table. -/
def ledger : Node → Label
  | primitiveRamanujanAlgebra => formallyBanked
  | shortLiftLocalProfileAlgebra => formallyBanked
  | shortLiftEulerAnalytic45 => nancVerifiedPassUninhabited
  | localProfileHarmonicTwists45 => formalCorePass
  | sharedG0PrimitiveUParam45 => formalCorePass
  | sharedG0PrimitiveURouter45 => formalCorePass
  | sharedG0BPairAveraged45 => formalFinitePass
  | primitiveReducedDenominator45 => formalCorePass
  | primitiveNearFreqCount45 => formalPrecursorPass
  | largeSharedG0Cells45 => repairPending
  | primitiveNearFreq45 => repairPending
  | sharedG0CauchyConfiguration45 => analyticRepairOpen
  | primitiveLocalProfileGram45 => strictlyReducedBlocked
  | primitiveSmallGcdFarHardDenGram45 => pendingChild
  | uniformK0 => open_
  | fcl => notReached
  | erdos287 => open_

/-- Which rows carry a proved conditional consumer only (uninhabited antecedent). -/
def hasConditionalConsumerOnly : Node → Bool
  | shortLiftEulerAnalytic45 => true
  | sharedG0CauchyConfiguration45 => true
  | primitiveLocalProfileGram45 => true
  | _ => false

/-- The exact main-line residual order after this delta. -/
def residualRank : Node → ℕ
  | sharedG0CauchyConfiguration45 => 1
  | largeSharedG0Cells45 => 2
  | primitiveNearFreq45 => 3
  | primitiveLocalProfileGram45 => 4
  | _ => 0

/-! ## §12.2  Ledger integrity -/

/-- **`no_closed_rows`.**  `LEAN_PROVED`. -/
theorem no_closed_rows : ∀ n : Node, ledger n ≠ closed := by decide +kernel

/-- **`erdos287_open`.**  `LEAN_PROVED`. -/
theorem erdos287_open : ledger erdos287 = open_ := by decide +kernel

/-- **`uniform_k0_open_fcl_not_reached`.**  `LEAN_PROVED`. -/
theorem uniform_k0_open_fcl_not_reached :
    ledger uniformK0 = open_ ∧ ledger fcl = notReached := by decide +kernel

/-- **`two_analytic_children_repair_pending`.**  `LEAN_PROVED`.

§8: neither analytic child is promoted.  Both are `repairPending`, neither is `closed`. -/
theorem two_analytic_children_repair_pending :
    ledger largeSharedG0Cells45 = repairPending ∧
      ledger primitiveNearFreq45 = repairPending ∧
      repairPending ≠ closed := by
  decide +kernel

/-- **`localProfileGram_strictly_reduced_not_promoted`.**  `LEAN_PROVED`.

§10: the historical hierarchy row is strictly reduced in research but its promotion is
blocked by the repair child; it is neither closed nor first on the residual list, and its
analytic interface is still **uninhabited**. -/
theorem localProfileGram_strictly_reduced_not_promoted :
    ledger primitiveLocalProfileGram45 = strictlyReducedBlocked ∧
      strictlyReducedBlocked ≠ closed ∧
      residualRank primitiveLocalProfileGram45 ≠ 1 ∧
      (∃ (X eta C : ℝ)
          (gram : Erdos287.PrimitiveLocalProfile.PrimitiveConductorConfig → ℝ),
        ¬ Erdos287.PrimitiveLocalProfile.PrimitiveLocalProfileGramInput X eta C gram) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    Erdos287.PrimitiveLocalProfile.primitiveLocalProfileGram_not_automatic⟩

/-- **`hardDen_child_conditional_not_promoted`.**  `LEAN_PROVED`.

§10: `287-K0-SP2-DET1-PRIMITIVE-SMALLGCD-FAR-HARDDEN-GRAM45` is a pending child, conditional
on both repair children closing; it is not current, not closed, and not inhabited. -/
theorem hardDen_child_conditional_not_promoted :
    ledger primitiveSmallGcdFarHardDenGram45 = pendingChild ∧
      pendingChild ≠ closed ∧
      residualRank primitiveSmallGcdFarHardDenGram45 = 0 ∧
      ledger largeSharedG0Cells45 ≠ closed ∧
      ledger primitiveNearFreq45 ≠ closed := by
  decide +kernel

/-- **`cauchyConfiguration_is_first_exact_research_residual`.**  `LEAN_PROVED`.

§9/§12: `287-K0-SP2-DET1-SHAREDG0-CAUCHY-CONFIGURATION45` is the current first exact research
residual, its row is `analyticRepairOpen`, and its interface is **uninhabited** (explicit
refuting data). -/
theorem cauchyConfiguration_is_first_exact_research_residual :
    ledger sharedG0CauchyConfiguration45 = analyticRepairOpen ∧
      residualRank sharedG0CauchyConfiguration45 = 1 ∧
      (∀ n : Node, residualRank n = 1 → n = sharedG0CauchyConfiguration45) ∧
      (∃ (K : ℝ) (cell : CauchyLedger → ℝ), ¬ SharedG0CauchyConfigurationInput K cell) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    sharedG0CauchyConfiguration_not_automatic⟩

/-! ## §12.3  The exact rows are backed by theorems -/

/-- **`exact_algebraic_rows_are_theorems`.**  `LEAN_PROVED`.

The `formalCorePass` / `formalFinitePass` / `formalPrecursorPass` rows of this delta are
backed by the actual kernel-checked statements of §§1–7. -/
theorem exact_algebraic_rows_are_theorems :
    ledger localProfileHarmonicTwists45 = formalCorePass ∧
      ledger sharedG0PrimitiveUParam45 = formalCorePass ∧
      ledger sharedG0PrimitiveURouter45 = formalCorePass ∧
      ledger sharedG0BPairAveraged45 = formalFinitePass ∧
      ledger primitiveReducedDenominator45 = formalCorePass ∧
      ledger primitiveNearFreqCount45 = formalPrecursorPass ∧
      -- §1: the exact finite harmonic twist expansion of the local profile
      (∀ (g b : ℕ), g ≠ 0 → b ≠ 0 → ∀ (D T : ℕ) (Psi : ℚ → ℚ),
        Erdos287.ShortLift.mProfile g b D Psi T
          = ∑ l ∈ (rad (2 * b * g)).divisors, (1 / (l : ℚ)) * twistInner l D T Psi) ∧
      -- §2: the fixed-`D` shared-`g₀` `u`-parametrisation
      (∀ (r1 r2 t1 t2 t10 t20 D : ℤ), IsCoprime r1 r2 → r1 ≠ 0 →
        r2 * t10 - r1 * t20 = D →
        (r2 * t1 - r1 * t2 = D ↔ ∃ u : ℤ, t1 = t10 + r1 * u ∧ t2 = t20 + r2 * u)) ∧
      -- §2: the excluded-residue count is exactly `ν_p(D)`
      (∀ (p : ℕ), p.Prime → ∀ t10 t20 r1 r2 : ℤ, ¬ (p : ℤ) ∣ r1 → ¬ (p : ℤ) ∣ r2 →
        (excludedU p t10 t20 r1 r2).card = nuP p (t10 * r2 - t20 * r1)) ∧
      -- §3: the two elementary local bounds and the product bound
      (∀ (g0 : ℕ) (t10 t20 r1 r2 C : ℤ),
        ‖primitiveUSum g0 t10 t20 r1 r2 C‖ ≤ g0) ∧
      (∀ (p : ℕ), p.Prime → ∀ t10 t20 r1 r2 C : ℤ,
        ¬ (p : ℤ) ∣ r1 → ¬ (p : ℤ) ∣ r2 → ¬ (p : ℤ) ∣ C →
        ‖primitiveUSum p t10 t20 r1 r2 C‖ ≤ 2) ∧
      -- §4: the unit-sector gcd reduction
      (∀ (g0 : ℕ) (b1 b2 x y : ℤ), (g0 : ℤ) ∣ 2 * b1 * x - 1 → (g0 : ℤ) ∣ 2 * b2 * y - 1 →
        Int.gcd (g0 : ℤ) (x - y) = Int.gcd (g0 : ℤ) (b1 - b2)) ∧
      -- §5: the averaged `b`-pair finite core
      (∀ (g0 : ℕ), 0 < g0 → ∀ B : ℕ,
        ∑ p ∈ Finset.range B ×ˢ Finset.range B, Int.gcd (g0 : ℤ) ((p.1 : ℤ) - (p.2 : ℤ))
          ≤ B ^ 2 * g0.divisors.card + B * g0) ∧
      -- §6: the reduced denominator
      (∀ (g0 r1 r2 : ℕ) (t1 t2 : ℤ), 0 < g0 → 0 < r1 → 0 < r2 → Nat.Coprime r1 r2 →
        Int.gcd t1 ((g0 : ℤ) * r1) = 1 → Int.gcd t2 ((g0 : ℤ) * r2) = 1 →
        r1 * r2 ≤ (((t1 * r2 - t2 * r1 : ℤ) : ℚ) / ((g0 * r1 * r2 : ℕ) : ℚ)).den) ∧
      -- §7: the near-frequency exact count precursor
      (∀ (g0 r1 r2 : ℕ), 0 < g0 → 0 < r1 → 0 < r2 → Nat.Coprime r1 r2 →
        ∀ H A : ℚ, 0 < H → 0 < A →
          (nearFreqSet g0 r1 r2 H A).card
            ≤ g0 + 2 * g0 * (⌊((g0 : ℚ) * r1 * r2) * H / A⌋).toNat) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel,
    fun _ _ hg hb D T Psi => mProfile_harmonic_twist_expansion hg hb D T Psi,
    fun _ _ _ _ _ _ _ hcop hr1 h0 => sharedG0_u_param_iff hcop hr1 h0,
    fun _ hp _ _ _ _ hr1 hr2 => card_excludedU hp hr1 hr2,
    fun g0 t10 t20 r1 r2 C => norm_primitiveUSum_le_modulus g0 t10 t20 r1 r2 C,
    fun _ hp _ _ _ _ _ hr1 hr2 hC => norm_primitiveUSum_le_two hp hr1 hr2 hC,
    fun _ _ _ _ _ hx hy => sharedGcd_reciprocalDiff_eq_originalDiff hx hy,
    fun _ hg0 B => bpair_gcd_sum_le_divisorCount hg0 B,
    fun _ _ _ _ _ hg0 hr1 hr2 hcop h1 h2 => reducedDenominator_ge hg0 hr1 hr2 hcop h1 h2,
    fun _ _ _ hg0 hr1 hr2 hcop _ _ hH hA => nearFreqSet_card_le hg0 hr1 hr2 hcop hH hA⟩

/-- **`router_crt_and_product_bound`.**  `LEAN_PROVED`.

§3: the CRT two-factor split of the primitive-`u` sum, together with the product bound
`|∏_p U_p| ≤ 2^{ω(g₀)} · gcd(g₀,C)` under the two elementary local bounds. -/
theorem router_crt_and_product_bound :
    (∀ (m n : ℕ), 0 < m → 0 < n → Nat.Coprime m n → ∀ a b : ℤ, a * n + b * m = 1 →
      ∀ t10 t20 r1 r2 C : ℤ,
        primitiveUSum (m * n) t10 t20 r1 r2 C
          = primitiveUSum m t10 t20 r1 r2 (C * a)
              * primitiveUSum n t10 t20 r1 r2 (C * b)) ∧
    (∀ (g0 : ℕ) (C : ℤ), C ≠ 0 → ∀ Uloc : ℕ → ℂ,
      (∀ p ∈ g0.primeFactors, ‖Uloc p‖ ≤ (if ((p : ℤ) ∣ C) then (p : ℝ) else 2)) →
      ‖∏ p ∈ g0.primeFactors, Uloc p‖
        ≤ 2 ^ g0.primeFactors.card * (Int.gcd (g0 : ℤ) C : ℝ)) :=
  ⟨fun _ _ hm hn hmn _ _ hab t10 t20 r1 r2 C =>
      primitiveUSum_crt_split hm hn hmn hab t10 t20 r1 r2 C,
    fun _ _ hC _ hbound => abs_prod_local_le hC _ hbound⟩

/-! ## §12.4  The analytic rows stay uninhabited -/

/-- **`analytic_rows_are_uninhabited`.**  `LEAN_PROVED`.

§0/§11: the short-lift Euler analytic input is upgraded in *research metadata* only — its
Lean interface is still uninhabited, exactly as the historical status file records it.  The
new Cauchy-configuration socket is likewise refuted by explicit data. -/
theorem analytic_rows_are_uninhabited :
    ledger shortLiftEulerAnalytic45 = nancVerifiedPassUninhabited ∧
      ledger sharedG0CauchyConfiguration45 = analyticRepairOpen ∧
      hasConditionalConsumerOnly shortLiftEulerAnalytic45 = true ∧
      hasConditionalConsumerOnly sharedG0CauchyConfiguration45 = true ∧
      -- the finite avatar of the Euler collapse is still a theorem …
      (∀ (n : ℕ), Squarefree n → ∀ H : ℕ,
        Erdos287.ShortLift.mProfileDivisor H n
          = ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ H), (1 - (1 : ℚ) / p)) ∧
      -- … while the new repair socket is refuted by explicit data
      (∃ (K : ℝ) (cell : CauchyLedger → ℝ), ¬ SharedG0CauchyConfigurationInput K cell) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    fun _ hn H => Erdos287.ShortLift.mProfileDivisor_euler_product hn H,
    sharedG0CauchyConfiguration_not_automatic⟩

/-- **`cauchy_amplitude_dichotomy_is_open`.**  `LEAN_PROVED`.

§8 B: the two candidate final amplitude exponents `density^{1/4}` and `density^{1/2}` are
genuinely different, and each is realised by a root-consistent ledger.  Nothing decides
between them here; that is the content of the repair. -/
theorem cauchy_amplitude_dichotomy_is_open :
    ((1 : ℚ) / 4 ≠ 1 / 2) ∧
      (∀ L : CauchyLedger, L.cauchyRoots = 1 → L.rootExponent = 1 / 2) ∧
      (∀ L : CauchyLedger, L.cauchyRoots = 2 → L.rootExponent = 1 / 4) :=
  ⟨amplitude_dichotomy_nontrivial, fun _ h => rootExponent_one h, fun _ h => rootExponent_two h⟩

/-! ## §12.5  Historical ledgers preserved -/

/-- **`historical_localProfile_status_preserved`.**  `LEAN_PROVED`.

The imported PRIMITIVE-LOCALPROFILE ledger — and, through it, BLOCK20 — is unmodified. -/
theorem historical_localProfile_status_preserved :
    Erdos287.PrimitiveLocalProfileStatus.ledger
        Erdos287.PrimitiveLocalProfileStatus.Node.erdos287
        = Erdos287.PrimitiveLocalProfileStatus.Label.open_ ∧
      Erdos287.PrimitiveLocalProfileStatus.ledger
        Erdos287.PrimitiveLocalProfileStatus.Node.fcl
        = Erdos287.PrimitiveLocalProfileStatus.Label.notReached ∧
      Erdos287.PrimitiveLocalProfileStatus.ledger
        Erdos287.PrimitiveLocalProfileStatus.Node.primitiveLocalProfileGram45
        = Erdos287.PrimitiveLocalProfileStatus.Label.analyticOpen ∧
      (∀ n : Erdos287.PrimitiveLocalProfileStatus.Node,
        Erdos287.PrimitiveLocalProfileStatus.ledger n
          ≠ Erdos287.PrimitiveLocalProfileStatus.Label.closed) ∧
      (∀ n : Erdos287.Block20Status.Node,
        Erdos287.Block20Status.ledger n ≠ Erdos287.Block20Status.Label.closed) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · exact Erdos287.PrimitiveLocalProfileStatus.no_closed_rows
  · exact Erdos287.Block20Status.no_closed_rows

end SharedG0RepairStatus
end Erdos287
