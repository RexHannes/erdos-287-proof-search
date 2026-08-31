import Mathlib
import RequestProject.Status.CurrentStatusErdos287SharedG0Repair
import RequestProject.CurrentProgramme.LevelPairProductModulus
import RequestProject.CurrentProgramme.LevelPairFixedDRigidity
import RequestProject.CurrentProgramme.LevelPairReciprocalNormalForm
import RequestProject.CurrentProgramme.LevelPairPrimeAssignment
import RequestProject.CurrentProgramme.SharedGcdGramSquare
import RequestProject.CurrentProgramme.PrimitiveTRamanujanFirewall
import RequestProject.CurrentProgramme.SharedGcdOneLevelMobiusSocket

/-!
# Append-only status layer — Erdős #287, ONE-LEVEL MÖBIUS Δ

This module is **append-only**.  `CurrentStatusErdos287SharedG0Repair` (and through it the
PRIMITIVE-LOCALPROFILE and BLOCK20 ledgers) is imported and left untouched;
`historical_sharedG0_status_preserved` re-checks a sample of its rows.  No historical file is
edited.

Frontier movement of this delta:

```
before : 287-K0-SP2-DET1-SHAREDG0-CAUCHY-CONFIGURATION45
after  : 287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-MOBIUS-GRAM45
```

Status corrections carried here:

* `SHAREDG0-BPAIR-AVERAGED45` — formal core pass (unchanged);
* `SHAREDG0-CAUCHY-CONFIGURATION45` — **research pass**, hence *superseded* as the first
  residual; it is neither closed nor first on the residual list any more;
* the `Q`-level near-density gain is `δ^{1/2}` and the final amplitude gain `δ^{1/4}`;
* `DET1-LARGESHAREDG0-CELLS45` — the old closure is **retracted**; analytic open;
* `DET1-PRIMITIVE-NEARFREQ45` — open, non-closing by the current Cauchy;
* `PRIMITIVE-SMALLGCD-FAR-HARDDEN-GRAM45` — not promoted;
* `SHAREDG0-SIGNED-LEVELPAIR-GRAM45` — strictly reduced by the exact pivot of this delta;
* `DET1-SHAREDGCD-ONELEVEL-ENERGY45` — provisional research subpolytope pass, NANC pending; the
  formal analytic input is uninhabited and the subpolytope is **not** marked closed.

`FCL` is `notReached`, `UNIFORM k = 0` and `ERDOS287` are `open_`; there is no `closed` row.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open ArithmeticFunction

namespace Erdos287
namespace OneLevelMobiusStatus

open Erdos287.LevelPairProduct
open Erdos287.LevelPairRigidity
open Erdos287.LevelPairReciprocal
open Erdos287.LevelPairPrimeAssignment
open Erdos287.SharedGcdGram
open Erdos287.PrimitiveTFirewall
open Erdos287.SharedGcdOneLevel

/-! ## §14.1  The ledger -/

/-- The nodes of the ONE-LEVEL MÖBIUS Δ pass. -/
inductive Node
  | shortLiftEuler
  | sharedG0BPairAveraged
  | sharedG0CauchyConfiguration
  | largeSharedG0
  | primitiveNearFreq
  | hardDenominatorCore
  | levelPairProductModSign
  | dNCoprime
  | levelPairNDivisorSplit
  | fixedDFrequencyRigidity
  | levelPairNReciprocalNormalForm
  | levelPairPrimeAssignment
  | sharedGcdGramSquare
  | primitiveTRamanujanFirewall
  | sharedGcdOneLevelEnergy
  | sharedG0SignedLevelPairGram45
  | sharedGcdOneLevelMobiusGram45
  | uniformK0
  | fcl
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-- The status labels.  `closed` exists only so that "no closed row" is a statement about this
ledger; it is never used. -/
inductive Label
  | closed
  | formalPass
  | formalCorePass
  | formalFixedNPass
  | nancVerifiedPassUninhabited
  | researchPassSuperseded
  | retractedAnalyticOpen
  | openNonclosing
  | notPromoted
  | provisionalResearchSubpolytope
  | strictlyReduced
  | analyticOpen
  | notReached
  | open_
  deriving DecidableEq, Fintype, Repr

open Node Label

/-- The ONE-LEVEL MÖBIUS Δ ledger, exactly the §14 table. -/
def ledger : Node → Label
  | shortLiftEuler => nancVerifiedPassUninhabited
  | sharedG0BPairAveraged => formalCorePass
  | sharedG0CauchyConfiguration => researchPassSuperseded
  | largeSharedG0 => retractedAnalyticOpen
  | primitiveNearFreq => openNonclosing
  | hardDenominatorCore => notPromoted
  | levelPairProductModSign => formalPass
  | dNCoprime => formalPass
  | levelPairNDivisorSplit => formalPass
  | fixedDFrequencyRigidity => formalPass
  | levelPairNReciprocalNormalForm => formalPass
  | levelPairPrimeAssignment => formalFixedNPass
  | sharedGcdGramSquare => formalPass
  | primitiveTRamanujanFirewall => formalPass
  | sharedGcdOneLevelEnergy => provisionalResearchSubpolytope
  | sharedG0SignedLevelPairGram45 => strictlyReduced
  | sharedGcdOneLevelMobiusGram45 => analyticOpen
  | uniformK0 => open_
  | fcl => notReached
  | erdos287 => open_

/-- The exact main-line residual order after this delta. -/
def residualRank : Node → ℕ
  | sharedGcdOneLevelMobiusGram45 => 1
  | sharedGcdOneLevelEnergy => 2
  | largeSharedG0 => 3
  | primitiveNearFreq => 4
  | _ => 0

/-- The `Q`-level near-density gain exponent. -/
def nearDensityExponent : ℚ := 1 / 2

/-- The final near amplitude exponent. -/
def finalAmplitudeExponent : ℚ := 1 / 4

/-! ## §14.2  Ledger integrity -/

/-- **`no_closed_rows`.**  `LEAN_PROVED`. -/
theorem no_closed_rows : ∀ n : Node, ledger n ≠ closed := by decide +kernel

/-- **`erdos287_open`.**  `LEAN_PROVED`. -/
theorem erdos287_open : ledger erdos287 = open_ := by decide +kernel

/-- **`uniform_k0_open_fcl_not_reached`.**  `LEAN_PROVED`. -/
theorem uniform_k0_open_fcl_not_reached :
    ledger uniformK0 = open_ ∧ ledger fcl = notReached := by decide +kernel

/-- **`amplitude_exponents`.**  `LEAN_PROVED`.

The `Q`-level near-density gain is `δ^{1/2}`; after the second Cauchy square root the final
amplitude gain is `δ^{1/4}`, and the two are different. -/
theorem amplitude_exponents :
    nearDensityExponent = 1 / 2 ∧ finalAmplitudeExponent = 1 / 4 ∧
      finalAmplitudeExponent ≠ nearDensityExponent := by
  refine ⟨rfl, rfl, ?_⟩
  unfold finalAmplitudeExponent nearDensityExponent
  norm_num

/-- **`cauchyConfiguration_superseded_not_closed`.**  `LEAN_PROVED`.

§0: the old first residual is a research pass and is superseded — it is *not* closed and no
longer ranks first. -/
theorem cauchyConfiguration_superseded_not_closed :
    ledger sharedG0CauchyConfiguration = researchPassSuperseded ∧
      researchPassSuperseded ≠ closed ∧
      residualRank sharedG0CauchyConfiguration = 0 := by
  decide +kernel

/-- **`largeSharedG0_retracted_and_nearFreq_open`.**  `LEAN_PROVED`.

§0: the old `DET1-LARGESHAREDG0-CELLS45` closure is retracted, `DET1-PRIMITIVE-NEARFREQ45` is
open / non-closing by the current Cauchy, and the hard-denominator core is not promoted. -/
theorem largeSharedG0_retracted_and_nearFreq_open :
    ledger largeSharedG0 = retractedAnalyticOpen ∧
      ledger primitiveNearFreq = openNonclosing ∧
      ledger hardDenominatorCore = notPromoted ∧
      retractedAnalyticOpen ≠ closed ∧ openNonclosing ≠ closed ∧ notPromoted ≠ closed := by
  decide +kernel

/-- **`energy_subpolytope_provisional_not_closed`.**  `LEAN_PROVED`.

§11: the one-level energy row is a *provisional* research subpolytope pass with the NANC audit
pending.  It is not closed, and its Lean analytic input is uninhabited (explicit refuting
data). -/
theorem energy_subpolytope_provisional_not_closed :
    ledger sharedGcdOneLevelEnergy = provisionalResearchSubpolytope ∧
      provisionalResearchSubpolytope ≠ closed ∧
      residualRank sharedGcdOneLevelEnergy ≠ 1 ∧
      (∃ (C : ℝ) (energy : EnergyLedger → ℝ), ¬ SharedGcdOneLevelEnergyInput C energy) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    sharedGcdOneLevelEnergy_not_automatic⟩

/-- **`oneLevelMobiusGram_is_first_exact_residual`.**  `LEAN_PROVED`.

§13: `287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-MOBIUS-GRAM45` is the unique first exact main-line
residual, its row is `analyticOpen`, and its interface is **uninhabited**. -/
theorem oneLevelMobiusGram_is_first_exact_residual :
    ledger sharedGcdOneLevelMobiusGram45 = analyticOpen ∧
      residualRank sharedGcdOneLevelMobiusGram45 = 1 ∧
      (∀ n : Node, residualRank n = 1 → n = sharedGcdOneLevelMobiusGram45) ∧
      (∃ K : ℝ, ¬ SharedGcdOneLevelMobiusGramInput K) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    sharedGcdOneLevelMobiusGram_not_automatic⟩

/-- **`signed_levelPair_gram_strictly_reduced`.**  `LEAN_PROVED`.

The signed level-pair Gram is strictly reduced by the exact pivot of this delta; the row is
`strictlyReduced`, which is not `closed`. -/
theorem signed_levelPair_gram_strictly_reduced :
    ledger sharedG0SignedLevelPairGram45 = strictlyReduced ∧
      strictlyReduced ≠ closed := by
  decide +kernel

/-! ## §14.3  The exact rows are backed by theorems -/

/-- **`exact_rows_are_theorems`.**  `LEAN_PROVED`.

Every `formalPass` / `formalFixedNPass` row of this delta is backed by the actual kernel-checked
statement of §§1–9 and §12. -/
theorem exact_rows_are_theorems :
    ledger levelPairProductModSign = formalPass ∧
      ledger dNCoprime = formalPass ∧
      ledger levelPairNDivisorSplit = formalPass ∧
      ledger fixedDFrequencyRigidity = formalPass ∧
      ledger levelPairNReciprocalNormalForm = formalPass ∧
      ledger levelPairPrimeAssignment = formalFixedNPass ∧
      ledger sharedGcdGramSquare = formalPass ∧
      ledger primitiveTRamanujanFirewall = formalPass ∧
      -- §1: product-modulus Möbius sign compression and the level-pair lcm
      (∀ g0 r1 r2 : ℕ, Squarefree g0 → Nat.Coprime g0 r1 → Nat.Coprime g0 r2 →
        Nat.Coprime r1 r2 →
        (moebius (g0 * r1) : ℤ) * (moebius (g0 * r2) : ℤ) = (moebius (r1 * r2) : ℤ)) ∧
      (∀ g0 r1 r2 : ℕ, 0 < g0 → Nat.Coprime r1 r2 →
        Nat.lcm (g0 * r1) (g0 * r2) = g0 * (r1 * r2)) ∧
      -- §2: `gcd(D,n) = 1`
      (∀ (g0 r1 r2 : ℕ) (t1 t2 : ℤ), Nat.Coprime r1 r2 →
        Int.gcd t1 ((g0 : ℤ) * r1) = 1 → Int.gcd t2 ((g0 : ℤ) * r2) = 1 →
        Int.gcd (t1 * r2 - t2 * r1) ((r1 * r2 : ℕ) : ℤ) = 1) ∧
      -- §3: the exact fixed-`n` level-pair reindexing
      (∀ (g0 n : ℕ), Squarefree g0 → 0 < g0 → Squarefree n → Nat.Coprime g0 n →
        ∀ K : ℕ → ℕ → ℂ,
          ∑ p ∈ n.divisorsAntidiagonal,
              ((moebius (g0 * p.1) : ℤ) : ℂ) * ((moebius (g0 * p.2) : ℤ) : ℂ)
                / (((g0 * p.1 : ℕ) : ℂ) * ((g0 * p.2 : ℕ) : ℂ)) * K (g0 * p.1) (g0 * p.2)
            = (1 / (g0 : ℂ) ^ 2) * (((moebius n : ℤ) : ℂ) / (n : ℂ))
                * ∑ r ∈ n.divisors, K (g0 * r) (g0 * (n / r))) ∧
      -- §4: the general fixed-`D` solution line
      (∀ r1 r2 x y D t1 t2 : ℤ, IsCoprime r1 r2 → r1 ≠ 0 → x * r2 - y * r1 = 1 →
        (t1 * r2 - t2 * r1 = D ↔ ∃ u : ℤ, t1 = x * D + r1 * u ∧ t2 = y * D + r2 * u)) ∧
      -- §5: the Farey difference depends only on `(g₀,n,D)`
      (∀ (g0 r1 r2 : ℕ), 0 < g0 → 0 < r1 → 0 < r2 → ∀ t1 t2 : ℤ,
        (t1 : ℚ) / ((g0 * r1 : ℕ) : ℚ) - (t2 : ℚ) / ((g0 * r2 : ℕ) : ℚ)
          = ((t1 * r2 - t2 * r1 : ℤ) : ℚ) / ((g0 : ℚ) * ((r1 * r2 : ℕ) : ℚ))) ∧
      -- §6: `gcd(2g₀β_r, n) = 1` and the CRT phase normal form
      (∀ g0 r s beta b1 b2 : ℤ, r ∣ beta - b1 → s ∣ beta - b2 →
        IsCoprime (2 * g0 * b1) r → IsCoprime (2 * g0 * b2) s →
        IsCoprime (2 * g0 * beta) (r * s)) ∧
      -- §7: the fixed-`n` two-state prime assignment
      (∀ (n : ℕ), Squarefree n → ∀ L1 L2 : ℕ → ℂ,
        ∑ r ∈ n.divisors, (∏ p ∈ r.primeFactors, L1 p) * (∏ p ∈ (n / r).primeFactors, L2 p)
          = ∏ p ∈ n.primeFactors, (L1 p + L2 p)) ∧
      -- §9: Möbius inversion of the shared-gcd projector
      (∀ (Om : ℕ → ℝ) (m : ℕ), 0 < m → ∑ d ∈ m.divisors, lambdaH Om d = Om m) ∧
      -- §12: the two signed local Ramanujan factors
      (∀ (p : ℕ), p.Prime → ∀ N : ℤ, ¬ (p : ℤ) ∣ N →
        Erdos287.PrimitiveRamanujan.ramanujan p N = -1) ∧
      (∀ (p : ℕ), p.Prime → ∀ N : ℤ, (p : ℤ) ∣ N →
        Erdos287.PrimitiveRamanujan.ramanujan p N = (p : ℂ) - 1) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    fun _ _ _ hg0 h1 h2 hr => moebius_levelPair_eq_moebius_n hg0 h1 h2 hr,
    fun _ _ _ hg0 hr => lcm_levelPair_eq hg0 hr,
    fun _ _ _ _ _ hcop h1 h2 => gcd_D_n_eq_one hcop h1 h2,
    fun _ _ hsq hpos hn hcop K => levelPair_reindex_fixed_n hsq hpos hn hcop K,
    fun _ _ _ _ _ _ _ hcop hr1 hxy => fixedD_solution_iff hcop hr1 hxy,
    fun _ _ _ hg0 hr1 hr2 t1 t2 => fareyDifference_eq_D_div_g0n hg0 hr1 hr2 t1 t2,
    fun _ _ _ _ _ _ h1 h2 hu1 hu2 => gcd_two_g0_beta_eq_one h1 h2 hu1 hu2,
    fun _ hn L1 L2 => fixed_n_two_state_product hn L1 L2,
    fun Om _ hm => sum_lambdaH_divisors Om hm,
    fun _ hp _ h => ramanujan_prime_not_dvd hp h,
    fun _ hp _ h => ramanujan_prime_dvd hp h⟩

/-- **`gram_square_and_one_level_are_theorems`.**  `LEAN_PROVED`.

§9: the exact Gram-as-square identity, its one-level form and the `λ_H` harmonic mass
inequality are all kernel-checked. -/
theorem gram_square_and_one_level_are_theorems :
    (∀ (Om : ℕ → ℝ) (G : Finset ℕ), (∀ g ∈ G, 0 < g) → ∀ (A : Finset ℕ) (rho : ℕ → ℝ)
        (V : ℕ → ℕ → ℂ) (w : ℕ → ℂ),
      gramSharedGcd Om G A rho V w
        = ∑ d ∈ divisorSupport G, ((lambdaH Om d : ℝ) : ℂ) *
            ∑ a ∈ A, (rho a : ℂ) *
              ((‖∑ g ∈ levelSlice G d, w g * V g a‖ : ℝ) : ℂ) ^ 2) ∧
    (∀ (Om : ℕ → ℝ) (G : Finset ℕ), (∀ g ∈ G, 0 < g) → (∀ g ∈ G, Squarefree g) →
      ∀ (A : Finset ℕ) (rho : ℕ → ℝ) (V : ℕ → ℕ → ℂ),
      gramSharedGcd Om G A rho V (fun g => ((moebius g : ℤ) : ℂ) / (g : ℂ))
        = ∑ d ∈ divisorSupport G, ((lambdaH Om d : ℝ) : ℂ) / (d : ℂ) ^ 2 *
            ∑ a ∈ A, (rho a : ℂ) *
              ((‖∑ m ∈ cofactorSlice G d,
                  ((moebius m : ℤ) : ℂ) / (m : ℂ) * V (d * m) a‖ : ℝ) : ℂ) ^ 2) ∧
    (∀ (Om : ℕ → ℝ) (X : ℕ),
      ∑ d ∈ Finset.Icc 1 X, |lambdaH Om d| / (d : ℝ) ^ 2
        ≤ (∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ) ^ 2) *
          (∑ k ∈ Finset.Icc 1 X, |(moebius k : ℝ)| / (k : ℝ) ^ 2)) :=
  ⟨fun Om _ hG A rho V w => sharedGcd_gram_square Om hG A rho V w,
    fun Om _ hG hsq A rho V => sharedGcd_oneLevel_gram Om hG hsq A rho V,
    fun Om X => lambdaH_harmonic_mass_le Om X⟩

/-- **`nonmultiplicativity_firewall_is_explicit`.**  `LEAN_PROVED`.

§8: the single explicit finite counterexample.  No universal negation is asserted. -/
theorem nonmultiplicativity_firewall_is_explicit :
    coeffK 15 = 4 ∧ coeffK 3 = 1 ∧ coeffK 5 = 1 ∧ coeffK 15 ≠ coeffK 3 * coeffK 5 :=
  localFactorK_not_multiplicative

/-! ## §14.4  Historical ledgers preserved -/

/-- **`historical_sharedG0_status_preserved`.**  `LEAN_PROVED`.

The imported SHARED-`g₀` REPAIR ledger — and, through it, PRIMITIVE-LOCALPROFILE and BLOCK20 —
is unmodified. -/
theorem historical_sharedG0_status_preserved :
    Erdos287.SharedG0RepairStatus.ledger Erdos287.SharedG0RepairStatus.Node.erdos287
        = Erdos287.SharedG0RepairStatus.Label.open_ ∧
      Erdos287.SharedG0RepairStatus.ledger Erdos287.SharedG0RepairStatus.Node.fcl
        = Erdos287.SharedG0RepairStatus.Label.notReached ∧
      Erdos287.SharedG0RepairStatus.ledger
          Erdos287.SharedG0RepairStatus.Node.sharedG0CauchyConfiguration45
        = Erdos287.SharedG0RepairStatus.Label.analyticRepairOpen ∧
      (∀ n : Erdos287.SharedG0RepairStatus.Node,
        Erdos287.SharedG0RepairStatus.ledger n
          ≠ Erdos287.SharedG0RepairStatus.Label.closed) ∧
      (∀ n : Erdos287.PrimitiveLocalProfileStatus.Node,
        Erdos287.PrimitiveLocalProfileStatus.ledger n
          ≠ Erdos287.PrimitiveLocalProfileStatus.Label.closed) ∧
      (∀ n : Erdos287.Block20Status.Node,
        Erdos287.Block20Status.ledger n ≠ Erdos287.Block20Status.Label.closed) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · exact Erdos287.SharedG0RepairStatus.no_closed_rows
  · exact Erdos287.PrimitiveLocalProfileStatus.no_closed_rows
  · exact Erdos287.Block20Status.no_closed_rows

end OneLevelMobiusStatus
end Erdos287
