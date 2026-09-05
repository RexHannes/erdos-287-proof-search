import RequestProject.Erdos287.Bank

/-!
# Erdős #287 — CURRENT STATUS (appended layer): effectivity certificate bank

This is an **append-only later-status layer**.  It does not overwrite or invalidate any
earlier status file; where an earlier file recorded the abstract `S₂^{ω(q)}` local model, the
P0 normalisation notice in
`RequestProject/CurrentProgramme/Erdos287September4BsrcLocalMobiusCollapse.lean`
now records explicitly that this is the **abstract** model and that the **physical** local
collapse is `Erdos287.SourceWeights.physicalBsrcMobiusCollapse45`.

## CLOSED / BANKED (kernel-proved algebra, or exact rational ledger arithmetic)

```
corrected physical B_src local collapse  : physicalBsrcMobiusCollapse45
q = 15 physical regression               : regression_q15_physical
gcd-descent algebra                      : squarefree_gcd_descent (+ _map, _real)
descent coprimality gcd(b,qv) = 1        : descentIndex_coprime
phase / W-argument / hyperbola descent   : phase_descent, W_argument_descent,
                                           hyperbola_support_gcd_descent
medium-k exact source normal form        : mediumK_source_normal_form
joint no-lattice kernel identity         : jointKernel_noLattice
repeated-core ledger, no double count    : repeated_core_ledger_disjoint / _total
exact rational certificate ledger        : certifiedSubtotal_correct,
                                           remainingCapacity_correct
sawtooth L² mass and the 11/108 bound    : sawtooth_sq_mean, sawtooth_l2_mass_le
```

## RECORDED NUMERICAL INPUTS (EXTERNAL MACHINE-CERTIFICATE RESULTS, transcribed exactly)

```
A  squarefree gamma, k = 1 and odd squarefree 3 ≤ k ≤ 31 : < 1.913023635e-7 · B_X
   (contains the q = 3 physical directed row, < 2.17e-8 · B_X)
B  joint no-lattice tail (incl. no-lattice p², p³)       : < 1.641148117e-7 · B_X
C  lattice-bearing repeated p²                            : < 1.663866835e-7 · B_X
D  lattice-bearing repeated p³                            : < 8.3528e-11  · B_X
E  nonlinear gamma drift                                  : < 8.1e-16     · B_X
```

## SUBTOTAL AUDIT (kernel-recomputed, do not use the printed figures)

```
certifiedSubtotal (exact)   = 52188738751 / 10^17 = 5.2188738751e-7
printed 5.218873872e-7      : NOT an upper bound  (short by 3.1e-16)
target                      = 886065 / 10^12      = 8.86065e-7
remainingCapacity (exact)   = 36417761249 / 10^17 = 3.6417761249e-7
printed 3.641776128e-7      : OVERSTATES capacity (by 3.1e-16)
```

## OPEN

```
squarefree lattice-bearing medium-k joint Bernoulli : OPEN
squarefree two-high nonlinear gap a ≤ 180           : OPEN
signed B_src floor                                   : OPEN
Maynard                                              : NOT ENTERED
Erdős #287                                           : OPEN
```

FIRST EXACT REMAINING NODE:
`ERDOS287-TOT-BSRC-SQFREE-LATTICEBEARING-MEDIUMK-GCDDESCENT-JOINT-BERNOULLI-DIRECTED45`.

PARALLEL SECOND NODE:
`ERDOS287-TOT-BSRC-SQFREE-TWOHIGH-A180-NONLINEAR-MELLIN-LATTICEBEARING45`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287
namespace CertificateBankStatus

/-- The `physicalBsrcCollapse` row is backed by the theorem it labels. -/
theorem row_physicalBsrcCollapse_backed (S2 : ℚ) {q : ℕ} (hq : Squarefree q) (hodd : Odd q) :
    ∑ d ∈ q.divisors, (moebius d : ℚ) * SourceWeights.Bsrc S2 d * SourceWeights.beta (q / d)
      = S2 * (moebius q : ℚ) :=
  SourceWeights.physicalBsrcMobiusCollapse45 S2 hq hodd

/-- The `gcdDescent` row is backed by the theorem it labels. -/
theorem row_gcdDescent_backed (S2 : ℚ) (F : ℕ → ℕ → ℚ) {U K : Finset ℕ}
    (hU0 : 0 ∉ U) (hK0 : 0 ∉ K) (hUsf : ∀ u ∈ U, Squarefree u) (hKsf : ∀ k ∈ K, Squarefree k) :
    ∑ u ∈ U, ∑ k ∈ K, (if Nat.Coprime u k then (1 : ℚ) else 0) *
        ((moebius u : ℚ) * SourceWeights.Bsrc S2 u * SourceWeights.beta k * F u k)
      = ∑ t ∈ GcdDescent.descentIndex U K,
          SourceWeights.lam t.1 * SourceWeights.beta t.2.1 * (moebius t.2.2 : ℚ) *
            SourceWeights.Bsrc S2 t.2.2 * F (t.1 * t.2.2) (t.1 * t.2.1) :=
  GcdDescent.squarefree_gcd_descent S2 F hU0 hK0 hUsf hKsf

/-- The `certifiedSubtotal` row is backed by the theorem it labels. -/
theorem row_certifiedSubtotal_backed :
    DirectedLedger.certifiedSubtotal = 52188738751 / 10 ^ 17 :=
  DirectedLedger.certifiedSubtotal_correct

/-- The `remainingCapacity` row is backed by the theorem it labels. -/
theorem row_remainingCapacity_backed :
    DirectedLedger.remainingCapacity = 36417761249 / 10 ^ 17 :=
  DirectedLedger.remainingCapacity_correct

/-- The printed research figures are **not** consistent with the exact component bounds. -/
theorem row_printed_figures_inconsistent :
    (5218873872 : ℚ) / 10 ^ 16 < DirectedLedger.certifiedSubtotal ∧
      DirectedLedger.remainingCapacity < (3641776128 : ℚ) / 10 ^ 16 :=
  ⟨DirectedLedger.printed_subtotal_is_not_an_upper_bound,
    DirectedLedger.printed_remaining_overstates_capacity⟩

end CertificateBankStatus
end Erdos287
