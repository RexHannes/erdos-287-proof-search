import RequestProject.Erdos287.FixedCertificateFordData
import RequestProject.Erdos287.FixedCertificateThreeError
import RequestProject.Erdos287.FixedCertificateSmoothParity
import RequestProject.Erdos287.FixedCertificateOrderCounterguard
import RequestProject.Erdos287.KummerDegeneracyRouters
import RequestProject.Status.Erdos287GoldV11Status

/-!
# Status ledger for the V12 reproof / Leanification run

**Erdős #287 remains OPEN.**  Nothing in this run proves it, and no theorem here or in
the files it imports claims otherwise.

## The V12 controlling correction

The V11 expectation — that a fixed Ford certificate reduces the leakage census to
H8/H9 + QK56 — is *withdrawn*, and this run certifies why it cannot be justified from the
divisor combinatorics: `Erdos287.Counterguard.finite_H8H9_only_census_fails` exhibits
nonzero truncated-Möbius weights at defect orders `k = 7, 10, 11, 12`, and
`Erdos287.Counterguard.balancedCellWeight_halfCut_ne_zero` shows no order is annihilated.

## What is kernel-checked in this run

| Item | Lean name |
| --- | --- |
| partial alternating binomial identity | `Erdos287.Counterguard.alternating_partial_binomial` |
| balanced-cell weight, closed form | `Erdos287.Counterguard.balancedCellWeight_eq` |
| H8/H9-only census fails | `Erdos287.Counterguard.finite_H8H9_only_census_fails` |
| three-error transference | `Erdos287.Transference4.sum_a_P_lower4` |
| positivity with three errors | `Erdos287.Transference4.sum_a_P_pos4` / `sum_a_P_pos4_fraction` |
| truncated Möbius weight | `Erdos287.SmoothParity.truncMobius_prime` etc. |
| smooth-parity packet consequences | `Erdos287.SmoothParity.smoothParity_prime_normalization` |
| parent leakage compiler | `Erdos287.SmoothParity.parent_prime_mass_pos` |
| Ford certificate data arithmetic | `Erdos287.FordData.twoVarWindow_nonempty` etc. |
| Kummer degeneracy routing | `Erdos287.Kummer.generic_disjoint_strata` / `generic_not_square` |

## What is *not* proved (external, and left as explicit antecedents)

* `FIXED_CERTIFICATE287_PIN` — `Erdos287.FordData.CertificatePinned` is never inhabited:
  the source dossier is not in this repository;
* `ERDOS287_FIXED_CERTIFICATE_SMOOTH_PARITY45` — the analytic bound field of
  `Erdos287.SmoothParity.FixedCertificateSmoothParityPacket`, together with its
  Gate-1B source-transcription field `cell_identity`;
* the Weil / interval-completion input (V11, `QuadraticKummerCorrelationBound`);
* the parent estimate `287-FIXED-CERTIFICATE-LEAKAGE45`, which needs *every* child.
-/

namespace Status
namespace Erdos287GoldV12

open Erdos287

/-! ## Part J — route firewall (logical facts only)

The alternative routes (`FullFMTypeII_1/6`, the generated Ford (7.23) route,
`SOURCE-ADAPTER45`, the global replacement certificate `C_FM`) remain **valid sufficient
alternatives** and are preserved untouched elsewhere in the project.

The only claim made below is the trivial sufficiency of the fixed-certificate wrapper
*when its own hypotheses are present*.  The stronger claim — that the fixed-certificate
route is analytically shorter — is **not** made anywhere in this project, and would
require a source-exhaustive packet theorem that does not exist here.  The counterguard in
`FixedCertificateOrderCounterguard.lean` is precisely the obstruction to such a claim. -/

/-- **Route sufficiency (V12 form).**  The fixed-certificate leakage route, with the
smooth-parity packet as one child and the remaining packets as the other, is a sufficient
wrapper for a positive prime-mass conclusion *when all of its own hypotheses are
present*.  No claim of relative analytic strength is made. -/
theorem fixedCertificateRoute_sufficient_V12
    (P N1 N2 Usmooth Urest : Finset ℕ) (a b w H : ℕ → ℝ) (Cc ET Es Er E2 EM : ℝ)
    (hw : ∀ n, w n = a n - b n)
    (ha : ∀ n, 0 ≤ a n)
    (hHP : ∀ p ∈ P, H p = 1)
    (hHN1 : ∀ n ∈ N1, H n ≤ 0)
    (hPN1 : Disjoint P N1) (hPN2 : Disjoint P N2) (hPU : Disjoint P (Usmooth ∪ Urest))
    (hN1N2 : Disjoint N1 N2) (hN1U : Disjoint N1 (Usmooth ∪ Urest))
    (hN2U : Disjoint N2 (Usmooth ∪ Urest))
    (hSR : Disjoint Usmooth Urest)
    (hTotal : |∑ n ∈ (P ∪ N1 ∪ N2 ∪ (Usmooth ∪ Urest)), w n * H n| ≤ ET)
    (hs : |∑ n ∈ Usmooth, w n * H n| ≤ Es)
    (hr : |∑ n ∈ Urest, w n * H n| ≤ Er)
    (hN2 : |∑ n ∈ N2, w n * H n| ≤ E2)
    (hMargin : Cc * (∑ p ∈ P, b p) - EM ≤ ∑ n ∈ N1, b n * H n)
    (hsmall : ET + (Es + Er) + E2 + EM < (1 + Cc) * (∑ p ∈ P, b p)) :
    0 < ∑ p ∈ P, a p :=
  SmoothParity.parent_prime_mass_pos P N1 N2 Usmooth Urest a b w H Cc ET Es Er E2 EM
    hw ha hHP hHN1 hPN1 hPN2 hPU hN1N2 hN1U hN2U hSR hTotal hs hr hN2 hMargin hsmall

/-! ## Axiom prints -/

-- Part G1: the Ford certificate data layer
#print axioms Erdos287.FordData.nu0_bounds
#print axioms Erdos287.FordData.twoVarWindow_nonempty
#print axioms Erdos287.FordData.twoVarWindow_width
#print axioms Erdos287.FordData.fordCandidate_empty
#print axioms Erdos287.FordData.fordCandidate_one
#print axioms Erdos287.FordData.fordCandidate_two_in
#print axioms Erdos287.FordData.fordCandidate_two_sample
#print axioms Erdos287.FordData.fordCandidate_three
#print axioms Erdos287.FordData.shrink_le
#print axioms Erdos287.FordData.pinned_two_var

-- Part G2: three-error transference
#print axioms Erdos287.Transference4.sum_a_P_identity4
#print axioms Erdos287.Transference4.sum_a_P_lower4
#print axioms Erdos287.Transference4.sum_a_P_pos4
#print axioms Erdos287.Transference4.sum_a_P_pos4_fraction
#print axioms Erdos287.Transference4.transference4_nonvacuous

-- Part G3 / I: smooth-parity packet and parent compiler
#print axioms Erdos287.SmoothParity.truncMobius_one
#print axioms Erdos287.SmoothParity.truncMobius_prime
#print axioms Erdos287.SmoothParity.sum_moebius_divisors_eq_zero
#print axioms Erdos287.SmoothParity.truncMobius_eq_zero_of_le
#print axioms Erdos287.SmoothParity.smoothParity_prime_normalization
#print axioms Erdos287.SmoothParity.smoothParity_inactive_cut
#print axioms Erdos287.SmoothParity.smoothParity_missing_source
#print axioms Erdos287.SmoothParity.parent_leakage_of_children
#print axioms Erdos287.SmoothParity.parent_leakage_two_children
#print axioms Erdos287.SmoothParity.parent_prime_mass_pos

-- Part G4: the high-order counterguard
#print axioms Erdos287.Counterguard.alternating_partial_binomial
#print axioms Erdos287.Counterguard.balancedCellWeight_eq_sum
#print axioms Erdos287.Counterguard.balancedCellWeight_eq
#print axioms Erdos287.Counterguard.balancedCellWeight_ne_zero
#print axioms Erdos287.Counterguard.balancedCellCut
#print axioms Erdos287.Counterguard.counterguard_k7
#print axioms Erdos287.Counterguard.counterguard_k8
#print axioms Erdos287.Counterguard.counterguard_k9
#print axioms Erdos287.Counterguard.counterguard_k10
#print axioms Erdos287.Counterguard.counterguard_k11
#print axioms Erdos287.Counterguard.counterguard_k12
#print axioms Erdos287.Counterguard.counterguard_k9_matches_bank
#print axioms Erdos287.Counterguard.finite_H8H9_only_census_fails
#print axioms Erdos287.Counterguard.balancedCellWeight_halfCut_ne_zero

-- Part F: degeneracy routers
#print axioms Erdos287.Kummer.generic_not_repeatedRoot
#print axioms Erdos287.Kummer.generic_not_degenerateLead
#print axioms Erdos287.Kummer.generic_not_nonUnit
#print axioms Erdos287.Kummer.generic_not_collision
#print axioms Erdos287.Kummer.generic_disjoint_strata
#print axioms Erdos287.Kummer.generic_not_square
#print axioms Erdos287.Kummer.generic_not_pmExceptional
#print axioms Erdos287.Kummer.repeatedRoot_router_nonvacuous

-- Part J: route firewall
#print axioms Status.Erdos287GoldV12.fixedCertificateRoute_sufficient_V12

end Erdos287GoldV12
end Status
