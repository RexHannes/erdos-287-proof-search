import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V16 §3: the fixed original Route-C parameters

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Recorded exactly (FINITE REGRESSION / parameter record):

    K = 2^82650,  P = 12 K,  a = 57384,  δ = 1/80,  θ_d = 273/500,  ξ = 1/1000,
    A_C = 1000273/273000.

Kernel-proved (LEAN BANK):
* `A_C_eq_two_div_theta_add_xi` — `A_C = 2/θ_d + ξ` exactly;
* `K_mod_26` — `K ≡ 12 (mod 26)` (used by the balanced 26-group blow-up);
* `routeC_margin_of_certificate` — from a `RouteCFunctionalCertificate` (audited rational bounds
  `μ_F > μ_lo`, `W_F < W_hi`) and the exact rational check `RouteCMarginCheck μ_lo W_hi err`
  the real score margin `μ_F − (A_C W_F + 90 + err)/99 − 350` is strictly positive.

**Firewall.**  The high-dimensional functional integrals defining `μ_F`, `W_F` are NOT
formalized.  They enter only as fields of the certified-input structure
`RouteCFunctionalCertificate`, which is never constructed.  The audited numerical values of
`μ_lo`, `W_hi` and of the frozen approximation error `err` were not supplied to this run; they are
parameters, and `RouteCMarginCheck` is a decidable rational inequality to be discharged by
`norm_num` once they are supplied.  The certificate carries no arithmetic moment.
-/

namespace Erdos287
namespace ResearchBankV16
namespace RouteCParameters

/-- `K = 2^82650`. -/
def K : ℕ := 2 ^ 82650

/-- `P = 12 K`. -/
def P : ℕ := 12 * K

/-- `a = 57384`. -/
def aParam : ℕ := 57384

/-- `δ = 1/80`. -/
def delta : ℚ := 1 / 80

/-- `θ_d = 273/500`. -/
def thetaD : ℚ := 273 / 500

/-- `ξ = 1/1000`. -/
def xi : ℚ := 1 / 1000

/-- `A_C = 1000273/273000`. -/
def A_C : ℚ := 1000273 / 273000

/-- Number of Route-C macro-groups. -/
def groups : ℕ := 26

/-- The Route-C score threshold `350 = 7 · 50`. -/
def threshold : ℚ := 350

/-- The Route-C pair-weight denominator `99`. -/
def pairDen : ℚ := 99

/-- The additive baseline constant `90`. -/
def baselineConst : ℚ := 90

theorem K_pos : 0 < K := pow_pos (by norm_num) _

theorem P_eq : P = 12 * K := rfl

/-- **`A_C = 2/θ_d + ξ`.** -/
theorem A_C_eq_two_div_theta_add_xi : A_C = 2 / thetaD + xi := by
  unfold A_C thetaD xi; norm_num

theorem A_C_pos : 0 < A_C := by unfold A_C; norm_num

theorem K_mod_26_aux : ∀ n : ℕ, 2 ^ (12 * n + 18) % 26 = 12 := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show 12 * (n + 1) + 18 = (12 * n + 18) + 12 by ring, pow_add, Nat.mul_mod, ih]
    norm_num

/-- `K ≡ 12 (mod 26)` (`2^12 ≡ 14`, `12 · 14 ≡ 12 (mod 26)`, `82650 = 12 · 6886 + 18`). -/
theorem K_mod_26 : K % 26 = 12 := by
  unfold K
  rw [show (82650 : ℕ) = 12 * 6886 + 18 by norm_num]; exact K_mod_26_aux 6886

/-- **Route-C functional certificate** (certified input; never constructed in the bank):
audited rational bounds on the functional constants.  No arithmetic moment appears here. -/
structure RouteCFunctionalCertificate (muLo WHi : ℚ) (muF WF : ℝ) : Prop where
  muF_gt : ((muLo : ℚ) : ℝ) < muF
  WF_lt : WF < ((WHi : ℚ) : ℝ)
  WF_nonneg : 0 ≤ WF

/-- The exact rational margin check at the audited bounds (decidable in `ℚ`). -/
def RouteCMarginCheck (muLo WHi err : ℚ) : Prop :=
  threshold + (A_C * WHi + baselineConst + err) / pairDen < muLo

/-- The rational margin at the audited bounds. -/
def marginAt (muLo WHi err : ℚ) : ℚ :=
  muLo - (A_C * WHi + baselineConst + err) / pairDen - threshold

theorem marginAt_pos {muLo WHi err : ℚ} (h : RouteCMarginCheck muLo WHi err) :
    0 < marginAt muLo WHi err := by
  unfold RouteCMarginCheck at h; unfold marginAt; linarith

/-- **Real score margin from the certificate.** -/
theorem routeC_margin_of_certificate {muLo WHi err : ℚ} {muF WF : ℝ}
    (C : RouteCFunctionalCertificate muLo WHi muF WF) :
    ((marginAt muLo WHi err : ℚ) : ℝ) <
      muF - (((A_C : ℚ) : ℝ) * WF + 90 + ((err : ℚ) : ℝ)) / 99 - 350 := by
  have hA : (0 : ℝ) < ((A_C : ℚ) : ℝ) := by exact_mod_cast A_C_pos
  have h1 := C.muF_gt
  have h2 : ((A_C : ℚ) : ℝ) * WF < ((A_C : ℚ) : ℝ) * ((WHi : ℚ) : ℝ) :=
    mul_lt_mul_of_pos_left C.WF_lt hA
  unfold marginAt threshold pairDen baselineConst
  push_cast
  linarith

theorem routeC_margin_pos {muLo WHi err : ℚ} {muF WF : ℝ}
    (C : RouteCFunctionalCertificate muLo WHi muF WF) (h : RouteCMarginCheck muLo WHi err) :
    0 < muF - (((A_C : ℚ) : ℝ) * WF + 90 + ((err : ℚ) : ℝ)) / 99 - 350 := by
  have := routeC_margin_of_certificate (err := err) C
  have h0 : (0 : ℝ) < ((marginAt muLo WHi err : ℚ) : ℝ) := by exact_mod_cast marginAt_pos h
  linarith

end RouteCParameters
end ResearchBankV16
end Erdos287
