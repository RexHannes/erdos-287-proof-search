import Mathlib
import RequestProject.Erdos287.CompensatedMeasure
import RequestProject.Erdos287.Early4490FiniteACompiler

/-!
# Erdős #287 effectivity — compensated summation by parts (§52)

```
COMPENSATED SUMMATION BY PARTS (exact) : KERNEL-PROVED
PRINCIPAL / ENDPOINT / Ê / JUMP SPLIT  : KERNEL-PROVED
NO SMALLNESS OF THE ERROR TERMS        : FIREWALL (explicit nonzero Ê witness)
```

The identity formalised here is the **exact discrete** compensated summation by parts on the
window `1 ≤ a ≤ Y`, in the strict Bernoulli endpoint convention already used by the bank
(the atom `a` carries the increment `G(a) − G(a−1)`, the endpoint contribution is evaluated
at the right endpoint and the lower endpoint enters through `G(0) = 0`):

    ∑_{1 ≤ a ≤ Y} a β(a) 1_{(a,M)=1} H(a)
        =  [ Ĝ_M(Y) H(Y) − ∑_{1 ≤ a < Y} Ĝ_M(a) ΔH(a) ]     (principal part)
         +   Ê_M(Y) H(Y)                                      (endpoint Ê term)
         − ∑_{1 ≤ a < Y} Ê_M(a) H'_reg(a)                     (regularised Ê term)
         − ∑_{1 ≤ a < Y} Ê_M(a) J(a)                          (hyperbola-interface jumps)

where the test increment splits as `ΔH(a) = H(a+1) − H(a) = H'_reg(a) + J(a)`, the jump part
`J` being supported on the hyperbola interfaces.  The continuous (integral) form of the same
identity is **not** claimed: it needs analytic integration by parts against a step measure and
is not reconstructed here.

**No error term is asserted to be small.**  `sbp_no_smallness_asserted` exhibits an explicit
finite instance in which the endpoint `Ê` term is nonzero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §52.1  The four parts -/

/-- The principal (density) part of the compensated summation by parts. -/
def sbpPrincipal (M : ℕ) (H : ℕ → ℚ) (Y : ℕ) : ℚ :=
  GhatM M Y * H Y - ∑ a ∈ Finset.Ico 1 Y, GhatM M a * (H (a + 1) - H a)

/-- The endpoint `Ê` term. -/
def sbpEndpoint (M : ℕ) (H : ℕ → ℚ) (Y : ℕ) : ℚ := EhatM M Y * H Y

/-- The regularised `Ê` term (the discrete analogue of `∫ Ê H'_reg`). -/
def sbpEhatReg (M : ℕ) (Hreg : ℕ → ℚ) (Y : ℕ) : ℚ :=
  ∑ a ∈ Finset.Ico 1 Y, EhatM M a * Hreg a

/-- The hyperbola-interface jump sum. -/
def sbpJump (M : ℕ) (J : ℕ → ℚ) (Y : ℕ) : ℚ :=
  ∑ a ∈ Finset.Ico 1 Y, EhatM M a * J a

@[simp] lemma GM_zero (M : ℕ) : GM M 0 = 0 := by simp [GM]

@[simp] lemma GhatM_zero (M : ℕ) : GhatM M 0 = 0 := by simp [GhatM]

@[simp] lemma EhatM_zero (M : ℕ) : EhatM M 0 = 0 := by simp [EhatM]

lemma GM_succ_sub (M a : ℕ) : GM M (a + 1) - GM M a = gz M (a + 1) := by
  rw [GM, GM, Finset.sum_Icc_succ_top (by omega)]
  ring

lemma GM_sub_pred {M a : ℕ} (ha : 1 ≤ a) : GM M a - GM M (a - 1) = gz M a := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  simpa using GM_succ_sub M b

/-! ## §52.2  The exact identity -/

/-- **`compensated_summation_by_parts`.**  `KERNEL-PROVED`.  The exact four-term compensated
summation by parts, in the strict Bernoulli endpoint convention.  The hypothesis `hsplit`
is the definition of the regularised increment and the interface jump; no estimate of any
term is asserted. -/
theorem compensated_summation_by_parts (M : ℕ) (H Hreg J : ℕ → ℚ) {Y : ℕ} (hY : 1 ≤ Y)
    (hsplit : ∀ a, H (a + 1) - H a = Hreg a + J a) :
    ∑ a ∈ Finset.Icc 1 Y, gz M a * H a
      = sbpPrincipal M H Y + sbpEndpoint M H Y - sbpEhatReg M Hreg Y - sbpJump M J Y := by
  have habel :
      ∑ a ∈ Finset.Icc 1 Y, (GM M a - GM M (a - 1)) * H a
        = GM M Y * H Y - GM M (1 - 1) * H 1
            - ∑ a ∈ Finset.Ico 1 Y, GM M a * (H (a + 1) - H a) :=
    abel_summation_general (GM M) H hY
  have hleft : ∑ a ∈ Finset.Icc 1 Y, gz M a * H a
      = ∑ a ∈ Finset.Icc 1 Y, (GM M a - GM M (a - 1)) * H a := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_Icc] at ha
    rw [GM_sub_pred ha.1]
  have hGsplit : ∀ a, GM M a = GhatM M a + EhatM M a := by
    intro a; rw [EhatM]; ring
  rw [hleft, habel]
  simp only [Nat.sub_self, GM_zero, zero_mul, sub_zero]
  rw [sbpPrincipal, sbpEndpoint, sbpEhatReg, sbpJump, hGsplit Y]
  have hsum : ∑ a ∈ Finset.Ico 1 Y, GM M a * (H (a + 1) - H a)
      = (∑ a ∈ Finset.Ico 1 Y, GhatM M a * (H (a + 1) - H a))
        + (∑ a ∈ Finset.Ico 1 Y, EhatM M a * Hreg a)
        + (∑ a ∈ Finset.Ico 1 Y, EhatM M a * J a) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hGsplit a, hsplit a]
    ring
  rw [hsum]
  ring

/-! ## §52.3  Firewall: no smallness is asserted -/

lemma gz_one_eq_one (M : ℕ) : gz M 1 = 1 := by
  simp [gz]

lemma etaM_one (M : ℕ) : etaM M 1 = 1 := by
  have h : hzRaw M 1 = 1 := by
    rw [hzRaw]
    norm_num [gz, Nat.coprime_one_left]
  simp [etaM, hz, h]

/-- **`sbp_no_smallness_asserted`.**  `KERNEL-PROVED`.  The compensated remainder is not
small by fiat: at `M = 1`, `Y = 1` the endpoint compensation equals `1/2 ≠ 0`, so the exact
identity above carries no bound on any of its terms. -/
theorem sbp_no_smallness_asserted : EhatM 1 1 = 1 / 2 ∧ EhatM 1 1 ≠ 0 := by
  have hG : GM 1 1 = 1 := by simp [GM, gz_one_eq_one]
  have hGh : GhatM 1 1 = 1 / 2 := by
    rw [GhatM]
    norm_num [etaM_one]
  refine ⟨by rw [EhatM, hG, hGh]; norm_num, ?_⟩
  rw [EhatM, hG, hGh]; norm_num

end Effectivity
end Erdos287
