import RequestProject.CurrentProgramme.NeutralFordSharedOtherParent

/-!
# Erdős #287 — §4  the effective `N2` constants bank, and §10 the `Ω_H` provenance firewall

```
C_2LF = 1078, C_ps = 3, C_Bps = 25                       : BANKED NUMERICAL DATA
K_collar ≤ 107222726423465                               : BANKED NUMERICAL DATA
ε = 1/2·10²¹,  X_N2 = ⌈exp(2·10²²)⌉                       : BANKED NUMERICAL DATA
2·X_N2 ≤ 4·10⁹                                            : KERNEL-PROVED FALSE
N2 finite splice for the current constants                : FAILS (kernel-proved)
Ω_H provenance                                            : UNRESOLVED (no silent default)
```

Nothing here asserts the *analytic* `N2` theorem: only the recorded numerical data and the
arithmetic consequence that the current constants do **not** splice into the finite bank
ceiling `M ≤ 4·10⁹`.  "Effective in principle" is therefore kept strictly separate from a
usable `M₀`.

This module is **append-only**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace N2ConstantsBank

/-! ## §4.1  The banked numerical data -/

/-- `C_2LF = 1078`. -/
def C_2LF : ℕ := 1078

/-- `C_ps = 3`. -/
def C_ps : ℕ := 3

/-- `C_Bps = 25`. -/
def C_Bps : ℕ := 25

/-- The banked upper bound for the collar constant `K_collar`. -/
def K_collar_bound : ℕ := 107222726423465

/-- `ε = 1 / 2·10²¹`. -/
noncomputable def epsilonN2 : ℝ := 1 / 2000000000000000000000

/-- The exponent of the `N2` threshold: `2·10²²`. -/
noncomputable def logXN2 : ℝ := 20000000000000000000000

/-- `X_N2 = ⌈exp(2·10²²)⌉`. -/
noncomputable def XN2 : ℕ := ⌈Real.exp logXN2⌉₊

/-- The finite-bank ceiling of the public finite theorem. -/
def finiteBankCeiling : ℕ := 4000000000

/-! ## §4.2  The splice arithmetic -/

/-- **`XN2_lower_bound`.**  `KERNEL-PROVED`.  `X_N2 ≥ exp(2·10²²) ≥ 1 + 2·10²²`. -/
theorem XN2_lower_bound : (2000000000000 : ℝ) ≤ (XN2 : ℝ) := by
  have h1 : logXN2 + 1 ≤ Real.exp logXN2 := Real.add_one_le_exp logXN2
  have h2 : Real.exp logXN2 ≤ (XN2 : ℝ) := Nat.le_ceil _
  have h3 : (2000000000000 : ℝ) ≤ logXN2 + 1 := by
    unfold logXN2
    norm_num
  linarith

/-- **`two_XN2_exceeds_finite_bank`.**  `KERNEL-PROVED`.  The literal record:

```
2 · X_N2 ≤ 4·10⁹   is   FALSE.
```
-/
theorem two_XN2_exceeds_finite_bank : ¬ (2 * XN2 ≤ finiteBankCeiling) := by
  intro h
  have hR : ((2 * XN2 : ℕ) : ℝ) ≤ ((finiteBankCeiling : ℕ) : ℝ) := by exact_mod_cast h
  have hlow := XN2_lower_bound
  have hceil : ((finiteBankCeiling : ℕ) : ℝ) = 4000000000 := by
    unfold finiteBankCeiling
    norm_num
  rw [hceil] at hR
  push_cast at hR
  linarith

/-- **`n2_finite_splice_fails`.**  `KERNEL-PROVED`.  With the current constants the `N2`
threshold cannot be spliced into the finite bank: `X_N2` alone already exceeds the ceiling. -/
theorem n2_finite_splice_fails : finiteBankCeiling < XN2 := by
  have hlow := XN2_lower_bound
  have hlt : ((finiteBankCeiling : ℕ) : ℝ) < (XN2 : ℝ) := by
    have hceil : ((finiteBankCeiling : ℕ) : ℝ) = 4000000000 := by
      unfold finiteBankCeiling
      norm_num
    rw [hceil]
    linarith
  exact_mod_cast hlt

/-- **`effective_in_principle_is_not_a_usable_M0`.**  `KERNEL-PROVED`.  Having an effective
threshold does not produce a usable `M₀ ≤ 4·10⁹`: the banked one provably does not. -/
theorem effective_in_principle_is_not_a_usable_M0 :
    ¬ (XN2 ≤ finiteBankCeiling) := by
  intro h
  exact absurd n2_finite_splice_fails (not_lt.mpr h)

end N2ConstantsBank

/-! ## §10  The `Ω_H` provenance firewall -/

namespace OmegaHProvenance

/-- The provenance of the shared-gcd coordinate `Ω_H`. -/
inductive Provenance
  /-- `Ω_H` is introduced by the proof and may legally be re-anchored. -/
  | proofLocal
  /-- `Ω_H` is a physical source datum; re-anchoring needs a different theorem. -/
  | physicalSource
  /-- Not yet determined by the source history.  No silent default is permitted. -/
  | unresolved
  deriving DecidableEq, Fintype, Repr

/-- The authoritative current provenance value. -/
def current : Provenance := Provenance.unresolved

/-- **`current_is_unresolved`.**  `KERNEL-PROVED`. -/
theorem current_is_unresolved : current = Provenance.unresolved := rfl

/-- **`no_silent_default`.**  `KERNEL-PROVED`.  The current value is neither of the two
resolutions, so nothing downstream may assume either. -/
theorem no_silent_default :
    current ≠ Provenance.proofLocal ∧ current ≠ Provenance.physicalSource := by
  constructor <;> decide

/-- **`reanchoring_requires_proof_local`.**  `KERNEL-PROVED`.  Re-anchoring is legal only in
the proof-local case, which is not the current value. -/
theorem reanchoring_requires_proof_local (h : current = Provenance.proofLocal) : False := by
  exact (no_silent_default.1) h

end OmegaHProvenance
end Erdos287
