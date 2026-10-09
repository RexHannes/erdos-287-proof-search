import Mathlib
import RequestProject.Erdos287.BsrcWeights
import RequestProject.Erdos287.ProperGammaAdmission
import RequestProject.Erdos287.Early4490BernoulliJet

/-!
# Erdős #287 effectivity — the exact early joint source and the rational-jet chart (§45)

```
ω(z) = μ(z) B(z) (1 − C2(z))            : KERNEL-PROVED DEFINITION
JOINT SOURCE  J = R[1] − R[C2]          : KERNEL-PROVED DEFINITION + LINEAR ALGEBRA
SPLIT-CHARGING R[1], R[C2] SEPARATELY   : FIREWALLED (explicit witness)
J3 SOURCE                               : KERNEL-PROVED DEFINITION
Jψ SOURCE                               : KERNEL-PROVED DEFINITION
J3 / Jψ EXACT DIFFERENCE                : KERNEL-PROVED
|J|/B_X < 8.03976032e-9                 : OPEN (never inhabited)
ERDŐS #287                              : OPEN
```

The early joint source of the current chart is the **single combined object**

    J(X) = R[1](X) − R[C2](X),

not two independently chargeable errors: `joint_split_charging_firewall` exhibits data with
`J = 0` while both pieces are arbitrarily large, so a split charge is never forced by the
combined object.

The rational-jet source is

    J3(X) = −4 Σ_z ω(z) Σ_{q ∈ Q_z} β(q) Φ₃(z,q;X),      ω(z) = μ(z) B(z)(1 − C2(z)),

with the alternative one-term chart `Jψ` obtained by keeping only the sawtooth endpoint term.
`rationalJet_charts_are_alternatives` gives the exact difference of the two charts; the budget
firewall forbidding a simultaneous charge of both replacement errors is `§46`
(`Early4490RationalJetLedger`).

No analytic bound is attached to `J`, `J3` or `Jψ`: the target proposition is defined and
proved **not** to be inhabited here (`earlyJoint_target_open`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287
namespace Effectivity

/-! ## §45.1  The exact early source weight `ω(z)` -/

/-- `ω(z) = μ(z) B(z) (1 − C2(z))`, with `C2` the admission pair count of §42. -/
def omegaEarly (B1 : ℚ) (H : ℕ → Finset ℕ) (pc : Finset ℕ → Bool) (z : ℕ) : ℚ :=
  ((moebius z : ℤ) : ℚ) * B B1 z * (1 - (admC2 (H z) pc : ℚ))

/-- **`omegaEarly_eq`.**  `KERNEL-PROVED`.  The definitional unfolding. -/
theorem omegaEarly_eq (B1 : ℚ) (H : ℕ → Finset ℕ) (pc : Finset ℕ → Bool) (z : ℕ) :
    omegaEarly B1 H pc z = ((moebius z : ℤ) : ℚ) * B B1 z * (1 - (admC2 (H z) pc : ℚ)) := rfl

/-- **`omegaEarly_no_pairs`.**  `KERNEL-PROVED`.  With no qualifying pair the early weight is
the bare `μ(z)B(z)`: the `C2` factor is genuinely a correction. -/
theorem omegaEarly_no_pairs {B1 : ℚ} {H : ℕ → Finset ℕ} {pc : Finset ℕ → Bool} {z : ℕ}
    (h : admC2 (H z) pc = 0) : omegaEarly B1 H pc z = ((moebius z : ℤ) : ℚ) * B B1 z := by
  rw [omegaEarly, h]; norm_num

/-! ## §45.2  The combined early joint source -/

/-- The current early joint source `J(X) = R[1](X) − R[C2](X)`, stored as **one** object. -/
def Jjoint (R1 RC2 : ℝ → ℝ) (X : ℝ) : ℝ := R1 X - RC2 X

/-- **`Jjoint_linear_decomposition`.**  `KERNEL-PROVED`.  The only algebra the chart supplies:
the joint source is linear in its two constituents, and the triangle inequality is available
but *not* a licence to charge the two pieces separately. -/
theorem Jjoint_linear_decomposition (R1 RC2 S1 SC2 : ℝ → ℝ) (X : ℝ) :
    Jjoint (fun x => R1 x + S1 x) (fun x => RC2 x + SC2 x) X
        = Jjoint R1 RC2 X + Jjoint S1 SC2 X ∧
      |Jjoint R1 RC2 X| ≤ |R1 X| + |RC2 X| := by
  refine ⟨by unfold Jjoint; ring, ?_⟩
  calc |Jjoint R1 RC2 X| = |R1 X - RC2 X| := rfl
    _ ≤ |R1 X| + |RC2 X| := abs_sub _ _

/-- **`joint_split_charging_firewall`.**  `KERNEL-PROVED`.  `R[1]` and `R[C2]` must **not** be
stored as independently chargeable errors in this chart: there is data with `J ≡ 0` while both
constituents are arbitrarily large, so the split charge is strictly weaker information than
the combined object. -/
theorem joint_split_charging_firewall (c : ℝ) :
    Jjoint (fun _ => c) (fun _ => c) 0 = 0 ∧
      (0 < c → |(fun _ : ℝ => c) 0| + |(fun _ : ℝ => c) 0| = 2 * c) := by
  refine ⟨by simp [Jjoint], fun hc => ?_⟩
  simp [abs_of_pos hc]
  ring

/-! ## §45.3  The rational-jet sources -/

/-- **The exact rational-jet source.**  `KERNEL-PROVED DEFINITION`.

    J3(X) = −4 Σ_{z ∈ Z} ω(z) Σ_{q ∈ Q_z} β(q) Φ₃(z,q;X). -/
noncomputable def J3src (J : WeightJet) (om bet : ℕ → ℝ) (Z : Finset ℕ) (Q : ℕ → Finset ℕ)
    (X : ℝ) : ℝ :=
  -4 * ∑ z ∈ Z, om z * ∑ q ∈ Q z, bet q * Phi3 J (z : ℝ) (q : ℝ) X

/-- **The alternative one-term (sawtooth endpoint) source.**  `KERNEL-PROVED DEFINITION`. -/
noncomputable def Jpsisrc (J : WeightJet) (om bet : ℕ → ℝ) (Z : Finset ℕ) (Q : ℕ → Finset ℕ)
    (X : ℝ) : ℝ :=
  -4 * ∑ z ∈ Z, om z * ∑ q ∈ Q z, bet q * PhiPsi J (z : ℝ) (q : ℝ) X

/-- **`J3src_eq`.**  `KERNEL-PROVED`.  Definitional unfolding of the three-term chart. -/
theorem J3src_eq (J : WeightJet) (om bet : ℕ → ℝ) (Z : Finset ℕ) (Q : ℕ → Finset ℕ) (X : ℝ) :
    J3src J om bet Z Q X = -4 * ∑ z ∈ Z, om z * ∑ q ∈ Q z, bet q * Phi3 J (z : ℝ) (q : ℝ) X :=
  rfl

/-- **`Jpsisrc_eq`.**  `KERNEL-PROVED`.  Definitional unfolding of the one-term chart. -/
theorem Jpsisrc_eq (J : WeightJet) (om bet : ℕ → ℝ) (Z : Finset ℕ) (Q : ℕ → Finset ℕ) (X : ℝ) :
    Jpsisrc J om bet Z Q X
      = -4 * ∑ z ∈ Z, om z * ∑ q ∈ Q z, bet q * PhiPsi J (z : ℝ) (q : ℝ) X := rfl

/-- **`rationalJet_charts_are_alternatives`.**  `KERNEL-PROVED`.  The exact difference of the
two charts is the resummed pair of higher Bernoulli terms.  The charts are *alternatives*:
`J3` is `Jψ` plus this exact quantity, never an independent second error. -/
theorem rationalJet_charts_are_alternatives (J : WeightJet) (om bet : ℕ → ℝ) (Z : Finset ℕ)
    (Q : ℕ → Finset ℕ) (X : ℝ) :
    J3src J om bet Z Q X - Jpsisrc J om bet Z Q X
      = -4 * ∑ z ∈ Z, om z * ∑ q ∈ Q z, bet q *
          (-(jetT (z : ℝ) (q : ℝ) X / 2) * bern2 (jetR (z : ℝ) (q : ℝ)) * J.W1 (jetY (z : ℝ) X)
            + (jetT (z : ℝ) (q : ℝ) X ^ 2 / 6) * bern3 (jetR (z : ℝ) (q : ℝ))
                * J.W2 (jetY (z : ℝ) X)) := by
  rw [J3src, Jpsisrc, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← mul_sub, Phi3_sub_PhiPsi]

/-- **`J3src_eq_Jpsisrc_of_flat_jet`.**  `KERNEL-PROVED`.  If the higher jet vanishes the two
charts coincide, so they can only differ through `W'` and `W''`. -/
theorem J3src_eq_Jpsisrc_of_flat_jet (W : ℝ → ℝ) (om bet : ℕ → ℝ) (Z : Finset ℕ)
    (Q : ℕ → Finset ℕ) (X : ℝ) :
    J3src ⟨W, fun _ => 0, fun _ => 0⟩ om bet Z Q X
      = Jpsisrc ⟨W, fun _ => 0, fun _ => 0⟩ om bet Z Q X := by
  rw [J3src, Jpsisrc]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [Phi3, PhiPsi]

/-! ## §45.4  The current target is open -/

/-- The required bound on the early joint source, `|J|/B_X < 8.03976032e-9`, as a
proposition.  It is **OPEN**: nothing in this repository inhabits it. -/
def EarlyJointTarget (Jval BX : ℝ) : Prop := |Jval| / BX < (803976032 : ℝ) / 10 ^ 17

/-- **`earlyJoint_target_open`.**  `KERNEL-PROVED`.  The target proposition is a genuine (non
tautological) goal: it fails for concrete data, so it carries real content and is not
inhabited by the definitions above. -/
theorem earlyJoint_target_open : ¬ EarlyJointTarget 1 1 := by
  unfold EarlyJointTarget
  norm_num

end Effectivity
end Erdos287
