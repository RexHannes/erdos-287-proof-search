import Mathlib
import RequestProject.Erdos287.BsrcWeights
import RequestProject.Erdos287.ProperGammaQFibre
import RequestProject.Erdos287.ProperGammaLaneRecombination

/-!
# Erdős #287 effectivity — the exact proper-γ source (§35)

```
PROPER-GAMMA SOURCE DEFINITION : KERNEL-PROVED (source-faithful algebra)
CLOSING ESTIMATE               : NOT ATTACHED / OPEN
ERDŐS #287                     : OPEN
```

The source is defined **source-faithfully**, retaining every physical marker:

    S_G^proper
      = −4 ∑_{q > q₀, q odd squarefree} β(q)
             ∑_{A^γ < z < Z^γ, (z,q) = 1} μ(z) B(z) e(z) 1_{zq live} I_X(z,q),

with `e(z)` the top-two γ admission, `1_{zq live}` the physical liveness marker, `I_X(z,q)`
the continuous endpoint datum, and the squarefree / coprimality / sign structure intact.  The
`q`-sum is replayed on the finite window `q ≤ Q_max`, so the object is a finite exact rational
expression; **no estimate of any kind is attached** to it here.

Kernel-proved algebra in this file: the even / non-squarefree `q` terms vanish
(`SGproper_drop_qfilter`), liveness kills a term (`SGproper_dead`), and two firewalls showing
that dropping the coprimality marker or the liveness marker genuinely *changes* the source.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287
namespace Effectivity

/-! ## §35.1  The source datum -/

/-- All physical data entering the proper-γ source: the normalisation `B1`, the γ-entry
window `A^γ < z < Z^γ`, the replayed `q`-window `q ≤ Q_max` with lower cutoff `q > qLower`,
the top-two γ admission `e`, the liveness marker and the continuous endpoint `I_X`. -/
structure ProperGammaData where
  /-- The physical normalisation constant. -/
  B1 : ℚ
  /-- The lower γ-entry endpoint `A^γ` (exclusive). -/
  Agam : ℕ
  /-- The upper γ-entry endpoint `Z^γ` (exclusive). -/
  Zgam : ℕ
  /-- The replayed `q`-window upper cutoff. -/
  Qmax : ℕ
  /-- The `q`-lower cutoff (`1` for the whole proper-γ source, `200` for the current
  survivor). -/
  qLower : ℕ
  /-- The top-two γ admission `e(z)`. -/
  adm : ℕ → ℚ
  /-- The physical liveness marker `1_{z q live}`. -/
  live : ℕ → ℕ → Bool
  /-- The continuous endpoint datum `I_X(z,q)`. -/
  IX : ℕ → ℕ → ℚ

/-- The exact `q`-condition of the proper-γ source: `q > qLower`, `q` odd and squarefree. -/
def ProperQ (D : ProperGammaData) (q : ℕ) : Prop :=
  D.qLower < q ∧ ¬ 2 ∣ q ∧ Squarefree q

instance (D : ProperGammaData) (q : ℕ) : Decidable (ProperQ D q) := by
  unfold ProperQ; infer_instance

/-- The exact `z`-weight of the source: `μ(z) B(z) e(z) 1_{zq live} I_X(z,q)`. -/
def sourceWeight (D : ProperGammaData) (z q : ℕ) : ℚ :=
  ((moebius z : ℤ) : ℚ) * B D.B1 z * D.adm z * (if D.live z q then 1 else 0) * D.IX z q

/-- The inner `z`-sum of the source at a fixed `q`. -/
def properZSum (D : ProperGammaData) (q : ℕ) : ℚ :=
  ∑ z ∈ (Finset.Ioo D.Agam D.Zgam) with Nat.Coprime z q, sourceWeight D z q

/-- **The exact proper-γ source.**  `KERNEL-PROVED DEFINITION`. -/
def SGproper (D : ProperGammaData) : ℚ :=
  -4 * ∑ q ∈ (Finset.Icc 1 D.Qmax) with ProperQ D q, beta q * properZSum D q

/-- **`SGproper_eq`.**  `KERNEL-PROVED`.  The definitional unfolding, kept as a named theorem
so that downstream files never re-inline the source. -/
theorem SGproper_eq (D : ProperGammaData) :
    SGproper D = -4 * ∑ q ∈ (Finset.Icc 1 D.Qmax) with ProperQ D q, beta q * properZSum D q :=
  rfl

/-! ## §35.2  Exact algebra of the source -/

/-- **`SGproper_drop_qfilter`.**  `KERNEL-PROVED`.  The odd/squarefree part of the `q`-filter
is redundant *for the value* of the source, because `β` vanishes on even and non-squarefree
arguments — but the cutoff `q > qLower` is **not** redundant. -/
theorem SGproper_drop_qfilter (D : ProperGammaData) :
    SGproper D
      = -4 * ∑ q ∈ (Finset.Icc 1 D.Qmax) with D.qLower < q, beta q * properZSum D q := by
  rw [SGproper, Finset.sum_filter, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : D.qLower < q
  · by_cases hodd : 2 ∣ q
    · simp [ProperQ, hq, hodd, beta_eq_zero_of_even hodd]
    · by_cases hsq : Squarefree q
      · simp [ProperQ, hq, hodd, hsq]
      · simp [ProperQ, hq, hodd, hsq, beta_eq_zero_of_not_squarefree hsq]
  · simp [ProperQ, hq]

/-- **`SGproper_dead`.**  `KERNEL-PROVED`.  If nothing is live, the source vanishes. -/
theorem SGproper_dead (D : ProperGammaData) (h : ∀ z q, D.live z q = false) :
    SGproper D = 0 := by
  have hz : ∀ q, properZSum D q = 0 := by
    intro q
    unfold properZSum
    refine Finset.sum_eq_zero fun z _ => ?_
    simp [sourceWeight, h z q]
  simp [SGproper, hz]

/-- **`SGproper_lane_weight`.**  `KERNEL-PROVED`.  The `z`-weight appearing in the source is
exactly the recombined lane weight of §32: for odd `d ≠ 0` and `c ∈ {1,2}`, the source weight
at `z = c d` equals `σ_c μ(d) B(d)`. -/
theorem SGproper_lane_weight (B1 : ℚ) {c d : ℕ} (hc : c = 1 ∨ c = 2) (hd : d ≠ 0)
    (hodd : ¬ 2 ∣ d) :
    ((moebius (c * d) : ℤ) : ℚ) * B B1 (c * d) = laneSign c * ((moebius d : ℤ) : ℚ) * B B1 d :=
  (lane_recombination B1 hc hd hodd).symm

/-! ## §35.3  Firewalls: the markers are not decoration -/

/-- The same source with the coprimality marker `(z,q) = 1` deleted. -/
def properZSumNoCoprime (D : ProperGammaData) (q : ℕ) : ℚ :=
  ∑ z ∈ Finset.Ioo D.Agam D.Zgam, sourceWeight D z q

/-- A concrete datum used by the firewalls: `A^γ = 1 < z < 4 = Z^γ`, all data equal to `1`. -/
def firewallData : ProperGammaData where
  B1 := 1
  Agam := 1
  Zgam := 4
  Qmax := 3
  qLower := 1
  adm := fun _ => 1
  live := fun _ _ => true
  IX := fun _ _ => 1

/-- The inner sum of the firewall datum, evaluated exactly. -/
theorem firewall_properZSum : properZSum firewallData 3 = -1 := by
  have hIoo : Finset.Ioo 1 4 = ({2, 3} : Finset ℕ) := by decide
  have hmu2 : (moebius 2 : ℤ) = -1 := by
    simpa using ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have hB2 : B (1 : ℚ) 2 = 1 := by
    have h : B0 2 = 1 := by simpa using B0_two_pow 1
    simp [B, h]
  unfold properZSum sourceWeight firewallData
  simp only [hIoo]
  rw [show (Finset.filter (fun z => Nat.Coprime z 3) ({2, 3} : Finset ℕ)) = {2} from by decide]
  simp [hmu2, hB2]

/-- The inner sum of the firewall datum with the coprimality marker deleted. -/
theorem firewall_properZSumNoCoprime : properZSumNoCoprime firewallData 3 = -3 := by
  have hIoo : Finset.Ioo 1 4 = ({2, 3} : Finset ℕ) := by decide
  have hmu2 : (moebius 2 : ℤ) = -1 := by
    simpa using ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have hmu3 : (moebius 3 : ℤ) = -1 := by
    simpa using ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3)
  have hB2 : B (1 : ℚ) 2 = 1 := by
    have h : B0 2 = 1 := by simpa using B0_two_pow 1
    simp [B, h]
  have hB3 : B (1 : ℚ) 3 = 2 := by
    rw [B, B0_prime (by norm_num) (by norm_num)]; norm_num
  unfold properZSumNoCoprime sourceWeight firewallData
  simp only [hIoo]
  rw [show ({2, 3} : Finset ℕ) = insert 2 {3} from rfl,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [hmu2, hmu3, hB2, hB3]
  norm_num

/-- **`coprimality_marker_matters`.**  `KERNEL-PROVED`.  Deleting the coprimality condition
changes the source: at `q = 3` the two inner sums differ. -/
theorem coprimality_marker_matters :
    properZSum firewallData 3 ≠ properZSumNoCoprime firewallData 3 := by
  rw [firewall_properZSum, firewall_properZSumNoCoprime]
  norm_num

/-- The firewall datum has a nonzero source. -/
theorem firewall_SGproper : SGproper firewallData = 4 := by
  have hfil : Finset.filter (fun q => ProperQ firewallData q)
      (Finset.Icc 1 firewallData.Qmax) = ({3} : Finset ℕ) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, ProperQ, firewallData]
    constructor
    · rintro ⟨⟨ha, hb⟩, hc, hd, -⟩
      omega
    · rintro rfl
      exact ⟨⟨by norm_num, by norm_num⟩, by norm_num, by decide,
        (by norm_num : Nat.Prime 3).squarefree⟩
  have hbeta3 : beta 3 = 1 := by
    rw [beta_prime (by norm_num) (by norm_num)]; norm_num
  rw [SGproper, hfil, Finset.sum_singleton, firewall_properZSum, hbeta3]
  norm_num

/-- **`liveness_marker_matters`.**  `KERNEL-PROVED`.  Deleting the liveness marker changes the
source: the all-dead datum has vanishing source while the all-live one does not. -/
theorem liveness_marker_matters :
    SGproper { firewallData with live := fun _ _ => false } = 0 ∧
      SGproper firewallData ≠ 0 := by
  refine ⟨SGproper_dead _ (fun _ _ => rfl), ?_⟩
  rw [firewall_SGproper]
  norm_num

end Effectivity
end Erdos287
