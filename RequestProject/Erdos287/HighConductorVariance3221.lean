import Mathlib
import RequestProject.Erdos287.PrePoissonDensity3221

/-!
# V19, Phases C/D/G — first Cauchy, the high-conductor residue object, and the variance socket

`3221-FIRST-CAUCHY-SIGN-CONSUMPTION45 : LEAN_PROVED / PROVED_ALGEBRAIC`
`3221-RRRKKK-REASSEMBLY45 : LEAN_PROVED / PROVED_ALGEBRAIC`
`3221-HIGHCOND-RESIDUE-OBJECT45 : PROVED_FINITE`
`3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45 : OPEN_ANALYTIC / UNINHABITED`

Everything proved in this file is finite algebra or elementary Cauchy–Schwarz.  **The
analytic variance bound is not proved and not assumed**: it is isolated in the structure
`InverseSampledHighCondLogVar3221Input`, which has no inhabitant anywhere in this project.

## Contents

* **§5 First Cauchy / sign consumption.**  `firstCauchy_sign_consumption` records that
  `‖∑_q μ(q) X_q‖²` is controlled by an energy whose `q`-weight is `μ(q)² = |μ(q)|²`; the
  weight is therefore *unsigned* after the Cauchy step.  `postCauchy_weight_sign_invariant`
  proves the weight is invariant under arbitrary `q`-wise sign flips, and
  `firstCauchy_loses_sign_information` exhibits two weight systems with identical
  post-Cauchy energies but different pre-Cauchy values — so the original signed `μ(q)` is
  provably **not** retained by the bound.  For squarefree `q`, `moebius_sq_of_squarefree`
  records `μ(q)² = 1`.

* **§6 The high-conductor residue object.**  `residueSum` is the exact finite residue sum
  `C_q(a) = ∑_{w ≡ a (q)} c(w)`, with the partition identity
  `residueSum_sum_over_classes`.  The literal low/high conductor split is proved in
  `CharacterGram3221` (character machinery is available, so no free `Prop` placeholder is
  used anywhere).

* **§7 RR/RK/KK reassembly.**  `normSq_sub_reassembly` and
  `highConductorEnergy_reassembles_crossTerms`: the exact identity
  `|R − K|² = |R|² − 2 Re(R conj K) + |K|²`, lifted to the finite `(q, m)` energy.  This is
  `PROVED_ALGEBRAIC` only; **no claim is made that the physical comparison term is thereby
  matched**.

* **§13 The analytic socket.**  `InverseSampledHighCond3221Data` is pure explicit data (no
  `Prop` field is free), and `Vhi` is its inverse-sampled high-conductor energy.  The
  inverse sampling point `−s (2m)⁻¹` is *identified* with the pre-Poisson divisibility
  condition of Phase B by `samplePoint_iff_affineSampled`.

* **§14 The open analytic input.**  `InverseSampledHighCondLogVar3221Input`, uninhabited,
  with an explicit positive saving parameter `Lsave` and target `Vhi ≤ scale / Lsave`.  No
  asymptotic notation is faked.  Non-automaticity is proved constructively
  (`highCondLogVar_not_automatic`).

**Honesty statement.**  Erdős #287 remains OPEN; Balanced7 remains OPEN; the inverse-sampled
high-conductor logarithmic variance bound is the current first analytic open node and is
**not** proved here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators
open scoped Classical

namespace Erdos287
namespace HighCond3221

/-! ## §5. First Cauchy: consumption of the `μ(q)` sign -/

/-- **`firstCauchy_sign_consumption`.**  `LEAN_PROVED / PROVED_ALGEBRAIC`.

The weighted Cauchy–Schwarz step: for any real `q`-weight `mu` and any complex family `X`,

`‖∑_q mu(q) X_q‖² ≤ (∑_q mu(q)²) · (∑_q ‖X_q‖²)`.

The right-hand side depends on `mu` **only through `mu(q)²`**: the original sign is
consumed by the Cauchy step and does not survive into the post-Cauchy variance. -/
theorem firstCauchy_sign_consumption (Q : Finset ℕ) (mu : ℕ → ℝ) (X : ℕ → ℂ) :
    ‖∑ q ∈ Q, (mu q : ℂ) * X q‖ ^ 2
      ≤ (∑ q ∈ Q, mu q ^ 2) * (∑ q ∈ Q, ‖X q‖ ^ 2) := by
  have h1 : ‖∑ q ∈ Q, (mu q : ℂ) * X q‖ ≤ ∑ q ∈ Q, |mu q| * ‖X q‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun q _ => ?_)
    rw [norm_mul]
    simp
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Q (fun q => |mu q|) (fun q => ‖X q‖)
  have h3 : ∑ q ∈ Q, |mu q| ^ 2 = ∑ q ∈ Q, mu q ^ 2 :=
    Finset.sum_congr rfl fun q _ => sq_abs (mu q)
  rw [h3] at h2
  have hnn : (0 : ℝ) ≤ ‖∑ q ∈ Q, (mu q : ℂ) * X q‖ := norm_nonneg _
  nlinarith [h1, h2, hnn]

/-- **The post-Cauchy `q`-weight is sign-blind.**  Flipping the sign of `mu` at any subset
of moduli leaves the post-Cauchy energy weight unchanged. -/
theorem postCauchy_weight_sign_invariant (Q : Finset ℕ) (mu eps : ℕ → ℝ)
    (heps : ∀ q ∈ Q, eps q = 1 ∨ eps q = -1) :
    ∑ q ∈ Q, (eps q * mu q) ^ 2 = ∑ q ∈ Q, mu q ^ 2 := by
  refine Finset.sum_congr rfl fun q hq => ?_
  rcases heps q hq with h | h <;> rw [h] <;> ring

/-- For squarefree `q` the post-Cauchy weight is `μ(q)² = 1`; the signed weight `μ(q)` has
been replaced by its square. -/
theorem moebius_sq_of_squarefree {q : ℕ} (hq : Squarefree q) :
    (ArithmeticFunction.moebius q : ℤ) ^ 2 = 1 :=
  ArithmeticFunction.moebius_sq_eq_one_of_squarefree hq

/-- **The sign-consumption firewall.**  `LEAN_PROVED`.

Two weight systems with *identical* post-Cauchy energies but *different* pre-Cauchy values.
Hence the Cauchy step of §5 genuinely destroys the sign information, and nothing downstream
of it may reintroduce a cancellation coming from the sign of `μ`. -/
theorem firstCauchy_loses_sign_information :
    ∃ (Q : Finset ℕ) (mu nu : ℕ → ℝ) (X : ℕ → ℂ),
      (∀ q ∈ Q, mu q ^ 2 = nu q ^ 2) ∧
        ‖∑ q ∈ Q, (mu q : ℂ) * X q‖ ≠ ‖∑ q ∈ Q, (nu q : ℂ) * X q‖ := by
  refine ⟨{0, 1}, fun _ => 1, fun q => if q = 0 then 1 else -1, fun _ => 1, ?_, ?_⟩
  · intro q hq
    rcases Finset.mem_insert.mp hq with h | h <;> simp [h]
  · rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1),
      Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
    norm_num

/-! ## §6. The high-conductor residue object -/

/-- The exact finite residue sum `C_q(a) = ∑_{w ≡ a (mod q)} c(w)`. -/
noncomputable def residueSum (q : ℕ) (Wbox : Finset ℤ) (c : ℤ → ℂ) (a : ZMod q) : ℂ :=
  ∑ w ∈ Wbox.filter (fun v : ℤ => ((v : ZMod q)) = a), c w

/-- The residue sums partition the total: `∑_a C_q(a) = ∑_w c(w)`. -/
theorem residueSum_sum_over_classes (q : ℕ) [NeZero q] (Wbox : Finset ℤ) (c : ℤ → ℂ) :
    ∑ a : ZMod q, residueSum q Wbox c a = ∑ w ∈ Wbox, c w := by
  simpa [residueSum] using Finset.sum_fiberwise Wbox (fun w : ℤ => ((w : ZMod q))) c

/-! ## §7. RR / RK / KK reassembly -/

/-- **`normSq_sub_reassembly`.**  `PROVED_ALGEBRAIC`.

`|R − K|² = |R|² − 2 Re(R · conj K) + |K|²`. -/
theorem normSq_sub_reassembly (R K : ℂ) :
    ‖R - K‖ ^ 2 = ‖R‖ ^ 2 - 2 * (R * (starRingEnd ℂ) K).re + ‖K‖ ^ 2 := by
  have h : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [h, h, h]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **`highConductorEnergy_reassembles_crossTerms`.**  `PROVED_ALGEBRAIC`.

The finite `(q, m)` energy of the difference `R − K` reassembles exactly as
`RR − RK − KR + KK`: one square of the reconstructed high-conductor remainder.

This is an algebraic identity only.  **It does not assert that the physical comparison term
`K` matches anything**; that remains the independent, uninhabited comparison interface. -/
theorem highConductorEnergy_reassembles_crossTerms {ι κ : Type*} (Qs : Finset ι)
    (Ms : Finset κ) (wt : ι → ℝ) (R K : ι → κ → ℂ) :
    ∑ q ∈ Qs, wt q * ∑ m ∈ Ms, ‖R q m - K q m‖ ^ 2
      = (∑ q ∈ Qs, wt q * ∑ m ∈ Ms, ‖R q m‖ ^ 2)
        - 2 * (∑ q ∈ Qs, wt q * ∑ m ∈ Ms, (R q m * (starRingEnd ℂ) (K q m)).re)
        + ∑ q ∈ Qs, wt q * ∑ m ∈ Ms, ‖K q m‖ ^ 2 := by
  have key : ∀ q ∈ Qs, wt q * ∑ m ∈ Ms, ‖R q m - K q m‖ ^ 2
      = wt q * (∑ m ∈ Ms, ‖R q m‖ ^ 2)
        - 2 * (wt q * (∑ m ∈ Ms, (R q m * (starRingEnd ℂ) (K q m)).re))
        + wt q * (∑ m ∈ Ms, ‖K q m‖ ^ 2) := by
    intro q _
    have hinner : ∑ m ∈ Ms, ‖R q m - K q m‖ ^ 2
        = (∑ m ∈ Ms, ‖R q m‖ ^ 2)
          - 2 * (∑ m ∈ Ms, (R q m * (starRingEnd ℂ) (K q m)).re)
          + ∑ m ∈ Ms, ‖K q m‖ ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => normSq_sub_reassembly (R q m) (K q m)
    rw [hinner]; ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]

/-! ## §13. The inverse-sampled high-conductor variance socket

Pure data: every field is an explicit finite object or an explicit arithmetic condition.
There is **no free `Prop` field**. -/

/-- **`InverseSampledHighCond3221Data`.**  The concrete data of the current analytic node:
the `q`-range, the `m`-range, the sign `s = ±1`, the coefficient `c`, the high-conductor
residue function, the `q`- and `m`-weights and the conductor cutoff. -/
structure InverseSampledHighCond3221Data where
  /-- The modulus box. -/
  Qbox : Finset ℕ
  /-- The `m` box. -/
  Mbox : Finset ℕ
  /-- The `w` box carrying the coefficient. -/
  Wbox : Finset ℤ
  /-- The sign `s ∈ {−1, +1}`. -/
  sign : ℤ
  /-- `s² = 1`, i.e. `s = ±1`. -/
  sign_sq : sign ^ 2 = 1
  /-- The coefficient `c(w)`. -/
  coeff : ℤ → ℂ
  /-- The high-conductor part of the residue sum. -/
  CHigh : (q : ℕ) → ZMod q → ℂ
  /-- The `q`-weight (post-Cauchy, hence unsigned: `μ(q)²`). -/
  qWeight : ℕ → ℝ
  /-- The `m`-weight. -/
  mWeight : ℕ → ℝ
  /-- The conductor cutoff `D`. -/
  conductorCut : ℕ
  /-- Every modulus is positive. -/
  q_pos : ∀ q ∈ Qbox, 0 < q
  /-- Every modulus is odd, so `2` is invertible. -/
  q_odd : ∀ q ∈ Qbox, Odd q
  /-- `2m` is a unit modulo every `q` in the box, so the inverse sampling point exists. -/
  m_unit : ∀ m ∈ Mbox, ∀ q ∈ Qbox, Nat.Coprime (2 * m) q
  /-- The `q`-weight is nonnegative (it is a square). -/
  qWeight_nonneg : ∀ q ∈ Qbox, 0 ≤ qWeight q
  /-- The `m`-weight is nonnegative. -/
  mWeight_nonneg : ∀ m ∈ Mbox, 0 ≤ mWeight m

namespace InverseSampledHighCond3221Data

variable (D : InverseSampledHighCond3221Data)

/-- The inverse sampling point `a = −s · (2m)⁻¹` in `ZMod q`. -/
def samplePoint (q m : ℕ) : ZMod q := -(D.sign : ZMod q) * ((2 * m : ℕ) : ZMod q)⁻¹

/-- **`samplePoint_iff_affineSampled`.**  `LEAN_PROVED`.

The inverse sampling point is *exactly* the pre-Poisson affine divisibility condition of
Phase B: `w ≡ −s (2m)⁻¹ (mod q)` iff `q ∣ 2 m w + s`.  This is what makes the socket below
the same object as the divisor-density count. -/
theorem samplePoint_iff_affineSampled {q m : ℕ} (hq : q ∈ D.Qbox) (hm : m ∈ D.Mbox)
    (w : ℤ) :
    ((w : ZMod q) = D.samplePoint q m)
      ↔ Erdos287.PrePoisson3221.AffineSampled (q : ℤ) D.sign (m : ℤ) w := by
  haveI : NeZero q := ⟨(D.q_pos q hq).ne'⟩
  have hu : IsUnit ((2 * m : ℕ) : ZMod q) :=
    (ZMod.isUnit_iff_coprime (2 * m) q).mpr (D.m_unit m hm q hq)
  have hcast : ((2 * (m : ℤ) * w + D.sign : ℤ) : ZMod q)
      = ((2 * m : ℕ) : ZMod q) * (w : ZMod q) + (D.sign : ZMod q) := by
    push_cast; ring
  have hdvd : Erdos287.PrePoisson3221.AffineSampled (q : ℤ) D.sign (m : ℤ) w
      ↔ ((2 * ((m : ℤ) * w) + D.sign : ℤ) : ZMod q) = 0 := by
    rw [Erdos287.PrePoisson3221.AffineSampled,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [hdvd]
  have hcast' : ((2 * ((m : ℤ) * w) + D.sign : ℤ) : ZMod q)
      = ((2 * m : ℕ) : ZMod q) * (w : ZMod q) + (D.sign : ZMod q) := by
    rw [show 2 * ((m : ℤ) * w) + D.sign = 2 * (m : ℤ) * w + D.sign by ring]
    exact hcast
  rw [hcast']
  constructor
  · intro h
    rw [h, samplePoint]
    have : ((2 * m : ℕ) : ZMod q) * (-(D.sign : ZMod q) * ((2 * m : ℕ) : ZMod q)⁻¹)
        = -(D.sign : ZMod q) * (((2 * m : ℕ) : ZMod q) * ((2 * m : ℕ) : ZMod q)⁻¹) := by
      ring
    rw [this, ZMod.mul_inv_of_unit _ hu]
    ring
  · intro h
    have hw : ((2 * m : ℕ) : ZMod q) * (w : ZMod q) = -(D.sign : ZMod q) := by
      linear_combination h
    have : (w : ZMod q)
        = ((2 * m : ℕ) : ZMod q)⁻¹ * (((2 * m : ℕ) : ZMod q) * (w : ZMod q)) := by
      rw [← mul_assoc, ZMod.inv_mul_of_unit _ hu, one_mul]
    rw [this, hw, samplePoint]
    ring

/-- **The inverse-sampled high-conductor energy.**

`V_hi(D) = ∑_q μ²(q) ∑_m mWeight(m) · ‖C_q^{>D}(−s (2m)⁻¹)‖²`. -/
noncomputable def Vhi : ℝ :=
  ∑ q ∈ D.Qbox, D.qWeight q * ∑ m ∈ D.Mbox, D.mWeight m * ‖D.CHigh q (D.samplePoint q m)‖ ^ 2

/-- The energy is nonnegative. -/
theorem Vhi_nonneg : 0 ≤ D.Vhi := by
  refine Finset.sum_nonneg fun q hq => mul_nonneg (D.qWeight_nonneg q hq) ?_
  exact Finset.sum_nonneg fun m hm => mul_nonneg (D.mWeight_nonneg m hm) (sq_nonneg _)

end InverseSampledHighCond3221Data

/-! ## §14. The open analytic input — `OPEN_ANALYTIC / UNINHABITED` -/

/-- **`InverseSampledHighCondLogVar3221Input`** —
`3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45 : OPEN_ANALYTIC`.

The desired numerical bound on the concrete energy `V_hi`: natural scale divided by a
logarithmic saving.  Rather than faking asymptotic notation, the saving is carried by an
explicit positive parameter `Lsave`, and the target is literally `V_hi ≤ scale / Lsave`.

**This structure is never inhabited in this project**, and no theorem here produces one. -/
structure InverseSampledHighCondLogVar3221Input (D : InverseSampledHighCond3221Data)
    (naturalScale Lsave : ℝ) : Prop where
  /-- The natural scale is positive. -/
  naturalScale_pos : 0 < naturalScale
  /-- The logarithmic saving parameter is positive. -/
  Lsave_pos : 0 < Lsave
  /-- **The open analytic estimate.** -/
  variance_bound : D.Vhi ≤ naturalScale / Lsave

/-! ### Non-automaticity

The analytic input is a genuine restriction: there is explicit data refuting it, so no
compiler downstream can be made unconditional by choosing convenient parameters. -/

/-- Explicit probe data: one odd modulus `q = 3`, one `m = 1`, unit high-conductor
residue, unit weights.  Its energy is exactly `1`. -/
noncomputable def probeData : InverseSampledHighCond3221Data where
  Qbox := {3}
  Mbox := {1}
  Wbox := ∅
  sign := 1
  sign_sq := by norm_num
  coeff := fun _ => 0
  CHigh := fun _ _ => 1
  qWeight := fun _ => 1
  mWeight := fun _ => 1
  conductorCut := 0
  q_pos := by intro q hq; simp at hq; omega
  q_odd := by intro q hq; simp at hq; exact ⟨1, by omega⟩
  m_unit := by intro m hm q hq; simp at hm hq; subst hm; subst hq; decide
  qWeight_nonneg := by intro q _; norm_num
  mWeight_nonneg := by intro m _; norm_num

/-- The probe energy is `1`. -/
theorem probeData_Vhi : probeData.Vhi = 1 := by
  simp [InverseSampledHighCond3221Data.Vhi, probeData]

/-- **`highCondLogVar_not_automatic`.**  `LEAN_PROVED`.

The inverse-sampled high-conductor variance input is **not** automatically satisfiable:
the probe data refutes it at natural scale `1` and saving `2`. -/
theorem highCondLogVar_not_automatic :
    ∃ (D : InverseSampledHighCond3221Data) (naturalScale Lsave : ℝ),
      0 < naturalScale ∧ 0 < Lsave ∧
        ¬ InverseSampledHighCondLogVar3221Input D naturalScale Lsave := by
  refine ⟨probeData, 1, 2, by norm_num, by norm_num, ?_⟩
  intro h
  have := h.variance_bound
  rw [probeData_Vhi] at this
  norm_num at this

end HighCond3221
end Erdos287
