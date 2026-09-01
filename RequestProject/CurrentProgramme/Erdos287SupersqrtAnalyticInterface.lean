import Mathlib
import RequestProject.Erdos287.MuLogQCell3221
import RequestProject.Erdos287.HighConductorVariance3221
import RequestProject.CurrentProgramme.Erdos287PhysicalBComparisonV2
import RequestProject.CurrentProgramme.Erdos287Supersqrt3221Dictionary
import RequestProject.CurrentProgramme.Erdos287StrictCellProductWeightBridge

/-!
# Semantic repair layer §14, §15, §21–§24 — the centered source compiler and the
super-square-root analytic interface

* §1 the exact centered source identity `centered = raw − principal`, and the reduction of
  the raw sum to the banked Möbius–log identity `Λ(2P+s) = ∑_{q ∣ N} μ(q) log(N/q)`;
* §2 the deterministic centered source compiler, conditional on
  `SP2PhysicalTwoBIndependent287InputV2` (which is **not** proved here);
* §3 the sub-square-root character large-sieve interface `SP2SubSqrtCharacterLargeSieveInput`
  — uninhabited — and the deterministic compiler from it;
* §4 the first-Cauchy sign firewall for the current super-sqrt source: any post-Cauchy route
  is **sign-blind**;
* §5 the pure-data object `SP2LabelledSingletonCenteredQCellSupersqrtData` (no analytic
  field) and the one-field analytic interface
  `SP2LabelledSingletonCenteredQCellSupersqrtInput`, left **uninhabited**, with an explicit
  nonautomatic counterguard.

Nothing analytic is proved.  `SP2-LABELLED-SINGLETON-CENTERED-QCELL-SUPERSQRT45` remains
open.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open ArithmeticFunction

namespace Erdos287
namespace SupersqrtFrontier

open Finset
open Erdos287.Vaughan
open Erdos287.MuLog
open Erdos287.V23QCell
open Erdos287.HighCond3221
open Erdos287.BComparisonV2
open Erdos287.SP2Source
open Erdos287.StrictCellSingleton
open Erdos287.StrictCellBridge
open Erdos287.V23Comparison

/-! ## §1.  The exact centered source identity -/

/-- The logarithmic amplitude `log(N/q)` of the `q`-cell (exact natural division on the
divisor locus). -/
noncomputable def logAmp (N q : ℕ) : ℝ := ArithmeticFunction.log (N / q)

/-- The raw `q`-cell sum: the `μ·log` mass carried by the divisibility locus. -/
noncomputable def rawSum (s : AffineSign) (Q : Finset ℕ) (P : ℤ) (N : ℕ) : ℝ :=
  ∑ q ∈ Q, (moebius q : ℝ) * logAmp N q * (if ((q : ℤ) ∣ 2 * P + s.val) then 1 else 0)

/-- The principal `q`-cell sum: the `μ·log/φ` mass. -/
noncomputable def principalSum (Q : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ q ∈ Q, (moebius q : ℝ) * logAmp N q * ((q.totient : ℝ))⁻¹

/-- The centered `q`-cell sum: the `μ·log` mass against `1_{q ∣ 2P+s} − 1/φ(q)`. -/
noncomputable def centeredSum (s : AffineSign) (Q : Finset ℕ) (P : ℤ) (N : ℕ) : ℝ :=
  ∑ q ∈ Q, (moebius q : ℝ) * logAmp N q *
    ((if ((q : ℤ) ∣ 2 * P + s.val) then 1 else 0) - ((q.totient : ℝ))⁻¹)

/-- **`centered_eq_raw_sub_principal`.**  `LEAN_PROVED`.

The exact linear identity `centered = raw − principal`. -/
theorem centered_eq_raw_sub_principal (s : AffineSign) (Q : Finset ℕ) (P : ℤ) (N : ℕ) :
    centeredSum s Q P N = rawSum s Q P N - principalSum Q N := by
  rw [centeredSum, rawSum, principalSum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- **`rawSum_eq_vonMangoldt`.**  `LEAN_PROVED`.

For a `q`-range containing all divisors of `N = 2P + s`, the raw sum is exactly the banked
Möbius–log value of the von Mangoldt function. -/
theorem rawSum_eq_vonMangoldt {s : AffineSign} {Q : Finset ℕ} {P : ℤ} {N : ℕ}
    (hN0 : N ≠ 0) (hN : (N : ℤ) = 2 * P + s.val) (hsub : N.divisors ⊆ Q) :
    rawSum s Q P N = vonMangoldt N := by
  classical
  have hzero : ∀ q ∈ Q, q ∉ N.divisors →
      (moebius q : ℝ) * logAmp N q * (if ((q : ℤ) ∣ 2 * P + s.val) then 1 else 0) = 0 := by
    intro q _ hq
    by_cases hdvd : ((q : ℤ) ∣ 2 * P + s.val)
    · exfalso
      rw [← hN] at hdvd
      exact hq (Nat.mem_divisors.mpr ⟨Int.ofNat_dvd.mp hdvd, hN0⟩)
    · rw [if_neg hdvd, mul_zero]
  have hres : ∀ q ∈ N.divisors,
      (moebius q : ℝ) * logAmp N q * (if ((q : ℤ) ∣ 2 * P + s.val) then 1 else 0)
        = (moebius q : ℝ) * ArithmeticFunction.log (N / q) := by
    intro q hq
    have hdvd : ((q : ℤ) ∣ 2 * P + s.val) := by
      rw [← hN]
      exact Int.ofNat_dvd.mpr (Nat.mem_divisors.mp hq).1
    rw [if_pos hdvd, mul_one, logAmp]
  rw [rawSum, ← Finset.sum_subset hsub hzero, Finset.sum_congr rfl hres]
  exact (vonMangoldt_eq_sum_divisors N).symm

/-- **`centered_source_identity`.**  `LEAN_PROVED`.

The exact deterministic identity behind the centered source:

```
    Λ(2P+s) − principal(Q,N) = centered(s,Q,P,N).
```
-/
theorem centered_source_identity {s : AffineSign} {Q : Finset ℕ} {P : ℤ} {N : ℕ}
    (hN0 : N ≠ 0) (hN : (N : ℤ) = 2 * P + s.val) (hsub : N.divisors ⊆ Q) :
    vonMangoldt N - principalSum Q N = centeredSum s Q P N := by
  rw [centered_eq_raw_sub_principal, rawSum_eq_vonMangoldt hN0 hN hsub]

/-! ## §2.  The centered source compiler, conditional on the B-V2 interface -/

/-- **`centered_source_compiler_of_BV2`.**  `CONDITIONAL / LEAN_PROVED`.

Given the V2 aggregate input and the identification of the physical aggregate `J` with the
principal `q`-cell sum, the deterministic conclusion is

```
    Λ(2P+s) − 2·Bsrc(Pmod) = centered(s,Q,P,N) + Err,   |Err| ≤ Cerr·log(z)^{−A}.
```

The V2 analytic premise is **not** proved here. -/
theorem centered_source_compiler_of_BV2
    {C : SP2PhysicalCell} {BsrcFun : ℕ → ℝ} {J : ℕ → ℝ → ℝ} {Aexp Cerr z0 : ℝ}
    (hV2 : SP2PhysicalTwoBIndependent287InputV2 C BsrcFun J Aexp Cerr z0)
    {pv : Fin 7 → ℕ} (hpv : pv ∈ C.cell) {z : ℝ} (hz : z0 ≤ z)
    {s : AffineSign} {Q : Finset ℕ} {P : ℤ} {N : ℕ}
    (hN0 : N ≠ 0) (hN : (N : ℤ) = 2 * P + s.val) (hsub : N.divisors ⊆ Q)
    (hJ : J (physModulus pv) z = principalSum Q N) :
    vonMangoldt N - 2 * BsrcFun (physModulus pv)
        = centeredSum s Q P N + (J (physModulus pv) z - 2 * BsrcFun (physModulus pv))
      ∧ |J (physModulus pv) z - 2 * BsrcFun (physModulus pv)|
          ≤ Cerr * (Real.log z) ^ (-Aexp) := by
  refine ⟨?_, hV2.aggregate_limit pv hpv z hz⟩
  have hid := centered_source_identity hN0 hN hsub
  rw [hJ] at *
  linarith [hid]

/-! ## §3.  The sub-square-root character large-sieve interface (uninhabited) -/

/-- **`SP2SubSqrtCharacterLargeSieveInput`** — `EXTERNAL / UNINHABITED`.

The sub-square-root packet estimate `|R_s(Q)| ≪ Q·X^{1/2}·L^{−5/2+C}`, as a pointwise
interface on the `q`-box.  No inhabitant is constructed; the multiplicative large sieve is
**not** encoded as an axiom. -/
structure SP2SubSqrtCharacterLargeSieveInput (Qbox : Finset ℕ) (coeff : ℕ → ℂ)
    (X L Csrc Cbound : ℝ) : Prop where
  /-- The implied constant is positive. -/
  const_pos : 0 < Cbound
  /-- The scale is large. -/
  scale_large : 2 ≤ L
  /-- The pointwise sub-square-root estimate. -/
  sub_sqrt_bound : ∀ q ∈ Qbox,
    ‖coeff q‖ ≤ Cbound * (q : ℝ) * X ^ (1 / 2 : ℝ) * L ^ (-(5 : ℝ) / 2 + Csrc)

/-- **`subSqrt_compiler`.**  `CONDITIONAL / LEAN_PROVED`.

The deterministic consequence: summing the pointwise interface over the `q`-box. -/
theorem subSqrt_compiler {Qbox : Finset ℕ} {coeff : ℕ → ℂ} {X L Csrc Cbound Qmax : ℝ}
    (h : SP2SubSqrtCharacterLargeSieveInput Qbox coeff X L Csrc Cbound)
    (hX : 0 ≤ X ^ (1 / 2 : ℝ)) (hL : 0 ≤ L ^ (-(5 : ℝ) / 2 + Csrc))
    (hQ : ∀ q ∈ Qbox, (q : ℝ) ≤ Qmax) :
    ∑ q ∈ Qbox, ‖coeff q‖
      ≤ (Qbox.card : ℝ) * Cbound * Qmax * X ^ (1 / 2 : ℝ) * L ^ (-(5 : ℝ) / 2 + Csrc) := by
  have hterm : ∀ q ∈ Qbox, ‖coeff q‖
      ≤ Cbound * Qmax * X ^ (1 / 2 : ℝ) * L ^ (-(5 : ℝ) / 2 + Csrc) := by
    intro q hq
    refine le_trans (h.sub_sqrt_bound q hq) ?_
    have hmul : Cbound * (q : ℝ) ≤ Cbound * Qmax :=
      mul_le_mul_of_nonneg_left (hQ q hq) h.const_pos.le
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmul hX) hL
    linarith [this]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  ring_nf
  exact le_refl _

/-- **`subSqrt_input_not_automatic`.**  `LEAN_PROVED`. -/
theorem subSqrt_input_not_automatic :
    ∃ (Qbox : Finset ℕ) (coeff : ℕ → ℂ) (X L Csrc Cbound : ℝ),
      ¬ SP2SubSqrtCharacterLargeSieveInput Qbox coeff X L Csrc Cbound := by
  refine ⟨∅, fun _ => 0, 0, 0, 0, 0, ?_⟩
  intro h
  exact absurd h.const_pos (by norm_num)

/-! ## §4.  The first-Cauchy sign firewall for the super-sqrt source -/

/-- The sign policy of a route. -/
inductive SignPolicy
  /-- The route has consumed the `μ(q)` sign in a Cauchy step. -/
  | signBlind
  /-- The route still carries the linear `μ(q)` sign. -/
  | signAware
  deriving DecidableEq, Repr

/-- Any post-Cauchy route of the current super-sqrt source is sign-blind. -/
def supersqrtRoutePolicy : SignPolicy := SignPolicy.signBlind

theorem supersqrt_route_is_sign_blind : supersqrtRoutePolicy = SignPolicy.signBlind := rfl

theorem supersqrt_route_not_sign_aware : supersqrtRoutePolicy ≠ SignPolicy.signAware := by
  decide

/-- **`supersqrt_firstCauchy_sign_firewall`.**  `LEAN_PROVED` (reuse).

The banked Cauchy step bounds the source by a quantity depending on the `q`-weight only
through its square, and two weight systems with equal squares have different pre-Cauchy
values.  Hence no downstream compiler of the super-sqrt route may reuse linear `μ(q)`
cancellation. -/
theorem supersqrt_firstCauchy_sign_firewall :
    (∀ (Q : Finset ℕ) (mu : ℕ → ℝ) (X : ℕ → ℂ),
        ‖∑ q ∈ Q, (mu q : ℂ) * X q‖ ^ 2
          ≤ (∑ q ∈ Q, mu q ^ 2) * (∑ q ∈ Q, ‖X q‖ ^ 2)) ∧
      ∃ (Q : Finset ℕ) (mu nu : ℕ → ℝ) (X : ℕ → ℂ),
        (∀ q ∈ Q, mu q ^ 2 = nu q ^ 2) ∧
          ‖∑ q ∈ Q, (mu q : ℂ) * X q‖ ≠ ‖∑ q ∈ Q, (nu q : ℂ) * X q‖ :=
  ⟨firstCauchy_sign_consumption, firstCauchy_loses_sign_information⟩

/-! ## §5.  The super-sqrt physical data object and its analytic interface -/

/-- The `Q`-range label of the data object. -/
inductive QRangeLabel
  /-- `Q ≤ √X`-type packets. -/
  | subSqrt
  /-- `Q > √X`-type packets: the current residual. -/
  | superSqrt
  deriving DecidableEq, Repr

/-- **`SP2LabelledSingletonCenteredQCellSupersqrtData`** — pure finite/source data for the
current analytic residual.  **No analytic bound field appears in this structure.** -/
structure SP2LabelledSingletonCenteredQCellSupersqrtData where
  /-- The `Q`-box. -/
  Qbox : Finset ℕ
  /-- The affine sign `s = ±1`. -/
  sign : AffineSign
  /-- The seven physical slot transforms. -/
  slotTransform : Fin 7 → ℂ
  /-- The centred inverse residue `a_s(q)`. -/
  centredResidue : (q : ℕ) → ZMod q
  /-- The smooth / nuclear coefficient. -/
  nuclear : ℝ
  /-- The exact `q`-weight metadata. -/
  qWeight : ℕ → ℝ
  /-- The range label: this datum lives beyond the square-root barrier. -/
  range : QRangeLabel
  /-- Optional `2 + 5` dictionary data: the outer modulus and the inner modulus. -/
  splitData : Option (ℕ × ℕ)
  /-- Every modulus is positive. -/
  q_pos : ∀ q ∈ Qbox, 0 < q
  /-- Every modulus is odd. -/
  q_odd : ∀ q ∈ Qbox, Odd q
  /-- The `q`-weight is nonnegative (it is a post-Cauchy square). -/
  qWeight_nonneg : ∀ q ∈ Qbox, 0 ≤ qWeight q
  /-- The datum is in the super-square-root range. -/
  is_superSqrt : range = QRangeLabel.superSqrt

/-- The finite residual functional attached to the data. -/
noncomputable def supersqrtResidual
    (D : SP2LabelledSingletonCenteredQCellSupersqrtData) : ℝ :=
  ∑ q ∈ D.Qbox, D.qWeight q * ‖∏ j, D.slotTransform j‖ * |D.nuclear|

/-- **`SP2LabelledSingletonCenteredQCellSupersqrtInput`** — `OPEN ANALYTIC / UNINHABITED`.

`SP2-LABELLED-SINGLETON-CENTERED-QCELL-SUPERSQRT45`.  One field only: the residual bound in
the range `X^{1/2}L^{−C} < Q ≤ X^{3/5}`.  **No inhabitant is constructed anywhere in this
repository.** -/
structure SP2LabelledSingletonCenteredQCellSupersqrtInput
    (D : SP2LabelledSingletonCenteredQCellSupersqrtData) (bound : ℝ) : Prop where
  /-- The residual bound. -/
  residual_bound : supersqrtResidual D ≤ bound

/-- **`supersqrt_input_not_automatic`.**  `LEAN_PROVED`.

The counterguard: the interface is a genuine restriction, refuted at explicit data. -/
theorem supersqrt_input_not_automatic :
    ∃ (D : SP2LabelledSingletonCenteredQCellSupersqrtData) (bound : ℝ),
      ¬ SP2LabelledSingletonCenteredQCellSupersqrtInput D bound := by
  classical
  refine ⟨⟨{1}, AffineSign.plus, fun _ => 1, fun q => (0 : ZMod q), 1, fun _ => 1,
    QRangeLabel.superSqrt, none, ?_, ?_, ?_, rfl⟩, -1, ?_⟩
  · intro q hq; simp at hq; omega
  · intro q hq; simp at hq; subst hq; exact odd_one
  · intro q _; norm_num
  · intro h
    have hb := h.residual_bound
    rw [supersqrtResidual] at hb
    simp at hb
    linarith [hb]

/-- **`supersqrt_residual_nonneg`.**  `LEAN_PROVED`.

The residual functional is nonnegative, so a *negative* bound is impossible: any inhabitant
of the interface carries genuine analytic content. -/
theorem supersqrt_residual_nonneg (D : SP2LabelledSingletonCenteredQCellSupersqrtData) :
    0 ≤ supersqrtResidual D := by
  refine Finset.sum_nonneg fun q hq => ?_
  have := D.qWeight_nonneg q hq
  positivity

/-! ## §6.  Conditional reassembly: the owner-chain compiler -/

/-- **`generatedTypeII_of_owner_chain`.**  `CONDITIONAL / LEAN_PROVED`.

The deterministic reassembly compiler:

```
    corrected physical source (finite fields)
  + B-V2 aggregate input
  + sub-sqrt owner
  + super-sqrt input
  + the explicit owner-chain transfer
      ⟹  SP2-LABELLED-SINGLETON-GENERATEDTYPEII45.
```

Every analytic ingredient enters as an explicit premise; **none** of them is constructed
here, and in particular the super-sqrt input is left uninhabited. -/
theorem generatedTypeII_of_owner_chain
    {C : SP2FixedCertificateData} {U : Finset (Fin 7)} {Y Z : ℕ} {target : ℝ}
    {Cell : SP2PhysicalCell} {BsrcFun : ℕ → ℝ} {J : ℕ → ℝ → ℝ} {Aexp Cerr z0 : ℝ}
    {Qbox : Finset ℕ} {coeff : ℕ → ℂ} {X L Csrc Cbound : ℝ}
    {D : SP2LabelledSingletonCenteredQCellSupersqrtData} {bound : ℝ}
    (hstrict : StrictCellHypotheses C U)
    (hwin : ∀ (i : Fin 7), ∀ p ∈ C.lam i, Y ≤ p ∧ p ≤ Z)
    (hgain : target < 1)
    (hB : SP2PhysicalTwoBIndependent287InputV2 Cell BsrcFun J Aexp Cerr z0)
    (hsub : SP2SubSqrtCharacterLargeSieveInput Qbox coeff X L Csrc Cbound)
    (hsuper : SP2LabelledSingletonCenteredQCellSupersqrtInput D bound)
    (htransfer :
      SP2PhysicalTwoBIndependent287InputV2 Cell BsrcFun J Aexp Cerr z0 →
      SP2SubSqrtCharacterLargeSieveInput Qbox coeff X L Csrc Cbound →
      SP2LabelledSingletonCenteredQCellSupersqrtInput D bound →
      ∀ a b : ℕ → ℂ, (∀ n, ‖a n‖ ≤ 1) → (∀ n, ‖b n‖ ≤ 1) →
        ‖∑ v ∈ cellVectors C,
            a (v (canonicalSingleton U)) * b (∏ i ∈ sixPrimeComplement U, v i)‖
          ≤ target * ((cellVectors C).card : ℝ)) :
    SP2LabelledSingletonGeneratedTypeIIInput C U Y Z target where
  labelled := hstrict.branch_small
  window := hwin
  gain := hgain
  typeII := htransfer hB hsub hsuper

/-- **`owner_chain_does_not_construct_supersqrt_input`.**  `LEAN_PROVED`.

The compiler above is an implication only: the super-sqrt input is refuted at explicit data,
so nothing in this file inhabits it. -/
theorem owner_chain_does_not_construct_supersqrt_input :
    ∃ (D : SP2LabelledSingletonCenteredQCellSupersqrtData) (bound : ℝ),
      ¬ SP2LabelledSingletonCenteredQCellSupersqrtInput D bound :=
  supersqrt_input_not_automatic

end SupersqrtFrontier
end Erdos287
