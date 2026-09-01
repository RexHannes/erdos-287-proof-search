import RequestProject.CurrentProgramme.Erdos287BalancedBUnitaryFourierCompiler

/-!
# Erdős #287 — the abstract `Δ × q_a` finite Fourier kernel (b-diagonal pivot)

This module formalises the **abstract finite kernel** underlying the latest b-diagonal
pivot.  Everything here is a finite, unconditional theorem about sums over residues; it is
an *abstract* kernel theorem and is explicitly **not** a physical statement about the
Erdős #287 b-diagonal: the physical realisation is the uninhabited dictionary interface of
`Erdos287PhysicalDictionaryInterfaces`.

Contents.

* §1 `deltaQ_unitaryFourier_bound` — for a unit `u`, unit-supported `Δ` and `q` ranges,
  `‖∑_{Δ,q} A Δ · B q · e_n(Δ u q⁻¹)‖² ≤ n (∑_Δ ‖A Δ‖²)(∑_q ‖B q‖²)`.
  Proved by reduction to the already banked reciprocal unitary Fourier bound (substitution
  `Δ = r⁻¹`); no second Fourier proof.
* §2 `phase_fiberwise` — residue aggregation for an *arbitrary* phase function
  (a generalisation of the banked `reciprocalPhase_fiberwise`).
* §3 `deltaQ_residueAggregation_compiler` — the exact finite residue-aggregation form:
  with fibre multiplicities `M_Δ`, `M_q` (for physical ranges of lengths `D`, `E` these are
  `D/n + 1` and `E/n + 1`, i.e. the `1 + D/n`, `1 + E/n` factors),
  `‖S‖² ≤ n · M_Δ · M_q · E_A · E_B`, and its square-root form.
* §4 the interval instantiation supplying `M_Δ = D/n + 1`, `M_q = E/n + 1`.
* §5 `cauchy_over_t` and `deltaQ_cauchy_over_t` — the Cauchy step over `t`:
  `‖∑_t S_t‖² ≤ n (1 + D/n)(1 + E/n) (∑_{t,Δ}‖A_t Δ‖²)(∑_{t,q}‖B_t q‖²)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace BDiagonalDeltaQ

open Erdos287.ReciprocalUnitaryFourier
open Erdos287.BalancedBUnitaryFourier

/-! ## §1  The residue-level `Δ × q` bound -/

/-- **`deltaQ_unitaryFourier_bound`.**  `LEAN_PROVED`.  For a unit `u` of `ZMod n` and
coefficient vectors supported on units,

`‖∑_{Δ ∈ D} ∑_{q ∈ Q} A Δ · B q · e_n(Δ u q⁻¹)‖² ≤ n (∑_Δ ‖A Δ‖²)(∑_q ‖B q‖²)`.

Reduction to the banked reciprocal unitary Fourier bound via `Δ = r⁻¹`. -/
theorem deltaQ_unitaryFourier_bound {n : ℕ} [NeZero n] {u : ZMod n} (hu : IsUnit u)
    (D Q : Finset (ZMod n)) (hD : ∀ d ∈ D, IsUnit d) (hQ : ∀ q ∈ Q, IsUnit q)
    (A B : ZMod n → ℂ) :
    ‖∑ d ∈ D, ∑ q ∈ Q, A d * B q * ZMod.stdAddChar (d * u * q⁻¹)‖ ^ 2
      ≤ (n : ℝ) * (∑ d ∈ D, ‖A d‖ ^ 2) * (∑ q ∈ Q, ‖B q‖ ^ 2) := by
  classical
  set D' : Finset (ZMod n) := D.image (fun d => d⁻¹) with hD'
  have hinj : Set.InjOn (fun d : ZMod n => d⁻¹) D := by
    intro d hd d' hd' h
    have h2 := congrArg (fun w : ZMod n => w⁻¹) h
    simpa [zmod_inv_inv_of_isUnit (hD d hd), zmod_inv_inv_of_isUnit (hD d' hd')] using h2
  have hD'unit : ∀ r ∈ D', IsUnit r := by
    intro r hr
    rw [hD', Finset.mem_image] at hr
    obtain ⟨d, hd, rfl⟩ := hr
    exact isUnit_zmod_inv (hD d hd)
  have key := reciprocalUnitaryFourier_bilinear_bound hu D' Q hD'unit hQ (fun r => A r⁻¹) B
  have hsum : ∑ r ∈ D', ∑ q ∈ Q, A r⁻¹ * B q * ZMod.stdAddChar (u * r⁻¹ * q⁻¹)
      = ∑ d ∈ D, ∑ q ∈ Q, A d * B q * ZMod.stdAddChar (d * u * q⁻¹) := by
    rw [hD', Finset.sum_image (fun d hd d' hd' h => hinj hd hd' h)]
    refine Finset.sum_congr rfl fun d hd => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [zmod_inv_inv_of_isUnit (hD d hd)]
    ring_nf
  have hA2 : ∑ r ∈ D', ‖A r⁻¹‖ ^ 2 = ∑ d ∈ D, ‖A d‖ ^ 2 := by
    rw [hD', Finset.sum_image (fun d hd d' hd' h => hinj hd hd' h)]
    exact Finset.sum_congr rfl fun d hd => by rw [zmod_inv_inv_of_isUnit (hD d hd)]
  rw [hsum, hA2] at key
  exact key

/-! ## §2  Residue aggregation for an arbitrary phase -/

/-- **`phase_fiberwise`.**  `LEAN_PROVED`.  Grouping a double sum by residue classes when
the phase depends on the summation variables only through their residues.  This
generalises the banked `reciprocalPhase_fiberwise` to an arbitrary phase function. -/
theorem phase_fiberwise (x : ℕ) [NeZero x] (sN sE : Finset ℕ) (A beta : ℕ → ℂ)
    (ph : ZMod x → ZMod x → ℂ) :
    ∑ r ∈ sN.image (fun n => ((n : ℕ) : ZMod x)), ∑ s ∈ sE.image (fun e => ((e : ℕ) : ZMod x)),
        residueAggregate x sN A r * residueAggregate x sE beta s * ph r s
      = ∑ n ∈ sN, ∑ e ∈ sE, A n * beta e * ph ((n : ℕ) : ZMod x) ((e : ℕ) : ZMod x) := by
  classical
  have hmapN : ∀ n ∈ sN, ((n : ℕ) : ZMod x) ∈ sN.image (fun n => ((n : ℕ) : ZMod x)) :=
    fun n hn => Finset.mem_image_of_mem _ hn
  have hmapE : ∀ e ∈ sE, ((e : ℕ) : ZMod x) ∈ sE.image (fun e => ((e : ℕ) : ZMod x)) :=
    fun e he => Finset.mem_image_of_mem _ he
  rw [← Finset.sum_fiberwise_of_maps_to hmapN
    (fun n => ∑ e ∈ sE, A n * beta e * ph ((n : ℕ) : ZMod x) ((e : ℕ) : ZMod x))]
  refine Finset.sum_congr rfl ?_
  intro r _
  have hinner : ∀ n ∈ sN.filter (fun n => ((n : ℕ) : ZMod x) = r),
      (∑ e ∈ sE, A n * beta e * ph ((n : ℕ) : ZMod x) ((e : ℕ) : ZMod x))
      = ∑ s ∈ sE.image (fun e => ((e : ℕ) : ZMod x)),
          ∑ e ∈ sE.filter (fun e => ((e : ℕ) : ZMod x) = s), A n * beta e * ph r s := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    rw [← Finset.sum_fiberwise_of_maps_to hmapE
      (fun e => A n * beta e * ph ((n : ℕ) : ZMod x) ((e : ℕ) : ZMod x))]
    refine Finset.sum_congr rfl ?_
    intro s _
    refine Finset.sum_congr rfl ?_
    intro e he
    simp only [Finset.mem_filter] at he
    rw [hn.2, he.2]
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro s _
  rw [residueAggregate, residueAggregate, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro n _
  rw [Finset.sum_mul]

/-! ## §3  The exact finite residue-aggregation compiler -/

/-- **`deltaQ_residueAggregation_compiler`.**  `LEAN_PROVED`.  The abstract `Δ × q_a`
kernel in exact finite residue-aggregation form.  For physical index sets `sD`, `sQ` of
naturals whose residues mod `n` are units, with residue-fibre multiplicities `MD`, `MQ` and
energies `EA`, `EB`,

`‖∑_{δ ∈ sD} ∑_{κ ∈ sQ} a δ · b κ · e_n(δ · u · κ⁻¹)‖² ≤ n · MD · MQ · EA · EB`. -/
theorem deltaQ_residueAggregation_compiler {n : ℕ} [NeZero n] {u : ZMod n} (hu : IsUnit u)
    (sD sQ : Finset ℕ) (a b : ℕ → ℂ)
    (hDunit : ∀ d ∈ sD, IsUnit ((d : ℕ) : ZMod n))
    (hQunit : ∀ q ∈ sQ, IsUnit ((q : ℕ) : ZMod n))
    (MD MQ EA EB : ℝ)
    (hMD : ∀ r : ZMod n, ((sD.filter (fun d => ((d : ℕ) : ZMod n) = r)).card : ℝ) ≤ MD)
    (hMQ : ∀ r : ZMod n, ((sQ.filter (fun q => ((q : ℕ) : ZMod n) = r)).card : ℝ) ≤ MQ)
    (hEA : ∑ d ∈ sD, ‖a d‖ ^ 2 ≤ EA) (hEB : ∑ q ∈ sQ, ‖b q‖ ^ 2 ≤ EB) :
    ‖∑ d ∈ sD, ∑ q ∈ sQ,
        a d * b q * ZMod.stdAddChar (((d : ℕ) : ZMod n) * u * (((q : ℕ) : ZMod n))⁻¹)‖ ^ 2
      ≤ (n : ℝ) * MD * MQ * EA * EB := by
  classical
  set UD : Finset (ZMod n) := sD.image (fun d => ((d : ℕ) : ZMod n)) with hUD
  set UQ : Finset (ZMod n) := sQ.image (fun q => ((q : ℕ) : ZMod n)) with hUQ
  have hUDunit : ∀ r ∈ UD, IsUnit r := by
    intro r hr
    rw [hUD, Finset.mem_image] at hr
    obtain ⟨d, hd, rfl⟩ := hr
    exact hDunit d hd
  have hUQunit : ∀ s ∈ UQ, IsUnit s := by
    intro s hs
    rw [hUQ, Finset.mem_image] at hs
    obtain ⟨q, hq, rfl⟩ := hs
    exact hQunit q hq
  have hbound := deltaQ_unitaryFourier_bound hu UD UQ hUDunit hUQunit
    (residueAggregate n sD a) (residueAggregate n sQ b)
  rw [phase_fiberwise n sD sQ a b (fun r s => ZMod.stdAddChar (r * u * s⁻¹))] at hbound
  have hMD0 : (0 : ℝ) ≤ MD := le_trans (by positivity) (hMD 0)
  have hMQ0 : (0 : ℝ) ≤ MQ := le_trans (by positivity) (hMQ 0)
  have hEA0 : (0 : ℝ) ≤ EA := le_trans (Finset.sum_nonneg fun d _ => by positivity) hEA
  have haggD : ∑ r ∈ UD, ‖residueAggregate n sD a r‖ ^ 2 ≤ MD * EA := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ UD)
      (fun r _ _ => by positivity)) ?_
    exact le_trans (residueAggregate_l2_le_maxFiber n sD a MD hMD)
      (mul_le_mul_of_nonneg_left hEA hMD0)
  have haggQ : ∑ s ∈ UQ, ‖residueAggregate n sQ b s‖ ^ 2 ≤ MQ * EB := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ UQ)
      (fun s _ _ => by positivity)) ?_
    exact le_trans (residueAggregate_l2_le_maxFiber n sQ b MQ hMQ)
      (mul_le_mul_of_nonneg_left hEB hMQ0)
  refine hbound.trans ?_
  calc (n : ℝ) * (∑ r ∈ UD, ‖residueAggregate n sD a r‖ ^ 2) *
        (∑ s ∈ UQ, ‖residueAggregate n sQ b s‖ ^ 2)
      ≤ (n : ℝ) * (MD * EA) * (∑ s ∈ UQ, ‖residueAggregate n sQ b s‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left haggD (by positivity))
          (Finset.sum_nonneg fun s _ => by positivity)
    _ ≤ (n : ℝ) * (MD * EA) * (MQ * EB) := by
        refine mul_le_mul_of_nonneg_left haggQ (by positivity)
    _ = (n : ℝ) * MD * MQ * EA * EB := by ring

/-- **Square-root form.**  `‖S‖ ≤ √n · √MD · √MQ · √EA · √EB`, i.e. the
`√n √(1 + D/n) √(1 + E/n) ‖A‖₂ ‖B‖₂` shape of the pivot. -/
theorem deltaQ_residueAggregation_sqrt {n : ℕ} [NeZero n] {u : ZMod n} (hu : IsUnit u)
    (sD sQ : Finset ℕ) (a b : ℕ → ℂ)
    (hDunit : ∀ d ∈ sD, IsUnit ((d : ℕ) : ZMod n))
    (hQunit : ∀ q ∈ sQ, IsUnit ((q : ℕ) : ZMod n))
    (MD MQ EA EB : ℝ)
    (hMD : ∀ r : ZMod n, ((sD.filter (fun d => ((d : ℕ) : ZMod n) = r)).card : ℝ) ≤ MD)
    (hMQ : ∀ r : ZMod n, ((sQ.filter (fun q => ((q : ℕ) : ZMod n) = r)).card : ℝ) ≤ MQ)
    (hEA : ∑ d ∈ sD, ‖a d‖ ^ 2 ≤ EA) (hEB : ∑ q ∈ sQ, ‖b q‖ ^ 2 ≤ EB) :
    ‖∑ d ∈ sD, ∑ q ∈ sQ,
        a d * b q * ZMod.stdAddChar (((d : ℕ) : ZMod n) * u * (((q : ℕ) : ZMod n))⁻¹)‖
      ≤ Real.sqrt n * Real.sqrt MD * Real.sqrt MQ * Real.sqrt EA * Real.sqrt EB := by
  have hMD0 : (0 : ℝ) ≤ MD := le_trans (by positivity) (hMD 0)
  have hMQ0 : (0 : ℝ) ≤ MQ := le_trans (by positivity) (hMQ 0)
  have hEA0 : (0 : ℝ) ≤ EA := le_trans (Finset.sum_nonneg fun d _ => by positivity) hEA
  have hEB0 : (0 : ℝ) ≤ EB := le_trans (Finset.sum_nonneg fun q _ => by positivity) hEB
  have hsq := deltaQ_residueAggregation_compiler hu sD sQ a b hDunit hQunit MD MQ EA EB
    hMD hMQ hEA hEB
  have hrhs : ((Real.sqrt n * Real.sqrt MD * Real.sqrt MQ * Real.sqrt EA * Real.sqrt EB) ^ 2)
      = (n : ℝ) * MD * MQ * EA * EB := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (n : ℝ)),
      Real.sq_sqrt hMD0, Real.sq_sqrt hMQ0, Real.sq_sqrt hEA0, Real.sq_sqrt hEB0]
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [hrhs]
  exact hsq

/-! ## §4  The interval instantiation: `M = length / n + 1` -/

/-- **`deltaQ_interval_compiler`.**  `LEAN_PROVED`.  Physical `Δ`- and `q`-ranges given by
integer intervals of lengths `D` and `E` supply the multiplicities `D/n + 1` and `E/n + 1`,
i.e. the `(1 + D/n)`, `(1 + E/n)` factors of the pivot. -/
theorem deltaQ_interval_compiler {n : ℕ} [NeZero n] {u : ZMod n} (hu : IsUnit u)
    (c1 D c2 E : ℕ) (a b : ℕ → ℂ)
    (hDunit : ∀ d ∈ Finset.Ico c1 (c1 + D), IsUnit ((d : ℕ) : ZMod n))
    (hQunit : ∀ q ∈ Finset.Ico c2 (c2 + E), IsUnit ((q : ℕ) : ZMod n)) :
    ‖∑ d ∈ Finset.Ico c1 (c1 + D), ∑ q ∈ Finset.Ico c2 (c2 + E),
        a d * b q * ZMod.stdAddChar (((d : ℕ) : ZMod n) * u * (((q : ℕ) : ZMod n))⁻¹)‖ ^ 2
      ≤ (n : ℝ) * ((D / n + 1 : ℕ) : ℝ) * ((E / n + 1 : ℕ) : ℝ) *
          (∑ d ∈ Finset.Ico c1 (c1 + D), ‖a d‖ ^ 2) *
          (∑ q ∈ Finset.Ico c2 (c2 + E), ‖b q‖ ^ 2) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  refine deltaQ_residueAggregation_compiler hu _ _ a b hDunit hQunit _ _ _ _ ?_ ?_ le_rfl le_rfl
  · intro r; exact_mod_cast interval_residue_fibre_card_le n hn c1 D r
  · intro r; exact_mod_cast interval_residue_fibre_card_le n hn c2 E r

/-! ## §5  The Cauchy step over `t` -/

/-- **`cauchy_over_t`.**  `LEAN_PROVED`.  If `‖S t‖² ≤ K · a t · b t` for every `t` in a
finite set, then `‖∑_t S t‖² ≤ K · (∑_t a t) · (∑_t b t)`. -/
theorem cauchy_over_t {ι : Type*} (T : Finset ι) (S : ι → ℂ) (a b : ι → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (ha : ∀ t ∈ T, 0 ≤ a t) (hb : ∀ t ∈ T, 0 ≤ b t)
    (hS : ∀ t ∈ T, ‖S t‖ ^ 2 ≤ K * a t * b t) :
    ‖∑ t ∈ T, S t‖ ^ 2 ≤ K * (∑ t ∈ T, a t) * (∑ t ∈ T, b t) := by
  have hnorm : ‖∑ t ∈ T, S t‖ ≤ Real.sqrt K * ∑ t ∈ T, Real.sqrt (a t) * Real.sqrt (b t) := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t ht => ?_)
    have h1 : ‖S t‖ ^ 2 ≤ (Real.sqrt K * (Real.sqrt (a t) * Real.sqrt (b t))) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hK, Real.sq_sqrt (ha t ht), Real.sq_sqrt (hb t ht)]
      calc ‖S t‖ ^ 2 ≤ K * a t * b t := hS t ht
        _ = K * (a t * b t) := by ring
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h1
  have hcs : (∑ t ∈ T, Real.sqrt (a t) * Real.sqrt (b t)) ^ 2
      ≤ (∑ t ∈ T, a t) * (∑ t ∈ T, b t) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq T (fun t => Real.sqrt (a t))
      (fun t => Real.sqrt (b t))
    calc (∑ t ∈ T, Real.sqrt (a t) * Real.sqrt (b t)) ^ 2
        ≤ (∑ t ∈ T, Real.sqrt (a t) ^ 2) * ∑ t ∈ T, Real.sqrt (b t) ^ 2 := h
      _ = (∑ t ∈ T, a t) * (∑ t ∈ T, b t) := by
          rw [Finset.sum_congr rfl (fun t ht => Real.sq_sqrt (ha t ht)),
            Finset.sum_congr rfl (fun t ht => Real.sq_sqrt (hb t ht))]
  calc ‖∑ t ∈ T, S t‖ ^ 2 ≤ (Real.sqrt K * ∑ t ∈ T, Real.sqrt (a t) * Real.sqrt (b t)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = K * (∑ t ∈ T, Real.sqrt (a t) * Real.sqrt (b t)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hK]
    _ ≤ K * ((∑ t ∈ T, a t) * (∑ t ∈ T, b t)) := mul_le_mul_of_nonneg_left hcs hK
    _ = K * (∑ t ∈ T, a t) * (∑ t ∈ T, b t) := by ring

/-- **`deltaQ_cauchy_over_t`.**  `LEAN_PROVED`.  The full abstract kernel theorem of the
b-diagonal pivot: with residue-level coefficient families `A t`, `B t` supported on units
and unit twists `u t`,

`‖∑_t S_t‖² ≤ n (∑_{t,Δ} ‖A t Δ‖²)(∑_{t,q} ‖B t q‖²)`,   `S_t = ∑_{Δ,q} A_t Δ · B_t q · e_n(Δ u_t q⁻¹)`. -/
theorem deltaQ_cauchy_over_t {n : ℕ} [NeZero n] {ι : Type*} (T : Finset ι)
    (u : ι → ZMod n) (hu : ∀ t ∈ T, IsUnit (u t))
    (D Q : Finset (ZMod n)) (hD : ∀ d ∈ D, IsUnit d) (hQ : ∀ q ∈ Q, IsUnit q)
    (A B : ι → ZMod n → ℂ) :
    ‖∑ t ∈ T, ∑ d ∈ D, ∑ q ∈ Q, A t d * B t q * ZMod.stdAddChar (d * u t * q⁻¹)‖ ^ 2
      ≤ (n : ℝ) * (∑ t ∈ T, ∑ d ∈ D, ‖A t d‖ ^ 2) * (∑ t ∈ T, ∑ q ∈ Q, ‖B t q‖ ^ 2) := by
  refine cauchy_over_t T
    (fun t => ∑ d ∈ D, ∑ q ∈ Q, A t d * B t q * ZMod.stdAddChar (d * u t * q⁻¹))
    (fun t => ∑ d ∈ D, ‖A t d‖ ^ 2) (fun t => ∑ q ∈ Q, ‖B t q‖ ^ 2) (n : ℝ)
    (by positivity) (fun t _ => Finset.sum_nonneg fun d _ => by positivity)
    (fun t _ => Finset.sum_nonneg fun q _ => by positivity) ?_
  intro t ht
  exact deltaQ_unitaryFourier_bound (hu t ht) D Q hD hQ (A t) (B t)

/-- **`deltaQ_cauchy_over_t_withMultiplicities`.**  `LEAN_PROVED`.  The same Cauchy step
carrying the residue-aggregation multiplicities: if every `t`-slice obeys the aggregation
bound with the *same* multiplicities `MD`, `MQ`, then

`‖∑_t S_t‖² ≤ n · MD · MQ · (∑_t E_A t)(∑_t E_B t)`,

which at interval ranges is `n (1 + D/n)(1 + E/n)` times the two total energies. -/
theorem deltaQ_cauchy_over_t_withMultiplicities {n : ℕ} [NeZero n] {ι : Type*} (T : Finset ι)
    (S : ι → ℂ) (EA EB : ι → ℝ) (MD MQ : ℝ) (hMD : 0 ≤ MD) (hMQ : 0 ≤ MQ)
    (hEA : ∀ t ∈ T, 0 ≤ EA t) (hEB : ∀ t ∈ T, 0 ≤ EB t)
    (hslice : ∀ t ∈ T, ‖S t‖ ^ 2 ≤ (n : ℝ) * MD * MQ * EA t * EB t) :
    ‖∑ t ∈ T, S t‖ ^ 2
      ≤ (n : ℝ) * MD * MQ * (∑ t ∈ T, EA t) * (∑ t ∈ T, EB t) := by
  refine cauchy_over_t T S EA EB ((n : ℝ) * MD * MQ) (by positivity) hEA hEB ?_
  intro t ht
  have := hslice t ht
  linarith [this]

/-! ## §6  Scope marker

Everything above is an abstract finite kernel theorem: the coefficient families `A`, `B`,
the twist `u` and the ranges are arbitrary.  Nothing here identifies them with the physical
b-diagonal data (Archimedean source factors, `U_e(Δ)`, the local harmonic profile, Perron
labels, `A0`/`C0` dependence, the gcd mask, the dyadic/source factors).  That identification
is the uninhabited `BDiagonalDeltaQPhysicalDictionary` interface. -/

end BDiagonalDeltaQ
end Erdos287
