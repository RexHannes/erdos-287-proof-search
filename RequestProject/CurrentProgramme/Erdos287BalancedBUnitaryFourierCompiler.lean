import Mathlib
import RequestProject.CurrentProgramme.Erdos287ReciprocalUnitaryFourier

/-!
# Balanced-`b` unitary Fourier compiler — Erdős #287 (append-only)

This module is **append-only** and sits strictly after
`Erdos287ReciprocalUnitaryFourier`, whose finite theorems it reuses (no second proof).

Contents.

* §1  residue aggregation of an interval-supported coefficient sequence, and the finite
  combinatorial `ℓ²` inequality `∑_r |agg r|² ≤ M ∑_n |A n|²`, where `M` is any uniform bound
  on the number of support points in one residue class;
* §2  the interval instantiation: an integer interval of length `N` meets each residue class
  modulo `x` in at most `N / x + 1` points (safe integer ceiling form, `ℕ`-division);
* §3  the balanced finite compiler: for coefficients supported on residues that are **units**,
  `‖∑_{n,e} A n β e e_x(C n⁻¹ e⁻¹)‖² ≤ x · M_N · M_E · E_A · E_B`;
* §4  the exact four-term contraction identity in the positive-real model;
* §5  the non-unit firewall: coprimality of each factor of a product coprime to `x`;
* §6  the product-convolution energy **hypothesis** (explicit theorem hypothesis, never an
  axiom, never assumed), and the three-carrier conditional compiler built from it.

Conservatism.

* The modulus is the exact finite modulus `x`; no analytic parameter `X` is substituted for it.
* No `φ(x)/x` density factor and no pointwise divisor bound occurs in any `ℓ²` statement.
* The product-convolution energy is *not* proved here; it appears only as a named hypothesis
  of §6, and a witness theorem shows it is not automatic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace BalancedBUnitaryFourier

open Finset
open Erdos287.ReciprocalUnitaryFourier

/-! ## §1  Residue aggregation -/

/-- **`norm_sum_sq_le_card`.**  `LEAN_PROVED`.  `‖∑_{i∈s} f i‖² ≤ #s · ∑_{i∈s} ‖f i‖²`. -/
theorem norm_sum_sq_le_card {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  simpa using norm_sum_mul_sq_le s (fun _ => (1 : ℂ)) f

/-- Aggregation of a finitely supported coefficient sequence over one residue class mod `x`. -/
noncomputable def residueAggregate (x : ℕ) (s : Finset ℕ) (A : ℕ → ℂ) (r : ZMod x) : ℂ :=
  ∑ n ∈ s.filter (fun n => ((n : ℕ) : ZMod x) = r), A n

/-- **`residueAggregate_l2_le_maxFiber`.**  `LEAN_PROVED`.  If every residue class mod `x`
contains at most `M` support points, then
`∑_r ‖residueAggregate x s A r‖² ≤ M · ∑_{n ∈ s} ‖A n‖²`. -/
theorem residueAggregate_l2_le_maxFiber (x : ℕ) [NeZero x] (s : Finset ℕ) (A : ℕ → ℂ) (M : ℝ)
    (hM : ∀ r : ZMod x, ((s.filter (fun n => ((n : ℕ) : ZMod x) = r)).card : ℝ) ≤ M) :
    ∑ r : ZMod x, ‖residueAggregate x s A r‖ ^ 2 ≤ M * ∑ n ∈ s, ‖A n‖ ^ 2 := by
  classical
  have step : ∀ r : ZMod x, ‖residueAggregate x s A r‖ ^ 2
      ≤ M * ∑ n ∈ s.filter (fun n => ((n : ℕ) : ZMod x) = r), ‖A n‖ ^ 2 := by
    intro r
    refine (norm_sum_sq_le_card _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hM r) (Finset.sum_nonneg fun n _ => by positivity)
  calc ∑ r : ZMod x, ‖residueAggregate x s A r‖ ^ 2
      ≤ ∑ r : ZMod x, M * ∑ n ∈ s.filter (fun n => ((n : ℕ) : ZMod x) = r), ‖A n‖ ^ 2 :=
        Finset.sum_le_sum fun r _ => step r
    _ = M * ∑ n ∈ s, ‖A n‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_fiberwise s (fun n => ((n : ℕ) : ZMod x))]

/-! ## §2  Interval fibres -/

/-- **`interval_residue_fibre_card_le`.**  `LEAN_PROVED`.  An integer interval of length `N`
meets each residue class modulo `x > 0` in at most `N / x + 1` points (`ℕ`-division: this is the
safe integer ceiling form). -/
theorem interval_residue_fibre_card_le (x : ℕ) (hx : 0 < x) (a N : ℕ) (r : ZMod x) :
    ((Finset.Ico a (a + N)).filter (fun n => ((n : ℕ) : ZMod x) = r)).card ≤ N / x + 1 := by
  classical
  have hcard : ((Finset.Ico a (a + N)).filter (fun n => ((n : ℕ) : ZMod x) = r)).card
      ≤ (Finset.range (N / x + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun n => (n - a) / x) ?_ ?_
    · intro n hn
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico, Finset.coe_range,
        Set.mem_Iio] at hn ⊢
      have h1 : n - a ≤ N := by omega
      have h2 := Nat.div_le_div_right (c := x) h1
      omega
    · intro n hn n' hn' h
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico] at hn hn'
      have hmod : n % x = n' % x := by
        have h0 : ((n : ℕ) : ZMod x) = ((n' : ℕ) : ZMod x) := hn.2.trans hn'.2.symm
        exact (ZMod.natCast_eq_natCast_iff' n n' x).mp h0
      simp only at h
      rcases le_total n n' with hle | hle
      · by_contra hne
        have hdvd : x ∣ n' - n := (Nat.modEq_iff_dvd' hle).mp hmod
        have hpos : 0 < n' - n := by omega
        have hxle : x ≤ n' - n := Nat.le_of_dvd hpos hdvd
        have hkey : (n - a) / x + 1 ≤ (n' - a) / x := by
          have h2 : (n - a) + x ≤ n' - a := by omega
          have h3 := Nat.div_le_div_right (c := x) h2
          rwa [Nat.add_div_right _ hx] at h3
        omega
      · by_contra hne
        have hdvd : x ∣ n - n' := (Nat.modEq_iff_dvd' hle).mp hmod.symm
        have hpos : 0 < n - n' := by omega
        have hxle : x ≤ n - n' := Nat.le_of_dvd hpos hdvd
        have hkey : (n' - a) / x + 1 ≤ (n - a) / x := by
          have h2 : (n' - a) + x ≤ n - a := by omega
          have h3 := Nat.div_le_div_right (c := x) h2
          rwa [Nat.add_div_right _ hx] at h3
        omega
  simpa using hcard

/-- **`intervalResidueAggregate_l2_bound`.**  `LEAN_PROVED`.  Interval corollary of
`residueAggregate_l2_le_maxFiber`: for coefficients supported on `[a, a+N)`,
`∑_r ‖agg r‖² ≤ (N / x + 1) ∑_n ‖A n‖²`. -/
theorem intervalResidueAggregate_l2_bound (x : ℕ) [NeZero x] (a N : ℕ) (A : ℕ → ℂ) :
    ∑ r : ZMod x, ‖residueAggregate x (Finset.Ico a (a + N)) A r‖ ^ 2
      ≤ ((N / x + 1 : ℕ) : ℝ) * ∑ n ∈ Finset.Ico a (a + N), ‖A n‖ ^ 2 := by
  have hx : 0 < x := Nat.pos_of_ne_zero (NeZero.ne x)
  refine residueAggregate_l2_le_maxFiber x _ A _ ?_
  intro r
  exact_mod_cast interval_residue_fibre_card_le x hx a N r

/-! ## §3  The balanced finite compiler -/

/-- **`reciprocalPhase_fiberwise`.**  `LEAN_PROVED`.  Grouping a reciprocal-phase double sum by
residue classes: the phase depends on `n` and `e` only through their residues, so the double sum
collapses to a double sum of residue aggregates. -/
theorem reciprocalPhase_fiberwise (x : ℕ) [NeZero x] (C : ZMod x) (sN sE : Finset ℕ)
    (A beta : ℕ → ℂ) :
    ∑ r ∈ sN.image (fun n => ((n : ℕ) : ZMod x)), ∑ s ∈ sE.image (fun e => ((e : ℕ) : ZMod x)),
        residueAggregate x sN A r * residueAggregate x sE beta s *
          ZMod.stdAddChar (C * r⁻¹ * s⁻¹)
      = ∑ n ∈ sN, ∑ e ∈ sE,
          A n * beta e *
            ZMod.stdAddChar (C * (((n : ℕ) : ZMod x))⁻¹ * (((e : ℕ) : ZMod x))⁻¹) := by
  classical
  have hmapN : ∀ n ∈ sN, ((n : ℕ) : ZMod x) ∈ sN.image (fun n => ((n : ℕ) : ZMod x)) :=
    fun n hn => Finset.mem_image_of_mem _ hn
  have hmapE : ∀ e ∈ sE, ((e : ℕ) : ZMod x) ∈ sE.image (fun e => ((e : ℕ) : ZMod x)) :=
    fun e he => Finset.mem_image_of_mem _ he
  rw [← Finset.sum_fiberwise_of_maps_to hmapN
    (fun n => ∑ e ∈ sE, A n * beta e *
      ZMod.stdAddChar (C * (((n : ℕ) : ZMod x))⁻¹ * (((e : ℕ) : ZMod x))⁻¹))]
  refine Finset.sum_congr rfl ?_
  intro r _
  have hinner : ∀ n ∈ sN.filter (fun n => ((n : ℕ) : ZMod x) = r),
      (∑ e ∈ sE, A n * beta e *
        ZMod.stdAddChar (C * (((n : ℕ) : ZMod x))⁻¹ * (((e : ℕ) : ZMod x))⁻¹))
      = ∑ s ∈ sE.image (fun e => ((e : ℕ) : ZMod x)),
          ∑ e ∈ sE.filter (fun e => ((e : ℕ) : ZMod x) = s),
            A n * beta e * ZMod.stdAddChar (C * r⁻¹ * s⁻¹) := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    rw [← Finset.sum_fiberwise_of_maps_to hmapE
      (fun e => A n * beta e *
        ZMod.stdAddChar (C * (((n : ℕ) : ZMod x))⁻¹ * (((e : ℕ) : ZMod x))⁻¹))]
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

/-- **`balancedReciprocalFourier_compiler`.**  `LEAN_PROVED`.  The clean finite compiler.

For coefficient sequences `A` on `sN` and `β` on `sE` whose support residues are **units** of
`ZMod x`, with residue-fibre bounds `M_N, M_E` and energy bounds `E_A, E_B`,

`‖∑_{n,e} A n β e e_x(C n⁻¹ e⁻¹)‖² ≤ x · M_N · M_E · E_A · E_B`.

`C` is an arbitrary unit; nothing about the pointwise shape of `A` or `β` is used. -/
theorem balancedReciprocalFourier_compiler {x : ℕ} [NeZero x] {C : ZMod x} (hC : IsUnit C)
    (sN sE : Finset ℕ) (A beta : ℕ → ℂ)
    (hNunit : ∀ n ∈ sN, IsUnit ((n : ℕ) : ZMod x))
    (hEunit : ∀ e ∈ sE, IsUnit ((e : ℕ) : ZMod x))
    (MN ME EA EB : ℝ)
    (hMN : ∀ r : ZMod x, ((sN.filter (fun n => ((n : ℕ) : ZMod x) = r)).card : ℝ) ≤ MN)
    (hME : ∀ r : ZMod x, ((sE.filter (fun e => ((e : ℕ) : ZMod x) = r)).card : ℝ) ≤ ME)
    (hEA : ∑ n ∈ sN, ‖A n‖ ^ 2 ≤ EA) (hEB : ∑ e ∈ sE, ‖beta e‖ ^ 2 ≤ EB) :
    ‖∑ n ∈ sN, ∑ e ∈ sE,
        A n * beta e *
          ZMod.stdAddChar (C * (((n : ℕ) : ZMod x))⁻¹ * (((e : ℕ) : ZMod x))⁻¹)‖ ^ 2
      ≤ (x : ℝ) * MN * ME * EA * EB := by
  classical
  set UN : Finset (ZMod x) := sN.image (fun n => ((n : ℕ) : ZMod x)) with hUN
  set UE : Finset (ZMod x) := sE.image (fun e => ((e : ℕ) : ZMod x)) with hUE
  have hUNunit : ∀ r ∈ UN, IsUnit r := by
    intro r hr
    rw [hUN, Finset.mem_image] at hr
    obtain ⟨n, hn, rfl⟩ := hr
    exact hNunit n hn
  have hUEunit : ∀ s ∈ UE, IsUnit s := by
    intro s hs
    rw [hUE, Finset.mem_image] at hs
    obtain ⟨e, he, rfl⟩ := hs
    exact hEunit e he
  have hbound := reciprocalUnitaryFourier_bilinear_bound hC UN UE hUNunit hUEunit
    (residueAggregate x sN A) (residueAggregate x sE beta)
  rw [reciprocalPhase_fiberwise x C sN sE A beta] at hbound
  -- the two aggregate energies
  have hMN0 : (0 : ℝ) ≤ MN := le_trans (by positivity) (hMN 0)
  have hME0 : (0 : ℝ) ≤ ME := le_trans (by positivity) (hME 0)
  have hEA0 : (0 : ℝ) ≤ EA := le_trans (Finset.sum_nonneg fun n _ => by positivity) hEA
  have haggN : ∑ r ∈ UN, ‖residueAggregate x sN A r‖ ^ 2 ≤ MN * EA := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ UN)
      (fun r _ _ => by positivity)) ?_
    exact le_trans (residueAggregate_l2_le_maxFiber x sN A MN hMN)
      (mul_le_mul_of_nonneg_left hEA hMN0)
  have haggE : ∑ s ∈ UE, ‖residueAggregate x sE beta s‖ ^ 2 ≤ ME * EB := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ UE)
      (fun s _ _ => by positivity)) ?_
    exact le_trans (residueAggregate_l2_le_maxFiber x sE beta ME hME)
      (mul_le_mul_of_nonneg_left hEB hME0)
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have haggN0 : (0 : ℝ) ≤ ∑ r ∈ UN, ‖residueAggregate x sN A r‖ ^ 2 :=
    Finset.sum_nonneg fun r _ => by positivity
  refine hbound.trans ?_
  calc (x : ℝ) * (∑ r ∈ UN, ‖residueAggregate x sN A r‖ ^ 2) *
        (∑ s ∈ UE, ‖residueAggregate x sE beta s‖ ^ 2)
      ≤ (x : ℝ) * (MN * EA) * (∑ s ∈ UE, ‖residueAggregate x sE beta s‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haggN hx0)
          (Finset.sum_nonneg fun s _ => by positivity)
    _ ≤ (x : ℝ) * (MN * EA) * (ME * EB) := by
        refine mul_le_mul_of_nonneg_left haggE (by positivity)
    _ = (x : ℝ) * MN * ME * EA * EB := by ring

/-! ## §4  The exact four-term contraction identity -/

/-- **`balancedFourier_contraction_identity`.**  `LEAN_PROVED`.  The exact field identity

`x (1 + N/x)(1 + E/x) / B = x/B + 1/E + 1/N + 1/x`,  when  `B = N · E`,

in the positive-real model.  Recorded so that later transcriptions cannot drift. -/
theorem balancedFourier_contraction_identity (x N E B : ℝ)
    (hx : 0 < x) (hN : 0 < N) (hE : 0 < E) (hB : B = N * E) :
    x * (1 + N / x) * (1 + E / x) / B = x / B + 1 / E + 1 / N + 1 / x := by
  subst hB
  field_simp
  ring

/-! ## §5  Non-unit firewall: coprimality of each factor -/

/-- **`coprime_product_left`.**  `LEAN_PROVED`.  If `ℓ · d · e` is coprime to `x`, so is `ℓ`. -/
theorem coprime_product_left {ell d e x : ℕ} (h : Nat.Coprime (ell * d * e) x) :
    Nat.Coprime ell x :=
  Nat.Coprime.coprime_dvd_left ⟨d * e, by ring⟩ h

/-- **`coprime_product_middle`.**  `LEAN_PROVED`.  If `ℓ · d · e` is coprime to `x`, so is `d`. -/
theorem coprime_product_middle {ell d e x : ℕ} (h : Nat.Coprime (ell * d * e) x) :
    Nat.Coprime d x := by
  refine Nat.Coprime.coprime_dvd_left ?_ h
  exact ⟨ell * e, by ring⟩

/-- **`coprime_product_right`.**  `LEAN_PROVED`.  If `ℓ · d · e` is coprime to `x`, so is `e`. -/
theorem coprime_product_right {ell d e x : ℕ} (h : Nat.Coprime (ell * d * e) x) :
    Nat.Coprime e x :=
  Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ rfl) h

/-- **`coprime_product_all`.**  `LEAN_PROVED`.  Packaged form: `b = ℓ · d · e` coprime to `x`
gives coprimality of all three factors.  This is the *minimum* formal arithmetic of the
non-unit firewall; it does **not** by itself establish that the conditioned coefficient
`C_Π = a_ρ b_ρ⁻¹ u_ρ` is a unit — that remains a source-level condition. -/
theorem coprime_product_all {b ell d e x : ℕ} (hb : b = ell * d * e) (h : Nat.Coprime b x) :
    Nat.Coprime ell x ∧ Nat.Coprime d x ∧ Nat.Coprime e x := by
  subst hb
  exact ⟨coprime_product_left h, coprime_product_middle h, coprime_product_right h⟩

/-! ## §6  Product-convolution energy: explicit hypothesis only -/

/-- **Interface, not proved here.**  The fixed-depth Dirichlet-convolution `ℓ²` bound for
`A n = ∑_{ℓ d = n} a_ℓ α_d`, written as a named proposition:

`∑_{n ∈ sN} ‖A n‖² ≤ Cconv · (∑_ℓ ‖a ℓ‖²)(∑_d ‖α d‖²)`.

It is **never** assumed: it occurs only as an explicit hypothesis of
`threeCarrierReciprocalFourier_of_productEnergy`.  No pointwise divisor maximum
(`sup τ(n) ≤ log^C`) is used or asserted anywhere. -/
def ProductConvolutionEnergyHypothesis (sN sa salpha : Finset ℕ) (A a alpha : ℕ → ℂ)
    (Cconv : ℝ) : Prop :=
  ∑ n ∈ sN, ‖A n‖ ^ 2 ≤ Cconv * (∑ l ∈ sa, ‖a l‖ ^ 2) * (∑ d ∈ salpha, ‖alpha d‖ ^ 2)

/-- **`productConvolutionEnergy_not_automatic`.**  `LEAN_PROVED`.  The convolution-energy
interface is a genuine hypothesis: there are data for which it fails.  Hence no theorem that
carries it is vacuous, and it cannot be discharged by pure logic. -/
theorem productConvolutionEnergy_not_automatic :
    ∃ (sN sa salpha : Finset ℕ) (A a alpha : ℕ → ℂ) (Cconv : ℝ),
      ¬ ProductConvolutionEnergyHypothesis sN sa salpha A a alpha Cconv := by
  refine ⟨{0}, ∅, ∅, fun _ => 1, fun _ => 0, fun _ => 0, 1, ?_⟩
  intro h
  simp only [ProductConvolutionEnergyHypothesis] at h
  norm_num at h

/-- **`threeCarrierReciprocalFourier_of_productEnergy`.**  `LEAN_PROVED (CONDITIONAL)`.

Three-factor grouping `n = S₁ S₂`: *if* a fixed-depth convolution-energy bound is supplied for
the `n`-coefficient, the reciprocal unitary Fourier compiler applies between the `n`-carrier and
the second carrier, with the convolution energy substituted for `E_A`.

The convolution-energy input is an explicit hypothesis.  Nothing here claims that the physical
transverse source actually has such a factorisation. -/
theorem threeCarrierReciprocalFourier_of_productEnergy {x : ℕ} [NeZero x] {C : ZMod x}
    (hC : IsUnit C) (sN sE sa salpha : Finset ℕ) (A beta a alpha : ℕ → ℂ)
    (hNunit : ∀ n ∈ sN, IsUnit ((n : ℕ) : ZMod x))
    (hEunit : ∀ e ∈ sE, IsUnit ((e : ℕ) : ZMod x))
    (MN ME EB Cconv : ℝ)
    (hMN : ∀ r : ZMod x, ((sN.filter (fun n => ((n : ℕ) : ZMod x) = r)).card : ℝ) ≤ MN)
    (hME : ∀ r : ZMod x, ((sE.filter (fun e => ((e : ℕ) : ZMod x) = r)).card : ℝ) ≤ ME)
    (hConv : ProductConvolutionEnergyHypothesis sN sa salpha A a alpha Cconv)
    (hEB : ∑ e ∈ sE, ‖beta e‖ ^ 2 ≤ EB) :
    ‖∑ n ∈ sN, ∑ e ∈ sE,
        A n * beta e *
          ZMod.stdAddChar (C * (((n : ℕ) : ZMod x))⁻¹ * (((e : ℕ) : ZMod x))⁻¹)‖ ^ 2
      ≤ (x : ℝ) * MN * ME *
          (Cconv * (∑ l ∈ sa, ‖a l‖ ^ 2) * (∑ d ∈ salpha, ‖alpha d‖ ^ 2)) * EB :=
  balancedReciprocalFourier_compiler hC sN sE A beta hNunit hEunit MN ME _ EB hMN hME hConv hEB

end BalancedBUnitaryFourier
end Erdos287
