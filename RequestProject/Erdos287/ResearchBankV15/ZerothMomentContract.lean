import Mathlib.Tactic
import RequestProject.Erdos287.ResearchBankV15.Normalization
import RequestProject.Erdos287.ResearchBankV15.CompleteLCMModulus
import RequestProject.Erdos287.ResearchBankV15.DivisorMultiplicity

/-!
# Erdős #287 — Research Bank V15 §B10(a): the zeroth-moment contract

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Exact finite algebra (proved):

* `Hit d e t` — `t ≡ b0 (mod W0)` and `d_i ∣ L_i(t)`, `e_i ∣ L_i(t)` for every labelled `i`;
* `weight_expand` / `weighted_expansion` — **square expansion** of the physical weight:
  `∑_t w(M,t) f(t) = ∑_{d,e ∈ D(M)} λ_d λ_e ∑_{t ∈ window, Hit d e t} f(t)` (any `f`);
* `S0_expansion` — `S0 = ∑_{d,e} λ_d λ_e · count(d,e)`;
* `hit_periodic` — `Hit d e` is periodic with the **complete** period `W0 · q`,
  `q = lcm(d_1,…,d_K,e_1,…,e_K)`;
* `periodic_count_abs` — for any `Q`-periodic predicate, the count on an interval of length `n`
  is `ρ n / Q` up to an error at most `ρ = #{r < Q}` hits;
* `S0_error_bound` — `|S0 − mainS0| ≤ errorMajorant = ∑_{d,e} |λ_d λ_e| ρ(d,e)`.

Analytic inputs (explicit providers, never constructed):

* `S0MainTermProvider` — the Mellin/Euler evaluation of `mainS0` (with the exact collision
  singular factors `(1 − ν_p/p)/(1 − 1/p)^K`, not merely the origin value): `mainS0/N_X → 1`;
* `DivisorMomentProvider` — the divisor-moment/Cauchy estimate `errorMajorant/N_X → 0`.

`s0_contract` — from the two providers, the V14 `S0Contract` holds for the actual `S0` and the
actual normalization `N_X = C_X S_W0(a) I`.
-/

namespace Erdos287
namespace ResearchBankV15
namespace ZerothMomentContract

open Finset
open ResearchBankV14 ResearchBankV14.BalancedKernelParameters
open ResearchBankV14.ConditionalAsymptoticImplication ResearchBankV14.ContactAnnulus
open FixedAffineSource MobiusCoefficients CompleteLCMModulus Normalization

/-! ## Periodic counting (generic) -/

theorem card_blocks (p : ℕ → Prop) [DecidablePred p] {Q : ℕ} (hp : Function.Periodic p Q)
    (a k : ℕ) : ((Ico a (a + Q * k)).filter p).card = k * Nat.count p Q := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : Ico a (a + Q * (k + 1)) =
        Ico a (a + Q * k) ∪ Ico (a + Q * k) (a + Q * k + Q) := by
      rw [Ico_union_Ico_eq_Ico (by omega) (by omega)]; congr 1; ring
    rw [hsplit, filter_union, card_union_of_disjoint
      (disjoint_filter_filter (Ico_disjoint_Ico_consecutive _ _ _)), ih,
      Nat.filter_Ico_card_eq_of_periodic _ _ p hp]
    ring

theorem periodic_count_bounds (p : ℕ → Prop) [DecidablePred p] {Q : ℕ} (hQ : 0 < Q)
    (hp : Function.Periodic p Q) (a n : ℕ) :
    (n / Q) * Nat.count p Q ≤ ((Ico a (a + n)).filter p).card ∧
      ((Ico a (a + n)).filter p).card ≤ (n / Q) * Nat.count p Q + Nat.count p Q := by
  have hn : n = Q * (n / Q) + n % Q := (Nat.div_add_mod n Q).symm
  have hsub : Ico a (a + n) = Ico a (a + Q * (n / Q)) ∪ Ico (a + Q * (n / Q)) (a + n) :=
    (Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
  rw [hsub, filter_union, card_union_of_disjoint
    (disjoint_filter_filter (Ico_disjoint_Ico_consecutive _ _ _)), card_blocks p hp]
  refine ⟨Nat.le_add_right _ _, Nat.add_le_add_left ?_ _⟩
  calc ((Ico (a + Q * (n / Q)) (a + n)).filter p).card
        ≤ ((Ico (a + Q * (n / Q)) (a + Q * (n / Q) + Q)).filter p).card := by
          apply card_le_card; apply filter_subset_filter; apply Ico_subset_Ico_right
          have := Nat.mod_lt n hQ; omega
      _ = Nat.count p Q := Nat.filter_Ico_card_eq_of_periodic _ _ p hp

/-- **Periodic counting**: `|#{t ∈ [a, a+n) : p t} − ρ n / Q| ≤ ρ`, `ρ = #{r < Q : p r}`. -/
theorem periodic_count_abs (p : ℕ → Prop) [DecidablePred p] {Q : ℕ} (hQ : 0 < Q)
    (hp : Function.Periodic p Q) (a n : ℕ) :
    |(((Ico a (a + n)).filter p).card : ℝ) - (Nat.count p Q : ℝ) * n / Q| ≤ Nat.count p Q := by
  obtain ⟨h1, h2⟩ := periodic_count_bounds p hQ hp a n
  have h1' : ((n / Q : ℕ) : ℝ) * (Nat.count p Q : ℝ) ≤ (((Ico a (a + n)).filter p).card : ℝ) := by
    exact_mod_cast h1
  have h2' : (((Ico a (a + n)).filter p).card : ℝ) ≤
      ((n / Q : ℕ) : ℝ) * (Nat.count p Q : ℝ) + (Nat.count p Q : ℝ) := by exact_mod_cast h2
  have hn : (n : ℝ) = Q * (n / Q : ℕ) + (n % Q : ℕ) := by
    exact_mod_cast (Nat.div_add_mod n Q).symm
  have hr : ((n % Q : ℕ) : ℝ) < Q := by exact_mod_cast Nat.mod_lt n hQ
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  set c := (((Ico a (a + n)).filter p).card : ℝ)
  set ρ := (Nat.count p Q : ℝ)
  set k := ((n / Q : ℕ) : ℝ)
  set r := ((n % Q : ℕ) : ℝ)
  have hρ : 0 ≤ ρ := by positivity
  have hr0 : 0 ≤ r := by positivity
  have he : ρ * n / Q = k * ρ + ρ * r / Q := by rw [hn]; field_simp
  have hq1 : ρ * r / Q ≤ ρ := by rw [div_le_iff₀ hQ']; nlinarith
  have hq0 : 0 ≤ ρ * r / Q := by positivity
  rw [he, abs_le]; constructor <;> linarith

/-! ## The square expansion of the physical weight -/

variable (src : SourceData)

/-- Joint divisibility / residue condition for the labelled pair `(d, e)`. -/
def Hit (d e : Fin K → ℕ) (t : ℕ) : Prop :=
  t % src.W0 = src.b0 ∧ ∀ i, d i ∣ L i t ∧ e i ∣ L i t

/-- Abbreviation for the actual coefficient at scale `M`. -/
noncomputable abbrev lamM (M : ℕ) (d : Fin K → ℕ) : ℝ := lam src.G (src.Xs M) src.W0 d

open Classical in
/-- Pointwise square expansion of the physical weight. -/
theorem weight_expand (M t : ℕ) :
    weight src M t =
      ∑ d ∈ src.D M, ∑ e ∈ src.D M, if Hit src d e t then lamM src M d * lamM src M e else 0 := by
  unfold weight sieveSum
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h0 : t % src.W0 = src.b0 <;> by_cases hd : ∀ i, d i ∣ L i t <;>
    by_cases he : ∀ i, e i ∣ L i t <;> simp [Hit, h0, hd, he, forall_and]

open Classical in
/-- **Square expansion** of any weighted window sum. -/
theorem weighted_expansion (M : ℕ) (f : ℕ → ℝ) :
    ∑ t ∈ window tuple M, weight src M t * f t =
      ∑ d ∈ src.D M, ∑ e ∈ src.D M,
        lamM src M d * lamM src M e * ∑ t ∈ (window tuple M).filter (Hit src d e), f t := by
  simp_rw [weight_expand, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

open Classical in
/-- The joint count `#{t ∈ window : Hit d e t}`. -/
noncomputable def count (M : ℕ) (d e : Fin K → ℕ) : ℕ :=
  ((window tuple M).filter (Hit src d e)).card

/-- **`S0` square expansion.** -/
theorem S0_expansion (M : ℕ) :
    S0 tuple (weightSystem src) M =
      ∑ d ∈ src.D M, ∑ e ∈ src.D M, lamM src M d * lamM src M e * (count src M d e : ℝ) := by
  classical
  have h := weighted_expansion src M (fun _ => 1)
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h
  unfold S0 count
  convert h using 1

/-! ## Complete period and the main term -/

/-- `Hit d e` is periodic with the complete period `W0 · q`. -/
theorem hit_periodic (d e : Fin K → ℕ) :
    Function.Periodic (Hit src d e) (src.W0 * completeModulus d e) := by
  intro t
  have hq := (dvd_completeModulus_iff d e (completeModulus d e)).1 dvd_rfl
  have hL : ∀ i, L i (t + src.W0 * completeModulus d e) =
      L i t + fixedSlopes i * src.W0 * completeModulus d e := fun i => by unfold L; ring
  have key : ∀ (m : ℕ) (i : Fin K), m ∣ completeModulus d e →
      (m ∣ L i (t + src.W0 * completeModulus d e) ↔ m ∣ L i t) := fun m i hm => by
    rw [hL]; exact Nat.dvd_add_left (Dvd.dvd.mul_left hm _)
  unfold Hit
  apply propext
  rw [Nat.add_mul_mod_self_left]
  simp only [key _ _ (hq.1 _), key _ _ (hq.2 _)]

open Classical in
/-- `ρ(d, e)`: the number of hitting residues modulo the complete period `W0 · q`. -/
noncomputable def residueCount (d e : Fin K → ℕ) : ℕ :=
  Nat.count (Hit src d e) (src.W0 * completeModulus d e)

/-- The window length. -/
noncomputable def wlen (M : ℕ) : ℕ :=
  ⌊((rho : ℚ) : ℝ) * X tuple M⌋₊ + 1 - ⌈X tuple M⌉₊

theorem window_eq_Ico (M : ℕ) :
    window tuple M = Ico ⌈X tuple M⌉₊ (⌈X tuple M⌉₊ + wlen M) := by
  ext t; simp only [window, wlen, mem_Icc, mem_Ico]; omega

/-- The main term of `S0`. -/
noncomputable def mainS0 (M : ℕ) : ℝ :=
  ∑ d ∈ src.D M, ∑ e ∈ src.D M, lamM src M d * lamM src M e *
    ((residueCount src d e : ℝ) * wlen M / (src.W0 * completeModulus d e : ℕ))

/-- The error majorant `∑_{d,e} |λ_d λ_e| ρ(d, e)`. -/
noncomputable def errorMajorant (M : ℕ) : ℝ :=
  ∑ d ∈ src.D M, ∑ e ∈ src.D M, |lamM src M d * lamM src M e| * (residueCount src d e : ℝ)

theorem lam_eq_zero_of_zero {M : ℕ} {d : Fin K → ℕ} {i : Fin K} (h : d i = 0) :
    lamM src M d = 0 :=
  lam_eq_zero_of_not_squarefree _ _ _ (i := i) (by rw [h]; exact not_squarefree_zero)

theorem completeModulus_pos {d e : Fin K → ℕ} (hd : ∀ i, d i ≠ 0) (he : ∀ i, e i ≠ 0) :
    0 < completeModulus d e := by
  unfold completeModulus
  apply Nat.lcm_pos <;> apply Nat.pos_of_ne_zero <;> rw [Ne, Finset.lcm_eq_zero_iff] <;>
    simp [hd, he]

/-- **Per-pair count error**: `|count − ρ n / (W0 q)| ≤ ρ` (all coordinates nonzero). -/
theorem count_error (M : ℕ) {d e : Fin K → ℕ} (hd : ∀ i, d i ≠ 0) (he : ∀ i, e i ≠ 0) :
    |(count src M d e : ℝ) -
        (residueCount src d e : ℝ) * wlen M / (src.W0 * completeModulus d e : ℕ)| ≤
      residueCount src d e := by
  classical
  unfold count residueCount
  rw [window_eq_Ico]
  convert periodic_count_abs (Hit src d e)
    (Nat.mul_pos src.W0_pos (completeModulus_pos hd he)) (hit_periodic src d e) _ _

/-- **`|S0 − mainS0| ≤ errorMajorant`** (exact finite algebra). -/
theorem S0_error_bound (M : ℕ) :
    |S0 tuple (weightSystem src) M - mainS0 src M| ≤ errorMajorant src M := by
  rw [S0_expansion]
  unfold mainS0 errorMajorant
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
  rw [← mul_sub, abs_mul]
  by_cases hd : ∀ i, d i ≠ 0
  · by_cases he : ∀ i, e i ≠ 0
    · exact mul_le_mul_of_nonneg_left (count_error src M hd he) (abs_nonneg _)
    · push_neg at he
      obtain ⟨i, hi⟩ := he
      simp [lam_eq_zero_of_zero src hi]
  · push_neg at hd
    obtain ⟨i, hi⟩ := hd
    simp [lam_eq_zero_of_zero src hi]

/-! ## Analytic providers and the contract -/

/-- **Main-term provider for `S0`** (explicit; never constructed): the Mellin / Euler-product
evaluation of the exact main term, keeping the collision singular factors, gives eventually
`N_X > 0` and `|mainS0 / N_X − 1| ≤ η`. -/
structure S0MainTermProvider : Prop where
  eventual : ∀ η > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, 0 < NX src M ∧ |mainS0 src M / NX src M - 1| ≤ η

/-- **Divisor-moment provider** (explicit; never constructed): eventually
`errorMajorant / N_X ≤ η`. -/
structure DivisorMomentProvider : Prop where
  eventual : ∀ η > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, errorMajorant src M / NX src M ≤ η

/-- **The zeroth-moment contract** for the actual source, conditional on the two providers. -/
theorem s0_contract (hm : S0MainTermProvider src) (hd : DivisorMomentProvider src) :
    S0Contract (S0 tuple (weightSystem src)) (NX src) := by
  intro η hη
  obtain ⟨M1, h1⟩ := hm.eventual (η / 2) (by positivity)
  obtain ⟨M2, h2⟩ := hd.eventual (η / 2) (by positivity)
  refine ⟨max M1 M2, fun M hM => ?_⟩
  obtain ⟨hN, hmain⟩ := h1 M (le_trans (le_max_left _ _) hM)
  have herr := h2 M (le_trans (le_max_right _ _) hM)
  refine ⟨hN, ?_⟩
  have hb := S0_error_bound src M
  have hdiv : |S0 tuple (weightSystem src) M / NX src M - mainS0 src M / NX src M| ≤
      errorMajorant src M / NX src M := by
    rw [← sub_div, abs_div, abs_of_pos hN]
    exact div_le_div_of_nonneg_right hb hN.le
  calc |S0 tuple (weightSystem src) M / NX src M - 1|
      ≤ |S0 tuple (weightSystem src) M / NX src M - mainS0 src M / NX src M| +
          |mainS0 src M / NX src M - 1| := abs_sub_le _ _ _
    _ ≤ η / 2 + η / 2 := add_le_add (hdiv.trans herr) hmain
    _ = η := by ring

end ZerothMomentContract
end ResearchBankV15
end Erdos287
