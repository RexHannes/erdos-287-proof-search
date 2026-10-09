import RequestProject.Erdos287.QSigma.Certificate
import RequestProject.Erdos287.QSigma.Audit

/-!
# Erdős #287 — post-`Q_Σ` bank, §4: the strengthened (V53) summed-depth certificate

**Status: BANK (proved in Lean).**

The existing `Erdos287.ExactSource.QSigma` is *already* the summed-depth certificate
`∏_p p^(∑_d κ_{p,d})` (see `Erdos287.ExactSource.Gamma`).  This file therefore does **not**
re-implement it; it exposes the V53 names as transparent aliases and adds the comparison with
the older maximal-depth certificate

  `Q_old = ∏_p p^(max_d κ_{p,d})`,

proving `Q_old ∣ QSigmaStrong` (exponentwise `max_d κ_{p,d} ≤ ∑_d κ_{p,d}`).

It also contains the strict synthetic fixture `V = {2,…,7}`, `W = 420`, `T = 235`
(**DIAGNOSTIC ONLY — not a #287 counterexample**), stated through an abstract version of the
same `κ` (`absKappa`), which is *definitionally* the concrete `kappa` on physical sources
(`kappa_eq_absKappa`).
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

open Erdos287.ExactSource

variable {a M : ℕ} {R : Finset ℕ}

/-! ## V53 names (aliases of the existing bank) -/

/-- `GammaSum_p = ∑_{d=1}^{e} κ_{p,d}` (alias of the banked `Gamma`). -/
noncomputable abbrev GammaSum (a M : ℕ) (R : Finset ℕ) (p : ℕ) : ℕ := Gamma a M R p

/-- `QSigmaStrong = ∏_p p^(∑_d κ_{p,d})` (alias of the banked `QSigma`). -/
noncomputable abbrev QSigmaStrong (a M : ℕ) (R : Finset ℕ) : ℕ := QSigma a M R

/-- **Exact valuation bound**: `GammaSum_p ≤ v_p(∏_{n∈E} n)` for every exact solution `E`. -/
theorem GammaSum_le_factorization (ha : 0 < a) {E : Finset ℕ} (h : SourceSol a M R E)
    {p : ℕ} (hp : p.Prime) : GammaSum a M R p ≤ (∏ n ∈ E, n).factorization p :=
  Gamma_le_factorization_prod ha h hp

/-- **`QSigmaStrong ∣ ∏_{n∈E} n`** for every exact solution `E`. -/
theorem QSigmaStrong_dvd_prod (ha : 0 < a) {E : Finset ℕ} (h : SourceSol a M R E) :
    QSigmaStrong a M R ∣ ∏ n ∈ E, n :=
  QSigma_dvd_prod ha h

/-- **Strengthened exclusion**: `QSigmaStrong > P_max(V, R_T)` ⇒ no exact solution. -/
theorem no_solution_of_QSigmaStrong_gt_Pmax (ha : 0 < a)
    (hQ : Pmax a M R (RT a M R) < QSigmaStrong a M R) (E : Finset ℕ) :
    ¬ SourceSol a M R E :=
  no_solution_of_QSigma_gt_Pmax ha hQ E

/-! ## The older maximal-depth certificate -/

/-- `max_{1 ≤ d ≤ e} κ_{p,d}`. -/
noncomputable def kappaMax (a M : ℕ) (R : Finset ℕ) (p : ℕ) : ℕ :=
  (Finset.Icc 1 (eW a M R p)).sup (fun d => kappa a M R p d)

/-- The older maximal-depth certificate `Q_old = ∏_p p^(max_d κ_{p,d})`. -/
noncomputable def Qold (a M : ℕ) (R : Finset ℕ) : ℕ :=
  ∏ p ∈ (W a M R).primeFactors, p ^ kappaMax a M R p

/-- Exponentwise comparison: `max_d κ_{p,d} ≤ ∑_d κ_{p,d}`. -/
theorem kappaMax_le_GammaSum (p : ℕ) : kappaMax a M R p ≤ GammaSum a M R p := by
  unfold kappaMax GammaSum Gamma
  refine Finset.sup_le (fun d hd => ?_)
  exact Finset.single_le_sum (f := fun d => kappa a M R p d) (fun _ _ => Nat.zero_le _) hd

/-- **`Q_old ∣ QSigmaStrong`.** -/
theorem Qold_dvd_QSigmaStrong : Qold a M R ∣ QSigmaStrong a M R := by
  unfold Qold QSigmaStrong QSigma
  refine Finset.prod_dvd_prod_of_dvd _ _ (fun p _ => ?_)
  exact pow_dvd_pow p (kappaMax_le_GammaSum p)

/-- The old certificate is never stronger: `Q_old > P_max` ⇒ `QSigmaStrong > P_max`. -/
theorem QSigmaStrong_gt_of_Qold_gt {k : ℕ} (h : k < Qold a M R) :
    k < QSigmaStrong a M R :=
  lt_of_lt_of_le h (Nat.le_of_dvd (Nat.pos_of_ne_zero (QSigma_ne_zero (a := a) (M := M)
    (R := R))) Qold_dvd_QSigmaStrong)

/-! ## Abstract `κ` (same definition, arbitrary `V`, `W`, `T`) -/

/-- Abstract depth set `S_{p,d}(V, W)`. -/
def absS (V : Finset ℕ) (W p d : ℕ) : Finset ℕ :=
  V.filter (fun n => p ^ (W.factorization p - d + 1) ∣ n)

/-- Abstract repair sizes. -/
def absRepairSizes (V : Finset ℕ) (W : ℕ) (T : ℤ) (p d : ℕ) : Set ℕ :=
  {k | ∃ F ⊆ absS V W p d, F.card = k ∧
    (∑ n ∈ F, ((W / n : ℕ) : ℤ)) ≡ T [ZMOD (p : ℤ) ^ d]}

/-- Abstract `κ_{p,d}`. -/
noncomputable def absKappa (V : Finset ℕ) (W : ℕ) (T : ℤ) (p d : ℕ) : ℕ :=
  sInf (absRepairSizes V W T p d)

/-- The physical `κ` is literally the abstract `κ` of `(V, W, T)`. -/
theorem kappa_eq_absKappa (p d : ℕ) :
    kappa a M R p d = absKappa (V a M R) (W a M R) (T a M R) p d := rfl

/-- Abstract summed-depth certificate. -/
noncomputable def absQSigma (V : Finset ℕ) (W : ℕ) (T : ℤ) : ℕ :=
  ∏ p ∈ W.primeFactors, p ^ ∑ d ∈ Finset.Icc 1 (W.factorization p), absKappa V W T p d

/-- Abstract maximal-depth certificate. -/
noncomputable def absQold (V : Finset ℕ) (W : ℕ) (T : ℤ) : ℕ :=
  ∏ p ∈ W.primeFactors, p ^ (Finset.Icc 1 (W.factorization p)).sup (absKappa V W T p)

theorem QSigma_eq_absQSigma : QSigma a M R = absQSigma (V a M R) (W a M R) (T a M R) := rfl

theorem Qold_eq_absQold : Qold a M R = absQold (V a M R) (W a M R) (T a M R) := rfl

open Classical in
/-- Abstract `P_max(V, k)`. -/
noncomputable def absPmax (V : Finset ℕ) (k : ℕ) : ℕ :=
  ((V.powerset).filter (fun F => Indep F ∧ F.card ≤ k)).sup (fun F => ∏ n ∈ F, n)

theorem Pmax_eq_absPmax (k : ℕ) : Pmax a M R k = absPmax (V a M R) k := rfl

/-! ## The strict synthetic fixture (DIAGNOSTIC ONLY) -/

namespace Fixture

/-- `V = {2,3,4,5,6,7}`. -/
def fV : Finset ℕ := {2, 3, 4, 5, 6, 7}

lemma sInf_eq_of {s : Set ℕ} {k : ℕ} (hk : k ∈ s) (hmin : ∀ j < k, j ∉ s) : sInf s = k := by
  apply le_antisymm (Nat.sInf_le hk)
  by_contra hc
  push_neg at hc
  exact hmin _ hc (Nat.sInf_mem ⟨k, hk⟩)

private lemma fac_of (p k m : ℕ) (hp : p.Prime) (hm : ¬ p ∣ m) :
    (p ^ k * m).factorization p = k := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0]
  simp [hp.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hm]

lemma f2 : (420 : ℕ).factorization 2 = 2 := fac_of 2 2 105 Nat.prime_two (by norm_num)
lemma f3 : (420 : ℕ).factorization 3 = 1 := fac_of 3 1 140 Nat.prime_three (by norm_num)
lemma f5 : (420 : ℕ).factorization 5 = 1 := fac_of 5 1 84 (by norm_num) (by norm_num)
lemma f7 : (420 : ℕ).factorization 7 = 1 := fac_of 7 1 60 (by norm_num) (by norm_num)

lemma pf : Nat.primeFactors 420 = {2, 3, 5, 7} := by
  rw [show (420 : ℕ) = 2 ^ 2 * (3 * (5 * 7)) by norm_num,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  decide

/-- Decidable form of abstract repair-size membership. -/
lemma mem_absRepairSizes_iff (V : Finset ℕ) (W : ℕ) (T : ℤ) (p d k : ℕ) :
    k ∈ absRepairSizes V W T p d ↔ ∃ F ∈ (absS V W p d).powerset, F.card = k ∧
      (∑ n ∈ F, ((W / n : ℕ) : ℤ)) % ((p : ℤ) ^ d) = T % ((p : ℤ) ^ d) := by
  simp [absRepairSizes, Int.ModEq]

lemma k21 : absKappa fV 420 235 2 1 = 1 := by
  apply sInf_eq_of
  · rw [mem_absRepairSizes_iff, absS, f2]; decide
  · intro j hj; rw [mem_absRepairSizes_iff, absS, f2]; interval_cases j; decide

lemma k22 : absKappa fV 420 235 2 2 = 2 := by
  apply sInf_eq_of
  · rw [mem_absRepairSizes_iff, absS, f2]; decide
  · intro j hj; rw [mem_absRepairSizes_iff, absS, f2]; interval_cases j <;> decide

lemma k31 : absKappa fV 420 235 3 1 = 1 := by
  apply sInf_eq_of
  · rw [mem_absRepairSizes_iff, absS, f3]; decide
  · intro j hj; rw [mem_absRepairSizes_iff, absS, f3]; interval_cases j; decide

lemma k51 : absKappa fV 420 235 5 1 = 0 := by
  apply sInf_eq_of
  · rw [mem_absRepairSizes_iff, absS, f5]; decide
  · intro j hj; omega

lemma k71 : absKappa fV 420 235 7 1 = 1 := by
  apply sInf_eq_of
  · rw [mem_absRepairSizes_iff, absS, f7]; decide
  · intro j hj; rw [mem_absRepairSizes_iff, absS, f7]; interval_cases j; decide

/-- Fixture: `Q_old = 84`. -/
theorem fixture_Qold : absQold fV 420 235 = 84 := by
  rw [absQold, pf]
  simp only [Finset.prod_insert (by decide : (2 : ℕ) ∉ ({3, 5, 7} : Finset ℕ)),
    Finset.prod_insert (by decide : (3 : ℕ) ∉ ({5, 7} : Finset ℕ)),
    Finset.prod_insert (by decide : (5 : ℕ) ∉ ({7} : Finset ℕ)), Finset.prod_singleton]
  rw [f2, f3, f5, f7]
  rw [show Finset.Icc 1 2 = {1, 2} by decide, show Finset.Icc 1 1 = {1} by decide]
  simp [k21, k22, k31, k51, k71]

/-- Fixture: `QSigmaStrong = 168`. -/
theorem fixture_QSigmaStrong : absQSigma fV 420 235 = 168 := by
  rw [absQSigma, pf]
  simp only [Finset.prod_insert (by decide : (2 : ℕ) ∉ ({3, 5, 7} : Finset ℕ)),
    Finset.prod_insert (by decide : (3 : ℕ) ∉ ({5, 7} : Finset ℕ)),
    Finset.prod_insert (by decide : (5 : ℕ) ∉ ({7} : Finset ℕ)), Finset.prod_singleton]
  rw [f2, f3, f5, f7]
  rw [show Finset.Icc 1 2 = {1, 2} by decide, show Finset.Icc 1 1 = {1} by decide]
  simp [k21, k22, k31, k51, k71]

/-- `R_T = ⌊7 · 235 / 420⌋ = 3`. -/
theorem fixture_RT : (7 * 235) / 420 = 3 := by norm_num

/-- Fixture: `P_max(V, 3) = 105` (attained by `{3,5,7}`). -/
theorem fixture_Pmax : absPmax fV 3 = 105 := by
  have : absPmax fV 3 = (fV.powerset.filter (fun F : Finset ℕ => (∀ x ∈ F, x + 1 ∉ F) ∧
      F.card ≤ 3)).sup (fun F => ∏ n ∈ F, n) := by
    unfold absPmax Indep; congr
  rw [this]; unfold fV; decide

/-- The new certificate excludes (`168 > 105`), the old one does not (`84 ≤ 105`). -/
theorem fixture_strict_improvement :
    absPmax fV 3 < absQSigma fV 420 235 ∧ absQold fV 420 235 ≤ absPmax fV 3 := by
  rw [fixture_Pmax, fixture_QSigmaStrong, fixture_Qold]; norm_num

/-- Direct check (independent of the certificate): the fixture has no exact solution. -/
theorem fixture_no_solution :
    ∀ E ∈ fV.powerset, Indep E → (∑ n ∈ E, ((420 / n : ℕ) : ℤ)) ≠ 235 := by
  unfold Indep fV
  decide

end Fixture

end Erdos287.PostQSigma
