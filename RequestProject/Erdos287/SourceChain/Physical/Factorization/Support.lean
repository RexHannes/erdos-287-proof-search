import RequestProject.Erdos287.SourceChain.Physical.Scalar.Bound
import RequestProject.Erdos287.SourceChain.Physical.Factorization.Modulus

/-!
# Erdős #287 — structured support of the actual scalar atoms and their Pascadi allocation

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

An *atom* of `ℓ_X` is a sector `(J, P)` with `P ∈ 𝐃_J^+` (`BoxAdm J P`), a low factor `b` with
`κ_J(b) ≠ 0` and a labelled tuple `q ∈ tuples J P` of distinct primes `q_i ∈ I_{P_i}`; its
modulus is `d = b ∏ q_i`.  We do **not** infer anything from `ellX_level : d ≤ D_tot`.

* `kappa_sector` — the low factor is in Pascadi's `𝒟⁺(D_low)` for even `J` and in `𝒟⁻(D_low)`
  for odd `J` (signed parity routing), squarefree, all primes `< u`, `b ≤ D_low`.
* `boxVec_vecHyp` — the vector of actual box **upper endpoints** `U_i = D_{P_i}^{1+τ}` lies in
  Pascadi's `𝒟⁺_J(D_int^{1+τ})` (Def. 5.1, `(5.2)`); this is derived from Lichtman's
  `𝐃_J^+` condition with the parity-dependent threshold.
* `boxVec_vecHyp_pascadi` — hence in `𝒟⁺_J(X^{3/5-50δ})` for every `δ ≤ 1/5000` (because
  `D_int^{1+τ} ≤ D_tot = X^{59/100}`).
* `atomColour` — the colouring of the `J` box positions given by Pascadi's Proposition 5.2
  (`prop52_vector`), applied with `N' = N / D_low`; it depends **only on the sector `(J,P)`**
  (allocation fixed over each box, at the box upper endpoints).
* `atom_factorization` — for every actual atom, `d = d₁ d₂ d₃` with `d₁ = b · ∏_{colour 0} q_i`,
  `d₂ = ∏_{colour 1} q_i`, `d₃ = ∏_{colour 2} q_i`, and
  `d₁ ≤ N X^{-δ}`, `N² d₂ d₃² ≤ D_low² X^{1-δ}`, `N² d₂⁵ d₃² ≤ D_low² X^{2-δ}`.
  The factor `D_low²` is the explicit price of inserting the low factor `b ≤ D_low` into `d₁`
  (the source's `x^{4β}`); `atom_factorization_clean` removes it when `D_low² ≤ X^{δ/2}`.
-/

open Finset Real

set_option autoImplicit false

namespace Erdos287.Physical.Sieve.ScalarParams

open Erdos287.Physical.Factor

variable (S : ScalarParams)

/-- The vector of box upper endpoints `U_i = D_{P_i}^{1+τ}` of a sector, padded by `1`. -/
noncomputable def boxVec (J : ℕ) (P : Fin J → Fin S.H) : ℕ → ℝ :=
  fun i => if h : i < J then S.boxTop (P ⟨i, h⟩) else 1

variable {S}

/-- **Signed parity routing of the low factor.** -/
theorem kappa_sector {J b : ℕ} (h : S.kappa J b ≠ 0) :
    Squarefree b ∧ (∀ p ∈ b.primeFactors, (p : ℝ) < S.u0) ∧
      (Even J → DplusSet S.Dlow b.primeFactors) ∧ (¬ Even J → DminusSet S.Dlow b.primeFactors) := by
  unfold kappa at h
  by_cases hJ : Even J
  · rw [if_pos hJ] at h
    unfold lamLowPlus at h
    split_ifs at h with hc
    · exact ⟨hc.1, hc.2.1, fun _ => hc.2.2, fun h' => absurd hJ h'⟩
    · exact absurd rfl h
  · rw [if_neg hJ] at h
    unfold lamLowMinus at h
    split_ifs at h with hc
    · exact ⟨hc.1, hc.2.1, fun h' => absurd h' hJ, fun _ => hc.2.2⟩
    · exact absurd rfl h

/-- Products over the positions of `Fin J` of a given colour, as products over `range J`. -/
lemma prod_fin_filter_eq (J : ℕ) (c : ℕ → Fin 3) (k : Fin 3) (f : Fin J → ℝ) :
    ∏ i ∈ univ.filter (fun i : Fin J => c i.val = k), f i =
      ∏ i ∈ (range J).filter (fun i => c i = k), (if h : i < J then f ⟨i, h⟩ else 1) := by
  rw [prod_filter, prod_filter, Finset.prod_fin_eq_prod_range]
  refine prod_congr rfl (fun i hi => ?_)
  have hi' : i < J := mem_range.1 hi
  simp [hi']

lemma prod_range_boxVec (J : ℕ) (P : Fin J → Fin S.H) (j : ℕ) (hj : j ≤ J) :
    ∏ i ∈ range j, S.boxVec J P i =
      ∏ i ∈ univ.filter (fun i : Fin J => i.val < j), S.boxTop (P i) := by
  rw [prod_filter, Finset.prod_fin_eq_prod_range, ← prod_range_mul_prod_Ico _ hj]
  have h1 : ∏ i ∈ Ico j J, (if h : i < J then (if (⟨i, h⟩ : Fin J).val < j then
      S.boxTop (P ⟨i, h⟩) else 1) else 1) = 1 :=
    prod_eq_one (fun i hi => by simp at hi; simp [show ¬ i < j by omega])
  rw [h1, mul_one]
  refine prod_congr rfl (fun i hi => ?_)
  have hi' : i < j := mem_range.1 hi
  simp [boxVec, show i < J by omega, hi']

/-- **Structured support of the box vector**: Lichtman's `𝐃_J^+` condition (with its
parity-dependent threshold) at the box *lower* endpoints implies Pascadi's `𝒟⁺_J(D_int^{1+τ})`
at the box *upper* endpoints `U_i = D_{P_i}^{1+τ}`. -/
theorem boxVec_vecHyp (hS : S.Good) {J : ℕ} {P : Fin J → Fin S.H} (hP : S.BoxAdm J P) :
    VecHyp (S.Dint ^ (1 + S.tau)) (S.boxVec J P) J := by
  have hτ := tau_pos hS
  refine ⟨fun i hi => ?_, fun i j hij hj => ?_, fun j hj hje => ?_⟩
  · simp only [boxVec, dif_pos hi]
    rw [boxTop_eq hS]; exact (boxEnd_gt_one hS _).le
  · simp only [boxVec, dif_pos hj, dif_pos (lt_of_le_of_lt hij hj)]
    rw [boxTop_eq hS, boxTop_eq hS, boxEnd_le_iff hS]
    have : P ⟨j, hj⟩ ≤ P ⟨i, by omega⟩ := hP.1 (show (⟨i, _⟩ : Fin J) ≤ ⟨j, hj⟩ from hij)
    have : (P ⟨j, hj⟩ : ℕ) ≤ P ⟨i, by omega⟩ := this
    omega
  · have hadm := hP.2 ⟨j, hj⟩ hje
    rw [prod_range_boxVec J P j hj.le]
    simp only [boxVec, dif_pos hj]
    have hfilt : univ.filter (fun i : Fin J => i.val < j) = univ.filter (· < (⟨j, hj⟩ : Fin J)) := by
      ext i; simp [Fin.lt_def]
    rw [hfilt]
    have hpos : ∀ i, 0 ≤ S.boxEnd i := fun i => (boxEnd_pos hS i).le
    unfold boxTop
    rw [Real.finset_prod_rpow _ _ (fun i _ => hpos _),
      ← Real.rpow_natCast (S.boxEnd ↑(P ⟨j, hj⟩) ^ (1 + S.tau)) 3,
      ← Real.rpow_mul (hpos _), mul_comm ((1 : ℝ) + S.tau), Real.rpow_mul (hpos _),
      Real.rpow_natCast, ← Real.mul_rpow (prod_nonneg (fun i _ => hpos _)) (pow_nonneg (hpos _) 3)]
    refine le_trans (Real.rpow_le_rpow (mul_nonneg (prod_nonneg (fun i _ => hpos _))
      (pow_nonneg (hpos _) 3)) hadm.le (by linarith)) (threshold_rpow_le hS J)

theorem Dint_rpow_le_Dtot (hS : S.Good) : S.Dint ^ (1 + S.tau) ≤ S.Dtot := by
  rw [← Dlow_mul hS]
  have := Dlow_ge_one hS
  have : 0 ≤ S.Dint ^ (1 + S.tau) := Real.rpow_nonneg (Dint_pos hS).le _
  nlinarith

/-- The box vector lies in Pascadi's `𝒟⁺_J(X^{3/5-50δ})` for every `0 ≤ δ ≤ 1/5000`. -/
theorem boxVec_vecHyp_pascadi (hS : S.Good) {δ : ℝ} (hδ : δ ≤ 1 / 5000) {J : ℕ}
    {P : Fin J → Fin S.H} (hP : S.BoxAdm J P) :
    VecHyp (S.X ^ (3 / 5 - 50 * δ)) (S.boxVec J P) J := by
  have h := boxVec_vecHyp hS hP
  have hle : S.Dint ^ (1 + S.tau) ≤ S.X ^ (3 / 5 - 50 * δ) := by
    refine (Dint_rpow_le_Dtot hS).trans ?_
    unfold Dtot
    exact Real.rpow_le_rpow_of_exponent_le hS.X_gt.le (by linarith)
  exact ⟨h.one_le, h.anti, fun j hj he => (h.plus j hj he).trans hle⟩

/-- **The Pascadi colouring of a sector** (finite choice; it depends only on `(J, P)`, i.e. the
allocation is fixed over each box).  Proposition 5.2 is applied to the box upper endpoints with
`N' = N / D_low`. -/
noncomputable def atomColour (δ N : ℝ) (J : ℕ) (P : Fin J → Fin S.H) : ℕ → Fin 3 :=
  Classical.epsilon (fun c : ℕ → Fin 3 => Sys53 S.X δ (N / S.Dlow)
    (cprod (S.boxVec J P) c 0 J) (cprod (S.boxVec J P) c 1 J) (cprod (S.boxVec J P) c 2 J))

/-- The parameter hypotheses for applying Proposition 5.2 to the scalar atoms. -/
structure AtomParams (S : ScalarParams) (δ N : ℝ) : Prop where
  good : S.Good
  δ_pos : 0 < δ
  δ_small : δ < 1 / 100000
  N_lo : S.X ^ (2 * δ) ≤ N / S.Dlow
  N_hi : N ≤ S.X ^ (1 / 3 + δ)

theorem atomColour_spec {δ N : ℝ} (hA : AtomParams S δ N) {J : ℕ} {P : Fin J → Fin S.H}
    (hP : S.BoxAdm J P) :
    Sys53 S.X δ (N / S.Dlow) (cprod (S.boxVec J P) (S.atomColour δ N J P) 0 J)
      (cprod (S.boxVec J P) (S.atomColour δ N J P) 1 J)
      (cprod (S.boxVec J P) (S.atomColour δ N J P) 2 J) := by
  have hS := hA.good
  have hDl := Dlow_ge_one hS
  apply Classical.epsilon_spec (p := fun c : ℕ → Fin 3 => Sys53 S.X δ (N / S.Dlow)
    (cprod (S.boxVec J P) c 0 J) (cprod (S.boxVec J P) c 1 J) (cprod (S.boxVec J P) c 2 J))
  refine prop52_vector hS.X_gt hA.δ_pos hA.δ_small hA.N_lo ?_
    (boxVec_vecHyp_pascadi hS (by linarith [hA.δ_small]) hP)
  refine le_trans ?_ hA.N_hi
  have hN0 : 0 ≤ N := by
    have := hA.N_lo
    have h0 : 0 < S.X ^ (2 * δ) := Real.rpow_pos_of_pos (by linarith [hS.X_gt]) _
    have : 0 < N / S.Dlow := lt_of_lt_of_le h0 this
    exact (div_pos_iff_of_pos_right (by linarith)).1 this |>.le
  exact div_le_self hN0 hDl

/-- The colour-`k` part of a labelled tuple. -/
def tupleFactor {J : ℕ} (c : ℕ → Fin 3) (k : Fin 3) (q : Fin J → ℕ) : ℕ :=
  ∏ i ∈ univ.filter (fun i : Fin J => c i.val = k), q i

lemma tupleFactor_mul {J : ℕ} (c : ℕ → Fin 3) (q : Fin J → ℕ) :
    tupleFactor c 0 q * tupleFactor c 1 q * tupleFactor c 2 q = ∏ i, q i := by
  unfold tupleFactor
  have := Finset.prod_fiberwise (univ : Finset (Fin J)) (fun i => c i.val) q
  rw [Fin.prod_univ_three] at this
  exact this

lemma tupleFactor_le {J : ℕ} {P : Fin J → Fin S.H} {q : Fin J → ℕ} (hq : q ∈ S.tuples J P)
    (c : ℕ → Fin 3) (k : Fin 3) :
    (tupleFactor c k q : ℝ) ≤ cprod (S.boxVec J P) c k J := by
  unfold tupleFactor cprod
  push_cast
  have e := prod_fin_filter_eq J c k (fun i => S.boxTop (P i))
  have e' : ∀ i ∈ (range J).filter (fun i => c i = k),
      (if h : i < J then S.boxTop (P ⟨i, h⟩) else 1) = S.boxVec J P i := fun i _ => rfl
  rw [prod_congr rfl e'] at e
  rw [← e]
  refine prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => ?_)
  exact ((mem_tuples hq).2 i).2.2

/-- **Pascadi factorization of every actual scalar atom.** -/
theorem atom_factorization {δ N : ℝ} (hA : AtomParams S δ N) {J : ℕ} {P : Fin J → Fin S.H}
    (hP : S.BoxAdm J P) {b : ℕ} (hb : S.kappa J b ≠ 0) {q : Fin J → ℕ}
    (hq : q ∈ S.tuples J P) :
    let c := S.atomColour δ N J P
    let d₁ := b * tupleFactor c 0 q
    let d₂ := tupleFactor c 1 q
    let d₃ := tupleFactor c 2 q
    b * ∏ i, q i = d₁ * d₂ * d₃ ∧
      (d₁ : ℝ) ≤ N * S.X ^ (-δ) ∧
      N ^ 2 * (d₂ : ℝ) * (d₃ : ℝ) ^ 2 ≤ S.Dlow ^ 2 * S.X ^ (1 - δ) ∧
      N ^ 2 * (d₂ : ℝ) ^ 5 * (d₃ : ℝ) ^ 2 ≤ S.Dlow ^ 2 * S.X ^ (2 - δ) := by
  intro c d₁ d₂ d₃
  have hS := hA.good
  have hDl := Dlow_ge_one hS
  obtain ⟨s1, s2, s3⟩ := atomColour_spec hA hP
  have hb' : (b : ℝ) ≤ S.Dlow := kappa_level hS hb
  have e0 := tupleFactor_le hq c 0
  have e1 := tupleFactor_le hq c 1
  have e2 := tupleFactor_le hq c 2
  set E0 := cprod (S.boxVec J P) c 0 J
  set E1 := cprod (S.boxVec J P) c 1 J
  set E2 := cprod (S.boxVec J P) c 2 J
  have n0 : (0 : ℝ) ≤ tupleFactor c 0 q := Nat.cast_nonneg _
  have n1 : (0 : ℝ) ≤ d₂ := Nat.cast_nonneg _
  have n2 : (0 : ℝ) ≤ d₃ := Nat.cast_nonneg _
  have hNdl : N / S.Dlow * S.Dlow = N := div_mul_cancel₀ N (by linarith)
  have m1 : 0 ≤ E1 := n1.trans e1
  have m2 : 0 ≤ E2 := n2.trans e2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [d₁, d₂, d₃, mul_assoc]; rw [← tupleFactor_mul c q]; ring
  · simp only [d₁]; push_cast
    have hX : 0 ≤ S.X ^ (-δ) := Real.rpow_nonneg (by linarith [hS.X_gt]) _
    calc (b : ℝ) * tupleFactor c 0 q ≤ S.Dlow * E0 :=
          mul_le_mul hb' e0 n0 (by linarith)
      _ ≤ S.Dlow * (N / S.Dlow * S.X ^ (-δ)) := mul_le_mul_of_nonneg_left s1 (by linarith)
      _ = N * S.X ^ (-δ) := by field_simp
  · calc N ^ 2 * (d₂ : ℝ) * (d₃ : ℝ) ^ 2 ≤ N ^ 2 * E1 * E2 ^ 2 := by gcongr
      _ = S.Dlow ^ 2 * ((N / S.Dlow) ^ 2 * E1 * E2 ^ 2) := by
          field_simp
      _ ≤ S.Dlow ^ 2 * S.X ^ (1 - δ) := by gcongr
  · calc N ^ 2 * (d₂ : ℝ) ^ 5 * (d₃ : ℝ) ^ 2 ≤ N ^ 2 * E1 ^ 5 * E2 ^ 2 := by gcongr
      _ = S.Dlow ^ 2 * ((N / S.Dlow) ^ 2 * E1 ^ 5 * E2 ^ 2) := by
          field_simp
      _ ≤ S.Dlow ^ 2 * S.X ^ (2 - δ) := by gcongr

/-- If the low level is negligible, `D_low² ≤ X^{δ/2}`, every actual atom satisfies Pascadi's
system (5.3) exactly with `δ/2`. -/
theorem atom_factorization_clean {δ N : ℝ} (hA : AtomParams S δ N)
    (hlow : S.Dlow ^ 2 ≤ S.X ^ (δ / 2)) {J : ℕ} {P : Fin J → Fin S.H}
    (hP : S.BoxAdm J P) {b : ℕ} (hb : S.kappa J b ≠ 0) {q : Fin J → ℕ}
    (hq : q ∈ S.tuples J P) :
    let c := S.atomColour δ N J P
    b * ∏ i, q i = (b * tupleFactor c 0 q) * tupleFactor c 1 q * tupleFactor c 2 q ∧
      Sys53 S.X (δ / 2) N (b * tupleFactor c 0 q : ℕ) (tupleFactor c 1 q) (tupleFactor c 2 q) := by
  intro c
  obtain ⟨h0, h1, h2, h3⟩ := atom_factorization hA hP hb hq
  have hS := hA.good
  have hX0 : 0 < S.X := by linarith [hS.X_gt]
  have hδ := hA.δ_pos
  refine ⟨h0, ?_, ?_, ?_⟩
  · refine h1.trans ?_
    have hN : 0 ≤ N := by
      have := (Real.rpow_pos_of_pos hX0 (2 * δ)).trans_le hA.N_lo
      exact ((div_pos_iff_of_pos_right (by linarith [Dlow_ge_one hS])).1 this).le
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hS.X_gt.le (by linarith)) hN
  · refine h2.trans ?_
    calc S.Dlow ^ 2 * S.X ^ (1 - δ) ≤ S.X ^ (δ / 2) * S.X ^ (1 - δ) :=
          mul_le_mul_of_nonneg_right hlow (Real.rpow_nonneg hX0.le _)
      _ = S.X ^ (1 - δ / 2) := by rw [← Real.rpow_add hX0]; ring_nf
  · refine h3.trans ?_
    calc S.Dlow ^ 2 * S.X ^ (2 - δ) ≤ S.X ^ (δ / 2) * S.X ^ (2 - δ) :=
          mul_le_mul_of_nonneg_right hlow (Real.rpow_nonneg hX0.le _)
      _ = S.X ^ (2 - δ / 2) := by rw [← Real.rpow_add hX0]; ring_nf

end Erdos287.Physical.Sieve.ScalarParams
