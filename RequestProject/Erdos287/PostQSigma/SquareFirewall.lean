import Mathlib

/-!
# Erdős #287 — post-`Q_Σ` bank, §24: the square-certificate firewall

**Status: BANK (proved in Lean).**  The route "exists some polynomial certificate" without
degree/height control is **RETIRED** as a reduction.

* `square_certificate_excludes` — the sound direction: a weight `U` on defect signatures with
  `U(0) = 1` and `∑_E U(sig E)² < 1` excludes every all-zero-defect configuration;
* `interpolation_firewall` — for any finite signature set `S ⊆ K^r` with `0 ∉ S` there is a
  polynomial `P` with `P(0) = 1` and `P|_S = 0`; so the bare existence of a polynomial
  certificate carries **no** information (it holds whenever the target is absent);
* `punctured_cube_degree` — a polynomial on `{0,1}^r` that is nonzero at the origin and vanishes
  at every other cube point has total degree `≥ r` (the delta-at-origin needs degree `r`).
  This retires matching-only constant-degree certificates.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

open MvPolynomial

/-- **Sound direction of square certificates.** -/
theorem square_certificate_excludes {α σ : Type*} [Zero σ] (Ω : Finset α) (sig : α → σ)
    (U : σ → ℚ) (hU0 : U 0 = 1) (hlt : ∑ E ∈ Ω, (U (sig E)) ^ 2 < 1) :
    ∀ E ∈ Ω, sig E ≠ 0 := by
  intro E hE h0
  have : (U (sig E)) ^ 2 ≤ ∑ E ∈ Ω, (U (sig E)) ^ 2 :=
    Finset.single_le_sum (f := fun E => (U (sig E)) ^ 2) (fun _ _ => sq_nonneg _) hE
  rw [h0, hU0] at this
  linarith

/-- **Interpolation firewall**: every finite signature set avoiding the origin is cut out by
some polynomial with value `1` at the origin. -/
theorem interpolation_firewall {K : Type*} [Field K] {r : ℕ} (S : Finset (Fin r → K))
    (h0 : (0 : Fin r → K) ∉ S) :
    ∃ P : MvPolynomial (Fin r) K, eval 0 P = 1 ∧ ∀ s ∈ S, eval s P = 0 := by
  classical
  have hex : ∀ s ∈ S, ∃ i, s i ≠ 0 := by
    intro s hs
    by_contra h; push_neg at h
    exact h0 (by convert hs; funext i; exact (h i).symm)
  let i : S → Fin r := fun s => (hex s.1 s.2).choose
  have hi : ∀ s : S, s.1 (i s) ≠ 0 := fun s => (hex s.1 s.2).choose_spec
  refine ⟨∏ s ∈ S.attach, (1 - C ((s.1 (i s))⁻¹) * X (i s)), ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_eq_one (fun s _ => by simp)
  · intro t ht
    rw [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_attach S ⟨t, ht⟩)
    simp only [map_sub, map_one, map_mul, eval_C, eval_X]
    rw [inv_mul_cancel₀ (hi ⟨t, ht⟩), sub_self]

/-- The cube point with support `T`. -/
def cubePt {r : ℕ} (T : Finset (Fin r)) : Fin r → ℚ := fun i => if i ∈ T then 1 else 0

lemma cubePt_empty {r : ℕ} : cubePt (∅ : Finset (Fin r)) = 0 := by
  funext i; simp [cubePt]

/-- Monomial evaluation at a cube point. -/
lemma prod_cubePt_pow {r : ℕ} (T : Finset (Fin r)) (d : Fin r →₀ ℕ) :
    ∏ i, (cubePt T i) ^ d i = if d.support ⊆ T then 1 else 0 := by
  classical
  split_ifs with h
  · apply Finset.prod_eq_one
    intro i _
    by_cases hi : d i = 0
    · simp [hi]
    · have : i ∈ T := h (Finsupp.mem_support_iff.2 hi)
      simp [cubePt, this]
  · rw [Finset.not_subset] at h
    obtain ⟨i, hi, hiT⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have : d i ≠ 0 := Finsupp.mem_support_iff.1 hi
    simp [cubePt, hiT, this]

/-- Alternating sum of a monomial over the cube vanishes unless its support is everything. -/
lemma alt_sum_monomial {r : ℕ} (d : Fin r →₀ ℕ) (hd : d.support ≠ Finset.univ) :
    ∑ T ∈ (Finset.univ : Finset (Fin r)).powerset,
      (-1 : ℚ) ^ T.card * (if d.support ⊆ T then 1 else 0) = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, i ∉ d.support := by
    by_contra h; push_neg at h
    exact hd (Finset.eq_univ_of_forall h)
  let g : Finset (Fin r) → Finset (Fin r) := fun T => if i ∈ T then T.erase i else insert i T
  have hsub : ∀ T : Finset (Fin r), d.support ⊆ g T ↔ d.support ⊆ T := by
    intro T
    simp only [g]
    split_ifs with hT
    · constructor
      · intro h; exact h.trans (Finset.erase_subset _ _)
      · intro h x hx
        exact Finset.mem_erase.2 ⟨fun e => hi (e ▸ hx), h hx⟩
    · constructor
      · intro h x hx
        have := h hx
        rcases Finset.mem_insert.1 this with e | e
        · exact absurd (e ▸ hx) hi
        · exact e
      · intro h; exact h.trans (Finset.subset_insert _ _)
  refine Finset.sum_involution (fun T _ => g T) ?_ ?_ ?_ ?_
  · intro T _
    beta_reduce
    rw [if_congr (hsub T) rfl rfl]
    by_cases hc : d.support ⊆ T
    · simp only [hc, if_true, mul_one]
      by_cases hT : i ∈ T
      · simp only [g, hT, if_true]
        rw [Finset.card_erase_of_mem hT]
        have h1 : 1 ≤ T.card := Finset.card_pos.2 ⟨i, hT⟩
        obtain ⟨k, hk⟩ : ∃ k, T.card = k + 1 := ⟨T.card - 1, by omega⟩
        rw [hk, Nat.add_sub_cancel, pow_succ]; ring
      · simp only [g, hT, if_false]
        rw [Finset.card_insert_of_notMem hT, pow_succ]; ring
    · simp [hc]
  · intro T _ _
    simp only [g]
    split_ifs with hT
    · intro h; have := congrArg (i ∈ ·) h; simp [hT] at this
    · intro h; have := congrArg (i ∈ ·) h; simp [hT] at this
  · intro T _; simp
  · intro T _
    simp only [g]
    split_ifs with h1 h2 h2
    · simp at h2
    · exact Finset.insert_erase h1
    · exact Finset.erase_insert h1
    · simp at h2

/-- **Punctured Boolean cube degree bound**: if `P(0) ≠ 0` and `P` vanishes on every nonzero
point of `{0,1}^r`, then `deg P ≥ r`. -/
theorem punctured_cube_degree {r : ℕ} (P : MvPolynomial (Fin r) ℚ) (h0 : eval 0 P ≠ 0)
    (h1 : ∀ T : Finset (Fin r), T.Nonempty → eval (cubePt T) P = 0) : r ≤ P.totalDegree := by
  classical
  by_contra hlt
  push_neg at hlt
  -- the alternating sum of `P` over the cube
  have hA : ∑ T ∈ (Finset.univ : Finset (Fin r)).powerset,
      (-1 : ℚ) ^ T.card * eval (cubePt T) P = eval 0 P := by
    rw [Finset.sum_eq_single ∅]
    · simp [cubePt_empty]
    · intro T _ hT
      rw [h1 T (Finset.nonempty_iff_ne_empty.2 hT), mul_zero]
    · intro h; exact absurd (Finset.empty_mem_powerset _) h
  have hB : ∑ T ∈ (Finset.univ : Finset (Fin r)).powerset,
      (-1 : ℚ) ^ T.card * eval (cubePt T) P = 0 := by
    simp_rw [eval_eq', Finset.mul_sum, prod_cubePt_pow]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro d hd
    have hdeg : (d.sum fun _ e => e) ≤ P.totalDegree := le_totalDegree hd
    have hsupp : d.support ≠ Finset.univ := by
      intro h
      have hcard : d.support.card ≤ d.sum fun _ e => e := by
        rw [Finsupp.sum]
        calc d.support.card = ∑ _x ∈ d.support, 1 := by simp
          _ ≤ ∑ x ∈ d.support, d x := Finset.sum_le_sum (fun x hx =>
              Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hx))
      rw [h, Finset.card_univ, Fintype.card_fin] at hcard
      omega
    have := alt_sum_monomial d hsupp
    calc ∑ T ∈ (Finset.univ : Finset (Fin r)).powerset,
          (-1 : ℚ) ^ T.card * (coeff d P * if d.support ⊆ T then 1 else 0)
        = coeff d P * ∑ T ∈ (Finset.univ : Finset (Fin r)).powerset,
          (-1 : ℚ) ^ T.card * (if d.support ⊆ T then 1 else 0) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun T _ => by ring)
      _ = 0 := by rw [this, mul_zero]
  exact h0 (hA.symm.trans hB)

end Erdos287.PostQSigma
