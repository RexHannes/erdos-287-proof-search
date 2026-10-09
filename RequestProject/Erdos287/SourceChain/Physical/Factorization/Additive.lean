import Mathlib

/-!
# Erdős #287 — Pascadi's Proposition 5.2, additive (logarithmic) core

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Formalization of the *constructive* proof of

* Pascadi, arXiv:2505.00653, **Lemma 5.3** (placing the first six prime factors) and
* Pascadi, arXiv:2505.00653, **Proposition 5.2** (factorization in the upper-bound linear sieve
  support), including the greedy process and its Cases 1, 2, 3.1, 3.2,

written in logarithmic coordinates: a prime `p_i` is recorded by `t_i = log p_i / log x`, the
level `D = x^{3/5-50δ}` by `Δ = 3/5 - 50δ`, and `N = x^n`.  A factorization `d = d₁ d₂ d₃` is a
*colouring* `c : ℕ → Fin 3` of the positions of the ordered prime list; colour `0` is `d₁`,
colour `1` is `d₂`, colour `2` is `d₃`, and `csumS t c k S` is `log_x` of the colour-`k` part.

All hypotheses of Pascadi's statement are kept: `0 < δ < 10⁻⁵`, `x^{2δ} ≤ N ≤ x^{1/3+δ}`, the
decreasing order `p₁ ≥ p₂ ≥ ⋯`, and the `𝒟⁺(D)` inequalities `p₁⋯p_{j-1} p_j³ ≤ D` for odd `j`
(here `0`-indexed, i.e. for even `j`).  The sequence is indexed by `ℕ`; a finite prime list is
padded by `t_i = 0` (`p_i = 1`), which handles `d = 1` and fewer than six prime factors.

The target system is Pascadi (5.3):
`d₁ ≤ N x^{-δ}`, `N² d₂ d₃² ≤ x^{1-δ}`, `N² d₂⁵ d₃² ≤ x^{2-δ}`.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.Factor

/-- `log_x` of the colour-`k` factor, restricted to the positions in `S`. -/
noncomputable def csumS (t : ℕ → ℝ) (c : ℕ → Fin 3) (k : Fin 3) (S : Finset ℕ) : ℝ :=
  ∑ i ∈ S.filter (fun i => c i = k), t i

/-- Pascadi's hypotheses (Prop. 5.2 / Lemma 5.3) in logarithmic coordinates. -/
structure AddHyp (δ n : ℝ) (t : ℕ → ℝ) : Prop where
  δ_pos : 0 < δ
  δ_small : δ < 1 / 100000
  n_lo : 2 * δ ≤ n
  n_hi : n ≤ 1 / 3 + δ
  nonneg : ∀ i, 0 ≤ t i
  anti : Antitone t
  plus : ∀ j, Even j → ∑ i ∈ range j, t i + 3 * t j ≤ 3 / 5 - 50 * δ

/-- Pascadi's system (5.3) for `(log_x d₁, log_x d₂, log_x d₃)`. -/
def Good53 (δ n a₁ a₂ a₃ : ℝ) : Prop :=
  a₁ ≤ n - δ ∧ 2 * n + a₂ + 2 * a₃ ≤ 1 - δ ∧ 2 * n + 5 * a₂ + 2 * a₃ ≤ 2 - δ

/-! ### Colour-sum bookkeeping -/

lemma csumS_update_insert (t : ℕ → ℝ) (c : ℕ → Fin 3) (a k : Fin 3) (S : Finset ℕ) (i : ℕ)
    (hi : i ∉ S) :
    csumS t (Function.update c i a) k (insert i S) = csumS t c k S + if a = k then t i else 0 := by
  unfold csumS
  have hS : S.filter (fun j => Function.update c i a j = k) = S.filter (fun j => c j = k) := by
    apply Finset.filter_congr
    intro j hj
    rw [Function.update_of_ne (by rintro rfl; exact hi hj)]
  rw [Finset.filter_insert]
  simp only [Function.update_self]
  split_ifs with h
  · rw [sum_insert (by simp [hi]), hS]; ring
  · rw [hS]; simp

lemma csumS_total (t : ℕ → ℝ) (c : ℕ → Fin 3) (S : Finset ℕ) :
    csumS t c 0 S + csumS t c 1 S + csumS t c 2 S = ∑ i ∈ S, t i := by
  unfold csumS
  rw [← Finset.sum_fiberwise S c t, Fin.sum_univ_three]

lemma csumS_mono (t : ℕ → ℝ) (ht : ∀ i, 0 ≤ t i) (c : ℕ → Fin 3) (k : Fin 3) {S S' : Finset ℕ}
    (h : S ⊆ S') : csumS t c k S ≤ csumS t c k S' :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ h)
    (fun i _ _ => ht i)

lemma csumS_nonneg (t : ℕ → ℝ) (ht : ∀ i, 0 ≤ t i) (c : ℕ → Fin 3) (k : Fin 3)
    (S : Finset ℕ) : 0 ≤ csumS t c k S :=
  Finset.sum_nonneg (fun i _ => ht i)

/-- **One greedy placement** (the elementary step used throughout Pascadi's proof): if
`a_α + a_β + 2 t_i ≤ C_α + C_β` then `t_i` fits into slot `α` or slot `β`. -/
lemma placeOne (t : ℕ → ℝ) (c : ℕ → Fin 3) (S : Finset ℕ) (i : ℕ) (hi : i ∉ S) (α β : Fin 3)
    (hαβ : α ≠ β) (Cα Cβ : ℝ) (hα : csumS t c α S ≤ Cα) (hβ : csumS t c β S ≤ Cβ)
    (h : csumS t c α S + csumS t c β S + 2 * t i ≤ Cα + Cβ) :
    ∃ c' : ℕ → Fin 3, csumS t c' α (insert i S) ≤ Cα ∧ csumS t c' β (insert i S) ≤ Cβ ∧
      csumS t c' α (insert i S) + csumS t c' β (insert i S) =
        csumS t c α S + csumS t c β S + t i ∧
      ∀ k, k ≠ α → k ≠ β → csumS t c' k (insert i S) = csumS t c k S := by
  by_cases h1 : csumS t c α S + t i ≤ Cα
  · refine ⟨Function.update c i α, ?_, ?_, ?_, ?_⟩
    · rw [csumS_update_insert _ _ _ _ _ _ hi, if_pos rfl]; exact h1
    · rw [csumS_update_insert _ _ _ _ _ _ hi, if_neg hαβ]; simpa using hβ
    · rw [csumS_update_insert _ _ _ _ _ _ hi, csumS_update_insert _ _ _ _ _ _ hi, if_pos rfl,
        if_neg hαβ]; ring
    · intro k hk _
      rw [csumS_update_insert _ _ _ _ _ _ hi, if_neg (Ne.symm hk)]; ring
  · refine ⟨Function.update c i β, ?_, ?_, ?_, ?_⟩
    · rw [csumS_update_insert _ _ _ _ _ _ hi, if_neg (Ne.symm hαβ)]; simpa using hα
    · rw [csumS_update_insert _ _ _ _ _ _ hi, if_pos rfl]; linarith
    · rw [csumS_update_insert _ _ _ _ _ _ hi, csumS_update_insert _ _ _ _ _ _ hi, if_pos rfl,
        if_neg (Ne.symm hαβ)]; ring
    · intro k _ hk
      rw [csumS_update_insert _ _ _ _ _ _ hi, if_neg (Ne.symm hk)]; ring

/-- **The two-slot greedy completion** (Pascadi, proof of Prop. 5.2, Cases 3.1 and 3.2): the
positions `j ≤ k < R` are placed one after another into slot `α` or `β`, the third slot being
frozen, as long as before each placement `a_α + a_β + 2 t_k ≤ C_α + C_β`. -/
lemma twoSlot (t : ℕ → ℝ) (c : ℕ → Fin 3) (j R : ℕ) (hjR : j ≤ R) (α β : Fin 3) (hαβ : α ≠ β)
    (Cα Cβ : ℝ) (hα : csumS t c α (range j) ≤ Cα) (hβ : csumS t c β (range j) ≤ Cβ)
    (hstep : ∀ k, j ≤ k → k < R →
      ∑ i ∈ range k, t i - ∑ i ∈ range j, t i + csumS t c α (range j) +
        csumS t c β (range j) + 2 * t k ≤ Cα + Cβ) :
    ∃ c' : ℕ → Fin 3, csumS t c' α (range R) ≤ Cα ∧ csumS t c' β (range R) ≤ Cβ ∧
      ∀ k, k ≠ α → k ≠ β → csumS t c' k (range R) = csumS t c k (range j) := by
  suffices H : ∃ c' : ℕ → Fin 3, csumS t c' α (range R) ≤ Cα ∧ csumS t c' β (range R) ≤ Cβ ∧
      csumS t c' α (range R) + csumS t c' β (range R) =
        ∑ i ∈ range R, t i - ∑ i ∈ range j, t i + csumS t c α (range j) +
          csumS t c β (range j) ∧
      ∀ k, k ≠ α → k ≠ β → csumS t c' k (range R) = csumS t c k (range j) by
    obtain ⟨c', h1, h2, -, h4⟩ := H
    exact ⟨c', h1, h2, h4⟩
  induction R, hjR using Nat.le_induction with
  | base => exact ⟨c, hα, hβ, by ring, fun _ _ _ => rfl⟩
  | succ R hjR ih =>
    obtain ⟨c', h1, h2, h3, h4⟩ := ih (fun k hk hkR => hstep k hk (by omega))
    have hR : R ∉ range R := by simp
    obtain ⟨c'', g1, g2, g3, g4⟩ := placeOne t c' (range R) R hR α β hαβ Cα Cβ h1 h2
      (by rw [h3]; linarith [hstep R hjR (by omega)])
    refine ⟨c'', ?_, ?_, ?_, ?_⟩
    · rwa [range_add_one]
    · rwa [range_add_one]
    · rw [range_add_one, g3, h3, sum_insert hR]; ring
    · intro k hk1 hk2; rw [range_add_one, g4 k hk1 hk2, h4 k hk1 hk2]

/-! ### Derived `𝒟⁺` inequalities -/

section Derived

variable {δ n : ℝ} {t : ℕ → ℝ}

/-- `p₁ ⋯ p_{k-1} p_k² ≤ D` for every `k` (Pascadi, first line of the proof of Prop. 5.2). -/
lemma AddHyp.sq (h : AddHyp δ n t) (k : ℕ) : ∑ i ∈ range k, t i + 2 * t k ≤ 3 / 5 - 50 * δ := by
  rcases Nat.even_or_odd k with hk | hk
  · linarith [h.plus k hk, h.nonneg k]
  · obtain ⟨m, rfl⟩ := hk
    have hm := h.plus (2 * m) (even_two_mul m)
    have hle : t (2 * m + 1) ≤ t (2 * m) := h.anti (by omega)
    rw [sum_range_succ]
    linarith

/-- `p_7 ≤ D^{1/9}` (positions `≥ 6`, `0`-indexed). -/
lemma AddHyp.tail_small (h : AddHyp δ n t) (m : ℕ) (hm : 6 ≤ m) :
    9 * t m ≤ 3 / 5 - 50 * δ := by
  have h6 := h.plus 6 (by decide)
  have hle : ∀ i ∈ range 6, t 6 ≤ t i := fun i hi => h.anti (by simp at hi; omega)
  have hs : ∑ i ∈ range 6, t 6 ≤ ∑ i ∈ range 6, t i := Finset.sum_le_sum hle
  simp only [sum_const, card_range, nsmul_eq_mul] at hs
  have : t m ≤ t 6 := h.anti hm
  push_cast at hs
  linarith

end Derived

/-! ### Lemma 5.3: placing the first six prime factors -/

/-- **Pascadi, Lemma 5.3.**  The first six positions can be coloured with
`d₁ ≤ D₁ = N x^{-δ}`, `d₂ ≤ D₂ = x^{4/15-5δ}`, `d₃ ≤ D₃ = x^{2/5+2δ}/N`. -/
theorem lemma53 {δ n : ℝ} {t : ℕ → ℝ} (h : AddHyp δ n t) :
    ∃ c : ℕ → Fin 3, csumS t c 0 (range 6) ≤ n - δ ∧
      csumS t c 1 (range 6) ≤ 4 / 15 - 5 * δ ∧ csumS t c 2 (range 6) ≤ 2 / 5 + 2 * δ - n := by
  have hδ := h.δ_pos; have hδ' := h.δ_small; have hn1 := h.n_lo; have hn2 := h.n_hi
  have h0 := h.plus 0 (by decide); have h2 := h.plus 2 (by decide)
  have h4 := h.plus 4 (by decide)
  simp only [sum_range_succ, sum_range_zero] at h0 h2 h4
  have a01 : t 1 ≤ t 0 := h.anti (by omega); have a12 : t 2 ≤ t 1 := h.anti (by omega)
  have a23 : t 3 ≤ t 2 := h.anti (by omega); have a34 : t 4 ≤ t 3 := h.anti (by omega)
  have a45 : t 5 ≤ t 4 := h.anti (by omega); have p5 := h.nonneg 5
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 0 := by decide
  have h12' : (1 : Fin 3) ≠ 2 := by decide
  -- generic: starting from all positions of `T` in colour 1, place the listed positions greedily
  -- into colours 0 and 2
  have start : ∀ T : Finset ℕ, csumS t (fun _ => 1) 0 T = 0 ∧ csumS t (fun _ => 1) 2 T = 0 ∧
      csumS t (fun _ => 1) 1 T = ∑ i ∈ T, t i := by
    intro T; simp [csumS]
  -- The three inequalities of Pascadi cannot hold simultaneously.
  by_cases C1 : t 0 + t 3 + t 4 ≤ 4 / 15 - 5 * δ
  · -- Case 1: `d₂ = p₁ p₄ p₅`; place `p₂, p₃, p₆`.
    obtain ⟨s0, s2, s1⟩ := start {0, 3, 4}
    have e1 : (1 : ℕ) ∉ ({0, 3, 4} : Finset ℕ) := by decide
    obtain ⟨c1, b1, b1', e1s, e1o⟩ := placeOne t (fun _ => 1) {0, 3, 4} 1 e1 0 2 h02
      (n - δ) (2 / 5 + 2 * δ - n) (by rw [s0]; linarith) (by rw [s2]; linarith)
      (by rw [s0, s2]; linarith)
    have e2 : (2 : ℕ) ∉ insert 1 ({0, 3, 4} : Finset ℕ) := by decide
    obtain ⟨c2, b2, b2', e2s, e2o⟩ := placeOne t c1 _ 2 e2 0 2 h02
      (n - δ) (2 / 5 + 2 * δ - n) b1 b1' (by rw [e1s, s0, s2]; linarith)
    have e5 : (5 : ℕ) ∉ insert 2 (insert 1 ({0, 3, 4} : Finset ℕ)) := by decide
    obtain ⟨c3, b3, b3', -, e3o⟩ := placeOne t c2 _ 5 e5 0 2 h02
      (n - δ) (2 / 5 + 2 * δ - n) b2 b2' (by rw [e2s, e1s, s0, s2]; linarith)
    have hset : insert 5 (insert 2 (insert 1 ({0, 3, 4} : Finset ℕ))) = range 6 := by decide
    rw [hset] at b3 b3' e3o
    refine ⟨c3, b3, ?_, b3'⟩
    rw [e3o 1 h12 h12', e2o 1 h12 h12', e1o 1 h12 h12', s1]
    simp [Finset.sum_insert]
    linarith
  by_cases C2 : t 1 + t 2 + t 4 ≤ 4 / 15 - 5 * δ
  · -- Case 2: `d₂ = p₂ p₃ p₅`; place `p₁, p₄, p₆`.
    obtain ⟨s0, s2, s1⟩ := start {1, 2, 4}
    have e1 : (0 : ℕ) ∉ ({1, 2, 4} : Finset ℕ) := by decide
    obtain ⟨c1, b1, b1', e1s, e1o⟩ := placeOne t (fun _ => 1) {1, 2, 4} 0 e1 0 2 h02
      (n - δ) (2 / 5 + 2 * δ - n) (by rw [s0]; linarith) (by rw [s2]; linarith)
      (by rw [s0, s2]; linarith)
    have e2 : (3 : ℕ) ∉ insert 0 ({1, 2, 4} : Finset ℕ) := by decide
    obtain ⟨c2, b2, b2', e2s, e2o⟩ := placeOne t c1 _ 3 e2 0 2 h02
      (n - δ) (2 / 5 + 2 * δ - n) b1 b1' (by rw [e1s, s0, s2]; linarith)
    have e5 : (5 : ℕ) ∉ insert 3 (insert 0 ({1, 2, 4} : Finset ℕ)) := by decide
    obtain ⟨c3, b3, b3', -, e3o⟩ := placeOne t c2 _ 5 e5 0 2 h02
      (n - δ) (2 / 5 + 2 * δ - n) b2 b2' (by rw [e2s, e1s, s0, s2]; linarith)
    have hset : insert 5 (insert 3 (insert 0 ({1, 2, 4} : Finset ℕ))) = range 6 := by decide
    rw [hset] at b3 b3' e3o
    refine ⟨c3, b3, ?_, b3'⟩
    rw [e3o 1 h12 h12', e2o 1 h12 h12', e1o 1 h12 h12', s1]
    simp [Finset.sum_insert]
    linarith
  · -- Case 3: the third inequality fails (the first two hold); `d₂ = p₂ p₃`;
    -- place `p₁, p₄, p₆`, then `p₅`.
    have C3 : t 0 + t 1 + t 2 + t 3 + 4 * t 4 ≤
        (n - δ) + (4 / 15 - 5 * δ) + (2 / 5 + 2 * δ - n) := by
      by_contra hc; push_neg at C1 C2 hc; linarith
    push_neg at C2
    obtain ⟨s0, s2, s1⟩ := start {1, 2}
    have e1 : (0 : ℕ) ∉ ({1, 2} : Finset ℕ) := by decide
    obtain ⟨c1, b1, b1', e1s, e1o⟩ := placeOne t (fun _ => 1) {1, 2} 0 e1 0 2 h02
      (n - δ) (2 / 5 + 2 * δ - n) (by rw [s0]; linarith) (by rw [s2]; linarith)
      (by rw [s0, s2]; linarith)
    have e2 : (3 : ℕ) ∉ insert 0 ({1, 2} : Finset ℕ) := by decide
    obtain ⟨c2, b2, b2', e2s, e2o⟩ := placeOne t c1 _ 3 e2 0 2 h02
      (n - δ) (2 / 5 + 2 * δ - n) b1 b1' (by rw [e1s, s0, s2]; linarith)
    have e5 : (5 : ℕ) ∉ insert 3 (insert 0 ({1, 2} : Finset ℕ)) := by decide
    obtain ⟨c3, b3, b3', e3s, e3o⟩ := placeOne t c2 _ 5 e5 0 2 h02
      (n - δ) (2 / 5 + 2 * δ - n) b2 b2' (by rw [e2s, e1s, s0, s2]; linarith)
    have e4 : (4 : ℕ) ∉ insert 5 (insert 3 (insert 0 ({1, 2} : Finset ℕ))) := by decide
    obtain ⟨c4, b4, b4', -, e4o⟩ := placeOne t c3 _ 4 e4 0 2 h02
      (n - δ) (2 / 5 + 2 * δ - n) b3 b3' (by rw [e3s, e2s, e1s, s0, s2]; linarith)
    have hset : insert 4 (insert 5 (insert 3 (insert 0 ({1, 2} : Finset ℕ)))) = range 6 := by
      decide
    rw [hset] at b4 b4' e4o
    refine ⟨c4, b4, ?_, b4'⟩
    rw [e4o 1 h12 h12', e3o 1 h12 h12', e2o 1 h12 h12', e1o 1 h12 h12', s1]
    simp [Finset.sum_insert]
    linarith

end Erdos287.Physical.Factor
