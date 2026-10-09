import RequestProject.Erdos287.ResearchBankV10.TypeIICoefficient

/-!
# Erdős #287 — Research Bank V10 §I: high-H / low-H local counting

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The positive decomposition-count identities underlying the two coefficient norms, with the three
layers kept **separate**:

1. **exact counting quantity** — `collision_identity`: `∑_t |fibre(t)|² = #{(x, y) : t(x) = t(y)}`
   (restricted to any predicate on `t`, e.g. `w ≠ 0` or `w = 0`); `norm_sq_le_collisions`: for unit
   weights, `‖G‖₂² ≤ #collisions`; `collisions_split`: collisions = (`w = 0`) + (`w ≠ 0`);
2. **divisor multiplicity factor** — the explicit real parameter `Dmult`;
3. **external asymptotic envelope** — `HighHCountEnvelope`: the `w ≠ 0` collision count is at most
   `Dmult·(Q⁻²N²H² + K N H³ + N²H + K N Q² H²)`.  This is a *hypothesis* (no `x^ε` magic constant).

`highH_norm_bound` composes them into the high-H skeleton.  The `w = 0` primitive-ratio count
(`wZero_count_le`: `≤ H N²`) and the low-H diagonal (`lowH_w_eq`, `lowH_diag_card`: `= H N`) are
exact.

**Cost comparison** (`lowH_cost_identity`, `lowH_cost_lt_one`): with the correct prefactor
relation `P_lo · C Q² = P_hi · H`,
`(P_lo/P_hi)² · (H N²)/(Q⁻² N² H²) = H/(C² Q²) < 1` under `H < Q²`, `C ≥ 1`.
Fixtures `smaller_norm_insufficient` and `wrong_prefactor_fails`: a smaller norm **without** the
correct prefactor does not give low-H success.
-/

namespace Erdos287
namespace ResearchBankV10
namespace TypeIIHighLow

open Finset TypeIICoefficient

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Fibre of `f` over `t` inside `S`. -/
def fibre (S : Finset α) (f : α → β) (t : β) : Finset α := S.filter (fun x => f x = t)

/-- **Collision identity** (restricted to a predicate `P` on the image). -/
theorem collision_identity (S : Finset α) (f : α → β) (P : β → Prop) [DecidablePred P] :
    ∑ t ∈ (S.image f).filter P, (fibre S f t).card ^ 2 =
      ((S ×ˢ S).filter (fun p => f p.1 = f p.2 ∧ P (f p.1))).card := by
  classical
  have hprod : ((S ×ˢ S).filter (fun p => f p.1 = f p.2 ∧ P (f p.1))) =
      ((S.image f).filter P).biUnion (fun t => fibre S f t ×ˢ fibre S f t) := by
    ext ⟨x, y⟩
    simp only [fibre, mem_filter, mem_product, mem_biUnion, mem_image]
    constructor
    · rintro ⟨⟨hx, hy⟩, hxy, hP⟩
      exact ⟨f x, ⟨⟨x, hx, rfl⟩, hP⟩, ⟨hx, rfl⟩, hy, hxy.symm⟩
    · rintro ⟨t, ⟨⟨z, hz, rfl⟩, hP⟩, ⟨hx, hfx⟩, hy, hfy⟩
      exact ⟨⟨hx, hy⟩, hfx.trans hfy.symm, hfx ▸ hP⟩
  rw [hprod, Finset.card_biUnion]
  · simp [sq, Finset.card_product]
  · intro t₁ _ t₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    simp only [fibre, mem_product, mem_filter] at h1 h2
    exact hne (h1.1.2.symm.trans h2.1.2)

/-- **Collision split**: collisions with `P` plus collisions with `¬P` = all collisions. -/
theorem collisions_split (S : Finset α) (f : α → β) (P : β → Prop) [DecidablePred P] :
    ((S ×ˢ S).filter (fun p => f p.1 = f p.2 ∧ P (f p.1))).card +
      ((S ×ˢ S).filter (fun p => f p.1 = f p.2 ∧ ¬ P (f p.1))).card =
      ((S ×ˢ S).filter (fun p => f p.1 = f p.2)).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext p; simp only [mem_union, mem_filter]; tauto
  · rw [Finset.disjoint_left]; intro p h1 h2
    simp only [mem_filter] at h1 h2; exact h2.2.2 h1.2.2

omit [DecidableEq α] [DecidableEq β] in
/-- Cauchy–Schwarz on one fibre: `‖∑_{fibre} φ‖² ≤ |fibre|²` for unit weights. -/
theorem fibre_norm_sq_le (T : Finset α) (φ : α → ℂ) (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    ‖∑ x ∈ T, φ x‖ ^ 2 ≤ (T.card : ℝ) ^ 2 := by
  have h1 : ‖∑ x ∈ T, φ x‖ ≤ T.card := by
    calc ‖∑ x ∈ T, φ x‖ ≤ ∑ x ∈ T, ‖φ x‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ T, (1 : ℝ) := Finset.sum_le_sum fun x _ => hφ x
      _ = T.card := by simp
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-- **Norm ≤ collisions**: for unit packet weights, the squared `ℓ²` norm of the grouped
coefficient restricted to `P` is at most the restricted collision count. -/
theorem norm_sq_le_collisions (S : Finset α) (f : α → β) (P : β → Prop) [DecidablePred P]
    (φ : α → ℂ) (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    ∑ t ∈ (S.image f).filter P, ‖∑ x ∈ fibre S f t, φ x‖ ^ 2 ≤
      (((S ×ˢ S).filter (fun p => f p.1 = f p.2 ∧ P (f p.1))).card : ℝ) := by
  rw [← collision_identity]
  push_cast
  exact Finset.sum_le_sum fun t _ => fibre_norm_sq_le _ φ hφ

/-! ## The Type-II instance -/

/-- `‖B^{≠0}‖₂²`: the squared norm of the grouped coefficient on `w ≠ 0`. -/
noncomputable def normSqNonzero (S : Finset CoeffVars) (φ : CoeffVars → ℂ) : ℝ :=
  ∑ t ∈ (S.image indexMap).filter (fun t => t.2.2 ≠ 0), ‖grouped S φ t‖ ^ 2

/-- The `w ≠ 0` collision count. -/
def collisionsNonzero (S : Finset CoeffVars) : ℕ :=
  ((S ×ˢ S).filter (fun p => indexMap p.1 = indexMap p.2 ∧ (indexMap p.1).2.2 ≠ 0)).card

/-- **Exact layer**: `‖B^{≠0}‖₂² ≤ #collisions(w ≠ 0)` for unit weights. -/
theorem normSqNonzero_le (S : Finset CoeffVars) (φ : CoeffVars → ℂ) (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    normSqNonzero S φ ≤ collisionsNonzero S :=
  norm_sq_le_collisions S indexMap (fun t => t.2.2 ≠ 0) φ hφ

/-- **External envelope** (hypothesis, never proved here): the `w ≠ 0` collision count is at
most the divisor-multiplicity factor times the four-term high-H envelope. -/
structure HighHCountEnvelope (S : Finset CoeffVars) (Dmult Q N H K : ℝ) : Prop where
  bound : (collisionsNonzero S : ℝ) ≤
    Dmult * (Q⁻¹ ^ 2 * N ^ 2 * H ^ 2 + K * N * H ^ 3 + N ^ 2 * H + K * N * Q ^ 2 * H ^ 2)

/-- **High-H skeleton**: exact counting + divisor factor + external envelope. -/
theorem highH_norm_bound (S : Finset CoeffVars) (φ : CoeffVars → ℂ) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    {Dmult Q N H K : ℝ} (henv : HighHCountEnvelope S Dmult Q N H K) :
    normSqNonzero S φ ≤
      Dmult * (Q⁻¹ ^ 2 * N ^ 2 * H ^ 2 + K * N * H ^ 3 + N ^ 2 * H + K * N * Q ^ 2 * H ^ 2) :=
  (normSqNonzero_le S φ hφ).trans henv.bound

/-! ## The `w = 0` primitive-ratio count -/

/-- The box of `(h, h', n₂, n₂') ∈ [1,H]² × [1,N]²` with `h n₂' = h' n₂`. -/
def wZeroSet (H N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Icc 1 H ×ˢ Icc 1 H ×ˢ Icc 1 N ×ˢ Icc 1 N).filter
    (fun p => p.1 * p.2.2.2 = p.2.1 * p.2.2.1)

/-- **`w = 0` count**: `#{h n₂' = h' n₂} ≤ H N²` (since `h'` is determined by `h, n₂, n₂'`). -/
theorem wZero_count_le (H N : ℕ) : (wZeroSet H N).card ≤ H * N ^ 2 := by
  have : (wZeroSet H N).card ≤ (Icc 1 H ×ˢ Icc 1 N ×ˢ Icc 1 N).card := by
    refine Finset.card_le_card_of_injOn (fun p => (p.1, p.2.2.1, p.2.2.2)) ?_ ?_
    · intro p hp
      simp only [wZeroSet, coe_filter, mem_product, mem_Icc, Set.mem_setOf_eq, coe_product,
        Set.mem_prod, coe_Icc, Set.mem_Icc] at hp ⊢
      exact ⟨hp.1.1, hp.1.2.2.1, hp.1.2.2.2⟩
    · rintro ⟨h₁, h₁', n₁, n₁'⟩ hp ⟨h₂, h₂', n₂, n₂'⟩ hq heq
      simp only [wZeroSet, coe_filter, mem_product, mem_Icc, Set.mem_setOf_eq] at hp hq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      have hn : 0 < n₁ := hp.1.2.2.1.1
      have : h₁' * n₁ = h₂' * n₁ := by rw [← hp.2, ← hq.2]
      have := Nat.eq_of_mul_eq_mul_right hn this
      subst this; rfl
  simpa [Finset.card_product, sq, mul_assoc] using this

/-! ## Low-H -/

/-- **Low-H index**: for `h = h'`, `w = a k h (n₂' − n₂)`. -/
theorem lowH_w_eq (a k h n₂ n₂' : ℤ) : a * k * (h * n₂' - h * n₂) = a * k * h * (n₂' - n₂) := by
  ring

/-- The low-H diagonal `(h, n₂, n₂')` with `n₂ = n₂'`. -/
def lowHDiag (H N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Icc 1 H ×ˢ Icc 1 N ×ˢ Icc 1 N).filter (fun p => p.2.1 = p.2.2)

/-- **Low-H diagonal count** `= H N`. -/
theorem lowH_diag_card (H N : ℕ) : (lowHDiag H N).card = H * N := by
  unfold lowHDiag
  rw [Finset.filter_product_right (q := fun q : ℕ × ℕ => q.1 = q.2)]
  rw [Finset.card_product]
  have : ((Icc 1 N ×ˢ Icc 1 N).filter (fun q : ℕ × ℕ => q.1 = q.2)) = (Icc 1 N).diag := by
    ext ⟨a, b⟩; simp only [mem_filter, mem_product, Finset.mem_diag]
    constructor
    · rintro ⟨⟨ha, -⟩, rfl⟩; exact ⟨ha, rfl⟩
    · rintro ⟨ha, rfl⟩; exact ⟨⟨ha, ha⟩, rfl⟩
  rw [this, Finset.diag_card]
  simp

/-! ## The cost comparison -/

/-- **Cost identity**: with the prefactor relation `P_lo · C Q² = P_hi · H`,
`(P_lo/P_hi)² · (H N²)/(Q⁻² N² H²) = H/(C² Q²)`. -/
theorem lowH_cost_identity {Plo Phi H N Q C : ℝ} (hPhi : Phi ≠ 0) (hH : H ≠ 0) (hN : N ≠ 0)
    (hQ : Q ≠ 0) (hC : C ≠ 0) (hrel : Plo * (C * Q ^ 2) = Phi * H) :
    (Plo / Phi) ^ 2 * ((H * N ^ 2) / (Q⁻¹ ^ 2 * N ^ 2 * H ^ 2)) = H / (C ^ 2 * Q ^ 2) := by
  have hP : Plo = Phi * H / (C * Q ^ 2) := by
    field_simp; linarith [hrel]
  rw [hP]
  field_simp

/-- **Low-H is cheaper**: `H/(C² Q²) < 1` under `H < Q²`, `C ≥ 1`. -/
theorem lowH_cost_lt_one {H Q C : ℝ} (hQ : Q ≠ 0) (hHQ : H < Q ^ 2) (hC : 1 ≤ C) :
    H / (C ^ 2 * Q ^ 2) < 1 := by
  have hQ2 : 0 < Q ^ 2 := by positivity
  have hC2 : 1 ≤ C ^ 2 := one_le_pow₀ hC
  rw [div_lt_one (by positivity)]
  nlinarith

/-- The composed low-H conclusion. -/
theorem lowH_cost_comparison {Plo Phi H N Q C : ℝ} (hPhi : Phi ≠ 0) (hH : H ≠ 0) (hN : N ≠ 0)
    (hQ : Q ≠ 0) (hrel : Plo * (C * Q ^ 2) = Phi * H) (hHQ : H < Q ^ 2) (hC : 1 ≤ C) :
    (Plo / Phi) ^ 2 * ((H * N ^ 2) / (Q⁻¹ ^ 2 * N ^ 2 * H ^ 2)) < 1 := by
  rw [lowH_cost_identity hPhi hH hN hQ (by linarith) hrel]
  exact lowH_cost_lt_one hQ hHQ hC

/-- **Fixture**: a smaller coefficient norm alone does not give a smaller cost. -/
theorem smaller_norm_insufficient :
    ¬ ∀ Plo Phi nlo nhi : ℝ, 0 < Plo → 0 < Phi → 0 < nlo → nlo < nhi →
      Plo ^ 2 * nlo < Phi ^ 2 * nhi := by
  intro h
  have := h 2 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

/-- **Fixture**: with the *wrong* prefactor `P_lo = P_hi`, the low-H/high-H cost ratio is
`Q²/H > 1` under `H < Q²` — low-H would *fail*. -/
theorem wrong_prefactor_fails {P H N Q : ℝ} (hP : P ≠ 0) (hH : 0 < H) (hN : N ≠ 0) (hQ : Q ≠ 0)
    (hHQ : H < Q ^ 2) :
    1 < (P / P) ^ 2 * ((H * N ^ 2) / (Q⁻¹ ^ 2 * N ^ 2 * H ^ 2)) := by
  have : (P / P) ^ 2 * ((H * N ^ 2) / (Q⁻¹ ^ 2 * N ^ 2 * H ^ 2)) = Q ^ 2 / H := by
    field_simp
  rw [this, one_lt_div hH]
  exact hHQ

end TypeIIHighLow
end ResearchBankV10
end Erdos287
