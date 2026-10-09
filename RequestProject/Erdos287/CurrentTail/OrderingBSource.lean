import RequestProject.Erdos287.CurrentTail.NearDiagonal

/-!
# Erdős #287 — current tail consolidation: Ordering A (retired) and Ordering B (live source)

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

## Ordering A — `CharacterBeforeCauchy = RETIRED`

Ordering A character-expands the tiny-base congruence `n ≡ c (mod f)` *before* the first
Cauchy step.  The referee showed this loses the true `1/f` density.  Recorded here:

* `Ordering`, `orderingStatus` with `orderingStatus .characterBeforeCauchy = .retired`;
* the counter-model `orderingA_loses_density`: for the indicator of a residue class
  `c (mod f)` inside `[1, fK]`, the Ordering-A route bound is `K √f` while the true sum and the
  Ordering-B bound are both `K`; so Ordering A only reaches a `1/√f`-scale bound.

## Ordering B — retain `f`, first Cauchy, congruence explicit

* `Rrel_eq_main_sub_coprimality` — the literal `R_rel` equals the relative-discrepancy form
  `∑ Γ_ξ ∑_d ℓ_X(d) Δ^{f_ξ,c_ξ}(d, b_{ξ,d})` minus an explicit coprimality-insertion error;
* `orderingB_first_cauchy` — first Cauchy with `f` retained inside the inner sum;
* `sq_sum_filter_eq_pairs` and `orderingB_expand` — opening the square produces pairs
  `(n₁,n₂)` both `≡ c (mod f)`;
* `orderingB_pair_congr` — every such pair satisfies **`n₁ ≡ n₂ (mod f)`** (kept explicit);
* `orderingB_routing` — the combined structural routing
  `retain f → first Cauchy → n₁ ≡ n₂ (f) → pair (relative-energy) form`.
-/

open scoped BigOperators
open Finset

namespace Erdos287.CurrentTail

/-! ### Status of the two orderings -/

/-- Route statuses used in this subtree. -/
inductive RouteStatus
  | live
  | retired
  deriving DecidableEq, Repr

/-- The two orderings of the tiny-base congruence versus the first Cauchy step. -/
inductive Ordering
  | characterBeforeCauchy
  | retainThenCauchy
  deriving DecidableEq, Repr, Fintype

/-- `CharacterBeforeCauchy = RETIRED`, `RetainThenCauchy = LIVE`. -/
def orderingStatus : Ordering → RouteStatus
  | .characterBeforeCauchy => .retired
  | .retainThenCauchy => .live

theorem CharacterBeforeCauchy_retired :
    orderingStatus .characterBeforeCauchy = .retired := rfl

theorem OrderingB_live : orderingStatus .retainThenCauchy = .live := rfl

/-! ### Ordering-A counter-model -/

/-- The bound produced by Ordering A for `|∑_{n ≡ c (f)} a_n|` with `‖a‖² = S2` over `[1,N]`:
after the character expansion each of the `φ(f)` characters is Cauchy'd over the full range,
and the `1/φ(f)` normalisation cancels the character count, leaving `√(N · S2)`. -/
noncomputable def orderingABound (N S2 : ℝ) : ℝ := Real.sqrt (N * S2)

/-- The Ordering-B bound: Cauchy over the retained support of size `T`: `√(T · S2)`. -/
noncomputable def orderingBBound (T S2 : ℝ) : ℝ := Real.sqrt (T * S2)

/-- The Ordering-B bound is valid: `|∑_{n∈T} a_n| ≤ √(|T| ∑ a_n²)`. -/
theorem orderingB_bound_valid (T : Finset ℕ) (a : ℕ → ℝ) :
    |∑ n ∈ T, a n| ≤ orderingBBound T.card (∑ n ∈ T, a n ^ 2) := by
  unfold orderingBBound
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt sq_sum_le_card_mul_sum_sq

/-- **Counter-model: Ordering A loses the `1/f` density.**  For the indicator of one residue
class modulo `f` in `[1, fK]` (so `|T| = K`, `‖a‖² = K`, true sum `K`):
the Ordering-B bound equals the truth `K`, while the Ordering-A bound is `K √f`. -/
theorem orderingA_loses_density (f K : ℕ) :
    orderingBBound K K = K ∧ orderingABound (f * K) K = K * Real.sqrt f := by
  constructor
  · unfold orderingBBound
    rw [← sq, Real.sqrt_sq (Nat.cast_nonneg _)]
  · unfold orderingABound
    rw [show (f : ℝ) * K * K = (K : ℝ) ^ 2 * f by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]

/-- The Ordering-A loss factor is at least `2` as soon as `f ≥ 4`. -/
theorem orderingA_loss_ge_two {f : ℕ} (K : ℕ) (hf : 4 ≤ f) :
    2 * orderingBBound K K ≤ orderingABound (f * K) K := by
  obtain ⟨hB, hA⟩ := orderingA_loses_density f K
  rw [hB, hA]
  have h2 : (2 : ℝ) ≤ Real.sqrt f := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hf)
  have hK' : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  nlinarith

/-! ### Ordering B: the literal relative remainder in relative-discrepancy form -/

namespace TensorSource

variable {ι : Type*} (T : TensorSource ι)

/-- Relative-discrepancy main part of `R_rel`. -/
noncomputable def RrelMain : ℝ :=
  ∑ j ∈ range T.ell, ∑ ξ ∈ T.Xi, T.Γ ξ * ∑ d ∈ T.D,
    T.lX d * DeltaRel T.S (T.α j) (T.f ξ) (T.c ξ) d (T.b ξ d)

/-- Coprimality-insertion error of `R_rel`. -/
noncomputable def RrelCoprime : ℝ :=
  ∑ j ∈ range T.ell, ∑ ξ ∈ T.Xi, T.Γ ξ * ∑ d ∈ T.D,
    T.lX d * ((1 / (Nat.totient d : ℝ)) *
      ∑ n ∈ T.S.filter (fun n => n ≡ T.c ξ [MOD T.f ξ] ∧ ¬ Nat.Coprime n d), T.α j n)

/-- **`R_rel = R_rel^main - R_rel^coprime`**, exactly, for compatible classes
`b_{ξ,d} ≡ c_ξ (mod f_ξ)`. -/
theorem Rrel_eq_main_sub_coprimality
    (hcompat : ∀ ξ ∈ T.Xi, ∀ d ∈ T.D, T.b ξ d ≡ T.c ξ [MOD T.f ξ]) :
    T.Rrel = T.RrelMain - T.RrelCoprime := by
  unfold Rrel RrelMain RrelCoprime
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun ξ hξ => ?_)
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [← mul_sub, relative_term_eq_DeltaRel T.S (T.α j) (T.d_pos d hd) (T.coprime ξ hξ d hd)
    (hcompat ξ hξ d hd)]

end TensorSource

/-! ### Ordering B: first Cauchy with the tiny base retained -/

/-- **First Cauchy, `f` retained.**
`(∑_m β_m ∑_{n≡c(f)} α_n K(m,n))² ≤ (∑_m β_m²) ∑_m (∑_{n≡c(f)} α_n K(m,n))²`. -/
theorem orderingB_first_cauchy (Mset S : Finset ℕ) (β α : ℕ → ℝ) (Kmn : ℕ → ℕ → ℝ)
    (f c : ℕ) :
    (∑ m ∈ Mset, β m * ∑ n ∈ S.filter (fun n => n ≡ c [MOD f]), α n * Kmn m n) ^ 2 ≤
      (∑ m ∈ Mset, β m ^ 2) *
        ∑ m ∈ Mset, (∑ n ∈ S.filter (fun n => n ≡ c [MOD f]), α n * Kmn m n) ^ 2 :=
  Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- Opening a square over a retained support produces pairs. -/
theorem sq_sum_filter_eq_pairs (T : Finset ℕ) (x : ℕ → ℝ) :
    (∑ n ∈ T, x n) ^ 2 = ∑ p ∈ T ×ˢ T, x p.1 * x p.2 := by
  rw [sq, Finset.sum_mul_sum, Finset.sum_product]

/-- **Pair expansion after the first Cauchy step.** -/
theorem orderingB_expand (Mset S : Finset ℕ) (α : ℕ → ℝ) (Kmn : ℕ → ℕ → ℝ) (f c : ℕ) :
    ∑ m ∈ Mset, (∑ n ∈ S.filter (fun n => n ≡ c [MOD f]), α n * Kmn m n) ^ 2 =
      ∑ p ∈ S.filter (fun n => n ≡ c [MOD f]) ×ˢ S.filter (fun n => n ≡ c [MOD f]),
        α p.1 * α p.2 * ∑ m ∈ Mset, Kmn m p.1 * Kmn m p.2 := by
  simp_rw [sq_sum_filter_eq_pairs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  ring

/-- **The congruence `n₁ ≡ n₂ (mod f)` survives the first Cauchy step.** -/
theorem orderingB_pair_congr (S : Finset ℕ) (f c : ℕ) :
    ∀ p ∈ S.filter (fun n => n ≡ c [MOD f]) ×ˢ S.filter (fun n => n ≡ c [MOD f]),
      p.1 ≡ p.2 [MOD f] := by
  intro p hp
  rw [Finset.mem_product] at hp
  exact (Finset.mem_filter.1 hp.1).2.trans (Finset.mem_filter.1 hp.2).2.symm

/-- The retained pairs lie in the congruent-pair set `{(n₁,n₂) : n₁ ≡ n₂ (f)}`. -/
theorem orderingB_pairs_subset (S : Finset ℕ) (f c : ℕ) :
    S.filter (fun n => n ≡ c [MOD f]) ×ˢ S.filter (fun n => n ≡ c [MOD f]) ⊆
      (S ×ˢ S).filter (fun p => p.1 ≡ p.2 [MOD f]) := by
  intro p hp
  refine Finset.mem_filter.2 ⟨?_, orderingB_pair_congr S f c p hp⟩
  rw [Finset.mem_product] at hp ⊢
  exact ⟨(Finset.mem_filter.1 hp.1).1, (Finset.mem_filter.1 hp.2).1⟩

/-- **Ordering-B structural routing** (retain `f` → first Cauchy → explicit congruence →
pair/relative-energy form). -/
theorem orderingB_routing (Mset S : Finset ℕ) (β α : ℕ → ℝ) (Kmn : ℕ → ℕ → ℝ) (f c : ℕ) :
    (∑ m ∈ Mset, β m * ∑ n ∈ S.filter (fun n => n ≡ c [MOD f]), α n * Kmn m n) ^ 2 ≤
      (∑ m ∈ Mset, β m ^ 2) *
        ∑ p ∈ S.filter (fun n => n ≡ c [MOD f]) ×ˢ S.filter (fun n => n ≡ c [MOD f]),
          α p.1 * α p.2 * ∑ m ∈ Mset, Kmn m p.1 * Kmn m p.2 ∧
    ∀ p ∈ S.filter (fun n => n ≡ c [MOD f]) ×ˢ S.filter (fun n => n ≡ c [MOD f]),
      p.1 ≡ p.2 [MOD f] := by
  refine ⟨?_, orderingB_pair_congr S f c⟩
  rw [← orderingB_expand]
  exact orderingB_first_cauchy Mset S β α Kmn f c

end Erdos287.CurrentTail
