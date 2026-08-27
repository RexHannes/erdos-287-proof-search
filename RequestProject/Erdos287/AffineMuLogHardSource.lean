import Mathlib
import RequestProject.Erdos287.AffineMuLogIdentity

/-!
# V15, Part 3 — the exact three-way `q`/`r` partition of the `μ`-log source

For a cutoff `U : ℕ` the factor pairs `q r = N` are split into three classes

* `A` : `q ≤ U`;
* `B` : `q > U` and `r ≤ U`;
* `C` : `q > U` and `r > U`   (the *hard* class).

Everything here is finite and exact:

* `pairClass_exhaustive` / `pairClass_union` — exhaustiveness,
* `pairClass_disjoint_*` — pairwise disjointness,
* `pair_sum_split` — exact recombination of an arbitrary weighted pair sum, over any
  additive commutative monoid,

and then the specialisations to `w (q,r) = μ(q) log r` on the divisor antidiagonal
(`mulog_sum_eq_smallQ_add_smallR_add_hard`) and to the affine argument `N = 2mn + s`
(`mulog_affine_sum_eq_smallQ_add_smallR_add_hard`).

The hard source is by definition

`muLogHard N U = ∑_{q r = N, q > U, r > U} μ(q) log r`.

**No smallness of any of the three pieces is asserted, here or anywhere else in this
project.**  The analytic labels ("Type I", "Type II") appear only in this documentation,
never in a theorem conclusion.

Ledger: `AFFINE287-MULOG-HARD-PARTITION45 : PROVED_FINITE/ALGEBRAIC`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction
open scoped BigOperators

namespace Erdos287
namespace MuLog

/-! ## The three classes of factor pairs -/

/-- Class `A`: pairs with small left factor, `q ≤ U`. -/
def pairSmallQ (s : Finset (ℕ × ℕ)) (U : ℕ) : Finset (ℕ × ℕ) :=
  s.filter (fun x => x.1 ≤ U)

/-- Class `B`: pairs with large left factor but small right factor, `q > U`, `r ≤ U`. -/
def pairSmallR (s : Finset (ℕ × ℕ)) (U : ℕ) : Finset (ℕ × ℕ) :=
  s.filter (fun x => U < x.1 ∧ x.2 ≤ U)

/-- Class `C`: the hard class, `q > U` and `r > U`. -/
def pairHard (s : Finset (ℕ × ℕ)) (U : ℕ) : Finset (ℕ × ℕ) :=
  s.filter (fun x => U < x.1 ∧ U < x.2)

@[simp] theorem mem_pairSmallQ {s : Finset (ℕ × ℕ)} {U : ℕ} {x : ℕ × ℕ} :
    x ∈ pairSmallQ s U ↔ x ∈ s ∧ x.1 ≤ U := by
  simp [pairSmallQ]

@[simp] theorem mem_pairSmallR {s : Finset (ℕ × ℕ)} {U : ℕ} {x : ℕ × ℕ} :
    x ∈ pairSmallR s U ↔ x ∈ s ∧ (U < x.1 ∧ x.2 ≤ U) := by
  simp [pairSmallR]

@[simp] theorem mem_pairHard {s : Finset (ℕ × ℕ)} {U : ℕ} {x : ℕ × ℕ} :
    x ∈ pairHard s U ↔ x ∈ s ∧ (U < x.1 ∧ U < x.2) := by
  simp [pairHard]

/-- **Exhaustiveness.** -/
theorem pairClass_exhaustive {s : Finset (ℕ × ℕ)} {U : ℕ} {x : ℕ × ℕ} (hx : x ∈ s) :
    x ∈ pairSmallQ s U ∨ x ∈ pairSmallR s U ∨ x ∈ pairHard s U := by
  by_cases h1 : x.1 ≤ U
  · exact Or.inl (by simp [hx, h1])
  · by_cases h2 : x.2 ≤ U
    · exact Or.inr (Or.inl (by simp [hx, h2]; omega))
    · exact Or.inr (Or.inr (by simp [hx]; omega))

/-- **Exhaustiveness, set form.** -/
theorem pairClass_union (s : Finset (ℕ × ℕ)) (U : ℕ) :
    pairSmallQ s U ∪ pairSmallR s U ∪ pairHard s U = s := by
  ext x
  constructor
  · intro hx
    simp only [Finset.mem_union, mem_pairSmallQ, mem_pairSmallR, mem_pairHard] at hx
    tauto
  · intro hx
    rcases pairClass_exhaustive (U := U) hx with h | h | h <;>
      simp only [Finset.mem_union] <;> tauto

/-- **Disjointness `A`/`B`.** -/
theorem pairClass_disjoint_QR (s : Finset (ℕ × ℕ)) (U : ℕ) :
    Disjoint (pairSmallQ s U) (pairSmallR s U) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [mem_pairSmallQ] at hx
  simp only [mem_pairSmallR] at hx'
  omega

/-- **Disjointness `A`/`C`.** -/
theorem pairClass_disjoint_QH (s : Finset (ℕ × ℕ)) (U : ℕ) :
    Disjoint (pairSmallQ s U) (pairHard s U) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [mem_pairSmallQ] at hx
  simp only [mem_pairHard] at hx'
  omega

/-- **Disjointness `B`/`C`.** -/
theorem pairClass_disjoint_RH (s : Finset (ℕ × ℕ)) (U : ℕ) :
    Disjoint (pairSmallR s U) (pairHard s U) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [mem_pairSmallR] at hx
  simp only [mem_pairHard] at hx'
  omega

/-- **`pair_sum_split`** — exact recombination of an arbitrary weighted pair sum. -/
theorem pair_sum_split {M : Type*} [AddCommMonoid M] (s : Finset (ℕ × ℕ)) (U : ℕ)
    (w : ℕ × ℕ → M) :
    ∑ x ∈ s, w x
      = (∑ x ∈ pairSmallQ s U, w x) + (∑ x ∈ pairSmallR s U, w x)
          + ∑ x ∈ pairHard s U, w x := by
  classical
  have h1 : (∑ x ∈ s.filter (fun x => x.1 ≤ U), w x)
      + ∑ x ∈ s.filter (fun x => ¬ x.1 ≤ U), w x = ∑ x ∈ s, w x :=
    Finset.sum_filter_add_sum_filter_not s _ w
  have h2 : (∑ x ∈ (s.filter (fun x => ¬ x.1 ≤ U)).filter (fun x => x.2 ≤ U), w x)
      + ∑ x ∈ (s.filter (fun x => ¬ x.1 ≤ U)).filter (fun x => ¬ x.2 ≤ U), w x
      = ∑ x ∈ s.filter (fun x => ¬ x.1 ≤ U), w x :=
    Finset.sum_filter_add_sum_filter_not _ _ w
  have e1 : (s.filter (fun x => ¬ x.1 ≤ U)).filter (fun x => x.2 ≤ U) = pairSmallR s U := by
    ext x
    simp only [Finset.mem_filter, mem_pairSmallR]
    constructor
    · rintro ⟨⟨hs, h1⟩, h2⟩; exact ⟨hs, by omega, h2⟩
    · rintro ⟨hs, h1, h2⟩; exact ⟨⟨hs, by omega⟩, h2⟩
  have e2 : (s.filter (fun x => ¬ x.1 ≤ U)).filter (fun x => ¬ x.2 ≤ U) = pairHard s U := by
    ext x
    simp only [Finset.mem_filter, mem_pairHard]
    constructor
    · rintro ⟨⟨hs, h1⟩, h2⟩; exact ⟨hs, by omega, by omega⟩
    · rintro ⟨hs, h1, h2⟩; exact ⟨⟨hs, by omega⟩, by omega⟩
  have e0 : s.filter (fun x => x.1 ≤ U) = pairSmallQ s U := rfl
  rw [e1, e2] at h2
  rw [e0] at h1
  rw [← h1, ← h2, add_assoc]

/-! ## Specialisation to the `μ`-log weight -/

/-- The `μ`-log weight of a factor pair. -/
noncomputable def muLogWeight (x : ℕ × ℕ) : ℝ :=
  (moebius x.1 : ℝ) * ArithmeticFunction.log x.2

/-- Class-`A` part of the `μ`-log source. -/
noncomputable def muLogSmallQ (N U : ℕ) : ℝ :=
  ∑ x ∈ pairSmallQ N.divisorsAntidiagonal U, muLogWeight x

/-- Class-`B` part of the `μ`-log source. -/
noncomputable def muLogSmallR (N U : ℕ) : ℝ :=
  ∑ x ∈ pairSmallR N.divisorsAntidiagonal U, muLogWeight x

/-- **The hard source** `∑_{q r = N, q > U, r > U} μ(q) log r`.  No bound on it is claimed. -/
noncomputable def muLogHard (N U : ℕ) : ℝ :=
  ∑ x ∈ pairHard N.divisorsAntidiagonal U, muLogWeight x

/-- **`mulog_sum_eq_smallQ_add_smallR_add_hard`** — `PROVED_FINITE`. -/
theorem mulog_sum_eq_smallQ_add_smallR_add_hard (N U : ℕ) :
    vonMangoldt N = muLogSmallQ N U + muLogSmallR N U + muLogHard N U := by
  rw [vonMangoldt_eq_sum_antidiagonal N, muLogSmallQ, muLogSmallR, muLogHard]
  exact pair_sum_split _ U muLogWeight

open Erdos287.Vaughan

/-- The affine specialisation of the three-way split, at `N = 2mn + s`. -/
theorem mulog_affine_sum_eq_smallQ_add_smallR_add_hard (s : AffineSign) (U m n : ℕ) :
    vonMangoldt (affineNat s m n)
      = muLogSmallQ (affineNat s m n) U + muLogSmallR (affineNat s m n) U
          + muLogHard (affineNat s m n) U :=
  mulog_sum_eq_smallQ_add_smallR_add_hard _ U

/-- Every pair in the hard class of `N = 2mn + s` really satisfies the determinant-one
relation `q r − 2 m n = s` in `ℤ` (positivity hypotheses carry the `Nat`-subtraction
firewall). -/
theorem pairHard_affine_det_one (s : AffineSign) {U m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {x : ℕ × ℕ} (hx : x ∈ pairHard (affineNat s m n).divisorsAntidiagonal U) :
    (x.1 : ℤ) * (x.2 : ℤ) - 2 * (m : ℤ) * (n : ℤ) = s.val := by
  simp only [mem_pairHard, Nat.mem_divisorsAntidiagonal] at hx
  have hmul : ((x.1 * x.2 : ℕ) : ℤ) = ((affineNat s m n : ℕ) : ℤ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) hx.1.1
  rw [Nat.cast_mul] at hmul
  rw [hmul, affineNat_cast s hm hn]
  ring

end MuLog
end Erdos287
