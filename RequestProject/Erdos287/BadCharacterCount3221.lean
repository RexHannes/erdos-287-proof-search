import Mathlib
import RequestProject.Erdos287.TwoHighProjector3221

/-!
# V21, Phase 3 — the **repaired** safe bad-character cardinality

`BADCHAR-D2-RELEDGER45 : FINITE / LEAN_PROVED`

The unsafe heuristic `#Bad_q ≪ D · τ(q)` is **not** banked as the controlling fixed-log
estimate.  Instead the count is organised by conductor layers, which gives a bound that is
completely **independent of `τ(q)`**:

```
#Bad(q,D)  ≤  ∑_{r ≤ D} φ(r) + #Exceptional
           ≤  D(D+1)/2 + #Exceptional
           ≤  (D+1)²            (for a single exceptional character).
```

`φPrimitive(r) ≤ φ(r) ≤ r` is used exactly as stated: the per-layer count
(`hlayer`, the number of characters mod `q` of conductor `r`, i.e. the number of primitive
characters of modulus `r`) enters as an explicit hypothesis, so no primitive-character
counting theorem is silently assumed.

No asymptotic notation occurs in any statement below.  Everything is a finite inequality on
natural numbers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace Erdos287
namespace V21BadCount

/-! ## §1. The abstract conductor-layer count -/

variable {α : Type*} [DecidableEq α]

/-- **`badCharacter_card_le_sum_totient`.**  `LEAN_PROVED_FINITE`.

Layered count of the bad set: every bad element either has conductor at most `D` (and then
it lies in the layer of its conductor) or belongs to the exceptional set. -/
theorem badCharacter_card_le_sum_totient (Bad Exc : Finset α) (cond : α → ℕ) (D : ℕ)
    (hsplit : ∀ a ∈ Bad, cond a ≤ D ∨ a ∈ Exc)
    (hlayer : ∀ r ≤ D, (Bad.filter (fun a => cond a = r)).card ≤ Nat.totient r) :
    Bad.card ≤ (∑ r ∈ Finset.range (D + 1), Nat.totient r) + Exc.card := by
  classical
  set S : Finset α := Bad.filter (fun a => cond a ≤ D) with hS
  have hsub : Bad ⊆ S ∪ Exc := by
    intro a ha
    rcases hsplit a ha with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha, h⟩)
    · exact Finset.mem_union_right _ h
  have h1 : Bad.card ≤ S.card + Exc.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hfib : ∀ a ∈ S, cond a ∈ Finset.range (D + 1) := by
    intro a ha
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp ha).2)
  have h2 : S.card = ∑ r ∈ Finset.range (D + 1), (S.filter (fun a => cond a = r)).card :=
    Finset.card_eq_sum_card_fiberwise hfib
  have h3 : ∀ r ∈ Finset.range (D + 1),
      (S.filter (fun a => cond a = r)).card ≤ Nat.totient r := by
    intro r hr
    refine le_trans (Finset.card_le_card ?_) (hlayer r (Nat.lt_succ_iff.mp
      (Finset.mem_range.mp hr)))
    intro a ha
    have h' := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h'.1).1, h'.2⟩
  have h4 : S.card ≤ ∑ r ∈ Finset.range (D + 1), Nat.totient r := by
    rw [h2]; exact Finset.sum_le_sum h3
  omega

/-- Alias for the layered count, in the V22 naming convention. -/
theorem badCharacter_card_le_totientSum (Bad Exc : Finset α) (cond : α → ℕ) (D : ℕ)
    (hsplit : ∀ a ∈ Bad, cond a ≤ D ∨ a ∈ Exc)
    (hlayer : ∀ r ≤ D, (Bad.filter (fun a => cond a = r)).card ≤ Nat.totient r) :
    Bad.card ≤ (∑ r ∈ Finset.range (D + 1), Nat.totient r) + Exc.card :=
  badCharacter_card_le_sum_totient Bad Exc cond D hsplit hlayer

/-- The Gauss sum `∑_{r ≤ D} r`, doubled, in exact natural arithmetic. -/
theorem two_mul_sum_range_succ_id (D : ℕ) :
    2 * (∑ r ∈ Finset.range (D + 1), r) = D * (D + 1) := by
  induction D with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      ring

/-- **`badCharacter_card_le_triangular`.**  `LEAN_PROVED_FINITE`.

The triangular form, `φ(r) ≤ r` applied layer by layer:
`2·#Bad ≤ D(D+1) + 2·#Exceptional`, equivalently `#Bad ≤ D(D+1)/2 + #Exceptional`. -/
theorem badCharacter_card_le_triangular (Bad Exc : Finset α) (cond : α → ℕ) (D : ℕ)
    (hsplit : ∀ a ∈ Bad, cond a ≤ D ∨ a ∈ Exc)
    (hlayer : ∀ r ≤ D, (Bad.filter (fun a => cond a = r)).card ≤ Nat.totient r) :
    2 * Bad.card ≤ D * (D + 1) + 2 * Exc.card := by
  have h1 := badCharacter_card_le_sum_totient Bad Exc cond D hsplit hlayer
  have h2 : (∑ r ∈ Finset.range (D + 1), Nat.totient r) ≤ ∑ r ∈ Finset.range (D + 1), r :=
    Finset.sum_le_sum fun r _ => Nat.totient_le r
  have h3 := two_mul_sum_range_succ_id D
  omega

/-- The divided form of the triangular bound. -/
theorem badCharacter_card_le_triangular_div (Bad Exc : Finset α) (cond : α → ℕ) (D : ℕ)
    (hsplit : ∀ a ∈ Bad, cond a ≤ D ∨ a ∈ Exc)
    (hlayer : ∀ r ≤ D, (Bad.filter (fun a => cond a = r)).card ≤ Nat.totient r) :
    Bad.card ≤ D * (D + 1) / 2 + Exc.card := by
  have h := badCharacter_card_le_triangular Bad Exc cond D hsplit hlayer
  have h2 := two_mul_sum_range_succ_id D
  omega

/-- **`badCharacter_card_le_sq`.**  `LEAN_PROVED_FINITE`.

The coarse safe consequence used by the log ledger: with at most one exceptional
character, `#Bad(q,D) ≤ (D+1)²`.  Nothing here depends on `τ(q)`. -/
theorem badCharacter_card_le_sq (Bad Exc : Finset α) (cond : α → ℕ) (D : ℕ)
    (hsplit : ∀ a ∈ Bad, cond a ≤ D ∨ a ∈ Exc)
    (hlayer : ∀ r ≤ D, (Bad.filter (fun a => cond a = r)).card ≤ Nat.totient r)
    (hexc : Exc.card ≤ 1) :
    Bad.card ≤ (D + 1) ^ 2 := by
  have h := badCharacter_card_le_triangular Bad Exc cond D hsplit hlayer
  have hsq : (D + 1) ^ 2 = D * D + 2 * D + 1 := by ring
  nlinarith [h, hexc, hsq, Nat.zero_le D]

/-! ## §2. The Dirichlet-character instance -/

open scoped Classical

/-- The bad set at modulus `q` and cutoff `D`: the low-conductor characters together with
the (convention-correct) exceptional set. -/
noncomputable def badSet (q D : ℕ) (Exc : Finset (DirichletCharacter ℂ q)) :
    Finset (DirichletCharacter ℂ q) :=
  (Finset.univ.filter (fun chi : DirichletCharacter ℂ q => chi.conductor ≤ D)) ∪ Exc

/-- With no exceptional character the complement of the bad set is exactly the V20 high
set: the two banks describe the *same* ambient splitting. -/
theorem highSetOf_badSet_eq_highSet (q D : ℕ) :
    Erdos287.V21TwoProj.highSetOf (badSet q D ∅) = Erdos287.CharGram3221.highSet q D := by
  ext chi
  simp [Erdos287.V21TwoProj.highSetOf, badSet, Erdos287.CharGram3221.highSet]

/-- **`dirichletBad_card_le_sq`.**  `LEAN_PROVED_FINITE`.

The safe `(D+1)²` count for the literal Dirichlet bad set, given the per-layer
primitive-character count as an explicit hypothesis and at most one exceptional
character. -/
theorem dirichletBad_card_le_sq (q D : ℕ) (Exc : Finset (DirichletCharacter ℂ q))
    (hlayer : ∀ r ≤ D,
      ((badSet q D Exc).filter (fun chi => chi.conductor = r)).card ≤ Nat.totient r)
    (hexc : Exc.card ≤ 1) :
    (badSet q D Exc).card ≤ (D + 1) ^ 2 := by
  refine badCharacter_card_le_sq (badSet q D Exc) Exc
    (fun chi : DirichletCharacter ℂ q => chi.conductor) D ?_ hlayer hexc
  intro chi hchi
  rcases Finset.mem_union.mp hchi with h | h
  · exact Or.inl (Finset.mem_filter.mp h).2
  · exact Or.inr h

end V21BadCount
end Erdos287
