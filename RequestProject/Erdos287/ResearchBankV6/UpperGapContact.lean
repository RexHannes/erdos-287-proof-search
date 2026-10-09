import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V6: the upper-gap contact relation (kernel)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The upper-gap contact relation records neighbouring physical denominators `|p j − q ℓ| = 1`, and
contacts with the frozen core/top trace.  Everything here is exact finite combinatorics:
symmetry, coprimality, the two-element contact fibre, injectivity of the partner cofactor for
rows of prime `≥ 3`, and the resulting counting bound.

**No sparsity is asserted beyond what is proved.**  `contact_bound_sharp` exhibits a position with
exactly two contacts, so the bound `≤ 2` per position is optimal and no stronger per-position
statement is available; `contact_count_not_globally_sparse` records that a per-position bound is
not a global sparsity statement.
-/

namespace Erdos287
namespace ResearchBankV6
namespace UpperGap

open Finset

/-! ## 1.  The contact relation -/

/-- Two physical positions are *in contact* when they differ by exactly one. -/
def Contact (x y : ℕ) : Prop := x + 1 = y ∨ y + 1 = x

instance (x y : ℕ) : Decidable (Contact x y) := by unfold Contact; infer_instance

/-- Contact of a `p`-row entry `p j` with a `q`-row entry `q ℓ`: `|p j − q ℓ| = 1`. -/
def RowContact (p j q l : ℕ) : Prop := Contact (p * j) (q * l)

theorem contact_symm {x y : ℕ} (h : Contact x y) : Contact y x := h.symm

theorem contact_comm {x y : ℕ} : Contact x y ↔ Contact y x := ⟨contact_symm, contact_symm⟩

theorem contact_ne {x y : ℕ} (h : Contact x y) : x ≠ y := by
  rcases h with h | h <;> omega

/-- Positions in contact are coprime. -/
theorem contact_coprime {x y : ℕ} (h : Contact x y) : Nat.Coprime x y := by
  rcases h with h | h
  · subst h; simp [Nat.Coprime]
  · subst h; simp [Nat.coprime_comm]

/-- Two rows in contact have distinct primes. -/
theorem rowContact_prime_ne {p q j l : ℕ} (hp : p.Prime)
    (h : RowContact p j q l) : p ≠ q := by
  intro hpq
  subst hpq
  have hcop : Nat.Coprime (p * j) (p * l) := contact_coprime h
  have hdvd : p ∣ Nat.gcd (p * j) (p * l) := Nat.dvd_gcd ⟨j, rfl⟩ ⟨l, rfl⟩
  rw [hcop] at hdvd
  exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.1 hdvd)

/-! ## 2.  The contact fibre -/

/-- The contact fibre of a position `x` inside the window `[1, M]`. -/
def contactFibre (M x : ℕ) : Finset ℕ := (Finset.Icc 1 M).filter (fun y => Contact x y)

/-- The contact fibre is contained in `{x − 1, x + 1}`. -/
theorem contactFibre_subset (M x : ℕ) : contactFibre M x ⊆ {x - 1, x + 1} := by
  intro y hy
  rw [contactFibre, Finset.mem_filter] at hy
  rcases hy.2 with h | h
  · simp [← h]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    left; omega

/-- **Exact contact counting.**  Every position has at most two contacts. -/
theorem contactFibre_card_le (M x : ℕ) : (contactFibre M x).card ≤ 2 := by
  refine le_trans (Finset.card_le_card (contactFibre_subset M x)) ?_
  exact le_trans (Finset.card_insert_le _ _) (by simp)

/-- The bound `≤ 2` is attained, hence optimal: no stronger per-position contact bound holds. -/
theorem contact_bound_sharp : (contactFibre 10 5).card = 2 := by decide

/-- **Firewall.**  A per-position contact bound is not a global sparsity statement: the total
number of contact pairs in a window can be as large as the window itself. -/
theorem contact_count_not_globally_sparse (M : ℕ) (hM : 2 ≤ M) :
    2 ≤ ∑ x ∈ Finset.Icc 1 M, (contactFibre M x).card := by
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 M := Finset.mem_Icc.2 ⟨le_refl 1, by omega⟩
  have h2 : (2 : ℕ) ∈ Finset.Icc 1 M := Finset.mem_Icc.2 ⟨by omega, hM⟩
  have key : ∀ x ∈ ({1, 2} : Finset ℕ), 1 ≤ (contactFibre M x).card := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · refine Finset.card_pos.2 ⟨2, ?_⟩
      rw [contactFibre, Finset.mem_filter]
      exact ⟨h2, Or.inl rfl⟩
    · refine Finset.card_pos.2 ⟨1, ?_⟩
      rw [contactFibre, Finset.mem_filter]
      exact ⟨h1, Or.inr rfl⟩
  have hsub : ({1, 2} : Finset ℕ) ⊆ Finset.Icc 1 M := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h1
    · exact h2
  calc (2 : ℕ) = ∑ _x ∈ ({1, 2} : Finset ℕ), 1 := by decide
    _ ≤ ∑ x ∈ ({1, 2} : Finset ℕ), (contactFibre M x).card := Finset.sum_le_sum key
    _ ≤ ∑ x ∈ Finset.Icc 1 M, (contactFibre M x).card :=
        Finset.sum_le_sum_of_subset hsub

/-! ## 3.  Injectivity of the partner cofactor -/

/-- **Partner injectivity.**  For a fixed position `x` and a fixed row prime `q ≥ 3`, at most one
cofactor `ℓ` puts `q ℓ` in contact with `x`. -/
theorem contact_partner_unique {x q l₁ l₂ : ℕ} (hq : 3 ≤ q)
    (h₁ : Contact x (q * l₁)) (h₂ : Contact x (q * l₂)) : l₁ = l₂ := by
  have hq0 : 0 < q := by omega
  have key : q * l₁ + 2 = q * l₂ ∨ q * l₂ + 2 = q * l₁ ∨ q * l₁ = q * l₂ := by
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> omega
  have main : ∀ a b : ℕ, q * a + 2 = q * b → False := by
    intro a b h
    have hlt : a < b := by
      by_contra hc
      have : q * b ≤ q * a := Nat.mul_le_mul_left _ (by omega)
      omega
    have h2 : q * (b - a) = 2 := by rw [Nat.mul_sub_left_distrib]; omega
    have := Nat.le_of_dvd (by norm_num) (⟨b - a, h2.symm⟩ : q ∣ 2)
    omega
  rcases key with h | h | h
  · exact (main _ _ h).elim
  · exact (main _ _ h).elim
  · exact Nat.eq_of_mul_eq_mul_left hq0 h

/-- The same statement for two rows: at fixed `p, j` and fixed `q ≥ 3`, the contacting cofactor of
the `q`-row is unique. -/
theorem rowContact_partner_unique {p j q l₁ l₂ : ℕ} (hq : 3 ≤ q)
    (h₁ : RowContact p j q l₁) (h₂ : RowContact p j q l₂) : l₁ = l₂ :=
  contact_partner_unique hq h₁ h₂

/-! ## 4.  Contacts with the frozen core/top trace -/

/-- The set of frozen-trace positions contacted by `x`. -/
def traceContacts (F : Finset ℕ) (x : ℕ) : Finset ℕ := F.filter (fun y => Contact x y)

/-- Contacts with the frozen trace are also at most two per position. -/
theorem traceContacts_card_le (F : Finset ℕ) (x : ℕ) : (traceContacts F x).card ≤ 2 := by
  have hsub : traceContacts F x ⊆ {x - 1, x + 1} := by
    intro y hy
    rw [traceContacts, Finset.mem_filter] at hy
    rcases hy.2 with h | h
    · simp [← h]
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      left; omega
  refine le_trans (Finset.card_le_card hsub) ?_
  exact le_trans (Finset.card_insert_le _ _) (by simp)

/-- Contact with the frozen trace is symmetric in the two endpoints. -/
theorem traceContacts_symm {F : Finset ℕ} {x y : ℕ} (hy : y ∈ traceContacts F x) :
    Contact y x := contact_symm (Finset.mem_filter.1 hy).2

end UpperGap
end ResearchBankV6
end Erdos287
