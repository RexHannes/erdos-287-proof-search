import RequestProject.Erdos287.ResearchBankV7.ErasureHit

/-!
# Erdős #287 — Research Bank V7: the guarded branch-to-HIT theorem (conditional, exact)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Exact rational theorem with an explicit hypothesis package.  Its inputs are

* a **genuine complete ENTRY reference word** `x₀`, represented by its actual selected support
  `T` (all denominators dividing the final modulus `J`) — never by a seed;
* a valid spine `𝒫 ⊆ T` with a certified reachable `J`-lattice interval `[A, B]`;
* compatible guards `G ⊆ T` (fixed ones) and a protected neutral set `Nprot ⊆ T`, both disjoint
  from the spine;
* an explicit zero budget `z`, with `|𝒫| ≤ z`;
* exact lower/upper mass margins `A ≤ w ≤ B` for the **actual deficit**
  `w = J·(S(x₀) − 1) = (∑_{n ∈ T} J/n) − J`.

Conclusion (`guarded_branch_to_hit`): the deficit is hit by an actual subset `S ⊆ 𝒫` of the
spine, so deleting `S` from the same physical branch — touching neither a guard nor a protected
neutral coordinate, and staying inside the zero budget — yields exactly `S = 1`.

Firewalls, machine-checked:

* `guarded_hit_does_not_give_entry_word` — the theorem does **not** produce a compatible ENTRY
  reference word;
* `guard_failure_does_not_kill_unguarded_branches` — failure of one fixed guarded construction
  does **not** refute unguarded ENTRY branches;
* `seed_mass_is_not_reference_mass` — a concrete counterfixture forbidding the substitution of the
  seed mass for `S(x₀)`.
-/

namespace Erdos287
namespace ResearchBankV7
namespace GuardedBranchHit

open Finset IntervalLifting

/-- The integer numerator weight of the denominator `n` at final modulus `J`. -/
def num (J n : ℕ) : ℤ := ((J / n : ℕ) : ℤ)

/-- For `n ∣ J` with `0 < n`, the numerator weight is the exact rational `J/n`. -/
theorem num_cast {J n : ℕ} (hn : 0 < n) (hdvd : n ∣ J) :
    ((num J n : ℤ) : ℚ) = (J : ℚ) / n := by
  have hn' : (n : ℚ) ≠ 0 := by positivity
  rw [num, Int.cast_natCast, Nat.cast_div hdvd hn']

/-- Exact conversion between rational subset mass and integer subset weight. -/
theorem mass_eq_weight_div {J : ℕ} (hJ : 0 < J) {S : Finset ℕ}
    (hS : ∀ n ∈ S, 0 < n ∧ n ∣ J) :
    ∑ n ∈ S, (1 : ℚ) / n = (∑ n ∈ S, (num J n : ℚ)) / J := by
  have hJ' : (J : ℚ) ≠ 0 := by positivity
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro n hn
  obtain ⟨hn0, hnd⟩ := hS n hn
  have hn' : (n : ℚ) ≠ 0 := by positivity
  rw [num_cast hn0 hnd]
  field_simp

/-- The complete hypothesis package of the guarded branch-to-HIT theorem. -/
structure GuardedBranch where
  /-- The final modulus. -/
  J : ℕ
  /-- Positivity of the final modulus. -/
  J_pos : 0 < J
  /-- The actual selected support of the complete ENTRY reference word `x₀`. -/
  T : Finset ℕ
  /-- Every selected denominator is positive and divides `J`. -/
  T_ok : ∀ n ∈ T, 0 < n ∧ n ∣ J
  /-- The certified spine. -/
  P : Finset ℕ
  /-- The spine is part of the reference word's support. -/
  P_sub : P ⊆ T
  /-- The fixed-one guards. -/
  G : Finset ℕ
  /-- The protected neutral coordinates. -/
  Nprot : Finset ℕ
  /-- Guards are compatible with the spine: they are never deleted. -/
  G_disj : Disjoint P G
  /-- Protected neutral coordinates are never deleted. -/
  N_disj : Disjoint P Nprot
  /-- The explicit zero budget. -/
  zeroBudget : ℕ
  /-- The spine fits the zero budget. -/
  budget_ok : P.card ≤ zeroBudget
  /-- Lattice step of the certified interval. -/
  g : ℤ
  /-- Lower endpoint of the certified interval. -/
  A : ℤ
  /-- Upper endpoint of the certified interval. -/
  B : ℤ
  /-- The certified reachable interval of the spine. -/
  cert : ReachesLattice (num J) P g A B
  /-- The deficit is a lattice point. -/
  deficit_lattice : g ∣ (∑ n ∈ T, num J n) - J
  /-- Exact lower mass margin. -/
  margin_lo : A ≤ (∑ n ∈ T, num J n) - J
  /-- Exact upper mass margin. -/
  margin_hi : (∑ n ∈ T, num J n) - J ≤ B

namespace GuardedBranch

variable (b : GuardedBranch)

/-- The actual mass `S(x₀)` of the complete ENTRY reference word. -/
def refMass : ℚ := ∑ n ∈ b.T, (1 : ℚ) / n

/-- The actual deficit `w = J·(S(x₀) − 1)`, as an integer. -/
def deficit : ℤ := (∑ n ∈ b.T, num b.J n) - b.J

/-- **The deficit really is `J·(S(x₀) − 1)`** — computed from the complete reference-word mass,
never from a seed mass. -/
theorem deficit_eq : (b.deficit : ℚ) = b.J * (b.refMass - 1) := by
  have hJ' : (b.J : ℚ) ≠ 0 := by
    have := b.J_pos; positivity
  have h := mass_eq_weight_div b.J_pos (S := b.T) b.T_ok
  rw [deficit, refMass]
  push_cast
  rw [h]
  field_simp

/-- **Guarded branch-to-HIT (conditional, exact).**  Under the stated hypothesis package the
actual deficit lies in the certified reachable `J`-lattice interval, hence there is an actual
subset `S` of the spine — within the zero budget, disjoint from the guards and from the protected
neutral set — whose deletion turns the same physical branch into an exact solution `S = 1`. -/
theorem guarded_branch_to_hit :
    ∃ S ⊆ b.P, S.card ≤ b.zeroBudget ∧ Disjoint S b.G ∧ Disjoint S b.Nprot ∧
      ∑ n ∈ b.T \ S, (1 : ℚ) / n = 1 := by
  classical
  obtain ⟨S, hSP, hsum⟩ :=
    b.cert b.deficit b.deficit_lattice b.margin_lo b.margin_hi
  refine ⟨S, hSP, le_trans (Finset.card_le_card hSP) b.budget_ok,
    Finset.disjoint_of_subset_left hSP b.G_disj,
    Finset.disjoint_of_subset_left hSP b.N_disj, ?_⟩
  have hST : S ⊆ b.T := hSP.trans b.P_sub
  have hJ' : (b.J : ℚ) ≠ 0 := by have := b.J_pos; positivity
  have hmass : ∑ n ∈ b.T \ S, (1 : ℚ) / n = (∑ n ∈ b.T \ S, (num b.J n : ℚ)) / b.J :=
    mass_eq_weight_div b.J_pos (fun n hn => b.T_ok n (Finset.mem_sdiff.1 hn).1)
  have hsub : ∑ n ∈ b.T \ S, (num b.J n : ℤ) = (∑ n ∈ b.T, num b.J n) - ∑ n ∈ S, num b.J n :=
    Finset.sum_sdiff_eq_sub hST
  have hval : ∑ n ∈ b.T \ S, (num b.J n : ℤ) = b.J := by
    rw [hsub, hsum, deficit]; ring
  rw [hmass]
  have : (∑ n ∈ b.T \ S, (num b.J n : ℚ)) = (b.J : ℚ) := by
    rw [← Int.cast_sum, hval]; push_cast; ring
  rw [this]
  field_simp

/-- The modified branch keeps every guard and every protected neutral coordinate. -/
theorem guards_preserved :
    ∃ S ⊆ b.P, (b.G ∩ b.T) ⊆ b.T \ S ∧ (b.Nprot ∩ b.T) ⊆ b.T \ S ∧
      ∑ n ∈ b.T \ S, (1 : ℚ) / n = 1 := by
  classical
  obtain ⟨S, hSP, _, hG, hN, hmass⟩ := b.guarded_branch_to_hit
  refine ⟨S, hSP, ?_, ?_, hmass⟩
  · intro n hn
    obtain ⟨hnG, hnT⟩ := Finset.mem_inter.1 hn
    exact Finset.mem_sdiff.2 ⟨hnT, fun hnS => (Finset.disjoint_left.1 hG hnS) hnG⟩
  · intro n hn
    obtain ⟨hnN, hnT⟩ := Finset.mem_inter.1 hn
    exact Finset.mem_sdiff.2 ⟨hnT, fun hnS => (Finset.disjoint_left.1 hN hnS) hnN⟩

end GuardedBranch

/-! ## Firewalls -/

/-- **Firewall.**  The guarded theorem is an implication about a *supplied* hypothesis package; it
does not produce a compatible ENTRY reference word. -/
theorem guarded_hit_does_not_give_entry_word :
    ¬ ∀ (H C : GuardedBranch → Prop), (∀ b, H b → C b) → ∃ b, H b := by
  intro h
  obtain ⟨b, hb⟩ := h (fun _ => False) (fun _ => True) (fun _ h => h.elim)
  exact hb

/-- **Firewall.**  Failure of one fixed guarded construction does not imply that no unguarded
ENTRY branch exists: from `¬P` and `P → Q` nothing follows about `Q`. -/
theorem guard_failure_does_not_kill_unguarded_branches :
    ¬ ∀ P Q : Prop, (P → Q) → ¬ P → ¬ Q := by
  intro h
  exact h False True (fun x => x.elim) not_false trivial

/-- **Counterfixture.**  The deficit must be computed from the *complete* reference-word mass.
Substituting the mass of a seed sub-word changes it: for `T = {2,3}` and seed `{2}` the masses
`5/6` and `1/2` differ. -/
theorem seed_mass_is_not_reference_mass :
    ∑ n ∈ ({2, 3} : Finset ℕ), (1 : ℚ) / n ≠ ∑ n ∈ ({2} : Finset ℕ), (1 : ℚ) / n := by
  norm_num

end GuardedBranchHit
end ResearchBankV7
end Erdos287
