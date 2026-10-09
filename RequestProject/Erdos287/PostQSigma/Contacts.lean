import Mathlib

/-!
# Erdős #287 — post-`Q_Σ` bank, §16–17: contacts, owner graph, owner-disjoint matching

**Status.**
* Definitions, the inclusion–exclusion reduction, the owner-degree bound, the greedy matching
  lemma and the distinct-row activation consequence: **BANK (proved in Lean)**.
* The every-`M` contact supply (`> M/5` contacts at threshold `M^{51/100}`, `> M/100` at
  `M^{3/5}`, for `M ≥ 2^1500`) needs explicit prime-counting estimates that are not formalised
  locally; it is isolated as the named proposition `ContactSupply` (**PAPER-LEVEL / EXTERNAL
  INPUT**, never asserted).

Definitions: `Pplus n` is the largest prime factor (`0` for `n ≤ 1`); the contact interval is
`I_M = [⌈46M/125⌉, M-1]`; `n` is a contact at exponent `θ = u/v` if `P⁺(n)^v > M^u` and
`P⁺(n+1)^v > M^u` (integer-safe form of `P⁺ > M^θ`).
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

/-- Largest prime factor (`0` for `n ≤ 1`). -/
def Pplus (n : ℕ) : ℕ := n.primeFactors.sup id

lemma Pplus_dvd {n : ℕ} (hn : 2 ≤ Pplus n) : Pplus n ∣ n := by
  have hne : n.primeFactors.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [Pplus, h] at hn
  obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup _ hne id
  rw [Pplus, hpe]
  exact Nat.dvd_of_mem_primeFactors hp

/-- The contact interval `I_M = [⌈46M/125⌉, M-1]`. -/
def contactInterval (M : ℕ) : Finset ℕ := Finset.Icc ((46 * M + 124) / 125) (M - 1)

/-- `P⁺(n)^v > M^u` (integer-safe `P⁺(n) > M^{u/v}`). -/
def Large (M u v n : ℕ) : Prop := M ^ u < (Pplus n) ^ v

open Classical in
/-- The contacts of `I_M` at exponent `u/v`. -/
noncomputable def contacts (M u v : ℕ) : Finset ℕ :=
  (contactInterval M).filter (fun n => Large M u v n ∧ Large M u v (n + 1))

open Classical in
/-- **Inclusion–exclusion reduction**:
`#contacts ≥ |I_M| - #{n : ¬ large n} - #{n : ¬ large (n+1)}`. -/
theorem contacts_card_ge (M u v : ℕ) :
    (contactInterval M).card ≤ (contacts M u v).card +
      ((contactInterval M).filter (fun n => ¬ Large M u v n)).card +
      ((contactInterval M).filter (fun n => ¬ Large M u v (n + 1))).card := by
  classical
  have h : contactInterval M ⊆ contacts M u v ∪
      (contactInterval M).filter (fun n => ¬ Large M u v n) ∪
      (contactInterval M).filter (fun n => ¬ Large M u v (n + 1)) := by
    intro n hn
    simp only [contacts, Finset.mem_union, Finset.mem_filter]
    by_cases h1 : Large M u v n <;> by_cases h2 : Large M u v (n + 1) <;> tauto
  exact (Finset.card_le_card h).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))

/-- **Every-`M` contact supply (PAPER-LEVEL; NOT asserted).**  For `M ≥ 2^1500`:
more than `M/5` contacts at exponent `51/100` and more than `M/100` at exponent `3/5`. -/
def ContactSupply : Prop :=
  ∀ M : ℕ, 2 ^ 1500 ≤ M → M < 5 * (contacts M 51 100).card ∧ M < 100 * (contacts M 3 5).card

/-! ## Greedy matching in a multigraph of bounded degree -/

/-- Two edges are vertex-disjoint. -/
def VDisj {ι V : Type*} (u v : ι → V) (c c' : ι) : Prop :=
  u c ≠ u c' ∧ u c ≠ v c' ∧ v c ≠ u c' ∧ v c ≠ v c'

/-- **Greedy matching lemma**: if every vertex lies on at most `Δ` edges of `C`, there is a
vertex-disjoint subfamily `F ⊆ C` with `|C| ≤ 2Δ |F|`. -/
theorem greedy_matching {ι V : Type*} [DecidableEq ι] [DecidableEq V] (u v : ι → V) (Δ : ℕ) :
    ∀ C : Finset ι, (∀ w : V, (C.filter (fun c => u c = w ∨ v c = w)).card ≤ Δ) →
      ∃ F ⊆ C, (∀ c ∈ F, ∀ c' ∈ F, c ≠ c' → VDisj u v c c') ∧ C.card ≤ 2 * Δ * F.card := by
  intro C
  induction C using Finset.strongInduction with
  | H C ih =>
    intro hdeg
    rcases C.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
    · exact ⟨∅, by simp, by simp, by simp⟩
    set N := C.filter (fun c' => (u c' = u c ∨ v c' = u c) ∨ (u c' = v c ∨ v c' = v c)) with hN
    have hNcard : N.card ≤ 2 * Δ := by
      rw [hN, Finset.filter_or]
      refine (Finset.card_union_le _ _).trans ?_
      have := hdeg (u c); have := hdeg (v c); omega
    have hcN : c ∈ N := by simp [hN, hc]
    have hsub : C \ N ⊂ C := Finset.sdiff_ssubset (Finset.filter_subset _ _) ⟨c, hcN⟩
    obtain ⟨F', hF'sub, hF'disj, hF'card⟩ := ih (C \ N) hsub (fun w =>
      (Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)).trans (hdeg w))
    have hcF' : c ∉ F' := fun h => (Finset.mem_sdiff.1 (hF'sub h)).2 hcN
    refine ⟨insert c F', Finset.insert_subset hc (hF'sub.trans Finset.sdiff_subset), ?_, ?_⟩
    · have hfar : ∀ c' ∈ F', VDisj u v c c' := by
        intro c' hc'
        have := (Finset.mem_sdiff.1 (hF'sub hc')).2
        simp only [hN, Finset.mem_filter, not_and, not_or] at this
        have h' := this (Finset.mem_sdiff.1 (hF'sub hc')).1
        exact ⟨fun e => h'.1.1 e.symm, fun e => h'.1.2 e.symm, fun e => h'.2.1 e.symm,
          fun e => h'.2.2 e.symm⟩
      intro x hx y hy hxy
      by_cases hxc : x = c <;> by_cases hyc : y = c
      · exact absurd (hxc.trans hyc.symm) hxy
      · rw [hxc]
        exact hfar y ((Finset.mem_insert.1 hy).resolve_left hyc)
      · rw [hyc]
        obtain ⟨h1, h2, h3, h4⟩ := hfar x ((Finset.mem_insert.1 hx).resolve_left hxc)
        exact ⟨fun e => h1 e.symm, fun e => h3 e.symm, fun e => h2 e.symm, fun e => h4 e.symm⟩
      · exact hF'disj x ((Finset.mem_insert.1 hx).resolve_left hxc) y
          ((Finset.mem_insert.1 hy).resolve_left hyc) hxy
    · have hC : C.card = (C \ N).card + N.card := by
        rw [Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)]
      rw [Finset.card_insert_of_notMem hcF', hC]
      nlinarith

/-! ## Owner-degree bound and owner-disjoint matching of contacts -/

/-- Number of multiples of `w` in `[1, M]` is `M / w`. -/
lemma card_multiples (M w : ℕ) : ((Finset.Icc 1 M).filter (fun n => w ∣ n)).card = M / w := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div M w]
  congr 1

/-- **Owner degree**: an owner `w` lies on at most `2 ⌊M/w⌋` contacts of `[1, M-1]`. -/
theorem owner_degree_le (M w : ℕ) (C : Finset ℕ)
    (hC : ∀ n ∈ C, 1 ≤ n ∧ n + 1 ≤ M ∧ 2 ≤ Pplus n ∧ 2 ≤ Pplus (n + 1)) :
    (C.filter (fun n => Pplus n = w ∨ Pplus (n + 1) = w)).card ≤ 2 * (M / w) := by
  classical
  rw [Finset.filter_or]
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : (C.filter (fun n => Pplus n = w)).card ≤ M / w := by
    rw [← card_multiples]
    apply Finset.card_le_card
    intro n hn
    obtain ⟨hnC, hnw⟩ := Finset.mem_filter.1 hn
    obtain ⟨h1, h2, h3, -⟩ := hC n hnC
    exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨h1, by omega⟩, hnw ▸ Pplus_dvd h3⟩
  have h2 : (C.filter (fun n => Pplus (n + 1) = w)).card ≤ M / w := by
    rw [← card_multiples]
    refine Finset.card_le_card_of_injOn (fun n => n + 1) ?_ (fun x _ y _ h => by simpa using h)
    intro n hn
    obtain ⟨hnC, hnw⟩ := Finset.mem_filter.1 hn
    obtain ⟨h1, h2, -, h4⟩ := hC n hnC
    exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, h2⟩, hnw ▸ Pplus_dvd h4⟩
  omega

/-- `w^5 > M^3` ⇒ `⌊M/w⌋^5 < M^2` (so the owner degree is `< 2 M^{2/5}`). -/
theorem div_pow_five_lt {M w : ℕ} (hw : M ^ 3 < w ^ 5) (hM : 0 < M) : (M / w) ^ 5 < M ^ 2 := by
  have hw0 : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h | h
    · rw [h] at hw; simp at hw
    · exact h
  have h1 : (M / w) * w ≤ M := Nat.div_mul_le_self M w
  have h2 : (M / w) ^ 5 * w ^ 5 ≤ M ^ 5 := by rw [← mul_pow]; exact Nat.pow_le_pow_left h1 5
  by_contra hc; push_neg at hc
  have : M ^ 2 * M ^ 3 < M ^ 2 * w ^ 5 := Nat.mul_lt_mul_of_pos_left hw (by positivity)
  have : M ^ 2 * w ^ 5 ≤ (M / w) ^ 5 * w ^ 5 := Nat.mul_le_mul_right _ hc
  have : M ^ 5 = M ^ 2 * M ^ 3 := by ring
  omega

/-- **Owner-disjoint contact matching.**  If every contact of `C ⊆ [1, M-1]` has both owners
`≥ 2` with `⌊M/owner⌋ ≤ D`, there is an owner-disjoint subfamily `F ⊆ C` with
`|C| ≤ 4 D |F|`.  With `100|C| > M` this gives `M < 400 D |F|` (and `D^5 < M^2` at exponent
`3/5` by `div_pow_five_lt`, i.e. `|F| > M^{3/5}/400`). -/
theorem contact_matching (M D : ℕ) (C : Finset ℕ)
    (hC : ∀ n ∈ C, 1 ≤ n ∧ n + 1 ≤ M ∧ 2 ≤ Pplus n ∧ 2 ≤ Pplus (n + 1))
    (hD : ∀ n ∈ C, M / Pplus n ≤ D ∧ M / Pplus (n + 1) ≤ D) :
    ∃ F ⊆ C, (∀ c ∈ F, ∀ c' ∈ F, c ≠ c' → VDisj Pplus (fun n => Pplus (n + 1)) c c') ∧
      C.card ≤ 4 * D * F.card := by
  classical
  obtain ⟨F, hF, hdisj, hcard⟩ := greedy_matching Pplus (fun n => Pplus (n + 1)) (2 * D) C
    (fun w => by
      by_cases hex : ∃ n ∈ C, Pplus n = w ∨ Pplus (n + 1) = w
      · obtain ⟨n, hn, hnw⟩ := hex
        have hw : 2 ≤ w := by
          obtain ⟨-, -, h3, h4⟩ := hC n hn
          rcases hnw with h | h <;> omega
        refine (owner_degree_le M w C hC).trans ?_
        rcases hnw with h | h
        · have := (hD n hn).1; rw [h] at this; omega
        · have := (hD n hn).2; rw [h] at this; omega
      · push_neg at hex
        have : (C.filter (fun n => Pplus n = w ∨ Pplus (n + 1) = w)) = ∅ :=
          Finset.filter_false_of_mem (fun n hn h => by
            rcases h with h | h
            · exact (hex n hn).1 h
            · exact (hex n hn).2 h)
        rw [this]; simp)
  exact ⟨F, hF, hdisj, by nlinarith⟩

/-- **Distinct-row activation.**  In an owner-disjoint matching `F`, a defect-free selected set
`A` (every `n ∈ F` has `n ∈ A` or `n+1 ∈ A`) activates `|F|` *distinct* owner rows: there is a
set `O` of owners with `|O| = |F|`, each `w ∈ O` dividing some selected denominator. -/
theorem distinct_rows_activated (A F : Finset ℕ)
    (hF : ∀ n ∈ F, 2 ≤ Pplus n ∧ 2 ≤ Pplus (n + 1))
    (hdisj : ∀ c ∈ F, ∀ c' ∈ F, c ≠ c' → VDisj Pplus (fun n => Pplus (n + 1)) c c')
    (hdef : ∀ n ∈ F, n ∈ A ∨ n + 1 ∈ A) :
    ∃ O : Finset ℕ, O.card = F.card ∧ ∀ w ∈ O, ∃ m ∈ A, w ∣ m := by
  classical
  let f : ℕ → ℕ := fun n => if n ∈ A then Pplus n else Pplus (n + 1)
  refine ⟨F.image f, ?_, ?_⟩
  · apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    by_contra hne
    have hd := hdisj x hx y hy hne
    simp only [f] at hxy
    split_ifs at hxy
    · exact hd.1 hxy
    · exact hd.2.1 hxy
    · exact hd.2.2.1 hxy
    · exact hd.2.2.2 hxy
  · intro w hw
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hw
    simp only [f]
    split_ifs with h
    · exact ⟨n, h, Pplus_dvd (hF n hn).1⟩
    · exact ⟨n + 1, (hdef n hn).resolve_left h, Pplus_dvd (hF n hn).2⟩

end Erdos287.PostQSigma
