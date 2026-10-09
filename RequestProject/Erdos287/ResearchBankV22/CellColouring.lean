import RequestProject.Erdos287.ResearchBankV22.CompletedPositiveWeight
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Erdős #287 — Research Bank V22 §7: exact cell colouring

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This REPLACES the invalid literal cell-indicator convolution.

Setting: a finite prime universe `α` (a `Fintype`), a rough sub-universe `Ur`, logarithmic
cells `cell : α → J`, and a three-bin allocation `kbin : Fin 3 → J → ℕ` (`k_j = Σ_i k_{j,i}`).
Every prime is coloured independently and uniformly with one of 3 colours: the colourings are
`ω : α → Fin 3` with the uniform probability `3^{-|α|}` (total mass one, `colouring_mass_one`).

* `G cell Ur kbin i ω B = 1` iff `B ⊆ Ur`, every atom of `B` has colour `i`, and cell `j`
  contains exactly `k_{j,i}` atoms of `B` — a `{0,1}`-valued, one-bounded weight
  (`G_zero_or_one`, `G_oneBounded`);
* `colourConv ω = G_0 ⋆ (G_1 ⋆ G_2)`;
* `pat A ω j i` = number of atoms of `A` in cell `j` with colour `i`.

Kernel-proved (LEAN BANK):
* `conv_collapse` — for weights on DISJOINT universes the convolution has at most one nonzero
  term: `(f ⋆ g)(A) = f(A ∩ U₁) g(A ∩ U₂)` (so no prime is double counted and no `p²` is
  created);
* **`colourConv_eq`** — `(G_0 ⋆ G_1 ⋆ G_2)(A) = 1(A ⊆ Ur ∧ pat A ω = k)` — `{0,1}`-valued;
* **`card_pattern`** — the number of colourings with pattern `κ` is
  `3^{|α|} · π(A, κ)` with the explicit multinomial probability
  `π = ∏_j [k_j! / (k_{j,0}! k_{j,1}! k_{j,2}!)] 3^{-k_j}` (induction on `A`, multinomial
  Pascal rule `pascal3`);
* **`exact_colouring_identity`** —
  `1(specified squarefree cell pattern of A) = π^{-1} · E_ω[(G_0 ⋆ G_1 ⋆ G_2)(A)]`;
* **`piProb_inv_le`** — `π^{-1} ≤ 3^R` whenever `Σ_j k_j ≤ R`.

The expectation is a FINITE average of total mass one; the number `3^{|α|}` of colourings
never appears as a multiplicative cost.
-/

namespace Erdos287
namespace ResearchBankV22
namespace CellColouring

open Finset RoundedRoughSieve CompletedPositiveWeight

/-! ### Collapse of convolutions on disjoint universes -/

section Collapse

variable {γ : Type*} [DecidableEq γ]

/-- **Collapse**: on disjoint universes the convolution has at most one nonzero term. -/
theorem conv_collapse {f g : Finset γ → ℝ} {U1 U2 : Finset γ} (hf : SupportedIn f U1)
    (hg : SupportedIn g U2) (hd : Disjoint U1 U2) (A : Finset γ) :
    conv f g A = if A ⊆ U1 ∪ U2 then f (A ∩ U1) * g (A ∩ U2) else 0 := by
  unfold conv
  split_ifs with hA
  · rw [sum_eq_single (A ∩ U1)]
    · congr 2
      ext p; simp only [mem_sdiff, mem_inter]
      constructor
      · rintro ⟨hp, hn⟩
        rcases mem_union.1 (hA hp) with h | h
        · exact absurd ⟨hp, h⟩ hn
        · exact ⟨hp, h⟩
      · rintro ⟨hp, h⟩; exact ⟨hp, fun ⟨_, h'⟩ => disjoint_left.1 hd h' h⟩
    · intro B hB hne
      rw [mem_powerset] at hB
      by_contra hprod
      have h1 := hf B (left_ne_zero_of_mul hprod)
      have h2 := hg _ (right_ne_zero_of_mul hprod)
      apply hne
      ext p; simp only [mem_inter]
      constructor
      · intro hp; exact ⟨hB hp, h1 hp⟩
      · rintro ⟨hp, hp1⟩
        by_contra hpB
        exact disjoint_left.1 hd hp1 (h2 (mem_sdiff.2 ⟨hp, hpB⟩))
    · intro h; exact absurd (mem_powerset.2 inter_subset_left) h
  · refine sum_eq_zero fun B hB => ?_
    by_contra hprod
    have h1 := hf B (left_ne_zero_of_mul hprod)
    have h2 := hg _ (right_ne_zero_of_mul hprod)
    apply hA
    intro p hp
    by_cases hpB : p ∈ B
    · exact mem_union_left _ (h1 hpB)
    · exact mem_union_right _ (h2 (mem_sdiff.2 ⟨hp, hpB⟩))

theorem conv_oneBounded_of_disjoint {f g : Finset γ → ℝ} {U1 U2 : Finset γ}
    (hf : SupportedIn f U1) (hg : SupportedIn g U2) (hd : Disjoint U1 U2) (hf1 : OneBounded f)
    (hg1 : OneBounded g) : OneBounded (conv f g) := by
  intro A
  rw [conv_collapse hf hg hd]
  split_ifs
  · rw [abs_mul]
    exact mul_le_one₀ (hf1 _) (abs_nonneg _) (hg1 _)
  · simp

end Collapse

/-! ### The colouring model -/

variable {α J : Type*} [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] (cell : α → J)

/-- Number of atoms of `A` in cell `j` with colour `i`. -/
def pat (A : Finset α) (ω : α → Fin 3) : J → Fin 3 → ℕ :=
  fun j i => (A.filter fun p => cell p = j ∧ ω p = i).card

/-- Number of atoms of `A` in cell `j`. -/
def cnt (A : Finset α) (j : J) : ℕ := (A.filter fun p => cell p = j).card

/-- `k₀! k₁! k₂!`. -/
def fact3 (κ : Fin 3 → ℕ) : ℝ :=
  ((κ 0).factorial : ℝ) * (κ 1).factorial * (κ 2).factorial

theorem fact3_pos (κ : Fin 3 → ℕ) : 0 < fact3 κ := by
  unfold fact3; have := Nat.factorial_pos (κ 0); have := Nat.factorial_pos (κ 1)
  have := Nat.factorial_pos (κ 2); positivity

/-- The cell pattern condition: cell `j` of `A` has `Σ_i κ j i` atoms. -/
def PatCond (A : Finset α) (κ : J → Fin 3 → ℕ) : Prop := ∀ j, ∑ i, κ j i = cnt cell A j

open Classical in
/-- **The multinomial probability** `π(A,κ) = ∏_j [k_j!/(k_{j0}! k_{j1}! k_{j2}!)] 3^{-k_j}`
(and `0` if the cell counts of `A` do not match). -/
noncomputable def piProb (A : Finset α) (κ : J → Fin 3 → ℕ) : ℝ :=
  if PatCond cell A κ then
    ∏ j, (((cnt cell A j).factorial : ℝ) / fact3 (κ j) * (1 / 3 : ℝ) ^ cnt cell A j)
  else 0

/-- Number of colourings with pattern `κ` on `A`. -/
def N (A : Finset α) (κ : J → Fin 3 → ℕ) : ℕ :=
  (univ.filter fun ω : α → Fin 3 => pat cell A ω = κ).card

/-- Decrement of the `(c, v)` entry. -/
def dec (κ : J → Fin 3 → ℕ) (c : J) (v : Fin 3) : J → Fin 3 → ℕ :=
  fun j i => κ j i - if c = j ∧ v = i then 1 else 0

/-- **Multinomial Pascal rule** for three colours. -/
theorem pascal3 (a b d n : ℕ) (h : a + b + d = n + 1) :
    ((n + 1).factorial : ℝ) / (a.factorial * b.factorial * d.factorial) =
      (if 1 ≤ a then (n.factorial : ℝ) / ((a - 1).factorial * b.factorial * d.factorial)
        else 0) +
      (if 1 ≤ b then (n.factorial : ℝ) / (a.factorial * (b - 1).factorial * d.factorial)
        else 0) +
      (if 1 ≤ d then (n.factorial : ℝ) / (a.factorial * b.factorial * (d - 1).factorial)
        else 0) := by
  have hf : ∀ m : ℕ, 1 ≤ m → (m.factorial : ℝ) = m * (m - 1).factorial := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp [Nat.factorial_succ]
  have ha := Nat.factorial_pos a
  have hb := Nat.factorial_pos b
  have hd := Nat.factorial_pos d
  have hn : ((n + 1).factorial : ℝ) = (n + 1) * n.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hsum : ((n : ℝ) + 1) = a + b + d := by exact_mod_cast h.symm
  have e : ∀ (m : ℕ) (X : ℝ), 0 < X →
      (if 1 ≤ m then (n.factorial : ℝ) / ((m - 1).factorial * X) else 0) =
        (n.factorial : ℝ) * m / (m.factorial * X) := by
    intro m X hX
    split_ifs with hm
    · rw [hf m hm]
      have := Nat.factorial_pos (m - 1)
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      field_simp
    · simp [show m = 0 by omega]
  have e1 := e a (b.factorial * d.factorial) (by positivity)
  have e2 := e b (a.factorial * d.factorial) (by positivity)
  have e3 := e d (a.factorial * b.factorial) (by positivity)
  rw [show ((a - 1).factorial : ℝ) * b.factorial * d.factorial =
    (a - 1).factorial * (b.factorial * d.factorial) by ring]
  rw [show (a.factorial : ℝ) * (b - 1).factorial * d.factorial =
    (b - 1).factorial * (a.factorial * d.factorial) by ring]
  rw [show (a.factorial : ℝ) * b.factorial * (d - 1).factorial =
    (d - 1).factorial * (a.factorial * b.factorial) by ring]
  rw [e1, e2, e3, hn, hsum]
  field_simp

/-- Symmetry of the colour at a single atom `x` for a predicate not looking at `ω x`. -/
theorem card_eval_eq (x : α) (P : (α → Fin 3) → Prop) [DecidablePred P]
    (hP : ∀ ω v, P (Function.update ω x v) ↔ P ω) (v : Fin 3) :
    3 * (univ.filter fun ω : α → Fin 3 => ω x = v ∧ P ω).card =
      (univ.filter P).card := by
  have hfib : ∀ v v' : Fin 3, (univ.filter fun ω : α → Fin 3 => ω x = v ∧ P ω).card =
      (univ.filter fun ω : α → Fin 3 => ω x = v' ∧ P ω).card := by
    intro v v'
    refine card_bij' (fun ω _ => Function.update ω x v') (fun ω _ => Function.update ω x v)
      ?_ ?_ ?_ ?_
    · intro ω hω
      simp only [mem_filter, mem_univ, true_and] at hω ⊢
      exact ⟨by simp, (hP ω v').2 hω.2⟩
    · intro ω hω
      simp only [mem_filter, mem_univ, true_and] at hω ⊢
      exact ⟨by simp, (hP ω v).2 hω.2⟩
    · intro ω hω
      simp only [mem_filter, mem_univ, true_and] at hω
      simp [← hω.1]
    · intro ω hω
      simp only [mem_filter, mem_univ, true_and] at hω
      simp [← hω.1]
  conv_rhs => rw [card_eq_sum_card_fiberwise (f := fun ω : α → Fin 3 => ω x) (t := univ)
    (fun _ _ => Finset.mem_coe.2 (mem_univ _))]
  simp only [filter_filter]
  rw [Fin.sum_univ_three]
  have e : ∀ v' : Fin 3, (univ.filter fun ω : α → Fin 3 => P ω ∧ ω x = v').card =
      (univ.filter fun ω : α → Fin 3 => ω x = v ∧ P ω).card := by
    intro v'
    rw [hfib v v']
    congr 1; ext ω; simp [and_comm]
  rw [e 0, e 1, e 2]
  ring

omit [Fintype α] [Fintype J] in
theorem cnt_insert {x : α} {A : Finset α} (hx : x ∉ A) (j : J) :
    cnt cell (insert x A) j = cnt cell A j + if cell x = j then 1 else 0 := by
  unfold cnt
  rw [filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun h' => hx (mem_filter.1 h').1)]
  · simp

omit [Fintype α] [Fintype J] in
theorem pat_insert {x : α} {A : Finset α} (hx : x ∉ A) (ω : α → Fin 3) (j : J) (i : Fin 3) :
    pat cell (insert x A) ω j i = pat cell A ω j i + if cell x = j ∧ ω x = i then 1 else 0 := by
  unfold pat
  rw [filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun h' => hx (mem_filter.1 h').1)]
  · simp

omit [Fintype α] [Fintype J] in
theorem pat_update {x : α} {A : Finset α} (hx : x ∉ A) (ω : α → Fin 3) (v : Fin 3) :
    pat cell A (Function.update ω x v) = pat cell A ω := by
  funext j i
  unfold pat
  congr 1
  refine filter_congr fun p hp => ?_
  have : p ≠ x := fun h => hx (h ▸ hp)
  simp [Function.update_of_ne this]

/-- **Counting recurrence**: `3 N(A ∪ {x}, κ) = Σ_v 1(κ_{c,v} ≥ 1) N(A, κ - e_{c,v})`. -/
theorem N_insert {x : α} {A : Finset α} (hx : x ∉ A) (κ : J → Fin 3 → ℕ) :
    (3 * N cell (insert x A) κ : ℝ) =
      ∑ v : Fin 3, if 1 ≤ κ (cell x) v then (N cell A (dec κ (cell x) v) : ℝ) else 0 := by
  have hsplit : N cell (insert x A) κ = ∑ v : Fin 3,
      (univ.filter fun ω : α → Fin 3 => ω x = v ∧ pat cell (insert x A) ω = κ).card := by
    unfold N
    rw [card_eq_sum_card_fiberwise (f := fun ω : α → Fin 3 => ω x) (t := univ)
      (fun _ _ => Finset.mem_coe.2 (mem_univ _))]
    refine sum_congr rfl fun v _ => ?_
    congr 1; ext ω; simp [and_comm]
  have hterm : ∀ v : Fin 3,
      (3 * (univ.filter fun ω : α → Fin 3 => ω x = v ∧ pat cell (insert x A) ω = κ).card : ℝ) =
        if 1 ≤ κ (cell x) v then (N cell A (dec κ (cell x) v) : ℝ) else 0 := by
    intro v
    have hiff : ∀ ω : α → Fin 3, ω x = v →
        (pat cell (insert x A) ω = κ ↔
          1 ≤ κ (cell x) v ∧ pat cell A ω = dec κ (cell x) v) := by
      intro ω hωx
      constructor
      · intro h
        have h1 : ∀ j i, pat cell A ω j i + (if cell x = j ∧ ω x = i then 1 else 0) = κ j i :=
          fun j i => by rw [← pat_insert cell hx, h]
        refine ⟨?_, ?_⟩
        · have := h1 (cell x) v; simp [hωx] at this; omega
        · funext j i; have := h1 j i; unfold dec; rw [hωx] at this
          split_ifs at this ⊢ <;> omega
      · rintro ⟨hk, h⟩
        funext j i
        rw [pat_insert cell hx, h]
        unfold dec; rw [hωx]
        split_ifs with h'
        · obtain ⟨rfl, rfl⟩ := h'; omega
        · omega
    split_ifs with hk
    · have hset : (univ.filter fun ω : α → Fin 3 => ω x = v ∧ pat cell (insert x A) ω = κ) =
          univ.filter fun ω : α → Fin 3 => ω x = v ∧ pat cell A ω = dec κ (cell x) v := by
        ext ω; simp only [mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, ((hiff ω h1).1 h2).2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, (hiff ω h1).2 ⟨hk, h2⟩⟩
      rw [hset]
      have := card_eval_eq x (fun ω => pat cell A ω = dec κ (cell x) v)
        (fun ω v' => by simp only [pat_update cell hx]) v
      unfold N
      exact_mod_cast this
    · have hset : (univ.filter fun ω : α → Fin 3 => ω x = v ∧ pat cell (insert x A) ω = κ) =
          ∅ := by
        rw [filter_eq_empty_iff]
        rintro ω - ⟨h1, h2⟩
        exact hk ((hiff ω h1).1 h2).1
      simp [hset]
  rw [hsplit]
  push_cast
  rw [mul_sum]
  exact sum_congr rfl fun v _ => hterm v

omit [Fintype α] [Fintype J] in
/-- The decremented pattern condition. -/
theorem patCond_dec {x : α} {A : Finset α} (hx : x ∉ A) (κ : J → Fin 3 → ℕ) (v : Fin 3)
    (hk : 1 ≤ κ (cell x) v) :
    PatCond cell A (dec κ (cell x) v) ↔ PatCond cell (insert x A) κ := by
  have key : ∀ j, ∑ i, dec κ (cell x) v j i + (if cell x = j then 1 else 0) = ∑ i, κ j i := by
    intro j
    by_cases hj : cell x = j
    · subst hj
      fin_cases v <;> simp [dec, Fin.sum_univ_three] at hk ⊢ <;> omega
    · simp [dec, hj]
  unfold PatCond
  constructor
  · intro h j; rw [cnt_insert cell hx, ← key j, h j]
  · intro h j; have := key j; rw [h j, cnt_insert cell hx] at this; omega

omit [Fintype α] in
/-- **Probability recurrence** mirroring `N_insert`. -/
theorem piProb_insert {x : α} {A : Finset α} (hx : x ∉ A) (κ : J → Fin 3 → ℕ) :
    3 * piProb cell (insert x A) κ =
      ∑ v : Fin 3, if 1 ≤ κ (cell x) v then piProb cell A (dec κ (cell x) v) else 0 := by
  classical
  set c := cell x
  by_cases hP : PatCond cell (insert x A) κ
  · have hPd : ∀ v, 1 ≤ κ c v → PatCond cell A (dec κ c v) :=
      fun v hk => (patCond_dec cell hx κ v hk).2 hP
    have hrest : ∀ v, ∀ j ∈ ({c}ᶜ : Finset J),
        (((cnt cell A j).factorial : ℝ) / fact3 (dec κ c v j) * (1 / 3 : ℝ) ^ cnt cell A j) =
        (((cnt cell (insert x A) j).factorial : ℝ) / fact3 (κ j) *
          (1 / 3 : ℝ) ^ cnt cell (insert x A) j) := by
      intro v j hj
      have hjc : c ≠ j := fun h => by simp [h] at hj
      have hd : dec κ c v j = κ j := by funext i; simp [dec, hjc]
      rw [hd, cnt_insert cell hx, if_neg hjc, add_zero]
    set Rest := ∏ j ∈ ({c}ᶜ : Finset J), (((cnt cell (insert x A) j).factorial : ℝ) /
      fact3 (κ j) * (1 / 3 : ℝ) ^ cnt cell (insert x A) j)
    have hL : piProb cell (insert x A) κ =
        ((cnt cell A c + 1).factorial : ℝ) / fact3 (κ c) * (1 / 3 : ℝ) ^ (cnt cell A c + 1) *
          Rest := by
      unfold piProb; rw [if_pos hP, Fintype.prod_eq_mul_prod_compl c, cnt_insert cell hx,
        if_pos rfl]
    have hR : ∀ v, 1 ≤ κ c v → piProb cell A (dec κ c v) =
        ((cnt cell A c).factorial : ℝ) / fact3 (dec κ c v c) * (1 / 3 : ℝ) ^ cnt cell A c *
          Rest := by
      intro v hk
      unfold piProb; rw [if_pos (hPd v hk), Fintype.prod_eq_mul_prod_compl c]
      congr 1
      exact prod_congr rfl (hrest v)
    have hsum : κ c 0 + κ c 1 + κ c 2 = cnt cell A c + 1 := by
      have := hP c; rw [Fin.sum_univ_three, cnt_insert cell hx, if_pos rfl] at this; exact this
    have hpas := pascal3 (κ c 0) (κ c 1) (κ c 2) (cnt cell A c) hsum
    rw [Fin.sum_univ_three, hL]
    have t0 : (if 1 ≤ κ c 0 then piProb cell A (dec κ c 0) else 0) =
        (if 1 ≤ κ c 0 then ((cnt cell A c).factorial : ℝ) /
          ((κ c 0 - 1).factorial * (κ c 1).factorial * (κ c 2).factorial) else 0) *
          (1 / 3 : ℝ) ^ cnt cell A c * Rest := by
      split_ifs with hk
      · rw [hR 0 hk]; simp [fact3, dec]
      · simp
    have t1 : (if 1 ≤ κ c 1 then piProb cell A (dec κ c 1) else 0) =
        (if 1 ≤ κ c 1 then ((cnt cell A c).factorial : ℝ) /
          ((κ c 0).factorial * (κ c 1 - 1).factorial * (κ c 2).factorial) else 0) *
          (1 / 3 : ℝ) ^ cnt cell A c * Rest := by
      split_ifs with hk
      · rw [hR 1 hk]; simp [fact3, dec]
      · simp
    have t2 : (if 1 ≤ κ c 2 then piProb cell A (dec κ c 2) else 0) =
        (if 1 ≤ κ c 2 then ((cnt cell A c).factorial : ℝ) /
          ((κ c 0).factorial * (κ c 1).factorial * (κ c 2 - 1).factorial) else 0) *
          (1 / 3 : ℝ) ^ cnt cell A c * Rest := by
      split_ifs with hk
      · rw [hR 2 hk]; simp [fact3, dec]
      · simp
    rw [t0, t1, t2]
    unfold fact3
    rw [hpas]
    ring
  · have hL : piProb cell (insert x A) κ = 0 := by unfold piProb; rw [if_neg hP]
    rw [hL, mul_zero]
    symm
    refine sum_eq_zero fun v _ => ?_
    split_ifs with hk
    · unfold piProb
      rw [if_neg (fun h => hP ((patCond_dec cell hx κ v hk).1 h))]
    · rfl

/-- **Exact count of colourings with a given cell/colour pattern.** -/
theorem card_pattern (A : Finset α) (κ : J → Fin 3 → ℕ) :
    (N cell A κ : ℝ) = 3 ^ Fintype.card α * piProb cell A κ := by
  classical
  induction A using Finset.induction_on generalizing κ with
  | empty =>
    have hpat : ∀ ω : α → Fin 3, pat cell ∅ ω = fun _ _ => 0 := fun ω => by
      funext j i; simp [pat]
    by_cases hκ : κ = fun _ _ => 0
    · subst hκ
      have hN : N cell ∅ (fun _ _ => 0) = 3 ^ Fintype.card α := by
        unfold N; simp [hpat]
      have hPi : piProb cell ∅ (fun _ _ => 0) = 1 := by
        unfold piProb
        rw [if_pos (show PatCond cell ∅ (fun _ _ => 0) from fun j => by simp [cnt])]
        refine prod_eq_one fun j _ => ?_
        simp [cnt, fact3]
      rw [hN, hPi]; push_cast; ring
    · have hN : N cell ∅ κ = 0 := by
        unfold N
        rw [card_eq_zero, filter_eq_empty_iff]
        intro ω _ h; exact hκ (by rw [← h, hpat])
      have hPi : piProb cell ∅ κ = 0 := by
        unfold piProb
        rw [if_neg]
        intro h
        apply hκ
        funext j i
        have := h j
        simp only [cnt, filter_empty, card_empty] at this
        have hle : κ j i ≤ ∑ i', κ j i' :=
          single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
        omega
      rw [hN, hPi]; simp
  | insert x A hx ih =>
    have h1 := N_insert cell hx κ
    have h2 := piProb_insert cell hx κ
    have : (3 : ℝ) * N cell (insert x A) κ = 3 * (3 ^ Fintype.card α * piProb cell (insert x A) κ)
        := by
      rw [h1, mul_left_comm, h2, mul_sum]
      refine sum_congr rfl fun v _ => ?_
      split_ifs
      · exact ih _
      · simp
    linarith

/-! ### The colour-class weights `G_i` and the exact colouring identity -/

variable (Ur : Finset α) (kbin : Fin 3 → J → ℕ)

open Classical in
/-- `G_{i,ω}(B) = 1` iff `B ⊆ Ur`, all atoms of `B` have colour `i`, and cell `j` contains
exactly `k_{j,i}` atoms of `B`. -/
noncomputable def G (i : Fin 3) (ω : α → Fin 3) (B : Finset α) : ℝ :=
  if B ⊆ Ur ∧ (∀ p ∈ B, ω p = i) ∧ (∀ j, cnt cell B j = kbin i j) then 1 else 0

theorem G_zero_or_one (i : Fin 3) (ω : α → Fin 3) (B : Finset α) :
    G cell Ur kbin i ω B = 0 ∨ G cell Ur kbin i ω B = 1 := by
  unfold G; split_ifs <;> simp

theorem G_oneBounded (i : Fin 3) (ω : α → Fin 3) : OneBounded (G cell Ur kbin i ω) := by
  intro B; unfold G; split_ifs <;> simp

/-- The colour class `{p : ω p = i}`. -/
def colourClass (ω : α → Fin 3) (i : Fin 3) : Finset α := univ.filter fun p => ω p = i

theorem G_supported (i : Fin 3) (ω : α → Fin 3) :
    SupportedIn (G cell Ur kbin i ω) (colourClass ω i) := by
  intro B hB p hp
  unfold G at hB
  split_ifs at hB with h
  · exact mem_filter.2 ⟨mem_univ _, h.2.1 p hp⟩
  · exact absurd rfl hB

theorem G_supported_rough (i : Fin 3) (ω : α → Fin 3) : SupportedIn (G cell Ur kbin i ω) Ur := by
  intro B hB
  unfold G at hB
  split_ifs at hB with h
  · exact h.1
  · exact absurd rfl hB

omit [DecidableEq α] in
theorem colourClass_disjoint (ω : α → Fin 3) {i i' : Fin 3} (h : i ≠ i') :
    Disjoint (colourClass ω i) (colourClass ω i') := by
  rw [disjoint_left]; intro p hp hp'
  simp only [colourClass, mem_filter] at hp hp'
  exact h (hp.2.symm.trans hp'.2)

/-- `colourConv ω = G_0 ⋆ (G_1 ⋆ G_2)`. -/
noncomputable def colourConv (ω : α → Fin 3) : Finset α → ℝ :=
  conv (G cell Ur kbin 0 ω) (conv (G cell Ur kbin 1 ω) (G cell Ur kbin 2 ω))

/-- The target pattern `κ j i = k_{j,i}`. -/
def target : J → Fin 3 → ℕ := fun j i => kbin i j

omit [Fintype α] [DecidableEq α] [Fintype J] in
theorem cnt_filter_colour (A : Finset α) (ω : α → Fin 3) (i : Fin 3) (j : J) :
    cnt cell (A.filter fun p => ω p = i) j = pat cell A ω j i := by
  unfold cnt pat; rw [filter_filter]; congr 1; ext p; simp [and_comm]

open Classical in
/-- **The colour convolution is `{0,1}`-valued** and detects exactly the specified pattern:
`(G_0 ⋆ G_1 ⋆ G_2)(A) = 1(A ⊆ Ur ∧ pat A ω = k)`. -/
theorem colourConv_eq (ω : α → Fin 3) (A : Finset α) :
    colourConv cell Ur kbin ω A =
      if A ⊆ Ur ∧ pat cell A ω = target kbin then 1 else 0 := by
  unfold colourConv
  have h12 := conv_collapse (G_supported cell Ur kbin 1 ω) (G_supported cell Ur kbin 2 ω)
    (colourClass_disjoint ω (by decide))
  have hsup12 : SupportedIn (conv (G cell Ur kbin 1 ω) (G cell Ur kbin 2 ω))
      (colourClass ω 1 ∪ colourClass ω 2) :=
    conv_supported (G_supported cell Ur kbin 1 ω) (G_supported cell Ur kbin 2 ω)
  have hd : Disjoint (colourClass ω 0) (colourClass ω 1 ∪ colourClass ω 2) :=
    disjoint_union_right.2 ⟨colourClass_disjoint ω (by decide),
      colourClass_disjoint ω (by decide)⟩
  have hall : ∀ B : Finset α, B ⊆ colourClass ω 0 ∪ (colourClass ω 1 ∪ colourClass ω 2) := by
    intro B p _
    simp only [colourClass, mem_union, mem_filter, mem_univ, true_and]
    rcases (show ∀ v : Fin 3, v = 0 ∨ v = 1 ∨ v = 2 by decide) (ω p) with h | h | h <;>
      simp [h]
  rw [conv_collapse (G_supported cell Ur kbin 0 ω) hsup12 hd, if_pos (hall A), h12,
    if_pos inter_subset_right]
  have e1 : A ∩ (colourClass ω 1 ∪ colourClass ω 2) ∩ colourClass ω 1 =
      A.filter fun p => ω p = 1 := by
    ext p; simp [colourClass]
  have e2 : A ∩ (colourClass ω 1 ∪ colourClass ω 2) ∩ colourClass ω 2 =
      A.filter fun p => ω p = 2 := by
    ext p; simp [colourClass]
  have e0 : A ∩ colourClass ω 0 = A.filter fun p => ω p = 0 := by
    ext p; simp [colourClass]
  rw [e0, e1, e2]
  have hG : ∀ i : Fin 3, G cell Ur kbin i ω (A.filter fun p => ω p = i) =
      if (A.filter fun p => ω p = i) ⊆ Ur ∧ ∀ j, pat cell A ω j i = kbin i j then 1 else 0 := by
    intro i
    unfold G
    simp only [cnt_filter_colour]
    congr 1
    apply propext
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, fun p hp => (mem_filter.1 hp).2, h3⟩
  rw [hG 0, hG 1, hG 2]
  have hUr : A ⊆ Ur ↔ ∀ i : Fin 3, (A.filter fun p => ω p = i) ⊆ Ur := by
    constructor
    · intro h i; exact (filter_subset _ _).trans h
    · intro h p hp; exact h (ω p) (mem_filter.2 ⟨hp, rfl⟩)
  have hpat : pat cell A ω = target kbin ↔ ∀ i : Fin 3, ∀ j, pat cell A ω j i = kbin i j := by
    constructor
    · intro h i j; rw [h]; rfl
    · intro h; funext j i; exact h i j
  by_cases hc : A ⊆ Ur ∧ pat cell A ω = target kbin
  · rw [if_pos hc]
    have h1 := hUr.1 hc.1
    have h2 := hpat.1 hc.2
    rw [if_pos ⟨h1 0, h2 0⟩, if_pos ⟨h1 1, h2 1⟩, if_pos ⟨h1 2, h2 2⟩]; norm_num
  · rw [if_neg hc]
    have : ¬ ((∀ i : Fin 3, (A.filter fun p => ω p = i) ⊆ Ur) ∧
        ∀ i : Fin 3, ∀ j, pat cell A ω j i = kbin i j) := fun h =>
      hc ⟨hUr.2 h.1, hpat.2 h.2⟩
    by_contra hne
    apply this
    have hne' : ∀ i : Fin 3, (A.filter fun p => ω p = i) ⊆ Ur ∧
        ∀ j, pat cell A ω j i = kbin i j := by
      intro i
      by_contra hi
      apply hne
      fin_cases i <;> simp_all
    exact ⟨fun i => (hne' i).1, fun i => (hne' i).2⟩

/-- The uniform finite average over colourings. -/
noncomputable def colourExp (F : (α → Fin 3) → ℝ) : ℝ :=
  (∑ ω : α → Fin 3, F ω) / 3 ^ Fintype.card α

/-- The colouring probability measure has total mass one. -/
theorem colouring_mass_one : colourExp (α := α) (fun _ => 1) = 1 := by
  unfold colourExp
  simp [Fintype.card_fin]

/-- The explicit multinomial probability `π = ∏_j [k_j!/(k_{j0}!k_{j1}!k_{j2}!)] 3^{-k_j}`. -/
noncomputable def piConst : ℝ :=
  ∏ j, (((∑ i, kbin i j).factorial : ℝ) / fact3 (target kbin j) *
    (1 / 3 : ℝ) ^ (∑ i, kbin i j))

omit [DecidableEq J] in
theorem piConst_pos : 0 < piConst (J := J) kbin := by
  unfold piConst
  refine prod_pos fun j _ => ?_
  have := Nat.factorial_pos (∑ i, kbin i j)
  have := fact3_pos (target kbin j)
  positivity

/-- The specified squarefree cell pattern: `A ⊆ Ur` and cell `j` contains `k_j` atoms of `A`. -/
def CellPattern (A : Finset α) : Prop := A ⊆ Ur ∧ PatCond cell A (target kbin)

open Classical in
/-- **The exact colouring identity**:
`1(specified squarefree cell pattern) = π^{-1} · E_ω[(G_0 ⋆ G_1 ⋆ G_2)(A)]`. -/
theorem exact_colouring_identity (A : Finset α) :
    (if CellPattern cell Ur kbin A then (1 : ℝ) else 0) =
      (piConst kbin)⁻¹ * colourExp (fun ω => colourConv cell Ur kbin ω A) := by
  have hpos := piConst_pos (J := J) kbin
  have hE : colourExp (fun ω => colourConv cell Ur kbin ω A) =
      if A ⊆ Ur then piProb cell A (target kbin) else 0 := by
    unfold colourExp
    simp_rw [colourConv_eq]
    split_ifs with hA
    · simp only [hA, true_and]
      rw [sum_boole]
      have := card_pattern cell A (target kbin)
      unfold N at this
      rw [this]
      have : (3 : ℝ) ^ Fintype.card α ≠ 0 := by positivity
      field_simp
    · simp [hA]
  rw [hE]
  unfold CellPattern
  by_cases hA : A ⊆ Ur
  · rw [if_pos hA]
    unfold piProb
    by_cases hP : PatCond cell A (target kbin)
    · rw [if_pos ⟨hA, hP⟩, if_pos hP]
      have : ∏ j, (((cnt cell A j).factorial : ℝ) / fact3 (target kbin j) *
          (1 / 3 : ℝ) ^ cnt cell A j) = piConst kbin := by
        unfold piConst
        refine prod_congr rfl fun j _ => ?_
        have hj := hP j
        simp only [target] at hj
        rw [← hj]
      rw [this, inv_mul_cancel₀ hpos.ne']
    · rw [if_neg (fun h => hP h.2), if_neg hP, mul_zero]
  · rw [if_neg (fun h => hA h.1), if_neg hA, mul_zero]

omit [DecidableEq J] in
/-- **`π^{-1} ≤ 3^R`** when the total number of rough atoms `Σ_j k_j` is at most `R`. -/
theorem piProb_inv_le {R : ℕ} (hR : ∑ j, ∑ i, kbin i j ≤ R) :
    (piConst (J := J) kbin)⁻¹ ≤ 3 ^ R := by
  have hpos := piConst_pos (J := J) kbin
  have hlow : (1 / 3 : ℝ) ^ R ≤ piConst kbin := by
    unfold piConst
    calc (1 / 3 : ℝ) ^ R ≤ (1 / 3 : ℝ) ^ (∑ j, ∑ i, kbin i j) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hR
      _ = ∏ j, (1 / 3 : ℝ) ^ (∑ i, kbin i j) := by rw [prod_pow_eq_pow_sum]
      _ ≤ _ := by
          refine prod_le_prod (fun j _ => by positivity) fun j _ => ?_
          have hm : fact3 (target kbin j) ≤ ((∑ i, kbin i j).factorial : ℝ) := by
            have := Nat.multinomial_spec (s := univ) (f := fun i => kbin i j)
            have hpos := Nat.multinomial_pos (s := univ) (f := fun i => kbin i j)
            have hle : ∏ i, (kbin i j).factorial ≤ (∑ i, kbin i j).factorial := by
              rw [← this]; exact Nat.le_mul_of_pos_right _ hpos
            unfold fact3 target
            rw [Fin.prod_univ_three] at hle
            exact_mod_cast hle
          have hf := fact3_pos (target kbin j)
          have : (1 : ℝ) ≤ ((∑ i, kbin i j).factorial : ℝ) / fact3 (target kbin j) := by
            rw [le_div_iff₀ hf]; linarith
          have h3 : (0 : ℝ) ≤ (1 / 3) ^ (∑ i, kbin i j) := by positivity
          nlinarith
  calc (piConst kbin)⁻¹ ≤ ((1 / 3 : ℝ) ^ R)⁻¹ := inv_anti₀ (by positivity) hlow
    _ = 3 ^ R := by rw [one_div, inv_pow, inv_inv]

end CellColouring
end ResearchBankV22
end Erdos287
