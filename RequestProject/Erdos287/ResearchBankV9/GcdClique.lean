import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V9 §3A: prescribed-shape gcd-clique, elementary core

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Kernel-proved:

* `gcd_eq_diff_iff` — `gcd(x, y) = |y − x|` iff `(y − x) ∣ x`;
* `clique_translate_iff` — the translates `C + b_i` form a gcd-clique
  (`gcd(C+b_i, C+b_j) = |b_i − b_j|`) iff `(b_j − b_i) ∣ C + b_i` for all `b_i < b_j`;
* `crt_exists` — the **general (non-coprime) Chinese remainder theorem** for a finite
  pairwise-compatible system, with its converse `compatible_of_solution`;
* `gcdClique_of_compatible` — pairwise compatibility of the clique congruence system gives a
  common translation `C` (arbitrarily large) realising the gcd-clique;
* fixtures: `{0,1,2,4}` with `C = 8` is a clique; `{0,1,2,3}` admits **no** translation
  (`shape_matters`), so the prescribed shape genuinely constrains the offsets.

`PrescribedShapeGCDClique` (offsets in prescribed scaled boxes) is stated as a proposition.
The box-placement counting/union-bound argument is **not** formalized in this bank, so this
proposition is **not** inhabited here.  `PrimeValuesOnClique` (Maynard-type prime supply on the
clique) is a **separate external interface**, also never inhabited; the two are kept apart.
-/

namespace Erdos287
namespace ResearchBankV9
namespace GcdClique

/-! ## 1.  The gcd identity -/

/-- `gcd(x, y) = |y − x|` iff `(y − x) ∣ x`. -/
theorem gcd_eq_diff_iff (x y : ℤ) : Int.gcd x y = (y - x).natAbs ↔ (y - x) ∣ x := by
  rw [← Int.gcd_sub_self_right, Int.gcd_eq_natAbs, Nat.gcd_eq_right_iff_dvd,
    Int.natAbs_dvd_natAbs]

/-- A list of integers is a gcd-clique: `gcd(x, y) = |y − x|` for all `x < y`. -/
def IsGcdClique (S : List ℤ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x < y → Int.gcd x y = (y - x).natAbs

/-- **Translation form.** -/
theorem clique_translate_iff (bs : List ℤ) (C : ℤ) :
    IsGcdClique (bs.map (C + ·)) ↔ ∀ bi ∈ bs, ∀ bj ∈ bs, bi < bj → (bj - bi) ∣ C + bi := by
  unfold IsGcdClique
  simp only [List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h bi hbi bj hbj hlt
    have := h _ bi hbi rfl _ bj hbj rfl (by linarith)
    rw [gcd_eq_diff_iff] at this
    simpa using this
  · rintro h _ bi hbi rfl _ bj hbj rfl hlt
    rw [gcd_eq_diff_iff]
    simpa using h bi hbi bj hbj (by linarith)

/-! ## 2.  The general Chinese remainder theorem -/

/-- `gcd(n, lcm(A, B)) ∣ lcm(gcd(n, A), gcd(n, B))`. -/
theorem gcd_lcm_dvd_lcm_gcd {n A B : ℕ} (hn : n ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) :
    Nat.gcd n (Nat.lcm A B) ∣ Nat.lcm (Nat.gcd n A) (Nat.gcd n B) := by
  have hg1 : Nat.gcd n A ≠ 0 := Nat.gcd_ne_zero_left hn
  have hg2 : Nat.gcd n B ≠ 0 := Nat.gcd_ne_zero_left hn
  rw [← Nat.factorization_le_iff_dvd (Nat.gcd_ne_zero_left hn) (Nat.lcm_ne_zero hg1 hg2),
    Nat.factorization_gcd hn (Nat.lcm_ne_zero hA hB), Nat.factorization_lcm hA hB,
    Nat.factorization_lcm hg1 hg2, Nat.factorization_gcd hn hA, Nat.factorization_gcd hn hB]
  intro p
  simp only [Finsupp.inf_apply, Finsupp.sup_apply]
  omega

/-- The lcm of the moduli of a congruence list. -/
def lcmList : List (ℤ × ℕ) → ℕ
  | [] => 1
  | q :: t => Nat.lcm q.2 (lcmList t)

theorem lcmList_ne_zero : ∀ l : List (ℤ × ℕ), (∀ q ∈ l, q.2 ≠ 0) → lcmList l ≠ 0
  | [], _ => by simp [lcmList]
  | q :: t, h => by
    simp only [lcmList]
    exact Nat.lcm_ne_zero (h q (by simp)) (lcmList_ne_zero t fun r hr => h r (by simp [hr]))

theorem dvd_lcmList : ∀ l : List (ℤ × ℕ), ∀ q ∈ l, q.2 ∣ lcmList l
  | [], q, hq => by simp at hq
  | r :: t, q, hq => by
    simp only [lcmList]
    rcases List.mem_cons.1 hq with rfl | hq
    · exact Nat.dvd_lcm_left _ _
    · exact (dvd_lcmList t q hq).trans (Nat.dvd_lcm_right _ _)

theorem gcd_lcmList_dvd {n : ℕ} (hn : n ≠ 0) (z : ℤ) :
    ∀ l : List (ℤ × ℕ), (∀ q ∈ l, q.2 ≠ 0) → (∀ q ∈ l, ((Nat.gcd n q.2 : ℕ) : ℤ) ∣ z) →
      ((Nat.gcd n (lcmList l) : ℕ) : ℤ) ∣ z
  | [], _, _ => by simp [lcmList]
  | q :: t, hne, h => by
    simp only [lcmList]
    have hq : q.2 ≠ 0 := hne q (by simp)
    have ht := lcmList_ne_zero t fun r hr => hne r (by simp [hr])
    have h1 : ((Nat.gcd n q.2 : ℕ) : ℤ) ∣ z := h q (by simp)
    have h2 := gcd_lcmList_dvd hn z t (fun r hr => hne r (by simp [hr]))
      (fun r hr => h r (by simp [hr]))
    rw [Int.natCast_dvd] at h1 h2 ⊢
    exact (gcd_lcm_dvd_lcm_gcd hn hq ht).trans (Nat.lcm_dvd h1 h2)

/-- Two-congruence CRT with the gcd compatibility condition. -/
theorem two_crt (a b : ℤ) (n L : ℕ) (h : ((Nat.gcd n L : ℕ) : ℤ) ∣ a - b) :
    ∃ y : ℤ, (n : ℤ) ∣ y - a ∧ (L : ℤ) ∣ y - b := by
  obtain ⟨k, hk⟩ := h
  have hg := Int.gcd_eq_gcd_ab (n : ℤ) (L : ℤ)
  rw [Int.gcd_natCast_natCast] at hg
  refine ⟨a - n * Int.gcdA n L * k, ⟨-(Int.gcdA n L * k), by ring⟩, ⟨Int.gcdB n L * k, ?_⟩⟩
  have : a - b = (n * Int.gcdA n L + L * Int.gcdB n L) * k := by rw [← hg]; exact hk
  linear_combination this

/-- **General CRT.**  A finite pairwise-compatible system `x ≡ a_i (mod n_i)` (`n_i ≠ 0`,
`gcd(n_i, n_j) ∣ a_i − a_j`) has a solution. -/
theorem crt_exists : ∀ l : List (ℤ × ℕ), (∀ q ∈ l, q.2 ≠ 0) →
    (∀ q ∈ l, ∀ r ∈ l, ((Nat.gcd q.2 r.2 : ℕ) : ℤ) ∣ q.1 - r.1) →
      ∃ x : ℤ, ∀ q ∈ l, (q.2 : ℤ) ∣ x - q.1
  | [], _, _ => ⟨0, by simp⟩
  | q :: t, hne, hc => by
    obtain ⟨x₀, hx₀⟩ := crt_exists t (fun r hr => hne r (by simp [hr]))
      (fun r hr s hs => hc r (by simp [hr]) s (by simp [hs]))
    have hq : q.2 ≠ 0 := hne q (by simp)
    have hcomp : ((Nat.gcd q.2 (lcmList t) : ℕ) : ℤ) ∣ q.1 - x₀ := by
      apply gcd_lcmList_dvd hq _ t (fun r hr => hne r (by simp [hr]))
      intro r hr
      have e1 : ((Nat.gcd q.2 r.2 : ℕ) : ℤ) ∣ q.1 - r.1 := hc q (by simp) r (by simp [hr])
      have e2 : ((Nat.gcd q.2 r.2 : ℕ) : ℤ) ∣ x₀ - r.1 :=
        (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)).trans (hx₀ r hr)
      have := dvd_sub e1 e2
      rwa [show q.1 - r.1 - (x₀ - r.1) = q.1 - x₀ by ring] at this
    obtain ⟨y, hy1, hy2⟩ := two_crt q.1 x₀ q.2 (lcmList t) hcomp
    refine ⟨y, ?_⟩
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact hy1
    · have h1 : (r.2 : ℤ) ∣ y - x₀ :=
        (Int.natCast_dvd_natCast.2 (dvd_lcmList t r hr)).trans hy2
      have := dvd_add h1 (hx₀ r hr)
      rwa [show y - x₀ + (x₀ - r.1) = y - r.1 by ring] at this

/-- The converse: a solvable system is pairwise compatible. -/
theorem compatible_of_solution (l : List (ℤ × ℕ)) (x : ℤ) (hx : ∀ q ∈ l, (q.2 : ℤ) ∣ x - q.1) :
    ∀ q ∈ l, ∀ r ∈ l, ((Nat.gcd q.2 r.2 : ℕ) : ℤ) ∣ q.1 - r.1 := by
  intro q hq r hr
  have h1 : ((Nat.gcd q.2 r.2 : ℕ) : ℤ) ∣ x - q.1 :=
    (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)).trans (hx q hq)
  have h2 : ((Nat.gcd q.2 r.2 : ℕ) : ℤ) ∣ x - r.1 :=
    (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)).trans (hx r hr)
  have := dvd_sub h2 h1
  rwa [show x - r.1 - (x - q.1) = q.1 - r.1 by ring] at this

/-- Solutions can be shifted by the lcm, hence taken arbitrarily large. -/
theorem crt_exists_ge (l : List (ℤ × ℕ)) (hne : ∀ q ∈ l, q.2 ≠ 0)
    (hc : ∀ q ∈ l, ∀ r ∈ l, ((Nat.gcd q.2 r.2 : ℕ) : ℤ) ∣ q.1 - r.1) (C₀ : ℤ) :
    ∃ x : ℤ, C₀ ≤ x ∧ ∀ q ∈ l, (q.2 : ℤ) ∣ x - q.1 := by
  obtain ⟨x, hx⟩ := crt_exists l hne hc
  have hL : (1 : ℤ) ≤ lcmList l := by
    have := lcmList_ne_zero l hne; exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  refine ⟨x + lcmList l * |C₀ - x|, ?_, ?_⟩
  · have h0 : 0 ≤ |C₀ - x| := abs_nonneg _
    have : |C₀ - x| ≤ lcmList l * |C₀ - x| := le_mul_of_one_le_left h0 hL
    have := le_abs_self (C₀ - x)
    linarith
  · intro q hq
    have h1 : (q.2 : ℤ) ∣ lcmList l * |C₀ - x| :=
      (Int.natCast_dvd_natCast.2 (dvd_lcmList l q hq)).mul_right _
    have := dvd_add (hx q hq) h1
    rwa [show x - q.1 + lcmList l * |C₀ - x| = x + lcmList l * |C₀ - x| - q.1 by ring] at this

/-! ## 3.  The clique congruence system -/

/-- All ordered pairs of a list. -/
def pairs (bs : List ℤ) : List (ℤ × ℤ) := bs.flatMap fun x => bs.map fun y => (x, y)

theorem mem_pairs {bs : List ℤ} {p : ℤ × ℤ} : p ∈ pairs bs ↔ p.1 ∈ bs ∧ p.2 ∈ bs := by
  obtain ⟨a, b⟩ := p
  simp [pairs, List.mem_flatMap, List.mem_map]

/-- The clique congruence system of the offsets `bs`: `C ≡ −b_i (mod b_j − b_i)` for `b_i < b_j`. -/
def cliqueSystem (bs : List ℤ) : List (ℤ × ℕ) :=
  ((pairs bs).filter fun p => p.1 < p.2).map fun p => (-p.1, (p.2 - p.1).natAbs)

theorem cliqueSystem_ne_zero (bs : List ℤ) : ∀ q ∈ cliqueSystem bs, q.2 ≠ 0 := by
  intro q hq
  simp only [cliqueSystem, List.mem_map, List.mem_filter, mem_pairs,
    decide_eq_true_eq] at hq
  obtain ⟨p, ⟨-, hlt⟩, rfl⟩ := hq
  simp only [ne_eq, Int.natAbs_eq_zero]
  omega

/-- **Pairwise compatibility gives a (large) common translation realising the gcd-clique.** -/
theorem gcdClique_of_compatible (bs : List ℤ)
    (hc : ∀ q ∈ cliqueSystem bs, ∀ r ∈ cliqueSystem bs,
      ((Nat.gcd q.2 r.2 : ℕ) : ℤ) ∣ q.1 - r.1) (C₀ : ℤ) :
    ∃ C : ℤ, C₀ ≤ C ∧ IsGcdClique (bs.map (C + ·)) := by
  obtain ⟨C, hC0, hC⟩ := crt_exists_ge _ (cliqueSystem_ne_zero bs) hc C₀
  refine ⟨C, hC0, (clique_translate_iff bs C).2 ?_⟩
  intro bi hbi bj hbj hlt
  have := hC (-bi, (bj - bi).natAbs) (by
    simp only [cliqueSystem, List.mem_map, List.mem_filter, mem_pairs, decide_eq_true_eq]
    exact ⟨(bi, bj), ⟨⟨hbi, hbj⟩, hlt⟩, rfl⟩)
  simp only [Int.natCast_natAbs, sub_neg_eq_add] at this
  exact (abs_dvd _ _).1 this

/-- Conversely, a clique translation makes the system compatible. -/
theorem compatible_of_clique (bs : List ℤ) (C : ℤ) (h : IsGcdClique (bs.map (C + ·))) :
    ∀ q ∈ cliqueSystem bs, ∀ r ∈ cliqueSystem bs, ((Nat.gcd q.2 r.2 : ℕ) : ℤ) ∣ q.1 - r.1 := by
  apply compatible_of_solution _ C
  intro q hq
  simp only [cliqueSystem, List.mem_map, List.mem_filter, mem_pairs,
    decide_eq_true_eq] at hq
  obtain ⟨p, ⟨⟨h1, h2⟩, hlt⟩, rfl⟩ := hq
  have := (clique_translate_iff bs C).1 h p.1 h1 p.2 h2 hlt
  simp only [Int.natCast_natAbs, sub_neg_eq_add]
  exact (abs_dvd _ _).2 this

/-! ## 4.  Fixtures -/

/-- `{8, 9, 10, 12}` (offsets `{0,1,2,4}`, `C = 8`) is a gcd-clique. -/
theorem clique_0124 : IsGcdClique ([0, 1, 2, 4].map ((8 : ℤ) + ·)) := by
  rw [clique_translate_iff]
  decide

/-- **The shape matters**: the offsets `{0,1,2,3}` admit no translation. -/
theorem shape_matters : ∀ C : ℤ, ¬ IsGcdClique ([0, 1, 2, 3].map (C + ·)) := by
  intro C h
  rw [clique_translate_iff] at h
  have h1 := h 0 (by simp) 2 (by simp) (by norm_num)
  have h2 := h 1 (by simp) 3 (by simp) (by norm_num)
  omega

/-! ## 5.  The two propositions kept apart -/

/-- **Prescribed-shape gcd-clique (box form).**  For pairwise disjoint rational intervals
`(lo_i, hi_i)` and every scale threshold, there are a scale `X` and offsets `b_i ∈ (lo_i X, hi_i X)`
admitting a gcd-clique translation.  **Not inhabited in this bank** (the counting/union-bound
placement argument is not formalized). -/
def PrescribedShapeGCDClique : Prop :=
  ∀ (lo hi : List ℚ), lo.length = hi.length → (∀ i < lo.length, lo[i]! < hi[i]!) →
    (∀ i < lo.length, ∀ j < lo.length, i < j → hi[i]! ≤ lo[j]!) →
      ∀ X₀ : ℕ, ∃ X ≥ X₀, ∃ bs : List ℤ, bs.length = lo.length ∧
        (∀ i < bs.length, lo[i]! * X < bs[i]! ∧ (bs[i]! : ℚ) < hi[i]! * X) ∧
        ∃ C : ℤ, IsGcdClique (bs.map (C + ·))

/-- **External interface (Maynard-type prime supply on a clique) — never inhabited.**  For a
gcd-clique shape `as` there are infinitely many `t` with all affine forms `a t + 1` prime. -/
def PrimeValuesOnClique (as : List ℕ) : Prop :=
  ∀ t₀ : ℕ, ∃ t ≥ t₀, ∀ a ∈ as, (a * t + 1).Prime

end GcdClique
end ResearchBankV9
end Erdos287
