import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V9 §3C: the circular annulus graph `G(n, r)`

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`G(n, r)` has vertex set `ℤ/nℤ` (represented by `[0, n)`), with an edge between two vertices when
their circular distance is at least `r + 1`.  Two vertices are *non-adjacent* iff they differ by
some `e ∈ [−r, r]` modulo `n` (`near_iff`).  Kernel-proved:

* `indep_card_le` — for `n > 3r` every independent set has at most `r + 1` vertices;
* `arc_indep` — the arc `{0, …, r}` is independent, so `α(G(n, r)) = r + 1`;
* `count_shift_lt` — exact covering count: each vertex lies in exactly `L` of the `n` cyclic
  windows of length `L`;
* `fracColouring_value_ge` — every fractional colouring has value `≥ n / (r + 1)` (weak duality
  with the uniform fractional clique);
* `arcColouring` / `arcColouring_value` — the explicit arc colouring with weights `1/(r+1)` is a
  fractional colouring of value exactly `n / (r + 1)`.

Hence `χ_f(G(n, r)) = n / (r + 1)` in the exact certificate form used by the programme.
-/

open scoped BigOperators

namespace Erdos287
namespace ResearchBankV9
namespace CircularGraph

/-- Non-adjacency ("nearness") in `G(n, r)`: `s ≡ t + e (mod n)` for some `|e| ≤ r`. -/
def Near (n r : ℤ) (s t : ℤ) : Prop := ∃ e : ℤ, |e| ≤ r ∧ n ∣ s - t - e

/-- Circular distance on `ℤ/nℤ`. -/
def cdist (n s t : ℤ) : ℤ := min ((s - t) % n) ((t - s) % n)

/-- Adjacency in `G(n, r)`: circular distance at least `r + 1`. -/
def Adj (n r s t : ℤ) : Prop := r + 1 ≤ cdist n s t

theorem emod_eq_of_dvd_sub {n a e : ℤ} (he0 : 0 ≤ e) (hen : e < n)
    (h : n ∣ a - e) : a % n = e := by
  obtain ⟨k, hk⟩ := h
  rw [show a = e + n * k by linarith, Int.add_mul_emod_self_left, Int.emod_eq_of_lt he0 hen]

/-- Non-adjacency is exactly nearness (for `0 ≤ r < n`). -/
theorem near_iff {n r : ℤ} (hn : 0 < n) (hr : 0 ≤ r) (hrn : r < n) (s t : ℤ) :
    ¬ Adj n r s t ↔ Near n r s t := by
  unfold Adj cdist Near
  constructor
  · intro h
    push_neg at h
    rcases min_choice ((s - t) % n) ((t - s) % n) with hm | hm <;> rw [hm] at h
    · refine ⟨(s - t) % n, ?_, ?_⟩
      · rw [abs_le]; constructor <;> [linarith [Int.emod_nonneg (s - t) hn.ne']; linarith]
      · exact ⟨(s - t) / n, by linarith [Int.emod_add_mul_ediv (s - t) n]⟩
    · refine ⟨-((t - s) % n), ?_, ?_⟩
      · rw [abs_le]; constructor <;> [linarith; linarith [Int.emod_nonneg (t - s) hn.ne']]
      · exact ⟨-((t - s) / n), by linarith [Int.emod_add_mul_ediv (t - s) n]⟩
  · rintro ⟨e, he, hd⟩
    rw [abs_le] at he
    push_neg
    rcases le_or_gt 0 e with h0 | h0
    · have : (s - t) % n = e := emod_eq_of_dvd_sub h0 (by linarith) hd
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · have : (t - s) % n = -e := emod_eq_of_dvd_sub (by linarith) (by linarith)
        (by obtain ⟨k, hk⟩ := hd; exact ⟨-k, by linarith⟩)
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)

/-- The vertex set `[0, n)`. -/
def V (n : ℤ) : Finset ℤ := Finset.Ico 0 n

/-- An independent set of `G(n, r)`. -/
def Indep (n r : ℤ) (S : Finset ℤ) : Prop :=
  S ⊆ V n ∧ ∀ s ∈ S, ∀ t ∈ S, Near n r s t

/-- A finite set of integers with all pairwise differences `≤ r` has at most `r + 1` elements. -/
theorem card_le_of_diam {T : Finset ℤ} {r : ℤ} (hr : 0 ≤ r)
    (hT : ∀ a ∈ T, ∀ b ∈ T, a - b ≤ r) : (T.card : ℤ) ≤ r + 1 := by
  rcases T.eq_empty_or_nonempty with h | hne
  · simp [h]; linarith
  · set m := T.min' hne
    have hsub : T ⊆ Finset.Icc m (m + r) := by
      intro a ha
      rw [Finset.mem_Icc]
      exact ⟨T.min'_le a ha, by linarith [hT a ha m (T.min'_mem hne)]⟩
    have := Finset.card_le_card hsub
    rw [Int.card_Icc] at this
    have h2 : ((m + r + 1 - m).toNat : ℤ) = r + 1 := by
      rw [show m + r + 1 - m = r + 1 by ring]; exact Int.toNat_of_nonneg (by linarith)
    calc (T.card : ℤ) ≤ ((m + r + 1 - m).toNat : ℤ) := by exact_mod_cast this
      _ = r + 1 := h2

/-- **`α(G(n, r)) ≤ r + 1` for `n > 3r`.** -/
theorem indep_card_le {n r : ℤ} (hr : 0 ≤ r) (hn : 3 * r < n) {S : Finset ℤ}
    (hS : Indep n r S) : (S.card : ℤ) ≤ r + 1 := by
  classical
  rcases S.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · simp [h]; linarith
  have hn0 : 0 < n := by linarith
  -- representatives `e_s ∈ [−r, r]` with `s ≡ x + e_s`
  have hrep : ∀ s ∈ S, ∃ e : ℤ, |e| ≤ r ∧ n ∣ s - x - e := fun s hs => hS.2 s hs x hx
  choose! e he hed using hrep
  have hinj : Set.InjOn e S := by
    intro s hs t ht hst
    have h1 := hed s hs
    have h2 := hed t ht
    rw [hst] at h1
    have hd : n ∣ s - t := by
      have := dvd_sub h1 h2
      rwa [show s - x - e t - (t - x - e t) = s - t by ring] at this
    have hs' := hS.1 hs
    have ht' := hS.1 ht
    simp only [V, Finset.mem_Ico] at hs' ht'
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> linarith)
    linarith
  have hdiam : ∀ a ∈ S.image e, ∀ b ∈ S.image e, a - b ≤ r := by
    simp only [Finset.mem_image]
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    obtain ⟨f, hf, hfd⟩ := hS.2 s hs t ht
    have hd : n ∣ e s - e t - f := by
      have := dvd_sub (dvd_sub (hed s hs) (hed t ht)) hfd
      have h' : n ∣ -(s - x - e s - (t - x - e t) - (s - t - f)) := (dvd_neg).2 this
      rwa [show -(s - x - e s - (t - x - e t) - (s - t - f)) = e s - e t - f by ring] at h'
    have hes := he s hs
    have het := he t ht
    rw [abs_le] at hes het hf
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> linarith)
    linarith
  have := card_le_of_diam hr hdiam
  rwa [Finset.card_image_of_injOn hinj] at this

/-- The arc `{0, …, r}`. -/
def arc0 (r : ℤ) : Finset ℤ := Finset.Icc 0 r

/-- **The arc is independent**, so `α(G(n, r)) = r + 1`. -/
theorem arc_indep {n r : ℤ} (hr : 0 ≤ r) (hrn : r < n) : Indep n r (arc0 r) ∧
    ((arc0 r).card : ℤ) = r + 1 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro s hs; simp only [arc0, Finset.mem_Icc, V, Finset.mem_Ico] at *; omega
  · intro s hs t ht
    simp only [arc0, Finset.mem_Icc] at hs ht
    exact ⟨s - t, by rw [abs_le]; constructor <;> linarith, ⟨0, by ring⟩⟩
  · simp only [arc0, Int.card_Icc]; omega

/-! ## Exact covering count -/

/-- **Exact covering count.**  For `0 ≤ L ≤ n`, each `v` satisfies `(v − k) mod n < L` for exactly
`L` shifts `k ∈ [0, n)`. -/
theorem count_shift_lt {n L : ℤ} (hn : 0 < n) (hL : 0 ≤ L) (hLn : L ≤ n) (v : ℤ) :
    (((V n).filter fun k => (v - k) % n < L).card : ℤ) = L := by
  have hbij : ((V n).filter fun k => (v - k) % n < L).card = (Finset.Ico 0 L).card := by
    apply Finset.card_bij (fun k _ => (v - k) % n)
    · intro k hk
      simp only [Finset.mem_filter] at hk
      simp only [Finset.mem_Ico]
      exact ⟨Int.emod_nonneg _ hn.ne', hk.2⟩
    · intro k₁ hk₁ k₂ hk₂ h
      simp only [Finset.mem_filter, V, Finset.mem_Ico] at hk₁ hk₂
      have hd : n ∣ k₂ - k₁ := by
        have := Int.ModEq.dvd (show (v - k₁) ≡ (v - k₂) [ZMOD n] from h)
        rwa [show v - k₂ - (v - k₁) = k₁ - k₂ by ring, ← dvd_neg, neg_sub] at this
      have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> linarith)
      linarith
    · intro d hd
      simp only [Finset.mem_Ico] at hd
      refine ⟨(v - d) % n, ?_, ?_⟩
      · simp only [Finset.mem_filter, V, Finset.mem_Ico]
        have h1 : (v - (v - d) % n) % n = d := by
          apply emod_eq_of_dvd_sub hd.1 (by linarith)
          exact ⟨(v - d) / n, by linarith [Int.emod_add_mul_ediv (v - d) n]⟩
        exact ⟨⟨Int.emod_nonneg _ hn.ne', Int.emod_lt_of_pos _ hn⟩, by rw [h1]; exact hd.2⟩
      · apply emod_eq_of_dvd_sub hd.1 (by linarith)
        exact ⟨(v - d) / n, by linarith [Int.emod_add_mul_ediv (v - d) n]⟩
  rw [hbij, Int.card_Ico]; omega

/-! ## Fractional colourings -/

/-- A fractional colouring of `G(n, r)`: finitely many independent sets with nonnegative
rational weights covering every vertex with total weight `≥ 1`. -/
structure FracColouring (n r : ℤ) where
  /-- The independent sets used. -/
  sets : List (Finset ℤ)
  /-- Their weights. -/
  w : Finset ℤ → ℚ
  /-- Every set used is independent. -/
  indep : ∀ I ∈ sets, Indep n r I
  /-- Nonnegative weights. -/
  nonneg : ∀ I ∈ sets, 0 ≤ w I
  /-- Every vertex is covered. -/
  cover : ∀ v ∈ V n, 1 ≤ (sets.map fun I => if v ∈ I then w I else 0).sum

/-- The value of a fractional colouring. -/
def FracColouring.value {n r : ℤ} (c : FracColouring n r) : ℚ := (c.sets.map c.w).sum

/-- Swapping the order of summation over a list of sets. -/
theorem sum_swap (sets : List (Finset ℤ)) (w : Finset ℤ → ℚ) (Vs : Finset ℤ) :
    ∑ v ∈ Vs, (sets.map fun I => if v ∈ I then w I else 0).sum =
      (sets.map fun I => w I * ((Vs.filter fun v => v ∈ I).card : ℚ)).sum := by
  induction sets with
  | nil => simp
  | cons I t ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
    congr 1
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    ring

/-- **Weak duality: every fractional colouring has value `≥ n / (r + 1)`** (for `n > 3r`). -/
theorem fracColouring_value_ge {n r : ℤ} (hr : 0 ≤ r) (hn : 3 * r < n)
    (c : FracColouring n r) : (n : ℚ) / (r + 1) ≤ c.value := by
  have hn0 : 0 < n := by linarith
  have hr0 : (0 : ℚ) ≤ r := by exact_mod_cast hr
  have hr1 : (0 : ℚ) < r + 1 := by linarith
  have hcov : (n : ℚ) ≤ ∑ v ∈ V n, (c.sets.map fun I => if v ∈ I then c.w I else 0).sum := by
    have hc : ((V n).card : ℤ) = n := by
      simp only [V, Int.card_Ico, sub_zero]; exact Int.toNat_of_nonneg hn0.le
    have : ((V n).card : ℚ) = n := by exact_mod_cast hc
    rw [← this]
    have := Finset.card_nsmul_le_sum (V n)
      (fun v => (c.sets.map fun I => if v ∈ I then c.w I else 0).sum) 1 c.cover
    simpa using this
  rw [sum_swap] at hcov
  have hbound : (c.sets.map fun I => c.w I * (((V n).filter fun v => v ∈ I).card : ℚ)).sum ≤
      (c.sets.map fun I => c.w I * (r + 1)).sum := by
    apply List.sum_le_sum
    intro I hI
    apply mul_le_mul_of_nonneg_left _ (c.nonneg I hI)
    have hsub : ((V n).filter fun v => v ∈ I) ⊆ I := fun x hx => (Finset.mem_filter.1 hx).2
    have := indep_card_le hr hn (c.indep I hI)
    have h2 : ((((V n).filter fun v => v ∈ I).card : ℤ) : ℚ) ≤ ((r + 1 : ℤ) : ℚ) := by
      exact_mod_cast (le_trans (by exact_mod_cast Finset.card_le_card hsub) this)
    push_cast at h2; exact h2
  have : (c.sets.map fun I => c.w I * (r + 1)).sum = c.value * (r + 1) := by
    unfold FracColouring.value
    induction c.sets with
    | nil => simp
    | cons I t ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [div_le_iff₀ hr1]
  linarith

/-- The cyclic arc starting at `k`: `{v ∈ [0,n) : (v − k) mod n ≤ r}`. -/
def arc (n r k : ℤ) : Finset ℤ := (V n).filter fun v => (v - k) % n < r + 1

theorem arc_indep' {n r : ℤ} (hr : 0 ≤ r) (hrn : r < n) (k : ℤ) : Indep n r (arc n r k) := by
  have hn : 0 < n := by linarith
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro s hs t ht
  simp only [arc, Finset.mem_filter] at hs ht
  refine ⟨(s - k) % n - (t - k) % n, ?_, ?_⟩
  · have := Int.emod_nonneg (s - k) hn.ne'
    have := Int.emod_nonneg (t - k) hn.ne'
    rw [abs_le]; constructor <;> linarith
  · refine ⟨(s - k) / n - (t - k) / n, ?_⟩
    linarith [Int.emod_add_mul_ediv (s - k) n, Int.emod_add_mul_ediv (t - k) n]

/-- **The arc colouring**: all `n` cyclic arcs with weight `1/(r+1)`. -/
noncomputable def arcColouring {n r : ℤ} (hr : 0 ≤ r) (hrn : r < n) : FracColouring n r where
  sets := (V n).toList.map (arc n r)
  w := fun _ => 1 / (r + 1)
  indep := by
    intro I hI
    simp only [List.mem_map] at hI
    obtain ⟨k, -, rfl⟩ := hI
    exact arc_indep' hr hrn k
  nonneg := by
    intro I _
    have : (0 : ℚ) ≤ r := by exact_mod_cast hr
    positivity
  cover := by
    intro v hv
    have hn : 0 < n := by linarith
    have hr0 : (0 : ℚ) ≤ r := by exact_mod_cast hr
    have hr1 : (0 : ℚ) < r + 1 := by linarith
    rw [List.map_map, Finset.sum_map_toList]
    simp only [Function.comp_def]
    rw [ Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hcount : (((V n).filter fun k => v ∈ arc n r k).card : ℚ) = r + 1 := by
      have hfil : ((V n).filter fun k => v ∈ arc n r k) =
          (V n).filter fun k => (v - k) % n < r + 1 := by
        ext k; simp [arc, hv]
      rw [hfil]
      have := count_shift_lt hn (by linarith : (0 : ℤ) ≤ r + 1) (by linarith) v
      exact_mod_cast this
    rw [hcount]; field_simp; rfl

/-- **The arc colouring has value exactly `n / (r + 1)`.** -/
theorem arcColouring_value {n r : ℤ} (hr : 0 ≤ r) (hrn : r < n) :
    (arcColouring hr hrn).value = (n : ℚ) / (r + 1) := by
  have hn : 0 < n := by linarith
  simp only [FracColouring.value, arcColouring, List.map_map, Finset.sum_map_toList,
    Function.comp_def, Finset.sum_const, nsmul_eq_mul]
  have hc : ((V n).card : ℤ) = n := by
    simp only [V, Int.card_Ico, sub_zero]; exact Int.toNat_of_nonneg hn.le
  have hc' : ((V n).card : ℚ) = n := by exact_mod_cast hc
  rw [hc']; ring

/-- **`χ_f(G(n, r)) = n / (r + 1)`** in certificate form: a fractional colouring of this value
exists, and none has smaller value. -/
theorem fractional_chromatic_eq {n r : ℤ} (hr : 0 ≤ r) (hn : 3 * r < n) :
    (∃ c : FracColouring n r, c.value = (n : ℚ) / (r + 1)) ∧
      ∀ c : FracColouring n r, (n : ℚ) / (r + 1) ≤ c.value :=
  ⟨⟨arcColouring hr (by linarith), arcColouring_value hr (by linarith)⟩,
   fracColouring_value_ge hr hn⟩

end CircularGraph
end ResearchBankV9
end Erdos287
