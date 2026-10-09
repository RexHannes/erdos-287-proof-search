import RequestProject.Erdos287.PostV71V87

/-!
# Erdős #287 — post-V87 → V90R: compatibility with the audited `PostV71V87` model

**ERDŐS #287 REMAINS OPEN.**

This subtree introduces **no new source model**.  It consumes, unchanged, the exact objects of
`Erdos287.PostV71V87`:

* `Word` — selected denominators `A ⊆ [a, M]`, both endpoints selected, gap-two
  (`gap : ∀ x, a ≤ x → x + 1 ≤ M → x ∈ A ∨ x + 1 ∈ A`);
* `ExactWord` — a `Word` with reciprocal mass exactly one;
* `Word.selRow q` — the selected part of the `q`-row;
* `ExactWord.toCounterexample` / `ofCounterexample` — the two directions of the exact
  equivalence with the project-wide `Erdos287Counterexample`.

The adapter theorems below are the only bridge: `counterexample_iff_exactWord` (an exact
equivalence), the endpoint identifications, and the harmonic width bounds
`e(a - 1) < M ≤ e²(a + 1)` re-exported for exact words.  The *omitted* denominators of a word
are the window positions not in `A`; `omitted_neighbours` restates the gap-two condition in
that language.
-/

open scoped BigOperators

namespace Erdos287.PostV87V90R

open Erdos287 Erdos287.PostV71V87

/-- **Model compatibility (exact equivalence).**  A finite set is an Erdős #287 counterexample
iff it is the selected set of an exact word of the `PostV71V87` model with left endpoint `> 1`. -/
theorem counterexample_iff_exactWord (A : Finset ℕ) :
    Erdos287Counterexample A ↔ ∃ W : ExactWord, 1 < W.a ∧ W.A = A := by
  constructor
  · intro h
    exact ⟨ofCounterexample h, ofCounterexample_one_lt_a h, rfl⟩
  · rintro ⟨W, ha, rfl⟩
    exact W.toCounterexample ha

/-- The left endpoint of the word attached to a counterexample is `min A`. -/
theorem ofCounterexample_a {A : Finset ℕ} (h : Erdos287Counterexample A) :
    (ofCounterexample h).a = A.min' h.nonempty := rfl

/-- The right endpoint of the word attached to a counterexample is `max A`. -/
theorem ofCounterexample_M {A : Finset ℕ} (h : Erdos287Counterexample A) :
    (ofCounterexample h).M = A.max' h.nonempty := rfl

/-- **Harmonic lower width bound** for exact words: `e (a - 1) < M`. -/
theorem ExactWord.exp_lower (W : ExactWord) (ha : 1 < W.a) :
    Real.exp 1 * ((W.a : ℝ) - 1) < W.M := by
  have h := (W.toCounterexample ha).toGap2CE.exp_lower
  rwa [W.gap2_N_eq ha, W.gap2_M_eq ha] at h

/-- **Harmonic upper width bound** for exact words: `M ≤ e² (a + 1)`. -/
theorem ExactWord.exp_upper (W : ExactWord) (ha : 1 < W.a) :
    (W.M : ℝ) ≤ Real.exp 1 ^ 2 * ((W.a : ℝ) + 1) := by
  have h := (W.toCounterexample ha).toGap2CE.exp_upper
  rwa [W.gap2_N_eq ha, W.gap2_M_eq ha] at h

/-- Gap-two in the language of omitted denominators: two consecutive window positions cannot
both be omitted. -/
theorem omitted_neighbours (W : Word) {n : ℕ} (hn : W.a ≤ n) (hn1 : n + 1 ≤ W.M)
    (h0 : n ∉ W.A) (h1 : n + 1 ∉ W.A) : False :=
  (W.gap n hn hn1).elim h0 h1

/-- Every selected denominator of a `q`-row is in the selected row `selRow q`. -/
theorem mem_selRow_iff (W : Word) {q n : ℕ} : n ∈ W.selRow q ↔ n ∈ W.A ∧ q ∣ n := by
  simp [Word.selRow]

end Erdos287.PostV87V90R
