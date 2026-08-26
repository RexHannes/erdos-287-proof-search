import RequestProject.Erdos287.Blocker

/-!
# Erdős Problem #287 — range-covering blocker pairs and finite chain certificates

Target 6.  A single blocker pair at `x` (with excluded prime powers dividing `x` and
`x+1`) already refutes every `Gap2CE` whose maximum `M` lies in the range
`[x+2, ⌊e·x⌋]` (`Gap2CE.blockerPair_covers_range`): the analytic lower bound
`e·(N-1) < M ≤ e·x` forces `N ≤ x`, so `x, x+1 ∈ [N, M]`.

We then bundle a list of such pairs into a finite **chain certificate** whose covered
`M`-ranges overlap to cover a whole interval `[lo, hi]` (`BlockerChain`), and prove that
any such certificate refutes every `Gap2CE` with `M ∈ [lo, hi]` (`BlockerChain.refutes`).
-/

open scoped BigOperators

namespace Erdos287

/-
`ExcludedPP` is monotone downward in the window bound `M`.
-/
theorem ExcludedPP.mono_M {M M' q : ℕ} (h : ExcludedPP M q) (hM : M' ≤ M) :
    ExcludedPP M' q := by
  obtain ⟨ p, e, hp, he, rfl, hpC ⟩ := h;
  exact ⟨ p, e, hp, he, rfl, lt_of_le_of_lt ( C_mono ( Nat.div_le_div_right hM ) ) hpC ⟩

namespace Gap2CE

variable (ce : Gap2CE)

/-
**Blocker pair covers a range.**  A blocker pair at `x` refutes every `Gap2CE`
whose maximum satisfies `x + 2 ≤ M` and `(M : ℝ) ≤ e · x` (i.e. `M ≤ ⌊e·x⌋`).
-/
theorem blockerPair_covers_range {x q₁ q₂ : ℕ}
    (hMlow : x + 2 ≤ ce.M)
    (hMhigh : (ce.M : ℝ) ≤ Real.exp 1 * x)
    (hq1 : ExcludedPP ce.M q₁) (hq2 : ExcludedPP ce.M q₂)
    (hd1 : q₁ ∣ x) (hd2 : q₂ ∣ x + 1) : False := by
  have := @Gap2CE.excludedPP_blockerPair;
  contrapose! this;
  refine' ⟨ ce, x, q₁, q₂, _, _, hq1, hq2, hd1, hd2, trivial ⟩;
  · exact Nat.le_of_lt_succ ( by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ Real.add_one_le_exp 1, show ( ce.M : ℝ ) ≥ x + 2 by norm_cast, Gap2CE.exp_lower ce ] );
  · linarith

end Gap2CE

/-! ## Finite chain certificates -/

/-- A single certified blocker pair, together with the top `Mmax` of the `M`-range it
covers.  `hrange` guarantees `Mmax ≤ ⌊e·x⌋`, so the pair refutes every `Gap2CE` with
`x + 2 ≤ M ≤ Mmax`. -/
structure ChainLink where
  /-- The blocking integer. -/
  x : ℕ
  /-- Top of the covered `M`-range. -/
  Mmax : ℕ
  /-- Prime power dividing `x`. -/
  q₁ : ℕ
  /-- Prime power dividing `x+1`. -/
  q₂ : ℕ
  /-- `q₁ ∣ x`. -/
  hd1 : q₁ ∣ x
  /-- `q₂ ∣ x+1`. -/
  hd2 : q₂ ∣ x + 1
  /-- `q₁` is excluded on `[1, Mmax]`. -/
  hexc1 : ExcludedPP Mmax q₁
  /-- `q₂` is excluded on `[1, Mmax]`. -/
  hexc2 : ExcludedPP Mmax q₂
  /-- `Mmax ≤ ⌊e·x⌋`. -/
  hrange : (Mmax : ℝ) ≤ Real.exp 1 * x

/-- The `M`-range covered by a single link: `[x+2, Mmax]`. -/
def ChainLink.covers (L : ChainLink) (M : ℕ) : Prop := L.x + 2 ≤ M ∧ M ≤ L.Mmax

/-
A single link refutes every `Gap2CE` whose maximum it covers.
-/
theorem ChainLink.refutes (L : ChainLink) (ce : Gap2CE) (h : L.covers ce.M) : False := by
  obtain ⟨hlo, hhi⟩ := h;
  apply Gap2CE.blockerPair_covers_range;
  exact hlo;
  exact le_trans ( Nat.cast_le.mpr hhi ) L.hrange;
  exact ExcludedPP.mono_M L.hexc1 hhi;
  exact ExcludedPP.mono_M L.hexc2 hhi;
  · exact L.hd1;
  · exact L.hd2

/-- A list of links covers `M` if some member does. -/
def Covers (links : List ChainLink) (M : ℕ) : Prop := ∃ L ∈ links, L.covers M

/-
If a list of links covers `ce.M`, it refutes the `Gap2CE`.
-/
theorem covers_refutes (links : List ChainLink) (ce : Gap2CE)
    (h : Covers links ce.M) : False := by
  exact h.elim fun L hL => L.refutes ce hL.2

/-- `chainFrom lo links hi`: the links, read in order, cover `[lo, hi]` with no gaps —
each link starts no later than the running lower bound, and its `Mmax + 1` becomes the
next lower bound. -/
def chainFrom (lo : ℕ) : List ChainLink → ℕ → Prop
  | [], hi => hi < lo
  | L :: rest, hi => L.x + 2 ≤ lo ∧ chainFrom (L.Mmax + 1) rest hi

/-
A chained list covers every point of `[lo, hi]`.
-/
theorem chainFrom_covers :
    ∀ (links : List ChainLink) (lo hi M : ℕ),
      chainFrom lo links hi → lo ≤ M → M ≤ hi → Covers links M := by
  intro links lo hi M h_chain hlo hhi
  induction' links with L rest ih generalizing lo hi;
  · grind +locals;
  · cases h_chain;
    by_cases hM : M ≤ L.Mmax;
    · exact ⟨ L, List.mem_cons_self, ⟨ by linarith, hM ⟩ ⟩;
    · exact Exists.elim ( ih _ _ ‹_› ( by linarith ) ( by linarith ) ) fun x hx => ⟨ x, List.mem_cons_of_mem _ hx.1, hx.2 ⟩

/-- A finite chain certificate: a list of blocker links whose covered ranges chain to
cover the whole interval `[lo, hi]`. -/
structure BlockerChain where
  /-- The certified blocker links, in increasing order. -/
  links : List ChainLink
  /-- Lower endpoint of the covered interval. -/
  lo : ℕ
  /-- Upper endpoint of the covered interval. -/
  hi : ℕ
  /-- The links chain to cover `[lo, hi]`. -/
  chain : chainFrom lo links hi

/-
**Any valid chain certificate refutes every `Gap2CE` with `M ∈ [lo, hi]`.**
-/
theorem BlockerChain.refutes (BC : BlockerChain) (ce : Gap2CE)
    (hlo : BC.lo ≤ ce.M) (hhi : ce.M ≤ BC.hi) : False := by
  convert covers_refutes BC.links ce ( chainFrom_covers BC.links BC.lo BC.hi ce.M BC.chain hlo hhi ) using 1

end Erdos287