import RequestProject.Erdos287.Blocker
import RequestProject.Erdos287.Counterexample

/-!
# Erdős Problem #287 — audit of the Fable SFT / follower-graph proposal

This file makes precise, and machine-checks, the audit conclusion:

**The certified kernel splits into a genuinely *local* (SFT-style) gap layer and an
essentially *non-local* arithmetic layer.**

* Local (SFT-valid) layer: `holes_isolated` / `blockerPair_contradiction` say that, over
  the two-letter alphabet `{inA, hole}`, the membership word of a `Gap2CE` avoids the
  single forbidden 2-block `(hole, hole)`.  This is a nearest-neighbour subshift of finite
  type.  We formalize its admissibility (`Gap2CE.word_locallyAdmissible`), the dichotomy
  half **(A)** "boundedly many holes" (`Gap2CE.two_mul_holes_le`), and the dichotomy half
  **(B)** "a cycle is a periodic symbolic fake" (`altWord_periodic`,
  `altWord_locallyAdmissible`) — the local subshift is nonempty and has periodic points,
  so the local rules alone cannot refute a counterexample.

* Non-local arithmetic layer: `topLayer_congruence`, `primePower_window_exclusion`,
  `Gap2CE.primeFree` depend essentially on the global parameters `M`, `N`, `q = pᵉ`,
  `⌊M/q⌋` and the top-layer maximum.  Two obstructions to a *fixed finite* SFT alphabet:
  the residue modulus `p` ranges over **all** primes (`modulus_alphabet_unbounded`), and
  the exclusion predicate is **not scale-invariant** — it flips as the window grows
  (`excludedPP_three_two` vs `not_excludedPP_four_two`, and `ExcludedPP.mono_M`).

Hence Fable's literal SFT schema does not match the certified kernel; the correct sound
replacement is the interval / blocker-pair-chain certificate graph already formalized in
`Chain.lean` (`ChainLink`, `chainFrom`, `BlockerChain`).  See `SFT_AUDIT.md`.
-/

open scoped BigOperators

namespace Erdos287

/-! ## The two-letter membership alphabet and the local rule -/

/-- The SFT alphabet: each integer position is either in `A` or is a hole. -/
inductive Cell where
  | inA
  | hole
deriving DecidableEq

/-- Local admissibility for the gap subshift: the 2-block `(hole, hole)` is forbidden
everywhere. -/
def LocallyAdmissible (w : ℕ → Cell) : Prop :=
  ∀ n, ¬ (w n = Cell.hole ∧ w (n + 1) = Cell.hole)

/-! ## The local (SFT-valid) layer of a `Gap2CE` -/

namespace Gap2CE

variable (ce : Gap2CE)

/-- The membership word of the counterexample. -/
def word (n : ℕ) : Cell := if n ∈ ce.A then Cell.inA else Cell.hole

@[simp] lemma word_eq_hole_iff {n : ℕ} : ce.word n = Cell.hole ↔ n ∉ ce.A := by
  unfold Gap2CE.word; aesop;

/-
**Local rule holds inside the window.**  On `[N, M]` the membership word avoids the
forbidden block `(hole, hole)` — this is exactly `holes_isolated` in symbolic form.
-/
theorem word_locallyAdmissible {n : ℕ} (hn0 : ce.N ≤ n) (hn1 : n + 1 ≤ ce.M) :
    ¬ (ce.word n = Cell.hole ∧ ce.word (n + 1) = Cell.hole) := by
  exact fun h => by have := ce.holes_isolated n hn0 hn1; aesop;

/-- The holes of the window `[N, M]`. -/
def holes : Finset ℕ := (Finset.Icc ce.N ce.M).filter (fun n => n ∉ ce.A)

/-
Each window hole maps (via `n ↦ n+1`) into `A`.
-/
theorem holes_card_le_A : ce.holes.card ≤ ce.A.card := by
  convert Finset.card_le_card ( show Finset.image ( fun n => n + 1 ) ce.holes ⊆ ce.A from ?_ ) using 1;
  · rw [ Finset.card_image_of_injective _ Nat.succ_injective ];
  · intro x hx;
    obtain ⟨ n, hn, rfl ⟩ := Finset.mem_image.mp hx;
    apply ce.forced_right;
    · exact Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1;
    · exact Nat.succ_le_of_lt ( lt_of_le_of_ne ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.2 ) ( by rintro rfl; exact Finset.mem_filter.mp hn |>.2 ( ce.M_mem ) ) );
    · exact Finset.mem_filter.mp hn |>.2

/-
**Dichotomy (A): boundedly many holes.**  Because no two window positions are both
holes, holes occupy at most half of the window `[N, M]`.
-/
theorem two_mul_holes_le : 2 * ce.holes.card ≤ ce.M + 1 - ce.N := by
  rw [ two_mul ];
  convert Nat.le_trans ( add_le_add_left ( Gap2CE.holes_card_le_A ce ) _ ) _;
  rw [ add_comm, ← Finset.card_union_of_disjoint ];
  · convert Finset.card_le_card ( show ce.holes ∪ ce.A ⊆ Finset.Icc ce.N ce.M from ?_ ) using 1;
    · simp +arith +decide [ Nat.card_Icc ];
    · exact Finset.union_subset ( Finset.filter_subset _ _ ) fun x hx => ce.mem_Icc hx;
  · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_filter.mp hx₁ |>.2 hx₂

end Gap2CE

/-! ## Dichotomy (B): the local subshift has periodic fakes -/

/-- The `2`-periodic alternating word `inA, hole, inA, hole, …`. -/
def altWord (n : ℕ) : Cell := if n % 2 = 0 then Cell.inA else Cell.hole

/-
The alternating word is `2`-periodic.
-/
theorem altWord_periodic : Function.Periodic altWord 2 := by
  intro n; unfold altWord; simp +decide [ Nat.add_mod ] ;

/-
**Dichotomy (B): a cycle is a symbolic fake.**  The alternating word satisfies the
local rule everywhere, yet is a mere periodic pattern with no arithmetic content — a cycle
in the follower graph of the *local* subshift does not encode a genuine counterexample.
-/
theorem altWord_locallyAdmissible : LocallyAdmissible altWord := by
  intro n; unfold altWord; split_ifs <;> norm_num;
  omega

/-
The local subshift is nontrivial: the periodic fake really does contain holes.
-/
theorem altWord_has_hole : ∃ n, altWord n = Cell.hole := by
  exists 1

/-! ## The non-local arithmetic layer: obstructions to a fixed finite alphabet -/

/-
**Unbounded modulus alphabet.**  The residue modulus `p` in the congruence /
window-exclusion rules ranges over arbitrarily large primes, so no fixed finite alphabet
`ℤ/p` captures the arithmetic layer.
-/
theorem modulus_alphabet_unbounded : ∀ B : ℕ, ∃ p, B < p ∧ p.Prime := by
  exact fun B => Exists.imp ( by tauto ) ( Nat.exists_infinite_primes ( B + 1 ) )

/-
**Scale-dependence, small window.**  At `M = 3`, `q = 2` is excluded (`⌊3/2⌋ = 1`,
`C 1 = 1 < 2`).
-/
theorem excludedPP_three_two : ExcludedPP 3 2 := by
  refine ⟨2, 1, Nat.prime_two, le_refl 1, by norm_num, ?_⟩
  show C (3 / 2) < (2 : ℤ)
  norm_num [show (3 : ℕ) / 2 = 1 from rfl, C_one]

/-
**Scale-dependence, larger window.**  At `M = 4`, `q = 2` is *not* excluded
(`⌊4/2⌋ = 2`, `C 2 = 3 ≥ 2`).  Together with `excludedPP_three_two`, the exclusion rule is
not scale-invariant, so it is not a fixed local window constraint.
-/
theorem not_excludedPP_four_two : ¬ ExcludedPP 4 2 := by
  rintro ⟨ p, e, hp, he, heq, hC ⟩;
  rcases e with ( _ | _ | e ) <;> simp_all +decide [ eq_comm, Nat.Prime.pow_eq_iff ]

end Erdos287