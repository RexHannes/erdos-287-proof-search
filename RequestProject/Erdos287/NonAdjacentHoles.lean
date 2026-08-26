import RequestProject.Erdos287.SFTAudit
import RequestProject.Erdos287.CeilingCRT

/-!
# Erdős Problem #287 — non-adjacent holes do **not** force a contradiction

The certified blocker mechanism (`Gap2CE.blockerPair_contradiction`) refutes a gap-`≤2`
counterexample only from **two adjacent holes** `x, x+1`: this is the unique block
forbidden by the local rule `holes_isolated` (equivalently `LocallyAdmissible`, the
nearest-neighbour subshift that forbids the 2-block `(hole, hole)`).

This file investigates whether two holes at **distance `d > 1`** can ever force a
contradiction when combined with `∑ 1/a = 1` and the p-adic / top-layer kernel.

## Verdict

**No.**  At the level of the local gap constraint — which is *all* that
`blockerPair_contradiction` uses — two holes at any distance `d ≥ 2` are compatible with
every gap `≤ 2`.  We certify explicit local models (`twoHoleWord`, `altWord`,
`mod3HoleWord`) that are `LocallyAdmissible` and yet contain the prescribed holes, and we
show the sharp contrast that **only** `d = 1` is inadmissible
(`twoHoleWord_one_not_admissible`).

The arithmetic layer cannot rescue the argument either: the CRT mechanism can *produce*
two holes at any prescribed distance `d` (`exists_crt_at_distance`), but distance-`d`
holes with `d ≥ 2` are non-adjacent, so `blockerPair_contradiction` never fires.  The only
surviving local contradiction is the adjacent one already certified.

See `NONADJACENT_HOLES.md` for the written analysis.
-/

open scoped BigOperators

namespace Erdos287

/-! ## 1. Two holes at a fixed distance `d` -/

/-- The membership word with holes **exactly** at positions `x` and `x + d`
(every other position is `inA`). -/
def twoHoleWord (x d n : ℕ) : Cell :=
  if n = x ∨ n = x + d then Cell.hole else Cell.inA

/-- Both prescribed holes are genuinely present. -/
theorem twoHoleWord_has_two_holes (x d : ℕ) :
    twoHoleWord x d x = Cell.hole ∧ twoHoleWord x d (x + d) = Cell.hole := by
  unfold twoHoleWord; constructor <;> simp

/-- **Refutation of the naive distance-`d` claim (local layer).**
For every `d ≥ 2`, two holes at distance `d` satisfy the local gap rule: the word with
holes exactly at `x` and `x + d` is `LocallyAdmissible`.  Hence the gap-`≤2` constraint
alone cannot rule out holes at distance `d`. -/
theorem twoHoleWord_locallyAdmissible (x : ℕ) {d : ℕ} (hd : 2 ≤ d) :
    LocallyAdmissible (twoHoleWord x d) := by
  intro n
  unfold twoHoleWord
  rintro ⟨h1, h2⟩
  split_ifs at h1 h2 with c1 c2
  all_goals omega

/-- **Adjacency is the unique local contradiction.**  For `d = 1` the two holes are
adjacent, so the word is *not* `LocallyAdmissible`. -/
theorem twoHoleWord_one_not_admissible (x : ℕ) :
    ¬ LocallyAdmissible (twoHoleWord x 1) := by
  intro h
  exact h x ⟨by simp [twoHoleWord], by simp [twoHoleWord]⟩

/-- **Main negative answer (Target 1).**  For every distance `d ≥ 2` there is a locally
admissible word exhibiting two holes at distance exactly `d`.  Since
`blockerPair_contradiction` is derived purely from the local rule (`holes_isolated`),
no distance-`d ≥ 2` analogue of it can hold: the gap-`≤2` kernel cannot refute a
configuration with holes at distance `d`. -/
theorem no_nonadjacent_local_contradiction {d : ℕ} (hd : 2 ≤ d) (x : ℕ) :
    ∃ w : ℕ → Cell, LocallyAdmissible w ∧ w x = Cell.hole ∧ w (x + d) = Cell.hole :=
  ⟨twoHoleWord x d, twoHoleWord_locallyAdmissible x hd,
    (twoHoleWord_has_two_holes x d).1, (twoHoleWord_has_two_holes x d).2⟩

/-- The whole requested band `d ∈ {2, …, 246}` is covered by the generic result:
every such distance admits a local model. -/
theorem distance_band_admissible (x : ℕ) :
    ∀ d ∈ Finset.Icc 2 246, LocallyAdmissible (twoHoleWord x d) :=
  fun _ hd => twoHoleWord_locallyAdmissible x (Finset.mem_Icc.mp hd).1

/-! ## 2. A block of many forced holes inside a short interval -/

/-- **Arbitrarily long blocks of forced holes are admissible.**  For every `k` there is a
set of `k` holes of the (locally admissible) alternating word `altWord`, all lying inside
the interval `[0, 2k]`.  Taking `k = 123` packs `123` forced holes into an interval of
length `246`, none of them adjacent. -/
theorem many_holes_block (k : ℕ) :
    ∃ S : Finset ℕ, S.card = k ∧ (∀ n ∈ S, altWord n = Cell.hole) ∧ (∀ n ∈ S, n ≤ 2 * k) := by
  refine ⟨(Finset.range k).image (fun i => 2 * i + 1), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab; dsimp only at hab; omega
  · intro n hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
    have hodd : (2 * i + 1) % 2 = 1 := by omega
    simp [altWord, hodd]
  · intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    have : i < k := Finset.mem_range.mp hi
    omega

/-- The alternating word is `LocallyAdmissible` (re-export from the SFT audit); it realizes
the densest possible admissible hole set — an entire parity class. -/
theorem altWord_block_locallyAdmissible : LocallyAdmissible altWord :=
  altWord_locallyAdmissible

/-- Any two distinct holes of the alternating word are non-adjacent: forced holes may fill
an entire parity class yet never become adjacent. -/
theorem altWord_holes_nonadjacent {m n : ℕ}
    (hm : altWord m = Cell.hole) (hn : altWord n = Cell.hole) :
    m + 1 ≠ n ∧ n + 1 ≠ m := by
  unfold altWord at hm hn
  split_ifs at hm hn
  omega

/-! ## 3. Forced holes in both parity classes, densely -/

/-- Holes at every multiple of `3`: this hits **both** parity classes (`0, 6, 12, …` even
and `3, 9, 15, …` odd) at pairwise distance `3`. -/
def mod3HoleWord (n : ℕ) : Cell := if n % 3 = 0 then Cell.hole else Cell.inA

/-- The `mod 3` hole pattern is `LocallyAdmissible`: dense holes in both parity classes are
compatible with all gaps `≤ 2`. -/
theorem mod3HoleWord_locallyAdmissible : LocallyAdmissible mod3HoleWord := by
  intro n
  unfold mod3HoleWord
  rintro ⟨h1, h2⟩
  split_ifs at h1 h2
  all_goals omega

/-- The `mod 3` pattern really does place forced holes in both parity classes. -/
theorem mod3HoleWord_both_parities :
    (∃ n, Even n ∧ mod3HoleWord n = Cell.hole) ∧
    (∃ n, Odd n ∧ mod3HoleWord n = Cell.hole) := by
  refine ⟨⟨0, by decide, by decide⟩, ⟨3, by decide, by decide⟩⟩

/-! ## 4. Distance / gcd controlled holes: the arithmetic mechanism cannot close -/

/-- **CRT interval-residue lemma at distance `d`.**  Given coprime `Q₁, Q₂ ≥ 1` with a
window long enough (`Q₁·Q₂ + d ≤ M - N + 1`), there is an `x` with `N ≤ x`, `x + d ≤ M`,
`Q₁ ∣ x`, and `Q₂ ∣ (x + d)`.

This is the distance-`d` analogue of `exists_crt_adjacent`: the arithmetic mechanism can
*produce* two hole-forcing multiples at any prescribed distance `d`.  For `d = 1` this is
exactly the adjacent case that fuels `blockerPair_contradiction`; for `d ≥ 2` the two
holes are non-adjacent, so no contradiction follows. -/
theorem exists_residue_in_interval {N m : ℕ} (hm : 1 ≤ m) (c : ℕ) :
    ∃ x, N ≤ x ∧ x < N + m ∧ x ≡ c [MOD m] := by
  have hc : c % m ∈ Finset.range m := Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
  rw [← Nat.image_Ico_mod N m] at hc
  obtain ⟨x, hx, hxm⟩ := Finset.mem_image.mp hc
  rw [Finset.mem_Ico] at hx
  exact ⟨x, hx.1, hx.2, hxm⟩

theorem exists_crt_at_distance {N M Q1 Q2 d : ℕ} (hcop : Nat.Coprime Q1 Q2)
    (h1 : 1 ≤ Q1) (h2 : 1 ≤ Q2) (hd : 1 ≤ d) (hle : Q1 * Q2 + d ≤ M - N + 1) :
    ∃ x, N ≤ x ∧ x + d ≤ M ∧ Q1 ∣ x ∧ Q2 ∣ (x + d) := by
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop 0 (Q2 - d % Q2)
  have hmpos : 1 ≤ Q1 * Q2 := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨x, hxlo, hxhi, hxk⟩ := exists_residue_in_interval (N := N) (m := Q1 * Q2) hmpos k
  refine ⟨x, hxlo, by omega, ?_, ?_⟩
  · have hx1 : x ≡ k [MOD Q1] := hxk.of_dvd ⟨Q2, rfl⟩
    exact (Nat.modEq_zero_iff_dvd).1 (hx1.trans hk1)
  · have hx2 : x ≡ k [MOD Q2] := hxk.of_dvd ⟨Q1, by ring⟩
    have hxk2 : x ≡ Q2 - d % Q2 [MOD Q2] := hx2.trans hk2
    have hdd : x + d ≡ (Q2 - d % Q2) + d [MOD Q2] := hxk2.add_right d
    have hz : (Q2 - d % Q2) + d ≡ 0 [MOD Q2] := by
      have hdlt : d % Q2 < Q2 := Nat.mod_lt _ (by omega)
      have h3 : (Q2 - d % Q2) + d ≡ (Q2 - d % Q2) + d % Q2 [MOD Q2] :=
        Nat.ModEq.add_left _ (Nat.mod_modEq d Q2).symm
      have h4 : (Q2 - d % Q2) + d % Q2 = Q2 := by omega
      rw [h4] at h3
      exact h3.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl)
    exact (Nat.modEq_zero_iff_dvd).1 (hdd.trans hz)

/-- **The gcd of the two hole positions is unconstrained.**  A local model with holes at
`x` and `x + d` exists for every `d ≥ 2` regardless of `Nat.gcd x (x + d)`; two explicit
witnesses (coprime endpoints and non-coprime endpoints) show both extremes occur. -/
theorem gcd_controlled_models :
    -- coprime endpoints: gcd (6) (6+5) = 1
    (LocallyAdmissible (twoHoleWord 6 5) ∧ Nat.gcd 6 (6 + 5) = 1) ∧
    -- non-coprime endpoints: gcd (6) (6+6) = 6
    (LocallyAdmissible (twoHoleWord 6 6) ∧ Nat.gcd 6 (6 + 6) = 6) := by
  refine ⟨⟨twoHoleWord_locallyAdmissible 6 (by norm_num), by decide⟩,
    ⟨twoHoleWord_locallyAdmissible 6 (by norm_num), by decide⟩⟩

end Erdos287
