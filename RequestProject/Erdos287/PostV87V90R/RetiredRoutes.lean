import RequestProject.Erdos287.PostV87V90R.ModelCompatibility

/-!
# Erdős #287 — post-V87 → V90R: V88 retained facts, retired consumers, closure-first failures

**ERDŐS #287 REMAINS OPEN.**

No V88 source document is present in the repository.  Only the following *elementary* V88
statements could be reconstructed with complete proofs; every other V88 item is recorded as
OPEN/INFORMAL in the report (no theorem is invented for it).

## V88 retained exact facts (BANK)

* `conductor_replication` — an absent modulus replicates to all its multiples;
* `primePower_replication` — an absent prime power `p^e` replicates to all `p^f`, `f ≥ e`;
* `guardOwner_unique` — re-export of the audited `Word.guard_triple_owner_unique`;
* `lcm_transfer` — absence transfers from either factor to the lcm.

## V88 negative conclusion: the single-minimal-grid / global-overload architecture

`isolated_omissions_realizable`: *any* pattern of omissions with no two consecutive interior
positions is realised by a genuine gap-two word.  Consequently (`single_grid_realizable`) the
forced omissions of one absent modulus `d ≥ 2` never exceed the gap-two capacity, and
(`even_multigrid_realizable`) neither does the union of the forced omissions of any family of
even moduli.  This is the exact capacity comparison behind the retirement of
"single-grid global overload" and "multi-grid overload of unchanged global capacity" as
sufficient consumers.

## Closure-first failures (KILL regression facts)

* `exterior_obligations_do_not_combine` — individually satisfiable exterior obligations need
  not have a common witness;
* `proximity_density_no_contact` — proximity plus density does not give guard contact.

## Retired owner

* `crossScale_retired_equiv_tail` — the audited `CrossScaleSynchronization287 M0` is
  *equivalent* to tail exclusion; it is an overstrong owner, not a reduction.
-/

open scoped BigOperators

namespace Erdos287.PostV87V90R

open Erdos287 Erdos287.PostV71V87

/-! ## V88 retained exact facts -/

/-- **Conductor replication.**  If `d` is absent from a word, so is every multiple of `d`. -/
theorem conductor_replication (W : Word) {d : ℕ} (hd : W.Absent d) (k : ℕ) :
    W.Absent (d * k) :=
  fun n hn h => hd n hn (dvd_trans (dvd_mul_right d k) h)

/-- **Prime-power replication.**  An absent `p^e` forces every `p^f` with `f ≥ e` absent. -/
theorem primePower_replication (W : Word) {p e f : ℕ} (hd : W.Absent (p ^ e)) (hf : e ≤ f) :
    W.Absent (p ^ f) :=
  fun n hn h => hd n hn (dvd_trans (pow_dvd_pow p hf) h)

/-- **Guard-owner uniqueness** (re-export): a guard triple centred at `y` contains at most one
multiple of a modulus `ℓ ≥ 3`. -/
theorem guardOwner_unique {ℓ y u w : ℕ} (hℓ : 3 ≤ ℓ)
    (hu : y ≤ u + 1 ∧ u ≤ y + 1) (hw : y ≤ w + 1 ∧ w ≤ y + 1) (hud : ℓ ∣ u) (hwd : ℓ ∣ w) :
    u = w :=
  Word.guard_triple_owner_unique hℓ hu hw hud hwd

/-- **LCM transfer.**  Absence of either factor transfers to the lcm. -/
theorem lcm_transfer (W : Word) {d₁ d₂ : ℕ} (h : W.Absent d₁ ∨ W.Absent d₂) :
    W.Absent (Nat.lcm d₁ d₂) := by
  rcases h with h | h
  · exact fun n hn hl => h n hn (dvd_trans (Nat.dvd_lcm_left d₁ d₂) hl)
  · exact fun n hn hl => h n hn (dvd_trans (Nat.dvd_lcm_right d₁ d₂) hl)

/-! ## Capacity comparison: isolated omission patterns are always realisable -/

/-- **Exact capacity theorem.**  For any window `[a, M]` (`0 < a ≤ M`) and any predicate `O`
with no two consecutive true values, there is a gap-two word on `[a, M]` whose omitted interior
positions are exactly those satisfying `O`. -/
theorem isolated_omissions_realizable {a M : ℕ} (ha : 0 < a) (haM : a ≤ M) (O : ℕ → Prop)
    [DecidablePred O] (hiso : ∀ n, O n → ¬ O (n + 1)) :
    ∃ W : Word, W.a = a ∧ W.M = M ∧ ∀ n, a < n → n < M → (n ∈ W.A ↔ ¬ O n) := by
  refine ⟨{ A := (Finset.Icc a M).filter (fun n => n = a ∨ n = M ∨ ¬ O n)
            a := a, M := M, a_pos := ha
            sub := Finset.filter_subset _ _
            a_mem := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨le_rfl, haM⟩, Or.inl rfl⟩
            M_mem := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨haM, le_rfl⟩, Or.inr (Or.inl rfl)⟩
            gap := ?_ }, rfl, rfl, ?_⟩
  · intro x hx hxM
    by_cases h : O x
    · right
      exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, hxM⟩, Or.inr (Or.inr (hiso x h))⟩
    · left
      exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hx, by omega⟩, Or.inr (Or.inr h)⟩
  · intro n han hnM
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨-, h | h | h⟩
      · omega
      · omega
      · exact h
    · intro h; exact ⟨⟨by omega, by omega⟩, Or.inr (Or.inr h)⟩

/-- **Single-grid insufficiency.**  The forced omissions of one modulus `d ≥ 2` (all interior
multiples of `d`) are realised by a gap-two word: a single grid never overloads the gap-two
capacity. -/
theorem single_grid_realizable {a M d : ℕ} (ha : 0 < a) (haM : a ≤ M) (hd : 2 ≤ d) :
    ∃ W : Word, W.a = a ∧ W.M = M ∧ ∀ n, a < n → n < M → (n ∈ W.A ↔ ¬ d ∣ n) :=
  isolated_omissions_realizable ha haM (fun n => d ∣ n) fun n h1 h2 => by
    have := (Nat.dvd_add_right h1).1 h2
    have := Nat.le_of_dvd one_pos this
    omega

/-- **Multi-grid insufficiency (even moduli).**  For any finite family `D` of even moduli, the
union of their forced omissions is realised by a gap-two word: multi-grid overload does not
automatically overload the unchanged global gap-two capacity. -/
theorem even_multigrid_realizable {a M : ℕ} (ha : 0 < a) (haM : a ≤ M) (D : Finset ℕ)
    (hD : ∀ d ∈ D, 2 ∣ d) :
    ∃ W : Word, W.a = a ∧ W.M = M ∧
      ∀ n, a < n → n < M → (n ∈ W.A ↔ ¬ ∃ d ∈ D, d ∣ n) :=
  isolated_omissions_realizable ha haM (fun n => ∃ d ∈ D, d ∣ n) fun n ⟨d, hd, h1⟩ ⟨d', hd', h2⟩ => by
    have e1 : 2 ∣ n := dvd_trans (hD d hd) h1
    have e2 : 2 ∣ n + 1 := dvd_trans (hD d' hd') h2
    omega

/-! ## Closure-first failures (regression facts) -/

/-- **Individual exterior obligations do not combine.**  Each prime `p ∈ {2,3}` has a
witness `n ∈ [2,3]` with `p ∤ n`, but no `n ∈ [2,3]` is coprime to both. -/
theorem exterior_obligations_do_not_combine :
    (∀ p ∈ ({2, 3} : Finset ℕ), ∃ n ∈ Finset.Icc 2 3, ¬ p ∣ n) ∧
      ¬ ∃ n ∈ Finset.Icc 2 3, ∀ p ∈ ({2, 3} : Finset ℕ), ¬ p ∣ n := by
  decide

/-- **Proximity plus density does not give contact.**  The even numbers of `[0,20]` have
density `> 1/2` and every window point is within distance `1` of one of them, yet the target
`7` is not hit. -/
theorem proximity_density_no_contact :
    let S := (Finset.range 21).filter (fun n => 2 ∣ n)
    (∀ x ∈ Finset.range 21, ∃ s ∈ S, x ≤ s + 1 ∧ s ≤ x + 1) ∧ 21 ≤ 2 * S.card ∧ 7 ∉ S := by
  decide

/-! ## Retired owner -/

/-- **Retired owner.**  `CrossScaleSynchronization287 M0` is *equivalent* to tail exclusion
(audited `crossScale_iff_tail`); it is overstrong and is not a conceptual reduction. -/
theorem crossScale_retired_equiv_tail (M0 : ℕ) :
    CrossScaleSynchronization287 M0 ↔ ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M → False :=
  crossScale_iff_tail M0

end Erdos287.PostV87V90R
