import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V8 §2F: the exact active-residue path DP

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A finite-state reference DP for the exact ENTRY system on a path of Boolean coordinates.
Each owner has integer weights on absolute positions and a modulus; its constraint is
`∑_i b_i w(i) ≡ 0 (mod d)`; the path constraint is no-`00`.  The DP state at a cut is

  `(previous bit, active owner residue vector)`.

Kernel-proved:

* `feasible_eq_of_state_eq` — same previous bit + same complete residue vector (+ both prefixes
  internally valid, same length) ⇒ **identical feasible suffix sets**;
* `forget_owner_of_final_zero` — an owner may be forgotten after its final coordinate when its
  residue is `0`; `owner_final_nonzero_infeasible` — with nonzero residue nothing is feasible;
* `forget_before_final_unsound`, `forget_nonzero_unsound` — counterfixtures: forgetting too early
  or with nonzero residue changes the feasible set;
* `same_bit_not_same_continuation` — **counterexample**: same previous bit does **not** imply the
  same continuation feasibility (the boundary-bit-only DP is not an exact interface);
* `resource_exhaustion_not_unsat` — a resource-bounded solver returning `outOfFuel` does not
  certify UNSAT, while an `unsat` verdict is sound (`boundedSolve_unsat_sound`).

These are finite fixtures and exact finite-state facts; no asymptotic claim is made.
-/

namespace Erdos287
namespace ResearchBankV8
namespace ActiveResidueDP

/-! ## 1.  Words, owners, validity -/

/-- An owner: integer weights on absolute positions and a modulus. -/
structure Owner where
  /-- Weight at each absolute position (`0` off the owner's coordinates). -/
  w : ℕ → ℤ
  /-- Modulus `d_p`. -/
  d : ℤ

/-- Weighted sum of a word placed at offset `off`. -/
def wsum (w : ℕ → ℤ) : ℕ → List Bool → ℤ
  | _, [] => 0
  | off, b :: l => (if b then w off else 0) + wsum w (off + 1) l

theorem wsum_append (w : ℕ → ℤ) (l₁ l₂ : List Bool) :
    ∀ off, wsum w off (l₁ ++ l₂) = wsum w off l₁ + wsum w (off + l₁.length) l₂ := by
  induction l₁ with
  | nil => intro off; simp [wsum]
  | cons b l ih =>
    intro off
    simp only [List.cons_append, wsum, ih, List.length_cons]
    rw [show off + 1 + l.length = off + (l.length + 1) by omega]; ring

/-- The link condition between a last bit and a first bit (no `00`). -/
def linkOK : Option Bool → Option Bool → Bool
  | some false, some false => false
  | _, _ => true

/-- No two adjacent zeros (Boolean form). -/
def noAdjB : List Bool → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => (a || b) && noAdjB (b :: l)

theorem noAdjB_cons (a : Bool) (l : List Bool) :
    noAdjB (a :: l) = (linkOK (some a) l.head? && noAdjB l) := by
  cases l with
  | nil => simp [noAdjB, linkOK]
  | cons b l => cases a <;> cases b <;> simp [noAdjB, linkOK]

theorem noAdjB_append (l₁ l₂ : List Bool) :
    noAdjB (l₁ ++ l₂) = (noAdjB l₁ && noAdjB l₂ && linkOK l₁.getLast? l₂.head?) := by
  induction l₁ with
  | nil => cases l₂ <;> simp [noAdjB, linkOK]
  | cons a l ih =>
    rw [List.cons_append, noAdjB_cons, ih, noAdjB_cons]
    cases l with
    | nil =>
      simp only [List.nil_append, List.head?_nil, List.getLast?_singleton]
      cases a <;> cases hh : l₂.head? <;> simp [linkOK, noAdjB]
      all_goals (rename_i v; cases v <;> simp)
    | cons b l =>
      have : (b :: l ++ l₂).head? = some b := rfl
      rw [this]
      simp only [List.head?_cons, List.getLast?_cons_cons]
      cases linkOK (some a) (some b) <;> simp [Bool.and_comm]

/-- A full word is valid: no `00` and every owner congruence holds. -/
def Valid (owners : List Owner) (word : List Bool) : Prop :=
  noAdjB word = true ∧ ∀ o ∈ owners, o.d ∣ wsum o.w 0 word

instance (owners : List Owner) (word : List Bool) : Decidable (Valid owners word) := by
  unfold Valid; infer_instance

/-- The feasible suffix set of a prefix. -/
def feasible (owners : List Owner) (pre : List Bool) : Set (List Bool) :=
  {s | Valid owners (pre ++ s)}

/-- The DP state at the cut after `pre`: previous bit and the complete active residue vector. -/
def state (owners : List Owner) (pre : List Bool) : Option Bool × List ℤ :=
  (pre.getLast?, owners.map fun o => wsum o.w 0 pre % o.d)

/-! ## 2.  Exactness of the state -/

theorem dvd_add_iff_of_emod_eq {d a a' b : ℤ} (h : a % d = a' % d) :
    d ∣ a + b ↔ d ∣ a' + b := by
  rw [Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero, Int.add_emod, h, ← Int.add_emod]

/-- **Exactness of the DP state.**  Two internally valid prefixes of equal length with the same
previous bit and the same complete active residue vector have identical feasible suffix sets. -/
theorem feasible_eq_of_state_eq (owners : List Owner) {p₁ p₂ : List Bool}
    (hv₁ : noAdjB p₁ = true) (hv₂ : noAdjB p₂ = true) (hlen : p₁.length = p₂.length)
    (hs : state owners p₁ = state owners p₂) : feasible owners p₁ = feasible owners p₂ := by
  simp only [state, Prod.mk.injEq] at hs
  obtain ⟨hlast, hres⟩ := hs
  ext s
  simp only [feasible, Set.mem_setOf_eq, Valid, noAdjB_append, hv₁, hv₂, hlast, Bool.true_and,
    wsum_append, Nat.zero_add, hlen]
  apply and_congr Iff.rfl
  apply forall₂_congr
  intro o ho
  have := (List.map_eq_map_iff.1 hres) o ho
  exact dvd_add_iff_of_emod_eq this

/-! ## 3.  Forgetting owners -/

/-- The suffix contribution of an owner vanishes after its final coordinate. -/
theorem wsum_zero_of_after (w : ℕ → ℤ) (k : ℕ) (hw : ∀ i, k ≤ i → w i = 0) :
    ∀ (s : List Bool) (off : ℕ), k ≤ off → wsum w off s = 0 := by
  intro s
  induction s with
  | nil => intro _ _; rfl
  | cons b l ih =>
    intro off hoff
    simp only [wsum, hw off hoff, ih (off + 1) (by omega), ite_self, add_zero]

/-- **An owner may be forgotten after its final coordinate once its residue is `0`.** -/
theorem forget_owner_of_final_zero (owners : List Owner) (o : Owner) (pre : List Bool)
    (hfinal : ∀ i, pre.length ≤ i → o.w i = 0) (hzero : o.d ∣ wsum o.w 0 pre) :
    feasible (o :: owners) pre = feasible owners pre := by
  ext s
  simp only [feasible, Set.mem_setOf_eq, Valid, List.mem_cons, forall_eq_or_imp]
  rw [wsum_append, wsum_zero_of_after o.w pre.length hfinal s _ (by omega), add_zero]
  tauto

/-- With nonzero residue after the final coordinate, no suffix is feasible. -/
theorem owner_final_nonzero_infeasible (owners : List Owner) (o : Owner) (pre : List Bool)
    (hfinal : ∀ i, pre.length ≤ i → o.w i = 0) (hnz : ¬ o.d ∣ wsum o.w 0 pre) :
    feasible (o :: owners) pre = ∅ := by
  ext s
  simp only [feasible, Set.mem_setOf_eq, Valid, List.mem_cons, forall_eq_or_imp,
    Set.mem_empty_iff_false, iff_false, not_and]
  intro _ h
  rw [wsum_append, wsum_zero_of_after o.w pre.length hfinal s _ (by omega), add_zero] at h
  exact absurd h hnz

/-! ## 4.  Finite counterfixtures -/

/-- An owner with weight `1` at position `1` only, modulus `2`. -/
def ownerAt1 : Owner := ⟨fun i => if i = 1 then 1 else 0, 2⟩

/-- **Forgetting before the final coordinate is unsound.**  After the prefix `[1]` the owner
`ownerAt1` has residue `0`, but its final coordinate (position `1`) is still ahead: the suffix
`[1]` is feasible without it and infeasible with it. -/
theorem forget_before_final_unsound :
    wsum ownerAt1.w 0 [true] % ownerAt1.d = 0 ∧
    [true] ∈ feasible [] [true] ∧ [true] ∉ feasible [ownerAt1] [true] := by
  refine ⟨by decide, ?_, ?_⟩
  · show Valid [] ([true] ++ [true]); decide
  · show ¬ Valid [ownerAt1] ([true] ++ [true]); decide

/-- An owner with weight `1` at position `0` only, modulus `2`. -/
def ownerAt0 : Owner := ⟨fun i => if i = 0 then 1 else 0, 2⟩

/-- **Forgetting with nonzero residue is unsound.** -/
theorem forget_nonzero_unsound :
    [true] ∈ feasible [] [true] ∧ [true] ∉ feasible [ownerAt0] [true] := by
  refine ⟨?_, ?_⟩
  · show Valid [] ([true] ++ [true]); decide
  · show ¬ Valid [ownerAt0] ([true] ++ [true]); decide

/-- A parity owner on positions `0, 1, 2`. -/
def parity3 : Owner := ⟨fun i => if i ≤ 2 then 1 else 0, 2⟩

/-- **Same previous bit does NOT imply same continuation feasibility.**  The prefixes `[1,1]` and
`[0,1]` end with the same bit, but the suffix `[0]` is feasible after the first and not after the
second (their residue vectors differ). -/
theorem same_bit_not_same_continuation :
    ([true, true] : List Bool).getLast? = ([false, true] : List Bool).getLast? ∧
    [false] ∈ feasible [parity3] [true, true] ∧ [false] ∉ feasible [parity3] [false, true] := by
  refine ⟨rfl, ?_, ?_⟩
  · show Valid [parity3] ([true, true] ++ [false]); decide
  · show ¬ Valid [parity3] ([false, true] ++ [false]); decide

/-- The boundary-bit-only interface is not exact. -/
theorem boundary_bit_only_not_exact :
    ¬ ∀ (owners : List Owner) (p₁ p₂ : List Bool), noAdjB p₁ = true → noAdjB p₂ = true →
      p₁.length = p₂.length → p₁.getLast? = p₂.getLast? →
        feasible owners p₁ = feasible owners p₂ := by
  intro h
  obtain ⟨hl, h1, h2⟩ := same_bit_not_same_continuation
  have := h [parity3] [true, true] [false, true] rfl rfl rfl hl
  rw [this] at h1
  exact h2 h1

/-! ## 5.  Resource exhaustion is not UNSAT -/

/-- Verdicts of a resource-bounded solver. -/
inductive Verdict
  | sat
  | unsat
  | outOfFuel
  deriving DecidableEq, Repr

/-- All words of length `n`. -/
def allWords : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allWords n).flatMap fun w => [false :: w, true :: w]

theorem mem_allWords : ∀ (n : ℕ) (w : List Bool), w.length = n → w ∈ allWords n := by
  intro n
  induction n with
  | zero => intro w hw; simp [List.length_eq_zero_iff.1 hw, allWords]
  | succ n ih =>
    intro w hw
    cases w with
    | nil => simp at hw
    | cons b w =>
      simp only [allWords, List.mem_flatMap]
      refine ⟨w, ih w (by simpa using hw), ?_⟩
      cases b <;> simp

/-- A resource-bounded exhaustive solver: it needs one unit of fuel per candidate word. -/
def boundedSolve (fuel n : ℕ) (P : List Bool → Bool) : Verdict :=
  if (allWords n).length ≤ fuel then
    if (allWords n).any P then Verdict.sat else Verdict.unsat
  else Verdict.outOfFuel

/-- An `unsat` verdict is sound. -/
theorem boundedSolve_unsat_sound {fuel n : ℕ} {P : List Bool → Bool}
    (h : boundedSolve fuel n P = Verdict.unsat) : ∀ w : List Bool, w.length = n → P w = false := by
  intro w hw
  unfold boundedSolve at h
  split_ifs at h with h1 h2
  have := mem_allWords n w hw
  by_contra hP
  simp only [Bool.not_eq_false] at hP
  exact h2 (List.any_eq_true.2 ⟨w, this, hP⟩)

/-- **Resource exhaustion is not UNSAT.** -/
theorem resource_exhaustion_not_unsat :
    boundedSolve 0 1 (fun _ => true) = Verdict.outOfFuel ∧
      ∃ w : List Bool, w.length = 1 ∧ (fun _ => true) w = true :=
  ⟨by decide, [true], rfl, rfl⟩

end ActiveResidueDP
end ResearchBankV8
end Erdos287
