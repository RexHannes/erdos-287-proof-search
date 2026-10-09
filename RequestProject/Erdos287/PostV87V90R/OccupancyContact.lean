import RequestProject.Erdos287.PostV87V90R.RowRigidity
import RequestProject.Erdos287.PostV87V90R.AffineCompiler
import RequestProject.Erdos287.PostV87V90R.MomentConsumer

/-!
# Erdős #287 — post-V87 → V90R: occupancy-to-contact consumer (unconditional)

**ERDŐS #287 REMAINS OPEN.**

Given a finite compiler `C : AffineContactCompiler r m K`, a window `[a, M]`, a cofactor
bound `H` and a parameter `t`, the *window control* `WindowControl C a M H t` collects exactly the
numerical facts consumed downstream:

* **source window** — on every oriented compiler edge the compiled positions satisfy
  `a ≤ n⁻(t)` and `n⁺(t) ≤ M`;
* **row bound / scale control** — `M < (slope · t + 1)(H + 1)` for every form (so all selected
  multiples of a form value have cofactor `≤ H`);
* **big prime** — `B_H < slope · t + 1` for every form.

Macroblock `j` is *occupied* at `t` when one of its forms takes a prime value.

Unconditional consumers:

* `false_of_edge` — two occupied macroblocks joined by an edge of `ContactCycle r m` produce a
  `ContactWitness` (adjacency identity + row rigidity), contradicting gap-two;
* `occupancy_contact_false` — **`m + 1` occupied macroblocks at one parameter are impossible**
  (by `α(ContactCycle r m) = m`);
* `moment_contact_false`, `sharp_contact_false` — the same from the repaired moment inequalities
  (Cauchy form, resp. sharp balanced form) on a finite weighted parameter set.
-/

open scoped BigOperators
open Finset Classical

namespace Erdos287.PostV87V90R

open Erdos287 Erdos287.PostV71V87

variable {r m K : ℕ} [NeZero r]

/-- The per-window, per-parameter numerical conditions consumed by the contact argument. -/
structure WindowControl (C : AffineContactCompiler r m K) (a M H t : ℕ) : Prop where
  window : ∀ j k i i', (ContactCycle r m).Adj j k → C.slope j i < C.slope k i' →
    a ≤ nMinus (C.slope j i) (C.slope k i') t ∧ nPlus (C.slope j i) (C.slope k i') t ≤ M
  rowBound : ∀ j i, M < (C.slope j i * t + 1) * (H + 1)
  bigPrime : ∀ j i, BH H < C.slope j i * t + 1

/-- Macroblocks occupied at parameter `t`: some form value is prime. -/
noncomputable def occupied (C : AffineContactCompiler r m K) (t : ℕ) : Finset (ZMod r) :=
  univ.filter (fun j => ∃ i, (C.slope j i * t + 1).Prime)

/-- Block counts: number of prime form values in macroblock `j` at parameter `t`. -/
noncomputable def blockCount (C : AffineContactCompiler r m K) : ℕ → ZMod r → ℕ :=
  fun t j => (univ.filter (fun i : Fin K => (C.slope j i * t + 1).Prime)).card

theorem Zcount_blockCount (C : AffineContactCompiler r m K) (t : ℕ) :
    Zcount (blockCount C) t = (occupied C t).card := by
  unfold Zcount occupied blockCount
  congr 1
  ext j
  simp [Finset.card_pos, Finset.filter_nonempty_iff]

/-- An oriented occupied compiler edge yields a contact witness. -/
noncomputable def contactWitness_of_oriented (W : ExactWord) (C : AffineContactCompiler r m K)
    {H t : ℕ} (hW : WindowControl C W.a W.M H t) {j k : ZMod r} {i i' : Fin K}
    (hadj : (ContactCycle r m).Adj j k) (hlt : C.slope j i < C.slope k i')
    (hpj : (C.slope j i * t + 1).Prime) (hpk : (C.slope k i' * t + 1).Prime) :
    ContactWitness W where
  p := C.slope k i' * t + 1
  q := C.slope j i * t + 1
  H := H
  n := nMinus (C.slope j i) (C.slope k i') t
  hp := hpk
  hq := hpj
  hpB := hW.bigPrime k i'
  hqB := hW.bigPrime j i
  hpM := hW.rowBound k i'
  hqM := hW.rowBound j i
  hpn := form_dvd_nMinus _ _ _
  hqn := by rw [← C.edge_adjacent hadj hlt t]; exact form_dvd_nPlus _ _ _
  hn := (hW.window j k i i' hadj hlt).1
  hn1 := by rw [← C.edge_adjacent hadj hlt t]; exact (hW.window j k i i' hadj hlt).2

/-- **Edge consumer.**  Two occupied macroblocks joined by a useful edge are impossible. -/
theorem false_of_edge (W : ExactWord) (C : AffineContactCompiler r m K) {H t : ℕ}
    (hW : WindowControl C W.a W.M H t) {j k : ZMod r} (hadj : (ContactCycle r m).Adj j k)
    (hj : j ∈ occupied C t) (hk : k ∈ occupied C t) : False := by
  obtain ⟨i, hi⟩ := (mem_filter.1 hj).2
  obtain ⟨i', hi'⟩ := (mem_filter.1 hk).2
  rcases lt_or_gt_of_ne (C.edge_ne j k i i' hadj) with h | h
  · exact (contactWitness_of_oriented W C hW hadj h hi hi').false
  · exact (contactWitness_of_oriented W C hW hadj.symm h hi' hi).false

/-- **Occupancy-to-contact consumer.**  For `1 ≤ m`, `2m ≤ r`: at no parameter with window
control can `m + 1` macroblocks be occupied. -/
theorem occupancy_contact_false (W : ExactWord) (C : AffineContactCompiler r m K) {H t : ℕ}
    (hm : 1 ≤ m) (hr : 2 * m ≤ r) (hW : WindowControl C W.a W.M H t)
    (hocc : m + 1 ≤ (occupied C t).card) : False := by
  obtain ⟨j, hj, k, hk, hadj⟩ := exists_useful_edge hm hr hocc
  exact false_of_edge W C hW hadj hj hk

/-- **Moment-to-contact consumer (Cauchy form).**  The repaired normalised moment
inequalities on a finite weighted parameter set with window control on its support are
incompatible with an exact word. -/
theorem moment_contact_false (W : ExactWord) (C : AffineContactCompiler r m K) {H : ℕ}
    (hm : 1 ≤ m) (hr : 2 * m ≤ r) (F : FiniteWeights) {μ Cpair : ℝ} (hμ : 0 < μ)
    (hP : μ ≤ F.E (fun t => (Pcount (blockCount C) t : ℝ)))
    (hQ : F.E (fun t => (Qcount (blockCount C) t : ℝ)) ≤ Cpair * μ ^ 2 / (2 * r))
    (hC : Cpair < r / m) (hμbig : (m : ℝ) * r / (r - m * Cpair) < μ)
    (hctrl : ∀ t ∈ F.T, 0 < F.w t → WindowControl C W.a W.M H t) : False := by
  have hr0 : (0 : ℝ) < r := Nat.cast_pos.2 (NeZero.pos r)
  obtain ⟨t, ht, hw, hZ⟩ :=
    occupancy_of_normalized_moments F (blockCount C) hr0 hm hμ hP hQ hC hμbig
  rw [Zcount_blockCount] at hZ
  exact occupancy_contact_false W C hm hr (hctrl t ht hw) hZ

/-- **Moment-to-contact consumer (sharp balanced form).** -/
theorem sharp_contact_false (W : ExactWord) (C : AffineContactCompiler r m K) {H : ℕ}
    (hm : 1 ≤ m) (hr : 2 * m ≤ r) (F : FiniteWeights)
    (hQ : F.E (fun t => (Qcount (blockCount C) t : ℝ)) <
      qlin m (F.E (fun t => (Pcount (blockCount C) t : ℝ))))
    (hctrl : ∀ t ∈ F.T, 0 < F.w t → WindowControl C W.a W.M H t) : False := by
  obtain ⟨t, ht, hw, hZ⟩ := exists_occupancy_of_sharp F (blockCount C) m hQ
  rw [Zcount_blockCount] at hZ
  exact occupancy_contact_false W C hm hr (hctrl t ht hw) hZ

end Erdos287.PostV87V90R
