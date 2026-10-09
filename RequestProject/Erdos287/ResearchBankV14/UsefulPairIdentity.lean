import RequestProject.Erdos287.ResearchBankV9.AffineContact

/-!
# Erdős #287 — Research Bank V14 §A6: useful-pair orientation

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For an edge `uv` put `d = gcd(a_u, a_v) = |a_u − a_v|` and `L_w(t) = a_w t + 1`.

* `useful_identity_oriented` — **oriented**: if `a_u < a_v` then
  `(a_v/d) L_u(t) − (a_u/d) L_v(t) = 1` (reusing the V9 affine contact identity);
* `useful_identity_pm_one` — **unoriented**: for `a_u ≠ a_v` only the `±1` statement holds;
* `signless_identity_false` — **regression fixture**: the old signless statement
  "`(a_v/d) L_u − (a_u/d) L_v = 1` for every edge" is false (`a_u = 3, a_v = 2, t = 0` gives `−1`).
-/

namespace Erdos287
namespace ResearchBankV14
namespace UsefulPairIdentity

open ResearchBankV9.AffineContact

/-- `L_a(t) = a t + 1`. -/
def L (a t : ℕ) : ℕ := a * t + 1

/-- Unsigned distance `|a_u − a_v|` in `ℕ`. -/
def dist (au av : ℕ) : ℕ := if au < av then av - au else au - av

/-- The (signless) expression `(a_v/d) L_u(t) − (a_u/d) L_v(t)` with `d = |a_u − a_v|`. -/
def expr (au av t : ℕ) : ℤ :=
  ((av / dist au av : ℕ) : ℤ) * (L au t : ℤ) - ((au / dist au av : ℕ) : ℤ) * (L av t : ℤ)

/-- **Oriented useful identity.** -/
theorem useful_identity_oriented {au av : ℕ} (hlt : au < av) (hg : Nat.gcd au av = av - au)
    (t : ℕ) :
    ((av / (av - au) : ℕ) : ℤ) * (L au t : ℤ) - ((au / (av - au) : ℕ) : ℤ) * (L av t : ℤ) = 1 :=
  affine_contact_identity hlt hg t

theorem expr_oriented {au av : ℕ} (hlt : au < av) (hg : Nat.gcd au av = av - au) (t : ℕ) :
    expr au av t = 1 := by
  unfold expr dist; rw [if_pos hlt]; exact useful_identity_oriented hlt hg t

theorem expr_reversed {au av : ℕ} (hlt : av < au) (hg : Nat.gcd au av = au - av) (t : ℕ) :
    expr au av t = -1 := by
  have hn : ¬ au < av := by omega
  unfold expr dist; rw [if_neg hn]
  have := useful_identity_oriented hlt (by rw [Nat.gcd_comm]; exact hg) t
  linarith

/-- **Unoriented statement: only `±1`.** -/
theorem useful_identity_pm_one {au av : ℕ} (hne : au ≠ av) (hg : Nat.gcd au av = dist au av)
    (t : ℕ) : expr au av t = 1 ∨ expr au av t = -1 := by
  rcases lt_or_gt_of_ne hne with h | h
  · left; unfold dist at hg; rw [if_pos h] at hg; exact expr_oriented h hg t
  · right
    have hn : ¬ au < av := by omega
    unfold dist at hg; rw [if_neg hn] at hg; exact expr_reversed h hg t

/-- **Regression fixture (old sign error).**  The signless consecutive identity is false. -/
theorem signless_identity_false :
    ¬ ∀ au av t : ℕ, au ≠ av → Nat.gcd au av = dist au av → expr au av t = 1 := by
  intro h
  have := h 3 2 0 (by decide) (by decide)
  revert this; decide

/-- The fixture value: `a_u = 3, a_v = 2, t = 0` gives exactly `−1`. -/
theorem fixture_value : expr 3 2 0 = -1 := by decide

end UsefulPairIdentity
end ResearchBankV14
end Erdos287
