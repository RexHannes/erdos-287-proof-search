import Mathlib
import RequestProject.CurrentProgramme.Erdos287FractionalLinearC0

/-!
# Centered graph-diagonal firewall and common-divisor collision arithmetic — Erdős #287

Append-only module, strictly after `Erdos287FractionalLinearC0`.

Contents.

* §1  **Graph diagonal.**  `graph_diagonal_forces_full_gcd` — with `b` a unit modulo `Q`,
  `Q ∣ (kappa - 1) b` forces `Q ∣ kappa - 1`.  `graph_literal_diagonal_impossible` — hence under
  the centered conditions `gcd (kappa - 1) Q = d < Q` the two relations `N = b` and
  `N ≡ kappa b (mod Q)` cannot hold simultaneously.
* §2  **Common-divisor collisions.**  For `g ∣ x`, `g ∣ x'`: equal `kappa`-residues mod `g`
  give CRT-compatible rows, and conversely, cancellation of a unit `b` recovers equality of the
  residues.  **No multiplicity bound for these collisions is formalised** — none is proved.
* §3  **The x-row firewall.**  The centered hypotheses of §1 are satisfiable *together with*
  `x₁ = x₂`.  Consequently "graph diagonal impossible" does **not** entail "x-row diagonal
  impossible"; §8 of the status ledger records this separation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace CommonX

/-! ## §1  Centered graph-diagonal firewall -/

/-- **`graph_diagonal_forces_full_gcd`.**  `LEAN_PROVED`.  The non-strict, positive form of the
firewall: `Q ∣ (kappa - 1) * b` with `b` a unit modulo `Q` forces the *full* divisibility
`Q ∣ kappa - 1`. -/
theorem graph_diagonal_forces_full_gcd {kappa b Q : ℤ} (hb : IsCoprime b Q)
    (h : Q ∣ (kappa - 1) * b) : Q ∣ kappa - 1 :=
  hb.symm.dvd_of_dvd_mul_right h

/-- **`gcd_eq_natAbs_of_dvd`.**  `LEAN_PROVED`.  If `Q ∣ a` then `gcd a Q = |Q|`. -/
theorem gcd_eq_natAbs_of_dvd {a Q : ℤ} (h : Q ∣ a) : Int.gcd a Q = Q.natAbs :=
  Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
    (Nat.dvd_gcd (Int.natAbs_dvd_natAbs.mpr h) dvd_rfl)

/-- The centered `kappa` conditions used by the graph-diagonal firewall:
`Q > 1`, `b` a unit modulo `Q`, and `gcd (kappa - 1) Q = d` with `d` a **proper** divisor. -/
def CenteredKappa (kappa b Q : ℤ) (d : ℕ) : Prop :=
  1 < Q ∧ IsCoprime b Q ∧ Int.gcd (kappa - 1) Q = d ∧ d < Q.natAbs

/-- **`graph_literal_diagonal_impossible`.**  `LEAN_PROVED`.  Under the centered conditions it is
impossible to have simultaneously `N = b` and `N ≡ kappa * b (mod Q)`. -/
theorem graph_literal_diagonal_impossible {kappa b N Q : ℤ} {d : ℕ}
    (hb : IsCoprime b Q) (hd : Int.gcd (kappa - 1) Q = d) (hlt : d < Q.natAbs)
    (hdiag : N = b) (hcong : Q ∣ N - kappa * b) : False := by
  rw [hdiag] at hcong
  have h1 : Q ∣ (kappa - 1) * b := by
    have hEq : (kappa - 1) * b = -(b - kappa * b) := by ring
    rw [hEq]
    exact dvd_neg.mpr hcong
  have h2 : Q ∣ kappa - 1 := graph_diagonal_forces_full_gcd hb h1
  rw [gcd_eq_natAbs_of_dvd h2] at hd
  omega

/-- **`graph_diagonal_impossible_of_centered`.**  `LEAN_PROVED`.  Packaged form of the
firewall. -/
theorem graph_diagonal_impossible_of_centered {kappa b Q : ℤ} {d : ℕ}
    (hc : CenteredKappa kappa b Q d) {N : ℤ} (hdiag : N = b) :
    ¬ Q ∣ N - kappa * b := by
  obtain ⟨_, hb, hd, hlt⟩ := hc
  exact fun hcong => graph_literal_diagonal_impossible hb hd hlt hdiag hcong

/-! ## §2  Common-divisor collision arithmetic -/

/-- **`commonDivisor_residue_compatible`.**  `LEAN_PROVED`.  If two rows have the same `kappa`
residue modulo a common divisor `g` of `x` and `x'`, the two congruence rows agree modulo `g`
(CRT compatibility).  The divisibilities `g ∣ x`, `g ∣ x'` are recorded in the statement even
though the identity itself needs only the residue equality. -/
theorem commonDivisor_residue_compatible {g x x' b k1 k2 : ℤ} (_hx : g ∣ x) (_hx' : g ∣ x')
    (h : g ∣ k1 - k2) : g ∣ k1 * b - k2 * b := by
  have hrw : k1 * b - k2 * b = (k1 - k2) * b := by ring
  rw [hrw]; exact h.mul_right b

/-- **`commonDivisor_residue_cancel_unit`.**  `LEAN_PROVED`.  The converse: if `b` is a unit
modulo `g` and the two rows agree after multiplication by `b`, the `kappa` residues themselves
agree modulo `g`.

This is the only collision statement banked.  **No bound on the number of such collisions is
formalised**, because none is proved. -/
theorem commonDivisor_residue_cancel_unit {g b k1 k2 : ℤ} (hb : IsCoprime b g)
    (h : g ∣ k1 * b - k2 * b) : g ∣ k1 - k2 := by
  refine hb.symm.dvd_of_dvd_mul_right ?_
  have hrw : (k1 - k2) * b = k1 * b - k2 * b := by ring
  rw [hrw]; exact h

/-- **`commonDivisor_residue_iff_unit`.**  `LEAN_PROVED`.  The two directions combined. -/
theorem commonDivisor_residue_iff_unit {g b k1 k2 : ℤ} (hb : IsCoprime b g) :
    g ∣ k1 * b - k2 * b ↔ g ∣ k1 - k2 :=
  ⟨commonDivisor_residue_cancel_unit hb,
    commonDivisor_residue_compatible (dvd_refl g) (dvd_refl g)⟩

/-! ## §3  The x-row firewall -/

/-- **`centered_kappa_satisfiable`.**  `LEAN_PROVED`.  The centered conditions are not vacuous:
`kappa = 3`, `b = 1`, `Q = 6`, `d = 2` satisfies them. -/
theorem centered_kappa_satisfiable : CenteredKappa 3 1 6 2 := by
  refine ⟨by norm_num, isCoprime_one_left, ?_, by norm_num⟩
  decide +kernel

/-- **`xRowDiagonal_not_excluded`.**  `LEAN_PROVED`.  **Firewall.**  There is a configuration in
which the centered conditions hold — so the *graph* diagonal `N = b` is arithmetically
impossible — while the *x-row* diagonal `x₁ = x₂` genuinely occurs.  Hence

```
graph diagonal impossible   ⇏   x-row diagonal impossible.
```
-/
theorem xRowDiagonal_not_excluded :
    ∃ (kappa b Q : ℤ) (d : ℕ) (x1 x2 : ℤ),
      CenteredKappa kappa b Q d ∧
      (∀ N : ℤ, N = b → ¬ Q ∣ N - kappa * b) ∧
      x1 = x2 :=
  ⟨3, 1, 6, 2, 5, 5, centered_kappa_satisfiable,
    fun _ hN => graph_diagonal_impossible_of_centered centered_kappa_satisfiable hN, rfl⟩

end CommonX
end Erdos287
