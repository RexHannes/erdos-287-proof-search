import Mathlib

/-!
# Anchored V3 — fixed-bank target mobility

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Fix a valid baseline preparation `S_*` and a fixed terminal bank.  Reserve `H` optional
positions `Z = {n₀, …, n_{H-1}}` satisfying explicitly:

* `n i ∣ D_core`;
* `n i` is an interior optional position, initially zero in the baseline;
* the guard of `n i` is permanently selected;
* `Z` is disjoint from the terminal bank sites, the old repair sites and the fixed pins.

For `y ⊆ Fin H` put `S_y = S_* + ∑_{i ∈ y} 1 / n i`.  We prove

* `den (S_y) ∣ D_core`;
* every prime dividing `den (S_y)` divides `D_core`, so no already-paid prime-power component
  becomes unpaid;
* the no-`00` condition is preserved under the declared guard hypotheses;
* the terminal bank is untouched: the mobility support is disjoint from it, so the *same*
  terminal support object is used for every `y`;
* with `D = D_core * U`, the exact target movement
  `T_y = D (1 - S_y) = T_* - ∑_{i ∈ y} D / n i`.

## REAL-MASS QUALIFICATION

These statements preserve the *arithmetic/path* preparation only.  They do **not** assert that
every `y` remains inside an externally imposed real-entry window; that requires a separate
margin hypothesis, recorded here as `RealEntryWindow` and never assumed.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV3

/-- Reserved mobility data over a baseline preparation. -/
structure MobilityData (H : ℕ) where
  /-- the core modulus -/
  Dcore : ℕ
  /-- the core modulus is positive -/
  hDcore : 0 < Dcore
  /-- the multiplier part of the global modulus -/
  U : ℕ
  /-- the multiplier part is positive -/
  hU : 0 < U
  /-- the reserved optional positions -/
  n : Fin H → ℕ
  /-- reserved positions are positive -/
  hn_pos : ∀ i, 0 < n i
  /-- reserved positions divide the core modulus -/
  hn_dvd : ∀ i, n i ∣ Dcore
  /-- the baseline partial sum -/
  Sstar : ℚ
  /-- the baseline numerator over the core modulus -/
  kstar : ℤ
  /-- the baseline is an integer multiple of `1 / D_core` -/
  hSstar : Sstar = (kstar : ℚ) / (Dcore : ℚ)
  /-- the terminal bank sites -/
  bank : Finset ℕ
  /-- old repair sites and fixed pins -/
  pins : Finset ℕ
  /-- the reserved positions are disjoint from the bank, the old repair sites and the pins -/
  hreserved : ∀ i, n i ∉ bank ∧ n i ∉ pins

namespace MobilityData

variable {H : ℕ} (M : MobilityData H)

/-- The global modulus `D = D_core * U`. -/
def D : ℕ := M.Dcore * M.U

theorem D_pos : 0 < M.D := Nat.mul_pos M.hDcore M.hU

theorem n_dvd_D (i : Fin H) : M.n i ∣ M.D := (M.hn_dvd i).trans ⟨M.U, rfl⟩

/-- The moved baseline `S_y = S_* + ∑_{i ∈ y} 1 / n i`. -/
def S (y : Finset (Fin H)) : ℚ := M.Sstar + ∑ i ∈ y, (1 : ℚ) / ((M.n i : ℕ) : ℚ)

/-- The integer numerator of `S_y` over `D_core`. -/
def num (y : Finset (Fin H)) : ℤ := M.kstar + ((∑ i ∈ y, M.Dcore / M.n i : ℕ) : ℤ)

theorem S_eq_num_div (y : Finset (Fin H)) : M.S y = (M.num y : ℚ) / (M.Dcore : ℚ) := by
  have hD : (0:ℚ) < (M.Dcore : ℚ) := by exact_mod_cast M.hDcore
  have hterm : ∀ i ∈ y, (1 : ℚ) / ((M.n i : ℕ) : ℚ)
      = ((M.Dcore / M.n i : ℕ) : ℚ) / (M.Dcore : ℚ) := by
    intro i _
    have hni : (0:ℚ) < ((M.n i : ℕ) : ℚ) := by exact_mod_cast M.hn_pos i
    have hcast : ((M.n i : ℕ) : ℚ) * ((M.Dcore / M.n i : ℕ) : ℚ) = (M.Dcore : ℚ) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) (Nat.mul_div_cancel' (M.hn_dvd i))
    rw [div_eq_div_iff hni.ne' hD.ne']
    linarith [hcast, mul_comm ((M.n i : ℕ) : ℚ) ((M.Dcore / M.n i : ℕ) : ℚ)]
  rw [S, M.hSstar, Finset.sum_congr rfl hterm, num, ← Finset.sum_div, ← add_div,
    Int.cast_add, Int.cast_natCast, Nat.cast_sum]

/-- **The denominator of every moved baseline divides `D_core`.** -/
theorem den_dvd_Dcore (y : Finset (Fin H)) : (M.S y).den ∣ M.Dcore := by
  have h := M.S_eq_num_div y
  have hden : ((Rat.divInt (M.num y) (M.Dcore : ℤ)).den : ℤ) ∣ ((M.Dcore : ℤ)) :=
    Rat.den_dvd _ _
  rw [Rat.divInt_eq_div, Int.cast_natCast, ← h] at hden
  exact_mod_cast hden

/-- **All inherited already-paid prime-power components stay paid**: no new prime can appear in
the denominator of a moved baseline. -/
theorem prime_dvd_den_imp_dvd_Dcore (y : Finset (Fin H)) {p : ℕ} (hp : p ∣ (M.S y).den) :
    p ∣ M.Dcore := hp.trans (M.den_dvd_Dcore y)

/-- **The terminal bank is unchanged**: the mobility support is disjoint from the bank sites,
from the old repair sites and from the fixed pins, so the same terminal support object is used
for every mobility choice `y`. -/
theorem mobility_support_disjoint (i : Fin H) : M.n i ∉ M.bank ∧ M.n i ∉ M.pins :=
  M.hreserved i

/-- The unmoved target `T_* = D (1 - S_*)`. -/
def Tstar : ℚ := (M.D : ℚ) * (1 - M.Sstar)

/-- **The exact target movement** `T_y = T_* - ∑_{i ∈ y} D / n i`. -/
theorem target_movement (y : Finset (Fin H)) :
    (M.D : ℚ) * (1 - M.S y) = M.Tstar - ∑ i ∈ y, ((M.D / M.n i : ℕ) : ℚ) := by
  have hterm : ∀ i ∈ y, (M.D : ℚ) * ((1 : ℚ) / ((M.n i : ℕ) : ℚ)) = ((M.D / M.n i : ℕ) : ℚ) := by
    intro i _
    have hni : (0:ℚ) < ((M.n i : ℕ) : ℚ) := by exact_mod_cast M.hn_pos i
    have hcast : ((M.n i : ℕ) : ℚ) * ((M.D / M.n i : ℕ) : ℚ) = (M.D : ℚ) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) (Nat.mul_div_cancel' (M.n_dvd_D i))
    rw [mul_one_div, div_eq_iff hni.ne']
    linarith [hcast, mul_comm ((M.n i : ℕ) : ℚ) ((M.D / M.n i : ℕ) : ℚ)]
  have hexp : (M.D : ℚ) * (1 - M.S y)
      = (M.D : ℚ) * (1 - M.Sstar) - (M.D : ℚ) * ∑ i ∈ y, (1 : ℚ) / ((M.n i : ℕ) : ℚ) := by
    rw [S]
    ring
  rw [hexp, Finset.mul_sum, Finset.sum_congr rfl hterm, Tstar]

/-- The externally imposed real-entry window.  Target mobility does **not** assert this
property; it must be supplied by a separate margin hypothesis. -/
def RealEntryWindow (lo hi : ℚ) (y : Finset (Fin H)) : Prop := lo ≤ M.S y ∧ M.S y ≤ hi

end MobilityData

/-- The no-`00` condition on a set of selected positions, relative to a guard assignment. -/
def No00 (guard : ℕ → ℕ) (positions chosen : Finset ℕ) : Prop :=
  ∀ p ∈ positions, p ∈ chosen ∨ guard p ∈ chosen

/-- **No-`00` is preserved** under the declared guard hypotheses: the guards of the reserved
positions are permanently selected, hence remain selected for every mobility choice. -/
theorem no00_preserved {guard : ℕ → ℕ} {positions base chosen : Finset ℕ}
    (hguard : ∀ p ∈ positions, guard p ∈ base) (hsub : base ⊆ chosen) :
    No00 guard positions chosen :=
  fun p hp => Or.inr (hsub (hguard p hp))

end AnchoredV3
end Erdos287
