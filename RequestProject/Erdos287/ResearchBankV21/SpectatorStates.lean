import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V21 §3: the spectator-state model at one good prime

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Fix a pair `i, j` and put `r = K - 2` (number of spectator forms).  At a good prime `p`
(outside the finite exceptional set, `p > r + 2`) the spectator state is

    Y_p = none      (no spectator form vanishes mod p)
    Y_p = some k    (spectator form k vanishes mod p),

with the REPAIRED local distribution

    Prob(Y_p = some k) = 1/(p-1),     Prob(Y_p = none) = (p-r-1)/(p-1).

The conditional sieve density of `L_j` is `q_p(none) = 1/(p-r-1)`, `q_p(some k) = 0`, and the
fixed envelope is `h(p) = 1/(p-r-1) = 1/(p-K+1)`.

Kernel-proved (LEAN BANK):
* `stateProb_sum_one`, `stateProb_nonneg` — the local law is a probability;
* `condDensity_le_envelope` — pointwise `q_p(Y) ≤ h(p)`;
* `condDensity_nonneg`, `envelope_lt_one`;
* `envelope_eq` — `h(p) = 1/(p-K+1)` when `r = K-2`;
* `average_condDensity` — averaged over `Y`, the density is `1/(p-1)`: the RAW density is
  `1/(p-1)`, but conditionally on `Y` it can be as large as `h(p) > 1/(p-1)`
  (`envelope_gt_raw`).  Only the ENVELOPE `h`, not `1/(p-1)`, controls the weighted sieve.
-/

namespace Erdos287
namespace ResearchBankV21
namespace SpectatorStates

/-- Spectator state: `none` = no spectator root, `some k` = spectator form `k` vanishes. -/
abbrev SpecState (r : ℕ) := Option (Fin r)

/-- The repaired local law of the spectator state at a good prime `p`. -/
noncomputable def stateProb (p r : ℕ) : SpecState r → ℝ
  | none => ((p : ℝ) - r - 1) / ((p : ℝ) - 1)
  | some _ => 1 / ((p : ℝ) - 1)

/-- The conditional density of `p ∣ L_j` given the spectator state. -/
noncomputable def condDensity (p r : ℕ) : SpecState r → ℝ
  | none => 1 / ((p : ℝ) - r - 1)
  | some _ => 0

/-- The fixed envelope `h(p) = 1/(p-r-1)`. -/
noncomputable def envelope (p r : ℕ) : ℝ := 1 / ((p : ℝ) - r - 1)

theorem stateProb_sum_one {p r : ℕ} (hp : r + 1 < p) :
    ∑ Y : SpecState r, stateProb p r Y = 1 := by
  rw [Fintype.sum_option]
  simp only [stateProb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have h2 : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [mul_one_div, ← add_div, div_eq_one_iff_eq h2]
  ring

theorem stateProb_nonneg {p r : ℕ} (hp : r + 1 < p) (Y : SpecState r) : 0 ≤ stateProb p r Y := by
  have hr : (r : ℝ) + 1 < p := by exact_mod_cast hp
  cases Y with
  | none => exact div_nonneg (by linarith) (by linarith)
  | some _ => exact div_nonneg zero_le_one (by linarith)

/-- **Pointwise domination** `q_p(Y) ≤ h(p)`. -/
theorem condDensity_le_envelope {p r : ℕ} (hp : r + 1 < p) (Y : SpecState r) :
    condDensity p r Y ≤ envelope p r := by
  have hr : (r : ℝ) + 1 < p := by exact_mod_cast hp
  cases Y with
  | none => exact le_rfl
  | some _ => exact div_nonneg zero_le_one (by linarith)

theorem condDensity_nonneg {p r : ℕ} (hp : r + 1 < p) (Y : SpecState r) :
    0 ≤ condDensity p r Y := by
  have hr : (r : ℝ) + 1 < p := by exact_mod_cast hp
  cases Y with
  | none => exact div_nonneg zero_le_one (by linarith)
  | some _ => exact le_rfl

theorem envelope_lt_one {p r : ℕ} (hp : r + 2 < p) : envelope p r < 1 := by
  have hr : (r : ℝ) + 2 < p := by exact_mod_cast hp
  unfold envelope
  rw [div_lt_one (by linarith)]
  linarith

/-- `h(p) = 1/(p-K+1)` for `r = K - 2`. -/
theorem envelope_eq {p K : ℕ} (hK : 2 ≤ K) : envelope p (K - 2) = 1 / ((p : ℝ) - K + 1) := by
  unfold envelope
  rw [Nat.cast_sub hK]
  congr 1
  push_cast
  ring

/-- **Averaged density is the raw density `1/(p-1)`.** -/
theorem average_condDensity {p r : ℕ} (hp : r + 1 < p) :
    ∑ Y : SpecState r, stateProb p r Y * condDensity p r Y = 1 / ((p : ℝ) - 1) := by
  rw [Fintype.sum_option]
  simp only [stateProb, condDensity, mul_zero, Finset.sum_const_zero, add_zero]
  have hr : (r : ℝ) + 1 < p := by exact_mod_cast hp
  have h1 : (p : ℝ) - r - 1 ≠ 0 := by linarith
  have h2 : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp

/-- The envelope strictly exceeds the raw density as soon as there is a spectator form. -/
theorem envelope_gt_raw {p r : ℕ} (hp : r + 1 < p) (hr : 0 < r) :
    1 / ((p : ℝ) - 1) < envelope p r := by
  have hr' : (r : ℝ) + 1 < p := by exact_mod_cast hp
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  unfold envelope
  apply one_div_lt_one_div_of_lt (by linarith)
  linarith

end SpectatorStates
end ResearchBankV21
end Erdos287
