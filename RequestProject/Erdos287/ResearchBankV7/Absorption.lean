import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V7: bounded adaptive absorption (exact finite charging)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This module is pure finite combinatorics: every theorem is kernel-proved, with no external input.
It formalizes the **charging theorem** underlying bounded adaptive absorption.

Setting (all finite).  `Z0` is the current zero set, `G0` the set of fixed-one guards, `W` the
family of absorbed rows, and `U ⊆ W` the sub-family of rows that are actually *used* for
branching.  Each charged row is charged either to a zero of `Z0` (at most **two** rows per zero)
or to a guard of `G0` (at most **one** row per guard); at most a `3γ`-fraction of the rows escapes
charging.  The conclusions are the exact finite bounds

* `(1 - 3γ) |W| ≤ 2|Z₀| + |G₀|`  (guarded form),
* `(1 - 3γ) |W| ≤ 2|Z₀|`         (unguarded form, `G₀ = ∅`),

and for the canonical choice `γ = 1/8`

* `|W| ≤ (16/5)|Z₀| + (8/5)|G₀|`,   `|U| ≤ (2/5)|Z₀| + (1/5)|G₀|`,
* `|W| ≤ (16/5)|Z₀|`,               `|U| ≤ (2/5)|Z₀|`.

A branching-bit budget (`branching_bits_le`) is banked in the same finite form.

**Scope firewall.**  Nothing here asserts that any absorbed row family or row completion *exists*:
the asymptotic existence of row completions is deliberately *not* encoded in these finite charging
lemmas (see `charging_does_not_give_existence`).
-/

namespace Erdos287
namespace ResearchBankV7
namespace Absorption

open Finset

/-! ## 1.  The finite fibre-counting kernel -/

/-- If `f` maps `s` into `t` and every fibre over `t` has at most `n` elements, then
`|s| ≤ n |t|`. -/
theorem card_le_of_fibre_bound {s t : Finset ℕ} {f : ℕ → ℕ} {n : ℕ}
    (hmaps : ∀ a ∈ s, f a ∈ t) (hfib : ∀ b ∈ t, {a ∈ s | f a = b}.card ≤ n) :
    s.card ≤ n * t.card := by
  have himg : s.image f ⊆ t := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
    exact hmaps a ha
  have h1 : s.card ≤ n * (s.image f).card :=
    Finset.card_le_mul_card_image s n (fun b hb => hfib b (himg hb))
  exact h1.trans (Nat.mul_le_mul_left n (Finset.card_le_card himg))

/-! ## 2.  Guarded charging data -/

/-- The exact finite hypotheses of the adaptive-absorption charging argument.

`W` is the absorbed row family, `Z0` the current zero set, `G0` the fixed-one guard set.  Rows in
`chargedZ` are charged to zeros (at most two per zero), rows in `chargedG` to guards (at most one
per guard); `gamma` bounds the fraction of rows that escape charging. -/
structure ChargingData where
  /-- The current zero set. -/
  Z0 : Finset ℕ
  /-- The fixed-one guard set (empty in the unguarded regime). -/
  G0 : Finset ℕ
  /-- The absorbed row family. -/
  W : Finset ℕ
  /-- The rows charged to zeros. -/
  chargedZ : Finset ℕ
  /-- The rows charged to guards. -/
  chargedG : Finset ℕ
  /-- The charging map to zeros. -/
  siteZ : ℕ → ℕ
  /-- The charging map to guards. -/
  siteG : ℕ → ℕ
  /-- Charged rows are rows. -/
  chargedZ_sub : chargedZ ⊆ W
  /-- Charged rows are rows. -/
  chargedG_sub : chargedG ⊆ W
  /-- The zero-charging map lands in the zero set. -/
  siteZ_maps : ∀ r ∈ chargedZ, siteZ r ∈ Z0
  /-- The guard-charging map lands in the guard set. -/
  siteG_maps : ∀ r ∈ chargedG, siteG r ∈ G0
  /-- **Two rows per zero.** -/
  siteZ_fibre : ∀ z ∈ Z0, {r ∈ chargedZ | siteZ r = z}.card ≤ 2
  /-- **One row per fixed-one guard.** -/
  siteG_fibre : ∀ g ∈ G0, {r ∈ chargedG | siteG r = g}.card ≤ 1
  /-- The escape fraction parameter. -/
  gamma : ℚ
  /-- At most a `3γ`-fraction of the absorbed rows escapes charging. -/
  escape : (W.card : ℚ) - (chargedZ.card + chargedG.card) ≤ 3 * gamma * W.card

/-- Rows charged to zeros are at most twice the number of zeros. -/
theorem chargedZ_card_le (c : ChargingData) : c.chargedZ.card ≤ 2 * c.Z0.card :=
  card_le_of_fibre_bound c.siteZ_maps c.siteZ_fibre

/-- Rows charged to guards are at most the number of guards. -/
theorem chargedG_card_le (c : ChargingData) : c.chargedG.card ≤ c.G0.card := by
  have := card_le_of_fibre_bound c.siteG_maps c.siteG_fibre
  simpa using this

/-! ## 3.  The guarded charging inequality -/

/-- **Guarded charging theorem (kernel).**  `(1 − 3γ)·|W| ≤ 2·z₀ + g₀`. -/
theorem guarded_charging (c : ChargingData) :
    (1 - 3 * c.gamma) * (c.W.card : ℚ) ≤ 2 * c.Z0.card + c.G0.card := by
  have hZ : (c.chargedZ.card : ℚ) ≤ 2 * c.Z0.card := by exact_mod_cast chargedZ_card_le c
  have hG : (c.chargedG.card : ℚ) ≤ c.G0.card := by exact_mod_cast chargedG_card_le c
  have h := c.escape
  nlinarith [h, hZ, hG]

/-- **Unguarded charging theorem (kernel).**  With no fixed-one guards, `(1 − 3γ)·W ≤ 2|Z₀|`. -/
theorem unguarded_charging (c : ChargingData) (hG : c.G0 = ∅) :
    (1 - 3 * c.gamma) * (c.W.card : ℚ) ≤ 2 * c.Z0.card := by
  have := guarded_charging c
  rw [hG] at this
  simpa using this

/-! ## 4.  The canonical choice `γ = 1/8` -/

/-- **Guarded budget at `γ = 1/8`.**  `|W| ≤ (16/5) z₀ + (8/5) g₀`. -/
theorem guarded_W_bound (c : ChargingData) (hγ : c.gamma = 1/8) :
    (c.W.card : ℚ) ≤ (16/5) * c.Z0.card + (8/5) * c.G0.card := by
  have h := guarded_charging c
  rw [hγ] at h
  linarith

/-- **Guarded branching budget at `γ = 1/8`.**  If the used family satisfies `|U| ≤ γ|W|`, then
`|U| ≤ (2/5) z₀ + (1/5) g₀`. -/
theorem guarded_U_bound (c : ChargingData) (hγ : c.gamma = 1/8) {U : Finset ℕ}
    (hU : (U.card : ℚ) ≤ c.gamma * c.W.card) :
    (U.card : ℚ) ≤ (2/5) * c.Z0.card + (1/5) * c.G0.card := by
  have hW := guarded_W_bound c hγ
  rw [hγ] at hU
  linarith

/-- **Unguarded budget at `γ = 1/8`.**  `|W| ≤ (16/5)|Z₀|`. -/
theorem unguarded_W_bound (c : ChargingData) (hγ : c.gamma = 1/8) (hG : c.G0 = ∅) :
    (c.W.card : ℚ) ≤ (16/5) * c.Z0.card := by
  have h := unguarded_charging c hG
  rw [hγ] at h
  linarith

/-- **Unguarded branching budget at `γ = 1/8`.**  `|U| ≤ (2/5)|Z₀|`. -/
theorem unguarded_U_bound (c : ChargingData) (hγ : c.gamma = 1/8) (hG : c.G0 = ∅) {U : Finset ℕ}
    (hU : (U.card : ℚ) ≤ c.gamma * c.W.card) :
    (U.card : ℚ) ≤ (2/5) * c.Z0.card := by
  have hW := unguarded_W_bound c hγ hG
  rw [hγ] at hU
  linarith

/-! ## 5.  Branching-bit budget -/

/-- **Branching-bit budget (kernel).**  If every absorbed row contributes at most `b` branching
bits, the whole absorption tree spends at most `b·((16/5) z₀ + (8/5) g₀)` bits. -/
theorem branching_bits_le (c : ChargingData) (hγ : c.gamma = 1/8) (b : ℕ) (bits : ℚ)
    (hbits : bits ≤ b * c.W.card) :
    bits ≤ (b : ℚ) * ((16/5) * c.Z0.card + (8/5) * c.G0.card) := by
  have hW := guarded_W_bound c hγ
  have hb : (0:ℚ) ≤ (b : ℚ) := by positivity
  nlinarith [hW, hbits, hb]

/-! ## 6.  Scope firewall -/

/-- **Firewall.**  The finite charging theorems are bounds *given* a charging datum; they do not
assert that any absorbed row family, row completion or zero set exists.  Formally, a universally
quantified implication never inhabits its own hypothesis. -/
theorem charging_does_not_give_existence :
    ¬ ∀ (H C : ChargingData → Prop), (∀ c, H c → C c) → ∃ c, H c := by
  intro h
  obtain ⟨c, hc⟩ := h (fun _ => False) (fun _ => True) (fun _ h => h.elim)
  exact hc

/-- **Firewall.**  A bound on `|W|` in terms of `|Z₀|` is vacuous when the configuration does not
exist: with an empty zero set and empty row family every budget above is satisfied, and no
completion has been produced. -/
theorem trivial_charging_datum_exists :
    ∃ c : ChargingData, c.Z0 = ∅ ∧ c.W = ∅ ∧ c.gamma = 1/8 :=
  ⟨{ Z0 := ∅, G0 := ∅, W := ∅, chargedZ := ∅, chargedG := ∅,
     siteZ := id, siteG := id,
     chargedZ_sub := by simp, chargedG_sub := by simp,
     siteZ_maps := by simp, siteG_maps := by simp,
     siteZ_fibre := by simp, siteG_fibre := by simp,
     gamma := 1/8, escape := by norm_num }, rfl, rfl, rfl⟩

end Absorption
end ResearchBankV7
end Erdos287
