import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V23 §1: the exact principal CRT measure

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Principal model for the prime form `L_i(t) = A_i t + 1`: the base residue `t ≡ t_W (mod W0)` is
fixed with `gcd(A_i t_W + 1, A_i W0) = 1`, and `t (mod L0)` is uniformly distributed over the
compatible residues for which `A_i t + 1` is a unit modulo `A_i L0` (`W0 ∣ L0`):

    T = { t < L0 : t ≡ t_W (mod W0),  gcd(A_i t + 1, A_i L0) = 1 }.

Kernel-proved finite CRT algebra (LEAN BANK):
* **`crt_count`** — `|T| · φ(A_i W0) = φ(A_i L0)` (the reduction map on units
  `(ℤ/A_i L0)^× → (ℤ/A_i W0)^×` is surjective with equal fibres, and `t ↦ A_i t + 1` identifies
  `T` with one fibre);
* **`principal_prob`** — for a compatible residue `t0 < L0`,

      Prob_i(t ≡ t0 mod L0) = φ(A_i W0)/φ(A_i L0) · 1(gcd(A_i t0 + 1, A_i L0) = 1);

* **`principal_Li_identity`** — hence
  `Li_i(x)/φ(A_i W0) · Prob_i(t ≡ t0) = Li_i(x)/φ(A_i L0) · 1(unit)`.

The finite modulus `L0` here is the CRT modulus of the principal model; it is never passed as
a new modulus to any prime-distribution theorem.
-/

namespace Erdos287
namespace ResearchBankV23
namespace PrincipalCRTMeasure

open Finset

/-- The compatible unit residues `T`. -/
def compatSet (A W0 L0 tW : ℕ) : Finset ℕ :=
  (range L0).filter fun t => t ≡ tW [MOD W0] ∧ Nat.Coprime (A * t + 1) (A * L0)

/-- Fibres of a surjective hom of finite groups: `|fibre| · |H| = |G|`. -/
theorem card_fiber_mul {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H] [DecidableEq H]
    (f : G →* H) (hf : Function.Surjective f) (c : H) :
    (univ.filter fun g => f g = c).card * Fintype.card H = Fintype.card G := by
  have hall : ∀ y : H, (univ.filter fun g => f g = y).card =
      (univ.filter fun g => f g = c).card := fun y =>
    MonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf c)
  have := card_eq_sum_card_fiberwise (s := (univ : Finset G)) (t := (univ : Finset H)) (f := f)
    (fun _ _ => Finset.mem_coe.2 (mem_univ _))
  simp only [card_univ] at this
  rw [this]
  simp_rw [hall]
  rw [sum_const, card_univ, smul_eq_mul, mul_comm]

variable {A W0 L0 tW : ℕ}

/-- **The CRT count** `|T| · φ(A W0) = φ(A L0)`. -/
theorem crt_count (hA : 0 < A) (hW : 0 < W0) (hL : 0 < L0) (hWL : W0 ∣ L0)
    (hc : Nat.Coprime (A * tW + 1) (A * W0)) :
    (compatSet A W0 L0 tW).card * Nat.totient (A * W0) = Nat.totient (A * L0) := by
  have hm : 0 < A * L0 := Nat.mul_pos hA hL
  haveI : NeZero (A * L0) := ⟨hm.ne'⟩
  haveI : NeZero (A * W0) := ⟨(Nat.mul_pos hA hW).ne'⟩
  have hdvd : A * W0 ∣ A * L0 := Nat.mul_dvd_mul_left A hWL
  set f := ZMod.unitsMap hdvd
  set c : (ZMod (A * W0))ˣ := ZMod.unitOfCoprime (A * tW + 1) hc
  have hfib := card_fiber_mul f (ZMod.unitsMap_surjective hdvd) c
  rw [ZMod.card_units_eq_totient, ZMod.card_units_eq_totient] at hfib
  rw [← hfib]
  congr 1
  refine card_bij (fun t ht => ZMod.unitOfCoprime (A * t + 1) (mem_filter.1 ht).2.2) ?_ ?_ ?_
  · intro t ht
    simp only [mem_filter, mem_univ, true_and]
    have ht' := (mem_filter.1 ht).2.1
    apply Units.ext
    rw [ZMod.unitsMap_val]
    simp only [ZMod.coe_unitOfCoprime, c]
    rw [ZMod.cast_natCast hdvd, ZMod.natCast_eq_natCast_iff]
    exact (Nat.ModEq.mul_left' A ht').add_right 1
  · intro t ht t' ht' h
    have h1 := congrArg (fun u : (ZMod (A * L0))ˣ => (u : ZMod (A * L0))) h
    simp only [ZMod.coe_unitOfCoprime] at h1
    rw [ZMod.natCast_eq_natCast_iff] at h1
    have h2 : A * t ≡ A * t' [MOD A * L0] := Nat.ModEq.add_right_cancel' 1 h1
    have h3 : t ≡ t' [MOD L0] := Nat.ModEq.mul_left_cancel' hA.ne' h2
    have ht1 := mem_range.1 (mem_filter.1 ht).1
    have ht2 := mem_range.1 (mem_filter.1 ht').1
    unfold Nat.ModEq at h3
    rwa [Nat.mod_eq_of_lt ht1, Nat.mod_eq_of_lt ht2] at h3
  · intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    set n := (u : ZMod (A * L0)).val with hn
    have hnu : ((n : ℕ) : ZMod (A * L0)) = u := ZMod.natCast_zmod_val _
    -- reduction of `n` modulo `A W0`
    have hred : n ≡ A * tW + 1 [MOD A * W0] := by
      have h1 := congrArg (fun v : (ZMod (A * W0))ˣ => (v : ZMod (A * W0))) hu
      simp only [c, ZMod.coe_unitOfCoprime] at h1
      rw [show (f u : ZMod (A * W0)) = ((u : ZMod (A * L0)).cast) from
        ZMod.unitsMap_val hdvd u] at h1
      rw [← hnu, ZMod.cast_natCast hdvd] at h1
      exact (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
    have hmodA : n ≡ 1 [MOD A] := by
      have := Nat.ModEq.of_mul_right W0 hred
      refine this.trans ?_
      unfold Nat.ModEq; simp [Nat.add_mod]
    -- choose `q` with `A q + 1 = n + A L0`
    have hdivA : A ∣ n + A * L0 - 1 := by
      have h1 : (n + A * L0 - 1) % A = 0 := by
        have hn1 : n % A = 1 % A := hmodA
        have : n + A * L0 - 1 + 1 = n + A * L0 := by omega
        have h2 : (n + A * L0 - 1 + 1) % A = (0 + 1) % A := by
          rw [this, Nat.add_mul_mod_self_left, hn1]
        exact (Nat.ModEq.add_right_cancel' 1 h2)
      exact Nat.dvd_of_mod_eq_zero h1
    obtain ⟨q, hq⟩ := hdivA
    set t := q % L0
    have htL : t < L0 := Nat.mod_lt _ hL
    have hAt : A * t + 1 ≡ n [MOD A * L0] := by
      have e1 : A * t ≡ A * q [MOD A * L0] := Nat.ModEq.mul_left' A (Nat.mod_modEq q L0)
      have e2 : A * q + 1 = n + A * L0 := by omega
      calc A * t + 1 ≡ A * q + 1 [MOD A * L0] := e1.add_right 1
        _ = n + A * L0 := e2
        _ ≡ n [MOD A * L0] := by unfold Nat.ModEq; simp
    have hcop : Nat.Coprime (A * t + 1) (A * L0) := by
      have hu' : Nat.Coprime n (A * L0) := by
        have := ZMod.val_coe_unit_coprime u
        exact this
      rw [Nat.Coprime, Nat.ModEq.gcd_eq hAt]
      exact hu'
    have hcompat : t ≡ tW [MOD W0] := by
      have e1 : A * t + 1 ≡ A * tW + 1 [MOD A * W0] :=
        (Nat.ModEq.of_mul_right (L0 / W0) (by
          rw [mul_assoc, Nat.mul_div_cancel' hWL]; exact hAt)).trans hred
      exact Nat.ModEq.mul_left_cancel' hA.ne' (Nat.ModEq.add_right_cancel' 1 e1)
    refine ⟨t, mem_filter.2 ⟨mem_range.2 htL, hcompat, hcop⟩, ?_⟩
    apply Units.ext
    simp only [ZMod.coe_unitOfCoprime]
    rw [← hnu, ZMod.natCast_eq_natCast_iff]
    exact hAt

/-- The principal probability `Prob_i(t ≡ t0 mod L0)` (uniform on `T`). -/
noncomputable def principalProb (A W0 L0 tW t0 : ℕ) : ℝ :=
  if t0 ∈ compatSet A W0 L0 tW then 1 / ((compatSet A W0 L0 tW).card : ℝ) else 0

/-- **The principal CRT probability**
`Prob_i(t ≡ t0) = φ(A W0)/φ(A L0) · 1(gcd(A t0 + 1, A L0) = 1)` for compatible `t0 < L0`. -/
theorem principal_prob (hA : 0 < A) (hW : 0 < W0) (hL : 0 < L0) (hWL : W0 ∣ L0)
    (hc : Nat.Coprime (A * tW + 1) (A * W0)) {t0 : ℕ} (ht0 : t0 < L0)
    (hcompat : t0 ≡ tW [MOD W0]) :
    principalProb A W0 L0 tW t0 =
      (Nat.totient (A * W0) : ℝ) / Nat.totient (A * L0) *
        (if Nat.gcd (A * t0 + 1) (A * L0) = 1 then 1 else 0) := by
  have hcount := crt_count hA hW hL hWL hc
  have hφW : 0 < Nat.totient (A * W0) := Nat.totient_pos.2 (Nat.mul_pos hA hW)
  have hφL : 0 < Nat.totient (A * L0) := Nat.totient_pos.2 (Nat.mul_pos hA hL)
  have hT : ((compatSet A W0 L0 tW).card : ℝ) =
      (Nat.totient (A * L0) : ℝ) / Nat.totient (A * W0) := by
    rw [eq_div_iff (by exact_mod_cast hφW.ne')]
    exact_mod_cast hcount
  unfold principalProb
  by_cases hg : Nat.gcd (A * t0 + 1) (A * L0) = 1
  · rw [if_pos (show t0 ∈ compatSet A W0 L0 tW from mem_filter.2 ⟨mem_range.2 ht0, hcompat, hg⟩),
      if_pos hg, hT]
    have : (Nat.totient (A * L0) : ℝ) ≠ 0 := by exact_mod_cast hφL.ne'
    have : (Nat.totient (A * W0) : ℝ) ≠ 0 := by exact_mod_cast hφW.ne'
    field_simp
  · rw [if_neg (by intro h; unfold compatSet at h; exact hg (mem_filter.1 h).2.2), if_neg hg,
      mul_zero]

/-- **The principal `Li` identity**
`Li_i(x)/φ(A W0) · Prob_i(t ≡ t0) = Li_i(x)/φ(A L0) · 1(unit)`. -/
theorem principal_Li_identity (hA : 0 < A) (hW : 0 < W0) (hL : 0 < L0) (hWL : W0 ∣ L0)
    (hc : Nat.Coprime (A * tW + 1) (A * W0)) {t0 : ℕ} (ht0 : t0 < L0)
    (hcompat : t0 ≡ tW [MOD W0]) (Li : ℝ) :
    Li / Nat.totient (A * W0) * principalProb A W0 L0 tW t0 =
      Li / Nat.totient (A * L0) * (if Nat.gcd (A * t0 + 1) (A * L0) = 1 then 1 else 0) := by
  rw [principal_prob hA hW hL hWL hc ht0 hcompat]
  have hφW : (Nat.totient (A * W0) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (Nat.mul_pos hA hW)).ne'
  field_simp

/-- Regression fixture: `A = 2, W0 = 1, L0 = 3, t_W = 0`: `T = {0, 2}` and
`|T| · φ(2) = 2 · 1 = 2 = φ(6)`. -/
theorem crt_count_fixture : compatSet 2 1 3 0 = {0, 2} ∧
    (compatSet 2 1 3 0).card * Nat.totient 2 = Nat.totient 6 := by
  refine ⟨by decide, by decide⟩

end PrincipalCRTMeasure
end ResearchBankV23
end Erdos287
