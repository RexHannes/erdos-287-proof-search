import Mathlib
import RequestProject.Erdos287.MuLogQCell3221
import RequestProject.CurrentProgramme.Erdos287WeightedSP2PhysicalSource

/-!
# Semantic repair layer §11–§13 — the exact centered `q`-cell and the seven-slot character
algebra

Everything in this file is **exact finite algebra**.  There is no analytic bound anywhere.

* §1 the centered `q`-cell
  `CenteredQCell s q n = 1_{n ≡ a_s(q)} − 1/φ(q)` with `a_s(q) = −s·2⁻¹ (mod q)`, the banked
  `Erdos287.V23QCell.aCoeff`, reused;
* §2 the exact routing identity `q ∣ 2n + s ↔ n ≡ a_s(q) (mod q)`, reusing the banked
  `aCoeff_spec`;
* §3 the exact character expansion on the unit sector,

  ```
      1_{n ≡ a_s(q)} − 1/φ(q) = (1/φ(q)) ∑_{χ ≠ χ₀} conj(χ(a_s(q))) χ(n),
  ```

  with `conj(χ(a)) = χ(a⁻¹)` proved (`conj_char_eq_char_inv`);
* §4 the exact seven-slot character product

  ```
      ∑_{pvec ∈ direct cell} ∏_j ω^phys_j(p_j) χ(∏_j p_j) = ∏_j S_j(χ),
  ```

  with **repeated-prime tuples included**: the direct product cell is not thinned.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace CenteredQCell

open Finset
open Erdos287.Vaughan
open Erdos287.V23QCell
open Erdos287.SP2Source
open Erdos287.StrictCellSingleton
open Erdos287.WeightedSP2

/-! ## §1.  The centered `q`-cell -/

/-- **`centeredQCell`** — the exact centered cell on the unit sector:

```
    centeredQCell s q n = 1_{n ≡ a_s(q) (mod q)} − 1/φ(q).
```
-/
noncomputable def centeredQCell (s : AffineSign) (q : ℕ) (n : ℤ) : ℂ :=
  (if (n : ZMod q) = aCoeff s q then (1 : ℂ) else 0) - ((q.totient : ℂ))⁻¹

/-- **`centeredQCell_dvd_iff`.**  `LEAN_PROVED` (reuses `aCoeff_spec`).

The exact finite routing identity `q ∣ 2n + s ↔ n ≡ a_s(q) (mod q)` for odd `q`. -/
theorem centeredQCell_dvd_iff {q : ℕ} [NeZero q] (hq : ¬ 2 ∣ q) (s : AffineSign) (n : ℤ) :
    ((q : ℤ) ∣ 2 * n + s.val) ↔ ((n : ZMod q) = aCoeff s q) :=
  aCoeff_spec hq s n

/-- On the divisibility locus the centered cell is `1 − 1/φ(q)`. -/
theorem centeredQCell_of_dvd {q : ℕ} [NeZero q] (hq : ¬ 2 ∣ q) (s : AffineSign) {n : ℤ}
    (h : (q : ℤ) ∣ 2 * n + s.val) :
    centeredQCell s q n = 1 - ((q.totient : ℂ))⁻¹ := by
  rw [centeredQCell, if_pos ((centeredQCell_dvd_iff hq s n).mp h)]

/-- Off the divisibility locus the centered cell is `−1/φ(q)`. -/
theorem centeredQCell_of_not_dvd {q : ℕ} [NeZero q] (hq : ¬ 2 ∣ q) (s : AffineSign) {n : ℤ}
    (h : ¬ ((q : ℤ) ∣ 2 * n + s.val)) :
    centeredQCell s q n = -((q.totient : ℂ))⁻¹ := by
  rw [centeredQCell, if_neg (fun hc => h ((centeredQCell_dvd_iff hq s n).mpr hc))]
  ring

/-! ## §2.  Conjugation of character values -/

/-- **`conj_char_eq_char_inv`.**  `LEAN_PROVED`.

For a unit residue, complex conjugation of a Dirichlet character value is evaluation at the
inverse residue. -/
theorem conj_char_eq_char_inv {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {a : ZMod q} (ha : IsUnit a) : (starRingEnd ℂ) (chi a) = chi a⁻¹ := by
  have h1 : chi a * chi a⁻¹ = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit _ ha, MulChar.map_one]
  have h2 : star (chi a) = (chi a)⁻¹ := by
    have h := MulChar.star_eq_inv chi
    have h3 : (star chi) a = chi⁻¹ a := by rw [h]
    simpa [MulChar.inv_apply_eq_inv'] using h3
  rw [show (starRingEnd ℂ) (chi a) = star (chi a) from rfl, h2]
  exact inv_eq_of_mul_eq_one_right h1

/-! ## §3.  Exact character orthogonality for the centered cell -/

/-- **`centeredQCell_character_expansion`.**  `LEAN_PROVED`.

The exact finite character algebra on the unit sector: for `gcd(n,q) = 1`,

```
    1_{n ≡ a_s(q)} − 1/φ(q) = (1/φ(q)) ∑_{χ ≠ χ₀} conj(χ(a_s(q))) χ(n).
```

No analytic input. -/
theorem centeredQCell_character_expansion {q : ℕ} [NeZero q] (hq : ¬ 2 ∣ q)
    (s : AffineSign) {n : ZMod q} (hn : IsUnit n) (hphi : 0 < q.totient) :
    (if n = aCoeff s q then (1 : ℂ) else 0) - ((q.totient : ℂ))⁻¹
      = ((q.totient : ℂ))⁻¹ *
          ∑ chi ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)),
            (starRingEnd ℂ) (chi (aCoeff s q)) * chi n := by
  classical
  have ha : IsUnit (aCoeff s q) := aCoeff_isUnit hq s
  have hne : ((q.totient : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hphi.ne'
  have hterm : ∀ chi : DirichletCharacter ℂ q,
      (starRingEnd ℂ) (chi (aCoeff s q)) * chi n = chi (aCoeff s q)⁻¹ * chi n := by
    intro chi; rw [conj_char_eq_char_inv chi ha]
  have htotal : ∑ chi : DirichletCharacter ℂ q,
      (starRingEnd ℂ) (chi (aCoeff s q)) * chi n
      = if aCoeff s q = n then (q.totient : ℂ) else 0 := by
    rw [Finset.sum_congr rfl (fun chi _ => hterm chi)]
    exact qCell_orthogonality ha n
  have hone : (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) (aCoeff s q)) *
      (1 : DirichletCharacter ℂ q) n = 1 := by
    rw [MulChar.one_apply ha, MulChar.one_apply hn]
    simp
  have herase : ∑ chi ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)),
      (starRingEnd ℂ) (chi (aCoeff s q)) * chi n
      = (if aCoeff s q = n then (q.totient : ℂ) else 0) - 1 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), htotal, hone]
  rw [herase]
  by_cases h : n = aCoeff s q
  · rw [if_pos h, if_pos h.symm]
    field_simp
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]
    ring

/-! ## §4.  The exact seven-slot character product -/

/-- **`slotTransform`** — the physical slot transform
`S_j(χ) = ∑_{p ∈ λ_j} ω^phys_j(p) χ(p)`. -/
noncomputable def slotTransform (C : SP2FixedCertificateData) (S : PhysicalSlotData)
    (q : ℕ) (chi : DirichletCharacter ℂ q) (j : Fin 7) : ℂ :=
  ∑ p ∈ C.lam j, omegaPhysical C S j p * chi ((p : ℕ) : ZMod q)

/-- **`sevenSlot_character_product`.**  `LEAN_PROVED`.

Exact product factorisation of the character transform of the direct seven-slot cell:

```
    ∑_{pvec ∈ ∏_j λ_j} (∏_j ω^phys_j(p_j)) χ(∏_j p_j) = ∏_j S_j(χ).
```

Repeated-prime tuples are **included**: the sum is over the full direct product cell. -/
theorem sevenSlot_character_product (C : SP2FixedCertificateData) (S : PhysicalSlotData)
    (q : ℕ) (chi : DirichletCharacter ℂ q) :
    ∑ v ∈ cellVectors C,
        (∏ j, omegaPhysical C S j (v j)) * chi ((pushforward v : ℕ) : ZMod q)
      = ∏ j, slotTransform C S q chi j := by
  classical
  have hstep : ∀ v : Fin 7 → ℕ,
      (∏ j, omegaPhysical C S j (v j)) * chi ((pushforward v : ℕ) : ZMod q)
        = ∏ j, (omegaPhysical C S j (v j) * chi ((v j : ℕ) : ZMod q)) := by
    intro v
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [pushforward, Nat.cast_prod, map_prod]
  rw [Finset.sum_congr rfl (fun v _ => hstep v)]
  simp only [slotTransform]
  rw [cellVectors]
  exact (Finset.prod_univ_sum C.lam
    (fun j p => omegaPhysical C S j p * chi ((p : ℕ) : ZMod q))).symm

/-- **`cellVectors_contains_repeats`.**  `LEAN_PROVED`.

Whenever two slots of the physical cell share a prime, the direct cell literally contains a
repeated-prime tuple.  This is the precise sense in which the seven-slot product identity
above covers the repeated-prime sector. -/
theorem cellVectors_contains_repeats {C : SP2FixedCertificateData} {i j : Fin 7}
    (hij : i ≠ j) {p : ℕ} (hpi : p ∈ C.lam i) (hpj : p ∈ C.lam j)
    (hne : ∀ k : Fin 7, (C.lam k).Nonempty) :
    ∃ v ∈ cellVectors C, ¬ Function.Injective v := by
  classical
  refine ⟨fun k => if k = i then p else if k = j then p else (hne k).choose, ?_, ?_⟩
  · rw [cellVectors, Fintype.mem_piFinset]
    intro k
    by_cases hki : k = i
    · subst hki; simpa using hpi
    · by_cases hkj : k = j
      · subst hkj; simp [hki, hpj]
      · simp only [hki, hkj, if_false]
        exact (hne k).choose_spec
  · intro hinj
    have : i = j := hinj (by simp)
    exact hij this

end CenteredQCell
end Erdos287
