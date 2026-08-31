import Mathlib
import RequestProject.CurrentProgramme.Erdos287TransverseGammaReduction
import RequestProject.CurrentProgramme.Erdos287BalancedBUnitaryFourierCompiler

/-!
# Bézout-row affine CRT algebra — Erdős #287 (append-only)

This module is **append-only**: it edits nothing, deletes nothing and reproves nothing.

It formalises the *exact finite arithmetic* of the Bézout row of the already-banked
one-conductor packet.  In the source normalisation the row data are

```
q = q̄_C ,   r = q_m = M₀ ,   A = Δ₀ A_C ,   B = Δ₀ h A_m ,
g = gcd(h A_m - A_C, r) ,     r = g r₀ ,     h = h_g + g ℓ ,
```

and the *reduced numerator coordinate* `γ_g(ℓ)` is pinned by its two CRT components

```
γ_g(ℓ) ≡ -A_C · g⁻¹      (mod m),
γ_g(ℓ) ≡ k_g + A_m · ℓ   (mod r₀).
```

Everything below is kernel-safe finite arithmetic.

**Hypothesis discipline.**

* No modular inverse is ever *introduced*: each inverse is a **field** of the data carrying its
  defining congruence (`gInv`, `u`, `v`), so the corresponding coprimality is supplied, never
  assumed silently.
* No global `gcd(r,m) = 1` assumption is made anywhere.  Only `gcd(m,r₀) = 1` is used, and only
  through the two supplied inverse fields.
* Nothing here asserts that the physical source has this shape, and nothing asserts any bound,
  saving, cancellation or closure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace TransverseBezoutRow

/-! ## §1  The Bézout-row data -/

/-- Exact Bézout-row data of a one-conductor packet.

`m`, `r₀` are the two coprime CRT moduli of the reduced numerator (`r = g · r₀`), `A_C`, `A_m`,
`k_g`, `h_g` are the integer source coefficients, and `gInv`, `u`, `v` are **supplied** modular
inverses, each with its defining congruence as a field.  No coprimality is assumed beyond what
these three fields state. -/
structure BezoutRowData where
  /-- First CRT modulus (the conductor component `m`). -/
  m : ℕ
  /-- Second CRT modulus: the reduced `r`-component `r₀ = r / g`. -/
  r0 : ℕ
  /-- The packet gcd `g`. -/
  g : ℕ
  /-- `0 < m`. -/
  m_pos : 0 < m
  /-- `0 < r₀`. -/
  r0_pos : 0 < r0
  /-- `0 < g`. -/
  g_pos : 0 < g
  /-- The `C`-side source numerator. -/
  A_C : ℤ
  /-- The `m`-side source numerator. -/
  A_m : ℤ
  /-- The constant of the `r₀`-component. -/
  k_g : ℤ
  /-- The base Bézout representative `h_g`. -/
  h_g : ℤ
  /-- A supplied inverse of `g` modulo `m`. -/
  gInv : ℤ
  /-- Its defining congruence. -/
  gInv_spec : (g : ℤ) * gInv ≡ 1 [ZMOD (m : ℤ)]
  /-- A supplied inverse of `r₀` modulo `m`. -/
  u : ℤ
  /-- Its defining congruence. -/
  u_spec : (r0 : ℤ) * u ≡ 1 [ZMOD (m : ℤ)]
  /-- A supplied inverse of `m` modulo `r₀`. -/
  v : ℤ
  /-- Its defining congruence. -/
  v_spec : (m : ℤ) * v ≡ 1 [ZMOD (r0 : ℤ)]

namespace BezoutRowData

variable (D : BezoutRowData)

/-- The unreduced `r`-modulus `r = g · r₀`. -/
def r : ℕ := D.g * D.r0

/-- The fused CRT modulus `M_g = m · r₀`. -/
def Mg : ℕ := D.m * D.r0

/-- **`r_eq`.**  `LEAN_PROVED`.  The exact splitting `r = g · r₀` holds by definition; no
division is performed. -/
theorem r_eq : D.r = D.g * D.r0 := rfl

/-- **`r_pos`.**  `LEAN_PROVED`. -/
theorem r_pos : 0 < D.r := Nat.mul_pos D.g_pos D.r0_pos

/-- **`Mg_pos`.**  `LEAN_PROVED`. -/
theorem Mg_pos : 0 < D.Mg := Nat.mul_pos D.m_pos D.r0_pos

/-- The `m`-component `c_m = -A_C · g⁻¹` of the reduced numerator coordinate. -/
def cM : ℤ := -D.A_C * D.gInv

/-- The `r₀`-component `d_ℓ = k_g + A_m ℓ`. -/
def dEll (ell : ℤ) : ℤ := D.k_g + D.A_m * ell

/-- The reduced numerator coordinate `γ_g(ℓ)`, built by explicit CRT from its two components. -/
def gammaG (ell : ℤ) : ℤ := D.cM * (D.r0 : ℤ) * D.u + D.dEll ell * (D.m : ℤ) * D.v

/-! ## §2  The two CRT congruences -/

/-- **`cM_spec`.**  `LEAN_PROVED`.  The inverse-free form of the `m`-component:
`g · c_m ≡ -A_C (mod m)`.  This is the statement that does **not** presuppose invertibility of
`g`; the inverse enters only through the supplied field `gInv_spec`. -/
theorem cM_spec : (D.g : ℤ) * D.cM ≡ -D.A_C [ZMOD (D.m : ℤ)] := by
  have h : (-D.A_C) * ((D.g : ℤ) * D.gInv) ≡ (-D.A_C) * 1 [ZMOD (D.m : ℤ)] :=
    Int.ModEq.mul_left _ D.gInv_spec
  calc (D.g : ℤ) * D.cM = (-D.A_C) * ((D.g : ℤ) * D.gInv) := by unfold cM; ring
    _ ≡ (-D.A_C) * 1 [ZMOD (D.m : ℤ)] := h
    _ = -D.A_C := by ring

/-- **`gammaG_mod_m`.**  `LEAN_PROVED`.  First CRT component:

`γ_g(ℓ) ≡ -A_C · g⁻¹  (mod m)`,

with `g⁻¹` the supplied inverse.  In particular the right-hand side does not depend on `ℓ`. -/
theorem gammaG_mod_m (ell : ℤ) : D.gammaG ell ≡ D.cM [ZMOD (D.m : ℤ)] := by
  have h1 : D.cM * ((D.r0 : ℤ) * D.u) ≡ D.cM * 1 [ZMOD (D.m : ℤ)] :=
    Int.ModEq.mul_left _ D.u_spec
  have h2 : D.dEll ell * ((D.m : ℤ) * D.v) ≡ D.dEll ell * 0 [ZMOD (D.m : ℤ)] :=
    Int.ModEq.mul_left _ (Int.modEq_zero_iff_dvd.mpr ⟨D.v, rfl⟩)
  have := h1.add h2
  calc D.gammaG ell = D.cM * ((D.r0 : ℤ) * D.u) + D.dEll ell * ((D.m : ℤ) * D.v) := by
        unfold gammaG; ring
    _ ≡ D.cM * 1 + D.dEll ell * 0 [ZMOD (D.m : ℤ)] := this
    _ = D.cM := by ring

/-- **`gammaG_mod_m_inverse_free`.**  `LEAN_PROVED`.  The inverse-free shape of the first CRT
component: `g · γ_g(ℓ) ≡ -A_C (mod m)`. -/
theorem gammaG_mod_m_inverse_free (ell : ℤ) :
    (D.g : ℤ) * D.gammaG ell ≡ -D.A_C [ZMOD (D.m : ℤ)] :=
  ((D.gammaG_mod_m ell).mul_left _).trans D.cM_spec

/-- **`gammaG_mod_r0`.**  `LEAN_PROVED`.  Second CRT component:

`γ_g(ℓ) ≡ k_g + A_m ℓ  (mod r₀)`. -/
theorem gammaG_mod_r0 (ell : ℤ) : D.gammaG ell ≡ D.k_g + D.A_m * ell [ZMOD (D.r0 : ℤ)] := by
  have h1 : D.cM * ((D.r0 : ℤ) * D.u) ≡ D.cM * 0 [ZMOD (D.r0 : ℤ)] :=
    Int.ModEq.mul_left _ (Int.modEq_zero_iff_dvd.mpr ⟨D.u, rfl⟩)
  have h2 : D.dEll ell * ((D.m : ℤ) * D.v) ≡ D.dEll ell * 1 [ZMOD (D.r0 : ℤ)] :=
    Int.ModEq.mul_left _ D.v_spec
  have := h1.add h2
  calc D.gammaG ell = D.cM * ((D.r0 : ℤ) * D.u) + D.dEll ell * ((D.m : ℤ) * D.v) := by
        unfold gammaG; ring
    _ ≡ D.cM * 0 + D.dEll ell * 1 [ZMOD (D.r0 : ℤ)] := this
    _ = D.k_g + D.A_m * ell := by unfold dEll; ring

/-- **`gammaG_affine_slope`.**  `LEAN_PROVED`.  The exact affine slope of the `r₀`-component:
`d_{ℓ+1} - d_ℓ = A_m`, as an integer identity (not merely a congruence). -/
theorem gammaG_affine_slope (ell : ℤ) : D.dEll (ell + 1) - D.dEll ell = D.A_m := by
  unfold dEll; ring

end BezoutRowData

/-! ## §3  Affine injectivity modulo `r₀` -/

/-- **`affine_residue_unique_of_unit_slope`.**  `LEAN_PROVED`.  Generic exact statement: if the
slope `s` is invertible modulo `d` (witness supplied), then an affine map `ℓ ↦ c + s ℓ` separates
residues modulo `d`. -/
theorem affine_residue_unique_of_unit_slope {d c s w e e' : ℤ} (hw : s * w ≡ 1 [ZMOD d])
    (h : c + s * e ≡ c + s * e' [ZMOD d]) : e ≡ e' [ZMOD d] := by
  have hs : s * e ≡ s * e' [ZMOD d] := by
    have := h.sub (Int.ModEq.refl c)
    simpa using this
  have hmul : (s * e) * w ≡ (s * e') * w [ZMOD d] := hs.mul_right w
  have h1 : e * (s * w) ≡ e * 1 [ZMOD d] := Int.ModEq.mul_left _ hw
  have h2 : e' * (s * w) ≡ e' * 1 [ZMOD d] := Int.ModEq.mul_left _ hw
  calc e = e * 1 := by ring
    _ ≡ e * (s * w) [ZMOD d] := h1.symm
    _ = (s * e) * w := by ring
    _ ≡ (s * e') * w [ZMOD d] := hmul
    _ = e' * (s * w) := by ring
    _ ≡ e' * 1 [ZMOD d] := h2
    _ = e' := by ring

/-- **`gammaG_affine_injective_mod_r0`.**  `LEAN_PROVED`.  Under an invertible slope `A_m`
modulo `r₀` (witness supplied), the map `ℓ ↦ k_g + A_m ℓ (mod r₀)` is injective modulo `r₀`:
two values of `ℓ` giving the same `r₀`-component are congruent modulo `r₀`. -/
theorem gammaG_affine_injective_mod_r0 (D : BezoutRowData) {w : ℤ}
    (hw : D.A_m * w ≡ 1 [ZMOD (D.r0 : ℤ)]) {e e' : ℤ}
    (h : D.dEll e ≡ D.dEll e' [ZMOD (D.r0 : ℤ)]) : e ≡ e' [ZMOD (D.r0 : ℤ)] :=
  affine_residue_unique_of_unit_slope hw h

/-- **`gammaG_affine_injective_zmod`.**  `LEAN_PROVED`.  The `ZMod r₀` form: if the slope is a
unit of `ZMod r₀`, the affine map `ℓ ↦ k + s ℓ` is an injective self-map of `ZMod r₀`. -/
theorem gammaG_affine_injective_zmod (n : ℕ) {s : ZMod n} (hs : IsUnit s) (k : ZMod n) :
    Function.Injective (fun e : ZMod n => k + s * e) := by
  intro e e' h
  simp only at h
  have hse : s * e = s * e' := by
    have := congrArg (fun z => z - k) h
    simpa using this
  obtain ⟨t, ht⟩ := hs.exists_left_inv
  calc e = (t * s) * e := by rw [ht, one_mul]
    _ = t * (s * e) := by ring
    _ = t * (s * e') := by rw [hse]
    _ = (t * s) * e' := by ring
    _ = e' := by rw [ht, one_mul]

/-! ## §4  Large-`g` router: the elementary residue-class core -/

/-- **`affineGcd_divisor_residue_class`.**  `LEAN_PROVED`.  The formal core of the large-`g`
router.  For any modulus `d` for which `A_m` is invertible (witness supplied), the condition

`d ∣ h A_m - A_C`

places `h` in a **single** residue class modulo `d`: any two solutions are congruent mod `d`.

No averaging, no harmonic weight and no tail bound is asserted here. -/
theorem affineGcd_divisor_residue_class {d A_C A_m w h h' : ℤ} (hw : A_m * w ≡ 1 [ZMOD d])
    (hh : d ∣ h * A_m - A_C) (hh' : d ∣ h' * A_m - A_C) : h ≡ h' [ZMOD d] := by
  have key : (-A_C) + A_m * h ≡ (-A_C) + A_m * h' [ZMOD d] := by
    have h1 : d ∣ ((-A_C) + A_m * h) - ((-A_C) + A_m * h') := by
      have : ((-A_C) + A_m * h) - ((-A_C) + A_m * h')
          = (h * A_m - A_C) - (h' * A_m - A_C) := by ring
      rw [this]
      exact dvd_sub hh hh'
    exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using h1))
  exact affine_residue_unique_of_unit_slope hw key

/-- **`affineGcd_solution_set_subset_class`.**  `LEAN_PROVED`.  Consequently, inside any
interval, the solution set of `d ∣ h A_m - A_C` is contained in one residue class mod `d`. -/
theorem affineGcd_solution_set_subset_class {A_C A_m w : ℤ} {d : ℕ}
    (hw : A_m * w ≡ 1 [ZMOD (d : ℤ)]) (a H : ℕ) {h₀ : ℕ}
    (hh₀ : h₀ ∈ (Finset.Ico a (a + H)).filter
      (fun h : ℕ => ((h : ℤ) * A_m - A_C) % (d : ℤ) = 0)) :
    (Finset.Ico a (a + H)).filter (fun h : ℕ => ((h : ℤ) * A_m - A_C) % (d : ℤ) = 0) ⊆
      (Finset.Ico a (a + H)).filter (fun h : ℕ => ((h : ℕ) : ZMod d) = ((h₀ : ℕ) : ZMod d)) := by
  intro h hh
  simp only [Finset.mem_filter] at hh hh₀ ⊢
  refine ⟨hh.1, ?_⟩
  have hcong : (h : ℤ) ≡ (h₀ : ℤ) [ZMOD (d : ℤ)] :=
    affineGcd_divisor_residue_class hw (Int.dvd_of_emod_eq_zero hh.2)
      (Int.dvd_of_emod_eq_zero hh₀.2)
  have hz : ((h : ℤ) : ZMod d) = ((h₀ : ℤ) : ZMod d) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr hcong
  simpa using hz

/-- **`affineGcd_interval_count`.**  `LEAN_PROVED`.  Finite counting form of the router core:
inside an interval of length `H`, the number of `h` with `d ∣ h A_m - A_C` is at most
`H / d + 1` (`ℕ`-division: the safe integer ceiling form).  No weighted average is claimed. -/
theorem affineGcd_interval_count {A_C A_m w : ℤ} {d : ℕ} (hd : 0 < d)
    (hw : A_m * w ≡ 1 [ZMOD (d : ℤ)]) (a H : ℕ) :
    ((Finset.Ico a (a + H)).filter
      (fun h : ℕ => ((h : ℤ) * A_m - A_C) % (d : ℤ) = 0)).card ≤ H / d + 1 := by
  set S := (Finset.Ico a (a + H)).filter
    (fun h : ℕ => ((h : ℤ) * A_m - A_C) % (d : ℤ) = 0) with hS
  rcases Finset.eq_empty_or_nonempty S with hemp | ⟨h₀, hh₀⟩
  · simp [hemp]
  · have hsub := affineGcd_solution_set_subset_class (A_C := A_C) hw a H (hS ▸ hh₀)
    exact le_trans (Finset.card_le_card hsub)
      (Erdos287.BalancedBUnitaryFourier.interval_residue_fibre_card_le d hd a H _)

end TransverseBezoutRow
end Erdos287
