import Mathlib
import RequestProject.Erdos287.DIKuznetsov3221Interface
import RequestProject.TrustedBank.FixedAffine.UnitTransport

/-!
# V18, Phase E — the literal 3221 normal-form *source pin*

`3221-LITERAL-NORMALFORM-SOURCE-PIN45 : SOURCE_BLOCKED / UNINHABITED`.

## What the repository actually contains

A repository-wide search for the objects a completed balanced-seven dispersion normal form
would need finds:

* **present** — an abstract Kloosterman-shaped finite sum with its exact unit-change
  (reindexing) identity, `TrustedBank.UnitTransport.kloostermanLike` and
  `kloostermanLike_unit_change`;
* **present** — the V17 finite off-diagonal package (`Erdos287.OffDiag3221`), the finite
  diagonal package (`Erdos287.Diagonal3221`), the `(e,h)` no-wrap/collision package
  (`Erdos287.EHNoWrap3221`) and the source *data record*
  `Erdos287.DI3221.BalancedSeven3221CompletedSource`;
* **absent** — any dispersion identity, any Poisson/completion identity, any additive
  character attached to the physical source, any `gcd` extraction lemma for the physical
  source, and any low-conductor projection of the physical source.

Consequently the completed nondegenerate child

```
K_λ = ∑_{r,s} (∑_m a_{m,r,s}) (∑_n e(n ω_{r,s})) (∑_c g_λ(s,c) S(·,·; s c))
```

**is not derived here and is not asserted here.**  It is *pinned* as the shape of the data
that a future derivation would have to produce: the structure below records it as an exact
equality field on explicitly given finite data, with no free `Prop` field, and **no
inhabitant is constructed anywhere in this project**.

What *is* proved here is the elementary, unconditional infrastructure that any such normal
form would use: the additive phase and its mod-1 representative invariance, the norm-one
property, the Kloosterman unit-change identity transported to the pinned data, and the
`ω`-dependence classification together with its counterguard (dependence on the product
`r s` is strictly stronger than dependence on the ordered pair `(r,s)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace Erdos287
namespace NormalForm3221

open Erdos287.DI3221

/-! ## §1. The additive phase `e(x)` and mod-1 representative invariance -/

/-- The additive phase `e(x) = exp(2πi x)`. -/
noncomputable def phase (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

/-- **Representative invariance mod 1**: the phase only depends on `x` modulo `ℤ`. -/
theorem phase_int_add (x : ℝ) (k : ℤ) : phase (x + (k : ℝ)) = phase x := by
  unfold phase
  have h : ((2 * Real.pi * (x + (k : ℝ)) : ℝ) : ℂ) * Complex.I
      = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I + (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The canonical representative in `[0,1)` gives the same phase. -/
theorem phase_fract (x : ℝ) : phase (Int.fract x) = phase x := by
  have h := phase_int_add (Int.fract x) ⌊x⌋
  rw [Int.fract_add_floor] at h
  exact h.symm

/-- Two representatives differing by an integer give the same phase. -/
theorem phase_congr {x y : ℝ} (k : ℤ) (h : x - y = (k : ℝ)) : phase x = phase y := by
  have hx : x = y + (k : ℝ) := by linarith
  rw [hx, phase_int_add]

/-- The phase is unimodular. -/
theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

/-! ## §2. `ω`-dependence classification

Which variables the phase `ω_{r,s}` is allowed to depend on is *source data*, never a
consequence of nomenclature.  The four admissible classifications are recorded as
predicates, with the implications that actually hold and a counterguard for the one that
does not. -/

/-- `ω` depends on `r` only. -/
def OmegaDependsOnR (om : ℕ → ℕ → ℝ) : Prop := ∀ r s₁ s₂, om r s₁ = om r s₂

/-- `ω` depends on `s` only. -/
def OmegaDependsOnS (om : ℕ → ℕ → ℝ) : Prop := ∀ r₁ r₂ s, om r₁ s = om r₂ s

/-- `ω` depends on the product `r s` only. -/
def OmegaDependsOnProduct (om : ℕ → ℕ → ℝ) : Prop :=
  ∃ f : ℕ → ℝ, ∀ r s, om r s = f (r * s)

/-- `ω` depends on the ordered pair `(r,s)` — the weakest classification, always true. -/
def OmegaDependsOnPair (om : ℕ → ℕ → ℝ) : Prop := ∃ f : ℕ → ℕ → ℝ, ∀ r s, om r s = f r s

theorem omegaDependsOnPair (om : ℕ → ℕ → ℝ) : OmegaDependsOnPair om := ⟨om, fun _ _ => rfl⟩

theorem omegaDependsOnPair_of_product {om : ℕ → ℕ → ℝ} (h : OmegaDependsOnProduct om) :
    OmegaDependsOnPair om := by
  obtain ⟨f, hf⟩ := h
  exact ⟨fun r s => f (r * s), hf⟩

/-- **Counterguard.**  Product-dependence is *strictly* stronger than pair-dependence:
`(r,s) ↦ r s` is not injective (`1·6 = 2·3`), so a phase separating `(1,6)` from `(2,3)`
depends on the ordered pair and not on the product. -/
theorem omega_product_strictly_stronger :
    ∃ om : ℕ → ℕ → ℝ, OmegaDependsOnPair om ∧ ¬ OmegaDependsOnProduct om := by
  refine ⟨fun r _ => (r : ℝ), omegaDependsOnPair _, ?_⟩
  rintro ⟨f, hf⟩
  have h1 : (1 : ℝ) = f 6 := by simpa using hf 1 6
  have h2 : (2 : ℝ) = f 6 := by simpa using hf 2 3
  rw [← h1] at h2
  norm_num at h2

/-! ## §3. The pinned normal form — `SOURCE_BLOCKED`, never inhabited -/

/-- **`3221-LITERAL-NORMALFORM-SOURCE-PIN45` — `SOURCE_BLOCKED / UNINHABITED`.**

The exact data a completed balanced-seven `3221` normal form must supply, on top of the
V17 source dictionary `S`: the `(r,s)` factorisation of the modulus, the `m`-coefficient
family `a_{m,r,s}`, the phase `ω_{r,s}`, the `c`-weight, the Kloosterman leg with modulus
`s c`, the unit/gcd/zero-mode/low-conductor routing conditions, and — the load-bearing
field — the **literal equality** between the completed value of `S` and the normal-form
expression.

Every field is a concrete equality, inequality or support condition; there is no free
`Prop` field, and **no inhabitant is constructed anywhere in this project**.  In particular
nothing downstream of this structure is unconditional. -/
structure BalancedSeven3221NormalForm (S : BalancedSeven3221CompletedSource) where
  /-- The `r` box (first modulus factor). -/
  Rbox : Finset ℕ
  /-- The `s` box (second modulus factor, also part of the Kloosterman modulus). -/
  Sbox : Finset ℕ
  /-- The `m` box. -/
  Mbox : Finset ℕ
  /-- The `c` box (Kloosterman modulus cofactor). -/
  Cbox : Finset ℕ
  /-- The `n` box (the phase variable). -/
  Nbox : Finset ℤ
  /-- `q = r s` with the two factors coprime. -/
  modulus_coprime : ∀ r ∈ Rbox, ∀ s ∈ Sbox, Nat.Coprime r s
  /-- The factorised moduli are moduli of the source dictionary. -/
  modulus_mem : ∀ r ∈ Rbox, ∀ s ∈ Sbox, r * s ∈ S.Qbox
  /-- The phase `ω_{r,s}`, as a real representative (only its class mod 1 matters). -/
  omega : ℕ → ℕ → ℝ
  /-- The coefficient family `a_{m,r,s}`. -/
  coeff : ℕ → ℕ → ℕ → ℂ
  /-- The `c`-weight `g_λ(s,c)`. -/
  cWeight : ℕ → ℕ → ℂ
  /-- The additive-character-shaped kernel used by the Kloosterman leg. -/
  psi : (q : ℕ) → ZMod q → ℂ
  /-- First Kloosterman argument. -/
  argA : (s c : ℕ) → ZMod (s * c)
  /-- Second Kloosterman argument. -/
  argB : (s c : ℕ) → ZMod (s * c)
  /-- The value of the Kloosterman leg. -/
  kloostLeg : ℕ → ℕ → ℂ
  /-- The Kloosterman modulus `s c` is nonzero on the boxes. -/
  kloost_ne : ∀ s ∈ Sbox, ∀ c ∈ Cbox, s * c ≠ 0
  /-- **The Kloosterman leg really is a Kloosterman-shaped sum of modulus `s c`.** -/
  kloostLeg_eq : ∀ (s : ℕ) (hs : s ∈ Sbox) (c : ℕ) (hc : c ∈ Cbox),
    kloostLeg s c =
      @TrustedBank.UnitTransport.kloostermanLike (s * c) ⟨kloost_ne s hs c hc⟩ ℂ _
        (psi (s * c)) (argA s c) (argB s c)
  /-- Unit condition on the `m` variable. -/
  unit_m : ∀ m ∈ Mbox, ∀ r ∈ Rbox, ∀ s ∈ Sbox, Nat.Coprime m (r * s)
  /-- gcd routing: the `r` factor and the Kloosterman cofactor are coprime. -/
  gcd_routing : ∀ r ∈ Rbox, ∀ c ∈ Cbox, Nat.Coprime r c
  /-- Zero-mode routing: the `n = 0` mode is not part of the completed sum. -/
  zero_mode_routed : (0 : ℤ) ∉ Nbox
  /-- Low-conductor routing: small `r` are handled elsewhere. -/
  lowConductor_routed : ∀ r ∈ Rbox, S.lowConductorCut < r
  /-- **The literal completed normal form.** -/
  normalForm :
    S.completedValue
      = ∑ r ∈ Rbox, ∑ s ∈ Sbox,
          (∑ m ∈ Mbox, coeff m r s) *
          (∑ n ∈ Nbox, phase ((n : ℝ) * omega r s)) *
          (∑ c ∈ Cbox, cWeight s c * kloostLeg s c)
  /-- Theorem-parameter metadata: the `r` scale. -/
  R0 : ℚ
  /-- Theorem-parameter metadata: the `s` scale. -/
  S0 : ℚ
  /-- Theorem-parameter metadata: the `m` scale. -/
  M0 : ℚ
  /-- Theorem-parameter metadata: the `n` scale. -/
  N0 : ℚ
  /-- Theorem-parameter metadata: the `c` scale. -/
  C0 : ℚ
  /-- The level (modulus) scale of the current source. -/
  Qlevel : ℚ
  /-- The exceptional spectral parameter `Z_3221` of the current source.  This is
  *dictionary metadata*, not an analytic bound. -/
  Z : ℚ
  /-- Scales are positive. -/
  R0_pos : 0 < R0
  /-- Scales are positive. -/
  S0_pos : 0 < S0
  /-- Scales are positive. -/
  M0_pos : 0 < M0
  /-- Scales are positive. -/
  N0_pos : 0 < N0
  /-- Scales are positive. -/
  C0_pos : 0 < C0
  /-- Scales are positive. -/
  Qlevel_pos : 0 < Qlevel
  /-- The spectral parameter is nonnegative. -/
  Z_nonneg : 0 ≤ Z

namespace BalancedSeven3221NormalForm

variable {S : BalancedSeven3221CompletedSource} (F : BalancedSeven3221NormalForm S)

/-- **The phase leg only depends on `ω_{r,s}` modulo `1`**: replacing the representative
`ω_{r,s}` by any representative of the same class mod `1` leaves every integer mode of the
phase leg unchanged. -/
theorem phase_leg_congr (r s : ℕ) (k : ℤ) (om' : ℝ) (h : F.omega r s - om' = (k : ℝ))
    (n : ℤ) : phase ((n : ℝ) * F.omega r s) = phase ((n : ℝ) * om') := by
  refine phase_congr (n * k) ?_
  have h' : F.omega r s = om' + (k : ℝ) := by linarith
  rw [h']
  push_cast
  ring

/-- **The Kloosterman unit-change identity, transported to the pinned data.**  For any unit
`λ` of `ZMod (s c)` the Kloosterman leg is unchanged by `(A,B) ↦ (Aλ, Bλ⁻¹)`. -/
theorem kloostLeg_unit_change {s : ℕ} (hs : s ∈ F.Sbox) {c : ℕ} (hc : c ∈ F.Cbox)
    (lam : (ZMod (s * c))ˣ) :
    F.kloostLeg s c =
      @TrustedBank.UnitTransport.kloostermanLike (s * c) ⟨F.kloost_ne s hs c hc⟩ ℂ _
        (F.psi (s * c)) (F.argA s c * (lam : ZMod (s * c)))
        (F.argB s c * ((lam⁻¹ : (ZMod (s * c))ˣ) : ZMod (s * c))) := by
  haveI : NeZero (s * c) := ⟨F.kloost_ne s hs c hc⟩
  rw [F.kloostLeg_eq s hs c hc]
  exact TrustedBank.UnitTransport.kloostermanLike_unit_change _ _ _ lam

/-- The moduli occurring in the normal form are genuinely above the low-conductor cut. -/
theorem modulus_above_cut {r : ℕ} (hr : r ∈ F.Rbox) {s : ℕ} (hs0 : 0 < s) :
    S.lowConductorCut < r * s := by
  have h := F.lowConductor_routed r hr
  calc S.lowConductorCut < r := h
    _ ≤ r * s := Nat.le_mul_of_pos_right _ hs0

/-- The `(r,s)` factorisation is genuine data: the *same* modulus can arise from two
different coprime factorisations, so `(r,s)` can never be recovered from `q` alone. -/
theorem factorisation_is_data :
    ∃ r₁ s₁ r₂ s₂ : ℕ, r₁ * s₁ = 6 ∧ r₂ * s₂ = 6 ∧ Nat.Coprime r₁ s₁ ∧ Nat.Coprime r₂ s₂ ∧
      (r₁, s₁) ≠ (r₂, s₂) :=
  Erdos287.DI3221.modulus_factorisation_not_unique

end BalancedSeven3221NormalForm

/-! ## §4. Non-fabrication record

The structure above is **not** inhabited in this project, and no theorem here produces one.
The two missing ingredients are named exactly:

* a dispersion/completion identity for the physical balanced-seven source (absent);
* a Poisson summation step producing the `n`-phase leg (absent).

Until both are present in the repository, `3221-LITERAL-NORMALFORM-SOURCE-PIN45` stays
`SOURCE_BLOCKED`, and every consequence of it stays conditional. -/

end NormalForm3221
end Erdos287
