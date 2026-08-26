import Mathlib
import RequestProject.TrustedBank.FixedAffine.UnitTransport

/-!
# Challenge B — Gate 1B, the source-opened SW/Yang line  (**OPEN**)

**Status: OPEN.**  Nothing here is claimed as a proof of Gate 1B, and nothing here is
imported by `TrustedBank/`.

*NPCF-2C38 power lane: DEAD.*  It is not revived anywhere in this file (nor anywhere in
this project): the two exact completions produce arithmetic level-dependent Fourier
transforms rather than two genuine smooth multiplicative variables, so the Pascadi
Proposition 3.8 shape is unavailable on that lane.  The restart kept here is the exact
**one-completion** source with `β_{D,P} = μ_D · Λ_P` still linear.

This file contains three kinds of material, sharply separated:

1. *Proved algebra* — linearity/bilinearity of the one-completion coefficient
   `β_{D,P} = μ_D Λ_P`, and invariance of the reciprocal source under fixed-unit
   reindexing (the latter via the trusted Bank B identity).
2. *Proved arithmetic bookkeeping* — the dyadic exponent budget with the exact rational
   margin `1/104`.
3. *An explicit interface* recording what a published convolution-BV theorem would have
   to supply, together with the (proved) derivation of the Gate conclusion **from that
   interface**.  The source-to-interface theorem is left open; no axiom is introduced,
   and no external theorem is postulated as a Lean fact.
-/

open scoped BigOperators

namespace Challenges
namespace Gate1B

/-! ## 1. The one-completion coefficient is still linear -/

variable {D P : Type*} [Fintype D] [Fintype P]

/-- The one-completion coefficient `β_{D,P} = μ_D · Λ_P`. -/
def beta (mu : D → ℂ) (Lam : P → ℂ) (d : D) (p : P) : ℂ := mu d * Lam p

omit [Fintype D] [Fintype P] in
/-- **Proved.**  `β` is separately additive in the `μ`-variable: the source stays
linear (no quadratic completion is introduced). -/
theorem beta_add_left (mu₁ mu₂ : D → ℂ) (Lam : P → ℂ) (d : D) (p : P) :
    beta (fun x => mu₁ x + mu₂ x) Lam d p = beta mu₁ Lam d p + beta mu₂ Lam d p := by
  simp [beta, add_mul]

omit [Fintype D] [Fintype P] in
/-- **Proved.**  `β` is separately additive in the `Λ`-variable. -/
theorem beta_add_right (mu : D → ℂ) (Lam₁ Lam₂ : P → ℂ) (d : D) (p : P) :
    beta mu (fun y => Lam₁ y + Lam₂ y) d p = beta mu Lam₁ d p + beta mu Lam₂ d p := by
  simp [beta, mul_add]

/-- **Proved.**  A `β`-weighted double sum against a *rank-one* test weight factorises
into a product of two linear forms — the bilinear (Type-II) shape. -/
theorem beta_double_sum_factorises (mu : D → ℂ) (Lam : P → ℂ) (u : D → ℂ) (v : P → ℂ) :
    ∑ d : D, ∑ p : P, beta mu Lam d p * (u d * v p)
      = (∑ d : D, mu d * u d) * (∑ p : P, Lam p * v p) := by
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun p _ => by simp [beta]; ring

/-! ## 2. Fixed-unit reindexing preserves the reciprocal source -/

/-- **Proved (Bank B).**  The reciprocal ("Kloosterman-shaped") source is invariant
under the fixed-unit substitution `(A, B) ↦ (Aλ, Bλ⁻¹)`. -/
theorem reciprocal_source_unit_invariance {q : ℕ} [NeZero q] (ψ : ZMod q → ℂ)
    (A B : ZMod q) (lam : (ZMod q)ˣ) :
    TrustedBank.UnitTransport.kloostermanLike ψ A B
      = TrustedBank.UnitTransport.kloostermanLike ψ (A * (lam : ZMod q))
          (B * ((lam⁻¹ : (ZMod q)ˣ) : ZMod q)) :=
  TrustedBank.UnitTransport.kloostermanLike_unit_change ψ A B lam

/-! ## 3. The dyadic exponent budget with the exact `1/104` margin -/

/-- The dyadic exponent bookkeeping of the Gate: a level of distribution `θ` supplied by
the convolution-BV input, the exponent `needed` demanded by the Gate, and the exact
rational margin `1/104`. -/
structure DyadicBudget where
  /-- the level of distribution supplied -/
  θ : ℚ
  /-- the exponent the Gate needs -/
  needed : ℚ
  /-- the margin -/
  margin : ℚ
  /-- the margin is exactly `1/104` -/
  hmargin : margin = 1 / 104
  /-- the supplied level is `1/2` plus the margin -/
  hθ : θ = 1 / 2 + margin
  /-- the Gate's requirement -/
  hneeded : needed ≤ 1 / 2 + 1 / 104

/-- **Proved.**  With the exact `1/104` margin the budget closes: the required exponent
never exceeds the supplied level. -/
theorem budget_closes (B : DyadicBudget) : B.needed ≤ B.θ := by
  rw [B.hθ, B.hmargin]
  exact B.hneeded

/-- **Proved.**  The margin is strictly positive, i.e. the budget is not on the nose. -/
theorem margin_pos (B : DyadicBudget) : 0 < B.margin := by
  rw [B.hmargin]; norm_num

/-! ## 4. The convolution-BV interface (source-to-interface theorem left OPEN) -/

/-- Everything a published convolution-type Bombieri–Vinogradov theorem would have to
supply for this Gate, recorded explicitly so that no theorem name can be waved at.

`BV θ` is the (abstract) assertion that the required convolution estimate holds at level
of distribution `θ`; `mono` is the standard monotonicity of such an estimate in the
level; `hθ` says the supplied level clears `1/2 + 1/104`. -/
structure ConvolutionBVInterface where
  /-- the level of distribution the interface supplies -/
  θ : ℚ
  /-- the abstract convolution-BV assertion at a given level -/
  BV : ℚ → Prop
  /-- the estimate holds at the supplied level -/
  hBV : BV θ
  /-- the estimate is monotone in the level -/
  mono : ∀ a b : ℚ, a ≤ b → BV b → BV a
  /-- the supplied level clears the Gate requirement -/
  hθ : 1 / 2 + 1 / 104 ≤ θ

/-- **Proved.**  The Gate conclusion — the convolution estimate at the required level
`1/2 + 1/104` — follows from the interface.  What remains open is exactly the
*source-to-interface* theorem: producing a `ConvolutionBVInterface` from the
authoritative one-completion source (q-side SW/Yang, or the v-side labelled-convolution
fallback). -/
theorem gate1B_conclusion_of_interface (I : ConvolutionBVInterface) :
    I.BV (1 / 2 + 1 / 104) :=
  I.mono _ _ I.hθ I.hBV

/-- **The open statement.**  There exists a convolution-BV interface arising from the
authoritative one-completion source.  This is a `Prop`-valued definition, *not* a
theorem. -/
def SourceToInterface (source : Type) : Prop :=
  Nonempty (source → ConvolutionBVInterface)

end Gate1B
end Challenges
