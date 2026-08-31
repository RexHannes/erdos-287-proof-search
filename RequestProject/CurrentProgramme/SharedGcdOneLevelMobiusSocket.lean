import Mathlib
import RequestProject.CurrentProgramme.SharedGcdGramSquare
import RequestProject.CurrentProgramme.PrimitiveTRamanujanFirewall

/-!
# The one-level analytic sockets — Erdős #287, ONE-LEVEL MÖBIUS Δ, §§11, 13

Two analytic interfaces are **stated and never inhabited**.

§11 — `SharedGcdOneLevelEnergyInput`.  The research bound

```
|Q_H| ≪ (A+G)(GB+B²)/H · log^{o(1)} X
```

together with the claimed fixed-power closed subpolytope

```
κ > max(α,θ) + max(β,θ) - 1 + δ.
```

The ledger records the subpolytope **margin**; the socket is `PROVISIONAL` — the subpolytope is
*not* marked closed anywhere in the formal layer, and the input has no inhabitant.

Status: `DET1-SHAREDGCD-ONELEVEL-ENERGY45 : RESEARCH PROVISIONAL PASS ON STRICT SUBPOLYTOPE;
NANC AUDIT PENDING; FORMAL ANALYTIC INPUT UNINHABITED.`

§13 — `SharedGcdOneLevelMobiusGramInput`, the current first exact main-line residual

```
287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-MOBIUS-GRAM45.
```

Its configuration retains, literally, all four sources of the research object: **primitive `t`**
(never completed inside the socket), the **reciprocal `b`** source, the **friable `a`** source,
and the **harmonic/Perron** parameters.  The quantity bounded is the repository's own exact
one-level functional

```
∑_d λ_H(d)/d² ∑_a ρ(a) | ∑_m μ(m)/m ∑_t^* G̃_{dm}(t) e_{dm}(ta) |²,
```

built from `Erdos287.SharedGcdGram.lambdaH` and the repository's additive phase.  Only trivial
conditional consumers use these sockets, and each carries explicit refuting data.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset ArithmeticFunction
open scoped BigOperators

namespace Erdos287
namespace SharedGcdOneLevel

open Erdos287.SharedGcdGram
open Erdos287.NormalForm3221

/-! ## §11  The one-level energy ledger and its analytic input -/

/-- The bookkeeping ledger of the one-level energy bound.  Nothing here is asserted; the ledger
only records which configuration the research bound is claimed in. -/
structure EnergyLedger where
  /-- Length of the friable `a`-source. -/
  A : ℚ
  /-- Level scale `G`. -/
  G : ℚ
  /-- Length of the reciprocal `b`-source. -/
  B : ℚ
  /-- The shared-gcd projector scale `H`. -/
  H : ℚ
  /-- Exponent `α` of the `a`-source. -/
  alpha : ℚ
  /-- Exponent `β` of the `b`-source. -/
  beta : ℚ
  /-- Exponent `θ` of the level range. -/
  theta : ℚ
  /-- The target exponent `κ`. -/
  kappa : ℚ
  /-- The fixed-power gain `δ`. -/
  delta : ℚ
  /-- A `log^{o(1)}` slack factor, recorded as an explicit number ≥ 1. -/
  logSlack : ℚ

namespace EnergyLedger

variable (L : EnergyLedger)

/-- The margin by which `L` sits inside the claimed subpolytope
`κ > max(α,θ) + max(β,θ) - 1 + δ`. -/
def subpolytopeMargin : ℚ := L.kappa - (max L.alpha L.theta + max L.beta L.theta - 1 + L.delta)

/-- Well-formedness: positive scales, a genuine fixed-power gain, and *strict* membership in the
claimed subpolytope. -/
structure Valid : Prop where
  /-- The friable source is nonempty. -/
  A_pos : 0 < L.A
  /-- The level scale is positive. -/
  G_pos : 0 < L.G
  /-- The reciprocal source is nonempty. -/
  B_pos : 0 < L.B
  /-- The projector scale is positive. -/
  H_pos : 0 < L.H
  /-- The fixed-power gain is genuine. -/
  delta_pos : 0 < L.delta
  /-- The recorded logarithmic slack is at least `1`. -/
  logSlack_ge_one : 1 ≤ L.logSlack
  /-- **Strict** subpolytope membership. -/
  strict_subpolytope : 0 < L.subpolytopeMargin

end EnergyLedger

/-- A valid energy ledger exists, so the socket below is not vacuous. -/
theorem exists_valid_energyLedger : ∃ L : EnergyLedger, L.Valid := by
  refine ⟨⟨1, 1, 1, 1, 0, 0, 0, 1, 1/2, 1⟩, ?_⟩
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  show (0 : ℚ) < _
  unfold EnergyLedger.subpolytopeMargin
  norm_num

/-- **`SharedGcdOneLevelEnergyInput` — ANALYTIC / UNINHABITED.**

The research one-level energy bound

```
|Q_H| ≤ C · (A+G)(GB+B²)/H · log^{o(1)}X
```

on the strict subpolytope.  This is an analytic statement; it is **not** proved anywhere in
this repository and the structure has **no inhabitant**.  In particular the subpolytope is
*not* marked closed in the formal layer. -/
structure SharedGcdOneLevelEnergyInput (C : ℝ) (energy : EnergyLedger → ℝ) : Prop where
  /-- The implied constant is explicit and nonnegative. -/
  C_nonneg : 0 ≤ C
  /-- Only *strict* subpolytope configurations are covered. -/
  strict_subpolytope_only : ∀ L : EnergyLedger, L.Valid → 0 < L.subpolytopeMargin
  /-- The analytic target itself. -/
  energy_bound : ∀ L : EnergyLedger, L.Valid →
    |energy L| ≤ C * (((L.A + L.G) * (L.G * L.B + L.B ^ 2) / L.H : ℚ) : ℝ) * (L.logSlack : ℝ)

/-- **Conditional consumer.**  `CONDITIONAL / LEAN_PROVED`.  The antecedent is uninhabited, so
nothing unconditional follows. -/
theorem sharedGcdOneLevelEnergy_compiler {C : ℝ} {energy : EnergyLedger → ℝ}
    (inp : SharedGcdOneLevelEnergyInput C energy) (L : EnergyLedger) (hL : L.Valid) :
    |energy L| ≤ C * (((L.A + L.G) * (L.G * L.B + L.B ^ 2) / L.H : ℚ) : ℝ) * (L.logSlack : ℝ) :=
  inp.energy_bound L hL

/-- **`sharedGcdOneLevelEnergy_not_automatic`.**  `LEAN_PROVED`.

Explicit data refuting the energy socket, so it is a real hypothesis and not automatic. -/
theorem sharedGcdOneLevelEnergy_not_automatic :
    ∃ (C : ℝ) (energy : EnergyLedger → ℝ), ¬ SharedGcdOneLevelEnergyInput C energy := by
  refine ⟨0, fun _ => 1, ?_⟩
  intro h
  obtain ⟨L, hL⟩ := exists_valid_energyLedger
  have hb := h.energy_bound L hL
  simp at hb
  linarith

/-! ## §13  The one-level Möbius Gram socket -/

/-- The literal configuration of the one-level Möbius source: the shared-gcd projector, the
outer level set, the inner Möbius level set, the friable `a`-source with its density, the
**primitive** `t`-sets, the twists `G̃`, the reciprocal `b`-source and the harmonic/Perron
parameters. -/
structure OneLevelMobiusConfig where
  /-- The shared-gcd projector `Ω_H`. -/
  Om : ℕ → ℝ
  /-- The outer levels `d`. -/
  levels : Finset ℕ
  /-- The inner Möbius levels `m`. -/
  inner : Finset ℕ
  /-- The friable `a`-source. -/
  friable : Finset ℕ
  /-- The friable density `ρ`. -/
  rho : ℕ → ℝ
  /-- The **primitive** residues `t^*` modulo each level. -/
  primitiveT : ℕ → Finset ℤ
  /-- The twists `G̃_{dm}(t)`. -/
  Gt : ℕ → ℤ → ℂ
  /-- The reciprocal `b`-source. -/
  recip : ℕ → ℤ
  /-- The friability parameter. -/
  ySmooth : ℕ
  /-- The projector scale `H`. -/
  H : ℕ
  /-- The harmonic/Perron main parameter. -/
  X : ℝ
  /-- The harmonic/Perron truncation height. -/
  perronHeight : ℝ

namespace OneLevelMobiusConfig

variable (cfg : OneLevelMobiusConfig)

/-- The exact one-level Möbius source

```
∑_d λ_H(d)/d² ∑_a ρ(a) | ∑_m μ(m)/m ∑_t^* G̃_{dm}(t) e_{dm}(ta) |².
``` -/
noncomputable def source : ℝ :=
  ∑ d ∈ cfg.levels, lambdaH cfg.Om d / (d : ℝ) ^ 2 *
    ∑ a ∈ cfg.friable, cfg.rho a *
      ‖∑ m ∈ cfg.inner, ((moebius m : ℤ) : ℂ) / (m : ℂ) *
          ∑ t ∈ cfg.primitiveT (d * m),
            cfg.Gt (d * m) t * phase ((t : ℝ) * (a : ℝ) / ((d * m : ℕ) : ℝ))‖ ^ 2

/-- Well-formedness of a configuration: all four sources are the genuine ones. -/
structure Valid : Prop where
  /-- The outer levels are positive and squarefree. -/
  levels_ok : ∀ d ∈ cfg.levels, 0 < d ∧ Squarefree d
  /-- The inner levels are positive and squarefree. -/
  inner_ok : ∀ m ∈ cfg.inner, 0 < m ∧ Squarefree m
  /-- **Primitive `t`**: every retained frequency is a unit modulo its level.  The socket does
  *not* complete the primitive sum. -/
  primitive_t : ∀ g : ℕ, ∀ t ∈ cfg.primitiveT g, IsCoprime t (g : ℤ)
  /-- **Reciprocal `b` source**: the reciprocal argument is a unit at each outer level. -/
  reciprocal_unit : ∀ d ∈ cfg.levels, IsCoprime (2 * cfg.recip d) (d : ℤ)
  /-- **Friable `a` source**: every `a` is `y`-smooth. -/
  friable_source : ∀ a ∈ cfg.friable, ∀ p ∈ a.primeFactors, p ≤ cfg.ySmooth
  /-- The friable density is nonnegative. -/
  rho_nonneg : ∀ a, 0 ≤ cfg.rho a
  /-- The shared-gcd projector is supported above its scale. -/
  projector_support : ∀ e, e < cfg.H → cfg.Om e = 0
  /-- The projector scale is positive. -/
  H_pos : 0 < cfg.H
  /-- **Harmonic/Perron parameters** are positive. -/
  X_pos : 0 < cfg.X
  /-- The Perron truncation height is positive. -/
  perronHeight_pos : 0 < cfg.perronHeight

end OneLevelMobiusConfig

/-- A valid configuration exists with a strictly positive source, so the socket below is
neither vacuous nor trivially satisfiable. -/
theorem exists_valid_config_with_positive_source :
    ∃ cfg : OneLevelMobiusConfig, cfg.Valid ∧ cfg.source = 1 ∧ cfg.X = 1 ∧ cfg.H = 1 := by
  refine ⟨⟨fun e => if e = 1 then 1 else 0, {1}, {1}, {1}, fun _ => 1, fun _ => {1},
    fun _ _ => 1, fun _ => 1, 1, 1, 1, 1⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, rfl, rfl⟩
  · intro d hd
    simp at hd
    subst hd
    exact ⟨Nat.one_pos, squarefree_one⟩
  · intro m hm
    simp at hm
    subst hm
    exact ⟨Nat.one_pos, squarefree_one⟩
  · intro g t ht
    simp at ht
    subst ht
    exact isCoprime_one_left
  · intro d hd
    simp at hd
    subst hd
    simpa using (isCoprime_one_right : IsCoprime (2 : ℤ) 1)
  · intro a ha p hp
    simp at ha
    subst ha
    simp at hp
  · intro a
    norm_num
  · intro e he
    interval_cases e
    · norm_num
  · exact Nat.one_pos
  · norm_num
  · norm_num
  · show ∑ d ∈ ({1} : Finset ℕ), _ = (1 : ℝ)
    simp only [Finset.sum_singleton]
    have hlam : lambdaH (fun e => if e = 1 then 1 else 0) 1 = 1 := by
      simp [lambdaH]
    rw [hlam]
    simp
    exact Or.inl (Erdos287.SharedG0Router.norm_phase 1)

/-- **`SharedGcdOneLevelMobiusGramInput` — ANALYTIC / UNINHABITED.**

The exact missing analytic input of

```
287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-MOBIUS-GRAM45.
```

Uniformly over valid configurations, the one-level Möbius source is claimed to beat the trivial
scale by the projector saving `1/H`:

```
|source(cfg)| ≤ K · X / H.
```

Primitive `t` is retained and **not** completed inside the socket.  This structure has **no
inhabitant** anywhere in the repository. -/
structure SharedGcdOneLevelMobiusGramInput (K : ℝ) : Prop where
  /-- The implied constant is explicit and nonnegative. -/
  K_nonneg : 0 ≤ K
  /-- The primitive-`t` restriction is part of the hypothesis class, not discharged. -/
  primitive_t_retained : ∀ cfg : OneLevelMobiusConfig, cfg.Valid →
    ∀ g : ℕ, ∀ t ∈ cfg.primitiveT g, IsCoprime t (g : ℤ)
  /-- The analytic target itself. -/
  source_bound : ∀ cfg : OneLevelMobiusConfig, cfg.Valid →
    |cfg.source| ≤ K * cfg.X / (cfg.H : ℝ)

/-- **Conditional consumer.**  `CONDITIONAL / LEAN_PROVED`. -/
theorem sharedGcdOneLevelMobiusGram_compiler {K : ℝ}
    (inp : SharedGcdOneLevelMobiusGramInput K) (cfg : OneLevelMobiusConfig) (hcfg : cfg.Valid) :
    |cfg.source| ≤ K * cfg.X / (cfg.H : ℝ) :=
  inp.source_bound cfg hcfg

/-- **`sharedGcdOneLevelMobiusGram_not_automatic`.**  `LEAN_PROVED`.

With `K = 0` the claimed bound fails on the explicit valid configuration of
`exists_valid_config_with_positive_source`, so the socket is a genuine hypothesis:
`287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-MOBIUS-GRAM45` is `ANALYTIC OPEN; UNINHABITED`. -/
theorem sharedGcdOneLevelMobiusGram_not_automatic :
    ∃ K : ℝ, ¬ SharedGcdOneLevelMobiusGramInput K := by
  refine ⟨0, ?_⟩
  intro h
  obtain ⟨cfg, hvalid, hsrc, hX, hH⟩ := exists_valid_config_with_positive_source
  have hb := h.source_bound cfg hvalid
  rw [hsrc, hX, hH] at hb
  simp at hb
  linarith

end SharedGcdOneLevel
end Erdos287
