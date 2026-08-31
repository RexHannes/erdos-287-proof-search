import Mathlib
import RequestProject.CurrentProgramme.SharedG0PrimitiveURouter
import RequestProject.CurrentProgramme.SharedG0BPairAveraged

/-!
# The current repair socket — Erdős #287, SHARED-`g₀` REPAIR Δ, §9

This module defines the **shared-`g₀` Cauchy configuration** that the current controlling
repair

```
287-K0-SP2-DET1-SHAREDG0-CAUCHY-CONFIGURATION45
```

is stated over, and states — but does **not** inhabit — the corresponding analytic /
norm-ledger input `SharedG0CauchyConfigurationInput`.

The hostile NANC audit returned `REPAIR` for both analytic children

* `DET1-LARGESHAREDG0-CELLS45`,
* `DET1-PRIMITIVE-NEARFREQ45`,

for exactly two reasons, both of which are carried explicitly by the ledger below:

* **A.** the proof must use the **averaged** `b₁,b₂` gcd router of §5 rather than the
  pointwise bound `|U(C)| ≤ g₀^{1+o(1)}`;
* **B.** the exact Cauchy configuration deciding whether the final near-frequency
  amplitude gain is `density^{1/4}` or `density^{1/2}` must be pinned down.

Accordingly the ledger records

* the actual **averaged** `b`-pair `U` bound (as an exponent pair over the finite core of §5);
* the natural **unoscillated** shared-`g₀` scale;
* the `Q`-level **near-density** gain;
* the **number of Cauchy square roots** applied;
* the resulting **final amplitude exponent**.

Only the trivial conditional consumer `sharedG0CauchyConfiguration_compiler` uses the socket,
and `sharedG0CauchyConfiguration_not_automatic` exhibits explicit data refuting it, so the
socket is neither vacuous nor automatic.

Status: **ANALYTIC REPAIR OPEN / UNINHABITED.**
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace Erdos287
namespace SharedG0Cauchy

/-! ## §9.1  The Cauchy ledger -/

/-- The exact missing analytic / norm ledger of the shared-`g₀` Cauchy repair.

Every field is a *bookkeeping* quantity: the structure records which configuration the
analytic argument is claimed to run in, and is never itself asserted. -/
structure CauchyLedger where
  /-- The shared conductor `g₀`. -/
  g0 : ℕ
  /-- The `b`-interval length `B` over which the `b`-pair router of §5 is averaged. -/
  B : ℕ
  /-- The conductor level `Q`. -/
  Q : ℕ
  /-- The exponent `θ_U` in the **averaged** `b`-pair `U` bound
  `∑_{b₁,b₂} |U_{g₀,D}(C(b₁,b₂))| ≤ B² · g₀^{θ_U}` — this is the quantity the audit
  demands be taken from §5, *not* the pointwise `g₀^{1+o(1)}`. -/
  thetaU : ℚ
  /-- The natural **unoscillated** shared-`g₀` scale, i.e. the size of the shared-`g₀` cell
  contribution with no cancellation exploited. -/
  unoscillatedScale : ℚ
  /-- The `Q`-level **near-density** gain `δ`. -/
  nearDensityGain : ℚ
  /-- The number of Cauchy–Schwarz square roots applied on the way to the final bound. -/
  cauchyRoots : ℕ
  /-- The final amplitude exponent `α`, so that the claimed gain is `δ^α`. -/
  amplitudeExponent : ℚ

namespace CauchyLedger

variable (L : CauchyLedger)

/-- The amplitude exponent that `k` Cauchy square roots produce from a density gain, namely
`2^{-k}`.  With `k = 1` this is `δ^{1/2}`; with `k = 2` it is `δ^{1/4}`. -/
def rootExponent : ℚ := (1 : ℚ) / 2 ^ L.cauchyRoots

/-- The ledger is *root-consistent* when its declared final amplitude exponent is exactly the
one produced by its declared number of Cauchy square roots.  This is the formal shape of
audit item **B**. -/
def RootConsistent : Prop := L.amplitudeExponent = L.rootExponent

/-- Well-formedness of a ledger: positive parameters, an averaged `U` exponent that is a
genuine improvement over the pointwise exponent `1`, a density gain in `(0,1]`, at least one
Cauchy square root, and root consistency. -/
structure Valid : Prop where
  /-- The shared conductor is positive. -/
  g0_pos : 0 < L.g0
  /-- The `b`-interval is nonempty. -/
  B_pos : 0 < L.B
  /-- The conductor level is positive. -/
  Q_pos : 0 < L.Q
  /-- The averaged `b`-pair exponent is nonnegative. -/
  thetaU_nonneg : 0 ≤ L.thetaU
  /-- **Audit item A**: the averaged exponent strictly beats the pointwise exponent `1`. -/
  thetaU_beats_pointwise : L.thetaU < 1
  /-- The unoscillated scale is positive. -/
  unoscillatedScale_pos : 0 < L.unoscillatedScale
  /-- The near-density gain is a genuine density. -/
  nearDensityGain_mem : 0 < L.nearDensityGain ∧ L.nearDensityGain ≤ 1
  /-- At least one Cauchy square root is applied. -/
  cauchyRoots_pos : 0 < L.cauchyRoots
  /-- **Audit item B**: the declared amplitude exponent matches the root count. -/
  root_consistent : L.RootConsistent

end CauchyLedger

/-- One Cauchy square root gives the amplitude exponent `1/2`. -/
theorem rootExponent_one {L : CauchyLedger} (h : L.cauchyRoots = 1) :
    L.rootExponent = 1 / 2 := by
  simp [CauchyLedger.rootExponent, h]

/-- Two Cauchy square roots give the amplitude exponent `1/4`. -/
theorem rootExponent_two {L : CauchyLedger} (h : L.cauchyRoots = 2) :
    L.rootExponent = 1 / 4 := by
  simp [CauchyLedger.rootExponent, h]
  norm_num

/-- The two candidate amplitude exponents of audit item **B** are genuinely different, so the
Cauchy configuration really has to be decided. -/
theorem amplitude_dichotomy_nontrivial : (1 : ℚ) / 4 ≠ 1 / 2 := by norm_num

/-- A valid ledger exists, so the socket below is not vacuously satisfiable by an empty
configuration class. -/
theorem exists_valid_ledger : ∃ L : CauchyLedger, L.Valid := by
  refine ⟨⟨1, 1, 1, 1/2, 1, 1, 1, 1/2⟩, ?_⟩
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    ⟨by norm_num, by norm_num⟩, by norm_num, ?_⟩
  show (1/2 : ℚ) = _
  simp [CauchyLedger.rootExponent]

/-! ## §9.2  The analytic repair socket — stated, never inhabited -/

/-- **`SharedG0CauchyConfigurationInput` — ANALYTIC / UNINHABITED.**

The exact missing analytic / norm ledger of

```
287-K0-SP2-DET1-SHAREDG0-CAUCHY-CONFIGURATION45.
```

Uniformly over valid Cauchy ledgers, the shared-`g₀` cell functional is claimed to beat its
own unoscillated scale by the declared amplitude gain:

```
|cell(L)| ≤ K · unoscillatedScale(L) · nearDensityGain(L) ^ amplitudeExponent(L).
```

This is an analytic statement.  It is **not** proved anywhere in this repository and this
structure has **no inhabitant**.  Both `DET1-LARGESHAREDG0-CELLS45` and
`DET1-PRIMITIVE-NEARFREQ45` are `REPAIR_PENDING` on it. -/
structure SharedG0CauchyConfigurationInput (K : ℝ) (cell : CauchyLedger → ℝ) : Prop where
  /-- The implied constant is explicit and nonnegative. -/
  K_nonneg : 0 ≤ K
  /-- The averaged `b`-pair router of §5, not the pointwise bound, is the one in force. -/
  uses_averaged_router : ∀ L : CauchyLedger, L.Valid → L.thetaU < 1
  /-- The analytic target itself. -/
  cell_bound : ∀ L : CauchyLedger, L.Valid →
    |cell L| ≤ K * (L.unoscillatedScale : ℝ) *
      (L.nearDensityGain : ℝ) ^ (L.amplitudeExponent : ℝ)

/-- The conclusion the socket would deliver, for a single ledger. -/
def SharedG0CauchyConclusion (K : ℝ) (L : CauchyLedger) (value : ℝ) : Prop :=
  |value| ≤ K * (L.unoscillatedScale : ℝ) *
    (L.nearDensityGain : ℝ) ^ (L.amplitudeExponent : ℝ)

/-- **Conditional consumer.**  `CONDITIONAL / LEAN_PROVED`.  Nothing unconditional is
obtained: the antecedent is uninhabited. -/
theorem sharedG0CauchyConfiguration_compiler {K : ℝ} {cell : CauchyLedger → ℝ}
    (inp : SharedG0CauchyConfigurationInput K cell) (L : CauchyLedger) (hL : L.Valid) :
    SharedG0CauchyConclusion K L (cell L) :=
  inp.cell_bound L hL

/-- **`sharedG0CauchyConfiguration_not_automatic`.**  `LEAN_PROVED`.

Explicit data refuting the socket: with `K = 0` and a cell functional of constant value `1`
the target bound fails on the valid ledger of `exists_valid_ledger`.  Hence the socket is a
real hypothesis, and `287-K0-SP2-DET1-SHAREDG0-CAUCHY-CONFIGURATION45` is
`ANALYTIC REPAIR OPEN; UNINHABITED`. -/
theorem sharedG0CauchyConfiguration_not_automatic :
    ∃ (K : ℝ) (cell : CauchyLedger → ℝ), ¬ SharedG0CauchyConfigurationInput K cell := by
  refine ⟨0, fun _ => 1, ?_⟩
  intro h
  obtain ⟨L, hL⟩ := exists_valid_ledger
  have hb := h.cell_bound L hL
  simp at hb
  linarith

end SharedG0Cauchy
end Erdos287
