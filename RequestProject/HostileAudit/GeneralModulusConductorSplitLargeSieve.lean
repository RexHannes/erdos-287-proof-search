import Mathlib
import RequestProject.HostileAudit.TotientComplementaryFactor

/-!
# Hostile-audit safe bank §5 — the general-modulus conductor-split compiler

`AFFINE287-SP2-SMALLR-GENERAL-MODULUS-CONDUCTOR-LS45`
`CONDITIONAL COMPILER / HOSTILE-AUDITED EXTERNAL ANALYSIS`

**Nothing analytic is proved here.**  The primitive multiplicative large sieve is *not*
proved; it enters as the uninhabited interface `PrimitiveWeightedLargeSieveInput`, stated in
its literal weighted form: for a fixed complementary factor `j` and a fixed divisor `d` of
the Möbius expansion,

```
L(j,d) ≤ (R/j + N·j/(R·d)) · E_d.
```

The divisor-sum / polylogarithmic aggregation of the energies `E_d` is likewise **not**
proved; it is the uninhabited interface `DivisorSumPolylogInput`.

What *is* proved (`general_modulus_conductorSplit_compiler`) is the finite inequality
compiler which, from those two interfaces plus the §3 induced-character algebra and the §4
complementary-factor bound `j < 2R/D`, produces the target schematic estimate

```
L_gen(R,D;c) ≤ (2·polylog) · (R + N/D) · ‖c‖₂².
```

That is exactly the `N/D` conductor saving, and it is a theorem *about the interfaces*, not
about Dirichlet characters.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace HostileAudit

/-! ## §5.1  The literal cell data -/

/-- The general-modulus cell weight: `L_gen = ∑_{(j,d)} L(j,d)`, the literal finite sum over
the pairs (complementary factor, Möbius divisor). -/
def Lgen (cells : Finset (ℕ × ℕ)) (Lval : ℕ × ℕ → ℝ) : ℝ := ∑ p ∈ cells, Lval p

/-- The schematic target of the general-modulus conductor-split large sieve. -/
noncomputable def LgenTarget (Rr N D polylog nrm2 : ℝ) : ℝ :=
  polylog * (Rr + N / D) * nrm2

/-! ## §5.2  The uninhabited primitive input -/

/-- **`PrimitiveWeightedLargeSieveInput`** — `EXTERNAL / ANALYTIC / UNINHABITED`.

The primitive multiplicative large sieve in its literal weighted, *fixed-`j`* form.  For each
cell `(j, d)` the primitive bound

```
L(j,d) ≤ (R/j + N·j/(R·d)) · E_d
```

is supplied by the source.  This structure is not inhabited anywhere in the repository, and
no proof of the primitive large sieve is attempted. -/
structure PrimitiveWeightedLargeSieveInput (N : ℕ) (Rr : ℝ) (cells : Finset (ℕ × ℕ))
    (Lval : ℕ × ℕ → ℝ) (E : ℕ → ℝ) : Prop where
  /-- The scales are nontrivial. -/
  scale : 0 < Rr ∧ 0 < N
  /-- The cell indices are positive: `j ≥ 1` and `d ≥ 1`. -/
  index_pos : ∀ p ∈ cells, 0 < p.1 ∧ 0 < p.2
  /-- The energies are nonnegative. -/
  energy_nonneg : ∀ p ∈ cells, 0 ≤ E p.2
  /-- The literal fixed-`j` primitive bound. -/
  fixed_j_bound :
    ∀ p ∈ cells, Lval p ≤ (Rr / p.1 + (N : ℝ) * p.1 / (Rr * p.2)) * E p.2

/-- **`DivisorSumPolylogInput`** — `EXTERNAL / UNINHABITED`.

The divisor-sum / polylogarithmic aggregation of the cell energies:

```
∑_{(j,d)} E_d ≤ polylog · ‖c‖₂².
```

Mathlib has no such divisor-sum estimate for the physical energies, so it stays an explicit
interface rather than an invented theorem. -/
structure DivisorSumPolylogInput (cells : Finset (ℕ × ℕ)) (E : ℕ → ℝ)
    (polylog nrm2 : ℝ) : Prop where
  /-- The polylogarithmic factor is nonnegative. -/
  polylog_nonneg : 0 ≤ polylog
  /-- The coefficient energy is nonnegative. -/
  nrm2_nonneg : 0 ≤ nrm2
  /-- The aggregated divisor-sum bound. -/
  divisor_energy : ∑ p ∈ cells, E p.2 ≤ polylog * nrm2

/-- **`ConductorWindowData`** — finite, *inhabitable* data (this is §4, not analysis).

The conductor window: each cell carries a primitive conductor `f > D` and the modulus
`r = f·j` lies in the dyadic window `[R, 2R)`. -/
structure ConductorWindowData (D Rr : ℝ) (cells : Finset (ℕ × ℕ)) (fcond : ℕ × ℕ → ℝ) :
    Prop where
  /-- The conductor cutoff is positive. -/
  D_pos : 0 < D
  /-- The conductor exceeds the cutoff — this is the high-conductor sector. -/
  cond_large : ∀ p ∈ cells, D < fcond p
  /-- The modulus lies in the dyadic window. -/
  dyadic : ∀ p ∈ cells, Rr ≤ fcond p * p.1 ∧ fcond p * p.1 < 2 * Rr

/-- **`window_gives_complementary_bound`.**  `LEAN_PROVED` (this is §4 applied cellwise). -/
theorem window_gives_complementary_bound {D Rr : ℝ} {cells : Finset (ℕ × ℕ)}
    {fcond : ℕ × ℕ → ℝ} (h : ConductorWindowData D Rr cells fcond) :
    ∀ p ∈ cells, (p.1 : ℝ) < 2 * Rr / D := by
  intro p hp
  exact complementary_factor_bound h.D_pos (h.cond_large p hp) (by positivity)
    (h.dyadic p hp).2

/-! ## §5.3  The cellwise inequality -/

/-- **`general_modulus_cell_bound`.**  `LEAN_PROVED`.

The exact per-cell inequality behind the `N/D` saving:

```
(R/j + N·j/(R·d)) · E_d ≤ 2·(R + N/D)·E_d
```

whenever `j ≥ 1`, `d ≥ 1`, `R > 0`, `D > 0`, `E_d ≥ 0` and `j ≤ 2R/D`. -/
theorem general_modulus_cell_bound {Rr D Nr jr dr Ed : ℝ}
    (hR : 0 < Rr) (hD : 0 < D) (hN : 0 ≤ Nr) (hj : 1 ≤ jr) (hd : 1 ≤ dr)
    (hwin : jr ≤ 2 * Rr / D) (hE : 0 ≤ Ed) :
    (Rr / jr + Nr * jr / (Rr * dr)) * Ed ≤ 2 * (Rr + Nr / D) * Ed := by
  have hj0 : 0 < jr := lt_of_lt_of_le zero_lt_one hj
  have hd0 : 0 < dr := lt_of_lt_of_le zero_lt_one hd
  -- first term
  have h1 : Rr / jr ≤ Rr := div_le_self hR.le hj
  -- second term
  have hRd : Rr ≤ Rr * dr := le_mul_of_one_le_right hR.le hd
  have h2 : Nr * jr / (Rr * dr) ≤ Nr * jr / Rr := by gcongr
  have h3 : Nr * jr ≤ Nr * (2 * Rr / D) := mul_le_mul_of_nonneg_left hwin hN
  have h4 : Nr * jr / Rr ≤ Nr * (2 * Rr / D) / Rr := by gcongr
  have h5 : Nr * (2 * Rr / D) / Rr = 2 * (Nr / D) := by
    field_simp
  have h6 : Nr * jr / (Rr * dr) ≤ 2 * (Nr / D) := by
    calc Nr * jr / (Rr * dr) ≤ Nr * jr / Rr := h2
      _ ≤ Nr * (2 * Rr / D) / Rr := h4
      _ = 2 * (Nr / D) := h5
  have hND : 0 ≤ Nr / D := div_nonneg hN hD.le
  have hsum : Rr / jr + Nr * jr / (Rr * dr) ≤ 2 * (Rr + Nr / D) := by linarith
  exact mul_le_mul_of_nonneg_right hsum hE

/-! ## §5.4  The conditional compiler -/

/-- **`general_modulus_conductorSplit_compiler`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

```
primitive weighted large sieve (UNINHABITED)
  + conductor window data (§4)
  + divisor-sum polylog aggregation (UNINHABITED)
      ⇒ L_gen(R,D;c) ≤ (2·polylog)·(R + N/D)·‖c‖₂².
```

The proof is pure finite inequality algebra; every analytic ingredient is an antecedent. -/
theorem general_modulus_conductorSplit_compiler
    {N : ℕ} {Rr D polylog nrm2 : ℝ} {cells : Finset (ℕ × ℕ)}
    {Lval : ℕ × ℕ → ℝ} {E : ℕ → ℝ} {fcond : ℕ × ℕ → ℝ}
    (hprim : PrimitiveWeightedLargeSieveInput N Rr cells Lval E)
    (hwin : ConductorWindowData D Rr cells fcond)
    (hdiv : DivisorSumPolylogInput cells E polylog nrm2) :
    Lgen cells Lval ≤ 2 * LgenTarget Rr N D polylog nrm2 := by
  have hR : 0 < Rr := hprim.scale.1
  have hD : 0 < D := hwin.D_pos
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hND : 0 ≤ Rr + (N : ℝ) / D := by positivity
  have hcell : ∀ p ∈ cells, Lval p ≤ 2 * (Rr + (N : ℝ) / D) * E p.2 := by
    intro p hp
    refine le_trans (hprim.fixed_j_bound p hp) ?_
    have hj : (1 : ℝ) ≤ (p.1 : ℝ) := by
      exact_mod_cast (hprim.index_pos p hp).1
    have hd : (1 : ℝ) ≤ (p.2 : ℝ) := by
      exact_mod_cast (hprim.index_pos p hp).2
    exact general_modulus_cell_bound hR hD hN hj hd
      (le_of_lt (window_gives_complementary_bound hwin p hp)) (hprim.energy_nonneg p hp)
  calc Lgen cells Lval = ∑ p ∈ cells, Lval p := rfl
    _ ≤ ∑ p ∈ cells, 2 * (Rr + (N : ℝ) / D) * E p.2 := Finset.sum_le_sum hcell
    _ = 2 * (Rr + (N : ℝ) / D) * ∑ p ∈ cells, E p.2 := by rw [Finset.mul_sum]
    _ ≤ 2 * (Rr + (N : ℝ) / D) * (polylog * nrm2) := by
        exact mul_le_mul_of_nonneg_left hdiv.divisor_energy (by linarith)
    _ = 2 * LgenTarget Rr N D polylog nrm2 := by
        unfold LgenTarget; ring

/-! ## §5.5  Firewalls -/

/-- **`primitiveLargeSieve_not_automatic`.**  `LEAN_PROVED`.

The primitive analytic input is not inhabited here: it is refuted by explicit data. -/
theorem primitiveLargeSieve_not_automatic :
    ∃ (N : ℕ) (Rr : ℝ) (cells : Finset (ℕ × ℕ)) (Lval : ℕ × ℕ → ℝ) (E : ℕ → ℝ),
      ¬ PrimitiveWeightedLargeSieveInput N Rr cells Lval E := by
  refine ⟨0, 0, ∅, fun _ => 0, fun _ => 0, ?_⟩
  intro h
  have := h.scale.1
  norm_num at this

/-- **`divisorSumPolylog_not_automatic`.**  `LEAN_PROVED`. -/
theorem divisorSumPolylog_not_automatic :
    ∃ (cells : Finset (ℕ × ℕ)) (E : ℕ → ℝ) (polylog nrm2 : ℝ),
      ¬ DivisorSumPolylogInput cells E polylog nrm2 := by
  refine ⟨{(1, 1)}, fun _ => 1, 0, 0, ?_⟩
  intro h
  have h1 := h.divisor_energy
  simp only [Finset.sum_singleton, mul_zero] at h1
  norm_num at h1

/-- **`general_modulus_compiler_is_conditional`.**  `LEAN_PROVED`.

The compiler proves nothing unconditionally: its analytic antecedents are refutable, and the
conclusion is only ever derived from them. -/
theorem general_modulus_compiler_is_conditional :
    (∃ (N : ℕ) (Rr : ℝ) (cells : Finset (ℕ × ℕ)) (Lval : ℕ × ℕ → ℝ) (E : ℕ → ℝ),
        ¬ PrimitiveWeightedLargeSieveInput N Rr cells Lval E) ∧
      (∃ (cells : Finset (ℕ × ℕ)) (E : ℕ → ℝ) (polylog nrm2 : ℝ),
        ¬ DivisorSumPolylogInput cells E polylog nrm2) :=
  ⟨primitiveLargeSieve_not_automatic, divisorSumPolylog_not_automatic⟩

end HostileAudit
end Erdos287
