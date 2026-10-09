import Mathlib.Tactic

/-!
# Contact-core route — exact transfer along a physical forcing path (PATH)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A physical forcing path

`p₀ — p₁ — ⋯ — p_j`

carries edge equations `pᵢ cᵢ - p_{i+1} dᵢ = σᵢ` with `σᵢ ∈ {±1}` (the sign is irrelevant for the
transfer identity, which is proved for arbitrary `σᵢ`).  With

`C₀ = D₀ = 1`, `R₀ = 0`, `C_{i+1} = cᵢ Cᵢ`, `D_{i+1} = dᵢ Dᵢ`, `R_{i+1} = cᵢ Rᵢ + σᵢ Dᵢ`

the exact transfer identity is

`D_j p_j = C_j p₀ - R_j`   (`path_transfer`),

with the unrolled remainder

`R_j = ∑_{i<j} σᵢ Dᵢ ∏_{r ∈ [i+1, j)} c_r`   (`Rseq_eq_sum`)

and its normalized form `R_j / C_j = ∑_{i<j} σᵢ Dᵢ / (Cᵢ cᵢ)` (`Rseq_div_Cseq`).

This **permanently replaces** the incorrect direct-terminal splice: `depthTwo_splice_counterfixture`
records the physical fixture `53 — 317 — 79` for which the two unit edges do *not* compose into a
unit relation between the endpoints.
-/

namespace Erdos287
namespace ResearchBankV5
namespace ContactCore

variable {R : Type*} [CommRing R]

/-- The numerator accumulator `C` of a forcing path. -/
def Cseq (c : ℕ → R) : ℕ → R
  | 0 => 1
  | i + 1 => c i * Cseq c i

/-- The denominator accumulator `D` of a forcing path. -/
def Dseq (d : ℕ → R) : ℕ → R
  | 0 => 1
  | i + 1 => d i * Dseq d i

/-- The remainder accumulator `R` of a forcing path. -/
def Rseq (c d σ : ℕ → R) : ℕ → R
  | 0 => 0
  | i + 1 => c i * Rseq c d σ i + σ i * Dseq d i

@[simp] theorem Cseq_zero (c : ℕ → R) : Cseq c 0 = 1 := rfl
@[simp] theorem Dseq_zero (d : ℕ → R) : Dseq d 0 = 1 := rfl
@[simp] theorem Rseq_zero (c d σ : ℕ → R) : Rseq c d σ 0 = 0 := rfl

theorem Cseq_succ (c : ℕ → R) (i : ℕ) : Cseq c (i + 1) = c i * Cseq c i := rfl
theorem Dseq_succ (d : ℕ → R) (i : ℕ) : Dseq d (i + 1) = d i * Dseq d i := rfl
theorem Rseq_succ (c d σ : ℕ → R) (i : ℕ) :
    Rseq c d σ (i + 1) = c i * Rseq c d σ i + σ i * Dseq d i := rfl

/-- **(PATH).**  Exact transfer along a physical forcing path: if every edge satisfies
`pᵢ cᵢ - p_{i+1} dᵢ = σᵢ`, then `D_j p_j = C_j p₀ - R_j`. -/
theorem path_transfer (c d σ p : ℕ → R) :
    ∀ j : ℕ, (∀ i, i < j → p i * c i - p (i + 1) * d i = σ i) →
      Dseq d j * p j = Cseq c j * p 0 - Rseq c d σ j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ n ih =>
      intro h
      have hn := ih fun i hi => h i (Nat.lt_succ_of_lt hi)
      have he := h n (Nat.lt_succ_self n)
      rw [Dseq_succ, Cseq_succ, Rseq_succ]
      linear_combination (-(Dseq d n)) * he + (c n) * hn

/-- `C_j` is the product of the numerators along the path. -/
theorem Cseq_eq_prod (c : ℕ → R) (j : ℕ) : Cseq c j = ∏ r ∈ Finset.range j, c r := by
  induction j with
  | zero => simp
  | succ n ih => rw [Cseq_succ, ih, Finset.prod_range_succ]; ring

/-- `D_j` is the product of the denominators along the path. -/
theorem Dseq_eq_prod (d : ℕ → R) (j : ℕ) : Dseq d j = ∏ r ∈ Finset.range j, d r := by
  induction j with
  | zero => simp
  | succ n ih => rw [Dseq_succ, ih, Finset.prod_range_succ]; ring

/-- **Unrolled remainder.**  `R_j = ∑_{i<j} σᵢ Dᵢ ∏_{r=i+1}^{j-1} c_r`. -/
theorem Rseq_eq_sum (c d σ : ℕ → R) (j : ℕ) :
    Rseq c d σ j = ∑ i ∈ Finset.range j, σ i * Dseq d i * ∏ r ∈ Finset.Ico (i + 1) j, c r := by
  induction j with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hterm : ∀ i ∈ Finset.range n,
          σ i * Dseq d i * ∏ r ∈ Finset.Ico (i + 1) (n + 1), c r
            = (σ i * Dseq d i * ∏ r ∈ Finset.Ico (i + 1) n, c r) * c n := by
        intro i hi
        have hle : i + 1 ≤ n := Finset.mem_range.1 hi
        rw [Finset.prod_Ico_succ_top hle]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← ih, Rseq_succ]
      simp [mul_comm]

/-- **Normalized remainder.**  Over a field, with all `cᵢ ≠ 0`,
`R_j / C_j = ∑_{i<j} σᵢ Dᵢ / (Cᵢ cᵢ)`. -/
theorem Rseq_div_Cseq {K : Type*} [Field K] (c d σ : ℕ → K) (hc : ∀ i, c i ≠ 0) (j : ℕ) :
    Rseq c d σ j / Cseq c j = ∑ i ∈ Finset.range j, σ i * Dseq d i / (Cseq c i * c i) := by
  rw [Rseq_eq_sum, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hle : i + 1 ≤ j := Finset.mem_range.1 hi
  have hsplit : Cseq c j = (Cseq c i * c i) * ∏ r ∈ Finset.Ico (i + 1) j, c r := by
    rw [Cseq_eq_prod, ← Finset.prod_range_mul_prod_Ico c hle, Cseq_eq_prod,
      Finset.prod_range_succ]
  have hne : (∏ r ∈ Finset.Ico (i + 1) j, c r) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun r _ => hc r
  rw [hsplit, mul_comm (σ i * Dseq d i)]
  rw [show (∏ r ∈ Finset.Ico (i + 1) j, c r) * (σ i * Dseq d i)
      = (σ i * Dseq d i) * (∏ r ∈ Finset.Ico (i + 1) j, c r) by ring]
  exact mul_div_mul_right _ _ hne

/-! ## The `53 — 317 — 79` depth-two counterfixture -/

/-- Numerators of the fixture path `53 — 317 — 79`. -/
def fixtureC : ℕ → ℤ := fun i => if i = 0 then 6 else 1

/-- Denominators of the fixture path `53 — 317 — 79`. -/
def fixtureD : ℕ → ℤ := fun i => if i = 0 then 1 else 4

/-- Signs of the fixture path `53 — 317 — 79` (both edges are `+1`). -/
def fixtureSigma : ℕ → ℤ := fun _ => 1

/-- Vertices of the fixture path. -/
def fixtureP : ℕ → ℤ := fun i => if i = 0 then 53 else if i = 1 then 317 else 79

/-- Both edges of the fixture are genuine unit contacts. -/
theorem fixture_edges :
    (6 * 53 - 1 * 317 : ℤ) = 1 ∧ (1 * 317 - 4 * 79 : ℤ) = 1 := by norm_num

/-- **Depth-two splice counterfixture.**  The two unit edges of `53 — 317 — 79` do *not* splice
into a unit relation between the endpoints: `6·53 - 4·79 = 2`. -/
theorem depthTwo_splice_counterfixture : (6 * 53 - 4 * 79 : ℤ) = 2 := by norm_num

/-- The PATH accumulators of the fixture: `C₂ = 6`, `D₂ = 4`, `R₂ = 2`. -/
theorem fixture_accumulators :
    Cseq fixtureC 2 = 6 ∧ Dseq fixtureD 2 = 4 ∧ Rseq fixtureC fixtureD fixtureSigma 2 = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [Cseq, Dseq, Rseq, fixtureC, fixtureD, fixtureSigma]

/-- PATH predicts the fixture exactly: `D₂ p₂ = C₂ p₀ - R₂`, i.e. `4·79 = 6·53 - 2`. -/
theorem fixture_path_transfer :
    Dseq fixtureD 2 * fixtureP 2 = Cseq fixtureC 2 * fixtureP 0
      - Rseq fixtureC fixtureD fixtureSigma 2 := by
  norm_num [Cseq, Dseq, Rseq, fixtureC, fixtureD, fixtureSigma, fixtureP]

/-- **Retirement of the direct terminal splice.**  A composition of two unit edges need not be a
unit edge; therefore "positive-density root pins ⟹ positive-density direct root-to-terminal
contacts" is *false as a global statement*, and direct incidence survives only at depth one. -/
theorem direct_splice_not_unit :
    ((6 : ℤ) * 53 - 1 * 317 = 1) ∧ ((1 : ℤ) * 317 - 4 * 79 = 1) ∧
      ((6 : ℤ) * 53 - 4 * 79 ≠ 1 ∧ (6 : ℤ) * 53 - 4 * 79 ≠ -1) := by
  norm_num

/-- The sharp form of the retirement: for the fixture path, the *spliced* pair `(C₂, D₂)` produces
the value `2`, not a unit. -/
theorem depthOne_only :
    Cseq fixtureC 2 * fixtureP 0 - Dseq fixtureD 2 * fixtureP 2 = 2 := by
  norm_num [Cseq, Dseq, fixtureC, fixtureD, fixtureP]

end ContactCore
end ResearchBankV5
end Erdos287
