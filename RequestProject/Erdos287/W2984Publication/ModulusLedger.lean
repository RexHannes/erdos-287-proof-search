import Mathlib

/-!
# W2.984 — the complete modulus ledger for the affine `S₁`, `S₂`, `S₃`

**ERDŐS #287 REMAINS OPEN.  Exact rational arithmetic and finite bookkeeping.**

Every divisor coordinate entering a remainder modulus is listed **exactly once** in the
finite type `ModulusSource` (5 constructors, `ledger_card`).  Exponents are in units of
`log X` (`X` = the size of the forms).  With the V92 parameters (`D₀ = X^{1/2-4δ}`, Maynard support
`X^δ`, small-prime square `H` supported on `[0, 2δ²]`) and a fixed base `a_j W ≤ X^{ε_W}`:

| source | exponent |
|---|---:|
| linear-sieve divisor `d` (`S₁`), resp. `dp` (`S₂`) | `1/2 - 4δ` |
| spectator lcms `∏ᵢ [dᵢ, dᵢ']` | `2δ` |
| small-prime-square divisor `e` | `2δ²` |
| small-prime-square divisor `e'` | `2δ²` |
| fixed base `a_j W` | `ε_W` |

* `totalS1_eq` — the `S₁/S₂` total is `1/2 - 2δ + 4δ² + ε_W`;
* `totalS1_lt_half` — `< 1/2` for `0 < δ ≤ 1/8`, `0 ≤ ε_W ≤ δ/2` (in fact `≤ 1/2 - δ`:
  `totalS1_le`), which is the level required by the modified Bombieri–Vinogradov theorem
  (Merikoski Prop. 8 / BFM Thm 4.2, moduli `≤ X^{1/2-δ}`);
* `v92_core_lt_half` — the V92 core inequality `1/2 - 2δ + 4δ² < 1/2` for `0 < δ < 1/2`;
* `totalS3_eq`, `totalS3_le` — the switched `S₃` ledger (Selberg weights `e, e' ≤ X^{1/4-2δ}`,
  spectators `2δ`, base `ε_W`; no small-prime square is needed there) is `1/2 - 2δ + ε_W`;
* `S2_level` — in `S₂` the sieve level `X^{1/2-4δ}/p` times `p` is exactly `X^{1/2-4δ}`;
* `reindex_fixed_base` — **fixed (possibly non-squarefree) base**: for non-negative errors,
  `∑_{q ∈ S} E(q·c) ≤ ∑_{q'' ∈ S'} E(q'')` whenever `c > 0` and `q·c ∈ S'`; this is how a
  bounded factor `a_j` is absorbed into Bombieri–Vinogradov over multiples of the squarefree `W`.
-/

open scoped BigOperators

namespace Erdos287.W2984Publication

/-- The five modulus contributors of the affine `S₁`/`S₂` remainders. -/
inductive ModulusSource
  | linearSieve
  | spectatorLcm
  | smallSquare1
  | smallSquare2
  | fixedBase
  deriving DecidableEq, Fintype, Repr

open ModulusSource

/-- Exactly five contributors: none duplicated, none missing. -/
theorem ledger_card : Fintype.card ModulusSource = 5 := by decide

/-- Exponent of each contributor (units of `log X`). -/
def exponentS1 (δ εW : ℚ) : ModulusSource → ℚ
  | linearSieve => 1/2 - 4 * δ
  | spectatorLcm => 2 * δ
  | smallSquare1 => 2 * δ ^ 2
  | smallSquare2 => 2 * δ ^ 2
  | fixedBase => εW

/-- Total `S₁/S₂` modulus exponent. -/
def totalS1 (δ εW : ℚ) : ℚ := ∑ s : ModulusSource, exponentS1 δ εW s

theorem totalS1_eq (δ εW : ℚ) : totalS1 δ εW = 1/2 - 2 * δ + 4 * δ ^ 2 + εW := by
  have hu : (Finset.univ : Finset ModulusSource) =
      {linearSieve, spectatorLcm, smallSquare1, smallSquare2, fixedBase} := by decide
  rw [totalS1, hu]
  simp [exponentS1]
  ring

/-- The V92 core inequality. -/
theorem v92_core_lt_half {δ : ℚ} (h0 : 0 < δ) (h1 : δ < 1/2) : 1/2 - 2 * δ + 4 * δ ^ 2 < 1/2 := by
  nlinarith

theorem totalS1_le {δ εW : ℚ} (h0 : 0 < δ) (h1 : δ ≤ 1/8) (hε : εW ≤ δ / 2) :
    totalS1 δ εW ≤ 1/2 - δ := by
  rw [totalS1_eq]; nlinarith

theorem totalS1_lt_half {δ εW : ℚ} (h0 : 0 < δ) (h1 : δ ≤ 1/8) (hε : εW ≤ δ / 2) :
    totalS1 δ εW < 1/2 := by
  have := totalS1_le h0 h1 hε; linarith

/-- Forgetting the two small-prime-square populations changes the total (regression aid). -/
theorem totalS1_ne_without_square {δ εW : ℚ} (h0 : 0 < δ) :
    totalS1 δ εW ≠ 1/2 - 2 * δ + εW := by
  rw [totalS1_eq]; intro h; nlinarith

/-- Switched `S₃` contributors. -/
inductive ModulusSourceS3
  | selbergLcm
  | spectatorLcm
  | fixedBase
  deriving DecidableEq, Fintype, Repr

def exponentS3 (δ εW : ℚ) : ModulusSourceS3 → ℚ
  | .selbergLcm => 1/2 - 4 * δ
  | .spectatorLcm => 2 * δ
  | .fixedBase => εW

def totalS3 (δ εW : ℚ) : ℚ := ∑ s : ModulusSourceS3, exponentS3 δ εW s

theorem totalS3_eq (δ εW : ℚ) : totalS3 δ εW = 1/2 - 2 * δ + εW := by
  have hu : (Finset.univ : Finset ModulusSourceS3) =
      {.selbergLcm, .spectatorLcm, .fixedBase} := by decide
  rw [totalS3, hu]
  simp [exponentS3]
  ring

theorem totalS3_le {δ εW : ℚ} (hε : εW ≤ δ) : totalS3 δ εW ≤ 1/2 - δ := by
  rw [totalS3_eq]; linarith

/-- `S₂`: level `X^{1/2-4δ}/p` times `p`. -/
theorem S2_level (δ θ : ℚ) : (1/2 - 4 * δ - θ) + θ = 1/2 - 4 * δ := by ring

/-- **Fixed-base reindexing.** -/
theorem reindex_fixed_base {E : ℕ → ℝ} (hE : ∀ q, 0 ≤ E q) {c : ℕ} (hc : 0 < c)
    {S S' : Finset ℕ} (hsub : ∀ q ∈ S, q * c ∈ S') :
    ∑ q ∈ S, E (q * c) ≤ ∑ q ∈ S', E q := by
  have hinj : Set.InjOn (fun q => q * c) S := fun a _ b _ h =>
    Nat.eq_of_mul_eq_mul_right hc h
  rw [← Finset.sum_image (f := E) hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hx
    exact hsub q hq
  · intro i _ _; exact hE i

end Erdos287.W2984Publication
