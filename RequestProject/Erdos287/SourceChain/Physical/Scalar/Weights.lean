import RequestProject.Erdos287.SourceChain.Physical.Scalar.RosserCore

/-!
# Erdős #287 — the actual parity-sensitive scalar sieve coefficient `ℓ_X`

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Literal definitions of `sources/physical_spec.md` §§13–15, with the precise conventions taken
from the original sources:

* Pascadi, arXiv:2505.00653v2, **Definition 5.1** (`𝒟^±(D)`, `𝐃_r^±(D)`) and the standard weights
  `λ^±_d = μ(d) 1_{d ∈ 𝒟^±(D)}`;
* Lichtman, arXiv:2109.02851v2, **§5** (the Proposition at the start of §5, the box grid
  `D^{ε²(1+τ)^j}`, the parity-dependent `𝐃_r^+`, the multiplicity factor `γ`, and the weights
  `λ^{(r)}_{(D_1,…,D_r)} = λ_{(D_1,…,D_r)} * λ^{(r)}` of `(lamD1Dr)`, `(lambdapm)`).

Levels (§13): `ε₀ = 1/T`, `τ = ε₀⁹`, `D_tot = X^{59/100}`, `D_int = D_tot^{1/(1+ε₀+τ)}`,
`u = D_int^{ε₀²}`, `D_low = D_int^{ε₀}`.  (Lichtman's `D` is our `D_int`; his `D^ε` is `D_low`;
his `u = D^{ε²}` is `u0`.)

Low primes: `p < u` (Lichtman: `b ∣ P(u)`, `P(u) = ∏_{p<u} p`).
High boxes: `I_j = (D_j, D_j^{1+τ}]` with `D_j = u^{(1+τ)^j}`, for the indices `j < H` with
`D_j ≤ √D_int` (Lichtman: `D_r ≤ ⋯ ≤ D_1 ≤ √D`).

A squarefree number is encoded by its set of prime factors; the decreasing enumeration
`p_1 > p_2 > ⋯` gives `p` the position `1 + #{q ∈ S : p < q}` (`Sieve.above`).
-/

open scoped BigOperators
open Finset

namespace Erdos287.Physical.Sieve

/-- Pascadi Def. 5.1, `𝒟^+(D)` on squarefree numbers (encoded by their prime sets):
`p_1 ⋯ p_{j-1} p_j^3 ≤ D` for every odd position `j`. -/
def DplusSet (D : ℝ) (S : Finset ℕ) : Prop :=
  ∀ p ∈ S, Even (above S p).card → (∏ q ∈ above S p, (q : ℝ)) * (p : ℝ) ^ 3 ≤ D

/-- Pascadi Def. 5.1, `𝒟^-(D)`: `p_1 ⋯ p_{j-1} p_j^3 ≤ D` for every even position `j`, and
`p_1^2 ≤ D` for the largest prime `p_1`. -/
def DminusSet (D : ℝ) (S : Finset ℕ) : Prop :=
  (∀ p ∈ S, Odd (above S p).card → (∏ q ∈ above S p, (q : ℝ)) * (p : ℝ) ^ 3 ≤ D) ∧
    (∀ p ∈ S, above S p = ∅ → (p : ℝ) ^ 2 ≤ D)

/-- The scalar parameters: the scale `X` and the reciprocal integer `T` (`ε₀ = 1/T`). -/
structure ScalarParams where
  X : ℝ
  T : ℕ

namespace ScalarParams

variable (S : ScalarParams)

/-- `ε₀ = 1/T`. -/
noncomputable def eps0 : ℝ := 1 / (S.T : ℝ)
/-- `τ = ε₀⁹`. -/
noncomputable def tau : ℝ := S.eps0 ^ 9
/-- `D_tot = X^{59/100}`. -/
noncomputable def Dtot : ℝ := S.X ^ ((59 : ℝ) / 100)
/-- `D_int = D_tot^{1/(1+ε₀+τ)}`. -/
noncomputable def Dint : ℝ := S.Dtot ^ (1 / (1 + S.eps0 + S.tau))
/-- `u = D_int^{ε₀²}` (low/high prime cutoff, bottom of the box grid). -/
noncomputable def u0 : ℝ := S.Dint ^ (S.eps0 ^ 2)
/-- `D_low = D_int^{ε₀}` (level of the low-prime weights). -/
noncomputable def Dlow : ℝ := S.Dint ^ S.eps0

/-! ### Low-prime weights -/

/-- A low prime: `p < u`. -/
def IsLow (p : ℕ) : Prop := p.Prime ∧ (p : ℝ) < S.u0

open Classical in
/-- **`λ⁺_low`**: `μ(b) 1_{b ∣ P(u)} 1_{b ∈ 𝒟^+(D_low)}`. -/
noncomputable def lamLowPlus (b : ℕ) : ℝ :=
  if Squarefree b ∧ (∀ p ∈ b.primeFactors, (p : ℝ) < S.u0) ∧ DplusSet S.Dlow b.primeFactors
  then (ArithmeticFunction.moebius b : ℝ) else 0

open Classical in
/-- **`λ⁻_low`**: `μ(b) 1_{b ∣ P(u)} 1_{b ∈ 𝒟^-(D_low)}`. -/
noncomputable def lamLowMinus (b : ℕ) : ℝ :=
  if Squarefree b ∧ (∀ p ∈ b.primeFactors, (p : ℝ) < S.u0) ∧ DminusSet S.Dlow b.primeFactors
  then (ArithmeticFunction.moebius b : ℝ) else 0

/-- **`κ_J`**: `λ⁺_low` for even high parity `J`, `λ⁻_low` for odd `J`. -/
noncomputable def kappa (J : ℕ) : ℕ → ℝ := if Even J then S.lamLowPlus else S.lamLowMinus

/-! ### High-prime box grid -/

/-- Box endpoints `D_j = u^{(1+τ)^j}` (Lichtman: `D^{ε²(1+τ)^j}`). -/
noncomputable def boxEnd (j : ℕ) : ℝ := S.u0 ^ ((1 + S.tau) ^ j)

/-- Top of box `j`: `D_j^{1+τ}`. -/
noncomputable def boxTop (j : ℕ) : ℝ := S.boxEnd j ^ (1 + S.tau)

open Classical in
/-- Number of boxes: the least `j` with `D_j > √D_int` (the grid is `{j : D_j ≤ √D_int}`). -/
noncomputable def H : ℕ :=
  if h : ∃ j, Real.sqrt S.Dint < S.boxEnd j then Nat.find h else 0

/-- `p` lies in box `j`: `D_j < p ≤ D_j^{1+τ}`. -/
def InBox (j : ℕ) (p : ℕ) : Prop := S.boxEnd j < p ∧ (p : ℝ) ≤ S.boxTop j

/-- A high prime: a prime owned by some box of the grid. -/
def IsHigh (p : ℕ) : Prop := p.Prime ∧ ∃ j < S.H, S.InBox j p

open Classical in
/-- The (unique, see `boxOf_spec`) box owning a high prime. -/
noncomputable def boxOf (p : ℕ) : ℕ := if h : ∃ j, j < S.H ∧ S.InBox j p then Nat.find h else 0

/-- Lichtman's threshold: `D_int` for even `r`, `D_int^{1/(1+τ)}` for odd `r`. -/
noncomputable def threshold (J : ℕ) : ℝ := if Even J then S.Dint else S.Dint ^ (1 / (1 + S.tau))

/-- **Lichtman's `𝐃_J^+`** for a labelled box vector `P = (P_1, …, P_J)` (`P_1 ≥ ⋯ ≥ P_J`,
box values `D_{P_i}`): for every odd position `m ≤ J`,
`D_{P_1} ⋯ D_{P_{m-1}} D_{P_m}^3 < D_int` (`J` even), `< D_int^{1/(1+τ)}` (`J` odd).
(`0`-indexed: position `m = i+1` is odd iff `i` is even.) -/
def BoxAdm (J : ℕ) (P : Fin J → Fin S.H) : Prop :=
  Antitone P ∧ ∀ i : Fin J, Even (i : ℕ) →
    (∏ i' ∈ univ.filter (· < i), S.boxEnd (P i')) * S.boxEnd (P i) ^ 3 < S.threshold J

open Classical in
/-- Labelled tuples of pairwise distinct primes, the `i`-th in box `P_i`. -/
noncomputable def tuples (J : ℕ) (P : Fin J → Fin S.H) : Finset (Fin J → ℕ) :=
  (Fintype.piFinset fun i => (range (⌊S.boxTop (P i)⌋₊ + 1)).filter
    (fun p => p.Prime ∧ S.InBox (P i) p)).filter Function.Injective

open Classical in
/-- **`T_P(a)`**: number of labelled tuples of pairwise distinct primes in the boxes `P` with
product `a`. -/
noncomputable def Tcount (J : ℕ) (P : Fin J → Fin S.H) (a : ℕ) : ℕ :=
  ((S.tuples J P).filter (fun p => ∏ i, p i = a)).card

/-- **`γ(P) = ∏_I m_I!`**, `m_I` the multiplicity of box `I` in `P`. -/
noncomputable def gammaP (J : ℕ) (P : Fin J → Fin S.H) : ℕ :=
  ∏ b : Fin S.H, (univ.filter (fun i => P i = b)).card.factorial

/-- **`B_P(a) = T_P(a)/γ(P)`** (the single canonical labelled-tuple convention). -/
noncomputable def Bcoef (J : ℕ) (P : Fin J → Fin S.H) (a : ℕ) : ℝ :=
  (S.Tcount J P a : ℝ) / (S.gammaP J P : ℝ)

/-! ### The complete scalar coefficient -/

open Classical in
/-- **The complete parity-sensitive scalar coefficient** (§15; Lichtman `(lambdapm)`):
`ℓ_X(d) = ∑_{0 ≤ J ≤ ε₀^{-2}} ∑_{P ∈ 𝐃_J^+} (-1)^J ∑_{ba = d} κ_J(b) B_P(a)`. -/
noncomputable def ellX (d : ℕ) : ℝ :=
  ∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H,
    if S.BoxAdm J P then
      (-1 : ℝ) ^ J * ∑ x ∈ d.divisorsAntidiagonal, S.kappa J x.1 * S.Bcoef J P x.2
    else 0

/-- **`U_X(v) = ∑_{d ∣ v} ℓ_X(d)`**. -/
noncomputable def UX (v : ℕ) : ℝ := ∑ d ∈ v.divisors, S.ellX d

/-- The top of the box grid, `z = D_H = u^{(1+τ)^H}`. -/
noncomputable def ztop : ℝ := S.boxEnd S.H

/-- Standing hypotheses on the parameters: `T ≥ 2` and `X > 1`. -/
structure Good : Prop where
  T_two : 2 ≤ S.T
  X_gt : 1 < S.X

end ScalarParams

end Erdos287.Physical.Sieve
