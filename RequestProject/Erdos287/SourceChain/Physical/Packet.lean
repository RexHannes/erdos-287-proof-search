import RequestProject.Erdos287.SourceChain.Physical.CRT

/-!
# Erdős #287 — physical source: designated-pair packets, `Γ_ξ`, `f_ξ`, `c_ξ`, `b_{ξ,d}`

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**  Literal construction of
`sources/physical_spec.md` §§5–6 (the Maynard coefficient `ω_d`) and §§8–10 (packet index,
`f_ξ = a_j W q_0`, `Γ_ξ = ω_d ω_{d'}`, the CRT residue `c_ξ`, the reduced pair
`(A_{jℓ}, B_{jℓ})` and the CRT residue `b_{ξ,d}`).

Nothing here is assumed: every residue is *defined* (as the least solution below the modulus)
and its existence, uniqueness and unit property are *proved* from the explicit presieve
hypotheses `PhysData.WGood` (all prime factors of the slopes and of their non-zero differences
divide `W`; the source asserts this holds eventually for `W = ∏_{p ≤ log log log X} p`, which is
proved in `Physical/Presieve.lean`).
-/

open scoped BigOperators
open Finset

namespace Erdos287.Physical

/-- Physical data at one scale: `k` affine forms `L_i(t) = a_i t + 1`, the presieve modulus
`W`, the scale `X`, the window constants `c₁ < c₂`, and the finite tensor decomposition
`F = ∑_v ∏_i f'_{i,v}` of the Maynard test function (§5). -/
structure PhysData where
  k : ℕ
  a : Fin k → ℕ
  W : ℕ
  X : ℝ
  c1 : ℝ
  c2 : ℝ
  V : ℕ
  fp : Fin V → Fin k → ℝ → ℝ

/-- The presieve hypotheses of §6: positive slopes, `W > 0`, every prime divisor of a slope
and of a non-zero slope difference divides `W`. -/
structure PhysData.WGood (P : PhysData) : Prop where
  a_pos : ∀ i, 0 < P.a i
  W_pos : 0 < P.W
  slope : ∀ i, ∀ p : ℕ, p.Prime → p ∣ P.a i → p ∣ P.W
  diff : ∀ i i', i ≠ i' → ∀ p : ℕ, p.Prime → (p : ℤ) ∣ (P.a i : ℤ) - P.a i' → p ∣ P.W

/-- A labelled designated-pair packet `ξ = (j, ℓ, d, d')` (§8). -/
structure Packet (k : ℕ) where
  j : Fin k
  l : Fin k
  d : Fin k → ℕ
  d' : Fin k → ℕ

namespace PhysData

variable (P : PhysData)

/-- The affine form `L_i(t) = a_i t + 1`. -/
def L (i : Fin P.k) (t : ℕ) : ℕ := P.a i * t + 1

/-- **The actual Maynard coefficient** (§6):
`ω_d = 1_{(∏ d_i, W)=1} (∏ μ(d_i)) ∑_v ∏_i f'_{i,v}(log d_i / log X)`. -/
noncomputable def omega (d : Fin P.k → ℕ) : ℝ :=
  if Nat.Coprime (∏ i, d i) P.W then
    (∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) *
      ∑ v, ∏ i, P.fp v i (Real.log (d i) / Real.log P.X)
  else 0

/-- `q_i = [d_i, d'_i]`. -/
def q (ξ : Packet P.k) (i : Fin P.k) : ℕ := Nat.lcm (ξ.d i) (ξ.d' i)

/-- Spectator coordinates `i ∉ {j, ℓ}`. -/
def spec (ξ : Packet P.k) : Finset (Fin P.k) := univ.filter (fun i => i ≠ ξ.j ∧ i ≠ ξ.l)

/-- `q_0 = ∏_{i ≠ j, ℓ} q_i`. -/
def q0 (ξ : Packet P.k) : ℕ := ∏ i ∈ P.spec ξ, P.q ξ i

/-- **`f_ξ = a_j W q_0`.** -/
def f (ξ : Packet P.k) : ℕ := P.a ξ.j * P.W * P.q0 ξ

/-- **`Γ_ξ = ω_d ω_{d'}`.** -/
noncomputable def Gamma (ξ : Packet P.k) : ℝ := P.omega ξ.d * P.omega ξ.d'

/-- The spectator residue `1 - a_j a_i⁻¹ (mod q_i)`, with the explicit Bézout inverse. -/
def specRes (ξ : Packet P.k) (i : Fin P.k) : ℤ :=
  1 - (P.a ξ.j : ℤ) * Nat.gcdA (P.a i) (P.q ξ i)

/-- The CRT system defining `c_ξ`: `x ≡ 1 (mod a_j W)` and `x ≡ 1 - a_j a_i⁻¹ (mod q_i)` for
every spectator `i`. -/
def System (ξ : Packet P.k) (x : ℤ) : Prop :=
  x ≡ 1 [ZMOD (P.a ξ.j * P.W : ℕ)] ∧ ∀ i ∈ P.spec ξ, x ≡ P.specRes ξ i [ZMOD (P.q ξ i : ℕ)]

open Classical in
/-- **`c_ξ`**: the least solution in `[0, f_ξ)` of the CRT system (`0` off the admissible
support, where it is never used). -/
noncomputable def cRes (ξ : Packet P.k) : ℕ :=
  if h : ∃ c, c < P.f ξ ∧ P.System ξ c then Nat.find h else 0

/-- The admissible/compatible physical support (§8): `j < ℓ`, the designated entries are `1`,
all entries are positive and coprime to `W`, and the spectator `q_i` are pairwise coprime. -/
def Admissible (ξ : Packet P.k) : Prop :=
  ξ.j < ξ.l ∧ ξ.d ξ.j = 1 ∧ ξ.d' ξ.j = 1 ∧ ξ.d ξ.l = 1 ∧ ξ.d' ξ.l = 1 ∧
    (∀ i, 0 < ξ.d i ∧ 0 < ξ.d' i) ∧ (∀ i, Nat.Coprime (ξ.d i) P.W ∧ Nat.Coprime (ξ.d' i) P.W) ∧
    (P.spec ξ : Set (Fin P.k)).Pairwise (Function.onFun Nat.Coprime (P.q ξ))

/-- `g_{jℓ} = (a_j, a_ℓ)`. -/
def g (ξ : Packet P.k) : ℕ := Nat.gcd (P.a ξ.j) (P.a ξ.l)

/-- `A_{jℓ} = a_ℓ / g_{jℓ}`. -/
def A (ξ : Packet P.k) : ℕ := P.a ξ.l / P.g ξ

/-- `B_{jℓ} = (a_ℓ - a_j) / g_{jℓ}` (an integer, possibly negative). -/
def B (ξ : Packet P.k) : ℤ := ((P.a ξ.l : ℤ) - P.a ξ.j) / (P.g ξ : ℤ)

open Classical in
/-- **`b_{ξ,d}`**: the least `b < f_ξ d` with `b ≡ c_ξ (mod f_ξ)` and
`A_{jℓ} b ≡ B_{jℓ} (mod d)`. -/
noncomputable def bRes (ξ : Packet P.k) (e : ℕ) : ℕ :=
  if h : ∃ b, b < P.f ξ * e ∧ (b : ℤ) ≡ P.cRes ξ [ZMOD (P.f ξ : ℕ)] ∧
      (P.A ξ : ℤ) * b ≡ P.B ξ [ZMOD (e : ℕ)] then Nat.find h else 0

end PhysData

end Erdos287.Physical
