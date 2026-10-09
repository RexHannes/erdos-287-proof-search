import RequestProject.Erdos287.W3Publication
import RequestProject.Erdos287.W2984Publication.ChenDecomposition
import RequestProject.Erdos287.W2984Publication.ScalarCertificate

/-!
# W2.984 — the explicit analytic-provider layer (narrow, never constructed)

**ERDŐS #287 REMAINS OPEN.  Nothing in this file is asserted; every structure below is an
explicit hypothesis that is never inhabited in the repository.**

## 1. The W3 framework, with the pair constant left free

`W3FrameworkProvider` packages the **unchanged** W3 / Banks–Freiberg–Maynard inputs, *with the
pair constant removed*:

* the finite affine contact compiler (`AffineContactCompiler r m K`) for any block geometry
  `1 ≤ m`, `2m ≤ r`, width `(r-m)/m < s ≤ 7`;
* normalised Maynard weights `F` on a window, first moment `𝔼P ≥ μ` with `μ > μ₀` arbitrary
  (BFM functional rescaling, BFM Lemma 4.6(i)(ii));
* the pair normaliser `𝔐 > 0` with `𝔐 (rK)² ≤ (1+η) μ²`, `η ≤ η₀` arbitrary (BFM Lemma 4.7:
  `L_K ≤ (1 + O(log^{-1/2} K)) J_K²/I_K`);
* window control (source window, row bound, big prime) on the support;
* the Chen size parameter `X ≥ 1`, the sifting primes `𝒫` (`sift`), and `L_i(t) > Z = ⌊X^{3/14}⌋`
  on the support;
* the spectator weights `ν_{b,i,i'} ≥ 0` (Merikoski's `ν_{H,j,ℓ}`: the Maynard square with
  `d_j = d_ℓ = 1`) and the **exact** agreement `w(t) = ν_{b,i,i'}(t)` whenever both designated
  forms are prime (BFM Lemma 4.6(iii), first step: a prime `> X^δ` has no non-trivial
  support divisor).

It contains **no pair bound, no occupancy and no contact conclusion**.

## 2. The four Chen providers (one recognisable lemma each)

For the *actual* framework data, designated prime coordinate `L_j = L_{b,i}` and sifted
coordinate `L_ℓ = L_{b,i'}` (`i ≠ i'`), `Y = ⌊X^{1/7}⌋`, `Z = ⌊X^{3/14}⌋`:

| provider | paper lemma | statement (eventually in `M`, every `ε > 0`) |
|---|---|---|
| `AffineChenS1Provider` | `AffineChenS1` (§6) | `S₁ ≤ (Ω₁ + C₁δ + ε) 𝔐` |
| `AffineChenS2Provider` | `AffineChenS2` (§9) | `S₂ ≥ (2Ω₂ - C₂δ - ε) 𝔐` (**lower** bound) |
| `AffineChenS3Provider` | `AffineChenS3` (§10) | `S₃ ≤ (2Ω₃ + C₃δ + ε) 𝔐` |
| `AffineChenSquareTailProvider` | `AffineSquareTail` (§5.4) | `S_sq ≤ ε 𝔐` |

The constants `Cᵢ ≥ 0` are fields, **independent of `X`, of the window, of `K`, `μ₀`, `η₀`
and of `δ`** (uniformity is part of the statement).  Their numerical values are a recorded
paper-level constant-extraction obligation (see `W2984_FORMALIZATION_REPORT.md`, §O(δ)).

`PairBoundProvider P c₀` is the *derived* per-pair statement
`𝔼[1_P(L_{b,i}) 1_P(L_{b,i'})] ≤ (c₀ + Cδ + ε) 𝔐`; it is **constructed** from the four Chen
providers in `MainTheorem.lean` (kernel), with `c₀ = 796682507263/200000000000`.
For `c₀ = 4` it is BFM Lemma 4.6(iii) (Selberg), which recovers W3.
-/

open scoped BigOperators
open Classical

namespace Erdos287.W2984Publication

open Erdos287 Erdos287.PostV71V87 Erdos287.PostV87V90R

/-- Merikoski's `Y = X^{1/7}` (`α = 1/7`). -/
noncomputable def chenY (X : ℝ) : ℕ := ⌊X ^ ((1 : ℝ) / 7)⌋₊

/-- Merikoski's `Z = X^{3/14}` (`β = 3/14`). -/
noncomputable def chenZ (X : ℝ) : ℕ := ⌊X ^ ((3 : ℝ) / 14)⌋₊

theorem chenY_le_chenZ {X : ℝ} (hX : 1 ≤ X) : chenY X ≤ chenZ X := by
  unfold chenY chenZ
  apply Nat.floor_le_floor
  exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)

/-- Expectation of `1_P(L_{b,i}) 1_P(L_{b,i'})` under the framework weights. -/
noncomputable def pairExpect {r m K : ℕ} [NeZero r] (F : FiniteWeights)
    (C : AffineContactCompiler r m K) (b : ZMod r) (i i' : Fin K) : ℝ :=
  F.E (fun t => ind (C.slope b i * t + 1).Prime * ind (C.slope b i' * t + 1).Prime)

/-- **W3-framework window data** (pair constant left free). -/
structure FrameworkWindowData {r m K : ℕ} [NeZero r] (C : AffineContactCompiler r m K)
    (H a M : ℕ) where
  F : FiniteWeights
  μ : ℝ
  hμ : 0 < μ
  firstMoment : μ ≤ F.E (fun t => (Pcount (blockCount C) t : ℝ))
  pairNorm : ℝ
  pairNorm_pos : 0 < pairNorm
  η : ℝ
  η_nonneg : 0 ≤ η
  normalizer : pairNorm * ((r : ℝ) * K) ^ 2 ≤ (1 + η) * μ ^ 2
  scaleControl : ∀ t ∈ F.T, 0 < F.w t → WindowControl C a M H t
  X : ℝ
  X_ge_one : 1 ≤ X
  sift : Finset ℕ
  sift_prime : ∀ p ∈ sift, p.Prime
  formsBig : ∀ t ∈ F.T, ∀ b i, chenZ X < C.slope b i * t + 1
  ν : ZMod r → Fin K → Fin K → ℕ → ℝ
  ν_nonneg : ∀ b i i' t, 0 ≤ ν b i i' t
  ν_agree : ∀ b i i', i ≠ i' → ∀ t ∈ F.T, (C.slope b i * t + 1).Prime →
    (C.slope b i' * t + 1).Prime → F.w t = ν b i i' t

namespace FrameworkWindowData

variable {r m K : ℕ} [NeZero r] {C : AffineContactCompiler r m K} {H a M : ℕ}
  (D : FrameworkWindowData C H a M)

/-- The designated prime form `L_j = L_{b,i}`. -/
def Lform (b : ZMod r) (i : Fin K) : ℕ → ℕ := fun t => C.slope b i * t + 1

/-- Affine `S₁` for the pair `(b, i, i')`. -/
noncomputable def S1 (b : ZMod r) (i i' : Fin K) : ℝ :=
  chenS1 D.sift (chenY D.X) D.F.T (D.ν b i i') (Lform (C := C) b i) (Lform (C := C) b i')

/-- Affine `S₂`. -/
noncomputable def S2 (b : ZMod r) (i i' : Fin K) : ℝ :=
  chenS2 D.sift (chenY D.X) (chenZ D.X) D.F.T (D.ν b i i') (Lform (C := C) b i)
    (Lform (C := C) b i')

/-- Affine switched `S₃`. -/
noncomputable def S3 (b : ZMod r) (i i' : Fin K) : ℝ :=
  chenS3 D.sift (chenY D.X) (chenZ D.X) D.F.T (D.ν b i i') (Lform (C := C) b i)
    (Lform (C := C) b i')

/-- Non-squarefree tail. -/
noncomputable def Ssq (b : ZMod r) (i i' : Fin K) : ℝ :=
  chenSsq D.sift (chenY D.X) (chenZ D.X) D.F.T (D.ν b i i') (Lform (C := C) b i)
    (Lform (C := C) b i')

end FrameworkWindowData

/-- Index of a framework family: block geometry, width, Maynard support `δ`, first-moment
target `μ₀`, normaliser slack `η₀`. -/
structure FamilyIndex where
  r : ℕ
  m : ℕ
  hr0 : 0 < r
  hm : 1 ≤ m
  hr : 2 * m ≤ r
  s : ℝ
  hs : ((r : ℝ) - m) / m < s
  hs7 : s ≤ 7
  δ : ℝ
  hδ : 0 < δ
  μ₀ : ℝ
  η₀ : ℝ
  hη₀ : 0 < η₀

instance (I : FamilyIndex) : NeZero I.r := ⟨I.hr0.ne'⟩

/-- A framework family for one index: compiler, cofactor bound, onset, window data. -/
structure FrameworkFamily (I : FamilyIndex) where
  K : ℕ
  compiler : AffineContactCompiler I.r I.m K
  H : ℕ
  onset : ℕ
  data : ∀ a M : ℕ, WideWindow I.s onset a M → FrameworkWindowData compiler H a M
  μ_large : ∀ a M h, I.μ₀ < (data a M h).μ
  η_small : ∀ a M h, (data a M h).η ≤ I.η₀

/-- **The W3 framework provider** (pair constant free; never constructed). -/
structure W3FrameworkProvider where
  δmax : ℝ
  δmax_pos : 0 < δmax
  family : ∀ I : FamilyIndex, I.δ ≤ δmax → FrameworkFamily I

variable (P : W3FrameworkProvider)

/-- **`AffineChenS1`** (affine analogue of Merikoski Lemma 15, with the v3 §6 repair). -/
structure AffineChenS1Provider where
  C₁ : ℝ
  C₁_nonneg : 0 ≤ C₁
  bound : ∀ (I : FamilyIndex) (hI : I.δ ≤ P.δmax), ∀ ε > 0, ∃ N₀ : ℕ,
    ∀ a M (hw : WideWindow I.s (P.family I hI).onset a M), N₀ ≤ M →
      ∀ b i i', i ≠ i' →
        ((P.family I hI).data a M hw).S1 b i i' ≤
          (Omega1 (1/7) + C₁ * I.δ + ε) * ((P.family I hI).data a M hw).pairNorm

/-- **`AffineChenS2`** (affine analogue of Merikoski Lemma 16; a **lower** bound). -/
structure AffineChenS2Provider where
  C₂ : ℝ
  C₂_nonneg : 0 ≤ C₂
  bound : ∀ (I : FamilyIndex) (hI : I.δ ≤ P.δmax), ∀ ε > 0, ∃ N₀ : ℕ,
    ∀ a M (hw : WideWindow I.s (P.family I hI).onset a M), N₀ ≤ M →
      ∀ b i i', i ≠ i' →
        (2 * Omega2 (1/7) (3/14) - C₂ * I.δ - ε) * ((P.family I hI).data a M hw).pairNorm ≤
          ((P.family I hI).data a M hw).S2 b i i'

/-- **`AffineChenS3`** (affine analogue of Merikoski Lemma 17, switched). -/
structure AffineChenS3Provider where
  C₃ : ℝ
  C₃_nonneg : 0 ≤ C₃
  bound : ∀ (I : FamilyIndex) (hI : I.δ ≤ P.δmax), ∀ ε > 0, ∃ N₀ : ℕ,
    ∀ a M (hw : WideWindow I.s (P.family I hI).onset a M), N₀ ≤ M →
      ∀ b i i', i ≠ i' →
        ((P.family I hI).data a M hw).S3 b i i' ≤
          (2 * Omega3 (1/7) (3/14) + C₃ * I.δ + ε) * ((P.family I hI).data a M hw).pairNorm

/-- **`AffineSquareTail`** — the non-squarefree tail created by the repaired Lemma 13 is
negligible. -/
structure AffineChenSquareTailProvider where
  bound : ∀ (I : FamilyIndex) (hI : I.δ ≤ P.δmax), ∀ ε > 0, ∃ N₀ : ℕ,
    ∀ a M (hw : WideWindow I.s (P.family I hI).onset a M), N₀ ≤ M →
      ∀ b i i', i ≠ i' →
        ((P.family I hI).data a M hw).Ssq b i i' ≤ ε * ((P.family I hI).data a M hw).pairNorm

/-- **Derived per-pair bound with constant `c₀`** (constructed in `MainTheorem.lean` from the Chen
providers for `c₀ = chenCertificate`; for `c₀ = 4` this is BFM Lemma 4.6(iii)). -/
structure PairBoundProvider (c₀ : ℝ) where
  Cerr : ℝ
  Cerr_nonneg : 0 ≤ Cerr
  bound : ∀ (I : FamilyIndex) (hI : I.δ ≤ P.δmax), ∀ ε > 0, ∃ N₀ : ℕ,
    ∀ a M (hw : WideWindow I.s (P.family I hI).onset a M), N₀ ≤ M →
      ∀ b i i', i ≠ i' →
        pairExpect ((P.family I hI).data a M hw).F (P.family I hI).compiler b i i' ≤
          (c₀ + Cerr * I.δ + ε) * ((P.family I hI).data a M hw).pairNorm

end Erdos287.W2984Publication
