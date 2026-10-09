import RequestProject.Erdos287.SourceChain.FourierPoisson

/-!
# Erdős #287 — source chain: literal `F_AA`, the cleanup `F_AA → F_AA^♯`, zero mode, (REC.1)

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**  Source level: `MESSAGE_LEVEL_SOURCE`
(source pack §7 (OB.5), §8 (OB.9)–(OB.10), §10 (Opus repair 2: sectors A–D), §11 (REC.1)).

* `FAAData`, `FAAData.FAA` — the literal actual–actual term (OB.9)
  `∑ C₁₂ 𝒫_M(fl[r₁,r₂], ρ)` with the actual coefficient and the CRT residue `ρ`;
  `FAAConditions` records (OB.10) `n₁ρ ≡ c (f)`, `A n₁ ρ ≡ B (lr₁)`, `A n₂ ρ ≡ B (r₂)`.
* `FAAData.sector` and `FAA_eq_sectors` — the **exact** sector decomposition
  `F_AA = F_A (common r) + F_B (common n) + F_D (diagonal) + F_C (near diagonal) + F_AA^♯`.
  The common-`n` sector is removed **only** when the rough-support flag is set
  (`roughSupport = true`); otherwise `F_AA^♯` does **not** carry `(n₁,n₂) = 1`.
* `clean_conditions` — every term of `F_AA^♯` has `(r₁,r₂) = 1`, `n₁ ≠ n₂`,
  `|n₁ - n₂| ≥ Δ`, and `(n₁,n₂) = 1` exactly when `roughSupport = true`.
* `AA1_cauchy` — (AA.1): `√(ML (MN²/(f²Lz₀) + MN/f)) ≤ (x/f)(z₀^{-1/2} + √(fL/N))`, `x = MN`.
* `nearDiag_cauchy` — `√(ML · MN²/(f²LK)) = (x/f) K^{-1/2}`.
* `zeroMode_vanishes_g1` — (OB.5) vanishes termwise when `g = (r₁,r₂) = 1`.
* `rec1_recombination` — (REC.1): `|∑ Γ_ξ S_ξ| ≤ R_paid + ∑ |Γ_ξ| √(𝓑_ξ |F_AA,ξ^♯|)`
  from per-packet bounds `|S_ξ| ≤ p_ξ + √(𝓑_ξ|F^♯_ξ|)` and `∑ |Γ_ξ| p_ξ ≤ R_paid`.
* `cell_sqrt_split` — `√(𝓑(a+b+c+d)) ≤ √(𝓑a)+√(𝓑b)+√(𝓑c)+√(𝓑d)`.
-/

open scoped BigOperators
open Finset

namespace Erdos287.SourceChain

open Erdos287.CurrentTail

/-! ### Literal `F_AA` (OB.9)–(OB.10) -/

/-- Data of the actual–actual term (OB.9). -/
structure FAAData where
  M : ℝ
  f : ℕ
  A : ℕ
  B : ℕ
  c : ℕ
  Ψhat : ℝ → ℂ
  Ls : Finset ℕ
  R1 : Finset ℕ
  R2 : Finset ℕ
  Ns : Finset ℕ
  C12 : ℕ → ℕ → ℕ → ℕ → ℕ → ℂ
  rho : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ
  /-- the near-diagonal threshold `N/(log x)^C` -/
  Δ : ℝ
  /-- the rough-support flag: `true` only when the actual rough-support theorem is supplied -/
  roughSupport : Bool

/-- (OB.10) for one tuple. -/
def FAAConditions (D : FAAData) (l r1 r2 n1 n2 : ℕ) : Prop :=
  (n1 : ℤ) * D.rho l r1 r2 n1 n2 ≡ D.c [ZMOD D.f] ∧
  (D.A : ℤ) * n1 * D.rho l r1 r2 n1 n2 ≡ D.B [ZMOD l * r1] ∧
  (D.A : ℤ) * n2 * D.rho l r1 r2 n1 n2 ≡ D.B [ZMOD r2]

namespace FAAData

variable (D : FAAData)

/-- The summand `C₁₂ 𝒫_M(fl[r₁,r₂], ρ)`. -/
noncomputable def term (l r1 r2 n1 n2 : ℕ) : ℂ :=
  D.C12 l r1 r2 n1 n2 * PF D.Ψhat D.M ((D.f * l * Nat.lcm r1 r2 : ℕ) : ℝ) (D.rho l r1 r2 n1 n2)

/-- Restricted sum over tuples satisfying `P`. -/
noncomputable def restrict (P : ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
    [∀ l r1 r2 n1 n2, Decidable (P l r1 r2 n1 n2)] : ℂ :=
  ∑ l ∈ D.Ls, ∑ r1 ∈ D.R1, ∑ r2 ∈ D.R2, ∑ n1 ∈ D.Ns, ∑ n2 ∈ D.Ns,
    if P l r1 r2 n1 n2 then D.term l r1 r2 n1 n2 else 0

/-- **(OB.9) literally.** -/
noncomputable def FAA : ℂ :=
  ∑ l ∈ D.Ls, ∑ r1 ∈ D.R1, ∑ r2 ∈ D.R2, ∑ n1 ∈ D.Ns, ∑ n2 ∈ D.Ns, D.term l r1 r2 n1 n2

/-- The five sectors of Opus repair 2 (pairwise disjoint, exhaustive). -/
inductive Sector
  | commonR
  | commonN
  | diagonal
  | nearDiag
  | clean
  deriving DecidableEq, Repr, Fintype

/-- Sector membership: A (common `r`), B (common `n`, only under rough support),
D (diagonal), C (near diagonal), and the clean remainder `♯`. -/
def inSector (s : Sector) (r1 r2 n1 n2 : ℕ) : Prop :=
  let A := 1 < Nat.gcd r1 r2
  let Bn := D.roughSupport = true ∧ 1 < Nat.gcd n1 n2
  let Dg := n1 = n2
  let C := |(n1 : ℝ) - n2| < D.Δ
  match s with
  | .commonR => A
  | .commonN => ¬ A ∧ Bn
  | .diagonal => ¬ A ∧ ¬ Bn ∧ Dg
  | .nearDiag => ¬ A ∧ ¬ Bn ∧ ¬ Dg ∧ C
  | .clean => ¬ A ∧ ¬ Bn ∧ ¬ Dg ∧ ¬ C

open Classical in
/-- Sector sum. -/
noncomputable def sector (s : Sector) : ℂ :=
  D.restrict (fun _ r1 r2 n1 n2 => D.inSector s r1 r2 n1 n2)

/-- `F_AA^♯` — the cleaned actual–actual residual (retains `f, A, B, c, l, r₁, r₂, n₁, n₂`,
the exact CRT residue `ρ`, the actual coefficients `C₁₂`, the Fourier weight and ranges). -/
noncomputable def FAAsharp : ℂ := D.sector .clean

open Classical in
theorem sector_partition (r1 r2 n1 n2 : ℕ) (x : ℂ) :
    x = (if D.inSector .commonR r1 r2 n1 n2 then x else 0) +
      (if D.inSector .commonN r1 r2 n1 n2 then x else 0) +
      (if D.inSector .diagonal r1 r2 n1 n2 then x else 0) +
      (if D.inSector .nearDiag r1 r2 n1 n2 then x else 0) +
      (if D.inSector .clean r1 r2 n1 n2 then x else 0) := by
  unfold inSector
  simp only
  by_cases hA : 1 < Nat.gcd r1 r2
  · rw [if_pos hA, if_neg (fun h => h.1 hA), if_neg (fun h => h.1 hA),
      if_neg (fun h => h.1 hA), if_neg (fun h => h.1 hA)]; ring
  by_cases hB : (D.roughSupport = true ∧ 1 < Nat.gcd n1 n2)
  · rw [if_neg hA, if_pos ⟨hA, hB⟩, if_neg (fun h => h.2.1 hB), if_neg (fun h => h.2.1 hB),
      if_neg (fun h => h.2.1 hB)]; ring
  by_cases hD : n1 = n2
  · rw [if_neg hA, if_neg (fun h => hB h.2), if_pos ⟨hA, hB, hD⟩,
      if_neg (fun h => h.2.2.1 hD), if_neg (fun h => h.2.2.1 hD)]; ring
  by_cases hC : |(n1 : ℝ) - n2| < D.Δ
  · rw [if_neg hA, if_neg (fun h => hB h.2), if_neg (fun h => hD h.2.2),
      if_pos ⟨hA, hB, hD, hC⟩, if_neg (fun h => h.2.2.2 hC)]; ring
  · rw [if_neg hA, if_neg (fun h => hB h.2), if_neg (fun h => hD h.2.2),
      if_neg (fun h => hC h.2.2.2), if_pos ⟨hA, hB, hD, hC⟩]; ring

open Classical in
/-- **Exact sector decomposition** `F_AA = F_A + F_B + F_D + F_C + F_AA^♯`. -/
theorem FAA_eq_sectors :
    D.FAA = D.sector .commonR + D.sector .commonN + D.sector .diagonal +
      D.sector .nearDiag + D.FAAsharp := by
  unfold FAA FAAsharp sector restrict
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine Finset.sum_congr rfl (fun r1 _ => ?_)
  refine Finset.sum_congr rfl (fun r2 _ => ?_)
  refine Finset.sum_congr rfl (fun n1 _ => ?_)
  refine Finset.sum_congr rfl (fun n2 _ => ?_)
  exact D.sector_partition r1 r2 n1 n2 _

/-- **Clean conditions of `F_AA^♯`** — exactly those established by the source:
`(r₁,r₂) = 1`, `n₁ ≠ n₂`, `|n₁ - n₂| ≥ Δ`, and `(n₁, n₂) = 1` only under rough support. -/
theorem clean_conditions {r1 r2 n1 n2 : ℕ} (h : D.inSector .clean r1 r2 n1 n2)
    (hr1 : 0 < r1) :
    Nat.gcd r1 r2 = 1 ∧ n1 ≠ n2 ∧ D.Δ ≤ |(n1 : ℝ) - n2| ∧
      (D.roughSupport = true → 0 < n1 → Nat.gcd n1 n2 = 1) := by
  unfold inSector at h
  simp only at h
  obtain ⟨hA, hB, hD, hC⟩ := h
  have hg : 0 < Nat.gcd r1 r2 := Nat.gcd_pos_of_pos_left _ hr1
  refine ⟨by omega, hD, not_lt.1 hC, fun hr hn1 => ?_⟩
  have : ¬ 1 < Nat.gcd n1 n2 := fun h => hB ⟨hr, h⟩
  have hg' : 0 < Nat.gcd n1 n2 := Nat.gcd_pos_of_pos_left _ hn1
  omega

open Classical in
/-- Without rough support the common-`n` sector is empty: nothing is removed there. -/
theorem commonN_empty_of_not_rough (hr : D.roughSupport = false) :
    D.sector .commonN = 0 := by
  unfold sector restrict inSector
  simp [hr]

end FAAData

/-! ### Cleanup payments after Cauchy (𝓑 = ML, x = MN) -/

/-- **(AA.1)** `√(ML (MN²/(f²Lz₀) + MN/f)) ≤ (x/f)(z₀^{-1/2} + √(fL/N))`. -/
theorem AA1_cauchy {M N L f z0 : ℝ} (hM : 0 < M) (hN : 0 < N) (hL : 0 < L) (hf : 0 < f)
    (hz : 0 < z0) :
    Real.sqrt (M * L * (M * N ^ 2 / (f ^ 2 * L * z0) + M * N / f)) ≤
      (M * N / f) * (1 / Real.sqrt z0 + Real.sqrt (f * L / N)) := by
  have e : M * L * (M * N ^ 2 / (f ^ 2 * L * z0) + M * N / f) =
      (M * N / f) ^ 2 * (1 / z0) + (M * N / f) ^ 2 * (f * L / N) := by
    field_simp
  rw [e]
  refine (sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)).trans (le_of_eq ?_)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (by positivity), Real.sqrt_div' _ hz.le, Real.sqrt_one]
  ring

/-- **Near diagonal** `√(ML · MN²/(f²LK)) = (x/f) K^{-1/2}` (arbitrary log saving for
`K = (log x)^C`, with the explicit `1/f` density kept). -/
theorem nearDiag_cauchy {M N L f K : ℝ} (hM : 0 < M) (hN : 0 < N) (hL : 0 < L) (hf : 0 < f)
    (hK : 0 < K) :
    Real.sqrt (M * L * (M * N ^ 2 / (f ^ 2 * L * K))) = (M * N / f) * (1 / Real.sqrt K) := by
  have e : M * L * (M * N ^ 2 / (f ^ 2 * L * K)) = (M * N / f) ^ 2 * (1 / K) := by
    field_simp
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), Real.sqrt_div' _ hK.le,
    Real.sqrt_one]

/-! ### Zero mode -/

/-- **(OB.5) at `g = 1`**: `1_{n₁ ≡ n₂ (1)} - 1/φ(1) = 0`. -/
theorem zeroMode_vanishes_g1 (n1 n2 : ℕ) :
    ind (n1 ≡ n2 [MOD 1]) - 1 / (Nat.totient 1 : ℝ) = 0 := by
  unfold ind
  simp [Nat.modEq_one]

/-- The full normalised zero mode `(1/(flt))(1_{n₁≡n₂ (g)} - 1/φ(g))` vanishes when
`g = (r₁,r₂) = 1`. -/
theorem zeroMode_full_vanishes {r1 r2 : ℕ} (hg : Nat.gcd r1 r2 = 1) (f l n1 n2 : ℕ) :
    (1 / ((f * l * Nat.lcm r1 r2 : ℕ) : ℝ)) *
      (ind (n1 ≡ n2 [MOD Nat.gcd r1 r2]) - 1 / (Nat.totient (Nat.gcd r1 r2) : ℝ)) = 0 := by
  rw [hg, zeroMode_vanishes_g1, mul_zero]

/-! ### (REC.1) recombination -/

/-- `√(𝓑(a+b+c+d)) ≤ √(𝓑a) + √(𝓑b) + √(𝓑c) + √(𝓑d)`. -/
theorem cell_sqrt_split {B a b c d : ℝ} (hB : 0 ≤ B) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) :
    Real.sqrt (B * (a + b + c + d)) ≤
      Real.sqrt (B * a) + Real.sqrt (B * b) + Real.sqrt (B * c) + Real.sqrt (B * d) := by
  rw [show B * (a + b + c + d) = B * a + B * b + B * c + B * d by ring]
  calc Real.sqrt (B * a + B * b + B * c + B * d)
      ≤ Real.sqrt (B * a + B * b + B * c) + Real.sqrt (B * d) :=
        sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)
    _ ≤ Real.sqrt (B * a + B * b) + Real.sqrt (B * c) + Real.sqrt (B * d) := by
        gcongr; exact sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)
    _ ≤ _ := by
        gcongr; exact sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)

/-- **(REC.1)**: `|∑ Γ_ξ S_ξ| ≤ R_paid + ∑ |Γ_ξ| √(𝓑_ξ |F^♯_ξ|)`. -/
theorem rec1_recombination {ι : Type*} (Xi : Finset ι) (Γ S p Bc F : ι → ℝ) (Rpaid : ℝ)
    (hS : ∀ ξ ∈ Xi, |S ξ| ≤ p ξ + Real.sqrt (Bc ξ * |F ξ|))
    (hpaid : ∑ ξ ∈ Xi, |Γ ξ| * p ξ ≤ Rpaid) :
    |∑ ξ ∈ Xi, Γ ξ * S ξ| ≤ Rpaid + ∑ ξ ∈ Xi, |Γ ξ| * Real.sqrt (Bc ξ * |F ξ|) := by
  calc |∑ ξ ∈ Xi, Γ ξ * S ξ| ≤ ∑ ξ ∈ Xi, |Γ ξ * S ξ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ξ ∈ Xi, (|Γ ξ| * p ξ + |Γ ξ| * Real.sqrt (Bc ξ * |F ξ|)) := by
        refine Finset.sum_le_sum (fun ξ hξ => ?_)
        rw [abs_mul, ← mul_add]
        exact mul_le_mul_of_nonneg_left (hS ξ hξ) (abs_nonneg _)
    _ = ∑ ξ ∈ Xi, |Γ ξ| * p ξ + ∑ ξ ∈ Xi, |Γ ξ| * Real.sqrt (Bc ξ * |F ξ|) :=
        Finset.sum_add_distrib
    _ ≤ _ := by linarith

end Erdos287.SourceChain
