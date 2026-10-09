import Mathlib

/-!
# Erdős #287 — current tail consolidation: the frozen exact source (V99 decomposition)

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.  This file is exact finite algebra.**

Weighted progression sums over a finite support `S ⊆ ℕ`:

* `progSum S α q b = ∑_{n ∈ S, n ≡ b (mod q)} α n`   (the `P_j(q,b)` of V99);
* `progErr S α M q b = progSum S α q b - M / φ(q)`   (the `E_j(q,b)` of V99, with a
  modulus-independent main mass `M`).

Kernel-proved:

* `v99_relative_centering` — for coprime `f, d ≥ 1`,
  `E(fd,b) = [P(fd,b) - P(f,c)/φ(d)] + E(f,c)/φ(d)`;
* `TensorSource` — the literal tensor data `(Γ_ξ, f_ξ, c_ξ, ℓ_X(d), b_{ξ,d})`;
* `TensorSource.RSigmaP`, `TensorSource.Rrel`, `TensorSource.Rpaid` — the literal remainders;
* `TensorSource.RSigmaP_eq_Rrel_add_Rpaid` — `R_Σ^P = R_rel + R_already_paid` (exact);
* `TensorSource.Rrel_indep_main` — the relative remainder does not involve the main masses
  (the zero-frequency/main term is removed exactly by centering);
* `TensorSource.Rpaid_factor` — `R_paid = ∑_j ∑_ξ Γ_ξ E_j(f_ξ,c_ξ) · ∑_d ℓ_X(d)/φ(d)`;
* `TensorSource.Rpaid_bound` — the base-fluctuation payment from a tiny-modulus fluctuation
  bound (the only analytic input for `R_already_paid`, a Siegel–Walfisz-type hypothesis).
-/

open scoped BigOperators
open Finset

namespace Erdos287.CurrentTail

/-- `P(q,b) = ∑_{n ∈ S, n ≡ b mod q} α n`. -/
noncomputable def progSum (S : Finset ℕ) (α : ℕ → ℝ) (q b : ℕ) : ℝ :=
  ∑ n ∈ S.filter (fun n => n ≡ b [MOD q]), α n

/-- `E(q,b) = P(q,b) - M/φ(q)` with a modulus-independent main mass `M`. -/
noncomputable def progErr (S : Finset ℕ) (α : ℕ → ℝ) (M : ℝ) (q b : ℕ) : ℝ :=
  progSum S α q b - M / (Nat.totient q : ℝ)

theorem totient_cast_pos {q : ℕ} (hq : 0 < q) : (0 : ℝ) < (Nat.totient q : ℝ) := by
  exact_mod_cast Nat.totient_pos.2 hq

/-- **V99 exact relative centering.**  For coprime `f, d ≥ 1` and any `b, c`:
`E(fd,b) = [P(fd,b) - P(f,c)/φ(d)] + E(f,c)/φ(d)`. -/
theorem v99_relative_centering (S : Finset ℕ) (α : ℕ → ℝ) (M : ℝ) {f d : ℕ}
    (hf : 0 < f) (hd : 0 < d) (hfd : Nat.Coprime f d) (b c : ℕ) :
    progErr S α M (f * d) b =
      (progSum S α (f * d) b - progSum S α f c / (Nat.totient d : ℝ)) +
        progErr S α M f c / (Nat.totient d : ℝ) := by
  have h1 := (totient_cast_pos hf).ne'
  have h2 := (totient_cast_pos hd).ne'
  unfold progErr
  rw [Nat.totient_mul hfd, Nat.cast_mul]
  field_simp
  ring

/-- **Literal tensor source data.**  Index set `Ξ` of tensor packets `ξ` with weights `Γ_ξ`,
tiny bases `f_ξ` and residues `c_ξ`; a finite set `D` of large moduli with weights `ℓ_X(d)`;
classes `b_{ξ,d}`; `ℓ` coloured sequences `α_j` on a finite support `S` with main masses
`mass_j`. -/
structure TensorSource (ι : Type*) where
  ell : ℕ
  Xi : Finset ι
  Γ : ι → ℝ
  f : ι → ℕ
  c : ι → ℕ
  D : Finset ℕ
  lX : ℕ → ℝ
  b : ι → ℕ → ℕ
  S : Finset ℕ
  α : ℕ → ℕ → ℝ
  mass : ℕ → ℝ
  f_pos : ∀ ξ ∈ Xi, 0 < f ξ
  d_pos : ∀ d ∈ D, 0 < d
  coprime : ∀ ξ ∈ Xi, ∀ d ∈ D, Nat.Coprime (f ξ) d

namespace TensorSource

variable {ι : Type*} (T : TensorSource ι)

/-- The literal source remainder
`R_Σ^P = ∑_{j<ℓ} ∑_ξ Γ_ξ ∑_d ℓ_X(d) E_j(f_ξ d, b_{ξ,d})`. -/
noncomputable def RSigmaP : ℝ :=
  ∑ j ∈ range T.ell, ∑ ξ ∈ T.Xi, T.Γ ξ * ∑ d ∈ T.D,
    T.lX d * progErr T.S (T.α j) (T.mass j) (T.f ξ * d) (T.b ξ d)

/-- The literal relative remainder
`R_rel = ∑_{j<ℓ} ∑_ξ Γ_ξ ∑_d ℓ_X(d) [P_j(f_ξ d, b) - P_j(f_ξ,c_ξ)/φ(d)]`. -/
noncomputable def Rrel : ℝ :=
  ∑ j ∈ range T.ell, ∑ ξ ∈ T.Xi, T.Γ ξ * ∑ d ∈ T.D,
    T.lX d * (progSum T.S (T.α j) (T.f ξ * d) (T.b ξ d) -
      progSum T.S (T.α j) (T.f ξ) (T.c ξ) / (Nat.totient d : ℝ))

/-- The already-paid base-fluctuation remainder
`R_paid = ∑_{j<ℓ} ∑_ξ Γ_ξ ∑_d ℓ_X(d) E_j(f_ξ,c_ξ)/φ(d)`. -/
noncomputable def Rpaid : ℝ :=
  ∑ j ∈ range T.ell, ∑ ξ ∈ T.Xi, T.Γ ξ * ∑ d ∈ T.D,
    T.lX d * (progErr T.S (T.α j) (T.mass j) (T.f ξ) (T.c ξ) / (Nat.totient d : ℝ))

/-- **`R_Σ^P = R_rel + R_already_paid`**, exactly, by summing V99 centering. -/
theorem RSigmaP_eq_Rrel_add_Rpaid : T.RSigmaP = T.Rrel + T.Rpaid := by
  unfold RSigmaP Rrel Rpaid
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ξ hξ => ?_)
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [← mul_add, v99_relative_centering T.S (T.α j) (T.mass j) (T.f_pos ξ hξ) (T.d_pos d hd)
    (T.coprime ξ hξ d hd) (T.b ξ d) (T.c ξ)]

/-- The relative remainder is independent of the main masses (zero-frequency term removed
exactly). -/
theorem Rrel_indep_main (m' : ℕ → ℝ) :
    ({ T with mass := m' } : TensorSource ι).Rrel = T.Rrel :=
  rfl

/-- Factorised form of the already-paid term. -/
theorem Rpaid_factor : T.Rpaid = ∑ j ∈ range T.ell, ∑ ξ ∈ T.Xi,
    T.Γ ξ * progErr T.S (T.α j) (T.mass j) (T.f ξ) (T.c ξ) *
      ∑ d ∈ T.D, T.lX d / (Nat.totient d : ℝ) := by
  unfold Rpaid
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  rw [mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun d _ => by ring)

/-- **Base-fluctuation payment.**  If every tiny-base fluctuation is at most `η` and
`|∑_d ℓ_X(d)/φ(d)| ≤ L`, then `|R_paid| ≤ ℓ · (∑_ξ |Γ_ξ|) · η · L`.  The hypothesis `hη`
is the (Siegel–Walfisz-type) analytic input for the base layer. -/
theorem Rpaid_bound {η L : ℝ}
    (hη : ∀ j ∈ range T.ell, ∀ ξ ∈ T.Xi,
      |progErr T.S (T.α j) (T.mass j) (T.f ξ) (T.c ξ)| ≤ η)
    (hL : |∑ d ∈ T.D, T.lX d / (Nat.totient d : ℝ)| ≤ L) :
    |T.Rpaid| ≤ T.ell * (∑ ξ ∈ T.Xi, |T.Γ ξ|) * η * L := by
  rw [Rpaid_factor]
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) hL
  calc |∑ j ∈ range T.ell, ∑ ξ ∈ T.Xi,
        T.Γ ξ * progErr T.S (T.α j) (T.mass j) (T.f ξ) (T.c ξ) *
          ∑ d ∈ T.D, T.lX d / (Nat.totient d : ℝ)|
      ≤ ∑ j ∈ range T.ell, ∑ ξ ∈ T.Xi, |T.Γ ξ| * η * L := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ξ hξ => ?_)
        rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hη j hj ξ hξ) (abs_nonneg _)) hL
          (abs_nonneg _) (mul_nonneg (abs_nonneg _) (le_trans (abs_nonneg _) (hη j hj ξ hξ)))
    _ = T.ell * (∑ ξ ∈ T.Xi, |T.Γ ξ|) * η * L := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.sum_mul,
          ← Finset.sum_mul]
        ring

end TensorSource

end Erdos287.CurrentTail
