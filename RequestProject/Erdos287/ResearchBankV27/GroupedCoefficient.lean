import RequestProject.Erdos287.ResearchBankV27.CommonCauchy

/-!
# Erdős #287 — Research Bank V27 §5.6: the grouped coefficient

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

After the common Cauchy step the energy `V(Ψ) = Σ_o |Σ_i Ψ(i) K(o;i)|²` is opened.  The
regrouped outer (Kloosterman) variables are `β = n₂ u₁`, `γ = n₁ u₂ v₂`; the pair of inner
variables `((s,h),(t,k))` enters only through the grouped frequency

    ℓ = h t − k s,   z = s t,   y = a f (h t − k s).

**LEAN BANK.**
* `bPsi` — `b_Ψ(z) = Σ_{grp(i,i') = z} Ψ(i) conj Ψ(i')`: its type has NO outer argument;
* **`grouped_expansion`** — if the outer correlation `Σ_o K(o;i) conj K(o;i')` depends on the
  inner pair only through `grp(i,i')` (i.e. equals `Σ_b Kl(b; grp(i,i'))` over the regrouped
  outer variables `b = (β,γ)`), then EXACTLY
  `V(Ψ) = Σ_b Σ_z b_Ψ(z) Kl(b; z)`;  the grouped coefficient `b_Ψ(z)` is the same for every
  `b = (β, γ)`;
* `grpConcrete`, `bPsiConcrete` — the literal grouping `(s,h),(t,k) ↦ (st, af(ht − ks))` and
  `b_Ψ(z,y) = Σ_{st = z, af(ht−ks) = y} Ψ(s,h) conj Ψ(t,k)`;
* `concrete_grouping_ell` — `y = a f ℓ` with `ℓ = ht − ks`.
-/

namespace Erdos287
namespace ResearchBankV27
namespace GroupedCoefficient

open Finset CommonCauchy

variable {O I Z B : Type*} [Fintype O] [Fintype I] [Fintype B] [DecidableEq Z]

/-- **The grouped coefficient** `b_Ψ(z)` (no outer argument). -/
noncomputable def bPsi (grp : I → I → Z) (Ψ : I → ℂ) (z : Z) : ℂ :=
  ∑ p ∈ (univ : Finset (I × I)).filter (fun p => grp p.1 p.2 = z), Ψ p.1 * starRingEnd ℂ (Ψ p.2)

theorem energy_eq_sum_pairs (K : O → I → ℂ) (Ψ : I → ℂ) :
    ((energy K Ψ : ℝ) : ℂ) = ∑ p : I × I, Ψ p.1 * starRingEnd ℂ (Ψ p.2) *
      ∑ o, K o p.1 * starRingEnd ℂ (K o p.2) := by
  unfold energy innerSum
  push_cast
  have : ∀ o, ((‖∑ i, Ψ i * K o i‖ : ℝ) : ℂ) ^ 2 =
      (∑ i, Ψ i * K o i) * starRingEnd ℂ (∑ i, Ψ i * K o i) := by
    intro o
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  simp_rw [this, map_sum, map_mul, Finset.sum_mul_sum]
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun o _ => by ring

/-- **Grouped expansion** (LEAN BANK). -/
theorem grouped_expansion (K : O → I → ℂ) (grp : I → I → Z) (Kl : B → Z → ℂ)
    (hgrp : ∀ i i', ∑ o, K o i * starRingEnd ℂ (K o i') = ∑ b, Kl b (grp i i')) (Ψ : I → ℂ)
    [Fintype Z] :
    ((energy K Ψ : ℝ) : ℂ) = ∑ b, ∑ z, bPsi grp Ψ z * Kl b z := by
  rw [energy_eq_sum_pairs]
  simp_rw [hgrp]
  unfold bPsi
  have h1 : ∀ b, ∑ z, (∑ p ∈ (univ : Finset (I × I)).filter (fun p => grp p.1 p.2 = z),
      Ψ p.1 * starRingEnd ℂ (Ψ p.2)) * Kl b z =
      ∑ p : I × I, Ψ p.1 * starRingEnd ℂ (Ψ p.2) * Kl b (grp p.1 p.2) := by
    intro b
    simp_rw [Finset.sum_mul]
    have : ∀ z, ∑ p ∈ (univ : Finset (I × I)).filter (fun p => grp p.1 p.2 = z),
        Ψ p.1 * starRingEnd ℂ (Ψ p.2) * Kl b z =
        ∑ p ∈ (univ : Finset (I × I)).filter (fun p => grp p.1 p.2 = z),
        Ψ p.1 * starRingEnd ℂ (Ψ p.2) * Kl b (grp p.1 p.2) := fun z =>
      Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.1 hp).2]
    simp_rw [this]
    exact Finset.sum_fiberwise univ (fun p : I × I => grp p.1 p.2) _
  simp_rw [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => by rw [Finset.mul_sum]

/-- The regrouped outer variable `β = n₂ u₁`. -/
def betaVar (n2 u1 : ℤ) : ℤ := n2 * u1

/-- The regrouped outer variable `γ = n₁ u₂ v₂`. -/
def gammaVar (n1 u2 v2 : ℤ) : ℤ := n1 * u2 * v2

/-- The literal grouping `((s,h),(t,k)) ↦ (z, y) = (s t, a f (h t − k s))`. -/
def grpConcrete (a f : ℤ) (sh tk : ℤ × ℤ) : ℤ × ℤ :=
  (sh.1 * tk.1, a * f * (sh.2 * tk.1 - tk.2 * sh.1))

/-- The grouped frequency `ℓ = h t − k s`. -/
def ellVar (sh tk : ℤ × ℤ) : ℤ := sh.2 * tk.1 - tk.2 * sh.1

theorem concrete_grouping_ell (a f : ℤ) (sh tk : ℤ × ℤ) :
    grpConcrete a f sh tk = (sh.1 * tk.1, a * f * ellVar sh tk) := rfl

/-- The literal grouped coefficient on a finite box `Ibox` of inner variables `(s,h)`:
`b_Ψ(z,y) = Σ_{st = z, af(ht − ks) = y} Ψ(s,h) conj Ψ(t,k)`. -/
noncomputable def bPsiConcrete (Ibox : Finset (ℤ × ℤ)) (a f : ℤ) (Ψ : ℤ × ℤ → ℂ) (zy : ℤ × ℤ) :
    ℂ :=
  bPsi (I := Ibox) (fun i i' => grpConcrete a f i.1 i'.1) (fun i => Ψ i.1) zy

end GroupedCoefficient
end ResearchBankV27
end Erdos287
