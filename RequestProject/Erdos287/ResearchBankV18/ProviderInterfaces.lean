import Mathlib

/-!
# Erdős #287 — Research Bank V18 §4: provider interfaces (EXTERNAL PROVIDER)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Maynard's exponential-sum lemmas are **not** formalized.  They enter only through the explicit
contracts below, whose statements contain their real content: an estimate `B` for a fixed
kernel `K` that is **stable under arbitrary one-bounded coefficient slots**.  Whether an actual
branch (its kernel, ranges, well-factorability) satisfies the source hypotheses is part of what a
user of the contract must supply; nothing in the bank constructs either contract.

* `MaynardFirstExponentialProvider K B` — two coefficient slots `(α_m)`, `(β_n)`;
* `MaynardSecondExponentialProvider K B` — three coefficient slots.
* `OneBounded` — sup-norm `≤ 1`.
* `first_provider_falsifiable` — the contract is a genuine proposition (fails for `B < 0`).
-/

namespace Erdos287
namespace ResearchBankV18
namespace ProviderInterfaces

/-- A one-bounded coefficient sequence. -/
def OneBounded {ι : Type*} (a : ι → ℂ) : Prop := ∀ i, ‖a i‖ ≤ 1

/-- The bilinear form `∑_{m,n} α_m β_n K(m,n)`. -/
noncomputable def bilin {ι κ : Type*} [Fintype ι] [Fintype κ] (K : ι → κ → ℂ) (α : ι → ℂ) (β : κ → ℂ) : ℂ :=
  ∑ i, ∑ j, α i * β j * K i j

/-- The trilinear form `∑_{m,n,r} α_m β_n γ_r K(m,n,r)`. -/
noncomputable def trilin {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ] (K : ι → κ → ρ → ℂ)
    (α : ι → ℂ) (β : κ → ℂ) (γ : ρ → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ r, α i * β j * γ r * K i j r

/-- **Maynard first exponential provider** (EXTERNAL PROVIDER contract; never constructed). -/
structure MaynardFirstExponentialProvider {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : ι → κ → ℂ) (B : ℝ) : Prop where
  stable : ∀ α β, OneBounded α → OneBounded β → ‖bilin K α β‖ ≤ B

/-- **Maynard second exponential provider** (EXTERNAL PROVIDER contract; never constructed). -/
structure MaynardSecondExponentialProvider {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    (K : ι → κ → ρ → ℂ) (B : ℝ) : Prop where
  stable : ∀ α β γ, OneBounded α → OneBounded β → OneBounded γ → ‖trilin K α β γ‖ ≤ B

/-- The first contract is a genuine (falsifiable) proposition. -/
theorem first_provider_falsifiable :
    ¬ MaynardFirstExponentialProvider (fun (_ : Unit) (_ : Unit) => (1 : ℂ)) (-1) := by
  intro h
  have := h.stable (fun _ => 1) (fun _ => 1) (fun _ => by simp) (fun _ => by simp)
  have h0 := norm_nonneg (bilin (fun (_ : Unit) (_ : Unit) => (1 : ℂ)) (fun _ => 1) fun _ => 1)
  linarith

end ProviderInterfaces
end ResearchBankV18
end Erdos287
