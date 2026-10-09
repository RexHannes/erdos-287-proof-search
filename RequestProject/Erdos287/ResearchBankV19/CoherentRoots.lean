import RequestProject.Erdos287.ResearchBankV19.ZeroFrequencyCompatibility

/-!
# Erdős #287 — Research Bank V19 §2: coherent root packets

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A root assignment `a : ℕ → ℤ` (one root per modulus) is **coherent** on `q₁, q₂` if
`a(q₁) ≡ a(q₂) (mod gcd(q₁, q₂))`.

Kernel-proved (LEAN BANK):
* **`coherent_zero_mode`** — for ONE coherent assignment `a` used by BOTH dispersion copies, with
  `a(q₁)` a unit mod `g`:
  `a(q₁) n₂ ≡ a(q₂) n₁ (mod g) ↔ n₁ ≡ n₂ (mod g)`.  This is the permitted zero-mode repair.

REPAIRED / RETIRED (`independent_copies_fail`): with two INDEPENDENT assignments `a ≠ a'` for the
two copies the equivalence fails (`q₁ = 3`, `q₂ = 6`, `a ≡ 1`, `a' ≡ 2`, `n₁ = n₂ = 1`), so no
independent-copy assignment satisfies the theorem automatically.
-/

namespace Erdos287
namespace ResearchBankV19
namespace CoherentRoots

/-- Coherence of a root assignment on two moduli. -/
def Coherent (a : ℕ → ℤ) (q₁ q₂ : ℕ) : Prop := a q₁ ≡ a q₂ [ZMOD (Nat.gcd q₁ q₂ : ℤ)]

/-- **The coherent zero-mode theorem** (same assignment `a` in both copies). -/
theorem coherent_zero_mode (a : ℕ → ℤ) {q₁ q₂ : ℕ} (hcoh : Coherent a q₁ q₂)
    (hunit : IsCoprime (a q₁) (Nat.gcd q₁ q₂ : ℤ)) (n₁ n₂ : ℤ) :
    a q₁ * n₂ ≡ a q₂ * n₁ [ZMOD (Nat.gcd q₁ q₂ : ℤ)] ↔ n₁ ≡ n₂ [ZMOD (Nat.gcd q₁ q₂ : ℤ)] := by
  set g : ℤ := ((Nat.gcd q₁ q₂ : ℕ) : ℤ)
  obtain ⟨u, v, huv⟩ := hunit
  have hinv : a q₁ * u ≡ 1 [ZMOD g] :=
    Int.modEq_iff_dvd.2 ⟨v, by linarith⟩
  have h2 : a q₂ * n₁ ≡ a q₁ * n₁ [ZMOD g] := (hcoh.symm).mul_right _
  constructor
  · intro h
    exact (ZeroFrequencyCompatibility.cancel_unit hinv (h.trans h2)).symm
  · intro h
    exact ((h.symm.mul_left (a q₁))).trans h2.symm

/-- **Independent copies fail** (REPAIRED / RETIRED). -/
theorem independent_copies_fail :
    ∃ (a a' : ℕ → ℤ) (q₁ q₂ : ℕ), IsCoprime (a q₁) (Nat.gcd q₁ q₂ : ℤ) ∧
      ¬ ∀ n₁ n₂ : ℤ, (a q₁ * n₂ ≡ a' q₂ * n₁ [ZMOD (Nat.gcd q₁ q₂ : ℤ)] ↔
        n₁ ≡ n₂ [ZMOD (Nat.gcd q₁ q₂ : ℤ)]) := by
  refine ⟨fun _ => 1, fun _ => 2, 3, 6, ?_, fun h => ?_⟩
  · exact ⟨1, 0, by norm_num⟩
  · have := (h 1 1).2 (Int.ModEq.refl _)
    revert this
    decide

/-- The coherent assignment is not coherent for the independent pair (sanity). -/
theorem independent_pair_not_coherent :
    ¬ ((fun _ : ℕ => (1 : ℤ)) 3 ≡ (fun _ : ℕ => (2 : ℤ)) 6 [ZMOD (Nat.gcd 3 6 : ℤ)]) := by
  decide

end CoherentRoots
end ResearchBankV19
end Erdos287
