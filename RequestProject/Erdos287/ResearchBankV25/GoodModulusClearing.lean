import Mathlib

/-!
# Erdős #287 — Research Bank V25 §3.5: good-modulus affine clearing

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Variable typing.  The prime variable is `p = A_i t + 1`.  The fixed exceptional modulus stays on
the ORIGINAL prime variable `p` (equivalently on `m₀ = m / A_j`); rational affine denominators
are cleared only on moduli coprime to the relevant fixed slopes.  No modular inverse of `A_j`
modulo `f` is ever introduced: the only inverse used is `u⁻¹` for a unit `u ∈ (ℤ/f)^×`.

**LEAN BANK.**

* `clearing_identity_j` — with `T = A_j p`:  `T − (A_j − A_i) = A_i (A_j t + 1)`;
* `clearing_identity_k` — `A_k T − A_j (A_k − A_i) = A_i A_j (A_k t + 1)`;
* `physical_divisibility_j` — `s ∣ A_j t + 1 ⟹ s ∣ T − (A_j − A_i)`;
* `physical_divisibility_prod` — `D ∣ ∏_k (A_k t + 1) ⟹ D ∣ ∏_k [A_k T − A_j (A_k − A_i)]`;
* `clearing_iff_of_coprime` — on a GOOD modulus (`gcd(s, A_i) = 1`) the clearing is reversible;
* `betaLift` / `betaLift_lattice` / `betaLift_off_lattice` — the supported-lattice map
  `m = A_j m₀`, `β'_u(m) = 1_{A_j ∣ m} β(m/A_j) 1_{m/A_j ≡ c u⁻¹ (f)}`.
-/

namespace Erdos287
namespace ResearchBankV25
namespace GoodModulusClearing

open Finset

/-- **Clearing identity for the `j`-th form** (LEAN BANK). -/
theorem clearing_identity_j (Ai Aj t : ℤ) :
    Aj * (Ai * t + 1) - (Aj - Ai) = Ai * (Aj * t + 1) := by ring

/-- **Clearing identity for the `k`-th form** (LEAN BANK). -/
theorem clearing_identity_k (Ai Aj Ak t : ℤ) :
    Ak * (Aj * (Ai * t + 1)) - Aj * (Ak - Ai) = Ai * Aj * (Ak * t + 1) := by ring

/-- **Physical divisibility, `j`-th form** (LEAN BANK): with `p = A_i t + 1`, `T = A_j p`. -/
theorem physical_divisibility_j {Ai Aj t s p T : ℤ} (hp : p = Ai * t + 1) (hT : T = Aj * p)
    (hs : s ∣ Aj * t + 1) : s ∣ T - (Aj - Ai) := by
  rw [hT, hp, clearing_identity_j]
  exact Dvd.dvd.mul_left hs Ai

/-- **Physical divisibility, product over all forms** (LEAN BANK). -/
theorem physical_divisibility_prod {ι : Type*} (K : Finset ι) (A : ι → ℤ) {Ai Aj t D p T : ℤ}
    (hp : p = Ai * t + 1) (hT : T = Aj * p) (hD : D ∣ ∏ k ∈ K, (A k * t + 1)) :
    D ∣ ∏ k ∈ K, (A k * T - Aj * (A k - Ai)) := by
  have : ∏ k ∈ K, (A k * T - Aj * (A k - Ai)) = (Ai * Aj) ^ K.card * ∏ k ∈ K, (A k * t + 1) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hT, hp, clearing_identity_k]
  rw [this]
  exact Dvd.dvd.mul_left hD _

/-- **Reversibility on a good modulus** (LEAN BANK): if `gcd(s, A_i) = 1` then
`s ∣ T − (A_j − A_i) ↔ s ∣ A_j t + 1`. -/
theorem clearing_iff_of_coprime {Ai Aj t s p T : ℤ} (hp : p = Ai * t + 1) (hT : T = Aj * p)
    (hcop : IsCoprime s Ai) : s ∣ T - (Aj - Ai) ↔ s ∣ Aj * t + 1 := by
  rw [hT, hp, clearing_identity_j]
  exact ⟨fun h => hcop.dvd_of_dvd_mul_left h, fun h => Dvd.dvd.mul_left h Ai⟩

/-- **The supported-lattice lift** `β'_u(m) = 1_{A_j ∣ m} β(m/A_j) 1_{m/A_j ≡ c u⁻¹ (mod f)}`.
Only the inverse of the UNIT `u` is used; `A_j` is never inverted modulo `f`. -/
noncomputable def betaLift (Aj f : ℕ) (c : ZMod f) (u : (ZMod f)ˣ) (β : ℕ → ℂ) (m : ℕ) : ℂ :=
  if Aj ∣ m then (if ((m / Aj : ℕ) : ZMod f) = c * ((u⁻¹ : (ZMod f)ˣ) : ZMod f) then β (m / Aj)
    else 0) else 0

/-- On the lattice `m = A_j m₀` the lift is the original coefficient in the original variable. -/
theorem betaLift_lattice {Aj f : ℕ} (hAj : 0 < Aj) (c : ZMod f) (u : (ZMod f)ˣ) (β : ℕ → ℂ)
    (m0 : ℕ) :
    betaLift Aj f c u β (Aj * m0) =
      if (m0 : ZMod f) = c * ((u⁻¹ : (ZMod f)ˣ) : ZMod f) then β m0 else 0 := by
  unfold betaLift
  rw [if_pos (dvd_mul_right Aj m0), Nat.mul_div_cancel_left m0 hAj]

/-- Off the lattice the lift vanishes. -/
theorem betaLift_off_lattice {Aj f : ℕ} (c : ZMod f) (u : (ZMod f)ˣ) (β : ℕ → ℂ) {m : ℕ}
    (hm : ¬ Aj ∣ m) : betaLift Aj f c u β m = 0 := by
  unfold betaLift; rw [if_neg hm]

/-- The integer map `T = A_j p` lands on the supported lattice. -/
theorem integer_map_on_lattice (Aj p : ℕ) : Aj ∣ Aj * p := dvd_mul_right Aj p

end GoodModulusClearing
end ResearchBankV25
end Erdos287
