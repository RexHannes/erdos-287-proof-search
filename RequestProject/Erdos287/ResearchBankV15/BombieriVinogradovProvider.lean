import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V15 §B7: the ordinary Bombieri–Vinogradov provider

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`OrdinaryBVProvider` states exactly the uniform (maximal over reduced residue classes) error
estimate used by the fixed-source first-moment argument:

    for every A > 0 there are B, C > 0 such that for all x ≥ 2 and every choice of reduced
    residues r(Q) (gcd(r(Q), Q) = 1),
        ∑_{Q ≤ √x / (log x)^B} | π(x; Q, r(Q)) − π(x)/φ(Q) | ≤ C · x / (log x)^A.

Quantifying over *every* choice function `r` is the maximal form (it is equivalent to putting
`max_{(r,Q)=1}` inside the sum).  The provider is **not** an axiom and is **not** constructed in
the bank; Bombieri–Vinogradov is not proved here.  Every downstream `S1` theorem takes it as an
explicit argument (`FirstMomentContract.s1_contract`).
-/

namespace Erdos287
namespace ResearchBankV15
namespace BombieriVinogradovProvider

/-- `π(x) = #{p ≤ x prime}`. -/
def primeCount (x : ℕ) : ℕ := ((Finset.Icc 1 x).filter Nat.Prime).card

/-- `π(x; Q, r) = #{p ≤ x prime, p ≡ r (mod Q)}`. -/
def primeAPCount (x Q r : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter fun n => n.Prime ∧ n % Q = r % Q).card

/-- The AP error `π(x; Q, r) − π(x)/φ(Q)`. -/
noncomputable def apError (x Q r : ℕ) : ℝ :=
  (primeAPCount x Q r : ℝ) - (primeCount x : ℝ) / (Nat.totient Q : ℝ)

/-- The BV modulus range `Q ≤ √x / (log x)^B`. -/
noncomputable def bvRange (x : ℕ) (B : ℝ) : Finset ℕ :=
  Finset.Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊

/-- **The ordinary Bombieri–Vinogradov provider** (explicit hypothesis; never constructed). -/
structure OrdinaryBVProvider : Prop where
  bv : ∀ A : ℝ, 0 < A → ∃ B C : ℝ, 0 < C ∧ ∀ x : ℕ, 2 ≤ x → ∀ r : ℕ → ℕ,
    (∀ Q, Nat.Coprime (r Q) Q) →
      ∑ Q ∈ bvRange x B, |apError x Q (r Q)| ≤ C * x / Real.log x ^ A

theorem primeCount_10 : primeCount 10 = 4 := by decide

theorem primeAPCount_fixture : primeAPCount 10 4 1 = 1 ∧ primeAPCount 10 4 3 = 2 := by decide

end BombieriVinogradovProvider
end ResearchBankV15
end Erdos287
