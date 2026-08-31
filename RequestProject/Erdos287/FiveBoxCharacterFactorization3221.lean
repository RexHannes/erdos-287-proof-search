import Mathlib
import RequestProject.Erdos287.HighConductorCharacterGram3221

/-!
# V20, Phase B — the labelled five-box character factorisation

`3221-FIVEBOX-CHARACTER-FACTORIZATION45 : LEAN_PROVED_FINITE`

The labelled `1 + 2 + 2 + 2` source of the V17–V19 bank is supported on a product box

`w = e · n · ℓ`,  `n = n₁ n₂`,  `ℓ = ℓ₁ ℓ₂`,

with independent coefficients on each labelled prime box.  A Dirichlet character is
multiplicative, so its finite transform factorises **exactly**.

* `blockSum` — a single labelled prime box transform `S_i(χ) = ∑_{p ∈ P_i} w_i(p) χ(p)`.
* `pairBlockSum` — a labelled two-prime block transform.
* `fiveBoxCHat` — the transform of the labelled five-box coefficient.
* `fiveBox_characterTransform_factor` —
  `ĉ_λ(χ) = Eta_λ(χ) · Beta_λ(χ) · Gamma_λ(χ)`.
* `fiveBox_characterTransform_eq_prod_five` —
  `ĉ_λ(χ) = ∏_{i=1}^{5} S_{i,λ}(χ)`.

The internal five-box label `ℓ` is a *box index*, never a modulus; the modulus is always
written `q`.

**No character-sum bound is proved, assumed, or implied.**  Erdős #287 remains OPEN;
Balanced7 remains OPEN.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

open Finset
open scoped BigOperators

namespace Erdos287
namespace V20FiveBox

open Erdos287.CharGram3221

/-- The five-fold expansion of a product of finite sums. -/
theorem sum_mul_sum5 {i1 i2 i3 i4 i5 : Type*} (s1 : Finset i1) (s2 : Finset i2)
    (s3 : Finset i3) (s4 : Finset i4) (s5 : Finset i5) (f1 : i1 → ℂ) (f2 : i2 → ℂ)
    (f3 : i3 → ℂ) (f4 : i4 → ℂ) (f5 : i5 → ℂ) :
    (∑ i ∈ s1, f1 i) * (∑ j ∈ s2, f2 j) * (∑ k ∈ s3, f3 k) * (∑ l ∈ s4, f4 l) *
        (∑ n ∈ s5, f5 n)
      = ∑ i ∈ s1, ∑ j ∈ s2, ∑ k ∈ s3, ∑ l ∈ s4, ∑ n ∈ s5,
          f1 i * f2 j * f3 k * f4 l * f5 n := by
  rw [sum_mul_sum4, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]

/-- The transform of a single labelled prime box, `S_i(χ) = ∑_{p ∈ P} w(p) χ(p)`. -/
noncomputable def blockSum (q : ℕ) (P : Finset ℕ) (w : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) : ℂ :=
  ∑ p ∈ P, w p * chi ((p : ℕ) : ZMod q)

/-- The transform of a labelled two-prime block, written as a literal convolution over the
labelled pair. -/
noncomputable def pairBlockSum (q : ℕ) (P1 P2 : Finset ℕ) (w1 w2 : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) : ℂ :=
  ∑ p ∈ P1, ∑ r ∈ P2, w1 p * w2 r * chi ((p * r : ℕ) : ZMod q)

/-- A labelled two-prime block transform is the product of its two box transforms. -/
theorem pairBlockSum_eq_mul (q : ℕ) (P1 P2 : Finset ℕ) (w1 w2 : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) :
    pairBlockSum q P1 P2 w1 w2 chi = blockSum q P1 w1 chi * blockSum q P2 w2 chi :=
  cHat_twoBox_factorisation chi P1 P2 w1 w2

/-- The character transform of the labelled five-box coefficient
`c_λ(w) = ∑_{e·n₁n₂·ℓ₁ℓ₂ = w} η(e) ν₁(n₁) ν₂(n₂) λ₁(ℓ₁) λ₂(ℓ₂)`. -/
noncomputable def fiveBoxCHat (q : ℕ) (Ebox N1 N2 L1 L2 : Finset ℕ)
    (eta nu1 nu2 lam1 lam2 : ℕ → ℂ) (chi : DirichletCharacter ℂ q) : ℂ :=
  ∑ e ∈ Ebox, ∑ n1 ∈ N1, ∑ n2 ∈ N2, ∑ l1 ∈ L1, ∑ l2 ∈ L2,
    eta e * nu1 n1 * nu2 n2 * lam1 l1 * lam2 l2 *
      chi ((e * n1 * n2 * l1 * l2 : ℕ) : ZMod q)

/-- **`fiveBox_characterTransform_eq_prod_five`.**  `LEAN_PROVED_FINITE`.

`ĉ_λ(χ) = ∏_{i=1}^{5} S_{i,λ}(χ)`: the transform of the labelled five-box coefficient is
the product of the five labelled box transforms.  Finite convolution and character
multiplicativity only. -/
theorem fiveBox_characterTransform_eq_prod_five (q : ℕ) (Ebox N1 N2 L1 L2 : Finset ℕ)
    (eta nu1 nu2 lam1 lam2 : ℕ → ℂ) (chi : DirichletCharacter ℂ q) :
    fiveBoxCHat q Ebox N1 N2 L1 L2 eta nu1 nu2 lam1 lam2 chi
      = blockSum q Ebox eta chi * blockSum q N1 nu1 chi * blockSum q N2 nu2 chi *
        blockSum q L1 lam1 chi * blockSum q L2 lam2 chi := by
  rw [blockSum, blockSum, blockSum, blockSum, blockSum, sum_mul_sum5, fiveBoxCHat]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun n1 _ =>
    Finset.sum_congr rfl fun n2 _ => Finset.sum_congr rfl fun l1 _ =>
      Finset.sum_congr rfl fun l2 _ => ?_
  have hmul : chi ((e * n1 * n2 * l1 * l2 : ℕ) : ZMod q)
      = chi ((e : ℕ) : ZMod q) * chi ((n1 : ℕ) : ZMod q) * chi ((n2 : ℕ) : ZMod q) *
        chi ((l1 : ℕ) : ZMod q) * chi ((l2 : ℕ) : ZMod q) := by
    push_cast
    rw [map_mul, map_mul, map_mul, map_mul]
  rw [hmul]
  ring

/-- **`fiveBox_characterTransform_factor`.**  `LEAN_PROVED_FINITE`.

The three-block form `ĉ_λ(χ) = Eta_λ(χ) · Beta_λ(χ) · Gamma_λ(χ)`, where `Beta` and `Gamma`
are the two labelled two-prime blocks written as literal convolutions. -/
theorem fiveBox_characterTransform_factor (q : ℕ) (Ebox N1 N2 L1 L2 : Finset ℕ)
    (eta nu1 nu2 lam1 lam2 : ℕ → ℂ) (chi : DirichletCharacter ℂ q) :
    fiveBoxCHat q Ebox N1 N2 L1 L2 eta nu1 nu2 lam1 lam2 chi
      = blockSum q Ebox eta chi * pairBlockSum q N1 N2 nu1 nu2 chi *
        pairBlockSum q L1 L2 lam1 lam2 chi := by
  rw [fiveBox_characterTransform_eq_prod_five, pairBlockSum_eq_mul, pairBlockSum_eq_mul]
  ring

/-- The five-box transform of the *high-conductor* coefficient family: on the high sector
the coefficient is the five-box transform, off it the coefficient vanishes. -/
theorem highCoeff_fiveBox (q Dcut : ℕ) (Wbox : Finset ℤ) (c : ℤ → ℂ)
    (chi : DirichletCharacter ℂ q) (hchi : Dcut < chi.conductor) :
    Erdos287.V20Gram.highCoeff q Dcut Wbox c chi = cHat q Wbox c chi := by
  rw [Erdos287.V20Gram.highCoeff, if_pos hchi]

/-- Off the high-conductor sector the coefficient is `0`; combined with the previous lemma
this is the literal indicator description of `F_q`. -/
theorem highCoeff_of_not_high (q Dcut : ℕ) (Wbox : Finset ℤ) (c : ℤ → ℂ)
    (chi : DirichletCharacter ℂ q) (hchi : ¬ Dcut < chi.conductor) :
    Erdos287.V20Gram.highCoeff q Dcut Wbox c chi = 0 := by
  rw [Erdos287.V20Gram.highCoeff, if_neg hchi]

end V20FiveBox
end Erdos287
