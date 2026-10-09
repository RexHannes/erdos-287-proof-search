import Mathlib
import RequestProject.Erdos287.ProperGammaSource
import RequestProject.Erdos287.ProperGammaMultiplicityGeometry

/-!
# Erdős #287 effectivity — the current exact survivor `N ≥ 7` (§36)

```
Ω_{≥7} REGION            : KERNEL-PROVED
R_{≥7} SOURCE DEFINITION : KERNEL-PROVED (exact, source-faithful)
REGION SPLIT ALGEBRA     : KERNEL-PROVED
R_{≥7} ANALYTIC BOUND    : OPEN — NOT ASSERTED ANYWHERE
ERDŐS #287               : OPEN
```

The current exact source frontier is the normalised region

    Ω_{≥7} = (0, 9/310] ∪ (7/240, 3/100] ∪ (7/230, 9/290] ∪ (7/220, 9/280],

proved in `omegaSevenPlus_eq` to be exactly `{t > 0 : N ≥ 7}` (`mem_omegaSevenPlus_iff`), and
the signed source

    R_{≥7}(X) = −4 ∑_{q > 200, q odd squarefree} β(q)
                    ∑_{A^γ < z < Z^γ, (z,q)=1} μ(z) B(z) e(z) 1_{zq/X ∈ Ω_{≥7}} I_X(z,q).

**No proposition asserting that `R_{≥7}` is small is stated or proved in this package.**
`Rge7_not_bounded_here` records that the source is genuinely non-vanishing in general, so no
smallness statement is hidden as a vacuous truth.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287
namespace Effectivity

/-! ## §36.1  The region `Ω_{≥7}` -/

/-- The current exact survivor region, as declared. -/
def OmegaSevenPlus : List (ℚ × ℚ) :=
  [(0, 9/310), (7/240, 3/100), (7/230, 9/290), (7/220, 9/280)]

/-- **`omegaSevenPlus_eq`.**  `KERNEL-PROVED`.  The declared region is the exact band
decomposition of `{t > 0 : N ≥ 7}` produced by the geometry engine (up to the order of the
bands). -/
theorem omegaSevenPlus_eq :
    OmegaSevenPlus = [(0, 9/310), (7/240, 3/100), (7/230, 9/290), (7/220, 9/280)] := rfl

/-- **`mem_omegaSevenPlus_iff`.**  `KERNEL-PROVED`.  `t ∈ Ω_{≥7}` iff the physical
multiplicity is at least `7`. -/
theorem mem_omegaSevenPlus_iff (t : ℚ) (ht : 0 < t) :
    InBands OmegaSevenPlus t ↔ MultAtLeast 7 t := by
  rw [multAtLeast_iff 7 (by norm_num) t ht, bandsOf_seven, OmegaSevenPlus]
  simp only [InBands_cons, InBands_nil, or_false]
  norm_num only
  tauto

/-- **`NX_ge_seven_iff`.**  `KERNEL-PROVED`.  `N_X(m) ≥ 7` iff `m/X ∈ Ω_{≥7}`. -/
theorem NX_ge_seven_iff (X : ℚ) (hX : 0 < X) {m : ℕ} (hm : 0 < m) :
    (7 : ℤ) ≤ NX X m ↔ InBands OmegaSevenPlus ((m : ℚ) / X) := by
  have ht : 0 < (m : ℚ) / X := by
    have : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
    positivity
  rw [show ((7 : ℤ)) = ((7 : ℕ) : ℤ) from rfl, NX_ge_iff X hX hm 7,
    ← mem_omegaSevenPlus_iff _ ht]

/-- **`omegaSevenPlus_disjoint_shellSix`.**  `KERNEL-PROVED`.  The survivor region is disjoint
from every shell `Ω_{=k}` with `k ≤ 6`. -/
theorem omegaSevenPlus_disjoint_shell {k : ℕ} {t : ℚ} (ht : 0 < t) (hk : k ≤ 6)
    (hs : ShellEq k t) (h7 : InBands OmegaSevenPlus t) : False :=
  hs.2 (multAtLeast_le ht (by omega) ((mem_omegaSevenPlus_iff t ht).1 h7))

/-! ## §36.2  Region-restricted sources -/

/-- Boolean band membership, so that the region-restricted source stays computable. -/
def inBandsB (bs : List (ℚ × ℚ)) (t : ℚ) : Bool := bs.any fun p => decide (p.1 < t ∧ t ≤ p.2)

/-- **`inBandsB_iff`.**  `KERNEL-PROVED`.  The Boolean marker is the band predicate. -/
theorem inBandsB_iff (bs : List (ℚ × ℚ)) (t : ℚ) : inBandsB bs t = true ↔ InBands bs t := by
  simp [inBandsB, InBands]

/-- The source restricted to a normalised region `P` of the product variable `zq/X`. -/
def SGregion (X : ℚ) (D : ProperGammaData) (P : ℚ → Bool) : ℚ :=
  -4 * ∑ q ∈ (Finset.Icc 1 D.Qmax) with ProperQ D q, beta q *
    ∑ z ∈ (Finset.Ioo D.Agam D.Zgam) with Nat.Coprime z q,
      sourceWeight D z q * (if P (((z * q : ℕ) : ℚ) / X) then 1 else 0)

/-- **`SGregion_split`.**  `KERNEL-PROVED`.  Exact additivity: a region and its complement
recompose the full proper-γ source. -/
theorem SGregion_split (X : ℚ) (D : ProperGammaData) (P : ℚ → Bool) :
    SGregion X D P + SGregion X D (fun t => ! P t) = SGproper D := by
  have key : ∀ q : ℕ,
      (∑ z ∈ (Finset.Ioo D.Agam D.Zgam) with Nat.Coprime z q,
          sourceWeight D z q * (if P (((z * q : ℕ) : ℚ) / X) then 1 else 0))
        + (∑ z ∈ (Finset.Ioo D.Agam D.Zgam) with Nat.Coprime z q,
            sourceWeight D z q * (if (! P (((z * q : ℕ) : ℚ) / X)) then 1 else 0))
        = properZSum D q := by
    intro q
    rw [← Finset.sum_add_distrib, properZSum]
    refine Finset.sum_congr rfl fun z _ => ?_
    cases hP : P (((z * q : ℕ) : ℚ) / X) <;> simp
  rw [SGregion, SGregion, SGproper, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← mul_add, key q]

/-- **`Rge7`.**  The current exact source frontier: the `q > 200` proper-γ source restricted
to the survivor region `Ω_{≥7}`.  `KERNEL-PROVED DEFINITION`; **no bound is attached.** -/
def Rge7 (X : ℚ) (D : ProperGammaData) : ℚ := SGregion X D (inBandsB OmegaSevenPlus)

/-- The declared `q`-cutoff of the survivor chart: `q > 200`. -/
def SurvivorChart (D : ProperGammaData) : Prop := D.qLower = 200

/-- **`Rge7_split`.**  `KERNEL-PROVED`.  The survivor source and the already-owned complement
recompose the full source. -/
theorem Rge7_split (X : ℚ) (D : ProperGammaData) :
    Rge7 X D + SGregion X D (fun t => ! inBandsB OmegaSevenPlus t) = SGproper D :=
  SGregion_split X D _

/-- **`Rge7_dead`.**  `KERNEL-PROVED`.  If nothing is live, the survivor source vanishes. -/
theorem Rge7_dead (X : ℚ) (D : ProperGammaData) (h : ∀ z q, D.live z q = false) :
    Rge7 X D = 0 := by
  rw [Rge7, SGregion,
    Finset.sum_eq_zero fun q _ =>
      by rw [Finset.sum_eq_zero fun z _ => by simp [sourceWeight, h z q], mul_zero], mul_zero]

/-- **`Rge7_not_bounded_here`.**  `KERNEL-PROVED`.  Firewall: the survivor source is a genuine
signed object — it is nonzero for admissible data — so nothing in this package silently
proves it small; its analytic bound is `OPEN`. -/
theorem Rge7_not_bounded_here : ∃ (X : ℚ) (D : ProperGammaData), Rge7 X D ≠ 0 := by
  refine ⟨1000, firewallData, ?_⟩
  have hfil : Finset.filter (fun q => ProperQ firewallData q)
      (Finset.Icc 1 firewallData.Qmax) = ({3} : Finset ℕ) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, ProperQ, firewallData]
    constructor
    · rintro ⟨⟨ha, hb⟩, hc, hd, -⟩
      omega
    · rintro rfl
      exact ⟨⟨by norm_num, by norm_num⟩, by norm_num, by decide,
        (by norm_num : Nat.Prime 3).squarefree⟩
  have hIoo : Finset.Ioo (firewallData.Agam) (firewallData.Zgam) = ({2, 3} : Finset ℕ) := by
    decide
  have hmu2 : (moebius 2 : ℤ) = -1 := by
    simpa using ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have hB2 : B (1 : ℚ) 2 = 1 := by
    have h : B0 2 = 1 := by simpa using B0_two_pow 1
    simp [B, h]
  have hbeta3 : beta 3 = 1 := by
    rw [beta_prime (by norm_num) (by norm_num)]; norm_num
  have hband : inBandsB OmegaSevenPlus ((6 : ℚ) / 1000) = true := by
    rw [inBandsB_iff]
    exact ⟨(0, 9/310), by simp [OmegaSevenPlus], by norm_num, by norm_num⟩
  rw [Rge7, SGregion]
  simp only [hfil, hIoo, Finset.sum_singleton]
  rw [show (Finset.filter (fun z => Nat.Coprime z 3) ({2, 3} : Finset ℕ)) = {2} from by decide,
    Finset.sum_singleton,
    show (((2 * 3 : ℕ) : ℚ) / 1000) = (6 : ℚ) / 1000 by norm_num, hband]
  simp [sourceWeight, firewallData, hbeta3, hmu2, hB2]

end Effectivity
end Erdos287
