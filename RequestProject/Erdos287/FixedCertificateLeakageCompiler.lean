import Mathlib
import RequestProject.Erdos287.FixedCertificateTransference

/-!
# The fixed-certificate leakage compiler

The central analytic target of the fixed-certificate route is, for one fixed positive
Ford certificate `g*`, an estimate of the form

`∑_{X/2 < n ≤ X, n ∉ P ∪ N_ε} H_{g*}(n) W(n/X) [Λ(2n−1) + Λ(2n+1) − 4B(n)] ≪_A X/log(X)^A`.

**This file does not prove that estimate, and does not assume it as an axiom.**  What it
does is build the exact *finite* compiler around it, so that the analytic estimate enters
only as an explicit, named antecedent.

## Source status (archaeology)

A search of this repository finds **no literal definition of an admissible fixed Ford
certificate `g*`**, hence no `H_{g*}`, no explicit `P`, `N_ε`, `U` and no published value
of the comparison margin `C_{g*}`.  Consequently:

* the certificate-specific data is carried abstractly by `FixedCertificateData`
  (a partition of the dyadic support together with the weights `a`, `b`, `H`);
* the positivity `1 + C_{g*} > 0` is **not** claimed: it appears as the explicit
  hypothesis `3 * delta < 1 + Cc` of `fixedCertificate_prime_mass_pos`;
* the source-specific `N2` repair is kept as a *separate* antecedent (the `E₂` slack of
  `ComparisonMarginN2`), never folded into another hypothesis.

## Shape of the compiler

`LeakageBound d E → TotalCorrelationBound d E → ComparisonMargin d Cc E →
  PrimeMassLowerBound d ((1 + Cc) * B d − 3E)`

with no analytic hypothesis hidden inside any definition: `LeakageBound`,
`TotalCorrelationBound` and `ComparisonMargin` are literal inequalities about the finite
sums of `d`.  The proof is the kernel-checked transference theorem of
`FixedCertificateTransference.lean`.
-/

open scoped BigOperators

namespace Erdos287
namespace FixedCertificate

/-- The finite data of a fixed-certificate configuration on one dyadic block.

* `P` — the certificate-positive region (`H = 1`);
* `Ngood` — the good composite region (`H ≤ 0`);
* `U` — the leakage region;
* `a` — the nonnegative prime-mass weight, in the intended application
  `a n = W(n/X)(Λ(2n−1) + Λ(2n+1))`;
* `b` — the comparison weight, in the intended application `b n = 4 W(n/X) B(n)`;
* `H` — the certificate kernel `H_{g*}`. -/
structure FixedCertificateData where
  /-- The certificate-positive region. -/
  P : Finset ℕ
  /-- The good composite region. -/
  Ngood : Finset ℕ
  /-- The leakage region. -/
  U : Finset ℕ
  /-- The prime-mass weight. -/
  a : ℕ → ℝ
  /-- The comparison weight. -/
  b : ℕ → ℝ
  /-- The certificate kernel. -/
  H : ℕ → ℝ
  /-- `P` and `Ngood` are disjoint. -/
  hPN : Disjoint P Ngood
  /-- `P` and `U` are disjoint. -/
  hPU : Disjoint P U
  /-- `Ngood` and `U` are disjoint. -/
  hNU : Disjoint Ngood U
  /-- The prime-mass weight is nonnegative. -/
  ha : ∀ n, 0 ≤ a n
  /-- The kernel is `1` on the certificate-positive region. -/
  hHP : ∀ p ∈ P, H p = 1
  /-- The kernel is nonpositive on the good region. -/
  hHN : ∀ n ∈ Ngood, H n ≤ 0

namespace FixedCertificateData

variable (d : FixedCertificateData)

/-- The dyadic support `P ∪ Ngood ∪ U`. -/
def support : Finset ℕ := d.P ∪ d.Ngood ∪ d.U

/-- The signed weight `w = a − b`. -/
def w : ℕ → ℝ := fun n => d.a n - d.b n

/-- The comparison mass `B = ∑_{p ∈ P} b p`. -/
def B : ℝ := ∑ p ∈ d.P, d.b p

end FixedCertificateData

open FixedCertificateData

/-- **Leakage hypothesis** (the analytic target, stated, never assumed): the correlation
sum restricted to the leakage region is at most `E` in absolute value. -/
def LeakageBound (d : FixedCertificateData) (E : ℝ) : Prop :=
  |∑ n ∈ d.U, d.w n * d.H n| ≤ E

/-- **Total-correlation hypothesis**: the full dyadic correlation sum is at most `E`. -/
def TotalCorrelationBound (d : FixedCertificateData) (E : ℝ) : Prop :=
  |∑ n ∈ d.support, d.w n * d.H n| ≤ E

/-- **Comparison margin** `C_{g*}`: on the good region the comparison weight against the
kernel is at least `C·B − E`. -/
def ComparisonMargin (d : FixedCertificateData) (Cc E : ℝ) : Prop :=
  Cc * d.B - E ≤ ∑ n ∈ d.Ngood, d.b n * d.H n

/-- **Comparison margin with the source-specific `N2` repair kept separate**: an extra,
independently accounted slack `E₂`. -/
def ComparisonMarginN2 (d : FixedCertificateData) (Cc E E₂ : ℝ) : Prop :=
  Cc * d.B - E - E₂ ≤ ∑ n ∈ d.Ngood, d.b n * d.H n

/-- **Conclusion**: a lower bound for the prime mass carried by the certificate-positive
region. -/
def PrimeMassLowerBound (d : FixedCertificateData) (L : ℝ) : Prop :=
  L ≤ ∑ p ∈ d.P, d.a p

/-- **The fixed-certificate leakage compiler.**  Every analytic input is an explicit
antecedent; the implication itself is kernel-checked finite algebra. -/
theorem fixedCertificate_leakage_compiler (d : FixedCertificateData) (Cc E : ℝ)
    (hLeak : LeakageBound d E)
    (hTotal : TotalCorrelationBound d E)
    (hMargin : ComparisonMargin d Cc E) :
    PrimeMassLowerBound d ((1 + Cc) * d.B - 3 * E) :=
  Transference.sum_a_P_lower d.P d.Ngood d.U d.a d.b d.w d.H Cc E
    (fun _ => rfl) d.ha d.hHP d.hHN d.hPN d.hPU d.hNU hTotal hLeak hMargin

/-- The same compiler with the `N2` repair carried as a separate antecedent: the extra
slack `E₂` appears additively and nowhere else. -/
theorem fixedCertificate_leakage_compiler_N2 (d : FixedCertificateData) (Cc E E₂ : ℝ)
    (hE₂ : 0 ≤ E₂)
    (hLeak : LeakageBound d E)
    (hTotal : TotalCorrelationBound d E)
    (hMargin : ComparisonMarginN2 d Cc E E₂) :
    PrimeMassLowerBound d ((1 + Cc) * d.B - 3 * E - 3 * E₂) := by
  have h : ComparisonMargin d Cc (E + E₂) := by
    have : Cc * d.B - (E + E₂) = Cc * d.B - E - E₂ := by ring
    rw [ComparisonMargin, this]
    exact hMargin
  have hLeak' : LeakageBound d (E + E₂) := le_trans hLeak (by linarith)
  have hTotal' : TotalCorrelationBound d (E + E₂) := le_trans hTotal (by linarith)
  have := fixedCertificate_leakage_compiler d Cc (E + E₂) hLeak' hTotal' h
  refine le_trans ?_ this
  simp only [PrimeMassLowerBound] at *
  linarith

/-- **Positive prime mass.**  If the error is a small multiple of the comparison mass and
the margin satisfies `3δ < 1 + C_{g*}`, the certificate-positive region carries strictly
positive prime mass.

The positivity of `1 + C_{g*}` is *not* asserted here: it is exactly what the hypothesis
`hdelta` (together with `0 ≤ delta`) demands, and no concrete certificate is supplied. -/
theorem fixedCertificate_prime_mass_pos (d : FixedCertificateData) (Cc E delta : ℝ)
    (hLeak : LeakageBound d E)
    (hTotal : TotalCorrelationBound d E)
    (hMargin : ComparisonMargin d Cc E)
    (hBpos : 0 < d.B)
    (hE : E ≤ delta * d.B)
    (hdelta : 3 * delta < 1 + Cc) :
    0 < ∑ p ∈ d.P, d.a p :=
  (Transference.sum_a_P_pos d.P d.Ngood d.U d.a d.b d.w d.H Cc E delta
    (fun _ => rfl) d.ha d.hHP d.hHN d.hPN d.hPU d.hNU hTotal hLeak hMargin hBpos hE
    hdelta).1

/-- Necessary condition recorded explicitly: the hypotheses of
`fixedCertificate_prime_mass_pos` force `1 + C_{g*} > 0` whenever `delta ≥ 0`. -/
theorem margin_positive_of_hyps {Cc delta : ℝ} (hdelta0 : 0 ≤ delta)
    (hdelta : 3 * delta < 1 + Cc) : 0 < 1 + Cc := by linarith

end FixedCertificate
end Erdos287
