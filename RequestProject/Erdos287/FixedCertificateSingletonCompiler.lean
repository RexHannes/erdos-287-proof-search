import Mathlib
import RequestProject.Erdos287.FixedCertificateSingletonFragment
import RequestProject.Erdos287.FixedCertificateSmoothParity

/-!
# The singleton Type-II socket and the conditional leakage compiler (V13, Parts B, I, J)

## Part B — status of the `k = 0`, `J = ∅` cell identity

The source statement is: on the smooth branch with `σ = ν₀ − 2ε`, `γ = 1/2 − ε` and
`P⁺(n) ≤ n^σ`, all prime factors of `n` lie below the Ford splitting threshold, hence the
canonical high-prime component is empty and the fixed Ford weight reduces to
`H_*(n) = ∑_{d ∣ n, d ≤ n^γ} μ(d)`, i.e. the existing `truncMobius` packet.

**Archaeology verdict: `K0_CELL_IDENTITY_SOURCE_STILL_EXTERNAL`.**

A repository-wide search finds *no* Lean object for the Ford canonical split, no `G_*`, no
`g*`, no splitting threshold and no `ε`/`εStar` shrink parameter: the only certificate
data present is the transcribed branch table `Erdos287.FordData.fordCandidate` together
with the never-inhabited predicate `Erdos287.FordData.CertificatePinned`.  Since the
canonical split is not encoded, the specialization cannot be *proved* — it could only be
assumed, which is exactly the firewall this run is forbidden to breach.  Therefore:

* no fake Ford factorisation definition is introduced;
* the `cell_identity` field of `Erdos287.SmoothParity.FixedCertificateSmoothParityPacket`
  is left uninhabited;
* the missing statement is named exactly, as `K0CellIdentitySource` below, and every
  downstream theorem in this file carries it as an explicit antecedent.

## Part I — the open analytic socket

`SingletonGeneratedTypeIIInput` is the smallest honest interface for
`287-SMOOTH-PARITY-SINGLETON-GENERATED-TYPEII45`.  It is a `Prop`-valued structure whose
arithmetic ingredients (`Lam`, `B`, `W`, `xi`, `kappa`) are **abstract parameters**: this
project does not contain the von Mangoldt function in Ford–Maynard normalisation, the
Ford–Maynard analytic weights, or any asymptotic theorem, and nothing here pretends
otherwise.  The structure is **never inhabited**.

Status: `287-SMOOTH-PARITY-SINGLETON-GENERATED-TYPEII45 = OPEN_ANALYTIC`.

## Part J — the conditional compiler

`smoothParity_of_singletonTypeII`, `parentLeakage_of_singletonTypeII` and
`primeMassPos_of_singletonTypeII` chain

  singleton Type-II bound (open analytic)
    + packet reduction (source-blocked)
    + cell identity (source-blocked)
    + `canonical_singleton_typeII` (proved)
  ⟹ smooth-parity packet bound ⟹ parent leakage bound ⟹ positive prime mass,

with the **three error channels kept separate** throughout: the total correlation error
`ET`, the leakage errors `Es`/`Er`, and the `N2` error `E2`.  `E2` is never merged into
the sign region: it is passed to `Erdos287.SmoothParity.parent_prime_mass_pos`, which
itself routes it through the four-region theorem `Transference4.sum_a_P_pos4_fraction`.

Classification: `PROVED_COMPILER / CONDITIONAL_ON_OPEN_ANALYTIC_INPUT`.

## Provider firewall

No bridge is asserted from `SingletonClass.mobius` to Gate 1B, from `SingletonClass.model`
to QK56, or from `SingletonGeneratedTypeIIInput` to Gate 1A, H8/H9, Pascadi, or a
well-factorable theorem.  Those dictionaries remain research questions outside Lean.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace Singleton

open Erdos287.SmoothParity

/-! ## Part B — the exact missing source statement -/

/-- **`K0CellIdentitySource`** — the literal statement that the `k = 0`, `J = ∅` cell of
the Ford factorisation reduces, on the smooth sector, to the truncated Möbius weight at
the cut `cut n` (in the source, `cut n = ⌊n^{1/2−ε}⌋`).

This project contains no Ford canonical split, so this predicate is **`SOURCE_BLOCKED`**:
it is never proved and never assumed globally, only carried as an antecedent. -/
def K0CellIdentitySource (sector : Finset ℕ) (Hs : ℕ → ℤ) (cut : ℕ → ℕ) : Prop :=
  ∀ n ∈ sector, Hs n = truncMobius n (cut n)

/-- Given the missing source identity, the packet's `cell_identity` field is exactly
discharged — and nothing more is needed.  This records that `K0CellIdentitySource` is
precisely the gap, not a proxy for it. -/
theorem k0CellIdentitySource_is_cell_identity {sector : Finset ℕ} {Hs : ℕ → ℤ} {cut : ℕ → ℕ}
    (h : K0CellIdentitySource sector Hs cut) {n : ℕ} (hn : n ∈ sector) :
    Hs n = ∑ d ∈ n.divisors.filter (fun d => d ≤ cut n), ArithmeticFunction.moebius d :=
  smoothParity_missing_source h hn

/-! ## Part I — the open analytic socket -/

/-- **`SingletonGeneratedTypeIIInput`** — `OPEN_ANALYTIC`.

The bilinear smallness statement for an *actual generated* singleton/complement packet:

`|∑_{(m,n) ∈ support} ξ(m) κ(n) W(mn/X) [Lam(2mn−1) + Lam(2mn+1) − 4 B(mn)]| ≤ E`

restricted to the singleton Type-II window `X^{σ/3} < m ≤ X^σ`, which is exactly the range
delivered by `canonical_singleton_typeII` / `singleton_real_power_window`.

`Lam`, `B`, `W`, `xi`, `kappa` are abstract function parameters.  In the intended
application `Lam` is von Mangoldt, `B` the Ford–Maynard comparison density and `W` the
smooth cutoff, but **none of that is formalised here**, and no theorem in this project
inhabits this structure. -/
structure SingletonGeneratedTypeIIInput
    (eps : ℝ) (cls : SingletonClass) (X E : ℝ) (complementDepth : ℕ)
    (support : Finset (ℕ × ℕ)) (xi kappa Lam B : ℕ → ℝ) (W : ℝ → ℝ) : Prop where
  /-- The base is in the asymptotic regime. -/
  X_gt_one : 1 < X
  /-- Every selected factor lies in the singleton Type-II window. -/
  window : ∀ p ∈ support,
    X ^ (sigmaOf eps / 3) < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ X ^ sigmaOf eps
  /-- The complement carries at most `39` fragmentation factors, the finite bound
  certified by `singleton_complement_depth_le_39`. -/
  complement_depth_le : complementDepth ≤ 39
  /-- **The open analytic estimate.** -/
  smallness :
    |∑ p ∈ support, xi p.1 * kappa p.2 * W ((p.1 * p.2 : ℕ) / X) *
      (Lam (2 * p.1 * p.2 - 1) + Lam (2 * p.1 * p.2 + 1) - 4 * B (p.1 * p.2))| ≤ E

/-- **`SingletonPacketReduction`** — `SOURCE_BLOCKED`.

The structural step identifying the smooth-parity packet sum `∑_{n ∈ sector} f(n) H_*(n)`
with (a quantity dominated by) the singleton Type-II bilinear sum.  In the source this is
the Heath-Brown/Ford dissection of the smooth branch; it is not encoded in this
repository, so it is carried as an explicit antecedent rather than assumed. -/
def SingletonPacketReduction
    (sector : Finset ℕ) (Hs : ℕ → ℤ) (f : ℕ → ℝ) (X : ℝ)
    (support : Finset (ℕ × ℕ)) (xi kappa Lam B : ℕ → ℝ) (W : ℝ → ℝ) : Prop :=
  |∑ n ∈ sector, f n * (Hs n : ℝ)| ≤
    |∑ p ∈ support, xi p.1 * kappa p.2 * W ((p.1 * p.2 : ℕ) / X) *
      (Lam (2 * p.1 * p.2 - 1) + Lam (2 * p.1 * p.2 + 1) - 4 * B (p.1 * p.2))|

/-! ## Part J — the conditional compiler -/

variable {eps : ℝ}

/-- **`smoothParity_of_singletonTypeII`** — `PROVED_COMPILER / CONDITIONAL_ON_OPEN_ANALYTIC_INPUT`.

Singleton Type-II bounds for a generated packet, together with the source-blocked packet
reduction and the source-blocked `k = 0`, `J = ∅` cell identity, give the smooth-parity
packet bound.

The fragmentation certificate `c` is a genuine input: `canonical_singleton_typeII` is
invoked to certify that the Type-II window the analytic socket is stated on is the one the
canonical singleton selection actually produces (`ε < z ≤ ε + σ`), so no step here quietly
widens the window. -/
theorem smoothParity_of_singletonTypeII
    (h : AdmissibleEps eps) (c : FordSmoothFragmentCertificate (sigmaOf eps))
    {cls : SingletonClass} {X E : ℝ} {dep : ℕ}
    {support : Finset (ℕ × ℕ)} {xi kappa Lam B : ℕ → ℝ} {W : ℝ → ℝ}
    {sector : Finset ℕ} {Hs : ℕ → ℤ} {cut : ℕ → ℕ} {f : ℕ → ℝ}
    (hcut : ∀ n ∈ sector, 1 ≤ cut n)
    (hcell : K0CellIdentitySource sector Hs cut)
    (hred : SingletonPacketReduction sector Hs f X support xi kappa Lam B W)
    (hinp : SingletonGeneratedTypeIIInput eps cls X E dep support xi kappa Lam B W) :
    FixedCertificateSmoothParityPacket sector Hs cut f E ∧
      eps < chosenSize c ∧ chosenSize c ≤ eps + sigmaOf eps := by
  obtain ⟨-, -, -, hw1, hw2⟩ := canonical_singleton_typeII h c
  exact ⟨{ cut_pos := hcut
           cell_identity := hcell
           analytic_bound := le_trans hred hinp.smallness }, hw1, hw2⟩

/-- **`parentLeakage_of_singletonTypeII`** — `PROVED_COMPILER / CONDITIONAL_ON_OPEN_ANALYTIC_INPUT`.

The smooth-parity child bound produced by the singleton route, together with the bound for
the remaining leakage children, gives the parent leakage bound over `Usmooth ∪ Urest`.
The two channels stay separate: the result is `Es + Er`, not a merged constant. -/
theorem parentLeakage_of_singletonTypeII
    (h : AdmissibleEps eps) (c : FordSmoothFragmentCertificate (sigmaOf eps))
    {cls : SingletonClass} {X Es Er : ℝ} {dep : ℕ}
    {support : Finset (ℕ × ℕ)} {xi kappa Lam B : ℕ → ℝ} {W : ℝ → ℝ}
    {Usmooth Urest : Finset ℕ} {Hs : ℕ → ℤ} {cut : ℕ → ℕ} {f : ℕ → ℝ}
    (hdisj : Disjoint Usmooth Urest)
    (hcut : ∀ n ∈ Usmooth, 1 ≤ cut n)
    (hcell : K0CellIdentitySource Usmooth Hs cut)
    (hred : SingletonPacketReduction Usmooth Hs f X support xi kappa Lam B W)
    (hinp : SingletonGeneratedTypeIIInput eps cls X Es dep support xi kappa Lam B W)
    (hr : |∑ n ∈ Urest, f n * (Hs n : ℝ)| ≤ Er) :
    |∑ n ∈ (Usmooth ∪ Urest), f n * (Hs n : ℝ)| ≤ Es + Er := by
  have hpkt := (smoothParity_of_singletonTypeII h c hcut hcell hred hinp).1
  exact parent_leakage_two_children Usmooth Urest (fun n => f n * (Hs n : ℝ)) Es Er
    hdisj hpkt.analytic_bound hr

/-- **`primeMassPos_of_singletonTypeII`** — `PROVED_COMPILER / CONDITIONAL_ON_OPEN_ANALYTIC_INPUT`.

The full chain: singleton Type-II input (open analytic) + packet reduction and cell
identity (source-blocked) + the remaining leakage children + the total-correlation channel
`ET` + the **separate** `N2` channel `E2` + the comparison margin `EM` give strictly
positive prime mass.

Every analytic ingredient is an explicit antecedent; nothing is assumed globally, and `E2`
is passed on its own channel, never folded into the sign region. -/
theorem primeMassPos_of_singletonTypeII
    (h : AdmissibleEps eps) (c : FordSmoothFragmentCertificate (sigmaOf eps))
    {cls : SingletonClass} {X Es Er ET E2 EM Cc : ℝ} {dep : ℕ}
    {support : Finset (ℕ × ℕ)} {xi kappa Lam B : ℕ → ℝ} {W : ℝ → ℝ}
    (P N1 N2 Usmooth Urest : Finset ℕ) (a b w H : ℕ → ℝ)
    {Hs : ℕ → ℤ} {cut : ℕ → ℕ}
    (hHs : ∀ n, (Hs n : ℝ) = H n) (hw : ∀ n, w n = a n - b n)
    (ha : ∀ n, 0 ≤ a n)
    (hHP : ∀ p ∈ P, H p = 1)
    (hHN1 : ∀ n ∈ N1, H n ≤ 0)
    (hPN1 : Disjoint P N1) (hPN2 : Disjoint P N2) (hPU : Disjoint P (Usmooth ∪ Urest))
    (hN1N2 : Disjoint N1 N2) (hN1U : Disjoint N1 (Usmooth ∪ Urest))
    (hN2U : Disjoint N2 (Usmooth ∪ Urest))
    (hSR : Disjoint Usmooth Urest)
    (hTotal : |∑ n ∈ (P ∪ N1 ∪ N2 ∪ (Usmooth ∪ Urest)), w n * H n| ≤ ET)
    (hcut : ∀ n ∈ Usmooth, 1 ≤ cut n)
    (hcell : K0CellIdentitySource Usmooth Hs cut)
    (hred : SingletonPacketReduction Usmooth Hs w X support xi kappa Lam B W)
    (hinp : SingletonGeneratedTypeIIInput eps cls X Es dep support xi kappa Lam B W)
    (hr : |∑ n ∈ Urest, w n * H n| ≤ Er)
    (hN2 : |∑ n ∈ N2, w n * H n| ≤ E2)
    (hMargin : Cc * (∑ p ∈ P, b p) - EM ≤ ∑ n ∈ N1, b n * H n)
    (hsmall : ET + (Es + Er) + E2 + EM < (1 + Cc) * (∑ p ∈ P, b p)) :
    0 < ∑ p ∈ P, a p := by
  have hpkt := (smoothParity_of_singletonTypeII h c hcut hcell hred hinp).1
  have hs : |∑ n ∈ Usmooth, w n * H n| ≤ Es := by
    have := hpkt.analytic_bound
    simpa [hHs] using this
  exact parent_prime_mass_pos P N1 N2 Usmooth Urest a b w H Cc ET Es Er E2 EM
    hw ha hHP hHN1 hPN1 hPN2 hPU hN1N2 hN1U hN2U hSR hTotal hs hr hN2 hMargin hsmall

/-! ## Non-vacuity guard for the fragmentation interface

The compiler above would be worthless if `FordSmoothFragmentCertificate` were an
unsatisfiable specification (every conclusion would then hold vacuously).  The witness
below shows the specification is satisfiable at a concrete admissible `ε`: eight pieces of
normalised size `1/8`, four per side, no terminal piece.

This is a **toy witness certifying satisfiability only**.  It is not the Ford–Maynard
fragmentation output, and it is not used by any theorem. -/

/-- A concrete admissible shrink parameter. -/
noncomputable def epsWitness : ℝ := 1 / 1000000

theorem epsWitness_admissible : AdmissibleEps epsWitness := by
  constructor <;> norm_num [epsWitness, nu0R]

/-- Satisfiability witness for `FordSmoothFragmentCertificate` (see the note above). -/
noncomputable def fragmentWitness :
    FordSmoothFragmentCertificate (sigmaOf epsWitness) where
  s := 4
  r := 4
  zu := fun _ => 1 / 8
  zv := fun _ => 1 / 8
  s_pos := by norm_num
  s_le := by norm_num
  r_pos := by norm_num
  r_le := by norm_num
  tu := none
  tv := none
  tu_last := by simp
  tv_last := by simp
  zu_term := by simp
  zv_term := by simp
  zu_nonterm := by
    intro i _ _
    constructor <;> norm_num [sigmaOf, nu0R, epsWitness]
  zv_nonterm := by
    intro i _ _
    constructor <;> norm_num [sigmaOf, nu0R, epsWitness]
  total := by norm_num

/-- The witness has `s + r = 8 ≥ 7`, consistent with `fragment_seven_le_card`. -/
theorem fragmentWitness_depth : fragmentDepth fragmentWitness = 8 := rfl

/-- On the witness the canonical selection is a Möbius singleton of size `1/8`, which
indeed lies in the Type-II window `(ε, ε + σ]`. -/
theorem fragmentWitness_chosen :
    chosenClass fragmentWitness = SingletonClass.mobius ∧
      chosenSize fragmentWitness = 1 / 8 ∧
      epsWitness < chosenSize fragmentWitness ∧
      chosenSize fragmentWitness ≤ epsWitness + sigmaOf epsWitness := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;>
    · show _
      norm_num [chosenSize, fragmentWitness, sigmaOf, nu0R, epsWitness]

end Singleton
end Erdos287
