import Mathlib
import RequestProject.HostileAudit.BalancedSevenSP2SourceAdapter

/-!
# BLOCK20 Δ, Phase A — the literal Balanced7 **source-seal repair**

This module is **append-only**.  It does not modify the historical Balanced7 hostile-audit
bank; it starts from the *actual repository* fixed-certificate definitions

* `Erdos287.SmoothParity.truncMobius` — the literal weight `H_*(n) = ∑_{d ∣ n, d ≤ T} μ(d)`;
* `Erdos287.SmoothParity.FixedCertificateSmoothParityPacket` — the literal `k = 0`, `J = ∅`
  SP-2 smooth packet;
* `Erdos287.SP2Source.SP2FixedCertificateData` / `SP2PacketNormalization` — the literal
  fixed certificate `g_*` metadata (`k = 0`, `J = ∅`, `Ω = 7`, depth `3`, unit sign,
  prime-supported cell);
* `Erdos287.PostBalanced7Pro.omegaBox` — the literal smooth-box weight
  `1_P(p)·V_i(p/Y)·p^{it}`;

and ends at the *actual* packet consumed by the Balanced7 compiler,
`Erdos287.HostileAudit.BalancedSevenSP2SourceSeal`.

## What is proved (§2A–§2C)

* `fixedCertificate_k0_Jempty_reduction` and `fixedCertificate_smoothCut_reduction` —
  the repository certificate weight on the `k = 0`, `J = ∅`, `P⁺(n) ≤ n^{σ_*}` sector is
  literally `∑_{e ∣ n, e ≤ n^{1/2 − ε_*}} μ(e)`;
* `fixedCertificate_sevenBox_eq_neg20` — starting at the repository packet (not at the
  abstract adapter theorem), `H_*(P) = −20` for a seven-prime source `P = p₁⋯p₇`;
* `omegaBox_dictionary`, `omegaBox_carries_no_vonMangoldt_factor`,
  `omegaBox_carries_no_log_factor`, `omegaBox_carries_no_inverse_log_factor` — the weight
  dictionary, with the three hidden-factor hypotheses explicitly **ruled out**, and
  `vonMangoldt_sum_divisors_eq_log` keeping the affine `log r` of `Λ = μ ⋆ log` separate.

## What is **not** proved (§2D)

The single remaining field is the cell identity itself.  It is isolated as

```
FixedCertificateSP2PacketMatchesCompilerPacket sector Hs cut
  := ∀ n ∈ sector, Hs n = truncMobius n (cut n)
```

and `balancedSevenSeal_of_cellIdentity` proves that *this one statement is the only thing
missing*: everything else in `BalancedSevenSP2SourceSeal` is discharged here from the
literal repository objects.  `sourceSeal_residual_not_automatic` shows the residual is a
genuine restriction.  Therefore

```
BALANCED7-SOURCE-SEAL45 : SOURCE_OPEN,
exact residual : FixedCertificateSP2PacketMatchesCompilerPacket.
```
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open ArithmeticFunction

namespace Erdos287
namespace Block20

open Erdos287.SmoothParity
open Erdos287.SP2Source
open Erdos287.HostileAudit
open Erdos287.PostBalanced7Pro

/-! ## §2A  The actual `k = 0`, `J = ∅` reduction -/

/-- The literal fixed-certificate cut `⌊n^{1/2 − ε_*}⌋`. -/
noncomputable def smoothCut (epsStar : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) ^ ((1 : ℝ) / 2 - epsStar)⌋₊

open Classical in
/-- The literal `P⁺(n) ≤ n^{σ_*}` smooth sector below `N`. -/
noncomputable def smoothSector (sigmaStar : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => ∀ p ∈ n.primeFactors, (p : ℝ) ≤ (n : ℝ) ^ sigmaStar)

/-- **`mem_smoothSector`.**  `LEAN_PROVED`. -/
theorem mem_smoothSector {sigmaStar : ℝ} {N n : ℕ} :
    n ∈ smoothSector sigmaStar N ↔
      (n < N ∧ ∀ p ∈ n.primeFactors, (p : ℝ) ≤ (n : ℝ) ^ sigmaStar) := by
  classical
  simp [smoothSector, Finset.mem_filter, Finset.mem_range]

/-- The exact relation `σ_* = ν₀ − 2ε_*` between the smoothness exponent of the sector and
the certificate parameter, transcribed at the repository's own `ν₀`. -/
noncomputable def sigmaStarOf (epsStar : ℝ) : ℝ := (Erdos287.FordData.nu0 : ℝ) - 2 * epsStar

/-- **`fixedCertificate_k0_Jempty_reduction`.**  `CONDITIONAL / LEAN_PROVED`.

The literal `k = 0`, `J = ∅` reduction, stated through the *actual* repository packet: on
the packet's sector the certificate weight is the truncated Möbius sum at the packet's own
cut. -/
theorem fixedCertificate_k0_Jempty_reduction
    {sector : Finset ℕ} {Hs : ℕ → ℤ} {cut : ℕ → ℕ} {f : ℕ → ℝ} {E : ℝ}
    (pkt : FixedCertificateSmoothParityPacket sector Hs cut f E)
    {n : ℕ} (hn : n ∈ sector) :
    Hs n = ∑ e ∈ n.divisors.filter (fun e => e ≤ cut n), moebius e :=
  smoothParity_missing_source pkt.cell_identity hn

/-- **`fixedCertificate_smoothCut_reduction`.**  `CONDITIONAL / LEAN_PROVED`.

The same reduction with the literal cut `⌊n^{1/2 − ε_*}⌋` and the literal
`P⁺(n) ≤ n^{σ_*}` sector, `σ_* = ν₀ − 2ε_*`:

```
H_*(n) = ∑_{e ∣ n, e ≤ n^{1/2 − ε_*}} μ(e).
```
-/
theorem fixedCertificate_smoothCut_reduction
    {N : ℕ} {Hs : ℕ → ℤ} {f : ℕ → ℝ} {E epsStar : ℝ}
    (pkt : FixedCertificateSmoothParityPacket (smoothSector (sigmaStarOf epsStar) N) Hs
      (smoothCut epsStar) f E)
    {n : ℕ} (hn : n ∈ smoothSector (sigmaStarOf epsStar) N) :
    Hs n = ∑ e ∈ n.divisors.filter (fun e => e ≤ ⌊(n : ℝ) ^ ((1 : ℝ) / 2 - epsStar)⌋₊),
      moebius e :=
  fixedCertificate_k0_Jempty_reduction pkt hn

/-! ## §2B  The actual seven-box packet: `H_*(P) = −20` -/

/-- **`fixedCertificate_sevenBox_eq_neg20`.**  `CONDITIONAL / LEAN_PROVED`.

The finite identity of the source seal, proved **from the repository's own fixed-certificate
packet** rather than from the abstract adapter statement: if `P = p₁⋯p₇` is a seven-prime
source in the packet's sector and the packet's cut severs the divisor lattice at depth `3`,
then the literal certificate weight is

```
H_*(P) = 1 − 7 + 21 − 35 = −20.
```
-/
theorem fixedCertificate_sevenBox_eq_neg20
    {sector : Finset ℕ} {Hs : ℕ → ℤ} {cut : ℕ → ℕ} {f : ℕ → ℝ} {E : ℝ}
    (pkt : FixedCertificateSmoothParityPacket sector Hs cut f E)
    {S : Finset ℕ} (hprime : ∀ p ∈ S, p.Prime) (hcard : S.card = 7)
    (hmem : (∏ p ∈ S, p) ∈ sector)
    (hcut : ∀ t ⊆ S, ((∏ p ∈ t, p) ≤ cut (∏ p ∈ S, p) ↔ t.card ≤ 3)) :
    Hs (∏ p ∈ S, p) = -20 := by
  rw [pkt.cell_identity _ hmem]
  exact truncMobius_sevenBox_eq_neg20 hprime hcard hcut

/-- **`fixedCertificate_sevenBox_depth_metadata`.**  `LEAN_PROVED`.

The depth used above is the depth recorded by the literal SP-2 certificate metadata
(`k = 0`, `J = ∅`, `Ω = 7`, `r = 3`). -/
theorem fixedCertificate_sevenBox_depth_metadata {C : SP2FixedCertificateData}
    (hC : SP2PacketNormalization C) : C.k = 0 ∧ C.J = ∅ ∧ C.bigOmega = 7 ∧ C.r = 3 :=
  ⟨hC.k_zero, hC.J_empty, hC.omega_seven, hC.depth_three⟩

/-! ## §2C  The weight dictionary -/

/-- **`omegaBox_dictionary`.**  `LEAN_PROVED`.

The literal repository weight is exactly `1_P(p) · V(p/Y) · p^{it}` — an indicator, a smooth
profile evaluated at `p/Y`, and an archimedean phase, and nothing else. -/
theorem omegaBox_dictionary (V : ℝ → ℝ) (Y t : ℝ) (p : ℕ) :
    omegaBox V Y t p
      = (if p.Prime then (1 : ℂ) else 0) * (V ((p : ℝ) / Y) : ℂ)
          * Complex.exp (t * Real.log p * Complex.I) := by
  unfold omegaBox
  split <;> simp

/-- **`omegaBox_dictionary_negative_twist`.**  `LEAN_PROVED`.

The `p^{-it}` convention is the `t ↦ −t` instance of the same dictionary; no other change
occurs. -/
theorem omegaBox_dictionary_negative_twist (V : ℝ → ℝ) (Y t : ℝ) (p : ℕ) :
    omegaBox V Y (-t) p
      = (if p.Prime then (1 : ℂ) else 0) * (V ((p : ℝ) / Y) : ℂ)
          * Complex.exp (-(t * Real.log p) * Complex.I) := by
  rw [omegaBox_dictionary]
  push_cast
  ring_nf

private theorem log_two_ne_log_three : Real.log ((2 : ℕ) : ℝ) ≠ Real.log ((3 : ℕ) : ℝ) := by
  intro h
  have h2 : (0 : ℝ) < ((2 : ℕ) : ℝ) := by norm_num
  have h3 : (0 : ℝ) < ((3 : ℕ) : ℝ) := by norm_num
  have hx := Real.exp_log h2
  rw [h, Real.exp_log h3] at hx
  norm_num at hx

/-- **`omegaBox_carries_no_vonMangoldt_factor`.**  `LEAN_PROVED`.

There is **no hidden `Λ(p)`**: with the flat profile and no twist, the literal weight is `1`
at every prime, hence it is not a constant multiple of `Λ`. -/
theorem omegaBox_carries_no_vonMangoldt_factor (Y : ℝ) :
    ¬ ∃ c : ℂ, ∀ p : ℕ, p.Prime →
      omegaBox (fun _ => 1) Y 0 p = c * (ArithmeticFunction.vonMangoldt p : ℂ) := by
  rintro ⟨c, hc⟩
  have hflat : ∀ p : ℕ, p.Prime → omegaBox (fun _ => 1) Y 0 p = 1 := by
    intro p hp
    simp [omegaBox, hp]
  have h2 := hc 2 Nat.prime_two
  have h3 := hc 3 Nat.prime_three
  rw [hflat 2 Nat.prime_two, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] at h2
  rw [hflat 3 Nat.prime_three, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three] at h3
  have hne : c ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    exact one_ne_zero h2
  have heq : c * ((Real.log ((2 : ℕ) : ℝ) : ℝ) : ℂ) = c * ((Real.log ((3 : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [← h2, ← h3]
  exact log_two_ne_log_three (Complex.ofReal_inj.mp (mul_left_cancel₀ hne heq))

/-- **`omegaBox_carries_no_log_factor`.**  `LEAN_PROVED`.

There is **no hidden `log p`** factor either. -/
theorem omegaBox_carries_no_log_factor (Y : ℝ) :
    ¬ ∃ c : ℂ, ∀ p : ℕ, p.Prime →
      omegaBox (fun _ => 1) Y 0 p = c * (Real.log p : ℂ) := by
  rintro ⟨c, hc⟩
  refine omegaBox_carries_no_vonMangoldt_factor Y ⟨c, ?_⟩
  intro p hp
  rw [hc p hp, ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- **`omegaBox_carries_no_inverse_log_factor`.**  `LEAN_PROVED`.

And there is **no hidden `1/log p`** factor. -/
theorem omegaBox_carries_no_inverse_log_factor (Y : ℝ) :
    ¬ ∃ c : ℂ, ∀ p : ℕ, p.Prime →
      omegaBox (fun _ => 1) Y 0 p = c / (Real.log p : ℂ) := by
  rintro ⟨c, hc⟩
  have hflat : ∀ p : ℕ, p.Prime → omegaBox (fun _ => 1) Y 0 p = 1 := by
    intro p hp
    simp [omegaBox, hp]
  have h2 := hc 2 Nat.prime_two
  have h3 := hc 3 Nat.prime_three
  rw [hflat 2 Nat.prime_two] at h2
  rw [hflat 3 Nat.prime_three] at h3
  have hl2 : ((Real.log ((2 : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 := by
    intro h
    rw [h, div_zero] at h2
    exact one_ne_zero h2
  have hl3 : ((Real.log ((3 : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 := by
    intro h
    rw [h, div_zero] at h3
    exact one_ne_zero h3
  have e2 : c = ((Real.log ((2 : ℕ) : ℝ) : ℝ) : ℂ) := by
    have := (div_eq_iff hl2).mp h2.symm
    simpa using this
  have e3 : c = ((Real.log ((3 : ℕ) : ℝ) : ℝ) : ℂ) := by
    have := (div_eq_iff hl3).mp h3.symm
    simpa using this
  exact log_two_ne_log_three (Complex.ofReal_inj.mp (e2 ▸ e3))

/-- **`vonMangoldt_sum_divisors_eq_log`.**  `LEAN_PROVED`.

The affine `log r` of `Λ = μ ⋆ log` is kept **separate** from the source weights: it enters
only through this convolution identity `∑_{d ∣ n} Λ(d) = log n`, which involves no box
weight at all. -/
theorem vonMangoldt_sum_divisors_eq_log (n : ℕ) :
    ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d = Real.log n := by
  have h := ArithmeticFunction.vonMangoldt_mul_zeta
  have h2 := congrArg (fun (F : ArithmeticFunction ℝ) => F n) h
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.log_apply] at h2
  exact h2

/-! ## §2D  The seal, and the single exact residual -/

/-- **The exact source-seal residual.**

`FixedCertificateSP2PacketMatchesCompilerPacket sector Hs cut` is the literal statement that
the repository's fixed-certificate weight *is* the packet consumed by the Balanced7 compiler
on the sector.  It is precisely the `cell_identity` field of
`FixedCertificateSmoothParityPacket`, i.e. the `k = 0`, `J = ∅` cell of the Ford
factorisation, which this repository does not derive. -/
def FixedCertificateSP2PacketMatchesCompilerPacket
    (sector : Finset ℕ) (Hs : ℕ → ℤ) (cut : ℕ → ℕ) : Prop :=
  ∀ n ∈ sector, Hs n = truncMobius n (cut n)

/-- **`balancedSevenSeal_of_cellIdentity`.**  `CONDITIONAL / LEAN_PROVED`.

**The source-seal repair.**  Every field of the compiler's packet
`BalancedSevenSP2SourceSeal` other than the cell identity is discharged here from the
literal repository objects:

* the metadata field from `SP2PacketNormalization` (`k = 0`, `J = ∅`, `Ω = 7`, `r = 3`);
* the phase field from the literal archimedean twist `p^{it}` (unimodularity is *proved*,
  `Complex.norm_exp_ofReal_mul_I`);
* the source-form field from the literal repository weight `omegaBox` (proved equal to the
  seven-box law by `boxWeight_eq_omegaBox`).

Hence the seal is available as soon as the single residual
`FixedCertificateSP2PacketMatchesCompilerPacket` is. -/
theorem balancedSevenSeal_of_cellIdentity
    {C : SP2FixedCertificateData} {sector : Finset ℕ} {Hs : ℕ → ℤ} {cut : ℕ → ℕ}
    {V : Fin 7 → ℝ → ℝ} {Y t : ℝ}
    (hC : SP2PacketNormalization C)
    (hV : ∀ (i : Fin 7) (x : ℝ), 0 ≤ V i x ∧ V i x ≤ 1)
    (hcell : FixedCertificateSP2PacketMatchesCompilerPacket sector Hs cut) :
    BalancedSevenSP2SourceSeal C sector Hs cut V
      (fun _ p => Complex.exp (t * Real.log p * Complex.I)) Y
      (fun i p => omegaBox (V i) Y t p) where
  packet := hC
  cell_identity := hcell
  profile_bounds := hV
  phase_unimodular := by
    intro _ p
    rw [show ((t : ℂ) * (Real.log p : ℂ) * Complex.I)
        = ((t * Real.log p : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  source_form := by
    intro i p
    exact (boxWeight_eq_omegaBox (V i) Y t p).symm

/-- **`sourceSeal_residual_is_exactly_the_cell_identity`.**  `LEAN_PROVED`.

Conversely, any inhabitant of the compiler packet supplies the residual: so the residual is
neither weaker nor stronger than what is missing. -/
theorem sourceSeal_residual_is_exactly_the_cell_identity
    {C : SP2FixedCertificateData} {sector : Finset ℕ} {Hs : ℕ → ℤ} {cut : ℕ → ℕ}
    {V : Fin 7 → ℝ → ℝ} {phase : Fin 7 → ℕ → ℂ} {Y : ℝ} {omegaSrc : Fin 7 → ℕ → ℂ}
    (h : BalancedSevenSP2SourceSeal C sector Hs cut V phase Y omegaSrc) :
    FixedCertificateSP2PacketMatchesCompilerPacket sector Hs cut :=
  h.cell_identity

/-- **`sourceSeal_residual_not_automatic`.**  `LEAN_PROVED`.

The residual is a genuine restriction, refuted by explicit data (`sector = {2}`,
`cut ≡ 5`, `H_* ≡ 1`, whereas `∑_{d ∣ 2, d ≤ 5} μ(d) = 0`).  Consequently

```
BALANCED7-SOURCE-SEAL45 : SOURCE_OPEN
```

with this one exact residual. -/
theorem sourceSeal_residual_not_automatic :
    ∃ (sector : Finset ℕ) (Hs : ℕ → ℤ) (cut : ℕ → ℕ),
      ¬ FixedCertificateSP2PacketMatchesCompilerPacket sector Hs cut := by
  refine ⟨{2}, fun _ => 1, fun _ => 5, ?_⟩
  intro h
  have h2 := h 2 (Finset.mem_singleton_self 2)
  have hd : (2 : ℕ).divisors.filter (fun d => d ≤ 5) = {1, 2} := by decide
  rw [truncMobius, hd] at h2
  rw [show ({1, 2} : Finset ℕ) = insert 1 {2} from rfl, Finset.sum_insert (by decide),
    Finset.sum_singleton] at h2
  norm_num [moebius_apply_prime Nat.prime_two] at h2

/-- **`sourceSeal_status_is_open`.**  `LEAN_PROVED`.

The honest two-sided statement of Phase A: the seal follows from the residual, and the
residual is not available. -/
theorem sourceSeal_status_is_open :
    (∀ (C : SP2FixedCertificateData) (sector : Finset ℕ) (Hs : ℕ → ℤ) (cut : ℕ → ℕ)
        (V : Fin 7 → ℝ → ℝ) (Y t : ℝ), SP2PacketNormalization C →
        (∀ (i : Fin 7) (x : ℝ), 0 ≤ V i x ∧ V i x ≤ 1) →
        FixedCertificateSP2PacketMatchesCompilerPacket sector Hs cut →
        BalancedSevenSP2SourceSeal C sector Hs cut V
          (fun _ p => Complex.exp (t * Real.log p * Complex.I)) Y
          (fun i p => omegaBox (V i) Y t p)) ∧
      (∃ (sector : Finset ℕ) (Hs : ℕ → ℤ) (cut : ℕ → ℕ),
        ¬ FixedCertificateSP2PacketMatchesCompilerPacket sector Hs cut) :=
  ⟨fun _ _ _ _ _ _ _ hC hV hcell => balancedSevenSeal_of_cellIdentity hC hV hcell,
    sourceSeal_residual_not_automatic⟩

end Block20
end Erdos287
