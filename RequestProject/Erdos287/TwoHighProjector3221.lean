import Mathlib
import RequestProject.Erdos287.HighConductorCharacterGram3221
import RequestProject.Erdos287.FiveBoxCharacterFactorization3221

/-!
# V21, Phase 1 — the two-high-projector algebra and the pre-projector variance

`3221-TWO-HIGHPROJECTOR-FIVEBOX-SIEVE45 : ALGEBRAIC LAYER / LEAN_PROVED_FINITE`

This file is **append-only V21 infrastructure**.  Nothing from V20 is deleted, rewritten or
weakened; the V20 objects (`shortMGram`, `autocorr`, `charSrc`,
`charSource_variance_eq_gram`, `highSet`, `highCoeff`, the five-box factorisation, the
conductor router, the HHH Gram object) are *imported and reused*.

## What is proved here (all finite identities, no analytic input)

* **§1.  Indicators.**  For an ambient finite character set and a `Bad` subset,
  `highIndicator_eq_one_sub_badIndicator` and the exact two-variable identity
  `twoHighProjector_pointwise`:
  `1_High(χ)·1_High(ψ) = 1 − 1_Bad(χ) − 1_Bad(ψ) + 1_Bad(χ)·1_Bad(ψ)`.
* **§2.  No omitted cell.**  `high_bad_disjoint`, `high_union_bad`,
  `high_card_add_bad_card`, `twoProjector_no_double_counting`.
* **§3.  The exact four-cell decomposition.**
  `highHighSum_eq_AA_sub_BA_sub_AB_add_BB` : `HH = AA − BA − AB + BB`,
  with `AA`, `BA`, `AB`, `BB` kept as **four separate finite source expressions**.
  No quotient conductor and no Burgess conductor-cell inclusion–exclusion is used.
* **§4.  The pre-projector variance, reconstructed from the V20 source.**
  `preProjectorVariance` is the literal `∑_m Φ(m) |∑_χ F(χ) χ(−2s) χ(m)|²` in the
  repository's conjugation convention (`conj(χ(a_m)) = χ(−2s)χ(m)`, V20
  `inverseSample_character_identity`), and
  * `preProjectorVariance_eq_AA` identifies it with the full-full cell `AA`;
  * `preProjectorVariance_eq_xiForm` proves the **finite equivalence** with the V20
    `ξ = χ ψ⁻¹` representation `∑_ξ ξ(t) G_{q,M}(ξ) A_q(ξ)` — it is *proved*, not assumed;
  * `preProjectorVariance_highSet_support` shows that for the literal high-conductor
    coefficient `highCoeff` the ambient sum is already supported on `highSet q Dcut`.
* **§5.  Ambient firewall.**  `TwoProjectorAmbientCompat3221` records that every remaining
  character restriction (primitivity, parity, unit sector, exceptional convention,
  quotient-conductor conditions) is *inside* `Bad` or inside the ambient set used by
  orthogonality.  It is **not inhabited** for the physical Balanced7 character data.
* **§6.  The `q`-summed channels** `AAChannel`, `BAChannel`, `ABChannel`, `BBChannel` and
  the top-level decomposition `VhiHigh_eq_channels`.

Erdős #287 remains **OPEN**; Balanced7 remains **OPEN**.  Nothing in this file is an
analytic estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

open Finset
open scoped BigOperators

namespace Erdos287
namespace V21TwoProj

open Erdos287.CharGram3221 Erdos287.V20Gram

/-! ## §1. The ambient set, the bad set and the two indicators -/

section Indicators

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The ambient finite character set: **one** set, used both by orthogonality and by the
projectors. -/
def ambientSet (α : Type*) [Fintype α] : Finset α := Finset.univ

/-- `High = Ambient \ Bad`. -/
def highSetOf (Bad : Finset α) : Finset α := Finset.univ \ Bad

/-- The bad indicator in `ℂ`. -/
noncomputable def badInd (Bad : Finset α) (a : α) : ℂ := if a ∈ Bad then 1 else 0

/-- The high indicator in `ℂ`. -/
noncomputable def highInd (Bad : Finset α) (a : α) : ℂ := if a ∈ highSetOf Bad then 1 else 0

theorem mem_highSetOf_iff (Bad : Finset α) (a : α) : a ∈ highSetOf Bad ↔ a ∉ Bad := by
  simp [highSetOf]

omit [DecidableEq α] in
theorem mem_ambientSet (a : α) : a ∈ ambientSet α := Finset.mem_univ a

/-- **`highIndicator_eq_one_sub_badIndicator`.**  `LEAN_PROVED`.

Pointwise, in the coefficient ring `ℂ`: `1_High = 1 − 1_Bad`. -/
theorem highIndicator_eq_one_sub_badIndicator (Bad : Finset α) (a : α) :
    highInd Bad a = 1 - badInd Bad a := by
  unfold highInd badInd
  by_cases h : a ∈ Bad
  · rw [if_pos h, if_neg (by simpa [mem_highSetOf_iff] using h)]
    ring
  · rw [if_neg h, if_pos ((mem_highSetOf_iff Bad a).mpr h)]
    ring

/-- **`twoHighProjector_pointwise`.**  `LEAN_PROVED`.

The exact two-variable projector identity

`1_High(χ)·1_High(ψ) = 1 − 1_Bad(χ) − 1_Bad(ψ) + 1_Bad(χ)·1_Bad(ψ)`. -/
theorem twoHighProjector_pointwise (Bad : Finset α) (a b : α) :
    highInd Bad a * highInd Bad b
      = 1 - badInd Bad a - badInd Bad b + badInd Bad a * badInd Bad b := by
  rw [highIndicator_eq_one_sub_badIndicator, highIndicator_eq_one_sub_badIndicator]
  ring

/-! ## §2. No omitted cell, no overlap, no double counting -/

theorem high_bad_disjoint (Bad : Finset α) : Disjoint (highSetOf Bad) Bad := by
  rw [Finset.disjoint_left]
  intro a ha
  exact (mem_highSetOf_iff Bad a).mp ha

theorem high_union_bad (Bad : Finset α) : highSetOf Bad ∪ Bad = Finset.univ := by
  ext a
  by_cases h : a ∈ Bad <;> simp [highSetOf, h]

theorem high_card_add_bad_card (Bad : Finset α) :
    (highSetOf Bad).card + Bad.card = Fintype.card α := by
  rw [← Finset.card_union_of_disjoint (high_bad_disjoint Bad), high_union_bad,
    Finset.card_univ]

/-- **`twoProjector_no_double_counting`.**  `LEAN_PROVED`.

Every ambient character lies in exactly one of `High`, `Bad`. -/
theorem twoProjector_no_double_counting (Bad : Finset α) (a : α) :
    (a ∈ highSetOf Bad ∧ a ∉ Bad) ∨ (a ∈ Bad ∧ a ∉ highSetOf Bad) := by
  by_cases h : a ∈ Bad
  · exact Or.inr ⟨h, by simpa [mem_highSetOf_iff] using h⟩
  · exact Or.inl ⟨(mem_highSetOf_iff Bad a).mpr h, h⟩

/-! ## §3. The exact four-cell decomposition -/

variable (K : α → α → ℂ)

/-- `AA` — the full–full cell (both characters range over the whole ambient set). -/
noncomputable def AA3221 (K : α → α → ℂ) : ℂ := ∑ a : α, ∑ b : α, K a b

/-- `BA` — first character bad, second character full. -/
noncomputable def BA3221 (Bad : Finset α) (K : α → α → ℂ) : ℂ := ∑ a ∈ Bad, ∑ b : α, K a b

/-- `AB` — first character full, second character bad. -/
noncomputable def AB3221 (Bad : Finset α) (K : α → α → ℂ) : ℂ := ∑ a : α, ∑ b ∈ Bad, K a b

/-- `BB` — both characters bad. -/
noncomputable def BB3221 (Bad : Finset α) (K : α → α → ℂ) : ℂ := ∑ a ∈ Bad, ∑ b ∈ Bad, K a b

/-- `HH` — both characters high. -/
noncomputable def HH3221 (Bad : Finset α) (K : α → α → ℂ) : ℂ :=
  ∑ a ∈ highSetOf Bad, ∑ b ∈ highSetOf Bad, K a b

/-- A finite sum over a subset is the indicator-weighted ambient sum. -/
theorem sum_eq_indicator_sum (S : Finset α) (f : α → ℂ) :
    ∑ a ∈ S, f a = ∑ a : α, (if a ∈ S then (1 : ℂ) else 0) * f a := by
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- The high–high cell written through the two indicators. -/
theorem HH3221_eq_indicator_sum (Bad : Finset α) (K : α → α → ℂ) :
    HH3221 Bad K = ∑ a : α, ∑ b : α, highInd Bad a * highInd Bad b * K a b := by
  rw [HH3221, sum_eq_indicator_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_eq_indicator_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [highInd, highInd]
  ring

/-- **`highHighSum_eq_AA_sub_BA_sub_AB_add_BB`.**  `LEAN_PROVED_FINITE`.

The exact finite sum decomposition `HIGH-HIGH = AA − BA − AB + BB`.  No quotient
conductor, no Burgess conductor-cell inclusion–exclusion, no omitted cell. -/
theorem highHighSum_eq_AA_sub_BA_sub_AB_add_BB (Bad : Finset α) (K : α → α → ℂ) :
    HH3221 Bad K = AA3221 K - BA3221 Bad K - AB3221 Bad K + BB3221 Bad K := by
  have hb : ∀ a : α, ∑ b ∈ highSetOf Bad, K a b
      = (∑ b : α, K a b) - ∑ b ∈ Bad, K a b := by
    intro a
    rw [highSetOf, Finset.sum_sdiff_eq_sub (Finset.subset_univ Bad)]
  rw [HH3221]
  simp only [hb]
  rw [Finset.sum_sub_distrib, highSetOf,
    Finset.sum_sdiff_eq_sub (Finset.subset_univ Bad),
    Finset.sum_sdiff_eq_sub (Finset.subset_univ Bad)]
  rw [AA3221, BA3221, AB3221, BB3221]
  ring

end Indicators

/-! ## §4. The pre-projector variance, reconstructed from the V20 source -/

section Variance

variable {q : ℕ}

/-- The **exact source kernel** of the character Gram:

`K(χ, ψ) = F(χ) conj(F(ψ)) ∑_{m ∈ M, (m,q)=1} Φ(m) χ(t) χ(m) conj(ψ(t) ψ(m))`,

with `t = −2s` the sign-carrying unit and `F` the (high-conductor) coefficient family.  In
the physical packet `F = ĉ_q` restricted to the high sector and `t = −2s`; the conjugation
convention is the V20 one (`inverseSample_character_identity`). -/
noncomputable def gramKernel (q : ℕ) (F : DirichletCharacter ℂ q → ℂ) (t : ZMod q)
    (Mset : Finset ℕ) (Phi : ℕ → ℂ) (chi psi : DirichletCharacter ℂ q) : ℂ :=
  F chi * (starRingEnd ℂ) (F psi) *
    ∑ m ∈ unitBox q Mset, Phi m *
      (chi t * chi ((m : ℕ) : ZMod q) * (starRingEnd ℂ) (psi t * psi ((m : ℕ) : ZMod q)))

/-- The **pre-projector variance** at a single modulus:

`∑_{m ∈ M, (m,q)=1} Φ(m) |∑_χ F(χ) χ(t) χ(m)|²`,

i.e. `φ(q)²` times the V20 quantity `∑_m Φ(m) |C_q^{>D}(a_m)|²` (the normalisation
`1/φ(q)²` is carried by the modulus weight, exactly as in the source). -/
noncomputable def preProjectorVariance (q : ℕ) (F : DirichletCharacter ℂ q → ℂ) (t : ZMod q)
    (Mset : Finset ℕ) (Phi : ℕ → ℂ) : ℂ :=
  ∑ m ∈ unitBox q Mset, Phi m *
    ((∑ chi : DirichletCharacter ℂ q, F chi * chi t * chi ((m : ℕ) : ZMod q)) *
      (starRingEnd ℂ)
        (∑ psi : DirichletCharacter ℂ q, F psi * psi t * psi ((m : ℕ) : ZMod q)))

/-- **`preProjectorVariance_eq_AA`.**  `LEAN_PROVED_FINITE`.

The pre-projector variance is exactly the full–full cell of the source kernel. -/
theorem preProjectorVariance_eq_AA (q : ℕ) (F : DirichletCharacter ℂ q → ℂ) (t : ZMod q)
    (Mset : Finset ℕ) (Phi : ℕ → ℂ) :
    preProjectorVariance q F t Mset Phi = AA3221 (gramKernel q F t Mset Phi) := by
  classical
  rw [preProjectorVariance, AA3221]
  have hexp : ∀ m : ℕ,
      Phi m * ((∑ chi : DirichletCharacter ℂ q, F chi * chi t * chi ((m : ℕ) : ZMod q)) *
        (starRingEnd ℂ)
          (∑ psi : DirichletCharacter ℂ q, F psi * psi t * psi ((m : ℕ) : ZMod q)))
        = ∑ chi : DirichletCharacter ℂ q, ∑ psi : DirichletCharacter ℂ q,
            F chi * (starRingEnd ℂ) (F psi) *
              (Phi m * (chi t * chi ((m : ℕ) : ZMod q) *
                (starRingEnd ℂ) (psi t * psi ((m : ℕ) : ZMod q)))) := by
    intro m
    rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun chi _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun psi _ => ?_
    simp only [map_mul]
    ring
  simp only [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun chi _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun psi _ => ?_
  rw [gramKernel, Finset.mul_sum]

/-- **`preProjectorVariance_eq_xiForm`.**  `LEAN_PROVED_FINITE`.

**The finite equivalence with the V20 `ξ = χ ψ⁻¹` representation is proved, not assumed:**

`∑_m Φ(m) |∑_χ F(χ) χ(t) χ(m)|² = ∑_ξ ξ(t) G_{q,M}(ξ) A_q(ξ)`,

where `G_{q,M}` is the V20 `shortMGram` and `A_q` the V20 `autocorr`. -/
theorem preProjectorVariance_eq_xiForm (q : ℕ) [NeZero q] (F : DirichletCharacter ℂ q → ℂ)
    {t : ZMod q} (ht : IsUnit t) (Mset : Finset ℕ) (Phi : ℕ → ℂ) :
    preProjectorVariance q F t Mset Phi
      = ∑ xi : DirichletCharacter ℂ q, xi t * shortMGram q Mset Phi xi * autocorr q F xi := by
  have htot : (q.totient : ℂ) ≠ 0 := by
    have : 0 < q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    exact_mod_cast this.ne'
  have hct : (starRingEnd ℂ) ((q.totient : ℂ)⁻¹) = (q.totient : ℂ)⁻¹ := by
    rw [map_inv₀]; norm_num
  have key := charSource_variance_eq_gram q F ht Mset Phi
  have hleft : ∑ m ∈ unitBox q Mset, Phi m *
      (charSrc q F t m * (starRingEnd ℂ) (charSrc q F t m))
      = (q.totient : ℂ)⁻¹ ^ 2 * preProjectorVariance q F t Mset Phi := by
    rw [preProjectorVariance, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [charSrc, map_mul, hct]
    ring
  rw [hleft] at key
  have hne : ((q.totient : ℂ)⁻¹) ^ 2 ≠ 0 := pow_ne_zero _ (inv_ne_zero htot)
  exact mul_left_cancel₀ hne key

/-- **`preProjectorVariance_highSet_support`.**  `LEAN_PROVED_FINITE`.

For the literal high-conductor coefficient family the ambient sum over *all* characters is
already the sum over `highSet q Dcut`: the projector does not silently enlarge the ambient
set. -/
theorem preProjectorVariance_highSet_support (q Dcut : ℕ) (Wbox : Finset ℤ) (c : ℤ → ℂ)
    (t : ZMod q) (m : ℕ) :
    (∑ chi : DirichletCharacter ℂ q,
        highCoeff q Dcut Wbox c chi * chi t * chi ((m : ℕ) : ZMod q))
      = ∑ chi ∈ highSet q Dcut, cHat q Wbox c chi * chi t * chi ((m : ℕ) : ZMod q) := by
  classical
  have h1 : (∑ chi ∈ highSet q Dcut,
        highCoeff q Dcut Wbox c chi * chi t * chi ((m : ℕ) : ZMod q))
      = ∑ chi : DirichletCharacter ℂ q,
          highCoeff q Dcut Wbox c chi * chi t * chi ((m : ℕ) : ZMod q) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro chi _ hchi
    have h : ¬ Dcut < chi.conductor := fun hlt =>
      hchi ((mem_highSet_iff_lt_conductor chi).mpr hlt)
    rw [Erdos287.V20FiveBox.highCoeff_of_not_high q Dcut Wbox c chi h]
    ring
  rw [← h1]
  refine Finset.sum_congr rfl fun chi hchi => ?_
  rw [Erdos287.V20FiveBox.highCoeff_fiveBox q Dcut Wbox c chi
    ((mem_highSet_iff_lt_conductor chi).mp hchi)]

end Variance

/-! ## §5. The ambient-set firewall -/

/-- **`TwoProjectorAmbientCompat3221`** — `SOURCE FIREWALL / UNINHABITED for the physical
character data`.

The four-cell identity `HH = AA − BA − AB + BB` is valid **only** if `High` and `Bad`
partition the *same* ambient set that orthogonality uses.  This structure states exactly
that, together with the requirement that every remaining character restriction — the set
`Restricted`, which collects primitivity, parity, unit-sector, exceptional-character and
quotient-conductor conventions — is already contained in `Bad`.

No inhabitant is produced anywhere in this repository for the physical Balanced7 character
data; `ambientCompat_of_source` is available only when the source definitions literally
supply the two inclusions. -/
structure TwoProjectorAmbientCompat3221 {α : Type*} [Fintype α] [DecidableEq α]
    (Ambient Bad Restricted : Finset α) : Prop where
  /-- The ambient set used by the projectors is the ambient set used by orthogonality. -/
  ambient_eq_univ : Ambient = Finset.univ
  /-- The bad set is inside the ambient set. -/
  bad_subset : Bad ⊆ Ambient
  /-- Every remaining character restriction is charged to `Bad`; nothing is left outside. -/
  restricted_subset_bad : Restricted ⊆ Bad

/-- Given the two literal inclusions, the ambient compatibility certificate exists.  This
is the *only* way an instance may be produced: from source definitions, never from an
analytic estimate. -/
theorem ambientCompat_of_source {α : Type*} [Fintype α] [DecidableEq α]
    {Bad Restricted : Finset α} (h : Restricted ⊆ Bad) :
    TwoProjectorAmbientCompat3221 Finset.univ Bad Restricted :=
  ⟨rfl, Finset.subset_univ Bad, h⟩

/-- **`ambientCompat_not_automatic`.**  `LEAN_PROVED`.

The ambient firewall is a genuine restriction: a restriction set that is *not* charged to
`Bad` refutes it. -/
theorem ambientCompat_not_automatic :
    ∃ (Ambient Bad Restricted : Finset (Fin 2)),
      ¬ TwoProjectorAmbientCompat3221 Ambient Bad Restricted := by
  refine ⟨Finset.univ, ∅, Finset.univ, ?_⟩
  intro h
  have := h.restricted_subset_bad (Finset.mem_univ (0 : Fin 2))
  simp at this

/-- Under the ambient firewall the four-cell decomposition is exactly the decomposition of
the sum over the orthogonality ambient set. -/
theorem highHigh_decomposition_under_ambientCompat {α : Type*} [Fintype α] [DecidableEq α]
    {Ambient Bad Restricted : Finset α}
    (hcompat : TwoProjectorAmbientCompat3221 Ambient Bad Restricted) (K : α → α → ℂ) :
    HH3221 Bad K
      = (∑ a ∈ Ambient, ∑ b ∈ Ambient, K a b) - BA3221 Bad K - AB3221 Bad K
        + BB3221 Bad K := by
  rw [highHighSum_eq_AA_sub_BA_sub_AB_add_BB, AA3221, hcompat.ambient_eq_univ]

/-! ## §6. The `q`-summed channels -/

section Channels

open scoped Classical

variable (Qbox : Finset ℕ) (wt : ℕ → ℂ) (Mset : Finset ℕ) (Phi : ℕ → ℂ) (s : ℤ)
  (F : (q : ℕ) → DirichletCharacter ℂ q → ℂ)
  (Bad : (q : ℕ) → Finset (DirichletCharacter ℂ q))

/-- The physical sign-carrying unit `t = −2s` at modulus `q`. -/
def signUnit (q : ℕ) (s : ℤ) : ZMod q := ((-2 * s : ℤ) : ZMod q)

/-- The high–high (two-projector) high-conductor variance:

`V_hi^{HH} = ∑_q wt(q) ∑_{χ,ψ ∈ High_q} K_q(χ,ψ)`,

with `wt(q) = μ²(q)/φ(q)²` in the physical packet. -/
noncomputable def VhiHigh : ℂ :=
  ∑ q ∈ Qbox, wt q * HH3221 (Bad q) (gramKernel q (F q) (signUnit q s) Mset Phi)

/-- The `AA` channel (`AA3221`): both characters full. -/
noncomputable def AAChannel : ℂ :=
  ∑ q ∈ Qbox, wt q * AA3221 (gramKernel q (F q) (signUnit q s) Mset Phi)

/-- The `BA` channel (`BA3221`): first character bad, second full. -/
noncomputable def BAChannel : ℂ :=
  ∑ q ∈ Qbox, wt q * BA3221 (Bad q) (gramKernel q (F q) (signUnit q s) Mset Phi)

/-- The `AB` channel (`AB3221`): first character full, second bad. -/
noncomputable def ABChannel : ℂ :=
  ∑ q ∈ Qbox, wt q * AB3221 (Bad q) (gramKernel q (F q) (signUnit q s) Mset Phi)

/-- The `BB` channel (`BB3221`): both characters bad. -/
noncomputable def BBChannel : ℂ :=
  ∑ q ∈ Qbox, wt q * BB3221 (Bad q) (gramKernel q (F q) (signUnit q s) Mset Phi)

/-- **`VhiHigh_eq_channels`.**  `LEAN_PROVED_FINITE`.

The top-level two-projector reassembly, with the four channels kept **separate**:

`V_hi^{HH} = AA − BA − AB + BB`. -/
theorem VhiHigh_eq_channels :
    VhiHigh Qbox wt Mset Phi s F Bad
      = AAChannel Qbox wt Mset Phi s F - BAChannel Qbox wt Mset Phi s F Bad
        - ABChannel Qbox wt Mset Phi s F Bad + BBChannel Qbox wt Mset Phi s F Bad := by
  rw [VhiHigh, AAChannel, BAChannel, ABChannel, BBChannel]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [highHighSum_eq_AA_sub_BA_sub_AB_add_BB]
  ring

/-- The `AA` channel is the `q`-weighted pre-projector variance: the two-projector route
starts from the *literal* source object, not from a remembered formula. -/
theorem AAChannel_eq_weighted_preProjectorVariance :
    AAChannel Qbox wt Mset Phi s F
      = ∑ q ∈ Qbox, wt q * preProjectorVariance q (F q) (signUnit q s) Mset Phi := by
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [preProjectorVariance_eq_AA]

end Channels

end V21TwoProj
end Erdos287
