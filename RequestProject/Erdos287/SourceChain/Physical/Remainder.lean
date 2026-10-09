import RequestProject.Erdos287.SourceChain.Physical.PairIdentity
import RequestProject.Erdos287.CurrentTail.ExactSource

/-!
# Erdős #287 — physical source: the literal remainder `R_Σ^P`, pair indexing and adapter

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**  `sources/physical_spec.md` §12, §21.

* `RSigmaP S = ∑_{j<ℓ} ∑_{ξ ∈ Ξ_{jℓ}} Γ_ξ ∑_{d, (d,f_ξ)=1} ℓ_X(d) E_j(f_ξ d, b_{ξ,d})` — the
  literal physical prime remainder (prime counts, scalar coefficient `ℓ_X` a parameter).
* `RSigmaP_eq_packetIndexed` — **exact pair-indexing identity**: the same sum written over the
  single labelled packet set `Ξ = ⋃_{j<ℓ} Ξ_{jℓ}` with designated coordinate `j = j(ξ)`.
* `pairTotal_eq_main_add_RSigmaP` — `∑_{j<ℓ} PairSum = Main + R_Σ^P` (exact).
* `RSigmaP_eq_rel_add_base` — `R_Σ^P = R_rel + R_base` on the same packet and scalar support
  (§21, from the already-proved `v99_relative_centering`).
* `packetTensor` / `RSigmaP_eq_sum_packetTensor` — **proved adapter** to the existing generic
  `Erdos287.CurrentTail.TensorSource`: one single-packet tensor source per labelled packet
  (with `ell = 1`, `α_0 = 1_{prime} 1_{𝒥_{j(ξ)}}`, scalar support restricted to `(d,f_ξ)=1`),
  and `R_Σ^P = ∑_{ξ ∈ Ξ} (packetTensor ξ).RSigmaP`.  The generic tensor's `j`-sum is the
  trivial one-element sum, so no unrestricted `j`-sum is introduced.
* `pcount_eq_progSum`, `eerr_eq_progErr` — the prime count is the generic `progSum` of the
  prime indicator of the window.

A single global `TensorSource` cannot carry `R_Σ^P`: its scalar support must be coprime to
*every* `f_ξ` and its sequences `α_j` cannot depend on `ξ`.  This is why the adapter is
packet-wise.
-/

open scoped BigOperators
open Finset

namespace Erdos287.Physical

namespace PhysData

variable (P : PhysData)

/-- Designated pairs `j < ℓ`. -/
def pairs : Finset (Fin P.k × Fin P.k) := (univ ×ˢ univ).filter (fun p => p.1 < p.2)

open Classical in
/-- **`Ξ`**: all labelled admissible packets, `Ξ = ⋃_{j<ℓ} Ξ_{jℓ}`. -/
noncomputable def XiAll : Finset (Packet P.k) := (P.pairs).biUnion (fun p => P.Xi p.1 p.2)

/-- **The literal physical prime remainder `R_Σ^P`** (§12). -/
noncomputable def RSigmaP (S : ScalarSieve) : ℝ := ∑ p ∈ P.pairs, P.PairRem S p.1 p.2

/-- Total main term `∑_{j<ℓ} PairMain`. -/
noncomputable def MainTotal (S : ScalarSieve) : ℝ := ∑ p ∈ P.pairs, P.PairMain S p.1 p.2

/-- Total literal pair moment `∑_{j<ℓ} PairSum`. -/
noncomputable def PairTotal (S : ScalarSieve) : ℝ := ∑ p ∈ P.pairs, P.PairSum S p.1 p.2

open Classical in
/-- Relative part `∑_ξ Γ_ξ ∑_d ℓ_X(d) [P_j(f_ξ d, b_{ξ,d}) - P_j(f_ξ, c_ξ)/φ(d)]`. -/
noncomputable def Rrel (S : ScalarSieve) : ℝ :=
  ∑ ξ ∈ P.XiAll, P.Gamma ξ * ∑ e ∈ S.supp.filter (fun e => Nat.Coprime (P.f ξ) e),
    S.coeff e * ((P.Pcount ξ.j (P.f ξ * e) (P.bRes ξ e) : ℝ) -
      (P.Pcount ξ.j (P.f ξ) (P.cRes ξ) : ℝ) / (Nat.totient e : ℝ))

open Classical in
/-- Base part `∑_ξ Γ_ξ ∑_d ℓ_X(d) E_j(f_ξ, c_ξ)/φ(d)` (paid by ordinary BV; not zero). -/
noncomputable def Rbase (S : ScalarSieve) : ℝ :=
  ∑ ξ ∈ P.XiAll, P.Gamma ξ * ∑ e ∈ S.supp.filter (fun e => Nat.Coprime (P.f ξ) e),
    S.coeff e * (P.Eerr ξ.j (P.f ξ) (P.cRes ξ) / (Nat.totient e : ℝ))

variable {P}

theorem mem_Xi {j l : Fin P.k} {ξ : Packet P.k} (h : ξ ∈ P.Xi j l) :
    ξ.j = j ∧ ξ.l = l ∧ P.Admissible ξ := by
  classical
  unfold Xi at h
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 h
  exact ⟨rfl, rfl, (Finset.mem_filter.1 hx).2⟩

theorem mem_XiAll {ξ : Packet P.k} (h : ξ ∈ P.XiAll) : P.Admissible ξ := by
  classical
  unfold XiAll at h
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.1 h
  exact (mem_Xi hp).2.2

/-- **Exact pair-indexing identity**: `R_Σ^P` is the sum over the labelled packet set `Ξ`
with designated coordinate `j(ξ)` — no extra unrestricted `j`-sum. -/
theorem RSigmaP_eq_packetIndexed (S : ScalarSieve) :
    P.RSigmaP S = ∑ ξ ∈ P.XiAll, P.Gamma ξ *
      ∑ e ∈ S.supp.filter (fun e => Nat.Coprime (P.f ξ) e),
        S.coeff e * P.Eerr ξ.j (P.f ξ * e) (P.bRes ξ e) := by
  classical
  unfold RSigmaP XiAll PairRem
  rw [Finset.sum_biUnion]
  intro p _ p' _ hne
  refine Finset.disjoint_left.2 (fun ξ h1 h2 => hne ?_)
  obtain ⟨a1, b1, -⟩ := mem_Xi h1
  obtain ⟨a2, b2, -⟩ := mem_Xi h2
  exact Prod.ext (a1.symm.trans a2) (b1.symm.trans b2)

/-- **`∑_{j<ℓ} PairSum = Main + R_Σ^P`** (exact, from the pair identity). -/
theorem pairTotal_eq_main_add_RSigmaP (hP : P.WGood) (S : ScalarSieve) (hS : S.Good P.W) :
    P.PairTotal S = P.MainTotal S + P.RSigmaP S := by
  unfold PairTotal MainTotal RSigmaP
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  exact pairSum_eq_main_add_rem hP S hS (Finset.mem_filter.1 hp).2

/-- **`R_Σ^P = R_rel + R_base`** (§21), on the same packet and scalar-divisor support. -/
theorem RSigmaP_eq_rel_add_base (hP : P.WGood) (S : ScalarSieve) (hS : S.Good P.W) :
    P.RSigmaP S = P.Rrel S + P.Rbase S := by
  classical
  rw [RSigmaP_eq_packetIndexed, Rrel, Rbase, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ξ hξ => ?_)
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun e he => ?_)
  obtain ⟨heS, hfe⟩ := Finset.mem_filter.1 he
  have hf := f_pos hP (mem_XiAll hξ)
  have he0 := (hS e heS).1
  have h1 : (0 : ℝ) < Nat.totient (P.f ξ) := by exact_mod_cast Nat.totient_pos.2 hf
  have h2 : (0 : ℝ) < Nat.totient e := by exact_mod_cast Nat.totient_pos.2 he0
  unfold Eerr
  rw [Nat.totient_mul hfe, Nat.cast_mul]
  field_simp
  ring

/-! ### Adapter to the generic `TensorSource` -/

open Classical in
/-- The prime indicator of the window `𝒥_j(X)`. -/
noncomputable def primeWindow (P : PhysData) (j : Fin P.k) (n : ℕ) : ℝ :=
  if n.Prime ∧ P.InJ j n then 1 else 0

/-- `P_j(q,b)` is the generic `progSum` of the prime indicator of the window. -/
theorem pcount_eq_progSum (j : Fin P.k) (q b : ℕ) :
    (P.Pcount j q b : ℝ) =
      Erdos287.CurrentTail.progSum (range (P.pMax j)) (P.primeWindow j) q b := by
  classical
  unfold Pcount Erdos287.CurrentTail.progSum primeWindow
  rw [Finset.sum_filter, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases h1 : n ≡ b [MOD q]
  · have h1' : (n : ℤ) ≡ b [ZMOD q] := (Int.natCast_modEq_iff).2 h1
    by_cases h2 : n.Prime ∧ P.InJ j n
    · simp [h1, h1', h2]
    · simp only [h1, h1', h2, if_true, and_true]
  · have h1' : ¬ (n : ℤ) ≡ b [ZMOD q] := fun h => h1 ((Int.natCast_modEq_iff).1 h)
    simp [h1, h1']

/-- `E_j(q,b)` is the generic `progErr` with main mass `V_j(X)`. -/
theorem eerr_eq_progErr (j : Fin P.k) (q b : ℕ) :
    P.Eerr j q b =
      Erdos287.CurrentTail.progErr (range (P.pMax j)) (P.primeWindow j) (P.Vmain j) q b := by
  unfold Eerr Erdos287.CurrentTail.progErr
  rw [pcount_eq_progSum]

open Classical in
/-- **Single-packet tensor source** for the labelled packet `ξ`: `ell = 1`, packet set `{ξ}`,
scalar support `{d ∈ supp ℓ_X : d > 0, (d, f_ξ) = 1}`, sequence `α_0` the prime indicator of
`𝒥_{j(ξ)}(X)`, main mass `V_{j(ξ)}(X)`. -/
noncomputable def packetTensor (P : PhysData) (S : ScalarSieve) (ξ : Packet P.k) :
    Erdos287.CurrentTail.TensorSource (Packet P.k) where
  ell := 1
  Xi := ({ξ} : Finset (Packet P.k)).filter (fun ξ' => 0 < P.f ξ')
  Γ := P.Gamma
  f := P.f
  c := P.cRes
  D := S.supp.filter (fun e => 0 < e ∧ Nat.Coprime (P.f ξ) e)
  lX := S.coeff
  b := P.bRes
  S := range (P.pMax ξ.j)
  α := fun _ => P.primeWindow ξ.j
  mass := fun _ => P.Vmain ξ.j
  f_pos := fun ξ' h => (Finset.mem_filter.1 h).2
  d_pos := fun e h => (Finset.mem_filter.1 h).2.1
  coprime := by
    intro ξ' h e he
    have := Finset.mem_singleton.1 (Finset.mem_filter.1 h).1
    subst this
    exact (Finset.mem_filter.1 he).2.2

/-- **Proved adapter**: `R_Σ^P = ∑_{ξ ∈ Ξ} (packetTensor ξ).RSigmaP`. -/
theorem RSigmaP_eq_sum_packetTensor (hP : P.WGood) (S : ScalarSieve) (hS : S.Good P.W) :
    P.RSigmaP S = ∑ ξ ∈ P.XiAll, (packetTensor P S ξ).RSigmaP := by
  classical
  rw [RSigmaP_eq_packetIndexed]
  refine Finset.sum_congr rfl (fun ξ hξ => ?_)
  have hf := f_pos hP (mem_XiAll hξ)
  unfold Erdos287.CurrentTail.TensorSource.RSigmaP packetTensor
  simp only [Finset.range_one, Finset.sum_singleton]
  rw [Finset.filter_singleton, if_pos hf, Finset.sum_singleton]
  congr 1
  have hD : S.supp.filter (fun e => 0 < e ∧ Nat.Coprime (P.f ξ) e) =
      S.supp.filter (fun e => Nat.Coprime (P.f ξ) e) := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, (hS e h.1).1, h.2⟩⟩
  rw [hD]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [eerr_eq_progErr]

/-- Centering through the adapter: `R_Σ^P = ∑_ξ (R_rel(ξ) + R_paid(ξ))` with the generic
`TensorSource.Rrel`/`Rpaid` of each single-packet source. -/
theorem RSigmaP_eq_sum_rel_paid (hP : P.WGood) (S : ScalarSieve) (hS : S.Good P.W) :
    P.RSigmaP S = ∑ ξ ∈ P.XiAll, ((packetTensor P S ξ).Rrel + (packetTensor P S ξ).Rpaid) := by
  rw [RSigmaP_eq_sum_packetTensor hP S hS]
  exact Finset.sum_congr rfl (fun ξ _ => (packetTensor P S ξ).RSigmaP_eq_Rrel_add_Rpaid)

end PhysData

end Erdos287.Physical

namespace Erdos287.Physical

/-- **Regression (why the naive instantiation is wrong).**  If a generic tensor source has
`j`-independent sequences and masses, its unrestricted `j`-sum multiplies the single-coordinate
remainder by `ell`: the generic `RSigmaP` with `ell = k` would count each labelled packet `k`
times.  The physical packets already carry their designated `j(ξ)`. -/
theorem generic_unrestricted_j_overcounts {ι : Type*} (T : Erdos287.CurrentTail.TensorSource ι)
    (hα : ∀ j, T.α j = T.α 0) (hm : ∀ j, T.mass j = T.mass 0) :
    T.RSigmaP = T.ell * ({ T with ell := 1 } : Erdos287.CurrentTail.TensorSource ι).RSigmaP := by
  unfold Erdos287.CurrentTail.TensorSource.RSigmaP
  simp only [Finset.range_one, Finset.sum_singleton]
  rw [Finset.sum_congr rfl (fun j _ => by rw [hα j, hm j]), Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]

end Erdos287.Physical
