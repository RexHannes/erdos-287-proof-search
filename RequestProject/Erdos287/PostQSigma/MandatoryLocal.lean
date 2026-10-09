import RequestProject.Erdos287.PostQSigma.MandatoryPrimary

/-!
# Erdős #287 — post-`Q_Σ` bank, §9–10 (V57): normalised source and the local mandatory criterion

**Status: BANK (proved in Lean).**  Everything here is exact; the definitions are stated for an
arbitrary compulsory set `R` (the raw source is `R = ∅`).

Notation: `q_{p,d} = p^(e-d+1)` with `p^e ‖ W`; the layer of `B` at depth `d` is
`{n ∈ B : q_{p,d} ∣ n}`, and `S_{p,d}` is its part inside `V`.

* `res a M R p d n = (W/n mod p^d)` — the physical residue (indexed by the position `n`, so
  repeated residue values are kept: this is a *multiset* indexed by positions);
* `cres a M R p d k = res (q_{p,d}·k)` — the normalised residue of cofactor `k`;
* `eta a M R p d = ∑_{n ∈ B \ V, q ∣ n} W/n mod p^d` — the fixed (endpoint / `R`-neighbour)
  contribution; for `R = ∅` the set `B \ V` is exactly the two selected endpoints `{a, M}`.

Main results:

* `T_cast_eq` — `T ≡ ∑_{n∈S_{p,d}} W/n + η_{p,d} (mod p^d)`;
* `selected_complement_congruence` — for every exact solution `E`,
  `∑_{n ∈ B\E, q ∣ n} W/n ≡ 0 (mod p^d)`;
* `mandatory_iff_local` — **V57 local characterisation**: `S_{p,d}` is mandatory iff
  `S_{p,d} ≠ ∅`, `η_{p,d} = 0`, and the position-indexed residue family on `S_{p,d}` has no
  nonempty zero-sum subfamily mod `p^d`;
* `exists_unreachable_iff_deepest` — some depth of `p` is unreachable iff the deepest depth
  `d = e_p` is unreachable;
* `S_empty_eq_cofactor_image`, `S_nonempty_iff_cofactor` — for `R = ∅`, `S_{p,d}` is the image
  of the physical cofactor interval `{k : a < q k < M}` under `k ↦ q k`.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

open Erdos287.ExactSource

variable {a M : ℕ} {R : Finset ℕ}

/-- `q_{p,d} = p^(e-d+1)`. -/
def qpd (a M : ℕ) (R : Finset ℕ) (p d : ℕ) : ℕ := p ^ (eW a M R p - d + 1)

/-- Physical residue `W/n mod p^d`. -/
def res (a M : ℕ) (R : Finset ℕ) (p d n : ℕ) : ZMod (p ^ d) := ((W a M R / n : ℕ) : ZMod (p ^ d))

/-- Normalised residue of the cofactor `k`: the residue of `q_{p,d} · k`. -/
def cres (a M : ℕ) (R : Finset ℕ) (p d k : ℕ) : ZMod (p ^ d) := res a M R p d (qpd a M R p d * k)

open Classical in
/-- Endpoint contribution `η_{p,d} = ∑_{n ∈ B \ V, q ∣ n} W/n mod p^d`. -/
noncomputable def eta (a M : ℕ) (R : Finset ℕ) (p d : ℕ) : ZMod (p ^ d) :=
  ∑ n ∈ (B a M R \ V a M R).filter (fun n => qpd a M R p d ∣ n), res a M R p d n

/-- Off-layer elements of `B` contribute `0 (mod p^d)`. -/
lemma pow_dvd_W_div_of_mem_B (ha : 0 < a) {p d n : ℕ} (hp : p.Prime)
    (hd : d ≤ eW a M R p) (hn : n ∈ B a M R) (hnS : ¬ qpd a M R p d ∣ n) :
    p ^ d ∣ W a M R / n := by
  have hnW := dvd_W_of_mem_B hn
  have hnpos : 0 < n := pos_of_mem_B ha hn
  have hW0 : W a M R ≠ 0 := W_ne_zero ha
  have hq0 : W a M R / n ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hW0) hnW) hnpos).ne'
  rw [hp.pow_dvd_iff_le_factorization hq0, Nat.factorization_div hnW]
  unfold qpd at hnS
  rw [hp.pow_dvd_iff_le_factorization hnpos.ne'] at hnS
  simp only [Finsupp.coe_tsub, Pi.sub_apply]
  unfold eW at hd hnS
  omega

lemma res_eq_zero_of_not_dvd (ha : 0 < a) {p d n : ℕ} (hp : p.Prime)
    (hd : d ≤ eW a M R p) (hn : n ∈ B a M R) (hnS : ¬ qpd a M R p d ∣ n) :
    res a M R p d n = 0 := by
  unfold res
  rw [ZMod.natCast_eq_zero_iff]
  exact pow_dvd_W_div_of_mem_B ha hp hd hn hnS

lemma W_cast_eq_zero {p d : ℕ} (hd : d ≤ eW a M R p) : ((W a M R : ℕ) : ZMod (p ^ d)) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact (pow_dvd_pow p hd).trans (Nat.ordProj_dvd _ _)

open Classical in
/-- Summing the residues over the layer part of any `F ⊆ B` (the off-layer part vanishes). -/
lemma sum_res_filter (ha : 0 < a) {p d : ℕ} (hp : p.Prime) (hd : d ≤ eW a M R p)
    {F : Finset ℕ} (hF : F ⊆ B a M R) :
    ∑ n ∈ F, res a M R p d n = ∑ n ∈ F.filter (fun n => qpd a M R p d ∣ n), res a M R p d n := by
  rw [← Finset.sum_filter_add_sum_filter_not F (fun n => qpd a M R p d ∣ n), add_eq_left]
  exact Finset.sum_eq_zero (fun n hn => by
    rw [Finset.mem_filter] at hn
    exact res_eq_zero_of_not_dvd ha hp hd (hF hn.1) hn.2)

lemma S_eq_filter (p d : ℕ) :
    S a M R p d = (V a M R).filter (fun n => qpd a M R p d ∣ n) := rfl

/-- The cast of an integer sum of `W/n` is the sum of residues. -/
lemma cast_sum_eq (p d : ℕ) (F : Finset ℕ) :
    (((∑ n ∈ F, ((W a M R / n : ℕ) : ℤ)) : ℤ) : ZMod (p ^ d)) = ∑ n ∈ F, res a M R p d n := by
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [Int.cast_natCast]; rfl

/-- **Exact target decomposition**: `T ≡ ∑_{S_{p,d}} W/n + η_{p,d} (mod p^d)`. -/
theorem T_cast_eq (ha : 0 < a) {p d : ℕ} (hp : p.Prime) (hd : d ≤ eW a M R p) :
    ((T a M R : ℤ) : ZMod (p ^ d)) = (∑ n ∈ S a M R p d, res a M R p d n) + eta a M R p d := by
  classical
  rw [T, Int.cast_sub, cast_sum_eq, Int.cast_natCast, W_cast_eq_zero hd, sub_zero]
  rw [← Finset.sum_sdiff (V_subset_B (a := a) (M := M) (R := R)), add_comm]
  congr 1
  · rw [S_eq_filter, ← sum_res_filter ha hp hd V_subset_B]
  · rw [eta, ← sum_res_filter ha hp hd Finset.sdiff_subset]

open Classical in
/-- **Selected-complement congruence.**  For every exact solution `E`, the selected
denominators of the layer satisfy `∑_{n ∈ B\E, q ∣ n} W/n ≡ 0 (mod p^d)`. -/
theorem selected_complement_congruence (ha : 0 < a) {p d : ℕ} (hp : p.Prime)
    (hd : d ≤ eW a M R p) {E : Finset ℕ} (h : SourceSol a M R E) :
    ∑ n ∈ (B a M R \ E).filter (fun n => qpd a M R p d ∣ n), res a M R p d n = 0 := by
  have hEB : E ⊆ B a M R := h.1.trans V_subset_B
  rw [← sum_res_filter ha hp hd Finset.sdiff_subset]
  have hsum : (∑ n ∈ B a M R \ E, ((W a M R / n : ℕ) : ℤ)) = W a M R := by
    have h1 := Finset.sum_sdiff (f := fun n => ((W a M R / n : ℕ) : ℤ)) hEB
    have h2 := h.2.2
    unfold T at h2
    linarith
  have := congrArg (fun z : ℤ => (z : ZMod (p ^ d))) hsum
  simp only [cast_sum_eq, Int.cast_natCast] at this
  rw [this, W_cast_eq_zero hd]

/-- Repair condition in `ZMod`. -/
lemma modEq_iff_cast (p d : ℕ) (F : Finset ℕ) :
    (∑ n ∈ F, ((W a M R / n : ℕ) : ℤ)) ≡ T a M R [ZMOD (p : ℤ) ^ d] ↔
      ∑ n ∈ F, res a M R p d n = ((T a M R : ℤ) : ZMod (p ^ d)) := by
  rw [← cast_sum_eq, ZMod.intCast_eq_intCast_iff]
  push_cast; rfl

/-- **V57 local characterisation of mandatory layers.** -/
theorem mandatory_iff_local (ha : 0 < a) {p d : ℕ} (hp : p.Prime) (hd : d ≤ eW a M R p) :
    Mandatory a M R p d ↔
      (S a M R p d).Nonempty ∧ eta a M R p d = 0 ∧
      ∀ G ⊆ S a M R p d, G.Nonempty → ∑ n ∈ G, res a M R p d n ≠ 0 := by
  classical
  have hT := T_cast_eq ha hp hd
  constructor
  · rintro ⟨hpos, hk⟩
    have hne : (RepairSizes a M R p d).Nonempty := by
      by_contra hc
      rw [Set.not_nonempty_iff_eq_empty] at hc
      simp [kappa, hc] at hpos
    obtain ⟨F, hFS, hFc, hFmod⟩ := Nat.sInf_mem hne
    have hFc' : F.card = (S a M R p d).card := hFc.trans hk
    have hFeq : F = S a M R p d := Finset.eq_of_subset_of_card_le hFS hFc'.ge
    rw [hFeq] at hFmod
    rw [modEq_iff_cast] at hFmod
    have heta : eta a M R p d = 0 := by
      rw [hT] at hFmod
      exact (add_eq_left.1 hFmod.symm)
    refine ⟨Finset.card_pos.1 (hk ▸ hpos), heta, fun G hGS hGne hG0 => ?_⟩
    have hmem : (S a M R p d \ G).card ∈ RepairSizes a M R p d := by
      refine ⟨S a M R p d \ G, Finset.sdiff_subset, rfl, ?_⟩
      rw [modEq_iff_cast, hT, heta, add_zero]
      have := Finset.sum_sdiff (f := fun n => res a M R p d n) hGS
      rw [hG0, add_zero] at this
      exact this
    have hle := Nat.sInf_le hmem
    have hlt : (S a M R p d \ G).card < (S a M R p d).card := Finset.card_lt_card
      (Finset.sdiff_ssubset hGS hGne)
    change kappa a M R p d ≤ _ at hle
    omega
  · rintro ⟨hne, heta, hzs⟩
    have hSmem : (S a M R p d).card ∈ RepairSizes a M R p d := by
      refine ⟨S a M R p d, subset_rfl, rfl, ?_⟩
      rw [modEq_iff_cast, hT, heta, add_zero]
    obtain ⟨F, hFS, hFc, hFmod⟩ := Nat.sInf_mem ⟨_, hSmem⟩
    rw [modEq_iff_cast, hT, heta, add_zero] at hFmod
    have hG : S a M R p d \ F = ∅ := by
      by_contra hc
      apply hzs (S a M R p d \ F) Finset.sdiff_subset (Finset.nonempty_iff_ne_empty.2 hc)
      have := Finset.sum_sdiff (f := fun n => res a M R p d n) hFS
      rw [hFmod] at this
      exact add_eq_right.1 this
    have hSF : S a M R p d ⊆ F := Finset.sdiff_eq_empty_iff_subset.1 hG
    have hFeq : F = S a M R p d := le_antisymm hFS hSF
    have hk : kappa a M R p d = (S a M R p d).card := by
      change sInf _ = _; rw [← hFc, hFeq]
    exact ⟨hk ▸ Finset.card_pos.2 hne, hk⟩

/-! ## Deepest-unreachable reduction -/

/-- Depth `d` of `p` is **unreachable** (`κ_{p,d} = ∞`). -/
def Unreachable (a M : ℕ) (R : Finset ℕ) (p d : ℕ) : Prop := RepairSizes a M R p d = ∅

/-- Reachability descends: a repair set mod `p^(d+1)` restricts to one mod `p^d`. -/
theorem reachable_of_reachable_succ (ha : 0 < a) {p d : ℕ} (hp : p.Prime)
    (hd : d + 1 ≤ eW a M R p) (h : (RepairSizes a M R p (d + 1)).Nonempty) :
    (RepairSizes a M R p d).Nonempty := by
  classical
  obtain ⟨_, F, hFS, -, hFmod⟩ := h
  refine ⟨_, F.filter (fun n => p ^ (eW a M R p - d + 1) ∣ n), ?_, rfl, ?_⟩
  · intro n hn
    rw [Finset.mem_filter] at hn
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 (hFS hn.1)).1, hn.2⟩
  · have hsplit := Finset.sum_filter_add_sum_filter_not F
      (fun n => p ^ (eW a M R p - d + 1) ∣ n) (fun n => ((W a M R / n : ℕ) : ℤ))
    have hrest : ((p : ℤ) ^ d) ∣ ∑ n ∈ F.filter (fun n => ¬ p ^ (eW a M R p - d + 1) ∣ n),
        ((W a M R / n : ℕ) : ℤ) := by
      refine Finset.dvd_sum (fun n hn => ?_)
      rw [Finset.mem_filter] at hn
      have := pow_dvd_W_div_of_not_mem_S ha hp (by omega)
        (Finset.mem_filter.1 (hFS hn.1)).1 hn.2
      exact_mod_cast this
    have hmod' : (∑ n ∈ F, ((W a M R / n : ℕ) : ℤ)) ≡ T a M R [ZMOD (p : ℤ) ^ d] :=
      Int.ModEq.of_mul_right (p : ℤ) (by rw [← pow_succ]; exact hFmod)
    rw [← hsplit] at hmod'
    have h0 : ∑ n ∈ F.filter (fun n => ¬ p ^ (eW a M R p - d + 1) ∣ n),
        ((W a M R / n : ℕ) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ d] := Int.modEq_zero_iff_dvd.2 hrest
    have := (Int.ModEq.add_left (∑ n ∈ F.filter (fun n => p ^ (eW a M R p - d + 1) ∣ n),
      ((W a M R / n : ℕ) : ℤ)) h0).symm.trans hmod'
    simpa using this

/-- Unreachability propagates to every deeper depth up to `e_p`. -/
theorem unreachable_mono (ha : 0 < a) {p d d' : ℕ} (hp : p.Prime) (hdd : d ≤ d')
    (hd' : d' ≤ eW a M R p) (h : Unreachable a M R p d) : Unreachable a M R p d' := by
  induction d', hdd using Nat.le_induction with
  | base => exact h
  | succ k hk ih =>
    have ih' := ih (by omega)
    by_contra hc
    rw [Unreachable, ← Ne, ← Set.nonempty_iff_ne_empty] at hc
    have := reachable_of_reachable_succ ha hp hd' hc
    rw [Unreachable] at ih'
    rw [ih'] at this
    exact Set.not_nonempty_empty this

/-- **Deepest-unreachable reduction**: some depth `1 ≤ d ≤ e_p` is unreachable iff the
deepest depth `e_p` is unreachable. -/
theorem exists_unreachable_iff_deepest (ha : 0 < a) {p : ℕ} (hp : p.Prime) :
    (∃ d, 1 ≤ d ∧ d ≤ eW a M R p ∧ Unreachable a M R p d) ↔
      (1 ≤ eW a M R p ∧ Unreachable a M R p (eW a M R p)) := by
  constructor
  · rintro ⟨d, h1, h2, h3⟩
    exact ⟨by omega, unreachable_mono ha hp h2 le_rfl h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨_, h1, le_rfl, h2⟩

/-! ## The physical cofactor interval (raw source `R = ∅`) -/

/-- Physical cofactor interval `{k : a < q k < M}`. -/
def cofInt (a M q : ℕ) : Finset ℕ := (Finset.range (M + 1)).filter (fun k => a < q * k ∧ q * k < M)

lemma V_empty_eq : V a M ∅ = Finset.Ioo a M := by
  ext n
  simp only [mem_V, mem_B, Finset.mem_Ioo, Finset.notMem_empty, not_false_eq_true,
    IsEmpty.forall_iff, implies_true, and_true]
  omega

/-- For the raw source, `S_{p,d}` is the image of the cofactor interval. -/
theorem S_empty_eq_cofactor_image {p d : ℕ} (hp : p.Prime) :
    S a M ∅ p d = (cofInt a M (qpd a M ∅ p d)).image (fun k => qpd a M ∅ p d * k) := by
  have hq : 0 < qpd a M ∅ p d := pow_pos hp.pos _
  ext n
  rw [S_eq_filter, V_empty_eq, Finset.mem_filter, Finset.mem_Ioo, Finset.mem_image]
  simp only [cofInt, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, k, rfl⟩
    refine ⟨k, ⟨?_, h1, h2⟩, rfl⟩
    have : k ≤ qpd a M ∅ p d * k := Nat.le_mul_of_pos_left k hq
    omega
  · rintro ⟨k, ⟨-, h1, h2⟩, rfl⟩
    exact ⟨⟨h1, h2⟩, dvd_mul_right _ _⟩

theorem S_nonempty_iff_cofactor {p d : ℕ} (hp : p.Prime) :
    (S a M ∅ p d).Nonempty ↔ (cofInt a M (qpd a M ∅ p d)).Nonempty := by
  rw [S_empty_eq_cofactor_image hp, Finset.image_nonempty]

/-- For the raw source, the fixed positions `B \ V` are exactly the two selected endpoints. -/
theorem B_sdiff_V_empty (haM : a ≤ M) : B a M ∅ \ V a M ∅ = {a, M} := by
  ext n
  rw [Finset.mem_sdiff, V_empty_eq, mem_B, Finset.mem_Ioo, Finset.mem_insert,
    Finset.mem_singleton]
  simp only [Finset.notMem_empty, not_false_eq_true, and_true]
  omega

end Erdos287.PostQSigma
