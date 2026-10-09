import RequestProject.Erdos287.SourceChain.Physical.Residues

/-!
# Erdős #287 — physical source: prime counts, the pair term and the exact pair identity

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**  Literal objects of
`sources/physical_spec.md` §§6, 8, 11, 12:

* `Tset` — the physical parameters `c₁X < t < c₂X`;
* `Pcount j q b` — `P_j(q,b) = #{p ∈ 𝒥_j(X) prime, p ≡ b (mod q)}` with
  `𝒥_j(X) = (a_j c₁X + 1, a_j c₂X + 1)` (prime counts, *not* von Mangoldt weights);
* `Vmain j = ∫_{a_j c₁X+1}^{a_j c₂X+1} dt / log t = Li(a_j c₂X+1) - Li(a_j c₁X+1)`;
* `Eerr j q b = P_j(q,b) - V_j(X)/φ(q)`;
* `MaynardInner j ℓ t = ∑_{d : d_j = d_ℓ = 1, d_i ∣ L_i(t)} ω_d` (the pair-term Maynard sum);
* `Xi j ℓ` — the labelled admissible packets `ξ = (j, ℓ, d, d')`;
* `ScalarSieve` — the scalar coefficient `ℓ_X` on a finite `W`-coprime support, with
  `U_X(v) = ∑_{d ∣ v} ℓ_X(d)`;
* `PairSum S j ℓ = ∑_t 1_{W ∣ t} 1_{L_j(t) prime} U_X(L_ℓ(t)) (∑ ω_d)(∑ ω_{d'})` — the literal
  designated-pair term of the Maynard square.

Kernel-proved:

* `maynardInner_eq_divisors` — the divisor-vector truncation in `MaynardInner` is lossless;
* `pairSum_eq_packets` — **the exact pair-indexing identity**
  `PairSum = ∑_{ξ ∈ Ξ_{jℓ}} Γ_ξ ∑_{d, (d,f_ξ)=1} ℓ_X(d) P_j(f_ξ d, b_{ξ,d})`;
* `pairSum_eq_main_add_rem` — `PairSum = PairMain + PairRem`, with
  `PairRem = ∑_ξ Γ_ξ ∑_d ℓ_X(d) E_j(f_ξ d, b_{ξ,d})`.

The coefficient `ℓ_X` is a *parameter* (`ScalarSieve`): the low-prime weights
`λ_low^±` that enter `ℓ_X` (§15) are not given by an explicit formula in the source.  Every
identity here holds for every choice of `ℓ_X` supported on `W`-coprime integers.
-/

open scoped BigOperators
open Finset

namespace Erdos287.Physical

namespace PhysData

variable (P : PhysData)

/-- `⌈c₂ X⌉`. -/
noncomputable def tMax : ℕ := ⌈P.c2 * P.X⌉₊

/-- The physical parameter range `c₁ X < t < c₂ X`. -/
noncomputable def Tset : Finset ℕ :=
  (range (P.tMax + 1)).filter (fun t => P.c1 * P.X < t ∧ (t : ℝ) < P.c2 * P.X)

/-- A bound for the prime window `𝒥_j(X)`. -/
noncomputable def pMax (j : Fin P.k) : ℕ := ⌈(P.a j : ℝ) * P.c2 * P.X⌉₊ + 2

/-- `p ∈ 𝒥_j(X) = (a_j c₁ X + 1, a_j c₂ X + 1)`. -/
def InJ (j : Fin P.k) (p : ℕ) : Prop :=
  (P.a j : ℝ) * P.c1 * P.X + 1 < p ∧ (p : ℝ) < P.a j * P.c2 * P.X + 1

open Classical in
/-- **`P_j(q,b)`**: the number of primes `p ∈ 𝒥_j(X)` with `p ≡ b (mod q)`. -/
noncomputable def Pcount (j : Fin P.k) (q b : ℕ) : ℕ :=
  ((range (P.pMax j)).filter (fun p => p.Prime ∧ P.InJ j p ∧ (p : ℤ) ≡ b [ZMOD q])).card

/-- **`V_j(X) = Li(a_j c₂X + 1) - Li(a_j c₁X + 1) = ∫ dt / log t`.** -/
noncomputable def Vmain (j : Fin P.k) : ℝ :=
  ∫ u in ((P.a j : ℝ) * P.c1 * P.X + 1)..((P.a j : ℝ) * P.c2 * P.X + 1), 1 / Real.log u

/-- **`E_j(q,b) = P_j(q,b) - V_j(X)/φ(q)`.** -/
noncomputable def Eerr (j : Fin P.k) (q b : ℕ) : ℝ :=
  (P.Pcount j q b : ℝ) - P.Vmain j / (Nat.totient q : ℝ)

/-- A divisor bound valid for every `L_i(t)`, `t ∈ Tset`. -/
noncomputable def Dmax : ℕ := (∑ i, P.a i) * P.tMax + 1

/-- Divisor vectors with designated entries `d_j = d_ℓ = 1`. -/
noncomputable def Dvec (j l : Fin P.k) : Finset (Fin P.k → ℕ) :=
  (Fintype.piFinset fun _ => Icc 1 P.Dmax).filter (fun d => d j = 1 ∧ d l = 1)

open Classical in
/-- The pair-term Maynard sum `∑_{d_j = d_ℓ = 1, d_i ∣ L_i(t)} ω_d`. -/
noncomputable def MaynardInner (j l : Fin P.k) (t : ℕ) : ℝ :=
  ∑ d ∈ (P.Dvec j l).filter (fun d => ∀ i, d i ∣ P.L i t), P.omega d

/-- The labelling map `(d, d') ↦ (j, ℓ, d, d')`. -/
def packetOf (j l : Fin P.k) : (Fin P.k → ℕ) × (Fin P.k → ℕ) ↪ Packet P.k where
  toFun x := ⟨j, l, x.1, x.2⟩
  inj' := by
    intro x y h
    simp only [Packet.mk.injEq, true_and] at h
    exact Prod.ext h.1 h.2

open Classical in
/-- **`Ξ_{jℓ}`**: the labelled admissible packets for the designated pair `(j, ℓ)`. -/
noncomputable def Xi (j l : Fin P.k) : Finset (Packet P.k) :=
  ((P.Dvec j l ×ˢ P.Dvec j l).filter (fun x => P.Admissible (P.packetOf j l x))).map
    (P.packetOf j l)

end PhysData

/-- The scalar upper-sieve coefficient `ℓ_X` on a finite support (§15).  Its internal
formula (the low-prime weights `λ_low^±`) is not supplied by the source, so it is a
parameter of every statement below. -/
structure ScalarSieve where
  supp : Finset ℕ
  coeff : ℕ → ℝ

namespace ScalarSieve

/-- Support hypothesis: positive and coprime to `W` (§10, "the physical scalar divisor is
coprime to `W`"). -/
def Good (S : ScalarSieve) (W : ℕ) : Prop := ∀ e ∈ S.supp, 0 < e ∧ Nat.Coprime e W

open Classical in
/-- `U_X(v) = ∑_{d ∣ v} ℓ_X(d)`. -/
noncomputable def U (S : ScalarSieve) (v : ℕ) : ℝ := ∑ e ∈ S.supp.filter (· ∣ v), S.coeff e

end ScalarSieve

namespace PhysData

variable (P : PhysData)

open Classical in
/-- **The literal designated-pair term**
`∑_t 1_{W∣t} 1_{L_j(t) prime} U_X(L_ℓ(t)) (∑_d ω_d)(∑_{d'} ω_{d'})`. -/
noncomputable def PairSum (S : ScalarSieve) (j l : Fin P.k) : ℝ :=
  ∑ t ∈ P.Tset, (if P.W ∣ t ∧ (P.L j t).Prime then (1 : ℝ) else 0) * S.U (P.L l t) *
    P.MaynardInner j l t * P.MaynardInner j l t

open Classical in
/-- The packet-side form `∑_{ξ} Γ_ξ ∑_{d, (d,f_ξ)=1} ℓ_X(d) P_j(f_ξ d, b_{ξ,d})`. -/
noncomputable def PairPackets (S : ScalarSieve) (j l : Fin P.k) : ℝ :=
  ∑ ξ ∈ P.Xi j l, P.Gamma ξ * ∑ e ∈ S.supp.filter (fun e => Nat.Coprime (P.f ξ) e),
    S.coeff e * (P.Pcount ξ.j (P.f ξ * e) (P.bRes ξ e) : ℝ)

open Classical in
/-- Main part `∑_ξ Γ_ξ ∑_d ℓ_X(d) V_j(X)/φ(f_ξ d)`. -/
noncomputable def PairMain (S : ScalarSieve) (j l : Fin P.k) : ℝ :=
  ∑ ξ ∈ P.Xi j l, P.Gamma ξ * ∑ e ∈ S.supp.filter (fun e => Nat.Coprime (P.f ξ) e),
    S.coeff e * (P.Vmain ξ.j / (Nat.totient (P.f ξ * e) : ℝ))

open Classical in
/-- **Pair remainder** `∑_ξ Γ_ξ ∑_d ℓ_X(d) E_j(f_ξ d, b_{ξ,d})`. -/
noncomputable def PairRem (S : ScalarSieve) (j l : Fin P.k) : ℝ :=
  ∑ ξ ∈ P.Xi j l, P.Gamma ξ * ∑ e ∈ S.supp.filter (fun e => Nat.Coprime (P.f ξ) e),
    S.coeff e * P.Eerr ξ.j (P.f ξ * e) (P.bRes ξ e)

variable {P}

/-- `PairPackets = PairMain + PairRem` (definition of `E_j`). -/
theorem pairPackets_eq_main_add_rem (S : ScalarSieve) (j l : Fin P.k) :
    P.PairPackets S j l = P.PairMain S j l + P.PairRem S j l := by
  unfold PairPackets PairMain PairRem Eerr
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun e _ => ?_)
  ring

/-! ### Proof of the exact pair identity -/

theorem expand_pair_square {β γ : Type*} (D : Finset β) (S : Finset γ)
    (A : Prop) [Decidable A] (C : β → Prop) [DecidablePred C]
    (E : γ → Prop) [DecidablePred E] (ω : β → ℝ) (l : γ → ℝ) :
    (if A then (1:ℝ) else 0) * (∑ e ∈ S.filter E, l e) *
      (∑ d ∈ D.filter C, ω d) * (∑ d ∈ D.filter C, ω d) =
      ∑ x ∈ D ×ˢ D, ∑ e ∈ S, ω x.1 * ω x.2 * l e *
        (if A ∧ C x.1 ∧ C x.2 ∧ E e then (1:ℝ) else 0) := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_product]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun d1 _ => Finset.sum_congr rfl (fun d2 _ =>
    Finset.sum_congr rfl (fun e _ => ?_)))
  by_cases hA : A <;> by_cases h1 : C d1 <;> by_cases h2 : C d2 <;>
    by_cases h3 : E e <;> simp [hA, h1, h2, h3]
  ring

variable (P) in
/-- The joint condition on `t` in the pair term. -/
def PairCond (j l : Fin P.k) (x : (Fin P.k → ℕ) × (Fin P.k → ℕ)) (e t : ℕ) : Prop :=
  (P.W ∣ t ∧ (P.L j t).Prime) ∧ (∀ i, x.1 i ∣ P.L i t) ∧ (∀ i, x.2 i ∣ P.L i t) ∧ e ∣ P.L l t

variable (P) in
open Classical in
/-- The number of physical parameters `t` satisfying the joint condition. -/
noncomputable def cnt (j l : Fin P.k) (x : (Fin P.k → ℕ) × (Fin P.k → ℕ)) (e : ℕ) : ℕ :=
  (P.Tset.filter (P.PairCond j l x e)).card

theorem pairSum_expand (S : ScalarSieve) (j l : Fin P.k) :
    P.PairSum S j l = ∑ x ∈ P.Dvec j l ×ˢ P.Dvec j l, ∑ e ∈ S.supp,
      P.omega x.1 * P.omega x.2 * S.coeff e * (P.cnt j l x e : ℝ) := by
  classical
  have h1 : ∀ t ∈ P.Tset, (if P.W ∣ t ∧ (P.L j t).Prime then (1 : ℝ) else 0) * S.U (P.L l t) *
      P.MaynardInner j l t * P.MaynardInner j l t =
      ∑ x ∈ P.Dvec j l ×ˢ P.Dvec j l, ∑ e ∈ S.supp, P.omega x.1 * P.omega x.2 * S.coeff e *
        (if P.PairCond j l x e t then (1:ℝ) else 0) := by
    intro t _
    unfold ScalarSieve.U MaynardInner PairCond
    convert expand_pair_square (P.Dvec j l) S.supp (P.W ∣ t ∧ (P.L j t).Prime)
      (fun d => ∀ i, d i ∣ P.L i t) (fun e => e ∣ P.L l t) P.omega S.coeff
  unfold PairSum
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [← Finset.mul_sum, cnt, Finset.card_filter]
  push_cast
  rfl

theorem packetOf_j (j l : Fin P.k) (x) : (P.packetOf j l x).j = j := rfl
theorem packetOf_l (j l : Fin P.k) (x) : (P.packetOf j l x).l = l := rfl
theorem packetOf_d (j l : Fin P.k) (x) : (P.packetOf j l x).d = x.1 := rfl
theorem packetOf_d' (j l : Fin P.k) (x) : (P.packetOf j l x).d' = x.2 := rfl

theorem pairCond_iff {j l : Fin P.k} {x : (Fin P.k → ℕ) × (Fin P.k → ℕ)}
    (hξ : P.Admissible (P.packetOf j l x)) (e t : ℕ) :
    P.PairCond j l x e t ↔ (P.L j t).Prime ∧ (P.W ∣ t ∧
      (∀ i ∈ P.spec (P.packetOf j l x), P.q (P.packetOf j l x) i ∣ P.L i t) ∧
        e ∣ P.L l t) := by
  obtain ⟨-, h1, h2, h3, h4, -⟩ := hξ
  simp only [packetOf_j, packetOf_l, packetOf_d, packetOf_d'] at h1 h2 h3 h4
  unfold PairCond q spec
  simp only [packetOf_j, packetOf_l, packetOf_d, packetOf_d', Finset.mem_filter,
    Finset.mem_univ, true_and, Nat.lcm_dvd_iff]
  constructor
  · rintro ⟨⟨hW, hp⟩, hd, hd', he⟩
    exact ⟨hp, hW, fun i _ => ⟨hd i, hd' i⟩, he⟩
  · rintro ⟨hp, hW, hd, he⟩
    refine ⟨⟨hW, hp⟩, fun i => ?_, fun i => ?_, he⟩
    · by_cases hij : i = j
      · subst hij; rw [h1]; exact one_dvd _
      by_cases hil : i = l
      · subst hil; rw [h3]; exact one_dvd _
      exact (hd i ⟨hij, hil⟩).1
    · by_cases hij : i = j
      · subst hij; rw [h2]; exact one_dvd _
      by_cases hil : i = l
      · subst hil; rw [h4]; exact one_dvd _
      exact (hd i ⟨hij, hil⟩).2

theorem L_injective (hP : P.WGood) (j : Fin P.k) : Function.Injective (P.L j) := by
  intro s t h
  unfold L at h
  have : P.a j * s = P.a j * t := by omega
  exact Nat.eq_of_mul_eq_mul_left (hP.a_pos j) this

/-- `t ∈ Tset ↔ L_j(t) ∈ 𝒥_j(X)` (for `a_j > 0`). -/
theorem mem_Tset_iff (hP : P.WGood) (j : Fin P.k) (t : ℕ) :
    t ∈ P.Tset ↔ P.InJ j (P.L j t) := by
  have ha : (0 : ℝ) < P.a j := by exact_mod_cast hP.a_pos j
  unfold Tset InJ L
  simp only [Finset.mem_filter, Finset.mem_range]
  push_cast
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    have h1' : P.c1 * P.X < t := by
      by_contra hc; push_neg at hc; nlinarith
    have h2' : (t : ℝ) < P.c2 * P.X := by
      by_contra hc; push_neg at hc; nlinarith
    refine ⟨?_, h1', h2'⟩
    have : t ≤ P.tMax := by
      unfold tMax
      exact_mod_cast (show (t : ℝ) ≤ ⌈P.c2 * P.X⌉₊ from h2'.le.trans (Nat.le_ceil _))
    omega

/-- **Counting identity**: for an admissible packet and an admissible scalar divisor, the
number of physical `t` equals the prime count `P_j(f_ξ d, b_{ξ,d})`. -/
theorem cnt_eq (hP : P.WGood) {j l : Fin P.k} {x : (Fin P.k → ℕ) × (Fin P.k → ℕ)}
    (hξ : P.Admissible (P.packetOf j l x)) {e : ℕ} (he0 : 0 < e) (heW : Nat.Coprime e P.W)
    (hfe : Nat.Coprime (P.f (P.packetOf j l x)) e) :
    P.cnt j l x e =
      P.Pcount j (P.f (P.packetOf j l x) * e) (P.bRes (P.packetOf j l x) e) := by
  classical
  have key := packet_congruence_iff hP hξ he0 heW hfe
  unfold cnt Pcount
  rw [← Finset.card_image_of_injective _ (L_injective hP j)]
  congr 1
  ext p
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    rw [pairCond_iff hξ] at hc
    obtain ⟨hp, hcong⟩ := hc
    have hcong' := (key t).1 hcong
    have hJ := (mem_Tset_iff hP j t).1 ht
    refine ⟨?_, hp, hJ, hcong'⟩
    have h2 := hJ.2
    have : (P.L j t : ℝ) ≤ ⌈(P.a j : ℝ) * P.c2 * P.X⌉₊ + 1 := by
      have := Nat.le_ceil ((P.a j : ℝ) * P.c2 * P.X); linarith
    unfold pMax
    exact_mod_cast (show (P.L j t : ℝ) < (⌈(P.a j : ℝ) * P.c2 * P.X⌉₊ + 2 : ℕ) by
      push_cast; linarith)
  · rintro ⟨-, hp, hJ, hcong⟩
    obtain ⟨-, hiffb⟩ := bRes_spec hP hξ he0 heW hfe
    have h1 := ((hiffb p).2 hcong).1
    have h2 := ((cRes_spec hP hξ).2 p).2 h1
    have h3 : (p : ℤ) ≡ 1 [ZMOD (P.a j : ℕ)] :=
      Int.ModEq.of_dvd (by exact_mod_cast Dvd.intro _ rfl) h2.1
    have h4 : P.a j ∣ p - 1 := by
      have := (Int.ModEq.dvd h3.symm)
      have hp1 : 1 ≤ p := hp.one_lt.le
      have : ((P.a j : ℕ) : ℤ) ∣ ((p - 1 : ℕ) : ℤ) := by push_cast [hp1]; exact this
      exact_mod_cast this
    obtain ⟨t, ht⟩ := h4
    have hLt : P.L j t = p := by
      unfold L; have := hp.one_lt; rw [← ht]; omega
    refine ⟨t, ⟨(mem_Tset_iff hP j t).2 (hLt ▸ hJ), ?_⟩, hLt⟩
    rw [pairCond_iff hξ]
    refine ⟨hLt ▸ hp, (key t).2 ?_⟩
    have : ((P.L (P.packetOf j l x).j t : ℕ) : ℤ) = p := by
      show ((P.L j t : ℕ) : ℤ) = p; rw [hLt]
    rw [this]; exact hcong

/-- A scalar divisor sharing a prime with `f_ξ` admits no physical `t`. -/
theorem cnt_zero_of_not_coprime (hP : P.WGood) {j l : Fin P.k}
    {x : (Fin P.k → ℕ) × (Fin P.k → ℕ)} (hξ : P.Admissible (P.packetOf j l x)) {e : ℕ}
    (heW : Nat.Coprime e P.W) (hnc : ¬ Nat.Coprime (P.f (P.packetOf j l x)) e) :
    P.cnt j l x e = 0 := by
  classical
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro t _ hc
  rw [pairCond_iff hξ] at hc
  obtain ⟨-, hW, hq, he⟩ := hc
  obtain ⟨p, hp, hpf, hpe⟩ := Nat.Prime.not_coprime_iff_dvd.1 hnc
  have hpW : ¬ p ∣ P.W := by
    intro h
    have := Nat.dvd_gcd hpe h
    rw [heW] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  unfold f q0 at hpf
  rcases (Nat.Prime.dvd_mul hp).1 hpf with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · exact hpW (hP.slope _ p hp h2)
    · exact hpW h2
  · obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 h1
    have hil : i ≠ l := (Finset.mem_filter.1 hi).2.2
    exact hP.no_common_prime heW hil hp hpe t (hpi.trans (hq i hi)) (hpe.trans he)

/-- `ω_d = 0` when some entry is not coprime to `W`. -/
theorem omega_eq_zero {d : Fin P.k → ℕ} {i : Fin P.k} (h : ¬ Nat.Coprime (d i) P.W) :
    P.omega d = 0 := by
  unfold omega
  rw [if_neg]
  intro hc
  exact h (Nat.Coprime.coprime_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) hc)

/-- Off the admissible support every term of the expanded pair sum vanishes. -/
theorem term_zero_of_not_admissible (hP : P.WGood) {j l : Fin P.k} (hjl : j < l)
    {x : (Fin P.k → ℕ) × (Fin P.k → ℕ)} (hx : x ∈ P.Dvec j l ×ˢ P.Dvec j l)
    (hna : ¬ P.Admissible (P.packetOf j l x)) (e : ℕ) (c : ℝ) :
    P.omega x.1 * P.omega x.2 * c * (P.cnt j l x e : ℝ) = 0 := by
  classical
  simp only [Dvec, Finset.mem_product, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_Icc] at hx
  obtain ⟨⟨hb1, h1j, h1l⟩, ⟨hb2, h2j, h2l⟩⟩ := hx
  by_cases hc : ∀ i, Nat.Coprime (x.1 i) P.W ∧ Nat.Coprime (x.2 i) P.W
  · -- the spectator `q_i` are not pairwise coprime: no physical `t`
    have hnpw : ¬ (P.spec (P.packetOf j l x) : Set (Fin P.k)).Pairwise
        (Function.onFun Nat.Coprime (P.q (P.packetOf j l x))) := by
      intro hpw
      exact hna ⟨hjl, h1j, h2j, h1l, h2l, fun i => ⟨(hb1 i).1, (hb2 i).1⟩, hc, hpw⟩
    have hzero : P.cnt j l x e = 0 := by
      unfold cnt
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro t _ hct
      apply hnpw
      intro i _ i' _ hii'
      by_contra hnc
      obtain ⟨p, hp, hpi, hpi'⟩ := Nat.Prime.not_coprime_iff_dvd.1 hnc
      have hqW : Nat.Coprime (P.q (P.packetOf j l x) i) P.W :=
        Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul _ _)
          (Nat.Coprime.mul_left (hc i).1 (hc i).2)
      have hdi : ∀ m, P.q (P.packetOf j l x) m ∣ P.L m t := fun m =>
        Nat.lcm_dvd (hct.2.1 m) (hct.2.2.1 m)
      exact hP.no_common_prime hqW hii' hp hpi t (hpi.trans (hdi i)) (hpi'.trans (hdi i'))
    rw [hzero]; simp
  · push_neg at hc
    obtain ⟨i, hi⟩ := hc
    by_cases h1 : Nat.Coprime (x.1 i) P.W
    · rw [omega_eq_zero (hi h1)]; simp
    · rw [omega_eq_zero h1]; simp

/-- **The exact pair-indexing identity** (§12): the literal designated-pair term of the
Maynard square equals the labelled packet sum
`∑_{ξ ∈ Ξ_{jℓ}} Γ_ξ ∑_{d ∈ supp ℓ_X, (d,f_ξ)=1} ℓ_X(d) P_j(f_ξ d, b_{ξ,d})`.
The designated coordinate is `j = j(ξ)`; there is no additional unrestricted `j`-sum. -/
theorem pairSum_eq_packets (hP : P.WGood) (S : ScalarSieve) (hS : S.Good P.W)
    {j l : Fin P.k} (hjl : j < l) : P.PairSum S j l = P.PairPackets S j l := by
  classical
  rw [pairSum_expand, PairPackets, Xi, Finset.sum_map]
  rw [← Finset.sum_filter_of_ne (p := fun x => P.Admissible (P.packetOf j l x))]
  · refine Finset.sum_congr rfl (fun x hx => ?_)
    have hξ := (Finset.mem_filter.1 hx).2
    rw [Gamma, Finset.mul_sum]
    rw [← Finset.sum_filter_of_ne (p := fun e => Nat.Coprime (P.f (P.packetOf j l x)) e)]
    · refine Finset.sum_congr rfl (fun e he => ?_)
      obtain ⟨heS, hfe⟩ := Finset.mem_filter.1 he
      rw [cnt_eq hP hξ (hS e heS).1 (hS e heS).2 hfe]
      simp only [packetOf_d, packetOf_d', packetOf_j]
      ring
    · intro e he hne
      by_contra hnc
      exact hne (by rw [cnt_zero_of_not_coprime hP hξ (hS e he).2 hnc]; simp)
  · intro x hx hne
    by_contra hna
    exact hne (Finset.sum_eq_zero (fun e _ =>
      term_zero_of_not_admissible hP hjl hx hna e (S.coeff e)))

/-- `PairSum = PairMain + PairRem`. -/
theorem pairSum_eq_main_add_rem (hP : P.WGood) (S : ScalarSieve) (hS : S.Good P.W)
    {j l : Fin P.k} (hjl : j < l) :
    P.PairSum S j l = P.PairMain S j l + P.PairRem S j l := by
  rw [pairSum_eq_packets hP S hS hjl, pairPackets_eq_main_add_rem]

end PhysData

end Erdos287.Physical
