import Mathlib

/-!
# Erdős #287 — post-`Q_Σ` bank, §20–21 (V61/V62): exact core/carry identity and the
contact–carry bridge

**Status: BANK (proved in Lean).**  The identity is exact (not a modular surrogate).

Data: `M`, a set `P` of primes with `M < p²` and `p ≤ M` (first-power large primes), and `h`
with `⌊M/p⌋ ≤ h < p` for all `p ∈ P`, `h ≤ M`.

* `W = lcm(1,…,M)`, `Lh = lcm(1,…,h)`, `D = W / ∏P`, `R = D / Lh`;
* for a selected set `x ⊆ [1, M]`: the core `{n ∈ x : p ∤ n ∀ p ∈ P}`, `C = ∑_{core} D/n`;
* rows `A_p = ∑_{n ∈ x, p ∣ n} Lh/(n/p)`; a row is *legal* if `p ∣ A_p`; `k_p = A_p / p`.

Results:

* `core_carry_identity` — `S(x) = C/D + (1/Lh) ∑_p k_p`;
* `core_carry_iff` — `S(x) = 1 ↔ R ∣ C ∧ ∑_p k_p = Lh - C/R` (in `ℤ`);
* `cover_lower_bound` — **contact–carry bridge**: defect-free ⇒ selected contact mass
  `≥ τ(G)`, the minimum reciprocal weight of a Boolean vertex cover;
* `tau_gt_tenth` — `5|E| > M` contacts in `[1, M]` ⇒ every cover has mass `> 1/10`;
* `core_cut` — with the identity: `S(x) = 1` and row mass `> 1/10` ⇒ `C/D < 9/10` and the
  integer cut `10 · (C/R) < 9 · Lh`.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma.CoreCarry

/-- Hypotheses on the large-prime set `P` and the row height `h`. -/
structure Hyp (M h : ℕ) (P : Finset ℕ) : Prop where
  prime : ∀ p ∈ P, p.Prime
  sq : ∀ p ∈ P, M < p * p
  le_M : ∀ p ∈ P, p ≤ M
  h_lt : ∀ p ∈ P, h < p
  div_le : ∀ p ∈ P, M / p ≤ h
  h_le : h ≤ M

/-- `lcm(1, …, n)`. -/
def lcmTo (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

def Dm (M : ℕ) (P : Finset ℕ) : ℕ := lcmTo M / ∏ p ∈ P, p

def Rm (M h : ℕ) (P : Finset ℕ) : ℕ := Dm M P / lcmTo h

open Classical in
def core (P x : Finset ℕ) : Finset ℕ := x.filter (fun n => ∀ p ∈ P, ¬ p ∣ n)

open Classical in
def row (x : Finset ℕ) (p : ℕ) : Finset ℕ := x.filter (fun n => p ∣ n)

def Cm (M : ℕ) (P x : Finset ℕ) : ℕ := ∑ n ∈ core P x, Dm M P / n

def Arow (h : ℕ) (x : Finset ℕ) (p : ℕ) : ℕ := ∑ n ∈ row x p, lcmTo h / (n / p)

def kRow (h : ℕ) (x : Finset ℕ) (p : ℕ) : ℕ := Arow h x p / p

lemma lcmTo_pos (n : ℕ) : 0 < lcmTo n := by
  apply Nat.pos_of_ne_zero
  intro h0
  rw [lcmTo, Finset.lcm_eq_zero_iff] at h0
  obtain ⟨x, hx, hx0⟩ := h0
  simp only [Finset.mem_Icc, id] at hx hx0; omega

lemma dvd_lcmTo {j n : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ n) : j ∣ lcmTo n :=
  Finset.dvd_lcm (f := id) (Finset.mem_Icc.2 ⟨h1, h2⟩)

variable {M h : ℕ} {P : Finset ℕ}

lemma prod_dvd_lcm (hyp : Hyp M h P) : ∏ p ∈ P, p ∣ lcmTo M :=
  Finset.prod_primes_dvd _ (fun p hp => (hyp.prime p hp).prime)
    (fun p hp => dvd_lcmTo (hyp.prime p hp).one_lt.le (hyp.le_M p hp))

lemma prod_pos (hyp : Hyp M h P) : 0 < ∏ p ∈ P, p :=
  Finset.prod_pos (fun p hp => (hyp.prime p hp).pos)

lemma lcm_eq_prod_mul_D (hyp : Hyp M h P) : lcmTo M = (∏ p ∈ P, p) * Dm M P :=
  (Nat.mul_div_cancel' (prod_dvd_lcm hyp)).symm

lemma D_pos (hyp : Hyp M h P) : 0 < Dm M P := by
  have := lcm_eq_prod_mul_D hyp
  have h1 := lcmTo_pos M
  rcases Nat.eq_zero_or_pos (Dm M P) with h0 | h0
  · rw [h0, mul_zero] at this; omega
  · exact h0

/-- Core denominators divide `D`. -/
lemma dvd_D_of_core (hyp : Hyp M h P) {x : Finset ℕ} (hx : x ⊆ Finset.Icc 1 M) {n : ℕ}
    (hn : n ∈ core P x) : n ∣ Dm M P := by
  classical
  obtain ⟨hnx, hnP⟩ := Finset.mem_filter.1 hn
  have hI := Finset.mem_Icc.1 (hx hnx)
  have hcop : Nat.Coprime n (∏ p ∈ P, p) := Nat.Coprime.prod_right (fun p hp =>
    (Nat.coprime_comm.1 ((hyp.prime p hp).coprime_iff_not_dvd.2 (hnP p hp))))
  have : n ∣ (∏ p ∈ P, p) * Dm M P := by
    rw [← lcm_eq_prod_mul_D hyp]; exact dvd_lcmTo hI.1 hI.2
  exact hcop.dvd_of_dvd_mul_left this

/-- `lcm(1,…,h)` divides `D`. -/
lemma lcmTo_h_dvd_D (hyp : Hyp M h P) : lcmTo h ∣ Dm M P := by
  have hfac : lcmTo h ∣ h.factorial := Finset.lcm_dvd (fun j hj => by
    have := Finset.mem_Icc.1 hj; exact Nat.dvd_factorial this.1 this.2)
  have hcop : Nat.Coprime (lcmTo h) (∏ p ∈ P, p) := Nat.Coprime.prod_right (fun p hp => by
    apply Nat.Coprime.coprime_dvd_left hfac
    rw [Nat.coprime_comm, (hyp.prime p hp).coprime_iff_not_dvd,
      (hyp.prime p hp).dvd_factorial]
    have := hyp.h_lt p hp; omega)
  have : lcmTo h ∣ (∏ p ∈ P, p) * Dm M P := by
    rw [← lcm_eq_prod_mul_D hyp]
    exact Finset.lcm_mono (fun j hj => by
      simp only [Finset.mem_Icc] at hj ⊢; exact ⟨hj.1, le_trans hj.2 hyp.h_le⟩)
  exact hcop.dvd_of_dvd_mul_left this

lemma D_eq_R_mul (hyp : Hyp M h P) : Dm M P = Rm M h P * lcmTo h :=
  (Nat.div_mul_cancel (lcmTo_h_dvd_D hyp)).symm

/-- Rows of distinct large primes are disjoint. -/
lemma rows_disjoint (hyp : Hyp M h P) {x : Finset ℕ} (hx : x ⊆ Finset.Icc 1 M) :
    (P : Set ℕ).PairwiseDisjoint (row x) := by
  classical
  intro p hp p' hp' hne
  rw [Function.onFun, Finset.disjoint_left]
  intro n hn hn'
  obtain ⟨hnx, hpn⟩ := Finset.mem_filter.1 hn
  obtain ⟨-, hpn'⟩ := Finset.mem_filter.1 hn'
  have hI := Finset.mem_Icc.1 (hx hnx)
  have hcop : Nat.Coprime p p' := (Nat.coprime_primes (hyp.prime p hp) (hyp.prime p' hp')).2 hne
  have hdvd : p * p' ∣ n := hcop.mul_dvd_of_dvd_of_dvd hpn hpn'
  have hle := Nat.le_of_dvd (by omega) hdvd
  have h1 := hyp.sq p hp
  have h2 := hyp.sq p' hp'
  rcases le_total p p' with hpp | hpp
  · have : p * p ≤ p * p' := Nat.mul_le_mul_left _ hpp; omega
  · have : p' * p' ≤ p * p' := Nat.mul_le_mul_right _ hpp; omega

/-- **Exact core/carry identity**: `S(x) = C/D + (1/Lh) ∑_p k_p` for legal rows. -/
theorem core_carry_identity (hyp : Hyp M h P) {x : Finset ℕ} (hx : x ⊆ Finset.Icc 1 M)
    (hleg : ∀ p ∈ P, p ∣ Arow h x p) :
    ∑ n ∈ x, (1 : ℚ) / n =
      (Cm M P x : ℚ) / Dm M P + (∑ p ∈ P, (kRow h x p : ℚ)) / lcmTo h := by
  classical
  have hD : (0 : ℚ) < Dm M P := by exact_mod_cast D_pos hyp
  have hL : (0 : ℚ) < lcmTo h := by exact_mod_cast lcmTo_pos h
  -- split `x` into the core and the rows
  have hsplit := Finset.sum_filter_add_sum_filter_not x (fun n => ∀ p ∈ P, ¬ p ∣ n)
    (fun n => (1 : ℚ) / n)
  have hrows : x.filter (fun n => ¬ ∀ p ∈ P, ¬ p ∣ n) = P.biUnion (row x) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_biUnion, row, not_forall, not_not]
    constructor
    · rintro ⟨hn, p, hp, hpn⟩; exact ⟨p, hp, hn, hpn⟩
    · rintro ⟨p, hp, hn, hpn⟩; exact ⟨hn, p, hp, hpn⟩
  rw [← hsplit, hrows, Finset.sum_biUnion (rows_disjoint hyp hx)]
  congr 1
  · -- core
    rw [Cm, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hdvd := dvd_D_of_core hyp hx hn
    have hn0 : (n : ℚ) ≠ 0 := by
      have := (Finset.mem_Icc.1 (hx (Finset.mem_filter.1 hn).1)).1
      exact_mod_cast (by omega : n ≠ 0)
    rw [Nat.cast_div hdvd hn0]
    field_simp
  · -- rows
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (hyp.prime p hp).ne_zero
    have hA : (Arow h x p : ℚ) = p * kRow h x p := by
      rw [kRow]; exact_mod_cast (Nat.mul_div_cancel' (hleg p hp)).symm
    have hrow : ∑ n ∈ row x p, (1 : ℚ) / n = (Arow h x p : ℚ) / (p * lcmTo h) := by
      rw [Arow, Nat.cast_sum, Finset.sum_div]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      obtain ⟨hnx, hpn⟩ := Finset.mem_filter.1 hn
      have hI := Finset.mem_Icc.1 (hx hnx)
      obtain ⟨m, rfl⟩ := hpn
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0, mul_zero] at hI; omega
        · exact h0
      have hmh : m ≤ h := by
        have := hyp.div_le p hp
        have : m ≤ M / p := by
          rw [Nat.le_div_iff_mul_le (hyp.prime p hp).pos, mul_comm]; exact hI.2
        omega
      rw [Nat.mul_div_cancel_left m (hyp.prime p hp).pos,
        Nat.cast_div (dvd_lcmTo hm1 hmh) (by exact_mod_cast (by omega : m ≠ 0))]
      have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      push_cast
      field_simp
    rw [hrow, hA]
    field_simp

/-- **Exact carry criterion**: `S(x) = 1 ↔ R ∣ C ∧ ∑_p k_p = Lh - C/R` (in `ℤ`). -/
theorem core_carry_iff (hyp : Hyp M h P) {x : Finset ℕ} (hx : x ⊆ Finset.Icc 1 M)
    (hleg : ∀ p ∈ P, p ∣ Arow h x p) :
    ∑ n ∈ x, (1 : ℚ) / n = 1 ↔
      Rm M h P ∣ Cm M P x ∧
        ((∑ p ∈ P, kRow h x p : ℕ) : ℤ) = (lcmTo h : ℤ) - ((Cm M P x / Rm M h P : ℕ) : ℤ) := by
  rw [core_carry_identity hyp hx hleg]
  have hDR := D_eq_R_mul hyp
  have hD : 0 < Dm M P := D_pos hyp
  have hL : 0 < lcmTo h := lcmTo_pos h
  have hR : 0 < Rm M h P := by
    rcases Nat.eq_zero_or_pos (Rm M h P) with h0 | h0
    · rw [h0, zero_mul] at hDR; omega
    · exact h0
  set C := Cm M P x
  set R := Rm M h P
  set L := lcmTo h
  set K := ∑ p ∈ P, kRow h x p
  have hKcast : (∑ p ∈ P, (kRow h x p : ℚ)) = (K : ℚ) := by simp [K]
  rw [hKcast, hDR]
  have hRq : (0 : ℚ) < R := by exact_mod_cast hR
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  have key : (C : ℚ) / (R * L : ℕ) + K / L = 1 ↔ C + R * K = R * L := by
    push_cast
    rw [div_add_div _ _ (by positivity) (by positivity), div_eq_one_iff_eq (by positivity)]
    constructor
    · intro h'
      have : ((C + R * K : ℕ) : ℚ) * L = ((R * L : ℕ) : ℚ) * L := by push_cast; nlinarith
      have := mul_right_cancel₀ hLq.ne' this
      exact_mod_cast this
    · intro h'
      have : ((C + R * K : ℕ) : ℚ) = ((R * L : ℕ) : ℚ) := by exact_mod_cast h'
      push_cast at this
      linear_combination (L : ℚ) * this
  rw [key]
  constructor
  · intro h'
    have hdvd : R ∣ C := ⟨L - K, by
      have : K ≤ L := by
        by_contra hc; push_neg at hc
        have : R * L < R * K := Nat.mul_lt_mul_of_pos_left hc hR
        omega
      rw [Nat.mul_sub]; omega⟩
    refine ⟨hdvd, ?_⟩
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, Nat.mul_div_cancel_left c hR]
    rw [hc] at h'
    have : c + K = L := by
      have : R * (c + K) = R * L := by rw [mul_add]; exact h'
      exact Nat.eq_of_mul_eq_mul_left hR this
    omega
  · rintro ⟨⟨c, hc⟩, hK⟩
    rw [hc, Nat.mul_div_cancel_left c hR] at hK
    rw [hc]
    have : c + K = L := by omega
    rw [← this, mul_add]

/-! ## Contact–carry bridge: weighted vertex covers -/

/-- Vertex set of the contact graph with edges `{n, n+1}`, `n ∈ Ed`. -/
def contactVertices (Ed : Finset ℕ) : Finset ℕ := Ed ∪ Ed.image (· + 1)

open Classical in
/-- The Boolean vertex covers of the contact graph. -/
noncomputable def covers (Ed : Finset ℕ) : Finset (Finset ℕ) :=
  (contactVertices Ed).powerset.filter (fun U => ∀ n ∈ Ed, n ∈ U ∨ n + 1 ∈ U)

lemma covers_nonempty (Ed : Finset ℕ) : (covers Ed).Nonempty := by
  classical
  refine ⟨contactVertices Ed, ?_⟩
  simp only [covers, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨subset_rfl, fun n hn => Or.inl (Finset.mem_union_left _ hn)⟩

/-- `τ(G_M)`: minimum selected reciprocal weight over Boolean vertex covers. -/
noncomputable def tauCover (Ed : Finset ℕ) : ℚ :=
  (covers Ed).inf' (covers_nonempty Ed) (fun U => ∑ u ∈ U, (1 : ℚ) / u)

/-- **Defect-free ⇒ selected contact mass `≥ τ(G)`.** -/
theorem cover_lower_bound (Ed x : Finset ℕ) (hdef : ∀ n ∈ Ed, n ∈ x ∨ n + 1 ∈ x) :
    tauCover Ed ≤ ∑ u ∈ x ∩ contactVertices Ed, (1 : ℚ) / u := by
  classical
  apply Finset.inf'_le
  simp only [covers, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨Finset.inter_subset_right, fun n hn => ?_⟩
  rcases hdef n hn with h | h
  · exact Or.inl (Finset.mem_inter.2 ⟨h, Finset.mem_union_left _ hn⟩)
  · exact Or.inr (Finset.mem_inter.2 ⟨h, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hn)⟩)

/-- **Path geometry**: if `M < 5 |Ed|` and all contact vertices lie in `[1, M]`, every cover has
reciprocal mass `> 1/10`; hence `τ(G) > 1/10`. -/
theorem tau_gt_tenth {M : ℕ} (Ed : Finset ℕ) (hV : ∀ u ∈ contactVertices Ed, 1 ≤ u ∧ u ≤ M)
    (hcount : M < 5 * Ed.card) : (1 : ℚ) / 10 < tauCover Ed := by
  classical
  rw [tauCover, Finset.lt_inf'_iff]
  intro U hU
  simp only [covers, Finset.mem_filter, Finset.mem_powerset] at hU
  obtain ⟨hUV, hcov⟩ := hU
  -- each vertex covers at most two edges
  set f : ℕ → ℕ := fun n => if n ∈ U then n else n + 1
  have hmaps : ∀ n ∈ Ed, f n ∈ U := by
    intro n hn; simp only [f]; split_ifs with h
    · exact h
    · exact (hcov n hn).resolve_left h
  have hfib : ∀ u ∈ U, (Ed.filter (fun n => f n = u)).card ≤ 2 := by
    intro u _
    have : Ed.filter (fun n => f n = u) ⊆ {u, u - 1} := by
      intro n hn
      obtain ⟨-, hfn⟩ := Finset.mem_filter.1 hn
      simp only [f] at hfn
      simp only [Finset.mem_insert, Finset.mem_singleton]
      split_ifs at hfn <;> omega
    exact (Finset.card_le_card this).trans (Finset.card_insert_le _ _)
  have hcard : Ed.card ≤ 2 * U.card := by
    have := Finset.card_le_mul_card_image_of_maps_to hmaps 2 hfib
    linarith
  have hM : (0 : ℚ) < M := by
    have : 0 < M := by
      rcases Ed.eq_empty_or_nonempty with h | ⟨n, hn⟩
      · rw [h] at hcount; simp at hcount
      · have := hV n (Finset.mem_union_left _ hn); omega
    exact_mod_cast this
  have hterm : ∀ u ∈ U, (1 : ℚ) / M ≤ 1 / u := by
    intro u hu
    have := hV u (hUV hu)
    apply one_div_le_one_div_of_le (by exact_mod_cast this.1) (by exact_mod_cast this.2)
  have hsum : (U.card : ℚ) * (1 / M) ≤ ∑ u ∈ U, (1 : ℚ) / u := by
    have := Finset.card_nsmul_le_sum U (fun u => (1 : ℚ) / u) (1 / M) hterm
    simpa [nsmul_eq_mul] using this
  have hc : (M : ℚ) < 5 * Ed.card := by exact_mod_cast hcount
  have hc2 : (Ed.card : ℚ) ≤ 2 * U.card := by exact_mod_cast hcard
  have : (1 : ℚ) / 10 < U.card * (1 / M) := by
    rw [div_lt_iff₀ (by norm_num), mul_one_div, div_mul_eq_mul_div, lt_div_iff₀ hM]
    linarith
  linarith

/-- Row mass of a legal configuration: `∑_{p} ∑_{row p} 1/n = K / Lh`. -/
theorem rows_mass (hyp : Hyp M h P) {x : Finset ℕ} (hx : x ⊆ Finset.Icc 1 M)
    (hleg : ∀ p ∈ P, p ∣ Arow h x p) :
    ∑ n ∈ P.biUnion (row x), (1 : ℚ) / n = (∑ p ∈ P, (kRow h x p : ℚ)) / lcmTo h := by
  classical
  have hid := core_carry_identity hyp hx hleg
  have hsplit := Finset.sum_filter_add_sum_filter_not x (fun n => ∀ p ∈ P, ¬ p ∣ n)
    (fun n => (1 : ℚ) / n)
  have hrows : x.filter (fun n => ¬ ∀ p ∈ P, ¬ p ∣ n) = P.biUnion (row x) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_biUnion, row, not_forall, not_not]
    constructor
    · rintro ⟨hn, p, hp, hpn⟩; exact ⟨p, hp, hn, hpn⟩
    · rintro ⟨p, hp, hn, hpn⟩; exact ⟨hn, p, hp, hpn⟩
  have hcore : ∑ n ∈ x.filter (fun n => ∀ p ∈ P, ¬ p ∣ n), (1 : ℚ) / n =
      (Cm M P x : ℚ) / Dm M P := by
    have hD : (0 : ℚ) < Dm M P := by exact_mod_cast D_pos hyp
    rw [Cm, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hdvd := dvd_D_of_core hyp hx hn
    have hn0 : (n : ℚ) ≠ 0 := by
      have := (Finset.mem_Icc.1 (hx (Finset.mem_filter.1 hn).1)).1
      exact_mod_cast (by omega : n ≠ 0)
    rw [Nat.cast_div hdvd hn0]
    field_simp
  rw [← hrows]
  rw [← hsplit, hcore] at hid
  linarith

/-- **Contact–carry lower bound**: defect-free on the contact graph, with every selected contact
vertex in some large-prime row, gives `K / Lh ≥ τ(G_M)`. -/
theorem contact_carry_lower_bound (hyp : Hyp M h P) {x : Finset ℕ} (hx : x ⊆ Finset.Icc 1 M)
    (hleg : ∀ p ∈ P, p ∣ Arow h x p) (Ed : Finset ℕ) (hdef : ∀ n ∈ Ed, n ∈ x ∨ n + 1 ∈ x)
    (hrow : ∀ u ∈ x ∩ contactVertices Ed, ∃ p ∈ P, p ∣ u) :
    tauCover Ed ≤ (∑ p ∈ P, (kRow h x p : ℚ)) / lcmTo h := by
  classical
  rw [← rows_mass hyp hx hleg]
  refine (cover_lower_bound Ed x hdef).trans ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro u hu
    obtain ⟨p, hp, hpu⟩ := hrow u hu
    exact Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_filter.2 ⟨(Finset.mem_inter.1 hu).1, hpu⟩⟩
  · intro _ _ _; positivity

/-- **Core cut** (exact PAY): if `S(x) = 1` and the row mass exceeds `1/10`, then
`C/D < 9/10` and `10 · (C/R) < 9 · Lh`. -/
theorem core_cut (hyp : Hyp M h P) {x : Finset ℕ} (hx : x ⊆ Finset.Icc 1 M)
    (hleg : ∀ p ∈ P, p ∣ Arow h x p) (hS : ∑ n ∈ x, (1 : ℚ) / n = 1)
    (hmass : (1 : ℚ) / 10 < (∑ p ∈ P, (kRow h x p : ℚ)) / lcmTo h) :
    (Cm M P x : ℚ) / Dm M P < 9 / 10 ∧ 10 * (Cm M P x / Rm M h P) < 9 * lcmTo h := by
  have hid := core_carry_identity hyp hx hleg
  refine ⟨by linarith, ?_⟩
  obtain ⟨-, hK⟩ := (core_carry_iff hyp hx hleg).1 hS
  have hL : (0 : ℚ) < lcmTo h := by exact_mod_cast lcmTo_pos h
  have hKq : (∑ p ∈ P, (kRow h x p : ℚ)) = ((∑ p ∈ P, kRow h x p : ℕ) : ℚ) := by rw [Nat.cast_sum]
  rw [hKq, lt_div_iff₀ hL] at hmass
  have hm : (lcmTo h : ℤ) < 10 * ((∑ p ∈ P, kRow h x p : ℕ) : ℤ) := by
    have : ((lcmTo h : ℕ) : ℚ) < 10 * ((∑ p ∈ P, kRow h x p : ℕ) : ℚ) := by linarith
    exact_mod_cast this
  have : (10 * (Cm M P x / Rm M h P) : ℤ) < 9 * lcmTo h := by omega
  exact_mod_cast this

/-- **Contact–carry cut** (combined): `S(x) = 1`, defect-free on a contact family with
`M < 5|E|` inside `[1, M]`, selected contact vertices in large-prime rows ⇒
`K/Lh > 1/10`, `C/D < 9/10` and `10 · (C/R) < 9 · Lh`. -/
theorem contact_carry_cut (hyp : Hyp M h P) {x : Finset ℕ} (hx : x ⊆ Finset.Icc 1 M)
    (hleg : ∀ p ∈ P, p ∣ Arow h x p) (hS : ∑ n ∈ x, (1 : ℚ) / n = 1) (Ed : Finset ℕ)
    (hV : ∀ u ∈ contactVertices Ed, 1 ≤ u ∧ u ≤ M) (hcount : M < 5 * Ed.card)
    (hdef : ∀ n ∈ Ed, n ∈ x ∨ n + 1 ∈ x) (hrow : ∀ u ∈ x ∩ contactVertices Ed, ∃ p ∈ P, p ∣ u) :
    (1 : ℚ) / 10 < (∑ p ∈ P, (kRow h x p : ℚ)) / lcmTo h ∧
      (Cm M P x : ℚ) / Dm M P < 9 / 10 ∧ 10 * (Cm M P x / Rm M h P) < 9 * lcmTo h := by
  have hmass := lt_of_lt_of_le (tau_gt_tenth Ed hV hcount)
    (contact_carry_lower_bound hyp hx hleg Ed hdef hrow)
  exact ⟨hmass, core_cut hyp hx hleg hS hmass⟩

end Erdos287.PostQSigma.CoreCarry
