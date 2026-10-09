import Mathlib

/-!
# Erdős #287 — post-`Q_Σ` bank, §22–§23: three-status generating functions and carry cosets

**Status: BANK (proved in Lean), as exact finite algebra.**

## §22 Three-status generating function

For an owner-disjoint matching edge `e = (p,q)` the contact endpoints carry a status
(`true` = selected, `false` = omitted).  Defect-freeness forbids the status `(false,false)`.
With status-conditioned row generating functions `F (p, s)` we put
`G_e = F_{p,1}F_{q,1} + F_{p,1}F_{q,0} + F_{p,0}F_{q,1}` and prove the exact factorisation
`∏_e G_e = ∑_{defect-free status assignments σ} ∏_e F_{p_e,σ₁(e)} F_{q_e,σ₂(e)}`.

**Relaxation.**  `∏_e G_e` treats different matching rows as independent: the path adjacency
constraints *between* rows and the coupling to the core are dropped.  It is therefore only an
upper relaxation.  The only sound use is the exclusion direction recorded in
`relaxed_coeff_zero_excludes`: if the true count is dominated coefficientwise by the relaxed
count and the relaxed coefficient vanishes, the true coefficient vanishes.

## §23 Status-conditioned carry cosets

A row with fixed contribution `A0` and variable cofactor reservoir `V` contributes the carry
`A0 + ∑_{j ∈ S} Lh/j` (`S ⊆ V`).  With `g = gcd {Lh/j : j ∈ V}` every such carry is
`≡ A0 (mod g)`, and `g = Lh / lcm V` (for nonempty `V`, all `j ∣ Lh`).  **Firewall:** if the
reservoir is LCM-complete (`lcm V = Lh`) then `g = 1` and the coset obstruction disappears.
These cosets are *not* claimed to be nontrivial in general.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma.StatusCarry

/-! ### §22 -/

/-- Defect-free statuses of a contact edge: not both endpoints omitted. -/
def allowed : Finset (Bool × Bool) := Finset.univ.filter (fun s => s.1 || s.2)

lemma allowed_eq : allowed = {(true, true), (true, false), (false, true)} := by decide

/-- Edge generating function `G_e`, as a sum over allowed statuses. -/
def Gedge {R ρ : Type*} [CommSemiring R] (F : ρ → Bool → R) (p q : ρ) : R :=
  ∑ s ∈ allowed, F p s.1 * F q s.2

/-- The explicit three-term form of `G_e`. -/
theorem Gedge_eq {R ρ : Type*} [CommSemiring R] (F : ρ → Bool → R) (p q : ρ) :
    Gedge F p q = F p true * F q true + F p true * F q false + F p false * F q true := by
  rw [Gedge, allowed_eq]
  simp [Finset.sum_insert, add_assoc]

/-- **Exact factorisation over owner-disjoint matching rows.** -/
theorem three_status_factorisation {R ρ E : Type*} [CommSemiring R] [Fintype E] [DecidableEq E]
    (F : ρ → Bool → R) (p q : E → ρ) :
    ∏ e, Gedge F (p e) (q e) =
      ∑ σ ∈ Fintype.piFinset (fun _ : E => allowed),
        ∏ e, F (p e) (σ e).1 * F (q e) (σ e).2 := by
  unfold Gedge
  exact Finset.prod_univ_sum (fun _ => allowed) (fun e s => F (p e) s.1 * F (q e) s.2)

/-- **Sound exclusion direction of the relaxation.** -/
theorem relaxed_coeff_zero_excludes (trueCount relaxed : ℕ → ℕ)
    (hdom : ∀ n, trueCount n ≤ relaxed n) (T : ℕ) (h0 : relaxed T = 0) : trueCount T = 0 := by
  have := hdom T; omega

/-! ### §23 -/

/-- The carry-coset modulus `g = gcd {Lh / j : j ∈ V}`. -/
def gco (Lh : ℕ) (V : Finset ℕ) : ℕ := V.gcd (fun j => Lh / j)

/-- The carry of a legal row with fixed part `A0` and variable selection `S ⊆ V`. -/
def carry (Lh A0 : ℕ) (S : Finset ℕ) : ℕ := A0 + ∑ j ∈ S, Lh / j

/-- **Every legal status-`s` carry lies in the coset `A0 mod g`.** -/
theorem carry_modEq (Lh A0 : ℕ) (V S : Finset ℕ) (hS : S ⊆ V) :
    carry Lh A0 S ≡ A0 [MOD gco Lh V] := by
  have hd : gco Lh V ∣ ∑ j ∈ S, Lh / j :=
    Finset.dvd_sum (fun j hj => Finset.gcd_dvd (hS hj))
  unfold carry
  have := (Nat.modEq_zero_iff_dvd.2 hd).add_left A0
  simpa using this

/-- `g = Lh / lcm V` for a nonempty reservoir of divisors of `Lh > 0`. -/
theorem gco_eq (Lh : ℕ) (hL : 0 < Lh) (V : Finset ℕ) (hV : V.Nonempty)
    (hdvd : ∀ j ∈ V, j ∣ Lh) : gco Lh V = Lh / V.lcm id := by
  set g := gco Lh V
  set l := V.lcm id
  have hl : l ∣ Lh := Finset.lcm_dvd (fun j hj => hdvd j hj)
  have hpos : ∀ j ∈ V, 0 < Lh / j := by
    intro j hj
    exact Nat.div_pos (Nat.le_of_dvd hL (hdvd j hj))
      (Nat.pos_of_dvd_of_pos (hdvd j hj) hL)
  have hg0 : g ≠ 0 := by
    obtain ⟨j, hj⟩ := hV
    intro h
    have : g ∣ Lh / j := Finset.gcd_dvd hj
    rw [h, zero_dvd_iff] at this
    exact (hpos j hj).ne' this
  have hgL : g ∣ Lh := by
    obtain ⟨j, hj⟩ := hV
    exact (Finset.gcd_dvd hj).trans (Nat.div_dvd_of_dvd (hdvd j hj))
  -- `Lh / l ∣ g`
  have h1 : Lh / l ∣ g := by
    apply Finset.dvd_gcd
    intro j hj
    have hjl : j ∣ l := Finset.dvd_lcm (s := V) (f := id) hj
    obtain ⟨c, hc⟩ := hjl
    have hj0 : 0 < j := Nat.pos_of_dvd_of_pos (hdvd j hj) hL
    refine ⟨c, ?_⟩
    have hLm : Lh = j * (Lh / l * c) := by
      calc Lh = l * (Lh / l) := (Nat.mul_div_cancel' hl).symm
        _ = j * (Lh / l * c) := by rw [hc]; ring
    conv_lhs => rw [hLm]
    exact Nat.mul_div_cancel_left _ hj0
  -- `l ∣ Lh / g`
  have h2 : l ∣ Lh / g := by
    apply Finset.lcm_dvd
    intro j hj
    obtain ⟨c, hc⟩ : g ∣ Lh / j := Finset.gcd_dvd hj
    have hLj : Lh = j * (g * c) := by
      rw [← hc]; exact (Nat.mul_div_cancel' (hdvd j hj)).symm
    refine ⟨c, ?_⟩
    rw [hLj, show j * (g * c) = g * (j * c) by ring, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hg0)]
    rfl
  have h3 : g ∣ Lh / l := by
    obtain ⟨c, hc⟩ := h2
    have hLg : Lh = g * (l * c) := by rw [← hc]; exact (Nat.mul_div_cancel' hgL).symm
    have hl0 : 0 < l := Nat.pos_of_dvd_of_pos hl hL
    refine ⟨c, ?_⟩
    rw [hLg, show g * (l * c) = l * (g * c) by ring, Nat.mul_div_cancel_left _ hl0]
  exact Nat.dvd_antisymm h3 h1

/-- **Firewall: an LCM-complete reservoir has trivial carry coset.** -/
theorem gco_eq_one_of_lcm_complete (Lh : ℕ) (hL : 0 < Lh) (V : Finset ℕ) (hV : V.Nonempty)
    (hdvd : ∀ j ∈ V, j ∣ Lh) (hcomplete : V.lcm id = Lh) : gco Lh V = 1 := by
  rw [gco_eq Lh hL V hV hdvd, hcomplete, Nat.div_self hL]

/-- **Edge-support containment in the union of the three allowed cosets.**  If the two
endpoint rows of an edge have carries in their status cosets and the status pair is allowed,
the edge carry lies in one of the three cosets `A0_{p,s} + A0_{q,t} mod gcd(g_{p,s}, g_{q,t})`. -/
theorem edge_carry_mem_cosets (A0p A0q gp gq : Bool → ℕ) (s : Bool × Bool) (hs : s ∈ allowed)
    (cp cq : ℕ) (hp : cp ≡ A0p s.1 [MOD gp s.1]) (hq : cq ≡ A0q s.2 [MOD gq s.2]) :
    ∃ t ∈ allowed, cp + cq ≡ A0p t.1 + A0q t.2 [MOD Nat.gcd (gp t.1) (gq t.2)] :=
  ⟨s, hs, Nat.ModEq.add
    (Nat.ModEq.of_dvd (Nat.gcd_dvd_left _ _) hp) (Nat.ModEq.of_dvd (Nat.gcd_dvd_right _ _) hq)⟩

/-- **Regression fixture (status-coset `g = 1` degeneration).**  With `Lh = 12` and the
LCM-complete reservoir `{3, 4}` the coset modulus is `gcd(4, 3) = 1`. -/
theorem fixture_g_one : gco 12 {3, 4} = 1 := by decide

/-- A non-complete reservoir can give a nontrivial coset: `Lh = 12`, `V = {2, 4}`, `g = 3`. -/
theorem fixture_g_three : gco 12 {2, 4} = 3 := by decide

end Erdos287.PostQSigma.StatusCarry
