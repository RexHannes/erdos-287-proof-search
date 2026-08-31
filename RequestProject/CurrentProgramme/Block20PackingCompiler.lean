import Mathlib
import RequestProject.CurrentProgramme.FixedCertificateBalancedSevenSourceSeal
import RequestProject.CurrentProgramme.SmallPrimePrefix

/-!
# BLOCK20 Δ, Phase B (§3–§5) — parameter ledger, procedural greedy packing, source split

**Append-only.**  Nothing historical is modified.

## §3  Parameter ledger

The exact repository parameter `ν₀ = 16623/100000` (`Erdos287.FordData.nu0`) is reused —
*not* replaced by `1/6`.  With `0 < ε_* ≤ ν₀/100` and `σ_* = ν₀ − 2ε_*` we prove the exact
rational bound `σ_* ≥ 0.1629054` (`sigmaStar_ge`), the contradiction inequality
`19·(σ_*/3) > 1` (`nineteen_blocks_overflow`), and record that `ε_* = 1/600` is **not** an
admissible endpoint (`eps_one_over_600_not_admissible`).

## §4  The procedural greedy rule

The packing is a **procedure**, not a classification by numeric range:

* STEP 1 — every atom of mass `> σ_*/3` becomes a singleton block (`bigAtoms`);
* STEP 2 — the remaining atoms (each `≤ σ_*/3`) are accumulated *in the given order* until
  the running sum first reaches `σ_*/3` (`groupSmall`);
* STEP 3 — at most one final leftover, of mass `< σ_*/3`, remains per side.

`packSide` implements one side, `packBoth` the two sides separately, and
`packBoth_validity` **constructs** an inhabitant of `Block20PackingValidity` from the actual
algorithm.  The validity structure is a genuine restriction
(`block20Validity_not_automatic`).

## §5  Source factorisation

The smooth/rough split at `z₀ = X^{1/420}` is reused from
`Erdos287.PostBalanced7Pro` (`coprime_smooth_rough` — the `gcd(d,m) = 1` bank), the finite
implication `Ω(m) ≤ 420` is proved (`bigOmega_rough_le_420`), and the truncated Möbius
divisor factorisation

```
M_γ(dm) = ∑_{e_d ∣ d} μ(e_d) ∑_{e_m ∣ m, e_d e_m ≤ (dm)^γ} μ(e_m)
```

is kernel-proved (`truncMobius_coprime_split`, `truncMobius_gamma_split`).  This does **not**
contradict the banked non-factorisation obstruction
`truncMoebius_not_prefix_factorisable`: the inner cut still couples `e_d` and `e_m`.

No analytic prime counting occurs in this module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open ArithmeticFunction

namespace Erdos287
namespace Block20

/-! ## §3  The constant / parameter ledger -/

/-- The exact repository parameter `ν₀ = 16623/100000`. -/
def nu0Q : ℚ := Erdos287.FordData.nu0

/-- **`nu0Q_value`.**  `LEAN_PROVED`. -/
theorem nu0Q_value : nu0Q = 16623 / 100000 := rfl

/-- **`nu0Q_ne_one_sixth`.**  `LEAN_PROVED`.  `ν₀` is *not* `1/6`. -/
theorem nu0Q_ne_one_sixth : nu0Q ≠ 1 / 6 := by
  rw [nu0Q_value]; norm_num

/-- `σ_* = ν₀ − 2ε_*`. -/
def sigmaStarQ (epsStar : ℚ) : ℚ := nu0Q - 2 * epsStar

/-- The admissible range of `ε_*`: `0 < ε_* ≤ ν₀/100`. -/
def EpsAdmissible (epsStar : ℚ) : Prop := 0 < epsStar ∧ epsStar ≤ nu0Q / 100

/-- **`sigmaStar_ge`.**  `LEAN_PROVED`.

The mandated exact rational inequality `σ_* ≥ 0.1629054`. -/
theorem sigmaStar_ge {epsStar : ℚ} (h : EpsAdmissible epsStar) :
    (1629054 : ℚ) / 10000000 ≤ sigmaStarQ epsStar := by
  obtain ⟨_, h2⟩ := h
  rw [sigmaStarQ, nu0Q_value]
  rw [nu0Q_value] at h2
  linarith

/-- **`sigmaStar_pos`.**  `LEAN_PROVED`. -/
theorem sigmaStar_pos {epsStar : ℚ} (h : EpsAdmissible epsStar) : 0 < sigmaStarQ epsStar :=
  lt_of_lt_of_le (by norm_num) (sigmaStar_ge h)

/-- **`sigmaStar_le_nu0`.**  `LEAN_PROVED`. -/
theorem sigmaStar_le_nu0 {epsStar : ℚ} (h : EpsAdmissible epsStar) :
    sigmaStarQ epsStar < nu0Q := by
  have := h.1
  rw [sigmaStarQ]
  linarith

/-- **`eps_one_over_600_not_admissible`.**  `LEAN_PROVED`.

`ε_* = 1/600` is **not** an admissible endpoint: `1/600 > ν₀/100`. -/
theorem eps_one_over_600_not_admissible : ¬ EpsAdmissible (1 / 600) := by
  rintro ⟨-, h⟩
  rw [nu0Q_value] at h
  norm_num at h

/-- **`nineteen_blocks_overflow`.**  `LEAN_PROVED`.

The exact rational contradiction route: nineteen non-final blocks already carry more than
the whole available mass, `19·(σ_*/3) > 1`. -/
theorem nineteen_blocks_overflow {epsStar : ℚ} (h : EpsAdmissible epsStar) :
    1 < 19 * (sigmaStarQ epsStar / 3) := by
  have := sigmaStar_ge h
  linarith

/-! ## §4  The procedural greedy packing -/

/-- The mass of a list of blocks. -/
def blocksMass (bs : List (List ℝ)) : ℝ := (bs.map List.sum).sum

/-- **`blocksMass_append`.**  `LEAN_PROVED`. -/
theorem blocksMass_append (bs cs : List (List ℝ)) :
    blocksMass (bs ++ cs) = blocksMass bs + blocksMass cs := by
  simp [blocksMass, List.sum_append]

/-- **`blocksMass_eq_flatten_sum`.**  `LEAN_PROVED`. -/
theorem blocksMass_eq_flatten_sum (bs : List (List ℝ)) : blocksMass bs = bs.flatten.sum := by
  simp [blocksMass, List.sum_flatten]

/-- **`blocksMass_ge`.**  `LEAN_PROVED`.  `thr · (#blocks) ≤ total block mass`. -/
theorem blocksMass_ge (thr : ℝ) (bs : List (List ℝ)) (h : ∀ b ∈ bs, thr ≤ b.sum) :
    thr * bs.length ≤ blocksMass bs := by
  induction bs with
  | nil => simp [blocksMass]
  | cons b rest ih =>
      have hb := h b (List.mem_cons_self ..)
      have hr := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
      simp only [blocksMass, List.map_cons, List.sum_cons, List.length_cons] at *
      push_cast
      linarith

/-- **`nonfinal_block_count_le_18`.**  `LEAN_PROVED`.

The arithmetic count lemma, with no floor arithmetic: if every listed (non-final) block has
mass at least `σ_*/3`, `σ_* ≥ 0.1629054`, and the total block mass is at most `1`, then there
are at most `18` such blocks. -/
theorem nonfinal_block_count_le_18 (sigma thr : ℝ) (bs : List (List ℝ))
    (hsig : (1629054 : ℝ) / 10000000 ≤ sigma) (hthr : thr = sigma / 3)
    (h : ∀ b ∈ bs, thr ≤ b.sum) (htot : blocksMass bs ≤ 1) : bs.length ≤ 18 := by
  by_contra hc
  push_neg at hc
  have h19 : (19 : ℝ) ≤ (bs.length : ℝ) := by exact_mod_cast hc
  have hthrpos : (0 : ℝ) < thr := by rw [hthr]; linarith
  have hmass := blocksMass_ge thr bs h
  nlinarith

open Classical in
/-- STEP 1 — the atoms that become singleton blocks. -/
noncomputable def bigAtoms (thr : ℝ) (l : List ℝ) : List ℝ := l.filter (fun a => decide (thr < a))

open Classical in
/-- The atoms that enter STEP 2. -/
noncomputable def smallAtoms (thr : ℝ) (l : List ℝ) : List ℝ :=
  l.filter (fun a => !decide (thr < a))

/-- **`mem_bigAtoms`.**  `LEAN_PROVED`. -/
theorem mem_bigAtoms {thr : ℝ} {l : List ℝ} {a : ℝ} (h : a ∈ bigAtoms thr l) :
    a ∈ l ∧ thr < a := by
  classical
  simpa [bigAtoms, List.mem_filter] using h

/-- **`mem_smallAtoms`.**  `LEAN_PROVED`. -/
theorem mem_smallAtoms {thr : ℝ} {l : List ℝ} {a : ℝ} (h : a ∈ smallAtoms thr l) :
    a ∈ l ∧ a ≤ thr := by
  classical
  have := h
  simp only [smallAtoms, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not,
    not_lt] at this
  exact this

/-- **`bigAtoms_append_smallAtoms_perm`.**  `LEAN_PROVED`.  STEP 1 and STEP 2 partition the
input: no atom is lost and no atom is duplicated. -/
theorem bigAtoms_append_smallAtoms_perm (thr : ℝ) (l : List ℝ) :
    (bigAtoms thr l ++ smallAtoms thr l).Perm l := by
  classical
  simpa [bigAtoms, smallAtoms] using List.filter_append_perm (fun a => decide (thr < a)) l

open Classical in
/-- STEP 2 — the greedy accumulation, in the given order, until the running sum first
reaches the threshold.  Returns the completed blocks and the final leftover. -/
noncomputable def groupSmall (thr : ℝ) : List ℝ → List ℝ → List (List ℝ) × List ℝ
  | [], acc => ([], acc.reverse)
  | a :: rest, acc =>
      if thr ≤ acc.sum + a then
        ((acc.reverse ++ [a]) :: (groupSmall thr rest []).1, (groupSmall thr rest []).2)
      else groupSmall thr rest (a :: acc)

/-- **`groupSmall_flatten`.**  `LEAN_PROVED`.  Exact conservation: the completed blocks and
the leftover reassemble the input, *in order*. -/
theorem groupSmall_flatten (thr : ℝ) (l acc : List ℝ) :
    (groupSmall thr l acc).1.flatten ++ (groupSmall thr l acc).2 = acc.reverse ++ l := by
  induction l generalizing acc with
  | nil => simp [groupSmall]
  | cons a rest ih =>
      by_cases h : thr ≤ acc.sum + a
      · simp only [groupSmall, if_pos h, List.flatten_cons, List.append_assoc]
        rw [ih (acc := [])]
        simp
      · simp only [groupSmall, if_neg h]
        rw [ih (acc := a :: acc)]
        simp

/-- **`groupSmall_block_ge`.**  `LEAN_PROVED`.  Every completed block has mass `≥ thr`. -/
theorem groupSmall_block_ge (thr : ℝ) (l acc : List ℝ) :
    ∀ b ∈ (groupSmall thr l acc).1, thr ≤ b.sum := by
  induction l generalizing acc with
  | nil => simp [groupSmall]
  | cons a rest ih =>
      by_cases h : thr ≤ acc.sum + a
      · simp only [groupSmall, if_pos h, List.mem_cons]
        rintro b (rfl | hb)
        · simpa [List.sum_append] using h
        · exact ih [] b hb
      · simp only [groupSmall, if_neg h]
        exact ih (a :: acc)

/-- **`groupSmall_leftover_lt`.**  `LEAN_PROVED`.  The single leftover has mass `< thr`. -/
theorem groupSmall_leftover_lt (thr : ℝ) (hthr : 0 < thr) (l : List ℝ) :
    ∀ acc : List ℝ, acc.sum < thr → (groupSmall thr l acc).2.sum < thr := by
  induction l with
  | nil => intro acc h; simpa [groupSmall] using h
  | cons a rest ih =>
      intro acc hacc
      by_cases h : thr ≤ acc.sum + a
      · simp only [groupSmall, if_pos h]
        exact ih [] (by simpa using hthr)
      · simp only [groupSmall, if_neg h]
        refine ih (a :: acc) ?_
        simp only [List.sum_cons]
        linarith [not_le.mp h]

/-- **`groupSmall_block_le`.**  `LEAN_PROVED`.  No completed block exceeds `2·thr`. -/
theorem groupSmall_block_le (thr : ℝ) (l : List ℝ) (hl : ∀ x ∈ l, x ≤ thr) :
    ∀ acc : List ℝ, acc.sum < thr → ∀ b ∈ (groupSmall thr l acc).1, b.sum ≤ 2 * thr := by
  induction l with
  | nil => intro acc h; simp [groupSmall]
  | cons a rest ih =>
      intro acc hacc
      have hall : ∀ x ∈ rest, x ≤ thr := fun x hx => hl x (List.mem_cons_of_mem _ hx)
      have ha : a ≤ thr := hl a (List.mem_cons_self ..)
      by_cases h : thr ≤ acc.sum + a
      · simp only [groupSmall, if_pos h, List.mem_cons]
        rintro b (rfl | hb)
        · have hsum : (acc.reverse ++ [a]).sum = acc.sum + a := by simp [List.sum_append]
          rw [hsum]; linarith
        · exact ih hall [] (by simpa using (by linarith : (0 : ℝ) < thr)) b hb
      · simp only [groupSmall, if_neg h]
        refine ih hall (a :: acc) ?_
        simp only [List.sum_cons]
        linarith [not_le.mp h]

/-! ### One side of the packing -/

/-- The output of the packing procedure on one side. -/
structure SidePacking where
  /-- The blocks produced (singletons first, then the greedy groups). -/
  blocks : List (List ℝ)
  /-- The single final leftover. -/
  leftover : List ℝ

/-- The procedural packing of one side. -/
noncomputable def packSide (thr : ℝ) (l : List ℝ) : SidePacking where
  blocks := (bigAtoms thr l).map (fun a => [a]) ++ (groupSmall thr (smallAtoms thr l) []).1
  leftover := (groupSmall thr (smallAtoms thr l) []).2

/-- **`packSide_perm`.**  `LEAN_PROVED`.

**Conservation.**  Every atom is assigned exactly once: blocks and leftover together are a
permutation of the input, so nothing is lost and nothing is duplicated. -/
theorem packSide_perm (thr : ℝ) (l : List ℝ) :
    ((packSide thr l).blocks.flatten ++ (packSide thr l).leftover).Perm l := by
  classical
  have h0 : ((bigAtoms thr l).map (fun a => [a])).flatten = bigAtoms thr l := by
    induction bigAtoms thr l with
    | nil => simp
    | cons a t ih => simp [ih]
  have h2 : (groupSmall thr (smallAtoms thr l) []).1.flatten
        ++ (groupSmall thr (smallAtoms thr l) []).2 = smallAtoms thr l := by
    simpa using groupSmall_flatten thr (smallAtoms thr l) []
  have h1 : ((packSide thr l).blocks.flatten ++ (packSide thr l).leftover)
      = bigAtoms thr l ++ smallAtoms thr l := by
    simp only [packSide, List.flatten_append, h0, List.append_assoc, h2]
  rw [h1]
  exact bigAtoms_append_smallAtoms_perm thr l

/-- **`packSide_mem`.**  `LEAN_PROVED`.  **Provenance / no straddling.**  Every atom in a
block of this side comes from this side's input list. -/
theorem packSide_mem {thr : ℝ} {l : List ℝ} {b : List ℝ} {x : ℝ}
    (hb : b ∈ (packSide thr l).blocks) (hx : x ∈ b) : x ∈ l := by
  have hperm := packSide_perm thr l
  have : x ∈ (packSide thr l).blocks.flatten ++ (packSide thr l).leftover := by
    exact List.mem_append_left _ (List.mem_flatten.mpr ⟨b, hb, hx⟩)
  exact hperm.mem_iff.mp this

/-- **`packSide_leftover_mem`.**  `LEAN_PROVED`. -/
theorem packSide_leftover_mem {thr : ℝ} {l : List ℝ} {x : ℝ}
    (hx : x ∈ (packSide thr l).leftover) : x ∈ l := by
  have hperm := packSide_perm thr l
  exact hperm.mem_iff.mp (List.mem_append_right _ hx)

/-- **`packSide_block_ge`.**  `LEAN_PROVED`.  Every block (singleton or grouped) has mass at
least the threshold. -/
theorem packSide_block_ge (thr : ℝ) (l : List ℝ) :
    ∀ b ∈ (packSide thr l).blocks, thr ≤ b.sum := by
  intro b hb
  simp only [packSide, List.mem_append, List.mem_map] at hb
  rcases hb with ⟨a, ha, rfl⟩ | hb
  · simpa using (mem_bigAtoms ha).2.le
  · exact groupSmall_block_ge thr (smallAtoms thr l) [] b hb

/-- **`packSide_block_le`.**  `LEAN_PROVED`.  With every atom of mass at most `σ` and
`2·thr ≤ σ`, every block has mass at most `σ`. -/
theorem packSide_block_le (thr sigma : ℝ) (l : List ℝ) (hthr : 0 < thr)
    (h2 : 2 * thr ≤ sigma) (hatoms : ∀ x ∈ l, x ≤ sigma) :
    ∀ b ∈ (packSide thr l).blocks, b.sum ≤ sigma := by
  intro b hb
  simp only [packSide, List.mem_append, List.mem_map] at hb
  rcases hb with ⟨a, ha, rfl⟩ | hb
  · simpa using hatoms a (mem_bigAtoms ha).1
  · refine le_trans ?_ h2
    exact groupSmall_block_le thr (smallAtoms thr l)
      (fun x hx => (mem_smallAtoms hx).2) [] (by simpa using hthr) b hb

/-- **`packSide_leftover_lt`.**  `LEAN_PROVED`.  At most one leftover per side, of mass
`< thr`. -/
theorem packSide_leftover_lt (thr : ℝ) (hthr : 0 < thr) (l : List ℝ) :
    (packSide thr l).leftover.sum < thr :=
  groupSmall_leftover_lt thr hthr (smallAtoms thr l) [] (by simpa using hthr)

/-- **`packSide_singleton_provenance`.**  `LEAN_PROVED`.  The singleton blocks are exactly
the STEP-1 atoms, and each really is above the threshold. -/
theorem packSide_singleton_provenance (thr : ℝ) (l : List ℝ) :
    ∀ b ∈ (bigAtoms thr l).map (fun a => [a]), ∃ a, b = [a] ∧ a ∈ l ∧ thr < a := by
  intro b hb
  simp only [List.mem_map] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  exact ⟨a, rfl, (mem_bigAtoms ha).1, (mem_bigAtoms ha).2⟩

/-- **`packSide_grouped_provenance`.**  `LEAN_PROVED`.  Every atom of a grouped block is a
STEP-2 atom, i.e. is at most the threshold: singleton and grouped provenance never mix. -/
theorem packSide_grouped_provenance (thr : ℝ) (l : List ℝ) :
    ∀ b ∈ (groupSmall thr (smallAtoms thr l) []).1, ∀ x ∈ b, x ≤ thr := by
  intro b hb x hx
  have hflat : (groupSmall thr (smallAtoms thr l) []).1.flatten
      ++ (groupSmall thr (smallAtoms thr l) []).2 = smallAtoms thr l := by
    simpa using groupSmall_flatten thr (smallAtoms thr l) []
  have hmem : x ∈ smallAtoms thr l := by
    have hx2 : x ∈ (groupSmall thr (smallAtoms thr l) []).1.flatten :=
      List.mem_flatten.mpr ⟨b, hb, hx⟩
    have hx3 : x ∈ (groupSmall thr (smallAtoms thr l) []).1.flatten
        ++ (groupSmall thr (smallAtoms thr l) []).2 := List.mem_append_left _ hx2
    rwa [hflat] at hx3
  exact (mem_smallAtoms hmem).2

/-- **`packSide_mass_le`.**  `LEAN_PROVED`.  The total block mass of a side is at most the
side's total mass (the leftover is nonnegative). -/
theorem packSide_mass_le (thr : ℝ) (l : List ℝ) (hnn : ∀ x ∈ l, 0 ≤ x) :
    blocksMass (packSide thr l).blocks ≤ l.sum := by
  have hperm := packSide_perm thr l
  have hsum : (packSide thr l).blocks.flatten.sum + (packSide thr l).leftover.sum = l.sum := by
    have := hperm.sum_eq
    rwa [List.sum_append] at this
  have hleft : 0 ≤ (packSide thr l).leftover.sum := by
    refine List.sum_nonneg ?_
    intro x hx
    exact hnn x (packSide_leftover_mem hx)
  rw [blocksMass_eq_flatten_sum]
  linarith

/-! ### The two-sided Block20 packing -/

/-- The two-sided packing: the `d`-side and the `m`-side are packed **separately**. -/
structure Block20Packing where
  /-- The `d`-side packing. -/
  dSide : SidePacking
  /-- The `m`-side packing. -/
  mSide : SidePacking

/-- The procedural two-sided packing. -/
noncomputable def packBoth (thr : ℝ) (ld lm : List ℝ) : Block20Packing where
  dSide := packSide thr ld
  mSide := packSide thr lm

/-- **`packBoth_no_straddle`.**  `LEAN_PROVED`.

No block straddles the `d`/`m` divide: atoms of a `d`-block come from the `d`-list and atoms
of an `m`-block from the `m`-list. -/
theorem packBoth_no_straddle (thr : ℝ) (ld lm : List ℝ) :
    (∀ b ∈ (packBoth thr ld lm).dSide.blocks, ∀ x ∈ b, x ∈ ld) ∧
      (∀ b ∈ (packBoth thr ld lm).mSide.blocks, ∀ x ∈ b, x ∈ lm) :=
  ⟨fun _ hb _ hx => packSide_mem hb hx, fun _ hb _ hx => packSide_mem hb hx⟩

/-- **`packBoth_nonfinal_count_le_18`.**  `LEAN_PROVED`.

The block count bound.  With `σ ≥ 0.1629054`, `thr = σ/3`, nonnegative atoms and total mass
at most `1`, the two sides together produce at most `18` non-final blocks. -/
theorem packBoth_nonfinal_count_le_18 (sigma thr : ℝ) (ld lm : List ℝ)
    (hsig : (1629054 : ℝ) / 10000000 ≤ sigma) (hthr : thr = sigma / 3)
    (hnnd : ∀ x ∈ ld, 0 ≤ x) (hnnm : ∀ x ∈ lm, 0 ≤ x)
    (htot : ld.sum + lm.sum ≤ 1) :
    (packBoth thr ld lm).dSide.blocks.length + (packBoth thr ld lm).mSide.blocks.length ≤ 18 := by
  have hall : ∀ b ∈ (packSide thr ld).blocks ++ (packSide thr lm).blocks, thr ≤ b.sum := by
    intro b hb
    rcases List.mem_append.mp hb with h | h
    · exact packSide_block_ge thr ld b h
    · exact packSide_block_ge thr lm b h
  have hmass : blocksMass ((packSide thr ld).blocks ++ (packSide thr lm).blocks) ≤ 1 := by
    rw [blocksMass_append]
    have h1 := packSide_mass_le thr ld hnnd
    have h2 := packSide_mass_le thr lm hnnm
    linarith
  have := nonfinal_block_count_le_18 sigma thr
    ((packSide thr ld).blocks ++ (packSide thr lm).blocks) hsig hthr hall hmass
  simpa [packBoth, List.length_append] using this

/-- **`packBoth_total_count_le_20`.**  `LEAN_PROVED`.

Counting the (at most two) leftovers, the total block count is at most `20`. -/
theorem packBoth_total_count_le_20 (sigma thr : ℝ) (ld lm : List ℝ)
    (hsig : (1629054 : ℝ) / 10000000 ≤ sigma) (hthr : thr = sigma / 3)
    (hnnd : ∀ x ∈ ld, 0 ≤ x) (hnnm : ∀ x ∈ lm, 0 ≤ x)
    (htot : ld.sum + lm.sum ≤ 1) :
    (packBoth thr ld lm).dSide.blocks.length + (packBoth thr ld lm).mSide.blocks.length + 2
      ≤ 20 := by
  have := packBoth_nonfinal_count_le_18 sigma thr ld lm hsig hthr hnnd hnnm htot
  omega

/-! ### The validity certificate -/

/-- **`Block20PackingValidity`** — the packing contract.  It is *not* a socket: the actual
algorithm constructs an inhabitant (`packBoth_validity`), and the contract is a genuine
restriction (`block20Validity_not_automatic`). -/
structure Block20PackingValidity (sigma thr : ℝ) (ld lm : List ℝ) (P : Block20Packing) : Prop where
  /-- Conservation on the `d`-side: every atom assigned exactly once. -/
  d_conservation : (P.dSide.blocks.flatten ++ P.dSide.leftover).Perm ld
  /-- Conservation on the `m`-side. -/
  m_conservation : (P.mSide.blocks.flatten ++ P.mSide.leftover).Perm lm
  /-- No block straddles the `d`/`m` divide. -/
  no_straddle : (∀ b ∈ P.dSide.blocks, ∀ x ∈ b, x ∈ ld) ∧
    (∀ b ∈ P.mSide.blocks, ∀ x ∈ b, x ∈ lm)
  /-- Every non-final block has mass at least `σ/3`. -/
  nonfinal_ge : (∀ b ∈ P.dSide.blocks, thr ≤ b.sum) ∧ (∀ b ∈ P.mSide.blocks, thr ≤ b.sum)
  /-- Every block has mass at most `σ`. -/
  block_le : (∀ b ∈ P.dSide.blocks, b.sum ≤ sigma) ∧ (∀ b ∈ P.mSide.blocks, b.sum ≤ sigma)
  /-- At most two leftovers globally, each of mass below the threshold. -/
  leftover_lt : P.dSide.leftover.sum < thr ∧ P.mSide.leftover.sum < thr
  /-- The total block count is at most `20`. -/
  count_le_20 : P.dSide.blocks.length + P.mSide.blocks.length + 2 ≤ 20

/-- **`packBoth_validity`.**  `LEAN_PROVED`.

**The constructive finite packing theorem.**  The procedural greedy rule really does satisfy
the whole Block20 contract. -/
theorem packBoth_validity (sigma thr : ℝ) (ld lm : List ℝ)
    (hsig : (1629054 : ℝ) / 10000000 ≤ sigma) (hthr : thr = sigma / 3)
    (hnnd : ∀ x ∈ ld, 0 ≤ x) (hnnm : ∀ x ∈ lm, 0 ≤ x)
    (hatd : ∀ x ∈ ld, x ≤ sigma) (hatm : ∀ x ∈ lm, x ≤ sigma)
    (htot : ld.sum + lm.sum ≤ 1) :
    Block20PackingValidity sigma thr ld lm (packBoth thr ld lm) := by
  have hthrpos : 0 < thr := by rw [hthr]; linarith
  have h2thr : 2 * thr ≤ sigma := by rw [hthr]; linarith
  exact
    { d_conservation := packSide_perm thr ld
      m_conservation := packSide_perm thr lm
      no_straddle := packBoth_no_straddle thr ld lm
      nonfinal_ge := ⟨packSide_block_ge thr ld, packSide_block_ge thr lm⟩
      block_le := ⟨packSide_block_le thr sigma ld hthrpos h2thr hatd,
        packSide_block_le thr sigma lm hthrpos h2thr hatm⟩
      leftover_lt := ⟨packSide_leftover_lt thr hthrpos ld, packSide_leftover_lt thr hthrpos lm⟩
      count_le_20 := packBoth_total_count_le_20 sigma thr ld lm hsig hthr hnnd hnnm htot }

/-- **`block20Validity_not_automatic`.**  `LEAN_PROVED`.

The validity contract is not vacuous: an arbitrary "packing" fails it. -/
theorem block20Validity_not_automatic :
    ∃ (sigma thr : ℝ) (ld lm : List ℝ) (P : Block20Packing),
      ¬ Block20PackingValidity sigma thr ld lm P := by
  refine ⟨1, 1, [1], [], ⟨⟨[], []⟩, ⟨[], []⟩⟩, ?_⟩
  intro h
  have := h.d_conservation
  simp only [List.flatten_nil, List.append_nil] at this
  have hlen := this.length_eq
  simp at hlen

/-! ## §5  Smooth / rough source factorisation -/

open Erdos287.PostBalanced7Pro

/-- **`block20_gcd_smooth_rough`.**  `LEAN_PROVED`.

The source-level decomposition `n = d·m` with `P⁺(d) < z₀`, `P⁻(m) ≥ z₀` and complete prime
powers on one side gives `gcd(d, m) = 1` (banked algebraically). -/
theorem block20_gcd_smooth_rough {z d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0)
    (hs : IsSmoothBelow z d) (hr : IsRoughAbove z m) : Nat.gcd d m = 1 :=
  coprime_smooth_rough hd hm hs hr

/-- **`block20_smoothRough_exists`.**  `LEAN_PROVED`.  Existence of the split at any cutoff. -/
theorem block20_smoothRough_exists {n : ℕ} (hn : n ≠ 0) (z : ℕ) :
    smoothPart z n * roughPart z n = n ∧ IsSmoothBelow z (smoothPart z n) ∧
      IsRoughAbove z (roughPart z n) :=
  ⟨smoothPart_mul_roughPart hn z, smoothPart_smooth z n, roughPart_rough z n⟩

/-- **`bigOmega_rough_le_420`.**  `LEAN_PROVED`.

The finite implication behind `Ω(m) ≤ 420`: a `z`-rough number of size at most `z^420` has
at most `420` prime factors with multiplicity.  With `z = z₀ = X^{1/420}` and `m ≤ X` this is
the source-level bound. -/
theorem bigOmega_rough_le_420 {z m : ℕ} (hz : 2 ≤ z) (hm : m ≠ 0)
    (hrough : IsRoughAbove z m) (hsize : m ≤ z ^ 420) : cardFactors m ≤ 420 := by
  have hlen : z ^ m.primeFactorsList.length ≤ m.primeFactorsList.prod := by
    refine List.pow_card_le_prod _ _ ?_
    intro x hx
    exact hrough x (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactorsList hx,
      Nat.dvd_of_mem_primeFactorsList hx, hm⟩)
  rw [Nat.prod_primeFactorsList hm] at hlen
  have hpow : z ^ m.primeFactorsList.length ≤ z ^ 420 := le_trans hlen hsize
  simpa [ArithmeticFunction.cardFactors_apply] using (Nat.pow_le_pow_iff_right hz).mp hpow

/-! ### The truncated-Möbius divisor factorisation -/

/-- **`truncMobius_coprime_split`.**  `LEAN_PROVED`.

The exact divisor factorisation `e = e_d · e_m` of the truncated Möbius weight at a coprime
product, in bijective form. -/
theorem truncMobius_coprime_split (d m B : ℕ) (hd : d ≠ 0) (hm : m ≠ 0)
    (hco : Nat.Coprime d m) :
    ∑ e ∈ (d * m).divisors.filter (fun e => e ≤ B), moebius e
      = ∑ p ∈ (d.divisors ×ˢ m.divisors).filter (fun p => p.1 * p.2 ≤ B),
          moebius p.1 * moebius p.2 := by
  classical
  refine Finset.sum_nbij' (fun e => (Nat.gcd e d, Nat.gcd e m)) (fun p => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
  · intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    obtain ⟨⟨hdvd, _⟩, hle⟩ := he
    have hsplit : Nat.gcd e d * Nat.gcd e m = e := by
      rw [← Nat.Coprime.gcd_mul e hco, Nat.gcd_eq_left hdvd]
    simp only [Finset.mem_filter, Finset.mem_product, Nat.mem_divisors]
    exact ⟨⟨⟨Nat.gcd_dvd_right e d, hd⟩, ⟨Nat.gcd_dvd_right e m, hm⟩⟩, by rw [hsplit]; exact hle⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Nat.mem_divisors] at hp
    obtain ⟨⟨⟨ha, _⟩, ⟨hb, _⟩⟩, hle⟩ := hp
    simp only [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨mul_dvd_mul ha hb, Nat.mul_ne_zero hd hm⟩, hle⟩
  · intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    show Nat.gcd e d * Nat.gcd e m = e
    rw [← Nat.Coprime.gcd_mul e hco, Nat.gcd_eq_left he.1.1]
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Nat.mem_divisors] at hp
    obtain ⟨⟨⟨ha, _⟩, ⟨hb, _⟩⟩, _⟩ := hp
    have hab : Nat.Coprime p.1 p.2 :=
      Nat.Coprime.coprime_dvd_left ha (Nat.Coprime.coprime_dvd_right hb hco)
    have h1 : Nat.gcd (p.1 * p.2) d = p.1 := by
      rw [Nat.gcd_comm, Nat.Coprime.gcd_mul d hab, Nat.gcd_eq_right ha,
        Nat.Coprime.gcd_eq_one (Nat.Coprime.coprime_dvd_right hb hco), mul_one]
    have h2 : Nat.gcd (p.1 * p.2) m = p.2 := by
      rw [Nat.gcd_comm, Nat.Coprime.gcd_mul m hab,
        Nat.Coprime.gcd_eq_one (Nat.Coprime.coprime_dvd_right ha hco.symm), Nat.gcd_eq_right hb,
        one_mul]
    show ((p.1 * p.2).gcd d, (p.1 * p.2).gcd m) = p
    rw [h1, h2]
  · intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    have hab : Nat.Coprime (Nat.gcd e d) (Nat.gcd e m) :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right e d)
        (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right e m) hco)
    have hsplit : Nat.gcd e d * Nat.gcd e m = e := by
      rw [← Nat.Coprime.gcd_mul e hco, Nat.gcd_eq_left he.1.1]
    show moebius e = moebius (Nat.gcd e d) * moebius (Nat.gcd e m)
    conv_lhs => rw [← hsplit]
    exact isMultiplicative_moebius.map_mul_of_coprime hab

/-- **`truncMobius_gamma_split`.**  `LEAN_PROVED`.

The mandated iterated form: for `gcd(d, m) = 1` and any cut `B` (in the source,
`B = ⌊(dm)^γ⌋`),

```
M_B(dm) = ∑_{e_d ∣ d} μ(e_d) · ∑_{e_m ∣ m, e_d·e_m ≤ B} μ(e_m).
```

The inner cut still couples `e_d` and `e_m`; this is *not* a product factorisation, in
accordance with the banked obstruction `truncMoebius_not_prefix_factorisable`. -/
theorem truncMobius_gamma_split (d m B : ℕ) (hd : d ≠ 0) (hm : m ≠ 0)
    (hco : Nat.Coprime d m) :
    Erdos287.SmoothParity.truncMobius (d * m) B
      = ∑ ed ∈ d.divisors, moebius ed *
          ∑ em ∈ m.divisors.filter (fun em => ed * em ≤ B), moebius em := by
  classical
  rw [Erdos287.SmoothParity.truncMobius, truncMobius_coprime_split d m B hd hm hco,
    Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun ed _ => ?_
  rw [Finset.mul_sum, Finset.sum_filter]

end Block20
end Erdos287
