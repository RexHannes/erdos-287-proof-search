import RequestProject.Erdos287.Direct.ReciprocalCompiler

/-!
# Route D — protected switches (value-preserving and value-moving)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Two kinds of local moves are formalised exactly.

**Value-preserving.**  The identity `1/(6k) = 1/(10k) + 1/(15k)` and precisely what it
preserves: the rational value always; the *cleared-denominator carry coordinates* only under
the explicit divisibility hypothesis `30k ∣ D` (`carry_neutral_of_dvd`), and
`carry_not_neutral_without_dvd` shows that hypothesis cannot be dropped.  Cardinality is *not*
preserved (`switch_changes_card`).

**Value-moving.**  The exact signed increment `1/(ck) − 1/(dk) = (d−c)/(cdk)`, and an abstract
`ProtectedSwitch` predicate collecting all the local conditions (support inside the interval,
no adjacency conflict, neighbour protection, non-collision with the swapped-in site).  From the
predicate we prove: the toggle preserves the endpoint pins and the no-two-consecutive-omissions
rule, preserves every additive tracked statistic that agrees on the two sites, and changes the
reciprocal value by exactly the stated increment.

Supply/abundance of switches is deliberately **not** part of these theorems: it is an analytic
input, kept as an interface in `Direct/TargetTuningFinite.lean`.
-/

open scoped BigOperators

namespace Erdos287
namespace Direct

/-! ## D.30  The value-preserving switch -/

/-- **`sixSwitch_identity`.**  `KERNEL-PROVED`.  `1/(6k) = 1/(10k) + 1/(15k)`. -/
theorem sixSwitch_identity (k : ℚ) (hk : k ≠ 0) :
    1 / (6 * k) = 1 / (10 * k) + 1 / (15 * k) := by
  field_simp
  ring

/-- **`recipSum_sixSwitch`.**  `KERNEL-PROVED`.  Performing the switch inside a selection
preserves the reciprocal sum exactly. -/
theorem recipSum_sixSwitch {A : Finset ℕ} {k : ℕ} (hk : 0 < k) (h6 : 6 * k ∈ A)
    (h10 : 10 * k ∉ A) (h15 : 15 * k ∉ A) :
    recipSum (insert (10 * k) (insert (15 * k) (A.erase (6 * k)))) = recipSum A := by
  have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h15' : 15 * k ∉ A.erase (6 * k) := fun h => h15 (Finset.mem_of_mem_erase h)
  have h10' : 10 * k ∉ insert (15 * k) (A.erase (6 * k)) := by
    intro h
    rcases Finset.mem_insert.1 h with h' | h'
    · omega
    · exact h10 (Finset.mem_of_mem_erase h')
  rw [recipSum_insert h10', recipSum_insert h15']
  have herase : recipSum A = 1 / ((6 * k : ℕ) : ℚ) + recipSum (A.erase (6 * k)) := by
    rw [← recipSum_insert (Finset.notMem_erase _ _), Finset.insert_erase h6]
  rw [herase]
  push_cast
  rw [sixSwitch_identity (k : ℚ) hk']
  ring

/-- **`carry_neutral_of_dvd`.**  `KERNEL-PROVED`.  Under the explicit divisibility hypothesis
`30k ∣ D`, the switch is neutral on the cleared-denominator (carry) coordinates. -/
theorem carry_neutral_of_dvd {D k : ℕ} (hk : 0 < k) (h : 30 * k ∣ D) :
    D / (6 * k) = D / (10 * k) + D / (15 * k) := by
  obtain ⟨c, rfl⟩ := h
  have h1 : 30 * k * c / (6 * k) = 5 * c := by
    rw [show 30 * k * c = (6 * k) * (5 * c) by ring, Nat.mul_div_cancel_left _ (by omega)]
  have h2 : 30 * k * c / (10 * k) = 3 * c := by
    rw [show 30 * k * c = (10 * k) * (3 * c) by ring, Nat.mul_div_cancel_left _ (by omega)]
  have h3 : 30 * k * c / (15 * k) = 2 * c := by
    rw [show 30 * k * c = (15 * k) * (2 * c) by ring, Nat.mul_div_cancel_left _ (by omega)]
  rw [h1, h2, h3]
  ring

/-- **`carry_not_neutral_without_dvd`.**  `KERNEL-PROVED` firewall.  Without `30k ∣ D` carry
neutrality genuinely fails: `D = 6`, `k = 1` gives `1 ≠ 0`. -/
theorem carry_not_neutral_without_dvd :
    (6 : ℕ) / (6 * 1) ≠ 6 / (10 * 1) + 6 / (15 * 1) := by decide

/-- **`switch_changes_card`.**  `KERNEL-PROVED` firewall.  The switch is *not* neutral on the
cardinality of the selection: it increases it by one. -/
theorem switch_changes_card {A : Finset ℕ} {k : ℕ} (hk : 0 < k) (h6 : 6 * k ∈ A)
    (h10 : 10 * k ∉ A) (h15 : 15 * k ∉ A) :
    (insert (10 * k) (insert (15 * k) (A.erase (6 * k)))).card = A.card + 1 := by
  have h15' : 15 * k ∉ A.erase (6 * k) := fun h => h15 (Finset.mem_of_mem_erase h)
  have h10' : 10 * k ∉ insert (15 * k) (A.erase (6 * k)) := by
    intro h
    rcases Finset.mem_insert.1 h with h' | h'
    · omega
    · exact h10 (Finset.mem_of_mem_erase h')
  rw [Finset.card_insert_of_notMem h10', Finset.card_insert_of_notMem h15',
    Finset.card_erase_of_mem h6]
  have : 1 ≤ A.card := Finset.card_pos.2 ⟨_, h6⟩
  omega

/-! ## D.31  The value-moving switch -/

/-- **`movingSwitch_increment`.**  `KERNEL-PROVED`.  The exact signed increment. -/
theorem movingSwitch_increment (c d k : ℚ) (hc : c ≠ 0) (hd : d ≠ 0) (hk : k ≠ 0) :
    1 / (c * k) - 1 / (d * k) = (d - c) / (c * d * k) := by
  field_simp

/-- The toggle that removes the position `out` from the selection and adds the position `inn`. -/
def toggle (eps : ℕ → Bool) (out inn : ℕ) : ℕ → Bool :=
  fun n => if n = out then false else if n = inn then true else eps n

/-- **The local conditions of a protected switch.**  Support inside the interval, the removed
site strictly interior (so the endpoint pins survive), no adjacency conflict (both neighbours of
the removed site are selected), and non-collision of the two sites. -/
structure ProtectedSwitch (a M : ℕ) (eps : ℕ → Bool) (out inn : ℕ) : Prop where
  /-- the removed site is currently selected -/
  out_sel : eps out = true
  /-- the added site is currently free -/
  inn_free : eps inn = false
  /-- the removed site is strictly interior -/
  out_interior : a < out ∧ out < M
  /-- the added site lies in the interval -/
  inn_range : a ≤ inn ∧ inn ≤ M
  /-- the two sites are distinct -/
  sites_ne : out ≠ inn
  /-- left neighbour protection -/
  left_guard : eps (out - 1) = true
  /-- right neighbour protection -/
  right_guard : eps (out + 1) = true

variable {a M : ℕ} {eps : ℕ → Bool} {out inn : ℕ}

/-- **`toggle_preserves_endpoints`.**  `KERNEL-PROVED`. -/
theorem toggle_preserves_endpoints (hs : ProtectedSwitch a M eps out inn)
    (hend : EndpointSelected a M eps) : EndpointSelected a M (toggle eps out inn) := by
  obtain ⟨hlo, hhi⟩ := hs.out_interior
  refine ⟨?_, ?_⟩
  · simp only [toggle]
    rw [if_neg (by omega)]
    by_cases h : a = inn
    · rw [if_pos h]
    · rw [if_neg h]; exact hend.1
  · simp only [toggle]
    rw [if_neg (by omega)]
    by_cases h : M = inn
    · rw [if_pos h]
    · rw [if_neg h]; exact hend.2

/-- **`toggle_preserves_isolation`.**  `KERNEL-PROVED`.  A protected switch never creates two
consecutive omissions. -/
theorem toggle_preserves_isolation (hs : ProtectedSwitch a M eps out inn)
    (hiso : NoTwoConsecutiveOmissions a M eps) :
    NoTwoConsecutiveOmissions a M (toggle eps out inn) := by
  obtain ⟨hlo, hhi⟩ := hs.out_interior
  intro n hn hn'
  by_cases hout : n = out
  · right
    subst hout
    simp only [toggle]
    rw [if_neg (by omega)]
    by_cases h : n + 1 = inn
    · rw [if_pos h]
    · rw [if_neg h]; exact hs.right_guard
  · by_cases hout' : n + 1 = out
    · left
      simp only [toggle]
      rw [if_neg hout]
      by_cases h : n = inn
      · rw [if_pos h]
      · rw [if_neg h]
        have : n = out - 1 := by omega
        rw [this]; exact hs.left_guard
    · rcases hiso n hn hn' with h | h
      · left
        simp only [toggle]
        rw [if_neg hout]
        by_cases h' : n = inn
        · rw [if_pos h']
        · rw [if_neg h']; exact h
      · right
        simp only [toggle]
        rw [if_neg hout']
        by_cases h' : n + 1 = inn
        · rw [if_pos h']
        · rw [if_neg h']; exact h

/-- **`selected_toggle`.**  `KERNEL-PROVED`.  The selected set after a protected switch. -/
theorem selected_toggle (hs : ProtectedSwitch a M eps out inn) :
    selected a M (toggle eps out inn) = insert inn ((selected a M eps).erase out) := by
  obtain ⟨hlo, hhi⟩ := hs.out_interior
  obtain ⟨hinnlo, hinnhi⟩ := hs.inn_range
  ext x
  simp only [Finset.mem_insert, Finset.mem_erase, mem_selected, toggle]
  constructor
  · intro hx
    obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
    by_cases hxo : x = out
    · rw [if_pos hxo] at hx3; exact absurd hx3 (by simp)
    · rw [if_neg hxo] at hx3
      by_cases hxi : x = inn
      · exact Or.inl hxi
      · rw [if_neg hxi] at hx3
        exact Or.inr ⟨hxo, ⟨hx1, hx2⟩, hx3⟩
  · intro hx
    rcases hx with rfl | ⟨hxo, ⟨hx1, hx2⟩, hx3⟩
    · refine ⟨⟨hinnlo, hinnhi⟩, ?_⟩
      rw [if_neg (Ne.symm hs.sites_ne), if_pos rfl]
    · refine ⟨⟨hx1, hx2⟩, ?_⟩
      rw [if_neg hxo]
      by_cases hxi : x = inn
      · rw [if_pos hxi]
      · rw [if_neg hxi]; exact hx3

/-- **`recipSum_toggle`.**  `KERNEL-PROVED`.  A protected switch moves the reciprocal value by
exactly `1/inn − 1/out`. -/
theorem recipSum_toggle (hs : ProtectedSwitch a M eps out inn) :
    recipSum (selected a M (toggle eps out inn)) =
      recipSum (selected a M eps) + 1 / (inn : ℚ) - 1 / (out : ℚ) := by
  obtain ⟨hlo, hhi⟩ := hs.out_interior
  obtain ⟨hinnlo, hinnhi⟩ := hs.inn_range
  have hout_mem : out ∈ selected a M eps :=
    mem_selected.2 ⟨⟨by omega, by omega⟩, hs.out_sel⟩
  have hinn_not : inn ∉ selected a M eps := by
    intro h
    have := (mem_selected.1 h).2
    rw [hs.inn_free] at this
    exact absurd this (by simp)
  have hinn_not' : inn ∉ (selected a M eps).erase out :=
    fun h => hinn_not (Finset.mem_of_mem_erase h)
  rw [selected_toggle hs, recipSum_insert hinn_not']
  have hsplit : recipSum (selected a M eps)
      = 1 / (out : ℚ) + recipSum ((selected a M eps).erase out) := by
    rw [← recipSum_insert (Finset.notMem_erase _ _), Finset.insert_erase hout_mem]
  rw [hsplit]
  ring

/-- **`tracked_sum_invariant`.**  `KERNEL-PROVED`.  Every additive tracked statistic that takes
the same value on the two sites is preserved by a protected switch. -/
theorem tracked_sum_invariant (hs : ProtectedSwitch a M eps out inn) (track : ℕ → ℤ)
    (hagree : track out = track inn) :
    ∑ n ∈ selected a M (toggle eps out inn), track n = ∑ n ∈ selected a M eps, track n := by
  obtain ⟨hlo, hhi⟩ := hs.out_interior
  obtain ⟨hinnlo, hinnhi⟩ := hs.inn_range
  have hout_mem : out ∈ selected a M eps :=
    mem_selected.2 ⟨⟨by omega, by omega⟩, hs.out_sel⟩
  have hinn_not : inn ∉ selected a M eps := by
    intro h
    have := (mem_selected.1 h).2
    rw [hs.inn_free] at this
    exact absurd this (by simp)
  have hinn_not' : inn ∉ (selected a M eps).erase out :=
    fun h => hinn_not (Finset.mem_of_mem_erase h)
  rw [selected_toggle hs, Finset.sum_insert hinn_not', ← hagree,
    ← Finset.sum_insert (Finset.notMem_erase out (selected a M eps)),
    Finset.insert_erase hout_mem]

end Direct
end Erdos287
