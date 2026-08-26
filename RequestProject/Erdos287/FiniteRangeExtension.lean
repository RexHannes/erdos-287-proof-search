import RequestProject.Erdos287.FiniteRemainder
import RequestProject.Erdos287.FiniteMasterReduction

/-!
# Erdős Problem #287 — the unconditional finite range

A chain of 34 window certificates (see `FiniteRemainder.lean`) covering every maximum
`3 ≤ M ≤ 4·10^9`.  Each certificate `(x, pu^au, pv^av, L, U)` blocks the whole interval
`[L, U]` of maxima at once, and the intervals are chained (`L_{i+1} = U_i + 1`), so the
verified range grows geometrically in the number of certificates rather than linearly.

Main results:

* `Erdos287.Gap2CE.no_of_M_le_4e9` — no gap-`≤2` counterexample has `3 ≤ M ≤ 4·10^9`;
* `Erdos287.no_Erdos287Counterexample_of_max_le_4e9` — no **exact** Erdős-#287
  counterexample has `max A ≤ 4·10^9` (the maximum of an exact counterexample is `≥ 4`,
  so the lower endpoint costs nothing).

The upper endpoint is limited only by the size of the primality certificates that the
kernel accepts: every primality side condition is discharged by `norm_num`, with no
`decide` on large primality and no `native_decide`.
-/

open scoped BigOperators

namespace Erdos287

namespace Gap2CE

/-- Window certificate at `x = 2` (`2^1 ∣ x`, `3^1 ∣ x+1`):
no gap-`≤2` counterexample has `3 ≤ M ≤ 3`. -/
theorem windowStep_0 (ce : Gap2CE) (h1 : 3 ≤ ce.M) (h2 : ce.M ≤ 3) : False :=
  ce.blocker_window (x := 2) (pu := 2) (au := 1) (pv := 3) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 3` (`3^1 ∣ x`, `2^2 ∣ x+1`):
no gap-`≤2` counterexample has `4 ≤ M ≤ 5`. -/
theorem windowStep_1 (ce : Gap2CE) (h1 : 4 ≤ ce.M) (h2 : ce.M ≤ 5) : False :=
  ce.blocker_window (x := 3) (pu := 3) (au := 1) (pv := 2) (av := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 4` (`2^2 ∣ x`, `5^1 ∣ x+1`):
no gap-`≤2` counterexample has `6 ≤ M ≤ 7`. -/
theorem windowStep_2 (ce : Gap2CE) (h1 : 6 ≤ ce.M) (h2 : ce.M ≤ 7) : False :=
  ce.blocker_window (x := 4) (pu := 2) (au := 2) (pv := 5) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 7` (`7^1 ∣ x`, `2^3 ∣ x+1`):
no gap-`≤2` counterexample has `8 ≤ M ≤ 14`. -/
theorem windowStep_3 (ce : Gap2CE) (h1 : 8 ≤ ce.M) (h2 : ce.M ≤ 14) : False :=
  ce.blocker_window (x := 7) (pu := 7) (au := 1) (pv := 2) (av := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 13` (`13^1 ∣ x`, `7^1 ∣ x+1`):
no gap-`≤2` counterexample has `15 ≤ M ≤ 20`. -/
theorem windowStep_4 (ce : Gap2CE) (h1 : 15 ≤ ce.M) (h2 : ce.M ≤ 20) : False :=
  ce.blocker_window (x := 13) (pu := 13) (au := 1) (pv := 7) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 16` (`2^4 ∣ x`, `17^1 ∣ x+1`):
no gap-`≤2` counterexample has `21 ≤ M ≤ 31`. -/
theorem windowStep_5 (ce : Gap2CE) (h1 : 21 ≤ ce.M) (h2 : ce.M ≤ 31) : False :=
  ce.blocker_window (x := 16) (pu := 2) (au := 4) (pv := 17) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 31` (`31^1 ∣ x`, `2^5 ∣ x+1`):
no gap-`≤2` counterexample has `32 ≤ M ≤ 62`. -/
theorem windowStep_6 (ce : Gap2CE) (h1 : 32 ≤ ce.M) (h2 : ce.M ≤ 62) : False :=
  ce.blocker_window (x := 31) (pu := 31) (au := 1) (pv := 2) (av := 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 61` (`61^1 ∣ x`, `31^1 ∣ x+1`):
no gap-`≤2` counterexample has `63 ≤ M ≤ 122`. -/
theorem windowStep_7 (ce : Gap2CE) (h1 : 63 ≤ ce.M) (h2 : ce.M ≤ 122) : False :=
  ce.blocker_window (x := 61) (pu := 61) (au := 1) (pv := 31) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 106` (`53^1 ∣ x`, `107^1 ∣ x+1`):
no gap-`≤2` counterexample has `123 ≤ M ≤ 212`. -/
theorem windowStep_8 (ce : Gap2CE) (h1 : 123 ≤ ce.M) (h2 : ce.M ≤ 212) : False :=
  ce.blocker_window (x := 106) (pu := 53) (au := 1) (pv := 107) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 193` (`193^1 ∣ x`, `97^1 ∣ x+1`):
no gap-`≤2` counterexample has `213 ≤ M ≤ 386`. -/
theorem windowStep_9 (ce : Gap2CE) (h1 : 213 ≤ ce.M) (h2 : ce.M ≤ 386) : False :=
  ce.blocker_window (x := 193) (pu := 193) (au := 1) (pv := 97) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 382` (`191^1 ∣ x`, `383^1 ∣ x+1`):
no gap-`≤2` counterexample has `387 ≤ M ≤ 764`. -/
theorem windowStep_10 (ce : Gap2CE) (h1 : 387 ≤ ce.M) (h2 : ce.M ≤ 764) : False :=
  ce.blocker_window (x := 382) (pu := 191) (au := 1) (pv := 383) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 757` (`757^1 ∣ x`, `379^1 ∣ x+1`):
no gap-`≤2` counterexample has `765 ≤ M ≤ 1514`. -/
theorem windowStep_11 (ce : Gap2CE) (h1 : 765 ≤ ce.M) (h2 : ce.M ≤ 1514) : False :=
  ce.blocker_window (x := 757) (pu := 757) (au := 1) (pv := 379) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 1486` (`743^1 ∣ x`, `1487^1 ∣ x+1`):
no gap-`≤2` counterexample has `1515 ≤ M ≤ 2972`. -/
theorem windowStep_12 (ce : Gap2CE) (h1 : 1515 ≤ ce.M) (h2 : ce.M ≤ 2972) : False :=
  ce.blocker_window (x := 1486) (pu := 743) (au := 1) (pv := 1487) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 2962` (`1481^1 ∣ x`, `2963^1 ∣ x+1`):
no gap-`≤2` counterexample has `2973 ≤ M ≤ 5924`. -/
theorem windowStep_13 (ce : Gap2CE) (h1 : 2973 ≤ ce.M) (h2 : ce.M ≤ 5924) : False :=
  ce.blocker_window (x := 2962) (pu := 1481) (au := 1) (pv := 2963) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 5923` (`5923^1 ∣ x`, `1481^1 ∣ x+1`):
no gap-`≤2` counterexample has `5925 ≤ M ≤ 11846`. -/
theorem windowStep_14 (ce : Gap2CE) (h1 : 5925 ≤ ce.M) (h2 : ce.M ≤ 11846) : False :=
  ce.blocker_window (x := 5923) (pu := 5923) (au := 1) (pv := 1481) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 11828` (`2957^1 ∣ x`, `3943^1 ∣ x+1`):
no gap-`≤2` counterexample has `11847 ≤ M ≤ 23656`. -/
theorem windowStep_15 (ce : Gap2CE) (h1 : 11847 ≤ ce.M) (h2 : ce.M ≤ 23656) : False :=
  ce.blocker_window (x := 11828) (pu := 2957) (au := 1) (pv := 3943) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 23626` (`11813^1 ∣ x`, `23627^1 ∣ x+1`):
no gap-`≤2` counterexample has `23657 ≤ M ≤ 47252`. -/
theorem windowStep_16 (ce : Gap2CE) (h1 : 23657 ≤ ce.M) (h2 : ce.M ≤ 47252) : False :=
  ce.blocker_window (x := 23626) (pu := 11813) (au := 1) (pv := 23627) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 47251` (`47251^1 ∣ x`, `11813^1 ∣ x+1`):
no gap-`≤2` counterexample has `47253 ≤ M ≤ 94502`. -/
theorem windowStep_17 (ce : Gap2CE) (h1 : 47253 ≤ ce.M) (h2 : ce.M ≤ 94502) : False :=
  ce.blocker_window (x := 47251) (pu := 47251) (au := 1) (pv := 11813) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 94442` (`47221^1 ∣ x`, `31481^1 ∣ x+1`):
no gap-`≤2` counterexample has `94503 ≤ M ≤ 188884`. -/
theorem windowStep_18 (ce : Gap2CE) (h1 : 94503 ≤ ce.M) (h2 : ce.M ≤ 188884) : False :=
  ce.blocker_window (x := 94442) (pu := 47221) (au := 1) (pv := 31481) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 188842` (`94421^1 ∣ x`, `188843^1 ∣ x+1`):
no gap-`≤2` counterexample has `188885 ≤ M ≤ 377684`. -/
theorem windowStep_19 (ce : Gap2CE) (h1 : 188885 ≤ ce.M) (h2 : ce.M ≤ 377684) : False :=
  ce.blocker_window (x := 188842) (pu := 94421) (au := 1) (pv := 188843) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 377665` (`75533^1 ∣ x`, `188833^1 ∣ x+1`):
no gap-`≤2` counterexample has `377685 ≤ M ≤ 755329`. -/
theorem windowStep_20 (ce : Gap2CE) (h1 : 377685 ≤ ce.M) (h2 : ce.M ≤ 755329) : False :=
  ce.blocker_window (x := 377665) (pu := 75533) (au := 1) (pv := 188833) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 755308` (`188827^1 ∣ x`, `755309^1 ∣ x+1`):
no gap-`≤2` counterexample has `755330 ≤ M ≤ 1510616`. -/
theorem windowStep_21 (ce : Gap2CE) (h1 : 755330 ≤ ce.M) (h2 : ce.M ≤ 1510616) : False :=
  ce.blocker_window (x := 755308) (pu := 188827) (au := 1) (pv := 755309) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 1510492` (`377623^1 ∣ x`, `1510493^1 ∣ x+1`):
no gap-`≤2` counterexample has `1510617 ≤ M ≤ 3020984`. -/
theorem windowStep_22 (ce : Gap2CE) (h1 : 1510617 ≤ ce.M) (h2 : ce.M ≤ 3020984) : False :=
  ce.blocker_window (x := 1510492) (pu := 377623) (au := 1) (pv := 1510493) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 3020956` (`755239^1 ∣ x`, `3020957^1 ∣ x+1`):
no gap-`≤2` counterexample has `3020985 ≤ M ≤ 6041912`. -/
theorem windowStep_23 (ce : Gap2CE) (h1 : 3020985 ≤ ce.M) (h2 : ce.M ≤ 6041912) : False :=
  ce.blocker_window (x := 3020956) (pu := 755239) (au := 1) (pv := 3020957) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 6041908` (`1510477^1 ∣ x`, `6041909^1 ∣ x+1`):
no gap-`≤2` counterexample has `6041913 ≤ M ≤ 12083816`. -/
theorem windowStep_24 (ce : Gap2CE) (h1 : 6041913 ≤ ce.M) (h2 : ce.M ≤ 12083816) : False :=
  ce.blocker_window (x := 6041908) (pu := 1510477) (au := 1) (pv := 6041909) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 12083781` (`4027927^1 ∣ x`, `6041891^1 ∣ x+1`):
no gap-`≤2` counterexample has `12083817 ≤ M ≤ 24167562`. -/
theorem windowStep_25 (ce : Gap2CE) (h1 : 12083817 ≤ ce.M) (h2 : ce.M ≤ 24167562) : False :=
  ce.blocker_window (x := 12083781) (pu := 4027927) (au := 1) (pv := 6041891) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 24167427` (`8055809^1 ∣ x`, `6041857^1 ∣ x+1`):
no gap-`≤2` counterexample has `24167563 ≤ M ≤ 48334854`. -/
theorem windowStep_26 (ce : Gap2CE) (h1 : 24167563 ≤ ce.M) (h2 : ce.M ≤ 48334854) : False :=
  ce.blocker_window (x := 24167427) (pu := 8055809) (au := 1) (pv := 6041857) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 48334771` (`48334771^1 ∣ x`, `12083693^1 ∣ x+1`):
no gap-`≤2` counterexample has `48334855 ≤ M ≤ 96669542`. -/
theorem windowStep_27 (ce : Gap2CE) (h1 : 48334855 ≤ ce.M) (h2 : ce.M ≤ 96669542) : False :=
  ce.blocker_window (x := 48334771) (pu := 48334771) (au := 1) (pv := 12083693) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 96669457` (`96669457^1 ∣ x`, `48334729^1 ∣ x+1`):
no gap-`≤2` counterexample has `96669543 ≤ M ≤ 193338914`. -/
theorem windowStep_28 (ce : Gap2CE) (h1 : 96669543 ≤ ce.M) (h2 : ce.M ≤ 193338914) : False :=
  ce.blocker_window (x := 96669457) (pu := 96669457) (au := 1) (pv := 48334729) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 193338913` (`193338913^1 ∣ x`, `96669457^1 ∣ x+1`):
no gap-`≤2` counterexample has `193338915 ≤ M ≤ 386677826`. -/
theorem windowStep_29 (ce : Gap2CE) (h1 : 193338915 ≤ ce.M) (h2 : ce.M ≤ 386677826) : False :=
  ce.blocker_window (x := 193338913) (pu := 193338913) (au := 1) (pv := 96669457) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 386677804` (`96669451^1 ∣ x`, `77335561^1 ∣ x+1`):
no gap-`≤2` counterexample has `386677827 ≤ M ≤ 773355608`. -/
theorem windowStep_30 (ce : Gap2CE) (h1 : 386677827 ≤ ce.M) (h2 : ce.M ≤ 773355608) : False :=
  ce.blocker_window (x := 386677804) (pu := 96669451) (au := 1) (pv := 77335561) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 773355454` (`386677727^1 ∣ x`, `154671091^1 ∣ x+1`):
no gap-`≤2` counterexample has `773355609 ≤ M ≤ 1546710908`. -/
theorem windowStep_31 (ce : Gap2CE) (h1 : 773355609 ≤ ce.M) (h2 : ce.M ≤ 1546710908) : False :=
  ce.blocker_window (x := 773355454) (pu := 386677727) (au := 1) (pv := 154671091) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 1546710908` (`386677727^1 ∣ x`, `515570303^1 ∣ x+1`):
no gap-`≤2` counterexample has `1546710909 ≤ M ≤ 3093421816`. -/
theorem windowStep_32 (ce : Gap2CE) (h1 : 1546710909 ≤ ce.M) (h2 : ce.M ≤ 3093421816) : False :=
  ce.blocker_window (x := 1546710908) (pu := 386677727) (au := 1) (pv := 515570303) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 3093421718` (`1546710859^1 ∣ x`, `1031140573^1 ∣ x+1`):
no gap-`≤2` counterexample has `3093421817 ≤ M ≤ 4000000000`. -/
theorem windowStep_33 (ce : Gap2CE) (h1 : 3093421817 ≤ ce.M) (h2 : ce.M ≤ 4000000000) : False :=
  ce.blocker_window (x := 3093421718) (pu := 1546710859) (au := 1) (pv := 1031140573) (av := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- **No gap-`≤2` counterexample has `3 ≤ M ≤ 4000000000`.** -/
theorem no_of_M_le_4e9 (ce : Gap2CE) (h3 : 3 ≤ ce.M) (hM : ce.M ≤ 4000000000) : False := by
  by_cases c0 : ce.M ≤ 3
  · exact windowStep_0 ce (by omega) c0
  by_cases c1 : ce.M ≤ 5
  · exact windowStep_1 ce (by omega) c1
  by_cases c2 : ce.M ≤ 7
  · exact windowStep_2 ce (by omega) c2
  by_cases c3 : ce.M ≤ 14
  · exact windowStep_3 ce (by omega) c3
  by_cases c4 : ce.M ≤ 20
  · exact windowStep_4 ce (by omega) c4
  by_cases c5 : ce.M ≤ 31
  · exact windowStep_5 ce (by omega) c5
  by_cases c6 : ce.M ≤ 62
  · exact windowStep_6 ce (by omega) c6
  by_cases c7 : ce.M ≤ 122
  · exact windowStep_7 ce (by omega) c7
  by_cases c8 : ce.M ≤ 212
  · exact windowStep_8 ce (by omega) c8
  by_cases c9 : ce.M ≤ 386
  · exact windowStep_9 ce (by omega) c9
  by_cases c10 : ce.M ≤ 764
  · exact windowStep_10 ce (by omega) c10
  by_cases c11 : ce.M ≤ 1514
  · exact windowStep_11 ce (by omega) c11
  by_cases c12 : ce.M ≤ 2972
  · exact windowStep_12 ce (by omega) c12
  by_cases c13 : ce.M ≤ 5924
  · exact windowStep_13 ce (by omega) c13
  by_cases c14 : ce.M ≤ 11846
  · exact windowStep_14 ce (by omega) c14
  by_cases c15 : ce.M ≤ 23656
  · exact windowStep_15 ce (by omega) c15
  by_cases c16 : ce.M ≤ 47252
  · exact windowStep_16 ce (by omega) c16
  by_cases c17 : ce.M ≤ 94502
  · exact windowStep_17 ce (by omega) c17
  by_cases c18 : ce.M ≤ 188884
  · exact windowStep_18 ce (by omega) c18
  by_cases c19 : ce.M ≤ 377684
  · exact windowStep_19 ce (by omega) c19
  by_cases c20 : ce.M ≤ 755329
  · exact windowStep_20 ce (by omega) c20
  by_cases c21 : ce.M ≤ 1510616
  · exact windowStep_21 ce (by omega) c21
  by_cases c22 : ce.M ≤ 3020984
  · exact windowStep_22 ce (by omega) c22
  by_cases c23 : ce.M ≤ 6041912
  · exact windowStep_23 ce (by omega) c23
  by_cases c24 : ce.M ≤ 12083816
  · exact windowStep_24 ce (by omega) c24
  by_cases c25 : ce.M ≤ 24167562
  · exact windowStep_25 ce (by omega) c25
  by_cases c26 : ce.M ≤ 48334854
  · exact windowStep_26 ce (by omega) c26
  by_cases c27 : ce.M ≤ 96669542
  · exact windowStep_27 ce (by omega) c27
  by_cases c28 : ce.M ≤ 193338914
  · exact windowStep_28 ce (by omega) c28
  by_cases c29 : ce.M ≤ 386677826
  · exact windowStep_29 ce (by omega) c29
  by_cases c30 : ce.M ≤ 773355608
  · exact windowStep_30 ce (by omega) c30
  by_cases c31 : ce.M ≤ 1546710908
  · exact windowStep_31 ce (by omega) c31
  by_cases c32 : ce.M ≤ 3093421816
  · exact windowStep_32 ce (by omega) c32
  exact windowStep_33 ce (by omega) hM

end Gap2CE

/-- **No exact Erdős-#287 counterexample has maximum `≤ 4000000000`.** -/
theorem no_Erdos287Counterexample_of_max_le_4e9 {A : Finset ℕ}
    (h : Erdos287Counterexample A) (hM : A.max' h.nonempty ≤ 4000000000) : False := by
  refine (h.toGap2CE).no_of_M_le_4e9 ?_ hM
  show 3 ≤ A.max' h.nonempty
  have := h.four_le_max
  omega

end Erdos287
