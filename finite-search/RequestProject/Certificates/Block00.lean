import RequestProject.PowMod

/-!
# Certified primes, block 0

Kernel-checked Lucas primality certificates for the prime pairs
`(q_i, P_i = 2 * q_i - 1)` with `0 ≤ i < 24`.
-/

namespace Erdos287

set_option maxRecDepth 100000

theorem prime_q000 : Nat.Prime 157 := by norm_num

theorem prime_P000 : Nat.Prime 313 := by norm_num

theorem prime_q001 : Nat.Prime 307 := by norm_num

theorem prime_P001 : Nat.Prime 613 := by norm_num

theorem prime_q002 : Nat.Prime 607 := by norm_num

theorem prime_P002 : Nat.Prime 1213 := by norm_num

theorem prime_q003 : Nat.Prime 1171 := by norm_num

theorem prime_P003 : Nat.Prime 2341 := by norm_num

theorem prime_q004 : Nat.Prime 2311 := by norm_num

theorem prime_P004 : Nat.Prime 4621 := by norm_num

theorem prime_q005 : Nat.Prime 4621 := by norm_num

theorem prime_P005 : Nat.Prime 9241 := by norm_num

theorem prime_q006 : Nat.Prime 9241 := by norm_num

theorem prime_P006 : Nat.Prime 18481 := by norm_num

theorem prime_q007 : Nat.Prime 18457 := by norm_num

theorem prime_P007 : Nat.Prime 36913 := by norm_num

theorem prime_q008 : Nat.Prime 36847 := by norm_num

theorem prime_P008 : Nat.Prime 73693 := by norm_num

theorem prime_q009 : Nat.Prime 73477 := by norm_num

theorem prime_P009 : Nat.Prime 146953 := by norm_num

theorem prime_q010 : Nat.Prime 146389 := by norm_num

theorem prime_P010 : Nat.Prime 292777 := by norm_num

theorem prime_q011 : Nat.Prime 292759 := by norm_num

theorem prime_P011 : Nat.Prime 585517 := by norm_num

theorem prime_q012 : Nat.Prime 585517 := by norm_num

theorem prime_P012 : Nat.Prime 1171033 := by norm_num

theorem prime_q013 : Nat.Prime 1170727 := by norm_num

theorem prime_P013 : Nat.Prime 2341453 := by norm_num

theorem prime_q014 : Nat.Prime 2341369 := by norm_num

theorem prime_P014 : Nat.Prime 4682737 := by norm_num

theorem prime_q015 : Nat.Prime 4682719 := by norm_num

theorem prime_P015 : Nat.Prime 9365437 := by norm_num

theorem prime_q016 : Nat.Prime 9365137 := by norm_num

theorem prime_P016 : Nat.Prime 18730273 :=
  prime_of_cert' (c := 585321) (t := 5) (a := 15) (ps := [3, 11, 17737])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q017 : Nat.Prime 18729721 :=
  prime_of_cert' (c := 2341215) (t := 3) (a := 11) (ps := [3, 3, 5, 52027])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P017 : Nat.Prime 37459441 :=
  prime_of_cert' (c := 2341215) (t := 4) (a := 13) (ps := [3, 3, 5, 52027])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q018 : Nat.Prime 37459297 :=
  prime_of_cert' (c := 1170603) (t := 5) (a := 15) (ps := [3, 3, 7, 17, 1093])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P018 : Nat.Prime 74918593 :=
  prime_of_cert' (c := 1170603) (t := 6) (a := 11) (ps := [3, 3, 7, 17, 1093])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q019 : Nat.Prime 74916577 :=
  prime_of_cert' (c := 2341143) (t := 5) (a := 5) (ps := [3, 3, 3, 3, 7, 4129])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P019 : Nat.Prime 149833153 :=
  prime_of_cert' (c := 2341143) (t := 6) (a := 10) (ps := [3, 3, 3, 3, 7, 4129])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q020 : Nat.Prime 149831041 :=
  prime_of_cert' (c := 2341110) (t := 6) (a := 11) (ps := [2, 3, 5, 73, 1069])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P020 : Nat.Prime 299662081 :=
  prime_of_cert' (c := 2341110) (t := 7) (a := 7) (ps := [2, 3, 5, 73, 1069])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q021 : Nat.Prime 299662081 :=
  prime_of_cert' (c := 2341110) (t := 7) (a := 7) (ps := [2, 3, 5, 73, 1069])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P021 : Nat.Prime 599324161 :=
  prime_of_cert' (c := 2341110) (t := 8) (a := 22) (ps := [2, 3, 5, 73, 1069])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q022 : Nat.Prime 599316481 :=
  prime_of_cert' (c := 2341080) (t := 8) (a := 31) (ps := [2, 2, 2, 3, 3, 5, 7, 929])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P022 : Nat.Prime 1198632961 :=
  prime_of_cert' (c := 2341080) (t := 9) (a := 41) (ps := [2, 2, 2, 3, 3, 5, 7, 929])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q023 : Nat.Prime 1198632961 :=
  prime_of_cert' (c := 2341080) (t := 9) (a := 41) (ps := [2, 2, 2, 3, 3, 5, 7, 929])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P023 : Nat.Prime 2397265921 :=
  prime_of_cert' (c := 2341080) (t := 10) (a := 11) (ps := [2, 2, 2, 3, 3, 5, 7, 929])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

end Erdos287
