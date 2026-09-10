import RequestProject.PowMod

/-!
# Certified primes, block 1

Kernel-checked Lucas primality certificates for the prime pairs
`(q_i, P_i = 2 * q_i - 1)` with `24 ≤ i < 48`.
-/

namespace Erdos287

set_option maxRecDepth 100000

theorem prime_q024 : Nat.Prime 2397112321 :=
  prime_of_cert' (c := 2340930) (t := 10) (a := 11) (ps := [2, 3, 5, 78031])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P024 : Nat.Prime 4794224641 :=
  prime_of_cert' (c := 2340930) (t := 11) (a := 14) (ps := [2, 3, 5, 78031])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q025 : Nat.Prime 4794034177 :=
  prime_of_cert' (c := 2340837) (t := 11) (a := 5) (ps := [3, 3, 199, 1307])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P025 : Nat.Prime 9588068353 :=
  prime_of_cert' (c := 2340837) (t := 12) (a := 5) (ps := [3, 3, 199, 1307])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q026 : Nat.Prime 9587171329 :=
  prime_of_cert' (c := 2340618) (t := 12) (a := 13) (ps := [2, 3, 7, 23, 2423])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P026 : Nat.Prime 19174342657 :=
  prime_of_cert' (c := 2340618) (t := 13) (a := 5) (ps := [2, 3, 7, 23, 2423])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q027 : Nat.Prime 19172794369 :=
  prime_of_cert' (c := 2340429) (t := 13) (a := 53) (ps := [3, 7, 13, 8573])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P027 : Nat.Prime 38345588737 :=
  prime_of_cert' (c := 2340429) (t := 14) (a := 5) (ps := [3, 7, 13, 8573])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q028 : Nat.Prime 38345588737 :=
  prime_of_cert' (c := 2340429) (t := 14) (a := 5) (ps := [3, 7, 13, 8573])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P028 : Nat.Prime 76691177473 :=
  prime_of_cert' (c := 2340429) (t := 15) (a := 5) (ps := [3, 7, 13, 8573])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q029 : Nat.Prime 76677120001 :=
  prime_of_cert' (c := 2340000) (t := 15) (a := 14) (ps := [2, 2, 2, 2, 2, 3, 3, 5, 5, 5, 5, 13])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P029 : Nat.Prime 153354240001 :=
  prime_of_cert' (c := 2340000) (t := 16) (a := 11) (ps := [2, 2, 2, 2, 2, 3, 3, 5, 5, 5, 5, 13])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q030 : Nat.Prime 153351684097 :=
  prime_of_cert' (c := 2339961) (t := 16) (a := 5) (ps := [3, 13, 59999])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P030 : Nat.Prime 306703368193 :=
  prime_of_cert' (c := 2339961) (t := 17) (a := 5) (ps := [3, 13, 59999])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q031 : Nat.Prime 306699042817 :=
  prime_of_cert' (c := 2339928) (t := 17) (a := 5) (ps := [2, 2, 2, 3, 3, 3, 3, 23, 157])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P031 : Nat.Prime 613398085633 :=
  prime_of_cert' (c := 2339928) (t := 18) (a := 17) (ps := [2, 2, 2, 3, 3, 3, 3, 23, 157])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q032 : Nat.Prime 613357191169 :=
  prime_of_cert' (c := 2339772) (t := 18) (a := 13) (ps := [2, 2, 3, 194981])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P032 : Nat.Prime 1226714382337 :=
  prime_of_cert' (c := 2339772) (t := 19) (a := 5) (ps := [2, 2, 3, 194981])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q033 : Nat.Prime 1226684497921 :=
  prime_of_cert' (c := 2339715) (t := 19) (a := 17) (ps := [3, 5, 7, 22283])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P033 : Nat.Prime 2453368995841 :=
  prime_of_cert' (c := 2339715) (t := 20) (a := 23) (ps := [3, 5, 7, 22283])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q034 : Nat.Prime 2453368995841 :=
  prime_of_cert' (c := 2339715) (t := 20) (a := 23) (ps := [3, 5, 7, 22283])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P034 : Nat.Prime 4906737991681 :=
  prime_of_cert' (c := 2339715) (t := 21) (a := 13) (ps := [3, 5, 7, 22283])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q035 : Nat.Prime 4906737991681 :=
  prime_of_cert' (c := 2339715) (t := 21) (a := 13) (ps := [3, 5, 7, 22283])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P035 : Nat.Prime 9813475983361 :=
  prime_of_cert' (c := 2339715) (t := 22) (a := 13) (ps := [3, 5, 7, 22283])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q036 : Nat.Prime 9813035581441 :=
  prime_of_cert' (c := 2339610) (t := 22) (a := 34) (ps := [2, 3, 5, 7, 13, 857])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P036 : Nat.Prime 19626071162881 :=
  prime_of_cert' (c := 2339610) (t := 23) (a := 11) (ps := [2, 3, 5, 7, 13, 857])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q037 : Nat.Prime 19616810139649 :=
  prime_of_cert' (c := 2338506) (t := 23) (a := 13) (ps := [2, 3, 3, 129917])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P037 : Nat.Prime 39233620279297 :=
  prime_of_cert' (c := 2338506) (t := 24) (a := 5) (ps := [2, 3, 3, 129917])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q038 : Nat.Prime 39229795074049 :=
  prime_of_cert' (c := 2338278) (t := 24) (a := 7) (ps := [2, 3, 389713])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P038 : Nat.Prime 78459590148097 :=
  prime_of_cert' (c := 2338278) (t := 25) (a := 5) (ps := [2, 3, 389713])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q039 : Nat.Prime 78459086831617 :=
  prime_of_cert' (c := 2338263) (t := 25) (a := 5) (ps := [3, 3, 73, 3559])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P039 : Nat.Prime 156918173663233 :=
  prime_of_cert' (c := 2338263) (t := 26) (a := 13) (ps := [3, 3, 73, 3559])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q040 : Nat.Prime 156874485792769 :=
  prime_of_cert' (c := 2337612) (t := 26) (a := 7) (ps := [2, 2, 3, 83, 2347])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P040 : Nat.Prime 313748971585537 :=
  prime_of_cert' (c := 2337612) (t := 27) (a := 5) (ps := [2, 2, 3, 83, 2347])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q041 : Nat.Prime 313610056237057 :=
  prime_of_cert' (c := 2336577) (t := 27) (a := 5) (ps := [3, 43, 59, 307])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P041 : Nat.Prime 627220112474113 :=
  prime_of_cert' (c := 2336577) (t := 28) (a := 5) (ps := [3, 43, 59, 307])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q042 : Nat.Prime 627136360611841 :=
  prime_of_cert' (c := 2336265) (t := 28) (a := 7) (ps := [3, 3, 5, 193, 269])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P042 : Nat.Prime 1254272721223681 :=
  prime_of_cert' (c := 2336265) (t := 29) (a := 14) (ps := [3, 3, 5, 193, 269])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q043 : Nat.Prime 1254269499998209 :=
  prime_of_cert' (c := 2336259) (t := 29) (a := 13) (ps := [3, 17, 19, 2411])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P043 : Nat.Prime 2508538999996417 :=
  prime_of_cert' (c := 2336259) (t := 30) (a := 23) (ps := [3, 17, 19, 2411])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q044 : Nat.Prime 2508303850536961 :=
  prime_of_cert' (c := 2336040) (t := 30) (a := 17) (ps := [2, 2, 2, 3, 3, 3, 3, 5, 7, 103])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P044 : Nat.Prime 5016607701073921 :=
  prime_of_cert' (c := 2336040) (t := 31) (a := 11) (ps := [2, 2, 2, 3, 3, 3, 3, 5, 7, 103])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q045 : Nat.Prime 5016607701073921 :=
  prime_of_cert' (c := 2336040) (t := 31) (a := 11) (ps := [2, 2, 2, 3, 3, 3, 3, 5, 7, 103])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P045 : Nat.Prime 10033215402147841 :=
  prime_of_cert' (c := 2336040) (t := 32) (a := 13) (ps := [2, 2, 2, 3, 3, 3, 3, 5, 7, 103])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q046 : Nat.Prime 10031939796860929 :=
  prime_of_cert' (c := 2335743) (t := 32) (a := 7) (ps := [3, 3, 3, 86509])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P046 : Nat.Prime 20063879593721857 :=
  prime_of_cert' (c := 2335743) (t := 33) (a := 5) (ps := [3, 3, 3, 86509])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q047 : Nat.Prime 20060916066287617 :=
  prime_of_cert' (c := 2335398) (t := 33) (a := 7) (ps := [2, 3, 13, 79, 379])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P047 : Nat.Prime 40121832132575233 :=
  prime_of_cert' (c := 2335398) (t := 34) (a := 5) (ps := [2, 3, 13, 79, 379])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

end Erdos287
