import RequestProject.PowMod

/-!
# Certified primes, block 2

Kernel-checked Lucas primality certificates for the prime pairs
`(q_i, P_i = 2 * q_i - 1)` with `48 ≤ i < 72`.
-/

namespace Erdos287

set_option maxRecDepth 100000

theorem prime_q048 : Nat.Prime 40119100533374977 :=
  prime_of_cert' (c := 2335239) (t := 34) (a := 10) (ps := [3, 3, 17, 15263])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P048 : Nat.Prime 80238201066749953 :=
  prime_of_cert' (c := 2335239) (t := 35) (a := 5) (ps := [3, 3, 17, 15263])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q049 : Nat.Prime 80236757957738497 :=
  prime_of_cert' (c := 2335197) (t := 35) (a := 7) (ps := [3, 73, 10663])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P049 : Nat.Prime 160473515915476993 :=
  prime_of_cert' (c := 2335197) (t := 36) (a := 7) (ps := [3, 73, 10663])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q050 : Nat.Prime 160424656367517697 :=
  prime_of_cert' (c := 2334486) (t := 36) (a := 5) (ps := [2, 3, 7, 11, 31, 163])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P050 : Nat.Prime 320849312735035393 :=
  prime_of_cert' (c := 2334486) (t := 37) (a := 19) (ps := [2, 3, 7, 11, 31, 163])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q051 : Nat.Prime 320700466348425217 :=
  prime_of_cert' (c := 2333403) (t := 37) (a := 5) (ps := [3, 3, 17, 101, 151])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P051 : Nat.Prime 641400932696850433 :=
  prime_of_cert' (c := 2333403) (t := 38) (a := 5) (ps := [3, 3, 17, 101, 151])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q052 : Nat.Prime 641345682237554689 :=
  prime_of_cert' (c := 2333202) (t := 38) (a := 7) (ps := [2, 3, 71, 5477])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P052 : Nat.Prime 1282691364475109377 :=
  prime_of_cert' (c := 2333202) (t := 39) (a := 7) (ps := [2, 3, 71, 5477])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q053 : Nat.Prime 1282214726184468481 :=
  prime_of_cert' (c := 2332335) (t := 39) (a := 13) (ps := [3, 5, 61, 2549])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P053 : Nat.Prime 2564429452368936961 :=
  prime_of_cert' (c := 2332335) (t := 40) (a := 22) (ps := [3, 5, 61, 2549])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q054 : Nat.Prime 2563839014624821249 :=
  prime_of_cert' (c := 2331798) (t := 40) (a := 19) (ps := [2, 3, 7, 59, 941])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P054 : Nat.Prime 5127678029249642497 :=
  prime_of_cert' (c := 2331798) (t := 41) (a := 19) (ps := [2, 3, 7, 59, 941])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q055 : Nat.Prime 5125402040180146177 :=
  prime_of_cert' (c := 2330763) (t := 41) (a := 7) (ps := [3, 776921])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P055 : Nat.Prime 10250804080360292353 :=
  prime_of_cert' (c := 2330763) (t := 42) (a := 13) (ps := [3, 776921])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q056 : Nat.Prime 10247004168174698497 :=
  prime_of_cert' (c := 2329899) (t := 42) (a := 5) (ps := [3, 11, 13, 5431])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P056 : Nat.Prime 20494008336349396993 :=
  prime_of_cert' (c := 2329899) (t := 43) (a := 10) (ps := [3, 11, 13, 5431])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q057 : Nat.Prime 20485484922210877441 :=
  prime_of_cert' (c := 2328930) (t := 43) (a := 7) (ps := [2, 3, 3, 5, 113, 229])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P057 : Nat.Prime 40970969844421754881 :=
  prime_of_cert' (c := 2328930) (t := 44) (a := 31) (ps := [2, 3, 3, 5, 113, 229])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q058 : Nat.Prime 40964161668422565889 :=
  prime_of_cert' (c := 2328543) (t := 44) (a := 19) (ps := [3, 3, 7, 23, 1607])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P058 : Nat.Prime 81928323336845131777 :=
  prime_of_cert' (c := 2328543) (t := 45) (a := 5) (ps := [3, 3, 7, 23, 1607])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q059 : Nat.Prime 81908796010335830017 :=
  prime_of_cert' (c := 2327988) (t := 45) (a := 7) (ps := [2, 2, 3, 13, 14923])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P059 : Nat.Prime 163817592020671660033 :=
  prime_of_cert' (c := 2327988) (t := 46) (a := 10) (ps := [2, 2, 3, 13, 14923])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q060 : Nat.Prime 163749826920028569601 :=
  prime_of_cert' (c := 2327025) (t := 46) (a := 21) (ps := [3, 5, 5, 19, 23, 71])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P060 : Nat.Prime 327499653840057139201 :=
  prime_of_cert' (c := 2327025) (t := 47) (a := 7) (ps := [3, 5, 5, 19, 23, 71])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q061 : Nat.Prime 327376790012722937857 :=
  prime_of_cert' (c := 2326152) (t := 47) (a := 5) (ps := [2, 2, 2, 3, 103, 941])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P061 : Nat.Prime 654753580025445875713 :=
  prime_of_cert' (c := 2326152) (t := 48) (a := 5) (ps := [2, 2, 2, 3, 103, 941])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q062 : Nat.Prime 654663226557921755137 :=
  prime_of_cert' (c := 2325831) (t := 48) (a := 13) (ps := [3, 389, 1993])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P062 : Nat.Prime 1309326453115843510273 :=
  prime_of_cert' (c := 2325831) (t := 49) (a := 10) (ps := [3, 389, 1993])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q063 : Nat.Prime 1308125680865195851777 :=
  prime_of_cert' (c := 2323698) (t := 49) (a := 5) (ps := [2, 3, 13, 31, 31, 31])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P063 : Nat.Prime 2616251361730391703553 :=
  prime_of_cert' (c := 2323698) (t := 50) (a := 10) (ps := [2, 3, 13, 31, 31, 31])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q064 : Nat.Prime 2614707752958110466049 :=
  prime_of_cert' (c := 2322327) (t := 50) (a := 22) (ps := [3, 7, 110587])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P064 : Nat.Prime 5229415505916220932097 :=
  prime_of_cert' (c := 2322327) (t := 51) (a := 5) (ps := [3, 7, 110587])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q065 : Nat.Prime 5227780699251485442049 :=
  prime_of_cert' (c := 2321601) (t := 51) (a := 13) (ps := [3, 773867])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P065 : Nat.Prime 10455561398502970884097 :=
  prime_of_cert' (c := 2321601) (t := 52) (a := 5) (ps := [3, 773867])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q066 : Nat.Prime 10454467023793519853569 :=
  prime_of_cert' (c := 2321358) (t := 52) (a := 17) (ps := [2, 3, 13, 29761])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P066 : Nat.Prime 20908934047587039707137 :=
  prime_of_cert' (c := 2321358) (t := 53) (a := 10) (ps := [2, 3, 13, 29761])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q067 : Nat.Prime 20908934047587039707137 :=
  prime_of_cert' (c := 2321358) (t := 53) (a := 10) (ps := [2, 3, 13, 29761])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P067 : Nat.Prime 41817868095174079414273 :=
  prime_of_cert' (c := 2321358) (t := 54) (a := 5) (ps := [2, 3, 13, 29761])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q068 : Nat.Prime 41815057849006600224769 :=
  prime_of_cert' (c := 2321202) (t := 54) (a := 7) (ps := [2, 3, 13, 29759])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P068 : Nat.Prime 83630115698013200449537 :=
  prime_of_cert' (c := 2321202) (t := 55) (a := 7) (ps := [2, 3, 13, 29759])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q069 : Nat.Prime 83559319111870936252417 :=
  prime_of_cert' (c := 2319237) (t := 55) (a := 10) (ps := [3, 3, 439, 587])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P069 : Nat.Prime 167118638223741872504833 :=
  prime_of_cert' (c := 2319237) (t := 56) (a := 7) (ps := [3, 3, 439, 587])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q070 : Nat.Prime 167002337266964656816129 :=
  prime_of_cert' (c := 2317623) (t := 56) (a := 17) (ps := [3, 7, 11, 79, 127])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P070 : Nat.Prime 334004674533929313632257 :=
  prime_of_cert' (c := 2317623) (t := 57) (a := 17) (ps := [3, 7, 11, 79, 127])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q071 : Nat.Prime 333861568152169988751361 :=
  prime_of_cert' (c := 2316630) (t := 57) (a := 22) (ps := [2, 3, 5, 31, 47, 53])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P071 : Nat.Prime 667723136304339977502721 :=
  prime_of_cert' (c := 2316630) (t := 58) (a := 7) (ps := [2, 3, 5, 31, 47, 53])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

end Erdos287
