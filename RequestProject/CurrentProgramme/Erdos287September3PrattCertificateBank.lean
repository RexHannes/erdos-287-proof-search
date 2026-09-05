import RequestProject.CurrentProgramme.Erdos287September3PrattEngine

/-!
# Erdős Problem #287 — the primality certificate bank for the September-3 finite extension

Every prime used by the 24 new window certificates of
`Erdos287September3FiniteExtension24Window.lean` is certified here, from the bottom up:

* small primes (`< 10^9`) by `norm_num` trial division;
* every larger prime by an explicit **recursive Pratt certificate**
  (`Erdos287.Pratt.prime_of_certificate`): the full factorisation of `p - 1`, each of whose
  bases is itself certified earlier in this file, together with a Lucas witness whose two
  modular-exponentiation side conditions are closed by kernel computation (`decide`) on the
  proved-correct `Erdos287.Pratt.powMod`.

No `native_decide`, no `axiom`, no `sorry`, no `unsafe`, no `implemented_by`.
-/

set_option maxRecDepth 100000

namespace Erdos287
namespace Certificates

/-! ### Leaf primes (trial division) -/
theorem prime_2 : Nat.Prime 2 := by norm_num
theorem prime_3 : Nat.Prime 3 := by norm_num
theorem prime_5 : Nat.Prime 5 := by norm_num
theorem prime_7 : Nat.Prime 7 := by norm_num
theorem prime_11 : Nat.Prime 11 := by norm_num
theorem prime_13 : Nat.Prime 13 := by norm_num
theorem prime_17 : Nat.Prime 17 := by norm_num
theorem prime_19 : Nat.Prime 19 := by norm_num
theorem prime_23 : Nat.Prime 23 := by norm_num
theorem prime_31 : Nat.Prime 31 := by norm_num
theorem prime_37 : Nat.Prime 37 := by norm_num
theorem prime_53 : Nat.Prime 53 := by norm_num
theorem prime_59 : Nat.Prime 59 := by norm_num
theorem prime_61 : Nat.Prime 61 := by norm_num
theorem prime_67 : Nat.Prime 67 := by norm_num
theorem prime_89 : Nat.Prime 89 := by norm_num
theorem prime_101 : Nat.Prime 101 := by norm_num
theorem prime_109 : Nat.Prime 109 := by norm_num
theorem prime_127 : Nat.Prime 127 := by norm_num
theorem prime_137 : Nat.Prime 137 := by norm_num
theorem prime_149 : Nat.Prime 149 := by norm_num
theorem prime_181 : Nat.Prime 181 := by norm_num
theorem prime_193 : Nat.Prime 193 := by norm_num
theorem prime_223 : Nat.Prime 223 := by norm_num
theorem prime_263 : Nat.Prime 263 := by norm_num
theorem prime_1019 : Nat.Prime 1019 := by norm_num
theorem prime_1063 : Nat.Prime 1063 := by norm_num
theorem prime_1213 : Nat.Prime 1213 := by norm_num
theorem prime_1511 : Nat.Prime 1511 := by norm_num
theorem prime_2099 : Nat.Prime 2099 := by norm_num
theorem prime_2741 : Nat.Prime 2741 := by norm_num
theorem prime_3079 : Nat.Prime 3079 := by norm_num
theorem prime_3593 : Nat.Prime 3593 := by norm_num
theorem prime_3767 : Nat.Prime 3767 := by norm_num
theorem prime_4919 : Nat.Prime 4919 := by norm_num
theorem prime_5693 : Nat.Prime 5693 := by norm_num
theorem prime_8369 : Nat.Prime 8369 := by norm_num
theorem prime_10321 : Nat.Prime 10321 := by norm_num
theorem prime_10331 : Nat.Prime 10331 := by norm_num
theorem prime_18233 : Nat.Prime 18233 := by norm_num
theorem prime_32297 : Nat.Prime 32297 := by norm_num
theorem prime_52529 : Nat.Prime 52529 := by norm_num
theorem prime_62653 : Nat.Prime 62653 := by norm_num
theorem prime_74707 : Nat.Prime 74707 := by norm_num
theorem prime_82567 : Nat.Prime 82567 := by norm_num
theorem prime_102559 : Nat.Prime 102559 := by norm_num
theorem prime_105277 : Nat.Prime 105277 := by norm_num
theorem prime_174929 : Nat.Prime 174929 := by norm_num
theorem prime_354041 : Nat.Prime 354041 := by norm_num
theorem prime_360193 : Nat.Prime 360193 := by norm_num
theorem prime_401371 : Nat.Prime 401371 := by norm_num
theorem prime_692957 : Nat.Prime 692957 := by norm_num
theorem prime_730727 : Nat.Prime 730727 := by norm_num
theorem prime_847993 : Nat.Prime 847993 := by norm_num
theorem prime_978343 : Nat.Prime 978343 := by norm_num
theorem prime_1093837 : Nat.Prime 1093837 := by norm_num
theorem prime_1132643 : Nat.Prime 1132643 := by norm_num
theorem prime_1211141 : Nat.Prime 1211141 := by norm_num
theorem prime_1443341 : Nat.Prime 1443341 := by norm_num
theorem prime_7748261 : Nat.Prime 7748261 := by norm_num
theorem prime_14150533 : Nat.Prime 14150533 := by norm_num
theorem prime_17812411 : Nat.Prime 17812411 := by norm_num
theorem prime_31249997 : Nat.Prime 31249997 := by norm_num
theorem prime_33333331 : Nat.Prime 33333331 := by norm_num
theorem prime_41335429 : Nat.Prime 41335429 := by norm_num
theorem prime_49946341 : Nat.Prime 49946341 := by norm_num
theorem prime_63058973 : Nat.Prime 63058973 := by norm_num
theorem prime_73754617 : Nat.Prime 73754617 := by norm_num
theorem prime_208172369 : Nat.Prime 208172369 := by norm_num
theorem prime_239812619 : Nat.Prime 239812619 := by norm_num
theorem prime_249880819 : Nat.Prime 249880819 := by norm_num
theorem prime_275657819 : Nat.Prime 275657819 := by norm_num

/-! ### Recursive Pratt certificates -/

/-- Pratt certificate: `1999999861` is prime.
`1999999861 - 1 = 2^2 * 3^1 * 5^1 * 33333331^1`; Lucas base `2`. -/
theorem prime_1999999861 : Nat.Prime 1999999861 :=
  Pratt.prime_of_certificate (p := 1999999861) (a := 2) (f := 31)
    (l := [(2, 2), (3, 1), (5, 1), (33333331, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_5, prime_33333331, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `1333333241` is prime.
`1333333241 - 1 = 2^3 * 5^1 * 33333331^1`; Lucas base `3`. -/
theorem prime_1333333241 : Nat.Prime 1333333241 :=
  Pratt.prime_of_certificate (p := 1333333241) (a := 3) (f := 31)
    (l := [(2, 3), (5, 1), (33333331, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_5, prime_33333331, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `2666666411` is prime.
`2666666411 - 1 = 2^1 * 5^1 * 17^1 * 149^1 * 105277^1`; Lucas base `2`. -/
theorem prime_2666666411 : Nat.Prime 2666666411 :=
  Pratt.prime_of_certificate (p := 2666666411) (a := 2) (f := 32)
    (l := [(2, 1), (5, 1), (17, 1), (149, 1), (105277, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_5, prime_17, prime_149, prime_105277, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `3999999617` is prime.
`3999999617 - 1 = 2^7 * 31249997^1`; Lucas base `3`. -/
theorem prime_3999999617 : Nat.Prime 3999999617 :=
  Pratt.prime_of_certificate (p := 3999999617) (a := 3) (f := 32)
    (l := [(2, 7), (31249997, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_31249997, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), trivial⟩

/-- Pratt certificate: `3999999599` is prime.
`3999999599 - 1 = 2^1 * 7^1 * 17^1 * 23^1 * 730727^1`; Lucas base `7`. -/
theorem prime_3999999599 : Nat.Prime 3999999599 :=
  Pratt.prime_of_certificate (p := 3999999599) (a := 7) (f := 32)
    (l := [(2, 1), (7, 1), (17, 1), (23, 1), (730727, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_7, prime_17, prime_23, prime_730727, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `5333332799` is prime.
`5333332799 - 1 = 2^1 * 32297^1 * 82567^1`; Lucas base `7`. -/
theorem prime_5333332799 : Nat.Prime 5333332799 :=
  Pratt.prime_of_certificate (p := 5333332799) (a := 7) (f := 33)
    (l := [(2, 1), (32297, 1), (82567, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_32297, prime_82567, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `15999998191` is prime.
`15999998191 - 1 = 2^1 * 3^1 * 5^1 * 11^2 * 59^1 * 74707^1`; Lucas base `3`. -/
theorem prime_15999998191 : Nat.Prime 15999998191 :=
  Pratt.prime_of_certificate (p := 15999998191) (a := 3) (f := 34)
    (l := [(2, 1), (3, 1), (5, 1), (11, 2), (59, 1), (74707, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_5, prime_11, prime_59, prime_74707, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `10666665461` is prime.
`10666665461 - 1 = 2^2 * 5^1 * 11^2 * 59^1 * 74707^1`; Lucas base `2`. -/
theorem prime_10666665461 : Nat.Prime 10666665461 :=
  Pratt.prime_of_certificate (p := 10666665461) (a := 2) (f := 34)
    (l := [(2, 2), (5, 1), (11, 2), (59, 1), (74707, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_5, prime_11, prime_59, prime_74707, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `12799998553` is prime.
`12799998553 - 1 = 2^3 * 3^1 * 11^2 * 59^1 * 74707^1`; Lucas base `5`. -/
theorem prime_12799998553 : Nat.Prime 12799998553 :=
  Pratt.prime_of_certificate (p := 12799998553) (a := 5) (f := 34)
    (l := [(2, 3), (3, 1), (11, 2), (59, 1), (74707, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_11, prime_59, prime_74707, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `63999992741` is prime.
`63999992741 - 1 = 2^2 * 5^1 * 23^1 * 193^1 * 263^1 * 2741^1`; Lucas base `2`. -/
theorem prime_63999992741 : Nat.Prime 63999992741 :=
  Pratt.prime_of_certificate (p := 63999992741) (a := 2) (f := 36)
    (l := [(2, 2), (5, 1), (23, 1), (193, 1), (263, 1), (2741, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_5, prime_23, prime_193, prime_263, prime_2741, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `127999985483` is prime.
`127999985483 - 1 = 2^1 * 63999992741^1`; Lucas base `2`. -/
theorem prime_127999985483 : Nat.Prime 127999985483 :=
  Pratt.prime_of_certificate (p := 127999985483) (a := 2) (f := 37)
    (l := [(2, 1), (63999992741, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_63999992741, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), trivial⟩

/-- Pratt certificate: `85333323631` is prime.
`85333323631 - 1 = 2^1 * 3^1 * 5^1 * 53^1 * 149^1 * 360193^1`; Lucas base `3`. -/
theorem prime_85333323631 : Nat.Prime 85333323631 :=
  Pratt.prime_of_certificate (p := 85333323631) (a := 3) (f := 37)
    (l := [(2, 1), (3, 1), (5, 1), (53, 1), (149, 1), (360193, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_5, prime_53, prime_149, prime_360193, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `127999985447` is prime.
`127999985447 - 1 = 2^1 * 3593^1 * 17812411^1`; Lucas base `5`. -/
theorem prime_127999985447 : Nat.Prime 127999985447 :=
  Pratt.prime_of_certificate (p := 127999985447) (a := 5) (f := 37)
    (l := [(2, 1), (3593, 1), (17812411, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3593, prime_17812411, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `255999970861` is prime.
`255999970861 - 1 = 2^2 * 3^1 * 5^1 * 3767^1 * 1132643^1`; Lucas base `2`. -/
theorem prime_255999970861 : Nat.Prime 255999970861 :=
  Pratt.prime_of_certificate (p := 255999970861) (a := 2) (f := 38)
    (l := [(2, 2), (3, 1), (5, 1), (3767, 1), (1132643, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_5, prime_3767, prime_1132643, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `170666647241` is prime.
`170666647241 - 1 = 2^3 * 5^1 * 3767^1 * 1132643^1`; Lucas base `6`. -/
theorem prime_170666647241 : Nat.Prime 170666647241 :=
  Pratt.prime_of_certificate (p := 170666647241) (a := 6) (f := 38)
    (l := [(2, 3), (5, 1), (3767, 1), (1132643, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_5, prime_3767, prime_1132643, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `1023999883441` is prime.
`1023999883441 - 1 = 2^4 * 3^1 * 5^1 * 3767^1 * 1132643^1`; Lucas base `11`. -/
theorem prime_1023999883441 : Nat.Prime 1023999883441 :=
  Pratt.prime_of_certificate (p := 1023999883441) (a := 11) (f := 40)
    (l := [(2, 4), (3, 1), (5, 1), (3767, 1), (1132643, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_5, prime_3767, prime_1132643, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `511999941721` is prime.
`511999941721 - 1 = 2^3 * 3^1 * 5^1 * 3767^1 * 1132643^1`; Lucas base `17`. -/
theorem prime_511999941721 : Nat.Prime 511999941721 :=
  Pratt.prime_of_certificate (p := 511999941721) (a := 17) (f := 39)
    (l := [(2, 3), (3, 1), (5, 1), (3767, 1), (1132643, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_5, prime_3767, prime_1132643, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `1023999883183` is prime.
`1023999883183 - 1 = 2^1 * 3^2 * 17^1 * 67^1 * 49946341^1`; Lucas base `3`. -/
theorem prime_1023999883183 : Nat.Prime 1023999883183 :=
  Pratt.prime_of_certificate (p := 1023999883183) (a := 3) (f := 40)
    (l := [(2, 1), (3, 2), (17, 1), (67, 1), (49946341, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_17, prime_67, prime_49946341, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `682666588789` is prime.
`682666588789 - 1 = 2^2 * 3^1 * 17^1 * 67^1 * 49946341^1`; Lucas base `2`. -/
theorem prime_682666588789 : Nat.Prime 682666588789 :=
  Pratt.prime_of_certificate (p := 682666588789) (a := 2) (f := 40)
    (l := [(2, 2), (3, 1), (17, 1), (67, 1), (49946341, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_17, prime_67, prime_49946341, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `4095999532733` is prime.
`4095999532733 - 1 = 2^2 * 1023999883183^1`; Lucas base `2`. -/
theorem prime_4095999532733 : Nat.Prime 4095999532733 :=
  Pratt.prime_of_certificate (p := 4095999532733) (a := 2) (f := 42)
    (l := [(2, 2), (1023999883183, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_1023999883183, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), trivial⟩

/-- Pratt certificate: `8191999065043` is prime.
`8191999065043 - 1 = 2^1 * 3^2 * 13^1 * 127^1 * 275657819^1`; Lucas base `2`. -/
theorem prime_8191999065043 : Nat.Prime 8191999065043 :=
  Pratt.prime_of_certificate (p := 8191999065043) (a := 2) (f := 43)
    (l := [(2, 1), (3, 2), (13, 1), (127, 1), (275657819, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_13, prime_127, prime_275657819, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `2047999766261` is prime.
`2047999766261 - 1 = 2^2 * 5^1 * 7^1 * 61^1 * 239812619^1`; Lucas base `2`. -/
theorem prime_2047999766261 : Nat.Prime 2047999766261 :=
  Pratt.prime_of_certificate (p := 2047999766261) (a := 2) (f := 41)
    (l := [(2, 2), (5, 1), (7, 1), (61, 1), (239812619, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_5, prime_7, prime_61, prime_239812619, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `5461332709979` is prime.
`5461332709979 - 1 = 2^1 * 1511^1 * 10331^1 * 174929^1`; Lucas base `2`. -/
theorem prime_5461332709979 : Nat.Prime 5461332709979 :=
  Pratt.prime_of_certificate (p := 5461332709979) (a := 2) (f := 43)
    (l := [(2, 1), (1511, 1), (10331, 1), (174929, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_1511, prime_10331, prime_174929, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `4591927727` is prime.
`4591927727 - 1 = 2^1 * 2099^1 * 1093837^1`; Lucas base `5`. -/
theorem prime_4591927727 : Nat.Prime 4591927727 :=
  Pratt.prime_of_certificate (p := 4591927727) (a := 5) (f := 33)
    (l := [(2, 1), (2099, 1), (1093837, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_2099, prime_1093837, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `8191999064969` is prime.
`8191999064969 - 1 = 2^3 * 223^1 * 4591927727^1`; Lucas base `3`. -/
theorem prime_8191999064969 : Nat.Prime 8191999064969 :=
  Pratt.prime_of_certificate (p := 8191999064969) (a := 3) (f := 43)
    (l := [(2, 3), (223, 1), (4591927727, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_223, prime_4591927727, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `3581201777` is prime.
`3581201777 - 1 = 2^4 * 17^1 * 19^1 * 692957^1`; Lucas base `3`. -/
theorem prime_3581201777 : Nat.Prime 3581201777 :=
  Pratt.prime_of_certificate (p := 3581201777) (a := 3) (f := 32)
    (l := [(2, 4), (17, 1), (19, 1), (692957, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_17, prime_19, prime_692957, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `10922665419851` is prime.
`10922665419851 - 1 = 2^1 * 5^2 * 61^1 * 3581201777^1`; Lucas base `2`. -/
theorem prime_10922665419851 : Nat.Prime 10922665419851 :=
  Pratt.prime_of_certificate (p := 10922665419851) (a := 2) (f := 44)
    (l := [(2, 1), (5, 2), (61, 1), (3581201777, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_5, prime_61, prime_3581201777, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `16383998129777` is prime.
`16383998129777 - 1 = 2^4 * 4919^1 * 208172369^1`; Lucas base `3`. -/
theorem prime_16383998129777 : Nat.Prime 16383998129777 :=
  Pratt.prime_of_certificate (p := 16383998129777) (a := 3) (f := 44)
    (l := [(2, 4), (4919, 1), (208172369, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_4919, prime_208172369, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `32767996259233` is prime.
`32767996259233 - 1 = 2^5 * 3^2 * 13^1 * 10321^1 * 847993^1`; Lucas base `5`. -/
theorem prime_32767996259233 : Nat.Prime 32767996259233 :=
  Pratt.prime_of_certificate (p := 32767996259233) (a := 5) (f := 45)
    (l := [(2, 5), (3, 2), (13, 1), (10321, 1), (847993, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_13, prime_10321, prime_847993, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `21845330839489` is prime.
`21845330839489 - 1 = 2^6 * 3^1 * 13^1 * 10321^1 * 847993^1`; Lucas base `7`. -/
theorem prime_21845330839489 : Nat.Prime 21845330839489 :=
  Pratt.prime_of_certificate (p := 21845330839489) (a := 7) (f := 45)
    (l := [(2, 6), (3, 1), (13, 1), (10321, 1), (847993, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_13, prime_10321, prime_847993, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `43690661678971` is prime.
`43690661678971 - 1 = 2^1 * 3^2 * 5^1 * 62653^1 * 7748261^1`; Lucas base `2`. -/
theorem prime_43690661678971 : Nat.Prime 43690661678971 :=
  Pratt.prime_of_certificate (p := 43690661678971) (a := 2) (f := 46)
    (l := [(2, 1), (3, 2), (5, 1), (62653, 1), (7748261, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_5, prime_62653, prime_7748261, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `65535992518457` is prime.
`65535992518457 - 1 = 2^3 * 109^1 * 1019^1 * 73754617^1`; Lucas base `3`. -/
theorem prime_65535992518457 : Nat.Prime 65535992518457 :=
  Pratt.prime_of_certificate (p := 65535992518457) (a := 3) (f := 46)
    (l := [(2, 3), (109, 1), (1019, 1), (73754617, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_109, prime_1019, prime_73754617, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `262143970073653` is prime.
`262143970073653 - 1 = 2^2 * 3^1 * 19^1 * 18233^1 * 63058973^1`; Lucas base `2`. -/
theorem prime_262143970073653 : Nat.Prime 262143970073653 :=
  Pratt.prime_of_certificate (p := 262143970073653) (a := 2) (f := 48)
    (l := [(2, 2), (3, 1), (19, 1), (18233, 1), (63058973, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_19, prime_18233, prime_63058973, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `131071985036827` is prime.
`131071985036827 - 1 = 2^1 * 3^1 * 19^1 * 18233^1 * 63058973^1`; Lucas base `2`. -/
theorem prime_131071985036827 : Nat.Prime 131071985036827 :=
  Pratt.prime_of_certificate (p := 131071985036827) (a := 2) (f := 47)
    (l := [(2, 1), (3, 1), (19, 1), (18233, 1), (63058973, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_19, prime_18233, prime_63058973, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `30825960733` is prime.
`30825960733 - 1 = 2^2 * 3^2 * 7^1 * 101^1 * 1211141^1`; Lucas base `2`. -/
theorem prime_30825960733 : Nat.Prime 30825960733 :=
  Pratt.prime_of_certificate (p := 30825960733) (a := 2) (f := 35)
    (l := [(2, 2), (3, 2), (7, 1), (101, 1), (1211141, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_7, prime_101, prime_1211141, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `131071985036717` is prime.
`131071985036717 - 1 = 2^2 * 1063^1 * 30825960733^1`; Lucas base `2`. -/
theorem prime_131071985036717 : Nat.Prime 131071985036717 :=
  Pratt.prime_of_certificate (p := 131071985036717) (a := 2) (f := 47)
    (l := [(2, 2), (1063, 1), (30825960733, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_1063, prime_30825960733, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `3355657579` is prime.
`3355657579 - 1 = 2^1 * 3^3 * 7^1 * 13^2 * 52529^1`; Lucas base `2`. -/
theorem prime_3355657579 : Nat.Prime 3355657579 :=
  Pratt.prime_of_certificate (p := 3355657579) (a := 2) (f := 32)
    (l := [(2, 1), (3, 3), (7, 1), (13, 2), (52529, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_7, prime_13, prime_52529, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `134226303161` is prime.
`134226303161 - 1 = 2^3 * 5^1 * 3355657579^1`; Lucas base `3`. -/
theorem prime_134226303161 : Nat.Prime 134226303161 :=
  Pratt.prime_of_certificate (p := 134226303161) (a := 3) (f := 37)
    (l := [(2, 3), (5, 1), (3355657579, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_5, prime_3355657579, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `174762646715623` is prime.
`174762646715623 - 1 = 2^1 * 3^1 * 7^1 * 31^1 * 134226303161^1`; Lucas base `5`. -/
theorem prime_174762646715623 : Nat.Prime 174762646715623 :=
  Pratt.prime_of_certificate (p := 174762646715623) (a := 5) (f := 48)
    (l := [(2, 1), (3, 1), (7, 1), (31, 1), (134226303161, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_7, prime_31, prime_134226303161, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `1048575880293313` is prime.
`1048575880293313 - 1 = 2^6 * 3^1 * 7^2 * 37^1 * 3079^1 * 978343^1`; Lucas base `10`. -/
theorem prime_1048575880293313 : Nat.Prime 1048575880293313 :=
  Pratt.prime_of_certificate (p := 1048575880293313) (a := 10) (f := 50)
    (l := [(2, 6), (3, 1), (7, 2), (37, 1), (3079, 1), (978343, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_7, prime_37, prime_3079, prime_978343, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `524287940146657` is prime.
`524287940146657 - 1 = 2^5 * 3^1 * 7^2 * 37^1 * 3079^1 * 978343^1`; Lucas base `10`. -/
theorem prime_524287940146657 : Nat.Prime 524287940146657 :=
  Pratt.prime_of_certificate (p := 524287940146657) (a := 10) (f := 49)
    (l := [(2, 5), (3, 1), (7, 2), (37, 1), (3079, 1), (978343, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_7, prime_37, prime_3079, prime_978343, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `14563553892959` is prime.
`14563553892959 - 1 = 2^1 * 7^1 * 23^1 * 181^1 * 249880819^1`; Lucas base `7`. -/
theorem prime_14563553892959 : Nat.Prime 14563553892959 :=
  Pratt.prime_of_certificate (p := 14563553892959) (a := 7) (f := 44)
    (l := [(2, 1), (7, 1), (23, 1), (181, 1), (249880819, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_7, prime_23, prime_181, prime_249880819, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `2097151760586097` is prime.
`2097151760586097 - 1 = 2^4 * 3^2 * 14563553892959^1`; Lucas base `5`. -/
theorem prime_2097151760586097 : Nat.Prime 2097151760586097 :=
  Pratt.prime_of_certificate (p := 2097151760586097) (a := 5) (f := 51)
    (l := [(2, 4), (3, 2), (14563553892959, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_14563553892959, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `1048575880293049` is prime.
`1048575880293049 - 1 = 2^3 * 3^2 * 14563553892959^1`; Lucas base `14`. -/
theorem prime_1048575880293049 : Nat.Prime 1048575880293049 :=
  Pratt.prime_of_certificate (p := 1048575880293049) (a := 14) (f := 50)
    (l := [(2, 3), (3, 2), (14563553892959, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_14563553892959, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `1048575880293013` is prime.
`1048575880293013 - 1 = 2^2 * 3^3 * 19^1 * 354041^1 * 1443341^1`; Lucas base `2`. -/
theorem prime_1048575880293013 : Nat.Prime 1048575880293013 :=
  Pratt.prime_of_certificate (p := 1048575880293013) (a := 2) (f := 50)
    (l := [(2, 2), (3, 3), (19, 1), (354041, 1), (1443341, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_19, prime_354041, prime_1443341, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `4194303521172053` is prime.
`4194303521172053 - 1 = 2^2 * 1048575880293013^1`; Lucas base `2`. -/
theorem prime_4194303521172053 : Nat.Prime 4194303521172053 :=
  Pratt.prime_of_certificate (p := 4194303521172053) (a := 2) (f := 52)
    (l := [(2, 2), (1048575880293013, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_1048575880293013, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), trivial⟩

/-- Pratt certificate: `8388607042343977` is prime.
`8388607042343977 - 1 = 2^3 * 3^1 * 7^1 * 1213^1 * 102559^1 * 401371^1`; Lucas base `13`. -/
theorem prime_8388607042343977 : Nat.Prime 8388607042343977 :=
  Pratt.prime_of_certificate (p := 8388607042343977) (a := 13) (f := 53)
    (l := [(2, 3), (3, 1), (7, 1), (1213, 1), (102559, 1), (401371, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_7, prime_1213, prime_102559, prime_401371, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `4194303521171989` is prime.
`4194303521171989 - 1 = 2^2 * 3^1 * 7^1 * 1213^1 * 102559^1 * 401371^1`; Lucas base `2`. -/
theorem prime_4194303521171989 : Nat.Prime 4194303521171989 :=
  Pratt.prime_of_certificate (p := 4194303521171989) (a := 2) (f := 52)
    (l := [(2, 2), (3, 1), (7, 1), (1213, 1), (102559, 1), (401371, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_7, prime_1213, prime_102559, prime_401371, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `8388607042343971` is prime.
`8388607042343971 - 1 = 2^1 * 3^2 * 5^1 * 13^1 * 89^1 * 5693^1 * 14150533^1`; Lucas base `3`. -/
theorem prime_8388607042343971 : Nat.Prime 8388607042343971 :=
  Pratt.prime_of_certificate (p := 8388607042343971) (a := 3) (f := 53)
    (l := [(2, 1), (3, 2), (5, 1), (13, 1), (89, 1), (5693, 1), (14150533, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_5, prime_13, prime_89, prime_5693, prime_14150533, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `5592404694895981` is prime.
`5592404694895981 - 1 = 2^2 * 3^1 * 5^1 * 13^1 * 89^1 * 5693^1 * 14150533^1`; Lucas base `6`. -/
theorem prime_5592404694895981 : Nat.Prime 5592404694895981 :=
  Pratt.prime_of_certificate (p := 5592404694895981) (a := 6) (f := 53)
    (l := [(2, 2), (3, 1), (5, 1), (13, 1), (89, 1), (5693, 1), (14150533, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_5, prime_13, prime_89, prime_5693, prime_14150533, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `33554428169375797` is prime.
`33554428169375797 - 1 = 2^2 * 3^1 * 59^1 * 137^1 * 8369^1 * 41335429^1`; Lucas base `2`. -/
theorem prime_33554428169375797 : Nat.Prime 33554428169375797 :=
  Pratt.prime_of_certificate (p := 33554428169375797) (a := 2) (f := 55)
    (l := [(2, 2), (3, 1), (59, 1), (137, 1), (8369, 1), (41335429, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_59, prime_137, prime_8369, prime_41335429, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

/-- Pratt certificate: `16777214084687899` is prime.
`16777214084687899 - 1 = 2^1 * 3^1 * 59^1 * 137^1 * 8369^1 * 41335429^1`; Lucas base `3`. -/
theorem prime_16777214084687899 : Nat.Prime 16777214084687899 :=
  Pratt.prime_of_certificate (p := 16777214084687899) (a := 3) (f := 54)
    (l := [(2, 1), (3, 1), (59, 1), (137, 1), (8369, 1), (41335429, 1)])
    (by norm_num) (by norm_num)
    ⟨prime_2, prime_3, prime_59, prime_137, prime_8369, prime_41335429, trivial⟩
    (by decide) (by decide)
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), (by decide), trivial⟩

end Certificates
end Erdos287
