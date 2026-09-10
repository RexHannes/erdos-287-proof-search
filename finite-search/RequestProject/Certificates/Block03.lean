import RequestProject.PowMod

/-!
# Certified primes, block 3

Kernel-checked Lucas primality certificates for the prime pairs
`(q_i, P_i = 2 * q_i - 1)` with `72 ≤ i < 96`.
-/

namespace Erdos287

set_option maxRecDepth 100000

theorem prime_q072 : Nat.Prime 667523392653666841264129 :=
  prime_of_cert' (c := 2315937) (t := 58) (a := 7) (ps := [3, 13, 43, 1381])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P072 : Nat.Prime 1335046785307333682528257 :=
  prime_of_cert' (c := 2315937) (t := 59) (a := 10) (ps := [3, 13, 43, 1381])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q073 : Nat.Prime 1334313527230403727851521 :=
  prime_of_cert' (c := 2314665) (t := 59) (a := 7) (ps := [3, 3, 5, 51437])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P073 : Nat.Prime 2668627054460807455703041 :=
  prime_of_cert' (c := 2314665) (t := 60) (a := 17) (ps := [3, 3, 5, 51437])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q074 : Nat.Prime 2666264718297868026249217 :=
  prime_of_cert' (c := 2312616) (t := 60) (a := 5) (ps := [2, 2, 2, 3, 167, 577])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P074 : Nat.Prime 5332529436595736052498433 :=
  prime_of_cert' (c := 2312616) (t := 61) (a := 5) (ps := [2, 2, 2, 3, 167, 577])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q075 : Nat.Prime 5329063754552887870488577 :=
  prime_of_cert' (c := 2311113) (t := 61) (a := 10) (ps := [3, 7, 167, 659])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P075 : Nat.Prime 10658127509105775740977153 :=
  prime_of_cert' (c := 2311113) (t := 62) (a := 10) (ps := [3, 7, 167, 659])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q076 : Nat.Prime 10652579650825607593328641 :=
  prime_of_cert' (c := 2309910) (t := 62) (a := 7) (ps := [2, 3, 5, 37, 2081])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P076 : Nat.Prime 21305159301651215186657281 :=
  prime_of_cert' (c := 2309910) (t := 63) (a := 17) (ps := [2, 3, 5, 37, 2081])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q077 : Nat.Prime 21305159301651215186657281 :=
  prime_of_cert' (c := 2309910) (t := 63) (a := 17) (ps := [2, 3, 5, 37, 2081])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P077 : Nat.Prime 42610318603302430373314561 :=
  prime_of_cert' (c := 2309910) (t := 64) (a := 7) (ps := [2, 3, 5, 37, 2081])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q078 : Nat.Prime 42607828292852479583846401 :=
  prime_of_cert' (c := 2309775) (t := 64) (a := 17) (ps := [3, 5, 5, 13, 23, 103])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P078 : Nat.Prime 85215656585704959167692801 :=
  prime_of_cert' (c := 2309775) (t := 65) (a := 11) (ps := [3, 5, 5, 13, 23, 103])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q079 : Nat.Prime 85206802148549578582917121 :=
  prime_of_cert' (c := 2309535) (t := 65) (a := 14) (ps := [3, 3, 5, 17, 3019])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P079 : Nat.Prime 170413604297099157165834241 :=
  prime_of_cert' (c := 2309535) (t := 66) (a := 14) (ps := [3, 3, 5, 17, 3019])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q080 : Nat.Prime 170362248561597949774135297 :=
  prime_of_cert' (c := 2308839) (t := 66) (a := 10) (ps := [3, 13, 53, 1117])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P080 : Nat.Prime 340724497123195899548270593 :=
  prime_of_cert' (c := 2308839) (t := 67) (a := 5) (ps := [3, 13, 53, 1117])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q081 : Nat.Prime 340612045771322566121619457 :=
  prime_of_cert' (c := 2308077) (t := 67) (a := 5) (ps := [3, 3, 317, 809])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P081 : Nat.Prime 681224091542645132243238913 :=
  prime_of_cert' (c := 2308077) (t := 68) (a := 5) (ps := [3, 3, 317, 809])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q082 : Nat.Prime 680641469577821089764999169 :=
  prime_of_cert' (c := 2306103) (t := 68) (a := 29) (ps := [3, 167, 4603])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P082 : Nat.Prime 1361282939155642179529998337 :=
  prime_of_cert' (c := 2306103) (t := 69) (a := 5) (ps := [3, 167, 4603])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q083 : Nat.Prime 1360581667732936037215764481 :=
  prime_of_cert' (c := 2304915) (t := 69) (a := 7) (ps := [3, 5, 37, 4153])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P083 : Nat.Prime 2721163335465872074431528961 :=
  prime_of_cert' (c := 2304915) (t := 70) (a := 26) (ps := [3, 5, 37, 4153])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q084 : Nat.Prime 2720398312095647191906910209 :=
  prime_of_cert' (c := 2304267) (t := 70) (a := 11) (ps := [3, 7, 179, 613])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P084 : Nat.Prime 5440796624191294383813820417 :=
  prime_of_cert' (c := 2304267) (t := 71) (a := 5) (ps := [3, 7, 179, 613])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q085 : Nat.Prime 5438961984812699526648299521 :=
  prime_of_cert' (c := 2303490) (t := 71) (a := 13) (ps := [2, 3, 5, 7, 7, 1567])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P085 : Nat.Prime 10877923969625399053296599041 :=
  prime_of_cert' (c := 2303490) (t := 72) (a := 13) (ps := [2, 3, 5, 7, 7, 1567])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q086 : Nat.Prime 10872752978326656791787601921 :=
  prime_of_cert' (c := 2302395) (t := 72) (a := 7) (ps := [3, 5, 17, 9029])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P086 : Nat.Prime 21745505956653313583575203841 :=
  prime_of_cert' (c := 2302395) (t := 73) (a := 11) (ps := [3, 5, 17, 9029])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q087 : Nat.Prime 21723405281513483643975106561 :=
  prime_of_cert' (c := 2300055) (t := 73) (a := 14) (ps := [3, 5, 153337])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P087 : Nat.Prime 43446810563026967287950213121 :=
  prime_of_cert' (c := 2300055) (t := 74) (a := 11) (ps := [3, 5, 153337])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q088 : Nat.Prime 43411902829985594870530572289 :=
  prime_of_cert' (c := 2298207) (t := 74) (a := 11) (ps := [3, 503, 1523])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P088 : Nat.Prime 86823805659971189741061144577 :=
  prime_of_cert' (c := 2298207) (t := 75) (a := 7) (ps := [3, 503, 1523])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q089 : Nat.Prime 86810318581296114034330828801 :=
  prime_of_cert' (c := 2297850) (t := 75) (a := 7) (ps := [2, 3, 5, 5, 15319])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P089 : Nat.Prime 173620637162592228068661657601 :=
  prime_of_cert' (c := 2297850) (t := 76) (a := 7) (ps := [2, 3, 5, 5, 15319])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q090 : Nat.Prime 173480099536062027427102064641 :=
  prime_of_cert' (c := 2295990) (t := 76) (a := 23) (ps := [2, 3, 3, 5, 97, 263])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P090 : Nat.Prime 346960199072124054854204129281 :=
  prime_of_cert' (c := 2295990) (t := 77) (a := 14) (ps := [2, 3, 3, 5, 97, 263])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q091 : Nat.Prime 346941158490465124444702507009 :=
  prime_of_cert' (c := 2295864) (t := 77) (a := 7) (ps := [2, 2, 2, 3, 3, 3, 3, 3, 1181])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P091 : Nat.Prime 693882316980930248889405014017 :=
  prime_of_cert' (c := 2295864) (t := 78) (a := 5) (ps := [2, 2, 2, 3, 3, 3, 3, 3, 1181])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q092 : Nat.Prime 693081705856890460718455848961 :=
  prime_of_cert' (c := 2293215) (t := 78) (a := 38) (ps := [3, 5, 17, 17, 23, 23])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P092 : Nat.Prime 1386163411713780921436911697921 :=
  prime_of_cert' (c := 2293215) (t := 79) (a := 14) (ps := [3, 5, 17, 17, 23, 23])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q093 : Nat.Prime 1383577519385625229632215187457 :=
  prime_of_cert' (c := 2288937) (t := 79) (a := 11) (ps := [3, 7, 7, 23, 677])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P093 : Nat.Prime 2767155038771250459264430374913 :=
  prime_of_cert' (c := 2288937) (t := 80) (a := 5) (ps := [3, 7, 7, 23, 677])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q094 : Nat.Prime 2766288238958586770146166046721 :=
  prime_of_cert' (c := 2288220) (t := 80) (a := 13) (ps := [2, 2, 3, 5, 11, 3467])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P094 : Nat.Prime 5532576477917173540292332093441 :=
  prime_of_cert' (c := 2288220) (t := 81) (a := 7) (ps := [2, 2, 3, 5, 11, 3467])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q095 : Nat.Prime 5526889690861706324654514241537 :=
  prime_of_cert' (c := 2285868) (t := 81) (a := 5) (ps := [2, 2, 3, 13, 14653])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P095 : Nat.Prime 11053779381723412649309028483073 :=
  prime_of_cert' (c := 2285868) (t := 82) (a := 5) (ps := [2, 2, 3, 13, 14653])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

end Erdos287
