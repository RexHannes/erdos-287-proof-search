import RequestProject.PowMod

/-!
# Certified primes, block 4

Kernel-checked Lucas primality certificates for the prime pairs
`(q_i, P_i = 2 * q_i - 1)` with `96 ≤ i < 120`.
-/

namespace Erdos287

set_option maxRecDepth 100000

theorem prime_q096 : Nat.Prime 11048658371951525080124973121537 :=
  prime_of_cert' (c := 2284809) (t := 82) (a := 10) (ps := [3, 761603])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P096 : Nat.Prime 22097316743903050160249946243073 :=
  prime_of_cert' (c := 2284809) (t := 83) (a := 5) (ps := [3, 761603])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q097 : Nat.Prime 22084521473028248925064856076289 :=
  prime_of_cert' (c := 2283486) (t := 83) (a := 11) (ps := [2, 3, 23, 16547])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P097 : Nat.Prime 44169042946056497850129712152577 :=
  prime_of_cert' (c := 2283486) (t := 84) (a := 5) (ps := [2, 3, 23, 16547])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q098 : Nat.Prime 44098770506013938685462391554049 :=
  prime_of_cert' (c := 2279853) (t := 84) (a := 13) (ps := [3, 3, 3, 17, 4967])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P098 : Nat.Prime 88197541012027877370924783108097 :=
  prime_of_cert' (c := 2279853) (t := 85) (a := 5) (ps := [3, 3, 3, 17, 4967])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q099 : Nat.Prime 88010689437348240285682196545537 :=
  prime_of_cert' (c := 2275023) (t := 85) (a := 5) (ps := [3, 758341])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P099 : Nat.Prime 176021378874696480571364393091073 :=
  prime_of_cert' (c := 2275023) (t := 86) (a := 5) (ps := [3, 758341])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q100 : Nat.Prime 175651853772969794559307004510209 :=
  prime_of_cert' (c := 2270247) (t := 86) (a := 11) (ps := [3, 7, 108107])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P100 : Nat.Prime 351303707545939589118614009020417 :=
  prime_of_cert' (c := 2270247) (t := 87) (a := 5) (ps := [3, 7, 108107])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q101 : Nat.Prime 350341828135414848645017389498369 :=
  prime_of_cert' (c := 2264031) (t := 87) (a := 17) (ps := [3, 3, 3, 3, 3, 7, 11, 11, 11])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P101 : Nat.Prime 700683656270829697290034778996737 :=
  prime_of_cert' (c := 2264031) (t := 88) (a := 17) (ps := [3, 3, 3, 3, 3, 7, 11, 11, 11])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q102 : Nat.Prime 699991028818849527026228718993409 :=
  prime_of_cert' (c := 2261793) (t := 88) (a := 7) (ps := [3, 753931])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P102 : Nat.Prime 1399982057637699054052457437986817 :=
  prime_of_cert' (c := 2261793) (t := 89) (a := 5) (ps := [3, 753931])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q103 : Nat.Prime 1399363706588076006605145325436929 :=
  prime_of_cert' (c := 2260794) (t := 89) (a := 13) (ps := [2, 3, 47, 8017])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P103 : Nat.Prime 2798727413176152013210290650873857 :=
  prime_of_cert' (c := 2260794) (t := 90) (a := 5) (ps := [2, 3, 47, 8017])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q104 : Nat.Prime 2797137898165709584937320175370241 :=
  prime_of_cert' (c := 2259510) (t := 90) (a := 13) (ps := [2, 3, 5, 11, 41, 167])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P104 : Nat.Prime 5594275796331419169874640350740481 :=
  prime_of_cert' (c := 2259510) (t := 91) (a := 26) (ps := [2, 3, 5, 11, 41, 167])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q105 : Nat.Prime 5593005669851112369712593849286657 :=
  prime_of_cert' (c := 2258997) (t := 91) (a := 7) (ps := [3, 13, 57923])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P105 : Nat.Prime 11186011339702224739425187698573313 :=
  prime_of_cert' (c := 2258997) (t := 92) (a := 5) (ps := [3, 13, 57923])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q106 : Nat.Prime 11176102867627784555704895108284417 :=
  prime_of_cert' (c := 2256996) (t := 92) (a := 10) (ps := [2, 2, 3, 7, 97, 277])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P106 : Nat.Prime 22352205735255569111409790216568833 :=
  prime_of_cert' (c := 2256996) (t := 93) (a := 5) (ps := [2, 2, 3, 7, 97, 277])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q107 : Nat.Prime 22347719440553198893293555790381057 :=
  prime_of_cert' (c := 2256543) (t := 93) (a := 5) (ps := [3, 3, 250727])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P107 : Nat.Prime 44695438881106397786587111580762113 :=
  prime_of_cert' (c := 2256543) (t := 94) (a := 7) (ps := [3, 3, 250727])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q108 : Nat.Prime 44664064528750749108900068176429057 :=
  prime_of_cert' (c := 2254959) (t := 94) (a := 31) (ps := [3, 3, 3, 3, 7, 41, 97])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P108 : Nat.Prime 89328129057501498217800136352858113 :=
  prime_of_cert' (c := 2254959) (t := 95) (a := 15) (ps := [3, 3, 3, 3, 7, 41, 97])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q109 : Nat.Prime 89205008492954331437179769054035969 :=
  prime_of_cert' (c := 2251851) (t := 95) (a := 37) (ps := [3, 7, 157, 683])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P109 : Nat.Prime 178410016985908662874359538108071937 :=
  prime_of_cert' (c := 2251851) (t := 96) (a := 5) (ps := [3, 7, 157, 683])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q110 : Nat.Prime 177282917145980738407753781870592001 :=
  prime_of_cert' (c := 2237625) (t := 96) (a := 7) (ps := [3, 3, 3, 3, 5, 5, 5, 13, 17])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P110 : Nat.Prime 354565834291961476815507563741184001 :=
  prime_of_cert' (c := 2237625) (t := 97) (a := 37) (ps := [3, 3, 3, 3, 5, 5, 5, 13, 17])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q111 : Nat.Prime 354348590670347364001826066229362689 :=
  prime_of_cert' (c := 2236254) (t := 97) (a := 13) (ps := [2, 3, 372709])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P111 : Nat.Prime 708697181340694728003652132458725377 :=
  prime_of_cert' (c := 2236254) (t := 98) (a := 10) (ps := [2, 3, 372709])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q112 : Nat.Prime 707324315740647555561831202887303169 :=
  prime_of_cert' (c := 2231922) (t := 98) (a := 17) (ps := [2, 3, 7, 11, 4831])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P112 : Nat.Prime 1414648631481295111123662405774606337 :=
  prime_of_cert' (c := 2231922) (t := 99) (a := 5) (ps := [2, 3, 7, 11, 4831])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q113 : Nat.Prime 1413271962929447253993636986093568001 :=
  prime_of_cert' (c := 2229750) (t := 99) (a := 7) (ps := [2, 3, 3, 5, 5, 5, 991])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P113 : Nat.Prime 2826543925858894507987273972187136001 :=
  prime_of_cert' (c := 2229750) (t := 100) (a := 33) (ps := [2, 3, 3, 5, 5, 5, 991])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q114 : Nat.Prime 2819991439906314790210937513318547457 :=
  prime_of_cert' (c := 2224581) (t := 100) (a := 10) (ps := [3, 109, 6803])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P114 : Nat.Prime 5639982879812629580421875026637094913 :=
  prime_of_cert' (c := 2224581) (t := 101) (a := 5) (ps := [3, 109, 6803])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q115 : Nat.Prime 5638241127887915993224218556432908289 :=
  prime_of_cert' (c := 2223894) (t := 101) (a := 23) (ps := [2, 3, 29, 12781])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P115 : Nat.Prime 11276482255775831986448437112865816577 :=
  prime_of_cert' (c := 2223894) (t := 102) (a := 5) (ps := [2, 3, 29, 12781])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q116 : Nat.Prime 11269104529282503691331726300210528257 :=
  prime_of_cert' (c := 2222439) (t := 102) (a := 5) (ps := [3, 727, 1019])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P116 : Nat.Prime 22538209058565007382663452600421056513 :=
  prime_of_cert' (c := 2222439) (t := 103) (a := 5) (ps := [3, 727, 1019])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q117 : Nat.Prime 22509215354036587319792420004707696641 :=
  prime_of_cert' (c := 2219580) (t := 103) (a := 7) (ps := [2, 2, 3, 3, 5, 11, 19, 59])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P117 : Nat.Prime 45018430708073174639584840009415393281 :=
  prime_of_cert' (c := 2219580) (t := 104) (a := 13) (ps := [2, 2, 3, 3, 5, 11, 19, 59])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q118 : Nat.Prime 44976567814651237591829812882761056257 :=
  prime_of_cert' (c := 2217516) (t := 104) (a := 5) (ps := [2, 2, 3, 7, 26399])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P118 : Nat.Prime 89953135629302475183659625765522112513 :=
  prime_of_cert' (c := 2217516) (t := 105) (a := 5) (ps := [2, 2, 3, 7, 26399])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q119 : Nat.Prime 89930987238015287559556675367117783041 :=
  prime_of_cert' (c := 2216970) (t := 105) (a := 13) (ps := [2, 3, 3, 3, 3, 5, 7, 17, 23])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P119 : Nat.Prime 179861974476030575119113350734235566081 :=
  prime_of_cert' (c := 2216970) (t := 106) (a := 31) (ps := [2, 3, 3, 3, 3, 5, 7, 17, 23])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

end Erdos287
