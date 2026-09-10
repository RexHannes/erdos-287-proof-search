import RequestProject.PowMod

/-!
# Certified primes, block 5

Kernel-checked Lucas primality certificates for the prime pairs
`(q_i, P_i = 2 * q_i - 1)` with `120 ≤ i < 144`.
-/

namespace Erdos287

set_option maxRecDepth 100000

theorem prime_q120 : Nat.Prime 179780195800508651583963995417050349569 :=
  prime_of_cert' (c := 2215962) (t := 106) (a := 11) (ps := [2, 3, 3, 7, 43, 409])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P120 : Nat.Prime 359560391601017303167927990834100699137 :=
  prime_of_cert' (c := 2215962) (t := 107) (a := 5) (ps := [2, 3, 3, 7, 43, 409])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q121 : Nat.Prime 358508951487164000573150565327433629697 :=
  prime_of_cert' (c := 2209482) (t := 107) (a := 15) (ps := [2, 3, 3, 11, 11159])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P121 : Nat.Prime 717017902974328001146301130654867259393 :=
  prime_of_cert' (c := 2209482) (t := 108) (a := 7) (ps := [2, 3, 3, 11, 11159])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q122 : Nat.Prime 716957542523347533775119463635040075777 :=
  prime_of_cert' (c := 2209296) (t := 108) (a := 5) (ps := [2, 2, 2, 2, 3, 46027])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P122 : Nat.Prime 1433915085046695067550238927270080151553 :=
  prime_of_cert' (c := 2209296) (t := 109) (a := 5) (ps := [2, 2, 2, 2, 3, 46027])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q123 : Nat.Prime 1433809941035309737290761184719413444609 :=
  prime_of_cert' (c := 2209134) (t := 109) (a := 13) (ps := [2, 3, 368189])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P123 : Nat.Prime 2867619882070619474581522369438826889217 :=
  prime_of_cert' (c := 2209134) (t := 110) (a := 5) (ps := [2, 3, 368189])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q124 : Nat.Prime 2867619882070619474581522369438826889217 :=
  prime_of_cert' (c := 2209134) (t := 110) (a := 5) (ps := [2, 3, 368189])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P124 : Nat.Prime 5735239764141238949163044738877653778433 :=
  prime_of_cert' (c := 2209134) (t := 111) (a := 5) (ps := [2, 3, 368189])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q125 : Nat.Prime 5714732787698455647444163543625399009281 :=
  prime_of_cert' (c := 2201235) (t := 111) (a := 11) (ps := [3, 5, 146749])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P125 : Nat.Prime 11429465575396911294888327087250798018561 :=
  prime_of_cert' (c := 2201235) (t := 112) (a := 7) (ps := [3, 5, 146749])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q126 : Nat.Prime 11417175408732759357891595402439534051329 :=
  prime_of_cert' (c := 2198868) (t := 112) (a := 23) (ps := [2, 2, 3, 7, 26177])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P126 : Nat.Prime 22834350817465518715783190804879068102657 :=
  prime_of_cert' (c := 2198868) (t := 113) (a := 10) (ps := [2, 2, 3, 7, 26177])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q127 : Nat.Prime 22833416204030982446810055315539808485377 :=
  prime_of_cert' (c := 2198778) (t := 113) (a := 10) (ps := [2, 3, 366463])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P127 : Nat.Prime 45666832408061964893620110631079616970753 :=
  prime_of_cert' (c := 2198778) (t := 114) (a := 11) (ps := [2, 3, 366463])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q128 : Nat.Prime 45657673196403509457683382835554872721409 :=
  prime_of_cert' (c := 2198337) (t := 114) (a := 11) (ps := [3, 67, 10937])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P128 : Nat.Prime 91315346392807018915366765671109745442817 :=
  prime_of_cert' (c := 2198337) (t := 115) (a := 5) (ps := [3, 67, 10937])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q129 : Nat.Prime 91159702102175578922373935513145043845121 :=
  prime_of_cert' (c := 2194590) (t := 115) (a := 7) (ps := [2, 3, 5, 191, 383])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P129 : Nat.Prime 182319404204351157844747871026290087690241 :=
  prime_of_cert' (c := 2194590) (t := 116) (a := 13) (ps := [2, 3, 5, 191, 383])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q130 : Nat.Prime 182185318330276354456068699489084307931137 :=
  prime_of_cert' (c := 2192976) (t := 116) (a := 5) (ps := [2, 2, 2, 2, 3, 3, 97, 157])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P130 : Nat.Prime 364370636660552708912137398978168615862273 :=
  prime_of_cert' (c := 2192976) (t := 117) (a := 7) (ps := [2, 2, 2, 2, 3, 3, 97, 157])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q131 : Nat.Prime 364166766316699197440130777570298118012929 :=
  prime_of_cert' (c := 2191749) (t := 117) (a := 31) (ps := [3, 7, 104369])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P131 : Nat.Prime 728333532633398394880261555140596236025857 :=
  prime_of_cert' (c := 2191749) (t := 118) (a := 5) (ps := [3, 7, 104369])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q132 : Nat.Prime 727421349921290996362481317545478849560577 :=
  prime_of_cert' (c := 2189004) (t := 118) (a := 5) (ps := [2, 2, 3, 182417])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P132 : Nat.Prime 1454842699842581992724962635090957699121153 :=
  prime_of_cert' (c := 2189004) (t := 119) (a := 5) (ps := [2, 2, 3, 182417])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q133 : Nat.Prime 1448765469445853357354046429211355963719681 :=
  prime_of_cert' (c := 2179860) (t := 119) (a := 7) (ps := [2, 2, 3, 5, 47, 773])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P133 : Nat.Prime 2897530938891706714708092858422711927439361 :=
  prime_of_cert' (c := 2179860) (t := 120) (a := 7) (ps := [2, 2, 3, 5, 47, 773])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q134 : Nat.Prime 2897518975839744650465236724159169404338177 :=
  prime_of_cert' (c := 2179851) (t := 120) (a := 7) (ps := [3, 19, 167, 229])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P134 : Nat.Prime 5795037951679489300930473448318338808676353 :=
  prime_of_cert' (c := 2179851) (t := 121) (a := 5) (ps := [3, 19, 167, 229])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q135 : Nat.Prime 5785411682534014940178904077587788553256961 :=
  prime_of_cert' (c := 2176230) (t := 121) (a := 23) (ps := [2, 3, 5, 7, 43, 241])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P135 : Nat.Prime 11570823365068029880357808155175577106513921 :=
  prime_of_cert' (c := 2176230) (t := 122) (a := 17) (ps := [2, 3, 5, 7, 43, 241])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q136 : Nat.Prime 11568239345844224003900883154250392116658177 :=
  prime_of_cert' (c := 2175744) (t := 122) (a := 5) (ps := [2, 2, 2, 2, 2, 2, 2, 2, 3, 2833])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P136 : Nat.Prime 23136478691688448007801766308500784233316353 :=
  prime_of_cert' (c := 2175744) (t := 123) (a := 7) (ps := [2, 2, 2, 2, 2, 2, 2, 2, 3, 2833])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q137 : Nat.Prime 23100557634330356441252413826503768201494529 :=
  prime_of_cert' (c := 2172366) (t := 123) (a := 22) (ps := [2, 3, 3, 3, 7, 7, 821])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P137 : Nat.Prime 46201115268660712882504827653007536402989057 :=
  prime_of_cert' (c := 2172366) (t := 124) (a := 5) (ps := [2, 3, 3, 3, 7, 7, 821])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q138 : Nat.Prime 46200158224503747743076336911924134554894337 :=
  prime_of_cert' (c := 2172321) (t := 124) (a := 5) (ps := [3, 3, 59, 4091])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P138 : Nat.Prime 92400316449007495486152673823848269109788673 :=
  prime_of_cert' (c := 2172321) (t := 125) (a := 10) (ps := [3, 3, 59, 4091])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q139 : Nat.Prime 92303208368547432672141813295252428256444417 :=
  prime_of_cert' (c := 2170038) (t := 125) (a := 11) (ps := [2, 3, 13, 43, 647])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P139 : Nat.Prime 184606416737094865344283626590504856512888833 :=
  prime_of_cert' (c := 2170038) (t := 126) (a := 10) (ps := [2, 3, 13, 43, 647])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q140 : Nat.Prime 184256010969758028961532216588501993197142017 :=
  prime_of_cert' (c := 2165919) (t := 126) (a := 10) (ps := [3, 7, 17, 6067])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P140 : Nat.Prime 368512021939516057923064433177003986394284033 :=
  prime_of_cert' (c := 2165919) (t := 127) (a := 5) (ps := [3, 7, 17, 6067])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q141 : Nat.Prime 368165444348807082098026986139334730470916097 :=
  prime_of_cert' (c := 2163882) (t := 127) (a := 5) (ps := [2, 3, 7, 51521])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P141 : Nat.Prime 736330888697614164196053972278669460941832193 :=
  prime_of_cert' (c := 2163882) (t := 128) (a := 20) (ps := [2, 3, 7, 51521])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q142 : Nat.Prime 732510878846559709005214128935640431000027137 :=
  prime_of_cert' (c := 2152656) (t := 128) (a := 5) (ps := [2, 2, 2, 2, 3, 3, 3, 3, 11, 151])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P142 : Nat.Prime 1465021757693119418010428257871280862000054273 :=
  prime_of_cert' (c := 2152656) (t := 129) (a := 5) (ps := [2, 2, 2, 2, 3, 3, 3, 3, 11, 151])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q143 : Nat.Prime 1463098481755282273814933264590076508068904961 :=
  prime_of_cert' (c := 2149830) (t := 129) (a := 7) (ps := [2, 3, 3, 5, 23887])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P143 : Nat.Prime 2926196963510564547629866529180153016137809921 :=
  prime_of_cert' (c := 2149830) (t := 130) (a := 17) (ps := [2, 3, 3, 5, 23887])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

end Erdos287
