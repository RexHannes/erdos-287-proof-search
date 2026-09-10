import RequestProject.PowMod

/-!
# Certified primes, block 6

Kernel-checked Lucas primality certificates for the prime pairs
`(q_i, P_i = 2 * q_i - 1)` with `144 ≤ i < 168`.
-/

namespace Erdos287

set_option maxRecDepth 100000

theorem prime_q144 : Nat.Prime 2925641622687749576057494301820824370416713729 :=
  prime_of_cert' (c := 2149422) (t := 130) (a := 7) (ps := [2, 3, 11, 29, 1123])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P144 : Nat.Prime 5851283245375499152114988603641648740833427457 :=
  prime_of_cert' (c := 2149422) (t := 131) (a := 5) (ps := [2, 3, 11, 29, 1123])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q145 : Nat.Prime 5847534694821498094001476068966180382216028161 :=
  prime_of_cert' (c := 2148045) (t := 131) (a := 7) (ps := [3, 5, 19, 7537])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P145 : Nat.Prime 11695069389642996188002952137932360764432056321 :=
  prime_of_cert' (c := 2148045) (t := 132) (a := 7) (ps := [3, 5, 19, 7537])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q146 : Nat.Prime 11670324055920505542939895536479922580094976001 :=
  prime_of_cert' (c := 2143500) (t := 132) (a := 7) (ps := [2, 2, 3, 5, 5, 5, 1429])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P146 : Nat.Prime 23340648111841011085879791072959845160189952001 :=
  prime_of_cert' (c := 2143500) (t := 133) (a := 7) (ps := [2, 2, 3, 5, 5, 5, 1429])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q147 : Nat.Prime 23155425613878605861447407006642585087330222081 :=
  prime_of_cert' (c := 2126490) (t := 133) (a := 7) (ps := [2, 3, 5, 73, 971])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P147 : Nat.Prime 46310851227757211722894814013285170174660444161 :=
  prime_of_cert' (c := 2126490) (t := 134) (a := 19) (ps := [2, 3, 5, 73, 971])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q148 : Nat.Prime 45818557921885351629033080701221482467782819841 :=
  prime_of_cert' (c := 2103885) (t := 134) (a := 41) (ps := [3, 3, 5, 7, 6679])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P148 : Nat.Prime 91637115843770703258066161402442964935565639681 :=
  prime_of_cert' (c := 2103885) (t := 135) (a := 13) (ps := [3, 3, 5, 7, 6679])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q149 : Nat.Prime 91610590152704482262962264425044443739946221569 :=
  prime_of_cert' (c := 2103276) (t := 135) (a := 11) (ps := [2, 2, 3, 7, 7, 7, 7, 73])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P149 : Nat.Prime 183221180305408964525924528850088887479892443137 :=
  prime_of_cert' (c := 2103276) (t := 136) (a := 10) (ps := [2, 2, 3, 7, 7, 7, 7, 73])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q150 : Nat.Prime 183069343591029906416019463393255973049795084289 :=
  prime_of_cert' (c := 2101533) (t := 136) (a := 11) (ps := [3, 7, 19, 23, 229])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P150 : Nat.Prime 366138687182059812832038926786511946099590168577 :=
  prime_of_cert' (c := 2101533) (t := 137) (a := 10) (ps := [3, 7, 19, 23, 229])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q151 : Nat.Prime 365649987257982637848351366710302737865025519617 :=
  prime_of_cert' (c := 2098728) (t := 137) (a := 5) (ps := [2, 2, 2, 3, 3, 103, 283])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P151 : Nat.Prime 731299974515965275696702733420605475730051039233 :=
  prime_of_cert' (c := 2098728) (t := 138) (a := 5) (ps := [2, 2, 2, 3, 3, 103, 283])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q152 : Nat.Prime 730440698927534392623780435275912493550773731329 :=
  prime_of_cert' (c := 2096262) (t := 138) (a := 11) (ps := [2, 3, 3, 7, 127, 131])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P152 : Nat.Prime 1460881397855068785247560870551824987101547462657 :=
  prime_of_cert' (c := 2096262) (t := 139) (a := 11) (ps := [2, 3, 3, 7, 127, 131])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q153 : Nat.Prime 1460866762991032249526124237736708561614309163009 :=
  prime_of_cert' (c := 4192482) (t := 138) (a := 17) (ps := [2, 3, 7, 173, 577])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P153 : Nat.Prime 2921733525982064499052248475473417123228618326017 :=
  prime_of_cert' (c := 4192482) (t := 139) (a := 13) (ps := [2, 3, 7, 173, 577])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q154 : Nat.Prime 2921095864049044014046795188529058584141806698497 :=
  prime_of_cert' (c := 4191567) (t := 139) (a := 5) (ps := [3, 1397189])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P154 : Nat.Prime 5842191728098088028093590377058117168283613396993 :=
  prime_of_cert' (c := 4191567) (t := 140) (a := 5) (ps := [3, 1397189])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q155 : Nat.Prime 5834941198315415759244698576654722369748981514241 :=
  prime_of_cert' (c := 4186365) (t := 140) (a := 7) (ps := [3, 5, 19, 37, 397])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P155 : Nat.Prime 11669882396630831518489397153309444739497963028481 :=
  prime_of_cert' (c := 4186365) (t := 141) (a := 26) (ps := [3, 5, 19, 37, 397])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q156 : Nat.Prime 11661527979960831983794999334851553847068785115137 :=
  prime_of_cert' (c := 4183368) (t := 141) (a := 10) (ps := [2, 2, 2, 3, 7, 37, 673])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P156 : Nat.Prime 23323055959921663967589998669703107694137570230273 :=
  prime_of_cert' (c := 4183368) (t := 142) (a := 10) (ps := [2, 2, 2, 3, 7, 37, 673])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q157 : Nat.Prime 23321684464091954334266794223029339819904952434689 :=
  prime_of_cert' (c := 4183122) (t := 142) (a := 7) (ps := [2, 3, 17, 41011])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P157 : Nat.Prime 46643368928183908668533588446058679639809904869377 :=
  prime_of_cert' (c := 4183122) (t := 143) (a := 5) (ps := [2, 3, 17, 41011])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q158 : Nat.Prime 46370943024838658576236588111640007255652848107521 :=
  prime_of_cert' (c := 4158690) (t := 143) (a := 14) (ps := [2, 3, 5, 67, 2069])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P158 : Nat.Prime 92741886049677317152473176223280014511305696215041 :=
  prime_of_cert' (c := 4158690) (t := 144) (a := 11) (ps := [2, 3, 5, 67, 2069])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q159 : Nat.Prime 92654578632225069762874063886242596176009782886401 :=
  prime_of_cert' (c := 4154775) (t := 144) (a := 7) (ps := [3, 5, 5, 31, 1787])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P159 : Nat.Prime 185309157264450139525748127772485192352019565772801 :=
  prime_of_cert' (c := 4154775) (t := 145) (a := 7) (ps := [3, 5, 5, 31, 1787])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q160 : Nat.Prime 184844588140474349584463655689429381685126981746689 :=
  prime_of_cert' (c := 4144359) (t := 145) (a := 11) (ps := [3, 31, 44563])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P160 : Nat.Prime 369689176280948699168927311378858763370253963493377 :=
  prime_of_cert' (c := 4144359) (t := 146) (a := 5) (ps := [3, 31, 44563])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q161 : Nat.Prime 369393736008558565473548246183182717877022734942209 :=
  prime_of_cert' (c := 4141047) (t := 146) (a := 7) (ps := [3, 17, 81197])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P161 : Nat.Prime 738787472017117130947096492366365435754045469884417 :=
  prime_of_cert' (c := 4141047) (t := 147) (a := 5) (ps := [3, 17, 81197])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q162 : Nat.Prime 738656343635349770883024262342922263388390305038337 :=
  prime_of_cert' (c := 4140312) (t := 147) (a := 5) (ps := [2, 2, 2, 3, 11, 15683])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P162 : Nat.Prime 1477312687270699541766048524685844526776780610076673 :=
  prime_of_cert' (c := 4140312) (t := 148) (a := 5) (ps := [2, 2, 2, 3, 11, 15683])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q163 : Nat.Prime 1474923474633109764925156953972986071918475892228097 :=
  prime_of_cert' (c := 4133616) (t := 148) (a := 5) (ps := [2, 2, 2, 2, 3, 86117])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P163 : Nat.Prime 2949846949266219529850313907945972143836951784456193 :=
  prime_of_cert' (c := 4133616) (t := 149) (a := 10) (ps := [2, 2, 2, 2, 3, 86117])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q164 : Nat.Prime 2947408496583231397393525826367167681396441861849089 :=
  prime_of_cert' (c := 4130199) (t := 149) (a := 7) (ps := [3, 3, 37, 79, 157])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P164 : Nat.Prime 5894816993166462794787051652734335362792883723698177 :=
  prime_of_cert' (c := 4130199) (t := 150) (a := 5) (ps := [3, 3, 37, 79, 157])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q165 : Nat.Prime 5894140477760120169803430025184816302098238301798401 :=
  prime_of_cert' (c := 4129725) (t := 150) (a := 22) (ps := [3, 5, 5, 17, 41, 79])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P165 : Nat.Prime 11788280955520240339606860050369632604196476603596801 :=
  prime_of_cert' (c := 4129725) (t := 151) (a := 22) (ps := [3, 5, 5, 17, 41, 79])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q166 : Nat.Prime 11769055929099491060009004938361147904709401006571521 :=
  prime_of_cert' (c := 4122990) (t := 151) (a := 19) (ps := [2, 3, 3, 5, 61, 751])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P166 : Nat.Prime 23538111858198982120018009876722295809418802013143041 :=
  prime_of_cert' (c := 4122990) (t := 152) (a := 7) (ps := [2, 3, 3, 5, 61, 751])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q167 : Nat.Prime 23485223767698070070665514031838375317645002954244097 :=
  prime_of_cert' (c := 4113726) (t := 152) (a := 7) (ps := [2, 3, 685621])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P167 : Nat.Prime 46970447535396140141331028063676750635290005908488193 :=
  prime_of_cert' (c := 4113726) (t := 153) (a := 15) (ps := [2, 3, 685621])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

end Erdos287
