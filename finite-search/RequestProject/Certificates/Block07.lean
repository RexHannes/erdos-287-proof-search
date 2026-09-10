import RequestProject.PowMod

/-!
# Certified primes, block 7

Kernel-checked Lucas primality certificates for the prime pairs
`(q_i, P_i = 2 * q_i - 1)` with `168 ≤ i < 192`.
-/

namespace Erdos287

set_option maxRecDepth 100000

theorem prime_q168 : Nat.Prime 46918244523787726952721440196058165901181670567968769 :=
  prime_of_cert' (c := 4109154) (t := 153) (a := 19) (ps := [2, 3, 7, 227, 431])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P168 : Nat.Prime 93836489047575453905442880392116331802363341135937537 :=
  prime_of_cert' (c := 4109154) (t := 154) (a := 10) (ps := [2, 3, 7, 227, 431])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q169 : Nat.Prime 93768734745107316577969281440574625369248979388203009 :=
  prime_of_cert' (c := 4106187) (t := 154) (a := 7) (ps := [3, 3, 3, 152081])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P169 : Nat.Prime 187537469490214633155938562881149250738497958776406017 :=
  prime_of_cert' (c := 4106187) (t := 155) (a := 10) (ps := [3, 3, 3, 152081])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q170 : Nat.Prime 187537469490214633155938562881149250738497958776406017 :=
  prime_of_cert' (c := 4106187) (t := 155) (a := 10) (ps := [3, 3, 3, 152081])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P170 : Nat.Prime 375074938980429266311877125762298501476995917552812033 :=
  prime_of_cert' (c := 4106187) (t := 156) (a := 10) (ps := [3, 3, 3, 152081])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q171 : Nat.Prime 374372596099839434278247867469876282718362513470128129 :=
  prime_of_cert' (c := 4098498) (t := 156) (a := 14) (ps := [2, 3, 683083])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P171 : Nat.Prime 748745192199678868556495734939752565436725026940256257 :=
  prime_of_cert' (c := 4098498) (t := 157) (a := 5) (ps := [2, 3, 683083])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q172 : Nat.Prime 747336121933587211780482607300409979070399250977259521 :=
  prime_of_cert' (c := 4090785) (t := 157) (a := 7) (ps := [3, 5, 272719])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P172 : Nat.Prime 1494672243867174423560965214600819958140798501954519041 :=
  prime_of_cert' (c := 4090785) (t := 158) (a := 13) (ps := [3, 5, 272719])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q173 : Nat.Prime 1491619532322199500090567267906483821983492172855377921 :=
  prime_of_cert' (c := 4082430) (t := 158) (a := 13) (ps := [2, 3, 5, 11, 89, 139])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P173 : Nat.Prime 2983239064644399000181134535812967643966984345710755841 :=
  prime_of_cert' (c := 4082430) (t := 159) (a := 21) (ps := [2, 3, 5, 11, 89, 139])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q174 : Nat.Prime 2978091655877719560103221157832140895171756151294394369 :=
  prime_of_cert' (c := 4075386) (t := 159) (a := 11) (ps := [2, 3, 7, 19, 5107])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P174 : Nat.Prime 5956183311755439120206442315664281790343512302588788737 :=
  prime_of_cert' (c := 4075386) (t := 160) (a := 5) (ps := [2, 3, 7, 19, 5107])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q175 : Nat.Prime 5945594732392976728564056619051252319866105071314927617 :=
  prime_of_cert' (c := 4068141) (t := 160) (a := 35) (ps := [3, 7, 11, 11, 1601])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P175 : Nat.Prime 11891189464785953457128113238102504639732210142629855233 :=
  prime_of_cert' (c := 4068141) (t := 161) (a := 5) (ps := [3, 7, 11, 11, 1601])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q176 : Nat.Prime 11869608931609125344637917627862616004663970642700271617 :=
  prime_of_cert' (c := 4060758) (t := 161) (a := 10) (ps := [2, 3, 13, 79, 659])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P176 : Nat.Prime 23739217863218250689275835255725232009327941285400543233 :=
  prime_of_cert' (c := 4060758) (t := 162) (a := 7) (ps := [2, 3, 13, 79, 659])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q177 : Nat.Prime 23707438971616127536222414332722649151348542688186073089 :=
  prime_of_cert' (c := 4055322) (t := 162) (a := 7) (ps := [2, 3, 19, 35573])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P177 : Nat.Prime 47414877943232255072444828665445298302697085376372146177 :=
  prime_of_cert' (c := 4055322) (t := 163) (a := 5) (ps := [2, 3, 19, 35573])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q178 : Nat.Prime 47393692015497506303742548050110243064044152978229166081 :=
  prime_of_cert' (c := 4053510) (t := 163) (a := 13) (ps := [2, 3, 3, 3, 5, 15013])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P178 : Nat.Prime 94787384030995012607485096100220486128088305956458332161 :=
  prime_of_cert' (c := 4053510) (t := 164) (a := 17) (ps := [2, 3, 3, 3, 5, 15013])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q179 : Nat.Prime 94751746775070335870727617449259532282937015697330405377 :=
  prime_of_cert' (c := 4051986) (t := 164) (a := 10) (ps := [2, 3, 61, 11071])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P179 : Nat.Prime 189503493550140671741455234898519064565874031394660810753 :=
  prime_of_cert' (c := 4051986) (t := 165) (a := 5) (ps := [2, 3, 61, 11071])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q180 : Nat.Prime 188580011587557119452724036155900961381677997986865479681 :=
  prime_of_cert' (c := 4032240) (t := 165) (a := 7) (ps := [2, 2, 2, 2, 3, 5, 53, 317])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P180 : Nat.Prime 377160023175114238905448072311801922763355995973730959361 :=
  prime_of_cert' (c := 4032240) (t := 166) (a := 7) (ps := [2, 2, 2, 2, 3, 5, 53, 317])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q181 : Nat.Prime 375275457735821884857706130423189591865434221325674610689 :=
  prime_of_cert' (c := 4012092) (t := 166) (a := 17) (ps := [2, 2, 3, 3, 3, 3, 7, 29, 61])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P181 : Nat.Prime 750550915471643769715412260846379183730868442651349221377 :=
  prime_of_cert' (c := 4012092) (t := 167) (a := 5) (ps := [2, 2, 3, 3, 3, 3, 7, 29, 61])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q182 : Nat.Prime 749790466939707754309012519554220247350081067830587949057 :=
  prime_of_cert' (c := 4008027) (t := 167) (a := 5) (ps := [3, 1336009])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P182 : Nat.Prime 1499580933879415508618025039108440494700162135661175898113 :=
  prime_of_cert' (c := 4008027) (t := 168) (a := 5) (ps := [3, 1336009])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q183 : Nat.Prime 1499291346098988214190200488180946759517515430563380461569 :=
  prime_of_cert' (c := 4007253) (t := 168) (a := 17) (ps := [3, 1335751])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P183 : Nat.Prime 2998582692197976428380400976361893519035030861126760923137 :=
  prime_of_cert' (c := 4007253) (t := 169) (a := 10) (ps := [3, 1335751])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q184 : Nat.Prime 2994429689145336934648033385541246929206376563212640321537 :=
  prime_of_cert' (c := 4001703) (t := 169) (a := 7) (ps := [3, 1333901])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P184 : Nat.Prime 5988859378290673869296066771082493858412753126425280643073 :=
  prime_of_cert' (c := 4001703) (t := 170) (a := 5) (ps := [3, 1333901])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q185 : Nat.Prime 5986610022042703721879941189459635543273125231014497484801 :=
  prime_of_cert' (c := 4000200) (t := 170) (a := 7) (ps := [2, 2, 2, 3, 5, 5, 59, 113])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P185 : Nat.Prime 11973220044085407443759882378919271086546250462028994969601 :=
  prime_of_cert' (c := 4000200) (t := 171) (a := 29) (ps := [2, 2, 2, 3, 5, 5, 59, 113])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q186 : Nat.Prime 11973220044085407443759882378919271086546250462028994969601 :=
  prime_of_cert' (c := 4000200) (t := 171) (a := 29) (ps := [2, 2, 2, 3, 5, 5, 59, 113])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P186 : Nat.Prime 23946440088170814887519764757838542173092500924057989939201 :=
  prime_of_cert' (c := 4000200) (t := 172) (a := 7) (ps := [2, 2, 2, 3, 5, 5, 59, 113])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q187 : Nat.Prime 23896532215810662874191118120473885424405667220692190363649 :=
  prime_of_cert' (c := 3991863) (t := 172) (a := 14) (ps := [3, 1330621])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P187 : Nat.Prime 47793064431621325748382236240947770848811334441384380727297 :=
  prime_of_cert' (c := 3991863) (t := 173) (a := 5) (ps := [3, 1330621])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q188 : Nat.Prime 47665879274350869987895199362280444798361476115642533806081 :=
  prime_of_cert' (c := 3981240) (t := 173) (a := 13) (ps := [2, 2, 2, 3, 3, 5, 11059])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P188 : Nat.Prime 95331758548701739975790398724560889596722952231285067612161 :=
  prime_of_cert' (c := 3981240) (t := 174) (a := 7) (ps := [2, 2, 2, 3, 3, 5, 11059])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q189 : Nat.Prime 95270267165124496185348770050096483440730250324007450574849 :=
  prime_of_cert' (c := 3978672) (t := 174) (a := 13) (ps := [2, 2, 2, 2, 3, 82889])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P189 : Nat.Prime 190540534330248992370697540100192966881460500648014901149697 :=
  prime_of_cert' (c := 3978672) (t := 175) (a := 5) (ps := [2, 2, 2, 2, 3, 82889])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q190 : Nat.Prime 190531339357003797037547390018030065026358788213281799536641 :=
  prime_of_cert' (c := 3978480) (t := 175) (a := 7) (ps := [2, 2, 2, 2, 3, 5, 11, 11, 137])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P190 : Nat.Prime 381062678714007594075094780036060130052717576426563599073281 :=
  prime_of_cert' (c := 3978480) (t := 176) (a := 13) (ps := [2, 2, 2, 2, 3, 5, 11, 11, 137])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_q191 : Nat.Prime 379241499325631093403043179387670381376634657322238660837377 :=
  prime_of_cert' (c := 3959466) (t := 176) (a := 5) (ps := [2, 3, 7, 94273])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

theorem prime_P191 : Nat.Prime 758482998651262186806086358775340762753269314644477321674753 :=
  prime_of_cert' (c := 3959466) (t := 177) (a := 5) (ps := [2, 3, 7, 94273])
    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)

end Erdos287
