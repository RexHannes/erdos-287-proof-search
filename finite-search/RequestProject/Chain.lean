import RequestProject.Small
import RequestProject.Certificates.Block00
import RequestProject.Certificates.Block01
import RequestProject.Certificates.Block02
import RequestProject.Certificates.Block03
import RequestProject.Certificates.Block04
import RequestProject.Certificates.Block05
import RequestProject.Certificates.Block06
import RequestProject.Certificates.Block07

/-!
# The certified chain of prime pairs

For each `i` the pair `(q_i, P_i = 2 * q_i - 1)` consists of two primes with `q_i > 11`,
so `windowPairSupply_of_prime_pair` gives `WindowPairSupply M` for `P_i + 1 <= M <= 2 * P_i`.
The chain satisfies `P_i < P_{i+1} <= 2 * P_i`, hence the intervals `[P_i + 1, 2 * P_i]`
overlap, and together with the small cases they cover every `M <= 10 ^ 60`.
-/

namespace Erdos287

/-- Bookkeeping step for chaining the covering intervals. -/
theorem cover_step {M lo B : ℕ} (h : B < M) (hb : lo ≤ B + 1) : lo ≤ M := by omega

theorem wps_chain000 {M : ℕ} (h1 : 314 ≤ M) (h2 : M ≤ 626) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 157) (P := 313) prime_q000 (by norm_num)
    (by norm_num) prime_P000 (by omega) (by omega)

theorem wps_chain001 {M : ℕ} (h1 : 614 ≤ M) (h2 : M ≤ 1226) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 307) (P := 613) prime_q001 (by norm_num)
    (by norm_num) prime_P001 (by omega) (by omega)

theorem wps_chain002 {M : ℕ} (h1 : 1214 ≤ M) (h2 : M ≤ 2426) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 607) (P := 1213) prime_q002 (by norm_num)
    (by norm_num) prime_P002 (by omega) (by omega)

theorem wps_chain003 {M : ℕ} (h1 : 2342 ≤ M) (h2 : M ≤ 4682) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 1171) (P := 2341) prime_q003 (by norm_num)
    (by norm_num) prime_P003 (by omega) (by omega)

theorem wps_chain004 {M : ℕ} (h1 : 4622 ≤ M) (h2 : M ≤ 9242) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 2311) (P := 4621) prime_q004 (by norm_num)
    (by norm_num) prime_P004 (by omega) (by omega)

theorem wps_chain005 {M : ℕ} (h1 : 9242 ≤ M) (h2 : M ≤ 18482) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 4621) (P := 9241) prime_q005 (by norm_num)
    (by norm_num) prime_P005 (by omega) (by omega)

theorem wps_chain006 {M : ℕ} (h1 : 18482 ≤ M) (h2 : M ≤ 36962) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 9241) (P := 18481) prime_q006 (by norm_num)
    (by norm_num) prime_P006 (by omega) (by omega)

theorem wps_chain007 {M : ℕ} (h1 : 36914 ≤ M) (h2 : M ≤ 73826) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 18457) (P := 36913) prime_q007 (by norm_num)
    (by norm_num) prime_P007 (by omega) (by omega)

theorem wps_chain008 {M : ℕ} (h1 : 73694 ≤ M) (h2 : M ≤ 147386) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 36847) (P := 73693) prime_q008 (by norm_num)
    (by norm_num) prime_P008 (by omega) (by omega)

theorem wps_chain009 {M : ℕ} (h1 : 146954 ≤ M) (h2 : M ≤ 293906) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 73477) (P := 146953) prime_q009 (by norm_num)
    (by norm_num) prime_P009 (by omega) (by omega)

theorem wps_chain010 {M : ℕ} (h1 : 292778 ≤ M) (h2 : M ≤ 585554) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 146389) (P := 292777) prime_q010 (by norm_num)
    (by norm_num) prime_P010 (by omega) (by omega)

theorem wps_chain011 {M : ℕ} (h1 : 585518 ≤ M) (h2 : M ≤ 1171034) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 292759) (P := 585517) prime_q011 (by norm_num)
    (by norm_num) prime_P011 (by omega) (by omega)

theorem wps_chain012 {M : ℕ} (h1 : 1171034 ≤ M) (h2 : M ≤ 2342066) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 585517) (P := 1171033) prime_q012 (by norm_num)
    (by norm_num) prime_P012 (by omega) (by omega)

theorem wps_chain013 {M : ℕ} (h1 : 2341454 ≤ M) (h2 : M ≤ 4682906) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 1170727) (P := 2341453) prime_q013 (by norm_num)
    (by norm_num) prime_P013 (by omega) (by omega)

theorem wps_chain014 {M : ℕ} (h1 : 4682738 ≤ M) (h2 : M ≤ 9365474) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 2341369) (P := 4682737) prime_q014 (by norm_num)
    (by norm_num) prime_P014 (by omega) (by omega)

theorem wps_chain015 {M : ℕ} (h1 : 9365438 ≤ M) (h2 : M ≤ 18730874) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 4682719) (P := 9365437) prime_q015 (by norm_num)
    (by norm_num) prime_P015 (by omega) (by omega)

theorem wps_chain016 {M : ℕ} (h1 : 18730274 ≤ M) (h2 : M ≤ 37460546) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 9365137) (P := 18730273) prime_q016 (by norm_num)
    (by norm_num) prime_P016 (by omega) (by omega)

theorem wps_chain017 {M : ℕ} (h1 : 37459442 ≤ M) (h2 : M ≤ 74918882) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 18729721) (P := 37459441) prime_q017 (by norm_num)
    (by norm_num) prime_P017 (by omega) (by omega)

theorem wps_chain018 {M : ℕ} (h1 : 74918594 ≤ M) (h2 : M ≤ 149837186) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 37459297) (P := 74918593) prime_q018 (by norm_num)
    (by norm_num) prime_P018 (by omega) (by omega)

theorem wps_chain019 {M : ℕ} (h1 : 149833154 ≤ M) (h2 : M ≤ 299666306) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 74916577) (P := 149833153) prime_q019 (by norm_num)
    (by norm_num) prime_P019 (by omega) (by omega)

theorem wps_chain020 {M : ℕ} (h1 : 299662082 ≤ M) (h2 : M ≤ 599324162) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 149831041) (P := 299662081) prime_q020 (by norm_num)
    (by norm_num) prime_P020 (by omega) (by omega)

theorem wps_chain021 {M : ℕ} (h1 : 599324162 ≤ M) (h2 : M ≤ 1198648322) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 299662081) (P := 599324161) prime_q021 (by norm_num)
    (by norm_num) prime_P021 (by omega) (by omega)

theorem wps_chain022 {M : ℕ} (h1 : 1198632962 ≤ M) (h2 : M ≤ 2397265922) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 599316481) (P := 1198632961) prime_q022 (by norm_num)
    (by norm_num) prime_P022 (by omega) (by omega)

theorem wps_chain023 {M : ℕ} (h1 : 2397265922 ≤ M) (h2 : M ≤ 4794531842) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 1198632961) (P := 2397265921) prime_q023 (by norm_num)
    (by norm_num) prime_P023 (by omega) (by omega)

theorem wps_chain024 {M : ℕ} (h1 : 4794224642 ≤ M) (h2 : M ≤ 9588449282) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 2397112321) (P := 4794224641) prime_q024 (by norm_num)
    (by norm_num) prime_P024 (by omega) (by omega)

theorem wps_chain025 {M : ℕ} (h1 : 9588068354 ≤ M) (h2 : M ≤ 19176136706) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 4794034177) (P := 9588068353) prime_q025 (by norm_num)
    (by norm_num) prime_P025 (by omega) (by omega)

theorem wps_chain026 {M : ℕ} (h1 : 19174342658 ≤ M) (h2 : M ≤ 38348685314) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 9587171329) (P := 19174342657) prime_q026 (by norm_num)
    (by norm_num) prime_P026 (by omega) (by omega)

theorem wps_chain027 {M : ℕ} (h1 : 38345588738 ≤ M) (h2 : M ≤ 76691177474) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 19172794369) (P := 38345588737) prime_q027 (by norm_num)
    (by norm_num) prime_P027 (by omega) (by omega)

theorem wps_chain028 {M : ℕ} (h1 : 76691177474 ≤ M) (h2 : M ≤ 153382354946) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 38345588737) (P := 76691177473) prime_q028 (by norm_num)
    (by norm_num) prime_P028 (by omega) (by omega)

theorem wps_chain029 {M : ℕ} (h1 : 153354240002 ≤ M) (h2 : M ≤ 306708480002) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 76677120001) (P := 153354240001) prime_q029 (by norm_num)
    (by norm_num) prime_P029 (by omega) (by omega)

theorem wps_chain030 {M : ℕ} (h1 : 306703368194 ≤ M) (h2 : M ≤ 613406736386) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 153351684097) (P := 306703368193) prime_q030 (by norm_num)
    (by norm_num) prime_P030 (by omega) (by omega)

theorem wps_chain031 {M : ℕ} (h1 : 613398085634 ≤ M) (h2 : M ≤ 1226796171266) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 306699042817) (P := 613398085633) prime_q031 (by norm_num)
    (by norm_num) prime_P031 (by omega) (by omega)

theorem wps_chain032 {M : ℕ} (h1 : 1226714382338 ≤ M) (h2 : M ≤ 2453428764674) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 613357191169) (P := 1226714382337) prime_q032 (by norm_num)
    (by norm_num) prime_P032 (by omega) (by omega)

theorem wps_chain033 {M : ℕ} (h1 : 2453368995842 ≤ M) (h2 : M ≤ 4906737991682) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 1226684497921) (P := 2453368995841) prime_q033 (by norm_num)
    (by norm_num) prime_P033 (by omega) (by omega)

theorem wps_chain034 {M : ℕ} (h1 : 4906737991682 ≤ M) (h2 : M ≤ 9813475983362) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 2453368995841) (P := 4906737991681) prime_q034 (by norm_num)
    (by norm_num) prime_P034 (by omega) (by omega)

theorem wps_chain035 {M : ℕ} (h1 : 9813475983362 ≤ M) (h2 : M ≤ 19626951966722) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 4906737991681) (P := 9813475983361) prime_q035 (by norm_num)
    (by norm_num) prime_P035 (by omega) (by omega)

theorem wps_chain036 {M : ℕ} (h1 : 19626071162882 ≤ M) (h2 : M ≤ 39252142325762) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 9813035581441) (P := 19626071162881) prime_q036 (by norm_num)
    (by norm_num) prime_P036 (by omega) (by omega)

theorem wps_chain037 {M : ℕ} (h1 : 39233620279298 ≤ M) (h2 : M ≤ 78467240558594) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 19616810139649) (P := 39233620279297) prime_q037 (by norm_num)
    (by norm_num) prime_P037 (by omega) (by omega)

theorem wps_chain038 {M : ℕ} (h1 : 78459590148098 ≤ M) (h2 : M ≤ 156919180296194) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 39229795074049) (P := 78459590148097) prime_q038 (by norm_num)
    (by norm_num) prime_P038 (by omega) (by omega)

theorem wps_chain039 {M : ℕ} (h1 : 156918173663234 ≤ M) (h2 : M ≤ 313836347326466) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 78459086831617) (P := 156918173663233) prime_q039 (by norm_num)
    (by norm_num) prime_P039 (by omega) (by omega)

theorem wps_chain040 {M : ℕ} (h1 : 313748971585538 ≤ M) (h2 : M ≤ 627497943171074) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 156874485792769) (P := 313748971585537) prime_q040 (by norm_num)
    (by norm_num) prime_P040 (by omega) (by omega)

theorem wps_chain041 {M : ℕ} (h1 : 627220112474114 ≤ M) (h2 : M ≤ 1254440224948226) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 313610056237057) (P := 627220112474113) prime_q041 (by norm_num)
    (by norm_num) prime_P041 (by omega) (by omega)

theorem wps_chain042 {M : ℕ} (h1 : 1254272721223682 ≤ M) (h2 : M ≤ 2508545442447362) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 627136360611841) (P := 1254272721223681) prime_q042 (by norm_num)
    (by norm_num) prime_P042 (by omega) (by omega)

theorem wps_chain043 {M : ℕ} (h1 : 2508538999996418 ≤ M) (h2 : M ≤ 5017077999992834) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 1254269499998209) (P := 2508538999996417) prime_q043 (by norm_num)
    (by norm_num) prime_P043 (by omega) (by omega)

theorem wps_chain044 {M : ℕ} (h1 : 5016607701073922 ≤ M) (h2 : M ≤ 10033215402147842) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 2508303850536961) (P := 5016607701073921) prime_q044 (by norm_num)
    (by norm_num) prime_P044 (by omega) (by omega)

theorem wps_chain045 {M : ℕ} (h1 : 10033215402147842 ≤ M) (h2 : M ≤ 20066430804295682) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 5016607701073921) (P := 10033215402147841) prime_q045 (by norm_num)
    (by norm_num) prime_P045 (by omega) (by omega)

theorem wps_chain046 {M : ℕ} (h1 : 20063879593721858 ≤ M) (h2 : M ≤ 40127759187443714) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 10031939796860929) (P := 20063879593721857) prime_q046 (by norm_num)
    (by norm_num) prime_P046 (by omega) (by omega)

theorem wps_chain047 {M : ℕ} (h1 : 40121832132575234 ≤ M) (h2 : M ≤ 80243664265150466) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 20060916066287617) (P := 40121832132575233) prime_q047 (by norm_num)
    (by norm_num) prime_P047 (by omega) (by omega)

theorem wps_chain048 {M : ℕ} (h1 : 80238201066749954 ≤ M) (h2 : M ≤ 160476402133499906) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 40119100533374977) (P := 80238201066749953) prime_q048 (by norm_num)
    (by norm_num) prime_P048 (by omega) (by omega)

theorem wps_chain049 {M : ℕ} (h1 : 160473515915476994 ≤ M) (h2 : M ≤ 320947031830953986) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 80236757957738497) (P := 160473515915476993) prime_q049 (by norm_num)
    (by norm_num) prime_P049 (by omega) (by omega)

theorem wps_chain050 {M : ℕ} (h1 : 320849312735035394 ≤ M) (h2 : M ≤ 641698625470070786) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 160424656367517697) (P := 320849312735035393) prime_q050 (by norm_num)
    (by norm_num) prime_P050 (by omega) (by omega)

theorem wps_chain051 {M : ℕ} (h1 : 641400932696850434 ≤ M) (h2 : M ≤ 1282801865393700866) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 320700466348425217) (P := 641400932696850433) prime_q051 (by norm_num)
    (by norm_num) prime_P051 (by omega) (by omega)

theorem wps_chain052 {M : ℕ} (h1 : 1282691364475109378 ≤ M) (h2 : M ≤ 2565382728950218754) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 641345682237554689) (P := 1282691364475109377) prime_q052 (by norm_num)
    (by norm_num) prime_P052 (by omega) (by omega)

theorem wps_chain053 {M : ℕ} (h1 : 2564429452368936962 ≤ M) (h2 : M ≤ 5128858904737873922) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 1282214726184468481) (P := 2564429452368936961) prime_q053 (by norm_num)
    (by norm_num) prime_P053 (by omega) (by omega)

theorem wps_chain054 {M : ℕ} (h1 : 5127678029249642498 ≤ M) (h2 : M ≤ 10255356058499284994) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 2563839014624821249) (P := 5127678029249642497) prime_q054 (by norm_num)
    (by norm_num) prime_P054 (by omega) (by omega)

theorem wps_chain055 {M : ℕ} (h1 : 10250804080360292354 ≤ M) (h2 : M ≤ 20501608160720584706) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 5125402040180146177) (P := 10250804080360292353) prime_q055 (by norm_num)
    (by norm_num) prime_P055 (by omega) (by omega)

theorem wps_chain056 {M : ℕ} (h1 : 20494008336349396994 ≤ M) (h2 : M ≤ 40988016672698793986) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 10247004168174698497) (P := 20494008336349396993) prime_q056 (by norm_num)
    (by norm_num) prime_P056 (by omega) (by omega)

theorem wps_chain057 {M : ℕ} (h1 : 40970969844421754882 ≤ M) (h2 : M ≤ 81941939688843509762) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 20485484922210877441) (P := 40970969844421754881) prime_q057 (by norm_num)
    (by norm_num) prime_P057 (by omega) (by omega)

theorem wps_chain058 {M : ℕ} (h1 : 81928323336845131778 ≤ M) (h2 : M ≤ 163856646673690263554) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 40964161668422565889) (P := 81928323336845131777) prime_q058 (by norm_num)
    (by norm_num) prime_P058 (by omega) (by omega)

theorem wps_chain059 {M : ℕ} (h1 : 163817592020671660034 ≤ M) (h2 : M ≤ 327635184041343320066) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 81908796010335830017) (P := 163817592020671660033) prime_q059 (by norm_num)
    (by norm_num) prime_P059 (by omega) (by omega)

theorem wps_chain060 {M : ℕ} (h1 : 327499653840057139202 ≤ M) (h2 : M ≤ 654999307680114278402) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 163749826920028569601) (P := 327499653840057139201) prime_q060 (by norm_num)
    (by norm_num) prime_P060 (by omega) (by omega)

theorem wps_chain061 {M : ℕ} (h1 : 654753580025445875714 ≤ M) (h2 : M ≤ 1309507160050891751426) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 327376790012722937857) (P := 654753580025445875713) prime_q061 (by norm_num)
    (by norm_num) prime_P061 (by omega) (by omega)

theorem wps_chain062 {M : ℕ} (h1 : 1309326453115843510274 ≤ M) (h2 : M ≤ 2618652906231687020546) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 654663226557921755137) (P := 1309326453115843510273) prime_q062 (by norm_num)
    (by norm_num) prime_P062 (by omega) (by omega)

theorem wps_chain063 {M : ℕ} (h1 : 2616251361730391703554 ≤ M) (h2 : M ≤ 5232502723460783407106) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 1308125680865195851777) (P := 2616251361730391703553) prime_q063 (by norm_num)
    (by norm_num) prime_P063 (by omega) (by omega)

theorem wps_chain064 {M : ℕ} (h1 : 5229415505916220932098 ≤ M) (h2 : M ≤ 10458831011832441864194) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 2614707752958110466049) (P := 5229415505916220932097) prime_q064 (by norm_num)
    (by norm_num) prime_P064 (by omega) (by omega)

theorem wps_chain065 {M : ℕ} (h1 : 10455561398502970884098 ≤ M) (h2 : M ≤ 20911122797005941768194) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 5227780699251485442049) (P := 10455561398502970884097) prime_q065 (by norm_num)
    (by norm_num) prime_P065 (by omega) (by omega)

theorem wps_chain066 {M : ℕ} (h1 : 20908934047587039707138 ≤ M) (h2 : M ≤ 41817868095174079414274) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 10454467023793519853569) (P := 20908934047587039707137) prime_q066 (by norm_num)
    (by norm_num) prime_P066 (by omega) (by omega)

theorem wps_chain067 {M : ℕ} (h1 : 41817868095174079414274 ≤ M) (h2 : M ≤ 83635736190348158828546) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 20908934047587039707137) (P := 41817868095174079414273) prime_q067 (by norm_num)
    (by norm_num) prime_P067 (by omega) (by omega)

theorem wps_chain068 {M : ℕ} (h1 : 83630115698013200449538 ≤ M) (h2 : M ≤ 167260231396026400899074) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 41815057849006600224769) (P := 83630115698013200449537) prime_q068 (by norm_num)
    (by norm_num) prime_P068 (by omega) (by omega)

theorem wps_chain069 {M : ℕ} (h1 : 167118638223741872504834 ≤ M) (h2 : M ≤ 334237276447483745009666) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 83559319111870936252417) (P := 167118638223741872504833) prime_q069 (by norm_num)
    (by norm_num) prime_P069 (by omega) (by omega)

theorem wps_chain070 {M : ℕ} (h1 : 334004674533929313632258 ≤ M) (h2 : M ≤ 668009349067858627264514) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 167002337266964656816129) (P := 334004674533929313632257) prime_q070 (by norm_num)
    (by norm_num) prime_P070 (by omega) (by omega)

theorem wps_chain071 {M : ℕ} (h1 : 667723136304339977502722 ≤ M) (h2 : M ≤ 1335446272608679955005442) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 333861568152169988751361) (P := 667723136304339977502721) prime_q071 (by norm_num)
    (by norm_num) prime_P071 (by omega) (by omega)

theorem wps_chain072 {M : ℕ} (h1 : 1335046785307333682528258 ≤ M) (h2 : M ≤ 2670093570614667365056514) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 667523392653666841264129) (P := 1335046785307333682528257) prime_q072 (by norm_num)
    (by norm_num) prime_P072 (by omega) (by omega)

theorem wps_chain073 {M : ℕ} (h1 : 2668627054460807455703042 ≤ M) (h2 : M ≤ 5337254108921614911406082) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 1334313527230403727851521) (P := 2668627054460807455703041) prime_q073 (by norm_num)
    (by norm_num) prime_P073 (by omega) (by omega)

theorem wps_chain074 {M : ℕ} (h1 : 5332529436595736052498434 ≤ M) (h2 : M ≤ 10665058873191472104996866) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 2666264718297868026249217) (P := 5332529436595736052498433) prime_q074 (by norm_num)
    (by norm_num) prime_P074 (by omega) (by omega)

theorem wps_chain075 {M : ℕ} (h1 : 10658127509105775740977154 ≤ M) (h2 : M ≤ 21316255018211551481954306) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 5329063754552887870488577) (P := 10658127509105775740977153) prime_q075 (by norm_num)
    (by norm_num) prime_P075 (by omega) (by omega)

theorem wps_chain076 {M : ℕ} (h1 : 21305159301651215186657282 ≤ M) (h2 : M ≤ 42610318603302430373314562) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 10652579650825607593328641) (P := 21305159301651215186657281) prime_q076 (by norm_num)
    (by norm_num) prime_P076 (by omega) (by omega)

theorem wps_chain077 {M : ℕ} (h1 : 42610318603302430373314562 ≤ M) (h2 : M ≤ 85220637206604860746629122) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 21305159301651215186657281) (P := 42610318603302430373314561) prime_q077 (by norm_num)
    (by norm_num) prime_P077 (by omega) (by omega)

theorem wps_chain078 {M : ℕ} (h1 : 85215656585704959167692802 ≤ M) (h2 : M ≤ 170431313171409918335385602) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 42607828292852479583846401) (P := 85215656585704959167692801) prime_q078 (by norm_num)
    (by norm_num) prime_P078 (by omega) (by omega)

theorem wps_chain079 {M : ℕ} (h1 : 170413604297099157165834242 ≤ M) (h2 : M ≤ 340827208594198314331668482) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 85206802148549578582917121) (P := 170413604297099157165834241) prime_q079 (by norm_num)
    (by norm_num) prime_P079 (by omega) (by omega)

theorem wps_chain080 {M : ℕ} (h1 : 340724497123195899548270594 ≤ M) (h2 : M ≤ 681448994246391799096541186) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 170362248561597949774135297) (P := 340724497123195899548270593) prime_q080 (by norm_num)
    (by norm_num) prime_P080 (by omega) (by omega)

theorem wps_chain081 {M : ℕ} (h1 : 681224091542645132243238914 ≤ M) (h2 : M ≤ 1362448183085290264486477826) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 340612045771322566121619457) (P := 681224091542645132243238913) prime_q081 (by norm_num)
    (by norm_num) prime_P081 (by omega) (by omega)

theorem wps_chain082 {M : ℕ} (h1 : 1361282939155642179529998338 ≤ M) (h2 : M ≤ 2722565878311284359059996674) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 680641469577821089764999169) (P := 1361282939155642179529998337) prime_q082 (by norm_num)
    (by norm_num) prime_P082 (by omega) (by omega)

theorem wps_chain083 {M : ℕ} (h1 : 2721163335465872074431528962 ≤ M) (h2 : M ≤ 5442326670931744148863057922) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 1360581667732936037215764481) (P := 2721163335465872074431528961) prime_q083 (by norm_num)
    (by norm_num) prime_P083 (by omega) (by omega)

theorem wps_chain084 {M : ℕ} (h1 : 5440796624191294383813820418 ≤ M) (h2 : M ≤ 10881593248382588767627640834) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 2720398312095647191906910209) (P := 5440796624191294383813820417) prime_q084 (by norm_num)
    (by norm_num) prime_P084 (by omega) (by omega)

theorem wps_chain085 {M : ℕ} (h1 : 10877923969625399053296599042 ≤ M) (h2 : M ≤ 21755847939250798106593198082) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 5438961984812699526648299521) (P := 10877923969625399053296599041) prime_q085 (by norm_num)
    (by norm_num) prime_P085 (by omega) (by omega)

theorem wps_chain086 {M : ℕ} (h1 : 21745505956653313583575203842 ≤ M) (h2 : M ≤ 43491011913306627167150407682) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 10872752978326656791787601921) (P := 21745505956653313583575203841) prime_q086 (by norm_num)
    (by norm_num) prime_P086 (by omega) (by omega)

theorem wps_chain087 {M : ℕ} (h1 : 43446810563026967287950213122 ≤ M) (h2 : M ≤ 86893621126053934575900426242) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 21723405281513483643975106561) (P := 43446810563026967287950213121) prime_q087 (by norm_num)
    (by norm_num) prime_P087 (by omega) (by omega)

theorem wps_chain088 {M : ℕ} (h1 : 86823805659971189741061144578 ≤ M) (h2 : M ≤ 173647611319942379482122289154) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 43411902829985594870530572289) (P := 86823805659971189741061144577) prime_q088 (by norm_num)
    (by norm_num) prime_P088 (by omega) (by omega)

theorem wps_chain089 {M : ℕ} (h1 : 173620637162592228068661657602 ≤ M) (h2 : M ≤ 347241274325184456137323315202) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 86810318581296114034330828801) (P := 173620637162592228068661657601) prime_q089 (by norm_num)
    (by norm_num) prime_P089 (by omega) (by omega)

theorem wps_chain090 {M : ℕ} (h1 : 346960199072124054854204129282 ≤ M) (h2 : M ≤ 693920398144248109708408258562) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 173480099536062027427102064641) (P := 346960199072124054854204129281) prime_q090 (by norm_num)
    (by norm_num) prime_P090 (by omega) (by omega)

theorem wps_chain091 {M : ℕ} (h1 : 693882316980930248889405014018 ≤ M) (h2 : M ≤ 1387764633961860497778810028034) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 346941158490465124444702507009) (P := 693882316980930248889405014017) prime_q091 (by norm_num)
    (by norm_num) prime_P091 (by omega) (by omega)

theorem wps_chain092 {M : ℕ} (h1 : 1386163411713780921436911697922 ≤ M) (h2 : M ≤ 2772326823427561842873823395842) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 693081705856890460718455848961) (P := 1386163411713780921436911697921) prime_q092 (by norm_num)
    (by norm_num) prime_P092 (by omega) (by omega)

theorem wps_chain093 {M : ℕ} (h1 : 2767155038771250459264430374914 ≤ M) (h2 : M ≤ 5534310077542500918528860749826) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 1383577519385625229632215187457) (P := 2767155038771250459264430374913) prime_q093 (by norm_num)
    (by norm_num) prime_P093 (by omega) (by omega)

theorem wps_chain094 {M : ℕ} (h1 : 5532576477917173540292332093442 ≤ M) (h2 : M ≤ 11065152955834347080584664186882) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 2766288238958586770146166046721) (P := 5532576477917173540292332093441) prime_q094 (by norm_num)
    (by norm_num) prime_P094 (by omega) (by omega)

theorem wps_chain095 {M : ℕ} (h1 : 11053779381723412649309028483074 ≤ M) (h2 : M ≤ 22107558763446825298618056966146) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 5526889690861706324654514241537) (P := 11053779381723412649309028483073) prime_q095 (by norm_num)
    (by norm_num) prime_P095 (by omega) (by omega)

theorem wps_chain096 {M : ℕ} (h1 : 22097316743903050160249946243074 ≤ M) (h2 : M ≤ 44194633487806100320499892486146) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 11048658371951525080124973121537) (P := 22097316743903050160249946243073) prime_q096 (by norm_num)
    (by norm_num) prime_P096 (by omega) (by omega)

theorem wps_chain097 {M : ℕ} (h1 : 44169042946056497850129712152578 ≤ M) (h2 : M ≤ 88338085892112995700259424305154) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 22084521473028248925064856076289) (P := 44169042946056497850129712152577) prime_q097 (by norm_num)
    (by norm_num) prime_P097 (by omega) (by omega)

theorem wps_chain098 {M : ℕ} (h1 : 88197541012027877370924783108098 ≤ M) (h2 : M ≤ 176395082024055754741849566216194) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 44098770506013938685462391554049) (P := 88197541012027877370924783108097) prime_q098 (by norm_num)
    (by norm_num) prime_P098 (by omega) (by omega)

theorem wps_chain099 {M : ℕ} (h1 : 176021378874696480571364393091074 ≤ M) (h2 : M ≤ 352042757749392961142728786182146) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 88010689437348240285682196545537) (P := 176021378874696480571364393091073) prime_q099 (by norm_num)
    (by norm_num) prime_P099 (by omega) (by omega)

theorem wps_chain100 {M : ℕ} (h1 : 351303707545939589118614009020418 ≤ M) (h2 : M ≤ 702607415091879178237228018040834) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 175651853772969794559307004510209) (P := 351303707545939589118614009020417) prime_q100 (by norm_num)
    (by norm_num) prime_P100 (by omega) (by omega)

theorem wps_chain101 {M : ℕ} (h1 : 700683656270829697290034778996738 ≤ M) (h2 : M ≤ 1401367312541659394580069557993474) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 350341828135414848645017389498369) (P := 700683656270829697290034778996737) prime_q101 (by norm_num)
    (by norm_num) prime_P101 (by omega) (by omega)

theorem wps_chain102 {M : ℕ} (h1 : 1399982057637699054052457437986818 ≤ M) (h2 : M ≤ 2799964115275398108104914875973634) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 699991028818849527026228718993409) (P := 1399982057637699054052457437986817) prime_q102 (by norm_num)
    (by norm_num) prime_P102 (by omega) (by omega)

theorem wps_chain103 {M : ℕ} (h1 : 2798727413176152013210290650873858 ≤ M) (h2 : M ≤ 5597454826352304026420581301747714) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 1399363706588076006605145325436929) (P := 2798727413176152013210290650873857) prime_q103 (by norm_num)
    (by norm_num) prime_P103 (by omega) (by omega)

theorem wps_chain104 {M : ℕ} (h1 : 5594275796331419169874640350740482 ≤ M) (h2 : M ≤ 11188551592662838339749280701480962) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 2797137898165709584937320175370241) (P := 5594275796331419169874640350740481) prime_q104 (by norm_num)
    (by norm_num) prime_P104 (by omega) (by omega)

theorem wps_chain105 {M : ℕ} (h1 : 11186011339702224739425187698573314 ≤ M) (h2 : M ≤ 22372022679404449478850375397146626) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 5593005669851112369712593849286657) (P := 11186011339702224739425187698573313) prime_q105 (by norm_num)
    (by norm_num) prime_P105 (by omega) (by omega)

theorem wps_chain106 {M : ℕ} (h1 : 22352205735255569111409790216568834 ≤ M) (h2 : M ≤ 44704411470511138222819580433137666) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 11176102867627784555704895108284417) (P := 22352205735255569111409790216568833) prime_q106 (by norm_num)
    (by norm_num) prime_P106 (by omega) (by omega)

theorem wps_chain107 {M : ℕ} (h1 : 44695438881106397786587111580762114 ≤ M) (h2 : M ≤ 89390877762212795573174223161524226) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 22347719440553198893293555790381057) (P := 44695438881106397786587111580762113) prime_q107 (by norm_num)
    (by norm_num) prime_P107 (by omega) (by omega)

theorem wps_chain108 {M : ℕ} (h1 : 89328129057501498217800136352858114 ≤ M) (h2 : M ≤ 178656258115002996435600272705716226) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 44664064528750749108900068176429057) (P := 89328129057501498217800136352858113) prime_q108 (by norm_num)
    (by norm_num) prime_P108 (by omega) (by omega)

theorem wps_chain109 {M : ℕ} (h1 : 178410016985908662874359538108071938 ≤ M) (h2 : M ≤ 356820033971817325748719076216143874) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 89205008492954331437179769054035969) (P := 178410016985908662874359538108071937) prime_q109 (by norm_num)
    (by norm_num) prime_P109 (by omega) (by omega)

theorem wps_chain110 {M : ℕ} (h1 : 354565834291961476815507563741184002 ≤ M) (h2 : M ≤ 709131668583922953631015127482368002) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 177282917145980738407753781870592001) (P := 354565834291961476815507563741184001) prime_q110 (by norm_num)
    (by norm_num) prime_P110 (by omega) (by omega)

theorem wps_chain111 {M : ℕ} (h1 : 708697181340694728003652132458725378 ≤ M) (h2 : M ≤ 1417394362681389456007304264917450754) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 354348590670347364001826066229362689) (P := 708697181340694728003652132458725377) prime_q111 (by norm_num)
    (by norm_num) prime_P111 (by omega) (by omega)

theorem wps_chain112 {M : ℕ} (h1 : 1414648631481295111123662405774606338 ≤ M) (h2 : M ≤ 2829297262962590222247324811549212674) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 707324315740647555561831202887303169) (P := 1414648631481295111123662405774606337) prime_q112 (by norm_num)
    (by norm_num) prime_P112 (by omega) (by omega)

theorem wps_chain113 {M : ℕ} (h1 : 2826543925858894507987273972187136002 ≤ M) (h2 : M ≤ 5653087851717789015974547944374272002) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 1413271962929447253993636986093568001) (P := 2826543925858894507987273972187136001) prime_q113 (by norm_num)
    (by norm_num) prime_P113 (by omega) (by omega)

theorem wps_chain114 {M : ℕ} (h1 : 5639982879812629580421875026637094914 ≤ M) (h2 : M ≤ 11279965759625259160843750053274189826) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 2819991439906314790210937513318547457) (P := 5639982879812629580421875026637094913) prime_q114 (by norm_num)
    (by norm_num) prime_P114 (by omega) (by omega)

theorem wps_chain115 {M : ℕ} (h1 : 11276482255775831986448437112865816578 ≤ M) (h2 : M ≤ 22552964511551663972896874225731633154) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 5638241127887915993224218556432908289) (P := 11276482255775831986448437112865816577) prime_q115 (by norm_num)
    (by norm_num) prime_P115 (by omega) (by omega)

theorem wps_chain116 {M : ℕ} (h1 : 22538209058565007382663452600421056514 ≤ M) (h2 : M ≤ 45076418117130014765326905200842113026) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 11269104529282503691331726300210528257) (P := 22538209058565007382663452600421056513) prime_q116 (by norm_num)
    (by norm_num) prime_P116 (by omega) (by omega)

theorem wps_chain117 {M : ℕ} (h1 : 45018430708073174639584840009415393282 ≤ M) (h2 : M ≤ 90036861416146349279169680018830786562) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 22509215354036587319792420004707696641) (P := 45018430708073174639584840009415393281) prime_q117 (by norm_num)
    (by norm_num) prime_P117 (by omega) (by omega)

theorem wps_chain118 {M : ℕ} (h1 : 89953135629302475183659625765522112514 ≤ M) (h2 : M ≤ 179906271258604950367319251531044225026) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 44976567814651237591829812882761056257) (P := 89953135629302475183659625765522112513) prime_q118 (by norm_num)
    (by norm_num) prime_P118 (by omega) (by omega)

theorem wps_chain119 {M : ℕ} (h1 : 179861974476030575119113350734235566082 ≤ M) (h2 : M ≤ 359723948952061150238226701468471132162) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 89930987238015287559556675367117783041) (P := 179861974476030575119113350734235566081) prime_q119 (by norm_num)
    (by norm_num) prime_P119 (by omega) (by omega)

theorem wps_chain120 {M : ℕ} (h1 : 359560391601017303167927990834100699138 ≤ M) (h2 : M ≤ 719120783202034606335855981668201398274) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 179780195800508651583963995417050349569) (P := 359560391601017303167927990834100699137) prime_q120 (by norm_num)
    (by norm_num) prime_P120 (by omega) (by omega)

theorem wps_chain121 {M : ℕ} (h1 : 717017902974328001146301130654867259394 ≤ M) (h2 : M ≤ 1434035805948656002292602261309734518786) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 358508951487164000573150565327433629697) (P := 717017902974328001146301130654867259393) prime_q121 (by norm_num)
    (by norm_num) prime_P121 (by omega) (by omega)

theorem wps_chain122 {M : ℕ} (h1 : 1433915085046695067550238927270080151554 ≤ M) (h2 : M ≤ 2867830170093390135100477854540160303106) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 716957542523347533775119463635040075777) (P := 1433915085046695067550238927270080151553) prime_q122 (by norm_num)
    (by norm_num) prime_P122 (by omega) (by omega)

theorem wps_chain123 {M : ℕ} (h1 : 2867619882070619474581522369438826889218 ≤ M) (h2 : M ≤ 5735239764141238949163044738877653778434) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 1433809941035309737290761184719413444609) (P := 2867619882070619474581522369438826889217) prime_q123 (by norm_num)
    (by norm_num) prime_P123 (by omega) (by omega)

theorem wps_chain124 {M : ℕ} (h1 : 5735239764141238949163044738877653778434 ≤ M) (h2 : M ≤ 11470479528282477898326089477755307556866) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 2867619882070619474581522369438826889217) (P := 5735239764141238949163044738877653778433) prime_q124 (by norm_num)
    (by norm_num) prime_P124 (by omega) (by omega)

theorem wps_chain125 {M : ℕ} (h1 : 11429465575396911294888327087250798018562 ≤ M) (h2 : M ≤ 22858931150793822589776654174501596037122) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 5714732787698455647444163543625399009281) (P := 11429465575396911294888327087250798018561) prime_q125 (by norm_num)
    (by norm_num) prime_P125 (by omega) (by omega)

theorem wps_chain126 {M : ℕ} (h1 : 22834350817465518715783190804879068102658 ≤ M) (h2 : M ≤ 45668701634931037431566381609758136205314) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 11417175408732759357891595402439534051329) (P := 22834350817465518715783190804879068102657) prime_q126 (by norm_num)
    (by norm_num) prime_P126 (by omega) (by omega)

theorem wps_chain127 {M : ℕ} (h1 : 45666832408061964893620110631079616970754 ≤ M) (h2 : M ≤ 91333664816123929787240221262159233941506) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 22833416204030982446810055315539808485377) (P := 45666832408061964893620110631079616970753) prime_q127 (by norm_num)
    (by norm_num) prime_P127 (by omega) (by omega)

theorem wps_chain128 {M : ℕ} (h1 : 91315346392807018915366765671109745442818 ≤ M) (h2 : M ≤ 182630692785614037830733531342219490885634) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 45657673196403509457683382835554872721409) (P := 91315346392807018915366765671109745442817) prime_q128 (by norm_num)
    (by norm_num) prime_P128 (by omega) (by omega)

theorem wps_chain129 {M : ℕ} (h1 : 182319404204351157844747871026290087690242 ≤ M) (h2 : M ≤ 364638808408702315689495742052580175380482) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 91159702102175578922373935513145043845121) (P := 182319404204351157844747871026290087690241) prime_q129 (by norm_num)
    (by norm_num) prime_P129 (by omega) (by omega)

theorem wps_chain130 {M : ℕ} (h1 : 364370636660552708912137398978168615862274 ≤ M) (h2 : M ≤ 728741273321105417824274797956337231724546) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 182185318330276354456068699489084307931137) (P := 364370636660552708912137398978168615862273) prime_q130 (by norm_num)
    (by norm_num) prime_P130 (by omega) (by omega)

theorem wps_chain131 {M : ℕ} (h1 : 728333532633398394880261555140596236025858 ≤ M) (h2 : M ≤ 1456667065266796789760523110281192472051714) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 364166766316699197440130777570298118012929) (P := 728333532633398394880261555140596236025857) prime_q131 (by norm_num)
    (by norm_num) prime_P131 (by omega) (by omega)

theorem wps_chain132 {M : ℕ} (h1 : 1454842699842581992724962635090957699121154 ≤ M) (h2 : M ≤ 2909685399685163985449925270181915398242306) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 727421349921290996362481317545478849560577) (P := 1454842699842581992724962635090957699121153) prime_q132 (by norm_num)
    (by norm_num) prime_P132 (by omega) (by omega)

theorem wps_chain133 {M : ℕ} (h1 : 2897530938891706714708092858422711927439362 ≤ M) (h2 : M ≤ 5795061877783413429416185716845423854878722) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 1448765469445853357354046429211355963719681) (P := 2897530938891706714708092858422711927439361) prime_q133 (by norm_num)
    (by norm_num) prime_P133 (by omega) (by omega)

theorem wps_chain134 {M : ℕ} (h1 : 5795037951679489300930473448318338808676354 ≤ M) (h2 : M ≤ 11590075903358978601860946896636677617352706) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 2897518975839744650465236724159169404338177) (P := 5795037951679489300930473448318338808676353) prime_q134 (by norm_num)
    (by norm_num) prime_P134 (by omega) (by omega)

theorem wps_chain135 {M : ℕ} (h1 : 11570823365068029880357808155175577106513922 ≤ M) (h2 : M ≤ 23141646730136059760715616310351154213027842) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 5785411682534014940178904077587788553256961) (P := 11570823365068029880357808155175577106513921) prime_q135 (by norm_num)
    (by norm_num) prime_P135 (by omega) (by omega)

theorem wps_chain136 {M : ℕ} (h1 : 23136478691688448007801766308500784233316354 ≤ M) (h2 : M ≤ 46272957383376896015603532617001568466632706) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 11568239345844224003900883154250392116658177) (P := 23136478691688448007801766308500784233316353) prime_q136 (by norm_num)
    (by norm_num) prime_P136 (by omega) (by omega)

theorem wps_chain137 {M : ℕ} (h1 : 46201115268660712882504827653007536402989058 ≤ M) (h2 : M ≤ 92402230537321425765009655306015072805978114) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 23100557634330356441252413826503768201494529) (P := 46201115268660712882504827653007536402989057) prime_q137 (by norm_num)
    (by norm_num) prime_P137 (by omega) (by omega)

theorem wps_chain138 {M : ℕ} (h1 : 92400316449007495486152673823848269109788674 ≤ M) (h2 : M ≤ 184800632898014990972305347647696538219577346) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 46200158224503747743076336911924134554894337) (P := 92400316449007495486152673823848269109788673) prime_q138 (by norm_num)
    (by norm_num) prime_P138 (by omega) (by omega)

theorem wps_chain139 {M : ℕ} (h1 : 184606416737094865344283626590504856512888834 ≤ M) (h2 : M ≤ 369212833474189730688567253181009713025777666) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 92303208368547432672141813295252428256444417) (P := 184606416737094865344283626590504856512888833) prime_q139 (by norm_num)
    (by norm_num) prime_P139 (by omega) (by omega)

theorem wps_chain140 {M : ℕ} (h1 : 368512021939516057923064433177003986394284034 ≤ M) (h2 : M ≤ 737024043879032115846128866354007972788568066) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 184256010969758028961532216588501993197142017) (P := 368512021939516057923064433177003986394284033) prime_q140 (by norm_num)
    (by norm_num) prime_P140 (by omega) (by omega)

theorem wps_chain141 {M : ℕ} (h1 : 736330888697614164196053972278669460941832194 ≤ M) (h2 : M ≤ 1472661777395228328392107944557338921883664386) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 368165444348807082098026986139334730470916097) (P := 736330888697614164196053972278669460941832193) prime_q141 (by norm_num)
    (by norm_num) prime_P141 (by omega) (by omega)

theorem wps_chain142 {M : ℕ} (h1 : 1465021757693119418010428257871280862000054274 ≤ M) (h2 : M ≤ 2930043515386238836020856515742561724000108546) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 732510878846559709005214128935640431000027137) (P := 1465021757693119418010428257871280862000054273) prime_q142 (by norm_num)
    (by norm_num) prime_P142 (by omega) (by omega)

theorem wps_chain143 {M : ℕ} (h1 : 2926196963510564547629866529180153016137809922 ≤ M) (h2 : M ≤ 5852393927021129095259733058360306032275619842) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 1463098481755282273814933264590076508068904961) (P := 2926196963510564547629866529180153016137809921) prime_q143 (by norm_num)
    (by norm_num) prime_P143 (by omega) (by omega)

theorem wps_chain144 {M : ℕ} (h1 : 5851283245375499152114988603641648740833427458 ≤ M) (h2 : M ≤ 11702566490750998304229977207283297481666854914) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 2925641622687749576057494301820824370416713729) (P := 5851283245375499152114988603641648740833427457) prime_q144 (by norm_num)
    (by norm_num) prime_P144 (by omega) (by omega)

theorem wps_chain145 {M : ℕ} (h1 : 11695069389642996188002952137932360764432056322 ≤ M) (h2 : M ≤ 23390138779285992376005904275864721528864112642) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 5847534694821498094001476068966180382216028161) (P := 11695069389642996188002952137932360764432056321) prime_q145 (by norm_num)
    (by norm_num) prime_P145 (by omega) (by omega)

theorem wps_chain146 {M : ℕ} (h1 : 23340648111841011085879791072959845160189952002 ≤ M) (h2 : M ≤ 46681296223682022171759582145919690320379904002) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 11670324055920505542939895536479922580094976001) (P := 23340648111841011085879791072959845160189952001) prime_q146 (by norm_num)
    (by norm_num) prime_P146 (by omega) (by omega)

theorem wps_chain147 {M : ℕ} (h1 : 46310851227757211722894814013285170174660444162 ≤ M) (h2 : M ≤ 92621702455514423445789628026570340349320888322) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 23155425613878605861447407006642585087330222081) (P := 46310851227757211722894814013285170174660444161) prime_q147 (by norm_num)
    (by norm_num) prime_P147 (by omega) (by omega)

theorem wps_chain148 {M : ℕ} (h1 : 91637115843770703258066161402442964935565639682 ≤ M) (h2 : M ≤ 183274231687541406516132322804885929871131279362) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 45818557921885351629033080701221482467782819841) (P := 91637115843770703258066161402442964935565639681) prime_q148 (by norm_num)
    (by norm_num) prime_P148 (by omega) (by omega)

theorem wps_chain149 {M : ℕ} (h1 : 183221180305408964525924528850088887479892443138 ≤ M) (h2 : M ≤ 366442360610817929051849057700177774959784886274) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 91610590152704482262962264425044443739946221569) (P := 183221180305408964525924528850088887479892443137) prime_q149 (by norm_num)
    (by norm_num) prime_P149 (by omega) (by omega)

theorem wps_chain150 {M : ℕ} (h1 : 366138687182059812832038926786511946099590168578 ≤ M) (h2 : M ≤ 732277374364119625664077853573023892199180337154) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 183069343591029906416019463393255973049795084289) (P := 366138687182059812832038926786511946099590168577) prime_q150 (by norm_num)
    (by norm_num) prime_P150 (by omega) (by omega)

theorem wps_chain151 {M : ℕ} (h1 : 731299974515965275696702733420605475730051039234 ≤ M) (h2 : M ≤ 1462599949031930551393405466841210951460102078466) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 365649987257982637848351366710302737865025519617) (P := 731299974515965275696702733420605475730051039233) prime_q151 (by norm_num)
    (by norm_num) prime_P151 (by omega) (by omega)

theorem wps_chain152 {M : ℕ} (h1 : 1460881397855068785247560870551824987101547462658 ≤ M) (h2 : M ≤ 2921762795710137570495121741103649974203094925314) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 730440698927534392623780435275912493550773731329) (P := 1460881397855068785247560870551824987101547462657) prime_q152 (by norm_num)
    (by norm_num) prime_P152 (by omega) (by omega)

theorem wps_chain153 {M : ℕ} (h1 : 2921733525982064499052248475473417123228618326018 ≤ M) (h2 : M ≤ 5843467051964128998104496950946834246457236652034) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 1460866762991032249526124237736708561614309163009) (P := 2921733525982064499052248475473417123228618326017) prime_q153 (by norm_num)
    (by norm_num) prime_P153 (by omega) (by omega)

theorem wps_chain154 {M : ℕ} (h1 : 5842191728098088028093590377058117168283613396994 ≤ M) (h2 : M ≤ 11684383456196176056187180754116234336567226793986) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 2921095864049044014046795188529058584141806698497) (P := 5842191728098088028093590377058117168283613396993) prime_q154 (by norm_num)
    (by norm_num) prime_P154 (by omega) (by omega)

theorem wps_chain155 {M : ℕ} (h1 : 11669882396630831518489397153309444739497963028482 ≤ M) (h2 : M ≤ 23339764793261663036978794306618889478995926056962) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 5834941198315415759244698576654722369748981514241) (P := 11669882396630831518489397153309444739497963028481) prime_q155 (by norm_num)
    (by norm_num) prime_P155 (by omega) (by omega)

theorem wps_chain156 {M : ℕ} (h1 : 23323055959921663967589998669703107694137570230274 ≤ M) (h2 : M ≤ 46646111919843327935179997339406215388275140460546) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 11661527979960831983794999334851553847068785115137) (P := 23323055959921663967589998669703107694137570230273) prime_q156 (by norm_num)
    (by norm_num) prime_P156 (by omega) (by omega)

theorem wps_chain157 {M : ℕ} (h1 : 46643368928183908668533588446058679639809904869378 ≤ M) (h2 : M ≤ 93286737856367817337067176892117359279619809738754) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 23321684464091954334266794223029339819904952434689) (P := 46643368928183908668533588446058679639809904869377) prime_q157 (by norm_num)
    (by norm_num) prime_P157 (by omega) (by omega)

theorem wps_chain158 {M : ℕ} (h1 : 92741886049677317152473176223280014511305696215042 ≤ M) (h2 : M ≤ 185483772099354634304946352446560029022611392430082) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 46370943024838658576236588111640007255652848107521) (P := 92741886049677317152473176223280014511305696215041) prime_q158 (by norm_num)
    (by norm_num) prime_P158 (by omega) (by omega)

theorem wps_chain159 {M : ℕ} (h1 : 185309157264450139525748127772485192352019565772802 ≤ M) (h2 : M ≤ 370618314528900279051496255544970384704039131545602) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 92654578632225069762874063886242596176009782886401) (P := 185309157264450139525748127772485192352019565772801) prime_q159 (by norm_num)
    (by norm_num) prime_P159 (by omega) (by omega)

theorem wps_chain160 {M : ℕ} (h1 : 369689176280948699168927311378858763370253963493378 ≤ M) (h2 : M ≤ 739378352561897398337854622757717526740507926986754) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 184844588140474349584463655689429381685126981746689) (P := 369689176280948699168927311378858763370253963493377) prime_q160 (by norm_num)
    (by norm_num) prime_P160 (by omega) (by omega)

theorem wps_chain161 {M : ℕ} (h1 : 738787472017117130947096492366365435754045469884418 ≤ M) (h2 : M ≤ 1477574944034234261894192984732730871508090939768834) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 369393736008558565473548246183182717877022734942209) (P := 738787472017117130947096492366365435754045469884417) prime_q161 (by norm_num)
    (by norm_num) prime_P161 (by omega) (by omega)

theorem wps_chain162 {M : ℕ} (h1 : 1477312687270699541766048524685844526776780610076674 ≤ M) (h2 : M ≤ 2954625374541399083532097049371689053553561220153346) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 738656343635349770883024262342922263388390305038337) (P := 1477312687270699541766048524685844526776780610076673) prime_q162 (by norm_num)
    (by norm_num) prime_P162 (by omega) (by omega)

theorem wps_chain163 {M : ℕ} (h1 : 2949846949266219529850313907945972143836951784456194 ≤ M) (h2 : M ≤ 5899693898532439059700627815891944287673903568912386) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 1474923474633109764925156953972986071918475892228097) (P := 2949846949266219529850313907945972143836951784456193) prime_q163 (by norm_num)
    (by norm_num) prime_P163 (by omega) (by omega)

theorem wps_chain164 {M : ℕ} (h1 : 5894816993166462794787051652734335362792883723698178 ≤ M) (h2 : M ≤ 11789633986332925589574103305468670725585767447396354) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 2947408496583231397393525826367167681396441861849089) (P := 5894816993166462794787051652734335362792883723698177) prime_q164 (by norm_num)
    (by norm_num) prime_P164 (by omega) (by omega)

theorem wps_chain165 {M : ℕ} (h1 : 11788280955520240339606860050369632604196476603596802 ≤ M) (h2 : M ≤ 23576561911040480679213720100739265208392953207193602) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 5894140477760120169803430025184816302098238301798401) (P := 11788280955520240339606860050369632604196476603596801) prime_q165 (by norm_num)
    (by norm_num) prime_P165 (by omega) (by omega)

theorem wps_chain166 {M : ℕ} (h1 : 23538111858198982120018009876722295809418802013143042 ≤ M) (h2 : M ≤ 47076223716397964240036019753444591618837604026286082) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 11769055929099491060009004938361147904709401006571521) (P := 23538111858198982120018009876722295809418802013143041) prime_q166 (by norm_num)
    (by norm_num) prime_P166 (by omega) (by omega)

theorem wps_chain167 {M : ℕ} (h1 : 46970447535396140141331028063676750635290005908488194 ≤ M) (h2 : M ≤ 93940895070792280282662056127353501270580011816976386) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 23485223767698070070665514031838375317645002954244097) (P := 46970447535396140141331028063676750635290005908488193) prime_q167 (by norm_num)
    (by norm_num) prime_P167 (by omega) (by omega)

theorem wps_chain168 {M : ℕ} (h1 : 93836489047575453905442880392116331802363341135937538 ≤ M) (h2 : M ≤ 187672978095150907810885760784232663604726682271875074) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 46918244523787726952721440196058165901181670567968769) (P := 93836489047575453905442880392116331802363341135937537) prime_q168 (by norm_num)
    (by norm_num) prime_P168 (by omega) (by omega)

theorem wps_chain169 {M : ℕ} (h1 : 187537469490214633155938562881149250738497958776406018 ≤ M) (h2 : M ≤ 375074938980429266311877125762298501476995917552812034) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 93768734745107316577969281440574625369248979388203009) (P := 187537469490214633155938562881149250738497958776406017) prime_q169 (by norm_num)
    (by norm_num) prime_P169 (by omega) (by omega)

theorem wps_chain170 {M : ℕ} (h1 : 375074938980429266311877125762298501476995917552812034 ≤ M) (h2 : M ≤ 750149877960858532623754251524597002953991835105624066) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 187537469490214633155938562881149250738497958776406017) (P := 375074938980429266311877125762298501476995917552812033) prime_q170 (by norm_num)
    (by norm_num) prime_P170 (by omega) (by omega)

theorem wps_chain171 {M : ℕ} (h1 : 748745192199678868556495734939752565436725026940256258 ≤ M) (h2 : M ≤ 1497490384399357737112991469879505130873450053880512514) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 374372596099839434278247867469876282718362513470128129) (P := 748745192199678868556495734939752565436725026940256257) prime_q171 (by norm_num)
    (by norm_num) prime_P171 (by omega) (by omega)

theorem wps_chain172 {M : ℕ} (h1 : 1494672243867174423560965214600819958140798501954519042 ≤ M) (h2 : M ≤ 2989344487734348847121930429201639916281597003909038082) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 747336121933587211780482607300409979070399250977259521) (P := 1494672243867174423560965214600819958140798501954519041) prime_q172 (by norm_num)
    (by norm_num) prime_P172 (by omega) (by omega)

theorem wps_chain173 {M : ℕ} (h1 : 2983239064644399000181134535812967643966984345710755842 ≤ M) (h2 : M ≤ 5966478129288798000362269071625935287933968691421511682) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 1491619532322199500090567267906483821983492172855377921) (P := 2983239064644399000181134535812967643966984345710755841) prime_q173 (by norm_num)
    (by norm_num) prime_P173 (by omega) (by omega)

theorem wps_chain174 {M : ℕ} (h1 : 5956183311755439120206442315664281790343512302588788738 ≤ M) (h2 : M ≤ 11912366623510878240412884631328563580687024605177577474) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 2978091655877719560103221157832140895171756151294394369) (P := 5956183311755439120206442315664281790343512302588788737) prime_q174 (by norm_num)
    (by norm_num) prime_P174 (by omega) (by omega)

theorem wps_chain175 {M : ℕ} (h1 : 11891189464785953457128113238102504639732210142629855234 ≤ M) (h2 : M ≤ 23782378929571906914256226476205009279464420285259710466) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 5945594732392976728564056619051252319866105071314927617) (P := 11891189464785953457128113238102504639732210142629855233) prime_q175 (by norm_num)
    (by norm_num) prime_P175 (by omega) (by omega)

theorem wps_chain176 {M : ℕ} (h1 : 23739217863218250689275835255725232009327941285400543234 ≤ M) (h2 : M ≤ 47478435726436501378551670511450464018655882570801086466) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 11869608931609125344637917627862616004663970642700271617) (P := 23739217863218250689275835255725232009327941285400543233) prime_q176 (by norm_num)
    (by norm_num) prime_P176 (by omega) (by omega)

theorem wps_chain177 {M : ℕ} (h1 : 47414877943232255072444828665445298302697085376372146178 ≤ M) (h2 : M ≤ 94829755886464510144889657330890596605394170752744292354) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 23707438971616127536222414332722649151348542688186073089) (P := 47414877943232255072444828665445298302697085376372146177) prime_q177 (by norm_num)
    (by norm_num) prime_P177 (by omega) (by omega)

theorem wps_chain178 {M : ℕ} (h1 : 94787384030995012607485096100220486128088305956458332162 ≤ M) (h2 : M ≤ 189574768061990025214970192200440972256176611912916664322) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 47393692015497506303742548050110243064044152978229166081) (P := 94787384030995012607485096100220486128088305956458332161) prime_q178 (by norm_num)
    (by norm_num) prime_P178 (by omega) (by omega)

theorem wps_chain179 {M : ℕ} (h1 : 189503493550140671741455234898519064565874031394660810754 ≤ M) (h2 : M ≤ 379006987100281343482910469797038129131748062789321621506) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 94751746775070335870727617449259532282937015697330405377) (P := 189503493550140671741455234898519064565874031394660810753) prime_q179 (by norm_num)
    (by norm_num) prime_P179 (by omega) (by omega)

theorem wps_chain180 {M : ℕ} (h1 : 377160023175114238905448072311801922763355995973730959362 ≤ M) (h2 : M ≤ 754320046350228477810896144623603845526711991947461918722) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 188580011587557119452724036155900961381677997986865479681) (P := 377160023175114238905448072311801922763355995973730959361) prime_q180 (by norm_num)
    (by norm_num) prime_P180 (by omega) (by omega)

theorem wps_chain181 {M : ℕ} (h1 : 750550915471643769715412260846379183730868442651349221378 ≤ M) (h2 : M ≤ 1501101830943287539430824521692758367461736885302698442754) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 375275457735821884857706130423189591865434221325674610689) (P := 750550915471643769715412260846379183730868442651349221377) prime_q181 (by norm_num)
    (by norm_num) prime_P181 (by omega) (by omega)

theorem wps_chain182 {M : ℕ} (h1 : 1499580933879415508618025039108440494700162135661175898114 ≤ M) (h2 : M ≤ 2999161867758831017236050078216880989400324271322351796226) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 749790466939707754309012519554220247350081067830587949057) (P := 1499580933879415508618025039108440494700162135661175898113) prime_q182 (by norm_num)
    (by norm_num) prime_P182 (by omega) (by omega)

theorem wps_chain183 {M : ℕ} (h1 : 2998582692197976428380400976361893519035030861126760923138 ≤ M) (h2 : M ≤ 5997165384395952856760801952723787038070061722253521846274) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 1499291346098988214190200488180946759517515430563380461569) (P := 2998582692197976428380400976361893519035030861126760923137) prime_q183 (by norm_num)
    (by norm_num) prime_P183 (by omega) (by omega)

theorem wps_chain184 {M : ℕ} (h1 : 5988859378290673869296066771082493858412753126425280643074 ≤ M) (h2 : M ≤ 11977718756581347738592133542164987716825506252850561286146) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 2994429689145336934648033385541246929206376563212640321537) (P := 5988859378290673869296066771082493858412753126425280643073) prime_q184 (by norm_num)
    (by norm_num) prime_P184 (by omega) (by omega)

theorem wps_chain185 {M : ℕ} (h1 : 11973220044085407443759882378919271086546250462028994969602 ≤ M) (h2 : M ≤ 23946440088170814887519764757838542173092500924057989939202) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 5986610022042703721879941189459635543273125231014497484801) (P := 11973220044085407443759882378919271086546250462028994969601) prime_q185 (by norm_num)
    (by norm_num) prime_P185 (by omega) (by omega)

theorem wps_chain186 {M : ℕ} (h1 : 23946440088170814887519764757838542173092500924057989939202 ≤ M) (h2 : M ≤ 47892880176341629775039529515677084346185001848115979878402) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 11973220044085407443759882378919271086546250462028994969601) (P := 23946440088170814887519764757838542173092500924057989939201) prime_q186 (by norm_num)
    (by norm_num) prime_P186 (by omega) (by omega)

theorem wps_chain187 {M : ℕ} (h1 : 47793064431621325748382236240947770848811334441384380727298 ≤ M) (h2 : M ≤ 95586128863242651496764472481895541697622668882768761454594) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 23896532215810662874191118120473885424405667220692190363649) (P := 47793064431621325748382236240947770848811334441384380727297) prime_q187 (by norm_num)
    (by norm_num) prime_P187 (by omega) (by omega)

theorem wps_chain188 {M : ℕ} (h1 : 95331758548701739975790398724560889596722952231285067612162 ≤ M) (h2 : M ≤ 190663517097403479951580797449121779193445904462570135224322) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 47665879274350869987895199362280444798361476115642533806081) (P := 95331758548701739975790398724560889596722952231285067612161) prime_q188 (by norm_num)
    (by norm_num) prime_P188 (by omega) (by omega)

theorem wps_chain189 {M : ℕ} (h1 : 190540534330248992370697540100192966881460500648014901149698 ≤ M) (h2 : M ≤ 381081068660497984741395080200385933762921001296029802299394) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 95270267165124496185348770050096483440730250324007450574849) (P := 190540534330248992370697540100192966881460500648014901149697) prime_q189 (by norm_num)
    (by norm_num) prime_P189 (by omega) (by omega)

theorem wps_chain190 {M : ℕ} (h1 : 381062678714007594075094780036060130052717576426563599073282 ≤ M) (h2 : M ≤ 762125357428015188150189560072120260105435152853127198146562) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 190531339357003797037547390018030065026358788213281799536641) (P := 381062678714007594075094780036060130052717576426563599073281) prime_q190 (by norm_num)
    (by norm_num) prime_P190 (by omega) (by omega)

theorem wps_chain191 {M : ℕ} (h1 : 758482998651262186806086358775340762753269314644477321674754 ≤ M) (h2 : M ≤ 1516965997302524373612172717550681525506538629288954643349506) : WindowPairSupply M :=
  windowPairSupply_of_prime_pair (q := 379241499325631093403043179387670381376634657322238660837377) (P := 758482998651262186806086358775340762753269314644477321674753) prime_q191 (by norm_num)
    (by norm_num) prime_P191 (by omega) (by omega)

theorem wps_block00 {M : ℕ} (h1 : 8 ≤ M) (h2 : M ≤ 4794531842) :
    WindowPairSupply M := by
  rcases le_or_gt M 14 with hle | hgt
  · exact windowPairSupply_seven (le_trans (by norm_num) h1) hle
  rcases le_or_gt M 26 with hle | hgt
  · exact windowPairSupply_thirteen (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 50 with hle | hgt
  · exact windowPairSupply_twentyfive (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 92 with hle | hgt
  · exact windowPairSupply_46 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 164 with hle | hgt
  · exact windowPairSupply_82 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 316 with hle | hgt
  · exact windowPairSupply_158 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 626 with hle | hgt
  · exact wps_chain000 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1226 with hle | hgt
  · exact wps_chain001 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 2426 with hle | hgt
  · exact wps_chain002 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 4682 with hle | hgt
  · exact wps_chain003 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 9242 with hle | hgt
  · exact wps_chain004 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 18482 with hle | hgt
  · exact wps_chain005 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 36962 with hle | hgt
  · exact wps_chain006 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 73826 with hle | hgt
  · exact wps_chain007 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 147386 with hle | hgt
  · exact wps_chain008 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 293906 with hle | hgt
  · exact wps_chain009 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 585554 with hle | hgt
  · exact wps_chain010 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1171034 with hle | hgt
  · exact wps_chain011 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 2342066 with hle | hgt
  · exact wps_chain012 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 4682906 with hle | hgt
  · exact wps_chain013 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 9365474 with hle | hgt
  · exact wps_chain014 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 18730874 with hle | hgt
  · exact wps_chain015 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 37460546 with hle | hgt
  · exact wps_chain016 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 74918882 with hle | hgt
  · exact wps_chain017 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 149837186 with hle | hgt
  · exact wps_chain018 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 299666306 with hle | hgt
  · exact wps_chain019 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 599324162 with hle | hgt
  · exact wps_chain020 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1198648322 with hle | hgt
  · exact wps_chain021 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 2397265922 with hle | hgt
  · exact wps_chain022 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 4794531842 with hle | hgt
  · exact wps_chain023 (cover_step hgt (by norm_num)) hle
  exact absurd h2 (Nat.not_le.2 hgt)

theorem wps_block01 {M : ℕ} (h1 : 4794531843 ≤ M) (h2 : M ≤ 80243664265150466) :
    WindowPairSupply M := by
  rcases le_or_gt M 9588449282 with hle | hgt
  · exact wps_chain024 (le_trans (by norm_num) h1) hle
  rcases le_or_gt M 19176136706 with hle | hgt
  · exact wps_chain025 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 38348685314 with hle | hgt
  · exact wps_chain026 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 76691177474 with hle | hgt
  · exact wps_chain027 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 153382354946 with hle | hgt
  · exact wps_chain028 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 306708480002 with hle | hgt
  · exact wps_chain029 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 613406736386 with hle | hgt
  · exact wps_chain030 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1226796171266 with hle | hgt
  · exact wps_chain031 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 2453428764674 with hle | hgt
  · exact wps_chain032 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 4906737991682 with hle | hgt
  · exact wps_chain033 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 9813475983362 with hle | hgt
  · exact wps_chain034 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 19626951966722 with hle | hgt
  · exact wps_chain035 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 39252142325762 with hle | hgt
  · exact wps_chain036 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 78467240558594 with hle | hgt
  · exact wps_chain037 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 156919180296194 with hle | hgt
  · exact wps_chain038 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 313836347326466 with hle | hgt
  · exact wps_chain039 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 627497943171074 with hle | hgt
  · exact wps_chain040 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1254440224948226 with hle | hgt
  · exact wps_chain041 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 2508545442447362 with hle | hgt
  · exact wps_chain042 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 5017077999992834 with hle | hgt
  · exact wps_chain043 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 10033215402147842 with hle | hgt
  · exact wps_chain044 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 20066430804295682 with hle | hgt
  · exact wps_chain045 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 40127759187443714 with hle | hgt
  · exact wps_chain046 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 80243664265150466 with hle | hgt
  · exact wps_chain047 (cover_step hgt (by norm_num)) hle
  exact absurd h2 (Nat.not_le.2 hgt)

theorem wps_block02 {M : ℕ} (h1 : 80243664265150467 ≤ M) (h2 : M ≤ 1335446272608679955005442) :
    WindowPairSupply M := by
  rcases le_or_gt M 160476402133499906 with hle | hgt
  · exact wps_chain048 (le_trans (by norm_num) h1) hle
  rcases le_or_gt M 320947031830953986 with hle | hgt
  · exact wps_chain049 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 641698625470070786 with hle | hgt
  · exact wps_chain050 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1282801865393700866 with hle | hgt
  · exact wps_chain051 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 2565382728950218754 with hle | hgt
  · exact wps_chain052 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 5128858904737873922 with hle | hgt
  · exact wps_chain053 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 10255356058499284994 with hle | hgt
  · exact wps_chain054 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 20501608160720584706 with hle | hgt
  · exact wps_chain055 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 40988016672698793986 with hle | hgt
  · exact wps_chain056 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 81941939688843509762 with hle | hgt
  · exact wps_chain057 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 163856646673690263554 with hle | hgt
  · exact wps_chain058 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 327635184041343320066 with hle | hgt
  · exact wps_chain059 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 654999307680114278402 with hle | hgt
  · exact wps_chain060 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1309507160050891751426 with hle | hgt
  · exact wps_chain061 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 2618652906231687020546 with hle | hgt
  · exact wps_chain062 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 5232502723460783407106 with hle | hgt
  · exact wps_chain063 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 10458831011832441864194 with hle | hgt
  · exact wps_chain064 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 20911122797005941768194 with hle | hgt
  · exact wps_chain065 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 41817868095174079414274 with hle | hgt
  · exact wps_chain066 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 83635736190348158828546 with hle | hgt
  · exact wps_chain067 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 167260231396026400899074 with hle | hgt
  · exact wps_chain068 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 334237276447483745009666 with hle | hgt
  · exact wps_chain069 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 668009349067858627264514 with hle | hgt
  · exact wps_chain070 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1335446272608679955005442 with hle | hgt
  · exact wps_chain071 (cover_step hgt (by norm_num)) hle
  exact absurd h2 (Nat.not_le.2 hgt)

theorem wps_block03 {M : ℕ} (h1 : 1335446272608679955005443 ≤ M) (h2 : M ≤ 22107558763446825298618056966146) :
    WindowPairSupply M := by
  rcases le_or_gt M 2670093570614667365056514 with hle | hgt
  · exact wps_chain072 (le_trans (by norm_num) h1) hle
  rcases le_or_gt M 5337254108921614911406082 with hle | hgt
  · exact wps_chain073 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 10665058873191472104996866 with hle | hgt
  · exact wps_chain074 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 21316255018211551481954306 with hle | hgt
  · exact wps_chain075 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 42610318603302430373314562 with hle | hgt
  · exact wps_chain076 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 85220637206604860746629122 with hle | hgt
  · exact wps_chain077 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 170431313171409918335385602 with hle | hgt
  · exact wps_chain078 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 340827208594198314331668482 with hle | hgt
  · exact wps_chain079 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 681448994246391799096541186 with hle | hgt
  · exact wps_chain080 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1362448183085290264486477826 with hle | hgt
  · exact wps_chain081 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 2722565878311284359059996674 with hle | hgt
  · exact wps_chain082 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 5442326670931744148863057922 with hle | hgt
  · exact wps_chain083 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 10881593248382588767627640834 with hle | hgt
  · exact wps_chain084 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 21755847939250798106593198082 with hle | hgt
  · exact wps_chain085 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 43491011913306627167150407682 with hle | hgt
  · exact wps_chain086 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 86893621126053934575900426242 with hle | hgt
  · exact wps_chain087 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 173647611319942379482122289154 with hle | hgt
  · exact wps_chain088 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 347241274325184456137323315202 with hle | hgt
  · exact wps_chain089 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 693920398144248109708408258562 with hle | hgt
  · exact wps_chain090 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1387764633961860497778810028034 with hle | hgt
  · exact wps_chain091 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 2772326823427561842873823395842 with hle | hgt
  · exact wps_chain092 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 5534310077542500918528860749826 with hle | hgt
  · exact wps_chain093 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 11065152955834347080584664186882 with hle | hgt
  · exact wps_chain094 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 22107558763446825298618056966146 with hle | hgt
  · exact wps_chain095 (cover_step hgt (by norm_num)) hle
  exact absurd h2 (Nat.not_le.2 hgt)

theorem wps_block04 {M : ℕ} (h1 : 22107558763446825298618056966147 ≤ M) (h2 : M ≤ 359723948952061150238226701468471132162) :
    WindowPairSupply M := by
  rcases le_or_gt M 44194633487806100320499892486146 with hle | hgt
  · exact wps_chain096 (le_trans (by norm_num) h1) hle
  rcases le_or_gt M 88338085892112995700259424305154 with hle | hgt
  · exact wps_chain097 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 176395082024055754741849566216194 with hle | hgt
  · exact wps_chain098 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 352042757749392961142728786182146 with hle | hgt
  · exact wps_chain099 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 702607415091879178237228018040834 with hle | hgt
  · exact wps_chain100 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1401367312541659394580069557993474 with hle | hgt
  · exact wps_chain101 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 2799964115275398108104914875973634 with hle | hgt
  · exact wps_chain102 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 5597454826352304026420581301747714 with hle | hgt
  · exact wps_chain103 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 11188551592662838339749280701480962 with hle | hgt
  · exact wps_chain104 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 22372022679404449478850375397146626 with hle | hgt
  · exact wps_chain105 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 44704411470511138222819580433137666 with hle | hgt
  · exact wps_chain106 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 89390877762212795573174223161524226 with hle | hgt
  · exact wps_chain107 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 178656258115002996435600272705716226 with hle | hgt
  · exact wps_chain108 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 356820033971817325748719076216143874 with hle | hgt
  · exact wps_chain109 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 709131668583922953631015127482368002 with hle | hgt
  · exact wps_chain110 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1417394362681389456007304264917450754 with hle | hgt
  · exact wps_chain111 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 2829297262962590222247324811549212674 with hle | hgt
  · exact wps_chain112 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 5653087851717789015974547944374272002 with hle | hgt
  · exact wps_chain113 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 11279965759625259160843750053274189826 with hle | hgt
  · exact wps_chain114 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 22552964511551663972896874225731633154 with hle | hgt
  · exact wps_chain115 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 45076418117130014765326905200842113026 with hle | hgt
  · exact wps_chain116 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 90036861416146349279169680018830786562 with hle | hgt
  · exact wps_chain117 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 179906271258604950367319251531044225026 with hle | hgt
  · exact wps_chain118 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 359723948952061150238226701468471132162 with hle | hgt
  · exact wps_chain119 (cover_step hgt (by norm_num)) hle
  exact absurd h2 (Nat.not_le.2 hgt)

theorem wps_block05 {M : ℕ} (h1 : 359723948952061150238226701468471132163 ≤ M) (h2 : M ≤ 5852393927021129095259733058360306032275619842) :
    WindowPairSupply M := by
  rcases le_or_gt M 719120783202034606335855981668201398274 with hle | hgt
  · exact wps_chain120 (le_trans (by norm_num) h1) hle
  rcases le_or_gt M 1434035805948656002292602261309734518786 with hle | hgt
  · exact wps_chain121 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 2867830170093390135100477854540160303106 with hle | hgt
  · exact wps_chain122 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 5735239764141238949163044738877653778434 with hle | hgt
  · exact wps_chain123 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 11470479528282477898326089477755307556866 with hle | hgt
  · exact wps_chain124 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 22858931150793822589776654174501596037122 with hle | hgt
  · exact wps_chain125 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 45668701634931037431566381609758136205314 with hle | hgt
  · exact wps_chain126 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 91333664816123929787240221262159233941506 with hle | hgt
  · exact wps_chain127 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 182630692785614037830733531342219490885634 with hle | hgt
  · exact wps_chain128 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 364638808408702315689495742052580175380482 with hle | hgt
  · exact wps_chain129 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 728741273321105417824274797956337231724546 with hle | hgt
  · exact wps_chain130 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1456667065266796789760523110281192472051714 with hle | hgt
  · exact wps_chain131 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 2909685399685163985449925270181915398242306 with hle | hgt
  · exact wps_chain132 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 5795061877783413429416185716845423854878722 with hle | hgt
  · exact wps_chain133 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 11590075903358978601860946896636677617352706 with hle | hgt
  · exact wps_chain134 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 23141646730136059760715616310351154213027842 with hle | hgt
  · exact wps_chain135 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 46272957383376896015603532617001568466632706 with hle | hgt
  · exact wps_chain136 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 92402230537321425765009655306015072805978114 with hle | hgt
  · exact wps_chain137 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 184800632898014990972305347647696538219577346 with hle | hgt
  · exact wps_chain138 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 369212833474189730688567253181009713025777666 with hle | hgt
  · exact wps_chain139 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 737024043879032115846128866354007972788568066 with hle | hgt
  · exact wps_chain140 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1472661777395228328392107944557338921883664386 with hle | hgt
  · exact wps_chain141 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 2930043515386238836020856515742561724000108546 with hle | hgt
  · exact wps_chain142 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 5852393927021129095259733058360306032275619842 with hle | hgt
  · exact wps_chain143 (cover_step hgt (by norm_num)) hle
  exact absurd h2 (Nat.not_le.2 hgt)

theorem wps_block06 {M : ℕ} (h1 : 5852393927021129095259733058360306032275619843 ≤ M) (h2 : M ≤ 93940895070792280282662056127353501270580011816976386) :
    WindowPairSupply M := by
  rcases le_or_gt M 11702566490750998304229977207283297481666854914 with hle | hgt
  · exact wps_chain144 (le_trans (by norm_num) h1) hle
  rcases le_or_gt M 23390138779285992376005904275864721528864112642 with hle | hgt
  · exact wps_chain145 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 46681296223682022171759582145919690320379904002 with hle | hgt
  · exact wps_chain146 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 92621702455514423445789628026570340349320888322 with hle | hgt
  · exact wps_chain147 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 183274231687541406516132322804885929871131279362 with hle | hgt
  · exact wps_chain148 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 366442360610817929051849057700177774959784886274 with hle | hgt
  · exact wps_chain149 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 732277374364119625664077853573023892199180337154 with hle | hgt
  · exact wps_chain150 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1462599949031930551393405466841210951460102078466 with hle | hgt
  · exact wps_chain151 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 2921762795710137570495121741103649974203094925314 with hle | hgt
  · exact wps_chain152 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 5843467051964128998104496950946834246457236652034 with hle | hgt
  · exact wps_chain153 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 11684383456196176056187180754116234336567226793986 with hle | hgt
  · exact wps_chain154 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 23339764793261663036978794306618889478995926056962 with hle | hgt
  · exact wps_chain155 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 46646111919843327935179997339406215388275140460546 with hle | hgt
  · exact wps_chain156 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 93286737856367817337067176892117359279619809738754 with hle | hgt
  · exact wps_chain157 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 185483772099354634304946352446560029022611392430082 with hle | hgt
  · exact wps_chain158 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 370618314528900279051496255544970384704039131545602 with hle | hgt
  · exact wps_chain159 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 739378352561897398337854622757717526740507926986754 with hle | hgt
  · exact wps_chain160 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1477574944034234261894192984732730871508090939768834 with hle | hgt
  · exact wps_chain161 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 2954625374541399083532097049371689053553561220153346 with hle | hgt
  · exact wps_chain162 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 5899693898532439059700627815891944287673903568912386 with hle | hgt
  · exact wps_chain163 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 11789633986332925589574103305468670725585767447396354 with hle | hgt
  · exact wps_chain164 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 23576561911040480679213720100739265208392953207193602 with hle | hgt
  · exact wps_chain165 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 47076223716397964240036019753444591618837604026286082 with hle | hgt
  · exact wps_chain166 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 93940895070792280282662056127353501270580011816976386 with hle | hgt
  · exact wps_chain167 (cover_step hgt (by norm_num)) hle
  exact absurd h2 (Nat.not_le.2 hgt)

theorem wps_block07 {M : ℕ} (h1 : 93940895070792280282662056127353501270580011816976387 ≤ M) (h2 : M ≤ 1516965997302524373612172717550681525506538629288954643349506) :
    WindowPairSupply M := by
  rcases le_or_gt M 187672978095150907810885760784232663604726682271875074 with hle | hgt
  · exact wps_chain168 (le_trans (by norm_num) h1) hle
  rcases le_or_gt M 375074938980429266311877125762298501476995917552812034 with hle | hgt
  · exact wps_chain169 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 750149877960858532623754251524597002953991835105624066 with hle | hgt
  · exact wps_chain170 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1497490384399357737112991469879505130873450053880512514 with hle | hgt
  · exact wps_chain171 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 2989344487734348847121930429201639916281597003909038082 with hle | hgt
  · exact wps_chain172 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 5966478129288798000362269071625935287933968691421511682 with hle | hgt
  · exact wps_chain173 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 11912366623510878240412884631328563580687024605177577474 with hle | hgt
  · exact wps_chain174 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 23782378929571906914256226476205009279464420285259710466 with hle | hgt
  · exact wps_chain175 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 47478435726436501378551670511450464018655882570801086466 with hle | hgt
  · exact wps_chain176 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 94829755886464510144889657330890596605394170752744292354 with hle | hgt
  · exact wps_chain177 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 189574768061990025214970192200440972256176611912916664322 with hle | hgt
  · exact wps_chain178 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 379006987100281343482910469797038129131748062789321621506 with hle | hgt
  · exact wps_chain179 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 754320046350228477810896144623603845526711991947461918722 with hle | hgt
  · exact wps_chain180 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1501101830943287539430824521692758367461736885302698442754 with hle | hgt
  · exact wps_chain181 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 2999161867758831017236050078216880989400324271322351796226 with hle | hgt
  · exact wps_chain182 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 5997165384395952856760801952723787038070061722253521846274 with hle | hgt
  · exact wps_chain183 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 11977718756581347738592133542164987716825506252850561286146 with hle | hgt
  · exact wps_chain184 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 23946440088170814887519764757838542173092500924057989939202 with hle | hgt
  · exact wps_chain185 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 47892880176341629775039529515677084346185001848115979878402 with hle | hgt
  · exact wps_chain186 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 95586128863242651496764472481895541697622668882768761454594 with hle | hgt
  · exact wps_chain187 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 190663517097403479951580797449121779193445904462570135224322 with hle | hgt
  · exact wps_chain188 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 381081068660497984741395080200385933762921001296029802299394 with hle | hgt
  · exact wps_chain189 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 762125357428015188150189560072120260105435152853127198146562 with hle | hgt
  · exact wps_chain190 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1516965997302524373612172717550681525506538629288954643349506 with hle | hgt
  · exact wps_chain191 (cover_step hgt (by norm_num)) hle
  exact absurd h2 (Nat.not_le.2 hgt)

/-- Every `M` with `8 <= M <= 10 ^ 60` admits a window pair supply. -/
theorem windowPairSupply_of_le {M : ℕ} (h1 : 8 ≤ M) (h2 : M ≤ 10 ^ 60) :
    WindowPairSupply M := by
  rcases le_or_gt M 4794531842 with hle | hgt
  · exact wps_block00 h1 hle
  rcases le_or_gt M 80243664265150466 with hle | hgt
  · exact wps_block01 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1335446272608679955005442 with hle | hgt
  · exact wps_block02 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 22107558763446825298618056966146 with hle | hgt
  · exact wps_block03 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 359723948952061150238226701468471132162 with hle | hgt
  · exact wps_block04 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 5852393927021129095259733058360306032275619842 with hle | hgt
  · exact wps_block05 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 93940895070792280282662056127353501270580011816976386 with hle | hgt
  · exact wps_block06 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1516965997302524373612172717550681525506538629288954643349506 with hle | hgt
  · exact wps_block07 (cover_step hgt (by norm_num)) hle
  omega

/-- Every `M` with `8 <= M <= 1516965997302524373612172717550681525506538629288954643349506`
(the top of the certified prime-pair chain) admits a window pair supply. -/
theorem windowPairSupply_of_le_chainCeiling {M : ℕ} (h1 : 8 ≤ M)
    (h2 : M ≤ 1516965997302524373612172717550681525506538629288954643349506) :
    WindowPairSupply M := by
  rcases le_or_gt M 4794531842 with hle | hgt
  · exact wps_block00 h1 hle
  rcases le_or_gt M 80243664265150466 with hle | hgt
  · exact wps_block01 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1335446272608679955005442 with hle | hgt
  · exact wps_block02 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 22107558763446825298618056966146 with hle | hgt
  · exact wps_block03 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 359723948952061150238226701468471132162 with hle | hgt
  · exact wps_block04 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 5852393927021129095259733058360306032275619842 with hle | hgt
  · exact wps_block05 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 93940895070792280282662056127353501270580011816976386 with hle | hgt
  · exact wps_block06 (cover_step hgt (by norm_num)) hle
  rcases le_or_gt M 1516965997302524373612172717550681525506538629288954643349506 with hle | hgt
  · exact wps_block07 (cover_step hgt (by norm_num)) hle
  omega

end Erdos287
