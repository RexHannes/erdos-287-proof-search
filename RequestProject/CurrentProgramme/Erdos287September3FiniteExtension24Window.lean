import RequestProject.CurrentProgramme.Erdos287September3PrattCertificateBank
import RequestProject.Erdos287.FiniteRangeExtension

/-!
# Erdős Problem #287 — the 24-window finite extension (kernel replay)

The unconditional finite bank of `RequestProject/Erdos287/FiniteRangeExtension.lean` stops
at `M ≤ 4·10^9`.  This module replays, **in the Lean kernel**, a chain of 24 further window
certificates which extends the excluded range to

    M ≤ 67108856338751594.

Each window is an instance of the already-proved interval blocker
`Erdos287.Gap2CE.blocker_window`; the only new ingredient is that the two prime-power
witnesses of each window are now primes of size up to `3.4·10^16`, certified in
`Erdos287September3PrattCertificateBank.lean` by recursive Pratt certificates rather than
by trial division.  The windows are contiguous (`L_{i+1} = U_i + 1`), so there is no gap.

Main results:

* `Erdos287.Gap2CE.no_of_M_le_extendedCeiling` — no gap-`≤2` counterexample has
  `3 ≤ M ≤ 67108856338751594`;
* `Erdos287.no_Erdos287Counterexample_of_max_le_extendedCeiling` — no exact Erdős-#287
  counterexample has `max A ≤ 67108856338751594`;
* `Erdos287.arithmeticCoverage_exceeds_twoExp375` — `38643198608805673 < 67108856338751594`
  (the extension covers the recorded arithmetic-coverage endpoint `⌈2·exp(37.5)⌉`).

**FIREWALL — FINITE-CERTIFICATE-COVERAGE.**  This is a *finite arithmetic* result only.
It excludes maxima below an explicit ceiling.  It does **not** assert that the medium
analytic branch is closed, it does not supply any analytic input, and it does not bear on
Erdős #287 itself, which remains open.
-/

set_option maxRecDepth 100000

namespace Erdos287

/-- The ceiling reached by the September-3 finite extension. -/
def extendedCeiling : ℕ := 67108856338751594

namespace Gap2CE

/-- Window certificate at `x = 3999999722` (`1999999861^1 ∣ x`, `1333333241^1 ∣ x+1`):
no gap-`≤2` counterexample has `4000000001 ≤ M ≤ 7999999444`. -/
theorem windowStepExt_0 (ce : Gap2CE) (h1 : 4000000001 ≤ ce.M) (h2 : ce.M ≤ 7999999444) : False :=
  ce.blocker_window (x := 3999999722) (pu := 1999999861) (au := 1) (pv := 1333333241) (av := 1)
    Certificates.prime_1999999861 Certificates.prime_1333333241 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 7999999233` (`2666666411^1 ∣ x`, `3999999617^1 ∣ x+1`):
no gap-`≤2` counterexample has `7999999445 ≤ M ≤ 15999998466`. -/
theorem windowStepExt_1 (ce : Gap2CE) (h1 : 7999999445 ≤ ce.M) (h2 : ce.M ≤ 15999998466) : False :=
  ce.blocker_window (x := 7999999233) (pu := 2666666411) (au := 1) (pv := 3999999617) (av := 1)
    Certificates.prime_2666666411 Certificates.prime_3999999617 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 15999998396` (`3999999599^1 ∣ x`, `5333332799^1 ∣ x+1`):
no gap-`≤2` counterexample has `15999998467 ≤ M ≤ 31999996792`. -/
theorem windowStepExt_2 (ce : Gap2CE) (h1 : 15999998467 ≤ ce.M) (h2 : ce.M ≤ 31999996792) : False :=
  ce.blocker_window (x := 15999998396) (pu := 3999999599) (au := 1) (pv := 5333332799) (av := 1)
    Certificates.prime_3999999599 Certificates.prime_5333332799 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 31999996382` (`15999998191^1 ∣ x`, `10666665461^1 ∣ x+1`):
no gap-`≤2` counterexample has `31999996793 ≤ M ≤ 63999992764`. -/
theorem windowStepExt_3 (ce : Gap2CE) (h1 : 31999996793 ≤ ce.M) (h2 : ce.M ≤ 63999992764) : False :=
  ce.blocker_window (x := 31999996382) (pu := 15999998191) (au := 1) (pv := 10666665461) (av := 1)
    Certificates.prime_15999998191 Certificates.prime_10666665461 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 63999992764` (`15999998191^1 ∣ x`, `12799998553^1 ∣ x+1`):
no gap-`≤2` counterexample has `63999992765 ≤ M ≤ 127999985528`. -/
theorem windowStepExt_4 (ce : Gap2CE) (h1 : 63999992765 ≤ ce.M) (h2 : ce.M ≤ 127999985528) : False :=
  ce.blocker_window (x := 63999992764) (pu := 15999998191) (au := 1) (pv := 12799998553) (av := 1)
    Certificates.prime_15999998191 Certificates.prime_12799998553 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 127999985482` (`63999992741^1 ∣ x`, `127999985483^1 ∣ x+1`):
no gap-`≤2` counterexample has `127999985529 ≤ M ≤ 255999970964`. -/
theorem windowStepExt_5 (ce : Gap2CE) (h1 : 127999985529 ≤ ce.M) (h2 : ce.M ≤ 255999970964) : False :=
  ce.blocker_window (x := 127999985482) (pu := 63999992741) (au := 1) (pv := 127999985483) (av := 1)
    Certificates.prime_63999992741 Certificates.prime_127999985483 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 255999970893` (`85333323631^1 ∣ x`, `127999985447^1 ∣ x+1`):
no gap-`≤2` counterexample has `255999970965 ≤ M ≤ 511999941786`. -/
theorem windowStepExt_6 (ce : Gap2CE) (h1 : 255999970965 ≤ ce.M) (h2 : ce.M ≤ 511999941786) : False :=
  ce.blocker_window (x := 255999970893) (pu := 85333323631) (au := 1) (pv := 127999985447) (av := 1)
    Certificates.prime_85333323631 Certificates.prime_127999985447 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 511999941722` (`255999970861^1 ∣ x`, `170666647241^1 ∣ x+1`):
no gap-`≤2` counterexample has `511999941787 ≤ M ≤ 1023999883444`. -/
theorem windowStepExt_7 (ce : Gap2CE) (h1 : 511999941787 ≤ ce.M) (h2 : ce.M ≤ 1023999883444) : False :=
  ce.blocker_window (x := 511999941722) (pu := 255999970861) (au := 1) (pv := 170666647241) (av := 1)
    Certificates.prime_255999970861 Certificates.prime_170666647241 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 1023999883441` (`1023999883441^1 ∣ x`, `511999941721^1 ∣ x+1`):
no gap-`≤2` counterexample has `1023999883445 ≤ M ≤ 2047999766882`. -/
theorem windowStepExt_8 (ce : Gap2CE) (h1 : 1023999883445 ≤ ce.M) (h2 : ce.M ≤ 2047999766882) : False :=
  ce.blocker_window (x := 1023999883441) (pu := 1023999883441) (au := 1) (pv := 511999941721) (av := 1)
    Certificates.prime_1023999883441 Certificates.prime_511999941721 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 2047999766366` (`1023999883183^1 ∣ x`, `682666588789^1 ∣ x+1`):
no gap-`≤2` counterexample has `2047999766883 ≤ M ≤ 4095999532732`. -/
theorem windowStepExt_9 (ce : Gap2CE) (h1 : 2047999766883 ≤ ce.M) (h2 : ce.M ≤ 4095999532732) : False :=
  ce.blocker_window (x := 2047999766366) (pu := 1023999883183) (au := 1) (pv := 682666588789) (av := 1)
    Certificates.prime_1023999883183 Certificates.prime_682666588789 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 4095999532732` (`1023999883183^1 ∣ x`, `4095999532733^1 ∣ x+1`):
no gap-`≤2` counterexample has `4095999532733 ≤ M ≤ 8191999065464`. -/
theorem windowStepExt_10 (ce : Gap2CE) (h1 : 4095999532733 ≤ ce.M) (h2 : ce.M ≤ 8191999065464) : False :=
  ce.blocker_window (x := 4095999532732) (pu := 1023999883183) (au := 1) (pv := 4095999532733) (av := 1)
    Certificates.prime_1023999883183 Certificates.prime_4095999532733 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 8191999065043` (`8191999065043^1 ∣ x`, `2047999766261^1 ∣ x+1`):
no gap-`≤2` counterexample has `8191999065465 ≤ M ≤ 16383998130086`. -/
theorem windowStepExt_11 (ce : Gap2CE) (h1 : 8191999065465 ≤ ce.M) (h2 : ce.M ≤ 16383998130086) : False :=
  ce.blocker_window (x := 8191999065043) (pu := 8191999065043) (au := 1) (pv := 2047999766261) (av := 1)
    Certificates.prime_8191999065043 Certificates.prime_2047999766261 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 16383998129937` (`5461332709979^1 ∣ x`, `8191999064969^1 ∣ x+1`):
no gap-`≤2` counterexample has `16383998130087 ≤ M ≤ 32767996259874`. -/
theorem windowStepExt_12 (ce : Gap2CE) (h1 : 16383998130087 ≤ ce.M) (h2 : ce.M ≤ 32767996259874) : False :=
  ce.blocker_window (x := 16383998129937) (pu := 5461332709979) (au := 1) (pv := 8191999064969) (av := 1)
    Certificates.prime_5461332709979 Certificates.prime_8191999064969 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 32767996259553` (`10922665419851^1 ∣ x`, `16383998129777^1 ∣ x+1`):
no gap-`≤2` counterexample has `32767996259875 ≤ M ≤ 65535992519106`. -/
theorem windowStepExt_13 (ce : Gap2CE) (h1 : 32767996259875 ≤ ce.M) (h2 : ce.M ≤ 65535992519106) : False :=
  ce.blocker_window (x := 32767996259553) (pu := 10922665419851) (au := 1) (pv := 16383998129777) (av := 1)
    Certificates.prime_10922665419851 Certificates.prime_16383998129777 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 65535992518466` (`32767996259233^1 ∣ x`, `21845330839489^1 ∣ x+1`):
no gap-`≤2` counterexample has `65535992519107 ≤ M ≤ 131071985036932`. -/
theorem windowStepExt_14 (ce : Gap2CE) (h1 : 65535992519107 ≤ ce.M) (h2 : ce.M ≤ 131071985036932) : False :=
  ce.blocker_window (x := 65535992518466) (pu := 32767996259233) (au := 1) (pv := 21845330839489) (av := 1)
    Certificates.prime_32767996259233 Certificates.prime_21845330839489 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 131071985036913` (`43690661678971^1 ∣ x`, `65535992518457^1 ∣ x+1`):
no gap-`≤2` counterexample has `131071985036933 ≤ M ≤ 262143970073826`. -/
theorem windowStepExt_15 (ce : Gap2CE) (h1 : 131071985036933 ≤ ce.M) (h2 : ce.M ≤ 262143970073826) : False :=
  ce.blocker_window (x := 131071985036913) (pu := 43690661678971) (au := 1) (pv := 65535992518457) (av := 1)
    Certificates.prime_43690661678971 Certificates.prime_65535992518457 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 262143970073653` (`262143970073653^1 ∣ x`, `131071985036827^1 ∣ x+1`):
no gap-`≤2` counterexample has `262143970073827 ≤ M ≤ 524287940147306`. -/
theorem windowStepExt_16 (ce : Gap2CE) (h1 : 262143970073827 ≤ ce.M) (h2 : ce.M ≤ 524287940147306) : False :=
  ce.blocker_window (x := 262143970073653) (pu := 262143970073653) (au := 1) (pv := 131071985036827) (av := 1)
    Certificates.prime_262143970073653 Certificates.prime_131071985036827 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 524287940146868` (`131071985036717^1 ∣ x`, `174762646715623^1 ∣ x+1`):
no gap-`≤2` counterexample has `524287940147307 ≤ M ≤ 1048575880293736`. -/
theorem windowStepExt_17 (ce : Gap2CE) (h1 : 524287940147307 ≤ ce.M) (h2 : ce.M ≤ 1048575880293736) : False :=
  ce.blocker_window (x := 524287940146868) (pu := 131071985036717) (au := 1) (pv := 174762646715623) (av := 1)
    Certificates.prime_131071985036717 Certificates.prime_174762646715623 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 1048575880293313` (`1048575880293313^1 ∣ x`, `524287940146657^1 ∣ x+1`):
no gap-`≤2` counterexample has `1048575880293737 ≤ M ≤ 2097151760586626`. -/
theorem windowStepExt_18 (ce : Gap2CE) (h1 : 1048575880293737 ≤ ce.M) (h2 : ce.M ≤ 2097151760586626) : False :=
  ce.blocker_window (x := 1048575880293313) (pu := 1048575880293313) (au := 1) (pv := 524287940146657) (av := 1)
    Certificates.prime_1048575880293313 Certificates.prime_524287940146657 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 2097151760586097` (`2097151760586097^1 ∣ x`, `1048575880293049^1 ∣ x+1`):
no gap-`≤2` counterexample has `2097151760586627 ≤ M ≤ 4194303521172194`. -/
theorem windowStepExt_19 (ce : Gap2CE) (h1 : 2097151760586627 ≤ ce.M) (h2 : ce.M ≤ 4194303521172194) : False :=
  ce.blocker_window (x := 2097151760586097) (pu := 2097151760586097) (au := 1) (pv := 1048575880293049) (av := 1)
    Certificates.prime_2097151760586097 Certificates.prime_1048575880293049 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 4194303521172052` (`1048575880293013^1 ∣ x`, `4194303521172053^1 ∣ x+1`):
no gap-`≤2` counterexample has `4194303521172195 ≤ M ≤ 8388607042344104`. -/
theorem windowStepExt_20 (ce : Gap2CE) (h1 : 4194303521172195 ≤ ce.M) (h2 : ce.M ≤ 8388607042344104) : False :=
  ce.blocker_window (x := 4194303521172052) (pu := 1048575880293013) (au := 1) (pv := 4194303521172053) (av := 1)
    Certificates.prime_1048575880293013 Certificates.prime_4194303521172053 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 8388607042343977` (`8388607042343977^1 ∣ x`, `4194303521171989^1 ∣ x+1`):
no gap-`≤2` counterexample has `8388607042344105 ≤ M ≤ 16777214084687954`. -/
theorem windowStepExt_21 (ce : Gap2CE) (h1 : 8388607042344105 ≤ ce.M) (h2 : ce.M ≤ 16777214084687954) : False :=
  ce.blocker_window (x := 8388607042343977) (pu := 8388607042343977) (au := 1) (pv := 4194303521171989) (av := 1)
    Certificates.prime_8388607042343977 Certificates.prime_4194303521171989 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 16777214084687942` (`8388607042343971^1 ∣ x`, `5592404694895981^1 ∣ x+1`):
no gap-`≤2` counterexample has `16777214084687955 ≤ M ≤ 33554428169375884`. -/
theorem windowStepExt_22 (ce : Gap2CE) (h1 : 16777214084687955 ≤ ce.M) (h2 : ce.M ≤ 33554428169375884) : False :=
  ce.blocker_window (x := 16777214084687942) (pu := 8388607042343971) (au := 1) (pv := 5592404694895981) (av := 1)
    Certificates.prime_8388607042343971 Certificates.prime_5592404694895981 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- Window certificate at `x = 33554428169375797` (`33554428169375797^1 ∣ x`, `16777214084687899^1 ∣ x+1`):
no gap-`≤2` counterexample has `33554428169375885 ≤ M ≤ 67108856338751594`. -/
theorem windowStepExt_23 (ce : Gap2CE) (h1 : 33554428169375885 ≤ ce.M) (h2 : ce.M ≤ 67108856338751594) : False :=
  ce.blocker_window (x := 33554428169375797) (pu := 33554428169375797) (au := 1) (pv := 16777214084687899) (av := 1)
    Certificates.prime_33554428169375797 Certificates.prime_16777214084687899 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

/-- **No gap-`≤2` counterexample has `3 ≤ M ≤ 67108856338751594`.**
The 34 windows of the original bank cover `[3, 4·10^9]`; the 24 windows above are
contiguous and cover `[4000000001, 67108856338751594]`. -/
theorem no_of_M_le_extendedCeiling (ce : Gap2CE) (h3 : 3 ≤ ce.M)
    (hM : ce.M ≤ 67108856338751594) : False := by
  by_cases c : ce.M ≤ 4000000000
  · exact ce.no_of_M_le_4e9 h3 c
  by_cases c0 : ce.M ≤ 7999999444
  · exact windowStepExt_0 ce (by omega) c0
  by_cases c1 : ce.M ≤ 15999998466
  · exact windowStepExt_1 ce (by omega) c1
  by_cases c2 : ce.M ≤ 31999996792
  · exact windowStepExt_2 ce (by omega) c2
  by_cases c3 : ce.M ≤ 63999992764
  · exact windowStepExt_3 ce (by omega) c3
  by_cases c4 : ce.M ≤ 127999985528
  · exact windowStepExt_4 ce (by omega) c4
  by_cases c5 : ce.M ≤ 255999970964
  · exact windowStepExt_5 ce (by omega) c5
  by_cases c6 : ce.M ≤ 511999941786
  · exact windowStepExt_6 ce (by omega) c6
  by_cases c7 : ce.M ≤ 1023999883444
  · exact windowStepExt_7 ce (by omega) c7
  by_cases c8 : ce.M ≤ 2047999766882
  · exact windowStepExt_8 ce (by omega) c8
  by_cases c9 : ce.M ≤ 4095999532732
  · exact windowStepExt_9 ce (by omega) c9
  by_cases c10 : ce.M ≤ 8191999065464
  · exact windowStepExt_10 ce (by omega) c10
  by_cases c11 : ce.M ≤ 16383998130086
  · exact windowStepExt_11 ce (by omega) c11
  by_cases c12 : ce.M ≤ 32767996259874
  · exact windowStepExt_12 ce (by omega) c12
  by_cases c13 : ce.M ≤ 65535992519106
  · exact windowStepExt_13 ce (by omega) c13
  by_cases c14 : ce.M ≤ 131071985036932
  · exact windowStepExt_14 ce (by omega) c14
  by_cases c15 : ce.M ≤ 262143970073826
  · exact windowStepExt_15 ce (by omega) c15
  by_cases c16 : ce.M ≤ 524287940147306
  · exact windowStepExt_16 ce (by omega) c16
  by_cases c17 : ce.M ≤ 1048575880293736
  · exact windowStepExt_17 ce (by omega) c17
  by_cases c18 : ce.M ≤ 2097151760586626
  · exact windowStepExt_18 ce (by omega) c18
  by_cases c19 : ce.M ≤ 4194303521172194
  · exact windowStepExt_19 ce (by omega) c19
  by_cases c20 : ce.M ≤ 8388607042344104
  · exact windowStepExt_20 ce (by omega) c20
  by_cases c21 : ce.M ≤ 16777214084687954
  · exact windowStepExt_21 ce (by omega) c21
  by_cases c22 : ce.M ≤ 33554428169375884
  · exact windowStepExt_22 ce (by omega) c22
  exact windowStepExt_23 ce (by omega) hM

end Gap2CE

/-- **No exact Erdős-#287 counterexample has maximum `≤ 67108856338751594`.** -/
theorem no_Erdos287Counterexample_of_max_le_extendedCeiling {A : Finset ℕ}
    (h : Erdos287Counterexample A) (hM : A.max' h.nonempty ≤ 67108856338751594) : False := by
  refine (h.toGap2CE).no_of_M_le_extendedCeiling ?_ hM
  show 3 ≤ A.max' h.nonempty
  have := h.four_le_max
  omega

/-- The same statement, phrased with the named ceiling. -/
theorem no_Erdos287Counterexample_of_max_le_extendedCeiling' {A : Finset ℕ}
    (h : Erdos287Counterexample A) (hM : A.max' h.nonempty ≤ extendedCeiling) : False :=
  no_Erdos287Counterexample_of_max_le_extendedCeiling h hM

/-- **`arithmeticCoverage_exceeds_twoExp375`.**  The recorded arithmetic-coverage endpoint
`⌈2·exp(37.5)⌉ = 38643198608805673` lies strictly below the new ceiling. -/
theorem arithmeticCoverage_exceeds_twoExp375 :
    38643198608805673 < extendedCeiling := by
  norm_num [extendedCeiling]

end Erdos287
