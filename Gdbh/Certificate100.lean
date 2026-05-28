import Gdbh.CircleMethod

set_option maxRecDepth 200000

namespace Gdbh

def certificate100Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 4, p := 2, q := 2 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6, p := 3, q := 3 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8, p := 3, q := 5 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 10, p := 3, q := 7 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 12, p := 5, q := 7 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 14, p := 3, q := 11 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 16, p := 3, q := 13 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 18, p := 5, q := 13 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 20, p := 3, q := 17 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 22, p := 3, q := 19 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 24, p := 5, q := 19 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 26, p := 3, q := 23 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 28, p := 5, q := 23 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 30, p := 7, q := 23 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 32, p := 3, q := 29 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 34, p := 3, q := 31 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 36, p := 5, q := 31 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 38, p := 7, q := 31 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 40, p := 3, q := 37 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 42, p := 5, q := 37 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 44, p := 3, q := 41 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 46, p := 3, q := 43 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 48, p := 5, q := 43 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 50, p := 3, q := 47 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 52, p := 5, q := 47 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 54, p := 7, q := 47 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 56, p := 3, q := 53 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 58, p := 5, q := 53 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 60, p := 7, q := 53 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 62, p := 3, q := 59 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 64, p := 3, q := 61 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 66, p := 5, q := 61 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 68, p := 7, q := 61 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 70, p := 3, q := 67 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 72, p := 5, q := 67 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 74, p := 3, q := 71 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 76, p := 3, q := 73 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 78, p := 5, q := 73 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 80, p := 7, q := 73 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 82, p := 3, q := 79 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 84, p := 5, q := 79 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 86, p := 3, q := 83 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 88, p := 5, q := 83 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 90, p := 7, q := 83 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 92, p := 3, q := 89 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 94, p := 5, q := 89 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 96, p := 7, q := 89 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 98, p := 19, q := 79 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 100, p := 3, q := 97 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate100 : List CertificateEntry :=
  verifiedCertificateEntries certificate100Verified

theorem certificate100_covers : CertificateCovers 100 certificate100 :=
  certificateCovers_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachUpTo100 : GoldbachUpTo 100 :=
  goldbachUpTo_of_certificate certificate100_covers

theorem strongGoldbach_from_certificate100_and_analytic_bridge
    (analytic_goldbach_above_100 : GoldbachAbove 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_above goldbachUpTo100 analytic_goldbach_above_100

theorem strongGoldbach_iff_goldbachAbove100 :
    StrongGoldbach ↔ GoldbachAbove 100 := by
  constructor
  · intro strong
    exact goldbachAbove_of_strongGoldbach (by decide) strong
  · intro above
    exact strongGoldbach_from_certificate100_and_analytic_bridge above

theorem strongGoldbach_from_certificate100_and_count_positive_bridge
    (count_positive_above_100 : GoldbachCountPositiveAbove 100) :
    StrongGoldbach :=
  strongGoldbach_from_certificate100_and_analytic_bridge
    (goldbachAbove_of_count_positive_above count_positive_above_100)

theorem strongGoldbach_iff_count_positive_above100 :
    StrongGoldbach ↔ GoldbachCountPositiveAbove 100 := by
  constructor
  · intro strong
    exact goldbachCountPositiveAbove_iff_goldbachAbove.mpr
      (strongGoldbach_iff_goldbachAbove100.mp strong)
  · intro count_positive
    exact strongGoldbach_iff_goldbachAbove100.mpr
      (goldbachCountPositiveAbove_iff_goldbachAbove.mp count_positive)

theorem strongGoldbach_from_certificate100_and_circle_method
    (bound : CircleMethodLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach := by
  exact strongGoldbach_from_certificate100_and_count_positive_bridge
    (goldbachCountPositiveAbove_mono hthreshold
      (count_positive_of_circle_method_lower_bound bound))

end Gdbh
