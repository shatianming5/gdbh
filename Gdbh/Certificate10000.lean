import Gdbh.FiniteIntervals
import Gdbh.GeneralHandoff
import Gdbh.ContaminatedWeightedGoldbach
import Gdbh.RealContaminatedWeightedGoldbach
import Gdbh.VonMangoldtGoldbach

set_option maxRecDepth 200000

namespace Gdbh

def certificate2To102Verified : List VerifiedCertificateEntry :=
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
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 102, p := 5, q := 97 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate2To102 : List CertificateEntry :=
  verifiedCertificateEntries certificate2To102Verified

theorem certificate2To102_covers :
    CertificateCoversBetween 2 102 certificate2To102 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween2To102 :
    GoldbachBetween 2 102 :=
  goldbachBetween_of_certificate certificate2To102_covers

def certificate102To202Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 104, p := 3, q := 101 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 106, p := 3, q := 103 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 108, p := 5, q := 103 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 110, p := 3, q := 107 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 112, p := 3, q := 109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 114, p := 5, q := 109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 116, p := 3, q := 113 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 118, p := 5, q := 113 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 120, p := 7, q := 113 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 122, p := 13, q := 109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 124, p := 11, q := 113 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 126, p := 13, q := 113 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 128, p := 19, q := 109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 130, p := 3, q := 127 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 132, p := 5, q := 127 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 134, p := 3, q := 131 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 136, p := 5, q := 131 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 138, p := 7, q := 131 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 140, p := 3, q := 137 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 142, p := 3, q := 139 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 144, p := 5, q := 139 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 146, p := 7, q := 139 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 148, p := 11, q := 137 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 150, p := 11, q := 139 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 152, p := 3, q := 149 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 154, p := 3, q := 151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 156, p := 5, q := 151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 158, p := 7, q := 151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 160, p := 3, q := 157 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 162, p := 5, q := 157 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 164, p := 7, q := 157 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 166, p := 3, q := 163 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 168, p := 5, q := 163 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 170, p := 3, q := 167 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 172, p := 5, q := 167 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 174, p := 7, q := 167 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 176, p := 3, q := 173 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 178, p := 5, q := 173 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 180, p := 7, q := 173 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 182, p := 3, q := 179 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 184, p := 3, q := 181 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 186, p := 5, q := 181 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 188, p := 7, q := 181 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 190, p := 11, q := 179 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 192, p := 11, q := 181 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 194, p := 3, q := 191 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 196, p := 3, q := 193 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 198, p := 5, q := 193 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 200, p := 3, q := 197 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 202, p := 3, q := 199 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate102To202 : List CertificateEntry :=
  verifiedCertificateEntries certificate102To202Verified

theorem certificate102To202_covers :
    CertificateCoversBetween 102 202 certificate102To202 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween102To202 :
    GoldbachBetween 102 202 :=
  goldbachBetween_of_certificate certificate102To202_covers

def certificate202To302Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 204, p := 5, q := 199 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 206, p := 7, q := 199 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 208, p := 11, q := 197 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 210, p := 11, q := 199 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 212, p := 13, q := 199 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 214, p := 3, q := 211 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 216, p := 5, q := 211 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 218, p := 7, q := 211 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 220, p := 23, q := 197 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 222, p := 11, q := 211 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 224, p := 13, q := 211 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 226, p := 3, q := 223 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 228, p := 5, q := 223 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 230, p := 3, q := 227 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 232, p := 3, q := 229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 234, p := 5, q := 229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 236, p := 3, q := 233 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 238, p := 5, q := 233 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 240, p := 7, q := 233 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 242, p := 3, q := 239 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 244, p := 3, q := 241 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 246, p := 5, q := 241 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 248, p := 7, q := 241 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 250, p := 11, q := 239 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 252, p := 11, q := 241 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 254, p := 3, q := 251 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 256, p := 5, q := 251 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 258, p := 7, q := 251 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 260, p := 3, q := 257 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 262, p := 5, q := 257 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 264, p := 7, q := 257 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 266, p := 3, q := 263 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 268, p := 5, q := 263 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 270, p := 7, q := 263 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 272, p := 3, q := 269 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 274, p := 3, q := 271 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 276, p := 5, q := 271 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 278, p := 7, q := 271 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 280, p := 3, q := 277 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 282, p := 5, q := 277 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 284, p := 3, q := 281 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 286, p := 3, q := 283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 288, p := 5, q := 283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 290, p := 7, q := 283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 292, p := 11, q := 281 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 294, p := 11, q := 283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 296, p := 3, q := 293 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 298, p := 5, q := 293 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 300, p := 7, q := 293 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 302, p := 19, q := 283 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate202To302 : List CertificateEntry :=
  verifiedCertificateEntries certificate202To302Verified

theorem certificate202To302_covers :
    CertificateCoversBetween 202 302 certificate202To302 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween202To302 :
    GoldbachBetween 202 302 :=
  goldbachBetween_of_certificate certificate202To302_covers

def certificate302To402Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 304, p := 11, q := 293 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 306, p := 13, q := 293 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 308, p := 31, q := 277 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 310, p := 3, q := 307 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 312, p := 5, q := 307 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 314, p := 3, q := 311 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 316, p := 3, q := 313 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 318, p := 5, q := 313 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 320, p := 3, q := 317 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 322, p := 5, q := 317 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 324, p := 7, q := 317 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 326, p := 13, q := 313 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 328, p := 11, q := 317 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 330, p := 13, q := 317 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 332, p := 19, q := 313 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 334, p := 3, q := 331 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 336, p := 5, q := 331 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 338, p := 7, q := 331 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 340, p := 3, q := 337 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 342, p := 5, q := 337 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 344, p := 7, q := 337 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 346, p := 29, q := 317 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 348, p := 11, q := 337 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 350, p := 3, q := 347 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 352, p := 3, q := 349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 354, p := 5, q := 349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 356, p := 3, q := 353 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 358, p := 5, q := 353 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 360, p := 7, q := 353 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 362, p := 3, q := 359 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 364, p := 5, q := 359 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 366, p := 7, q := 359 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 368, p := 19, q := 349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 370, p := 3, q := 367 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 372, p := 5, q := 367 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 374, p := 7, q := 367 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 376, p := 3, q := 373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 378, p := 5, q := 373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 380, p := 7, q := 373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 382, p := 3, q := 379 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 384, p := 5, q := 379 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 386, p := 3, q := 383 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 388, p := 5, q := 383 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 390, p := 7, q := 383 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 392, p := 3, q := 389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 394, p := 5, q := 389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 396, p := 7, q := 389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 398, p := 19, q := 379 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 400, p := 3, q := 397 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 402, p := 5, q := 397 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate302To402 : List CertificateEntry :=
  verifiedCertificateEntries certificate302To402Verified

theorem certificate302To402_covers :
    CertificateCoversBetween 302 402 certificate302To402 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween302To402 :
    GoldbachBetween 302 402 :=
  goldbachBetween_of_certificate certificate302To402_covers

def certificate402To502Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 404, p := 3, q := 401 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 406, p := 5, q := 401 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 408, p := 7, q := 401 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 410, p := 13, q := 397 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 412, p := 3, q := 409 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 414, p := 5, q := 409 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 416, p := 7, q := 409 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 418, p := 17, q := 401 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 420, p := 11, q := 409 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 422, p := 3, q := 419 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 424, p := 3, q := 421 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 426, p := 5, q := 421 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 428, p := 7, q := 421 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 430, p := 11, q := 419 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 432, p := 11, q := 421 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 434, p := 3, q := 431 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 436, p := 3, q := 433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 438, p := 5, q := 433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 440, p := 7, q := 433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 442, p := 3, q := 439 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 444, p := 5, q := 439 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 446, p := 3, q := 443 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 448, p := 5, q := 443 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 450, p := 7, q := 443 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 452, p := 3, q := 449 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 454, p := 5, q := 449 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 456, p := 7, q := 449 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 458, p := 19, q := 439 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 460, p := 3, q := 457 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 462, p := 5, q := 457 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 464, p := 3, q := 461 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 466, p := 3, q := 463 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 468, p := 5, q := 463 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 470, p := 3, q := 467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 472, p := 5, q := 467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 474, p := 7, q := 467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 476, p := 13, q := 463 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 478, p := 11, q := 467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 480, p := 13, q := 467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 482, p := 3, q := 479 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 484, p := 5, q := 479 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 486, p := 7, q := 479 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 488, p := 31, q := 457 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 490, p := 3, q := 487 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 492, p := 5, q := 487 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 494, p := 3, q := 491 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 496, p := 5, q := 491 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 498, p := 7, q := 491 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 500, p := 13, q := 487 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 502, p := 3, q := 499 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate402To502 : List CertificateEntry :=
  verifiedCertificateEntries certificate402To502Verified

theorem certificate402To502_covers :
    CertificateCoversBetween 402 502 certificate402To502 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween402To502 :
    GoldbachBetween 402 502 :=
  goldbachBetween_of_certificate certificate402To502_covers

def certificate502To602Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 504, p := 5, q := 499 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 506, p := 3, q := 503 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 508, p := 5, q := 503 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 510, p := 7, q := 503 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 512, p := 3, q := 509 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 514, p := 5, q := 509 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 516, p := 7, q := 509 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 518, p := 19, q := 499 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 520, p := 11, q := 509 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 522, p := 13, q := 509 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 524, p := 3, q := 521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 526, p := 3, q := 523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 528, p := 5, q := 523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 530, p := 7, q := 523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 532, p := 11, q := 521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 534, p := 11, q := 523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 536, p := 13, q := 523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 538, p := 17, q := 521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 540, p := 17, q := 523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 542, p := 19, q := 523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 544, p := 3, q := 541 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 546, p := 5, q := 541 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 548, p := 7, q := 541 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 550, p := 3, q := 547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 552, p := 5, q := 547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 554, p := 7, q := 547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 556, p := 47, q := 509 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 558, p := 11, q := 547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 560, p := 3, q := 557 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 562, p := 5, q := 557 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 564, p := 7, q := 557 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 566, p := 3, q := 563 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 568, p := 5, q := 563 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 570, p := 7, q := 563 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 572, p := 3, q := 569 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 574, p := 3, q := 571 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 576, p := 5, q := 571 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 578, p := 7, q := 571 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 580, p := 3, q := 577 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 582, p := 5, q := 577 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 584, p := 7, q := 577 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 586, p := 17, q := 569 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 588, p := 11, q := 577 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 590, p := 3, q := 587 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 592, p := 5, q := 587 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 594, p := 7, q := 587 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 596, p := 3, q := 593 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 598, p := 5, q := 593 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 600, p := 7, q := 593 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 602, p := 3, q := 599 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate502To602 : List CertificateEntry :=
  verifiedCertificateEntries certificate502To602Verified

theorem certificate502To602_covers :
    CertificateCoversBetween 502 602 certificate502To602 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween502To602 :
    GoldbachBetween 502 602 :=
  goldbachBetween_of_certificate certificate502To602_covers

def certificate602To702Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 604, p := 3, q := 601 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 606, p := 5, q := 601 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 608, p := 7, q := 601 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 610, p := 3, q := 607 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 612, p := 5, q := 607 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 614, p := 7, q := 607 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 616, p := 3, q := 613 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 618, p := 5, q := 613 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 620, p := 3, q := 617 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 622, p := 3, q := 619 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 624, p := 5, q := 619 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 626, p := 7, q := 619 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 628, p := 11, q := 617 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 630, p := 11, q := 619 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 632, p := 13, q := 619 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 634, p := 3, q := 631 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 636, p := 5, q := 631 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 638, p := 7, q := 631 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 640, p := 23, q := 617 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 642, p := 11, q := 631 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 644, p := 3, q := 641 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 646, p := 3, q := 643 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 648, p := 5, q := 643 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 650, p := 3, q := 647 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 652, p := 5, q := 647 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 654, p := 7, q := 647 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 656, p := 3, q := 653 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 658, p := 5, q := 653 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 660, p := 7, q := 653 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 662, p := 3, q := 659 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 664, p := 3, q := 661 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 666, p := 5, q := 661 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 668, p := 7, q := 661 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 670, p := 11, q := 659 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 672, p := 11, q := 661 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 674, p := 13, q := 661 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 676, p := 3, q := 673 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 678, p := 5, q := 673 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 680, p := 3, q := 677 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 682, p := 5, q := 677 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 684, p := 7, q := 677 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 686, p := 3, q := 683 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 688, p := 5, q := 683 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 690, p := 7, q := 683 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 692, p := 19, q := 673 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 694, p := 3, q := 691 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 696, p := 5, q := 691 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 698, p := 7, q := 691 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 700, p := 17, q := 683 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 702, p := 11, q := 691 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate602To702 : List CertificateEntry :=
  verifiedCertificateEntries certificate602To702Verified

theorem certificate602To702_covers :
    CertificateCoversBetween 602 702 certificate602To702 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween602To702 :
    GoldbachBetween 602 702 :=
  goldbachBetween_of_certificate certificate602To702_covers

def certificate702To802Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 704, p := 3, q := 701 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 706, p := 5, q := 701 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 708, p := 7, q := 701 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 710, p := 19, q := 691 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 712, p := 3, q := 709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 714, p := 5, q := 709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 716, p := 7, q := 709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 718, p := 17, q := 701 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 720, p := 11, q := 709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 722, p := 3, q := 719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 724, p := 5, q := 719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 726, p := 7, q := 719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 728, p := 19, q := 709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 730, p := 3, q := 727 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 732, p := 5, q := 727 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 734, p := 7, q := 727 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 736, p := 3, q := 733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 738, p := 5, q := 733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 740, p := 7, q := 733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 742, p := 3, q := 739 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 744, p := 5, q := 739 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 746, p := 3, q := 743 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 748, p := 5, q := 743 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 750, p := 7, q := 743 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 752, p := 13, q := 739 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 754, p := 3, q := 751 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 756, p := 5, q := 751 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 758, p := 7, q := 751 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 760, p := 3, q := 757 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 762, p := 5, q := 757 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 764, p := 3, q := 761 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 766, p := 5, q := 761 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 768, p := 7, q := 761 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 770, p := 13, q := 757 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 772, p := 3, q := 769 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 774, p := 5, q := 769 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 776, p := 3, q := 773 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 778, p := 5, q := 773 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 780, p := 7, q := 773 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 782, p := 13, q := 769 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 784, p := 11, q := 773 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 786, p := 13, q := 773 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 788, p := 19, q := 769 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 790, p := 3, q := 787 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 792, p := 5, q := 787 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 794, p := 7, q := 787 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 796, p := 23, q := 773 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 798, p := 11, q := 787 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 800, p := 3, q := 797 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 802, p := 5, q := 797 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate702To802 : List CertificateEntry :=
  verifiedCertificateEntries certificate702To802Verified

theorem certificate702To802_covers :
    CertificateCoversBetween 702 802 certificate702To802 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween702To802 :
    GoldbachBetween 702 802 :=
  goldbachBetween_of_certificate certificate702To802_covers

def certificate802To902Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 804, p := 7, q := 797 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 806, p := 19, q := 787 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 808, p := 11, q := 797 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 810, p := 13, q := 797 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 812, p := 3, q := 809 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 814, p := 3, q := 811 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 816, p := 5, q := 811 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 818, p := 7, q := 811 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 820, p := 11, q := 809 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 822, p := 11, q := 811 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 824, p := 3, q := 821 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 826, p := 3, q := 823 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 828, p := 5, q := 823 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 830, p := 3, q := 827 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 832, p := 3, q := 829 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 834, p := 5, q := 829 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 836, p := 7, q := 829 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 838, p := 11, q := 827 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 840, p := 11, q := 829 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 842, p := 3, q := 839 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 844, p := 5, q := 839 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 846, p := 7, q := 839 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 848, p := 19, q := 829 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 850, p := 11, q := 839 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 852, p := 13, q := 839 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 854, p := 31, q := 823 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 856, p := 3, q := 853 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 858, p := 5, q := 853 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 860, p := 3, q := 857 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 862, p := 3, q := 859 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 864, p := 5, q := 859 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 866, p := 3, q := 863 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 868, p := 5, q := 863 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 870, p := 7, q := 863 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 872, p := 13, q := 859 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 874, p := 11, q := 863 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 876, p := 13, q := 863 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 878, p := 19, q := 859 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 880, p := 3, q := 877 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 882, p := 5, q := 877 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 884, p := 3, q := 881 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 886, p := 3, q := 883 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 888, p := 5, q := 883 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 890, p := 3, q := 887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 892, p := 5, q := 887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 894, p := 7, q := 887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 896, p := 13, q := 883 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 898, p := 11, q := 887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 900, p := 13, q := 887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 902, p := 19, q := 883 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate802To902 : List CertificateEntry :=
  verifiedCertificateEntries certificate802To902Verified

theorem certificate802To902_covers :
    CertificateCoversBetween 802 902 certificate802To902 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween802To902 :
    GoldbachBetween 802 902 :=
  goldbachBetween_of_certificate certificate802To902_covers

def certificate902To1002Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 904, p := 17, q := 887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 906, p := 19, q := 887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 908, p := 31, q := 877 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 910, p := 3, q := 907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 912, p := 5, q := 907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 914, p := 3, q := 911 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 916, p := 5, q := 911 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 918, p := 7, q := 911 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 920, p := 13, q := 907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 922, p := 3, q := 919 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 924, p := 5, q := 919 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 926, p := 7, q := 919 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 928, p := 17, q := 911 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 930, p := 11, q := 919 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 932, p := 3, q := 929 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 934, p := 5, q := 929 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 936, p := 7, q := 929 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 938, p := 19, q := 919 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 940, p := 3, q := 937 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 942, p := 5, q := 937 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 944, p := 3, q := 941 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 946, p := 5, q := 941 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 948, p := 7, q := 941 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 950, p := 3, q := 947 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 952, p := 5, q := 947 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 954, p := 7, q := 947 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 956, p := 3, q := 953 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 958, p := 5, q := 953 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 960, p := 7, q := 953 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 962, p := 43, q := 919 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 964, p := 11, q := 953 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 966, p := 13, q := 953 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 968, p := 31, q := 937 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 970, p := 3, q := 967 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 972, p := 5, q := 967 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 974, p := 3, q := 971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 976, p := 5, q := 971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 978, p := 7, q := 971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 980, p := 3, q := 977 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 982, p := 5, q := 977 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 984, p := 7, q := 977 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 986, p := 3, q := 983 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 988, p := 5, q := 983 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 990, p := 7, q := 983 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 992, p := 73, q := 919 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 994, p := 3, q := 991 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 996, p := 5, q := 991 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 998, p := 7, q := 991 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1000, p := 3, q := 997 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1002, p := 5, q := 997 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate902To1002 : List CertificateEntry :=
  verifiedCertificateEntries certificate902To1002Verified

theorem certificate902To1002_covers :
    CertificateCoversBetween 902 1002 certificate902To1002 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween902To1002 :
    GoldbachBetween 902 1002 :=
  goldbachBetween_of_certificate certificate902To1002_covers

def certificate1002To1102Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 1004, p := 7, q := 997 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1006, p := 23, q := 983 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1008, p := 11, q := 997 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1010, p := 13, q := 997 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1012, p := 3, q := 1009 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1014, p := 5, q := 1009 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1016, p := 3, q := 1013 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1018, p := 5, q := 1013 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1020, p := 7, q := 1013 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1022, p := 3, q := 1019 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1024, p := 3, q := 1021 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1026, p := 5, q := 1021 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1028, p := 7, q := 1021 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1030, p := 11, q := 1019 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1032, p := 11, q := 1021 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1034, p := 3, q := 1031 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1036, p := 3, q := 1033 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1038, p := 5, q := 1033 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1040, p := 7, q := 1033 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1042, p := 3, q := 1039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1044, p := 5, q := 1039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1046, p := 7, q := 1039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1048, p := 17, q := 1031 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1050, p := 11, q := 1039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1052, p := 3, q := 1049 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1054, p := 3, q := 1051 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1056, p := 5, q := 1051 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1058, p := 7, q := 1051 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1060, p := 11, q := 1049 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1062, p := 11, q := 1051 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1064, p := 3, q := 1061 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1066, p := 3, q := 1063 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1068, p := 5, q := 1063 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1070, p := 7, q := 1063 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1072, p := 3, q := 1069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1074, p := 5, q := 1069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1076, p := 7, q := 1069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1078, p := 17, q := 1061 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1080, p := 11, q := 1069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1082, p := 13, q := 1069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1084, p := 23, q := 1061 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1086, p := 17, q := 1069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1088, p := 19, q := 1069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1090, p := 3, q := 1087 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1092, p := 5, q := 1087 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1094, p := 3, q := 1091 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1096, p := 3, q := 1093 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1098, p := 5, q := 1093 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1100, p := 3, q := 1097 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1102, p := 5, q := 1097 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate1002To1102 : List CertificateEntry :=
  verifiedCertificateEntries certificate1002To1102Verified

theorem certificate1002To1102_covers :
    CertificateCoversBetween 1002 1102 certificate1002To1102 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween1002To1102 :
    GoldbachBetween 1002 1102 :=
  goldbachBetween_of_certificate certificate1002To1102_covers

def certificate1102To1202Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 1104, p := 7, q := 1097 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1106, p := 3, q := 1103 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1108, p := 5, q := 1103 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1110, p := 7, q := 1103 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1112, p := 3, q := 1109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1114, p := 5, q := 1109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1116, p := 7, q := 1109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1118, p := 31, q := 1087 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1120, p := 3, q := 1117 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1122, p := 5, q := 1117 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1124, p := 7, q := 1117 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1126, p := 3, q := 1123 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1128, p := 5, q := 1123 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1130, p := 7, q := 1123 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1132, p := 3, q := 1129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1134, p := 5, q := 1129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1136, p := 7, q := 1129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1138, p := 29, q := 1109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1140, p := 11, q := 1129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1142, p := 13, q := 1129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1144, p := 41, q := 1103 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1146, p := 17, q := 1129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1148, p := 19, q := 1129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1150, p := 41, q := 1109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1152, p := 23, q := 1129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1154, p := 3, q := 1151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1156, p := 3, q := 1153 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1158, p := 5, q := 1153 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1160, p := 7, q := 1153 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1162, p := 11, q := 1151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1164, p := 11, q := 1153 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1166, p := 3, q := 1163 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1168, p := 5, q := 1163 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1170, p := 7, q := 1163 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1172, p := 19, q := 1153 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1174, p := 3, q := 1171 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1176, p := 5, q := 1171 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1178, p := 7, q := 1171 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1180, p := 17, q := 1163 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1182, p := 11, q := 1171 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1184, p := 3, q := 1181 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1186, p := 5, q := 1181 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1188, p := 7, q := 1181 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1190, p := 3, q := 1187 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1192, p := 5, q := 1187 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1194, p := 7, q := 1187 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1196, p := 3, q := 1193 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1198, p := 5, q := 1193 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1200, p := 7, q := 1193 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1202, p := 31, q := 1171 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate1102To1202 : List CertificateEntry :=
  verifiedCertificateEntries certificate1102To1202Verified

theorem certificate1102To1202_covers :
    CertificateCoversBetween 1102 1202 certificate1102To1202 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween1102To1202 :
    GoldbachBetween 1102 1202 :=
  goldbachBetween_of_certificate certificate1102To1202_covers

def certificate1202To1302Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 1204, p := 3, q := 1201 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1206, p := 5, q := 1201 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1208, p := 7, q := 1201 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1210, p := 17, q := 1193 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1212, p := 11, q := 1201 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1214, p := 13, q := 1201 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1216, p := 3, q := 1213 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1218, p := 5, q := 1213 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1220, p := 3, q := 1217 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1222, p := 5, q := 1217 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1224, p := 7, q := 1217 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1226, p := 3, q := 1223 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1228, p := 5, q := 1223 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1230, p := 7, q := 1223 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1232, p := 3, q := 1229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1234, p := 3, q := 1231 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1236, p := 5, q := 1231 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1238, p := 7, q := 1231 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1240, p := 3, q := 1237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1242, p := 5, q := 1237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1244, p := 7, q := 1237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1246, p := 17, q := 1229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1248, p := 11, q := 1237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1250, p := 13, q := 1237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1252, p := 3, q := 1249 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1254, p := 5, q := 1249 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1256, p := 7, q := 1249 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1258, p := 29, q := 1229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1260, p := 11, q := 1249 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1262, p := 3, q := 1259 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1264, p := 5, q := 1259 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1266, p := 7, q := 1259 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1268, p := 19, q := 1249 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1270, p := 11, q := 1259 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1272, p := 13, q := 1259 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1274, p := 37, q := 1237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1276, p := 17, q := 1259 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1278, p := 19, q := 1259 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1280, p := 3, q := 1277 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1282, p := 3, q := 1279 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1284, p := 5, q := 1279 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1286, p := 3, q := 1283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1288, p := 5, q := 1283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1290, p := 7, q := 1283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1292, p := 3, q := 1289 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1294, p := 3, q := 1291 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1296, p := 5, q := 1291 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1298, p := 7, q := 1291 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1300, p := 3, q := 1297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1302, p := 5, q := 1297 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate1202To1302 : List CertificateEntry :=
  verifiedCertificateEntries certificate1202To1302Verified

theorem certificate1202To1302_covers :
    CertificateCoversBetween 1202 1302 certificate1202To1302 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween1202To1302 :
    GoldbachBetween 1202 1302 :=
  goldbachBetween_of_certificate certificate1202To1302_covers

def certificate1302To1402Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 1304, p := 3, q := 1301 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1306, p := 3, q := 1303 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1308, p := 5, q := 1303 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1310, p := 3, q := 1307 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1312, p := 5, q := 1307 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1314, p := 7, q := 1307 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1316, p := 13, q := 1303 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1318, p := 11, q := 1307 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1320, p := 13, q := 1307 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1322, p := 3, q := 1319 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1324, p := 3, q := 1321 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1326, p := 5, q := 1321 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1328, p := 7, q := 1321 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1330, p := 3, q := 1327 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1332, p := 5, q := 1327 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1334, p := 7, q := 1327 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1336, p := 17, q := 1319 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1338, p := 11, q := 1327 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1340, p := 13, q := 1327 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1342, p := 23, q := 1319 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1344, p := 17, q := 1327 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1346, p := 19, q := 1327 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1348, p := 29, q := 1319 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1350, p := 23, q := 1327 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1352, p := 31, q := 1321 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1354, p := 47, q := 1307 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1356, p := 29, q := 1327 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1358, p := 31, q := 1327 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1360, p := 41, q := 1319 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1362, p := 41, q := 1321 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1364, p := 3, q := 1361 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1366, p := 5, q := 1361 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1368, p := 7, q := 1361 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1370, p := 3, q := 1367 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1372, p := 5, q := 1367 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1374, p := 7, q := 1367 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1376, p := 3, q := 1373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1378, p := 5, q := 1373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1380, p := 7, q := 1373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1382, p := 61, q := 1321 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1384, p := 3, q := 1381 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1386, p := 5, q := 1381 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1388, p := 7, q := 1381 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1390, p := 17, q := 1373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1392, p := 11, q := 1381 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1394, p := 13, q := 1381 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1396, p := 23, q := 1373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1398, p := 17, q := 1381 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1400, p := 19, q := 1381 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1402, p := 3, q := 1399 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate1302To1402 : List CertificateEntry :=
  verifiedCertificateEntries certificate1302To1402Verified

theorem certificate1302To1402_covers :
    CertificateCoversBetween 1302 1402 certificate1302To1402 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween1302To1402 :
    GoldbachBetween 1302 1402 :=
  goldbachBetween_of_certificate certificate1302To1402_covers

def certificate1402To1502Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 1404, p := 5, q := 1399 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1406, p := 7, q := 1399 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1408, p := 41, q := 1367 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1410, p := 11, q := 1399 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1412, p := 3, q := 1409 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1414, p := 5, q := 1409 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1416, p := 7, q := 1409 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1418, p := 19, q := 1399 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1420, p := 11, q := 1409 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1422, p := 13, q := 1409 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1424, p := 43, q := 1381 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1426, p := 3, q := 1423 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1428, p := 5, q := 1423 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1430, p := 3, q := 1427 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1432, p := 3, q := 1429 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1434, p := 5, q := 1429 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1436, p := 3, q := 1433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1438, p := 5, q := 1433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1440, p := 7, q := 1433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1442, p := 3, q := 1439 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1444, p := 5, q := 1439 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1446, p := 7, q := 1439 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1448, p := 19, q := 1429 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1450, p := 3, q := 1447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1452, p := 5, q := 1447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1454, p := 3, q := 1451 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1456, p := 3, q := 1453 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1458, p := 5, q := 1453 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1460, p := 7, q := 1453 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1462, p := 3, q := 1459 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1464, p := 5, q := 1459 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1466, p := 7, q := 1459 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1468, p := 17, q := 1451 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1470, p := 11, q := 1459 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1472, p := 13, q := 1459 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1474, p := 3, q := 1471 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1476, p := 5, q := 1471 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1478, p := 7, q := 1471 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1480, p := 29, q := 1451 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1482, p := 11, q := 1471 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1484, p := 3, q := 1481 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1486, p := 3, q := 1483 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1488, p := 5, q := 1483 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1490, p := 3, q := 1487 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1492, p := 3, q := 1489 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1494, p := 5, q := 1489 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1496, p := 3, q := 1493 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1498, p := 5, q := 1493 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1500, p := 7, q := 1493 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1502, p := 3, q := 1499 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate1402To1502 : List CertificateEntry :=
  verifiedCertificateEntries certificate1402To1502Verified

theorem certificate1402To1502_covers :
    CertificateCoversBetween 1402 1502 certificate1402To1502 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween1402To1502 :
    GoldbachBetween 1402 1502 :=
  goldbachBetween_of_certificate certificate1402To1502_covers

def certificate1502To1602Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 1504, p := 5, q := 1499 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1506, p := 7, q := 1499 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1508, p := 19, q := 1489 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1510, p := 11, q := 1499 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1512, p := 13, q := 1499 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1514, p := 3, q := 1511 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1516, p := 5, q := 1511 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1518, p := 7, q := 1511 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1520, p := 31, q := 1489 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1522, p := 11, q := 1511 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1524, p := 13, q := 1511 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1526, p := 3, q := 1523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1528, p := 5, q := 1523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1530, p := 7, q := 1523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1532, p := 43, q := 1489 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1534, p := 3, q := 1531 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1536, p := 5, q := 1531 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1538, p := 7, q := 1531 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1540, p := 17, q := 1523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1542, p := 11, q := 1531 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1544, p := 13, q := 1531 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1546, p := 3, q := 1543 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1548, p := 5, q := 1543 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1550, p := 7, q := 1543 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1552, p := 3, q := 1549 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1554, p := 5, q := 1549 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1556, p := 3, q := 1553 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1558, p := 5, q := 1553 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1560, p := 7, q := 1553 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1562, p := 3, q := 1559 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1564, p := 5, q := 1559 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1566, p := 7, q := 1559 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1568, p := 19, q := 1549 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1570, p := 3, q := 1567 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1572, p := 5, q := 1567 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1574, p := 3, q := 1571 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1576, p := 5, q := 1571 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1578, p := 7, q := 1571 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1580, p := 13, q := 1567 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1582, p := 3, q := 1579 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1584, p := 5, q := 1579 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1586, p := 3, q := 1583 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1588, p := 5, q := 1583 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1590, p := 7, q := 1583 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1592, p := 13, q := 1579 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1594, p := 11, q := 1583 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1596, p := 13, q := 1583 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1598, p := 19, q := 1579 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1600, p := 3, q := 1597 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1602, p := 5, q := 1597 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate1502To1602 : List CertificateEntry :=
  verifiedCertificateEntries certificate1502To1602Verified

theorem certificate1502To1602_covers :
    CertificateCoversBetween 1502 1602 certificate1502To1602 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween1502To1602 :
    GoldbachBetween 1502 1602 :=
  goldbachBetween_of_certificate certificate1502To1602_covers

def certificate1602To1702Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 1604, p := 3, q := 1601 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1606, p := 5, q := 1601 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1608, p := 7, q := 1601 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1610, p := 3, q := 1607 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1612, p := 3, q := 1609 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1614, p := 5, q := 1609 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1616, p := 3, q := 1613 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1618, p := 5, q := 1613 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1620, p := 7, q := 1613 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1622, p := 3, q := 1619 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1624, p := 3, q := 1621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1626, p := 5, q := 1621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1628, p := 7, q := 1621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1630, p := 3, q := 1627 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1632, p := 5, q := 1627 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1634, p := 7, q := 1627 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1636, p := 17, q := 1619 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1638, p := 11, q := 1627 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1640, p := 3, q := 1637 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1642, p := 5, q := 1637 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1644, p := 7, q := 1637 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1646, p := 19, q := 1627 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1648, p := 11, q := 1637 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1650, p := 13, q := 1637 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1652, p := 31, q := 1621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1654, p := 17, q := 1637 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1656, p := 19, q := 1637 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1658, p := 31, q := 1627 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1660, p := 3, q := 1657 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1662, p := 5, q := 1657 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1664, p := 7, q := 1657 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1666, p := 3, q := 1663 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1668, p := 5, q := 1663 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1670, p := 3, q := 1667 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1672, p := 3, q := 1669 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1674, p := 5, q := 1669 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1676, p := 7, q := 1669 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1678, p := 11, q := 1667 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1680, p := 11, q := 1669 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1682, p := 13, q := 1669 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1684, p := 17, q := 1667 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1686, p := 17, q := 1669 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1688, p := 19, q := 1669 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1690, p := 23, q := 1667 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1692, p := 23, q := 1669 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1694, p := 31, q := 1663 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1696, p := 3, q := 1693 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1698, p := 5, q := 1693 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1700, p := 3, q := 1697 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1702, p := 3, q := 1699 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate1602To1702 : List CertificateEntry :=
  verifiedCertificateEntries certificate1602To1702Verified

theorem certificate1602To1702_covers :
    CertificateCoversBetween 1602 1702 certificate1602To1702 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween1602To1702 :
    GoldbachBetween 1602 1702 :=
  goldbachBetween_of_certificate certificate1602To1702_covers

def certificate1702To1802Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 1704, p := 5, q := 1699 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1706, p := 7, q := 1699 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1708, p := 11, q := 1697 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1710, p := 11, q := 1699 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1712, p := 3, q := 1709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1714, p := 5, q := 1709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1716, p := 7, q := 1709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1718, p := 19, q := 1699 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1720, p := 11, q := 1709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1722, p := 13, q := 1709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1724, p := 3, q := 1721 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1726, p := 3, q := 1723 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1728, p := 5, q := 1723 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1730, p := 7, q := 1723 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1732, p := 11, q := 1721 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1734, p := 11, q := 1723 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1736, p := 3, q := 1733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1738, p := 5, q := 1733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1740, p := 7, q := 1733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1742, p := 19, q := 1723 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1744, p := 3, q := 1741 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1746, p := 5, q := 1741 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1748, p := 7, q := 1741 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1750, p := 3, q := 1747 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1752, p := 5, q := 1747 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1754, p := 7, q := 1747 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1756, p := 3, q := 1753 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1758, p := 5, q := 1753 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1760, p := 7, q := 1753 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1762, p := 3, q := 1759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1764, p := 5, q := 1759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1766, p := 7, q := 1759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1768, p := 47, q := 1721 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1770, p := 11, q := 1759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1772, p := 13, q := 1759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1774, p := 41, q := 1733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1776, p := 17, q := 1759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1778, p := 19, q := 1759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1780, p := 3, q := 1777 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1782, p := 5, q := 1777 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1784, p := 7, q := 1777 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1786, p := 3, q := 1783 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1788, p := 5, q := 1783 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1790, p := 3, q := 1787 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1792, p := 3, q := 1789 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1794, p := 5, q := 1789 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1796, p := 7, q := 1789 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1798, p := 11, q := 1787 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1800, p := 11, q := 1789 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1802, p := 13, q := 1789 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate1702To1802 : List CertificateEntry :=
  verifiedCertificateEntries certificate1702To1802Verified

theorem certificate1702To1802_covers :
    CertificateCoversBetween 1702 1802 certificate1702To1802 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween1702To1802 :
    GoldbachBetween 1702 1802 :=
  goldbachBetween_of_certificate certificate1702To1802_covers

def certificate1802To1902Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 1804, p := 3, q := 1801 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1806, p := 5, q := 1801 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1808, p := 7, q := 1801 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1810, p := 23, q := 1787 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1812, p := 11, q := 1801 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1814, p := 3, q := 1811 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1816, p := 5, q := 1811 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1818, p := 7, q := 1811 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1820, p := 19, q := 1801 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1822, p := 11, q := 1811 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1824, p := 13, q := 1811 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1826, p := 3, q := 1823 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1828, p := 5, q := 1823 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1830, p := 7, q := 1823 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1832, p := 31, q := 1801 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1834, p := 3, q := 1831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1836, p := 5, q := 1831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1838, p := 7, q := 1831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1840, p := 17, q := 1823 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1842, p := 11, q := 1831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1844, p := 13, q := 1831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1846, p := 23, q := 1823 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1848, p := 17, q := 1831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1850, p := 3, q := 1847 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1852, p := 5, q := 1847 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1854, p := 7, q := 1847 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1856, p := 67, q := 1789 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1858, p := 11, q := 1847 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1860, p := 13, q := 1847 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1862, p := 31, q := 1831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1864, p := 3, q := 1861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1866, p := 5, q := 1861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1868, p := 7, q := 1861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1870, p := 3, q := 1867 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1872, p := 5, q := 1867 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1874, p := 3, q := 1871 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1876, p := 3, q := 1873 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1878, p := 5, q := 1873 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1880, p := 3, q := 1877 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1882, p := 3, q := 1879 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1884, p := 5, q := 1879 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1886, p := 7, q := 1879 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1888, p := 11, q := 1877 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1890, p := 11, q := 1879 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1892, p := 3, q := 1889 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1894, p := 5, q := 1889 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1896, p := 7, q := 1889 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1898, p := 19, q := 1879 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1900, p := 11, q := 1889 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1902, p := 13, q := 1889 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate1802To1902 : List CertificateEntry :=
  verifiedCertificateEntries certificate1802To1902Verified

theorem certificate1802To1902_covers :
    CertificateCoversBetween 1802 1902 certificate1802To1902 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween1802To1902 :
    GoldbachBetween 1802 1902 :=
  goldbachBetween_of_certificate certificate1802To1902_covers

def certificate1902To2002Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 1904, p := 3, q := 1901 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1906, p := 5, q := 1901 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1908, p := 7, q := 1901 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1910, p := 3, q := 1907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1912, p := 5, q := 1907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1914, p := 7, q := 1907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1916, p := 3, q := 1913 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1918, p := 5, q := 1913 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1920, p := 7, q := 1913 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1922, p := 43, q := 1879 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1924, p := 11, q := 1913 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1926, p := 13, q := 1913 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1928, p := 61, q := 1867 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1930, p := 17, q := 1913 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1932, p := 19, q := 1913 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1934, p := 3, q := 1931 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1936, p := 3, q := 1933 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1938, p := 5, q := 1933 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1940, p := 7, q := 1933 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1942, p := 11, q := 1931 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1944, p := 11, q := 1933 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1946, p := 13, q := 1933 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1948, p := 17, q := 1931 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1950, p := 17, q := 1933 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1952, p := 3, q := 1949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1954, p := 3, q := 1951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1956, p := 5, q := 1951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1958, p := 7, q := 1951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1960, p := 11, q := 1949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1962, p := 11, q := 1951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1964, p := 13, q := 1951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1966, p := 17, q := 1949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1968, p := 17, q := 1951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1970, p := 19, q := 1951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1972, p := 23, q := 1949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1974, p := 23, q := 1951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1976, p := 3, q := 1973 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1978, p := 5, q := 1973 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1980, p := 7, q := 1973 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1982, p := 3, q := 1979 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1984, p := 5, q := 1979 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1986, p := 7, q := 1979 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1988, p := 37, q := 1951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1990, p := 3, q := 1987 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1992, p := 5, q := 1987 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1994, p := 7, q := 1987 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1996, p := 3, q := 1993 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 1998, p := 5, q := 1993 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2000, p := 3, q := 1997 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2002, p := 3, q := 1999 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate1902To2002 : List CertificateEntry :=
  verifiedCertificateEntries certificate1902To2002Verified

theorem certificate1902To2002_covers :
    CertificateCoversBetween 1902 2002 certificate1902To2002 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween1902To2002 :
    GoldbachBetween 1902 2002 :=
  goldbachBetween_of_certificate certificate1902To2002_covers

def certificate2002To2102Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 2004, p := 5, q := 1999 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2006, p := 3, q := 2003 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2008, p := 5, q := 2003 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2010, p := 7, q := 2003 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2012, p := 13, q := 1999 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2014, p := 3, q := 2011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2016, p := 5, q := 2011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2018, p := 7, q := 2011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2020, p := 3, q := 2017 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2022, p := 5, q := 2017 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2024, p := 7, q := 2017 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2026, p := 23, q := 2003 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2028, p := 11, q := 2017 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2030, p := 3, q := 2027 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2032, p := 3, q := 2029 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2034, p := 5, q := 2029 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2036, p := 7, q := 2029 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2038, p := 11, q := 2027 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2040, p := 11, q := 2029 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2042, p := 3, q := 2039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2044, p := 5, q := 2039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2046, p := 7, q := 2039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2048, p := 19, q := 2029 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2050, p := 11, q := 2039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2052, p := 13, q := 2039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2054, p := 37, q := 2017 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2056, p := 3, q := 2053 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2058, p := 5, q := 2053 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2060, p := 7, q := 2053 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2062, p := 23, q := 2039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2064, p := 11, q := 2053 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2066, p := 3, q := 2063 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2068, p := 5, q := 2063 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2070, p := 7, q := 2063 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2072, p := 3, q := 2069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2074, p := 5, q := 2069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2076, p := 7, q := 2069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2078, p := 61, q := 2017 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2080, p := 11, q := 2069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2082, p := 13, q := 2069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2084, p := 3, q := 2081 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2086, p := 3, q := 2083 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2088, p := 5, q := 2083 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2090, p := 3, q := 2087 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2092, p := 3, q := 2089 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2094, p := 5, q := 2089 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2096, p := 7, q := 2089 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2098, p := 11, q := 2087 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2100, p := 11, q := 2089 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2102, p := 3, q := 2099 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate2002To2102 : List CertificateEntry :=
  verifiedCertificateEntries certificate2002To2102Verified

theorem certificate2002To2102_covers :
    CertificateCoversBetween 2002 2102 certificate2002To2102 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween2002To2102 :
    GoldbachBetween 2002 2102 :=
  goldbachBetween_of_certificate certificate2002To2102_covers

def certificate2102To2202Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 2104, p := 5, q := 2099 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2106, p := 7, q := 2099 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2108, p := 19, q := 2089 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2110, p := 11, q := 2099 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2112, p := 13, q := 2099 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2114, p := 3, q := 2111 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2116, p := 3, q := 2113 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2118, p := 5, q := 2113 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2120, p := 7, q := 2113 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2122, p := 11, q := 2111 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2124, p := 11, q := 2113 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2126, p := 13, q := 2113 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2128, p := 17, q := 2111 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2130, p := 17, q := 2113 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2132, p := 3, q := 2129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2134, p := 3, q := 2131 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2136, p := 5, q := 2131 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2138, p := 7, q := 2131 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2140, p := 3, q := 2137 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2142, p := 5, q := 2137 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2144, p := 3, q := 2141 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2146, p := 3, q := 2143 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2148, p := 5, q := 2143 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2150, p := 7, q := 2143 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2152, p := 11, q := 2141 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2154, p := 11, q := 2143 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2156, p := 3, q := 2153 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2158, p := 5, q := 2153 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2160, p := 7, q := 2153 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2162, p := 19, q := 2143 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2164, p := 3, q := 2161 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2166, p := 5, q := 2161 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2168, p := 7, q := 2161 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2170, p := 17, q := 2153 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2172, p := 11, q := 2161 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2174, p := 13, q := 2161 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2176, p := 23, q := 2153 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2178, p := 17, q := 2161 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2180, p := 19, q := 2161 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2182, p := 3, q := 2179 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2184, p := 5, q := 2179 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2186, p := 7, q := 2179 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2188, p := 47, q := 2141 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2190, p := 11, q := 2179 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2192, p := 13, q := 2179 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2194, p := 41, q := 2153 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2196, p := 17, q := 2179 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2198, p := 19, q := 2179 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2200, p := 47, q := 2153 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2202, p := 23, q := 2179 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate2102To2202 : List CertificateEntry :=
  verifiedCertificateEntries certificate2102To2202Verified

theorem certificate2102To2202_covers :
    CertificateCoversBetween 2102 2202 certificate2102To2202 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween2102To2202 :
    GoldbachBetween 2102 2202 :=
  goldbachBetween_of_certificate certificate2102To2202_covers

def certificate2202To2302Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 2204, p := 43, q := 2161 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2206, p := 3, q := 2203 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2208, p := 5, q := 2203 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2210, p := 3, q := 2207 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2212, p := 5, q := 2207 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2214, p := 7, q := 2207 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2216, p := 3, q := 2213 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2218, p := 5, q := 2213 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2220, p := 7, q := 2213 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2222, p := 19, q := 2203 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2224, p := 3, q := 2221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2226, p := 5, q := 2221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2228, p := 7, q := 2221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2230, p := 17, q := 2213 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2232, p := 11, q := 2221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2234, p := 13, q := 2221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2236, p := 23, q := 2213 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2238, p := 17, q := 2221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2240, p := 3, q := 2237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2242, p := 3, q := 2239 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2244, p := 5, q := 2239 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2246, p := 3, q := 2243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2248, p := 5, q := 2243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2250, p := 7, q := 2243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2252, p := 13, q := 2239 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2254, p := 3, q := 2251 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2256, p := 5, q := 2251 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2258, p := 7, q := 2251 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2260, p := 17, q := 2243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2262, p := 11, q := 2251 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2264, p := 13, q := 2251 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2266, p := 23, q := 2243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2268, p := 17, q := 2251 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2270, p := 3, q := 2267 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2272, p := 3, q := 2269 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2274, p := 5, q := 2269 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2276, p := 3, q := 2273 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2278, p := 5, q := 2273 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2280, p := 7, q := 2273 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2282, p := 13, q := 2269 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2284, p := 3, q := 2281 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2286, p := 5, q := 2281 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2288, p := 7, q := 2281 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2290, p := 3, q := 2287 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2292, p := 5, q := 2287 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2294, p := 7, q := 2287 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2296, p := 3, q := 2293 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2298, p := 5, q := 2293 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2300, p := 3, q := 2297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2302, p := 5, q := 2297 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate2202To2302 : List CertificateEntry :=
  verifiedCertificateEntries certificate2202To2302Verified

theorem certificate2202To2302_covers :
    CertificateCoversBetween 2202 2302 certificate2202To2302 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween2202To2302 :
    GoldbachBetween 2202 2302 :=
  goldbachBetween_of_certificate certificate2202To2302_covers

def certificate2302To2402Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 2304, p := 7, q := 2297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2306, p := 13, q := 2293 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2308, p := 11, q := 2297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2310, p := 13, q := 2297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2312, p := 3, q := 2309 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2314, p := 3, q := 2311 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2316, p := 5, q := 2311 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2318, p := 7, q := 2311 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2320, p := 11, q := 2309 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2322, p := 11, q := 2311 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2324, p := 13, q := 2311 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2326, p := 17, q := 2309 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2328, p := 17, q := 2311 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2330, p := 19, q := 2311 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2332, p := 23, q := 2309 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2334, p := 23, q := 2311 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2336, p := 3, q := 2333 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2338, p := 5, q := 2333 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2340, p := 7, q := 2333 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2342, p := 3, q := 2339 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2344, p := 3, q := 2341 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2346, p := 5, q := 2341 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2348, p := 7, q := 2341 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2350, p := 3, q := 2347 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2352, p := 5, q := 2347 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2354, p := 3, q := 2351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2356, p := 5, q := 2351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2358, p := 7, q := 2351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2360, p := 3, q := 2357 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2362, p := 5, q := 2357 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2364, p := 7, q := 2357 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2366, p := 19, q := 2347 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2368, p := 11, q := 2357 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2370, p := 13, q := 2357 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2372, p := 31, q := 2341 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2374, p := 3, q := 2371 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2376, p := 5, q := 2371 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2378, p := 7, q := 2371 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2380, p := 3, q := 2377 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2382, p := 5, q := 2377 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2384, p := 3, q := 2381 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2386, p := 3, q := 2383 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2388, p := 5, q := 2383 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2390, p := 7, q := 2383 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2392, p := 3, q := 2389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2394, p := 5, q := 2389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2396, p := 3, q := 2393 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2398, p := 5, q := 2393 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2400, p := 7, q := 2393 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2402, p := 3, q := 2399 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate2302To2402 : List CertificateEntry :=
  verifiedCertificateEntries certificate2302To2402Verified

theorem certificate2302To2402_covers :
    CertificateCoversBetween 2302 2402 certificate2302To2402 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween2302To2402 :
    GoldbachBetween 2302 2402 :=
  goldbachBetween_of_certificate certificate2302To2402_covers

def certificate2402To2502Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 2404, p := 5, q := 2399 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2406, p := 7, q := 2399 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2408, p := 19, q := 2389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2410, p := 11, q := 2399 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2412, p := 13, q := 2399 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2414, p := 3, q := 2411 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2416, p := 5, q := 2411 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2418, p := 7, q := 2411 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2420, p := 3, q := 2417 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2422, p := 5, q := 2417 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2424, p := 7, q := 2417 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2426, p := 3, q := 2423 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2428, p := 5, q := 2423 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2430, p := 7, q := 2423 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2432, p := 43, q := 2389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2434, p := 11, q := 2423 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2436, p := 13, q := 2423 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2438, p := 61, q := 2377 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2440, p := 3, q := 2437 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2442, p := 5, q := 2437 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2444, p := 3, q := 2441 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2446, p := 5, q := 2441 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2448, p := 7, q := 2441 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2450, p := 3, q := 2447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2452, p := 5, q := 2447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2454, p := 7, q := 2447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2456, p := 19, q := 2437 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2458, p := 11, q := 2447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2460, p := 13, q := 2447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2462, p := 3, q := 2459 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2464, p := 5, q := 2459 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2466, p := 7, q := 2459 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2468, p := 31, q := 2437 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2470, p := 3, q := 2467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2472, p := 5, q := 2467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2474, p := 7, q := 2467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2476, p := 3, q := 2473 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2478, p := 5, q := 2473 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2480, p := 3, q := 2477 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2482, p := 5, q := 2477 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2484, p := 7, q := 2477 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2486, p := 13, q := 2473 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2488, p := 11, q := 2477 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2490, p := 13, q := 2477 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2492, p := 19, q := 2473 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2494, p := 17, q := 2477 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2496, p := 19, q := 2477 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2498, p := 31, q := 2467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2500, p := 23, q := 2477 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2502, p := 29, q := 2473 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate2402To2502 : List CertificateEntry :=
  verifiedCertificateEntries certificate2402To2502Verified

theorem certificate2402To2502_covers :
    CertificateCoversBetween 2402 2502 certificate2402To2502 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween2402To2502 :
    GoldbachBetween 2402 2502 :=
  goldbachBetween_of_certificate certificate2402To2502_covers

def certificate2502To2602Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 2504, p := 31, q := 2473 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2506, p := 3, q := 2503 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2508, p := 5, q := 2503 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2510, p := 7, q := 2503 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2512, p := 53, q := 2459 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2514, p := 11, q := 2503 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2516, p := 13, q := 2503 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2518, p := 41, q := 2477 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2520, p := 17, q := 2503 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2522, p := 19, q := 2503 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2524, p := 3, q := 2521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2526, p := 5, q := 2521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2528, p := 7, q := 2521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2530, p := 53, q := 2477 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2532, p := 11, q := 2521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2534, p := 3, q := 2531 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2536, p := 5, q := 2531 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2538, p := 7, q := 2531 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2540, p := 19, q := 2521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2542, p := 3, q := 2539 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2544, p := 5, q := 2539 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2546, p := 3, q := 2543 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2548, p := 5, q := 2543 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2550, p := 7, q := 2543 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2552, p := 3, q := 2549 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2554, p := 3, q := 2551 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2556, p := 5, q := 2551 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2558, p := 7, q := 2551 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2560, p := 3, q := 2557 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2562, p := 5, q := 2557 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2564, p := 7, q := 2557 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2566, p := 17, q := 2549 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2568, p := 11, q := 2557 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2570, p := 13, q := 2557 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2572, p := 23, q := 2549 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2574, p := 17, q := 2557 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2576, p := 19, q := 2557 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2578, p := 29, q := 2549 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2580, p := 23, q := 2557 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2582, p := 3, q := 2579 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2584, p := 5, q := 2579 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2586, p := 7, q := 2579 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2588, p := 31, q := 2557 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2590, p := 11, q := 2579 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2592, p := 13, q := 2579 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2594, p := 3, q := 2591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2596, p := 3, q := 2593 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2598, p := 5, q := 2593 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2600, p := 7, q := 2593 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2602, p := 11, q := 2591 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate2502To2602 : List CertificateEntry :=
  verifiedCertificateEntries certificate2502To2602Verified

theorem certificate2502To2602_covers :
    CertificateCoversBetween 2502 2602 certificate2502To2602 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween2502To2602 :
    GoldbachBetween 2502 2602 :=
  goldbachBetween_of_certificate certificate2502To2602_covers

def certificate2602To2702Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 2604, p := 11, q := 2593 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2606, p := 13, q := 2593 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2608, p := 17, q := 2591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2610, p := 17, q := 2593 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2612, p := 3, q := 2609 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2614, p := 5, q := 2609 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2616, p := 7, q := 2609 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2618, p := 61, q := 2557 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2620, p := 3, q := 2617 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2622, p := 5, q := 2617 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2624, p := 3, q := 2621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2626, p := 5, q := 2621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2628, p := 7, q := 2621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2630, p := 13, q := 2617 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2632, p := 11, q := 2621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2634, p := 13, q := 2621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2636, p := 3, q := 2633 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2638, p := 5, q := 2633 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2640, p := 7, q := 2633 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2642, p := 103, q := 2539 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2644, p := 11, q := 2633 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2646, p := 13, q := 2633 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2648, p := 31, q := 2617 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2650, p := 3, q := 2647 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2652, p := 5, q := 2647 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2654, p := 7, q := 2647 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2656, p := 23, q := 2633 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2658, p := 11, q := 2647 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2660, p := 3, q := 2657 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2662, p := 3, q := 2659 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2664, p := 5, q := 2659 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2666, p := 3, q := 2663 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2668, p := 5, q := 2663 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2670, p := 7, q := 2663 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2672, p := 13, q := 2659 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2674, p := 3, q := 2671 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2676, p := 5, q := 2671 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2678, p := 7, q := 2671 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2680, p := 3, q := 2677 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2682, p := 5, q := 2677 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2684, p := 7, q := 2677 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2686, p := 3, q := 2683 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2688, p := 5, q := 2683 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2690, p := 3, q := 2687 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2692, p := 3, q := 2689 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2694, p := 5, q := 2689 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2696, p := 3, q := 2693 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2698, p := 5, q := 2693 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2700, p := 7, q := 2693 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2702, p := 3, q := 2699 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate2602To2702 : List CertificateEntry :=
  verifiedCertificateEntries certificate2602To2702Verified

theorem certificate2602To2702_covers :
    CertificateCoversBetween 2602 2702 certificate2602To2702 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween2602To2702 :
    GoldbachBetween 2602 2702 :=
  goldbachBetween_of_certificate certificate2602To2702_covers

def certificate2702To2802Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 2704, p := 5, q := 2699 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2706, p := 7, q := 2699 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2708, p := 19, q := 2689 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2710, p := 3, q := 2707 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2712, p := 5, q := 2707 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2714, p := 3, q := 2711 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2716, p := 3, q := 2713 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2718, p := 5, q := 2713 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2720, p := 7, q := 2713 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2722, p := 3, q := 2719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2724, p := 5, q := 2719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2726, p := 7, q := 2719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2728, p := 17, q := 2711 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2730, p := 11, q := 2719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2732, p := 3, q := 2729 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2734, p := 3, q := 2731 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2736, p := 5, q := 2731 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2738, p := 7, q := 2731 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2740, p := 11, q := 2729 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2742, p := 11, q := 2731 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2744, p := 3, q := 2741 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2746, p := 5, q := 2741 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2748, p := 7, q := 2741 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2750, p := 19, q := 2731 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2752, p := 3, q := 2749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2754, p := 5, q := 2749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2756, p := 3, q := 2753 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2758, p := 5, q := 2753 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2760, p := 7, q := 2753 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2762, p := 13, q := 2749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2764, p := 11, q := 2753 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2766, p := 13, q := 2753 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2768, p := 19, q := 2749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2770, p := 3, q := 2767 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2772, p := 5, q := 2767 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2774, p := 7, q := 2767 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2776, p := 23, q := 2753 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2778, p := 11, q := 2767 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2780, p := 3, q := 2777 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2782, p := 5, q := 2777 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2784, p := 7, q := 2777 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2786, p := 19, q := 2767 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2788, p := 11, q := 2777 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2790, p := 13, q := 2777 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2792, p := 3, q := 2789 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2794, p := 3, q := 2791 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2796, p := 5, q := 2791 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2798, p := 7, q := 2791 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2800, p := 3, q := 2797 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2802, p := 5, q := 2797 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate2702To2802 : List CertificateEntry :=
  verifiedCertificateEntries certificate2702To2802Verified

theorem certificate2702To2802_covers :
    CertificateCoversBetween 2702 2802 certificate2702To2802 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween2702To2802 :
    GoldbachBetween 2702 2802 :=
  goldbachBetween_of_certificate certificate2702To2802_covers

def certificate2802To2902Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 2804, p := 3, q := 2801 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2806, p := 3, q := 2803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2808, p := 5, q := 2803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2810, p := 7, q := 2803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2812, p := 11, q := 2801 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2814, p := 11, q := 2803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2816, p := 13, q := 2803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2818, p := 17, q := 2801 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2820, p := 17, q := 2803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2822, p := 3, q := 2819 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2824, p := 5, q := 2819 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2826, p := 7, q := 2819 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2828, p := 31, q := 2797 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2830, p := 11, q := 2819 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2832, p := 13, q := 2819 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2834, p := 31, q := 2803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2836, p := 3, q := 2833 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2838, p := 5, q := 2833 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2840, p := 3, q := 2837 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2842, p := 5, q := 2837 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2844, p := 7, q := 2837 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2846, p := 3, q := 2843 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2848, p := 5, q := 2843 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2850, p := 7, q := 2843 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2852, p := 19, q := 2833 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2854, p := 3, q := 2851 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2856, p := 5, q := 2851 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2858, p := 7, q := 2851 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2860, p := 3, q := 2857 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2862, p := 5, q := 2857 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2864, p := 3, q := 2861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2866, p := 5, q := 2861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2868, p := 7, q := 2861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2870, p := 13, q := 2857 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2872, p := 11, q := 2861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2874, p := 13, q := 2861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2876, p := 19, q := 2857 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2878, p := 17, q := 2861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2880, p := 19, q := 2861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2882, p := 3, q := 2879 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2884, p := 5, q := 2879 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2886, p := 7, q := 2879 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2888, p := 31, q := 2857 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2890, p := 3, q := 2887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2892, p := 5, q := 2887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2894, p := 7, q := 2887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2896, p := 17, q := 2879 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2898, p := 11, q := 2887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2900, p := 3, q := 2897 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2902, p := 5, q := 2897 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate2802To2902 : List CertificateEntry :=
  verifiedCertificateEntries certificate2802To2902Verified

theorem certificate2802To2902_covers :
    CertificateCoversBetween 2802 2902 certificate2802To2902 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween2802To2902 :
    GoldbachBetween 2802 2902 :=
  goldbachBetween_of_certificate certificate2802To2902_covers

def certificate2902To3002Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 2904, p := 7, q := 2897 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2906, p := 3, q := 2903 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2908, p := 5, q := 2903 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2910, p := 7, q := 2903 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2912, p := 3, q := 2909 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2914, p := 5, q := 2909 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2916, p := 7, q := 2909 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2918, p := 31, q := 2887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2920, p := 3, q := 2917 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2922, p := 5, q := 2917 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2924, p := 7, q := 2917 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2926, p := 17, q := 2909 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2928, p := 11, q := 2917 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2930, p := 3, q := 2927 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2932, p := 5, q := 2927 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2934, p := 7, q := 2927 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2936, p := 19, q := 2917 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2938, p := 11, q := 2927 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2940, p := 13, q := 2927 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2942, p := 3, q := 2939 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2944, p := 5, q := 2939 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2946, p := 7, q := 2939 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2948, p := 31, q := 2917 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2950, p := 11, q := 2939 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2952, p := 13, q := 2939 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2954, p := 37, q := 2917 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2956, p := 3, q := 2953 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2958, p := 5, q := 2953 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2960, p := 3, q := 2957 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2962, p := 5, q := 2957 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2964, p := 7, q := 2957 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2966, p := 3, q := 2963 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2968, p := 5, q := 2963 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2970, p := 7, q := 2963 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2972, p := 3, q := 2969 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2974, p := 3, q := 2971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2976, p := 5, q := 2971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2978, p := 7, q := 2971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2980, p := 11, q := 2969 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2982, p := 11, q := 2971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2984, p := 13, q := 2971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2986, p := 17, q := 2969 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2988, p := 17, q := 2971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2990, p := 19, q := 2971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2992, p := 23, q := 2969 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2994, p := 23, q := 2971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2996, p := 43, q := 2953 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 2998, p := 29, q := 2969 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3000, p := 29, q := 2971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3002, p := 3, q := 2999 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate2902To3002 : List CertificateEntry :=
  verifiedCertificateEntries certificate2902To3002Verified

theorem certificate2902To3002_covers :
    CertificateCoversBetween 2902 3002 certificate2902To3002 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween2902To3002 :
    GoldbachBetween 2902 3002 :=
  goldbachBetween_of_certificate certificate2902To3002_covers

def certificate3002To3102Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 3004, p := 3, q := 3001 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3006, p := 5, q := 3001 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3008, p := 7, q := 3001 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3010, p := 11, q := 2999 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3012, p := 11, q := 3001 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3014, p := 3, q := 3011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3016, p := 5, q := 3011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3018, p := 7, q := 3011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3020, p := 19, q := 3001 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3022, p := 3, q := 3019 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3024, p := 5, q := 3019 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3026, p := 3, q := 3023 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3028, p := 5, q := 3023 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3030, p := 7, q := 3023 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3032, p := 13, q := 3019 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3034, p := 11, q := 3023 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3036, p := 13, q := 3023 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3038, p := 19, q := 3019 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3040, p := 3, q := 3037 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3042, p := 5, q := 3037 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3044, p := 3, q := 3041 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3046, p := 5, q := 3041 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3048, p := 7, q := 3041 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3050, p := 13, q := 3037 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3052, p := 3, q := 3049 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3054, p := 5, q := 3049 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3056, p := 7, q := 3049 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3058, p := 17, q := 3041 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3060, p := 11, q := 3049 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3062, p := 13, q := 3049 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3064, p := 3, q := 3061 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3066, p := 5, q := 3061 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3068, p := 7, q := 3061 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3070, p := 3, q := 3067 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3072, p := 5, q := 3067 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3074, p := 7, q := 3067 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3076, p := 53, q := 3023 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3078, p := 11, q := 3067 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3080, p := 13, q := 3067 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3082, p := 3, q := 3079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3084, p := 5, q := 3079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3086, p := 3, q := 3083 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3088, p := 5, q := 3083 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3090, p := 7, q := 3083 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3092, p := 3, q := 3089 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3094, p := 5, q := 3089 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3096, p := 7, q := 3089 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3098, p := 19, q := 3079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3100, p := 11, q := 3089 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3102, p := 13, q := 3089 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate3002To3102 : List CertificateEntry :=
  verifiedCertificateEntries certificate3002To3102Verified

theorem certificate3002To3102_covers :
    CertificateCoversBetween 3002 3102 certificate3002To3102 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween3002To3102 :
    GoldbachBetween 3002 3102 :=
  goldbachBetween_of_certificate certificate3002To3102_covers

def certificate3102To3202Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 3104, p := 37, q := 3067 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3106, p := 17, q := 3089 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3108, p := 19, q := 3089 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3110, p := 31, q := 3079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3112, p := 3, q := 3109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3114, p := 5, q := 3109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3116, p := 7, q := 3109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3118, p := 29, q := 3089 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3120, p := 11, q := 3109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3122, p := 3, q := 3119 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3124, p := 3, q := 3121 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3126, p := 5, q := 3121 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3128, p := 7, q := 3121 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3130, p := 11, q := 3119 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3132, p := 11, q := 3121 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3134, p := 13, q := 3121 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3136, p := 17, q := 3119 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3138, p := 17, q := 3121 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3140, p := 3, q := 3137 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3142, p := 5, q := 3137 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3144, p := 7, q := 3137 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3146, p := 37, q := 3109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3148, p := 11, q := 3137 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3150, p := 13, q := 3137 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3152, p := 31, q := 3121 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3154, p := 17, q := 3137 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3156, p := 19, q := 3137 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3158, p := 37, q := 3121 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3160, p := 23, q := 3137 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3162, p := 41, q := 3121 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3164, p := 43, q := 3121 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3166, p := 3, q := 3163 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3168, p := 5, q := 3163 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3170, p := 3, q := 3167 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3172, p := 3, q := 3169 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3174, p := 5, q := 3169 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3176, p := 7, q := 3169 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3178, p := 11, q := 3167 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3180, p := 11, q := 3169 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3182, p := 13, q := 3169 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3184, p := 3, q := 3181 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3186, p := 5, q := 3181 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3188, p := 7, q := 3181 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3190, p := 3, q := 3187 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3192, p := 5, q := 3187 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3194, p := 3, q := 3191 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3196, p := 5, q := 3191 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3198, p := 7, q := 3191 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3200, p := 13, q := 3187 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3202, p := 11, q := 3191 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate3102To3202 : List CertificateEntry :=
  verifiedCertificateEntries certificate3102To3202Verified

theorem certificate3102To3202_covers :
    CertificateCoversBetween 3102 3202 certificate3102To3202 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween3102To3202 :
    GoldbachBetween 3102 3202 :=
  goldbachBetween_of_certificate certificate3102To3202_covers

def certificate3202To3302Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 3204, p := 13, q := 3191 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3206, p := 3, q := 3203 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3208, p := 5, q := 3203 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3210, p := 7, q := 3203 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3212, p := 3, q := 3209 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3214, p := 5, q := 3209 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3216, p := 7, q := 3209 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3218, p := 31, q := 3187 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3220, p := 3, q := 3217 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3222, p := 5, q := 3217 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3224, p := 3, q := 3221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3226, p := 5, q := 3221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3228, p := 7, q := 3221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3230, p := 13, q := 3217 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3232, p := 3, q := 3229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3234, p := 5, q := 3229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3236, p := 7, q := 3229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3238, p := 17, q := 3221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3240, p := 11, q := 3229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3242, p := 13, q := 3229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3244, p := 23, q := 3221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3246, p := 17, q := 3229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3248, p := 19, q := 3229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3250, p := 29, q := 3221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3252, p := 23, q := 3229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3254, p := 3, q := 3251 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3256, p := 3, q := 3253 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3258, p := 5, q := 3253 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3260, p := 3, q := 3257 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3262, p := 3, q := 3259 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3264, p := 5, q := 3259 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3266, p := 7, q := 3259 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3268, p := 11, q := 3257 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3270, p := 11, q := 3259 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3272, p := 13, q := 3259 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3274, p := 3, q := 3271 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3276, p := 5, q := 3271 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3278, p := 7, q := 3271 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3280, p := 23, q := 3257 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3282, p := 11, q := 3271 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3284, p := 13, q := 3271 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3286, p := 29, q := 3257 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3288, p := 17, q := 3271 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3290, p := 19, q := 3271 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3292, p := 41, q := 3251 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3294, p := 23, q := 3271 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3296, p := 37, q := 3259 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3298, p := 41, q := 3257 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3300, p := 29, q := 3271 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3302, p := 3, q := 3299 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate3202To3302 : List CertificateEntry :=
  verifiedCertificateEntries certificate3202To3302Verified

theorem certificate3202To3302_covers :
    CertificateCoversBetween 3202 3302 certificate3202To3302 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween3202To3302 :
    GoldbachBetween 3202 3302 :=
  goldbachBetween_of_certificate certificate3202To3302_covers

def certificate3302To3402Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 3304, p := 3, q := 3301 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3306, p := 5, q := 3301 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3308, p := 7, q := 3301 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3310, p := 3, q := 3307 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3312, p := 5, q := 3307 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3314, p := 7, q := 3307 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3316, p := 3, q := 3313 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3318, p := 5, q := 3313 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3320, p := 7, q := 3313 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3322, p := 3, q := 3319 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3324, p := 5, q := 3319 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3326, p := 3, q := 3323 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3328, p := 5, q := 3323 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3330, p := 7, q := 3323 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3332, p := 3, q := 3329 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3334, p := 3, q := 3331 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3336, p := 5, q := 3331 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3338, p := 7, q := 3331 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3340, p := 11, q := 3329 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3342, p := 11, q := 3331 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3344, p := 13, q := 3331 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3346, p := 3, q := 3343 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3348, p := 5, q := 3343 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3350, p := 3, q := 3347 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3352, p := 5, q := 3347 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3354, p := 7, q := 3347 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3356, p := 13, q := 3343 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3358, p := 11, q := 3347 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3360, p := 13, q := 3347 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3362, p := 3, q := 3359 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3364, p := 3, q := 3361 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3366, p := 5, q := 3361 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3368, p := 7, q := 3361 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3370, p := 11, q := 3359 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3372, p := 11, q := 3361 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3374, p := 3, q := 3371 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3376, p := 3, q := 3373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3378, p := 5, q := 3373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3380, p := 7, q := 3373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3382, p := 11, q := 3371 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3384, p := 11, q := 3373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3386, p := 13, q := 3373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3388, p := 17, q := 3371 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3390, p := 17, q := 3373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3392, p := 3, q := 3389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3394, p := 3, q := 3391 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3396, p := 5, q := 3391 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3398, p := 7, q := 3391 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3400, p := 11, q := 3389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3402, p := 11, q := 3391 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate3302To3402 : List CertificateEntry :=
  verifiedCertificateEntries certificate3302To3402Verified

theorem certificate3302To3402_covers :
    CertificateCoversBetween 3302 3402 certificate3302To3402 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween3302To3402 :
    GoldbachBetween 3302 3402 :=
  goldbachBetween_of_certificate certificate3302To3402_covers

def certificate3402To3502Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 3404, p := 13, q := 3391 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3406, p := 17, q := 3389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3408, p := 17, q := 3391 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3410, p := 3, q := 3407 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3412, p := 5, q := 3407 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3414, p := 7, q := 3407 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3416, p := 3, q := 3413 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3418, p := 5, q := 3413 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3420, p := 7, q := 3413 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3422, p := 31, q := 3391 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3424, p := 11, q := 3413 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3426, p := 13, q := 3413 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3428, p := 37, q := 3391 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3430, p := 17, q := 3413 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3432, p := 19, q := 3413 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3434, p := 43, q := 3391 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3436, p := 3, q := 3433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3438, p := 5, q := 3433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3440, p := 7, q := 3433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3442, p := 29, q := 3413 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3444, p := 11, q := 3433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3446, p := 13, q := 3433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3448, p := 41, q := 3407 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3450, p := 17, q := 3433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3452, p := 3, q := 3449 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3454, p := 5, q := 3449 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3456, p := 7, q := 3449 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3458, p := 67, q := 3391 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3460, p := 3, q := 3457 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3462, p := 5, q := 3457 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3464, p := 3, q := 3461 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3466, p := 3, q := 3463 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3468, p := 5, q := 3463 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3470, p := 3, q := 3467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3472, p := 3, q := 3469 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3474, p := 5, q := 3469 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3476, p := 7, q := 3469 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3478, p := 11, q := 3467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3480, p := 11, q := 3469 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3482, p := 13, q := 3469 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3484, p := 17, q := 3467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3486, p := 17, q := 3469 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3488, p := 19, q := 3469 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3490, p := 23, q := 3467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3492, p := 23, q := 3469 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3494, p := 3, q := 3491 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3496, p := 5, q := 3491 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3498, p := 7, q := 3491 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3500, p := 31, q := 3469 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3502, p := 3, q := 3499 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate3402To3502 : List CertificateEntry :=
  verifiedCertificateEntries certificate3402To3502Verified

theorem certificate3402To3502_covers :
    CertificateCoversBetween 3402 3502 certificate3402To3502 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween3402To3502 :
    GoldbachBetween 3402 3502 :=
  goldbachBetween_of_certificate certificate3402To3502_covers

def certificate3502To3602Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 3504, p := 5, q := 3499 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3506, p := 7, q := 3499 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3508, p := 17, q := 3491 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3510, p := 11, q := 3499 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3512, p := 13, q := 3499 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3514, p := 3, q := 3511 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3516, p := 5, q := 3511 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3518, p := 7, q := 3511 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3520, p := 3, q := 3517 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3522, p := 5, q := 3517 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3524, p := 7, q := 3517 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3526, p := 59, q := 3467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3528, p := 11, q := 3517 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3530, p := 3, q := 3527 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3532, p := 3, q := 3529 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3534, p := 5, q := 3529 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3536, p := 3, q := 3533 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3538, p := 5, q := 3533 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3540, p := 7, q := 3533 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3542, p := 3, q := 3539 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3544, p := 3, q := 3541 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3546, p := 5, q := 3541 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3548, p := 7, q := 3541 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3550, p := 3, q := 3547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3552, p := 5, q := 3547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3554, p := 7, q := 3547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3556, p := 17, q := 3539 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3558, p := 11, q := 3547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3560, p := 3, q := 3557 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3562, p := 3, q := 3559 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3564, p := 5, q := 3559 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3566, p := 7, q := 3559 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3568, p := 11, q := 3557 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3570, p := 11, q := 3559 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3572, p := 13, q := 3559 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3574, p := 3, q := 3571 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3576, p := 5, q := 3571 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3578, p := 7, q := 3571 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3580, p := 23, q := 3557 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3582, p := 11, q := 3571 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3584, p := 3, q := 3581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3586, p := 3, q := 3583 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3588, p := 5, q := 3583 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3590, p := 7, q := 3583 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3592, p := 11, q := 3581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3594, p := 11, q := 3583 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3596, p := 3, q := 3593 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3598, p := 5, q := 3593 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3600, p := 7, q := 3593 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3602, p := 19, q := 3583 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate3502To3602 : List CertificateEntry :=
  verifiedCertificateEntries certificate3502To3602Verified

theorem certificate3502To3602_covers :
    CertificateCoversBetween 3502 3602 certificate3502To3602 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween3502To3602 :
    GoldbachBetween 3502 3602 :=
  goldbachBetween_of_certificate certificate3502To3602_covers

def certificate3602To3702Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 3604, p := 11, q := 3593 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3606, p := 13, q := 3593 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3608, p := 37, q := 3571 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3610, p := 3, q := 3607 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3612, p := 5, q := 3607 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3614, p := 7, q := 3607 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3616, p := 3, q := 3613 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3618, p := 5, q := 3613 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3620, p := 3, q := 3617 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3622, p := 5, q := 3617 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3624, p := 7, q := 3617 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3626, p := 3, q := 3623 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3628, p := 5, q := 3623 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3630, p := 7, q := 3623 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3632, p := 19, q := 3613 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3634, p := 3, q := 3631 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3636, p := 5, q := 3631 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3638, p := 7, q := 3631 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3640, p := 3, q := 3637 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3642, p := 5, q := 3637 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3644, p := 7, q := 3637 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3646, p := 3, q := 3643 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3648, p := 5, q := 3643 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3650, p := 7, q := 3643 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3652, p := 29, q := 3623 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3654, p := 11, q := 3643 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3656, p := 13, q := 3643 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3658, p := 41, q := 3617 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3660, p := 17, q := 3643 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3662, p := 3, q := 3659 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3664, p := 5, q := 3659 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3666, p := 7, q := 3659 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3668, p := 31, q := 3637 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3670, p := 11, q := 3659 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3672, p := 13, q := 3659 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3674, p := 3, q := 3671 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3676, p := 3, q := 3673 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3678, p := 5, q := 3673 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3680, p := 3, q := 3677 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3682, p := 5, q := 3677 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3684, p := 7, q := 3677 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3686, p := 13, q := 3673 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3688, p := 11, q := 3677 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3690, p := 13, q := 3677 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3692, p := 19, q := 3673 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3694, p := 3, q := 3691 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3696, p := 5, q := 3691 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3698, p := 7, q := 3691 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3700, p := 3, q := 3697 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3702, p := 5, q := 3697 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate3602To3702 : List CertificateEntry :=
  verifiedCertificateEntries certificate3602To3702Verified

theorem certificate3602To3702_covers :
    CertificateCoversBetween 3602 3702 certificate3602To3702 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween3602To3702 :
    GoldbachBetween 3602 3702 :=
  goldbachBetween_of_certificate certificate3602To3702_covers

def certificate3702To3802Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 3704, p := 3, q := 3701 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3706, p := 5, q := 3701 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3708, p := 7, q := 3701 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3710, p := 13, q := 3697 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3712, p := 3, q := 3709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3714, p := 5, q := 3709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3716, p := 7, q := 3709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3718, p := 17, q := 3701 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3720, p := 11, q := 3709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3722, p := 3, q := 3719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3724, p := 5, q := 3719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3726, p := 7, q := 3719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3728, p := 19, q := 3709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3730, p := 3, q := 3727 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3732, p := 5, q := 3727 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3734, p := 7, q := 3727 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3736, p := 3, q := 3733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3738, p := 5, q := 3733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3740, p := 7, q := 3733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3742, p := 3, q := 3739 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3744, p := 5, q := 3739 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3746, p := 7, q := 3739 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3748, p := 29, q := 3719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3750, p := 11, q := 3739 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3752, p := 13, q := 3739 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3754, p := 53, q := 3701 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3756, p := 17, q := 3739 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3758, p := 19, q := 3739 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3760, p := 41, q := 3719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3762, p := 23, q := 3739 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3764, p := 3, q := 3761 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3766, p := 5, q := 3761 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3768, p := 7, q := 3761 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3770, p := 3, q := 3767 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3772, p := 3, q := 3769 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3774, p := 5, q := 3769 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3776, p := 7, q := 3769 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3778, p := 11, q := 3767 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3780, p := 11, q := 3769 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3782, p := 3, q := 3779 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3784, p := 5, q := 3779 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3786, p := 7, q := 3779 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3788, p := 19, q := 3769 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3790, p := 11, q := 3779 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3792, p := 13, q := 3779 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3794, p := 61, q := 3733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3796, p := 3, q := 3793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3798, p := 5, q := 3793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3800, p := 3, q := 3797 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3802, p := 5, q := 3797 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate3702To3802 : List CertificateEntry :=
  verifiedCertificateEntries certificate3702To3802Verified

theorem certificate3702To3802_covers :
    CertificateCoversBetween 3702 3802 certificate3702To3802 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween3702To3802 :
    GoldbachBetween 3702 3802 :=
  goldbachBetween_of_certificate certificate3702To3802_covers

def certificate3802To3902Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 3804, p := 7, q := 3797 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3806, p := 3, q := 3803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3808, p := 5, q := 3803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3810, p := 7, q := 3803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3812, p := 19, q := 3793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3814, p := 11, q := 3803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3816, p := 13, q := 3803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3818, p := 79, q := 3739 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3820, p := 17, q := 3803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3822, p := 19, q := 3803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3824, p := 3, q := 3821 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3826, p := 3, q := 3823 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3828, p := 5, q := 3823 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3830, p := 7, q := 3823 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3832, p := 11, q := 3821 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3834, p := 11, q := 3823 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3836, p := 3, q := 3833 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3838, p := 5, q := 3833 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3840, p := 7, q := 3833 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3842, p := 19, q := 3823 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3844, p := 11, q := 3833 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3846, p := 13, q := 3833 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3848, p := 79, q := 3769 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3850, p := 3, q := 3847 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3852, p := 5, q := 3847 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3854, p := 3, q := 3851 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3856, p := 3, q := 3853 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3858, p := 5, q := 3853 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3860, p := 7, q := 3853 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3862, p := 11, q := 3851 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3864, p := 11, q := 3853 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3866, p := 3, q := 3863 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3868, p := 5, q := 3863 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3870, p := 7, q := 3863 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3872, p := 19, q := 3853 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3874, p := 11, q := 3863 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3876, p := 13, q := 3863 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3878, p := 31, q := 3847 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3880, p := 3, q := 3877 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3882, p := 5, q := 3877 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3884, p := 3, q := 3881 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3886, p := 5, q := 3881 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3888, p := 7, q := 3881 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3890, p := 13, q := 3877 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3892, p := 3, q := 3889 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3894, p := 5, q := 3889 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3896, p := 7, q := 3889 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3898, p := 17, q := 3881 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3900, p := 11, q := 3889 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3902, p := 13, q := 3889 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate3802To3902 : List CertificateEntry :=
  verifiedCertificateEntries certificate3802To3902Verified

theorem certificate3802To3902_covers :
    CertificateCoversBetween 3802 3902 certificate3802To3902 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween3802To3902 :
    GoldbachBetween 3802 3902 :=
  goldbachBetween_of_certificate certificate3802To3902_covers

def certificate3902To4002Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 3904, p := 23, q := 3881 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3906, p := 17, q := 3889 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3908, p := 19, q := 3889 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3910, p := 3, q := 3907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3912, p := 5, q := 3907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3914, p := 3, q := 3911 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3916, p := 5, q := 3911 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3918, p := 7, q := 3911 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3920, p := 3, q := 3917 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3922, p := 3, q := 3919 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3924, p := 5, q := 3919 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3926, p := 3, q := 3923 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3928, p := 5, q := 3923 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3930, p := 7, q := 3923 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3932, p := 3, q := 3929 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3934, p := 3, q := 3931 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3936, p := 5, q := 3931 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3938, p := 7, q := 3931 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3940, p := 11, q := 3929 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3942, p := 11, q := 3931 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3944, p := 13, q := 3931 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3946, p := 3, q := 3943 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3948, p := 5, q := 3943 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3950, p := 3, q := 3947 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3952, p := 5, q := 3947 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3954, p := 7, q := 3947 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3956, p := 13, q := 3943 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3958, p := 11, q := 3947 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3960, p := 13, q := 3947 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3962, p := 19, q := 3943 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3964, p := 17, q := 3947 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3966, p := 19, q := 3947 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3968, p := 37, q := 3931 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3970, p := 3, q := 3967 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3972, p := 5, q := 3967 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3974, p := 7, q := 3967 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3976, p := 29, q := 3947 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3978, p := 11, q := 3967 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3980, p := 13, q := 3967 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3982, p := 53, q := 3929 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3984, p := 17, q := 3967 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3986, p := 19, q := 3967 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3988, p := 41, q := 3947 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3990, p := 23, q := 3967 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3992, p := 3, q := 3989 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3994, p := 5, q := 3989 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3996, p := 7, q := 3989 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 3998, p := 31, q := 3967 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4000, p := 11, q := 3989 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4002, p := 13, q := 3989 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate3902To4002 : List CertificateEntry :=
  verifiedCertificateEntries certificate3902To4002Verified

theorem certificate3902To4002_covers :
    CertificateCoversBetween 3902 4002 certificate3902To4002 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween3902To4002 :
    GoldbachBetween 3902 4002 :=
  goldbachBetween_of_certificate certificate3902To4002_covers

def certificate4002To4102Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 4004, p := 3, q := 4001 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4006, p := 3, q := 4003 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4008, p := 5, q := 4003 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4010, p := 3, q := 4007 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4012, p := 5, q := 4007 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4014, p := 7, q := 4007 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4016, p := 3, q := 4013 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4018, p := 5, q := 4013 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4020, p := 7, q := 4013 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4022, p := 3, q := 4019 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4024, p := 3, q := 4021 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4026, p := 5, q := 4021 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4028, p := 7, q := 4021 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4030, p := 3, q := 4027 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4032, p := 5, q := 4027 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4034, p := 7, q := 4027 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4036, p := 17, q := 4019 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4038, p := 11, q := 4027 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4040, p := 13, q := 4027 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4042, p := 23, q := 4019 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4044, p := 17, q := 4027 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4046, p := 19, q := 4027 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4048, p := 29, q := 4019 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4050, p := 23, q := 4027 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4052, p := 3, q := 4049 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4054, p := 3, q := 4051 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4056, p := 5, q := 4051 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4058, p := 7, q := 4051 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4060, p := 3, q := 4057 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4062, p := 5, q := 4057 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4064, p := 7, q := 4057 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4066, p := 17, q := 4049 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4068, p := 11, q := 4057 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4070, p := 13, q := 4057 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4072, p := 23, q := 4049 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4074, p := 17, q := 4057 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4076, p := 3, q := 4073 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4078, p := 5, q := 4073 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4080, p := 7, q := 4073 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4082, p := 3, q := 4079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4084, p := 5, q := 4079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4086, p := 7, q := 4079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4088, p := 31, q := 4057 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4090, p := 11, q := 4079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4092, p := 13, q := 4079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4094, p := 3, q := 4091 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4096, p := 3, q := 4093 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4098, p := 5, q := 4093 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4100, p := 7, q := 4093 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4102, p := 3, q := 4099 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate4002To4102 : List CertificateEntry :=
  verifiedCertificateEntries certificate4002To4102Verified

theorem certificate4002To4102_covers :
    CertificateCoversBetween 4002 4102 certificate4002To4102 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween4002To4102 :
    GoldbachBetween 4002 4102 :=
  goldbachBetween_of_certificate certificate4002To4102_covers

def certificate4102To4202Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 4104, p := 5, q := 4099 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4106, p := 7, q := 4099 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4108, p := 17, q := 4091 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4110, p := 11, q := 4099 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4112, p := 13, q := 4099 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4114, p := 3, q := 4111 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4116, p := 5, q := 4111 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4118, p := 7, q := 4111 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4120, p := 29, q := 4091 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4122, p := 11, q := 4111 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4124, p := 13, q := 4111 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4126, p := 47, q := 4079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4128, p := 17, q := 4111 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4130, p := 3, q := 4127 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4132, p := 3, q := 4129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4134, p := 5, q := 4129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4136, p := 3, q := 4133 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4138, p := 5, q := 4133 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4140, p := 7, q := 4133 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4142, p := 3, q := 4139 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4144, p := 5, q := 4139 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4146, p := 7, q := 4139 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4148, p := 19, q := 4129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4150, p := 11, q := 4139 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4152, p := 13, q := 4139 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4154, p := 43, q := 4111 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4156, p := 3, q := 4153 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4158, p := 5, q := 4153 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4160, p := 3, q := 4157 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4162, p := 3, q := 4159 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4164, p := 5, q := 4159 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4166, p := 7, q := 4159 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4168, p := 11, q := 4157 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4170, p := 11, q := 4159 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4172, p := 13, q := 4159 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4174, p := 17, q := 4157 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4176, p := 17, q := 4159 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4178, p := 19, q := 4159 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4180, p := 3, q := 4177 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4182, p := 5, q := 4177 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4184, p := 7, q := 4177 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4186, p := 29, q := 4157 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4188, p := 11, q := 4177 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4190, p := 13, q := 4177 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4192, p := 53, q := 4139 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4194, p := 17, q := 4177 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4196, p := 19, q := 4177 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4198, p := 41, q := 4157 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4200, p := 23, q := 4177 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4202, p := 43, q := 4159 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate4102To4202 : List CertificateEntry :=
  verifiedCertificateEntries certificate4102To4202Verified

theorem certificate4102To4202_covers :
    CertificateCoversBetween 4102 4202 certificate4102To4202 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween4102To4202 :
    GoldbachBetween 4102 4202 :=
  goldbachBetween_of_certificate certificate4102To4202_covers

def certificate4202To4302Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 4204, p := 3, q := 4201 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4206, p := 5, q := 4201 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4208, p := 7, q := 4201 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4210, p := 53, q := 4157 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4212, p := 11, q := 4201 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4214, p := 3, q := 4211 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4216, p := 5, q := 4211 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4218, p := 7, q := 4211 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4220, p := 3, q := 4217 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4222, p := 3, q := 4219 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4224, p := 5, q := 4219 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4226, p := 7, q := 4219 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4228, p := 11, q := 4217 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4230, p := 11, q := 4219 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4232, p := 3, q := 4229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4234, p := 3, q := 4231 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4236, p := 5, q := 4231 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4238, p := 7, q := 4231 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4240, p := 11, q := 4229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4242, p := 11, q := 4231 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4244, p := 3, q := 4241 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4246, p := 3, q := 4243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4248, p := 5, q := 4243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4250, p := 7, q := 4243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4252, p := 11, q := 4241 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4254, p := 11, q := 4243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4256, p := 3, q := 4253 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4258, p := 5, q := 4253 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4260, p := 7, q := 4253 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4262, p := 3, q := 4259 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4264, p := 3, q := 4261 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4266, p := 5, q := 4261 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4268, p := 7, q := 4261 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4270, p := 11, q := 4259 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4272, p := 11, q := 4261 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4274, p := 3, q := 4271 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4276, p := 3, q := 4273 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4278, p := 5, q := 4273 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4280, p := 7, q := 4273 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4282, p := 11, q := 4271 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4284, p := 11, q := 4273 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4286, p := 3, q := 4283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4288, p := 5, q := 4283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4290, p := 7, q := 4283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4292, p := 3, q := 4289 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4294, p := 5, q := 4289 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4296, p := 7, q := 4289 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4298, p := 37, q := 4261 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4300, p := 3, q := 4297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4302, p := 5, q := 4297 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate4202To4302 : List CertificateEntry :=
  verifiedCertificateEntries certificate4202To4302Verified

theorem certificate4202To4302_covers :
    CertificateCoversBetween 4202 4302 certificate4202To4302 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween4202To4302 :
    GoldbachBetween 4202 4302 :=
  goldbachBetween_of_certificate certificate4202To4302_covers

def certificate4302To4402Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 4304, p := 7, q := 4297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4306, p := 17, q := 4289 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4308, p := 11, q := 4297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4310, p := 13, q := 4297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4312, p := 23, q := 4289 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4314, p := 17, q := 4297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4316, p := 19, q := 4297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4318, p := 29, q := 4289 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4320, p := 23, q := 4297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4322, p := 61, q := 4261 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4324, p := 41, q := 4283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4326, p := 29, q := 4297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4328, p := 31, q := 4297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4330, p := 3, q := 4327 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4332, p := 5, q := 4327 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4334, p := 7, q := 4327 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4336, p := 47, q := 4289 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4338, p := 11, q := 4327 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4340, p := 3, q := 4337 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4342, p := 3, q := 4339 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4344, p := 5, q := 4339 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4346, p := 7, q := 4339 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4348, p := 11, q := 4337 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4350, p := 11, q := 4339 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4352, p := 3, q := 4349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4354, p := 5, q := 4349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4356, p := 7, q := 4349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4358, p := 19, q := 4339 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4360, p := 3, q := 4357 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4362, p := 5, q := 4357 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4364, p := 7, q := 4357 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4366, p := 3, q := 4363 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4368, p := 5, q := 4363 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4370, p := 7, q := 4363 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4372, p := 23, q := 4349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4374, p := 11, q := 4363 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4376, p := 3, q := 4373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4378, p := 5, q := 4373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4380, p := 7, q := 4373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4382, p := 19, q := 4363 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4384, p := 11, q := 4373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4386, p := 13, q := 4373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4388, p := 31, q := 4357 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4390, p := 17, q := 4373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4392, p := 19, q := 4373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4394, p := 3, q := 4391 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4396, p := 5, q := 4391 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4398, p := 7, q := 4391 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4400, p := 3, q := 4397 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4402, p := 5, q := 4397 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate4302To4402 : List CertificateEntry :=
  verifiedCertificateEntries certificate4302To4402Verified

theorem certificate4302To4402_covers :
    CertificateCoversBetween 4302 4402 certificate4302To4402 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween4302To4402 :
    GoldbachBetween 4302 4402 :=
  goldbachBetween_of_certificate certificate4302To4402_covers

def certificate4402To4502Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 4404, p := 7, q := 4397 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4406, p := 43, q := 4363 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4408, p := 11, q := 4397 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4410, p := 13, q := 4397 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4412, p := 3, q := 4409 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4414, p := 5, q := 4409 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4416, p := 7, q := 4409 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4418, p := 61, q := 4357 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4420, p := 11, q := 4409 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4422, p := 13, q := 4409 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4424, p := 3, q := 4421 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4426, p := 3, q := 4423 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4428, p := 5, q := 4423 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4430, p := 7, q := 4423 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4432, p := 11, q := 4421 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4434, p := 11, q := 4423 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4436, p := 13, q := 4423 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4438, p := 17, q := 4421 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4440, p := 17, q := 4423 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4442, p := 19, q := 4423 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4444, p := 3, q := 4441 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4446, p := 5, q := 4441 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4448, p := 7, q := 4441 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4450, p := 3, q := 4447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4452, p := 5, q := 4447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4454, p := 3, q := 4451 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4456, p := 5, q := 4451 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4458, p := 7, q := 4451 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4460, p := 3, q := 4457 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4462, p := 5, q := 4457 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4464, p := 7, q := 4457 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4466, p := 3, q := 4463 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4468, p := 5, q := 4463 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4470, p := 7, q := 4463 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4472, p := 31, q := 4441 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4474, p := 11, q := 4463 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4476, p := 13, q := 4463 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4478, p := 31, q := 4447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4480, p := 17, q := 4463 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4482, p := 19, q := 4463 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4484, p := 3, q := 4481 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4486, p := 3, q := 4483 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4488, p := 5, q := 4483 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4490, p := 7, q := 4483 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4492, p := 11, q := 4481 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4494, p := 11, q := 4483 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4496, p := 3, q := 4493 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4498, p := 5, q := 4493 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4500, p := 7, q := 4493 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4502, p := 19, q := 4483 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate4402To4502 : List CertificateEntry :=
  verifiedCertificateEntries certificate4402To4502Verified

theorem certificate4402To4502_covers :
    CertificateCoversBetween 4402 4502 certificate4402To4502 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween4402To4502 :
    GoldbachBetween 4402 4502 :=
  goldbachBetween_of_certificate certificate4402To4502_covers

def certificate4502To4602Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 4504, p := 11, q := 4493 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4506, p := 13, q := 4493 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4508, p := 61, q := 4447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4510, p := 3, q := 4507 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4512, p := 5, q := 4507 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4514, p := 7, q := 4507 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4516, p := 3, q := 4513 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4518, p := 5, q := 4513 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4520, p := 3, q := 4517 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4522, p := 3, q := 4519 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4524, p := 5, q := 4519 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4526, p := 3, q := 4523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4528, p := 5, q := 4523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4530, p := 7, q := 4523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4532, p := 13, q := 4519 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4534, p := 11, q := 4523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4536, p := 13, q := 4523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4538, p := 19, q := 4519 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4540, p := 17, q := 4523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4542, p := 19, q := 4523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4544, p := 31, q := 4513 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4546, p := 23, q := 4523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4548, p := 29, q := 4519 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4550, p := 3, q := 4547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4552, p := 3, q := 4549 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4554, p := 5, q := 4549 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4556, p := 7, q := 4549 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4558, p := 11, q := 4547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4560, p := 11, q := 4549 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4562, p := 13, q := 4549 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4564, p := 3, q := 4561 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4566, p := 5, q := 4561 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4568, p := 7, q := 4561 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4570, p := 3, q := 4567 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4572, p := 5, q := 4567 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4574, p := 7, q := 4567 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4576, p := 29, q := 4547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4578, p := 11, q := 4567 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4580, p := 13, q := 4567 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4582, p := 59, q := 4523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4584, p := 17, q := 4567 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4586, p := 3, q := 4583 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4588, p := 5, q := 4583 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4590, p := 7, q := 4583 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4592, p := 31, q := 4561 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4594, p := 3, q := 4591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4596, p := 5, q := 4591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4598, p := 7, q := 4591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4600, p := 3, q := 4597 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4602, p := 5, q := 4597 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate4502To4602 : List CertificateEntry :=
  verifiedCertificateEntries certificate4502To4602Verified

theorem certificate4502To4602_covers :
    CertificateCoversBetween 4502 4602 certificate4502To4602 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween4502To4602 :
    GoldbachBetween 4502 4602 :=
  goldbachBetween_of_certificate certificate4502To4602_covers

def certificate4602To4702Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 4604, p := 7, q := 4597 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4606, p := 3, q := 4603 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4608, p := 5, q := 4603 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4610, p := 7, q := 4603 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4612, p := 29, q := 4583 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4614, p := 11, q := 4603 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4616, p := 13, q := 4603 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4618, p := 71, q := 4547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4620, p := 17, q := 4603 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4622, p := 19, q := 4603 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4624, p := 3, q := 4621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4626, p := 5, q := 4621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4628, p := 7, q := 4621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4630, p := 47, q := 4583 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4632, p := 11, q := 4621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4634, p := 13, q := 4621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4636, p := 53, q := 4583 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4638, p := 17, q := 4621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4640, p := 3, q := 4637 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4642, p := 3, q := 4639 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4644, p := 5, q := 4639 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4646, p := 3, q := 4643 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4648, p := 5, q := 4643 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4650, p := 7, q := 4643 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4652, p := 3, q := 4649 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4654, p := 3, q := 4651 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4656, p := 5, q := 4651 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4658, p := 7, q := 4651 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4660, p := 3, q := 4657 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4662, p := 5, q := 4657 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4664, p := 7, q := 4657 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4666, p := 3, q := 4663 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4668, p := 5, q := 4663 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4670, p := 7, q := 4663 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4672, p := 23, q := 4649 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4674, p := 11, q := 4663 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4676, p := 3, q := 4673 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4678, p := 5, q := 4673 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4680, p := 7, q := 4673 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4682, p := 3, q := 4679 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4684, p := 5, q := 4679 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4686, p := 7, q := 4679 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4688, p := 31, q := 4657 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4690, p := 11, q := 4679 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4692, p := 13, q := 4679 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4694, p := 3, q := 4691 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4696, p := 5, q := 4691 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4698, p := 7, q := 4691 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4700, p := 37, q := 4663 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4702, p := 11, q := 4691 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate4602To4702 : List CertificateEntry :=
  verifiedCertificateEntries certificate4602To4702Verified

theorem certificate4602To4702_covers :
    CertificateCoversBetween 4602 4702 certificate4602To4702 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween4602To4702 :
    GoldbachBetween 4602 4702 :=
  goldbachBetween_of_certificate certificate4602To4702_covers

def certificate4702To4802Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 4704, p := 13, q := 4691 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4706, p := 3, q := 4703 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4708, p := 5, q := 4703 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4710, p := 7, q := 4703 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4712, p := 61, q := 4651 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4714, p := 11, q := 4703 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4716, p := 13, q := 4703 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4718, p := 61, q := 4657 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4720, p := 17, q := 4703 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4722, p := 19, q := 4703 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4724, p := 3, q := 4721 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4726, p := 3, q := 4723 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4728, p := 5, q := 4723 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4730, p := 7, q := 4723 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4732, p := 3, q := 4729 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4734, p := 5, q := 4729 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4736, p := 3, q := 4733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4738, p := 5, q := 4733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4740, p := 7, q := 4733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4742, p := 13, q := 4729 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4744, p := 11, q := 4733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4746, p := 13, q := 4733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4748, p := 19, q := 4729 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4750, p := 17, q := 4733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4752, p := 19, q := 4733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4754, p := 3, q := 4751 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4756, p := 5, q := 4751 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4758, p := 7, q := 4751 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4760, p := 31, q := 4729 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4762, p := 3, q := 4759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4764, p := 5, q := 4759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4766, p := 7, q := 4759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4768, p := 17, q := 4751 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4770, p := 11, q := 4759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4772, p := 13, q := 4759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4774, p := 23, q := 4751 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4776, p := 17, q := 4759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4778, p := 19, q := 4759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4780, p := 29, q := 4751 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4782, p := 23, q := 4759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4784, p := 61, q := 4723 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4786, p := 3, q := 4783 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4788, p := 5, q := 4783 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4790, p := 3, q := 4787 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4792, p := 3, q := 4789 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4794, p := 5, q := 4789 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4796, p := 3, q := 4793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4798, p := 5, q := 4793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4800, p := 7, q := 4793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4802, p := 3, q := 4799 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate4702To4802 : List CertificateEntry :=
  verifiedCertificateEntries certificate4702To4802Verified

theorem certificate4702To4802_covers :
    CertificateCoversBetween 4702 4802 certificate4702To4802 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween4702To4802 :
    GoldbachBetween 4702 4802 :=
  goldbachBetween_of_certificate certificate4702To4802_covers

def certificate4802To4902Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 4804, p := 3, q := 4801 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4806, p := 5, q := 4801 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4808, p := 7, q := 4801 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4810, p := 11, q := 4799 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4812, p := 11, q := 4801 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4814, p := 13, q := 4801 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4816, p := 3, q := 4813 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4818, p := 5, q := 4813 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4820, p := 3, q := 4817 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4822, p := 5, q := 4817 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4824, p := 7, q := 4817 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4826, p := 13, q := 4813 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4828, p := 11, q := 4817 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4830, p := 13, q := 4817 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4832, p := 19, q := 4813 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4834, p := 3, q := 4831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4836, p := 5, q := 4831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4838, p := 7, q := 4831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4840, p := 23, q := 4817 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4842, p := 11, q := 4831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4844, p := 13, q := 4831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4846, p := 29, q := 4817 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4848, p := 17, q := 4831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4850, p := 19, q := 4831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4852, p := 53, q := 4799 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4854, p := 23, q := 4831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4856, p := 43, q := 4813 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4858, p := 41, q := 4817 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4860, p := 29, q := 4831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4862, p := 31, q := 4831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4864, p := 3, q := 4861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4866, p := 5, q := 4861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4868, p := 7, q := 4861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4870, p := 53, q := 4817 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4872, p := 11, q := 4861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4874, p := 3, q := 4871 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4876, p := 5, q := 4871 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4878, p := 7, q := 4871 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4880, p := 3, q := 4877 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4882, p := 5, q := 4877 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4884, p := 7, q := 4877 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4886, p := 73, q := 4813 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4888, p := 11, q := 4877 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4890, p := 13, q := 4877 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4892, p := 3, q := 4889 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4894, p := 5, q := 4889 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4896, p := 7, q := 4889 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4898, p := 37, q := 4861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4900, p := 11, q := 4889 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4902, p := 13, q := 4889 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate4802To4902 : List CertificateEntry :=
  verifiedCertificateEntries certificate4802To4902Verified

theorem certificate4802To4902_covers :
    CertificateCoversBetween 4802 4902 certificate4802To4902 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween4802To4902 :
    GoldbachBetween 4802 4902 :=
  goldbachBetween_of_certificate certificate4802To4902_covers

def certificate4902To5002Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 4904, p := 43, q := 4861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4906, p := 3, q := 4903 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4908, p := 5, q := 4903 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4910, p := 7, q := 4903 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4912, p := 3, q := 4909 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4914, p := 5, q := 4909 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4916, p := 7, q := 4909 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4918, p := 29, q := 4889 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4920, p := 11, q := 4909 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4922, p := 3, q := 4919 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4924, p := 5, q := 4919 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4926, p := 7, q := 4919 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4928, p := 19, q := 4909 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4930, p := 11, q := 4919 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4932, p := 13, q := 4919 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4934, p := 3, q := 4931 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4936, p := 3, q := 4933 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4938, p := 5, q := 4933 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4940, p := 3, q := 4937 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4942, p := 5, q := 4937 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4944, p := 7, q := 4937 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4946, p := 3, q := 4943 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4948, p := 5, q := 4943 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4950, p := 7, q := 4943 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4952, p := 19, q := 4933 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4954, p := 3, q := 4951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4956, p := 5, q := 4951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4958, p := 7, q := 4951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4960, p := 3, q := 4957 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4962, p := 5, q := 4957 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4964, p := 7, q := 4957 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4966, p := 23, q := 4943 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4968, p := 11, q := 4957 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4970, p := 3, q := 4967 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4972, p := 3, q := 4969 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4974, p := 5, q := 4969 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4976, p := 3, q := 4973 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4978, p := 5, q := 4973 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4980, p := 7, q := 4973 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4982, p := 13, q := 4969 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4984, p := 11, q := 4973 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4986, p := 13, q := 4973 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4988, p := 19, q := 4969 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4990, p := 3, q := 4987 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4992, p := 5, q := 4987 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4994, p := 7, q := 4987 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4996, p := 3, q := 4993 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 4998, p := 5, q := 4993 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5000, p := 7, q := 4993 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5002, p := 3, q := 4999 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate4902To5002 : List CertificateEntry :=
  verifiedCertificateEntries certificate4902To5002Verified

theorem certificate4902To5002_covers :
    CertificateCoversBetween 4902 5002 certificate4902To5002 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween4902To5002 :
    GoldbachBetween 4902 5002 :=
  goldbachBetween_of_certificate certificate4902To5002_covers

def certificate5002To5102Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 5004, p := 5, q := 4999 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5006, p := 3, q := 5003 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5008, p := 5, q := 5003 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5010, p := 7, q := 5003 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5012, p := 3, q := 5009 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5014, p := 3, q := 5011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5016, p := 5, q := 5011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5018, p := 7, q := 5011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5020, p := 11, q := 5009 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5022, p := 11, q := 5011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5024, p := 3, q := 5021 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5026, p := 3, q := 5023 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5028, p := 5, q := 5023 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5030, p := 7, q := 5023 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5032, p := 11, q := 5021 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5034, p := 11, q := 5023 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5036, p := 13, q := 5023 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5038, p := 17, q := 5021 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5040, p := 17, q := 5023 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5042, p := 3, q := 5039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5044, p := 5, q := 5039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5046, p := 7, q := 5039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5048, p := 37, q := 5011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5050, p := 11, q := 5039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5052, p := 13, q := 5039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5054, p := 3, q := 5051 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5056, p := 5, q := 5051 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5058, p := 7, q := 5051 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5060, p := 37, q := 5023 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5062, p := 3, q := 5059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5064, p := 5, q := 5059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5066, p := 7, q := 5059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5068, p := 17, q := 5051 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5070, p := 11, q := 5059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5072, p := 13, q := 5059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5074, p := 23, q := 5051 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5076, p := 17, q := 5059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5078, p := 19, q := 5059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5080, p := 3, q := 5077 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5082, p := 5, q := 5077 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5084, p := 3, q := 5081 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5086, p := 5, q := 5081 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5088, p := 7, q := 5081 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5090, p := 3, q := 5087 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5092, p := 5, q := 5087 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5094, p := 7, q := 5087 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5096, p := 19, q := 5077 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5098, p := 11, q := 5087 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5100, p := 13, q := 5087 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5102, p := 3, q := 5099 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate5002To5102 : List CertificateEntry :=
  verifiedCertificateEntries certificate5002To5102Verified

theorem certificate5002To5102_covers :
    CertificateCoversBetween 5002 5102 certificate5002To5102 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween5002To5102 :
    GoldbachBetween 5002 5102 :=
  goldbachBetween_of_certificate certificate5002To5102_covers

def certificate5102To5202Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 5104, p := 3, q := 5101 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5106, p := 5, q := 5101 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5108, p := 7, q := 5101 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5110, p := 3, q := 5107 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5112, p := 5, q := 5107 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5114, p := 7, q := 5107 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5116, p := 3, q := 5113 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5118, p := 5, q := 5113 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5120, p := 7, q := 5113 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5122, p := 3, q := 5119 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5124, p := 5, q := 5119 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5126, p := 7, q := 5119 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5128, p := 29, q := 5099 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5130, p := 11, q := 5119 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5132, p := 13, q := 5119 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5134, p := 47, q := 5087 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5136, p := 17, q := 5119 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5138, p := 19, q := 5119 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5140, p := 41, q := 5099 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5142, p := 23, q := 5119 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5144, p := 31, q := 5113 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5146, p := 47, q := 5099 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5148, p := 29, q := 5119 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5150, p := 3, q := 5147 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5152, p := 5, q := 5147 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5154, p := 7, q := 5147 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5156, p := 3, q := 5153 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5158, p := 5, q := 5153 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5160, p := 7, q := 5153 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5162, p := 43, q := 5119 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5164, p := 11, q := 5153 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5166, p := 13, q := 5153 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5168, p := 61, q := 5107 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5170, p := 3, q := 5167 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5172, p := 5, q := 5167 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5174, p := 3, q := 5171 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5176, p := 5, q := 5171 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5178, p := 7, q := 5171 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5180, p := 13, q := 5167 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5182, p := 3, q := 5179 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5184, p := 5, q := 5179 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5186, p := 7, q := 5179 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5188, p := 17, q := 5171 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5190, p := 11, q := 5179 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5192, p := 3, q := 5189 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5194, p := 5, q := 5189 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5196, p := 7, q := 5189 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5198, p := 19, q := 5179 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5200, p := 3, q := 5197 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5202, p := 5, q := 5197 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate5102To5202 : List CertificateEntry :=
  verifiedCertificateEntries certificate5102To5202Verified

theorem certificate5102To5202_covers :
    CertificateCoversBetween 5102 5202 certificate5102To5202 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween5102To5202 :
    GoldbachBetween 5102 5202 :=
  goldbachBetween_of_certificate certificate5102To5202_covers

def certificate5202To5302Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 5204, p := 7, q := 5197 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5206, p := 17, q := 5189 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5208, p := 11, q := 5197 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5210, p := 13, q := 5197 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5212, p := 3, q := 5209 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5214, p := 5, q := 5209 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5216, p := 7, q := 5209 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5218, p := 29, q := 5189 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5220, p := 11, q := 5209 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5222, p := 13, q := 5209 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5224, p := 53, q := 5171 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5226, p := 17, q := 5209 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5228, p := 19, q := 5209 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5230, p := 3, q := 5227 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5232, p := 5, q := 5227 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5234, p := 3, q := 5231 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5236, p := 3, q := 5233 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5238, p := 5, q := 5233 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5240, p := 3, q := 5237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5242, p := 5, q := 5237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5244, p := 7, q := 5237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5246, p := 13, q := 5233 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5248, p := 11, q := 5237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5250, p := 13, q := 5237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5252, p := 19, q := 5233 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5254, p := 17, q := 5237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5256, p := 19, q := 5237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5258, p := 31, q := 5227 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5260, p := 23, q := 5237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5262, p := 29, q := 5233 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5264, p := 3, q := 5261 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5266, p := 5, q := 5261 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5268, p := 7, q := 5261 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5270, p := 37, q := 5233 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5272, p := 11, q := 5261 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5274, p := 13, q := 5261 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5276, p := 3, q := 5273 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5278, p := 5, q := 5273 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5280, p := 7, q := 5273 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5282, p := 3, q := 5279 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5284, p := 3, q := 5281 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5286, p := 5, q := 5281 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5288, p := 7, q := 5281 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5290, p := 11, q := 5279 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5292, p := 11, q := 5281 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5294, p := 13, q := 5281 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5296, p := 17, q := 5279 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5298, p := 17, q := 5281 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5300, p := 3, q := 5297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5302, p := 5, q := 5297 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate5202To5302 : List CertificateEntry :=
  verifiedCertificateEntries certificate5202To5302Verified

theorem certificate5202To5302_covers :
    CertificateCoversBetween 5202 5302 certificate5202To5302 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween5202To5302 :
    GoldbachBetween 5202 5302 :=
  goldbachBetween_of_certificate certificate5202To5302_covers

def certificate5302To5402Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 5304, p := 7, q := 5297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5306, p := 3, q := 5303 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5308, p := 5, q := 5303 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5310, p := 7, q := 5303 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5312, p := 3, q := 5309 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5314, p := 5, q := 5309 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5316, p := 7, q := 5309 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5318, p := 37, q := 5281 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5320, p := 11, q := 5309 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5322, p := 13, q := 5309 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5324, p := 43, q := 5281 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5326, p := 3, q := 5323 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5328, p := 5, q := 5323 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5330, p := 7, q := 5323 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5332, p := 23, q := 5309 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5334, p := 11, q := 5323 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5336, p := 3, q := 5333 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5338, p := 5, q := 5333 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5340, p := 7, q := 5333 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5342, p := 19, q := 5323 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5344, p := 11, q := 5333 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5346, p := 13, q := 5333 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5348, p := 67, q := 5281 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5350, p := 3, q := 5347 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5352, p := 5, q := 5347 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5354, p := 3, q := 5351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5356, p := 5, q := 5351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5358, p := 7, q := 5351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5360, p := 13, q := 5347 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5362, p := 11, q := 5351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5364, p := 13, q := 5351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5366, p := 19, q := 5347 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5368, p := 17, q := 5351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5370, p := 19, q := 5351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5372, p := 139, q := 5233 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5374, p := 23, q := 5351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5376, p := 29, q := 5347 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5378, p := 31, q := 5347 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5380, p := 29, q := 5351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5382, p := 31, q := 5351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5384, p := 3, q := 5381 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5386, p := 5, q := 5381 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5388, p := 7, q := 5381 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5390, p := 3, q := 5387 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5392, p := 5, q := 5387 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5394, p := 7, q := 5387 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5396, p := 3, q := 5393 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5398, p := 5, q := 5393 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5400, p := 7, q := 5393 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5402, p := 3, q := 5399 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate5302To5402 : List CertificateEntry :=
  verifiedCertificateEntries certificate5302To5402Verified

theorem certificate5302To5402_covers :
    CertificateCoversBetween 5302 5402 certificate5302To5402 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween5302To5402 :
    GoldbachBetween 5302 5402 :=
  goldbachBetween_of_certificate certificate5302To5402_covers

def certificate5402To5502Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 5404, p := 5, q := 5399 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5406, p := 7, q := 5399 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5408, p := 61, q := 5347 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5410, p := 3, q := 5407 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5412, p := 5, q := 5407 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5414, p := 7, q := 5407 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5416, p := 3, q := 5413 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5418, p := 5, q := 5413 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5420, p := 3, q := 5417 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5422, p := 3, q := 5419 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5424, p := 5, q := 5419 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5426, p := 7, q := 5419 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5428, p := 11, q := 5417 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5430, p := 11, q := 5419 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5432, p := 13, q := 5419 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5434, p := 3, q := 5431 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5436, p := 5, q := 5431 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5438, p := 7, q := 5431 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5440, p := 3, q := 5437 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5442, p := 5, q := 5437 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5444, p := 3, q := 5441 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5446, p := 3, q := 5443 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5448, p := 5, q := 5443 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5450, p := 7, q := 5443 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5452, p := 3, q := 5449 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5454, p := 5, q := 5449 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5456, p := 7, q := 5449 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5458, p := 17, q := 5441 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5460, p := 11, q := 5449 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5462, p := 13, q := 5449 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5464, p := 23, q := 5441 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5466, p := 17, q := 5449 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5468, p := 19, q := 5449 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5470, p := 29, q := 5441 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5472, p := 23, q := 5449 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5474, p := 3, q := 5471 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5476, p := 5, q := 5471 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5478, p := 7, q := 5471 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5480, p := 3, q := 5477 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5482, p := 3, q := 5479 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5484, p := 5, q := 5479 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5486, p := 3, q := 5483 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5488, p := 5, q := 5483 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5490, p := 7, q := 5483 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5492, p := 13, q := 5479 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5494, p := 11, q := 5483 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5496, p := 13, q := 5483 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5498, p := 19, q := 5479 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5500, p := 17, q := 5483 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5502, p := 19, q := 5483 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate5402To5502 : List CertificateEntry :=
  verifiedCertificateEntries certificate5402To5502Verified

theorem certificate5402To5502_covers :
    CertificateCoversBetween 5402 5502 certificate5402To5502 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween5402To5502 :
    GoldbachBetween 5402 5502 :=
  goldbachBetween_of_certificate certificate5402To5502_covers

def certificate5502To5602Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 5504, p := 3, q := 5501 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5506, p := 3, q := 5503 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5508, p := 5, q := 5503 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5510, p := 3, q := 5507 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5512, p := 5, q := 5507 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5514, p := 7, q := 5507 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5516, p := 13, q := 5503 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5518, p := 11, q := 5507 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5520, p := 13, q := 5507 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5522, p := 3, q := 5519 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5524, p := 3, q := 5521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5526, p := 5, q := 5521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5528, p := 7, q := 5521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5530, p := 3, q := 5527 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5532, p := 5, q := 5527 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5534, p := 3, q := 5531 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5536, p := 5, q := 5531 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5538, p := 7, q := 5531 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5540, p := 13, q := 5527 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5542, p := 11, q := 5531 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5544, p := 13, q := 5531 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5546, p := 19, q := 5527 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5548, p := 17, q := 5531 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5550, p := 19, q := 5531 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5552, p := 31, q := 5521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5554, p := 23, q := 5531 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5556, p := 29, q := 5527 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5558, p := 31, q := 5527 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5560, p := 3, q := 5557 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5562, p := 5, q := 5557 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5564, p := 7, q := 5557 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5566, p := 3, q := 5563 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5568, p := 5, q := 5563 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5570, p := 7, q := 5563 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5572, p := 3, q := 5569 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5574, p := 5, q := 5569 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5576, p := 3, q := 5573 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5578, p := 5, q := 5573 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5580, p := 7, q := 5573 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5582, p := 13, q := 5569 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5584, p := 3, q := 5581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5586, p := 5, q := 5581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5588, p := 7, q := 5581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5590, p := 17, q := 5573 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5592, p := 11, q := 5581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5594, p := 3, q := 5591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5596, p := 5, q := 5591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5598, p := 7, q := 5591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5600, p := 19, q := 5581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5602, p := 11, q := 5591 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate5502To5602 : List CertificateEntry :=
  verifiedCertificateEntries certificate5502To5602Verified

theorem certificate5502To5602_covers :
    CertificateCoversBetween 5502 5602 certificate5502To5602 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween5502To5602 :
    GoldbachBetween 5502 5602 :=
  goldbachBetween_of_certificate certificate5502To5602_covers

def certificate5602To5702Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 5604, p := 13, q := 5591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5606, p := 37, q := 5569 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5608, p := 17, q := 5591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5610, p := 19, q := 5591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5612, p := 31, q := 5581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5614, p := 23, q := 5591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5616, p := 43, q := 5573 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5618, p := 37, q := 5581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5620, p := 29, q := 5591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5622, p := 31, q := 5591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5624, p := 43, q := 5581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5626, p := 3, q := 5623 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5628, p := 5, q := 5623 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5630, p := 7, q := 5623 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5632, p := 41, q := 5591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5634, p := 11, q := 5623 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5636, p := 13, q := 5623 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5638, p := 47, q := 5591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5640, p := 17, q := 5623 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5642, p := 3, q := 5639 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5644, p := 3, q := 5641 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5646, p := 5, q := 5641 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5648, p := 7, q := 5641 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5650, p := 3, q := 5647 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5652, p := 5, q := 5647 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5654, p := 3, q := 5651 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5656, p := 3, q := 5653 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5658, p := 5, q := 5653 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5660, p := 3, q := 5657 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5662, p := 3, q := 5659 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5664, p := 5, q := 5659 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5666, p := 7, q := 5659 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5668, p := 11, q := 5657 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5670, p := 11, q := 5659 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5672, p := 3, q := 5669 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5674, p := 5, q := 5669 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5676, p := 7, q := 5669 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5678, p := 19, q := 5659 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5680, p := 11, q := 5669 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5682, p := 13, q := 5669 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5684, p := 31, q := 5653 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5686, p := 3, q := 5683 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5688, p := 5, q := 5683 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5690, p := 7, q := 5683 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5692, p := 3, q := 5689 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5694, p := 5, q := 5689 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5696, p := 3, q := 5693 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5698, p := 5, q := 5693 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5700, p := 7, q := 5693 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5702, p := 13, q := 5689 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate5602To5702 : List CertificateEntry :=
  verifiedCertificateEntries certificate5602To5702Verified

theorem certificate5602To5702_covers :
    CertificateCoversBetween 5602 5702 certificate5602To5702 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween5602To5702 :
    GoldbachBetween 5602 5702 :=
  goldbachBetween_of_certificate certificate5602To5702_covers

def certificate5702To5802Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 5704, p := 3, q := 5701 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5706, p := 5, q := 5701 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5708, p := 7, q := 5701 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5710, p := 17, q := 5693 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5712, p := 11, q := 5701 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5714, p := 3, q := 5711 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5716, p := 5, q := 5711 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5718, p := 7, q := 5711 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5720, p := 3, q := 5717 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5722, p := 5, q := 5717 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5724, p := 7, q := 5717 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5726, p := 37, q := 5689 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5728, p := 11, q := 5717 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5730, p := 13, q := 5717 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5732, p := 31, q := 5701 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5734, p := 17, q := 5717 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5736, p := 19, q := 5717 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5738, p := 37, q := 5701 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5740, p := 3, q := 5737 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5742, p := 5, q := 5737 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5744, p := 3, q := 5741 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5746, p := 3, q := 5743 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5748, p := 5, q := 5743 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5750, p := 7, q := 5743 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5752, p := 3, q := 5749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5754, p := 5, q := 5749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5756, p := 7, q := 5749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5758, p := 17, q := 5741 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5760, p := 11, q := 5749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5762, p := 13, q := 5749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5764, p := 23, q := 5741 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5766, p := 17, q := 5749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5768, p := 19, q := 5749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5770, p := 29, q := 5741 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5772, p := 23, q := 5749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5774, p := 31, q := 5743 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5776, p := 59, q := 5717 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5778, p := 29, q := 5749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5780, p := 31, q := 5749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5782, p := 3, q := 5779 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5784, p := 5, q := 5779 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5786, p := 3, q := 5783 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5788, p := 5, q := 5783 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5790, p := 7, q := 5783 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5792, p := 13, q := 5779 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5794, p := 3, q := 5791 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5796, p := 5, q := 5791 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5798, p := 7, q := 5791 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5800, p := 17, q := 5783 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5802, p := 11, q := 5791 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate5702To5802 : List CertificateEntry :=
  verifiedCertificateEntries certificate5702To5802Verified

theorem certificate5702To5802_covers :
    CertificateCoversBetween 5702 5802 certificate5702To5802 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween5702To5802 :
    GoldbachBetween 5702 5802 :=
  goldbachBetween_of_certificate certificate5702To5802_covers

def certificate5802To5902Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 5804, p := 3, q := 5801 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5806, p := 5, q := 5801 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5808, p := 7, q := 5801 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5810, p := 3, q := 5807 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5812, p := 5, q := 5807 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5814, p := 7, q := 5807 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5816, p := 3, q := 5813 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5818, p := 5, q := 5813 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5820, p := 7, q := 5813 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5822, p := 31, q := 5791 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5824, p := 3, q := 5821 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5826, p := 5, q := 5821 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5828, p := 7, q := 5821 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5830, p := 3, q := 5827 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5832, p := 5, q := 5827 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5834, p := 7, q := 5827 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5836, p := 23, q := 5813 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5838, p := 11, q := 5827 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5840, p := 13, q := 5827 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5842, p := 3, q := 5839 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5844, p := 5, q := 5839 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5846, p := 3, q := 5843 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5848, p := 5, q := 5843 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5850, p := 7, q := 5843 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5852, p := 3, q := 5849 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5854, p := 3, q := 5851 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5856, p := 5, q := 5851 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5858, p := 7, q := 5851 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5860, p := 3, q := 5857 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5862, p := 5, q := 5857 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5864, p := 3, q := 5861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5866, p := 5, q := 5861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5868, p := 7, q := 5861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5870, p := 3, q := 5867 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5872, p := 3, q := 5869 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5874, p := 5, q := 5869 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5876, p := 7, q := 5869 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5878, p := 11, q := 5867 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5880, p := 11, q := 5869 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5882, p := 3, q := 5879 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5884, p := 3, q := 5881 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5886, p := 5, q := 5881 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5888, p := 7, q := 5881 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5890, p := 11, q := 5879 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5892, p := 11, q := 5881 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5894, p := 13, q := 5881 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5896, p := 17, q := 5879 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5898, p := 17, q := 5881 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5900, p := 3, q := 5897 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5902, p := 5, q := 5897 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate5802To5902 : List CertificateEntry :=
  verifiedCertificateEntries certificate5802To5902Verified

theorem certificate5802To5902_covers :
    CertificateCoversBetween 5802 5902 certificate5802To5902 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween5802To5902 :
    GoldbachBetween 5802 5902 :=
  goldbachBetween_of_certificate certificate5802To5902_covers

def certificate5902To6002Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 5904, p := 7, q := 5897 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5906, p := 3, q := 5903 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5908, p := 5, q := 5903 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5910, p := 7, q := 5903 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5912, p := 31, q := 5881 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5914, p := 11, q := 5903 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5916, p := 13, q := 5903 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5918, p := 37, q := 5881 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5920, p := 17, q := 5903 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5922, p := 19, q := 5903 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5924, p := 43, q := 5881 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5926, p := 3, q := 5923 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5928, p := 5, q := 5923 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5930, p := 3, q := 5927 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5932, p := 5, q := 5927 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5934, p := 7, q := 5927 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5936, p := 13, q := 5923 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5938, p := 11, q := 5927 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5940, p := 13, q := 5927 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5942, p := 3, q := 5939 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5944, p := 5, q := 5939 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5946, p := 7, q := 5939 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5948, p := 67, q := 5881 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5950, p := 11, q := 5939 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5952, p := 13, q := 5939 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5954, p := 31, q := 5923 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5956, p := 3, q := 5953 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5958, p := 5, q := 5953 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5960, p := 7, q := 5953 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5962, p := 23, q := 5939 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5964, p := 11, q := 5953 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5966, p := 13, q := 5953 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5968, p := 29, q := 5939 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5970, p := 17, q := 5953 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5972, p := 19, q := 5953 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5974, p := 47, q := 5927 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5976, p := 23, q := 5953 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5978, p := 97, q := 5881 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5980, p := 41, q := 5939 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5982, p := 29, q := 5953 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5984, p := 3, q := 5981 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5986, p := 5, q := 5981 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5988, p := 7, q := 5981 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5990, p := 3, q := 5987 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5992, p := 5, q := 5987 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5994, p := 7, q := 5987 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5996, p := 43, q := 5953 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 5998, p := 11, q := 5987 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6000, p := 13, q := 5987 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6002, p := 79, q := 5923 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate5902To6002 : List CertificateEntry :=
  verifiedCertificateEntries certificate5902To6002Verified

theorem certificate5902To6002_covers :
    CertificateCoversBetween 5902 6002 certificate5902To6002 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween5902To6002 :
    GoldbachBetween 5902 6002 :=
  goldbachBetween_of_certificate certificate5902To6002_covers

def certificate6002To6102Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 6004, p := 17, q := 5987 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6006, p := 19, q := 5987 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6008, p := 127, q := 5881 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6010, p := 3, q := 6007 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6012, p := 5, q := 6007 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6014, p := 3, q := 6011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6016, p := 5, q := 6011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6018, p := 7, q := 6011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6020, p := 13, q := 6007 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6022, p := 11, q := 6011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6024, p := 13, q := 6011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6026, p := 19, q := 6007 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6028, p := 17, q := 6011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6030, p := 19, q := 6011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6032, p := 3, q := 6029 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6034, p := 5, q := 6029 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6036, p := 7, q := 6029 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6038, p := 31, q := 6007 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6040, p := 3, q := 6037 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6042, p := 5, q := 6037 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6044, p := 7, q := 6037 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6046, p := 3, q := 6043 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6048, p := 5, q := 6043 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6050, p := 3, q := 6047 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6052, p := 5, q := 6047 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6054, p := 7, q := 6047 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6056, p := 3, q := 6053 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6058, p := 5, q := 6053 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6060, p := 7, q := 6053 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6062, p := 19, q := 6043 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6064, p := 11, q := 6053 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6066, p := 13, q := 6053 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6068, p := 31, q := 6037 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6070, p := 3, q := 6067 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6072, p := 5, q := 6067 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6074, p := 7, q := 6067 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6076, p := 3, q := 6073 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6078, p := 5, q := 6073 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6080, p := 7, q := 6073 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6082, p := 3, q := 6079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6084, p := 5, q := 6079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6086, p := 7, q := 6079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6088, p := 41, q := 6047 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6090, p := 11, q := 6079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6092, p := 3, q := 6089 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6094, p := 3, q := 6091 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6096, p := 5, q := 6091 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6098, p := 7, q := 6091 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6100, p := 11, q := 6089 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6102, p := 11, q := 6091 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate6002To6102 : List CertificateEntry :=
  verifiedCertificateEntries certificate6002To6102Verified

theorem certificate6002To6102_covers :
    CertificateCoversBetween 6002 6102 certificate6002To6102 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween6002To6102 :
    GoldbachBetween 6002 6102 :=
  goldbachBetween_of_certificate certificate6002To6102_covers

def certificate6102To6202Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 6104, p := 3, q := 6101 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6106, p := 5, q := 6101 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6108, p := 7, q := 6101 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6110, p := 19, q := 6091 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6112, p := 11, q := 6101 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6114, p := 13, q := 6101 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6116, p := 3, q := 6113 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6118, p := 5, q := 6113 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6120, p := 7, q := 6113 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6122, p := 31, q := 6091 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6124, p := 3, q := 6121 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6126, p := 5, q := 6121 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6128, p := 7, q := 6121 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6130, p := 17, q := 6113 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6132, p := 11, q := 6121 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6134, p := 3, q := 6131 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6136, p := 3, q := 6133 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6138, p := 5, q := 6133 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6140, p := 7, q := 6133 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6142, p := 11, q := 6131 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6144, p := 11, q := 6133 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6146, p := 3, q := 6143 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6148, p := 5, q := 6143 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6150, p := 7, q := 6143 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6152, p := 19, q := 6133 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6154, p := 3, q := 6151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6156, p := 5, q := 6151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6158, p := 7, q := 6151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6160, p := 17, q := 6143 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6162, p := 11, q := 6151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6164, p := 13, q := 6151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6166, p := 3, q := 6163 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6168, p := 5, q := 6163 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6170, p := 7, q := 6163 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6172, p := 29, q := 6143 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6174, p := 11, q := 6163 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6176, p := 3, q := 6173 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6178, p := 5, q := 6173 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6180, p := 7, q := 6173 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6182, p := 19, q := 6163 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6184, p := 11, q := 6173 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6186, p := 13, q := 6173 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6188, p := 37, q := 6151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6190, p := 17, q := 6173 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6192, p := 19, q := 6173 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6194, p := 31, q := 6163 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6196, p := 23, q := 6173 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6198, p := 47, q := 6151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6200, p := 3, q := 6197 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6202, p := 3, q := 6199 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate6102To6202 : List CertificateEntry :=
  verifiedCertificateEntries certificate6102To6202Verified

theorem certificate6102To6202_covers :
    CertificateCoversBetween 6102 6202 certificate6102To6202 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween6102To6202 :
    GoldbachBetween 6102 6202 :=
  goldbachBetween_of_certificate certificate6102To6202_covers

def certificate6202To6302Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 6204, p := 5, q := 6199 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6206, p := 3, q := 6203 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6208, p := 5, q := 6203 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6210, p := 7, q := 6203 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6212, p := 13, q := 6199 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6214, p := 3, q := 6211 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6216, p := 5, q := 6211 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6218, p := 7, q := 6211 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6220, p := 3, q := 6217 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6222, p := 5, q := 6217 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6224, p := 3, q := 6221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6226, p := 5, q := 6221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6228, p := 7, q := 6221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6230, p := 13, q := 6217 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6232, p := 3, q := 6229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6234, p := 5, q := 6229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6236, p := 7, q := 6229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6238, p := 17, q := 6221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6240, p := 11, q := 6229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6242, p := 13, q := 6229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6244, p := 23, q := 6221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6246, p := 17, q := 6229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6248, p := 19, q := 6229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6250, p := 3, q := 6247 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6252, p := 5, q := 6247 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6254, p := 7, q := 6247 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6256, p := 53, q := 6203 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6258, p := 11, q := 6247 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6260, p := 3, q := 6257 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6262, p := 5, q := 6257 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6264, p := 7, q := 6257 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6266, p := 3, q := 6263 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6268, p := 5, q := 6263 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6270, p := 7, q := 6263 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6272, p := 3, q := 6269 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6274, p := 3, q := 6271 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6276, p := 5, q := 6271 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6278, p := 7, q := 6271 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6280, p := 3, q := 6277 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6282, p := 5, q := 6277 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6284, p := 7, q := 6277 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6286, p := 17, q := 6269 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6288, p := 11, q := 6277 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6290, p := 3, q := 6287 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6292, p := 5, q := 6287 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6294, p := 7, q := 6287 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6296, p := 19, q := 6277 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6298, p := 11, q := 6287 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6300, p := 13, q := 6287 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6302, p := 3, q := 6299 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate6202To6302 : List CertificateEntry :=
  verifiedCertificateEntries certificate6202To6302Verified

theorem certificate6202To6302_covers :
    CertificateCoversBetween 6202 6302 certificate6202To6302 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween6202To6302 :
    GoldbachBetween 6202 6302 :=
  goldbachBetween_of_certificate certificate6202To6302_covers

def certificate6302To6402Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 6304, p := 3, q := 6301 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6306, p := 5, q := 6301 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6308, p := 7, q := 6301 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6310, p := 11, q := 6299 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6312, p := 11, q := 6301 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6314, p := 3, q := 6311 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6316, p := 5, q := 6311 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6318, p := 7, q := 6311 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6320, p := 3, q := 6317 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6322, p := 5, q := 6317 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6324, p := 7, q := 6317 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6326, p := 3, q := 6323 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6328, p := 5, q := 6323 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6330, p := 7, q := 6323 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6332, p := 3, q := 6329 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6334, p := 5, q := 6329 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6336, p := 7, q := 6329 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6338, p := 37, q := 6301 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6340, p := 3, q := 6337 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6342, p := 5, q := 6337 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6344, p := 7, q := 6337 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6346, p := 3, q := 6343 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6348, p := 5, q := 6343 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6350, p := 7, q := 6343 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6352, p := 23, q := 6329 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6354, p := 11, q := 6343 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6356, p := 3, q := 6353 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6358, p := 5, q := 6353 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6360, p := 7, q := 6353 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6362, p := 3, q := 6359 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6364, p := 3, q := 6361 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6366, p := 5, q := 6361 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6368, p := 7, q := 6361 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6370, p := 3, q := 6367 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6372, p := 5, q := 6367 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6374, p := 7, q := 6367 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6376, p := 3, q := 6373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6378, p := 5, q := 6373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6380, p := 7, q := 6373 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6382, p := 3, q := 6379 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6384, p := 5, q := 6379 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6386, p := 7, q := 6379 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6388, p := 29, q := 6359 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6390, p := 11, q := 6379 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6392, p := 3, q := 6389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6394, p := 5, q := 6389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6396, p := 7, q := 6389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6398, p := 19, q := 6379 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6400, p := 3, q := 6397 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6402, p := 5, q := 6397 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate6302To6402 : List CertificateEntry :=
  verifiedCertificateEntries certificate6302To6402Verified

theorem certificate6302To6402_covers :
    CertificateCoversBetween 6302 6402 certificate6302To6402 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween6302To6402 :
    GoldbachBetween 6302 6402 :=
  goldbachBetween_of_certificate certificate6302To6402_covers

def certificate6402To6502Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 6404, p := 7, q := 6397 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6406, p := 17, q := 6389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6408, p := 11, q := 6397 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6410, p := 13, q := 6397 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6412, p := 23, q := 6389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6414, p := 17, q := 6397 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6416, p := 19, q := 6397 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6418, p := 29, q := 6389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6420, p := 23, q := 6397 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6422, p := 43, q := 6379 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6424, p := 3, q := 6421 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6426, p := 5, q := 6421 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6428, p := 7, q := 6421 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6430, p := 3, q := 6427 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6432, p := 5, q := 6427 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6434, p := 7, q := 6427 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6436, p := 47, q := 6389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6438, p := 11, q := 6427 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6440, p := 13, q := 6427 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6442, p := 53, q := 6389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6444, p := 17, q := 6427 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6446, p := 19, q := 6427 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6448, p := 59, q := 6389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6450, p := 23, q := 6427 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6452, p := 3, q := 6449 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6454, p := 3, q := 6451 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6456, p := 5, q := 6451 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6458, p := 7, q := 6451 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6460, p := 11, q := 6449 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6462, p := 11, q := 6451 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6464, p := 13, q := 6451 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6466, p := 17, q := 6449 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6468, p := 17, q := 6451 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6470, p := 19, q := 6451 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6472, p := 3, q := 6469 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6474, p := 5, q := 6469 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6476, p := 3, q := 6473 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6478, p := 5, q := 6473 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6480, p := 7, q := 6473 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6482, p := 13, q := 6469 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6484, p := 3, q := 6481 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6486, p := 5, q := 6481 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6488, p := 7, q := 6481 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6490, p := 17, q := 6473 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6492, p := 11, q := 6481 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6494, p := 3, q := 6491 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6496, p := 5, q := 6491 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6498, p := 7, q := 6491 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6500, p := 19, q := 6481 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6502, p := 11, q := 6491 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate6402To6502 : List CertificateEntry :=
  verifiedCertificateEntries certificate6402To6502Verified

theorem certificate6402To6502_covers :
    CertificateCoversBetween 6402 6502 certificate6402To6502 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween6402To6502 :
    GoldbachBetween 6402 6502 :=
  goldbachBetween_of_certificate certificate6402To6502_covers

def certificate6502To6602Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 6504, p := 13, q := 6491 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6506, p := 37, q := 6469 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6508, p := 17, q := 6491 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6510, p := 19, q := 6491 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6512, p := 31, q := 6481 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6514, p := 23, q := 6491 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6516, p := 43, q := 6473 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6518, p := 37, q := 6481 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6520, p := 29, q := 6491 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6522, p := 31, q := 6491 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6524, p := 3, q := 6521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6526, p := 5, q := 6521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6528, p := 7, q := 6521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6530, p := 61, q := 6469 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6532, p := 3, q := 6529 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6534, p := 5, q := 6529 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6536, p := 7, q := 6529 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6538, p := 17, q := 6521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6540, p := 11, q := 6529 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6542, p := 13, q := 6529 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6544, p := 23, q := 6521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6546, p := 17, q := 6529 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6548, p := 19, q := 6529 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6550, p := 3, q := 6547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6552, p := 5, q := 6547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6554, p := 3, q := 6551 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6556, p := 3, q := 6553 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6558, p := 5, q := 6553 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6560, p := 7, q := 6553 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6562, p := 11, q := 6551 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6564, p := 11, q := 6553 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6566, p := 3, q := 6563 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6568, p := 5, q := 6563 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6570, p := 7, q := 6563 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6572, p := 3, q := 6569 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6574, p := 3, q := 6571 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6576, p := 5, q := 6571 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6578, p := 7, q := 6571 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6580, p := 3, q := 6577 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6582, p := 5, q := 6577 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6584, p := 3, q := 6581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6586, p := 5, q := 6581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6588, p := 7, q := 6581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6590, p := 13, q := 6577 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6592, p := 11, q := 6581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6594, p := 13, q := 6581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6596, p := 19, q := 6577 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6598, p := 17, q := 6581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6600, p := 19, q := 6581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6602, p := 3, q := 6599 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate6502To6602 : List CertificateEntry :=
  verifiedCertificateEntries certificate6502To6602Verified

theorem certificate6502To6602_covers :
    CertificateCoversBetween 6502 6602 certificate6502To6602 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween6502To6602 :
    GoldbachBetween 6502 6602 :=
  goldbachBetween_of_certificate certificate6502To6602_covers

def certificate6602To6702Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 6604, p := 5, q := 6599 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6606, p := 7, q := 6599 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6608, p := 31, q := 6577 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6610, p := 3, q := 6607 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6612, p := 5, q := 6607 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6614, p := 7, q := 6607 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6616, p := 17, q := 6599 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6618, p := 11, q := 6607 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6620, p := 13, q := 6607 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6622, p := 3, q := 6619 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6624, p := 5, q := 6619 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6626, p := 7, q := 6619 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6628, p := 29, q := 6599 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6630, p := 11, q := 6619 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6632, p := 13, q := 6619 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6634, p := 53, q := 6581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6636, p := 17, q := 6619 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6638, p := 19, q := 6619 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6640, p := 3, q := 6637 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6642, p := 5, q := 6637 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6644, p := 7, q := 6637 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6646, p := 47, q := 6599 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6648, p := 11, q := 6637 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6650, p := 13, q := 6637 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6652, p := 53, q := 6599 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6654, p := 17, q := 6637 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6656, p := 3, q := 6653 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6658, p := 5, q := 6653 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6660, p := 7, q := 6653 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6662, p := 3, q := 6659 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6664, p := 3, q := 6661 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6666, p := 5, q := 6661 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6668, p := 7, q := 6661 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6670, p := 11, q := 6659 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6672, p := 11, q := 6661 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6674, p := 13, q := 6661 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6676, p := 3, q := 6673 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6678, p := 5, q := 6673 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6680, p := 7, q := 6673 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6682, p := 3, q := 6679 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6684, p := 5, q := 6679 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6686, p := 7, q := 6679 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6688, p := 29, q := 6659 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6690, p := 11, q := 6679 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6692, p := 3, q := 6689 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6694, p := 3, q := 6691 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6696, p := 5, q := 6691 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6698, p := 7, q := 6691 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6700, p := 11, q := 6689 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6702, p := 11, q := 6691 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate6602To6702 : List CertificateEntry :=
  verifiedCertificateEntries certificate6602To6702Verified

theorem certificate6602To6702_covers :
    CertificateCoversBetween 6602 6702 certificate6602To6702 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween6602To6702 :
    GoldbachBetween 6602 6702 :=
  goldbachBetween_of_certificate certificate6602To6702_covers

def certificate6702To6802Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 6704, p := 3, q := 6701 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6706, p := 3, q := 6703 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6708, p := 5, q := 6703 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6710, p := 7, q := 6703 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6712, p := 3, q := 6709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6714, p := 5, q := 6709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6716, p := 7, q := 6709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6718, p := 17, q := 6701 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6720, p := 11, q := 6709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6722, p := 3, q := 6719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6724, p := 5, q := 6719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6726, p := 7, q := 6719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6728, p := 19, q := 6709 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6730, p := 11, q := 6719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6732, p := 13, q := 6719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6734, p := 31, q := 6703 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6736, p := 3, q := 6733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6738, p := 5, q := 6733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6740, p := 3, q := 6737 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6742, p := 5, q := 6737 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6744, p := 7, q := 6737 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6746, p := 13, q := 6733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6748, p := 11, q := 6737 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6750, p := 13, q := 6737 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6752, p := 19, q := 6733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6754, p := 17, q := 6737 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6756, p := 19, q := 6737 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6758, p := 67, q := 6691 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6760, p := 23, q := 6737 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6762, p := 29, q := 6733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6764, p := 3, q := 6761 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6766, p := 3, q := 6763 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6768, p := 5, q := 6763 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6770, p := 7, q := 6763 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6772, p := 11, q := 6761 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6774, p := 11, q := 6763 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6776, p := 13, q := 6763 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6778, p := 17, q := 6761 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6780, p := 17, q := 6763 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6782, p := 3, q := 6779 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6784, p := 3, q := 6781 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6786, p := 5, q := 6781 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6788, p := 7, q := 6781 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6790, p := 11, q := 6779 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6792, p := 11, q := 6781 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6794, p := 3, q := 6791 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6796, p := 3, q := 6793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6798, p := 5, q := 6793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6800, p := 7, q := 6793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6802, p := 11, q := 6791 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate6702To6802 : List CertificateEntry :=
  verifiedCertificateEntries certificate6702To6802Verified

theorem certificate6702To6802_covers :
    CertificateCoversBetween 6702 6802 certificate6702To6802 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween6702To6802 :
    GoldbachBetween 6702 6802 :=
  goldbachBetween_of_certificate certificate6702To6802_covers

def certificate6802To6902Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 6804, p := 11, q := 6793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6806, p := 3, q := 6803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6808, p := 5, q := 6803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6810, p := 7, q := 6803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6812, p := 19, q := 6793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6814, p := 11, q := 6803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6816, p := 13, q := 6803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6818, p := 37, q := 6781 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6820, p := 17, q := 6803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6822, p := 19, q := 6803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6824, p := 31, q := 6793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6826, p := 3, q := 6823 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6828, p := 5, q := 6823 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6830, p := 3, q := 6827 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6832, p := 3, q := 6829 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6834, p := 5, q := 6829 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6836, p := 3, q := 6833 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6838, p := 5, q := 6833 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6840, p := 7, q := 6833 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6842, p := 13, q := 6829 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6844, p := 3, q := 6841 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6846, p := 5, q := 6841 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6848, p := 7, q := 6841 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6850, p := 17, q := 6833 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6852, p := 11, q := 6841 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6854, p := 13, q := 6841 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6856, p := 23, q := 6833 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6858, p := 17, q := 6841 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6860, p := 3, q := 6857 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6862, p := 5, q := 6857 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6864, p := 7, q := 6857 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6866, p := 3, q := 6863 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6868, p := 5, q := 6863 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6870, p := 7, q := 6863 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6872, p := 3, q := 6869 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6874, p := 3, q := 6871 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6876, p := 5, q := 6871 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6878, p := 7, q := 6871 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6880, p := 11, q := 6869 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6882, p := 11, q := 6871 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6884, p := 13, q := 6871 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6886, p := 3, q := 6883 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6888, p := 5, q := 6883 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6890, p := 7, q := 6883 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6892, p := 23, q := 6869 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6894, p := 11, q := 6883 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6896, p := 13, q := 6883 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6898, p := 29, q := 6869 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6900, p := 17, q := 6883 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6902, p := 3, q := 6899 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate6802To6902 : List CertificateEntry :=
  verifiedCertificateEntries certificate6802To6902Verified

theorem certificate6802To6902_covers :
    CertificateCoversBetween 6802 6902 certificate6802To6902 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween6802To6902 :
    GoldbachBetween 6802 6902 :=
  goldbachBetween_of_certificate certificate6802To6902_covers

def certificate6902To7002Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 6904, p := 5, q := 6899 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6906, p := 7, q := 6899 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6908, p := 37, q := 6871 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6910, p := 3, q := 6907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6912, p := 5, q := 6907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6914, p := 3, q := 6911 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6916, p := 5, q := 6911 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6918, p := 7, q := 6911 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6920, p := 3, q := 6917 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6922, p := 5, q := 6917 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6924, p := 7, q := 6917 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6926, p := 19, q := 6907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6928, p := 11, q := 6917 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6930, p := 13, q := 6917 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6932, p := 61, q := 6871 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6934, p := 17, q := 6917 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6936, p := 19, q := 6917 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6938, p := 31, q := 6907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6940, p := 23, q := 6917 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6942, p := 31, q := 6911 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6944, p := 37, q := 6907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6946, p := 29, q := 6917 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6948, p := 31, q := 6917 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6950, p := 3, q := 6947 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6952, p := 3, q := 6949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6954, p := 5, q := 6949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6956, p := 7, q := 6949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6958, p := 11, q := 6947 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6960, p := 11, q := 6949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6962, p := 3, q := 6959 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6964, p := 3, q := 6961 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6966, p := 5, q := 6961 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6968, p := 7, q := 6961 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6970, p := 3, q := 6967 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6972, p := 5, q := 6967 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6974, p := 3, q := 6971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6976, p := 5, q := 6971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6978, p := 7, q := 6971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6980, p := 3, q := 6977 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6982, p := 5, q := 6977 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6984, p := 7, q := 6977 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6986, p := 3, q := 6983 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6988, p := 5, q := 6983 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6990, p := 7, q := 6983 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6992, p := 31, q := 6961 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6994, p := 3, q := 6991 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6996, p := 5, q := 6991 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 6998, p := 7, q := 6991 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7000, p := 3, q := 6997 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7002, p := 5, q := 6997 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate6902To7002 : List CertificateEntry :=
  verifiedCertificateEntries certificate6902To7002Verified

theorem certificate6902To7002_covers :
    CertificateCoversBetween 6902 7002 certificate6902To7002 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween6902To7002 :
    GoldbachBetween 6902 7002 :=
  goldbachBetween_of_certificate certificate6902To7002_covers

def certificate7002To7102Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 7004, p := 3, q := 7001 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7006, p := 5, q := 7001 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7008, p := 7, q := 7001 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7010, p := 13, q := 6997 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7012, p := 11, q := 7001 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7014, p := 13, q := 7001 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7016, p := 3, q := 7013 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7018, p := 5, q := 7013 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7020, p := 7, q := 7013 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7022, p := 3, q := 7019 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7024, p := 5, q := 7019 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7026, p := 7, q := 7019 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7028, p := 31, q := 6997 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7030, p := 3, q := 7027 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7032, p := 5, q := 7027 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7034, p := 7, q := 7027 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7036, p := 17, q := 7019 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7038, p := 11, q := 7027 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7040, p := 13, q := 7027 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7042, p := 3, q := 7039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7044, p := 5, q := 7039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7046, p := 3, q := 7043 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7048, p := 5, q := 7043 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7050, p := 7, q := 7043 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7052, p := 13, q := 7039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7054, p := 11, q := 7043 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7056, p := 13, q := 7043 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7058, p := 19, q := 7039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7060, p := 3, q := 7057 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7062, p := 5, q := 7057 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7064, p := 7, q := 7057 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7066, p := 23, q := 7043 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7068, p := 11, q := 7057 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7070, p := 13, q := 7057 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7072, p := 3, q := 7069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7074, p := 5, q := 7069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7076, p := 7, q := 7069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7078, p := 59, q := 7019 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7080, p := 11, q := 7069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7082, p := 3, q := 7079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7084, p := 5, q := 7079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7086, p := 7, q := 7079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7088, p := 19, q := 7069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7090, p := 11, q := 7079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7092, p := 13, q := 7079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7094, p := 37, q := 7057 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7096, p := 17, q := 7079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7098, p := 19, q := 7079 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7100, p := 31, q := 7069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7102, p := 23, q := 7079 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate7002To7102 : List CertificateEntry :=
  verifiedCertificateEntries certificate7002To7102Verified

theorem certificate7002To7102_covers :
    CertificateCoversBetween 7002 7102 certificate7002To7102 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween7002To7102 :
    GoldbachBetween 7002 7102 :=
  goldbachBetween_of_certificate certificate7002To7102_covers

def certificate7102To7202Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 7104, p := 47, q := 7057 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7106, p := 3, q := 7103 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7108, p := 5, q := 7103 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7110, p := 7, q := 7103 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7112, p := 3, q := 7109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7114, p := 5, q := 7109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7116, p := 7, q := 7109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7118, p := 61, q := 7057 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7120, p := 11, q := 7109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7122, p := 13, q := 7109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7124, p := 3, q := 7121 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7126, p := 5, q := 7121 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7128, p := 7, q := 7121 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7130, p := 3, q := 7127 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7132, p := 3, q := 7129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7134, p := 5, q := 7129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7136, p := 7, q := 7129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7138, p := 11, q := 7127 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7140, p := 11, q := 7129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7142, p := 13, q := 7129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7144, p := 17, q := 7127 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7146, p := 17, q := 7129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7148, p := 19, q := 7129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7150, p := 23, q := 7127 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7152, p := 23, q := 7129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7154, p := 3, q := 7151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7156, p := 5, q := 7151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7158, p := 7, q := 7151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7160, p := 31, q := 7129 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7162, p := 3, q := 7159 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7164, p := 5, q := 7159 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7166, p := 7, q := 7159 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7168, p := 17, q := 7151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7170, p := 11, q := 7159 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7172, p := 13, q := 7159 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7174, p := 23, q := 7151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7176, p := 17, q := 7159 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7178, p := 19, q := 7159 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7180, p := 3, q := 7177 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7182, p := 5, q := 7177 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7184, p := 7, q := 7177 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7186, p := 59, q := 7127 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7188, p := 11, q := 7177 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7190, p := 3, q := 7187 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7192, p := 5, q := 7187 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7194, p := 7, q := 7187 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7196, p := 3, q := 7193 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7198, p := 5, q := 7193 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7200, p := 7, q := 7193 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7202, p := 43, q := 7159 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate7102To7202 : List CertificateEntry :=
  verifiedCertificateEntries certificate7102To7202Verified

theorem certificate7102To7202_covers :
    CertificateCoversBetween 7102 7202 certificate7102To7202 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween7102To7202 :
    GoldbachBetween 7102 7202 :=
  goldbachBetween_of_certificate certificate7102To7202_covers

def certificate7202To7302Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 7204, p := 11, q := 7193 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7206, p := 13, q := 7193 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7208, p := 31, q := 7177 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7210, p := 3, q := 7207 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7212, p := 5, q := 7207 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7214, p := 3, q := 7211 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7216, p := 3, q := 7213 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7218, p := 5, q := 7213 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7220, p := 7, q := 7213 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7222, p := 3, q := 7219 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7224, p := 5, q := 7219 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7226, p := 7, q := 7219 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7228, p := 17, q := 7211 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7230, p := 11, q := 7219 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7232, p := 3, q := 7229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7234, p := 5, q := 7229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7236, p := 7, q := 7229 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7238, p := 19, q := 7219 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7240, p := 3, q := 7237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7242, p := 5, q := 7237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7244, p := 7, q := 7237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7246, p := 3, q := 7243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7248, p := 5, q := 7243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7250, p := 3, q := 7247 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7252, p := 5, q := 7247 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7254, p := 7, q := 7247 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7256, p := 3, q := 7253 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7258, p := 5, q := 7253 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7260, p := 7, q := 7253 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7262, p := 19, q := 7243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7264, p := 11, q := 7253 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7266, p := 13, q := 7253 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7268, p := 31, q := 7237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7270, p := 17, q := 7253 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7272, p := 19, q := 7253 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7274, p := 31, q := 7243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7276, p := 23, q := 7253 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7278, p := 31, q := 7247 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7280, p := 37, q := 7243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7282, p := 29, q := 7253 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7284, p := 31, q := 7253 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7286, p := 3, q := 7283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7288, p := 5, q := 7283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7290, p := 7, q := 7283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7292, p := 73, q := 7219 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7294, p := 11, q := 7283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7296, p := 13, q := 7283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7298, p := 61, q := 7237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7300, p := 3, q := 7297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7302, p := 5, q := 7297 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate7202To7302 : List CertificateEntry :=
  verifiedCertificateEntries certificate7202To7302Verified

theorem certificate7202To7302_covers :
    CertificateCoversBetween 7202 7302 certificate7202To7302 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween7202To7302 :
    GoldbachBetween 7202 7302 :=
  goldbachBetween_of_certificate certificate7202To7302_covers

def certificate7302To7402Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 7304, p := 7, q := 7297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7306, p := 23, q := 7283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7308, p := 11, q := 7297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7310, p := 3, q := 7307 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7312, p := 3, q := 7309 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7314, p := 5, q := 7309 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7316, p := 7, q := 7309 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7318, p := 11, q := 7307 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7320, p := 11, q := 7309 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7322, p := 13, q := 7309 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7324, p := 3, q := 7321 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7326, p := 5, q := 7321 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7328, p := 7, q := 7321 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7330, p := 23, q := 7307 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7332, p := 11, q := 7321 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7334, p := 3, q := 7331 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7336, p := 3, q := 7333 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7338, p := 5, q := 7333 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7340, p := 7, q := 7333 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7342, p := 11, q := 7331 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7344, p := 11, q := 7333 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7346, p := 13, q := 7333 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7348, p := 17, q := 7331 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7350, p := 17, q := 7333 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7352, p := 3, q := 7349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7354, p := 3, q := 7351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7356, p := 5, q := 7351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7358, p := 7, q := 7351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7360, p := 11, q := 7349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7362, p := 11, q := 7351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7364, p := 13, q := 7351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7366, p := 17, q := 7349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7368, p := 17, q := 7351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7370, p := 19, q := 7351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7372, p := 3, q := 7369 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7374, p := 5, q := 7369 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7376, p := 7, q := 7369 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7378, p := 29, q := 7349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7380, p := 11, q := 7369 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7382, p := 13, q := 7369 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7384, p := 53, q := 7331 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7386, p := 17, q := 7369 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7388, p := 19, q := 7369 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7390, p := 41, q := 7349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7392, p := 23, q := 7369 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7394, p := 43, q := 7351 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7396, p := 3, q := 7393 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7398, p := 5, q := 7393 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7400, p := 7, q := 7393 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7402, p := 53, q := 7349 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate7302To7402 : List CertificateEntry :=
  verifiedCertificateEntries certificate7302To7402Verified

theorem certificate7302To7402_covers :
    CertificateCoversBetween 7302 7402 certificate7302To7402 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween7302To7402 :
    GoldbachBetween 7302 7402 :=
  goldbachBetween_of_certificate certificate7302To7402_covers

def certificate7402To7502Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 7404, p := 11, q := 7393 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7406, p := 13, q := 7393 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7408, p := 59, q := 7349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7410, p := 17, q := 7393 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7412, p := 19, q := 7393 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7414, p := 3, q := 7411 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7416, p := 5, q := 7411 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7418, p := 7, q := 7411 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7420, p := 3, q := 7417 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7422, p := 5, q := 7417 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7424, p := 7, q := 7417 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7426, p := 173, q := 7253 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7428, p := 11, q := 7417 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7430, p := 13, q := 7417 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7432, p := 83, q := 7349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7434, p := 17, q := 7417 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7436, p := 3, q := 7433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7438, p := 5, q := 7433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7440, p := 7, q := 7433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7442, p := 31, q := 7411 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7444, p := 11, q := 7433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7446, p := 13, q := 7433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7448, p := 31, q := 7417 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7450, p := 17, q := 7433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7452, p := 19, q := 7433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7454, p := 3, q := 7451 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7456, p := 5, q := 7451 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7458, p := 7, q := 7451 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7460, p := 3, q := 7457 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7462, p := 3, q := 7459 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7464, p := 5, q := 7459 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7466, p := 7, q := 7459 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7468, p := 11, q := 7457 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7470, p := 11, q := 7459 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7472, p := 13, q := 7459 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7474, p := 17, q := 7457 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7476, p := 17, q := 7459 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7478, p := 19, q := 7459 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7480, p := 3, q := 7477 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7482, p := 5, q := 7477 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7484, p := 3, q := 7481 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7486, p := 5, q := 7481 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7488, p := 7, q := 7481 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7490, p := 3, q := 7487 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7492, p := 3, q := 7489 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7494, p := 5, q := 7489 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7496, p := 7, q := 7489 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7498, p := 11, q := 7487 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7500, p := 11, q := 7489 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7502, p := 3, q := 7499 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate7402To7502 : List CertificateEntry :=
  verifiedCertificateEntries certificate7402To7502Verified

theorem certificate7402To7502_covers :
    CertificateCoversBetween 7402 7502 certificate7402To7502 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween7402To7502 :
    GoldbachBetween 7402 7502 :=
  goldbachBetween_of_certificate certificate7402To7502_covers

def certificate7502To7602Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 7504, p := 5, q := 7499 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7506, p := 7, q := 7499 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7508, p := 19, q := 7489 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7510, p := 3, q := 7507 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7512, p := 5, q := 7507 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7514, p := 7, q := 7507 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7516, p := 17, q := 7499 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7518, p := 11, q := 7507 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7520, p := 3, q := 7517 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7522, p := 5, q := 7517 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7524, p := 7, q := 7517 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7526, p := 3, q := 7523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7528, p := 5, q := 7523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7530, p := 7, q := 7523 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7532, p := 3, q := 7529 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7534, p := 5, q := 7529 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7536, p := 7, q := 7529 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7538, p := 31, q := 7507 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7540, p := 3, q := 7537 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7542, p := 5, q := 7537 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7544, p := 3, q := 7541 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7546, p := 5, q := 7541 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7548, p := 7, q := 7541 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7550, p := 3, q := 7547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7552, p := 3, q := 7549 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7554, p := 5, q := 7549 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7556, p := 7, q := 7549 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7558, p := 11, q := 7547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7560, p := 11, q := 7549 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7562, p := 3, q := 7559 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7564, p := 3, q := 7561 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7566, p := 5, q := 7561 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7568, p := 7, q := 7561 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7570, p := 11, q := 7559 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7572, p := 11, q := 7561 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7574, p := 13, q := 7561 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7576, p := 3, q := 7573 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7578, p := 5, q := 7573 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7580, p := 3, q := 7577 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7582, p := 5, q := 7577 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7584, p := 7, q := 7577 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7586, p := 3, q := 7583 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7588, p := 5, q := 7583 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7590, p := 7, q := 7583 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7592, p := 3, q := 7589 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7594, p := 3, q := 7591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7596, p := 5, q := 7591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7598, p := 7, q := 7591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7600, p := 11, q := 7589 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7602, p := 11, q := 7591 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate7502To7602 : List CertificateEntry :=
  verifiedCertificateEntries certificate7502To7602Verified

theorem certificate7502To7602_covers :
    CertificateCoversBetween 7502 7602 certificate7502To7602 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween7502To7602 :
    GoldbachBetween 7502 7602 :=
  goldbachBetween_of_certificate certificate7502To7602_covers

def certificate7602To7702Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 7604, p := 13, q := 7591 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7606, p := 3, q := 7603 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7608, p := 5, q := 7603 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7610, p := 3, q := 7607 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7612, p := 5, q := 7607 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7614, p := 7, q := 7607 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7616, p := 13, q := 7603 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7618, p := 11, q := 7607 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7620, p := 13, q := 7607 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7622, p := 19, q := 7603 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7624, p := 3, q := 7621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7626, p := 5, q := 7621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7628, p := 7, q := 7621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7630, p := 23, q := 7607 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7632, p := 11, q := 7621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7634, p := 13, q := 7621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7636, p := 29, q := 7607 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7638, p := 17, q := 7621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7640, p := 19, q := 7621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7642, p := 3, q := 7639 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7644, p := 5, q := 7639 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7646, p := 3, q := 7643 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7648, p := 5, q := 7643 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7650, p := 7, q := 7643 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7652, p := 3, q := 7649 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7654, p := 5, q := 7649 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7656, p := 7, q := 7649 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7658, p := 19, q := 7639 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7660, p := 11, q := 7649 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7662, p := 13, q := 7649 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7664, p := 43, q := 7621 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7666, p := 17, q := 7649 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7668, p := 19, q := 7649 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7670, p := 31, q := 7639 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7672, p := 3, q := 7669 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7674, p := 5, q := 7669 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7676, p := 3, q := 7673 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7678, p := 5, q := 7673 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7680, p := 7, q := 7673 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7682, p := 13, q := 7669 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7684, p := 3, q := 7681 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7686, p := 5, q := 7681 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7688, p := 7, q := 7681 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7690, p := 3, q := 7687 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7692, p := 5, q := 7687 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7694, p := 3, q := 7691 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7696, p := 5, q := 7691 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7698, p := 7, q := 7691 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7700, p := 13, q := 7687 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7702, p := 3, q := 7699 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate7602To7702 : List CertificateEntry :=
  verifiedCertificateEntries certificate7602To7702Verified

theorem certificate7602To7702_covers :
    CertificateCoversBetween 7602 7702 certificate7602To7702 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween7602To7702 :
    GoldbachBetween 7602 7702 :=
  goldbachBetween_of_certificate certificate7602To7702_covers

def certificate7702To7802Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 7704, p := 5, q := 7699 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7706, p := 3, q := 7703 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7708, p := 5, q := 7703 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7710, p := 7, q := 7703 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7712, p := 13, q := 7699 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7714, p := 11, q := 7703 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7716, p := 13, q := 7703 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7718, p := 19, q := 7699 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7720, p := 3, q := 7717 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7722, p := 5, q := 7717 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7724, p := 7, q := 7717 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7726, p := 3, q := 7723 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7728, p := 5, q := 7723 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7730, p := 3, q := 7727 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7732, p := 5, q := 7727 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7734, p := 7, q := 7727 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7736, p := 13, q := 7723 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7738, p := 11, q := 7727 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7740, p := 13, q := 7727 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7742, p := 19, q := 7723 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7744, p := 3, q := 7741 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7746, p := 5, q := 7741 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7748, p := 7, q := 7741 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7750, p := 23, q := 7727 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7752, p := 11, q := 7741 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7754, p := 13, q := 7741 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7756, p := 3, q := 7753 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7758, p := 5, q := 7753 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7760, p := 3, q := 7757 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7762, p := 3, q := 7759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7764, p := 5, q := 7759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7766, p := 7, q := 7759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7768, p := 11, q := 7757 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7770, p := 11, q := 7759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7772, p := 13, q := 7759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7774, p := 17, q := 7757 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7776, p := 17, q := 7759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7778, p := 19, q := 7759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7780, p := 23, q := 7757 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7782, p := 23, q := 7759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7784, p := 31, q := 7753 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7786, p := 29, q := 7757 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7788, p := 29, q := 7759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7790, p := 31, q := 7759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7792, p := 3, q := 7789 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7794, p := 5, q := 7789 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7796, p := 3, q := 7793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7798, p := 5, q := 7793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7800, p := 7, q := 7793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7802, p := 13, q := 7789 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate7702To7802 : List CertificateEntry :=
  verifiedCertificateEntries certificate7702To7802Verified

theorem certificate7702To7802_covers :
    CertificateCoversBetween 7702 7802 certificate7702To7802 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween7702To7802 :
    GoldbachBetween 7702 7802 :=
  goldbachBetween_of_certificate certificate7702To7802_covers

def certificate7802To7902Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 7804, p := 11, q := 7793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7806, p := 13, q := 7793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7808, p := 19, q := 7789 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7810, p := 17, q := 7793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7812, p := 19, q := 7793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7814, p := 61, q := 7753 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7816, p := 23, q := 7793 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7818, p := 29, q := 7789 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7820, p := 3, q := 7817 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7822, p := 5, q := 7817 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7824, p := 7, q := 7817 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7826, p := 3, q := 7823 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7828, p := 5, q := 7823 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7830, p := 7, q := 7823 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7832, p := 3, q := 7829 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7834, p := 5, q := 7829 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7836, p := 7, q := 7829 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7838, p := 79, q := 7759 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7840, p := 11, q := 7829 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7842, p := 13, q := 7829 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7844, p := 3, q := 7841 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7846, p := 5, q := 7841 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7848, p := 7, q := 7841 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7850, p := 61, q := 7789 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7852, p := 11, q := 7841 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7854, p := 13, q := 7841 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7856, p := 3, q := 7853 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7858, p := 5, q := 7853 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7860, p := 7, q := 7853 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7862, p := 73, q := 7789 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7864, p := 11, q := 7853 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7866, p := 13, q := 7853 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7868, p := 79, q := 7789 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7870, p := 3, q := 7867 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7872, p := 5, q := 7867 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7874, p := 7, q := 7867 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7876, p := 3, q := 7873 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7878, p := 5, q := 7873 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7880, p := 3, q := 7877 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7882, p := 3, q := 7879 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7884, p := 5, q := 7879 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7886, p := 3, q := 7883 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7888, p := 5, q := 7883 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7890, p := 7, q := 7883 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7892, p := 13, q := 7879 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7894, p := 11, q := 7883 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7896, p := 13, q := 7883 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7898, p := 19, q := 7879 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7900, p := 17, q := 7883 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7902, p := 19, q := 7883 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate7802To7902 : List CertificateEntry :=
  verifiedCertificateEntries certificate7802To7902Verified

theorem certificate7802To7902_covers :
    CertificateCoversBetween 7802 7902 certificate7802To7902 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween7802To7902 :
    GoldbachBetween 7802 7902 :=
  goldbachBetween_of_certificate certificate7802To7902_covers

def certificate7902To8002Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 7904, p := 3, q := 7901 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7906, p := 5, q := 7901 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7908, p := 7, q := 7901 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7910, p := 3, q := 7907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7912, p := 5, q := 7907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7914, p := 7, q := 7907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7916, p := 37, q := 7879 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7918, p := 11, q := 7907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7920, p := 13, q := 7907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7922, p := 3, q := 7919 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7924, p := 5, q := 7919 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7926, p := 7, q := 7919 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7928, p := 61, q := 7867 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7930, p := 3, q := 7927 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7932, p := 5, q := 7927 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7934, p := 7, q := 7927 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7936, p := 3, q := 7933 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7938, p := 5, q := 7933 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7940, p := 3, q := 7937 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7942, p := 5, q := 7937 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7944, p := 7, q := 7937 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7946, p := 13, q := 7933 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7948, p := 11, q := 7937 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7950, p := 13, q := 7937 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7952, p := 3, q := 7949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7954, p := 3, q := 7951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7956, p := 5, q := 7951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7958, p := 7, q := 7951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7960, p := 11, q := 7949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7962, p := 11, q := 7951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7964, p := 13, q := 7951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7966, p := 3, q := 7963 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7968, p := 5, q := 7963 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7970, p := 7, q := 7963 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7972, p := 23, q := 7949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7974, p := 11, q := 7963 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7976, p := 13, q := 7963 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7978, p := 29, q := 7949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7980, p := 17, q := 7963 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7982, p := 19, q := 7963 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7984, p := 47, q := 7937 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7986, p := 23, q := 7963 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7988, p := 37, q := 7951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7990, p := 41, q := 7949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7992, p := 29, q := 7963 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7994, p := 31, q := 7963 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7996, p := 3, q := 7993 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 7998, p := 5, q := 7993 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8000, p := 7, q := 7993 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8002, p := 53, q := 7949 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate7902To8002 : List CertificateEntry :=
  verifiedCertificateEntries certificate7902To8002Verified

theorem certificate7902To8002_covers :
    CertificateCoversBetween 7902 8002 certificate7902To8002 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween7902To8002 :
    GoldbachBetween 7902 8002 :=
  goldbachBetween_of_certificate certificate7902To8002_covers

def certificate8002To8102Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 8004, p := 11, q := 7993 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8006, p := 13, q := 7993 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8008, p := 59, q := 7949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8010, p := 17, q := 7993 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8012, p := 3, q := 8009 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8014, p := 3, q := 8011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8016, p := 5, q := 8011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8018, p := 7, q := 8011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8020, p := 3, q := 8017 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8022, p := 5, q := 8017 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8024, p := 7, q := 8017 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8026, p := 17, q := 8009 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8028, p := 11, q := 8017 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8030, p := 13, q := 8017 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8032, p := 23, q := 8009 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8034, p := 17, q := 8017 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8036, p := 19, q := 8017 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8038, p := 29, q := 8009 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8040, p := 23, q := 8017 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8042, p := 3, q := 8039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8044, p := 5, q := 8039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8046, p := 7, q := 8039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8048, p := 31, q := 8017 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8050, p := 11, q := 8039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8052, p := 13, q := 8039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8054, p := 37, q := 8017 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8056, p := 3, q := 8053 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8058, p := 5, q := 8053 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8060, p := 7, q := 8053 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8062, p := 3, q := 8059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8064, p := 5, q := 8059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8066, p := 7, q := 8059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8068, p := 29, q := 8039 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8070, p := 11, q := 8059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8072, p := 3, q := 8069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8074, p := 5, q := 8069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8076, p := 7, q := 8069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8078, p := 19, q := 8059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8080, p := 11, q := 8069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8082, p := 13, q := 8069 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8084, p := 3, q := 8081 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8086, p := 5, q := 8081 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8088, p := 7, q := 8081 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8090, p := 3, q := 8087 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8092, p := 3, q := 8089 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8094, p := 5, q := 8089 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8096, p := 3, q := 8093 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8098, p := 5, q := 8093 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8100, p := 7, q := 8093 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8102, p := 13, q := 8089 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate8002To8102 : List CertificateEntry :=
  verifiedCertificateEntries certificate8002To8102Verified

theorem certificate8002To8102_covers :
    CertificateCoversBetween 8002 8102 certificate8002To8102 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween8002To8102 :
    GoldbachBetween 8002 8102 :=
  goldbachBetween_of_certificate certificate8002To8102_covers

def certificate8102To8202Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 8104, p := 3, q := 8101 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8106, p := 5, q := 8101 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8108, p := 7, q := 8101 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8110, p := 17, q := 8093 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8112, p := 11, q := 8101 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8114, p := 3, q := 8111 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8116, p := 5, q := 8111 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8118, p := 7, q := 8111 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8120, p := 3, q := 8117 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8122, p := 5, q := 8117 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8124, p := 7, q := 8117 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8126, p := 3, q := 8123 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8128, p := 5, q := 8123 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8130, p := 7, q := 8123 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8132, p := 31, q := 8101 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8134, p := 11, q := 8123 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8136, p := 13, q := 8123 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8138, p := 37, q := 8101 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8140, p := 17, q := 8123 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8142, p := 19, q := 8123 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8144, p := 43, q := 8101 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8146, p := 23, q := 8123 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8148, p := 31, q := 8117 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8150, p := 3, q := 8147 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8152, p := 5, q := 8147 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8154, p := 7, q := 8147 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8156, p := 67, q := 8089 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8158, p := 11, q := 8147 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8160, p := 13, q := 8147 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8162, p := 61, q := 8101 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8164, p := 3, q := 8161 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8166, p := 5, q := 8161 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8168, p := 7, q := 8161 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8170, p := 3, q := 8167 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8172, p := 5, q := 8167 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8174, p := 3, q := 8171 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8176, p := 5, q := 8171 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8178, p := 7, q := 8171 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8180, p := 13, q := 8167 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8182, p := 3, q := 8179 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8184, p := 5, q := 8179 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8186, p := 7, q := 8179 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8188, p := 17, q := 8171 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8190, p := 11, q := 8179 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8192, p := 13, q := 8179 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8194, p := 3, q := 8191 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8196, p := 5, q := 8191 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8198, p := 7, q := 8191 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8200, p := 29, q := 8171 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8202, p := 11, q := 8191 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate8102To8202 : List CertificateEntry :=
  verifiedCertificateEntries certificate8102To8202Verified

theorem certificate8102To8202_covers :
    CertificateCoversBetween 8102 8202 certificate8102To8202 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween8102To8202 :
    GoldbachBetween 8102 8202 :=
  goldbachBetween_of_certificate certificate8102To8202_covers

def certificate8202To8302Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 8204, p := 13, q := 8191 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8206, p := 59, q := 8147 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8208, p := 17, q := 8191 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8210, p := 19, q := 8191 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8212, p := 3, q := 8209 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8214, p := 5, q := 8209 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8216, p := 7, q := 8209 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8218, p := 47, q := 8171 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8220, p := 11, q := 8209 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8222, p := 3, q := 8219 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8224, p := 3, q := 8221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8226, p := 5, q := 8221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8228, p := 7, q := 8221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8230, p := 11, q := 8219 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8232, p := 11, q := 8221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8234, p := 3, q := 8231 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8236, p := 3, q := 8233 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8238, p := 5, q := 8233 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8240, p := 3, q := 8237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8242, p := 5, q := 8237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8244, p := 7, q := 8237 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8246, p := 3, q := 8243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8248, p := 5, q := 8243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8250, p := 7, q := 8243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8252, p := 19, q := 8233 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8254, p := 11, q := 8243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8256, p := 13, q := 8243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8258, p := 37, q := 8221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8260, p := 17, q := 8243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8262, p := 19, q := 8243 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8264, p := 31, q := 8233 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8266, p := 3, q := 8263 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8268, p := 5, q := 8263 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8270, p := 7, q := 8263 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8272, p := 3, q := 8269 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8274, p := 5, q := 8269 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8276, p := 3, q := 8273 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8278, p := 5, q := 8273 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8280, p := 7, q := 8273 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8282, p := 13, q := 8269 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8284, p := 11, q := 8273 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8286, p := 13, q := 8273 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8288, p := 19, q := 8269 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8290, p := 3, q := 8287 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8292, p := 5, q := 8287 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8294, p := 3, q := 8291 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8296, p := 3, q := 8293 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8298, p := 5, q := 8293 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8300, p := 3, q := 8297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8302, p := 5, q := 8297 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate8202To8302 : List CertificateEntry :=
  verifiedCertificateEntries certificate8202To8302Verified

theorem certificate8202To8302_covers :
    CertificateCoversBetween 8202 8302 certificate8202To8302 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween8202To8302 :
    GoldbachBetween 8202 8302 :=
  goldbachBetween_of_certificate certificate8202To8302_covers

def certificate8302To8402Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 8304, p := 7, q := 8297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8306, p := 13, q := 8293 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8308, p := 11, q := 8297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8310, p := 13, q := 8297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8312, p := 19, q := 8293 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8314, p := 3, q := 8311 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8316, p := 5, q := 8311 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8318, p := 7, q := 8311 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8320, p := 3, q := 8317 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8322, p := 5, q := 8317 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8324, p := 7, q := 8317 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8326, p := 29, q := 8297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8328, p := 11, q := 8317 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8330, p := 13, q := 8317 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8332, p := 3, q := 8329 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8334, p := 5, q := 8329 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8336, p := 7, q := 8329 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8338, p := 41, q := 8297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8340, p := 11, q := 8329 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8342, p := 13, q := 8329 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8344, p := 47, q := 8297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8346, p := 17, q := 8329 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8348, p := 19, q := 8329 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8350, p := 53, q := 8297 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8352, p := 23, q := 8329 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8354, p := 37, q := 8317 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8356, p := 3, q := 8353 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8358, p := 5, q := 8353 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8360, p := 7, q := 8353 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8362, p := 71, q := 8291 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8364, p := 11, q := 8353 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8366, p := 3, q := 8363 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8368, p := 5, q := 8363 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8370, p := 7, q := 8363 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8372, p := 3, q := 8369 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8374, p := 5, q := 8369 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8376, p := 7, q := 8369 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8378, p := 61, q := 8317 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8380, p := 3, q := 8377 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8382, p := 5, q := 8377 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8384, p := 7, q := 8377 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8386, p := 17, q := 8369 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8388, p := 11, q := 8377 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8390, p := 3, q := 8387 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8392, p := 3, q := 8389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8394, p := 5, q := 8389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8396, p := 7, q := 8389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8398, p := 11, q := 8387 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8400, p := 11, q := 8389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8402, p := 13, q := 8389 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate8302To8402 : List CertificateEntry :=
  verifiedCertificateEntries certificate8302To8402Verified

theorem certificate8302To8402_covers :
    CertificateCoversBetween 8302 8402 certificate8302To8402 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween8302To8402 :
    GoldbachBetween 8302 8402 :=
  goldbachBetween_of_certificate certificate8302To8402_covers

def certificate8402To8502Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 8404, p := 17, q := 8387 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8406, p := 17, q := 8389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8408, p := 19, q := 8389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8410, p := 23, q := 8387 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8412, p := 23, q := 8389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8414, p := 37, q := 8377 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8416, p := 29, q := 8387 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8418, p := 29, q := 8389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8420, p := 31, q := 8389 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8422, p := 3, q := 8419 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8424, p := 5, q := 8419 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8426, p := 3, q := 8423 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8428, p := 5, q := 8423 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8430, p := 7, q := 8423 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8432, p := 3, q := 8429 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8434, p := 3, q := 8431 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8436, p := 5, q := 8431 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8438, p := 7, q := 8431 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8440, p := 11, q := 8429 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8442, p := 11, q := 8431 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8444, p := 13, q := 8431 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8446, p := 3, q := 8443 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8448, p := 5, q := 8443 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8450, p := 3, q := 8447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8452, p := 5, q := 8447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8454, p := 7, q := 8447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8456, p := 13, q := 8443 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8458, p := 11, q := 8447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8460, p := 13, q := 8447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8462, p := 19, q := 8443 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8464, p := 3, q := 8461 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8466, p := 5, q := 8461 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8468, p := 7, q := 8461 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8470, p := 3, q := 8467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8472, p := 5, q := 8467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8474, p := 7, q := 8467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8476, p := 29, q := 8447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8478, p := 11, q := 8467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8480, p := 13, q := 8467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8482, p := 53, q := 8429 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8484, p := 17, q := 8467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8486, p := 19, q := 8467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8488, p := 41, q := 8447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8490, p := 23, q := 8467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8492, p := 31, q := 8461 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8494, p := 47, q := 8447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8496, p := 29, q := 8467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8498, p := 31, q := 8467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8500, p := 53, q := 8447 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8502, p := 41, q := 8461 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate8402To8502 : List CertificateEntry :=
  verifiedCertificateEntries certificate8402To8502Verified

theorem certificate8402To8502_covers :
    CertificateCoversBetween 8402 8502 certificate8402To8502 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween8402To8502 :
    GoldbachBetween 8402 8502 :=
  goldbachBetween_of_certificate certificate8402To8502_covers

def certificate8502To8602Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 8504, p := 3, q := 8501 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8506, p := 5, q := 8501 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8508, p := 7, q := 8501 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8510, p := 43, q := 8467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8512, p := 11, q := 8501 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8514, p := 13, q := 8501 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8516, p := 3, q := 8513 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8518, p := 5, q := 8513 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8520, p := 7, q := 8513 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8522, p := 61, q := 8461 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8524, p := 3, q := 8521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8526, p := 5, q := 8521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8528, p := 7, q := 8521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8530, p := 3, q := 8527 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8532, p := 5, q := 8527 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8534, p := 7, q := 8527 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8536, p := 23, q := 8513 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8538, p := 11, q := 8527 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8540, p := 3, q := 8537 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8542, p := 3, q := 8539 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8544, p := 5, q := 8539 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8546, p := 3, q := 8543 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8548, p := 5, q := 8543 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8550, p := 7, q := 8543 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8552, p := 13, q := 8539 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8554, p := 11, q := 8543 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8556, p := 13, q := 8543 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8558, p := 19, q := 8539 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8560, p := 17, q := 8543 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8562, p := 19, q := 8543 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8564, p := 37, q := 8527 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8566, p := 3, q := 8563 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8568, p := 5, q := 8563 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8570, p := 7, q := 8563 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8572, p := 29, q := 8543 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8574, p := 11, q := 8563 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8576, p := 3, q := 8573 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8578, p := 5, q := 8573 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8580, p := 7, q := 8573 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8582, p := 19, q := 8563 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8584, p := 3, q := 8581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8586, p := 5, q := 8581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8588, p := 7, q := 8581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8590, p := 17, q := 8573 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8592, p := 11, q := 8581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8594, p := 13, q := 8581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8596, p := 23, q := 8573 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8598, p := 17, q := 8581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8600, p := 3, q := 8597 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8602, p := 3, q := 8599 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate8502To8602 : List CertificateEntry :=
  verifiedCertificateEntries certificate8502To8602Verified

theorem certificate8502To8602_covers :
    CertificateCoversBetween 8502 8602 certificate8502To8602 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween8502To8602 :
    GoldbachBetween 8502 8602 :=
  goldbachBetween_of_certificate certificate8502To8602_covers

def certificate8602To8702Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 8604, p := 5, q := 8599 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8606, p := 7, q := 8599 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8608, p := 11, q := 8597 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8610, p := 11, q := 8599 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8612, p := 3, q := 8609 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8614, p := 5, q := 8609 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8616, p := 7, q := 8609 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8618, p := 19, q := 8599 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8620, p := 11, q := 8609 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8622, p := 13, q := 8609 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8624, p := 43, q := 8581 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8626, p := 3, q := 8623 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8628, p := 5, q := 8623 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8630, p := 3, q := 8627 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8632, p := 3, q := 8629 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8634, p := 5, q := 8629 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8636, p := 7, q := 8629 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8638, p := 11, q := 8627 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8640, p := 11, q := 8629 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8642, p := 13, q := 8629 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8644, p := 3, q := 8641 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8646, p := 5, q := 8641 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8648, p := 7, q := 8641 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8650, p := 3, q := 8647 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8652, p := 5, q := 8647 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8654, p := 7, q := 8647 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8656, p := 29, q := 8627 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8658, p := 11, q := 8647 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8660, p := 13, q := 8647 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8662, p := 53, q := 8609 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8664, p := 17, q := 8647 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8666, p := 3, q := 8663 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8668, p := 5, q := 8663 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8670, p := 7, q := 8663 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8672, p := 3, q := 8669 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8674, p := 5, q := 8669 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8676, p := 7, q := 8669 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8678, p := 31, q := 8647 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8680, p := 3, q := 8677 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8682, p := 5, q := 8677 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8684, p := 3, q := 8681 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8686, p := 5, q := 8681 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8688, p := 7, q := 8681 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8690, p := 13, q := 8677 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8692, p := 3, q := 8689 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8694, p := 5, q := 8689 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8696, p := 3, q := 8693 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8698, p := 5, q := 8693 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8700, p := 7, q := 8693 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8702, p := 3, q := 8699 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate8602To8702 : List CertificateEntry :=
  verifiedCertificateEntries certificate8602To8702Verified

theorem certificate8602To8702_covers :
    CertificateCoversBetween 8602 8702 certificate8602To8702 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween8602To8702 :
    GoldbachBetween 8602 8702 :=
  goldbachBetween_of_certificate certificate8602To8702_covers

def certificate8702To8802Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 8704, p := 5, q := 8699 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8706, p := 7, q := 8699 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8708, p := 19, q := 8689 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8710, p := 3, q := 8707 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8712, p := 5, q := 8707 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8714, p := 7, q := 8707 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8716, p := 3, q := 8713 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8718, p := 5, q := 8713 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8720, p := 7, q := 8713 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8722, p := 3, q := 8719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8724, p := 5, q := 8719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8726, p := 7, q := 8719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8728, p := 29, q := 8699 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8730, p := 11, q := 8719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8732, p := 13, q := 8719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8734, p := 3, q := 8731 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8736, p := 5, q := 8731 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8738, p := 7, q := 8731 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8740, p := 3, q := 8737 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8742, p := 5, q := 8737 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8744, p := 3, q := 8741 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8746, p := 5, q := 8741 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8748, p := 7, q := 8741 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8750, p := 3, q := 8747 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8752, p := 5, q := 8747 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8754, p := 7, q := 8747 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8756, p := 3, q := 8753 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8758, p := 5, q := 8753 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8760, p := 7, q := 8753 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8762, p := 31, q := 8731 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8764, p := 3, q := 8761 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8766, p := 5, q := 8761 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8768, p := 7, q := 8761 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8770, p := 17, q := 8753 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8772, p := 11, q := 8761 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8774, p := 13, q := 8761 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8776, p := 23, q := 8753 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8778, p := 17, q := 8761 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8780, p := 19, q := 8761 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8782, p := 3, q := 8779 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8784, p := 5, q := 8779 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8786, p := 3, q := 8783 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8788, p := 5, q := 8783 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8790, p := 7, q := 8783 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8792, p := 13, q := 8779 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8794, p := 11, q := 8783 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8796, p := 13, q := 8783 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8798, p := 19, q := 8779 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8800, p := 17, q := 8783 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8802, p := 19, q := 8783 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate8702To8802 : List CertificateEntry :=
  verifiedCertificateEntries certificate8702To8802Verified

theorem certificate8702To8802_covers :
    CertificateCoversBetween 8702 8802 certificate8702To8802 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween8702To8802 :
    GoldbachBetween 8702 8802 :=
  goldbachBetween_of_certificate certificate8702To8802_covers

def certificate8802To8902Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 8804, p := 43, q := 8761 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8806, p := 3, q := 8803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8808, p := 5, q := 8803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8810, p := 3, q := 8807 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8812, p := 5, q := 8807 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8814, p := 7, q := 8807 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8816, p := 13, q := 8803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8818, p := 11, q := 8807 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8820, p := 13, q := 8807 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8822, p := 3, q := 8819 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8824, p := 3, q := 8821 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8826, p := 5, q := 8821 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8828, p := 7, q := 8821 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8830, p := 11, q := 8819 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8832, p := 11, q := 8821 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8834, p := 3, q := 8831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8836, p := 5, q := 8831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8838, p := 7, q := 8831 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8840, p := 3, q := 8837 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8842, p := 3, q := 8839 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8844, p := 5, q := 8839 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8846, p := 7, q := 8839 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8848, p := 11, q := 8837 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8850, p := 11, q := 8839 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8852, p := 3, q := 8849 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8854, p := 5, q := 8849 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8856, p := 7, q := 8849 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8858, p := 19, q := 8839 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8860, p := 11, q := 8849 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8862, p := 13, q := 8849 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8864, p := 3, q := 8861 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8866, p := 3, q := 8863 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8868, p := 5, q := 8863 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8870, p := 3, q := 8867 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8872, p := 5, q := 8867 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8874, p := 7, q := 8867 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8876, p := 13, q := 8863 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8878, p := 11, q := 8867 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8880, p := 13, q := 8867 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8882, p := 19, q := 8863 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8884, p := 17, q := 8867 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8886, p := 19, q := 8867 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8888, p := 67, q := 8821 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8890, p := 3, q := 8887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8892, p := 5, q := 8887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8894, p := 7, q := 8887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8896, p := 3, q := 8893 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8898, p := 5, q := 8893 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8900, p := 7, q := 8893 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8902, p := 41, q := 8861 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate8802To8902 : List CertificateEntry :=
  verifiedCertificateEntries certificate8802To8902Verified

theorem certificate8802To8902_covers :
    CertificateCoversBetween 8802 8902 certificate8802To8902 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween8802To8902 :
    GoldbachBetween 8802 8902 :=
  goldbachBetween_of_certificate certificate8802To8902_covers

def certificate8902To9002Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 8904, p := 11, q := 8893 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8906, p := 13, q := 8893 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8908, p := 41, q := 8867 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8910, p := 17, q := 8893 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8912, p := 19, q := 8893 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8914, p := 47, q := 8867 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8916, p := 23, q := 8893 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8918, p := 31, q := 8887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8920, p := 53, q := 8867 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8922, p := 29, q := 8893 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8924, p := 31, q := 8893 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8926, p := 3, q := 8923 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8928, p := 5, q := 8923 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8930, p := 7, q := 8923 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8932, p := 3, q := 8929 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8934, p := 5, q := 8929 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8936, p := 3, q := 8933 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8938, p := 5, q := 8933 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8940, p := 7, q := 8933 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8942, p := 13, q := 8929 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8944, p := 3, q := 8941 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8946, p := 5, q := 8941 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8948, p := 7, q := 8941 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8950, p := 17, q := 8933 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8952, p := 11, q := 8941 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8954, p := 3, q := 8951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8956, p := 5, q := 8951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8958, p := 7, q := 8951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8960, p := 19, q := 8941 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8962, p := 11, q := 8951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8964, p := 13, q := 8951 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8966, p := 3, q := 8963 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8968, p := 5, q := 8963 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8970, p := 7, q := 8963 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8972, p := 3, q := 8969 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8974, p := 3, q := 8971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8976, p := 5, q := 8971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8978, p := 7, q := 8971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8980, p := 11, q := 8969 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8982, p := 11, q := 8971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8984, p := 13, q := 8971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8986, p := 17, q := 8969 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8988, p := 17, q := 8971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8990, p := 19, q := 8971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8992, p := 23, q := 8969 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8994, p := 23, q := 8971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8996, p := 67, q := 8929 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 8998, p := 29, q := 8969 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9000, p := 29, q := 8971 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9002, p := 3, q := 8999 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate8902To9002 : List CertificateEntry :=
  verifiedCertificateEntries certificate8902To9002Verified

theorem certificate8902To9002_covers :
    CertificateCoversBetween 8902 9002 certificate8902To9002 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween8902To9002 :
    GoldbachBetween 8902 9002 :=
  goldbachBetween_of_certificate certificate8902To9002_covers

def certificate9002To9102Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 9004, p := 3, q := 9001 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9006, p := 5, q := 9001 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9008, p := 7, q := 9001 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9010, p := 3, q := 9007 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9012, p := 5, q := 9007 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9014, p := 3, q := 9011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9016, p := 3, q := 9013 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9018, p := 5, q := 9013 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9020, p := 7, q := 9013 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9022, p := 11, q := 9011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9024, p := 11, q := 9013 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9026, p := 13, q := 9013 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9028, p := 17, q := 9011 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9030, p := 17, q := 9013 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9032, p := 3, q := 9029 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9034, p := 5, q := 9029 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9036, p := 7, q := 9029 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9038, p := 31, q := 9007 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9040, p := 11, q := 9029 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9042, p := 13, q := 9029 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9044, p := 3, q := 9041 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9046, p := 3, q := 9043 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9048, p := 5, q := 9043 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9050, p := 7, q := 9043 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9052, p := 3, q := 9049 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9054, p := 5, q := 9049 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9056, p := 7, q := 9049 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9058, p := 17, q := 9041 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9060, p := 11, q := 9049 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9062, p := 3, q := 9059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9064, p := 5, q := 9059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9066, p := 7, q := 9059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9068, p := 19, q := 9049 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9070, p := 3, q := 9067 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9072, p := 5, q := 9067 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9074, p := 7, q := 9067 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9076, p := 17, q := 9059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9078, p := 11, q := 9067 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9080, p := 13, q := 9067 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9082, p := 23, q := 9059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9084, p := 17, q := 9067 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9086, p := 19, q := 9067 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9088, p := 29, q := 9059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9090, p := 23, q := 9067 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9092, p := 43, q := 9049 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9094, p := 3, q := 9091 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9096, p := 5, q := 9091 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9098, p := 7, q := 9091 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9100, p := 41, q := 9059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9102, p := 11, q := 9091 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate9002To9102 : List CertificateEntry :=
  verifiedCertificateEntries certificate9002To9102Verified

theorem certificate9002To9102_covers :
    CertificateCoversBetween 9002 9102 certificate9002To9102 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween9002To9102 :
    GoldbachBetween 9002 9102 :=
  goldbachBetween_of_certificate certificate9002To9102_covers

def certificate9102To9202Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 9104, p := 13, q := 9091 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9106, p := 3, q := 9103 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9108, p := 5, q := 9103 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9110, p := 7, q := 9103 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9112, p := 3, q := 9109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9114, p := 5, q := 9109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9116, p := 7, q := 9109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9118, p := 59, q := 9059 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9120, p := 11, q := 9109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9122, p := 13, q := 9109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9124, p := 83, q := 9041 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9126, p := 17, q := 9109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9128, p := 19, q := 9109 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9130, p := 3, q := 9127 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9132, p := 5, q := 9127 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9134, p := 7, q := 9127 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9136, p := 3, q := 9133 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9138, p := 5, q := 9133 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9140, p := 3, q := 9137 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9142, p := 5, q := 9137 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9144, p := 7, q := 9137 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9146, p := 13, q := 9133 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9148, p := 11, q := 9137 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9150, p := 13, q := 9137 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9152, p := 19, q := 9133 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9154, p := 3, q := 9151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9156, p := 5, q := 9151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9158, p := 7, q := 9151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9160, p := 3, q := 9157 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9162, p := 5, q := 9157 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9164, p := 3, q := 9161 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9166, p := 5, q := 9161 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9168, p := 7, q := 9161 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9170, p := 13, q := 9157 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9172, p := 11, q := 9161 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9174, p := 13, q := 9161 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9176, p := 3, q := 9173 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9178, p := 5, q := 9173 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9180, p := 7, q := 9173 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9182, p := 31, q := 9151 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9184, p := 3, q := 9181 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9186, p := 5, q := 9181 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9188, p := 7, q := 9181 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9190, p := 3, q := 9187 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9192, p := 5, q := 9187 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9194, p := 7, q := 9187 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9196, p := 23, q := 9173 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9198, p := 11, q := 9187 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9200, p := 13, q := 9187 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9202, p := 3, q := 9199 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate9102To9202 : List CertificateEntry :=
  verifiedCertificateEntries certificate9102To9202Verified

theorem certificate9102To9202_covers :
    CertificateCoversBetween 9102 9202 certificate9102To9202 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween9102To9202 :
    GoldbachBetween 9102 9202 :=
  goldbachBetween_of_certificate certificate9102To9202_covers

def certificate9202To9302Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 9204, p := 5, q := 9199 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9206, p := 3, q := 9203 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9208, p := 5, q := 9203 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9210, p := 7, q := 9203 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9212, p := 3, q := 9209 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9214, p := 5, q := 9209 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9216, p := 7, q := 9209 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9218, p := 19, q := 9199 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9220, p := 11, q := 9209 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9222, p := 13, q := 9209 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9224, p := 3, q := 9221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9226, p := 5, q := 9221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9228, p := 7, q := 9221 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9230, p := 3, q := 9227 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9232, p := 5, q := 9227 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9234, p := 7, q := 9227 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9236, p := 37, q := 9199 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9238, p := 11, q := 9227 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9240, p := 13, q := 9227 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9242, p := 3, q := 9239 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9244, p := 3, q := 9241 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9246, p := 5, q := 9241 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9248, p := 7, q := 9241 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9250, p := 11, q := 9239 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9252, p := 11, q := 9241 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9254, p := 13, q := 9241 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9256, p := 17, q := 9239 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9258, p := 17, q := 9241 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9260, p := 3, q := 9257 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9262, p := 5, q := 9257 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9264, p := 7, q := 9257 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9266, p := 67, q := 9199 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9268, p := 11, q := 9257 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9270, p := 13, q := 9257 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9272, p := 31, q := 9241 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9274, p := 17, q := 9257 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9276, p := 19, q := 9257 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9278, p := 37, q := 9241 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9280, p := 3, q := 9277 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9282, p := 5, q := 9277 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9284, p := 3, q := 9281 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9286, p := 3, q := 9283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9288, p := 5, q := 9283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9290, p := 7, q := 9283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9292, p := 11, q := 9281 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9294, p := 11, q := 9283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9296, p := 3, q := 9293 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9298, p := 5, q := 9293 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9300, p := 7, q := 9293 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9302, p := 19, q := 9283 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate9202To9302 : List CertificateEntry :=
  verifiedCertificateEntries certificate9202To9302Verified

theorem certificate9202To9302_covers :
    CertificateCoversBetween 9202 9302 certificate9202To9302 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween9202To9302 :
    GoldbachBetween 9202 9302 :=
  goldbachBetween_of_certificate certificate9202To9302_covers

def certificate9302To9402Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 9304, p := 11, q := 9293 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9306, p := 13, q := 9293 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9308, p := 31, q := 9277 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9310, p := 17, q := 9293 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9312, p := 19, q := 9293 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9314, p := 3, q := 9311 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9316, p := 5, q := 9311 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9318, p := 7, q := 9311 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9320, p := 37, q := 9283 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9322, p := 3, q := 9319 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9324, p := 5, q := 9319 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9326, p := 3, q := 9323 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9328, p := 5, q := 9323 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9330, p := 7, q := 9323 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9332, p := 13, q := 9319 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9334, p := 11, q := 9323 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9336, p := 13, q := 9323 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9338, p := 19, q := 9319 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9340, p := 3, q := 9337 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9342, p := 5, q := 9337 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9344, p := 3, q := 9341 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9346, p := 3, q := 9343 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9348, p := 5, q := 9343 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9350, p := 7, q := 9343 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9352, p := 3, q := 9349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9354, p := 5, q := 9349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9356, p := 7, q := 9349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9358, p := 17, q := 9341 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9360, p := 11, q := 9349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9362, p := 13, q := 9349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9364, p := 23, q := 9341 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9366, p := 17, q := 9349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9368, p := 19, q := 9349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9370, p := 29, q := 9341 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9372, p := 23, q := 9349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9374, p := 3, q := 9371 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9376, p := 5, q := 9371 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9378, p := 7, q := 9371 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9380, p := 3, q := 9377 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9382, p := 5, q := 9377 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9384, p := 7, q := 9377 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9386, p := 37, q := 9349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9388, p := 11, q := 9377 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9390, p := 13, q := 9377 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9392, p := 43, q := 9349 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9394, p := 3, q := 9391 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9396, p := 5, q := 9391 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9398, p := 7, q := 9391 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9400, p := 3, q := 9397 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9402, p := 5, q := 9397 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate9302To9402 : List CertificateEntry :=
  verifiedCertificateEntries certificate9302To9402Verified

theorem certificate9302To9402_covers :
    CertificateCoversBetween 9302 9402 certificate9302To9402 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween9302To9402 :
    GoldbachBetween 9302 9402 :=
  goldbachBetween_of_certificate certificate9302To9402_covers

def certificate9402To9502Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 9404, p := 7, q := 9397 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9406, p := 3, q := 9403 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9408, p := 5, q := 9403 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9410, p := 7, q := 9403 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9412, p := 41, q := 9371 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9414, p := 11, q := 9403 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9416, p := 3, q := 9413 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9418, p := 5, q := 9413 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9420, p := 7, q := 9413 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9422, p := 3, q := 9419 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9424, p := 3, q := 9421 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9426, p := 5, q := 9421 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9428, p := 7, q := 9421 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9430, p := 11, q := 9419 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9432, p := 11, q := 9421 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9434, p := 3, q := 9431 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9436, p := 3, q := 9433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9438, p := 5, q := 9433 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9440, p := 3, q := 9437 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9442, p := 3, q := 9439 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9444, p := 5, q := 9439 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9446, p := 7, q := 9439 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9448, p := 11, q := 9437 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9450, p := 11, q := 9439 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9452, p := 13, q := 9439 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9454, p := 17, q := 9437 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9456, p := 17, q := 9439 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9458, p := 19, q := 9439 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9460, p := 23, q := 9437 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9462, p := 23, q := 9439 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9464, p := 3, q := 9461 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9466, p := 3, q := 9463 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9468, p := 5, q := 9463 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9470, p := 3, q := 9467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9472, p := 5, q := 9467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9474, p := 7, q := 9467 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9476, p := 3, q := 9473 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9478, p := 5, q := 9473 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9480, p := 7, q := 9473 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9482, p := 3, q := 9479 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9484, p := 5, q := 9479 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9486, p := 7, q := 9479 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9488, p := 67, q := 9421 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9490, p := 11, q := 9479 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9492, p := 13, q := 9479 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9494, p := 3, q := 9491 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9496, p := 5, q := 9491 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9498, p := 7, q := 9491 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9500, p := 3, q := 9497 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9502, p := 5, q := 9497 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate9402To9502 : List CertificateEntry :=
  verifiedCertificateEntries certificate9402To9502Verified

theorem certificate9402To9502_covers :
    CertificateCoversBetween 9402 9502 certificate9402To9502 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween9402To9502 :
    GoldbachBetween 9402 9502 :=
  goldbachBetween_of_certificate certificate9402To9502_covers

def certificate9502To9602Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 9504, p := 7, q := 9497 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9506, p := 43, q := 9463 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9508, p := 11, q := 9497 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9510, p := 13, q := 9497 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9512, p := 73, q := 9439 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9514, p := 3, q := 9511 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9516, p := 5, q := 9511 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9518, p := 7, q := 9511 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9520, p := 23, q := 9497 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9522, p := 11, q := 9511 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9524, p := 3, q := 9521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9526, p := 5, q := 9521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9528, p := 7, q := 9521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9530, p := 19, q := 9511 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9532, p := 11, q := 9521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9534, p := 13, q := 9521 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9536, p := 3, q := 9533 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9538, p := 5, q := 9533 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9540, p := 7, q := 9533 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9542, p := 3, q := 9539 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9544, p := 5, q := 9539 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9546, p := 7, q := 9539 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9548, p := 37, q := 9511 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9550, p := 3, q := 9547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9552, p := 5, q := 9547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9554, p := 3, q := 9551 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9556, p := 5, q := 9551 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9558, p := 7, q := 9551 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9560, p := 13, q := 9547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9562, p := 11, q := 9551 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9564, p := 13, q := 9551 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9566, p := 19, q := 9547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9568, p := 17, q := 9551 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9570, p := 19, q := 9551 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9572, p := 61, q := 9511 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9574, p := 23, q := 9551 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9576, p := 29, q := 9547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9578, p := 31, q := 9547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9580, p := 29, q := 9551 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9582, p := 31, q := 9551 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9584, p := 37, q := 9547 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9586, p := 47, q := 9539 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9588, p := 37, q := 9551 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9590, p := 3, q := 9587 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9592, p := 5, q := 9587 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9594, p := 7, q := 9587 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9596, p := 157, q := 9439 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9598, p := 11, q := 9587 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9600, p := 13, q := 9587 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9602, p := 139, q := 9463 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate9502To9602 : List CertificateEntry :=
  verifiedCertificateEntries certificate9502To9602Verified

theorem certificate9502To9602_covers :
    CertificateCoversBetween 9502 9602 certificate9502To9602 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween9502To9602 :
    GoldbachBetween 9502 9602 :=
  goldbachBetween_of_certificate certificate9502To9602_covers

def certificate9602To9702Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 9604, p := 3, q := 9601 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9606, p := 5, q := 9601 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9608, p := 7, q := 9601 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9610, p := 23, q := 9587 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9612, p := 11, q := 9601 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9614, p := 13, q := 9601 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9616, p := 3, q := 9613 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9618, p := 5, q := 9613 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9620, p := 7, q := 9613 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9622, p := 3, q := 9619 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9624, p := 5, q := 9619 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9626, p := 3, q := 9623 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9628, p := 5, q := 9623 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9630, p := 7, q := 9623 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9632, p := 3, q := 9629 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9634, p := 3, q := 9631 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9636, p := 5, q := 9631 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9638, p := 7, q := 9631 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9640, p := 11, q := 9629 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9642, p := 11, q := 9631 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9644, p := 13, q := 9631 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9646, p := 3, q := 9643 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9648, p := 5, q := 9643 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9650, p := 7, q := 9643 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9652, p := 3, q := 9649 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9654, p := 5, q := 9649 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9656, p := 7, q := 9649 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9658, p := 29, q := 9629 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9660, p := 11, q := 9649 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9662, p := 13, q := 9649 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9664, p := 3, q := 9661 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9666, p := 5, q := 9661 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9668, p := 7, q := 9661 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9670, p := 41, q := 9629 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9672, p := 11, q := 9661 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9674, p := 13, q := 9661 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9676, p := 47, q := 9629 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9678, p := 17, q := 9661 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9680, p := 3, q := 9677 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9682, p := 3, q := 9679 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9684, p := 5, q := 9679 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9686, p := 7, q := 9679 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9688, p := 11, q := 9677 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9690, p := 11, q := 9679 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9692, p := 3, q := 9689 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9694, p := 5, q := 9689 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9696, p := 7, q := 9689 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9698, p := 19, q := 9679 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9700, p := 3, q := 9697 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9702, p := 5, q := 9697 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate9602To9702 : List CertificateEntry :=
  verifiedCertificateEntries certificate9602To9702Verified

theorem certificate9602To9702_covers :
    CertificateCoversBetween 9602 9702 certificate9602To9702 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween9602To9702 :
    GoldbachBetween 9602 9702 :=
  goldbachBetween_of_certificate certificate9602To9702_covers

def certificate9702To9802Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 9704, p := 7, q := 9697 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9706, p := 17, q := 9689 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9708, p := 11, q := 9697 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9710, p := 13, q := 9697 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9712, p := 23, q := 9689 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9714, p := 17, q := 9697 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9716, p := 19, q := 9697 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9718, p := 29, q := 9689 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9720, p := 23, q := 9697 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9722, p := 3, q := 9719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9724, p := 3, q := 9721 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9726, p := 5, q := 9721 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9728, p := 7, q := 9721 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9730, p := 11, q := 9719 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9732, p := 11, q := 9721 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9734, p := 13, q := 9721 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9736, p := 3, q := 9733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9738, p := 5, q := 9733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9740, p := 7, q := 9733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9742, p := 3, q := 9739 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9744, p := 5, q := 9739 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9746, p := 3, q := 9743 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9748, p := 5, q := 9743 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9750, p := 7, q := 9743 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9752, p := 3, q := 9749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9754, p := 5, q := 9749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9756, p := 7, q := 9749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9758, p := 19, q := 9739 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9760, p := 11, q := 9749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9762, p := 13, q := 9749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9764, p := 31, q := 9733 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9766, p := 17, q := 9749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9768, p := 19, q := 9749 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9770, p := 3, q := 9767 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9772, p := 3, q := 9769 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9774, p := 5, q := 9769 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9776, p := 7, q := 9769 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9778, p := 11, q := 9767 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9780, p := 11, q := 9769 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9782, p := 13, q := 9769 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9784, p := 3, q := 9781 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9786, p := 5, q := 9781 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9788, p := 7, q := 9781 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9790, p := 3, q := 9787 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9792, p := 5, q := 9787 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9794, p := 3, q := 9791 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9796, p := 5, q := 9791 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9798, p := 7, q := 9791 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9800, p := 13, q := 9787 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9802, p := 11, q := 9791 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate9702To9802 : List CertificateEntry :=
  verifiedCertificateEntries certificate9702To9802Verified

theorem certificate9702To9802_covers :
    CertificateCoversBetween 9702 9802 certificate9702To9802 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween9702To9802 :
    GoldbachBetween 9702 9802 :=
  goldbachBetween_of_certificate certificate9702To9802_covers

def certificate9802To9902Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 9804, p := 13, q := 9791 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9806, p := 3, q := 9803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9808, p := 5, q := 9803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9810, p := 7, q := 9803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9812, p := 31, q := 9781 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9814, p := 3, q := 9811 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9816, p := 5, q := 9811 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9818, p := 7, q := 9811 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9820, p := 3, q := 9817 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9822, p := 5, q := 9817 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9824, p := 7, q := 9817 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9826, p := 23, q := 9803 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9828, p := 11, q := 9817 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9830, p := 13, q := 9817 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9832, p := 3, q := 9829 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9834, p := 5, q := 9829 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9836, p := 3, q := 9833 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9838, p := 5, q := 9833 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9840, p := 7, q := 9833 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9842, p := 3, q := 9839 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9844, p := 5, q := 9839 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9846, p := 7, q := 9839 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9848, p := 19, q := 9829 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9850, p := 11, q := 9839 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9852, p := 13, q := 9839 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9854, p := 3, q := 9851 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9856, p := 5, q := 9851 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9858, p := 7, q := 9851 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9860, p := 3, q := 9857 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9862, p := 3, q := 9859 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9864, p := 5, q := 9859 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9866, p := 7, q := 9859 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9868, p := 11, q := 9857 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9870, p := 11, q := 9859 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9872, p := 13, q := 9859 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9874, p := 3, q := 9871 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9876, p := 5, q := 9871 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9878, p := 7, q := 9871 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9880, p := 23, q := 9857 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9882, p := 11, q := 9871 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9884, p := 13, q := 9871 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9886, p := 3, q := 9883 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9888, p := 5, q := 9883 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9890, p := 3, q := 9887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9892, p := 5, q := 9887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9894, p := 7, q := 9887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9896, p := 13, q := 9883 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9898, p := 11, q := 9887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9900, p := 13, q := 9887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9902, p := 19, q := 9883 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate9802To9902 : List CertificateEntry :=
  verifiedCertificateEntries certificate9802To9902Verified

theorem certificate9802To9902_covers :
    CertificateCoversBetween 9802 9902 certificate9802To9902 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween9802To9902 :
    GoldbachBetween 9802 9902 :=
  goldbachBetween_of_certificate certificate9802To9902_covers

def certificate9902To10000Verified : List VerifiedCertificateEntry :=
  [
    { entry := { n := 9904, p := 3, q := 9901 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9906, p := 5, q := 9901 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9908, p := 7, q := 9901 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9910, p := 3, q := 9907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9912, p := 5, q := 9907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9914, p := 7, q := 9907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9916, p := 29, q := 9887 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9918, p := 11, q := 9907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9920, p := 13, q := 9907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9922, p := 71, q := 9851 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9924, p := 17, q := 9907 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9926, p := 3, q := 9923 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9928, p := 5, q := 9923 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9930, p := 7, q := 9923 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9932, p := 3, q := 9929 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9934, p := 3, q := 9931 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9936, p := 5, q := 9931 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9938, p := 7, q := 9931 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9940, p := 11, q := 9929 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9942, p := 11, q := 9931 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9944, p := 3, q := 9941 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9946, p := 5, q := 9941 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9948, p := 7, q := 9941 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9950, p := 19, q := 9931 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9952, p := 3, q := 9949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9954, p := 5, q := 9949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9956, p := 7, q := 9949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9958, p := 17, q := 9941 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9960, p := 11, q := 9949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9962, p := 13, q := 9949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9964, p := 23, q := 9941 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9966, p := 17, q := 9949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9968, p := 19, q := 9949 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9970, p := 3, q := 9967 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9972, p := 5, q := 9967 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9974, p := 7, q := 9967 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9976, p := 3, q := 9973 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9978, p := 5, q := 9973 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9980, p := 7, q := 9973 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9982, p := 41, q := 9941 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9984, p := 11, q := 9973 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9986, p := 13, q := 9973 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9988, p := 47, q := 9941 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9990, p := 17, q := 9973 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9992, p := 19, q := 9973 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9994, p := 53, q := 9941 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9996, p := 23, q := 9973 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 9998, p := 31, q := 9967 },
      valid := by norm_num [CertificateEntry.Valid] },
    { entry := { n := 10000, p := 59, q := 9941 },
      valid := by norm_num [CertificateEntry.Valid] }
  ]

def certificate9902To10000 : List CertificateEntry :=
  verifiedCertificateEntries certificate9902To10000Verified

theorem certificate9902To10000_covers :
    CertificateCoversBetween 9902 10000 certificate9902To10000 :=
  certificateCoversBetween_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversBetweenListCheck
        VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachBetween9902To10000 :
    GoldbachBetween 9902 10000 :=
  goldbachBetween_of_certificate certificate9902To10000_covers

theorem goldbachBetween102To302 :
    GoldbachBetween 102 302 :=
  goldbachBetween_of_between_and_between
    goldbachBetween102To202
    goldbachBetween202To302

theorem goldbachBetween2To302 :
    GoldbachBetween 2 302 :=
  goldbachBetween_of_between_and_between
    goldbachBetween2To102
    goldbachBetween102To302

theorem goldbachBetween402To602 :
    GoldbachBetween 402 602 :=
  goldbachBetween_of_between_and_between
    goldbachBetween402To502
    goldbachBetween502To602

theorem goldbachBetween302To602 :
    GoldbachBetween 302 602 :=
  goldbachBetween_of_between_and_between
    goldbachBetween302To402
    goldbachBetween402To602

theorem goldbachBetween2To602 :
    GoldbachBetween 2 602 :=
  goldbachBetween_of_between_and_between
    goldbachBetween2To302
    goldbachBetween302To602

theorem goldbachBetween702To902 :
    GoldbachBetween 702 902 :=
  goldbachBetween_of_between_and_between
    goldbachBetween702To802
    goldbachBetween802To902

theorem goldbachBetween602To902 :
    GoldbachBetween 602 902 :=
  goldbachBetween_of_between_and_between
    goldbachBetween602To702
    goldbachBetween702To902

theorem goldbachBetween1002To1202 :
    GoldbachBetween 1002 1202 :=
  goldbachBetween_of_between_and_between
    goldbachBetween1002To1102
    goldbachBetween1102To1202

theorem goldbachBetween902To1202 :
    GoldbachBetween 902 1202 :=
  goldbachBetween_of_between_and_between
    goldbachBetween902To1002
    goldbachBetween1002To1202

theorem goldbachBetween602To1202 :
    GoldbachBetween 602 1202 :=
  goldbachBetween_of_between_and_between
    goldbachBetween602To902
    goldbachBetween902To1202

theorem goldbachBetween2To1202 :
    GoldbachBetween 2 1202 :=
  goldbachBetween_of_between_and_between
    goldbachBetween2To602
    goldbachBetween602To1202

theorem goldbachBetween1302To1502 :
    GoldbachBetween 1302 1502 :=
  goldbachBetween_of_between_and_between
    goldbachBetween1302To1402
    goldbachBetween1402To1502

theorem goldbachBetween1202To1502 :
    GoldbachBetween 1202 1502 :=
  goldbachBetween_of_between_and_between
    goldbachBetween1202To1302
    goldbachBetween1302To1502

theorem goldbachBetween1602To1802 :
    GoldbachBetween 1602 1802 :=
  goldbachBetween_of_between_and_between
    goldbachBetween1602To1702
    goldbachBetween1702To1802

theorem goldbachBetween1502To1802 :
    GoldbachBetween 1502 1802 :=
  goldbachBetween_of_between_and_between
    goldbachBetween1502To1602
    goldbachBetween1602To1802

theorem goldbachBetween1202To1802 :
    GoldbachBetween 1202 1802 :=
  goldbachBetween_of_between_and_between
    goldbachBetween1202To1502
    goldbachBetween1502To1802

theorem goldbachBetween1902To2102 :
    GoldbachBetween 1902 2102 :=
  goldbachBetween_of_between_and_between
    goldbachBetween1902To2002
    goldbachBetween2002To2102

theorem goldbachBetween1802To2102 :
    GoldbachBetween 1802 2102 :=
  goldbachBetween_of_between_and_between
    goldbachBetween1802To1902
    goldbachBetween1902To2102

theorem goldbachBetween2102To2302 :
    GoldbachBetween 2102 2302 :=
  goldbachBetween_of_between_and_between
    goldbachBetween2102To2202
    goldbachBetween2202To2302

theorem goldbachBetween2302To2502 :
    GoldbachBetween 2302 2502 :=
  goldbachBetween_of_between_and_between
    goldbachBetween2302To2402
    goldbachBetween2402To2502

theorem goldbachBetween2102To2502 :
    GoldbachBetween 2102 2502 :=
  goldbachBetween_of_between_and_between
    goldbachBetween2102To2302
    goldbachBetween2302To2502

theorem goldbachBetween1802To2502 :
    GoldbachBetween 1802 2502 :=
  goldbachBetween_of_between_and_between
    goldbachBetween1802To2102
    goldbachBetween2102To2502

theorem goldbachBetween1202To2502 :
    GoldbachBetween 1202 2502 :=
  goldbachBetween_of_between_and_between
    goldbachBetween1202To1802
    goldbachBetween1802To2502

theorem goldbachBetween2To2502 :
    GoldbachBetween 2 2502 :=
  goldbachBetween_of_between_and_between
    goldbachBetween2To1202
    goldbachBetween1202To2502

theorem goldbachBetween2602To2802 :
    GoldbachBetween 2602 2802 :=
  goldbachBetween_of_between_and_between
    goldbachBetween2602To2702
    goldbachBetween2702To2802

theorem goldbachBetween2502To2802 :
    GoldbachBetween 2502 2802 :=
  goldbachBetween_of_between_and_between
    goldbachBetween2502To2602
    goldbachBetween2602To2802

theorem goldbachBetween2902To3102 :
    GoldbachBetween 2902 3102 :=
  goldbachBetween_of_between_and_between
    goldbachBetween2902To3002
    goldbachBetween3002To3102

theorem goldbachBetween2802To3102 :
    GoldbachBetween 2802 3102 :=
  goldbachBetween_of_between_and_between
    goldbachBetween2802To2902
    goldbachBetween2902To3102

theorem goldbachBetween2502To3102 :
    GoldbachBetween 2502 3102 :=
  goldbachBetween_of_between_and_between
    goldbachBetween2502To2802
    goldbachBetween2802To3102

theorem goldbachBetween3202To3402 :
    GoldbachBetween 3202 3402 :=
  goldbachBetween_of_between_and_between
    goldbachBetween3202To3302
    goldbachBetween3302To3402

theorem goldbachBetween3102To3402 :
    GoldbachBetween 3102 3402 :=
  goldbachBetween_of_between_and_between
    goldbachBetween3102To3202
    goldbachBetween3202To3402

theorem goldbachBetween3502To3702 :
    GoldbachBetween 3502 3702 :=
  goldbachBetween_of_between_and_between
    goldbachBetween3502To3602
    goldbachBetween3602To3702

theorem goldbachBetween3402To3702 :
    GoldbachBetween 3402 3702 :=
  goldbachBetween_of_between_and_between
    goldbachBetween3402To3502
    goldbachBetween3502To3702

theorem goldbachBetween3102To3702 :
    GoldbachBetween 3102 3702 :=
  goldbachBetween_of_between_and_between
    goldbachBetween3102To3402
    goldbachBetween3402To3702

theorem goldbachBetween2502To3702 :
    GoldbachBetween 2502 3702 :=
  goldbachBetween_of_between_and_between
    goldbachBetween2502To3102
    goldbachBetween3102To3702

theorem goldbachBetween3802To4002 :
    GoldbachBetween 3802 4002 :=
  goldbachBetween_of_between_and_between
    goldbachBetween3802To3902
    goldbachBetween3902To4002

theorem goldbachBetween3702To4002 :
    GoldbachBetween 3702 4002 :=
  goldbachBetween_of_between_and_between
    goldbachBetween3702To3802
    goldbachBetween3802To4002

theorem goldbachBetween4102To4302 :
    GoldbachBetween 4102 4302 :=
  goldbachBetween_of_between_and_between
    goldbachBetween4102To4202
    goldbachBetween4202To4302

theorem goldbachBetween4002To4302 :
    GoldbachBetween 4002 4302 :=
  goldbachBetween_of_between_and_between
    goldbachBetween4002To4102
    goldbachBetween4102To4302

theorem goldbachBetween3702To4302 :
    GoldbachBetween 3702 4302 :=
  goldbachBetween_of_between_and_between
    goldbachBetween3702To4002
    goldbachBetween4002To4302

theorem goldbachBetween4402To4602 :
    GoldbachBetween 4402 4602 :=
  goldbachBetween_of_between_and_between
    goldbachBetween4402To4502
    goldbachBetween4502To4602

theorem goldbachBetween4302To4602 :
    GoldbachBetween 4302 4602 :=
  goldbachBetween_of_between_and_between
    goldbachBetween4302To4402
    goldbachBetween4402To4602

theorem goldbachBetween4602To4802 :
    GoldbachBetween 4602 4802 :=
  goldbachBetween_of_between_and_between
    goldbachBetween4602To4702
    goldbachBetween4702To4802

theorem goldbachBetween4802To5002 :
    GoldbachBetween 4802 5002 :=
  goldbachBetween_of_between_and_between
    goldbachBetween4802To4902
    goldbachBetween4902To5002

theorem goldbachBetween4602To5002 :
    GoldbachBetween 4602 5002 :=
  goldbachBetween_of_between_and_between
    goldbachBetween4602To4802
    goldbachBetween4802To5002

theorem goldbachBetween4302To5002 :
    GoldbachBetween 4302 5002 :=
  goldbachBetween_of_between_and_between
    goldbachBetween4302To4602
    goldbachBetween4602To5002

theorem goldbachBetween3702To5002 :
    GoldbachBetween 3702 5002 :=
  goldbachBetween_of_between_and_between
    goldbachBetween3702To4302
    goldbachBetween4302To5002

theorem goldbachBetween2502To5002 :
    GoldbachBetween 2502 5002 :=
  goldbachBetween_of_between_and_between
    goldbachBetween2502To3702
    goldbachBetween3702To5002

theorem goldbachBetween2To5002 :
    GoldbachBetween 2 5002 :=
  goldbachBetween_of_between_and_between
    goldbachBetween2To2502
    goldbachBetween2502To5002

theorem goldbachBetween5102To5302 :
    GoldbachBetween 5102 5302 :=
  goldbachBetween_of_between_and_between
    goldbachBetween5102To5202
    goldbachBetween5202To5302

theorem goldbachBetween5002To5302 :
    GoldbachBetween 5002 5302 :=
  goldbachBetween_of_between_and_between
    goldbachBetween5002To5102
    goldbachBetween5102To5302

theorem goldbachBetween5402To5602 :
    GoldbachBetween 5402 5602 :=
  goldbachBetween_of_between_and_between
    goldbachBetween5402To5502
    goldbachBetween5502To5602

theorem goldbachBetween5302To5602 :
    GoldbachBetween 5302 5602 :=
  goldbachBetween_of_between_and_between
    goldbachBetween5302To5402
    goldbachBetween5402To5602

theorem goldbachBetween5002To5602 :
    GoldbachBetween 5002 5602 :=
  goldbachBetween_of_between_and_between
    goldbachBetween5002To5302
    goldbachBetween5302To5602

theorem goldbachBetween5702To5902 :
    GoldbachBetween 5702 5902 :=
  goldbachBetween_of_between_and_between
    goldbachBetween5702To5802
    goldbachBetween5802To5902

theorem goldbachBetween5602To5902 :
    GoldbachBetween 5602 5902 :=
  goldbachBetween_of_between_and_between
    goldbachBetween5602To5702
    goldbachBetween5702To5902

theorem goldbachBetween6002To6202 :
    GoldbachBetween 6002 6202 :=
  goldbachBetween_of_between_and_between
    goldbachBetween6002To6102
    goldbachBetween6102To6202

theorem goldbachBetween5902To6202 :
    GoldbachBetween 5902 6202 :=
  goldbachBetween_of_between_and_between
    goldbachBetween5902To6002
    goldbachBetween6002To6202

theorem goldbachBetween5602To6202 :
    GoldbachBetween 5602 6202 :=
  goldbachBetween_of_between_and_between
    goldbachBetween5602To5902
    goldbachBetween5902To6202

theorem goldbachBetween5002To6202 :
    GoldbachBetween 5002 6202 :=
  goldbachBetween_of_between_and_between
    goldbachBetween5002To5602
    goldbachBetween5602To6202

theorem goldbachBetween6302To6502 :
    GoldbachBetween 6302 6502 :=
  goldbachBetween_of_between_and_between
    goldbachBetween6302To6402
    goldbachBetween6402To6502

theorem goldbachBetween6202To6502 :
    GoldbachBetween 6202 6502 :=
  goldbachBetween_of_between_and_between
    goldbachBetween6202To6302
    goldbachBetween6302To6502

theorem goldbachBetween6602To6802 :
    GoldbachBetween 6602 6802 :=
  goldbachBetween_of_between_and_between
    goldbachBetween6602To6702
    goldbachBetween6702To6802

theorem goldbachBetween6502To6802 :
    GoldbachBetween 6502 6802 :=
  goldbachBetween_of_between_and_between
    goldbachBetween6502To6602
    goldbachBetween6602To6802

theorem goldbachBetween6202To6802 :
    GoldbachBetween 6202 6802 :=
  goldbachBetween_of_between_and_between
    goldbachBetween6202To6502
    goldbachBetween6502To6802

theorem goldbachBetween6902To7102 :
    GoldbachBetween 6902 7102 :=
  goldbachBetween_of_between_and_between
    goldbachBetween6902To7002
    goldbachBetween7002To7102

theorem goldbachBetween6802To7102 :
    GoldbachBetween 6802 7102 :=
  goldbachBetween_of_between_and_between
    goldbachBetween6802To6902
    goldbachBetween6902To7102

theorem goldbachBetween7102To7302 :
    GoldbachBetween 7102 7302 :=
  goldbachBetween_of_between_and_between
    goldbachBetween7102To7202
    goldbachBetween7202To7302

theorem goldbachBetween7302To7502 :
    GoldbachBetween 7302 7502 :=
  goldbachBetween_of_between_and_between
    goldbachBetween7302To7402
    goldbachBetween7402To7502

theorem goldbachBetween7102To7502 :
    GoldbachBetween 7102 7502 :=
  goldbachBetween_of_between_and_between
    goldbachBetween7102To7302
    goldbachBetween7302To7502

theorem goldbachBetween6802To7502 :
    GoldbachBetween 6802 7502 :=
  goldbachBetween_of_between_and_between
    goldbachBetween6802To7102
    goldbachBetween7102To7502

theorem goldbachBetween6202To7502 :
    GoldbachBetween 6202 7502 :=
  goldbachBetween_of_between_and_between
    goldbachBetween6202To6802
    goldbachBetween6802To7502

theorem goldbachBetween5002To7502 :
    GoldbachBetween 5002 7502 :=
  goldbachBetween_of_between_and_between
    goldbachBetween5002To6202
    goldbachBetween6202To7502

theorem goldbachBetween7602To7802 :
    GoldbachBetween 7602 7802 :=
  goldbachBetween_of_between_and_between
    goldbachBetween7602To7702
    goldbachBetween7702To7802

theorem goldbachBetween7502To7802 :
    GoldbachBetween 7502 7802 :=
  goldbachBetween_of_between_and_between
    goldbachBetween7502To7602
    goldbachBetween7602To7802

theorem goldbachBetween7902To8102 :
    GoldbachBetween 7902 8102 :=
  goldbachBetween_of_between_and_between
    goldbachBetween7902To8002
    goldbachBetween8002To8102

theorem goldbachBetween7802To8102 :
    GoldbachBetween 7802 8102 :=
  goldbachBetween_of_between_and_between
    goldbachBetween7802To7902
    goldbachBetween7902To8102

theorem goldbachBetween7502To8102 :
    GoldbachBetween 7502 8102 :=
  goldbachBetween_of_between_and_between
    goldbachBetween7502To7802
    goldbachBetween7802To8102

theorem goldbachBetween8202To8402 :
    GoldbachBetween 8202 8402 :=
  goldbachBetween_of_between_and_between
    goldbachBetween8202To8302
    goldbachBetween8302To8402

theorem goldbachBetween8102To8402 :
    GoldbachBetween 8102 8402 :=
  goldbachBetween_of_between_and_between
    goldbachBetween8102To8202
    goldbachBetween8202To8402

theorem goldbachBetween8502To8702 :
    GoldbachBetween 8502 8702 :=
  goldbachBetween_of_between_and_between
    goldbachBetween8502To8602
    goldbachBetween8602To8702

theorem goldbachBetween8402To8702 :
    GoldbachBetween 8402 8702 :=
  goldbachBetween_of_between_and_between
    goldbachBetween8402To8502
    goldbachBetween8502To8702

theorem goldbachBetween8102To8702 :
    GoldbachBetween 8102 8702 :=
  goldbachBetween_of_between_and_between
    goldbachBetween8102To8402
    goldbachBetween8402To8702

theorem goldbachBetween7502To8702 :
    GoldbachBetween 7502 8702 :=
  goldbachBetween_of_between_and_between
    goldbachBetween7502To8102
    goldbachBetween8102To8702

theorem goldbachBetween8802To9002 :
    GoldbachBetween 8802 9002 :=
  goldbachBetween_of_between_and_between
    goldbachBetween8802To8902
    goldbachBetween8902To9002

theorem goldbachBetween8702To9002 :
    GoldbachBetween 8702 9002 :=
  goldbachBetween_of_between_and_between
    goldbachBetween8702To8802
    goldbachBetween8802To9002

theorem goldbachBetween9102To9302 :
    GoldbachBetween 9102 9302 :=
  goldbachBetween_of_between_and_between
    goldbachBetween9102To9202
    goldbachBetween9202To9302

theorem goldbachBetween9002To9302 :
    GoldbachBetween 9002 9302 :=
  goldbachBetween_of_between_and_between
    goldbachBetween9002To9102
    goldbachBetween9102To9302

theorem goldbachBetween8702To9302 :
    GoldbachBetween 8702 9302 :=
  goldbachBetween_of_between_and_between
    goldbachBetween8702To9002
    goldbachBetween9002To9302

theorem goldbachBetween9402To9602 :
    GoldbachBetween 9402 9602 :=
  goldbachBetween_of_between_and_between
    goldbachBetween9402To9502
    goldbachBetween9502To9602

theorem goldbachBetween9302To9602 :
    GoldbachBetween 9302 9602 :=
  goldbachBetween_of_between_and_between
    goldbachBetween9302To9402
    goldbachBetween9402To9602

theorem goldbachBetween9602To9802 :
    GoldbachBetween 9602 9802 :=
  goldbachBetween_of_between_and_between
    goldbachBetween9602To9702
    goldbachBetween9702To9802

theorem goldbachBetween9802To10000 :
    GoldbachBetween 9802 10000 :=
  goldbachBetween_of_between_and_between
    goldbachBetween9802To9902
    goldbachBetween9902To10000

theorem goldbachBetween9602To10000 :
    GoldbachBetween 9602 10000 :=
  goldbachBetween_of_between_and_between
    goldbachBetween9602To9802
    goldbachBetween9802To10000

theorem goldbachBetween9302To10000 :
    GoldbachBetween 9302 10000 :=
  goldbachBetween_of_between_and_between
    goldbachBetween9302To9602
    goldbachBetween9602To10000

theorem goldbachBetween8702To10000 :
    GoldbachBetween 8702 10000 :=
  goldbachBetween_of_between_and_between
    goldbachBetween8702To9302
    goldbachBetween9302To10000

theorem goldbachBetween7502To10000 :
    GoldbachBetween 7502 10000 :=
  goldbachBetween_of_between_and_between
    goldbachBetween7502To8702
    goldbachBetween8702To10000

theorem goldbachBetween5002To10000 :
    GoldbachBetween 5002 10000 :=
  goldbachBetween_of_between_and_between
    goldbachBetween5002To7502
    goldbachBetween7502To10000

theorem goldbachBetween2To10000 :
    GoldbachBetween 2 10000 :=
  goldbachBetween_of_between_and_between
    goldbachBetween2To5002
    goldbachBetween5002To10000

theorem goldbachUpTo10000_of_chunkedCertificate2To10000 :
    GoldbachUpTo 10000 :=
  goldbachUpTo_of_between_two goldbachBetween2To10000

theorem explicitLowerBound100_from_chunkedCertificate2To10000_and_explicit_lower_bound
    {T : Nat}
    (hthreshold : T ≤ 10000)
    (lower_bound : ExplicitGoldbachLowerBound T) :
    ExplicitGoldbachLowerBound 100 :=
  explicit_lower_bound100_of_finite_and_explicit_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 hthreshold lower_bound

theorem strongGoldbach_from_chunkedCertificate2To10000_and_explicit_lower_bound
    {T : Nat}
    (hthreshold : T ≤ 10000)
    (lower_bound : ExplicitGoldbachLowerBound T) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_explicit_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 hthreshold lower_bound

theorem strongGoldbach_from_chunkedCertificate2To10000_and_circle_method_lower_bound
    (bound : CircleMethodLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_circle_method_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_major_minor_arc_estimate
    (estimate : MajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_count_positive_above
    {T : Nat}
    (hthreshold : T ≤ 10000)
    (count_positive : GoldbachCountPositiveAbove T) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_count_positive_above_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 hthreshold count_positive

theorem strongGoldbach_from_chunkedCertificate2To10000_and_weighted_lower_bound
    (bound : WeightedGoldbachLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_weighted_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_weighted_major_minor_arc_estimate
    (estimate : WeightedMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_weighted_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_contaminated_weighted_lower_bound
    (bound : ContaminatedWeightedGoldbachLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_contaminated_weighted_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_contaminated_weighted_major_minor_arc_estimate
    (estimate : ContaminatedWeightedMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_contaminated_weighted_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_real_contaminated_weighted_lower_bound
    (bound : RealContaminatedWeightedGoldbachLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_real_contaminated_weighted_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_real_contaminated_weighted_major_minor_arc_estimate
    (estimate : RealContaminatedWeightedMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_real_contaminated_weighted_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_lower_bound
    (bound : VonMangoldtGoldbachLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_major_minor_arc_estimate
    (estimate : VonMangoldtMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_prime_power_contamination_lower_bound
    (bound : VonMangoldtPrimePowerContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_prime_power_contamination_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_prime_power_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtPrimePowerContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_prime_power_contamination_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_split_prime_power_contamination_lower_bound
    (bound : VonMangoldtSplitPrimePowerContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_split_prime_power_contamination_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_split_prime_power_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtSplitPrimePowerContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_split_prime_power_contamination_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_pointwise_split_contamination_lower_bound
    (bound : VonMangoldtPointwiseSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_pointwise_split_contamination_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_pointwise_split_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtPointwiseSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_pointwise_split_contamination_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_uniform_split_contamination_lower_bound
    (bound : VonMangoldtUniformSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_uniform_split_contamination_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_uniform_split_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtUniformSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_uniform_split_contamination_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_counted_split_contamination_lower_bound
    (bound : VonMangoldtCountedSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_counted_split_contamination_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_counted_split_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtCountedSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_counted_split_contamination_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_trivial_count_split_contamination_lower_bound
    (bound : VonMangoldtTrivialCountSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_trivial_count_split_contamination_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_trivial_count_split_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtTrivialCountSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_trivial_count_split_contamination_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_weight_bound_split_contamination_lower_bound
    (bound : VonMangoldtWeightBoundSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_weight_bound_split_contamination_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_weight_bound_split_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtWeightBoundSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_weight_bound_split_contamination_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_log_weight_split_contamination_lower_bound
    (bound : VonMangoldtLogWeightSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_log_weight_split_contamination_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_log_weight_split_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtLogWeightSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_log_weight_split_contamination_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_count_bound_log_weight_split_contamination_lower_bound
    (bound : VonMangoldtCountBoundLogWeightSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_count_bound_log_weight_split_contamination_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_count_bound_log_weight_split_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtCountBoundLogWeightSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_count_bound_log_weight_split_contamination_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_canonical_log_count_contamination_lower_bound
    (bound : VonMangoldtCanonicalLogCountContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_canonical_log_count_contamination_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_canonical_log_count_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtCanonicalLogCountContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_canonical_log_count_contamination_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_direct_raw_log_count_lower_bound
    (bound : VonMangoldtDirectRawLogCountLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_direct_raw_log_count_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_direct_raw_weight_sum_lower_bound
    (bound : VonMangoldtDirectRawWeightSumLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_direct_raw_weight_sum_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_split_threshold_direct_raw_weight_sum_lower_bound
    (bound : VonMangoldtSplitThresholdDirectRawWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_direct_raw_weight_sum_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_eventually_direct_raw_weight_sum_lower_bound
    (bound : VonMangoldtEventuallyDirectRawWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_direct_raw_weight_sum_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_positive_linear_raw_weight_sum_lower_bound
    (bound : VonMangoldtPositiveLinearRawWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_weight_sum_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_relative_error_positive_linear_raw_weight_sum_lower_bound
    (bound : VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_relative_error_positive_linear_raw_weight_sum_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_relative_error_weight_sum_major_minor_arc_estimate
    (estimate : VonMangoldtRelativeErrorWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_relative_error_weight_sum_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_split_threshold_relative_error_weight_sum_major_minor_arc_estimate
    (estimate : VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_relative_error_weight_sum_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_eventually_relative_error_weight_sum_major_minor_arc_estimate
    (estimate : VonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_relative_error_weight_sum_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound
    (bound : VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_eventually_positive_linear_raw_weight_sum_lower_bound
    (bound : VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_positive_linear_raw_weight_sum_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_direct_weight_sum_major_minor_arc_estimate
    (estimate : VonMangoldtDirectWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_direct_weight_sum_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_split_threshold_direct_weight_sum_major_minor_arc_estimate
    (estimate : VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectWeightSumMajorMinorArcEstimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_direct_weight_sum_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_eventually_direct_weight_sum_major_minor_arc_estimate
    (estimate : VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectWeightSumMajorMinorArcEstimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_direct_weight_sum_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_sqrt_log_count_raw_lower_bound
    (bound : VonMangoldtSqrtLogCountRawLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_sqrt_log_count_raw_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_sqrt_log_count_linear_raw_lower_bound
    (bound : VonMangoldtSqrtLogCountLinearRawLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_sqrt_log_count_linear_raw_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_positive_linear_raw_lower_bound
    (bound : VonMangoldtPositiveLinearRawLowerBound)
    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_eventually_positive_linear_raw_lower_bound
    (bound : VonMangoldtEventuallyPositiveLinearRawLowerBound)
    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_positive_linear_raw_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound
    (bound : VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound
    (bound : VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound
    (bound : VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound
    (bound : VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound)
    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound
    (bound : VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_eventually_hardy_littlewood_normalized_estimate
    (estimate : VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate)
    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_hardy_littlewood_normalized_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_hardy_littlewood_normalized_estimate
    (estimate : VonMangoldtHardyLittlewoodNormalizedEstimate)
    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate
    (estimate : VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_hardy_littlewood_normalized_weight_sum_estimate
    (estimate : VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate)
    (hthreshold : estimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_weight_sum_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_eventually_positive_linear_major_minor_arc_estimate
    (estimate : VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate)
    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_positive_linear_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_arc_estimate
    (estimate : VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate)
    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_split_threshold_relative_error_sqrt_log_count_major_minor_arc_estimate
    (estimate : VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate)
    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_relative_error_sqrt_log_count_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_eventually_positive_linear_weight_sum_major_minor_arc_estimate
    (estimate : VonMangoldtEventuallyPositiveLinearWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_positive_linear_weight_sum_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate
    (estimate : VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_sqrt_log_count_major_minor_arc_estimate
    (estimate : VonMangoldtSqrtLogCountMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_sqrt_log_count_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_canonical_log_contamination_lower_bound
    (bound : VonMangoldtCanonicalLogContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_canonical_log_contamination_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_canonical_log_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtCanonicalLogContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_canonical_log_contamination_major_minor_arc_estimate_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 estimate hthreshold

theorem strongGoldbach_from_chunkedCertificate2To10000_and_vonMangoldt_direct_raw_log_lower_bound
    (bound : VonMangoldtDirectRawLogLowerBound)
    (hthreshold : bound.threshold ≤ 10000) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_direct_raw_log_lower_bound_le
    goldbachUpTo10000_of_chunkedCertificate2To10000 bound hthreshold

end Gdbh
