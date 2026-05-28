import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace Gdbh

def GoldbachRepresentation (n : Nat) : Prop :=
  ∃ p q : Nat, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

def StrongGoldbach : Prop :=
  ∀ n : Nat, 2 < n → Even n → GoldbachRepresentation n

def GoldbachUpTo (B : Nat) : Prop :=
  ∀ n : Nat, 2 < n → n ≤ B → Even n → GoldbachRepresentation n

def GoldbachAbove (B : Nat) : Prop :=
  ∀ n : Nat, B < n → Even n → GoldbachRepresentation n

def GoldbachPrimeSubWitnesses (n : Nat) : Finset Nat :=
  (Finset.range n.succ).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))

def GoldbachCount (n : Nat) : Nat :=
  (GoldbachPrimeSubWitnesses n).card

def GoldbachCountPositiveAbove (B : Nat) : Prop :=
  ∀ n : Nat, B < n → Even n → 0 < GoldbachCount n

theorem goldbachRepresentation_of_prime_sub {n p : Nat}
    (hp : Nat.Prime p)
    (hq : Nat.Prime (n - p))
    (hp_le : p ≤ n) :
    GoldbachRepresentation n := by
  exact ⟨p, n - p, hp, hq, Nat.add_sub_of_le hp_le⟩

theorem goldbachRepresentation_of_count_pos {n : Nat}
    (hcount : 0 < GoldbachCount n) :
    GoldbachRepresentation n := by
  rw [GoldbachCount, GoldbachPrimeSubWitnesses, Finset.card_pos] at hcount
  rcases hcount with ⟨p, hp_mem⟩
  rcases Finset.mem_filter.mp hp_mem with ⟨hp_range, hp_props⟩
  rcases hp_props with ⟨hp_prime, hsub_prime⟩
  have hp_le : p ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hp_range)
  exact goldbachRepresentation_of_prime_sub hp_prime hsub_prime hp_le

theorem goldbachCount_pos_of_representation {n : Nat}
    (representation : GoldbachRepresentation n) :
    0 < GoldbachCount n := by
  rcases representation with ⟨p, q, hp, hq, hsum⟩
  rw [GoldbachCount, GoldbachPrimeSubWitnesses, Finset.card_pos]
  refine ⟨p, ?_⟩
  rw [Finset.mem_filter]
  constructor
  · rw [Finset.mem_range]
    have hp_le : p ≤ n := by
      rw [← hsum]
      exact Nat.le_add_right p q
    exact Nat.lt_succ_of_le hp_le
  · constructor
    · exact hp
    · have hsub : n - p = q := by
        rw [← hsum]
        exact Nat.add_sub_cancel_left p q
      simpa [hsub] using hq

theorem goldbachCount_pos_iff_representation {n : Nat} :
    0 < GoldbachCount n ↔ GoldbachRepresentation n := by
  constructor
  · exact goldbachRepresentation_of_count_pos
  · exact goldbachCount_pos_of_representation

theorem goldbachAbove_of_count_positive_above {B : Nat}
    (count_positive : GoldbachCountPositiveAbove B) :
    GoldbachAbove B := by
  intro n hBn hEven
  exact goldbachRepresentation_of_count_pos (count_positive n hBn hEven)

theorem goldbachCountPositiveAbove_iff_goldbachAbove {B : Nat} :
    GoldbachCountPositiveAbove B ↔ GoldbachAbove B := by
  constructor
  · exact goldbachAbove_of_count_positive_above
  · intro above n hBn hEven
    exact goldbachCount_pos_of_representation (above n hBn hEven)

theorem goldbachCountPositiveAbove_mono {B C : Nat}
    (hBC : B ≤ C)
    (count_positive : GoldbachCountPositiveAbove B) :
    GoldbachCountPositiveAbove C := by
  intro n hCn hEven
  exact count_positive n (lt_of_le_of_lt hBC hCn) hEven

theorem strongGoldbach_of_finite_and_above {B : Nat}
    (finite : GoldbachUpTo B)
    (above : GoldbachAbove B) :
    StrongGoldbach := by
  intro n hn hEven
  by_cases hle : n ≤ B
  · exact finite n hn hle hEven
  · exact above n (Nat.lt_of_not_ge hle) hEven

theorem goldbachUpTo_of_strongGoldbach {B : Nat}
    (strong : StrongGoldbach) :
    GoldbachUpTo B := by
  intro n hn _hle hEven
  exact strong n hn hEven

theorem goldbachAbove_of_strongGoldbach {B : Nat}
    (hB : 2 ≤ B)
    (strong : StrongGoldbach) :
    GoldbachAbove B := by
  intro n _hgt hEven
  have hn : 2 < n := lt_of_le_of_lt hB _hgt
  exact strong n hn hEven

theorem strongGoldbach_iff_finite_and_above {B : Nat} (hB : 2 ≤ B) :
    StrongGoldbach ↔ GoldbachUpTo B ∧ GoldbachAbove B := by
  constructor
  · intro strong
    exact ⟨goldbachUpTo_of_strongGoldbach strong,
      goldbachAbove_of_strongGoldbach hB strong⟩
  · intro h
    exact strongGoldbach_of_finite_and_above h.1 h.2

theorem goldbachAbove_mono {B C : Nat}
    (hBC : B ≤ C)
    (above : GoldbachAbove B) :
    GoldbachAbove C := by
  intro n hCn hEven
  exact above n (lt_of_le_of_lt hBC hCn) hEven

structure CertificateEntry where
  n : Nat
  p : Nat
  q : Nat
deriving Repr, DecidableEq

def CertificateEntry.Valid (entry : CertificateEntry) : Prop :=
  Even entry.n ∧
    2 < entry.n ∧
    Nat.Prime entry.p ∧
    Nat.Prime entry.q ∧
    entry.p + entry.q = entry.n

def CertificateEntry.ValidCheck (entry : CertificateEntry) : Prop :=
  entry.n % 2 = 0 ∧
    2 < entry.n ∧
    Nat.Prime entry.p ∧
    Nat.Prime entry.q ∧
    entry.p + entry.q = entry.n

theorem CertificateEntry.valid_of_validCheck {entry : CertificateEntry}
    (valid : entry.ValidCheck) :
    entry.Valid := by
  rcases valid with ⟨hEven, hgt, hp, hq, hsum⟩
  exact ⟨Nat.even_iff.mpr hEven, hgt, hp, hq, hsum⟩

structure VerifiedCertificateEntry where
  entry : CertificateEntry
  valid : entry.Valid

def verifiedCertificateEntries
    (entries : List VerifiedCertificateEntry) : List CertificateEntry :=
  entries.map (fun entry => entry.entry)

def CertificateCovers (B : Nat) (entries : List CertificateEntry) : Prop :=
  ∀ n : Nat,
    2 < n →
    n ≤ B →
    Even n →
    ∃ entry ∈ entries, entry.n = n ∧ entry.Valid

def CertificateEntry.matchesValidCheck (n : Nat) (entry : CertificateEntry) : Bool :=
  decide
    (entry.n = n ∧
      entry.n % 2 = 0 ∧
      2 < entry.n ∧
      2 ≤ entry.p ∧
      Nat.minFac entry.p = entry.p ∧
      2 ≤ entry.q ∧
      Nat.minFac entry.q = entry.q ∧
      entry.p + entry.q = entry.n)

def CertificateHasValidEntryCheck (n : Nat) (entries : List CertificateEntry) : Bool :=
  entries.any (fun entry => entry.matchesValidCheck n)

def CertificateCoversListCheck
    (B : Nat) (entries : List CertificateEntry) : Bool :=
  (List.range (B + 1)).all fun n =>
    if decide (2 < n ∧ n ≤ B ∧ n % 2 = 0) then
      CertificateHasValidEntryCheck n entries
    else
      true

def VerifiedCertificateHasEntryCheck
    (n : Nat) (entries : List VerifiedCertificateEntry) : Bool :=
  entries.any (fun entry => decide (entry.entry.n = n))

def VerifiedCertificateCoversListCheck
    (B : Nat) (entries : List VerifiedCertificateEntry) : Bool :=
  (List.range (B + 1)).all fun n =>
    if decide (2 < n ∧ n ≤ B ∧ n % 2 = 0) then
      VerifiedCertificateHasEntryCheck n entries
    else
      true

theorem certificateHasValidEntry_of_check
    {n : Nat} {entries : List CertificateEntry}
    (checked : CertificateHasValidEntryCheck n entries = true) :
    ∃ entry ∈ entries, entry.n = n ∧ entry.ValidCheck := by
  rcases List.any_eq_true.mp checked with ⟨entry, hentry_mem, hentry_check⟩
  simp only [CertificateEntry.matchesValidCheck] at hentry_check
  rcases of_decide_eq_true hentry_check with
    ⟨hentry_n, hmod, hgt, hp_two, hp_minFac, hq_two, hq_minFac, hsum⟩
  exact ⟨entry, hentry_mem, hentry_n, hmod, hgt,
    Nat.prime_def_minFac.mpr ⟨hp_two, hp_minFac⟩,
    Nat.prime_def_minFac.mpr ⟨hq_two, hq_minFac⟩, hsum⟩

theorem verifiedCertificateHasEntry_of_check
    {n : Nat} {entries : List VerifiedCertificateEntry}
    (checked : VerifiedCertificateHasEntryCheck n entries = true) :
    ∃ entry ∈ entries, entry.entry.n = n := by
  simpa [VerifiedCertificateHasEntryCheck]
    using (List.any_eq_true.mp checked)

theorem certificateCovers_of_list_check {B : Nat} {entries : List CertificateEntry}
    (covers : CertificateCoversListCheck B entries = true) :
    CertificateCovers B entries := by
  intro n hn hle hEven
  have hmem : n ∈ List.range (B + 1) :=
    List.mem_range.mpr (Nat.lt_succ_of_le hle)
  have hconditions : 2 < n ∧ n ≤ B ∧ n % 2 = 0 :=
    ⟨hn, hle, Nat.even_iff.mp hEven⟩
  have hentry_check : CertificateHasValidEntryCheck n entries = true := by
    simpa [CertificateCoversListCheck, hconditions]
      using (List.all_eq_true.mp covers n hmem)
  rcases certificateHasValidEntry_of_check hentry_check with
    ⟨entry, hentry_mem, hentry_n, hentry_valid⟩
  exact ⟨entry, hentry_mem, hentry_n,
    CertificateEntry.valid_of_validCheck hentry_valid⟩

theorem certificateCovers_of_verified_list_check
    {B : Nat} {entries : List VerifiedCertificateEntry}
    (covers : VerifiedCertificateCoversListCheck B entries = true) :
    CertificateCovers B (verifiedCertificateEntries entries) := by
  intro n hn hle hEven
  have hmem : n ∈ List.range (B + 1) :=
    List.mem_range.mpr (Nat.lt_succ_of_le hle)
  have hconditions : 2 < n ∧ n ≤ B ∧ n % 2 = 0 :=
    ⟨hn, hle, Nat.even_iff.mp hEven⟩
  have hentry_check : VerifiedCertificateHasEntryCheck n entries = true := by
    simpa [VerifiedCertificateCoversListCheck, hconditions]
      using (List.all_eq_true.mp covers n hmem)
  rcases verifiedCertificateHasEntry_of_check hentry_check with
    ⟨entry, hentry_mem, hentry_n⟩
  exact ⟨entry.entry, List.mem_map.mpr ⟨entry, hentry_mem, rfl⟩,
    hentry_n, entry.valid⟩

theorem goldbachUpTo_of_certificate {B : Nat} {entries : List CertificateEntry}
    (covers : CertificateCovers B entries) :
    GoldbachUpTo B := by
  intro n hn hle hEven
  rcases covers n hn hle hEven with ⟨entry, _entry_mem, entry_n, entry_valid⟩
  rcases entry_valid with ⟨_entry_even, _entry_gt_two, hp, hq, hsum⟩
  exact ⟨entry.p, entry.q, hp, hq, by simpa [entry_n] using hsum⟩

def certificate20Verified : List VerifiedCertificateEntry :=
  [ { entry := { n := 4, p := 2, q := 2 },
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
      valid := by norm_num [CertificateEntry.Valid] } ]

def certificate20 : List CertificateEntry :=
  verifiedCertificateEntries certificate20Verified

theorem certificate20_covers : CertificateCovers 20 certificate20 := by
  exact certificateCovers_of_verified_list_check
    (by
      unfold VerifiedCertificateCoversListCheck VerifiedCertificateHasEntryCheck
      rfl)

theorem goldbachUpTo20 : GoldbachUpTo 20 :=
  goldbachUpTo_of_certificate certificate20_covers

theorem strongGoldbach_from_certificate20_and_analytic_bridge
    (analytic_goldbach_above_20 : GoldbachAbove 20) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_above goldbachUpTo20 analytic_goldbach_above_20

end Gdbh
