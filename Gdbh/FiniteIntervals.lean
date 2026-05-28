import Mathlib.Tactic.Order
import Gdbh.Goldbach

namespace Gdbh

def GoldbachBetween (A B : Nat) : Prop :=
  ∀ n : Nat, A < n → n ≤ B → Even n → GoldbachRepresentation n

def CertificateCoversBetween
    (A B : Nat) (entries : List CertificateEntry) : Prop :=
  ∀ n : Nat,
    A < n →
    n ≤ B →
    Even n →
    ∃ entry ∈ entries, entry.n = n ∧ entry.Valid

def CertificateCoversBetweenListCheck
    (A B : Nat) (entries : List CertificateEntry) : Bool :=
  (List.range' (A + 1) (B - A)).all fun n =>
    if decide (n ≤ B ∧ n % 2 = 0) then
      CertificateHasValidEntryCheck n entries
    else
      true

def VerifiedCertificateCoversBetweenListCheck
    (A B : Nat) (entries : List VerifiedCertificateEntry) : Bool :=
  (List.range' (A + 1) (B - A)).all fun n =>
    if decide (n ≤ B ∧ n % 2 = 0) then
      VerifiedCertificateHasEntryCheck n entries
    else
      true

theorem certificateCoversBetween_of_list_check
    {A B : Nat} {entries : List CertificateEntry}
    (covers : CertificateCoversBetweenListCheck A B entries = true) :
    CertificateCoversBetween A B entries := by
  intro n hAn hle hEven
  have hmem : n ∈ List.range' (A + 1) (B - A) := by
    rw [List.mem_range']
    refine ⟨n - (A + 1), ?_, ?_⟩ <;> omega
  have hconditions : n ≤ B ∧ n % 2 = 0 :=
    ⟨hle, Nat.even_iff.mp hEven⟩
  have hentry_check : CertificateHasValidEntryCheck n entries = true := by
    simpa [CertificateCoversBetweenListCheck, hconditions]
      using (List.all_eq_true.mp covers n hmem)
  rcases certificateHasValidEntry_of_check hentry_check with
    ⟨entry, hentry_mem, hentry_n, hentry_valid⟩
  exact ⟨entry, hentry_mem, hentry_n,
    CertificateEntry.valid_of_validCheck hentry_valid⟩

theorem certificateCoversBetween_of_verified_list_check
    {A B : Nat} {entries : List VerifiedCertificateEntry}
    (covers : VerifiedCertificateCoversBetweenListCheck A B entries = true) :
    CertificateCoversBetween A B (verifiedCertificateEntries entries) := by
  intro n hAn hle hEven
  have hmem : n ∈ List.range' (A + 1) (B - A) := by
    rw [List.mem_range']
    refine ⟨n - (A + 1), ?_, ?_⟩ <;> omega
  have hconditions : n ≤ B ∧ n % 2 = 0 :=
    ⟨hle, Nat.even_iff.mp hEven⟩
  have hentry_check : VerifiedCertificateHasEntryCheck n entries = true := by
    simpa [VerifiedCertificateCoversBetweenListCheck, hconditions]
      using (List.all_eq_true.mp covers n hmem)
  rcases verifiedCertificateHasEntry_of_check hentry_check with
    ⟨entry, hentry_mem, hentry_n⟩
  exact ⟨entry.entry, List.mem_map.mpr ⟨entry, hentry_mem, rfl⟩,
    hentry_n, entry.valid⟩

theorem goldbachBetween_of_certificate
    {A B : Nat} {entries : List CertificateEntry}
    (covers : CertificateCoversBetween A B entries) :
    GoldbachBetween A B := by
  intro n hAn hle hEven
  rcases covers n hAn hle hEven with
    ⟨entry, _entry_mem, entry_n, entry_valid⟩
  rcases entry_valid with ⟨_entry_even, _entry_gt_two, hp, hq, hsum⟩
  exact ⟨entry.p, entry.q, hp, hq, by simpa [entry_n] using hsum⟩

theorem goldbachUpTo_of_between_two {B : Nat}
    (between : GoldbachBetween 2 B) :
    GoldbachUpTo B := by
  intro n hn hle hEven
  exact between n hn hle hEven

theorem goldbachUpTo_of_upTo_and_between {A B : Nat}
    (upTo : GoldbachUpTo A)
    (between : GoldbachBetween A B) :
    GoldbachUpTo B := by
  intro n hn hle hEven
  by_cases hleA : n ≤ A
  · exact upTo n hn hleA hEven
  · exact between n (Nat.lt_of_not_ge hleA) hle hEven

theorem goldbachBetween_of_between_and_between {A B C : Nat}
    (first : GoldbachBetween A B)
    (second : GoldbachBetween B C) :
    GoldbachBetween A C := by
  intro n hAn hleC hEven
  by_cases hleB : n ≤ B
  · exact first n hAn hleB hEven
  · exact second n (Nat.lt_of_not_ge hleB) hleC hEven

end Gdbh
