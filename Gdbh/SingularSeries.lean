import Mathlib

namespace Gdbh

noncomputable def goldbachOddPrimeLocalFactor (p : Nat) : ℝ :=
  ((p : ℝ) - 1) / ((p : ℝ) - 2)

noncomputable def goldbachSingularSeriesLocalPrimes (n : Nat) : Finset Nat :=
  n.divisors.filter (fun p => Nat.Prime p ∧ 2 < p)

noncomputable def goldbachSingularSeriesLocalMultiplier (n : Nat) : ℝ :=
  (goldbachSingularSeriesLocalPrimes n).prod goldbachOddPrimeLocalFactor

noncomputable def goldbachSingularSeriesFromBase (base : ℝ) (n : Nat) : ℝ :=
  base * goldbachSingularSeriesLocalMultiplier n

/--
Certificate-friendly normalized Goldbach singular-series shape with a fixed
conservative base.  This packages the easy local-factor lower-bound part of the
Hardy-Littlewood handoff.  It does not prove that the raw von Mangoldt
convolution has this function as its main term; that remains the separate
`raw_normalized_error_bound` obligation.
-/
noncomputable def goldbachSingularSeriesQuarterBase : ℝ := 1 / 4

noncomputable def goldbachSingularSeriesFromQuarter (n : Nat) : ℝ :=
  goldbachSingularSeriesFromBase goldbachSingularSeriesQuarterBase n

theorem one_le_goldbachOddPrimeLocalFactor {p : Nat} (hp : 2 < p) :
    1 ≤ goldbachOddPrimeLocalFactor p := by
  have hden_pos : 0 < (p : ℝ) - 2 := by
    exact sub_pos.mpr (by exact_mod_cast hp)
  have hden_le_num : (p : ℝ) - 2 ≤ (p : ℝ) - 1 := by linarith
  simpa [goldbachOddPrimeLocalFactor] using
    (one_le_div hden_pos).mpr hden_le_num

theorem one_le_goldbachSingularSeriesLocalMultiplier (n : Nat) :
    1 ≤ goldbachSingularSeriesLocalMultiplier n := by
  classical
  dsimp [goldbachSingularSeriesLocalMultiplier]
  exact Finset.one_le_prod (fun p hp => by
    rw [goldbachSingularSeriesLocalPrimes, Finset.mem_filter] at hp
    exact one_le_goldbachOddPrimeLocalFactor hp.2.2)

theorem base_le_goldbachSingularSeriesFromBase
    {base : ℝ} (hbase_nonneg : 0 ≤ base) (n : Nat) :
    base ≤ goldbachSingularSeriesFromBase base n := by
  exact le_mul_of_one_le_right hbase_nonneg
    (one_le_goldbachSingularSeriesLocalMultiplier n)

theorem coefficient_le_goldbachSingularSeriesFromBase
    {coefficient base : ℝ}
    (hcoeff_base : coefficient ≤ base)
    (hbase_nonneg : 0 ≤ base)
    (n : Nat) :
    coefficient ≤ goldbachSingularSeriesFromBase base n :=
  hcoeff_base.trans
    (base_le_goldbachSingularSeriesFromBase hbase_nonneg n)

theorem goldbachSingularSeriesFromBase_lower_bound
    {threshold : Nat} {coefficient base : ℝ}
    (hcoeff_base : coefficient ≤ base)
    (hbase_nonneg : 0 ≤ base) :
    ∀ n : Nat, threshold < n → Even n →
      coefficient ≤ goldbachSingularSeriesFromBase base n := by
  intro n _hn _heven
  exact coefficient_le_goldbachSingularSeriesFromBase
    hcoeff_base hbase_nonneg n

theorem one_fourth_le_goldbachSingularSeriesFromQuarter
    {threshold : Nat} :
    ∀ n : Nat, threshold < n → Even n →
      (1 / 4 : ℝ) ≤ goldbachSingularSeriesFromQuarter n := by
  simpa [goldbachSingularSeriesFromQuarter,
    goldbachSingularSeriesQuarterBase] using
    (goldbachSingularSeriesFromBase_lower_bound
      (threshold := threshold)
      (coefficient := (1 / 4 : ℝ))
      (base := (1 / 4 : ℝ))
      (by norm_num)
      (by norm_num))

end Gdbh
