import Gdbh.PathC_GoldbachLocalFactor
import Gdbh.SingularSeries

/-!
# Path C -- Goldbach singular multiplier average tools

This file starts the elementary average-order toolchain for the corrected
singular-factor route.  Its first task is to identify the Path C multiplier
with the standard finite singular-series product over odd prime divisors.

The average-order bound itself is deliberately kept separate: the theorem
below removes the distracting `if p ∣ n then ... else 1` truncation shape and
leaves the next agent with the usual odd-prime-divisor product.
-/

namespace Gdbh
namespace PathCSingularAverage

open scoped BigOperators
open Gdbh.PathCGoldbachLocalFactor

/-- Odd primes up to `N`, used as the fixed ambient prime set for finite
average expansions. -/
noncomputable def oddPrimeSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 3 N).filter Nat.Prime

/-- The additive part of the Goldbach singular local factor. -/
noncomputable def singularPrimeWeight (p : ℕ) : ℝ :=
  1 / ((p : ℝ) - 2)

/-- The local singular weight is nonnegative for odd primes in the ambient
range. -/
theorem singularPrimeWeight_nonneg {p : ℕ} (hp3 : 3 ≤ p) :
    0 ≤ singularPrimeWeight p := by
  unfold singularPrimeWeight
  have hpos : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (2 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 2 < p)
    linarith
  positivity

/-- The Path C local correction factor equals the standard odd-prime local
factor used by `SingularSeries.lean`. -/
theorem goldbachSingularFactorTerm_eq_seriesLocalFactor (p : ℕ) (hp : 2 < p) :
    (1 + 1 / ((p : ℝ) - 2)) = goldbachOddPrimeLocalFactor p := by
  have hden : (p : ℝ) - 2 ≠ 0 := by
    have : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    linarith
  simp [goldbachOddPrimeLocalFactor]
  field_simp [hden]
  ring

/-- Odd prime divisors of `n` are exactly the primes in `[3, n]` that divide
`n`. -/
theorem goldbachSingularSeriesLocalPrimes_eq_filter_dvd (n : ℕ) :
    n.divisors.filter (fun p => Nat.Prime p ∧ 2 < p) =
      (Finset.Icc 3 n).filter (fun p => Nat.Prime p ∧ p ∣ n) := by
  classical
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpdivs, hpprime, hp2⟩
    have hpdvd : p ∣ n := Nat.dvd_of_mem_divisors hpdivs
    have hple : p ≤ n := Nat.divisor_le hpdivs
    refine Finset.mem_filter.mpr ⟨?_, hpprime, hpdvd⟩
    exact Finset.mem_Icc.mpr ⟨by omega, hple⟩
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpIcc, hpprime, hpdvd⟩
    rcases Finset.mem_Icc.mp hpIcc with ⟨hp3, hple⟩
    have hnne : n ≠ 0 := by omega
    refine Finset.mem_filter.mpr ⟨?_, hpprime, by omega⟩
    exact Nat.mem_divisors.mpr ⟨hpdvd, hnne⟩

/-- The Path C multiplier is the standard finite product over odd prime
divisors of `n`. -/
theorem goldbachSingularMultiplier_eq_seriesLocalMultiplier (n : ℕ) :
    goldbachSingularMultiplier n = goldbachSingularSeriesLocalMultiplier n := by
  classical
  unfold goldbachSingularMultiplier truncatedGoldbachSingularMultiplier
  unfold goldbachSingularSeriesLocalMultiplier goldbachSingularSeriesLocalPrimes
  rw [goldbachSingularSeriesLocalPrimes_eq_filter_dvd n]
  let s : Finset ℕ := (Finset.Icc 3 n).filter (fun p => Nat.Prime p ∧ p ∣ n)
  let t : Finset ℕ := (Finset.Icc 3 n).filter Nat.Prime
  have hsub : s ⊆ t := by
    intro p hp
    dsimp [s, t] at hp ⊢
    rcases Finset.mem_filter.mp hp with ⟨hpIcc, hpprime, _⟩
    exact Finset.mem_filter.mpr ⟨hpIcc, hpprime⟩
  have hprod_subset :
      (∏ p ∈ s, (if p ∣ n then (1 + 1 / ((p : ℝ) - 2)) else 1)) =
        ∏ p ∈ t, (if p ∣ n then (1 + 1 / ((p : ℝ) - 2)) else 1) := by
    exact Finset.prod_subset hsub (by
      intro p hpt hps
      dsimp [s, t] at hpt hps
      rcases Finset.mem_filter.mp hpt with ⟨hpIcc, hpprime⟩
      have hp_not_dvd : ¬ p ∣ n := by
        intro hpdvd
        exact hps (Finset.mem_filter.mpr ⟨hpIcc, hpprime, hpdvd⟩)
      simp [hp_not_dvd])
  have hprod_eq :
      (∏ p ∈ s, goldbachOddPrimeLocalFactor p) =
        ∏ p ∈ s, (if p ∣ n then (1 + 1 / ((p : ℝ) - 2)) else 1) := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    dsimp [s] at hp
    rcases Finset.mem_filter.mp hp with ⟨hpIcc, _hpprime, hpdvd⟩
    rcases Finset.mem_Icc.mp hpIcc with ⟨hp3, _⟩
    rw [if_pos hpdvd]
    exact (goldbachSingularFactorTerm_eq_seriesLocalFactor p (by omega : 2 < p)).symm
  change (∏ p ∈ t, (if p ∣ n then (1 + 1 / ((p : ℝ) - 2)) else 1)) =
    ∏ p ∈ s, goldbachOddPrimeLocalFactor p
  rw [hprod_eq, hprod_subset]

/-- Sum-level restatement of the Path C singular multiplier in the standard
odd-prime-divisor product form. -/
theorem sum_goldbachSingularMultiplier_eq_seriesLocalMultiplier (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, goldbachSingularMultiplier n) =
      ∑ n ∈ Finset.Icc 2 N, goldbachSingularSeriesLocalMultiplier n := by
  refine Finset.sum_congr rfl ?_
  intro n _hn
  exact goldbachSingularMultiplier_eq_seriesLocalMultiplier n

/-- For `2 ≤ n ≤ N`, the singular multiplier can be evaluated as a product
over the fixed ambient odd-prime set up to `N`; primes above `n` contribute
the neutral factor `1`. -/
theorem goldbachSingularMultiplier_fixedProduct
    (N n : ℕ) (hn2 : 2 ≤ n) (hnN : n ≤ N) :
    goldbachSingularMultiplier n =
      ∏ p ∈ oddPrimeSet N,
        if p ∣ n then (1 + singularPrimeWeight p) else 1 := by
  classical
  unfold goldbachSingularMultiplier truncatedGoldbachSingularMultiplier
  unfold oddPrimeSet singularPrimeWeight
  refine Finset.prod_subset ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, le_trans hp.1.2 hnN⟩, hp.2⟩
  · intro p hpN hpn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hpN hpn
    have hp_gt_n : n < p := by
      by_contra hnot
      have hp_le_n : p ≤ n := by omega
      exact hpn ⟨⟨hpN.1.1, hp_le_n⟩, hpN.2⟩
    have hp_not_dvd : ¬ p ∣ n := by
      intro hpdvd
      have hple : p ≤ n := Nat.le_of_dvd (by omega : 0 < n) hpdvd
      omega
    simp [hp_not_dvd]

/-- Fixed-ambient finite powerset expansion of the Goldbach singular
multiplier.  This is the form designed for summing first over `n` and then
swapping the finite sums. -/
theorem goldbachSingularMultiplier_powerset_expand
    (N n : ℕ) (hn2 : 2 ≤ n) (hnN : n ≤ N) :
    goldbachSingularMultiplier n =
      ∑ T ∈ (oddPrimeSet N).powerset,
        ∏ p ∈ T, if p ∣ n then singularPrimeWeight p else 0 := by
  classical
  rw [goldbachSingularMultiplier_fixedProduct N n hn2 hnN]
  let f : ℕ → ℝ := fun p => if p ∣ n then singularPrimeWeight p else 0
  let g : ℕ → ℝ := fun _ => 1
  have hlocal :
      (∏ p ∈ oddPrimeSet N,
          (if p ∣ n then (1 + singularPrimeWeight p) else 1)) =
        ∏ p ∈ oddPrimeSet N, (f p + g p) := by
    refine Finset.prod_congr rfl ?_
    intro p _hp
    dsimp [f, g]
    by_cases hpdvd : p ∣ n
    · simp [hpdvd]
      ring
    · simp [hpdvd]
  rw [hlocal, Finset.prod_add]
  refine Finset.sum_congr rfl ?_
  intro T _hT
  simp [f, g]

/-- Each fixed powerset term is nonnegative. -/
theorem singularPowersetTerm_nonneg
    {N n : ℕ} {T : Finset ℕ} (hT : T ∈ (oddPrimeSet N).powerset) :
    0 ≤ ∏ p ∈ T, if p ∣ n then singularPrimeWeight p else 0 := by
  classical
  refine Finset.prod_nonneg ?_
  intro p hpT
  by_cases hpdvd : p ∣ n
  · rw [if_pos hpdvd]
    rw [Finset.mem_powerset] at hT
    have hpOdd : p ∈ oddPrimeSet N := hT hpT
    unfold oddPrimeSet at hpOdd
    rcases Finset.mem_filter.mp hpOdd with ⟨hpIcc, _hpprime⟩
    rcases Finset.mem_Icc.mp hpIcc with ⟨hp3, _⟩
    exact singularPrimeWeight_nonneg hp3
  · simp [hpdvd]

/-- Odd primes in the fixed ambient set are pairwise relatively prime. -/
theorem oddPrimeSet_pairwise_isRelPrime (N : ℕ) :
    ((oddPrimeSet N : Finset ℕ) : Set ℕ).Pairwise
      (fun p q => IsRelPrime p q) := by
  intro p hp q hq hpq
  unfold oddPrimeSet at hp hq
  rcases Finset.mem_filter.mp hp with ⟨_hpIcc, hpprime⟩
  rcases Finset.mem_filter.mp hq with ⟨_hqIcc, hqprime⟩
  exact Nat.coprime_iff_isRelPrime.mp
    ((Nat.coprime_primes hpprime hqprime).mpr hpq)

/-- If every prime in a powerset term divides `n`, then the squarefree
index product also divides `n`. -/
theorem singularPowersetIndexProduct_dvd
    {N n : ℕ} {T : Finset ℕ} (hT : T ∈ (oddPrimeSet N).powerset)
    (hAll : ∀ p ∈ T, p ∣ n) :
    (∏ p ∈ T, p) ∣ n := by
  classical
  rw [Finset.mem_powerset] at hT
  have hpair : ((T : Finset ℕ) : Set ℕ).Pairwise
      (fun p q => IsRelPrime p q) := by
    intro p hp q hq hpq
    exact oddPrimeSet_pairwise_isRelPrime N (hT hp) (hT hq) hpq
  simpa using
    (Finset.prod_dvd_of_isRelPrime
      (t := T) (s := fun p : ℕ => p) (z := n) hpair hAll)

/-- The coefficient attached to a powerset term is nonnegative. -/
theorem singularPowersetCoeff_nonneg
    {N : ℕ} {T : Finset ℕ} (hT : T ∈ (oddPrimeSet N).powerset) :
    0 ≤ ∏ p ∈ T, singularPrimeWeight p := by
  rw [Finset.mem_powerset] at hT
  refine Finset.prod_nonneg ?_
  intro p hpT
  have hpOdd : p ∈ oddPrimeSet N := hT hpT
  unfold oddPrimeSet at hpOdd
  rcases Finset.mem_filter.mp hpOdd with ⟨hpIcc, _hpprime⟩
  rcases Finset.mem_Icc.mp hpIcc with ⟨hp3, _⟩
  exact singularPrimeWeight_nonneg hp3

/-- If all primes in `T` divide `n`, the corresponding powerset term is just
its coefficient. -/
theorem singularPowersetTerm_eq_coeff_of_forall_dvd
    {n : ℕ} {T : Finset ℕ} (hAll : ∀ p ∈ T, p ∣ n) :
    (∏ p ∈ T, if p ∣ n then singularPrimeWeight p else 0) =
      ∏ p ∈ T, singularPrimeWeight p := by
  refine Finset.prod_congr rfl ?_
  intro p hpT
  simp [hAll p hpT]

/-- If some prime in `T` does not divide `n`, the corresponding powerset
term is zero. -/
theorem singularPowersetTerm_eq_zero_of_not_forall_dvd
    {n : ℕ} {T : Finset ℕ} (hNotAll : ¬ ∀ p ∈ T, p ∣ n) :
    (∏ p ∈ T, if p ∣ n then singularPrimeWeight p else 0) = 0 := by
  classical
  push Not at hNotAll
  rcases hNotAll with ⟨p, hpT, hpndvd⟩
  exact Finset.prod_eq_zero hpT (by simp [hpndvd])

/-- A powerset term vanishes unless the squarefree index product divides
`n`. -/
theorem singularPowersetTerm_eq_zero_of_not_indexProduct_dvd
    {N n : ℕ} {T : Finset ℕ} (hT : T ∈ (oddPrimeSet N).powerset)
    (hndvd : ¬ (∏ p ∈ T, p) ∣ n) :
    (∏ p ∈ T, if p ∣ n then singularPrimeWeight p else 0) = 0 := by
  classical
  by_cases hAll : ∀ p ∈ T, p ∣ n
  · exact False.elim (hndvd (singularPowersetIndexProduct_dvd hT hAll))
  · exact singularPowersetTerm_eq_zero_of_not_forall_dvd hAll

/-- Pointwise domination of a powerset term by the indicator of divisibility
by its squarefree index product. -/
theorem singularPowersetTerm_le_indexProduct_indicator
    {N n : ℕ} {T : Finset ℕ} (hT : T ∈ (oddPrimeSet N).powerset) :
    (∏ p ∈ T, if p ∣ n then singularPrimeWeight p else 0) ≤
      if (∏ p ∈ T, p) ∣ n then
        ∏ p ∈ T, singularPrimeWeight p
      else 0 := by
  classical
  by_cases hdiv : (∏ p ∈ T, p) ∣ n
  · rw [if_pos hdiv]
    by_cases hAll : ∀ p ∈ T, p ∣ n
    · rw [singularPowersetTerm_eq_coeff_of_forall_dvd hAll]
    · rw [singularPowersetTerm_eq_zero_of_not_forall_dvd hAll]
      exact singularPowersetCoeff_nonneg hT
  · rw [if_neg hdiv]
    rw [singularPowersetTerm_eq_zero_of_not_indexProduct_dvd hT hdiv]

/-- The interval `[2, N]` contains at most `N / d` multiples of `d`. -/
theorem card_Icc_two_filter_dvd_le_div (N d : ℕ) :
    ((Finset.Icc 2 N).filter (fun n => d ∣ n)).card ≤ N / d := by
  have hsub :
      ((Finset.Icc 2 N).filter (fun n => d ∣ n)) ⊆
        ((Finset.Ioc 0 N).filter (fun n => d ∣ n)) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnIcc, hdvd⟩
    rcases Finset.mem_Icc.mp hnIcc with ⟨hn2, hnN⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨by omega, hnN⟩, hdvd⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.Ioc_filter_dvd_card_eq_div] at hcard
  exact hcard

/-- Real-valued version of `card_Icc_two_filter_dvd_le_div`. -/
theorem card_Icc_two_filter_dvd_le_div_real (N d : ℕ) :
    (((Finset.Icc 2 N).filter (fun n => d ∣ n)).card : ℝ) ≤
      ((N / d : ℕ) : ℝ) := by
  exact_mod_cast card_Icc_two_filter_dvd_le_div N d

/-- Summing a constant over the multiples of `d` in `[2, N]`. -/
theorem sum_Icc_two_ite_dvd_const (N d : ℕ) (a : ℝ) :
    (∑ n ∈ Finset.Icc 2 N, if d ∣ n then a else 0) =
      a * (((Finset.Icc 2 N).filter (fun n => d ∣ n)).card : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  simp [mul_comm]

/-- Each fixed powerset term has total mass bounded by its coefficient times
the elementary count of multiples of its squarefree index product. -/
theorem sum_singularPowersetTerm_le_coeff_mul_div
    {N : ℕ} {T : Finset ℕ} (hT : T ∈ (oddPrimeSet N).powerset) :
    (∑ n ∈ Finset.Icc 2 N,
        ∏ p ∈ T, if p ∣ n then singularPrimeWeight p else 0) ≤
      (∏ p ∈ T, singularPrimeWeight p) *
        ((N / (∏ p ∈ T, p) : ℕ) : ℝ) := by
  classical
  let d : ℕ := ∏ p ∈ T, p
  let a : ℝ := ∏ p ∈ T, singularPrimeWeight p
  have hpoint : ∀ n ∈ Finset.Icc 2 N,
      (∏ p ∈ T, if p ∣ n then singularPrimeWeight p else 0) ≤
        if d ∣ n then a else 0 := by
    intro n _hn
    simpa [d, a] using
      (singularPowersetTerm_le_indexProduct_indicator
        (N := N) (n := n) (T := T) hT)
  have hsum_le :
      (∑ n ∈ Finset.Icc 2 N,
          ∏ p ∈ T, if p ∣ n then singularPrimeWeight p else 0) ≤
        ∑ n ∈ Finset.Icc 2 N, if d ∣ n then a else 0 :=
    Finset.sum_le_sum hpoint
  have hindicator :
      (∑ n ∈ Finset.Icc 2 N, if d ∣ n then a else 0) =
        a * (((Finset.Icc 2 N).filter (fun n => d ∣ n)).card : ℝ) :=
    sum_Icc_two_ite_dvd_const N d a
  have hcard :
      (((Finset.Icc 2 N).filter (fun n => d ∣ n)).card : ℝ) ≤
        ((N / d : ℕ) : ℝ) :=
    card_Icc_two_filter_dvd_le_div_real N d
  have ha_nonneg : 0 ≤ a := by
    simpa [a] using singularPowersetCoeff_nonneg hT
  calc
    (∑ n ∈ Finset.Icc 2 N,
        ∏ p ∈ T, if p ∣ n then singularPrimeWeight p else 0)
        ≤ ∑ n ∈ Finset.Icc 2 N, if d ∣ n then a else 0 := hsum_le
    _ = a * (((Finset.Icc 2 N).filter (fun n => d ∣ n)).card : ℝ) := hindicator
    _ ≤ a * ((N / d : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hcard ha_nonneg
    _ = (∏ p ∈ T, singularPrimeWeight p) *
        ((N / (∏ p ∈ T, p) : ℕ) : ℝ) := by
          simp [a, d]

/-- Summed version of the fixed powerset expansion with the finite sums
swapped. -/
theorem sum_goldbachSingularMultiplier_powerset_expand (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, goldbachSingularMultiplier n) =
      ∑ T ∈ (oddPrimeSet N).powerset,
        ∑ n ∈ Finset.Icc 2 N,
          ∏ p ∈ T, if p ∣ n then singularPrimeWeight p else 0 := by
  classical
  calc
    (∑ n ∈ Finset.Icc 2 N, goldbachSingularMultiplier n)
        = ∑ n ∈ Finset.Icc 2 N,
            ∑ T ∈ (oddPrimeSet N).powerset,
              ∏ p ∈ T, if p ∣ n then singularPrimeWeight p else 0 := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rcases Finset.mem_Icc.mp hn with ⟨hn2, hnN⟩
            exact goldbachSingularMultiplier_powerset_expand N n hn2 hnN
    _ = ∑ T ∈ (oddPrimeSet N).powerset,
        ∑ n ∈ Finset.Icc 2 N,
          ∏ p ∈ T, if p ∣ n then singularPrimeWeight p else 0 := by
            rw [Finset.sum_comm]

/-- Aggregate version: the full singular multiplier sum is bounded by the
finite divisor-sum generated by the powerset expansion. -/
theorem sum_goldbachSingularMultiplier_le_powerset_divisor_sum (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, goldbachSingularMultiplier n) ≤
      ∑ T ∈ (oddPrimeSet N).powerset,
        (∏ p ∈ T, singularPrimeWeight p) *
          ((N / (∏ p ∈ T, p) : ℕ) : ℝ) := by
  classical
  rw [sum_goldbachSingularMultiplier_powerset_expand N]
  exact Finset.sum_le_sum (fun T hT =>
    sum_singularPowersetTerm_le_coeff_mul_div hT)

/-- Dividing the powerset coefficient by its squarefree index product gives
the product of the local ratios. -/
theorem singularPowersetCoeff_div_indexProduct_eq_prod (T : Finset ℕ) :
    (∏ p ∈ T, singularPrimeWeight p) /
        (((∏ p ∈ T, p) : ℕ) : ℝ) =
      ∏ p ∈ T, singularPrimeWeight p / (p : ℝ) := by
  rw [show (((∏ p ∈ T, p) : ℕ) : ℝ) = ∏ p ∈ T, (p : ℝ) by simp]
  rw [Finset.prod_div_distrib]

/-- The finite Euler-product expansion associated to the singular multiplier
average. -/
theorem singularPowersetEulerProduct_expand (N : ℕ) :
    (∑ T ∈ (oddPrimeSet N).powerset,
        ∏ p ∈ T, singularPrimeWeight p / (p : ℝ)) =
      ∏ p ∈ oddPrimeSet N, (1 + singularPrimeWeight p / (p : ℝ)) := by
  let f : ℕ → ℝ := fun p => singularPrimeWeight p / (p : ℝ)
  let g : ℕ → ℝ := fun _ => 1
  have hprod :
      (∏ p ∈ oddPrimeSet N, (1 + singularPrimeWeight p / (p : ℝ))) =
        ∏ p ∈ oddPrimeSet N, (f p + g p) := by
    refine Finset.prod_congr rfl ?_
    intro p _hp
    dsimp [f, g]
    ring
  rw [hprod, Finset.prod_add]
  simp [f, g]

/-- The powerset divisor-sum is bounded by `N` times the finite Euler
product. -/
theorem powerset_divisor_sum_le_N_mul_eulerProduct (N : ℕ) :
    (∑ T ∈ (oddPrimeSet N).powerset,
        (∏ p ∈ T, singularPrimeWeight p) *
          ((N / (∏ p ∈ T, p) : ℕ) : ℝ)) ≤
      (N : ℝ) *
        ∏ p ∈ oddPrimeSet N, (1 + singularPrimeWeight p / (p : ℝ)) := by
  classical
  have hterm : ∀ T ∈ (oddPrimeSet N).powerset,
      (∏ p ∈ T, singularPrimeWeight p) *
          ((N / (∏ p ∈ T, p) : ℕ) : ℝ) ≤
        (N : ℝ) * (∏ p ∈ T, singularPrimeWeight p / (p : ℝ)) := by
    intro T hT
    let d : ℕ := ∏ p ∈ T, p
    let a : ℝ := ∏ p ∈ T, singularPrimeWeight p
    have ha_nonneg : 0 ≤ a := by
      simpa [a] using singularPowersetCoeff_nonneg hT
    have hfloor : (((N / d : ℕ) : ℝ)) ≤ (N : ℝ) / (d : ℝ) :=
      Nat.cast_div_le
    have hmul : a * (((N / d : ℕ) : ℝ)) ≤
        a * ((N : ℝ) / (d : ℝ)) :=
      mul_le_mul_of_nonneg_left hfloor ha_nonneg
    have hcomm : a * ((N : ℝ) / (d : ℝ)) =
        (N : ℝ) * (a / (d : ℝ)) := by
      ring
    have hprod : a / (d : ℝ) =
        ∏ p ∈ T, singularPrimeWeight p / (p : ℝ) := by
      simp [a, d]
    calc
      (∏ p ∈ T, singularPrimeWeight p) *
          ((N / (∏ p ∈ T, p) : ℕ) : ℝ)
          = a * (((N / d : ℕ) : ℝ)) := by simp [a, d]
      _ ≤ a * ((N : ℝ) / (d : ℝ)) := hmul
      _ = (N : ℝ) * (∏ p ∈ T, singularPrimeWeight p / (p : ℝ)) := by
        rw [hcomm, hprod]
  calc
    (∑ T ∈ (oddPrimeSet N).powerset,
        (∏ p ∈ T, singularPrimeWeight p) *
          ((N / (∏ p ∈ T, p) : ℕ) : ℝ))
        ≤ ∑ T ∈ (oddPrimeSet N).powerset,
            (N : ℝ) * (∏ p ∈ T, singularPrimeWeight p / (p : ℝ)) :=
          Finset.sum_le_sum hterm
    _ = (N : ℝ) *
        (∑ T ∈ (oddPrimeSet N).powerset,
          ∏ p ∈ T, singularPrimeWeight p / (p : ℝ)) := by
          rw [Finset.mul_sum]
    _ = (N : ℝ) *
        ∏ p ∈ oddPrimeSet N, (1 + singularPrimeWeight p / (p : ℝ)) := by
          rw [singularPowersetEulerProduct_expand]

/-- Current closed reduction for the occupied-average branch: the singular
multiplier sum is controlled by a standard finite Euler product. -/
theorem sum_goldbachSingularMultiplier_le_N_mul_eulerProduct (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, goldbachSingularMultiplier n) ≤
      (N : ℝ) *
        ∏ p ∈ oddPrimeSet N, (1 + singularPrimeWeight p / (p : ℝ)) :=
  (sum_goldbachSingularMultiplier_le_powerset_divisor_sum N).trans
    (powerset_divisor_sum_le_N_mul_eulerProduct N)

/-- The local Euler factor is at least one on the ambient interval. -/
theorem one_le_singularEulerFactor {m : ℕ} (hm3 : 3 ≤ m) :
    1 ≤ 1 + singularPrimeWeight m / (m : ℝ) := by
  have hw : 0 ≤ singularPrimeWeight m := singularPrimeWeight_nonneg hm3
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hquot : 0 ≤ singularPrimeWeight m / (m : ℝ) := by
    exact div_nonneg hw (le_of_lt hm_pos)
  linarith

/-- Exact telescoping product over all integers from `3` to `N`. -/
theorem allInteger_singularEulerProduct_eq (N : ℕ) (hN : 3 ≤ N) :
    (∏ m ∈ Finset.Icc 3 N, (1 + singularPrimeWeight m / (m : ℝ))) =
      2 * (((N : ℝ) - 1) / (N : ℝ)) := by
  refine Nat.le_induction ?base ?step N hN
  · norm_num [singularPrimeWeight]
  · intro n hn ih
    rw [Finset.prod_Icc_succ_top (a := 3) (b := n) (by omega)
      (f := fun m => (1 + singularPrimeWeight m / (m : ℝ)))]
    rw [ih]
    unfold singularPrimeWeight
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hn1_0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (by omega : n + 1 ≠ 0)
    have hn_sub : ((n + 1 : ℕ) : ℝ) - 2 ≠ 0 := by
      have : (2 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 2 < n + 1)
      linarith
    field_simp [hn0, hn1_0, hn_sub]
    norm_num
    ring

/-- The all-integer telescoping product is uniformly bounded by `2`. -/
theorem allInteger_singularEulerProduct_le_two (N : ℕ) :
    (∏ m ∈ Finset.Icc 3 N, (1 + singularPrimeWeight m / (m : ℝ))) ≤ 2 := by
  by_cases hN : 3 ≤ N
  · rw [allInteger_singularEulerProduct_eq N hN]
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hfrac : ((N : ℝ) - 1) / (N : ℝ) ≤ 1 := by
      rw [div_le_one hNpos]
      linarith
    calc
      2 * (((N : ℝ) - 1) / (N : ℝ)) ≤ 2 * 1 :=
        mul_le_mul_of_nonneg_left hfrac (by norm_num)
      _ = 2 := by ring
  · have hempty : Finset.Icc 3 N = (∅ : Finset ℕ) := by
      ext m
      simp [Finset.mem_Icc]
      omega
    simp [hempty]

/-- The prime Euler product is bounded by the all-integer telescoping product. -/
theorem singularPrimeEulerProduct_le_allIntegerProduct (N : ℕ) :
    (∏ p ∈ oddPrimeSet N, (1 + singularPrimeWeight p / (p : ℝ))) ≤
      ∏ m ∈ Finset.Icc 3 N, (1 + singularPrimeWeight m / (m : ℝ)) := by
  classical
  have hsub : oddPrimeSet N ⊆ Finset.Icc 3 N := by
    intro p hp
    unfold oddPrimeSet at hp
    exact (Finset.mem_filter.mp hp).1
  refine Finset.prod_le_prod_of_subset_of_one_le hsub ?_ ?_
  · intro p hp
    have hpIcc : p ∈ Finset.Icc 3 N := hsub hp
    have hp3 : 3 ≤ p := (Finset.mem_Icc.mp hpIcc).1
    exact (zero_le_one.trans (one_le_singularEulerFactor hp3))
  · intro m hm _hmnot
    have hm3 : 3 ≤ m := (Finset.mem_Icc.mp hm).1
    exact one_le_singularEulerFactor hm3

/-- Uniform bound for the finite prime Euler product generated by the
singular multiplier average. -/
theorem singularPrimeEulerProduct_le_two (N : ℕ) :
    (∏ p ∈ oddPrimeSet N, (1 + singularPrimeWeight p / (p : ℝ))) ≤ 2 :=
  (singularPrimeEulerProduct_le_allIntegerProduct N).trans
    (allInteger_singularEulerProduct_le_two N)

/-- Uniform average bound for the Goldbach singular multiplier on `[2, N]`. -/
theorem sum_goldbachSingularMultiplier_le_two_mul_N (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, goldbachSingularMultiplier n) ≤
      2 * (N : ℝ) := by
  have hsum := sum_goldbachSingularMultiplier_le_N_mul_eulerProduct N
  have hprod := singularPrimeEulerProduct_le_two N
  have hN_nonneg : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
  calc
    (∑ n ∈ Finset.Icc 2 N, goldbachSingularMultiplier n)
        ≤ (N : ℝ) *
          ∏ p ∈ oddPrimeSet N, (1 + singularPrimeWeight p / (p : ℝ)) := hsum
    _ ≤ (N : ℝ) * 2 := mul_le_mul_of_nonneg_left hprod hN_nonneg
    _ = 2 * (N : ℝ) := by ring

end PathCSingularAverage
end Gdbh
