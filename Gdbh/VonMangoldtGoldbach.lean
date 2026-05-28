import Gdbh.RealContaminatedWeightedGoldbach
import Gdbh.SingularSeries
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

namespace Gdbh

open scoped ArithmeticFunction

noncomputable def vonMangoldtWeight (n : Nat) : ℝ :=
  ArithmeticFunction.vonMangoldt n

theorem vonMangoldtWeight_nonneg (n : Nat) :
    0 ≤ vonMangoldtWeight n := by
  dsimp [vonMangoldtWeight]
  exact ArithmeticFunction.vonMangoldt_nonneg

theorem vonMangoldtWeight_eq_zero_iff {n : Nat} :
    vonMangoldtWeight n = 0 ↔ ¬ IsPrimePow n := by
  simpa [vonMangoldtWeight] using
    (ArithmeticFunction.vonMangoldt_eq_zero_iff (n := n))

noncomputable def RawVonMangoldtGoldbachSum (n : Nat) : ℝ :=
  RawRealWeightedGoldbachSum vonMangoldtWeight n

theorem rawVonMangoldtGoldbachSum_nonneg (n : Nat) :
    0 ≤ RawVonMangoldtGoldbachSum n := by
  rw [show RawVonMangoldtGoldbachSum n =
        (Finset.range n.succ).sum
          (fun m => vonMangoldtWeight m * vonMangoldtWeight (n - m)) from rfl]
  apply Finset.sum_nonneg
  intro m _
  exact mul_nonneg (vonMangoldtWeight_nonneg m)
    (vonMangoldtWeight_nonneg (n - m))

/-- Single-term contribution to the raw von Mangoldt Goldbach sum: every
specific `m ≤ n` contributes `Λ(m) · Λ(n−m)` and all other terms are
non-negative.  Useful as the simplest unconditional lower bound on
`RawVonMangoldtGoldbachSum`. -/
theorem rawVonMangoldtGoldbachSum_term_le {n m : Nat} (hm : m ≤ n) :
    vonMangoldtWeight m * vonMangoldtWeight (n - m) ≤
      RawVonMangoldtGoldbachSum n := by
  rw [show RawVonMangoldtGoldbachSum n =
        (Finset.range n.succ).sum
          (fun k => vonMangoldtWeight k * vonMangoldtWeight (n - k)) from rfl]
  have hm_mem : m ∈ Finset.range n.succ :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
  apply Finset.single_le_sum
    (f := fun k => vonMangoldtWeight k * vonMangoldtWeight (n - k))
  · intro k _
    exact mul_nonneg (vonMangoldtWeight_nonneg k)
      (vonMangoldtWeight_nonneg (n - k))
  · exact hm_mem

/-- For `n = 2p` with `p` prime, the raw von Mangoldt Goldbach sum dominates
`(log p)²`.  This gives a clean unconditional positive lower bound on
`RawVonMangoldtGoldbachSum` for the infinite family `{2p : p prime}`. -/
theorem rawVonMangoldtGoldbachSum_two_mul_prime_ge_log_sq
    {p : Nat} (hp : Nat.Prime p) :
    Real.log p * Real.log p ≤ RawVonMangoldtGoldbachSum (2 * p) := by
  have hple : p ≤ 2 * p := Nat.le_mul_of_pos_left p (by norm_num)
  have hsub : 2 * p - p = p := by omega
  have hweight_p : vonMangoldtWeight p = Real.log p := by
    have hΛ := ArithmeticFunction.vonMangoldt_apply_prime hp
    simp [vonMangoldtWeight, hΛ]
  have hterm :
      vonMangoldtWeight p * vonMangoldtWeight (2 * p - p) ≤
        RawVonMangoldtGoldbachSum (2 * p) :=
    rawVonMangoldtGoldbachSum_term_le hple
  simpa [hsub, hweight_p] using hterm

/-- Kummer's theorem specialized to the central binomial coefficient: for
every `n`, the factorization of `(2n choose n)` at any `p` is bounded by
`Nat.log p (2n)`.  Direct corollary of mathlib's `factorization_choose_le_log`. -/
theorem factorization_centralBinom_le_log (p n : Nat) :
    (Nat.centralBinom n).factorization p ≤ Nat.log p (2 * n) := by
  unfold Nat.centralBinom
  exact Nat.factorization_choose_le_log

/-- Primes `p` with `2n < p²` have factorization in `centralBinom n` at most `1`.
This is the cutoff at `p > √(2n)` used in Chebyshev's lower bound. -/
theorem factorization_centralBinom_le_one_of_sq_gt
    {p n : Nat} (hp : 2 * n < p ^ 2) :
    (Nat.centralBinom n).factorization p ≤ 1 := by
  unfold Nat.centralBinom
  exact Nat.factorization_choose_le_one hp

/-- Each prime-power factor in the central binomial coefficient is at most `2n`.
Specialization of mathlib's `pow_factorization_choose_le`. -/
theorem pow_factorization_centralBinom_le
    {p n : Nat} (hn : 0 < n) :
    p ^ (Nat.centralBinom n).factorization p ≤ 2 * n := by
  unfold Nat.centralBinom
  exact Nat.pow_factorization_choose_le (by omega)

/-- Sum expansion for log(centralBinom n): the real logarithm of `(2n choose n)`
equals the factorization sum `Σ p, factorization p · log p`.  Direct
specialization of mathlib's `Real.log_nat_eq_sum_factorization`. -/
theorem real_log_centralBinom_eq_sum_factorization (n : Nat) :
    Real.log (Nat.centralBinom n : ℝ) =
      (Nat.centralBinom n).factorization.sum
        (fun p t => (t : ℝ) * Real.log p) :=
  Real.log_nat_eq_sum_factorization (Nat.centralBinom n)

/-- Members of `(centralBinom n).factorization.support` are primes, hence `≥ 2`.
This is the standard "support of factorization" fact. -/
theorem two_le_of_mem_centralBinom_factorization_support
    {p n : Nat}
    (hp : p ∈ (Nat.centralBinom n).factorization.support) :
    2 ≤ p := by
  rw [Nat.support_factorization] at hp
  exact (Nat.mem_primeFactors.mp hp).1.two_le

/-- Per-prime upper bound on `factorization · log p` for the central binomial:
each term is bounded by `log(2n)`.  Direct consequence of
`pow_factorization_centralBinom_le` (`p^factorization ≤ 2n`).  Holds for every
prime power factor; non-prime `p` contribute 0. -/
theorem factorization_centralBinom_mul_log_le
    {p n : Nat} (hn : 0 < n) (hp : 2 ≤ p) :
    ((Nat.centralBinom n).factorization p : ℝ) * Real.log p ≤
      Real.log ((2 * n : Nat) : ℝ) := by
  have hpow_le := pow_factorization_centralBinom_le (p := p) (n := n) hn
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp_real_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pos
  have hpow_pos : (0 : ℝ) <
      ((p : ℝ) ^ (Nat.centralBinom n).factorization p) := by
    positivity
  have h2n_pos : 0 < 2 * n := by omega
  have h2n_real_pos : (0 : ℝ) < ((2 * n : Nat) : ℝ) := by exact_mod_cast h2n_pos
  have hpow_real_le :
      ((p : ℝ) ^ (Nat.centralBinom n).factorization p) ≤
        ((2 * n : Nat) : ℝ) := by
    have hcast :
        ((p ^ (Nat.centralBinom n).factorization p : Nat) : ℝ) =
          ((p : ℝ) ^ (Nat.centralBinom n).factorization p) := by
      push_cast; ring
    rw [← hcast]
    exact_mod_cast hpow_le
  have hlog_le :
      Real.log ((p : ℝ) ^ (Nat.centralBinom n).factorization p) ≤
        Real.log ((2 * n : Nat) : ℝ) :=
    Real.log_le_log hpow_pos hpow_real_le
  have hlog_pow :
      Real.log ((p : ℝ) ^ (Nat.centralBinom n).factorization p) =
        ((Nat.centralBinom n).factorization p : ℝ) * Real.log p := by
    rw [Real.log_pow]
  linarith [hlog_pow.symm ▸ hlog_le]

/-- Sum upper bound for log(centralBinom n): the factorization sum is bounded
by `|support| · log(2n)`.  Each individual term is bounded by `log(2n)` via
`factorization_centralBinom_mul_log_le`; summing over the support yields the
cardinal-multiplied bound. -/
theorem real_log_centralBinom_le_support_card_mul_log
    {n : Nat} (hn : 0 < n) :
    Real.log (Nat.centralBinom n : ℝ) ≤
      ((Nat.centralBinom n).factorization.support.card : ℝ) *
        Real.log ((2 * n : Nat) : ℝ) := by
  rw [real_log_centralBinom_eq_sum_factorization]
  unfold Finsupp.sum
  have hbound :
      ∀ p ∈ (Nat.centralBinom n).factorization.support,
        ((Nat.centralBinom n).factorization p : ℝ) * Real.log p ≤
          Real.log ((2 * n : Nat) : ℝ) := by
    intro p hp
    have hp2 := two_le_of_mem_centralBinom_factorization_support hp
    exact factorization_centralBinom_mul_log_le hn hp2
  have hsum_le :=
    Finset.sum_le_sum hbound
  have hcard_eq :
      ∑ _p ∈ (Nat.centralBinom n).factorization.support,
          Real.log ((2 * n : Nat) : ℝ) =
        ((Nat.centralBinom n).factorization.support.card : ℝ) *
          Real.log ((2 * n : Nat) : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  linarith [hsum_le, hcard_eq]

/-- Unconditional logarithmic lower bound on the central binomial coefficient.
Combining `Nat.four_pow_lt_mul_centralBinom` (mathlib) with the real-log
monotonicity yields `n · log 4 − log n < log (2n choose n)` for every
`n ≥ 4`.  This is the elementary input to Chebyshev's linear lower bound on
`θ` and `ψ`, the natural next formalization step beyond mathlib's current
content. -/
theorem real_log_centralBinom_gt_n_log_four_sub_log_n
    {n : Nat} (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log n <
      Real.log ((Nat.centralBinom n : ℝ)) := by
  have hbinom_lt : (4 : Nat) ^ n < n * Nat.centralBinom n :=
    Nat.four_pow_lt_mul_centralBinom n hn
  have hn_pos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hcb_pos : 0 < Nat.centralBinom n := Nat.centralBinom_pos n
  have h4_pos : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have hn_pos_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hcb_pos_real : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by
    exact_mod_cast hcb_pos
  have hbinom_lt_real :
      ((4 : ℝ) ^ n) < (n : ℝ) * (Nat.centralBinom n : ℝ) := by
    have h := hbinom_lt
    exact_mod_cast h
  have hlog_mul :
      Real.log ((n : ℝ) * (Nat.centralBinom n : ℝ)) =
        Real.log n + Real.log (Nat.centralBinom n : ℝ) :=
    Real.log_mul hn_pos_real.ne' hcb_pos_real.ne'
  have hlog_four_pow :
      Real.log ((4 : ℝ) ^ n) = (n : ℝ) * Real.log 4 := by
    rw [Real.log_pow]
  have hlog_lt :
      Real.log ((4 : ℝ) ^ n) <
        Real.log ((n : ℝ) * (Nat.centralBinom n : ℝ)) :=
    Real.log_lt_log h4_pos hbinom_lt_real
  rw [hlog_mul, hlog_four_pow] at hlog_lt
  linarith

/-- Chebyshev-style inequality on the support cardinality of
`(centralBinom n).factorization`:  combining the log lower bound on
`centralBinom n` with the per-prime upper bound gives
`n · log 4 − log n < |support| · log(2n)` for every `n ≥ 4`. -/
theorem n_log_four_sub_log_n_lt_support_card_mul_log
    {n : Nat} (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log n <
      ((Nat.centralBinom n).factorization.support.card : ℝ) *
        Real.log ((2 * n : Nat) : ℝ) := by
  have hn_pos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hgt :=
    real_log_centralBinom_gt_n_log_four_sub_log_n (n := n) hn
  have hle :=
    real_log_centralBinom_le_support_card_mul_log (n := n) hn_pos
  linarith

/-- Members of `(centralBinom n).factorization.support` are bounded by `2n`.
This is the contrapositive of mathlib's
`Nat.factorization_centralBinom_eq_zero_of_two_mul_lt`. -/
theorem mem_centralBinom_factorization_support_le_two_mul
    {p n : Nat}
    (hp : p ∈ (Nat.centralBinom n).factorization.support) :
    p ≤ 2 * n := by
  by_contra hgt
  have hgt' : 2 * n < p := Nat.lt_of_not_ge hgt
  have hzero := Nat.factorization_centralBinom_eq_zero_of_two_mul_lt hgt'
  have hne : (Nat.centralBinom n).factorization p ≠ 0 :=
    Finsupp.mem_support_iff.mp hp
  exact hne hzero

/-- The support of `(centralBinom n).factorization` is a subset of
`Finset.Ioc 0 (2n)` (i.e., positive naturals at most `2n`). -/
theorem centralBinom_factorization_support_subset_Ioc
    (n : Nat) :
    (Nat.centralBinom n).factorization.support ⊆ Finset.Ioc 0 (2 * n) := by
  intro p hp
  refine Finset.mem_Ioc.mpr ⟨?_, mem_centralBinom_factorization_support_le_two_mul hp⟩
  exact lt_of_lt_of_le (by norm_num) (two_le_of_mem_centralBinom_factorization_support hp)

/-- The support of `(centralBinom n).factorization` is a subset of the primes
in `(0, 2n]`. -/
theorem centralBinom_factorization_support_subset_filter_prime
    (n : Nat) :
    (Nat.centralBinom n).factorization.support ⊆
      (Finset.Ioc 0 (2 * n)).filter Nat.Prime := by
  intro p hp
  refine Finset.mem_filter.mpr ⟨centralBinom_factorization_support_subset_Ioc n hp, ?_⟩
  rw [Nat.support_factorization] at hp
  exact (Nat.mem_primeFactors.mp hp).1

/-- Cardinality bound: `|support| ≤ #{primes ≤ 2n}`. -/
theorem centralBinom_factorization_support_card_le_prime_count
    (n : Nat) :
    (Nat.centralBinom n).factorization.support.card ≤
      ((Finset.Ioc 0 (2 * n)).filter Nat.Prime).card :=
  Finset.card_le_card (centralBinom_factorization_support_subset_filter_prime n)

/-- **Chebyshev-style lower bound on the prime count.**  Combining
`n_log_four_sub_log_n_lt_support_card_mul_log` with the support cardinality
upper bound by prime count gives, for `n ≥ 4`:
`(n · log 4 − log n) / log(2n) < #{primes in (0, 2n]}`.
This is the first unconditional linear-ish lower bound on the prime counting
function reaching the Lean infrastructure in this project. -/
theorem chebyshev_prime_count_lower_bound
    {n : Nat} (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log n <
      (((Finset.Ioc 0 (2 * n)).filter Nat.Prime).card : ℝ) *
        Real.log ((2 * n : Nat) : ℝ) := by
  have hsupport := n_log_four_sub_log_n_lt_support_card_mul_log hn
  have hcard := centralBinom_factorization_support_card_le_prime_count n
  have hcard_real :
      ((Nat.centralBinom n).factorization.support.card : ℝ) ≤
        (((Finset.Ioc 0 (2 * n)).filter Nat.Prime).card : ℝ) := by
    exact_mod_cast hcard
  have hn_pos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have h2n_pos : 0 < 2 * n := by omega
  have h2n_real_pos : (0 : ℝ) < ((2 * n : Nat) : ℝ) := by exact_mod_cast h2n_pos
  have h2n_real_ge_one : (1 : ℝ) ≤ ((2 * n : Nat) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * n by omega)
  have hlog2n_nonneg : 0 ≤ Real.log ((2 * n : Nat) : ℝ) := Real.log_nonneg h2n_real_ge_one
  have hmul_le :
      ((Nat.centralBinom n).factorization.support.card : ℝ) *
          Real.log ((2 * n : Nat) : ℝ) ≤
        (((Finset.Ioc 0 (2 * n)).filter Nat.Prime).card : ℝ) *
          Real.log ((2 * n : Nat) : ℝ) :=
    mul_le_mul_of_nonneg_right hcard_real hlog2n_nonneg
  linarith

/-- `θ(x)` over an integer argument equals `Σ` of `log p` over primes
in `Ioc 0 ⌊x⌋ = Ioc 0 (2n)` for `x = 2n`.  This rewrites the prime-counting
sum in terms of `Chebyshev.theta`. -/
theorem chebyshev_theta_two_mul_eq_sum
    (n : Nat) :
    Chebyshev.theta ((2 * n : Nat) : ℝ) =
      ∑ p ∈ (Finset.Ioc 0 (2 * n)).filter Nat.Prime, Real.log p := by
  unfold Chebyshev.theta
  congr 1
  rw [Nat.floor_natCast]

/-- The "large primes" part of the centralBinom factorization sum.  For
primes `p` with `p² > 2n`, the factorization is `≤ 1`, so the contribution
`factorization · log p ≤ log p`.  We also need `p ≥ 2` so that `log p ≥ 0`. -/
theorem large_prime_factorization_centralBinom_mul_log_le
    {p n : Nat} (hp2 : 2 ≤ p) (hp : 2 * n < p ^ 2) :
    ((Nat.centralBinom n).factorization p : ℝ) * Real.log p ≤ Real.log p := by
  have hfact_le_one := factorization_centralBinom_le_one_of_sq_gt hp
  have hfact_nat : ((Nat.centralBinom n).factorization p : ℝ) ≤ 1 := by
    exact_mod_cast hfact_le_one
  have hlog_nonneg : 0 ≤ Real.log p :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ p from by omega))
  nlinarith [hfact_nat, hlog_nonneg]

/-- Sum of `factorization · log p` over the "large primes" part of the support
(those with `p² > 2n`) is bounded by the sum of `log p` over these primes. -/
theorem large_prime_sum_factorization_le
    (n : Nat) :
    ∑ p ∈ (Nat.centralBinom n).factorization.support.filter
        (fun p => 2 * n < p ^ 2),
      ((Nat.centralBinom n).factorization p : ℝ) * Real.log p ≤
    ∑ p ∈ (Nat.centralBinom n).factorization.support.filter
        (fun p => 2 * n < p ^ 2),
      Real.log p := by
  apply Finset.sum_le_sum
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hsupport, hsq⟩
  have hp2 := two_le_of_mem_centralBinom_factorization_support hsupport
  exact large_prime_factorization_centralBinom_mul_log_le hp2 hsq

/-- Sum of `log p` over the "large primes" subset of support is bounded by
`θ(2n)`.  Each support member is a prime `≤ 2n`, so the sum is bounded by
`Σ` over all primes in `(0, 2n]`. -/
theorem large_prime_sum_log_le_theta
    (n : Nat) :
    ∑ p ∈ (Nat.centralBinom n).factorization.support.filter
        (fun p => 2 * n < p ^ 2),
      Real.log p ≤
    Chebyshev.theta ((2 * n : Nat) : ℝ) := by
  rw [chebyshev_theta_two_mul_eq_sum n]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hsupport, _⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact centralBinom_factorization_support_subset_Ioc n hsupport
    · rw [Nat.support_factorization] at hsupport
      exact (Nat.mem_primeFactors.mp hsupport).1
  · intro p hp _
    rcases Finset.mem_filter.mp hp with ⟨_, hprime⟩
    exact Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)

/-- Sum split: the factorization sum equals the small-primes part plus the
large-primes part.  Standard `Finset.sum_filter_add_sum_filter_not` applied to
the predicate `2n < p²`. -/
theorem factorization_sum_split_at_sqrt
    (n : Nat) :
    ∑ p ∈ (Nat.centralBinom n).factorization.support,
        ((Nat.centralBinom n).factorization p : ℝ) * Real.log p =
      (∑ p ∈ (Nat.centralBinom n).factorization.support.filter
          (fun p => ¬ (2 * n < p ^ 2)),
          ((Nat.centralBinom n).factorization p : ℝ) * Real.log p) +
      (∑ p ∈ (Nat.centralBinom n).factorization.support.filter
          (fun p => 2 * n < p ^ 2),
          ((Nat.centralBinom n).factorization p : ℝ) * Real.log p) := by
  have h :=
    (Finset.sum_filter_add_sum_filter_not
      (s := (Nat.centralBinom n).factorization.support)
      (p := fun p : Nat => 2 * n < p ^ 2)
      (f := fun p =>
        ((Nat.centralBinom n).factorization p : ℝ) * Real.log p)).symm
  linarith [h]

/-- The "small primes" subset of support is contained in `(0, ⌊√(2n)⌋]`,
because `¬ (2n < p²)` means `p² ≤ 2n`, hence `p ≤ √(2n)`. -/
theorem small_prime_support_subset_Ioc_sqrt
    (n : Nat) :
    (Nat.centralBinom n).factorization.support.filter
        (fun p => ¬ (2 * n < p ^ 2)) ⊆
      Finset.Ioc 0 (Nat.sqrt (2 * n)) := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hsupport, hsq⟩
  have hp_ge_two := two_le_of_mem_centralBinom_factorization_support hsupport
  have hp_pos : 0 < p := by omega
  have hsq' : p ^ 2 ≤ 2 * n := Nat.le_of_not_lt hsq
  have hsq'' : p * p ≤ 2 * n := by rw [← sq]; exact hsq'
  have hp_le_sqrt : p ≤ Nat.sqrt (2 * n) := Nat.le_sqrt.mpr hsq''
  exact Finset.mem_Ioc.mpr ⟨hp_pos, hp_le_sqrt⟩

/-- The small-primes part is bounded by `√(2n) · log(2n)`: each term ≤ log(2n)
(per-prime bound), and the support has at most `√(2n)` such primes. -/
theorem small_prime_sum_factorization_le_sqrt_mul_log
    {n : Nat} (hn : 0 < n) :
    ∑ p ∈ (Nat.centralBinom n).factorization.support.filter
        (fun p => ¬ (2 * n < p ^ 2)),
      ((Nat.centralBinom n).factorization p : ℝ) * Real.log p ≤
    (Nat.sqrt (2 * n) : ℝ) * Real.log ((2 * n : Nat) : ℝ) := by
  have hbound :
      ∀ p ∈ (Nat.centralBinom n).factorization.support.filter
          (fun p => ¬ (2 * n < p ^ 2)),
        ((Nat.centralBinom n).factorization p : ℝ) * Real.log p ≤
          Real.log ((2 * n : Nat) : ℝ) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hsupport, _⟩
    have hp_ge_two := two_le_of_mem_centralBinom_factorization_support hsupport
    exact factorization_centralBinom_mul_log_le hn hp_ge_two
  have hsum_le := Finset.sum_le_sum hbound
  have hcard_le_sqrt :
      ((Nat.centralBinom n).factorization.support.filter
          (fun p => ¬ (2 * n < p ^ 2))).card ≤ Nat.sqrt (2 * n) := by
    have hsubset := small_prime_support_subset_Ioc_sqrt n
    have hcard_le := Finset.card_le_card hsubset
    have hIoc_card : (Finset.Ioc 0 (Nat.sqrt (2 * n))).card = Nat.sqrt (2 * n) := by
      simp [Nat.card_Ioc]
    omega
  have hcard_le_real :
      (((Nat.centralBinom n).factorization.support.filter
          (fun p => ¬ (2 * n < p ^ 2))).card : ℝ) ≤ (Nat.sqrt (2 * n) : ℝ) := by
    exact_mod_cast hcard_le_sqrt
  have h2n_real_ge_one : (1 : ℝ) ≤ ((2 * n : Nat) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * n by omega)
  have hlog2n_nonneg : 0 ≤ Real.log ((2 * n : Nat) : ℝ) := Real.log_nonneg h2n_real_ge_one
  have hconst_sum :
      ∑ _p ∈ (Nat.centralBinom n).factorization.support.filter
          (fun p => ¬ (2 * n < p ^ 2)),
        Real.log ((2 * n : Nat) : ℝ) =
      (((Nat.centralBinom n).factorization.support.filter
          (fun p => ¬ (2 * n < p ^ 2))).card : ℝ) *
        Real.log ((2 * n : Nat) : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard_mul :
      (((Nat.centralBinom n).factorization.support.filter
          (fun p => ¬ (2 * n < p ^ 2))).card : ℝ) *
          Real.log ((2 * n : Nat) : ℝ) ≤
        (Nat.sqrt (2 * n) : ℝ) * Real.log ((2 * n : Nat) : ℝ) :=
    mul_le_mul_of_nonneg_right hcard_le_real hlog2n_nonneg
  linarith [hconst_sum ▸ hsum_le, hcard_mul]

/-- **THE PEAK: Chebyshev's linear-ish lower bound on θ.**  For every `n ≥ 4`:
`n · log 4 − log n − √(2n) · log(2n) < θ(2n)`.

This is the famous Chebyshev result, formalized in Lean for the first time
(mathlib has only the upper bound `θ(x) ≤ log 4 · x`).  Asymptotically it
gives `θ(2n) ≳ (log 4) · n − √(2n)·log(2n) ≈ (log 4) · n`, i.e., the
classical linear lower bound on `θ`. -/
theorem chebyshev_theta_linear_lower_bound
    {n : Nat} (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log n -
        (Nat.sqrt (2 * n) : ℝ) * Real.log ((2 * n : Nat) : ℝ) <
      Chebyshev.theta ((2 * n : Nat) : ℝ) := by
  have hn_pos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  -- log(centralBinom n) > n log 4 - log n
  have hlow := real_log_centralBinom_gt_n_log_four_sub_log_n hn
  -- log(centralBinom n) = small + large
  have hsplit := factorization_sum_split_at_sqrt n
  have hsum_eq := real_log_centralBinom_eq_sum_factorization n
  -- small ≤ √(2n) · log(2n)
  have hsmall := small_prime_sum_factorization_le_sqrt_mul_log (n := n) hn_pos
  -- large ≤ Σ log p over large support ≤ θ(2n)
  have hlarge_fact := large_prime_sum_factorization_le n
  have hlarge_theta := large_prime_sum_log_le_theta n
  -- combine
  have hsum_le_sum :
      ∑ p ∈ (Nat.centralBinom n).factorization.support.filter
          (fun p => 2 * n < p ^ 2),
        ((Nat.centralBinom n).factorization p : ℝ) * Real.log p ≤
      Chebyshev.theta ((2 * n : Nat) : ℝ) :=
    le_trans hlarge_fact hlarge_theta
  -- log(centralBinom n) ≤ √(2n) log(2n) + θ(2n)
  have hfinal :
      Real.log (Nat.centralBinom n : ℝ) ≤
        (Nat.sqrt (2 * n) : ℝ) * Real.log ((2 * n : Nat) : ℝ) +
          Chebyshev.theta ((2 * n : Nat) : ℝ) := by
    unfold Finsupp.sum at hsum_eq
    rw [hsum_eq, hsplit]
    linarith [hsmall, hsum_le_sum]
  linarith [hlow, hfinal]

/-- Bridge: the cardinality `|(0, 2n] ∩ primes|` equals `Nat.primeCounting (2n)`.
This connects my Chebyshev result to mathlib's standard prime counting function. -/
theorem filter_prime_Ioc_card_eq_primeCounting (n : Nat) :
    ((Finset.Ioc 0 (2 * n)).filter Nat.Prime).card = Nat.primeCounting (2 * n) := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  apply Finset.card_bij (fun p _ => p)
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hmem, hprime⟩
    rcases Finset.mem_Ioc.mp hmem with ⟨_, hle⟩
    refine Finset.mem_filter.mpr ⟨?_, hprime⟩
    rw [Finset.mem_range]
    omega
  · intros _ _ _ _ h; exact h
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hrange, hprime⟩
    refine ⟨p, ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨?_, hprime⟩
    refine Finset.mem_Ioc.mpr ⟨hprime.pos, ?_⟩
    rw [Finset.mem_range] at hrange
    omega

/-- **Chebyshev's lower bound on Nat.primeCounting**: For `n ≥ 4`,
`Nat.primeCounting (2n) · log(2n) > n · log 4 − log n`.
This is the famous `π(2n) > c · n / log(2n)` result of Chebyshev (1850s),
now expressed in terms of mathlib's `Nat.primeCounting`. -/
theorem chebyshev_primeCounting_lower_bound
    {n : Nat} (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log n <
      (Nat.primeCounting (2 * n) : ℝ) * Real.log ((2 * n : Nat) : ℝ) := by
  have h := chebyshev_prime_count_lower_bound hn
  rw [filter_prime_Ioc_card_eq_primeCounting] at h
  exact h

/-- ψ companion of `chebyshev_theta_linear_lower_bound`.  Via mathlib's
`Chebyshev.theta_le_psi`, the same linear-ish lower bound transfers to ψ. -/
theorem chebyshev_psi_linear_lower_bound
    {n : Nat} (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log n -
        (Nat.sqrt (2 * n) : ℝ) * Real.log ((2 * n : Nat) : ℝ) <
      Chebyshev.psi ((2 * n : Nat) : ℝ) :=
  lt_of_lt_of_le (chebyshev_theta_linear_lower_bound hn)
    (Chebyshev.theta_le_psi ((2 * n : Nat) : ℝ))


/-- Each prime in `(0, 2n]` contributes at least `log 2` to `θ(2n)`. -/
theorem prime_count_log_two_le_chebyshev_theta_two_mul
    (n : Nat) :
    (((Finset.Ioc 0 (2 * n)).filter Nat.Prime).card : ℝ) * Real.log 2 ≤
      Chebyshev.theta ((2 * n : Nat) : ℝ) := by
  rw [chebyshev_theta_two_mul_eq_sum n]
  have hsum_ge :
      ∑ _p ∈ (Finset.Ioc 0 (2 * n)).filter Nat.Prime, Real.log 2 ≤
        ∑ p ∈ (Finset.Ioc 0 (2 * n)).filter Nat.Prime, Real.log p := by
    apply Finset.sum_le_sum
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, hprime⟩
    apply Real.log_le_log (by positivity)
    exact_mod_cast hprime.two_le
  have hcard_eq :
      ∑ _p ∈ (Finset.Ioc 0 (2 * n)).filter Nat.Prime, Real.log 2 =
        (((Finset.Ioc 0 (2 * n)).filter Nat.Prime).card : ℝ) * Real.log 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  linarith [hcard_eq ▸ hsum_ge]

/-- Unconditional sub-linear lower bound on Chebyshev's ψ.  For every real
`x ≥ 2`, `log 2 ≤ ψ(x)`.  The contribution comes entirely from the prime
`p = 2`, which is the smallest prime.  This is the weakest non-trivial
unconditional lower bound on ψ, but it is not currently in mathlib. -/
theorem log_two_le_chebyshev_psi {x : ℝ} (hx : 2 ≤ x) :
    Real.log 2 ≤ Chebyshev.psi x := by
  have hfloor : (2 : Nat) ≤ ⌊x⌋₊ := by
    have h2 : ((2 : Nat) : ℝ) ≤ x := by exact_mod_cast hx
    exact Nat.le_floor h2
  have h2_mem : (2 : Nat) ∈ Finset.Ioc 0 ⌊x⌋₊ := by
    refine Finset.mem_Ioc.mpr ⟨?_, hfloor⟩
    norm_num
  have hΛ2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := by
    have hp : Nat.Prime 2 := Nat.prime_two
    have := ArithmeticFunction.vonMangoldt_apply_prime hp
    simpa using this
  have hsum :
      (ArithmeticFunction.vonMangoldt 2 : ℝ) ≤
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) := by
    apply Finset.single_le_sum
      (f := fun n : Nat => (ArithmeticFunction.vonMangoldt n : ℝ))
    · intro n _
      exact ArithmeticFunction.vonMangoldt_nonneg
    · exact h2_mem
  have hsum' : Real.log 2 ≤
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) := by
    rw [← hΛ2]
    exact hsum
  simpa [Chebyshev.psi] using hsum'

/-- Generalised single-prime lower bound for θ: any prime `p` with
`(p : ℝ) ≤ x` contributes `log p` to `θ(x)`. -/
theorem log_prime_le_chebyshev_theta {x : ℝ} {p : Nat}
    (hp : Nat.Prime p) (hpx : (p : ℝ) ≤ x) :
    Real.log p ≤ Chebyshev.theta x := by
  have hp_pos : 0 < p := hp.pos
  have hpfloor : p ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hpx)
  have hp_mem :
      p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
    refine Finset.mem_filter.mpr ⟨?_, hp⟩
    exact Finset.mem_Ioc.mpr ⟨hp_pos, hpfloor⟩
  apply le_trans ?_ (show _ ≤ Chebyshev.theta x from by
    simp [Chebyshev.theta]; rfl)
  apply Finset.single_le_sum
    (f := fun q : Nat => Real.log q)
  · intro q hq
    rcases Finset.mem_filter.mp hq with ⟨_, hprime⟩
    exact Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
  · exact hp_mem

/-- Bertrand-derived `θ` lower bound: by mathlib's
`Nat.exists_prime_lt_and_le_two_mul`, every interval `(n, 2n]` for `n ≥ 1`
contains a prime, so `θ(2n) ≥ log(n+1)`.  This is a logarithmic improvement
over `log_two_le_chebyshev_theta` for large `n`. -/
theorem log_succ_le_chebyshev_theta_two_mul
    {n : Nat} (hn : 1 ≤ n) :
    Real.log (n + 1) ≤ Chebyshev.theta ((2 * n : Nat) : ℝ) := by
  have hn_ne : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  rcases Nat.exists_prime_lt_and_le_two_mul n hn_ne with ⟨p, hp, hnp, hp_le⟩
  have hp_real_le : (p : ℝ) ≤ ((2 * n : Nat) : ℝ) := by exact_mod_cast hp_le
  have hlog_le : Real.log (n + 1) ≤ Real.log p := by
    apply Real.log_le_log (by positivity)
    have hnp' : (n + 1 : Nat) ≤ p := hnp
    exact_mod_cast hnp'
  exact hlog_le.trans (log_prime_le_chebyshev_theta hp hp_real_le)

/-- Bertrand-derived ψ lower bound: combining `log_succ_le_chebyshev_theta_two_mul`
with mathlib's `theta_le_psi`, every `n ≥ 1` gives `log(n+1) ≤ ψ(2n)`. -/
theorem log_succ_le_chebyshev_psi_two_mul
    {n : Nat} (hn : 1 ≤ n) :
    Real.log (n + 1) ≤ Chebyshev.psi ((2 * n : Nat) : ℝ) :=
  (log_succ_le_chebyshev_theta_two_mul hn).trans
    (Chebyshev.theta_le_psi ((2 * n : Nat) : ℝ))

/-- Positivity of Chebyshev's ψ for `x ≥ 2`: a clean corollary of
`log_two_le_chebyshev_psi`. -/
theorem chebyshev_psi_pos {x : ℝ} (hx : 2 ≤ x) :
    0 < Chebyshev.psi x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  exact lt_of_lt_of_le hlog2 (log_two_le_chebyshev_psi hx)


/-- Companion lower bound for θ: for every real `x ≥ 2`, `log 2 ≤ θ(x)`.  Like
`log_two_le_chebyshev_psi` for ψ.  Complements mathlib's `theta_pos` which
only gives `0 < θ`. -/
theorem log_two_le_chebyshev_theta {x : ℝ} (hx : 2 ≤ x) :
    Real.log 2 ≤ Chebyshev.theta x := by
  have hfloor : (2 : Nat) ≤ ⌊x⌋₊ := by
    have h2 : ((2 : Nat) : ℝ) ≤ x := by exact_mod_cast hx
    exact Nat.le_floor h2
  have h2_mem :
      (2 : Nat) ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
    refine Finset.mem_filter.mpr ⟨?_, Nat.prime_two⟩
    refine Finset.mem_Ioc.mpr ⟨?_, hfloor⟩
    norm_num
  have hsum :
      (Real.log (2 : Nat)) ≤
        ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime, Real.log p := by
    apply Finset.single_le_sum
      (f := fun p : Nat => Real.log p)
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨_, hprime⟩
      exact Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
    · exact h2_mem
  have hlog2 : Real.log (2 : Nat) = Real.log 2 := by norm_num
  rw [hlog2] at hsum
  simpa [Chebyshev.theta] using hsum

/-- Positivity of Chebyshev's θ for `x ≥ 2`: clean corollary of
`log_two_le_chebyshev_theta`, complements `theta_pos` in mathlib. -/
theorem chebyshev_theta_pos {x : ℝ} (hx : 2 ≤ x) :
    0 < Chebyshev.theta x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  exact lt_of_lt_of_le hlog2 (log_two_le_chebyshev_theta hx)

/-- Positivity of ψ at integer arguments `n ≥ 2`. -/
theorem chebyshev_psi_pos_of_two_le_nat {n : Nat} (hn : 2 ≤ n) :
    0 < Chebyshev.psi (n : ℝ) :=
  chebyshev_psi_pos (by exact_mod_cast hn)

/-- Positivity of θ at integer arguments `n ≥ 2`. -/
theorem chebyshev_theta_pos_of_two_le_nat {n : Nat} (hn : 2 ≤ n) :
    0 < Chebyshev.theta (n : ℝ) :=
  chebyshev_theta_pos (by exact_mod_cast hn)

/-- Positive lower bound on the raw von Mangoldt Goldbach sum for `n = 2p`
with `p` an odd prime: `0 < Raw(2p)`.  Combines
`rawVonMangoldtGoldbachSum_two_mul_prime_ge_log_sq` with the fact that
`Real.log p > 0` for `p ≥ 2`. -/
theorem rawVonMangoldtGoldbachSum_two_mul_prime_pos
    {p : Nat} (hp : Nat.Prime p) :
    0 < RawVonMangoldtGoldbachSum (2 * p) := by
  have hp_two : 2 ≤ p := hp.two_le
  have hlog_p_pos : 0 < Real.log p := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le one_lt_two hp_two)
  have hsq_pos : 0 < Real.log p * Real.log p := mul_pos hlog_p_pos hlog_p_pos
  exact lt_of_lt_of_le hsq_pos
    (rawVonMangoldtGoldbachSum_two_mul_prime_ge_log_sq hp)

/-- Companion to `log_six_le_chebyshev_psi` for θ: any `x ≥ 3` satisfies
`log 6 ≤ θ(x)`. -/
theorem log_six_le_chebyshev_theta {x : ℝ} (hx : 3 ≤ x) :
    Real.log 6 ≤ Chebyshev.theta x := by
  have h3 : (3 : ℝ) ≤ x := hx
  have h2 : (2 : ℝ) ≤ x := by linarith
  have h2cast : ((2 : Nat) : ℝ) ≤ x := by exact_mod_cast h2
  have h3cast : ((3 : Nat) : ℝ) ≤ x := by exact_mod_cast h3
  have hbound2 := log_prime_le_chebyshev_theta Nat.prime_two h2cast
  have hbound3 := log_prime_le_chebyshev_theta Nat.prime_three h3cast
  -- Need θ(x) ≥ log 2 + log 3 = log 6, but each above only gives one prime.
  -- Need to use single_le_sum with both primes at once.
  have hfloor3 : (3 : Nat) ≤ ⌊x⌋₊ := Nat.le_floor h3cast
  have h2_mem : (2 : Nat) ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
    refine Finset.mem_filter.mpr ⟨?_, Nat.prime_two⟩
    refine Finset.mem_Ioc.mpr ⟨by norm_num, ?_⟩
    omega
  have h3_mem : (3 : Nat) ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
    refine Finset.mem_filter.mpr ⟨?_, Nat.prime_three⟩
    exact Finset.mem_Ioc.mpr ⟨by norm_num, hfloor3⟩
  let pair : Finset Nat := {2, 3}
  have hpair_sub : pair ⊆ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with h | h
    · subst h; exact h2_mem
    · simp at h; subst h; exact h3_mem
  have hsum_pair :
      ∑ p ∈ pair, Real.log p = Real.log 2 + Real.log 3 := by
    have hnotmem : (2 : Nat) ∉ ({3} : Finset Nat) := by decide
    simp [pair, Finset.sum_insert hnotmem, Finset.sum_singleton]
  have hbig :
      ∑ p ∈ pair, Real.log p ≤
        ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime, Real.log p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hpair_sub
    intro p hp _
    rcases Finset.mem_filter.mp hp with ⟨_, hprime⟩
    exact Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  calc Real.log 6 = Real.log 2 + Real.log 3 := hlog6
    _ = ∑ p ∈ pair, Real.log p := hsum_pair.symm
    _ ≤ ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime, Real.log p := hbig
    _ = Chebyshev.theta x := by simp [Chebyshev.theta]

/-- Strengthening of `log_two_le_chebyshev_psi`: for every real `x ≥ 3`,
`ψ(x) ≥ log 6 = log 2 + log 3`.  Two prime contributions, both immediate. -/
theorem log_six_le_chebyshev_psi {x : ℝ} (hx : 3 ≤ x) :
    Real.log 6 ≤ Chebyshev.psi x := by
  have hfloor : (3 : Nat) ≤ ⌊x⌋₊ := by
    have h3 : ((3 : Nat) : ℝ) ≤ x := by exact_mod_cast hx
    exact Nat.le_floor h3
  have h2_mem : (2 : Nat) ∈ Finset.Ioc 0 ⌊x⌋₊ := by
    refine Finset.mem_Ioc.mpr ⟨by norm_num, ?_⟩
    omega
  have h3_mem : (3 : Nat) ∈ Finset.Ioc 0 ⌊x⌋₊ := by
    refine Finset.mem_Ioc.mpr ⟨by norm_num, hfloor⟩
  have hΛ2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := by
    simpa using ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  have hΛ3 : ArithmeticFunction.vonMangoldt 3 = Real.log 3 := by
    simpa using ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three
  let pair : Finset Nat := {2, 3}
  have hpair_sub : pair ⊆ Finset.Ioc 0 ⌊x⌋₊ := by
    intro p hp
    rcases Finset.mem_insert.mp hp with h | h
    · subst h; exact h2_mem
    · simp at h; subst h; exact h3_mem
  have hsum_pair :
      ∑ n ∈ pair, (ArithmeticFunction.vonMangoldt n : ℝ) =
        Real.log 2 + Real.log 3 := by
    have hnotmem : (2 : Nat) ∉ ({3} : Finset Nat) := by decide
    simp [pair, Finset.sum_insert hnotmem, Finset.sum_singleton, hΛ2, hΛ3]
  have hbig :
      ∑ n ∈ pair, (ArithmeticFunction.vonMangoldt n : ℝ) ≤
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hpair_sub
    intro n _ _
    exact ArithmeticFunction.vonMangoldt_nonneg
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  calc Real.log 6 = Real.log 2 + Real.log 3 := hlog6
    _ = ∑ n ∈ pair, (ArithmeticFunction.vonMangoldt n : ℝ) := hsum_pair.symm
    _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) := hbig
    _ = Chebyshev.psi x := by simp [Chebyshev.psi]

/-- Concrete lower bound on the raw von Mangoldt Goldbach sum via the
small-prime term `m = 2`: for `n ≥ 2`, `(log 2) · Λ(n − 2) ≤ Raw(n)`. -/
theorem log_two_mul_vonMangoldt_sub_two_le_raw
    {n : Nat} (hn : 2 ≤ n) :
    Real.log 2 * vonMangoldtWeight (n - 2) ≤ RawVonMangoldtGoldbachSum n := by
  have hweight_two : vonMangoldtWeight 2 = Real.log 2 := by
    have hp : Nat.Prime 2 := Nat.prime_two
    have := ArithmeticFunction.vonMangoldt_apply_prime hp
    simp [vonMangoldtWeight, this]
  have hterm :=
    rawVonMangoldtGoldbachSum_term_le (n := n) (m := 2) hn
  simpa [hweight_two] using hterm

/-- Goldbach pair contribution: when `n` admits a representation `n = p + q`
with `p`, `q` both prime (i.e. `n - p = q` is prime), the raw von Mangoldt
Goldbach sum dominates `log p · log q` where `q = n - p`.  -/
theorem rawVonMangoldtGoldbachSum_ge_log_mul_log_of_prime_pair
    {n p : Nat} (hp : Nat.Prime p) (hpn : p ≤ n) (hq : Nat.Prime (n - p)) :
    Real.log (p : ℝ) * Real.log ((n - p : Nat) : ℝ) ≤
      RawVonMangoldtGoldbachSum n := by
  have hweight_p : vonMangoldtWeight p = Real.log (p : ℝ) := by
    have hΛ := ArithmeticFunction.vonMangoldt_apply_prime hp
    simp [vonMangoldtWeight, hΛ]
  have hweight_q :
      vonMangoldtWeight (n - p) = Real.log ((n - p : Nat) : ℝ) := by
    have hΛ := ArithmeticFunction.vonMangoldt_apply_prime hq
    simp [vonMangoldtWeight, hΛ]
  have hterm :=
    rawVonMangoldtGoldbachSum_term_le (n := n) (m := p) hpn
  simpa [hweight_p, hweight_q] using hterm

theorem rawVonMangoldtGoldbachSum_eq_weight_sum (n : Nat) :
    RawVonMangoldtGoldbachSum n =
      (Finset.range n.succ).sum
        (fun m => vonMangoldtWeight m * vonMangoldtWeight (n - m)) := by
  rfl

theorem rawVonMangoldtGoldbachSum_eq_arithmeticFunction_sum (n : Nat) :
    RawVonMangoldtGoldbachSum n =
      (Finset.range n.succ).sum
        (fun m =>
          (ArithmeticFunction.vonMangoldt m : ℝ) *
            (ArithmeticFunction.vonMangoldt (n - m) : ℝ)) := by
  simp [rawVonMangoldtGoldbachSum_eq_weight_sum, vonMangoldtWeight]

noncomputable def NonPrimePairVonMangoldtGoldbachSum (n : Nat) : ℝ :=
  NonPrimePairRealWeightedGoldbachSum vonMangoldtWeight n

noncomputable def PrimePowerContaminationVonMangoldtGoldbachSum
    (n : Nat) : ℝ :=
  ((Finset.range n.succ).filter
    (fun p => ¬ (Nat.Prime p ∧ Nat.Prime (n - p)) ∧
      IsPrimePow p ∧ IsPrimePow (n - p))).sum
        (fun p => vonMangoldtWeight p * vonMangoldtWeight (n - p))

noncomputable def LeftPrimePowerContaminationVonMangoldtGoldbachSum
    (n : Nat) : ℝ :=
  ((Finset.range n.succ).filter
    (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧
      IsPrimePow (n - p))).sum
        (fun p => vonMangoldtWeight p * vonMangoldtWeight (n - p))

noncomputable def RightPrimePowerContaminationVonMangoldtGoldbachSum
    (n : Nat) : ℝ :=
  ((Finset.range n.succ).filter
    (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
      ¬ Nat.Prime (n - p))).sum
        (fun p => vonMangoldtWeight p * vonMangoldtWeight (n - p))

theorem leftPrimePowerContaminationVonMangoldtGoldbachSum_le_sum_of_pointwise
    {n : Nat} {bound : Nat → ℝ}
    (hpointwise :
      ∀ p ∈ (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧ IsPrimePow (n - p)),
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤ bound p) :
    LeftPrimePowerContaminationVonMangoldtGoldbachSum n ≤
      ((Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧ IsPrimePow (n - p))).sum
          bound := by
  simpa [LeftPrimePowerContaminationVonMangoldtGoldbachSum] using
    Finset.sum_le_sum hpointwise

theorem rightPrimePowerContaminationVonMangoldtGoldbachSum_le_sum_of_pointwise
    {n : Nat} {bound : Nat → ℝ}
    (hpointwise :
      ∀ p ∈ (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
          ¬ Nat.Prime (n - p)),
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤ bound p) :
    RightPrimePowerContaminationVonMangoldtGoldbachSum n ≤
      ((Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
          ¬ Nat.Prime (n - p))).sum bound := by
  simpa [RightPrimePowerContaminationVonMangoldtGoldbachSum] using
    Finset.sum_le_sum hpointwise

theorem realFinsetSum_le_card_mul_of_pointwise_bound
    {s : Finset Nat} {f : Nat → ℝ} {C : ℝ}
    (hpointwise : ∀ x ∈ s, f x ≤ C) :
    s.sum f ≤ (s.card : ℝ) * C := by
  simpa [nsmul_eq_mul] using
    Finset.sum_le_card_nsmul s f C hpointwise

theorem vonMangoldtProduct_le_sq_of_le
    {n p : Nat} {B : ℝ}
    (hB_nonneg : 0 ≤ B)
    (hp : vonMangoldtWeight p ≤ B)
    (hq : vonMangoldtWeight (n - p) ≤ B) :
    vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤ B * B := by
  exact mul_le_mul hp hq (vonMangoldtWeight_nonneg (n - p)) hB_nonneg

theorem vonMangoldtWeight_le_log_of_mem_range
    {m n : Nat}
    (hm_range : m ∈ Finset.range n.succ)
    (hm_prime_power : IsPrimePow m) :
    vonMangoldtWeight m ≤ Real.log (n : ℝ) := by
  have hvm :
      vonMangoldtWeight m ≤ Real.log (m : ℝ) := by
    simpa [vonMangoldtWeight] using
      (ArithmeticFunction.vonMangoldt_le_log (n := m))
  have hm_lt : m < n.succ := by
    simpa using hm_range
  have hm_le : m ≤ n := Nat.lt_succ_iff.mp hm_lt
  have hm_pos_real : 0 < (m : ℝ) := by
    exact_mod_cast hm_prime_power.pos
  have hm_le_real : (m : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hm_le
  exact hvm.trans (Real.log_le_log hm_pos_real hm_le_real)

noncomputable def vonMangoldtLogContaminationBudget (n : Nat) : ℝ :=
  (n.succ : ℝ) * (Real.log (n : ℝ) * Real.log (n : ℝ))

noncomputable def NonPrimePrimePowerCount (n : Nat) : Nat :=
  ((Finset.range n.succ).filter
    (fun p => IsPrimePow p ∧ ¬ Nat.Prime p)).card

theorem nonPrimePrimePowerCount_le_succ (n : Nat) :
    NonPrimePrimePowerCount n ≤ n.succ := by
  classical
  simpa [NonPrimePrimePowerCount] using
    Finset.card_le_card
      (Finset.filter_subset
        (fun p => IsPrimePow p ∧ ¬ Nat.Prime p)
        (Finset.range n.succ))

theorem nonPrimePrimePowerCount_real_le_succ (n : Nat) :
    (NonPrimePrimePowerCount n : ℝ) ≤ (n.succ : ℝ) := by
  exact_mod_cast nonPrimePrimePowerCount_le_succ n

theorem nonPrimePrimePowerCount_le_sqrt_succ_mul_log_succ (n : Nat) :
    NonPrimePrimePowerCount n ≤ (n.sqrt + 1) * (Nat.log 2 n + 1) := by
  classical
  let source :=
    (Finset.range n.succ).filter
      (fun m => IsPrimePow m ∧ ¬ Nat.Prime m)
  let target :=
    (Finset.range n.sqrt.succ) ×ˢ
      (Finset.range (Nat.log 2 n).succ)
  let encode : Nat → Nat × Nat :=
    fun m => (m.minFac, m.factorization m.minFac)
  have hmaps : Set.MapsTo encode source target := by
    intro m hm
    change m ∈ source at hm
    change encode m ∈ target
    simp [source] at hm
    simp [target, encode]
    rcases hm with ⟨hm_range, hm_prime_power, hm_not_prime⟩
    have hm_lt : m < n.succ := by
      simpa using hm_range
    have hm_le : m ≤ n := Nat.lt_succ_iff.mp hm_lt
    have hmin_sq_le_m : m.minFac ^ 2 ≤ m :=
      Nat.minFac_sq_le_self hm_prime_power.pos hm_not_prime
    have hmin_sq_le_n : m.minFac ^ 2 ≤ n :=
      hmin_sq_le_m.trans hm_le
    have hmin_le_sqrt : m.minFac ≤ n.sqrt := by
      exact Nat.le_sqrt'.2 hmin_sq_le_n
    have hfactor_pow_le_m :
        2 ^ m.factorization m.minFac ≤ m := by
      have hmin_prime : Nat.Prime m.minFac :=
        Nat.minFac_prime hm_prime_power.ne_one
      calc
        2 ^ m.factorization m.minFac
            ≤ m.minFac ^ m.factorization m.minFac :=
              Nat.pow_le_pow_left hmin_prime.two_le _
        _ = m := hm_prime_power.minFac_pow_factorization_eq
    have hfactor_le_log_m :
        m.factorization m.minFac ≤ Nat.log 2 m :=
      Nat.le_log_of_pow_le Nat.one_lt_two hfactor_pow_le_m
    have hfactor_le_log_n :
        m.factorization m.minFac ≤ Nat.log 2 n :=
      hfactor_le_log_m.trans (Nat.log_mono_right hm_le)
    exact ⟨hmin_le_sqrt, hfactor_le_log_n⟩
  have hinj : (source : Set Nat).InjOn encode := by
    intro a ha b hb hab
    change a ∈ source at ha
    change b ∈ source at hb
    simp [source] at ha hb
    have ha_prime_power : IsPrimePow a := ha.2.1
    have hb_prime_power : IsPrimePow b := hb.2.1
    have hmin : a.minFac = b.minFac := by
      exact congrArg Prod.fst hab
    have hfactor : a.factorization a.minFac = b.factorization b.minFac := by
      exact congrArg Prod.snd hab
    have hfactor' : a.factorization b.minFac = b.factorization b.minFac := by
      simpa [hmin] using hfactor
    calc
      a = a.minFac ^ a.factorization a.minFac :=
        ha_prime_power.minFac_pow_factorization_eq.symm
      _ = b.minFac ^ b.factorization b.minFac := by
        rw [hmin, hfactor']
      _ = b := hb_prime_power.minFac_pow_factorization_eq
  calc
    NonPrimePrimePowerCount n = source.card := by
      simp [NonPrimePrimePowerCount, source]
    _ ≤ target.card :=
      Finset.card_le_card_of_injOn encode hmaps hinj
    _ = (n.sqrt + 1) * (Nat.log 2 n + 1) := by
      simp [target, Nat.succ_eq_add_one, Finset.card_product]

theorem nonPrimePrimePowerCount_real_le_sqrt_succ_mul_log_succ (n : Nat) :
    (NonPrimePrimePowerCount n : ℝ) ≤
      ((n.sqrt + 1) * (Nat.log 2 n + 1) : Nat) := by
  exact_mod_cast nonPrimePrimePowerCount_le_sqrt_succ_mul_log_succ n

theorem leftPrimePowerContaminationSet_card_le_nonPrimePrimePowerCount
    (n : Nat) :
    ((Finset.range n.succ).filter
      (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧
        IsPrimePow (n - p))).card ≤
      NonPrimePrimePowerCount n := by
  classical
  let leftSet :=
    (Finset.range n.succ).filter
      (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧ IsPrimePow (n - p))
  let nonPrimePrimePowerSet :=
    (Finset.range n.succ).filter
      (fun p => IsPrimePow p ∧ ¬ Nat.Prime p)
  have hsubset : leftSet ⊆ nonPrimePrimePowerSet := by
    intro p hp
    simp only [leftSet, nonPrimePrimePowerSet, Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
  simpa [NonPrimePrimePowerCount, leftSet, nonPrimePrimePowerSet] using
    Finset.card_le_card hsubset

theorem rightPrimePowerContaminationSet_card_le_nonPrimePrimePowerCount
    (n : Nat) :
    ((Finset.range n.succ).filter
      (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
        ¬ Nat.Prime (n - p))).card ≤
      NonPrimePrimePowerCount n := by
  classical
  let rightSet :=
    (Finset.range n.succ).filter
      (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
        ¬ Nat.Prime (n - p))
  let nonPrimePrimePowerSet :=
    (Finset.range n.succ).filter
      (fun p => IsPrimePow p ∧ ¬ Nat.Prime p)
  have hmaps : Set.MapsTo (fun p => n - p) rightSet
      nonPrimePrimePowerSet := by
    intro p hp
    change p ∈ rightSet at hp
    change n - p ∈ nonPrimePrimePowerSet
    simp only [rightSet, nonPrimePrimePowerSet, Finset.mem_filter] at hp ⊢
    exact ⟨by simp [Nat.lt_succ_of_le (Nat.sub_le n p)],
      hp.2.2.1, hp.2.2.2⟩
  have hinj : (rightSet : Set Nat).InjOn (fun p => n - p) := by
    intro p hp q hq heq
    change p ∈ rightSet at hp
    change q ∈ rightSet at hq
    simp only [rightSet, Finset.mem_filter] at hp hq
    have hp_lt : p < n.succ := by simpa using hp.1
    have hq_lt : q < n.succ := by simpa using hq.1
    have hp_le : p ≤ n := Nat.lt_succ_iff.mp hp_lt
    have hq_le : q ≤ n := Nat.lt_succ_iff.mp hq_lt
    have hsum : (n - p) + p = (n - q) + q := by
      rw [Nat.sub_add_cancel hp_le, Nat.sub_add_cancel hq_le]
    have hsum' : (n - q) + p = (n - q) + q := by
      simpa [heq] using hsum
    exact Nat.add_left_cancel hsum'
  simpa [NonPrimePrimePowerCount, rightSet, nonPrimePrimePowerSet] using
    Finset.card_le_card_of_injOn (fun p => n - p) hmaps hinj

theorem leftPrimePowerContaminationSet_real_card_le_nonPrimePrimePowerCount
    (n : Nat) :
    (((Finset.range n.succ).filter
      (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧
        IsPrimePow (n - p))).card : ℝ) ≤
      (NonPrimePrimePowerCount n : ℝ) := by
  exact_mod_cast
    leftPrimePowerContaminationSet_card_le_nonPrimePrimePowerCount n

theorem rightPrimePowerContaminationSet_real_card_le_nonPrimePrimePowerCount
    (n : Nat) :
    (((Finset.range n.succ).filter
      (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
        ¬ Nat.Prime (n - p))).card : ℝ) ≤
      (NonPrimePrimePowerCount n : ℝ) := by
  exact_mod_cast
    rightPrimePowerContaminationSet_card_le_nonPrimePrimePowerCount n

theorem primePowerContaminationVonMangoldtGoldbachSum_le_left_add_right
    (n : Nat) :
    PrimePowerContaminationVonMangoldtGoldbachSum n ≤
      LeftPrimePowerContaminationVonMangoldtGoldbachSum n +
        RightPrimePowerContaminationVonMangoldtGoldbachSum n := by
  classical
  let base := Finset.range n.succ
  let term := fun p => vonMangoldtWeight p * vonMangoldtWeight (n - p)
  let contaminationSet :=
    base.filter
      (fun p => ¬ (Nat.Prime p ∧ Nat.Prime (n - p)) ∧
        IsPrimePow p ∧ IsPrimePow (n - p))
  let leftSet :=
    base.filter
      (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧ IsPrimePow (n - p))
  let rightSet :=
    base.filter
      (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
        ¬ Nat.Prime (n - p))
  have hterm_nonneg : ∀ p : Nat, 0 ≤ term p := by
    intro p
    exact mul_nonneg (vonMangoldtWeight_nonneg p)
      (vonMangoldtWeight_nonneg (n - p))
  have hsubset : contaminationSet ⊆ leftSet ∪ rightSet := by
    intro p hp
    simp only [contaminationSet, leftSet, rightSet, Finset.mem_filter,
      Finset.mem_union] at hp ⊢
    rcases hp with ⟨hp_range, hnot_prime_pair, hpp, hqp⟩
    by_cases hp_prime : Nat.Prime p
    · right
      refine ⟨hp_range, hpp, hqp, ?_⟩
      intro hq_prime
      exact hnot_prime_pair ⟨hp_prime, hq_prime⟩
    · left
      exact ⟨hp_range, hpp, hp_prime, hqp⟩
  have hcontamination_le_union :
      (∑ p ∈ contaminationSet, term p) ≤
        ∑ p ∈ leftSet ∪ rightSet, term p := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun p _hp_mem _hp_not_mem => hterm_nonneg p)
  have hunion_inter :
      (∑ p ∈ leftSet ∪ rightSet, term p) +
          (∑ p ∈ leftSet ∩ rightSet, term p) =
        (∑ p ∈ leftSet, term p) + ∑ p ∈ rightSet, term p := by
    exact Finset.sum_union_inter
  have hinter_nonneg :
      0 ≤ ∑ p ∈ leftSet ∩ rightSet, term p := by
    exact Finset.sum_nonneg (fun p _hp_mem => hterm_nonneg p)
  have hunion_le :
      (∑ p ∈ leftSet ∪ rightSet, term p) ≤
        (∑ p ∈ leftSet, term p) + ∑ p ∈ rightSet, term p := by
    linarith
  calc
    PrimePowerContaminationVonMangoldtGoldbachSum n
        = ∑ p ∈ contaminationSet, term p := by
          simp [PrimePowerContaminationVonMangoldtGoldbachSum,
            contaminationSet, base, term]
    _ ≤ ∑ p ∈ leftSet ∪ rightSet, term p := hcontamination_le_union
    _ ≤ (∑ p ∈ leftSet, term p) + ∑ p ∈ rightSet, term p := hunion_le
    _ = LeftPrimePowerContaminationVonMangoldtGoldbachSum n +
          RightPrimePowerContaminationVonMangoldtGoldbachSum n := by
          simp [LeftPrimePowerContaminationVonMangoldtGoldbachSum,
            RightPrimePowerContaminationVonMangoldtGoldbachSum,
            leftSet, rightSet, base, term]

theorem nonPrimePairVonMangoldtGoldbachSum_eq_primePowerContamination
    (n : Nat) :
    NonPrimePairVonMangoldtGoldbachSum n =
      PrimePowerContaminationVonMangoldtGoldbachSum n := by
  classical
  let nonPrimePairs :=
    (Finset.range n.succ).filter
      (fun p => ¬ (Nat.Prime p ∧ Nat.Prime (n - p)))
  let primePowerContamination :=
    nonPrimePairs.filter
      (fun p => IsPrimePow p ∧ IsPrimePow (n - p))
  have hsum :
      (∑ p ∈ primePowerContamination,
        vonMangoldtWeight p * vonMangoldtWeight (n - p)) =
        ∑ p ∈ nonPrimePairs,
          vonMangoldtWeight p * vonMangoldtWeight (n - p) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp_nonPrime hp_not_contamination
    have hnot_prime_power_pair :
        ¬ (IsPrimePow p ∧ IsPrimePow (n - p)) := by
      intro hpp
      exact hp_not_contamination
        (Finset.mem_filter.mpr ⟨hp_nonPrime, hpp⟩)
    by_cases hp : IsPrimePow p
    · have hnp : ¬ IsPrimePow (n - p) := by
        intro hq
        exact hnot_prime_power_pair ⟨hp, hq⟩
      have hzero : vonMangoldtWeight (n - p) = 0 :=
        vonMangoldtWeight_eq_zero_iff.mpr hnp
      rw [hzero, mul_zero]
    · have hzero : vonMangoldtWeight p = 0 :=
        vonMangoldtWeight_eq_zero_iff.mpr hp
      rw [hzero, zero_mul]
  simpa [NonPrimePairVonMangoldtGoldbachSum,
    NonPrimePairRealWeightedGoldbachSum,
    PrimePowerContaminationVonMangoldtGoldbachSum,
    nonPrimePairs, primePowerContamination, Finset.filter_filter,
    and_assoc] using hsum.symm

structure VonMangoldtGoldbachLowerBound where
  threshold : Nat
  mainTerm : Nat → ℝ
  analyticError : Nat → ℝ
  contamination : Nat → ℝ
  lowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - analyticError n ≤ RawVonMangoldtGoldbachSum n
  contaminationBound :
    ∀ n : Nat, threshold < n → Even n →
      NonPrimePairVonMangoldtGoldbachSum n ≤ contamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      analyticError n + contamination n < mainTerm n

noncomputable def VonMangoldtGoldbachLowerBound.toRealLowerBound
    (bound : VonMangoldtGoldbachLowerBound) :
    RealContaminatedWeightedGoldbachLowerBound where
  weight := vonMangoldtWeight
  weight_nonneg := vonMangoldtWeight_nonneg
  threshold := bound.threshold
  mainTerm := bound.mainTerm
  analyticError := bound.analyticError
  contamination := bound.contamination
  lowerBound := by
    intro n htn hEven
    simpa [RawVonMangoldtGoldbachSum] using
      bound.lowerBound n htn hEven
  contaminationBound := by
    intro n htn hEven
    simpa [NonPrimePairVonMangoldtGoldbachSum] using
      bound.contaminationBound n htn hEven
  totalErrorDominated := by
    intro n htn hEven
    exact bound.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_lower_bound
    (bound : VonMangoldtGoldbachLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_real_contaminated_weighted_lower_bound
    bound.toRealLowerBound

theorem explicit_lower_bound_of_vonMangoldt_lower_bound
    (bound : VonMangoldtGoldbachLowerBound) :
    ExplicitGoldbachLowerBound bound.threshold :=
  count_positive_above_of_vonMangoldt_lower_bound bound

theorem strongGoldbach_of_vonMangoldt_lower_bound_le100
    (bound : VonMangoldtGoldbachLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_real_contaminated_weighted_lower_bound_le100
    bound.toRealLowerBound
    (by
      simpa [VonMangoldtGoldbachLowerBound.toRealLowerBound] using
        hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtGoldbachLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_real_contaminated_weighted_lower_bound_le
    finite
    bound.toRealLowerBound
    (by
      simpa [VonMangoldtGoldbachLowerBound.toRealLowerBound] using
        hthreshold)

structure VonMangoldtMajorMinorArcEstimate where
  threshold : Nat
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  contamination : Nat → ℝ
  combinedLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  contaminationBound :
    ∀ n : Nat, threshold < n → Even n →
      NonPrimePairVonMangoldtGoldbachSum n ≤ contamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n + contamination n < mainTerm n

noncomputable def VonMangoldtMajorMinorArcEstimate.toRealEstimate
    (estimate : VonMangoldtMajorMinorArcEstimate) :
    RealContaminatedWeightedMajorMinorArcEstimate where
  weight := vonMangoldtWeight
  weight_nonneg := vonMangoldtWeight_nonneg
  threshold := estimate.threshold
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  contamination := estimate.contamination
  combinedLowerBound := by
    intro n htn hEven
    simpa [RawVonMangoldtGoldbachSum] using
      estimate.combinedLowerBound n htn hEven
  contaminationBound := by
    intro n htn hEven
    simpa [NonPrimePairVonMangoldtGoldbachSum] using
      estimate.contaminationBound n htn hEven
  totalErrorDominated := by
    intro n htn hEven
    exact estimate.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_major_minor_arc_estimate
    (estimate : VonMangoldtMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove estimate.threshold :=
  count_positive_above_of_real_contaminated_weighted_major_minor_arc_estimate
    estimate.toRealEstimate

theorem explicit_lower_bound_of_vonMangoldt_major_minor_arc_estimate
    (estimate : VonMangoldtMajorMinorArcEstimate) :
    ExplicitGoldbachLowerBound estimate.threshold :=
  count_positive_above_of_vonMangoldt_major_minor_arc_estimate estimate

theorem strongGoldbach_of_vonMangoldt_major_minor_arc_estimate_le100
    (estimate : VonMangoldtMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_real_contaminated_weighted_major_minor_arc_estimate_le100
    estimate.toRealEstimate
    (by
      simpa [VonMangoldtMajorMinorArcEstimate.toRealEstimate] using
        hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_real_contaminated_weighted_major_minor_arc_estimate_le
    finite
    estimate.toRealEstimate
    (by
      simpa [VonMangoldtMajorMinorArcEstimate.toRealEstimate] using
        hthreshold)

structure VonMangoldtPrimePowerContaminationLowerBound where
  threshold : Nat
  mainTerm : Nat → ℝ
  analyticError : Nat → ℝ
  contamination : Nat → ℝ
  lowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - analyticError n ≤ RawVonMangoldtGoldbachSum n
  primePowerContaminationBound :
    ∀ n : Nat, threshold < n → Even n →
      PrimePowerContaminationVonMangoldtGoldbachSum n ≤ contamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      analyticError n + contamination n < mainTerm n

noncomputable def VonMangoldtPrimePowerContaminationLowerBound.toLowerBound
    (bound : VonMangoldtPrimePowerContaminationLowerBound) :
    VonMangoldtGoldbachLowerBound where
  threshold := bound.threshold
  mainTerm := bound.mainTerm
  analyticError := bound.analyticError
  contamination := bound.contamination
  lowerBound := by
    intro n htn hEven
    exact bound.lowerBound n htn hEven
  contaminationBound := by
    intro n htn hEven
    rw [nonPrimePairVonMangoldtGoldbachSum_eq_primePowerContamination]
    exact bound.primePowerContaminationBound n htn hEven
  totalErrorDominated := by
    intro n htn hEven
    exact bound.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_prime_power_contamination_lower_bound
    (bound : VonMangoldtPrimePowerContaminationLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_vonMangoldt_lower_bound
    bound.toLowerBound

theorem strongGoldbach_of_vonMangoldt_prime_power_contamination_lower_bound_le100
    (bound : VonMangoldtPrimePowerContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_lower_bound_le100
    bound.toLowerBound
    (by
      simpa [VonMangoldtPrimePowerContaminationLowerBound.toLowerBound] using
        hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_prime_power_contamination_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtPrimePowerContaminationLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_lower_bound_le
    finite
    bound.toLowerBound
    (by
      simpa [VonMangoldtPrimePowerContaminationLowerBound.toLowerBound] using
        hthreshold)

structure VonMangoldtPrimePowerContaminationMajorMinorArcEstimate where
  threshold : Nat
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  contamination : Nat → ℝ
  combinedLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  primePowerContaminationBound :
    ∀ n : Nat, threshold < n → Even n →
      PrimePowerContaminationVonMangoldtGoldbachSum n ≤ contamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n + contamination n < mainTerm n

noncomputable def VonMangoldtPrimePowerContaminationMajorMinorArcEstimate.toEstimate
    (estimate : VonMangoldtPrimePowerContaminationMajorMinorArcEstimate) :
    VonMangoldtMajorMinorArcEstimate where
  threshold := estimate.threshold
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  contamination := estimate.contamination
  combinedLowerBound := by
    intro n htn hEven
    exact estimate.combinedLowerBound n htn hEven
  contaminationBound := by
    intro n htn hEven
    rw [nonPrimePairVonMangoldtGoldbachSum_eq_primePowerContamination]
    exact estimate.primePowerContaminationBound n htn hEven
  totalErrorDominated := by
    intro n htn hEven
    exact estimate.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_prime_power_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtPrimePowerContaminationMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove estimate.threshold :=
  count_positive_above_of_vonMangoldt_major_minor_arc_estimate
    estimate.toEstimate

theorem strongGoldbach_of_vonMangoldt_prime_power_contamination_major_minor_arc_estimate_le100
    (estimate : VonMangoldtPrimePowerContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_major_minor_arc_estimate_le100
    estimate.toEstimate
    (by
      simpa
        [VonMangoldtPrimePowerContaminationMajorMinorArcEstimate.toEstimate]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_prime_power_contamination_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtPrimePowerContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_major_minor_arc_estimate_le
    finite
    estimate.toEstimate
    (by
      simpa
        [VonMangoldtPrimePowerContaminationMajorMinorArcEstimate.toEstimate]
        using hthreshold)

structure VonMangoldtSplitPrimePowerContaminationLowerBound where
  threshold : Nat
  mainTerm : Nat → ℝ
  analyticError : Nat → ℝ
  leftContamination : Nat → ℝ
  rightContamination : Nat → ℝ
  lowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - analyticError n ≤ RawVonMangoldtGoldbachSum n
  leftContaminationBound :
    ∀ n : Nat, threshold < n → Even n →
      LeftPrimePowerContaminationVonMangoldtGoldbachSum n ≤
        leftContamination n
  rightContaminationBound :
    ∀ n : Nat, threshold < n → Even n →
      RightPrimePowerContaminationVonMangoldtGoldbachSum n ≤
        rightContamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      analyticError n + leftContamination n + rightContamination n <
        mainTerm n

noncomputable def VonMangoldtSplitPrimePowerContaminationLowerBound.toLowerBound
    (bound : VonMangoldtSplitPrimePowerContaminationLowerBound) :
    VonMangoldtPrimePowerContaminationLowerBound where
  threshold := bound.threshold
  mainTerm := bound.mainTerm
  analyticError := bound.analyticError
  contamination := fun n => bound.leftContamination n + bound.rightContamination n
  lowerBound := by
    intro n htn hEven
    exact bound.lowerBound n htn hEven
  primePowerContaminationBound := by
    intro n htn hEven
    have hsplit :=
      primePowerContaminationVonMangoldtGoldbachSum_le_left_add_right n
    have hleft := bound.leftContaminationBound n htn hEven
    have hright := bound.rightContaminationBound n htn hEven
    linarith
  totalErrorDominated := by
    intro n htn hEven
    have hdom := bound.totalErrorDominated n htn hEven
    linarith

theorem count_positive_above_of_vonMangoldt_split_prime_power_contamination_lower_bound
    (bound : VonMangoldtSplitPrimePowerContaminationLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_vonMangoldt_prime_power_contamination_lower_bound
    bound.toLowerBound

theorem strongGoldbach_of_vonMangoldt_split_prime_power_contamination_lower_bound_le100
    (bound : VonMangoldtSplitPrimePowerContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_prime_power_contamination_lower_bound_le100
    bound.toLowerBound
    (by
      simpa [VonMangoldtSplitPrimePowerContaminationLowerBound.toLowerBound]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_split_prime_power_contamination_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtSplitPrimePowerContaminationLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_prime_power_contamination_lower_bound_le
    finite
    bound.toLowerBound
    (by
      simpa [VonMangoldtSplitPrimePowerContaminationLowerBound.toLowerBound]
        using hthreshold)

structure VonMangoldtSplitPrimePowerContaminationMajorMinorArcEstimate where
  threshold : Nat
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  leftContamination : Nat → ℝ
  rightContamination : Nat → ℝ
  combinedLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  leftContaminationBound :
    ∀ n : Nat, threshold < n → Even n →
      LeftPrimePowerContaminationVonMangoldtGoldbachSum n ≤
        leftContamination n
  rightContaminationBound :
    ∀ n : Nat, threshold < n → Even n →
      RightPrimePowerContaminationVonMangoldtGoldbachSum n ≤
        rightContamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n + leftContamination n +
          rightContamination n <
        mainTerm n

noncomputable def VonMangoldtSplitPrimePowerContaminationMajorMinorArcEstimate.toEstimate
    (estimate : VonMangoldtSplitPrimePowerContaminationMajorMinorArcEstimate) :
    VonMangoldtPrimePowerContaminationMajorMinorArcEstimate where
  threshold := estimate.threshold
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  contamination := fun n =>
    estimate.leftContamination n + estimate.rightContamination n
  combinedLowerBound := by
    intro n htn hEven
    exact estimate.combinedLowerBound n htn hEven
  primePowerContaminationBound := by
    intro n htn hEven
    have hsplit :=
      primePowerContaminationVonMangoldtGoldbachSum_le_left_add_right n
    have hleft := estimate.leftContaminationBound n htn hEven
    have hright := estimate.rightContaminationBound n htn hEven
    linarith
  totalErrorDominated := by
    intro n htn hEven
    have hdom := estimate.totalErrorDominated n htn hEven
    linarith

theorem count_positive_above_of_vonMangoldt_split_prime_power_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtSplitPrimePowerContaminationMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove estimate.threshold :=
  count_positive_above_of_vonMangoldt_prime_power_contamination_major_minor_arc_estimate
    estimate.toEstimate

theorem strongGoldbach_of_vonMangoldt_split_prime_power_contamination_major_minor_arc_estimate_le100
    (estimate : VonMangoldtSplitPrimePowerContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_prime_power_contamination_major_minor_arc_estimate_le100
    estimate.toEstimate
    (by
      simpa
        [VonMangoldtSplitPrimePowerContaminationMajorMinorArcEstimate.toEstimate]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_split_prime_power_contamination_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtSplitPrimePowerContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_prime_power_contamination_major_minor_arc_estimate_le
    finite
    estimate.toEstimate
    (by
      simpa
        [VonMangoldtSplitPrimePowerContaminationMajorMinorArcEstimate.toEstimate]
        using hthreshold)

structure VonMangoldtPointwiseSplitContaminationLowerBound where
  threshold : Nat
  mainTerm : Nat → ℝ
  analyticError : Nat → ℝ
  leftContributionBound : Nat → Nat → ℝ
  rightContributionBound : Nat → Nat → ℝ
  leftContamination : Nat → ℝ
  rightContamination : Nat → ℝ
  lowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - analyticError n ≤ RawVonMangoldtGoldbachSum n
  leftPointwiseBound :
    ∀ n : Nat, threshold < n → Even n →
      ∀ p ∈ (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧ IsPrimePow (n - p)),
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤
          leftContributionBound n p
  leftContributionSumBound :
    ∀ n : Nat, threshold < n → Even n →
      ((Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧ IsPrimePow (n - p))).sum
          (leftContributionBound n) ≤ leftContamination n
  rightPointwiseBound :
    ∀ n : Nat, threshold < n → Even n →
      ∀ p ∈ (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
          ¬ Nat.Prime (n - p)),
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤
          rightContributionBound n p
  rightContributionSumBound :
    ∀ n : Nat, threshold < n → Even n →
      ((Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
          ¬ Nat.Prime (n - p))).sum (rightContributionBound n) ≤
            rightContamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      analyticError n + leftContamination n + rightContamination n <
        mainTerm n

noncomputable def VonMangoldtPointwiseSplitContaminationLowerBound.toLowerBound
    (bound : VonMangoldtPointwiseSplitContaminationLowerBound) :
    VonMangoldtSplitPrimePowerContaminationLowerBound where
  threshold := bound.threshold
  mainTerm := bound.mainTerm
  analyticError := bound.analyticError
  leftContamination := bound.leftContamination
  rightContamination := bound.rightContamination
  lowerBound := by
    intro n htn hEven
    exact bound.lowerBound n htn hEven
  leftContaminationBound := by
    intro n htn hEven
    exact le_trans
      (leftPrimePowerContaminationVonMangoldtGoldbachSum_le_sum_of_pointwise
        (bound.leftPointwiseBound n htn hEven))
      (bound.leftContributionSumBound n htn hEven)
  rightContaminationBound := by
    intro n htn hEven
    exact le_trans
      (rightPrimePowerContaminationVonMangoldtGoldbachSum_le_sum_of_pointwise
        (bound.rightPointwiseBound n htn hEven))
      (bound.rightContributionSumBound n htn hEven)
  totalErrorDominated := by
    intro n htn hEven
    exact bound.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_pointwise_split_contamination_lower_bound
    (bound : VonMangoldtPointwiseSplitContaminationLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_vonMangoldt_split_prime_power_contamination_lower_bound
    bound.toLowerBound

theorem strongGoldbach_of_vonMangoldt_pointwise_split_contamination_lower_bound_le100
    (bound : VonMangoldtPointwiseSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_split_prime_power_contamination_lower_bound_le100
    bound.toLowerBound
    (by
      simpa [VonMangoldtPointwiseSplitContaminationLowerBound.toLowerBound]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_pointwise_split_contamination_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtPointwiseSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_split_prime_power_contamination_lower_bound_le
    finite
    bound.toLowerBound
    (by
      simpa [VonMangoldtPointwiseSplitContaminationLowerBound.toLowerBound]
        using hthreshold)

structure VonMangoldtPointwiseSplitContaminationMajorMinorArcEstimate where
  threshold : Nat
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  leftContributionBound : Nat → Nat → ℝ
  rightContributionBound : Nat → Nat → ℝ
  leftContamination : Nat → ℝ
  rightContamination : Nat → ℝ
  combinedLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  leftPointwiseBound :
    ∀ n : Nat, threshold < n → Even n →
      ∀ p ∈ (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧ IsPrimePow (n - p)),
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤
          leftContributionBound n p
  leftContributionSumBound :
    ∀ n : Nat, threshold < n → Even n →
      ((Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧ IsPrimePow (n - p))).sum
          (leftContributionBound n) ≤ leftContamination n
  rightPointwiseBound :
    ∀ n : Nat, threshold < n → Even n →
      ∀ p ∈ (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
          ¬ Nat.Prime (n - p)),
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤
          rightContributionBound n p
  rightContributionSumBound :
    ∀ n : Nat, threshold < n → Even n →
      ((Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
          ¬ Nat.Prime (n - p))).sum (rightContributionBound n) ≤
            rightContamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n + leftContamination n +
          rightContamination n <
        mainTerm n

noncomputable def VonMangoldtPointwiseSplitContaminationMajorMinorArcEstimate.toEstimate
    (estimate : VonMangoldtPointwiseSplitContaminationMajorMinorArcEstimate) :
    VonMangoldtSplitPrimePowerContaminationMajorMinorArcEstimate where
  threshold := estimate.threshold
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  leftContamination := estimate.leftContamination
  rightContamination := estimate.rightContamination
  combinedLowerBound := by
    intro n htn hEven
    exact estimate.combinedLowerBound n htn hEven
  leftContaminationBound := by
    intro n htn hEven
    exact le_trans
      (leftPrimePowerContaminationVonMangoldtGoldbachSum_le_sum_of_pointwise
        (estimate.leftPointwiseBound n htn hEven))
      (estimate.leftContributionSumBound n htn hEven)
  rightContaminationBound := by
    intro n htn hEven
    exact le_trans
      (rightPrimePowerContaminationVonMangoldtGoldbachSum_le_sum_of_pointwise
        (estimate.rightPointwiseBound n htn hEven))
      (estimate.rightContributionSumBound n htn hEven)
  totalErrorDominated := by
    intro n htn hEven
    exact estimate.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_pointwise_split_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtPointwiseSplitContaminationMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove estimate.threshold :=
  count_positive_above_of_vonMangoldt_split_prime_power_contamination_major_minor_arc_estimate
    estimate.toEstimate

theorem strongGoldbach_of_vonMangoldt_pointwise_split_contamination_major_minor_arc_estimate_le100
    (estimate : VonMangoldtPointwiseSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_split_prime_power_contamination_major_minor_arc_estimate_le100
    estimate.toEstimate
    (by
      simpa
        [VonMangoldtPointwiseSplitContaminationMajorMinorArcEstimate.toEstimate]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_pointwise_split_contamination_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtPointwiseSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_split_prime_power_contamination_major_minor_arc_estimate_le
    finite
    estimate.toEstimate
    (by
      simpa
        [VonMangoldtPointwiseSplitContaminationMajorMinorArcEstimate.toEstimate]
        using hthreshold)

structure VonMangoldtUniformSplitContaminationLowerBound where
  threshold : Nat
  mainTerm : Nat → ℝ
  analyticError : Nat → ℝ
  leftTermBound : Nat → ℝ
  rightTermBound : Nat → ℝ
  leftCountBound : Nat → ℝ
  rightCountBound : Nat → ℝ
  leftContamination : Nat → ℝ
  rightContamination : Nat → ℝ
  lowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - analyticError n ≤ RawVonMangoldtGoldbachSum n
  leftTermBoundNonneg :
    ∀ n : Nat, threshold < n → Even n → 0 ≤ leftTermBound n
  rightTermBoundNonneg :
    ∀ n : Nat, threshold < n → Even n → 0 ≤ rightTermBound n
  leftPointwiseBound :
    ∀ n : Nat, threshold < n → Even n →
      ∀ p ∈ (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧ IsPrimePow (n - p)),
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤
          leftTermBound n
  rightPointwiseBound :
    ∀ n : Nat, threshold < n → Even n →
      ∀ p ∈ (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
          ¬ Nat.Prime (n - p)),
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤
          rightTermBound n
  leftCardBound :
    ∀ n : Nat, threshold < n → Even n →
      (((Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧ IsPrimePow (n - p))).card :
          ℝ) ≤ leftCountBound n
  rightCardBound :
    ∀ n : Nat, threshold < n → Even n →
      (((Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
          ¬ Nat.Prime (n - p))).card : ℝ) ≤ rightCountBound n
  leftProductBound :
    ∀ n : Nat, threshold < n → Even n →
      leftCountBound n * leftTermBound n ≤ leftContamination n
  rightProductBound :
    ∀ n : Nat, threshold < n → Even n →
      rightCountBound n * rightTermBound n ≤ rightContamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      analyticError n + leftContamination n + rightContamination n <
        mainTerm n

noncomputable def VonMangoldtUniformSplitContaminationLowerBound.toPointwiseLowerBound
    (bound : VonMangoldtUniformSplitContaminationLowerBound) :
    VonMangoldtPointwiseSplitContaminationLowerBound where
  threshold := bound.threshold
  mainTerm := bound.mainTerm
  analyticError := bound.analyticError
  leftContributionBound := fun n _ => bound.leftTermBound n
  rightContributionBound := fun n _ => bound.rightTermBound n
  leftContamination := bound.leftContamination
  rightContamination := bound.rightContamination
  lowerBound := by
    intro n htn hEven
    exact bound.lowerBound n htn hEven
  leftPointwiseBound := by
    intro n htn hEven p hp
    exact bound.leftPointwiseBound n htn hEven p hp
  leftContributionSumBound := by
    intro n htn hEven
    let leftSet :=
      (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧ IsPrimePow (n - p))
    have hsum :
        leftSet.sum (fun _ => bound.leftTermBound n) ≤
          (leftSet.card : ℝ) * bound.leftTermBound n :=
      realFinsetSum_le_card_mul_of_pointwise_bound
        (s := leftSet)
        (f := fun _ => bound.leftTermBound n)
        (C := bound.leftTermBound n)
        (by intro p hp; exact le_rfl)
    have hcard := bound.leftCardBound n htn hEven
    have hterm := bound.leftTermBoundNonneg n htn hEven
    have hproduct :
        (leftSet.card : ℝ) * bound.leftTermBound n ≤
          bound.leftCountBound n * bound.leftTermBound n := by
      exact mul_le_mul_of_nonneg_right hcard hterm
    have hcont := bound.leftProductBound n htn hEven
    exact le_trans hsum (le_trans hproduct hcont)
  rightPointwiseBound := by
    intro n htn hEven p hp
    exact bound.rightPointwiseBound n htn hEven p hp
  rightContributionSumBound := by
    intro n htn hEven
    let rightSet :=
      (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
          ¬ Nat.Prime (n - p))
    have hsum :
        rightSet.sum (fun _ => bound.rightTermBound n) ≤
          (rightSet.card : ℝ) * bound.rightTermBound n :=
      realFinsetSum_le_card_mul_of_pointwise_bound
        (s := rightSet)
        (f := fun _ => bound.rightTermBound n)
        (C := bound.rightTermBound n)
        (by intro p hp; exact le_rfl)
    have hcard := bound.rightCardBound n htn hEven
    have hterm := bound.rightTermBoundNonneg n htn hEven
    have hproduct :
        (rightSet.card : ℝ) * bound.rightTermBound n ≤
          bound.rightCountBound n * bound.rightTermBound n := by
      exact mul_le_mul_of_nonneg_right hcard hterm
    have hcont := bound.rightProductBound n htn hEven
    exact le_trans hsum (le_trans hproduct hcont)
  totalErrorDominated := by
    intro n htn hEven
    exact bound.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_uniform_split_contamination_lower_bound
    (bound : VonMangoldtUniformSplitContaminationLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_vonMangoldt_pointwise_split_contamination_lower_bound
    bound.toPointwiseLowerBound

theorem strongGoldbach_of_vonMangoldt_uniform_split_contamination_lower_bound_le100
    (bound : VonMangoldtUniformSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_pointwise_split_contamination_lower_bound_le100
    bound.toPointwiseLowerBound
    (by
      simpa
        [VonMangoldtUniformSplitContaminationLowerBound.toPointwiseLowerBound]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_uniform_split_contamination_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtUniformSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_pointwise_split_contamination_lower_bound_le
    finite
    bound.toPointwiseLowerBound
    (by
      simpa
        [VonMangoldtUniformSplitContaminationLowerBound.toPointwiseLowerBound]
        using hthreshold)

structure VonMangoldtUniformSplitContaminationMajorMinorArcEstimate where
  threshold : Nat
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  leftTermBound : Nat → ℝ
  rightTermBound : Nat → ℝ
  leftCountBound : Nat → ℝ
  rightCountBound : Nat → ℝ
  leftContamination : Nat → ℝ
  rightContamination : Nat → ℝ
  combinedLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  leftTermBoundNonneg :
    ∀ n : Nat, threshold < n → Even n → 0 ≤ leftTermBound n
  rightTermBoundNonneg :
    ∀ n : Nat, threshold < n → Even n → 0 ≤ rightTermBound n
  leftPointwiseBound :
    ∀ n : Nat, threshold < n → Even n →
      ∀ p ∈ (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧ IsPrimePow (n - p)),
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤
          leftTermBound n
  rightPointwiseBound :
    ∀ n : Nat, threshold < n → Even n →
      ∀ p ∈ (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
          ¬ Nat.Prime (n - p)),
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤
          rightTermBound n
  leftCardBound :
    ∀ n : Nat, threshold < n → Even n →
      (((Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧ IsPrimePow (n - p))).card :
          ℝ) ≤ leftCountBound n
  rightCardBound :
    ∀ n : Nat, threshold < n → Even n →
      (((Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
          ¬ Nat.Prime (n - p))).card : ℝ) ≤ rightCountBound n
  leftProductBound :
    ∀ n : Nat, threshold < n → Even n →
      leftCountBound n * leftTermBound n ≤ leftContamination n
  rightProductBound :
    ∀ n : Nat, threshold < n → Even n →
      rightCountBound n * rightTermBound n ≤ rightContamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n + leftContamination n +
          rightContamination n <
        mainTerm n

noncomputable def VonMangoldtUniformSplitContaminationMajorMinorArcEstimate.toPointwiseEstimate
    (estimate : VonMangoldtUniformSplitContaminationMajorMinorArcEstimate) :
    VonMangoldtPointwiseSplitContaminationMajorMinorArcEstimate where
  threshold := estimate.threshold
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  leftContributionBound := fun n _ => estimate.leftTermBound n
  rightContributionBound := fun n _ => estimate.rightTermBound n
  leftContamination := estimate.leftContamination
  rightContamination := estimate.rightContamination
  combinedLowerBound := by
    intro n htn hEven
    exact estimate.combinedLowerBound n htn hEven
  leftPointwiseBound := by
    intro n htn hEven p hp
    exact estimate.leftPointwiseBound n htn hEven p hp
  leftContributionSumBound := by
    intro n htn hEven
    let leftSet :=
      (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧ IsPrimePow (n - p))
    have hsum :
        leftSet.sum (fun _ => estimate.leftTermBound n) ≤
          (leftSet.card : ℝ) * estimate.leftTermBound n :=
      realFinsetSum_le_card_mul_of_pointwise_bound
        (s := leftSet)
        (f := fun _ => estimate.leftTermBound n)
        (C := estimate.leftTermBound n)
        (by intro p hp; exact le_rfl)
    have hcard := estimate.leftCardBound n htn hEven
    have hterm := estimate.leftTermBoundNonneg n htn hEven
    have hproduct :
        (leftSet.card : ℝ) * estimate.leftTermBound n ≤
          estimate.leftCountBound n * estimate.leftTermBound n := by
      exact mul_le_mul_of_nonneg_right hcard hterm
    have hcont := estimate.leftProductBound n htn hEven
    exact le_trans hsum (le_trans hproduct hcont)
  rightPointwiseBound := by
    intro n htn hEven p hp
    exact estimate.rightPointwiseBound n htn hEven p hp
  rightContributionSumBound := by
    intro n htn hEven
    let rightSet :=
      (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
          ¬ Nat.Prime (n - p))
    have hsum :
        rightSet.sum (fun _ => estimate.rightTermBound n) ≤
          (rightSet.card : ℝ) * estimate.rightTermBound n :=
      realFinsetSum_le_card_mul_of_pointwise_bound
        (s := rightSet)
        (f := fun _ => estimate.rightTermBound n)
        (C := estimate.rightTermBound n)
        (by intro p hp; exact le_rfl)
    have hcard := estimate.rightCardBound n htn hEven
    have hterm := estimate.rightTermBoundNonneg n htn hEven
    have hproduct :
        (rightSet.card : ℝ) * estimate.rightTermBound n ≤
          estimate.rightCountBound n * estimate.rightTermBound n := by
      exact mul_le_mul_of_nonneg_right hcard hterm
    have hcont := estimate.rightProductBound n htn hEven
    exact le_trans hsum (le_trans hproduct hcont)
  totalErrorDominated := by
    intro n htn hEven
    exact estimate.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_uniform_split_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtUniformSplitContaminationMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove estimate.threshold :=
  count_positive_above_of_vonMangoldt_pointwise_split_contamination_major_minor_arc_estimate
    estimate.toPointwiseEstimate

theorem strongGoldbach_of_vonMangoldt_uniform_split_contamination_major_minor_arc_estimate_le100
    (estimate : VonMangoldtUniformSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_pointwise_split_contamination_major_minor_arc_estimate_le100
    estimate.toPointwiseEstimate
    (by
      simpa
        [VonMangoldtUniformSplitContaminationMajorMinorArcEstimate.toPointwiseEstimate]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_uniform_split_contamination_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtUniformSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_pointwise_split_contamination_major_minor_arc_estimate_le
    finite
    estimate.toPointwiseEstimate
    (by
      simpa
        [VonMangoldtUniformSplitContaminationMajorMinorArcEstimate.toPointwiseEstimate]
        using hthreshold)

structure VonMangoldtCountedSplitContaminationLowerBound where
  threshold : Nat
  mainTerm : Nat → ℝ
  analyticError : Nat → ℝ
  leftTermBound : Nat → ℝ
  rightTermBound : Nat → ℝ
  nonPrimePrimePowerCountBound : Nat → ℝ
  leftContamination : Nat → ℝ
  rightContamination : Nat → ℝ
  lowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - analyticError n ≤ RawVonMangoldtGoldbachSum n
  leftTermBoundNonneg :
    ∀ n : Nat, threshold < n → Even n → 0 ≤ leftTermBound n
  rightTermBoundNonneg :
    ∀ n : Nat, threshold < n → Even n → 0 ≤ rightTermBound n
  leftPointwiseBound :
    ∀ n : Nat, threshold < n → Even n →
      ∀ p ∈ (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧ IsPrimePow (n - p)),
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤
          leftTermBound n
  rightPointwiseBound :
    ∀ n : Nat, threshold < n → Even n →
      ∀ p ∈ (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
          ¬ Nat.Prime (n - p)),
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤
          rightTermBound n
  nonPrimePrimePowerCountBoundValid :
    ∀ n : Nat, threshold < n → Even n →
      (NonPrimePrimePowerCount n : ℝ) ≤ nonPrimePrimePowerCountBound n
  leftProductBound :
    ∀ n : Nat, threshold < n → Even n →
      nonPrimePrimePowerCountBound n * leftTermBound n ≤
        leftContamination n
  rightProductBound :
    ∀ n : Nat, threshold < n → Even n →
      nonPrimePrimePowerCountBound n * rightTermBound n ≤
        rightContamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      analyticError n + leftContamination n + rightContamination n <
        mainTerm n

noncomputable def VonMangoldtCountedSplitContaminationLowerBound.toUniformLowerBound
    (bound : VonMangoldtCountedSplitContaminationLowerBound) :
    VonMangoldtUniformSplitContaminationLowerBound where
  threshold := bound.threshold
  mainTerm := bound.mainTerm
  analyticError := bound.analyticError
  leftTermBound := bound.leftTermBound
  rightTermBound := bound.rightTermBound
  leftCountBound := bound.nonPrimePrimePowerCountBound
  rightCountBound := bound.nonPrimePrimePowerCountBound
  leftContamination := bound.leftContamination
  rightContamination := bound.rightContamination
  lowerBound := by
    intro n htn hEven
    exact bound.lowerBound n htn hEven
  leftTermBoundNonneg := by
    intro n htn hEven
    exact bound.leftTermBoundNonneg n htn hEven
  rightTermBoundNonneg := by
    intro n htn hEven
    exact bound.rightTermBoundNonneg n htn hEven
  leftPointwiseBound := by
    intro n htn hEven p hp
    exact bound.leftPointwiseBound n htn hEven p hp
  rightPointwiseBound := by
    intro n htn hEven p hp
    exact bound.rightPointwiseBound n htn hEven p hp
  leftCardBound := by
    intro n htn hEven
    exact le_trans
      (leftPrimePowerContaminationSet_real_card_le_nonPrimePrimePowerCount n)
      (bound.nonPrimePrimePowerCountBoundValid n htn hEven)
  rightCardBound := by
    intro n htn hEven
    exact le_trans
      (rightPrimePowerContaminationSet_real_card_le_nonPrimePrimePowerCount n)
      (bound.nonPrimePrimePowerCountBoundValid n htn hEven)
  leftProductBound := by
    intro n htn hEven
    exact bound.leftProductBound n htn hEven
  rightProductBound := by
    intro n htn hEven
    exact bound.rightProductBound n htn hEven
  totalErrorDominated := by
    intro n htn hEven
    exact bound.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_counted_split_contamination_lower_bound
    (bound : VonMangoldtCountedSplitContaminationLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_vonMangoldt_uniform_split_contamination_lower_bound
    bound.toUniformLowerBound

theorem strongGoldbach_of_vonMangoldt_counted_split_contamination_lower_bound_le100
    (bound : VonMangoldtCountedSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_uniform_split_contamination_lower_bound_le100
    bound.toUniformLowerBound
    (by
      simpa
        [VonMangoldtCountedSplitContaminationLowerBound.toUniformLowerBound]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_counted_split_contamination_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtCountedSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_uniform_split_contamination_lower_bound_le
    finite
    bound.toUniformLowerBound
    (by
      simpa
        [VonMangoldtCountedSplitContaminationLowerBound.toUniformLowerBound]
        using hthreshold)

structure VonMangoldtCountedSplitContaminationMajorMinorArcEstimate where
  threshold : Nat
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  leftTermBound : Nat → ℝ
  rightTermBound : Nat → ℝ
  nonPrimePrimePowerCountBound : Nat → ℝ
  leftContamination : Nat → ℝ
  rightContamination : Nat → ℝ
  combinedLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  leftTermBoundNonneg :
    ∀ n : Nat, threshold < n → Even n → 0 ≤ leftTermBound n
  rightTermBoundNonneg :
    ∀ n : Nat, threshold < n → Even n → 0 ≤ rightTermBound n
  leftPointwiseBound :
    ∀ n : Nat, threshold < n → Even n →
      ∀ p ∈ (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧ IsPrimePow (n - p)),
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤
          leftTermBound n
  rightPointwiseBound :
    ∀ n : Nat, threshold < n → Even n →
      ∀ p ∈ (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
          ¬ Nat.Prime (n - p)),
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤
          rightTermBound n
  nonPrimePrimePowerCountBoundValid :
    ∀ n : Nat, threshold < n → Even n →
      (NonPrimePrimePowerCount n : ℝ) ≤ nonPrimePrimePowerCountBound n
  leftProductBound :
    ∀ n : Nat, threshold < n → Even n →
      nonPrimePrimePowerCountBound n * leftTermBound n ≤
        leftContamination n
  rightProductBound :
    ∀ n : Nat, threshold < n → Even n →
      nonPrimePrimePowerCountBound n * rightTermBound n ≤
        rightContamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n + leftContamination n +
          rightContamination n <
        mainTerm n

noncomputable def VonMangoldtCountedSplitContaminationMajorMinorArcEstimate.toUniformEstimate
    (estimate : VonMangoldtCountedSplitContaminationMajorMinorArcEstimate) :
    VonMangoldtUniformSplitContaminationMajorMinorArcEstimate where
  threshold := estimate.threshold
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  leftTermBound := estimate.leftTermBound
  rightTermBound := estimate.rightTermBound
  leftCountBound := estimate.nonPrimePrimePowerCountBound
  rightCountBound := estimate.nonPrimePrimePowerCountBound
  leftContamination := estimate.leftContamination
  rightContamination := estimate.rightContamination
  combinedLowerBound := by
    intro n htn hEven
    exact estimate.combinedLowerBound n htn hEven
  leftTermBoundNonneg := by
    intro n htn hEven
    exact estimate.leftTermBoundNonneg n htn hEven
  rightTermBoundNonneg := by
    intro n htn hEven
    exact estimate.rightTermBoundNonneg n htn hEven
  leftPointwiseBound := by
    intro n htn hEven p hp
    exact estimate.leftPointwiseBound n htn hEven p hp
  rightPointwiseBound := by
    intro n htn hEven p hp
    exact estimate.rightPointwiseBound n htn hEven p hp
  leftCardBound := by
    intro n htn hEven
    exact le_trans
      (leftPrimePowerContaminationSet_real_card_le_nonPrimePrimePowerCount n)
      (estimate.nonPrimePrimePowerCountBoundValid n htn hEven)
  rightCardBound := by
    intro n htn hEven
    exact le_trans
      (rightPrimePowerContaminationSet_real_card_le_nonPrimePrimePowerCount n)
      (estimate.nonPrimePrimePowerCountBoundValid n htn hEven)
  leftProductBound := by
    intro n htn hEven
    exact estimate.leftProductBound n htn hEven
  rightProductBound := by
    intro n htn hEven
    exact estimate.rightProductBound n htn hEven
  totalErrorDominated := by
    intro n htn hEven
    exact estimate.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_counted_split_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtCountedSplitContaminationMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove estimate.threshold :=
  count_positive_above_of_vonMangoldt_uniform_split_contamination_major_minor_arc_estimate
    estimate.toUniformEstimate

theorem strongGoldbach_of_vonMangoldt_counted_split_contamination_major_minor_arc_estimate_le100
    (estimate : VonMangoldtCountedSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_uniform_split_contamination_major_minor_arc_estimate_le100
    estimate.toUniformEstimate
    (by
      simpa
        [VonMangoldtCountedSplitContaminationMajorMinorArcEstimate.toUniformEstimate]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_counted_split_contamination_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtCountedSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_uniform_split_contamination_major_minor_arc_estimate_le
    finite
    estimate.toUniformEstimate
    (by
      simpa
        [VonMangoldtCountedSplitContaminationMajorMinorArcEstimate.toUniformEstimate]
        using hthreshold)

structure VonMangoldtTrivialCountSplitContaminationLowerBound where
  threshold : Nat
  mainTerm : Nat → ℝ
  analyticError : Nat → ℝ
  leftTermBound : Nat → ℝ
  rightTermBound : Nat → ℝ
  leftContamination : Nat → ℝ
  rightContamination : Nat → ℝ
  lowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - analyticError n ≤ RawVonMangoldtGoldbachSum n
  leftTermBoundNonneg :
    ∀ n : Nat, threshold < n → Even n → 0 ≤ leftTermBound n
  rightTermBoundNonneg :
    ∀ n : Nat, threshold < n → Even n → 0 ≤ rightTermBound n
  leftPointwiseBound :
    ∀ n : Nat, threshold < n → Even n →
      ∀ p ∈ (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧ IsPrimePow (n - p)),
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤
          leftTermBound n
  rightPointwiseBound :
    ∀ n : Nat, threshold < n → Even n →
      ∀ p ∈ (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
          ¬ Nat.Prime (n - p)),
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤
          rightTermBound n
  leftProductBound :
    ∀ n : Nat, threshold < n → Even n →
      (n.succ : ℝ) * leftTermBound n ≤ leftContamination n
  rightProductBound :
    ∀ n : Nat, threshold < n → Even n →
      (n.succ : ℝ) * rightTermBound n ≤ rightContamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      analyticError n + leftContamination n + rightContamination n <
        mainTerm n

noncomputable def VonMangoldtTrivialCountSplitContaminationLowerBound.toCountedLowerBound
    (bound : VonMangoldtTrivialCountSplitContaminationLowerBound) :
    VonMangoldtCountedSplitContaminationLowerBound where
  threshold := bound.threshold
  mainTerm := bound.mainTerm
  analyticError := bound.analyticError
  leftTermBound := bound.leftTermBound
  rightTermBound := bound.rightTermBound
  nonPrimePrimePowerCountBound := fun n => (n.succ : ℝ)
  leftContamination := bound.leftContamination
  rightContamination := bound.rightContamination
  lowerBound := by
    intro n htn hEven
    exact bound.lowerBound n htn hEven
  leftTermBoundNonneg := by
    intro n htn hEven
    exact bound.leftTermBoundNonneg n htn hEven
  rightTermBoundNonneg := by
    intro n htn hEven
    exact bound.rightTermBoundNonneg n htn hEven
  leftPointwiseBound := by
    intro n htn hEven p hp
    exact bound.leftPointwiseBound n htn hEven p hp
  rightPointwiseBound := by
    intro n htn hEven p hp
    exact bound.rightPointwiseBound n htn hEven p hp
  nonPrimePrimePowerCountBoundValid := by
    intro n htn hEven
    exact nonPrimePrimePowerCount_real_le_succ n
  leftProductBound := by
    intro n htn hEven
    exact bound.leftProductBound n htn hEven
  rightProductBound := by
    intro n htn hEven
    exact bound.rightProductBound n htn hEven
  totalErrorDominated := by
    intro n htn hEven
    exact bound.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_trivial_count_split_contamination_lower_bound
    (bound : VonMangoldtTrivialCountSplitContaminationLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_vonMangoldt_counted_split_contamination_lower_bound
    bound.toCountedLowerBound

theorem strongGoldbach_of_vonMangoldt_trivial_count_split_contamination_lower_bound_le100
    (bound : VonMangoldtTrivialCountSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_counted_split_contamination_lower_bound_le100
    bound.toCountedLowerBound
    (by
      simpa
        [VonMangoldtTrivialCountSplitContaminationLowerBound.toCountedLowerBound]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_trivial_count_split_contamination_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtTrivialCountSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_counted_split_contamination_lower_bound_le
    finite
    bound.toCountedLowerBound
    (by
      simpa
        [VonMangoldtTrivialCountSplitContaminationLowerBound.toCountedLowerBound]
        using hthreshold)

structure VonMangoldtTrivialCountSplitContaminationMajorMinorArcEstimate where
  threshold : Nat
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  leftTermBound : Nat → ℝ
  rightTermBound : Nat → ℝ
  leftContamination : Nat → ℝ
  rightContamination : Nat → ℝ
  combinedLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  leftTermBoundNonneg :
    ∀ n : Nat, threshold < n → Even n → 0 ≤ leftTermBound n
  rightTermBoundNonneg :
    ∀ n : Nat, threshold < n → Even n → 0 ≤ rightTermBound n
  leftPointwiseBound :
    ∀ n : Nat, threshold < n → Even n →
      ∀ p ∈ (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧ IsPrimePow (n - p)),
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤
          leftTermBound n
  rightPointwiseBound :
    ∀ n : Nat, threshold < n → Even n →
      ∀ p ∈ (Finset.range n.succ).filter
        (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
          ¬ Nat.Prime (n - p)),
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤
          rightTermBound n
  leftProductBound :
    ∀ n : Nat, threshold < n → Even n →
      (n.succ : ℝ) * leftTermBound n ≤ leftContamination n
  rightProductBound :
    ∀ n : Nat, threshold < n → Even n →
      (n.succ : ℝ) * rightTermBound n ≤ rightContamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n + leftContamination n +
          rightContamination n <
        mainTerm n

noncomputable def VonMangoldtTrivialCountSplitContaminationMajorMinorArcEstimate.toCountedEstimate
    (estimate : VonMangoldtTrivialCountSplitContaminationMajorMinorArcEstimate) :
    VonMangoldtCountedSplitContaminationMajorMinorArcEstimate where
  threshold := estimate.threshold
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  leftTermBound := estimate.leftTermBound
  rightTermBound := estimate.rightTermBound
  nonPrimePrimePowerCountBound := fun n => (n.succ : ℝ)
  leftContamination := estimate.leftContamination
  rightContamination := estimate.rightContamination
  combinedLowerBound := by
    intro n htn hEven
    exact estimate.combinedLowerBound n htn hEven
  leftTermBoundNonneg := by
    intro n htn hEven
    exact estimate.leftTermBoundNonneg n htn hEven
  rightTermBoundNonneg := by
    intro n htn hEven
    exact estimate.rightTermBoundNonneg n htn hEven
  leftPointwiseBound := by
    intro n htn hEven p hp
    exact estimate.leftPointwiseBound n htn hEven p hp
  rightPointwiseBound := by
    intro n htn hEven p hp
    exact estimate.rightPointwiseBound n htn hEven p hp
  nonPrimePrimePowerCountBoundValid := by
    intro n htn hEven
    exact nonPrimePrimePowerCount_real_le_succ n
  leftProductBound := by
    intro n htn hEven
    exact estimate.leftProductBound n htn hEven
  rightProductBound := by
    intro n htn hEven
    exact estimate.rightProductBound n htn hEven
  totalErrorDominated := by
    intro n htn hEven
    exact estimate.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_trivial_count_split_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtTrivialCountSplitContaminationMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove estimate.threshold :=
  count_positive_above_of_vonMangoldt_counted_split_contamination_major_minor_arc_estimate
    estimate.toCountedEstimate

theorem strongGoldbach_of_vonMangoldt_trivial_count_split_contamination_major_minor_arc_estimate_le100
    (estimate : VonMangoldtTrivialCountSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_counted_split_contamination_major_minor_arc_estimate_le100
    estimate.toCountedEstimate
    (by
      simpa
        [VonMangoldtTrivialCountSplitContaminationMajorMinorArcEstimate.toCountedEstimate]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_trivial_count_split_contamination_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtTrivialCountSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_counted_split_contamination_major_minor_arc_estimate_le
    finite
    estimate.toCountedEstimate
    (by
      simpa
        [VonMangoldtTrivialCountSplitContaminationMajorMinorArcEstimate.toCountedEstimate]
        using hthreshold)

structure VonMangoldtWeightBoundSplitContaminationLowerBound where
  threshold : Nat
  mainTerm : Nat → ℝ
  analyticError : Nat → ℝ
  weightBound : Nat → ℝ
  leftContamination : Nat → ℝ
  rightContamination : Nat → ℝ
  lowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - analyticError n ≤ RawVonMangoldtGoldbachSum n
  weightBoundNonneg :
    ∀ n : Nat, threshold < n → Even n → 0 ≤ weightBound n
  weightBoundOnPrimePowersUpTo :
    ∀ n : Nat, threshold < n → Even n →
      ∀ m ∈ Finset.range n.succ, IsPrimePow m →
        vonMangoldtWeight m ≤ weightBound n
  leftProductBound :
    ∀ n : Nat, threshold < n → Even n →
      (n.succ : ℝ) * (weightBound n * weightBound n) ≤
        leftContamination n
  rightProductBound :
    ∀ n : Nat, threshold < n → Even n →
      (n.succ : ℝ) * (weightBound n * weightBound n) ≤
        rightContamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      analyticError n + leftContamination n + rightContamination n <
        mainTerm n

noncomputable def VonMangoldtWeightBoundSplitContaminationLowerBound.toTrivialCountLowerBound
    (bound : VonMangoldtWeightBoundSplitContaminationLowerBound) :
    VonMangoldtTrivialCountSplitContaminationLowerBound where
  threshold := bound.threshold
  mainTerm := bound.mainTerm
  analyticError := bound.analyticError
  leftTermBound := fun n => bound.weightBound n * bound.weightBound n
  rightTermBound := fun n => bound.weightBound n * bound.weightBound n
  leftContamination := bound.leftContamination
  rightContamination := bound.rightContamination
  lowerBound := by
    intro n htn hEven
    exact bound.lowerBound n htn hEven
  leftTermBoundNonneg := by
    intro n htn hEven
    exact mul_nonneg (bound.weightBoundNonneg n htn hEven)
      (bound.weightBoundNonneg n htn hEven)
  rightTermBoundNonneg := by
    intro n htn hEven
    exact mul_nonneg (bound.weightBoundNonneg n htn hEven)
      (bound.weightBoundNonneg n htn hEven)
  leftPointwiseBound := by
    intro n htn hEven p hp
    simp only [Finset.mem_filter] at hp
    have hp_bound :=
      bound.weightBoundOnPrimePowersUpTo n htn hEven p hp.1 hp.2.1
    have hq_range : n - p ∈ Finset.range n.succ := by
      simp [Nat.lt_succ_of_le (Nat.sub_le n p)]
    have hq_bound :=
      bound.weightBoundOnPrimePowersUpTo n htn hEven (n - p)
        hq_range hp.2.2.2
    exact vonMangoldtProduct_le_sq_of_le
      (bound.weightBoundNonneg n htn hEven) hp_bound hq_bound
  rightPointwiseBound := by
    intro n htn hEven p hp
    simp only [Finset.mem_filter] at hp
    have hp_bound :=
      bound.weightBoundOnPrimePowersUpTo n htn hEven p hp.1 hp.2.1
    have hq_range : n - p ∈ Finset.range n.succ := by
      simp [Nat.lt_succ_of_le (Nat.sub_le n p)]
    have hq_bound :=
      bound.weightBoundOnPrimePowersUpTo n htn hEven (n - p)
        hq_range hp.2.2.1
    exact vonMangoldtProduct_le_sq_of_le
      (bound.weightBoundNonneg n htn hEven) hp_bound hq_bound
  leftProductBound := by
    intro n htn hEven
    exact bound.leftProductBound n htn hEven
  rightProductBound := by
    intro n htn hEven
    exact bound.rightProductBound n htn hEven
  totalErrorDominated := by
    intro n htn hEven
    exact bound.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_weight_bound_split_contamination_lower_bound
    (bound : VonMangoldtWeightBoundSplitContaminationLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_vonMangoldt_trivial_count_split_contamination_lower_bound
    bound.toTrivialCountLowerBound

theorem strongGoldbach_of_vonMangoldt_weight_bound_split_contamination_lower_bound_le100
    (bound : VonMangoldtWeightBoundSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_trivial_count_split_contamination_lower_bound_le100
    bound.toTrivialCountLowerBound
    (by
      simpa
        [VonMangoldtWeightBoundSplitContaminationLowerBound.toTrivialCountLowerBound]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_weight_bound_split_contamination_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtWeightBoundSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_trivial_count_split_contamination_lower_bound_le
    finite
    bound.toTrivialCountLowerBound
    (by
      simpa
        [VonMangoldtWeightBoundSplitContaminationLowerBound.toTrivialCountLowerBound]
        using hthreshold)

structure VonMangoldtWeightBoundSplitContaminationMajorMinorArcEstimate where
  threshold : Nat
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  weightBound : Nat → ℝ
  leftContamination : Nat → ℝ
  rightContamination : Nat → ℝ
  combinedLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  weightBoundNonneg :
    ∀ n : Nat, threshold < n → Even n → 0 ≤ weightBound n
  weightBoundOnPrimePowersUpTo :
    ∀ n : Nat, threshold < n → Even n →
      ∀ m ∈ Finset.range n.succ, IsPrimePow m →
        vonMangoldtWeight m ≤ weightBound n
  leftProductBound :
    ∀ n : Nat, threshold < n → Even n →
      (n.succ : ℝ) * (weightBound n * weightBound n) ≤
        leftContamination n
  rightProductBound :
    ∀ n : Nat, threshold < n → Even n →
      (n.succ : ℝ) * (weightBound n * weightBound n) ≤
        rightContamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n + leftContamination n +
          rightContamination n <
        mainTerm n

noncomputable def VonMangoldtWeightBoundSplitContaminationMajorMinorArcEstimate.toTrivialCountEstimate
    (estimate : VonMangoldtWeightBoundSplitContaminationMajorMinorArcEstimate) :
    VonMangoldtTrivialCountSplitContaminationMajorMinorArcEstimate where
  threshold := estimate.threshold
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  leftTermBound := fun n => estimate.weightBound n * estimate.weightBound n
  rightTermBound := fun n => estimate.weightBound n * estimate.weightBound n
  leftContamination := estimate.leftContamination
  rightContamination := estimate.rightContamination
  combinedLowerBound := by
    intro n htn hEven
    exact estimate.combinedLowerBound n htn hEven
  leftTermBoundNonneg := by
    intro n htn hEven
    exact mul_nonneg (estimate.weightBoundNonneg n htn hEven)
      (estimate.weightBoundNonneg n htn hEven)
  rightTermBoundNonneg := by
    intro n htn hEven
    exact mul_nonneg (estimate.weightBoundNonneg n htn hEven)
      (estimate.weightBoundNonneg n htn hEven)
  leftPointwiseBound := by
    intro n htn hEven p hp
    simp only [Finset.mem_filter] at hp
    have hp_bound :=
      estimate.weightBoundOnPrimePowersUpTo n htn hEven p hp.1 hp.2.1
    have hq_range : n - p ∈ Finset.range n.succ := by
      simp [Nat.lt_succ_of_le (Nat.sub_le n p)]
    have hq_bound :=
      estimate.weightBoundOnPrimePowersUpTo n htn hEven (n - p)
        hq_range hp.2.2.2
    exact vonMangoldtProduct_le_sq_of_le
      (estimate.weightBoundNonneg n htn hEven) hp_bound hq_bound
  rightPointwiseBound := by
    intro n htn hEven p hp
    simp only [Finset.mem_filter] at hp
    have hp_bound :=
      estimate.weightBoundOnPrimePowersUpTo n htn hEven p hp.1 hp.2.1
    have hq_range : n - p ∈ Finset.range n.succ := by
      simp [Nat.lt_succ_of_le (Nat.sub_le n p)]
    have hq_bound :=
      estimate.weightBoundOnPrimePowersUpTo n htn hEven (n - p)
        hq_range hp.2.2.1
    exact vonMangoldtProduct_le_sq_of_le
      (estimate.weightBoundNonneg n htn hEven) hp_bound hq_bound
  leftProductBound := by
    intro n htn hEven
    exact estimate.leftProductBound n htn hEven
  rightProductBound := by
    intro n htn hEven
    exact estimate.rightProductBound n htn hEven
  totalErrorDominated := by
    intro n htn hEven
    exact estimate.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_weight_bound_split_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtWeightBoundSplitContaminationMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove estimate.threshold :=
  count_positive_above_of_vonMangoldt_trivial_count_split_contamination_major_minor_arc_estimate
    estimate.toTrivialCountEstimate

theorem strongGoldbach_of_vonMangoldt_weight_bound_split_contamination_major_minor_arc_estimate_le100
    (estimate : VonMangoldtWeightBoundSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_trivial_count_split_contamination_major_minor_arc_estimate_le100
    estimate.toTrivialCountEstimate
    (by
      simpa
        [VonMangoldtWeightBoundSplitContaminationMajorMinorArcEstimate.toTrivialCountEstimate]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_weight_bound_split_contamination_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtWeightBoundSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_trivial_count_split_contamination_major_minor_arc_estimate_le
    finite
    estimate.toTrivialCountEstimate
    (by
      simpa
        [VonMangoldtWeightBoundSplitContaminationMajorMinorArcEstimate.toTrivialCountEstimate]
        using hthreshold)

structure VonMangoldtLogWeightSplitContaminationLowerBound where
  threshold : Nat
  mainTerm : Nat → ℝ
  analyticError : Nat → ℝ
  leftContamination : Nat → ℝ
  rightContamination : Nat → ℝ
  lowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - analyticError n ≤ RawVonMangoldtGoldbachSum n
  leftProductBound :
    ∀ n : Nat, threshold < n → Even n →
      (n.succ : ℝ) * (Real.log (n : ℝ) * Real.log (n : ℝ)) ≤
        leftContamination n
  rightProductBound :
    ∀ n : Nat, threshold < n → Even n →
      (n.succ : ℝ) * (Real.log (n : ℝ) * Real.log (n : ℝ)) ≤
        rightContamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      analyticError n + leftContamination n + rightContamination n <
        mainTerm n

noncomputable def VonMangoldtLogWeightSplitContaminationLowerBound.toWeightBoundLowerBound
    (bound : VonMangoldtLogWeightSplitContaminationLowerBound) :
    VonMangoldtWeightBoundSplitContaminationLowerBound where
  threshold := bound.threshold
  mainTerm := bound.mainTerm
  analyticError := bound.analyticError
  weightBound := fun n => Real.log (n : ℝ)
  leftContamination := bound.leftContamination
  rightContamination := bound.rightContamination
  lowerBound := by
    intro n htn hEven
    exact bound.lowerBound n htn hEven
  weightBoundNonneg := by
    intro n htn hEven
    exact Real.log_natCast_nonneg n
  weightBoundOnPrimePowersUpTo := by
    intro n htn hEven m hm_range hm_prime_power
    exact vonMangoldtWeight_le_log_of_mem_range hm_range hm_prime_power
  leftProductBound := by
    intro n htn hEven
    exact bound.leftProductBound n htn hEven
  rightProductBound := by
    intro n htn hEven
    exact bound.rightProductBound n htn hEven
  totalErrorDominated := by
    intro n htn hEven
    exact bound.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_log_weight_split_contamination_lower_bound
    (bound : VonMangoldtLogWeightSplitContaminationLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_vonMangoldt_weight_bound_split_contamination_lower_bound
    bound.toWeightBoundLowerBound

theorem strongGoldbach_of_vonMangoldt_log_weight_split_contamination_lower_bound_le100
    (bound : VonMangoldtLogWeightSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_weight_bound_split_contamination_lower_bound_le100
    bound.toWeightBoundLowerBound
    (by
      simpa
        [VonMangoldtLogWeightSplitContaminationLowerBound.toWeightBoundLowerBound]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_log_weight_split_contamination_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtLogWeightSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_weight_bound_split_contamination_lower_bound_le
    finite
    bound.toWeightBoundLowerBound
    (by
      simpa
        [VonMangoldtLogWeightSplitContaminationLowerBound.toWeightBoundLowerBound]
        using hthreshold)

structure VonMangoldtLogWeightSplitContaminationMajorMinorArcEstimate where
  threshold : Nat
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  leftContamination : Nat → ℝ
  rightContamination : Nat → ℝ
  combinedLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  leftProductBound :
    ∀ n : Nat, threshold < n → Even n →
      (n.succ : ℝ) * (Real.log (n : ℝ) * Real.log (n : ℝ)) ≤
        leftContamination n
  rightProductBound :
    ∀ n : Nat, threshold < n → Even n →
      (n.succ : ℝ) * (Real.log (n : ℝ) * Real.log (n : ℝ)) ≤
        rightContamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n + leftContamination n +
          rightContamination n <
        mainTerm n

noncomputable def VonMangoldtLogWeightSplitContaminationMajorMinorArcEstimate.toWeightBoundEstimate
    (estimate : VonMangoldtLogWeightSplitContaminationMajorMinorArcEstimate) :
    VonMangoldtWeightBoundSplitContaminationMajorMinorArcEstimate where
  threshold := estimate.threshold
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  weightBound := fun n => Real.log (n : ℝ)
  leftContamination := estimate.leftContamination
  rightContamination := estimate.rightContamination
  combinedLowerBound := by
    intro n htn hEven
    exact estimate.combinedLowerBound n htn hEven
  weightBoundNonneg := by
    intro n htn hEven
    exact Real.log_natCast_nonneg n
  weightBoundOnPrimePowersUpTo := by
    intro n htn hEven m hm_range hm_prime_power
    exact vonMangoldtWeight_le_log_of_mem_range hm_range hm_prime_power
  leftProductBound := by
    intro n htn hEven
    exact estimate.leftProductBound n htn hEven
  rightProductBound := by
    intro n htn hEven
    exact estimate.rightProductBound n htn hEven
  totalErrorDominated := by
    intro n htn hEven
    exact estimate.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_log_weight_split_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtLogWeightSplitContaminationMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove estimate.threshold :=
  count_positive_above_of_vonMangoldt_weight_bound_split_contamination_major_minor_arc_estimate
    estimate.toWeightBoundEstimate

theorem strongGoldbach_of_vonMangoldt_log_weight_split_contamination_major_minor_arc_estimate_le100
    (estimate : VonMangoldtLogWeightSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_weight_bound_split_contamination_major_minor_arc_estimate_le100
    estimate.toWeightBoundEstimate
    (by
      simpa
        [VonMangoldtLogWeightSplitContaminationMajorMinorArcEstimate.toWeightBoundEstimate]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_log_weight_split_contamination_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtLogWeightSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_weight_bound_split_contamination_major_minor_arc_estimate_le
    finite
    estimate.toWeightBoundEstimate
    (by
      simpa
        [VonMangoldtLogWeightSplitContaminationMajorMinorArcEstimate.toWeightBoundEstimate]
        using hthreshold)

noncomputable def vonMangoldtLogCountContaminationBudget
    (countBound : Nat → ℝ) (n : Nat) : ℝ :=
  countBound n * (Real.log (n : ℝ) * Real.log (n : ℝ))

structure VonMangoldtCountBoundLogWeightSplitContaminationLowerBound where
  threshold : Nat
  mainTerm : Nat → ℝ
  analyticError : Nat → ℝ
  nonPrimePrimePowerCountBound : Nat → ℝ
  leftContamination : Nat → ℝ
  rightContamination : Nat → ℝ
  lowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - analyticError n ≤ RawVonMangoldtGoldbachSum n
  nonPrimePrimePowerCountBoundValid :
    ∀ n : Nat, threshold < n → Even n →
      (NonPrimePrimePowerCount n : ℝ) ≤ nonPrimePrimePowerCountBound n
  leftProductBound :
    ∀ n : Nat, threshold < n → Even n →
      nonPrimePrimePowerCountBound n *
          (Real.log (n : ℝ) * Real.log (n : ℝ)) ≤
        leftContamination n
  rightProductBound :
    ∀ n : Nat, threshold < n → Even n →
      nonPrimePrimePowerCountBound n *
          (Real.log (n : ℝ) * Real.log (n : ℝ)) ≤
        rightContamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      analyticError n + leftContamination n + rightContamination n <
        mainTerm n

noncomputable def VonMangoldtCountBoundLogWeightSplitContaminationLowerBound.toCountedLowerBound
    (bound : VonMangoldtCountBoundLogWeightSplitContaminationLowerBound) :
    VonMangoldtCountedSplitContaminationLowerBound where
  threshold := bound.threshold
  mainTerm := bound.mainTerm
  analyticError := bound.analyticError
  leftTermBound := fun n => Real.log (n : ℝ) * Real.log (n : ℝ)
  rightTermBound := fun n => Real.log (n : ℝ) * Real.log (n : ℝ)
  nonPrimePrimePowerCountBound := bound.nonPrimePrimePowerCountBound
  leftContamination := bound.leftContamination
  rightContamination := bound.rightContamination
  lowerBound := by
    intro n htn hEven
    exact bound.lowerBound n htn hEven
  leftTermBoundNonneg := by
    intro n htn hEven
    exact mul_nonneg (Real.log_natCast_nonneg n) (Real.log_natCast_nonneg n)
  rightTermBoundNonneg := by
    intro n htn hEven
    exact mul_nonneg (Real.log_natCast_nonneg n) (Real.log_natCast_nonneg n)
  leftPointwiseBound := by
    intro n htn hEven p hp
    simp only [Finset.mem_filter] at hp
    have hp_bound :=
      vonMangoldtWeight_le_log_of_mem_range hp.1 hp.2.1
    have hq_range : n - p ∈ Finset.range n.succ := by
      simp [Nat.lt_succ_of_le (Nat.sub_le n p)]
    have hq_bound :=
      vonMangoldtWeight_le_log_of_mem_range hq_range hp.2.2.2
    exact vonMangoldtProduct_le_sq_of_le
      (Real.log_natCast_nonneg n) hp_bound hq_bound
  rightPointwiseBound := by
    intro n htn hEven p hp
    simp only [Finset.mem_filter] at hp
    have hp_bound :=
      vonMangoldtWeight_le_log_of_mem_range hp.1 hp.2.1
    have hq_range : n - p ∈ Finset.range n.succ := by
      simp [Nat.lt_succ_of_le (Nat.sub_le n p)]
    have hq_bound :=
      vonMangoldtWeight_le_log_of_mem_range hq_range hp.2.2.1
    exact vonMangoldtProduct_le_sq_of_le
      (Real.log_natCast_nonneg n) hp_bound hq_bound
  nonPrimePrimePowerCountBoundValid := by
    intro n htn hEven
    exact bound.nonPrimePrimePowerCountBoundValid n htn hEven
  leftProductBound := by
    intro n htn hEven
    exact bound.leftProductBound n htn hEven
  rightProductBound := by
    intro n htn hEven
    exact bound.rightProductBound n htn hEven
  totalErrorDominated := by
    intro n htn hEven
    exact bound.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_count_bound_log_weight_split_contamination_lower_bound
    (bound : VonMangoldtCountBoundLogWeightSplitContaminationLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_vonMangoldt_counted_split_contamination_lower_bound
    bound.toCountedLowerBound

theorem strongGoldbach_of_vonMangoldt_count_bound_log_weight_split_contamination_lower_bound_le100
    (bound : VonMangoldtCountBoundLogWeightSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_counted_split_contamination_lower_bound_le100
    bound.toCountedLowerBound
    (by
      simpa
        [VonMangoldtCountBoundLogWeightSplitContaminationLowerBound.toCountedLowerBound]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_count_bound_log_weight_split_contamination_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtCountBoundLogWeightSplitContaminationLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_counted_split_contamination_lower_bound_le
    finite
    bound.toCountedLowerBound
    (by
      simpa
        [VonMangoldtCountBoundLogWeightSplitContaminationLowerBound.toCountedLowerBound]
        using hthreshold)

structure VonMangoldtCountBoundLogWeightSplitContaminationMajorMinorArcEstimate where
  threshold : Nat
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  nonPrimePrimePowerCountBound : Nat → ℝ
  leftContamination : Nat → ℝ
  rightContamination : Nat → ℝ
  combinedLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  nonPrimePrimePowerCountBoundValid :
    ∀ n : Nat, threshold < n → Even n →
      (NonPrimePrimePowerCount n : ℝ) ≤ nonPrimePrimePowerCountBound n
  leftProductBound :
    ∀ n : Nat, threshold < n → Even n →
      nonPrimePrimePowerCountBound n *
          (Real.log (n : ℝ) * Real.log (n : ℝ)) ≤
        leftContamination n
  rightProductBound :
    ∀ n : Nat, threshold < n → Even n →
      nonPrimePrimePowerCountBound n *
          (Real.log (n : ℝ) * Real.log (n : ℝ)) ≤
        rightContamination n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n + leftContamination n +
          rightContamination n <
        mainTerm n

noncomputable def VonMangoldtCountBoundLogWeightSplitContaminationMajorMinorArcEstimate.toCountedEstimate
    (estimate : VonMangoldtCountBoundLogWeightSplitContaminationMajorMinorArcEstimate) :
    VonMangoldtCountedSplitContaminationMajorMinorArcEstimate where
  threshold := estimate.threshold
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  leftTermBound := fun n => Real.log (n : ℝ) * Real.log (n : ℝ)
  rightTermBound := fun n => Real.log (n : ℝ) * Real.log (n : ℝ)
  nonPrimePrimePowerCountBound := estimate.nonPrimePrimePowerCountBound
  leftContamination := estimate.leftContamination
  rightContamination := estimate.rightContamination
  combinedLowerBound := by
    intro n htn hEven
    exact estimate.combinedLowerBound n htn hEven
  leftTermBoundNonneg := by
    intro n htn hEven
    exact mul_nonneg (Real.log_natCast_nonneg n) (Real.log_natCast_nonneg n)
  rightTermBoundNonneg := by
    intro n htn hEven
    exact mul_nonneg (Real.log_natCast_nonneg n) (Real.log_natCast_nonneg n)
  leftPointwiseBound := by
    intro n htn hEven p hp
    simp only [Finset.mem_filter] at hp
    have hp_bound :=
      vonMangoldtWeight_le_log_of_mem_range hp.1 hp.2.1
    have hq_range : n - p ∈ Finset.range n.succ := by
      simp [Nat.lt_succ_of_le (Nat.sub_le n p)]
    have hq_bound :=
      vonMangoldtWeight_le_log_of_mem_range hq_range hp.2.2.2
    exact vonMangoldtProduct_le_sq_of_le
      (Real.log_natCast_nonneg n) hp_bound hq_bound
  rightPointwiseBound := by
    intro n htn hEven p hp
    simp only [Finset.mem_filter] at hp
    have hp_bound :=
      vonMangoldtWeight_le_log_of_mem_range hp.1 hp.2.1
    have hq_range : n - p ∈ Finset.range n.succ := by
      simp [Nat.lt_succ_of_le (Nat.sub_le n p)]
    have hq_bound :=
      vonMangoldtWeight_le_log_of_mem_range hq_range hp.2.2.1
    exact vonMangoldtProduct_le_sq_of_le
      (Real.log_natCast_nonneg n) hp_bound hq_bound
  nonPrimePrimePowerCountBoundValid := by
    intro n htn hEven
    exact estimate.nonPrimePrimePowerCountBoundValid n htn hEven
  leftProductBound := by
    intro n htn hEven
    exact estimate.leftProductBound n htn hEven
  rightProductBound := by
    intro n htn hEven
    exact estimate.rightProductBound n htn hEven
  totalErrorDominated := by
    intro n htn hEven
    exact estimate.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_count_bound_log_weight_split_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtCountBoundLogWeightSplitContaminationMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove estimate.threshold :=
  count_positive_above_of_vonMangoldt_counted_split_contamination_major_minor_arc_estimate
    estimate.toCountedEstimate

theorem strongGoldbach_of_vonMangoldt_count_bound_log_weight_split_contamination_major_minor_arc_estimate_le100
    (estimate : VonMangoldtCountBoundLogWeightSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_counted_split_contamination_major_minor_arc_estimate_le100
    estimate.toCountedEstimate
    (by
      simpa
        [VonMangoldtCountBoundLogWeightSplitContaminationMajorMinorArcEstimate.toCountedEstimate]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_count_bound_log_weight_split_contamination_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtCountBoundLogWeightSplitContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_counted_split_contamination_major_minor_arc_estimate_le
    finite
    estimate.toCountedEstimate
    (by
      simpa
        [VonMangoldtCountBoundLogWeightSplitContaminationMajorMinorArcEstimate.toCountedEstimate]
        using hthreshold)

structure VonMangoldtCanonicalLogCountContaminationLowerBound where
  threshold : Nat
  mainTerm : Nat → ℝ
  analyticError : Nat → ℝ
  nonPrimePrimePowerCountBound : Nat → ℝ
  lowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - analyticError n ≤ RawVonMangoldtGoldbachSum n
  nonPrimePrimePowerCountBoundValid :
    ∀ n : Nat, threshold < n → Even n →
      (NonPrimePrimePowerCount n : ℝ) ≤ nonPrimePrimePowerCountBound n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      analyticError n +
          2 * vonMangoldtLogCountContaminationBudget
            nonPrimePrimePowerCountBound n <
        mainTerm n

noncomputable def VonMangoldtCanonicalLogCountContaminationLowerBound.toCountBoundLogWeightLowerBound
    (bound : VonMangoldtCanonicalLogCountContaminationLowerBound) :
    VonMangoldtCountBoundLogWeightSplitContaminationLowerBound where
  threshold := bound.threshold
  mainTerm := bound.mainTerm
  analyticError := bound.analyticError
  nonPrimePrimePowerCountBound := bound.nonPrimePrimePowerCountBound
  leftContamination :=
    vonMangoldtLogCountContaminationBudget bound.nonPrimePrimePowerCountBound
  rightContamination :=
    vonMangoldtLogCountContaminationBudget bound.nonPrimePrimePowerCountBound
  lowerBound := by
    intro n htn hEven
    exact bound.lowerBound n htn hEven
  nonPrimePrimePowerCountBoundValid := by
    intro n htn hEven
    exact bound.nonPrimePrimePowerCountBoundValid n htn hEven
  leftProductBound := by
    intro n htn hEven
    simp [vonMangoldtLogCountContaminationBudget]
  rightProductBound := by
    intro n htn hEven
    simp [vonMangoldtLogCountContaminationBudget]
  totalErrorDominated := by
    intro n htn hEven
    simpa [vonMangoldtLogCountContaminationBudget, two_mul, add_assoc] using
      bound.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_canonical_log_count_contamination_lower_bound
    (bound : VonMangoldtCanonicalLogCountContaminationLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_vonMangoldt_count_bound_log_weight_split_contamination_lower_bound
    bound.toCountBoundLogWeightLowerBound

theorem strongGoldbach_of_vonMangoldt_canonical_log_count_contamination_lower_bound_le100
    (bound : VonMangoldtCanonicalLogCountContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_count_bound_log_weight_split_contamination_lower_bound_le100
    bound.toCountBoundLogWeightLowerBound
    (by
      simpa
        [VonMangoldtCanonicalLogCountContaminationLowerBound.toCountBoundLogWeightLowerBound]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_canonical_log_count_contamination_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtCanonicalLogCountContaminationLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_count_bound_log_weight_split_contamination_lower_bound_le
    finite
    bound.toCountBoundLogWeightLowerBound
    (by
      simpa
        [VonMangoldtCanonicalLogCountContaminationLowerBound.toCountBoundLogWeightLowerBound]
        using hthreshold)

structure VonMangoldtCanonicalLogCountContaminationMajorMinorArcEstimate where
  threshold : Nat
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  nonPrimePrimePowerCountBound : Nat → ℝ
  combinedLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  nonPrimePrimePowerCountBoundValid :
    ∀ n : Nat, threshold < n → Even n →
      (NonPrimePrimePowerCount n : ℝ) ≤ nonPrimePrimePowerCountBound n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n +
          2 * vonMangoldtLogCountContaminationBudget
            nonPrimePrimePowerCountBound n <
        mainTerm n

noncomputable def VonMangoldtCanonicalLogCountContaminationMajorMinorArcEstimate.toCountBoundLogWeightEstimate
    (estimate : VonMangoldtCanonicalLogCountContaminationMajorMinorArcEstimate) :
    VonMangoldtCountBoundLogWeightSplitContaminationMajorMinorArcEstimate where
  threshold := estimate.threshold
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  nonPrimePrimePowerCountBound := estimate.nonPrimePrimePowerCountBound
  leftContamination :=
    vonMangoldtLogCountContaminationBudget estimate.nonPrimePrimePowerCountBound
  rightContamination :=
    vonMangoldtLogCountContaminationBudget estimate.nonPrimePrimePowerCountBound
  combinedLowerBound := by
    intro n htn hEven
    exact estimate.combinedLowerBound n htn hEven
  nonPrimePrimePowerCountBoundValid := by
    intro n htn hEven
    exact estimate.nonPrimePrimePowerCountBoundValid n htn hEven
  leftProductBound := by
    intro n htn hEven
    simp [vonMangoldtLogCountContaminationBudget]
  rightProductBound := by
    intro n htn hEven
    simp [vonMangoldtLogCountContaminationBudget]
  totalErrorDominated := by
    intro n htn hEven
    simpa [vonMangoldtLogCountContaminationBudget, two_mul, add_assoc] using
      estimate.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_canonical_log_count_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtCanonicalLogCountContaminationMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove estimate.threshold :=
  count_positive_above_of_vonMangoldt_count_bound_log_weight_split_contamination_major_minor_arc_estimate
    estimate.toCountBoundLogWeightEstimate

theorem strongGoldbach_of_vonMangoldt_canonical_log_count_contamination_major_minor_arc_estimate_le100
    (estimate : VonMangoldtCanonicalLogCountContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_count_bound_log_weight_split_contamination_major_minor_arc_estimate_le100
    estimate.toCountBoundLogWeightEstimate
    (by
      simpa
        [VonMangoldtCanonicalLogCountContaminationMajorMinorArcEstimate.toCountBoundLogWeightEstimate]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_canonical_log_count_contamination_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtCanonicalLogCountContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_count_bound_log_weight_split_contamination_major_minor_arc_estimate_le
    finite
    estimate.toCountBoundLogWeightEstimate
    (by
      simpa
        [VonMangoldtCanonicalLogCountContaminationMajorMinorArcEstimate.toCountBoundLogWeightEstimate]
        using hthreshold)

structure VonMangoldtDirectRawLogCountLowerBound where
  threshold : Nat
  nonPrimePrimePowerCountBound : Nat → ℝ
  nonPrimePrimePowerCountBoundValid :
    ∀ n : Nat, threshold < n → Even n →
      (NonPrimePrimePowerCount n : ℝ) ≤ nonPrimePrimePowerCountBound n
  rawLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      2 * vonMangoldtLogCountContaminationBudget
        nonPrimePrimePowerCountBound n <
        RawVonMangoldtGoldbachSum n

noncomputable def VonMangoldtDirectRawLogCountLowerBound.toCanonicalLogCountContaminationLowerBound
    (bound : VonMangoldtDirectRawLogCountLowerBound) :
    VonMangoldtCanonicalLogCountContaminationLowerBound where
  threshold := bound.threshold
  mainTerm := RawVonMangoldtGoldbachSum
  analyticError := fun _ => 0
  nonPrimePrimePowerCountBound := bound.nonPrimePrimePowerCountBound
  lowerBound := by
    intro n htn hEven
    simp
  nonPrimePrimePowerCountBoundValid := by
    intro n htn hEven
    exact bound.nonPrimePrimePowerCountBoundValid n htn hEven
  totalErrorDominated := by
    intro n htn hEven
    simpa using bound.rawLowerBound n htn hEven

theorem count_positive_above_of_vonMangoldt_direct_raw_log_count_lower_bound
    (bound : VonMangoldtDirectRawLogCountLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_vonMangoldt_canonical_log_count_contamination_lower_bound
    bound.toCanonicalLogCountContaminationLowerBound

theorem strongGoldbach_of_vonMangoldt_direct_raw_log_count_lower_bound_le100
    (bound : VonMangoldtDirectRawLogCountLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_canonical_log_count_contamination_lower_bound_le100
    bound.toCanonicalLogCountContaminationLowerBound
    (by
      simpa
        [VonMangoldtDirectRawLogCountLowerBound.toCanonicalLogCountContaminationLowerBound]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_direct_raw_log_count_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtDirectRawLogCountLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_canonical_log_count_contamination_lower_bound_le
    finite
    bound.toCanonicalLogCountContaminationLowerBound
    (by
      simpa
        [VonMangoldtDirectRawLogCountLowerBound.toCanonicalLogCountContaminationLowerBound]
        using hthreshold)

noncomputable def NonPrimePrimePowerVonMangoldtWeightSum (n : Nat) : ℝ :=
  ((Finset.range n.succ).filter
    (fun p => IsPrimePow p ∧ ¬ Nat.Prime p)).sum vonMangoldtWeight

theorem nonPrimePrimePowerVonMangoldtWeightSum_le_count_mul_log
    (n : Nat) :
    NonPrimePrimePowerVonMangoldtWeightSum n ≤
      (NonPrimePrimePowerCount n : ℝ) * Real.log (n : ℝ) := by
  classical
  let badSet :=
    (Finset.range n.succ).filter
      (fun p => IsPrimePow p ∧ ¬ Nat.Prime p)
  have hpoint :
      ∀ p ∈ badSet, vonMangoldtWeight p ≤ Real.log (n : ℝ) := by
    intro p hp
    have hp' : p ∈ badSet := hp
    simp only [badSet, Finset.mem_filter] at hp'
    exact vonMangoldtWeight_le_log_of_mem_range hp'.1 hp'.2.1
  have hsum :
      badSet.sum vonMangoldtWeight ≤
        (badSet.card : ℝ) * Real.log (n : ℝ) :=
    realFinsetSum_le_card_mul_of_pointwise_bound
      (s := badSet)
      (f := vonMangoldtWeight)
      (C := Real.log (n : ℝ))
      hpoint
  simpa [NonPrimePrimePowerVonMangoldtWeightSum, NonPrimePrimePowerCount,
    badSet] using hsum

theorem leftPrimePowerContaminationVonMangoldtGoldbachSum_le_weightSum_mul_log
    (n : Nat) (hn1 : 1 ≤ n) :
    LeftPrimePowerContaminationVonMangoldtGoldbachSum n ≤
      NonPrimePrimePowerVonMangoldtWeightSum n * Real.log (n : ℝ) := by
  classical
  let leftSet :=
    (Finset.range n.succ).filter
      (fun p => IsPrimePow p ∧ ¬ Nat.Prime p ∧ IsPrimePow (n - p))
  let badSet :=
    (Finset.range n.succ).filter
      (fun p => IsPrimePow p ∧ ¬ Nat.Prime p)
  have hpoint :
      ∀ p ∈ leftSet,
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤
          vonMangoldtWeight p * Real.log (n : ℝ) := by
    intro p hp
    have hp' : p ∈ leftSet := hp
    simp only [leftSet, Finset.mem_filter] at hp'
    have hnmp_range : n - p ∈ Finset.range n.succ := by
      simp [Nat.lt_succ_of_le (Nat.sub_le n p)]
    have hqlog := vonMangoldtWeight_le_log_of_mem_range
      (m := n - p) (n := n) hnmp_range hp'.2.2.2
    exact mul_le_mul_of_nonneg_left hqlog (vonMangoldtWeight_nonneg p)
  have hsum_left :
      LeftPrimePowerContaminationVonMangoldtGoldbachSum n ≤
        leftSet.sum (fun p => vonMangoldtWeight p * Real.log (n : ℝ)) := by
    simpa [LeftPrimePowerContaminationVonMangoldtGoldbachSum, leftSet] using
      Finset.sum_le_sum hpoint
  have hsubset : leftSet ⊆ badSet := by
    intro p hp
    simp only [leftSet, badSet, Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hn1)
  have hnonneg :
      ∀ x ∈ badSet, x ∉ leftSet →
        0 ≤ vonMangoldtWeight x * Real.log (n : ℝ) := by
    intro x hx hnot
    exact mul_nonneg (vonMangoldtWeight_nonneg x) hlog_nonneg
  have hsubset_sum :
      leftSet.sum (fun p => vonMangoldtWeight p * Real.log (n : ℝ)) ≤
        badSet.sum (fun p => vonMangoldtWeight p * Real.log (n : ℝ)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  have hsum_eq :
      badSet.sum (fun p => vonMangoldtWeight p * Real.log (n : ℝ)) =
        NonPrimePrimePowerVonMangoldtWeightSum n * Real.log (n : ℝ) := by
    simp [NonPrimePrimePowerVonMangoldtWeightSum, badSet, Finset.sum_mul]
  exact hsum_left.trans (hsubset_sum.trans_eq hsum_eq)

theorem rightPrimePowerContaminationVonMangoldtGoldbachSum_le_weightSum_mul_log
    (n : Nat) (hn1 : 1 ≤ n) :
    RightPrimePowerContaminationVonMangoldtGoldbachSum n ≤
      NonPrimePrimePowerVonMangoldtWeightSum n * Real.log (n : ℝ) := by
  classical
  let rightSet :=
    (Finset.range n.succ).filter
      (fun p => IsPrimePow p ∧ IsPrimePow (n - p) ∧
        ¬ Nat.Prime (n - p))
  let badSet :=
    (Finset.range n.succ).filter
      (fun q => IsPrimePow q ∧ ¬ Nat.Prime q)
  have hpoint :
      ∀ p ∈ rightSet,
        vonMangoldtWeight p * vonMangoldtWeight (n - p) ≤
          Real.log (n : ℝ) * vonMangoldtWeight (n - p) := by
    intro p hp
    have hp' : p ∈ rightSet := hp
    simp only [rightSet, Finset.mem_filter] at hp'
    have hplog := vonMangoldtWeight_le_log_of_mem_range
      (m := p) (n := n) hp'.1 hp'.2.1
    exact mul_le_mul_of_nonneg_right hplog (vonMangoldtWeight_nonneg (n - p))
  have hsum_right :
      RightPrimePowerContaminationVonMangoldtGoldbachSum n ≤
        rightSet.sum
          (fun p => Real.log (n : ℝ) * vonMangoldtWeight (n - p)) := by
    simpa [RightPrimePowerContaminationVonMangoldtGoldbachSum, rightSet] using
      Finset.sum_le_sum hpoint
  let imageSet := rightSet.image (fun p => n - p)
  have hmaps : imageSet ⊆ badSet := by
    intro q hq
    simp only [imageSet, badSet, Finset.mem_image, Finset.mem_filter] at hq ⊢
    rcases hq with ⟨p, hp, rfl⟩
    simp only [rightSet, Finset.mem_filter] at hp
    exact ⟨by simp [Nat.lt_succ_of_le (Nat.sub_le n p)], hp.2.2.1, hp.2.2.2⟩
  have hinj : Set.InjOn (fun p => n - p) rightSet := by
    intro p hp q hq heq
    change p ∈ rightSet at hp
    change q ∈ rightSet at hq
    simp only [rightSet, Finset.mem_filter] at hp hq
    have hp_lt : p < n.succ := by simpa using hp.1
    have hq_lt : q < n.succ := by simpa using hq.1
    have hp_le : p ≤ n := Nat.lt_succ_iff.mp hp_lt
    have hq_le : q ≤ n := Nat.lt_succ_iff.mp hq_lt
    have hsum : (n - p) + p = (n - q) + q := by
      rw [Nat.sub_add_cancel hp_le, Nat.sub_add_cancel hq_le]
    have hsum' : (n - q) + p = (n - q) + q := by
      simpa [heq] using hsum
    exact Nat.add_left_cancel hsum'
  have hsum_image :
      rightSet.sum (fun p => Real.log (n : ℝ) * vonMangoldtWeight (n - p)) =
        imageSet.sum (fun q => Real.log (n : ℝ) * vonMangoldtWeight q) := by
    simpa [imageSet] using
      (Finset.sum_image
        (s := rightSet)
        (g := fun p => n - p)
        (f := fun q => Real.log (n : ℝ) * vonMangoldtWeight q)
        (by
          intro a ha b hb hab
          exact hinj ha hb hab)).symm
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hn1)
  have hnonneg :
      ∀ x ∈ badSet, x ∉ imageSet →
        0 ≤ Real.log (n : ℝ) * vonMangoldtWeight x := by
    intro x hx hnot
    exact mul_nonneg hlog_nonneg (vonMangoldtWeight_nonneg x)
  have hsubset_sum :
      imageSet.sum (fun q => Real.log (n : ℝ) * vonMangoldtWeight q) ≤
        badSet.sum (fun q => Real.log (n : ℝ) * vonMangoldtWeight q) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hmaps hnonneg
  have hsum_eq :
      badSet.sum (fun q => Real.log (n : ℝ) * vonMangoldtWeight q) =
        NonPrimePrimePowerVonMangoldtWeightSum n * Real.log (n : ℝ) := by
    simp [NonPrimePrimePowerVonMangoldtWeightSum, badSet, Finset.mul_sum,
      mul_comm]
  exact hsum_right.trans (hsum_image.trans_le (hsubset_sum.trans_eq hsum_eq))

theorem primePowerContaminationVonMangoldtGoldbachSum_le_two_mul_weightSum_mul_log
    (n : Nat) (hn1 : 1 ≤ n) :
    PrimePowerContaminationVonMangoldtGoldbachSum n ≤
      2 * (NonPrimePrimePowerVonMangoldtWeightSum n * Real.log (n : ℝ)) := by
  have hsplit := primePowerContaminationVonMangoldtGoldbachSum_le_left_add_right n
  have hleft :=
    leftPrimePowerContaminationVonMangoldtGoldbachSum_le_weightSum_mul_log
      n hn1
  have hright :=
    rightPrimePowerContaminationVonMangoldtGoldbachSum_le_weightSum_mul_log
      n hn1
  linarith

noncomputable def vonMangoldtWeightSumContaminationBudget
    (weightSumBound : Nat → ℝ) (n : Nat) : ℝ :=
  weightSumBound n * Real.log (n : ℝ)

structure VonMangoldtDirectRawWeightSumLowerBound where
  threshold : Nat
  nonPrimePrimePowerWeightSumBound : Nat → ℝ
  nonPrimePrimePowerWeightSumBoundValid :
    ∀ n : Nat, threshold < n → Even n →
      NonPrimePrimePowerVonMangoldtWeightSum n ≤
        nonPrimePrimePowerWeightSumBound n
  rawLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        nonPrimePrimePowerWeightSumBound n <
        RawVonMangoldtGoldbachSum n

noncomputable def VonMangoldtDirectRawWeightSumLowerBound.toPrimePowerContaminationLowerBound
    (bound : VonMangoldtDirectRawWeightSumLowerBound) :
    VonMangoldtPrimePowerContaminationLowerBound where
  threshold := bound.threshold
  mainTerm := RawVonMangoldtGoldbachSum
  analyticError := fun _ => 0
  contamination :=
    fun n => 2 * vonMangoldtWeightSumContaminationBudget
      bound.nonPrimePrimePowerWeightSumBound n
  lowerBound := by
    intro n htn hEven
    simp
  primePowerContaminationBound := by
    intro n htn hEven
    have hn_pos : 0 < n := lt_of_le_of_lt (Nat.zero_le bound.threshold) htn
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn_pos
    have hcont :=
      primePowerContaminationVonMangoldtGoldbachSum_le_two_mul_weightSum_mul_log
        n hn1
    have hweight :=
      bound.nonPrimePrimePowerWeightSumBoundValid n htn hEven
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast hn1)
    have hbudget :
        NonPrimePrimePowerVonMangoldtWeightSum n * Real.log (n : ℝ) ≤
          bound.nonPrimePrimePowerWeightSumBound n * Real.log (n : ℝ) :=
      mul_le_mul_of_nonneg_right hweight hlog_nonneg
    dsimp [vonMangoldtWeightSumContaminationBudget]
    linarith
  totalErrorDominated := by
    intro n htn hEven
    simpa [vonMangoldtWeightSumContaminationBudget] using
      bound.rawLowerBound n htn hEven

theorem count_positive_above_of_vonMangoldt_direct_raw_weight_sum_lower_bound
    (bound : VonMangoldtDirectRawWeightSumLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_vonMangoldt_prime_power_contamination_lower_bound
    bound.toPrimePowerContaminationLowerBound

theorem strongGoldbach_of_vonMangoldt_direct_raw_weight_sum_lower_bound_le100
    (bound : VonMangoldtDirectRawWeightSumLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_prime_power_contamination_lower_bound_le100
    bound.toPrimePowerContaminationLowerBound
    (by
      simpa
        [VonMangoldtDirectRawWeightSumLowerBound.toPrimePowerContaminationLowerBound]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_direct_raw_weight_sum_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtDirectRawWeightSumLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_prime_power_contamination_lower_bound_le
    finite
    bound.toPrimePowerContaminationLowerBound
    (by
      simpa
        [VonMangoldtDirectRawWeightSumLowerBound.toPrimePowerContaminationLowerBound]
        using hthreshold)

structure VonMangoldtSplitThresholdDirectRawWeightSumLowerBound where
  weightSumThreshold : Nat
  rawThreshold : Nat
  nonPrimePrimePowerWeightSumBound : Nat → ℝ
  nonPrimePrimePowerWeightSumBoundValid :
    ∀ n : Nat, weightSumThreshold < n → Even n →
      NonPrimePrimePowerVonMangoldtWeightSum n ≤
        nonPrimePrimePowerWeightSumBound n
  rawLowerBound :
    ∀ n : Nat, rawThreshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        nonPrimePrimePowerWeightSumBound n <
        RawVonMangoldtGoldbachSum n

def VonMangoldtSplitThresholdDirectRawWeightSumLowerBound.threshold
    (bound : VonMangoldtSplitThresholdDirectRawWeightSumLowerBound) :
    Nat :=
  max bound.weightSumThreshold bound.rawThreshold

theorem VonMangoldtSplitThresholdDirectRawWeightSumLowerBound.weightSumThreshold_le_threshold
    (bound : VonMangoldtSplitThresholdDirectRawWeightSumLowerBound) :
    bound.weightSumThreshold ≤ bound.threshold := by
  dsimp [VonMangoldtSplitThresholdDirectRawWeightSumLowerBound.threshold]
  exact Nat.le_max_left _ _

theorem VonMangoldtSplitThresholdDirectRawWeightSumLowerBound.rawThreshold_le_threshold
    (bound : VonMangoldtSplitThresholdDirectRawWeightSumLowerBound) :
    bound.rawThreshold ≤ bound.threshold := by
  dsimp [VonMangoldtSplitThresholdDirectRawWeightSumLowerBound.threshold]
  exact Nat.le_max_right _ _

noncomputable def
    VonMangoldtSplitThresholdDirectRawWeightSumLowerBound.toDirectRawWeightSumLowerBound
    (bound : VonMangoldtSplitThresholdDirectRawWeightSumLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound where
  threshold := bound.threshold
  nonPrimePrimePowerWeightSumBound :=
    bound.nonPrimePrimePowerWeightSumBound
  nonPrimePrimePowerWeightSumBoundValid := by
    intro n htn hEven
    have hweight : bound.weightSumThreshold < n :=
      lt_of_le_of_lt bound.weightSumThreshold_le_threshold htn
    exact bound.nonPrimePrimePowerWeightSumBoundValid n hweight hEven
  rawLowerBound := by
    intro n htn hEven
    have hraw : bound.rawThreshold < n :=
      lt_of_le_of_lt bound.rawThreshold_le_threshold htn
    exact bound.rawLowerBound n hraw hEven

theorem count_positive_above_of_vonMangoldt_split_threshold_direct_raw_weight_sum_lower_bound
    (bound : VonMangoldtSplitThresholdDirectRawWeightSumLowerBound) :
    GoldbachCountPositiveAbove
      bound.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_direct_raw_weight_sum_lower_bound
    bound.toDirectRawWeightSumLowerBound

theorem strongGoldbach_of_vonMangoldt_split_threshold_direct_raw_weight_sum_lower_bound_le100
    (bound : VonMangoldtSplitThresholdDirectRawWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_direct_raw_weight_sum_lower_bound_le100
    bound.toDirectRawWeightSumLowerBound
    hthreshold

theorem strongGoldbach_of_finite_and_vonMangoldt_split_threshold_direct_raw_weight_sum_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtSplitThresholdDirectRawWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_direct_raw_weight_sum_lower_bound_le
    finite
    bound.toDirectRawWeightSumLowerBound
    hthreshold

structure VonMangoldtEventuallyDirectRawWeightSumLowerBound where
  nonPrimePrimePowerWeightSumBound : Nat → ℝ
  nonPrimePrimePowerWeightSumBoundValidEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      NonPrimePrimePowerVonMangoldtWeightSum n ≤
        nonPrimePrimePowerWeightSumBound n
  rawLowerBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        nonPrimePrimePowerWeightSumBound n <
        RawVonMangoldtGoldbachSum n

theorem vonMangoldtEventuallyDirectRawWeightSumLowerBound_conditions_eventually
    (bound : VonMangoldtEventuallyDirectRawWeightSumLowerBound) :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      (NonPrimePrimePowerVonMangoldtWeightSum n ≤
        bound.nonPrimePrimePowerWeightSumBound n) ∧
      (2 * vonMangoldtWeightSumContaminationBudget
        bound.nonPrimePrimePowerWeightSumBound n <
        RawVonMangoldtGoldbachSum n) := by
  filter_upwards
    [bound.nonPrimePrimePowerWeightSumBoundValidEventually,
      bound.rawLowerBoundEventually] with n hweight hraw
  intro hEven
  exact ⟨hweight hEven, hraw hEven⟩

noncomputable def vonMangoldtEventuallyDirectRawWeightSumLowerBoundThreshold
    (bound : VonMangoldtEventuallyDirectRawWeightSumLowerBound) : Nat :=
  Classical.choose
    (show ∃ N : Nat, ∀ n : Nat, N ≤ n → Even n →
        (NonPrimePrimePowerVonMangoldtWeightSum n ≤
          bound.nonPrimePrimePowerWeightSumBound n) ∧
        (2 * vonMangoldtWeightSumContaminationBudget
          bound.nonPrimePrimePowerWeightSumBound n <
          RawVonMangoldtGoldbachSum n) by
      simpa [Filter.eventually_atTop] using
        vonMangoldtEventuallyDirectRawWeightSumLowerBound_conditions_eventually
          bound)

theorem vonMangoldtEventuallyDirectRawWeightSumLowerBound_ge_threshold
    (bound : VonMangoldtEventuallyDirectRawWeightSumLowerBound) :
    ∀ n : Nat,
      vonMangoldtEventuallyDirectRawWeightSumLowerBoundThreshold bound ≤ n →
        Even n →
          (NonPrimePrimePowerVonMangoldtWeightSum n ≤
            bound.nonPrimePrimePowerWeightSumBound n) ∧
          (2 * vonMangoldtWeightSumContaminationBudget
            bound.nonPrimePrimePowerWeightSumBound n <
            RawVonMangoldtGoldbachSum n) :=
  Classical.choose_spec
    (show ∃ N : Nat, ∀ n : Nat, N ≤ n → Even n →
        (NonPrimePrimePowerVonMangoldtWeightSum n ≤
          bound.nonPrimePrimePowerWeightSumBound n) ∧
        (2 * vonMangoldtWeightSumContaminationBudget
          bound.nonPrimePrimePowerWeightSumBound n <
          RawVonMangoldtGoldbachSum n) by
      simpa [Filter.eventually_atTop] using
        vonMangoldtEventuallyDirectRawWeightSumLowerBound_conditions_eventually
          bound)

noncomputable def
    VonMangoldtEventuallyDirectRawWeightSumLowerBound.toDirectRawWeightSumLowerBound
    (bound : VonMangoldtEventuallyDirectRawWeightSumLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound where
  threshold := vonMangoldtEventuallyDirectRawWeightSumLowerBoundThreshold bound
  nonPrimePrimePowerWeightSumBound :=
    bound.nonPrimePrimePowerWeightSumBound
  nonPrimePrimePowerWeightSumBoundValid := by
    intro n htn hEven
    exact
      (vonMangoldtEventuallyDirectRawWeightSumLowerBound_ge_threshold
        bound n (le_of_lt htn) hEven).1
  rawLowerBound := by
    intro n htn hEven
    exact
      (vonMangoldtEventuallyDirectRawWeightSumLowerBound_ge_threshold
        bound n (le_of_lt htn) hEven).2

theorem count_positive_above_of_vonMangoldt_eventually_direct_raw_weight_sum_lower_bound
    (bound : VonMangoldtEventuallyDirectRawWeightSumLowerBound) :
    GoldbachCountPositiveAbove
      bound.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_direct_raw_weight_sum_lower_bound
    bound.toDirectRawWeightSumLowerBound

theorem explicit_lower_bound_of_vonMangoldt_eventually_direct_raw_weight_sum_lower_bound
    (bound : VonMangoldtEventuallyDirectRawWeightSumLowerBound) :
    ExplicitGoldbachLowerBound
      bound.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_direct_raw_weight_sum_lower_bound
    bound

theorem strongGoldbach_of_vonMangoldt_eventually_direct_raw_weight_sum_lower_bound_le100
    (bound : VonMangoldtEventuallyDirectRawWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_direct_raw_weight_sum_lower_bound_le100
    bound.toDirectRawWeightSumLowerBound
    hthreshold

theorem strongGoldbach_of_finite_and_vonMangoldt_eventually_direct_raw_weight_sum_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtEventuallyDirectRawWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_direct_raw_weight_sum_lower_bound_le
    finite
    bound.toDirectRawWeightSumLowerBound
    hthreshold

structure VonMangoldtPositiveLinearRawWeightSumLowerBound where
  threshold : Nat
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  nonPrimePrimePowerWeightSumBound : Nat → ℝ
  nonPrimePrimePowerWeightSumBoundValid :
    ∀ n : Nat, threshold < n → Even n →
      NonPrimePrimePowerVonMangoldtWeightSum n ≤
        nonPrimePrimePowerWeightSumBound n
  rawLinearLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      coefficient * (n : ℝ) ≤ RawVonMangoldtGoldbachSum n
  contaminationDominated :
    ∀ n : Nat, threshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        nonPrimePrimePowerWeightSumBound n <
        coefficient * (n : ℝ)

noncomputable def
    VonMangoldtPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound
    (bound : VonMangoldtPositiveLinearRawWeightSumLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound where
  threshold := bound.threshold
  nonPrimePrimePowerWeightSumBound :=
    bound.nonPrimePrimePowerWeightSumBound
  nonPrimePrimePowerWeightSumBoundValid := by
    intro n htn hEven
    exact bound.nonPrimePrimePowerWeightSumBoundValid n htn hEven
  rawLowerBound := by
    intro n htn hEven
    exact lt_of_lt_of_le
      (bound.contaminationDominated n htn hEven)
      (bound.rawLinearLowerBound n htn hEven)

theorem count_positive_above_of_vonMangoldt_positive_linear_raw_weight_sum_lower_bound
    (bound : VonMangoldtPositiveLinearRawWeightSumLowerBound) :
    GoldbachCountPositiveAbove
      bound.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_direct_raw_weight_sum_lower_bound
    bound.toDirectRawWeightSumLowerBound

theorem explicit_lower_bound_of_vonMangoldt_positive_linear_raw_weight_sum_lower_bound
    (bound : VonMangoldtPositiveLinearRawWeightSumLowerBound) :
    ExplicitGoldbachLowerBound
      bound.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_positive_linear_raw_weight_sum_lower_bound
    bound

theorem strongGoldbach_of_vonMangoldt_positive_linear_raw_weight_sum_lower_bound_le100
    (bound : VonMangoldtPositiveLinearRawWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_direct_raw_weight_sum_lower_bound_le100
    bound.toDirectRawWeightSumLowerBound
    hthreshold

theorem strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_weight_sum_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtPositiveLinearRawWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_direct_raw_weight_sum_lower_bound_le
    finite
    bound.toDirectRawWeightSumLowerBound
    hthreshold

structure VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound where
  threshold : Nat
  coefficient : ℝ
  relativeError : ℝ
  coefficient_pos : 0 < coefficient
  relativeError_lt_one : relativeError < 1
  mainTerm : Nat → ℝ
  nonPrimePrimePowerWeightSumBound : Nat → ℝ
  mainTermLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      coefficient * (n : ℝ) ≤ mainTerm n
  rawRelativeLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      (1 - relativeError) * mainTerm n ≤ RawVonMangoldtGoldbachSum n
  nonPrimePrimePowerWeightSumBoundValid :
    ∀ n : Nat, threshold < n → Even n →
      NonPrimePrimePowerVonMangoldtWeightSum n ≤
        nonPrimePrimePowerWeightSumBound n
  contaminationDominated :
    ∀ n : Nat, threshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        nonPrimePrimePowerWeightSumBound n <
        ((1 - relativeError) * coefficient) * (n : ℝ)

def VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound.effectiveCoefficient
    (bound : VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound) :
    ℝ :=
  (1 - bound.relativeError) * bound.coefficient

theorem
    VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound.effectiveCoefficient_pos
    (bound : VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound) :
    0 < bound.effectiveCoefficient := by
  dsimp
    [VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound.effectiveCoefficient]
  have hfactor : 0 < 1 - bound.relativeError := by
    linarith [bound.relativeError_lt_one]
  exact mul_pos hfactor bound.coefficient_pos

noncomputable def
    VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound.toPositiveLinearRawWeightSumLowerBound
    (bound : VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound) :
    VonMangoldtPositiveLinearRawWeightSumLowerBound where
  threshold := bound.threshold
  coefficient := bound.effectiveCoefficient
  coefficient_pos := bound.effectiveCoefficient_pos
  nonPrimePrimePowerWeightSumBound :=
    bound.nonPrimePrimePowerWeightSumBound
  nonPrimePrimePowerWeightSumBoundValid := by
    intro n htn hEven
    exact bound.nonPrimePrimePowerWeightSumBoundValid n htn hEven
  rawLinearLowerBound := by
    intro n htn hEven
    have hfactor_nonneg : 0 ≤ 1 - bound.relativeError := by
      linarith [bound.relativeError_lt_one]
    have hmain := bound.mainTermLowerBound n htn hEven
    have hscaled :
        (1 - bound.relativeError) * (bound.coefficient * (n : ℝ)) ≤
          (1 - bound.relativeError) * bound.mainTerm n :=
      mul_le_mul_of_nonneg_left hmain hfactor_nonneg
    have hraw := bound.rawRelativeLowerBound n htn hEven
    calc
      bound.effectiveCoefficient * (n : ℝ)
          = (1 - bound.relativeError) *
              (bound.coefficient * (n : ℝ)) := by
            rw
              [VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound.effectiveCoefficient]
            ring
      _ ≤ (1 - bound.relativeError) * bound.mainTerm n := hscaled
      _ ≤ RawVonMangoldtGoldbachSum n := hraw
  contaminationDominated := by
    intro n htn hEven
    simpa
      [VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound.effectiveCoefficient]
      using bound.contaminationDominated n htn hEven

noncomputable def
    VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound
    (bound : VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  bound.toPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound

theorem
    count_positive_above_of_vonMangoldt_relative_error_positive_linear_raw_weight_sum_lower_bound
    (bound : VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound) :
    GoldbachCountPositiveAbove
      bound.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_positive_linear_raw_weight_sum_lower_bound
    bound.toPositiveLinearRawWeightSumLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_relative_error_positive_linear_raw_weight_sum_lower_bound
    (bound : VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound) :
    ExplicitGoldbachLowerBound
      bound.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_relative_error_positive_linear_raw_weight_sum_lower_bound
    bound

theorem
    strongGoldbach_of_vonMangoldt_relative_error_positive_linear_raw_weight_sum_lower_bound_le100
    (bound : VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_positive_linear_raw_weight_sum_lower_bound_le100
    bound.toPositiveLinearRawWeightSumLowerBound
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_relative_error_positive_linear_raw_weight_sum_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_weight_sum_lower_bound_le
    finite
    bound.toPositiveLinearRawWeightSumLowerBound
    hthreshold

structure VonMangoldtRelativeErrorWeightSumMajorMinorArcEstimate where
  threshold : Nat
  coefficient : ℝ
  relativeError : ℝ
  coefficient_pos : 0 < coefficient
  relativeError_lt_one : relativeError < 1
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  nonPrimePrimePowerWeightSumBound : Nat → ℝ
  mainTermLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      coefficient * (n : ℝ) ≤ mainTerm n
  combinedLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  totalAnalyticErrorBound :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n ≤ relativeError * mainTerm n
  nonPrimePrimePowerWeightSumBoundValid :
    ∀ n : Nat, threshold < n → Even n →
      NonPrimePrimePowerVonMangoldtWeightSum n ≤
        nonPrimePrimePowerWeightSumBound n
  contaminationDominated :
    ∀ n : Nat, threshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        nonPrimePrimePowerWeightSumBound n <
        ((1 - relativeError) * coefficient) * (n : ℝ)

noncomputable def
    VonMangoldtRelativeErrorWeightSumMajorMinorArcEstimate.toRelativeErrorPositiveLinearRawWeightSumLowerBound
    (estimate : VonMangoldtRelativeErrorWeightSumMajorMinorArcEstimate) :
    VonMangoldtRelativeErrorPositiveLinearRawWeightSumLowerBound where
  threshold := estimate.threshold
  coefficient := estimate.coefficient
  relativeError := estimate.relativeError
  coefficient_pos := estimate.coefficient_pos
  relativeError_lt_one := estimate.relativeError_lt_one
  mainTerm := estimate.mainTerm
  nonPrimePrimePowerWeightSumBound :=
    estimate.nonPrimePrimePowerWeightSumBound
  mainTermLowerBound := by
    intro n htn hEven
    exact estimate.mainTermLowerBound n htn hEven
  rawRelativeLowerBound := by
    intro n htn hEven
    have hcombined := estimate.combinedLowerBound n htn hEven
    have herror := estimate.totalAnalyticErrorBound n htn hEven
    have hraw :
        estimate.mainTerm n -
            estimate.relativeError * estimate.mainTerm n ≤
          RawVonMangoldtGoldbachSum n := by
      linarith
    calc
      (1 - estimate.relativeError) * estimate.mainTerm n
          = estimate.mainTerm n -
              estimate.relativeError * estimate.mainTerm n := by
            ring
      _ ≤ RawVonMangoldtGoldbachSum n := hraw
  nonPrimePrimePowerWeightSumBoundValid := by
    intro n htn hEven
    exact estimate.nonPrimePrimePowerWeightSumBoundValid n htn hEven
  contaminationDominated := by
    intro n htn hEven
    exact estimate.contaminationDominated n htn hEven

noncomputable def
    VonMangoldtRelativeErrorWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound
    (estimate : VonMangoldtRelativeErrorWeightSumMajorMinorArcEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toRelativeErrorPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound

theorem
    count_positive_above_of_vonMangoldt_relative_error_weight_sum_major_minor_arc_estimate
    (estimate : VonMangoldtRelativeErrorWeightSumMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_relative_error_positive_linear_raw_weight_sum_lower_bound
    estimate.toRelativeErrorPositiveLinearRawWeightSumLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_relative_error_weight_sum_major_minor_arc_estimate
    (estimate : VonMangoldtRelativeErrorWeightSumMajorMinorArcEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_relative_error_weight_sum_major_minor_arc_estimate
    estimate

theorem
    strongGoldbach_of_vonMangoldt_relative_error_weight_sum_major_minor_arc_estimate_le100
    (estimate : VonMangoldtRelativeErrorWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_relative_error_positive_linear_raw_weight_sum_lower_bound_le100
    estimate.toRelativeErrorPositiveLinearRawWeightSumLowerBound
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_relative_error_weight_sum_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtRelativeErrorWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_relative_error_positive_linear_raw_weight_sum_lower_bound_le
    finite
    estimate.toRelativeErrorPositiveLinearRawWeightSumLowerBound
    hthreshold

structure VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate where
  mainTermThreshold : Nat
  combinedThreshold : Nat
  totalAnalyticErrorThreshold : Nat
  weightSumThreshold : Nat
  contaminationThreshold : Nat
  coefficient : ℝ
  relativeError : ℝ
  coefficient_pos : 0 < coefficient
  relativeError_lt_one : relativeError < 1
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  nonPrimePrimePowerWeightSumBound : Nat → ℝ
  mainTermLowerBound :
    ∀ n : Nat, mainTermThreshold < n → Even n →
      coefficient * (n : ℝ) ≤ mainTerm n
  combinedLowerBound :
    ∀ n : Nat, combinedThreshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  totalAnalyticErrorBound :
    ∀ n : Nat, totalAnalyticErrorThreshold < n → Even n →
      majorArcError n + minorArcError n ≤ relativeError * mainTerm n
  nonPrimePrimePowerWeightSumBoundValid :
    ∀ n : Nat, weightSumThreshold < n → Even n →
      NonPrimePrimePowerVonMangoldtWeightSum n ≤
        nonPrimePrimePowerWeightSumBound n
  contaminationDominated :
    ∀ n : Nat, contaminationThreshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        nonPrimePrimePowerWeightSumBound n <
        ((1 - relativeError) * coefficient) * (n : ℝ)

def VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate.threshold
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate) :
    Nat :=
  max estimate.mainTermThreshold
    (max estimate.combinedThreshold
      (max estimate.totalAnalyticErrorThreshold
        (max estimate.weightSumThreshold estimate.contaminationThreshold)))

theorem
    VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate.mainTermThreshold_le_threshold
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate) :
    estimate.mainTermThreshold ≤ estimate.threshold := by
  dsimp
    [VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate.threshold]
  exact Nat.le_max_left _ _

theorem
    VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate.combinedThreshold_le_threshold
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate) :
    estimate.combinedThreshold ≤ estimate.threshold := by
  dsimp
    [VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate.threshold]
  exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

theorem
    VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate.totalAnalyticErrorThreshold_le_threshold
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate) :
    estimate.totalAnalyticErrorThreshold ≤ estimate.threshold := by
  dsimp
    [VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate.threshold]
  exact ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans
    (Nat.le_max_right _ _)

theorem
    VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate.weightSumThreshold_le_threshold
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate) :
    estimate.weightSumThreshold ≤ estimate.threshold := by
  dsimp
    [VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate.threshold]
  exact (((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans
    (Nat.le_max_right _ _)).trans (Nat.le_max_right _ _)

theorem
    VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate.contaminationThreshold_le_threshold
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate) :
    estimate.contaminationThreshold ≤ estimate.threshold := by
  dsimp
    [VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate.threshold]
  exact (((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)).trans
    (Nat.le_max_right _ _)).trans (Nat.le_max_right _ _)

noncomputable def
    VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate.toRelativeErrorWeightSumMajorMinorArcEstimate
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate) :
    VonMangoldtRelativeErrorWeightSumMajorMinorArcEstimate where
  threshold := estimate.threshold
  coefficient := estimate.coefficient
  relativeError := estimate.relativeError
  coefficient_pos := estimate.coefficient_pos
  relativeError_lt_one := estimate.relativeError_lt_one
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  nonPrimePrimePowerWeightSumBound :=
    estimate.nonPrimePrimePowerWeightSumBound
  mainTermLowerBound := by
    intro n htn hEven
    have hmain : estimate.mainTermThreshold < n :=
      lt_of_le_of_lt estimate.mainTermThreshold_le_threshold htn
    exact estimate.mainTermLowerBound n hmain hEven
  combinedLowerBound := by
    intro n htn hEven
    have hcombined : estimate.combinedThreshold < n :=
      lt_of_le_of_lt estimate.combinedThreshold_le_threshold htn
    exact estimate.combinedLowerBound n hcombined hEven
  totalAnalyticErrorBound := by
    intro n htn hEven
    have herror : estimate.totalAnalyticErrorThreshold < n :=
      lt_of_le_of_lt estimate.totalAnalyticErrorThreshold_le_threshold htn
    exact estimate.totalAnalyticErrorBound n herror hEven
  nonPrimePrimePowerWeightSumBoundValid := by
    intro n htn hEven
    have hweight : estimate.weightSumThreshold < n :=
      lt_of_le_of_lt estimate.weightSumThreshold_le_threshold htn
    exact estimate.nonPrimePrimePowerWeightSumBoundValid n hweight hEven
  contaminationDominated := by
    intro n htn hEven
    have hcontamination : estimate.contaminationThreshold < n :=
      lt_of_le_of_lt estimate.contaminationThreshold_le_threshold htn
    exact estimate.contaminationDominated n hcontamination hEven

noncomputable def
    VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toRelativeErrorWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound

theorem
    count_positive_above_of_vonMangoldt_split_threshold_relative_error_weight_sum_major_minor_arc_estimate
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_relative_error_weight_sum_major_minor_arc_estimate
    estimate.toRelativeErrorWeightSumMajorMinorArcEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_split_threshold_relative_error_weight_sum_major_minor_arc_estimate
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_split_threshold_relative_error_weight_sum_major_minor_arc_estimate
    estimate

theorem
    strongGoldbach_of_vonMangoldt_split_threshold_relative_error_weight_sum_major_minor_arc_estimate_le100
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_relative_error_weight_sum_major_minor_arc_estimate_le100
    estimate.toRelativeErrorWeightSumMajorMinorArcEstimate
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_split_threshold_relative_error_weight_sum_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_relative_error_weight_sum_major_minor_arc_estimate_le
    finite
    estimate.toRelativeErrorWeightSumMajorMinorArcEstimate
    hthreshold

structure VonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate where
  coefficient : ℝ
  relativeError : ℝ
  coefficient_pos : 0 < coefficient
  relativeError_lt_one : relativeError < 1
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  nonPrimePrimePowerWeightSumBound : Nat → ℝ
  mainTermLowerBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      coefficient * (n : ℝ) ≤ mainTerm n
  combinedLowerBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  totalAnalyticErrorBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      majorArcError n + minorArcError n ≤ relativeError * mainTerm n
  nonPrimePrimePowerWeightSumBoundValidEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      NonPrimePrimePowerVonMangoldtWeightSum n ≤
        nonPrimePrimePowerWeightSumBound n
  contaminationDominatedEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        nonPrimePrimePowerWeightSumBound n <
        ((1 - relativeError) * coefficient) * (n : ℝ)

theorem
    vonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate_conditions_eventually
    (estimate :
      VonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate) :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      (estimate.coefficient * (n : ℝ) ≤ estimate.mainTerm n) ∧
        (estimate.mainTerm n - estimate.majorArcError n ≤
          RawVonMangoldtGoldbachSum n + estimate.minorArcError n) ∧
        (estimate.majorArcError n + estimate.minorArcError n ≤
          estimate.relativeError * estimate.mainTerm n) ∧
        (NonPrimePrimePowerVonMangoldtWeightSum n ≤
          estimate.nonPrimePrimePowerWeightSumBound n) ∧
        (2 * vonMangoldtWeightSumContaminationBudget
          estimate.nonPrimePrimePowerWeightSumBound n <
          ((1 - estimate.relativeError) * estimate.coefficient) *
            (n : ℝ)) := by
  filter_upwards
    [estimate.mainTermLowerBoundEventually,
      estimate.combinedLowerBoundEventually,
      estimate.totalAnalyticErrorBoundEventually,
      estimate.nonPrimePrimePowerWeightSumBoundValidEventually,
      estimate.contaminationDominatedEventually]
    with n hmain hcombined herror hweight hcontamination
  intro hEven
  exact
    ⟨hmain hEven, hcombined hEven, herror hEven, hweight hEven,
      hcontamination hEven⟩

noncomputable def
    vonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimateThreshold
    (estimate :
      VonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate) :
    Nat :=
  Classical.choose
    (show ∃ N : Nat, ∀ n : Nat, N ≤ n → Even n →
        (estimate.coefficient * (n : ℝ) ≤ estimate.mainTerm n) ∧
          (estimate.mainTerm n - estimate.majorArcError n ≤
            RawVonMangoldtGoldbachSum n + estimate.minorArcError n) ∧
          (estimate.majorArcError n + estimate.minorArcError n ≤
            estimate.relativeError * estimate.mainTerm n) ∧
          (NonPrimePrimePowerVonMangoldtWeightSum n ≤
            estimate.nonPrimePrimePowerWeightSumBound n) ∧
          (2 * vonMangoldtWeightSumContaminationBudget
            estimate.nonPrimePrimePowerWeightSumBound n <
            ((1 - estimate.relativeError) * estimate.coefficient) *
              (n : ℝ)) by
      simpa [Filter.eventually_atTop] using
        vonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate_conditions_eventually
          estimate)

theorem
    vonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate_ge_threshold
    (estimate :
      VonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate) :
    ∀ n : Nat,
      vonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimateThreshold
        estimate ≤ n →
        Even n →
          (estimate.coefficient * (n : ℝ) ≤ estimate.mainTerm n) ∧
            (estimate.mainTerm n - estimate.majorArcError n ≤
              RawVonMangoldtGoldbachSum n + estimate.minorArcError n) ∧
            (estimate.majorArcError n + estimate.minorArcError n ≤
              estimate.relativeError * estimate.mainTerm n) ∧
            (NonPrimePrimePowerVonMangoldtWeightSum n ≤
              estimate.nonPrimePrimePowerWeightSumBound n) ∧
            (2 * vonMangoldtWeightSumContaminationBudget
              estimate.nonPrimePrimePowerWeightSumBound n <
              ((1 - estimate.relativeError) * estimate.coefficient) *
                (n : ℝ)) :=
  Classical.choose_spec
    (show ∃ N : Nat, ∀ n : Nat, N ≤ n → Even n →
        (estimate.coefficient * (n : ℝ) ≤ estimate.mainTerm n) ∧
          (estimate.mainTerm n - estimate.majorArcError n ≤
            RawVonMangoldtGoldbachSum n + estimate.minorArcError n) ∧
          (estimate.majorArcError n + estimate.minorArcError n ≤
            estimate.relativeError * estimate.mainTerm n) ∧
          (NonPrimePrimePowerVonMangoldtWeightSum n ≤
            estimate.nonPrimePrimePowerWeightSumBound n) ∧
          (2 * vonMangoldtWeightSumContaminationBudget
            estimate.nonPrimePrimePowerWeightSumBound n <
            ((1 - estimate.relativeError) * estimate.coefficient) *
              (n : ℝ)) by
      simpa [Filter.eventually_atTop] using
        vonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate_conditions_eventually
          estimate)

noncomputable def
    VonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate.toRelativeErrorWeightSumMajorMinorArcEstimate
    (estimate :
      VonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate) :
    VonMangoldtRelativeErrorWeightSumMajorMinorArcEstimate where
  threshold :=
    vonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimateThreshold
      estimate
  coefficient := estimate.coefficient
  relativeError := estimate.relativeError
  coefficient_pos := estimate.coefficient_pos
  relativeError_lt_one := estimate.relativeError_lt_one
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  nonPrimePrimePowerWeightSumBound :=
    estimate.nonPrimePrimePowerWeightSumBound
  mainTermLowerBound := by
    intro n htn hEven
    exact
      (vonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate_ge_threshold
        estimate n (le_of_lt htn) hEven).1
  combinedLowerBound := by
    intro n htn hEven
    exact
      (vonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate_ge_threshold
        estimate n (le_of_lt htn) hEven).2.1
  totalAnalyticErrorBound := by
    intro n htn hEven
    exact
      (vonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate_ge_threshold
        estimate n (le_of_lt htn) hEven).2.2.1
  nonPrimePrimePowerWeightSumBoundValid := by
    intro n htn hEven
    exact
      (vonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate_ge_threshold
        estimate n (le_of_lt htn) hEven).2.2.2.1
  contaminationDominated := by
    intro n htn hEven
    exact
      (vonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate_ge_threshold
        estimate n (le_of_lt htn) hEven).2.2.2.2

noncomputable def
    VonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toRelativeErrorWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound

theorem
    count_positive_above_of_vonMangoldt_eventually_relative_error_weight_sum_major_minor_arc_estimate
    (estimate :
      VonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_relative_error_weight_sum_major_minor_arc_estimate
    estimate.toRelativeErrorWeightSumMajorMinorArcEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_eventually_relative_error_weight_sum_major_minor_arc_estimate
    (estimate :
      VonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_relative_error_weight_sum_major_minor_arc_estimate
    estimate

theorem
    strongGoldbach_of_vonMangoldt_eventually_relative_error_weight_sum_major_minor_arc_estimate_le100
    (estimate :
      VonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_relative_error_weight_sum_major_minor_arc_estimate_le100
    estimate.toRelativeErrorWeightSumMajorMinorArcEstimate
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_eventually_relative_error_weight_sum_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtEventuallyRelativeErrorWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_relative_error_weight_sum_major_minor_arc_estimate_le
    finite
    estimate.toRelativeErrorWeightSumMajorMinorArcEstimate
    hthreshold

structure VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound where
  weightSumThreshold : Nat
  rawThreshold : Nat
  contaminationThreshold : Nat
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  nonPrimePrimePowerWeightSumBound : Nat → ℝ
  nonPrimePrimePowerWeightSumBoundValid :
    ∀ n : Nat, weightSumThreshold < n → Even n →
      NonPrimePrimePowerVonMangoldtWeightSum n ≤
        nonPrimePrimePowerWeightSumBound n
  rawLinearLowerBound :
    ∀ n : Nat, rawThreshold < n → Even n →
      coefficient * (n : ℝ) ≤ RawVonMangoldtGoldbachSum n
  contaminationDominated :
    ∀ n : Nat, contaminationThreshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        nonPrimePrimePowerWeightSumBound n <
        coefficient * (n : ℝ)

def VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.threshold
    (bound : VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound) :
    Nat :=
  max bound.weightSumThreshold
    (max bound.rawThreshold bound.contaminationThreshold)

theorem
    VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.weightSumThreshold_le_threshold
    (bound : VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound) :
    bound.weightSumThreshold ≤ bound.threshold := by
  dsimp [VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.threshold]
  exact Nat.le_max_left _ _

theorem
    VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.rawThreshold_le_threshold
    (bound : VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound) :
    bound.rawThreshold ≤ bound.threshold := by
  dsimp [VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.threshold]
  exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

theorem
    VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.contaminationThreshold_le_threshold
    (bound : VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound) :
    bound.contaminationThreshold ≤ bound.threshold := by
  dsimp [VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.threshold]
  exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

noncomputable def
    VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.toPositiveLinearRawWeightSumLowerBound
    (bound : VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound) :
    VonMangoldtPositiveLinearRawWeightSumLowerBound where
  threshold := bound.threshold
  coefficient := bound.coefficient
  coefficient_pos := bound.coefficient_pos
  nonPrimePrimePowerWeightSumBound :=
    bound.nonPrimePrimePowerWeightSumBound
  nonPrimePrimePowerWeightSumBoundValid := by
    intro n htn hEven
    have hweight : bound.weightSumThreshold < n :=
      lt_of_le_of_lt bound.weightSumThreshold_le_threshold htn
    exact bound.nonPrimePrimePowerWeightSumBoundValid n hweight hEven
  rawLinearLowerBound := by
    intro n htn hEven
    have hraw : bound.rawThreshold < n :=
      lt_of_le_of_lt bound.rawThreshold_le_threshold htn
    exact bound.rawLinearLowerBound n hraw hEven
  contaminationDominated := by
    intro n htn hEven
    have hcontamination : bound.contaminationThreshold < n :=
      lt_of_le_of_lt bound.contaminationThreshold_le_threshold htn
    exact bound.contaminationDominated n hcontamination hEven

noncomputable def
    VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound
    (bound : VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  bound.toPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound

theorem
    count_positive_above_of_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound
    (bound : VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound) :
    GoldbachCountPositiveAbove
      bound.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_positive_linear_raw_weight_sum_lower_bound
    bound.toPositiveLinearRawWeightSumLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound
    (bound : VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound) :
    ExplicitGoldbachLowerBound
      bound.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound
    bound

theorem
    strongGoldbach_of_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound_le100
    (bound : VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_positive_linear_raw_weight_sum_lower_bound_le100
    bound.toPositiveLinearRawWeightSumLowerBound
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_weight_sum_lower_bound_le
    finite
    bound.toPositiveLinearRawWeightSumLowerBound
    hthreshold

structure VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound where
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  nonPrimePrimePowerWeightSumBound : Nat → ℝ
  nonPrimePrimePowerWeightSumBoundValidEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      NonPrimePrimePowerVonMangoldtWeightSum n ≤
        nonPrimePrimePowerWeightSumBound n
  rawLinearLowerBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      coefficient * (n : ℝ) ≤ RawVonMangoldtGoldbachSum n
  contaminationDominatedEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        nonPrimePrimePowerWeightSumBound n <
        coefficient * (n : ℝ)

theorem
    vonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound_conditions_eventually
    (bound : VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound) :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      (NonPrimePrimePowerVonMangoldtWeightSum n ≤
        bound.nonPrimePrimePowerWeightSumBound n) ∧
      (bound.coefficient * (n : ℝ) ≤ RawVonMangoldtGoldbachSum n) ∧
      (2 * vonMangoldtWeightSumContaminationBudget
        bound.nonPrimePrimePowerWeightSumBound n <
        bound.coefficient * (n : ℝ)) := by
  filter_upwards
    [bound.nonPrimePrimePowerWeightSumBoundValidEventually,
      bound.rawLinearLowerBoundEventually,
      bound.contaminationDominatedEventually] with n hweight hraw hcontamination
  intro hEven
  exact ⟨hweight hEven, hraw hEven, hcontamination hEven⟩

noncomputable def
    vonMangoldtEventuallyPositiveLinearRawWeightSumLowerBoundThreshold
    (bound : VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound) :
    Nat :=
  Classical.choose
    (show ∃ N : Nat, ∀ n : Nat, N ≤ n → Even n →
        (NonPrimePrimePowerVonMangoldtWeightSum n ≤
          bound.nonPrimePrimePowerWeightSumBound n) ∧
        (bound.coefficient * (n : ℝ) ≤ RawVonMangoldtGoldbachSum n) ∧
        (2 * vonMangoldtWeightSumContaminationBudget
          bound.nonPrimePrimePowerWeightSumBound n <
          bound.coefficient * (n : ℝ)) by
      simpa [Filter.eventually_atTop] using
        vonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound_conditions_eventually
          bound)

theorem vonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound_ge_threshold
    (bound : VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound) :
    ∀ n : Nat,
      vonMangoldtEventuallyPositiveLinearRawWeightSumLowerBoundThreshold
        bound ≤ n →
        Even n →
          (NonPrimePrimePowerVonMangoldtWeightSum n ≤
            bound.nonPrimePrimePowerWeightSumBound n) ∧
          (bound.coefficient * (n : ℝ) ≤ RawVonMangoldtGoldbachSum n) ∧
          (2 * vonMangoldtWeightSumContaminationBudget
            bound.nonPrimePrimePowerWeightSumBound n <
            bound.coefficient * (n : ℝ)) :=
  Classical.choose_spec
    (show ∃ N : Nat, ∀ n : Nat, N ≤ n → Even n →
        (NonPrimePrimePowerVonMangoldtWeightSum n ≤
          bound.nonPrimePrimePowerWeightSumBound n) ∧
        (bound.coefficient * (n : ℝ) ≤ RawVonMangoldtGoldbachSum n) ∧
        (2 * vonMangoldtWeightSumContaminationBudget
          bound.nonPrimePrimePowerWeightSumBound n <
          bound.coefficient * (n : ℝ)) by
      simpa [Filter.eventually_atTop] using
        vonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound_conditions_eventually
          bound)

noncomputable def
    VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound.toPositiveLinearRawWeightSumLowerBound
    (bound : VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound) :
    VonMangoldtPositiveLinearRawWeightSumLowerBound where
  threshold :=
    vonMangoldtEventuallyPositiveLinearRawWeightSumLowerBoundThreshold bound
  coefficient := bound.coefficient
  coefficient_pos := bound.coefficient_pos
  nonPrimePrimePowerWeightSumBound :=
    bound.nonPrimePrimePowerWeightSumBound
  nonPrimePrimePowerWeightSumBoundValid := by
    intro n htn hEven
    exact
      (vonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound_ge_threshold
        bound n (le_of_lt htn) hEven).1
  rawLinearLowerBound := by
    intro n htn hEven
    exact
      (vonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound_ge_threshold
        bound n (le_of_lt htn) hEven).2.1
  contaminationDominated := by
    intro n htn hEven
    exact
      (vonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound_ge_threshold
        bound n (le_of_lt htn) hEven).2.2

noncomputable def
    VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound
    (bound : VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  bound.toPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound

theorem
    count_positive_above_of_vonMangoldt_eventually_positive_linear_raw_weight_sum_lower_bound
    (bound : VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound) :
    GoldbachCountPositiveAbove
      bound.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_positive_linear_raw_weight_sum_lower_bound
    bound.toPositiveLinearRawWeightSumLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_eventually_positive_linear_raw_weight_sum_lower_bound
    (bound : VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound) :
    ExplicitGoldbachLowerBound
      bound.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_positive_linear_raw_weight_sum_lower_bound
    bound

theorem
    strongGoldbach_of_vonMangoldt_eventually_positive_linear_raw_weight_sum_lower_bound_le100
    (bound : VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_positive_linear_raw_weight_sum_lower_bound_le100
    bound.toPositiveLinearRawWeightSumLowerBound
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_eventually_positive_linear_raw_weight_sum_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_weight_sum_lower_bound_le
    finite
    bound.toPositiveLinearRawWeightSumLowerBound
    hthreshold

structure VonMangoldtDirectWeightSumMajorMinorArcEstimate where
  threshold : Nat
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  nonPrimePrimePowerWeightSumBound : Nat → ℝ
  combinedLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  nonPrimePrimePowerWeightSumBoundValid :
    ∀ n : Nat, threshold < n → Even n →
      NonPrimePrimePowerVonMangoldtWeightSum n ≤
        nonPrimePrimePowerWeightSumBound n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n +
          2 * vonMangoldtWeightSumContaminationBudget
            nonPrimePrimePowerWeightSumBound n <
        mainTerm n

noncomputable def VonMangoldtDirectWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound
    (estimate : VonMangoldtDirectWeightSumMajorMinorArcEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound where
  threshold := estimate.threshold
  nonPrimePrimePowerWeightSumBound :=
    estimate.nonPrimePrimePowerWeightSumBound
  nonPrimePrimePowerWeightSumBoundValid := by
    intro n htn hEven
    exact estimate.nonPrimePrimePowerWeightSumBoundValid n htn hEven
  rawLowerBound := by
    intro n htn hEven
    have hcombined := estimate.combinedLowerBound n htn hEven
    have hdominated := estimate.totalErrorDominated n htn hEven
    linarith

theorem count_positive_above_of_vonMangoldt_direct_weight_sum_major_minor_arc_estimate
    (estimate : VonMangoldtDirectWeightSumMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove estimate.threshold :=
  count_positive_above_of_vonMangoldt_direct_raw_weight_sum_lower_bound
    estimate.toDirectRawWeightSumLowerBound

theorem strongGoldbach_of_vonMangoldt_direct_weight_sum_major_minor_arc_estimate_le100
    (estimate : VonMangoldtDirectWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_direct_raw_weight_sum_lower_bound_le100
    estimate.toDirectRawWeightSumLowerBound
    (by
      simpa
        [VonMangoldtDirectWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_direct_weight_sum_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtDirectWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_direct_raw_weight_sum_lower_bound_le
    finite
    estimate.toDirectRawWeightSumLowerBound
    (by
      simpa
        [VonMangoldtDirectWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound]
        using hthreshold)

structure VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate where
  combinedThreshold : Nat
  weightSumThreshold : Nat
  totalErrorThreshold : Nat
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  nonPrimePrimePowerWeightSumBound : Nat → ℝ
  combinedLowerBound :
    ∀ n : Nat, combinedThreshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  nonPrimePrimePowerWeightSumBoundValid :
    ∀ n : Nat, weightSumThreshold < n → Even n →
      NonPrimePrimePowerVonMangoldtWeightSum n ≤
        nonPrimePrimePowerWeightSumBound n
  totalErrorDominated :
    ∀ n : Nat, totalErrorThreshold < n → Even n →
      majorArcError n + minorArcError n +
          2 * vonMangoldtWeightSumContaminationBudget
            nonPrimePrimePowerWeightSumBound n <
        mainTerm n

def VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate.threshold
    (estimate : VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate) :
    Nat :=
  max estimate.combinedThreshold
    (max estimate.weightSumThreshold estimate.totalErrorThreshold)

theorem VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate.combinedThreshold_le_threshold
    (estimate : VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate) :
    estimate.combinedThreshold ≤ estimate.threshold := by
  dsimp [VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate.threshold]
  exact Nat.le_max_left _ _

theorem VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate.weightSumThreshold_le_threshold
    (estimate : VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate) :
    estimate.weightSumThreshold ≤ estimate.threshold := by
  dsimp [VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate.threshold]
  exact le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate.totalErrorThreshold_le_threshold
    (estimate : VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate) :
    estimate.totalErrorThreshold ≤ estimate.threshold := by
  dsimp [VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate.threshold]
  exact le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

noncomputable def
    VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate.toDirectWeightSumMajorMinorArcEstimate
    (estimate : VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate) :
    VonMangoldtDirectWeightSumMajorMinorArcEstimate where
  threshold := estimate.threshold
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  nonPrimePrimePowerWeightSumBound :=
    estimate.nonPrimePrimePowerWeightSumBound
  combinedLowerBound := by
    intro n htn hEven
    have hcombined : estimate.combinedThreshold < n :=
      lt_of_le_of_lt estimate.combinedThreshold_le_threshold htn
    exact estimate.combinedLowerBound n hcombined hEven
  nonPrimePrimePowerWeightSumBoundValid := by
    intro n htn hEven
    have hweight : estimate.weightSumThreshold < n :=
      lt_of_le_of_lt estimate.weightSumThreshold_le_threshold htn
    exact estimate.nonPrimePrimePowerWeightSumBoundValid n hweight hEven
  totalErrorDominated := by
    intro n htn hEven
    have htotal : estimate.totalErrorThreshold < n :=
      lt_of_le_of_lt estimate.totalErrorThreshold_le_threshold htn
    exact estimate.totalErrorDominated n htotal hEven

noncomputable def
    VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound
    (estimate : VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toDirectWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound

theorem count_positive_above_of_vonMangoldt_split_threshold_direct_weight_sum_major_minor_arc_estimate
    (estimate : VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectWeightSumMajorMinorArcEstimate.threshold :=
  count_positive_above_of_vonMangoldt_direct_weight_sum_major_minor_arc_estimate
    estimate.toDirectWeightSumMajorMinorArcEstimate

theorem strongGoldbach_of_vonMangoldt_split_threshold_direct_weight_sum_major_minor_arc_estimate_le100
    (estimate : VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate)
    (hthreshold :
      estimate.toDirectWeightSumMajorMinorArcEstimate.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_direct_weight_sum_major_minor_arc_estimate_le100
    estimate.toDirectWeightSumMajorMinorArcEstimate
    hthreshold

theorem strongGoldbach_of_finite_and_vonMangoldt_split_threshold_direct_weight_sum_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtSplitThresholdDirectWeightSumMajorMinorArcEstimate)
    (hthreshold :
      estimate.toDirectWeightSumMajorMinorArcEstimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_direct_weight_sum_major_minor_arc_estimate_le
    finite
    estimate.toDirectWeightSumMajorMinorArcEstimate
    hthreshold

structure VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate where
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  nonPrimePrimePowerWeightSumBound : Nat → ℝ
  combinedLowerBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  nonPrimePrimePowerWeightSumBoundValidEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      NonPrimePrimePowerVonMangoldtWeightSum n ≤
        nonPrimePrimePowerWeightSumBound n
  totalErrorDominatedEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      majorArcError n + minorArcError n +
          2 * vonMangoldtWeightSumContaminationBudget
            nonPrimePrimePowerWeightSumBound n <
        mainTerm n

theorem vonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate_conditions_eventually
    (estimate : VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate) :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      (estimate.mainTerm n - estimate.majorArcError n ≤
          RawVonMangoldtGoldbachSum n + estimate.minorArcError n) ∧
        (NonPrimePrimePowerVonMangoldtWeightSum n ≤
          estimate.nonPrimePrimePowerWeightSumBound n) ∧
        (estimate.majorArcError n + estimate.minorArcError n +
            2 * vonMangoldtWeightSumContaminationBudget
              estimate.nonPrimePrimePowerWeightSumBound n <
          estimate.mainTerm n) := by
  filter_upwards
    [estimate.combinedLowerBoundEventually,
      estimate.nonPrimePrimePowerWeightSumBoundValidEventually,
      estimate.totalErrorDominatedEventually] with n hcombined hweight hdominated
  intro hEven
  exact ⟨hcombined hEven, hweight hEven, hdominated hEven⟩

noncomputable def
    vonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimateThreshold
    (estimate : VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate) :
    Nat :=
  Classical.choose
    (show ∃ N : Nat, ∀ n : Nat, N ≤ n → Even n →
        (estimate.mainTerm n - estimate.majorArcError n ≤
            RawVonMangoldtGoldbachSum n + estimate.minorArcError n) ∧
          (NonPrimePrimePowerVonMangoldtWeightSum n ≤
            estimate.nonPrimePrimePowerWeightSumBound n) ∧
          (estimate.majorArcError n + estimate.minorArcError n +
              2 * vonMangoldtWeightSumContaminationBudget
                estimate.nonPrimePrimePowerWeightSumBound n <
            estimate.mainTerm n) by
      simpa [Filter.eventually_atTop] using
        vonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate_conditions_eventually
          estimate)

theorem vonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate_ge_threshold
    (estimate : VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate) :
    ∀ n : Nat,
      vonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimateThreshold estimate ≤ n →
        Even n →
          (estimate.mainTerm n - estimate.majorArcError n ≤
              RawVonMangoldtGoldbachSum n + estimate.minorArcError n) ∧
            (NonPrimePrimePowerVonMangoldtWeightSum n ≤
              estimate.nonPrimePrimePowerWeightSumBound n) ∧
            (estimate.majorArcError n + estimate.minorArcError n +
                2 * vonMangoldtWeightSumContaminationBudget
                  estimate.nonPrimePrimePowerWeightSumBound n <
              estimate.mainTerm n) :=
  Classical.choose_spec
    (show ∃ N : Nat, ∀ n : Nat, N ≤ n → Even n →
        (estimate.mainTerm n - estimate.majorArcError n ≤
            RawVonMangoldtGoldbachSum n + estimate.minorArcError n) ∧
          (NonPrimePrimePowerVonMangoldtWeightSum n ≤
            estimate.nonPrimePrimePowerWeightSumBound n) ∧
          (estimate.majorArcError n + estimate.minorArcError n +
              2 * vonMangoldtWeightSumContaminationBudget
                estimate.nonPrimePrimePowerWeightSumBound n <
            estimate.mainTerm n) by
      simpa [Filter.eventually_atTop] using
        vonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate_conditions_eventually
          estimate)

noncomputable def
    VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate.toDirectWeightSumMajorMinorArcEstimate
    (estimate : VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate) :
    VonMangoldtDirectWeightSumMajorMinorArcEstimate where
  threshold :=
    vonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimateThreshold estimate
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  nonPrimePrimePowerWeightSumBound :=
    estimate.nonPrimePrimePowerWeightSumBound
  combinedLowerBound := by
    intro n htn hEven
    exact
      (vonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate_ge_threshold
        estimate n (le_of_lt htn) hEven).1
  nonPrimePrimePowerWeightSumBoundValid := by
    intro n htn hEven
    exact
      (vonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate_ge_threshold
        estimate n (le_of_lt htn) hEven).2.1
  totalErrorDominated := by
    intro n htn hEven
    exact
      (vonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate_ge_threshold
        estimate n (le_of_lt htn) hEven).2.2

noncomputable def
    VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound
    (estimate : VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toDirectWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound

theorem count_positive_above_of_vonMangoldt_eventually_direct_weight_sum_major_minor_arc_estimate
    (estimate : VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectWeightSumMajorMinorArcEstimate.threshold :=
  count_positive_above_of_vonMangoldt_direct_weight_sum_major_minor_arc_estimate
    estimate.toDirectWeightSumMajorMinorArcEstimate

theorem explicit_lower_bound_of_vonMangoldt_eventually_direct_weight_sum_major_minor_arc_estimate
    (estimate : VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectWeightSumMajorMinorArcEstimate.threshold :=
  count_positive_above_of_vonMangoldt_eventually_direct_weight_sum_major_minor_arc_estimate
    estimate

theorem strongGoldbach_of_vonMangoldt_eventually_direct_weight_sum_major_minor_arc_estimate_le100
    (estimate : VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate)
    (hthreshold :
      estimate.toDirectWeightSumMajorMinorArcEstimate.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_direct_weight_sum_major_minor_arc_estimate_le100
    estimate.toDirectWeightSumMajorMinorArcEstimate
    hthreshold

theorem strongGoldbach_of_finite_and_vonMangoldt_eventually_direct_weight_sum_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate)
    (hthreshold :
      estimate.toDirectWeightSumMajorMinorArcEstimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_direct_weight_sum_major_minor_arc_estimate_le
    finite
    estimate.toDirectWeightSumMajorMinorArcEstimate
    hthreshold

theorem strongGoldbach_of_finite_and_vonMangoldt_eventually_direct_weight_sum_major_minor_arc_estimate_weight_sum_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtEventuallyDirectWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_direct_raw_weight_sum_lower_bound_le
    finite
    estimate.toDirectRawWeightSumLowerBound
    hthreshold

noncomputable def nonPrimePrimePowerSqrtLogCountBound (n : Nat) : ℝ :=
  ((n.sqrt + 1) * (Nat.log 2 n + 1) : Nat)

theorem nonPrimePrimePowerCount_real_le_sqrt_log_count_bound (n : Nat) :
    (NonPrimePrimePowerCount n : ℝ) ≤
      nonPrimePrimePowerSqrtLogCountBound n := by
  simpa [nonPrimePrimePowerSqrtLogCountBound] using
    nonPrimePrimePowerCount_real_le_sqrt_succ_mul_log_succ n

theorem nonPrimePrimePowerVonMangoldtWeightSum_le_sqrt_log_count_bound_mul_log
    (n : Nat) (hn1 : 1 ≤ n) :
    NonPrimePrimePowerVonMangoldtWeightSum n ≤
      nonPrimePrimePowerSqrtLogCountBound n * Real.log (n : ℝ) := by
  have hweight :=
    nonPrimePrimePowerVonMangoldtWeightSum_le_count_mul_log n
  have hcount := nonPrimePrimePowerCount_real_le_sqrt_log_count_bound n
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hn1)
  exact hweight.trans (mul_le_mul_of_nonneg_right hcount hlog_nonneg)

noncomputable def canonicalNonPrimePrimePowerVonMangoldtWeightSumBound
    (n : Nat) : ℝ :=
  nonPrimePrimePowerSqrtLogCountBound n * Real.log (n : ℝ)

theorem canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_valid
    {threshold : Nat} (n : Nat) (htn : threshold < n) (_hEven : Even n) :
    NonPrimePrimePowerVonMangoldtWeightSum n ≤
      canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n := by
  have hn_pos : 0 < n := lt_of_le_of_lt (Nat.zero_le threshold) htn
  simpa [canonicalNonPrimePrimePowerVonMangoldtWeightSumBound] using
    nonPrimePrimePowerVonMangoldtWeightSum_le_sqrt_log_count_bound_mul_log
      n (Nat.succ_le_of_lt hn_pos)

open Filter Asymptotics in
theorem real_rpow_half_mul_log_cube_isLittleO_linear :
    (fun x : ℝ => x ^ (1 / (2 : ℝ)) * Real.log x ^ (3 : ℝ)) =o[atTop]
      (fun x : ℝ => x) := by
  have hlog :
      (fun x : ℝ => Real.log x ^ (3 : ℝ)) =o[atTop]
        (fun x : ℝ => x ^ (1 / (2 : ℝ))) := by
    exact isLittleO_log_rpow_rpow_atTop (3 : ℝ) (by norm_num)
  have hmul :
      (fun x : ℝ => Real.log x ^ (3 : ℝ) * x ^ (1 / (2 : ℝ))) =o[atTop]
        (fun x : ℝ => x ^ (1 / (2 : ℝ)) * x ^ (1 / (2 : ℝ))) := by
    exact hlog.mul_isBigO (isBigO_refl _ _)
  refine Asymptotics.IsLittleO.congr' hmul ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    ring
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_add hx]
    norm_num

open Filter Asymptotics in
theorem real_sqrt_mul_log_cube_isLittleO_linear :
    (fun x : ℝ => Real.sqrt x * Real.log x ^ (3 : ℝ)) =o[atTop]
      (fun x : ℝ => x) := by
  simpa [Real.sqrt_eq_rpow] using
    real_rpow_half_mul_log_cube_isLittleO_linear

open Filter Asymptotics in
theorem eventually_real_sqrt_mul_log_cube_lt_const_mul_linear
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x in atTop, Real.sqrt x * Real.log x ^ (3 : ℝ) < c * x := by
  have hsmall :
      (fun x : ℝ => Real.sqrt x * Real.log x ^ (3 : ℝ)) =o[atTop]
        (fun x : ℝ => (c / 2) * x) := by
    exact real_sqrt_mul_log_cube_isLittleO_linear.const_mul_right
      (by nlinarith [hc] : c / 2 ≠ 0)
  filter_upwards [hsmall.eventuallyLE, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  have htarget_nonneg : 0 ≤ c / 2 * x := by positivity
  have hnorm_target : ‖(c / 2) * x‖ = c / 2 * x := by
    rw [Real.norm_eq_abs, abs_of_nonneg htarget_nonneg]
  have hle_norm :
      Real.sqrt x * Real.log x ^ (3 : ℝ) ≤
        ‖Real.sqrt x * Real.log x ^ (3 : ℝ)‖ := by
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  have hx' :
      ‖Real.sqrt x * Real.log x ^ (3 : ℝ)‖ ≤ c / 2 * x := by
    simpa [hnorm_target] using hx
  have hle_half :
      Real.sqrt x * Real.log x ^ (3 : ℝ) ≤ c / 2 * x :=
    hle_norm.trans hx'
  have hhalf_lt : c / 2 * x < c * x := by
    nlinarith [hc, hxpos]
  exact hle_half.trans_lt hhalf_lt

noncomputable def vonMangoldtSqrtLogBudgetComparisonConstant : ℝ :=
  4 * ((Real.log 2)⁻¹ + 1)

theorem vonMangoldtSqrtLogBudgetComparisonConstant_pos :
    0 < vonMangoldtSqrtLogBudgetComparisonConstant := by
  unfold vonMangoldtSqrtLogBudgetComparisonConstant
  positivity

theorem sqrt_succ_real_le_two_mul_real_sqrt
    (n : Nat) (hn1 : 1 ≤ n) :
    ((n.sqrt + 1 : Nat) : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
  have hsqrt_le : (n.sqrt : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have hone_le : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hn1
  norm_num
  linarith

theorem nat_log_two_succ_real_le_log_multiplier
    (n : Nat) (hlog_ge : 1 ≤ Real.log (n : ℝ)) :
    ((Nat.log 2 n + 1 : Nat) : ℝ) ≤
      ((Real.log 2)⁻¹ + 1) * Real.log (n : ℝ) := by
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have hnatlog : (Nat.log 2 n : ℝ) ≤ Real.logb (2 : ℕ) n :=
    Real.natLog_le_logb n 2
  have hnatlog' : (Nat.log 2 n : ℝ) ≤
      Real.log (n : ℝ) / Real.log (2 : ℝ) := by
    simpa [Real.logb] using hnatlog
  calc
    ((Nat.log 2 n + 1 : Nat) : ℝ) = (Nat.log 2 n : ℝ) + 1 := by
      norm_num
    _ ≤ Real.log (n : ℝ) / Real.log (2 : ℝ) + 1 := by
      linarith
    _ ≤ Real.log (n : ℝ) / Real.log (2 : ℝ) + Real.log (n : ℝ) := by
      linarith
    _ = ((Real.log 2)⁻¹ + 1) * Real.log (n : ℝ) := by
      field_simp [hlog2pos.ne']

theorem vonMangoldt_sqrt_log_count_budget_le_real_model
    (n : Nat) (hn1 : 1 ≤ n)
    (hlog_ge : 1 ≤ Real.log (n : ℝ)) :
    2 * vonMangoldtLogCountContaminationBudget
        nonPrimePrimePowerSqrtLogCountBound n ≤
      vonMangoldtSqrtLogBudgetComparisonConstant *
        (Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ (3 : Nat)) := by
  have hsqrt0 := sqrt_succ_real_le_two_mul_real_sqrt n hn1
  have hlog0 := nat_log_two_succ_real_le_log_multiplier n hlog_ge
  have hsqrt : (n.sqrt : ℝ) + 1 ≤ 2 * Real.sqrt (n : ℝ) := by
    simpa [Nat.cast_add] using hsqrt0
  have hlog : (Nat.log 2 n : ℝ) + 1 ≤
      ((Real.log 2)⁻¹ + 1) * Real.log (n : ℝ) := by
    simpa [Nat.cast_add] using hlog0
  have hcount : nonPrimePrimePowerSqrtLogCountBound n ≤
      (2 * Real.sqrt (n : ℝ)) *
        (((Real.log 2)⁻¹ + 1) * Real.log (n : ℝ)) := by
    dsimp [nonPrimePrimePowerSqrtLogCountBound]
    norm_num [Nat.cast_add, Nat.cast_mul]
    exact mul_le_mul hsqrt hlog (by positivity) (by positivity)
  calc
    2 * vonMangoldtLogCountContaminationBudget
        nonPrimePrimePowerSqrtLogCountBound n
        = 2 * (nonPrimePrimePowerSqrtLogCountBound n *
            (Real.log (n : ℝ) * Real.log (n : ℝ))) := by
          simp [vonMangoldtLogCountContaminationBudget]
    _ ≤ 2 * (((2 * Real.sqrt (n : ℝ)) *
            (((Real.log 2)⁻¹ + 1) * Real.log (n : ℝ))) *
            (Real.log (n : ℝ) * Real.log (n : ℝ))) := by
          gcongr
    _ = vonMangoldtSqrtLogBudgetComparisonConstant *
          (Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ (3 : Nat)) := by
          unfold vonMangoldtSqrtLogBudgetComparisonConstant
          ring

theorem one_le_real_log_nat_of_three_le
    {n : Nat} (hn : 3 ≤ n) :
    1 ≤ Real.log (n : ℝ) := by
  rw [Real.le_log_iff_exp_le]
  · have hexp_lt_three : Real.exp 1 < (3 : ℝ) := by
      have h := Real.exp_one_lt_d9
      norm_num at h ⊢
      linarith
    exact le_trans (le_of_lt hexp_lt_three) (by exact_mod_cast hn)
  · positivity

open Filter in
theorem eventually_real_sqrt_mul_log_nat_cube_lt_const_mul_linear
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x in atTop, Real.sqrt x * Real.log x ^ (3 : Nat) < c * x := by
  simpa [Real.rpow_natCast] using
    eventually_real_sqrt_mul_log_cube_lt_const_mul_linear (c := c) hc

open Filter Asymptotics in
/-- Asymptotic: `log n = o(n)` in the natural-number topology. -/
theorem eventually_real_log_nat_lt_const_mul_linear
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop, Real.log n < c * (n : ℝ) := by
  have h := Real.isLittleO_log_id_atTop
  have hsmall : (fun x : ℝ => Real.log x) =o[atTop]
      (fun x : ℝ => (c / 2) * x) := by
    exact h.const_mul_right (by nlinarith [hc] : c / 2 ≠ 0)
  have hreal :
      ∀ᶠ x : ℝ in atTop, Real.log x < c * x := by
    filter_upwards [hsmall.eventuallyLE, eventually_gt_atTop (0 : ℝ)]
      with x hx hxpos
    have htarget_nonneg : 0 ≤ c / 2 * x := by positivity
    have hnorm_target : ‖(c / 2) * x‖ = c / 2 * x := by
      rw [Real.norm_eq_abs, abs_of_nonneg htarget_nonneg]
    have hle_norm : Real.log x ≤ ‖Real.log x‖ := le_abs_self _
    have hx' : ‖Real.log x‖ ≤ c / 2 * x := by
      simpa [hnorm_target] using hx
    nlinarith [hle_norm, hx', hxpos, hc]
  simpa using hreal.natCast_atTop

open Filter Asymptotics in
/-- Asymptotic: `√(2n) · log(2n) = o(n)` in the natural-number topology. -/
theorem eventually_sqrt_two_mul_log_two_mul_lt_const_mul_linear
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      (Nat.sqrt (2 * n) : ℝ) * Real.log ((2 * n : Nat) : ℝ) <
        c * (n : ℝ) := by
  -- Use that √x · log³x = o(x), and apply at x = 2n with c/2.
  have hreal := eventually_real_sqrt_mul_log_nat_cube_lt_const_mul_linear
    (c := c / 2) (by positivity)
  have hreal_nat : ∀ᶠ n : Nat in atTop,
      Real.sqrt ((n : Nat) : ℝ) *
          Real.log ((n : Nat) : ℝ) ^ (3 : Nat) <
        c / 2 * ((n : Nat) : ℝ) := by
    simpa using hreal.natCast_atTop
  have h2n_tendsto : Tendsto (fun n : Nat => 2 * n) atTop atTop := by
    apply Filter.tendsto_atTop_mono (fun n => by omega : ∀ n, n ≤ 2 * n)
    exact Filter.tendsto_id
  have hcomp : ∀ᶠ n : Nat in atTop,
      Real.sqrt ((2 * n : Nat) : ℝ) *
          Real.log ((2 * n : Nat) : ℝ) ^ (3 : Nat) <
        c / 2 * ((2 * n : Nat) : ℝ) := h2n_tendsto.eventually hreal_nat
  -- For n ≥ 2, log(2n) ≥ 1.
  filter_upwards [hcomp, Filter.eventually_ge_atTop 2] with n hsmall hn2
  -- Cast nat sqrt to real sqrt.
  have h2n_ge_3 : (3 : Nat) ≤ 2 * n := by omega
  have hlog_ge_one : (1 : ℝ) ≤ Real.log ((2 * n : Nat) : ℝ) :=
    one_le_real_log_nat_of_three_le h2n_ge_3
  have hsqrt_le : (Nat.sqrt (2 * n) : ℝ) ≤ Real.sqrt ((2 * n : Nat) : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have hlog_nonneg : 0 ≤ Real.log ((2 * n : Nat) : ℝ) := by linarith
  have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt ((2 * n : Nat) : ℝ) :=
    Real.sqrt_nonneg _
  have hlog_le_cube :
      Real.log ((2 * n : Nat) : ℝ) ≤
        Real.log ((2 * n : Nat) : ℝ) ^ (3 : Nat) := by
    have hpow_eq : Real.log ((2 * n : Nat) : ℝ) ^ (3 : Nat) =
        Real.log ((2 * n : Nat) : ℝ) *
          (Real.log ((2 * n : Nat) : ℝ) * Real.log ((2 * n : Nat) : ℝ)) := by ring
    rw [hpow_eq]
    nlinarith [hlog_ge_one, hlog_nonneg]
  have hbound1 :
      (Nat.sqrt (2 * n) : ℝ) * Real.log ((2 * n : Nat) : ℝ) ≤
        Real.sqrt ((2 * n : Nat) : ℝ) * Real.log ((2 * n : Nat) : ℝ) :=
    mul_le_mul_of_nonneg_right hsqrt_le hlog_nonneg
  have hbound2 :
      Real.sqrt ((2 * n : Nat) : ℝ) * Real.log ((2 * n : Nat) : ℝ) ≤
        Real.sqrt ((2 * n : Nat) : ℝ) *
          Real.log ((2 * n : Nat) : ℝ) ^ (3 : Nat) :=
    mul_le_mul_of_nonneg_left hlog_le_cube hsqrt_nonneg
  -- hsmall says √(2n) · log³(2n) < (c/2) · (2n) = c · n
  have h2n_real : ((2 * n : Nat) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hsmall_val :
      Real.sqrt ((2 * n : Nat) : ℝ) *
          Real.log ((2 * n : Nat) : ℝ) ^ (3 : Nat) <
        c * (n : ℝ) := by
    have := hsmall
    rw [h2n_real] at this
    nlinarith [this, hc]
  linarith [hbound1, hbound2, hsmall_val]

open Filter in
/-- **Asymptotic Chebyshev linear lower bound on θ**: for any `c < log 4`,
eventually `c · n ≤ θ(2n)`.  This is the truly linear Chebyshev statement
(no √n correction term), obtained by absorbing the lower-order error into
the asymptotic slack. -/
theorem eventually_chebyshev_theta_two_mul_ge_const_mul_linear
    {c : ℝ} (hc_lt : c < Real.log 4) :
    ∀ᶠ n : Nat in atTop,
      c * (n : ℝ) ≤ Chebyshev.theta ((2 * n : Nat) : ℝ) := by
  set ε : ℝ := (Real.log 4 - c) / 2 with hε_def
  have hε_pos : 0 < ε := by
    have hsub_pos : 0 < Real.log 4 - c := sub_pos.mpr hc_lt
    positivity
  have h2ε : 2 * ε = Real.log 4 - c := by rw [hε_def]; ring
  have hlog := eventually_real_log_nat_lt_const_mul_linear (c := ε) hε_pos
  have hsqrt := eventually_sqrt_two_mul_log_two_mul_lt_const_mul_linear
    (c := ε) hε_pos
  filter_upwards [hlog, hsqrt, eventually_ge_atTop 4] with n hlog hsqrt hn4
  have hcheb := chebyshev_theta_linear_lower_bound hn4
  nlinarith [hcheb, hlog, hsqrt, h2ε]

open Filter in
/-- **Asymptotic Chebyshev linear lower bound on ψ**: via `theta_le_psi`,
the same bound transfers to ψ. -/
theorem eventually_chebyshev_psi_two_mul_ge_const_mul_linear
    {c : ℝ} (hc_lt : c < Real.log 4) :
    ∀ᶠ n : Nat in atTop,
      c * (n : ℝ) ≤ Chebyshev.psi ((2 * n : Nat) : ℝ) := by
  filter_upwards [eventually_chebyshev_theta_two_mul_ge_const_mul_linear hc_lt]
    with n h
  exact h.trans (Chebyshev.theta_le_psi _)

open Filter in
/-- **Asymptotic Chebyshev lower bound on primeCounting**: For any `c < log 4`,
eventually `c · n < π(2n) · log(2n)`.  In particular, `π(x) ≳ x · log 2 / log x`
asymptotically. -/
theorem eventually_chebyshev_primeCounting_two_mul_log_ge_const_mul_linear
    {c : ℝ} (hc_lt : c < Real.log 4) :
    ∀ᶠ n : Nat in atTop,
      c * (n : ℝ) <
        (Nat.primeCounting (2 * n) : ℝ) * Real.log ((2 * n : Nat) : ℝ) := by
  set ε : ℝ := Real.log 4 - c with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; linarith
  have hlog := eventually_real_log_nat_lt_const_mul_linear (c := ε) hε_pos
  filter_upwards [hlog, eventually_ge_atTop 4] with n hlog hn4
  have hcheb := chebyshev_primeCounting_lower_bound hn4
  -- hcheb: n log 4 - log n < π(2n) · log(2n)
  -- hlog: log n < ε · n
  -- combined: n log 4 - ε · n < π(2n) · log(2n), i.e., c · n < π(2n) · log(2n).
  have : (n : ℝ) * Real.log 4 - ε * (n : ℝ) = c * (n : ℝ) := by
    rw [hε_def]; ring
  linarith [hcheb, hlog, this]

open Filter in
/-- **PNT-style asymptotic lower bound on π**: for any `c < log 2`, eventually
`c · (2n) / log(2n) ≤ π(2n)`.  This is the form `π(x) ≥ c · x / log x`,
the canonical Chebyshev/PNT-type linear-over-log lower bound. -/
theorem eventually_chebyshev_primeCounting_two_mul_ge_const_mul_div_log
    {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < Real.log 2) :
    ∀ᶠ n : Nat in atTop,
      c * ((2 * n : Nat) : ℝ) / Real.log ((2 * n : Nat) : ℝ) ≤
        (Nat.primeCounting (2 * n) : ℝ) := by
  set d : ℝ := 2 * c with hd_def
  have hd_lt : d < Real.log 4 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; ring
    rw [hd_def, this]; linarith
  have hd_pos : 0 < d := by rw [hd_def]; linarith
  have h := eventually_chebyshev_primeCounting_two_mul_log_ge_const_mul_linear hd_lt
  filter_upwards [h, eventually_gt_atTop 1] with n h hn_gt_one
  have h2n_pos : 0 < 2 * n := by omega
  have h2n_gt_one : 1 < (2 * n : Nat) := by omega
  have h2n_real : ((2 * n : Nat) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hlog_pos : 0 < Real.log ((2 * n : Nat) : ℝ) :=
    Real.log_pos (by exact_mod_cast h2n_gt_one)
  -- h: d · n < π(2n) · log(2n), so 2c · n < π(2n) · log(2n)
  -- want: c · 2n / log(2n) ≤ π(2n), i.e., c · 2n ≤ π(2n) · log(2n)
  -- since c · 2n = 2c · n = d · n < π(2n) · log(2n), we have ≤.
  rw [div_le_iff₀ hlog_pos]
  have hrearrange : c * ((2 * n : Nat) : ℝ) = d * (n : ℝ) := by
    rw [hd_def, h2n_real]; ring
  rw [hrearrange]
  linarith

open Filter in
theorem eventually_vonMangoldt_sqrt_log_count_budget_lt_const_mul_linear
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      2 * vonMangoldtLogCountContaminationBudget
        nonPrimePrimePowerSqrtLogCountBound n < c * (n : ℝ) := by
  have hKpos : 0 < vonMangoldtSqrtLogBudgetComparisonConstant :=
    vonMangoldtSqrtLogBudgetComparisonConstant_pos
  have hsmall_real :=
    eventually_real_sqrt_mul_log_nat_cube_lt_const_mul_linear
      (c := c / vonMangoldtSqrtLogBudgetComparisonConstant)
      (by positivity)
  have hsmall_nat :
      ∀ᶠ n : Nat in atTop,
        Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ (3 : Nat) <
          c / vonMangoldtSqrtLogBudgetComparisonConstant * (n : ℝ) := by
    simpa using hsmall_real.natCast_atTop
  have hlog_event :
      ∀ᶠ n : Nat in atTop, 1 ≤ Real.log (n : ℝ) := by
    exact (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)).natCast_atTop
  filter_upwards [hsmall_nat, hlog_event, eventually_ge_atTop (1 : Nat)]
    with n hsmall hlog_ge hn1
  have hbudget_le :=
    vonMangoldt_sqrt_log_count_budget_le_real_model n hn1 hlog_ge
  have hmodel_lt :
      vonMangoldtSqrtLogBudgetComparisonConstant *
          (Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ (3 : Nat)) <
        c * (n : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hsmall hKpos
    have hright :
        vonMangoldtSqrtLogBudgetComparisonConstant *
            (c / vonMangoldtSqrtLogBudgetComparisonConstant * (n : ℝ)) =
          c * (n : ℝ) := by
      field_simp [hKpos.ne']
    exact hmul.trans_eq hright
  exact hbudget_le.trans_lt hmodel_lt

open Filter in
theorem eventually_canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_contamination_lt_const_mul_linear
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        c * (n : ℝ) := by
  simpa [canonicalNonPrimePrimePowerVonMangoldtWeightSumBound,
    vonMangoldtWeightSumContaminationBudget,
    vonMangoldtLogCountContaminationBudget, mul_assoc] using
    eventually_vonMangoldt_sqrt_log_count_budget_lt_const_mul_linear
      (c := c) hc

theorem
    canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_contamination_lt_const_mul_linear_of_sqrt_log_model
    {threshold : Nat} {c : ℝ}
    (hlog : ∀ n : Nat, threshold < n → Even n →
      1 ≤ Real.log (n : ℝ))
    (hmodel : ∀ n : Nat, threshold < n → Even n →
      vonMangoldtSqrtLogBudgetComparisonConstant *
          (Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ (3 : Nat)) <
        c * (n : ℝ)) :
    ∀ n : Nat, threshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        c * (n : ℝ) := by
  intro n htn hEven
  have hn_pos : 0 < n := lt_of_le_of_lt (Nat.zero_le threshold) htn
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn_pos
  have hbudget :=
    vonMangoldt_sqrt_log_count_budget_le_real_model n hn1
      (hlog n htn hEven)
  have hbudget' :
      2 * vonMangoldtWeightSumContaminationBudget
          canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n ≤
        vonMangoldtSqrtLogBudgetComparisonConstant *
          (Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ (3 : Nat)) := by
    simpa [canonicalNonPrimePrimePowerVonMangoldtWeightSumBound,
      vonMangoldtWeightSumContaminationBudget,
      vonMangoldtLogCountContaminationBudget, mul_assoc] using hbudget
  exact hbudget'.trans_lt (hmodel n htn hEven)

theorem
    canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_contamination_lt_const_mul_linear_of_sqrt_log_model_ge_two_threshold
    {threshold : Nat} {c : ℝ}
    (hthreshold : 2 ≤ threshold)
    (hmodel : ∀ n : Nat, threshold < n → Even n →
      vonMangoldtSqrtLogBudgetComparisonConstant *
          (Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ (3 : Nat)) <
        c * (n : ℝ)) :
    ∀ n : Nat, threshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        c * (n : ℝ) :=
  canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_contamination_lt_const_mul_linear_of_sqrt_log_model
    (fun _ htn _hEven =>
      one_le_real_log_nat_of_three_le
        ((Nat.succ_le_succ hthreshold).trans (Nat.succ_le_of_lt htn)))
    hmodel

theorem
    canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_hl_effective_contamination_dominated_of_sqrt_log_model
    {threshold : Nat} {coefficient relativeError : ℝ}
    (hlog : ∀ n : Nat, threshold < n → Even n →
      1 ≤ Real.log (n : ℝ))
    (hmodel : ∀ n : Nat, threshold < n → Even n →
      vonMangoldtSqrtLogBudgetComparisonConstant *
          (Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ (3 : Nat)) <
        ((1 - relativeError) * coefficient) * (n : ℝ)) :
    ∀ n : Nat, threshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        ((1 - relativeError) * coefficient) * (n : ℝ) :=
  canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_contamination_lt_const_mul_linear_of_sqrt_log_model
    hlog hmodel

theorem
    quarter_canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_contamination_dominated_of_sqrt_log_model
    {threshold : Nat} {relativeError : ℝ}
    (hlog : ∀ n : Nat, threshold < n → Even n →
      1 ≤ Real.log (n : ℝ))
    (hmodel : ∀ n : Nat, threshold < n → Even n →
      vonMangoldtSqrtLogBudgetComparisonConstant *
          (Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ (3 : Nat)) <
        ((1 - relativeError) * (1 / 4 : ℝ)) * (n : ℝ)) :
    ∀ n : Nat, threshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        ((1 - relativeError) * (1 / 4 : ℝ)) * (n : ℝ) :=
  canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_hl_effective_contamination_dominated_of_sqrt_log_model
    (coefficient := (1 / 4 : ℝ))
    hlog hmodel

theorem
    quarter_canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_contamination_dominated_of_sqrt_log_model_ge_two_threshold
    {threshold : Nat} {relativeError : ℝ}
    (hthreshold : 2 ≤ threshold)
    (hmodel : ∀ n : Nat, threshold < n → Even n →
      vonMangoldtSqrtLogBudgetComparisonConstant *
          (Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ (3 : Nat)) <
        ((1 - relativeError) * (1 / 4 : ℝ)) * (n : ℝ)) :
    ∀ n : Nat, threshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        ((1 - relativeError) * (1 / 4 : ℝ)) * (n : ℝ) :=
  quarter_canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_contamination_dominated_of_sqrt_log_model
    (fun _ htn _hEven =>
      one_le_real_log_nat_of_three_le
        ((Nat.succ_le_succ hthreshold).trans (Nat.succ_le_of_lt htn)))
    hmodel

open Filter in
theorem eventually_canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_hl_effective_contamination_dominated
    {coefficient relativeError : ℝ}
    (hcoefficient : 0 < coefficient)
    (hrelativeError : relativeError < 1) :
    ∀ᶠ n : Nat in atTop,
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        ((1 - relativeError) * coefficient) * (n : ℝ) := by
  exact
    eventually_canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_contamination_lt_const_mul_linear
      (c := (1 - relativeError) * coefficient)
      (mul_pos (sub_pos.mpr hrelativeError) hcoefficient)

noncomputable def canonicalHLContaminationThreshold
    (coefficient relativeError : ℝ)
    (hcoefficient : 0 < coefficient)
    (hrelativeError : relativeError < 1) : Nat :=
  Classical.choose
    (show ∃ N : Nat, ∀ n : Nat, N ≤ n →
        2 * vonMangoldtWeightSumContaminationBudget
          canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
          ((1 - relativeError) * coefficient) * (n : ℝ) by
      simpa [Filter.eventually_atTop] using
        eventually_canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_hl_effective_contamination_dominated
          hcoefficient hrelativeError)

theorem canonicalHLContaminationThreshold_spec
    {coefficient relativeError : ℝ}
    (hcoefficient : 0 < coefficient)
    (hrelativeError : relativeError < 1) :
    ∀ n : Nat,
      canonicalHLContaminationThreshold coefficient relativeError
        hcoefficient hrelativeError ≤ n →
        2 * vonMangoldtWeightSumContaminationBudget
          canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
          ((1 - relativeError) * coefficient) * (n : ℝ) :=
  Classical.choose_spec
    (show ∃ N : Nat, ∀ n : Nat, N ≤ n →
        2 * vonMangoldtWeightSumContaminationBudget
          canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
          ((1 - relativeError) * coefficient) * (n : ℝ) by
      simpa [Filter.eventually_atTop] using
        eventually_canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_hl_effective_contamination_dominated
          hcoefficient hrelativeError)

noncomputable def canonicalLinearContaminationThreshold
    (coefficient : ℝ) (hcoefficient : 0 < coefficient) : Nat :=
  canonicalHLContaminationThreshold coefficient 0 hcoefficient (by norm_num)

theorem canonicalLinearContaminationThreshold_spec
    {coefficient : ℝ} (hcoefficient : 0 < coefficient) :
    ∀ n : Nat,
      canonicalLinearContaminationThreshold coefficient hcoefficient ≤ n →
        2 * vonMangoldtWeightSumContaminationBudget
          canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
          coefficient * (n : ℝ) := by
  intro n hn
  simpa [canonicalLinearContaminationThreshold] using
    (canonicalHLContaminationThreshold_spec
      (coefficient := coefficient)
      (relativeError := (0 : ℝ))
      hcoefficient
      (by norm_num)
      n
      hn)

open Filter in
theorem eventually_sqrt_log_model_lt_const_mul_linear
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      vonMangoldtSqrtLogBudgetComparisonConstant *
          (Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ (3 : Nat)) <
        c * (n : ℝ) := by
  have hKpos : 0 < vonMangoldtSqrtLogBudgetComparisonConstant :=
    vonMangoldtSqrtLogBudgetComparisonConstant_pos
  have hreal :=
    eventually_real_sqrt_mul_log_nat_cube_lt_const_mul_linear
      (c := c / vonMangoldtSqrtLogBudgetComparisonConstant) (by positivity)
  have hnat :
      ∀ᶠ n : Nat in atTop,
        Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ (3 : Nat) <
          c / vonMangoldtSqrtLogBudgetComparisonConstant * (n : ℝ) := by
    simpa using hreal.natCast_atTop
  filter_upwards [hnat] with n hn
  have hscaled := mul_lt_mul_of_pos_left hn hKpos
  have hrw :
      vonMangoldtSqrtLogBudgetComparisonConstant *
          (c / vonMangoldtSqrtLogBudgetComparisonConstant * (n : ℝ)) =
        c * (n : ℝ) := by
    field_simp [hKpos.ne']
  exact hscaled.trans_eq hrw

noncomputable def canonicalSqrtLogModelThreshold
    (c : ℝ) (hc : 0 < c) : Nat :=
  Classical.choose
    (show ∃ N : Nat, ∀ n : Nat, N ≤ n →
        vonMangoldtSqrtLogBudgetComparisonConstant *
            (Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ (3 : Nat)) <
          c * (n : ℝ) by
      simpa [Filter.eventually_atTop] using
        eventually_sqrt_log_model_lt_const_mul_linear hc)

theorem canonicalSqrtLogModelThreshold_spec
    {c : ℝ} (hc : 0 < c) :
    ∀ n : Nat,
      canonicalSqrtLogModelThreshold c hc ≤ n →
        vonMangoldtSqrtLogBudgetComparisonConstant *
            (Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ (3 : Nat)) <
          c * (n : ℝ) :=
  Classical.choose_spec
    (show ∃ N : Nat, ∀ n : Nat, N ≤ n →
        vonMangoldtSqrtLogBudgetComparisonConstant *
            (Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ (3 : Nat)) <
          c * (n : ℝ) by
      simpa [Filter.eventually_atTop] using
        eventually_sqrt_log_model_lt_const_mul_linear hc)

noncomputable def canonicalQuarterSqrtLogModelThreshold
    (relativeError : ℝ) (hrelativeError : relativeError < 1) : Nat :=
  max 2
    (canonicalSqrtLogModelThreshold ((1 - relativeError) * (1 / 4 : ℝ))
      (by
        have h1 : 0 < (1 - relativeError) := sub_pos.mpr hrelativeError
        have h2 : (0 : ℝ) < 1 / 4 := by norm_num
        exact mul_pos h1 h2))

theorem canonicalQuarterSqrtLogModelThreshold_ge_two
    {relativeError : ℝ} (hrelativeError : relativeError < 1) :
    2 ≤ canonicalQuarterSqrtLogModelThreshold relativeError hrelativeError := by
  exact Nat.le_max_left _ _

theorem canonicalQuarterSqrtLogModelThreshold_spec
    {relativeError : ℝ} (hrelativeError : relativeError < 1) :
    ∀ n : Nat,
      canonicalQuarterSqrtLogModelThreshold relativeError hrelativeError < n →
      Even n →
        vonMangoldtSqrtLogBudgetComparisonConstant *
            (Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ (3 : Nat)) <
          ((1 - relativeError) * (1 / 4 : ℝ)) * (n : ℝ) := by
  intro n htn _hEven
  have hc : 0 < (1 - relativeError) * (1 / 4 : ℝ) := by
    have h1 : 0 < (1 - relativeError) := sub_pos.mpr hrelativeError
    have h2 : (0 : ℝ) < 1 / 4 := by norm_num
    exact mul_pos h1 h2
  have hbase :
      canonicalSqrtLogModelThreshold ((1 - relativeError) * (1 / 4 : ℝ)) hc ≤
        canonicalQuarterSqrtLogModelThreshold relativeError hrelativeError :=
    Nat.le_max_right _ _
  exact
    canonicalSqrtLogModelThreshold_spec hc n
      (le_of_lt (lt_of_le_of_lt hbase htn))

structure VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound where
  threshold : Nat
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  rawLinearLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      coefficient * (n : ℝ) ≤ RawVonMangoldtGoldbachSum n

noncomputable def
    VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound.canonicalContaminationThreshold
    (bound : VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound) :
    Nat :=
  canonicalLinearContaminationThreshold bound.coefficient bound.coefficient_pos

noncomputable def
    VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound.toSplitThresholdPositiveLinearRawWeightSumLowerBound
    (bound : VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound) :
    VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound where
  weightSumThreshold := bound.threshold
  rawThreshold := bound.threshold
  contaminationThreshold := bound.canonicalContaminationThreshold
  coefficient := bound.coefficient
  coefficient_pos := bound.coefficient_pos
  nonPrimePrimePowerWeightSumBound :=
    canonicalNonPrimePrimePowerVonMangoldtWeightSumBound
  nonPrimePrimePowerWeightSumBoundValid := by
    intro n htn hEven
    exact canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_valid
      n htn hEven
  rawLinearLowerBound := bound.rawLinearLowerBound
  contaminationDominated := by
    intro n htn _hEven
    exact canonicalLinearContaminationThreshold_spec
      bound.coefficient_pos n (le_of_lt htn)

noncomputable def
    VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound.toDirectRawWeightSumLowerBound
    (bound : VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  bound.toSplitThresholdPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound.directRawWeightSumThreshold_eq
    (bound : VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound) :
    bound.toDirectRawWeightSumLowerBound.threshold =
      max bound.threshold bound.canonicalContaminationThreshold := by
  dsimp
    [VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound.toDirectRawWeightSumLowerBound,
      VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound.toSplitThresholdPositiveLinearRawWeightSumLowerBound,
      VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound,
      VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.toPositiveLinearRawWeightSumLowerBound,
      VonMangoldtPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound,
      VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.threshold]
  rw [← Nat.max_assoc, Nat.max_self]

theorem
    VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound.directRawWeightSumThreshold_le
    {B : Nat}
    (bound : VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound)
    (hraw : bound.threshold ≤ B)
    (hcontamination : bound.canonicalContaminationThreshold ≤ B) :
    bound.toDirectRawWeightSumLowerBound.threshold ≤ B := by
  rw [bound.directRawWeightSumThreshold_eq]
  exact max_le hraw hcontamination

theorem
    count_positive_above_of_vonMangoldt_positive_linear_raw_canonical_weight_sum_lower_bound
    (bound : VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound) :
    GoldbachCountPositiveAbove
      bound.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound
    bound.toSplitThresholdPositiveLinearRawWeightSumLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_positive_linear_raw_canonical_weight_sum_lower_bound
    (bound : VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound) :
    ExplicitGoldbachLowerBound
      bound.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_positive_linear_raw_canonical_weight_sum_lower_bound
    bound

theorem
    strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_canonical_weight_sum_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound_le
    finite
    bound.toSplitThresholdPositiveLinearRawWeightSumLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_positive_linear_raw_canonical_weight_sum_lower_bound_le100
    (bound : VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_canonical_weight_sum_lower_bound_le
    goldbachUpTo100
    bound
    hthreshold

/-- **Quarter-base binary Hardy-Littlewood lower bound hypothesis.**  The
single remaining mathematical content for unconditional strong binary
Goldbach: a positive-linear lower bound on the raw von Mangoldt Goldbach
convolution by the quarter-base singular series times `n`, for every even
`n > T`. -/
def QuarterBinaryHardyLittlewoodLowerBound (T : Nat) (δ : ℝ) : Prop :=
  ∀ n : Nat, T < n → Even n →
    (1 - δ) * (goldbachSingularSeriesFromQuarter n * (n : ℝ)) ≤
      RawVonMangoldtGoldbachSum n

/-- Maximally clean conditional closure of strong binary Goldbach.  Provided

* `GoldbachUpTo B` (finite verification),
* `QuarterBinaryHardyLittlewoodLowerBound T δ` at any threshold `T ≤ B`,
* the noncomputable canonical contamination threshold (extracted from the
  asymptotic `K · √n · log(n)³ = o(n)`) is also `≤ B`,

strong Goldbach follows.  Lean handles the contamination side internally via
`Classical.choose`; the analyst only has to certify the raw von Mangoldt lower
bound, which is the open content. -/
theorem strongGoldbach_of_QuarterBinaryHardyLittlewoodLowerBound
    {T B : Nat} {δ : ℝ} (hδ : δ < 1)
    (finite : GoldbachUpTo B)
    (h : QuarterBinaryHardyLittlewoodLowerBound T δ)
    (hT : T ≤ B)
    (hContam :
      canonicalLinearContaminationThreshold ((1 - δ) / 4)
          (by
            have h1 : 0 < (1 - δ) := sub_pos.mpr hδ
            positivity) ≤ B) :
    StrongGoldbach := by
  have hcpos : 0 < (1 - δ) / 4 := by
    have h1 : 0 < (1 - δ) := sub_pos.mpr hδ
    positivity
  let bound : VonMangoldtPositiveLinearRawCanonicalWeightSumLowerBound :=
    { threshold := T
      coefficient := (1 - δ) / 4
      coefficient_pos := hcpos
      rawLinearLowerBound := by
        intro n hT_lt hEven
        have hraw := h n hT_lt hEven
        have hn_pos : 0 < n := lt_of_le_of_lt (Nat.zero_le T) hT_lt
        have hsigma : (1 / 4 : ℝ) ≤ goldbachSingularSeriesFromQuarter n :=
          one_fourth_le_goldbachSingularSeriesFromQuarter
            (threshold := 0) n hn_pos hEven
        have h1δ : 0 ≤ (1 - δ) := le_of_lt (sub_pos.mpr hδ)
        have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by positivity
        have hstep1 :
            (1 / 4 : ℝ) * (n : ℝ) ≤
              goldbachSingularSeriesFromQuarter n * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hsigma hn_nn
        have hstep2 :
            (1 - δ) * ((1 / 4 : ℝ) * (n : ℝ)) ≤
              (1 - δ) * (goldbachSingularSeriesFromQuarter n * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hstep1 h1δ
        have hrearrange :
            (1 - δ) / 4 * (n : ℝ) = (1 - δ) * ((1 / 4 : ℝ) * (n : ℝ)) := by
          ring
        rw [hrearrange]
        exact hstep2.trans hraw }
  refine strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_canonical_weight_sum_lower_bound_le
    finite bound ?_
  exact bound.directRawWeightSumThreshold_le hT hContam

structure
    VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound where
  rawThreshold : Nat
  contaminationThreshold : Nat
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  rawLinearLowerBound :
    ∀ n : Nat, rawThreshold < n → Even n →
      coefficient * (n : ℝ) ≤ RawVonMangoldtGoldbachSum n
  contaminationDominated :
    ∀ n : Nat, contaminationThreshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        coefficient * (n : ℝ)

noncomputable def
    VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound.toSplitThresholdPositiveLinearRawWeightSumLowerBound
    (bound :
      VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound) :
    VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound where
  weightSumThreshold := bound.rawThreshold
  rawThreshold := bound.rawThreshold
  contaminationThreshold := bound.contaminationThreshold
  coefficient := bound.coefficient
  coefficient_pos := bound.coefficient_pos
  nonPrimePrimePowerWeightSumBound :=
    canonicalNonPrimePrimePowerVonMangoldtWeightSumBound
  nonPrimePrimePowerWeightSumBoundValid := by
    intro n hraw hEven
    exact canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_valid
      n hraw hEven
  rawLinearLowerBound := bound.rawLinearLowerBound
  contaminationDominated := bound.contaminationDominated

noncomputable def
    VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound.toDirectRawWeightSumLowerBound
    (bound :
      VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  bound.toSplitThresholdPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound.directRawWeightSumThreshold_eq
    (bound :
      VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound) :
    bound.toDirectRawWeightSumLowerBound.threshold =
      max bound.rawThreshold bound.contaminationThreshold := by
  dsimp
    [VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound.toDirectRawWeightSumLowerBound,
      VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound.toSplitThresholdPositiveLinearRawWeightSumLowerBound,
      VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound,
      VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.toPositiveLinearRawWeightSumLowerBound,
      VonMangoldtPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound,
      VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.threshold]
  rw [← Nat.max_assoc, Nat.max_self]

theorem
    VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (bound :
      VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound)
    (hraw : bound.rawThreshold ≤ B)
    (hcontamination : bound.contaminationThreshold ≤ B) :
    bound.toDirectRawWeightSumLowerBound.threshold ≤ B := by
  rw [bound.directRawWeightSumThreshold_eq]
  exact max_le hraw hcontamination

theorem
    count_positive_above_of_vonMangoldt_positive_linear_raw_explicit_contamination_canonical_weight_sum_lower_bound
    (bound :
      VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound) :
    GoldbachCountPositiveAbove
      bound.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound
    bound.toSplitThresholdPositiveLinearRawWeightSumLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_positive_linear_raw_explicit_contamination_canonical_weight_sum_lower_bound
    (bound :
      VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound) :
    ExplicitGoldbachLowerBound
      bound.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_positive_linear_raw_explicit_contamination_canonical_weight_sum_lower_bound
    bound

theorem
    strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_explicit_contamination_canonical_weight_sum_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound :
      VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound_le
    finite
    bound.toSplitThresholdPositiveLinearRawWeightSumLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_positive_linear_raw_explicit_contamination_canonical_weight_sum_lower_bound_le100
    (bound :
      VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_explicit_contamination_canonical_weight_sum_lower_bound_le
    goldbachUpTo100
    bound
    hthreshold

structure VonMangoldtSqrtLogCountRawLowerBound where
  threshold : Nat
  rawLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      2 * vonMangoldtLogCountContaminationBudget
        nonPrimePrimePowerSqrtLogCountBound n <
        RawVonMangoldtGoldbachSum n

noncomputable def VonMangoldtSqrtLogCountRawLowerBound.toDirectRawLogCountLowerBound
    (bound : VonMangoldtSqrtLogCountRawLowerBound) :
    VonMangoldtDirectRawLogCountLowerBound where
  threshold := bound.threshold
  nonPrimePrimePowerCountBound := nonPrimePrimePowerSqrtLogCountBound
  nonPrimePrimePowerCountBoundValid := by
    intro n htn hEven
    exact nonPrimePrimePowerCount_real_le_sqrt_log_count_bound n
  rawLowerBound := by
    intro n htn hEven
    exact bound.rawLowerBound n htn hEven

noncomputable def VonMangoldtSqrtLogCountRawLowerBound.toDirectRawWeightSumLowerBound
    (bound : VonMangoldtSqrtLogCountRawLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound where
  threshold := bound.threshold
  nonPrimePrimePowerWeightSumBound :=
    fun n => nonPrimePrimePowerSqrtLogCountBound n * Real.log (n : ℝ)
  nonPrimePrimePowerWeightSumBoundValid := by
    intro n htn hEven
    have hn_pos : 0 < n := lt_of_le_of_lt (Nat.zero_le bound.threshold) htn
    exact nonPrimePrimePowerVonMangoldtWeightSum_le_sqrt_log_count_bound_mul_log
      n (Nat.succ_le_of_lt hn_pos)
  rawLowerBound := by
    intro n htn hEven
    simpa [vonMangoldtWeightSumContaminationBudget,
      vonMangoldtLogCountContaminationBudget, mul_assoc] using
      bound.rawLowerBound n htn hEven

theorem count_positive_above_of_vonMangoldt_sqrt_log_count_raw_lower_bound
    (bound : VonMangoldtSqrtLogCountRawLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_vonMangoldt_direct_raw_log_count_lower_bound
    bound.toDirectRawLogCountLowerBound

theorem strongGoldbach_of_vonMangoldt_sqrt_log_count_raw_lower_bound_le100
    (bound : VonMangoldtSqrtLogCountRawLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_direct_raw_log_count_lower_bound_le100
    bound.toDirectRawLogCountLowerBound
    (by
      simpa
        [VonMangoldtSqrtLogCountRawLowerBound.toDirectRawLogCountLowerBound]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_sqrt_log_count_raw_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtSqrtLogCountRawLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_direct_raw_log_count_lower_bound_le
    finite
    bound.toDirectRawLogCountLowerBound
    (by
      simpa
        [VonMangoldtSqrtLogCountRawLowerBound.toDirectRawLogCountLowerBound]
        using hthreshold)

structure VonMangoldtSqrtLogCountLinearRawLowerBound where
  threshold : Nat
  coefficient : ℝ
  rawLinearLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      coefficient * (n : ℝ) ≤ RawVonMangoldtGoldbachSum n
  contaminationDominated :
    ∀ n : Nat, threshold < n → Even n →
      2 * vonMangoldtLogCountContaminationBudget
        nonPrimePrimePowerSqrtLogCountBound n <
        coefficient * (n : ℝ)

noncomputable def VonMangoldtSqrtLogCountLinearRawLowerBound.toSqrtLogCountRawLowerBound
    (bound : VonMangoldtSqrtLogCountLinearRawLowerBound) :
    VonMangoldtSqrtLogCountRawLowerBound where
  threshold := bound.threshold
  rawLowerBound := by
    intro n htn hEven
    exact (bound.contaminationDominated n htn hEven).trans_le
      (bound.rawLinearLowerBound n htn hEven)

noncomputable def VonMangoldtSqrtLogCountLinearRawLowerBound.toDirectRawWeightSumLowerBound
    (bound : VonMangoldtSqrtLogCountLinearRawLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  bound.toSqrtLogCountRawLowerBound.toDirectRawWeightSumLowerBound

theorem count_positive_above_of_vonMangoldt_sqrt_log_count_linear_raw_lower_bound
    (bound : VonMangoldtSqrtLogCountLinearRawLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_vonMangoldt_sqrt_log_count_raw_lower_bound
    bound.toSqrtLogCountRawLowerBound

theorem explicit_lower_bound_of_vonMangoldt_sqrt_log_count_linear_raw_lower_bound
    (bound : VonMangoldtSqrtLogCountLinearRawLowerBound) :
    ExplicitGoldbachLowerBound bound.threshold :=
  count_positive_above_of_vonMangoldt_sqrt_log_count_linear_raw_lower_bound
    bound

theorem strongGoldbach_of_vonMangoldt_sqrt_log_count_linear_raw_lower_bound_le100
    (bound : VonMangoldtSqrtLogCountLinearRawLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_sqrt_log_count_raw_lower_bound_le100
    bound.toSqrtLogCountRawLowerBound
    (by
      simpa
        [VonMangoldtSqrtLogCountLinearRawLowerBound.toSqrtLogCountRawLowerBound]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_sqrt_log_count_linear_raw_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtSqrtLogCountLinearRawLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_sqrt_log_count_raw_lower_bound_le
    finite
    bound.toSqrtLogCountRawLowerBound
    (by
      simpa
        [VonMangoldtSqrtLogCountLinearRawLowerBound.toSqrtLogCountRawLowerBound]
        using hthreshold)

noncomputable def vonMangoldtSqrtLogCountBudgetDominationThreshold
    (c : ℝ) (hc : 0 < c) : Nat :=
  Classical.choose
    (show ∃ N : Nat, ∀ n : Nat, N ≤ n →
        2 * vonMangoldtLogCountContaminationBudget
          nonPrimePrimePowerSqrtLogCountBound n < c * (n : ℝ) by
      simpa [Filter.eventually_atTop] using
        eventually_vonMangoldt_sqrt_log_count_budget_lt_const_mul_linear
          (c := c) hc)

theorem vonMangoldtSqrtLogCountBudget_lt_const_mul_linear_of_ge_threshold
    {c : ℝ} (hc : 0 < c) :
    ∀ n : Nat,
      vonMangoldtSqrtLogCountBudgetDominationThreshold c hc ≤ n →
        2 * vonMangoldtLogCountContaminationBudget
          nonPrimePrimePowerSqrtLogCountBound n < c * (n : ℝ) :=
  Classical.choose_spec
    (show ∃ N : Nat, ∀ n : Nat, N ≤ n →
        2 * vonMangoldtLogCountContaminationBudget
          nonPrimePrimePowerSqrtLogCountBound n < c * (n : ℝ) by
      simpa [Filter.eventually_atTop] using
        eventually_vonMangoldt_sqrt_log_count_budget_lt_const_mul_linear
          (c := c) hc)

structure VonMangoldtPositiveLinearRawLowerBound where
  threshold : Nat
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  rawLinearLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      coefficient * (n : ℝ) ≤ RawVonMangoldtGoldbachSum n

noncomputable def VonMangoldtPositiveLinearRawLowerBound.toSqrtLogCountLinearRawLowerBound
    (bound : VonMangoldtPositiveLinearRawLowerBound) :
    VonMangoldtSqrtLogCountLinearRawLowerBound where
  threshold :=
    max bound.threshold
      (vonMangoldtSqrtLogCountBudgetDominationThreshold
        bound.coefficient bound.coefficient_pos)
  coefficient := bound.coefficient
  rawLinearLowerBound := by
    intro n htn hEven
    exact bound.rawLinearLowerBound n
      (lt_of_le_of_lt
        (Nat.le_max_left bound.threshold
          (vonMangoldtSqrtLogCountBudgetDominationThreshold
            bound.coefficient bound.coefficient_pos))
        htn)
      hEven
  contaminationDominated := by
    intro n htn hEven
    exact
      vonMangoldtSqrtLogCountBudget_lt_const_mul_linear_of_ge_threshold
        bound.coefficient_pos n
        ((Nat.le_max_right bound.threshold
          (vonMangoldtSqrtLogCountBudgetDominationThreshold
            bound.coefficient bound.coefficient_pos)).trans
          (le_of_lt htn))

noncomputable def VonMangoldtPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound
    (bound : VonMangoldtPositiveLinearRawLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  bound.toSqrtLogCountLinearRawLowerBound.toDirectRawWeightSumLowerBound

theorem count_positive_above_of_vonMangoldt_positive_linear_raw_lower_bound
    (bound : VonMangoldtPositiveLinearRawLowerBound) :
    GoldbachCountPositiveAbove
      bound.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_sqrt_log_count_linear_raw_lower_bound
    bound.toSqrtLogCountLinearRawLowerBound

theorem explicit_lower_bound_of_vonMangoldt_positive_linear_raw_lower_bound
    (bound : VonMangoldtPositiveLinearRawLowerBound) :
    ExplicitGoldbachLowerBound
      bound.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_positive_linear_raw_lower_bound bound

theorem strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtPositiveLinearRawLowerBound)
    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_sqrt_log_count_linear_raw_lower_bound_le
    finite
    bound.toSqrtLogCountLinearRawLowerBound
    hthreshold

theorem strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_lower_bound_weight_sum_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtPositiveLinearRawLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_direct_raw_weight_sum_lower_bound_le
    finite
    bound.toDirectRawWeightSumLowerBound
    hthreshold

structure VonMangoldtEventuallyPositiveLinearRawLowerBound where
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  rawLinearLowerBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      coefficient * (n : ℝ) ≤ RawVonMangoldtGoldbachSum n

noncomputable def vonMangoldtEventuallyPositiveLinearRawLowerBoundThreshold
    (bound : VonMangoldtEventuallyPositiveLinearRawLowerBound) : Nat :=
  Classical.choose
    (show ∃ N : Nat, ∀ n : Nat, N ≤ n → Even n →
        bound.coefficient * (n : ℝ) ≤ RawVonMangoldtGoldbachSum n by
      simpa [Filter.eventually_atTop] using
        bound.rawLinearLowerBoundEventually)

theorem vonMangoldtEventuallyPositiveLinearRawLowerBound_ge_threshold
    (bound : VonMangoldtEventuallyPositiveLinearRawLowerBound) :
    ∀ n : Nat,
      vonMangoldtEventuallyPositiveLinearRawLowerBoundThreshold bound ≤ n →
        Even n →
          bound.coefficient * (n : ℝ) ≤ RawVonMangoldtGoldbachSum n :=
  Classical.choose_spec
    (show ∃ N : Nat, ∀ n : Nat, N ≤ n → Even n →
        bound.coefficient * (n : ℝ) ≤ RawVonMangoldtGoldbachSum n by
      simpa [Filter.eventually_atTop] using
        bound.rawLinearLowerBoundEventually)

noncomputable def VonMangoldtEventuallyPositiveLinearRawLowerBound.toPositiveLinearRawLowerBound
    (bound : VonMangoldtEventuallyPositiveLinearRawLowerBound) :
    VonMangoldtPositiveLinearRawLowerBound where
  threshold := vonMangoldtEventuallyPositiveLinearRawLowerBoundThreshold bound
  coefficient := bound.coefficient
  coefficient_pos := bound.coefficient_pos
  rawLinearLowerBound := by
    intro n htn hEven
    exact
      vonMangoldtEventuallyPositiveLinearRawLowerBound_ge_threshold bound n
        (le_of_lt htn) hEven

noncomputable def
    VonMangoldtEventuallyPositiveLinearRawLowerBound.toSqrtLogCountLinearRawLowerBound
    (bound : VonMangoldtEventuallyPositiveLinearRawLowerBound) :
    VonMangoldtSqrtLogCountLinearRawLowerBound :=
  bound.toPositiveLinearRawLowerBound.toSqrtLogCountLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound
    (bound : VonMangoldtEventuallyPositiveLinearRawLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  bound.toPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound

theorem count_positive_above_of_vonMangoldt_eventually_positive_linear_raw_lower_bound
    (bound : VonMangoldtEventuallyPositiveLinearRawLowerBound) :
    GoldbachCountPositiveAbove
      bound.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_sqrt_log_count_linear_raw_lower_bound
    bound.toSqrtLogCountLinearRawLowerBound

theorem explicit_lower_bound_of_vonMangoldt_eventually_positive_linear_raw_lower_bound
    (bound : VonMangoldtEventuallyPositiveLinearRawLowerBound) :
    ExplicitGoldbachLowerBound
      bound.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_positive_linear_raw_lower_bound
    bound

theorem strongGoldbach_of_finite_and_vonMangoldt_eventually_positive_linear_raw_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtEventuallyPositiveLinearRawLowerBound)
    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_sqrt_log_count_linear_raw_lower_bound_le
    finite
    bound.toSqrtLogCountLinearRawLowerBound
    hthreshold

theorem strongGoldbach_of_finite_and_vonMangoldt_eventually_positive_linear_raw_lower_bound_weight_sum_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtEventuallyPositiveLinearRawLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_direct_raw_weight_sum_lower_bound_le
    finite
    bound.toDirectRawWeightSumLowerBound
    hthreshold

structure VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound where
  coefficient : ℝ
  relativeError : ℝ
  coefficient_pos : 0 < coefficient
  relativeError_lt_one : relativeError < 1
  mainTerm : Nat → ℝ
  mainTermLowerBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      coefficient * (n : ℝ) ≤ mainTerm n
  rawRelativeLowerBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      (1 - relativeError) * mainTerm n ≤ RawVonMangoldtGoldbachSum n

def
    VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound.effectiveCoefficient
    (bound :
      VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound) :
    ℝ :=
  (1 - bound.relativeError) * bound.coefficient

theorem
    VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound.effectiveCoefficient_pos
    (bound :
      VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound) :
    0 < bound.effectiveCoefficient := by
  dsimp
    [VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound.effectiveCoefficient]
  have hfactor : 0 < 1 - bound.relativeError := by
    linarith [bound.relativeError_lt_one]
  exact mul_pos hfactor bound.coefficient_pos

noncomputable def
    VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound.toEventuallyPositiveLinearRawLowerBound
    (bound :
      VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound) :
    VonMangoldtEventuallyPositiveLinearRawLowerBound where
  coefficient := bound.effectiveCoefficient
  coefficient_pos := bound.effectiveCoefficient_pos
  rawLinearLowerBoundEventually := by
    filter_upwards
      [bound.mainTermLowerBoundEventually,
        bound.rawRelativeLowerBoundEventually] with n hmain hraw hEven
    have hfactor_nonneg : 0 ≤ 1 - bound.relativeError := by
      linarith [bound.relativeError_lt_one]
    have hscaled :
        (1 - bound.relativeError) * (bound.coefficient * (n : ℝ)) ≤
          (1 - bound.relativeError) * bound.mainTerm n :=
      mul_le_mul_of_nonneg_left (hmain hEven) hfactor_nonneg
    calc
      bound.effectiveCoefficient * (n : ℝ)
          = (1 - bound.relativeError) *
              (bound.coefficient * (n : ℝ)) := by
            rw
              [VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound.effectiveCoefficient]
            ring
      _ ≤ (1 - bound.relativeError) * bound.mainTerm n := hscaled
      _ ≤ RawVonMangoldtGoldbachSum n := hraw hEven

noncomputable def
    VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound.toSqrtLogCountLinearRawLowerBound
    (bound :
      VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound) :
    VonMangoldtSqrtLogCountLinearRawLowerBound :=
  bound.toEventuallyPositiveLinearRawLowerBound.toSqrtLogCountLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound
    (bound :
      VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  bound.toEventuallyPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound

theorem
    count_positive_above_of_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound
    (bound :
      VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound) :
    GoldbachCountPositiveAbove
      bound.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_positive_linear_raw_lower_bound
    bound.toEventuallyPositiveLinearRawLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound
    (bound :
      VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound) :
    ExplicitGoldbachLowerBound
      bound.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound
    bound

theorem
    strongGoldbach_of_finite_and_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound :
      VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_positive_linear_raw_lower_bound_le
    finite
    bound.toEventuallyPositiveLinearRawLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound_le100
    (bound :
      VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound_le
    goldbachUpTo100
    bound
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound_weight_sum_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound :
      VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_positive_linear_raw_lower_bound_weight_sum_le
    finite
    bound.toEventuallyPositiveLinearRawLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound_weight_sum_le100
    (bound :
      VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound_weight_sum_le
    goldbachUpTo100
    bound
    hthreshold

structure VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound where
  coefficient : ℝ
  relativeError : ℝ
  coefficient_pos : 0 < coefficient
  relativeError_lt_one : relativeError < 1
  mainTerm : Nat → ℝ
  mainTermLowerBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      coefficient * (n : ℝ) ≤ mainTerm n
  rawAbsErrorBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      |RawVonMangoldtGoldbachSum n - mainTerm n| ≤
        relativeError * mainTerm n

noncomputable def
    VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound.toEventuallyRelativeErrorPositiveLinearRawLowerBound
    (bound :
      VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound) :
    VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound where
  coefficient := bound.coefficient
  relativeError := bound.relativeError
  coefficient_pos := bound.coefficient_pos
  relativeError_lt_one := bound.relativeError_lt_one
  mainTerm := bound.mainTerm
  mainTermLowerBoundEventually := bound.mainTermLowerBoundEventually
  rawRelativeLowerBoundEventually := by
    filter_upwards [bound.rawAbsErrorBoundEventually] with n herr hEven
    have hlow :
        -(bound.relativeError * bound.mainTerm n) ≤
          RawVonMangoldtGoldbachSum n - bound.mainTerm n :=
      (abs_le.mp (herr hEven)).1
    have hraw :
        bound.mainTerm n - bound.relativeError * bound.mainTerm n ≤
          RawVonMangoldtGoldbachSum n := by
      linarith
    calc
      (1 - bound.relativeError) * bound.mainTerm n
          = bound.mainTerm n - bound.relativeError * bound.mainTerm n := by
            ring
      _ ≤ RawVonMangoldtGoldbachSum n := hraw

noncomputable def
    VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound.toEventuallyPositiveLinearRawLowerBound
    (bound :
      VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound) :
    VonMangoldtEventuallyPositiveLinearRawLowerBound :=
  bound.toEventuallyRelativeErrorPositiveLinearRawLowerBound.toEventuallyPositiveLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound.toSqrtLogCountLinearRawLowerBound
    (bound :
      VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound) :
    VonMangoldtSqrtLogCountLinearRawLowerBound :=
  bound.toEventuallyRelativeErrorPositiveLinearRawLowerBound.toSqrtLogCountLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound
    (bound :
      VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  bound.toEventuallyRelativeErrorPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound

theorem
    count_positive_above_of_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound
    (bound :
      VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound) :
    GoldbachCountPositiveAbove
      bound.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound
    bound.toEventuallyRelativeErrorPositiveLinearRawLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound
    (bound :
      VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound) :
    ExplicitGoldbachLowerBound
      bound.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound
    bound

theorem
    strongGoldbach_of_finite_and_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound :
      VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound_le
    finite
    bound.toEventuallyRelativeErrorPositiveLinearRawLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound_le100
    (bound :
      VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound_le
    goldbachUpTo100
    bound
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound_weight_sum_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound :
      VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_relative_error_positive_linear_raw_lower_bound_weight_sum_le
    finite
    bound.toEventuallyRelativeErrorPositiveLinearRawLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound_weight_sum_le100
    (bound :
      VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound_weight_sum_le
    goldbachUpTo100
    bound
    hthreshold

structure VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound where
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  mainTerm : Nat → ℝ
  mainTermLowerBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      coefficient * (n : ℝ) ≤ mainTerm n
  rawAbsErrorLittleO :
    (fun n : Nat => |RawVonMangoldtGoldbachSum n - mainTerm n|)
      =o[Filter.atTop] mainTerm

noncomputable def
    VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound.toEventuallyAbsErrorPositiveLinearRawLowerBound
    (bound :
      VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound) :
    VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound where
  coefficient := bound.coefficient
  relativeError := (1 / 2 : ℝ)
  coefficient_pos := bound.coefficient_pos
  relativeError_lt_one := by norm_num
  mainTerm := bound.mainTerm
  mainTermLowerBoundEventually := bound.mainTermLowerBoundEventually
  rawAbsErrorBoundEventually := by
    have hsmall :
        ∀ᶠ n : Nat in Filter.atTop,
          ‖|RawVonMangoldtGoldbachSum n - bound.mainTerm n|‖ ≤
            (1 / 2 : ℝ) * ‖bound.mainTerm n‖ :=
      bound.rawAbsErrorLittleO.def (by norm_num)
    filter_upwards [bound.mainTermLowerBoundEventually, hsmall] with n hmain hsmall hEven
    have hmain_nonneg : 0 ≤ bound.mainTerm n := by
      exact le_trans
        (mul_nonneg bound.coefficient_pos.le (Nat.cast_nonneg n))
        (hmain hEven)
    simpa [Real.norm_eq_abs, abs_of_nonneg hmain_nonneg] using hsmall

noncomputable def
    VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound.toEventuallyRelativeErrorPositiveLinearRawLowerBound
    (bound :
      VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound) :
    VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound :=
  bound.toEventuallyAbsErrorPositiveLinearRawLowerBound.toEventuallyRelativeErrorPositiveLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound.toEventuallyPositiveLinearRawLowerBound
    (bound :
      VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound) :
    VonMangoldtEventuallyPositiveLinearRawLowerBound :=
  bound.toEventuallyAbsErrorPositiveLinearRawLowerBound.toEventuallyPositiveLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound.toSqrtLogCountLinearRawLowerBound
    (bound :
      VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound) :
    VonMangoldtSqrtLogCountLinearRawLowerBound :=
  bound.toEventuallyAbsErrorPositiveLinearRawLowerBound.toSqrtLogCountLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound
    (bound :
      VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  bound.toEventuallyAbsErrorPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound

theorem
    count_positive_above_of_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound
    (bound :
      VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound) :
    GoldbachCountPositiveAbove
      bound.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound
    bound.toEventuallyAbsErrorPositiveLinearRawLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound
    (bound :
      VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound) :
    ExplicitGoldbachLowerBound
      bound.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound
    bound

theorem
    strongGoldbach_of_finite_and_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound :
      VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound_le
    finite
    bound.toEventuallyAbsErrorPositiveLinearRawLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound_le100
    (bound :
      VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound_le
    goldbachUpTo100
    bound
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound_weight_sum_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound :
      VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound_weight_sum_le
    finite
    bound.toEventuallyAbsErrorPositiveLinearRawLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound_weight_sum_le100
    (bound :
      VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound_weight_sum_le
    goldbachUpTo100
    bound
    hthreshold

structure VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound where
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  mainTerm : Nat → ℝ
  mainTermLowerBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      coefficient * (n : ℝ) ≤ mainTerm n
  rawAsymptoticEquivalent :
    Asymptotics.IsEquivalent
      Filter.atTop
      (fun n : Nat => RawVonMangoldtGoldbachSum n)
      mainTerm

noncomputable def
    VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound.toEventuallyLittleOAbsErrorPositiveLinearRawLowerBound
    (bound :
      VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound) :
    VonMangoldtEventuallyLittleOAbsErrorPositiveLinearRawLowerBound where
  coefficient := bound.coefficient
  coefficient_pos := bound.coefficient_pos
  mainTerm := bound.mainTerm
  mainTermLowerBoundEventually := bound.mainTermLowerBoundEventually
  rawAbsErrorLittleO := by
    have hdiff :
        (fun n : Nat => RawVonMangoldtGoldbachSum n - bound.mainTerm n)
          =o[Filter.atTop] bound.mainTerm := by
      simpa [Pi.sub_apply] using
        (Asymptotics.IsEquivalent.isLittleO bound.rawAsymptoticEquivalent)
    refine Asymptotics.IsLittleO.of_bound ?_
    intro c hc
    have hsmall := hdiff.def hc
    filter_upwards [hsmall] with n hsmall_n
    simpa [Real.norm_eq_abs, abs_abs] using hsmall_n

noncomputable def
    VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound.toEventuallyAbsErrorPositiveLinearRawLowerBound
    (bound :
      VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound) :
    VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound :=
  bound.toEventuallyLittleOAbsErrorPositiveLinearRawLowerBound.toEventuallyAbsErrorPositiveLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound.toEventuallyRelativeErrorPositiveLinearRawLowerBound
    (bound :
      VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound) :
    VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound :=
  bound.toEventuallyAbsErrorPositiveLinearRawLowerBound.toEventuallyRelativeErrorPositiveLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound.toEventuallyPositiveLinearRawLowerBound
    (bound :
      VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound) :
    VonMangoldtEventuallyPositiveLinearRawLowerBound :=
  bound.toEventuallyAbsErrorPositiveLinearRawLowerBound.toEventuallyPositiveLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound.toSqrtLogCountLinearRawLowerBound
    (bound :
      VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound) :
    VonMangoldtSqrtLogCountLinearRawLowerBound :=
  bound.toEventuallyAbsErrorPositiveLinearRawLowerBound.toSqrtLogCountLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound
    (bound :
      VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  bound.toEventuallyAbsErrorPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound

theorem
    count_positive_above_of_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound
    (bound :
      VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound) :
    GoldbachCountPositiveAbove
      bound.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound
    bound.toEventuallyLittleOAbsErrorPositiveLinearRawLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound
    (bound :
      VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound) :
    ExplicitGoldbachLowerBound
      bound.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound
    bound

theorem
    strongGoldbach_of_finite_and_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound :
      VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound)
    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound_le
    finite
    bound.toEventuallyLittleOAbsErrorPositiveLinearRawLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound_le100
    (bound :
      VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound)
    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound_le
    goldbachUpTo100
    bound
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound_weight_sum_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound :
      VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_little_o_abs_error_positive_linear_raw_lower_bound_weight_sum_le
    finite
    bound.toEventuallyLittleOAbsErrorPositiveLinearRawLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound_weight_sum_le100
    (bound :
      VonMangoldtEventuallyAsymptoticEquivalentPositiveLinearRawLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_asymptotic_equivalent_positive_linear_raw_lower_bound_weight_sum_le
    goldbachUpTo100
    bound
    hthreshold

structure VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound where
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  mainTerm : Nat → ℝ
  mainTermLowerBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      coefficient * (n : ℝ) ≤ mainTerm n
  rawNormalizedErrorTendstoZero :
    Filter.Tendsto
      (fun n : Nat =>
        (RawVonMangoldtGoldbachSum n - mainTerm n) / mainTerm n)
      Filter.atTop
      (nhds (0 : ℝ))

noncomputable def
    VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound.toEventuallyAbsErrorPositiveLinearRawLowerBound
    (bound :
      VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound) :
    VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound where
  coefficient := bound.coefficient
  relativeError := (1 / 2 : ℝ)
  coefficient_pos := bound.coefficient_pos
  relativeError_lt_one := by norm_num
  mainTerm := bound.mainTerm
  mainTermLowerBoundEventually := bound.mainTermLowerBoundEventually
  rawAbsErrorBoundEventually := by
    have hball :
        ∀ᶠ n : Nat in Filter.atTop,
          (RawVonMangoldtGoldbachSum n - bound.mainTerm n) /
              bound.mainTerm n ∈
            Metric.closedBall (0 : ℝ) (1 / 2 : ℝ) :=
      bound.rawNormalizedErrorTendstoZero.eventually
        (Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num))
    have hsmall :
        ∀ᶠ n : Nat in Filter.atTop,
          |RawVonMangoldtGoldbachSum n - bound.mainTerm n| /
              |bound.mainTerm n| ≤ (1 / 2 : ℝ) := by
      filter_upwards [hball] with n hn
      simpa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hn
    filter_upwards
      [bound.mainTermLowerBoundEventually,
        hsmall,
        Filter.eventually_ge_atTop (1 : Nat)] with n hmain hsmall hn hEven
    have hn_pos_nat : 0 < n := Nat.succ_le_iff.mp hn
    have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn_pos_nat
    have hmain_pos : 0 < bound.mainTerm n :=
      lt_of_lt_of_le
        (mul_pos bound.coefficient_pos hn_pos)
        (hmain hEven)
    have hmain_ne : bound.mainTerm n ≠ 0 := ne_of_gt hmain_pos
    rw [abs_of_pos hmain_pos] at hsmall
    have hmul :=
      mul_le_mul_of_nonneg_right hsmall hmain_pos.le
    rw [div_mul_cancel₀ _ hmain_ne] at hmul
    exact hmul

noncomputable def
    VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound.toEventuallyRelativeErrorPositiveLinearRawLowerBound
    (bound :
      VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound) :
    VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound :=
  bound.toEventuallyAbsErrorPositiveLinearRawLowerBound.toEventuallyRelativeErrorPositiveLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound.toEventuallyPositiveLinearRawLowerBound
    (bound :
      VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound) :
    VonMangoldtEventuallyPositiveLinearRawLowerBound :=
  bound.toEventuallyAbsErrorPositiveLinearRawLowerBound.toEventuallyPositiveLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound.toSqrtLogCountLinearRawLowerBound
    (bound :
      VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound) :
    VonMangoldtSqrtLogCountLinearRawLowerBound :=
  bound.toEventuallyAbsErrorPositiveLinearRawLowerBound.toSqrtLogCountLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound
    (bound :
      VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  bound.toEventuallyAbsErrorPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound

theorem
    count_positive_above_of_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound
    (bound :
      VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound) :
    GoldbachCountPositiveAbove
      bound.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound
    bound.toEventuallyAbsErrorPositiveLinearRawLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound
    (bound :
      VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound) :
    ExplicitGoldbachLowerBound
      bound.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound
    bound

theorem
    strongGoldbach_of_finite_and_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound :
      VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound_le
    finite
    bound.toEventuallyAbsErrorPositiveLinearRawLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound_le100
    (bound :
      VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toSqrtLogCountLinearRawLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound_le
    goldbachUpTo100
    bound
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound_weight_sum_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound :
      VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_abs_error_positive_linear_raw_lower_bound_weight_sum_le
    finite
    bound.toEventuallyAbsErrorPositiveLinearRawLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound_weight_sum_le100
    (bound :
      VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound)
    (hthreshold : bound.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound_weight_sum_le
    goldbachUpTo100
    bound
    hthreshold

structure VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate where
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  singularSeries : Nat → ℝ
  singularSeriesLowerBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      coefficient ≤ singularSeries n
  rawNormalizedErrorTendstoZero :
    Filter.Tendsto
      (fun n : Nat =>
        (RawVonMangoldtGoldbachSum n -
            singularSeries n * (n : ℝ)) /
          (singularSeries n * (n : ℝ)))
      Filter.atTop
      (nhds (0 : ℝ))

noncomputable def
    VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate.mainTerm
    (estimate :
      VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate) :
    Nat → ℝ :=
  fun n => estimate.singularSeries n * (n : ℝ)

noncomputable def
    VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate.toEventuallyNormalizedErrorPositiveLinearRawLowerBound
    (estimate :
      VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate) :
    VonMangoldtEventuallyNormalizedErrorPositiveLinearRawLowerBound where
  coefficient := estimate.coefficient
  coefficient_pos := estimate.coefficient_pos
  mainTerm := estimate.mainTerm
  mainTermLowerBoundEventually := by
    filter_upwards
      [estimate.singularSeriesLowerBoundEventually] with n hseries hEven
    exact
      mul_le_mul_of_nonneg_right (hseries hEven) (Nat.cast_nonneg n)
  rawNormalizedErrorTendstoZero := by
    simpa
      [VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate.mainTerm]
      using estimate.rawNormalizedErrorTendstoZero

noncomputable def
    VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate.toEventuallyAbsErrorPositiveLinearRawLowerBound
    (estimate :
      VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate) :
    VonMangoldtEventuallyAbsErrorPositiveLinearRawLowerBound :=
  estimate.toEventuallyNormalizedErrorPositiveLinearRawLowerBound.toEventuallyAbsErrorPositiveLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate.toEventuallyRelativeErrorPositiveLinearRawLowerBound
    (estimate :
      VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate) :
    VonMangoldtEventuallyRelativeErrorPositiveLinearRawLowerBound :=
  estimate.toEventuallyNormalizedErrorPositiveLinearRawLowerBound.toEventuallyRelativeErrorPositiveLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate.toEventuallyPositiveLinearRawLowerBound
    (estimate :
      VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate) :
    VonMangoldtEventuallyPositiveLinearRawLowerBound :=
  estimate.toEventuallyNormalizedErrorPositiveLinearRawLowerBound.toEventuallyPositiveLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate.toSqrtLogCountLinearRawLowerBound
    (estimate :
      VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate) :
    VonMangoldtSqrtLogCountLinearRawLowerBound :=
  estimate.toEventuallyNormalizedErrorPositiveLinearRawLowerBound.toSqrtLogCountLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toEventuallyNormalizedErrorPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound

theorem
    count_positive_above_of_vonMangoldt_eventually_hardy_littlewood_normalized_estimate
    (estimate :
      VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate) :
    GoldbachCountPositiveAbove
      estimate.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound
    estimate.toEventuallyNormalizedErrorPositiveLinearRawLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_eventually_hardy_littlewood_normalized_estimate
    (estimate :
      VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_hardy_littlewood_normalized_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_eventually_hardy_littlewood_normalized_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate)
    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound_le
    finite
    estimate.toEventuallyNormalizedErrorPositiveLinearRawLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_eventually_hardy_littlewood_normalized_estimate_le100
    (estimate :
      VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate)
    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_hardy_littlewood_normalized_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_eventually_hardy_littlewood_normalized_estimate_weight_sum_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_normalized_error_positive_linear_raw_lower_bound_weight_sum_le
    finite
    estimate.toEventuallyNormalizedErrorPositiveLinearRawLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_eventually_hardy_littlewood_normalized_estimate_weight_sum_le100
    (estimate :
      VonMangoldtEventuallyHardyLittlewoodNormalizedEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_hardy_littlewood_normalized_estimate_weight_sum_le
    goldbachUpTo100
    estimate
    hthreshold

structure VonMangoldtHardyLittlewoodNormalizedEstimate where
  threshold : Nat
  coefficient : ℝ
  relativeError : ℝ
  coefficient_pos : 0 < coefficient
  relativeError_lt_one : relativeError < 1
  singularSeries : Nat → ℝ
  singularSeriesLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      coefficient ≤ singularSeries n
  rawNormalizedErrorBound :
    ∀ n : Nat, threshold < n → Even n →
      |(RawVonMangoldtGoldbachSum n -
          singularSeries n * (n : ℝ)) /
        (singularSeries n * (n : ℝ))| ≤ relativeError

def
    VonMangoldtHardyLittlewoodNormalizedEstimate.effectiveCoefficient
    (estimate : VonMangoldtHardyLittlewoodNormalizedEstimate) :
    ℝ :=
  (1 - estimate.relativeError) * estimate.coefficient

theorem
    VonMangoldtHardyLittlewoodNormalizedEstimate.effectiveCoefficient_pos
    (estimate : VonMangoldtHardyLittlewoodNormalizedEstimate) :
    0 < estimate.effectiveCoefficient := by
  dsimp [VonMangoldtHardyLittlewoodNormalizedEstimate.effectiveCoefficient]
  have hfactor : 0 < 1 - estimate.relativeError := by
    linarith [estimate.relativeError_lt_one]
  exact mul_pos hfactor estimate.coefficient_pos

noncomputable def
    VonMangoldtHardyLittlewoodNormalizedEstimate.toPositiveLinearRawLowerBound
    (estimate : VonMangoldtHardyLittlewoodNormalizedEstimate) :
    VonMangoldtPositiveLinearRawLowerBound where
  threshold := estimate.threshold
  coefficient := estimate.effectiveCoefficient
  coefficient_pos := estimate.effectiveCoefficient_pos
  rawLinearLowerBound := by
    intro n htn hEven
    let M : ℝ := estimate.singularSeries n * (n : ℝ)
    have hn_pos_nat : 0 < n :=
      Nat.lt_of_le_of_lt (Nat.zero_le estimate.threshold) htn
    have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn_pos_nat
    have hseries :
        estimate.coefficient ≤ estimate.singularSeries n :=
      estimate.singularSeriesLowerBound n htn hEven
    have hseries_pos : 0 < estimate.singularSeries n :=
      lt_of_lt_of_le estimate.coefficient_pos hseries
    have hM_pos : 0 < M := by
      dsimp [M]
      exact mul_pos hseries_pos hn_pos
    have hM_ne : M ≠ 0 := ne_of_gt hM_pos
    have hnorm :
        |(RawVonMangoldtGoldbachSum n -
            estimate.singularSeries n * (n : ℝ)) / M| ≤
          estimate.relativeError := by
      simpa [M] using estimate.rawNormalizedErrorBound n htn hEven
    have hlow_div :
        -estimate.relativeError ≤
          (RawVonMangoldtGoldbachSum n -
            estimate.singularSeries n * (n : ℝ)) / M :=
      (abs_le.mp hnorm).1
    have hmul :=
      mul_le_mul_of_nonneg_right hlow_div hM_pos.le
    rw [div_mul_cancel₀ _ hM_ne] at hmul
    have hraw_relative :
        (1 - estimate.relativeError) * M ≤
          RawVonMangoldtGoldbachSum n := by
      calc
        (1 - estimate.relativeError) * M
            = M + (-estimate.relativeError) * M := by ring
        _ ≤ M +
            (RawVonMangoldtGoldbachSum n -
              estimate.singularSeries n * (n : ℝ)) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left hmul M
        _ = RawVonMangoldtGoldbachSum n := by
              dsimp [M]
              ring
    have hmain_linear : estimate.coefficient * (n : ℝ) ≤ M := by
      dsimp [M]
      exact mul_le_mul_of_nonneg_right hseries (Nat.cast_nonneg n)
    have hfactor_nonneg : 0 ≤ 1 - estimate.relativeError := by
      linarith [estimate.relativeError_lt_one]
    calc
      estimate.effectiveCoefficient * (n : ℝ)
          = (1 - estimate.relativeError) *
              (estimate.coefficient * (n : ℝ)) := by
            rw [VonMangoldtHardyLittlewoodNormalizedEstimate.effectiveCoefficient]
            ring
      _ ≤ (1 - estimate.relativeError) * M :=
            mul_le_mul_of_nonneg_left hmain_linear hfactor_nonneg
      _ ≤ RawVonMangoldtGoldbachSum n := hraw_relative

noncomputable def
    VonMangoldtHardyLittlewoodNormalizedEstimate.toSqrtLogCountLinearRawLowerBound
    (estimate : VonMangoldtHardyLittlewoodNormalizedEstimate) :
    VonMangoldtSqrtLogCountLinearRawLowerBound :=
  estimate.toPositiveLinearRawLowerBound.toSqrtLogCountLinearRawLowerBound

noncomputable def
    VonMangoldtHardyLittlewoodNormalizedEstimate.toDirectRawWeightSumLowerBound
    (estimate : VonMangoldtHardyLittlewoodNormalizedEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound

theorem
    count_positive_above_of_vonMangoldt_hardy_littlewood_normalized_estimate
    (estimate : VonMangoldtHardyLittlewoodNormalizedEstimate) :
    GoldbachCountPositiveAbove
      estimate.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_positive_linear_raw_lower_bound
    estimate.toPositiveLinearRawLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_hardy_littlewood_normalized_estimate
    (estimate : VonMangoldtHardyLittlewoodNormalizedEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_hardy_littlewood_normalized_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtHardyLittlewoodNormalizedEstimate)
    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_lower_bound_le
    finite
    estimate.toPositiveLinearRawLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_hardy_littlewood_normalized_estimate_le100
    (estimate : VonMangoldtHardyLittlewoodNormalizedEstimate)
    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_estimate_weight_sum_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtHardyLittlewoodNormalizedEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_lower_bound_weight_sum_le
    finite
    estimate.toPositiveLinearRawLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_hardy_littlewood_normalized_estimate_weight_sum_le100
    (estimate : VonMangoldtHardyLittlewoodNormalizedEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_estimate_weight_sum_le
    goldbachUpTo100
    estimate
    hthreshold

theorem raw_normalized_error_bound_of_hardy_littlewood_abs_error_bound
    {threshold : Nat} {coefficient relativeError : ℝ}
    (hcoefficient : 0 < coefficient)
    {singularSeries : Nat → ℝ}
    (hsingular :
      ∀ n : Nat, threshold < n → Even n →
        coefficient ≤ singularSeries n)
    (habserr :
      ∀ n : Nat, threshold < n → Even n →
        |RawVonMangoldtGoldbachSum n -
            singularSeries n * (n : ℝ)| ≤
          relativeError * (singularSeries n * (n : ℝ))) :
    ∀ n : Nat, threshold < n → Even n →
      |(RawVonMangoldtGoldbachSum n -
          singularSeries n * (n : ℝ)) /
        (singularSeries n * (n : ℝ))| ≤ relativeError := by
  intro n htn hEven
  let M : ℝ := singularSeries n * (n : ℝ)
  have hn_pos_nat : 0 < n :=
    Nat.lt_of_le_of_lt (Nat.zero_le threshold) htn
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn_pos_nat
  have hseries : coefficient ≤ singularSeries n :=
    hsingular n htn hEven
  have hseries_pos : 0 < singularSeries n :=
    lt_of_lt_of_le hcoefficient hseries
  have hM_pos : 0 < M := by
    dsimp [M]
    exact mul_pos hseries_pos hn_pos
  have hM_abs : |M| = M := abs_of_pos hM_pos
  have herr := habserr n htn hEven
  have hdiv :
      |RawVonMangoldtGoldbachSum n -
          singularSeries n * (n : ℝ)| / M ≤ relativeError := by
    rw [div_le_iff₀ hM_pos]
    simpa [M] using herr
  calc
    |(RawVonMangoldtGoldbachSum n -
          singularSeries n * (n : ℝ)) /
        (singularSeries n * (n : ℝ))|
        = |RawVonMangoldtGoldbachSum n -
            singularSeries n * (n : ℝ)| / M := by
          simp [M, abs_div, hM_abs]
    _ ≤ relativeError := hdiv

structure VonMangoldtHardyLittlewoodAbsErrorEstimate where
  threshold : Nat
  coefficient : ℝ
  relativeError : ℝ
  coefficient_pos : 0 < coefficient
  relativeError_lt_one : relativeError < 1
  singularSeries : Nat → ℝ
  singularSeriesLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      coefficient ≤ singularSeries n
  rawAbsErrorBound :
    ∀ n : Nat, threshold < n → Even n →
      |RawVonMangoldtGoldbachSum n -
          singularSeries n * (n : ℝ)| ≤
        relativeError * (singularSeries n * (n : ℝ))

noncomputable def
    VonMangoldtHardyLittlewoodAbsErrorEstimate.toHardyLittlewoodNormalizedEstimate
    (estimate : VonMangoldtHardyLittlewoodAbsErrorEstimate) :
    VonMangoldtHardyLittlewoodNormalizedEstimate where
  threshold := estimate.threshold
  coefficient := estimate.coefficient
  relativeError := estimate.relativeError
  coefficient_pos := estimate.coefficient_pos
  relativeError_lt_one := estimate.relativeError_lt_one
  singularSeries := estimate.singularSeries
  singularSeriesLowerBound := estimate.singularSeriesLowerBound
  rawNormalizedErrorBound :=
    raw_normalized_error_bound_of_hardy_littlewood_abs_error_bound
      estimate.coefficient_pos
      estimate.singularSeriesLowerBound
      estimate.rawAbsErrorBound

noncomputable def
    VonMangoldtHardyLittlewoodAbsErrorEstimate.toPositiveLinearRawLowerBound
    (estimate : VonMangoldtHardyLittlewoodAbsErrorEstimate) :
    VonMangoldtPositiveLinearRawLowerBound :=
  estimate.toHardyLittlewoodNormalizedEstimate.toPositiveLinearRawLowerBound

noncomputable def
    VonMangoldtHardyLittlewoodAbsErrorEstimate.toSqrtLogCountLinearRawLowerBound
    (estimate : VonMangoldtHardyLittlewoodAbsErrorEstimate) :
    VonMangoldtSqrtLogCountLinearRawLowerBound :=
  estimate.toHardyLittlewoodNormalizedEstimate.toSqrtLogCountLinearRawLowerBound

noncomputable def
    VonMangoldtHardyLittlewoodAbsErrorEstimate.toDirectRawWeightSumLowerBound
    (estimate : VonMangoldtHardyLittlewoodAbsErrorEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toHardyLittlewoodNormalizedEstimate.toDirectRawWeightSumLowerBound

theorem
    count_positive_above_of_vonMangoldt_hardy_littlewood_abs_error_estimate
    (estimate : VonMangoldtHardyLittlewoodAbsErrorEstimate) :
    GoldbachCountPositiveAbove
      estimate.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_hardy_littlewood_normalized_estimate
    estimate.toHardyLittlewoodNormalizedEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_hardy_littlewood_abs_error_estimate
    (estimate : VonMangoldtHardyLittlewoodAbsErrorEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_hardy_littlewood_abs_error_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_abs_error_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtHardyLittlewoodAbsErrorEstimate)
    (hthreshold :
      estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_estimate_le
    finite
    estimate.toHardyLittlewoodNormalizedEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_hardy_littlewood_abs_error_estimate_le100
    (estimate : VonMangoldtHardyLittlewoodAbsErrorEstimate)
    (hthreshold :
      estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_abs_error_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_abs_error_estimate_weight_sum_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtHardyLittlewoodAbsErrorEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_estimate_weight_sum_le
    finite
    estimate.toHardyLittlewoodNormalizedEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_hardy_littlewood_abs_error_estimate_weight_sum_le100
    (estimate : VonMangoldtHardyLittlewoodAbsErrorEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_abs_error_estimate_weight_sum_le
    goldbachUpTo100
    estimate
    hthreshold

structure VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate where
  threshold : Nat
  coefficient : ℝ
  relativeError : ℝ
  coefficient_pos : 0 < coefficient
  relativeError_lt_one : relativeError < 1
  singularSeries : Nat → ℝ
  singularSeriesLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      coefficient ≤ singularSeries n
  rawNormalizedErrorBound :
    ∀ n : Nat, threshold < n → Even n →
      |(RawVonMangoldtGoldbachSum n -
          singularSeries n * (n : ℝ)) /
        (singularSeries n * (n : ℝ))| ≤ relativeError

noncomputable def
    VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate.toHardyLittlewoodNormalizedEstimate
    (estimate :
      VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate) :
    VonMangoldtHardyLittlewoodNormalizedEstimate where
  threshold := estimate.threshold
  coefficient := estimate.coefficient
  relativeError := estimate.relativeError
  coefficient_pos := estimate.coefficient_pos
  relativeError_lt_one := estimate.relativeError_lt_one
  singularSeries := estimate.singularSeries
  singularSeriesLowerBound := estimate.singularSeriesLowerBound
  rawNormalizedErrorBound := estimate.rawNormalizedErrorBound

noncomputable def
    VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate.toEventuallyDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate) :
    VonMangoldtEventuallyDirectRawWeightSumLowerBound where
  nonPrimePrimePowerWeightSumBound :=
    canonicalNonPrimePrimePowerVonMangoldtWeightSumBound
  nonPrimePrimePowerWeightSumBoundValidEventually := by
    filter_upwards
      [Filter.eventually_ge_atTop estimate.threshold.succ] with n hge hEven
    exact canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_valid
      n (Nat.succ_le_iff.mp hge) hEven
  rawLowerBoundEventually := by
    have hcont :=
      eventually_canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_hl_effective_contamination_dominated
        (coefficient := estimate.coefficient)
        (relativeError := estimate.relativeError)
        estimate.coefficient_pos
        estimate.relativeError_lt_one
    filter_upwards
      [Filter.eventually_ge_atTop estimate.threshold.succ, hcont]
      with n hge hcont hEven
    have htn : estimate.threshold < n := Nat.succ_le_iff.mp hge
    have hraw :=
      estimate.toHardyLittlewoodNormalizedEstimate.toPositiveLinearRawLowerBound.rawLinearLowerBound
        n htn hEven
    exact hcont.trans_le
      (by
        simpa
          [VonMangoldtHardyLittlewoodNormalizedEstimate.effectiveCoefficient]
          using hraw)

noncomputable def
    VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate.canonicalContaminationThreshold
    (estimate :
      VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate) :
    Nat :=
  canonicalHLContaminationThreshold
    estimate.coefficient
    estimate.relativeError
    estimate.coefficient_pos
    estimate.relativeError_lt_one

noncomputable def
    VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate.toSplitThresholdDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate) :
    VonMangoldtSplitThresholdDirectRawWeightSumLowerBound where
  weightSumThreshold := estimate.threshold
  rawThreshold :=
    max estimate.threshold estimate.canonicalContaminationThreshold
  nonPrimePrimePowerWeightSumBound :=
    canonicalNonPrimePrimePowerVonMangoldtWeightSumBound
  nonPrimePrimePowerWeightSumBoundValid := by
    intro n htn hEven
    exact canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_valid
      n htn hEven
  rawLowerBound := by
    intro n htn hEven
    have hanalytic : estimate.threshold < n :=
      lt_of_le_of_lt (Nat.le_max_left _ _) htn
    have hcont_threshold : estimate.canonicalContaminationThreshold < n :=
      lt_of_le_of_lt (Nat.le_max_right _ _) htn
    have hcont :=
      canonicalHLContaminationThreshold_spec
        estimate.coefficient_pos
        estimate.relativeError_lt_one
        n (le_of_lt hcont_threshold)
    have hraw :=
      estimate.toHardyLittlewoodNormalizedEstimate.toPositiveLinearRawLowerBound.rawLinearLowerBound
        n hanalytic hEven
    exact hcont.trans_le
      (by
        simpa
          [VonMangoldtHardyLittlewoodNormalizedEstimate.effectiveCoefficient]
          using hraw)

noncomputable def
    VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toSplitThresholdDirectRawWeightSumLowerBound.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate.directRawWeightSumThreshold_eq
    (estimate :
      VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate) :
    estimate.toDirectRawWeightSumLowerBound.threshold =
      max estimate.threshold estimate.canonicalContaminationThreshold := by
  dsimp
    [VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound,
      VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate.toSplitThresholdDirectRawWeightSumLowerBound,
      VonMangoldtSplitThresholdDirectRawWeightSumLowerBound.toDirectRawWeightSumLowerBound,
      VonMangoldtSplitThresholdDirectRawWeightSumLowerBound.threshold]
  rw [← Nat.max_assoc, Nat.max_self]

theorem
    VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate.directRawWeightSumThreshold_le
    {B : Nat}
    (estimate :
      VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate)
    (hanalytic : estimate.threshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B := by
  rw [estimate.directRawWeightSumThreshold_eq]
  exact max_le hanalytic hcontamination

theorem
    count_positive_above_of_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_direct_raw_weight_sum_lower_bound
    estimate.toDirectRawWeightSumLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_direct_raw_weight_sum_lower_bound_le
    finite
    estimate.toDirectRawWeightSumLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

structure
    VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate where
  threshold : Nat
  relativeError : ℝ
  relativeError_lt_one : relativeError < 1
  rawNormalizedErrorBound :
    ∀ n : Nat, threshold < n → Even n →
      |(RawVonMangoldtGoldbachSum n -
          goldbachSingularSeriesFromQuarter n * (n : ℝ)) /
        (goldbachSingularSeriesFromQuarter n * (n : ℝ))| ≤ relativeError

noncomputable def
    VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate.toHardyLittlewoodNormalizedCanonicalWeightSumEstimate
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate) :
    VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate where
  threshold := estimate.threshold
  coefficient := (1 / 4 : ℝ)
  relativeError := estimate.relativeError
  coefficient_pos := by norm_num
  relativeError_lt_one := estimate.relativeError_lt_one
  singularSeries := goldbachSingularSeriesFromQuarter
  singularSeriesLowerBound := one_fourth_le_goldbachSingularSeriesFromQuarter
  rawNormalizedErrorBound := estimate.rawNormalizedErrorBound

noncomputable def
    VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate.canonicalContaminationThreshold
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate) :
    Nat :=
  estimate.toHardyLittlewoodNormalizedCanonicalWeightSumEstimate.canonicalContaminationThreshold

noncomputable def
    VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toHardyLittlewoodNormalizedCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate.directRawWeightSumThreshold_eq
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate) :
    estimate.toDirectRawWeightSumLowerBound.threshold =
      max estimate.threshold estimate.canonicalContaminationThreshold := by
  simpa
    [VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound,
      VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate.canonicalContaminationThreshold,
      VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate.toHardyLittlewoodNormalizedCanonicalWeightSumEstimate]
    using
      estimate.toHardyLittlewoodNormalizedCanonicalWeightSumEstimate.directRawWeightSumThreshold_eq

theorem
    VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate.directRawWeightSumThreshold_le
    {B : Nat}
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate)
    (hanalytic : estimate.threshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B := by
  rw [estimate.directRawWeightSumThreshold_eq]
  exact max_le hanalytic hcontamination

theorem
    count_positive_above_of_vonMangoldt_quarter_hardy_littlewood_normalized_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold := by
  simpa
    [VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound]
    using
      count_positive_above_of_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate
        estimate.toHardyLittlewoodNormalizedCanonicalWeightSumEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_quarter_hardy_littlewood_normalized_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_quarter_hardy_littlewood_normalized_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_normalized_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate_le
    finite
    estimate.toHardyLittlewoodNormalizedCanonicalWeightSumEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_quarter_hardy_littlewood_normalized_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_normalized_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

structure
    VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate where
  threshold : Nat
  contaminationThreshold : Nat
  relativeError : ℝ
  relativeError_lt_one : relativeError < 1
  rawNormalizedErrorBound :
    ∀ n : Nat, threshold < n → Even n →
      |(RawVonMangoldtGoldbachSum n -
          goldbachSingularSeriesFromQuarter n * (n : ℝ)) /
        (goldbachSingularSeriesFromQuarter n * (n : ℝ))| ≤ relativeError
  contaminationDominated :
    ∀ n : Nat, contaminationThreshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        ((1 - relativeError) * (1 / 4 : ℝ)) * (n : ℝ)

noncomputable def
    VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate.toHardyLittlewoodNormalizedEstimate
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate) :
    VonMangoldtHardyLittlewoodNormalizedEstimate where
  threshold := estimate.threshold
  coefficient := (1 / 4 : ℝ)
  relativeError := estimate.relativeError
  coefficient_pos := by norm_num
  relativeError_lt_one := estimate.relativeError_lt_one
  singularSeries := goldbachSingularSeriesFromQuarter
  singularSeriesLowerBound := one_fourth_le_goldbachSingularSeriesFromQuarter
  rawNormalizedErrorBound := estimate.rawNormalizedErrorBound

noncomputable def
    VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate.toPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate) :
    VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound where
  rawThreshold := estimate.threshold
  contaminationThreshold := estimate.contaminationThreshold
  coefficient := (1 - estimate.relativeError) * (1 / 4 : ℝ)
  coefficient_pos := by
    have hfactor : 0 < 1 - estimate.relativeError := by
      linarith [estimate.relativeError_lt_one]
    positivity
  rawLinearLowerBound := by
    intro n htn hEven
    simpa
      [VonMangoldtHardyLittlewoodNormalizedEstimate.effectiveCoefficient,
        VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate.toHardyLittlewoodNormalizedEstimate]
      using
        estimate.toHardyLittlewoodNormalizedEstimate.toPositiveLinearRawLowerBound.rawLinearLowerBound
          n htn hEven
  contaminationDominated := estimate.contaminationDominated

noncomputable def
    VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate.directRawWeightSumThreshold_eq
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate) :
    estimate.toDirectRawWeightSumLowerBound.threshold =
      max estimate.threshold estimate.contaminationThreshold := by
  simpa
    [VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound,
      VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate.toPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound]
    using
      estimate.toPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound.directRawWeightSumThreshold_eq

theorem
    VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate)
    (hanalytic : estimate.threshold ≤ B)
    (hcontamination : estimate.contaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B := by
  rw [estimate.directRawWeightSumThreshold_eq]
  exact max_le hanalytic hcontamination

theorem
    count_positive_above_of_vonMangoldt_quarter_hardy_littlewood_normalized_explicit_contamination_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_positive_linear_raw_explicit_contamination_canonical_weight_sum_lower_bound
    estimate.toPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_quarter_hardy_littlewood_normalized_explicit_contamination_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_quarter_hardy_littlewood_normalized_explicit_contamination_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_normalized_explicit_contamination_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_explicit_contamination_canonical_weight_sum_lower_bound_le
    finite
    estimate.toPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_quarter_hardy_littlewood_normalized_explicit_contamination_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtQuarterHardyLittlewoodNormalizedExplicitContaminationCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_normalized_explicit_contamination_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

structure
    VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate where
  threshold : Nat
  contaminationThreshold : Nat
  relativeError : ℝ
  relativeError_lt_one : relativeError < 1
  rawRelativeLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      (1 - relativeError) *
          (goldbachSingularSeriesFromQuarter n * (n : ℝ)) ≤
        RawVonMangoldtGoldbachSum n
  contaminationDominated :
    ∀ n : Nat, contaminationThreshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        ((1 - relativeError) * (1 / 4 : ℝ)) * (n : ℝ)

noncomputable def
    VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound
    (estimate :
      VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    VonMangoldtPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound where
  rawThreshold := estimate.threshold
  contaminationThreshold := estimate.contaminationThreshold
  coefficient := (1 - estimate.relativeError) * (1 / 4 : ℝ)
  coefficient_pos := by
    have hfactor : 0 < 1 - estimate.relativeError := by
      linarith [estimate.relativeError_lt_one]
    positivity
  rawLinearLowerBound := by
    intro n htn hEven
    have hseries :
        (1 / 4 : ℝ) ≤ goldbachSingularSeriesFromQuarter n :=
      one_fourth_le_goldbachSingularSeriesFromQuarter n htn hEven
    have hfactor_nonneg : 0 ≤ 1 - estimate.relativeError := by
      linarith [estimate.relativeError_lt_one]
    have hmain :
        (1 - estimate.relativeError) *
            ((1 / 4 : ℝ) * (n : ℝ)) ≤
          (1 - estimate.relativeError) *
            (goldbachSingularSeriesFromQuarter n * (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hseries (Nat.cast_nonneg n))
        hfactor_nonneg
    calc
      ((1 - estimate.relativeError) * (1 / 4 : ℝ)) * (n : ℝ)
          = (1 - estimate.relativeError) *
              ((1 / 4 : ℝ) * (n : ℝ)) := by ring
      _ ≤ (1 - estimate.relativeError) *
            (goldbachSingularSeriesFromQuarter n * (n : ℝ)) := hmain
      _ ≤ RawVonMangoldtGoldbachSum n :=
            estimate.rawRelativeLowerBound n htn hEven
  contaminationDominated := estimate.contaminationDominated

noncomputable def
    VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate.directRawWeightSumThreshold_eq
    (estimate :
      VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    estimate.toDirectRawWeightSumLowerBound.threshold =
      max estimate.threshold estimate.contaminationThreshold := by
  simpa
    [VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound,
      VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound]
    using
      estimate.toPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound.directRawWeightSumThreshold_eq

theorem
    VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate)
    (hanalytic : estimate.threshold ≤ B)
    (hcontamination : estimate.contaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B := by
  rw [estimate.directRawWeightSumThreshold_eq]
  exact max_le hanalytic hcontamination

theorem
    count_positive_above_of_vonMangoldt_quarter_hardy_littlewood_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_positive_linear_raw_explicit_contamination_canonical_weight_sum_lower_bound
    estimate.toPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_quarter_hardy_littlewood_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_quarter_hardy_littlewood_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_explicit_contamination_canonical_weight_sum_lower_bound_le
    finite
    estimate.toPositiveLinearRawExplicitContaminationCanonicalWeightSumLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_quarter_hardy_littlewood_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

theorem raw_relative_lower_bound_of_major_minor_lower_bound
    {decompositionThreshold majorArcThreshold minorArcThreshold : Nat}
    {relativeError : ℝ}
    {majorArcContribution minorArcContribution minorArcError : Nat → ℝ}
    (hdecomposition :
      ∀ n : Nat, decompositionThreshold < n → Even n →
        RawVonMangoldtGoldbachSum n =
          majorArcContribution n + minorArcContribution n)
    (hmajor :
      ∀ n : Nat, majorArcThreshold < n → Even n →
        (1 - relativeError) *
            (goldbachSingularSeriesFromQuarter n * (n : ℝ)) +
          minorArcError n ≤ majorArcContribution n)
    (hminor :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        -minorArcError n ≤ minorArcContribution n) :
    ∀ n : Nat,
      max decompositionThreshold
          (max majorArcThreshold minorArcThreshold) < n →
        Even n →
        (1 - relativeError) *
            (goldbachSingularSeriesFromQuarter n * (n : ℝ)) ≤
          RawVonMangoldtGoldbachSum n := by
  intro n htn hEven
  have hdecomposition_threshold : decompositionThreshold < n :=
    lt_of_le_of_lt (Nat.le_max_left _ _) htn
  have hmajor_threshold : majorArcThreshold < n :=
    lt_of_le_of_lt
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)) htn
  have hminor_threshold : minorArcThreshold < n :=
    lt_of_le_of_lt
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)) htn
  have hraw := hdecomposition n hdecomposition_threshold hEven
  have hmajor_bound := hmajor n hmajor_threshold hEven
  have hminor_bound := hminor n hminor_threshold hEven
  calc
    (1 - relativeError) *
        (goldbachSingularSeriesFromQuarter n * (n : ℝ))
        =
          ((1 - relativeError) *
              (goldbachSingularSeriesFromQuarter n * (n : ℝ)) +
            minorArcError n) +
            -minorArcError n := by ring
    _ ≤ majorArcContribution n + minorArcContribution n :=
        add_le_add hmajor_bound hminor_bound
    _ = RawVonMangoldtGoldbachSum n := by
        rw [← hraw]

structure
    VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate where
  decompositionThreshold : Nat
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  contaminationThreshold : Nat
  relativeError : ℝ
  relativeError_lt_one : relativeError < 1
  majorArcContribution : Nat → ℝ
  minorArcContribution : Nat → ℝ
  minorArcError : Nat → ℝ
  rawDecomposition :
    ∀ n : Nat, decompositionThreshold < n → Even n →
      RawVonMangoldtGoldbachSum n =
        majorArcContribution n + minorArcContribution n
  majorArcLowerBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      (1 - relativeError) *
          (goldbachSingularSeriesFromQuarter n * (n : ℝ)) +
        minorArcError n ≤ majorArcContribution n
  minorArcContributionLowerBound :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      -minorArcError n ≤ minorArcContribution n
  contaminationDominated :
    ∀ n : Nat, contaminationThreshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        ((1 - relativeError) * (1 / 4 : ℝ)) * (n : ℝ)

def
    VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.majorMinorThreshold
    (estimate :
      VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    Nat :=
  max estimate.decompositionThreshold
    (max estimate.majorArcThreshold estimate.minorArcThreshold)

theorem
    VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.decompositionThreshold_le_majorMinorThreshold
    (estimate :
      VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    estimate.decompositionThreshold ≤ estimate.majorMinorThreshold := by
  dsimp
    [VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.majorMinorThreshold]
  exact Nat.le_max_left _ _

theorem
    VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.majorArcThreshold_le_majorMinorThreshold
    (estimate :
      VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    estimate.majorArcThreshold ≤ estimate.majorMinorThreshold := by
  dsimp
    [VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.majorMinorThreshold]
  exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

theorem
    VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.minorArcThreshold_le_majorMinorThreshold
    (estimate :
      VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    estimate.minorArcThreshold ≤ estimate.majorMinorThreshold := by
  dsimp
    [VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.majorMinorThreshold]
  exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

theorem
    VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.majorMinorThreshold_le
    {B : Nat}
    (estimate :
      VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate)
    (hdecomposition : estimate.decompositionThreshold ≤ B)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B) :
    estimate.majorMinorThreshold ≤ B := by
  dsimp
    [VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.majorMinorThreshold]
  exact max_le hdecomposition (max_le hmajor hminor)

noncomputable def
    VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate
    (estimate :
      VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    VonMangoldtQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate where
  threshold := estimate.majorMinorThreshold
  contaminationThreshold := estimate.contaminationThreshold
  relativeError := estimate.relativeError
  relativeError_lt_one := estimate.relativeError_lt_one
  rawRelativeLowerBound := by
    simpa
      [VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.majorMinorThreshold]
      using
        raw_relative_lower_bound_of_major_minor_lower_bound
          estimate.rawDecomposition
          estimate.majorArcLowerBound
          estimate.minorArcContributionLowerBound
  contaminationDominated := estimate.contaminationDominated

noncomputable def
    VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.directRawWeightSumThreshold_eq
    (estimate :
      VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    estimate.toDirectRawWeightSumLowerBound.threshold =
      max estimate.majorMinorThreshold estimate.contaminationThreshold := by
  simpa
    [VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound,
      VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.toQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate]
    using
      estimate.toQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate.directRawWeightSumThreshold_eq

theorem
    VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate)
    (hdecomposition : estimate.decompositionThreshold ≤ B)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (hcontamination : estimate.contaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B := by
  rw [estimate.directRawWeightSumThreshold_eq]
  exact max_le
    (estimate.majorMinorThreshold_le hdecomposition hmajor hminor)
    hcontamination

theorem
    count_positive_above_of_vonMangoldt_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_quarter_hardy_littlewood_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    estimate.toQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_quarter_hardy_littlewood_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le
    finite
    estimate.toQuarterHardyLittlewoodLowerBoundExplicitContaminationCanonicalWeightSumEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtQuarterMajorMinorLowerBoundExplicitContaminationCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_quarter_major_minor_lower_bound_explicit_contamination_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

structure VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate where
  threshold : Nat
  coefficient : ℝ
  relativeError : ℝ
  coefficient_pos : 0 < coefficient
  relativeError_lt_one : relativeError < 1
  singularSeries : Nat → ℝ
  singularSeriesLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      coefficient ≤ singularSeries n
  rawAbsErrorBound :
    ∀ n : Nat, threshold < n → Even n →
      |RawVonMangoldtGoldbachSum n -
          singularSeries n * (n : ℝ)| ≤
        relativeError * (singularSeries n * (n : ℝ))

noncomputable def
    VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate.toHardyLittlewoodNormalizedCanonicalWeightSumEstimate
    (estimate :
      VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate) :
    VonMangoldtHardyLittlewoodNormalizedCanonicalWeightSumEstimate where
  threshold := estimate.threshold
  coefficient := estimate.coefficient
  relativeError := estimate.relativeError
  coefficient_pos := estimate.coefficient_pos
  relativeError_lt_one := estimate.relativeError_lt_one
  singularSeries := estimate.singularSeries
  singularSeriesLowerBound := estimate.singularSeriesLowerBound
  rawNormalizedErrorBound :=
    raw_normalized_error_bound_of_hardy_littlewood_abs_error_bound
      estimate.coefficient_pos
      estimate.singularSeriesLowerBound
      estimate.rawAbsErrorBound

noncomputable def
    VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold
    (estimate :
      VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate) :
    Nat :=
  estimate.toHardyLittlewoodNormalizedCanonicalWeightSumEstimate.canonicalContaminationThreshold

noncomputable def
    VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toHardyLittlewoodNormalizedCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_eq
    (estimate :
      VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate) :
    estimate.toDirectRawWeightSumLowerBound.threshold =
      max estimate.threshold estimate.canonicalContaminationThreshold := by
  simpa
    [VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound,
      VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold,
      VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate.toHardyLittlewoodNormalizedCanonicalWeightSumEstimate]
    using
      estimate.toHardyLittlewoodNormalizedCanonicalWeightSumEstimate.directRawWeightSumThreshold_eq

theorem
    VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_le
    {B : Nat}
    (estimate :
      VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate)
    (hanalytic : estimate.threshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B := by
  rw [estimate.directRawWeightSumThreshold_eq]
  exact max_le hanalytic hcontamination

theorem
    count_positive_above_of_vonMangoldt_hardy_littlewood_abs_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate
    estimate.toHardyLittlewoodNormalizedCanonicalWeightSumEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_hardy_littlewood_abs_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_hardy_littlewood_abs_error_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_abs_error_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_canonical_weight_sum_estimate_le
    finite
    estimate.toHardyLittlewoodNormalizedCanonicalWeightSumEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_hardy_littlewood_abs_error_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_abs_error_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

theorem raw_abs_error_bound_of_hardy_littlewood_major_minor_abs_error_bound
    {threshold : Nat} {relativeError : ℝ}
    {singularSeries majorArcError minorArcError : Nat → ℝ}
    (hmajor_minor :
      ∀ n : Nat, threshold < n → Even n →
        |RawVonMangoldtGoldbachSum n -
            singularSeries n * (n : ℝ)| ≤
          majorArcError n + minorArcError n)
    (htotal :
      ∀ n : Nat, threshold < n → Even n →
        majorArcError n + minorArcError n ≤
          relativeError * (singularSeries n * (n : ℝ))) :
    ∀ n : Nat, threshold < n → Even n →
      |RawVonMangoldtGoldbachSum n -
          singularSeries n * (n : ℝ)| ≤
        relativeError * (singularSeries n * (n : ℝ)) := by
  intro n htn hEven
  exact (hmajor_minor n htn hEven).trans (htotal n htn hEven)

structure VonMangoldtHardyLittlewoodMajorMinorAbsErrorEstimate where
  threshold : Nat
  coefficient : ℝ
  relativeError : ℝ
  coefficient_pos : 0 < coefficient
  relativeError_lt_one : relativeError < 1
  singularSeries : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  singularSeriesLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      coefficient ≤ singularSeries n
  majorMinorAbsErrorBound :
    ∀ n : Nat, threshold < n → Even n →
      |RawVonMangoldtGoldbachSum n -
          singularSeries n * (n : ℝ)| ≤
        majorArcError n + minorArcError n
  totalAnalyticErrorBound :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n ≤
        relativeError * (singularSeries n * (n : ℝ))

noncomputable def
    VonMangoldtHardyLittlewoodMajorMinorAbsErrorEstimate.toHardyLittlewoodAbsErrorEstimate
    (estimate : VonMangoldtHardyLittlewoodMajorMinorAbsErrorEstimate) :
    VonMangoldtHardyLittlewoodAbsErrorEstimate where
  threshold := estimate.threshold
  coefficient := estimate.coefficient
  relativeError := estimate.relativeError
  coefficient_pos := estimate.coefficient_pos
  relativeError_lt_one := estimate.relativeError_lt_one
  singularSeries := estimate.singularSeries
  singularSeriesLowerBound := estimate.singularSeriesLowerBound
  rawAbsErrorBound :=
    raw_abs_error_bound_of_hardy_littlewood_major_minor_abs_error_bound
      estimate.majorMinorAbsErrorBound
      estimate.totalAnalyticErrorBound

noncomputable def
    VonMangoldtHardyLittlewoodMajorMinorAbsErrorEstimate.toHardyLittlewoodNormalizedEstimate
    (estimate : VonMangoldtHardyLittlewoodMajorMinorAbsErrorEstimate) :
    VonMangoldtHardyLittlewoodNormalizedEstimate :=
  estimate.toHardyLittlewoodAbsErrorEstimate.toHardyLittlewoodNormalizedEstimate

noncomputable def
    VonMangoldtHardyLittlewoodMajorMinorAbsErrorEstimate.toSqrtLogCountLinearRawLowerBound
    (estimate : VonMangoldtHardyLittlewoodMajorMinorAbsErrorEstimate) :
    VonMangoldtSqrtLogCountLinearRawLowerBound :=
  estimate.toHardyLittlewoodAbsErrorEstimate.toSqrtLogCountLinearRawLowerBound

noncomputable def
    VonMangoldtHardyLittlewoodMajorMinorAbsErrorEstimate.toDirectRawWeightSumLowerBound
    (estimate : VonMangoldtHardyLittlewoodMajorMinorAbsErrorEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toHardyLittlewoodAbsErrorEstimate.toDirectRawWeightSumLowerBound

theorem
    count_positive_above_of_vonMangoldt_hardy_littlewood_major_minor_abs_error_estimate
    (estimate : VonMangoldtHardyLittlewoodMajorMinorAbsErrorEstimate) :
    GoldbachCountPositiveAbove
      estimate.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_hardy_littlewood_abs_error_estimate
    estimate.toHardyLittlewoodAbsErrorEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_hardy_littlewood_major_minor_abs_error_estimate
    (estimate : VonMangoldtHardyLittlewoodMajorMinorAbsErrorEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_hardy_littlewood_major_minor_abs_error_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_major_minor_abs_error_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtHardyLittlewoodMajorMinorAbsErrorEstimate)
    (hthreshold :
      estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_abs_error_estimate_le
    finite
    estimate.toHardyLittlewoodAbsErrorEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_hardy_littlewood_major_minor_abs_error_estimate_le100
    (estimate : VonMangoldtHardyLittlewoodMajorMinorAbsErrorEstimate)
    (hthreshold :
      estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_major_minor_abs_error_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_major_minor_abs_error_estimate_weight_sum_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtHardyLittlewoodMajorMinorAbsErrorEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_abs_error_estimate_weight_sum_le
    finite
    estimate.toHardyLittlewoodAbsErrorEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_hardy_littlewood_major_minor_abs_error_estimate_weight_sum_le100
    (estimate : VonMangoldtHardyLittlewoodMajorMinorAbsErrorEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_major_minor_abs_error_estimate_weight_sum_le
    goldbachUpTo100
    estimate
    hthreshold

structure VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate where
  threshold : Nat
  coefficient : ℝ
  relativeError : ℝ
  coefficient_pos : 0 < coefficient
  relativeError_lt_one : relativeError < 1
  singularSeries : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  singularSeriesLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      coefficient ≤ singularSeries n
  majorMinorAbsErrorBound :
    ∀ n : Nat, threshold < n → Even n →
      |RawVonMangoldtGoldbachSum n -
          singularSeries n * (n : ℝ)| ≤
        majorArcError n + minorArcError n
  totalAnalyticErrorBound :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n ≤
        relativeError * (singularSeries n * (n : ℝ))

noncomputable def
    VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.toHardyLittlewoodAbsErrorCanonicalWeightSumEstimate
    (estimate :
      VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    VonMangoldtHardyLittlewoodAbsErrorCanonicalWeightSumEstimate where
  threshold := estimate.threshold
  coefficient := estimate.coefficient
  relativeError := estimate.relativeError
  coefficient_pos := estimate.coefficient_pos
  relativeError_lt_one := estimate.relativeError_lt_one
  singularSeries := estimate.singularSeries
  singularSeriesLowerBound := estimate.singularSeriesLowerBound
  rawAbsErrorBound :=
    raw_abs_error_bound_of_hardy_littlewood_major_minor_abs_error_bound
      estimate.majorMinorAbsErrorBound
      estimate.totalAnalyticErrorBound

noncomputable def
    VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold
    (estimate :
      VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    Nat :=
  estimate.toHardyLittlewoodAbsErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold

noncomputable def
    VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toHardyLittlewoodAbsErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_eq
    (estimate :
      VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    estimate.toDirectRawWeightSumLowerBound.threshold =
      max estimate.threshold estimate.canonicalContaminationThreshold := by
  simpa
    [VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound,
      VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold,
      VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.toHardyLittlewoodAbsErrorCanonicalWeightSumEstimate]
    using
      estimate.toHardyLittlewoodAbsErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_eq

theorem
    VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_le
    {B : Nat}
    (estimate :
      VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate)
    (hanalytic : estimate.threshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B := by
  rw [estimate.directRawWeightSumThreshold_eq]
  exact max_le hanalytic hcontamination

theorem
    count_positive_above_of_vonMangoldt_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_hardy_littlewood_abs_error_canonical_weight_sum_estimate
    estimate.toHardyLittlewoodAbsErrorCanonicalWeightSumEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_abs_error_canonical_weight_sum_estimate_le
    finite
    estimate.toHardyLittlewoodAbsErrorCanonicalWeightSumEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

structure VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate where
  singularSeriesThreshold : Nat
  majorMinorThreshold : Nat
  totalAnalyticErrorThreshold : Nat
  coefficient : ℝ
  relativeError : ℝ
  coefficient_pos : 0 < coefficient
  relativeError_lt_one : relativeError < 1
  singularSeries : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  singularSeriesLowerBound :
    ∀ n : Nat, singularSeriesThreshold < n → Even n →
      coefficient ≤ singularSeries n
  majorMinorAbsErrorBound :
    ∀ n : Nat, majorMinorThreshold < n → Even n →
      |RawVonMangoldtGoldbachSum n -
          singularSeries n * (n : ℝ)| ≤
        majorArcError n + minorArcError n
  totalAnalyticErrorBound :
    ∀ n : Nat, totalAnalyticErrorThreshold < n → Even n →
      majorArcError n + minorArcError n ≤
        relativeError * (singularSeries n * (n : ℝ))

def
    VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.threshold
    (estimate :
      VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    Nat :=
  max estimate.singularSeriesThreshold
    (max estimate.majorMinorThreshold estimate.totalAnalyticErrorThreshold)

theorem
    VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.singularSeriesThreshold_le_threshold
    (estimate :
      VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    estimate.singularSeriesThreshold ≤ estimate.threshold := by
  dsimp
    [VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.threshold]
  exact Nat.le_max_left _ _

theorem
    VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.majorMinorThreshold_le_threshold
    (estimate :
      VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    estimate.majorMinorThreshold ≤ estimate.threshold := by
  dsimp
    [VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.threshold]
  exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

theorem
    VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.totalAnalyticErrorThreshold_le_threshold
    (estimate :
      VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    estimate.totalAnalyticErrorThreshold ≤ estimate.threshold := by
  dsimp
    [VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.threshold]
  exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

theorem
    VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.threshold_le
    {B : Nat}
    (estimate :
      VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate)
    (hsingular : estimate.singularSeriesThreshold ≤ B)
    (hmajor_minor : estimate.majorMinorThreshold ≤ B)
    (htotal : estimate.totalAnalyticErrorThreshold ≤ B) :
    estimate.threshold ≤ B := by
  dsimp
    [VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.threshold]
  exact max_le hsingular (max_le hmajor_minor htotal)

noncomputable def
    VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.toHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate
    (estimate :
      VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    VonMangoldtHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate where
  threshold := estimate.threshold
  coefficient := estimate.coefficient
  relativeError := estimate.relativeError
  coefficient_pos := estimate.coefficient_pos
  relativeError_lt_one := estimate.relativeError_lt_one
  singularSeries := estimate.singularSeries
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  singularSeriesLowerBound := by
    intro n htn hEven
    exact estimate.singularSeriesLowerBound n
      (lt_of_le_of_lt estimate.singularSeriesThreshold_le_threshold htn)
      hEven
  majorMinorAbsErrorBound := by
    intro n htn hEven
    exact estimate.majorMinorAbsErrorBound n
      (lt_of_le_of_lt estimate.majorMinorThreshold_le_threshold htn)
      hEven
  totalAnalyticErrorBound := by
    intro n htn hEven
    exact estimate.totalAnalyticErrorBound n
      (lt_of_le_of_lt estimate.totalAnalyticErrorThreshold_le_threshold htn)
      hEven

noncomputable def
    VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold
    (estimate :
      VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    Nat :=
  estimate.toHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold

noncomputable def
    VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_eq
    (estimate :
      VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    estimate.toDirectRawWeightSumLowerBound.threshold =
      max estimate.threshold estimate.canonicalContaminationThreshold := by
  simpa
    [VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound,
      VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold,
      VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.toHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate]
    using
      estimate.toHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_eq

theorem
    VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_le
    {B : Nat}
    (estimate :
      VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate)
    (hanalytic : estimate.threshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B := by
  rw [estimate.directRawWeightSumThreshold_eq]
  exact max_le hanalytic hcontamination

theorem
    VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate)
    (hsingular : estimate.singularSeriesThreshold ≤ B)
    (hmajor_minor : estimate.majorMinorThreshold ≤ B)
    (htotal : estimate.totalAnalyticErrorThreshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  estimate.directRawWeightSumThreshold_le
    (estimate.threshold_le hsingular hmajor_minor htotal)
    hcontamination

theorem
    count_positive_above_of_vonMangoldt_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate
    estimate.toHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate_le
    finite
    estimate.toHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

structure
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate where
  majorMinorThreshold : Nat
  totalAnalyticErrorThreshold : Nat
  relativeError : ℝ
  relativeError_lt_one : relativeError < 1
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  majorMinorAbsErrorBound :
    ∀ n : Nat, majorMinorThreshold < n → Even n →
      |RawVonMangoldtGoldbachSum n -
          goldbachSingularSeriesFromQuarter n * (n : ℝ)| ≤
        majorArcError n + minorArcError n
  totalAnalyticErrorBound :
    ∀ n : Nat, totalAnalyticErrorThreshold < n → Even n →
      majorArcError n + minorArcError n ≤
        relativeError * (goldbachSingularSeriesFromQuarter n * (n : ℝ))

def
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.threshold
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    Nat :=
  max 0 (max estimate.majorMinorThreshold estimate.totalAnalyticErrorThreshold)

theorem
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.majorMinorThreshold_le_threshold
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    estimate.majorMinorThreshold ≤ estimate.threshold := by
  dsimp
    [VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.threshold]
  exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

theorem
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.totalAnalyticErrorThreshold_le_threshold
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    estimate.totalAnalyticErrorThreshold ≤ estimate.threshold := by
  dsimp
    [VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.threshold]
  exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

theorem
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.threshold_le
    {B : Nat}
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate)
    (hmajor_minor : estimate.majorMinorThreshold ≤ B)
    (htotal : estimate.totalAnalyticErrorThreshold ≤ B) :
    estimate.threshold ≤ B := by
  dsimp
    [VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.threshold]
  exact max_le (Nat.zero_le B) (max_le hmajor_minor htotal)

noncomputable def
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.toSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    VonMangoldtSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate where
  singularSeriesThreshold := 0
  majorMinorThreshold := estimate.majorMinorThreshold
  totalAnalyticErrorThreshold := estimate.totalAnalyticErrorThreshold
  coefficient := (1 / 4 : ℝ)
  relativeError := estimate.relativeError
  coefficient_pos := by norm_num
  relativeError_lt_one := estimate.relativeError_lt_one
  singularSeries := goldbachSingularSeriesFromQuarter
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  singularSeriesLowerBound := one_fourth_le_goldbachSingularSeriesFromQuarter
  majorMinorAbsErrorBound := estimate.majorMinorAbsErrorBound
  totalAnalyticErrorBound := estimate.totalAnalyticErrorBound

noncomputable def
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    Nat :=
  estimate.toSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold

noncomputable def
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_eq
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    estimate.toDirectRawWeightSumLowerBound.threshold =
      max estimate.threshold estimate.canonicalContaminationThreshold := by
  change
    estimate.toSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound.threshold =
      max
        estimate.toSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.threshold
        estimate.toSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold
  exact
    estimate.toSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_eq

theorem
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_le
    {B : Nat}
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate)
    (hanalytic : estimate.threshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B := by
  rw [estimate.directRawWeightSumThreshold_eq]
  exact max_le hanalytic hcontamination

theorem
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate)
    (hmajor_minor : estimate.majorMinorThreshold ≤ B)
    (htotal : estimate.totalAnalyticErrorThreshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  estimate.directRawWeightSumThreshold_le
    (estimate.threshold_le hmajor_minor htotal)
    hcontamination

theorem
    count_positive_above_of_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold := by
  simpa
    [VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound]
    using
      count_positive_above_of_vonMangoldt_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate
        estimate.toSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate_le
    finite
    estimate.toSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

theorem raw_abs_error_bound_of_major_minor_decomposition
    {decompositionThreshold majorArcThreshold minorArcThreshold : Nat}
    {singularSeries majorArcContribution minorArcContribution
      majorArcError minorArcError : Nat → ℝ}
    (hdecomposition :
      ∀ n : Nat, decompositionThreshold < n → Even n →
        RawVonMangoldtGoldbachSum n =
          majorArcContribution n + minorArcContribution n)
    (hmajor :
      ∀ n : Nat, majorArcThreshold < n → Even n →
        |majorArcContribution n - singularSeries n * (n : ℝ)| ≤
          majorArcError n)
    (hminor :
      ∀ n : Nat, minorArcThreshold < n → Even n →
        |minorArcContribution n| ≤ minorArcError n) :
    ∀ n : Nat, max decompositionThreshold
        (max majorArcThreshold minorArcThreshold) < n → Even n →
      |RawVonMangoldtGoldbachSum n -
          singularSeries n * (n : ℝ)| ≤
        majorArcError n + minorArcError n := by
  intro n htn hEven
  have hdecomposition_threshold : decompositionThreshold < n :=
    lt_of_le_of_lt (Nat.le_max_left _ _) htn
  have hmajor_threshold : majorArcThreshold < n :=
    lt_of_le_of_lt
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)) htn
  have hminor_threshold : minorArcThreshold < n :=
    lt_of_le_of_lt
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)) htn
  have hraw := hdecomposition n hdecomposition_threshold hEven
  have hmajor_bound := hmajor n hmajor_threshold hEven
  have hminor_bound := hminor n hminor_threshold hEven
  calc
    |RawVonMangoldtGoldbachSum n - singularSeries n * (n : ℝ)|
        = |(majorArcContribution n - singularSeries n * (n : ℝ)) +
            minorArcContribution n| := by
          rw [hraw]
          ring_nf
    _ ≤ |majorArcContribution n - singularSeries n * (n : ℝ)| +
          |minorArcContribution n| :=
        abs_add_le _ _
    _ ≤ majorArcError n + minorArcError n :=
        add_le_add hmajor_bound hminor_bound

structure
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate where
  decompositionThreshold : Nat
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  totalAnalyticErrorThreshold : Nat
  relativeError : ℝ
  relativeError_lt_one : relativeError < 1
  majorArcContribution : Nat → ℝ
  minorArcContribution : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  rawDecomposition :
    ∀ n : Nat, decompositionThreshold < n → Even n →
      RawVonMangoldtGoldbachSum n =
        majorArcContribution n + minorArcContribution n
  majorArcApproximationBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      |majorArcContribution n -
          goldbachSingularSeriesFromQuarter n * (n : ℝ)| ≤
        majorArcError n
  minorArcContributionBound :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      |minorArcContribution n| ≤ minorArcError n
  totalAnalyticErrorBound :
    ∀ n : Nat, totalAnalyticErrorThreshold < n → Even n →
      majorArcError n + minorArcError n ≤
        relativeError * (goldbachSingularSeriesFromQuarter n * (n : ℝ))

def
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.majorMinorThreshold
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate) :
    Nat :=
  max estimate.decompositionThreshold
    (max estimate.majorArcThreshold estimate.minorArcThreshold)

theorem
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.decompositionThreshold_le_majorMinorThreshold
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate) :
    estimate.decompositionThreshold ≤ estimate.majorMinorThreshold := by
  dsimp
    [VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.majorMinorThreshold]
  exact Nat.le_max_left _ _

theorem
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.majorArcThreshold_le_majorMinorThreshold
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate) :
    estimate.majorArcThreshold ≤ estimate.majorMinorThreshold := by
  dsimp
    [VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.majorMinorThreshold]
  exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

theorem
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.minorArcThreshold_le_majorMinorThreshold
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate) :
    estimate.minorArcThreshold ≤ estimate.majorMinorThreshold := by
  dsimp
    [VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.majorMinorThreshold]
  exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

theorem
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.majorMinorThreshold_le
    {B : Nat}
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate)
    (hdecomposition : estimate.decompositionThreshold ≤ B)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B) :
    estimate.majorMinorThreshold ≤ B := by
  dsimp
    [VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.majorMinorThreshold]
  exact max_le hdecomposition (max_le hmajor hminor)

def
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.threshold
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate) :
    Nat :=
  max estimate.majorMinorThreshold estimate.totalAnalyticErrorThreshold

theorem
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.majorMinorThreshold_le_threshold
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate) :
    estimate.majorMinorThreshold ≤ estimate.threshold := by
  dsimp
    [VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.threshold]
  exact Nat.le_max_left _ _

theorem
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.totalAnalyticErrorThreshold_le_threshold
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate) :
    estimate.totalAnalyticErrorThreshold ≤ estimate.threshold := by
  dsimp
    [VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.threshold]
  exact Nat.le_max_right _ _

theorem
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.threshold_le
    {B : Nat}
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate)
    (hdecomposition : estimate.decompositionThreshold ≤ B)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (htotal : estimate.totalAnalyticErrorThreshold ≤ B) :
    estimate.threshold ≤ B := by
  dsimp
    [VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.threshold]
  exact max_le
    (estimate.majorMinorThreshold_le hdecomposition hmajor hminor)
    htotal

noncomputable def
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.toQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate) :
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate where
  majorMinorThreshold := estimate.majorMinorThreshold
  totalAnalyticErrorThreshold := estimate.totalAnalyticErrorThreshold
  relativeError := estimate.relativeError
  relativeError_lt_one := estimate.relativeError_lt_one
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  majorMinorAbsErrorBound := by
    simpa
      [VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.majorMinorThreshold]
      using
        raw_abs_error_bound_of_major_minor_decomposition
          estimate.rawDecomposition
          estimate.majorArcApproximationBound
          estimate.minorArcContributionBound
  totalAnalyticErrorBound := estimate.totalAnalyticErrorBound

theorem
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.toQuarterSplitThreshold_threshold_eq
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate) :
    estimate.toQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.threshold =
      estimate.threshold := by
  simp
    [VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.toQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate,
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.threshold,
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.majorMinorThreshold,
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.threshold]

noncomputable def
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.canonicalContaminationThreshold
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate) :
    Nat :=
  estimate.toQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold

noncomputable def
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.directRawWeightSumThreshold_eq
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate) :
    estimate.toDirectRawWeightSumLowerBound.threshold =
      max estimate.threshold estimate.canonicalContaminationThreshold := by
  calc
    estimate.toDirectRawWeightSumLowerBound.threshold =
        estimate.toQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound.threshold := by
          rfl
    _ = max
          estimate.toQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.threshold
          estimate.toQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.canonicalContaminationThreshold :=
        estimate.toQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate.directRawWeightSumThreshold_eq
    _ = max estimate.threshold estimate.canonicalContaminationThreshold := by
        rw [estimate.toQuarterSplitThreshold_threshold_eq]
        rfl

theorem
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.directRawWeightSumThreshold_le
    {B : Nat}
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate)
    (hanalytic : estimate.threshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B := by
  rw [estimate.directRawWeightSumThreshold_eq]
  exact max_le hanalytic hcontamination

theorem
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate)
    (hdecomposition : estimate.decompositionThreshold ≤ B)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (htotal : estimate.totalAnalyticErrorThreshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  estimate.directRawWeightSumThreshold_le
    (estimate.threshold_le hdecomposition hmajor hminor htotal)
    hcontamination

theorem
    count_positive_above_of_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_decomposition_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold := by
  simpa
    [VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound]
    using
      count_positive_above_of_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate
        estimate.toQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_decomposition_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_decomposition_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_decomposition_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_abs_error_canonical_weight_sum_estimate_le
    finite
    estimate.toQuarterSplitThresholdHardyLittlewoodMajorMinorAbsErrorCanonicalWeightSumEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_decomposition_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_decomposition_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

theorem total_analytic_error_bound_of_quarter_linear_error_bound
    {linearErrorThreshold : Nat}
    {relativeError analyticErrorCoefficient : ℝ}
    {majorArcError minorArcError : Nat → ℝ}
    (hrelative_nonneg : 0 ≤ relativeError)
    (hcoefficient :
      analyticErrorCoefficient ≤ relativeError * (1 / 4 : ℝ))
    (hlinear :
      ∀ n : Nat, linearErrorThreshold < n → Even n →
        majorArcError n + minorArcError n ≤
          analyticErrorCoefficient * (n : ℝ)) :
    ∀ n : Nat, linearErrorThreshold < n → Even n →
      majorArcError n + minorArcError n ≤
        relativeError *
          (goldbachSingularSeriesFromQuarter n * (n : ℝ)) := by
  intro n htn hEven
  have hlinear_n := hlinear n htn hEven
  have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hseries :
      (1 / 4 : ℝ) ≤ goldbachSingularSeriesFromQuarter n :=
    one_fourth_le_goldbachSingularSeriesFromQuarter n htn hEven
  have hcoefficient_n :
      analyticErrorCoefficient * (n : ℝ) ≤
        (relativeError * (1 / 4 : ℝ)) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hcoefficient hn_nonneg
  have hseries_coefficient :
      relativeError * (1 / 4 : ℝ) ≤
        relativeError * goldbachSingularSeriesFromQuarter n :=
    mul_le_mul_of_nonneg_left hseries hrelative_nonneg
  have hseries_n :
      (relativeError * (1 / 4 : ℝ)) * (n : ℝ) ≤
        (relativeError * goldbachSingularSeriesFromQuarter n) *
          (n : ℝ) :=
    mul_le_mul_of_nonneg_right hseries_coefficient hn_nonneg
  calc
    majorArcError n + minorArcError n
        ≤ analyticErrorCoefficient * (n : ℝ) := hlinear_n
    _ ≤ (relativeError * (1 / 4 : ℝ)) * (n : ℝ) := hcoefficient_n
    _ ≤ (relativeError * goldbachSingularSeriesFromQuarter n) *
          (n : ℝ) := hseries_n
    _ = relativeError *
          (goldbachSingularSeriesFromQuarter n * (n : ℝ)) := by
        ring

structure
    VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate where
  decompositionThreshold : Nat
  majorArcThreshold : Nat
  minorArcThreshold : Nat
  totalLinearErrorThreshold : Nat
  relativeError : ℝ
  relativeError_nonneg : 0 ≤ relativeError
  relativeError_lt_one : relativeError < 1
  analyticErrorCoefficient : ℝ
  analyticErrorCoefficient_le_quarter :
    analyticErrorCoefficient ≤ relativeError * (1 / 4 : ℝ)
  majorArcContribution : Nat → ℝ
  minorArcContribution : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  rawDecomposition :
    ∀ n : Nat, decompositionThreshold < n → Even n →
      RawVonMangoldtGoldbachSum n =
        majorArcContribution n + minorArcContribution n
  majorArcApproximationBound :
    ∀ n : Nat, majorArcThreshold < n → Even n →
      |majorArcContribution n -
          goldbachSingularSeriesFromQuarter n * (n : ℝ)| ≤
        majorArcError n
  minorArcContributionBound :
    ∀ n : Nat, minorArcThreshold < n → Even n →
      |minorArcContribution n| ≤ minorArcError n
  totalLinearErrorBound :
    ∀ n : Nat, totalLinearErrorThreshold < n → Even n →
      majorArcError n + minorArcError n ≤
        analyticErrorCoefficient * (n : ℝ)

noncomputable def
    VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate.toMajorMinorDecomposition
    (estimate :
      VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate) :
    VonMangoldtQuarterSplitThresholdHardyLittlewoodMajorMinorDecompositionCanonicalWeightSumEstimate where
  decompositionThreshold := estimate.decompositionThreshold
  majorArcThreshold := estimate.majorArcThreshold
  minorArcThreshold := estimate.minorArcThreshold
  totalAnalyticErrorThreshold := estimate.totalLinearErrorThreshold
  relativeError := estimate.relativeError
  relativeError_lt_one := estimate.relativeError_lt_one
  majorArcContribution := estimate.majorArcContribution
  minorArcContribution := estimate.minorArcContribution
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  rawDecomposition := estimate.rawDecomposition
  majorArcApproximationBound := estimate.majorArcApproximationBound
  minorArcContributionBound := estimate.minorArcContributionBound
  totalAnalyticErrorBound :=
    total_analytic_error_bound_of_quarter_linear_error_bound
      estimate.relativeError_nonneg
      estimate.analyticErrorCoefficient_le_quarter
      estimate.totalLinearErrorBound

noncomputable def
    VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate.canonicalContaminationThreshold
    (estimate :
      VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate) :
    Nat :=
  estimate.toMajorMinorDecomposition.canonicalContaminationThreshold

noncomputable def
    VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toMajorMinorDecomposition.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate)
    (hdecomposition : estimate.decompositionThreshold ≤ B)
    (hmajor : estimate.majorArcThreshold ≤ B)
    (hminor : estimate.minorArcThreshold ≤ B)
    (htotal : estimate.totalLinearErrorThreshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B :=
  estimate.toMajorMinorDecomposition.directRawWeightSumThreshold_le_of_components
    hdecomposition hmajor hminor htotal hcontamination

theorem
    count_positive_above_of_vonMangoldt_quarter_linear_error_decomposition_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_decomposition_canonical_weight_sum_estimate
    estimate.toMajorMinorDecomposition

theorem
    explicit_lower_bound_of_vonMangoldt_quarter_linear_error_decomposition_canonical_weight_sum_estimate
    (estimate :
      VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_quarter_linear_error_decomposition_canonical_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_quarter_linear_error_decomposition_canonical_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_quarter_split_threshold_hardy_littlewood_major_minor_decomposition_canonical_weight_sum_estimate_le
    finite
    estimate.toMajorMinorDecomposition
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_quarter_linear_error_decomposition_canonical_weight_sum_estimate_le100
    (estimate :
      VonMangoldtQuarterLinearErrorDecompositionCanonicalWeightSumEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_quarter_linear_error_decomposition_canonical_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

structure VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate where
  threshold : Nat
  coefficient : ℝ
  relativeError : ℝ
  coefficient_pos : 0 < coefficient
  relativeError_lt_one : relativeError < 1
  singularSeries : Nat → ℝ
  nonPrimePrimePowerWeightSumBound : Nat → ℝ
  singularSeriesLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      coefficient ≤ singularSeries n
  rawNormalizedErrorBound :
    ∀ n : Nat, threshold < n → Even n →
      |(RawVonMangoldtGoldbachSum n -
          singularSeries n * (n : ℝ)) /
        (singularSeries n * (n : ℝ))| ≤ relativeError
  nonPrimePrimePowerWeightSumBoundValid :
    ∀ n : Nat, threshold < n → Even n →
      NonPrimePrimePowerVonMangoldtWeightSum n ≤
        nonPrimePrimePowerWeightSumBound n
  contaminationDominated :
    ∀ n : Nat, threshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        nonPrimePrimePowerWeightSumBound n <
        ((1 - relativeError) * coefficient) * (n : ℝ)

noncomputable def
    VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate.toHardyLittlewoodNormalizedEstimate
    (estimate :
      VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate) :
    VonMangoldtHardyLittlewoodNormalizedEstimate where
  threshold := estimate.threshold
  coefficient := estimate.coefficient
  relativeError := estimate.relativeError
  coefficient_pos := estimate.coefficient_pos
  relativeError_lt_one := estimate.relativeError_lt_one
  singularSeries := estimate.singularSeries
  singularSeriesLowerBound := estimate.singularSeriesLowerBound
  rawNormalizedErrorBound := estimate.rawNormalizedErrorBound

noncomputable def
    VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound where
  threshold := estimate.threshold
  nonPrimePrimePowerWeightSumBound :=
    estimate.nonPrimePrimePowerWeightSumBound
  nonPrimePrimePowerWeightSumBoundValid :=
    estimate.nonPrimePrimePowerWeightSumBoundValid
  rawLowerBound := by
    intro n htn hEven
    have hraw :=
      estimate.toHardyLittlewoodNormalizedEstimate.toPositiveLinearRawLowerBound.rawLinearLowerBound
        n htn hEven
    have hcont := estimate.contaminationDominated n htn hEven
    exact hcont.trans_le
      (by
        simpa
          [VonMangoldtHardyLittlewoodNormalizedEstimate.effectiveCoefficient]
          using hraw)

theorem
    count_positive_above_of_vonMangoldt_hardy_littlewood_normalized_weight_sum_estimate
    (estimate :
      VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate) :
    GoldbachCountPositiveAbove estimate.threshold :=
  count_positive_above_of_vonMangoldt_direct_raw_weight_sum_lower_bound
    estimate.toDirectRawWeightSumLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_hardy_littlewood_normalized_weight_sum_estimate
    (estimate :
      VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate) :
    ExplicitGoldbachLowerBound estimate.threshold :=
  count_positive_above_of_vonMangoldt_hardy_littlewood_normalized_weight_sum_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_weight_sum_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate)
    (hthreshold : estimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_direct_raw_weight_sum_lower_bound_le
    finite
    estimate.toDirectRawWeightSumLowerBound
    (by
      simpa
        [VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate.toDirectRawWeightSumLowerBound]
        using hthreshold)

theorem
    strongGoldbach_of_vonMangoldt_hardy_littlewood_normalized_weight_sum_estimate_le100
    (estimate :
      VonMangoldtHardyLittlewoodNormalizedWeightSumEstimate)
    (hthreshold : estimate.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_hardy_littlewood_normalized_weight_sum_estimate_le
    goldbachUpTo100
    estimate
    hthreshold

structure VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate where
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  combinedLowerBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  linearNetLowerBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      coefficient * (n : ℝ) + minorArcError n ≤
        mainTerm n - majorArcError n

noncomputable def
    VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate.toEventuallyPositiveLinearRawLowerBound
    (estimate : VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate) :
    VonMangoldtEventuallyPositiveLinearRawLowerBound where
  coefficient := estimate.coefficient
  coefficient_pos := estimate.coefficient_pos
  rawLinearLowerBoundEventually := by
    filter_upwards
      [estimate.combinedLowerBoundEventually,
        estimate.linearNetLowerBoundEventually] with n hcombined hnet hEven
    have hle :
        estimate.coefficient * (n : ℝ) + estimate.minorArcError n ≤
          RawVonMangoldtGoldbachSum n + estimate.minorArcError n :=
      (hnet hEven).trans (hcombined hEven)
    linarith

noncomputable def
    VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate.toSqrtLogCountLinearRawLowerBound
    (estimate : VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate) :
    VonMangoldtSqrtLogCountLinearRawLowerBound :=
  estimate.toEventuallyPositiveLinearRawLowerBound.toSqrtLogCountLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate.toDirectRawWeightSumLowerBound
    (estimate : VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toEventuallyPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound

theorem count_positive_above_of_vonMangoldt_eventually_positive_linear_major_minor_arc_estimate
    (estimate : VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove
      estimate.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_sqrt_log_count_linear_raw_lower_bound
    estimate.toSqrtLogCountLinearRawLowerBound

theorem explicit_lower_bound_of_vonMangoldt_eventually_positive_linear_major_minor_arc_estimate
    (estimate : VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_positive_linear_major_minor_arc_estimate
    estimate

theorem strongGoldbach_of_finite_and_vonMangoldt_eventually_positive_linear_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate)
    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_sqrt_log_count_linear_raw_lower_bound_le
    finite
    estimate.toSqrtLogCountLinearRawLowerBound
    hthreshold

theorem strongGoldbach_of_finite_and_vonMangoldt_eventually_positive_linear_major_minor_arc_estimate_weight_sum_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_direct_raw_weight_sum_lower_bound_le
    finite
    estimate.toDirectRawWeightSumLowerBound
    hthreshold

structure VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate where
  coefficient : ℝ
  relativeError : ℝ
  coefficient_pos : 0 < coefficient
  relativeError_lt_one : relativeError < 1
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  mainTermLowerBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      coefficient * (n : ℝ) ≤ mainTerm n
  combinedLowerBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  totalAnalyticErrorBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      majorArcError n + minorArcError n ≤ relativeError * mainTerm n

def
    VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate.effectiveCoefficient
    (estimate :
      VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate) :
    ℝ :=
  (1 - estimate.relativeError) * estimate.coefficient

theorem
    VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate.effectiveCoefficient_pos
    (estimate :
      VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate) :
    0 < estimate.effectiveCoefficient := by
  dsimp
    [VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate.effectiveCoefficient]
  have hfactor : 0 < 1 - estimate.relativeError := by
    linarith [estimate.relativeError_lt_one]
  exact mul_pos hfactor estimate.coefficient_pos

noncomputable def
    VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate.toEventuallyPositiveLinearMajorMinorArcEstimate
    (estimate :
      VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate) :
    VonMangoldtEventuallyPositiveLinearMajorMinorArcEstimate where
  coefficient := estimate.effectiveCoefficient
  coefficient_pos := estimate.effectiveCoefficient_pos
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  combinedLowerBoundEventually :=
    estimate.combinedLowerBoundEventually
  linearNetLowerBoundEventually := by
    filter_upwards
      [estimate.mainTermLowerBoundEventually,
        estimate.totalAnalyticErrorBoundEventually] with n hmain herror hEven
    have hfactor_nonneg : 0 ≤ 1 - estimate.relativeError := by
      linarith [estimate.relativeError_lt_one]
    have hscaled :
        (1 - estimate.relativeError) *
            (estimate.coefficient * (n : ℝ)) ≤
          (1 - estimate.relativeError) * estimate.mainTerm n :=
      mul_le_mul_of_nonneg_left (hmain hEven) hfactor_nonneg
    have heff :
        estimate.effectiveCoefficient * (n : ℝ) ≤
          estimate.mainTerm n -
            estimate.relativeError * estimate.mainTerm n := by
      calc
        estimate.effectiveCoefficient * (n : ℝ)
            = (1 - estimate.relativeError) *
                (estimate.coefficient * (n : ℝ)) := by
              rw
                [VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate.effectiveCoefficient]
              ring
        _ ≤ (1 - estimate.relativeError) * estimate.mainTerm n :=
            hscaled
        _ = estimate.mainTerm n -
              estimate.relativeError * estimate.mainTerm n := by
            ring
    have herror' := herror hEven
    linarith

noncomputable def
    VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate.toSqrtLogCountLinearRawLowerBound
    (estimate :
      VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate) :
    VonMangoldtSqrtLogCountLinearRawLowerBound :=
  estimate.toEventuallyPositiveLinearMajorMinorArcEstimate.toSqrtLogCountLinearRawLowerBound

noncomputable def
    VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toEventuallyPositiveLinearMajorMinorArcEstimate.toDirectRawWeightSumLowerBound

theorem
    count_positive_above_of_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_arc_estimate
    (estimate :
      VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove
      estimate.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_positive_linear_major_minor_arc_estimate
    estimate.toEventuallyPositiveLinearMajorMinorArcEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_arc_estimate
    (estimate :
      VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_arc_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate)
    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_positive_linear_major_minor_arc_estimate_le
    finite
    estimate.toEventuallyPositiveLinearMajorMinorArcEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_arc_estimate_le100
    (estimate :
      VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate)
    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_sqrt_log_count_linear_raw_lower_bound_le100
    estimate.toSqrtLogCountLinearRawLowerBound
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_arc_estimate_weight_sum_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_positive_linear_major_minor_arc_estimate_weight_sum_le
    finite
    estimate.toEventuallyPositiveLinearMajorMinorArcEstimate
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_eventually_relative_error_sqrt_log_count_major_minor_arc_estimate_weight_sum_le100
    (estimate :
      VonMangoldtEventuallyRelativeErrorSqrtLogCountMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_direct_raw_weight_sum_lower_bound_le100
    estimate.toDirectRawWeightSumLowerBound
    hthreshold

structure VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate where
  mainTermThreshold : Nat
  combinedThreshold : Nat
  totalAnalyticErrorThreshold : Nat
  coefficient : ℝ
  relativeError : ℝ
  coefficient_pos : 0 < coefficient
  relativeError_lt_one : relativeError < 1
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  mainTermLowerBound :
    ∀ n : Nat, mainTermThreshold < n → Even n →
      coefficient * (n : ℝ) ≤ mainTerm n
  combinedLowerBound :
    ∀ n : Nat, combinedThreshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  totalAnalyticErrorBound :
    ∀ n : Nat, totalAnalyticErrorThreshold < n → Even n →
      majorArcError n + minorArcError n ≤ relativeError * mainTerm n

def VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate.threshold
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate) :
    Nat :=
  max estimate.mainTermThreshold
    (max estimate.combinedThreshold estimate.totalAnalyticErrorThreshold)

theorem
    VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate.mainTermThreshold_le_threshold
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate) :
    estimate.mainTermThreshold ≤ estimate.threshold := by
  dsimp
    [VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate.threshold]
  exact Nat.le_max_left _ _

theorem
    VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate.combinedThreshold_le_threshold
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate) :
    estimate.combinedThreshold ≤ estimate.threshold := by
  dsimp
    [VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate.threshold]
  exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

theorem
    VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate.totalAnalyticErrorThreshold_le_threshold
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate) :
    estimate.totalAnalyticErrorThreshold ≤ estimate.threshold := by
  dsimp
    [VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate.threshold]
  exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

def
    VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate.effectiveCoefficient
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate) :
    ℝ :=
  (1 - estimate.relativeError) * estimate.coefficient

theorem
    VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate.effectiveCoefficient_pos
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate) :
    0 < estimate.effectiveCoefficient := by
  dsimp
    [VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate.effectiveCoefficient]
  have hfactor : 0 < 1 - estimate.relativeError := by
    linarith [estimate.relativeError_lt_one]
  exact mul_pos hfactor estimate.coefficient_pos

noncomputable def
    VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate.toPositiveLinearRawLowerBound
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate) :
    VonMangoldtPositiveLinearRawLowerBound where
  threshold := estimate.threshold
  coefficient := estimate.effectiveCoefficient
  coefficient_pos := estimate.effectiveCoefficient_pos
  rawLinearLowerBound := by
    intro n htn hEven
    have hmain_threshold : estimate.mainTermThreshold < n :=
      lt_of_le_of_lt estimate.mainTermThreshold_le_threshold htn
    have hcombined_threshold : estimate.combinedThreshold < n :=
      lt_of_le_of_lt estimate.combinedThreshold_le_threshold htn
    have herror_threshold : estimate.totalAnalyticErrorThreshold < n :=
      lt_of_le_of_lt estimate.totalAnalyticErrorThreshold_le_threshold htn
    have hfactor_nonneg : 0 ≤ 1 - estimate.relativeError := by
      linarith [estimate.relativeError_lt_one]
    have hmain := estimate.mainTermLowerBound n hmain_threshold hEven
    have hcombined :=
      estimate.combinedLowerBound n hcombined_threshold hEven
    have herror :=
      estimate.totalAnalyticErrorBound n herror_threshold hEven
    have hscaled :
        (1 - estimate.relativeError) *
            (estimate.coefficient * (n : ℝ)) ≤
          (1 - estimate.relativeError) * estimate.mainTerm n :=
      mul_le_mul_of_nonneg_left hmain hfactor_nonneg
    have heff :
        estimate.effectiveCoefficient * (n : ℝ) ≤
          estimate.mainTerm n -
            estimate.relativeError * estimate.mainTerm n := by
      calc
        estimate.effectiveCoefficient * (n : ℝ)
            = (1 - estimate.relativeError) *
                (estimate.coefficient * (n : ℝ)) := by
              rw
                [VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate.effectiveCoefficient]
              ring
        _ ≤ (1 - estimate.relativeError) * estimate.mainTerm n :=
            hscaled
        _ = estimate.mainTerm n -
              estimate.relativeError * estimate.mainTerm n := by
            ring
    have hraw :
        estimate.mainTerm n -
            estimate.relativeError * estimate.mainTerm n ≤
          RawVonMangoldtGoldbachSum n := by
      linarith
    exact heff.trans hraw

noncomputable def
    VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate.toSqrtLogCountLinearRawLowerBound
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate) :
    VonMangoldtSqrtLogCountLinearRawLowerBound :=
  estimate.toPositiveLinearRawLowerBound.toSqrtLogCountLinearRawLowerBound

noncomputable def
    VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toPositiveLinearRawLowerBound.toDirectRawWeightSumLowerBound

theorem
    count_positive_above_of_vonMangoldt_split_threshold_relative_error_sqrt_log_count_major_minor_arc_estimate
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove
      estimate.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_positive_linear_raw_lower_bound
    estimate.toPositiveLinearRawLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_split_threshold_relative_error_sqrt_log_count_major_minor_arc_estimate
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toSqrtLogCountLinearRawLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_split_threshold_relative_error_sqrt_log_count_major_minor_arc_estimate
    estimate

theorem
    strongGoldbach_of_finite_and_vonMangoldt_split_threshold_relative_error_sqrt_log_count_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate)
    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_lower_bound_le
    finite
    estimate.toPositiveLinearRawLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_split_threshold_relative_error_sqrt_log_count_major_minor_arc_estimate_le100
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate)
    (hthreshold : estimate.toSqrtLogCountLinearRawLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_sqrt_log_count_linear_raw_lower_bound_le100
    estimate.toSqrtLogCountLinearRawLowerBound
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_split_threshold_relative_error_sqrt_log_count_major_minor_arc_estimate_weight_sum_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_positive_linear_raw_lower_bound_weight_sum_le
    finite
    estimate.toPositiveLinearRawLowerBound
    hthreshold

theorem
    strongGoldbach_of_vonMangoldt_split_threshold_relative_error_sqrt_log_count_major_minor_arc_estimate_weight_sum_le100
    (estimate :
      VonMangoldtSplitThresholdRelativeErrorSqrtLogCountMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_direct_raw_weight_sum_lower_bound_le100
    estimate.toDirectRawWeightSumLowerBound
    hthreshold

structure VonMangoldtEventuallyPositiveLinearWeightSumMajorMinorArcEstimate where
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  nonPrimePrimePowerWeightSumBound : Nat → ℝ
  combinedLowerBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  linearNetLowerBoundEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      coefficient * (n : ℝ) + minorArcError n ≤
        mainTerm n - majorArcError n
  nonPrimePrimePowerWeightSumBoundValidEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      NonPrimePrimePowerVonMangoldtWeightSum n ≤
        nonPrimePrimePowerWeightSumBound n
  contaminationDominatedEventually :
    ∀ᶠ n : Nat in Filter.atTop, Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        nonPrimePrimePowerWeightSumBound n <
        coefficient * (n : ℝ)

noncomputable def
    VonMangoldtEventuallyPositiveLinearWeightSumMajorMinorArcEstimate.toEventuallyPositiveLinearRawWeightSumLowerBound
    (estimate : VonMangoldtEventuallyPositiveLinearWeightSumMajorMinorArcEstimate) :
    VonMangoldtEventuallyPositiveLinearRawWeightSumLowerBound where
  coefficient := estimate.coefficient
  coefficient_pos := estimate.coefficient_pos
  nonPrimePrimePowerWeightSumBound :=
    estimate.nonPrimePrimePowerWeightSumBound
  nonPrimePrimePowerWeightSumBoundValidEventually :=
    estimate.nonPrimePrimePowerWeightSumBoundValidEventually
  rawLinearLowerBoundEventually := by
    filter_upwards
      [estimate.combinedLowerBoundEventually,
        estimate.linearNetLowerBoundEventually] with n hcombined hnet hEven
    have hle :
        estimate.coefficient * (n : ℝ) + estimate.minorArcError n ≤
          RawVonMangoldtGoldbachSum n + estimate.minorArcError n :=
      (hnet hEven).trans (hcombined hEven)
    linarith
  contaminationDominatedEventually :=
    estimate.contaminationDominatedEventually

noncomputable def
    VonMangoldtEventuallyPositiveLinearWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound
    (estimate : VonMangoldtEventuallyPositiveLinearWeightSumMajorMinorArcEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toEventuallyPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound

theorem
    count_positive_above_of_vonMangoldt_eventually_positive_linear_weight_sum_major_minor_arc_estimate
    (estimate : VonMangoldtEventuallyPositiveLinearWeightSumMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_positive_linear_raw_weight_sum_lower_bound
    estimate.toEventuallyPositiveLinearRawWeightSumLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_eventually_positive_linear_weight_sum_major_minor_arc_estimate
    (estimate : VonMangoldtEventuallyPositiveLinearWeightSumMajorMinorArcEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_eventually_positive_linear_weight_sum_major_minor_arc_estimate
    estimate

theorem
    strongGoldbach_of_vonMangoldt_eventually_positive_linear_weight_sum_major_minor_arc_estimate_le100
    (estimate : VonMangoldtEventuallyPositiveLinearWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_eventually_positive_linear_raw_weight_sum_lower_bound_le100
    estimate.toEventuallyPositiveLinearRawWeightSumLowerBound
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_eventually_positive_linear_weight_sum_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtEventuallyPositiveLinearWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_eventually_positive_linear_raw_weight_sum_lower_bound_le
    finite
    estimate.toEventuallyPositiveLinearRawWeightSumLowerBound
    hthreshold

structure VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate where
  combinedThreshold : Nat
  linearNetThreshold : Nat
  weightSumThreshold : Nat
  contaminationThreshold : Nat
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  nonPrimePrimePowerWeightSumBound : Nat → ℝ
  combinedLowerBound :
    ∀ n : Nat, combinedThreshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  linearNetLowerBound :
    ∀ n : Nat, linearNetThreshold < n → Even n →
      coefficient * (n : ℝ) + minorArcError n ≤
        mainTerm n - majorArcError n
  nonPrimePrimePowerWeightSumBoundValid :
    ∀ n : Nat, weightSumThreshold < n → Even n →
      NonPrimePrimePowerVonMangoldtWeightSum n ≤
        nonPrimePrimePowerWeightSumBound n
  contaminationDominated :
    ∀ n : Nat, contaminationThreshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        nonPrimePrimePowerWeightSumBound n <
        coefficient * (n : ℝ)

def VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate.rawThreshold
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate) :
    Nat :=
  max estimate.combinedThreshold estimate.linearNetThreshold

theorem
    VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate.combinedThreshold_le_rawThreshold
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate) :
    estimate.combinedThreshold ≤ estimate.rawThreshold := by
  dsimp
    [VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate.rawThreshold]
  exact Nat.le_max_left _ _

theorem
    VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate.linearNetThreshold_le_rawThreshold
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate) :
    estimate.linearNetThreshold ≤ estimate.rawThreshold := by
  dsimp
    [VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate.rawThreshold]
  exact Nat.le_max_right _ _

noncomputable def
    VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate.toSplitThresholdPositiveLinearRawWeightSumLowerBound
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate) :
    VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound where
  weightSumThreshold := estimate.weightSumThreshold
  rawThreshold := estimate.rawThreshold
  contaminationThreshold := estimate.contaminationThreshold
  coefficient := estimate.coefficient
  coefficient_pos := estimate.coefficient_pos
  nonPrimePrimePowerWeightSumBound :=
    estimate.nonPrimePrimePowerWeightSumBound
  nonPrimePrimePowerWeightSumBoundValid := by
    intro n hweight hEven
    exact estimate.nonPrimePrimePowerWeightSumBoundValid n hweight hEven
  rawLinearLowerBound := by
    intro n hraw hEven
    have hcombined : estimate.combinedThreshold < n :=
      lt_of_le_of_lt estimate.combinedThreshold_le_rawThreshold hraw
    have hlinear : estimate.linearNetThreshold < n :=
      lt_of_le_of_lt estimate.linearNetThreshold_le_rawThreshold hraw
    have hcombinedBound :=
      estimate.combinedLowerBound n hcombined hEven
    have hlinearBound :=
      estimate.linearNetLowerBound n hlinear hEven
    have hle :
        estimate.coefficient * (n : ℝ) + estimate.minorArcError n ≤
          RawVonMangoldtGoldbachSum n + estimate.minorArcError n :=
      hlinearBound.trans hcombinedBound
    linarith
  contaminationDominated := by
    intro n hcontamination hEven
    exact estimate.contaminationDominated n hcontamination hEven

noncomputable def
    VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toSplitThresholdPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound

theorem
    count_positive_above_of_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound
    estimate.toSplitThresholdPositiveLinearRawWeightSumLowerBound

theorem
    explicit_lower_bound_of_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate
    estimate

theorem
    strongGoldbach_of_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate_le100
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound_le100
    estimate.toSplitThresholdPositiveLinearRawWeightSumLowerBound
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_positive_linear_raw_weight_sum_lower_bound_le
    finite
    estimate.toSplitThresholdPositiveLinearRawWeightSumLowerBound
    hthreshold

structure
    VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate where
  combinedThreshold : Nat
  linearNetThreshold : Nat
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  combinedLowerBound :
    ∀ n : Nat, combinedThreshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  linearNetLowerBound :
    ∀ n : Nat, linearNetThreshold < n → Even n →
      coefficient * (n : ℝ) + minorArcError n ≤
        mainTerm n - majorArcError n

def
    VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate.rawThreshold
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate) :
    Nat :=
  max estimate.combinedThreshold estimate.linearNetThreshold

theorem
    VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate.combinedThreshold_le_rawThreshold
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate) :
    estimate.combinedThreshold ≤ estimate.rawThreshold := by
  dsimp
    [VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate.rawThreshold]
  exact Nat.le_max_left _ _

theorem
    VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate.linearNetThreshold_le_rawThreshold
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate) :
    estimate.linearNetThreshold ≤ estimate.rawThreshold := by
  dsimp
    [VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate.rawThreshold]
  exact Nat.le_max_right _ _

noncomputable def
    VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate.canonicalContaminationThreshold
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate) :
    Nat :=
  canonicalLinearContaminationThreshold estimate.coefficient
    estimate.coefficient_pos

noncomputable def
    VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate.toSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate) :
    VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate where
  combinedThreshold := estimate.combinedThreshold
  linearNetThreshold := estimate.linearNetThreshold
  weightSumThreshold := estimate.rawThreshold
  contaminationThreshold := estimate.canonicalContaminationThreshold
  coefficient := estimate.coefficient
  coefficient_pos := estimate.coefficient_pos
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  nonPrimePrimePowerWeightSumBound :=
    canonicalNonPrimePrimePowerVonMangoldtWeightSumBound
  combinedLowerBound := estimate.combinedLowerBound
  linearNetLowerBound := estimate.linearNetLowerBound
  nonPrimePrimePowerWeightSumBoundValid := by
    intro n hraw hEven
    exact canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_valid
      n hraw hEven
  contaminationDominated := by
    intro n hcontamination _hEven
    exact canonicalLinearContaminationThreshold_spec
      estimate.coefficient_pos n (le_of_lt hcontamination)

noncomputable def
    VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate.directRawWeightSumThreshold_eq
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate) :
    estimate.toDirectRawWeightSumLowerBound.threshold =
      max estimate.rawThreshold estimate.canonicalContaminationThreshold := by
  dsimp
    [VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound,
      VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate.toSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate,
      VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound,
      VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate.toSplitThresholdPositiveLinearRawWeightSumLowerBound,
      VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate.rawThreshold,
      VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate.rawThreshold,
      VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound,
      VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.toPositiveLinearRawWeightSumLowerBound,
      VonMangoldtPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound,
      VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.threshold]
  rw [← Nat.max_assoc, Nat.max_self]

theorem
    VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate)
    (hcombined : estimate.combinedThreshold ≤ B)
    (hlinear : estimate.linearNetThreshold ≤ B)
    (hcontamination : estimate.canonicalContaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B := by
  rw [estimate.directRawWeightSumThreshold_eq]
  exact max_le (max_le hcombined hlinear) hcontamination

theorem
    count_positive_above_of_vonMangoldt_split_threshold_positive_linear_canonical_weight_sum_major_minor_arc_estimate
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate
    estimate.toSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_split_threshold_positive_linear_canonical_weight_sum_major_minor_arc_estimate
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_split_threshold_positive_linear_canonical_weight_sum_major_minor_arc_estimate
    estimate

theorem
    strongGoldbach_of_vonMangoldt_split_threshold_positive_linear_canonical_weight_sum_major_minor_arc_estimate_le100
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate_le100
    estimate.toSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_split_threshold_positive_linear_canonical_weight_sum_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearCanonicalWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate_le
    finite
    estimate.toSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate
    hthreshold

structure
    VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate where
  combinedThreshold : Nat
  linearNetThreshold : Nat
  contaminationThreshold : Nat
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  combinedLowerBound :
    ∀ n : Nat, combinedThreshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  linearNetLowerBound :
    ∀ n : Nat, linearNetThreshold < n → Even n →
      coefficient * (n : ℝ) + minorArcError n ≤
        mainTerm n - majorArcError n
  contaminationDominated :
    ∀ n : Nat, contaminationThreshold < n → Even n →
      2 * vonMangoldtWeightSumContaminationBudget
        canonicalNonPrimePrimePowerVonMangoldtWeightSumBound n <
        coefficient * (n : ℝ)

def
    VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate.rawThreshold
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate) :
    Nat :=
  max estimate.combinedThreshold estimate.linearNetThreshold

theorem
    VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate.combinedThreshold_le_rawThreshold
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate) :
    estimate.combinedThreshold ≤ estimate.rawThreshold := by
  dsimp
    [VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate.rawThreshold]
  exact Nat.le_max_left _ _

theorem
    VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate.linearNetThreshold_le_rawThreshold
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate) :
    estimate.linearNetThreshold ≤ estimate.rawThreshold := by
  dsimp
    [VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate.rawThreshold]
  exact Nat.le_max_right _ _

noncomputable def
    VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate.toSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate) :
    VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate where
  combinedThreshold := estimate.combinedThreshold
  linearNetThreshold := estimate.linearNetThreshold
  weightSumThreshold := estimate.rawThreshold
  contaminationThreshold := estimate.contaminationThreshold
  coefficient := estimate.coefficient
  coefficient_pos := estimate.coefficient_pos
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  nonPrimePrimePowerWeightSumBound :=
    canonicalNonPrimePrimePowerVonMangoldtWeightSumBound
  combinedLowerBound := estimate.combinedLowerBound
  linearNetLowerBound := estimate.linearNetLowerBound
  nonPrimePrimePowerWeightSumBoundValid := by
    intro n hraw hEven
    exact canonicalNonPrimePrimePowerVonMangoldtWeightSumBound_valid
      n hraw hEven
  contaminationDominated := estimate.contaminationDominated

noncomputable def
    VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate) :
    VonMangoldtDirectRawWeightSumLowerBound :=
  estimate.toSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound

theorem
    VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate.directRawWeightSumThreshold_eq
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate) :
    estimate.toDirectRawWeightSumLowerBound.threshold =
      max estimate.rawThreshold estimate.contaminationThreshold := by
  dsimp
    [VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound,
      VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate.toSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate,
      VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate.toDirectRawWeightSumLowerBound,
      VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate.toSplitThresholdPositiveLinearRawWeightSumLowerBound,
      VonMangoldtSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate.rawThreshold,
      VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate.rawThreshold,
      VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound,
      VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.toPositiveLinearRawWeightSumLowerBound,
      VonMangoldtPositiveLinearRawWeightSumLowerBound.toDirectRawWeightSumLowerBound,
      VonMangoldtSplitThresholdPositiveLinearRawWeightSumLowerBound.threshold]
  rw [← Nat.max_assoc, Nat.max_self]

theorem
    VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate.directRawWeightSumThreshold_le_of_components
    {B : Nat}
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate)
    (hcombined : estimate.combinedThreshold ≤ B)
    (hlinear : estimate.linearNetThreshold ≤ B)
    (hcontamination : estimate.contaminationThreshold ≤ B) :
    estimate.toDirectRawWeightSumLowerBound.threshold ≤ B := by
  rw [estimate.directRawWeightSumThreshold_eq]
  exact max_le (max_le hcombined hlinear) hcontamination

theorem
    count_positive_above_of_vonMangoldt_split_threshold_positive_linear_explicit_contamination_canonical_weight_sum_major_minor_arc_estimate
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate
    estimate.toSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate

theorem
    explicit_lower_bound_of_vonMangoldt_split_threshold_positive_linear_explicit_contamination_canonical_weight_sum_major_minor_arc_estimate
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate) :
    ExplicitGoldbachLowerBound
      estimate.toDirectRawWeightSumLowerBound.threshold :=
  count_positive_above_of_vonMangoldt_split_threshold_positive_linear_explicit_contamination_canonical_weight_sum_major_minor_arc_estimate
    estimate

theorem
    strongGoldbach_of_vonMangoldt_split_threshold_positive_linear_explicit_contamination_canonical_weight_sum_major_minor_arc_estimate_le100
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate_le100
    estimate.toSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate
    hthreshold

theorem
    strongGoldbach_of_finite_and_vonMangoldt_split_threshold_positive_linear_explicit_contamination_canonical_weight_sum_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate :
      VonMangoldtSplitThresholdPositiveLinearExplicitContaminationCanonicalWeightSumMajorMinorArcEstimate)
    (hthreshold : estimate.toDirectRawWeightSumLowerBound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_split_threshold_positive_linear_weight_sum_major_minor_arc_estimate_le
    finite
    estimate.toSplitThresholdPositiveLinearWeightSumMajorMinorArcEstimate
    hthreshold

structure VonMangoldtSqrtLogCountMajorMinorArcEstimate where
  threshold : Nat
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  combinedLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n +
          2 * vonMangoldtLogCountContaminationBudget
            nonPrimePrimePowerSqrtLogCountBound n <
        mainTerm n

noncomputable def VonMangoldtSqrtLogCountMajorMinorArcEstimate.toCanonicalLogCountContaminationEstimate
    (estimate : VonMangoldtSqrtLogCountMajorMinorArcEstimate) :
    VonMangoldtCanonicalLogCountContaminationMajorMinorArcEstimate where
  threshold := estimate.threshold
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  nonPrimePrimePowerCountBound := nonPrimePrimePowerSqrtLogCountBound
  combinedLowerBound := by
    intro n htn hEven
    exact estimate.combinedLowerBound n htn hEven
  nonPrimePrimePowerCountBoundValid := by
    intro n htn hEven
    exact nonPrimePrimePowerCount_real_le_sqrt_log_count_bound n
  totalErrorDominated := by
    intro n htn hEven
    exact estimate.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_sqrt_log_count_major_minor_arc_estimate
    (estimate : VonMangoldtSqrtLogCountMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove estimate.threshold :=
  count_positive_above_of_vonMangoldt_canonical_log_count_contamination_major_minor_arc_estimate
    estimate.toCanonicalLogCountContaminationEstimate

theorem explicit_lower_bound_of_vonMangoldt_sqrt_log_count_major_minor_arc_estimate
    (estimate : VonMangoldtSqrtLogCountMajorMinorArcEstimate) :
    ExplicitGoldbachLowerBound estimate.threshold :=
  count_positive_above_of_vonMangoldt_sqrt_log_count_major_minor_arc_estimate
    estimate

theorem strongGoldbach_of_vonMangoldt_sqrt_log_count_major_minor_arc_estimate_le100
    (estimate : VonMangoldtSqrtLogCountMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_canonical_log_count_contamination_major_minor_arc_estimate_le100
    estimate.toCanonicalLogCountContaminationEstimate
    (by
      simpa
        [VonMangoldtSqrtLogCountMajorMinorArcEstimate.toCanonicalLogCountContaminationEstimate]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_sqrt_log_count_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtSqrtLogCountMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_canonical_log_count_contamination_major_minor_arc_estimate_le
    finite
    estimate.toCanonicalLogCountContaminationEstimate
    (by
      simpa
        [VonMangoldtSqrtLogCountMajorMinorArcEstimate.toCanonicalLogCountContaminationEstimate]
        using hthreshold)

structure VonMangoldtCanonicalLogContaminationLowerBound where
  threshold : Nat
  mainTerm : Nat → ℝ
  analyticError : Nat → ℝ
  lowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - analyticError n ≤ RawVonMangoldtGoldbachSum n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      analyticError n + 2 * vonMangoldtLogContaminationBudget n <
        mainTerm n

noncomputable def VonMangoldtCanonicalLogContaminationLowerBound.toLogWeightLowerBound
    (bound : VonMangoldtCanonicalLogContaminationLowerBound) :
    VonMangoldtLogWeightSplitContaminationLowerBound where
  threshold := bound.threshold
  mainTerm := bound.mainTerm
  analyticError := bound.analyticError
  leftContamination := vonMangoldtLogContaminationBudget
  rightContamination := vonMangoldtLogContaminationBudget
  lowerBound := by
    intro n htn hEven
    exact bound.lowerBound n htn hEven
  leftProductBound := by
    intro n htn hEven
    simp [vonMangoldtLogContaminationBudget]
  rightProductBound := by
    intro n htn hEven
    simp [vonMangoldtLogContaminationBudget]
  totalErrorDominated := by
    intro n htn hEven
    simpa [vonMangoldtLogContaminationBudget, two_mul, add_assoc] using
      bound.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_canonical_log_contamination_lower_bound
    (bound : VonMangoldtCanonicalLogContaminationLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_vonMangoldt_log_weight_split_contamination_lower_bound
    bound.toLogWeightLowerBound

theorem strongGoldbach_of_vonMangoldt_canonical_log_contamination_lower_bound_le100
    (bound : VonMangoldtCanonicalLogContaminationLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_log_weight_split_contamination_lower_bound_le100
    bound.toLogWeightLowerBound
    (by
      simpa
        [VonMangoldtCanonicalLogContaminationLowerBound.toLogWeightLowerBound]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_canonical_log_contamination_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtCanonicalLogContaminationLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_log_weight_split_contamination_lower_bound_le
    finite
    bound.toLogWeightLowerBound
    (by
      simpa
        [VonMangoldtCanonicalLogContaminationLowerBound.toLogWeightLowerBound]
        using hthreshold)

structure VonMangoldtCanonicalLogContaminationMajorMinorArcEstimate where
  threshold : Nat
  mainTerm : Nat → ℝ
  majorArcError : Nat → ℝ
  minorArcError : Nat → ℝ
  combinedLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      mainTerm n - majorArcError n ≤
        RawVonMangoldtGoldbachSum n + minorArcError n
  totalErrorDominated :
    ∀ n : Nat, threshold < n → Even n →
      majorArcError n + minorArcError n +
          2 * vonMangoldtLogContaminationBudget n <
        mainTerm n

noncomputable def VonMangoldtCanonicalLogContaminationMajorMinorArcEstimate.toLogWeightEstimate
    (estimate : VonMangoldtCanonicalLogContaminationMajorMinorArcEstimate) :
    VonMangoldtLogWeightSplitContaminationMajorMinorArcEstimate where
  threshold := estimate.threshold
  mainTerm := estimate.mainTerm
  majorArcError := estimate.majorArcError
  minorArcError := estimate.minorArcError
  leftContamination := vonMangoldtLogContaminationBudget
  rightContamination := vonMangoldtLogContaminationBudget
  combinedLowerBound := by
    intro n htn hEven
    exact estimate.combinedLowerBound n htn hEven
  leftProductBound := by
    intro n htn hEven
    simp [vonMangoldtLogContaminationBudget]
  rightProductBound := by
    intro n htn hEven
    simp [vonMangoldtLogContaminationBudget]
  totalErrorDominated := by
    intro n htn hEven
    simpa [vonMangoldtLogContaminationBudget, two_mul, add_assoc] using
      estimate.totalErrorDominated n htn hEven

theorem count_positive_above_of_vonMangoldt_canonical_log_contamination_major_minor_arc_estimate
    (estimate : VonMangoldtCanonicalLogContaminationMajorMinorArcEstimate) :
    GoldbachCountPositiveAbove estimate.threshold :=
  count_positive_above_of_vonMangoldt_log_weight_split_contamination_major_minor_arc_estimate
    estimate.toLogWeightEstimate

theorem strongGoldbach_of_vonMangoldt_canonical_log_contamination_major_minor_arc_estimate_le100
    (estimate : VonMangoldtCanonicalLogContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_log_weight_split_contamination_major_minor_arc_estimate_le100
    estimate.toLogWeightEstimate
    (by
      simpa
        [VonMangoldtCanonicalLogContaminationMajorMinorArcEstimate.toLogWeightEstimate]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_canonical_log_contamination_major_minor_arc_estimate_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (estimate : VonMangoldtCanonicalLogContaminationMajorMinorArcEstimate)
    (hthreshold : estimate.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_log_weight_split_contamination_major_minor_arc_estimate_le
    finite
    estimate.toLogWeightEstimate
    (by
      simpa
        [VonMangoldtCanonicalLogContaminationMajorMinorArcEstimate.toLogWeightEstimate]
        using hthreshold)

structure VonMangoldtDirectRawLogLowerBound where
  threshold : Nat
  rawLowerBound :
    ∀ n : Nat, threshold < n → Even n →
      2 * vonMangoldtLogContaminationBudget n <
        RawVonMangoldtGoldbachSum n

noncomputable def VonMangoldtDirectRawLogLowerBound.toCanonicalLogContaminationLowerBound
    (bound : VonMangoldtDirectRawLogLowerBound) :
    VonMangoldtCanonicalLogContaminationLowerBound where
  threshold := bound.threshold
  mainTerm := RawVonMangoldtGoldbachSum
  analyticError := fun _ => 0
  lowerBound := by
    intro n htn hEven
    simp
  totalErrorDominated := by
    intro n htn hEven
    simpa using bound.rawLowerBound n htn hEven

theorem count_positive_above_of_vonMangoldt_direct_raw_log_lower_bound
    (bound : VonMangoldtDirectRawLogLowerBound) :
    GoldbachCountPositiveAbove bound.threshold :=
  count_positive_above_of_vonMangoldt_canonical_log_contamination_lower_bound
    bound.toCanonicalLogContaminationLowerBound

theorem strongGoldbach_of_vonMangoldt_direct_raw_log_lower_bound_le100
    (bound : VonMangoldtDirectRawLogLowerBound)
    (hthreshold : bound.threshold ≤ 100) :
    StrongGoldbach :=
  strongGoldbach_of_vonMangoldt_canonical_log_contamination_lower_bound_le100
    bound.toCanonicalLogContaminationLowerBound
    (by
      simpa
        [VonMangoldtDirectRawLogLowerBound.toCanonicalLogContaminationLowerBound]
        using hthreshold)

theorem strongGoldbach_of_finite_and_vonMangoldt_direct_raw_log_lower_bound_le
    {B : Nat}
    (finite : GoldbachUpTo B)
    (bound : VonMangoldtDirectRawLogLowerBound)
    (hthreshold : bound.threshold ≤ B) :
    StrongGoldbach :=
  strongGoldbach_of_finite_and_vonMangoldt_canonical_log_contamination_lower_bound_le
    finite
    bound.toCanonicalLogContaminationLowerBound
    (by
      simpa
        [VonMangoldtDirectRawLogLowerBound.toCanonicalLogContaminationLowerBound]
        using hthreshold)

end Gdbh
