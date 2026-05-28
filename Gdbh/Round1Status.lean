import Gdbh.AnalyticBridge
import Gdbh.Certificate50000
import Gdbh.PathA_Final
import Gdbh.PathC_KGoldbachUnconditional
import Gdbh.PathC_KEstimate

namespace Gdbh
namespace Round1Status

/-!
# Round 1 status bridges

This file records the current formally checked Round 1 frontier.  It does
not prove Goldbach.  It names the remaining global target and packages the
four Path C residual inputs that are still needed before the K-Goldbach
fallback can be claimed unconditionally.
-/

/-- The current global Lean target after the finite certificate up to `100`. -/
def CurrentFormalTarget : Prop :=
  ExplicitGoldbachLowerBound 100

/-- The intermediate target after using a chunked finite certificate up to
`10000`.  The current root module proves its status via the stronger `50000`
certificate. -/
def CurrentFormalTarget10000 : Prop :=
  ExplicitGoldbachLowerBound 10000

/-- The previous target after using the chunked finite certificate up to
`20000`.  The current root module proves its status via the stronger `50000`
certificate. -/
def CurrentFormalTarget20000 : Prop :=
  ExplicitGoldbachLowerBound 20000

/-- The strongest current target after using the chunked finite certificate up
to `50000`. -/
def CurrentFormalTarget50000 : Prop :=
  ExplicitGoldbachLowerBound 50000

/-- The exact binary Goldbach statement from `goal.md`. -/
def BinaryGoldbachConjecture : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- An even natural number greater than two is at least four. -/
theorem four_le_of_two_lt_even {n : ℕ}
    (hn : 2 < n) (hEven : Even n) :
    4 ≤ n := by
  rcases hEven with ⟨k, rfl⟩
  omega

/-- The exact statement from `goal.md` is equivalent to the project's
`StrongGoldbach` definition. -/
theorem binaryGoldbachConjecture_iff_strongGoldbach :
    BinaryGoldbachConjecture ↔ StrongGoldbach := by
  constructor
  · intro h n hn hEven
    exact h n (four_le_of_two_lt_even hn hEven) hEven
  · intro h n hn hEven
    exact h n (by omega) hEven

/-- The exact `goal.md` statement gives the finite prefix through any
threshold. -/
theorem goldbachUpTo_of_binaryGoldbachConjecture {B : ℕ}
    (h : BinaryGoldbachConjecture) :
    GoldbachUpTo B :=
  goldbachUpTo_of_strongGoldbach
    (binaryGoldbachConjecture_iff_strongGoldbach.mp h)

/-- The exact `goal.md` statement gives an explicit tail target above any
threshold `B >= 2`. -/
theorem explicitLowerBound_of_binaryGoldbachConjecture {B : ℕ}
    (hB : 2 ≤ B)
    (h : BinaryGoldbachConjecture) :
    ExplicitGoldbachLowerBound B :=
  explicit_lower_bound_of_count_positive_above
    (by
      intro n hBn hEven
      exact goldbachCount_pos_of_representation
        ((binaryGoldbachConjecture_iff_strongGoldbach.mp h) n
          (lt_of_le_of_lt hB hBn) hEven))

/-- A finite Goldbach check through `B` plus an explicit tail theorem above
the same `B` proves the exact `goal.md` statement. -/
theorem binaryGoldbachConjecture_of_goldbachUpTo_and_explicitLowerBound
    {B : ℕ}
    (finite : GoldbachUpTo B)
    (lower_bound : ExplicitGoldbachLowerBound B) :
    BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_iff_strongGoldbach.mpr
    (strongGoldbach_of_finite_and_explicit_lower_bound_le
      finite (by rfl) lower_bound)

/-- For any `B >= 2`, the exact `goal.md` statement is equivalent to finite
verification through `B` plus the infinite tail target above `B`. -/
theorem binaryGoldbachConjecture_iff_goldbachUpTo_and_explicitLowerBound
    {B : ℕ} (hB : 2 ≤ B) :
    BinaryGoldbachConjecture ↔
      GoldbachUpTo B ∧ ExplicitGoldbachLowerBound B := by
  constructor
  · intro h
    exact
      ⟨goldbachUpTo_of_binaryGoldbachConjecture h,
        explicitLowerBound_of_binaryGoldbachConjecture hB h⟩
  · intro h
    exact
      binaryGoldbachConjecture_of_goldbachUpTo_and_explicitLowerBound
        h.1 h.2

/-- If a finite certificate covers through `B`, then any tail threshold `T`
with `2 <= T <= B` is an exact reduction of the literal `goal.md` statement. -/
theorem binaryGoldbachConjecture_iff_explicitLowerBound_of_goldbachUpTo_le
    {B T : ℕ}
    (hT : 2 ≤ T)
    (finite : GoldbachUpTo B)
    (hthreshold : T ≤ B) :
    BinaryGoldbachConjecture ↔ ExplicitGoldbachLowerBound T := by
  constructor
  · exact explicitLowerBound_of_binaryGoldbachConjecture hT
  · intro lower_bound
    exact
      binaryGoldbachConjecture_iff_strongGoldbach.mpr
        (strongGoldbach_of_finite_and_explicit_lower_bound_le
          finite hthreshold lower_bound)

/-- The current `50000` chunked certificate makes the literal `goal.md`
statement exactly equivalent to the current `ExplicitGoldbachLowerBound 50000`
tail theorem. -/
theorem binaryGoldbachConjecture_iff_explicitLowerBound50000_of_chunkedCertificate2To50000 :
    BinaryGoldbachConjecture ↔ ExplicitGoldbachLowerBound 50000 :=
  binaryGoldbachConjecture_iff_explicitLowerBound_of_goldbachUpTo_le
    (B := 50000) (T := 50000) (by norm_num)
    goldbachUpTo50000_of_chunkedCertificate2To50000 (by rfl)

/-- The project-wide conjecture is equivalent to the current explicit lower
bound target. -/
theorem strongGoldbach_iff_currentFormalTarget :
    StrongGoldbach ↔ CurrentFormalTarget := by
  simpa [CurrentFormalTarget] using strongGoldbach_iff_explicit_lower_bound100

/-- The exact statement from `goal.md` is equivalent to the current formal
target. -/
theorem binaryGoldbachConjecture_iff_currentFormalTarget :
    BinaryGoldbachConjecture ↔ CurrentFormalTarget :=
  binaryGoldbachConjecture_iff_strongGoldbach.trans
    strongGoldbach_iff_currentFormalTarget

/-- The project-wide conjecture is also equivalent to the intermediate
remaining target above `10000`, using the stronger current chunked finite
certificate through `50000`. -/
theorem strongGoldbach_iff_currentFormalTarget10000 :
    StrongGoldbach ↔ CurrentFormalTarget10000 := by
  constructor
  · intro h n hn hEven
    exact goldbachCount_pos_of_representation (h n (by omega) hEven)
  · intro h
    exact
      strongGoldbach_from_chunkedCertificate2To50000_and_explicit_lower_bound
        (T := 10000) (by norm_num) h

/-- The exact statement from `goal.md` is equivalent to the intermediate
finite-certificate target above `10000`. -/
theorem binaryGoldbachConjecture_iff_currentFormalTarget10000 :
    BinaryGoldbachConjecture ↔ CurrentFormalTarget10000 :=
  binaryGoldbachConjecture_iff_strongGoldbach.trans
    strongGoldbach_iff_currentFormalTarget10000

/-- The `10000` finite reduction implies the older `100`-threshold status
target. -/
theorem currentFormalTarget_of_currentFormalTarget10000
    (h : CurrentFormalTarget10000) :
    CurrentFormalTarget :=
  explicitLowerBound100_from_chunkedCertificate2To50000_and_explicit_lower_bound
    (T := 10000) (by norm_num) h

/-- The project-wide conjecture is also equivalent to the previous remaining
target above `20000`, using the chunked finite certificate through `50000`. -/
theorem strongGoldbach_iff_currentFormalTarget20000 :
    StrongGoldbach ↔ CurrentFormalTarget20000 := by
  constructor
  · intro h n hn hEven
    exact goldbachCount_pos_of_representation (h n (by omega) hEven)
  · intro h
    exact
      strongGoldbach_from_chunkedCertificate2To50000_and_explicit_lower_bound
        (T := 20000) (by norm_num) h

/-- The exact statement from `goal.md` is equivalent to the previous
finite-certificate target above `20000`. -/
theorem binaryGoldbachConjecture_iff_currentFormalTarget20000 :
    BinaryGoldbachConjecture ↔ CurrentFormalTarget20000 :=
  binaryGoldbachConjecture_iff_strongGoldbach.trans
    strongGoldbach_iff_currentFormalTarget20000

/-- The `20000` finite reduction implies the previous `10000`-threshold
status target. -/
theorem currentFormalTarget10000_of_currentFormalTarget20000
    (h : CurrentFormalTarget20000) :
    CurrentFormalTarget10000 :=
  explicit_lower_bound_of_finite_and_explicit_lower_bound_le
    (A := 10000) (B := 50000) (T := 20000)
    (by decide) goldbachUpTo50000_of_chunkedCertificate2To50000 (by norm_num) h

/-- The `20000` finite reduction also implies the older `100`-threshold status
target. -/
theorem currentFormalTarget_of_currentFormalTarget20000
    (h : CurrentFormalTarget20000) :
    CurrentFormalTarget :=
  explicitLowerBound100_from_chunkedCertificate2To50000_and_explicit_lower_bound
    (T := 20000) (by norm_num) h

/-- The project-wide conjecture is also equivalent to the strongest remaining
target above `50000`, using the chunked finite certificate through `50000`. -/
theorem strongGoldbach_iff_currentFormalTarget50000 :
    StrongGoldbach ↔ CurrentFormalTarget50000 := by
  constructor
  · intro h n hn hEven
    exact goldbachCount_pos_of_representation (h n (by omega) hEven)
  · intro h
    exact
      strongGoldbach_from_chunkedCertificate2To50000_and_explicit_lower_bound
        (T := 50000) (by rfl) h

/-- The exact statement from `goal.md` is equivalent to the strongest
finite-certificate target above `50000`. -/
theorem binaryGoldbachConjecture_iff_currentFormalTarget50000 :
    BinaryGoldbachConjecture ↔ CurrentFormalTarget50000 :=
  binaryGoldbachConjecture_iff_strongGoldbach.trans
    strongGoldbach_iff_currentFormalTarget50000

/-- The `50000` finite reduction implies the previous `20000`-threshold
status target. -/
theorem currentFormalTarget20000_of_currentFormalTarget50000
    (h : CurrentFormalTarget50000) :
    CurrentFormalTarget20000 :=
  explicit_lower_bound_of_finite_and_explicit_lower_bound_le
    (A := 20000) (B := 50000) (T := 50000)
    (by decide) goldbachUpTo50000_of_chunkedCertificate2To50000 (by rfl) h

/-- The `50000` finite reduction implies the previous `10000`-threshold
status target. -/
theorem currentFormalTarget10000_of_currentFormalTarget50000
    (h : CurrentFormalTarget50000) :
    CurrentFormalTarget10000 :=
  explicit_lower_bound_of_finite_and_explicit_lower_bound_le
    (A := 10000) (B := 50000) (T := 50000)
    (by decide) goldbachUpTo50000_of_chunkedCertificate2To50000 (by rfl) h

/-- The `50000` finite reduction also implies the older `100`-threshold status
target. -/
theorem currentFormalTarget_of_currentFormalTarget50000
    (h : CurrentFormalTarget50000) :
    CurrentFormalTarget :=
  explicitLowerBound100_from_chunkedCertificate2To50000_and_explicit_lower_bound
    (T := 50000) (by rfl) h

/-- The current Phase 5 Path A headline, when its RH hypothesis, reduced
analytic content, finite verification, and threshold coverage inputs are
supplied, yields the exact binary statement from `goal.md`. -/
theorem binaryGoldbachConjecture_under_RH_phase5_reduced
    (rh : RiemannHypothesis)
    (content : PathA_Phase5ReducedContent)
    {B : Nat} (finite : GoldbachUpTo B)
    (threshold_covered :
      ∀ T : Nat, ∀ δ : ℝ, (h : δ < 1) →
        QuarterBinaryHardyLittlewoodLowerBound T δ →
        T ≤ B ∧
          canonicalLinearContaminationThreshold ((1 - δ) / 4)
              (by have h1 : 0 < (1 - δ) := sub_pos.mpr h; positivity) ≤ B) :
    BinaryGoldbachConjecture :=
  binaryGoldbachConjecture_iff_strongGoldbach.mpr
    (strongGoldbach_under_RH_phase5_reduced rh content finite threshold_covered)

/-- The Path C K-Goldbach conclusion currently produced once the residual
analytic inputs are supplied. -/
def PathCKGoldbachConclusion : Prop :=
  ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n →
    ∃ ps : List ℕ, ps.length ≤ K ∧
      (∀ p ∈ ps, Nat.Prime p ∨ p = 0 ∨ p = 1) ∧ ps.sum = n

/-- The stricter Path C endgame needed to reach binary Goldbach: every even
`n >= 4` is a sum of at most two actual primes, with no `0`/`1` padding. -/
def PathCPrimeOnlyTwoConclusion : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n →
    ∃ ps : List ℕ, ps.length ≤ 2 ∧
      (∀ p ∈ ps, Nat.Prime p) ∧ ps.sum = n

/-- A prime-only at-most-two-summand Path C conclusion implies the exact binary
Goldbach statement. -/
theorem binaryGoldbachConjecture_of_pathCPrimeOnlyTwoConclusion
    (h : PathCPrimeOnlyTwoConclusion) :
    BinaryGoldbachConjecture := by
  intro n hn hEven
  rcases h n hn hEven with ⟨ps, hLen, hPrime, hSum⟩
  cases ps with
  | nil =>
      simp at hSum
      omega
  | cons p ps' =>
      cases ps' with
      | nil =>
          simp at hSum
          have hp : Nat.Prime p := hPrime p (by simp)
          have hpEven : Even p := by
            simpa [hSum] using hEven
          have hp_two : p = 2 := (Nat.Prime.even_iff hp).mp hpEven
          omega
      | cons q ps'' =>
          cases ps'' with
          | nil =>
              have hp : Nat.Prime p := hPrime p (by simp)
              have hq : Nat.Prime q := hPrime q (by simp)
              refine ⟨p, q, hp, hq, ?_⟩
              simpa using hSum
          | cons r ps''' =>
              simp at hLen

/-- Conversely, the exact binary statement gives the prime-only two-summand
Path C endgame. -/
theorem pathCPrimeOnlyTwoConclusion_of_binaryGoldbachConjecture
    (h : BinaryGoldbachConjecture) :
    PathCPrimeOnlyTwoConclusion := by
  intro n hn hEven
  rcases h n hn hEven with ⟨p, q, hp, hq, hsum⟩
  refine ⟨[p, q], by simp, ?_, by simpa using hsum⟩
  intro r hr
  simp at hr
  rcases hr with rfl | rfl
  · exact hp
  · exact hq

/-- The prime-only two-summand Path C endgame is exactly binary Goldbach. -/
theorem pathCPrimeOnlyTwoConclusion_iff_binaryGoldbachConjecture :
    PathCPrimeOnlyTwoConclusion ↔ BinaryGoldbachConjecture := by
  constructor
  · exact binaryGoldbachConjecture_of_pathCPrimeOnlyTwoConclusion
  · exact pathCPrimeOnlyTwoConclusion_of_binaryGoldbachConjecture

/-- The four named Path C residuals at the Round 1 frontier. -/
structure PathCFourResiduals : Prop where
  /-- Halberstam-Richert 3.11 paired-sieve kernel at `z = sqrt n`. -/
  hKernel :
    PathCLocalMainTermRefinedAtSqrtClosure.BrunGoldbachLocalMainTermRefinedAtSqrtKernel
  /-- Mertens-3/singular-series growth bound residual. -/
  hMertens3 :
    PathCBrunGoldbachSingularSeries.SingularSeriesMertens3Bound
  /-- Upgrade from the stabilized at-sqrt statement to the universal-in-`z`
  statement. -/
  hUniversal :
    PathCFullChainAudit.AtSqrtFixAStrongToUniversal
  /-- Weighted Schnirelmann absorption bridge. -/
  hSchnirelmann :
    PathCUnconditionalFixAStrong.WeightedSchnirelmannResidualBridge

/-- The Round 1 Path C residual count. -/
def pathCResidualCount : Nat := 4

theorem pathCResidualCount_eq_four : pathCResidualCount = 4 := rfl

/-- Closing the four named Path C residuals gives the current K-Goldbach
fallback conclusion. -/
theorem pathC_kGoldbach_of_fourResiduals
    (h : PathCFourResiduals) :
    PathCKGoldbachConclusion := by
  simpa [PathCKGoldbachConclusion] using
    PathCKGoldbachUnconditional.pathC_kGoldbach_unconditional
      h.hKernel h.hMertens3 h.hUniversal h.hSchnirelmann

/-- The documented Path C K bookkeeping target from `PathC_KEstimate`. -/
def pathCDocumentedKBound : Nat :=
  PathCKEstimate.kEstimateDocumented

theorem pathCDocumentedKBound_eq_202 :
    pathCDocumentedKBound = 202 := by
  simpa [pathCDocumentedKBound] using PathCKEstimate.kEstimate_audit

end Round1Status
end Gdbh
