# Round 1 Initial Decomposition

Date: 2026-05-25

## Current verified state

- The project directory is not a Git repository, so the current filesystem is
  the authoritative state.
- `python3 audit_lean_source.py` passed on 2026-05-25:
  `OK: scanned 194 Lean files; no banned project assumptions or placeholders`.
- `proof_status.json` records `complete: false`; the strongest current
  finite-reduction target is `Gdbh.ExplicitGoldbachLowerBound 50000`.
- `proof_status.json` keeps the legacy `finite_certificate` manifest at bound
  `100`, and separately records `strongest_finite_certificate` from
  `cert50000_manifest.json` at bound `50000`.
- `Gdbh/AnalyticBridge.lean` states
  `Gdbh.strongGoldbach_iff_explicit_lower_bound100`, and
  `Gdbh/Round1Status.lean` strengthens the current finite-reduction target to
  `Gdbh.ExplicitGoldbachLowerBound 50000` using the chunked certificate
  through `50000`.
- `Gdbh/Round1Status.lean` now also proves the generic exact decomposition:
  for every `B >= 2`, the literal `goal.md` statement is equivalent to
  `Gdbh.GoldbachUpTo B ∧ Gdbh.ExplicitGoldbachLowerBound B`.
- It also proves the covered-threshold variant: if a finite certificate gives
  `Gdbh.GoldbachUpTo B` and `2 <= T <= B`, then the literal `goal.md`
  statement is equivalent to `Gdbh.ExplicitGoldbachLowerBound T`. The current
  chunked certificate instantiates this at `T = B = 50000`.
- `Gdbh/PathC_FinalSummaryPhase29.lean` records four named open Path C
  residuals. These are not closed by the current worktree.
- `Gdbh/PathC_KEstimate.lean` documents the current Path C bookkeeping target
  as `K <= 202`, not `K = 2`.
- `Gdbh/PathC_HalfDensityShape.lean` records the exact output of applying
  the closed Schnirelmann half-density basis theorem to `primesSumset`: a
  half-density hypothesis for `primesSumset` gives at most four
  `primesAndOne` summands, still permitting `0`/`1` padding and not closing
  binary Goldbach.
- `Gdbh/FiniteQuotientObstruction.lean` now formalizes a finite-quotient
  obstruction note: bounded modular pair-sum coverage can hold for every
  positive modulus up to a fixed finite bound while natural-number pair-sum
  coverage still fails above twice that bound. This is a method obstruction,
  not a statement about primes and not a proof of Goldbach.
- `Gdbh/ExceptionalSetObstruction.lean` now formalizes the exceptional-range
  obstruction behind density-one/cofinite/eventual routes: coverage above a
  threshold proves the binary-Goldbach-shaped universal statement only when
  the finite range through that threshold is also checked.
- `Gdbh/FinitePrefixObstruction.lean` now formalizes the complementary finite
  prefix obstruction: perfect verification through any finite threshold, even
  the current `50000` threshold, still does not prove the universal statement
  without an infinite tail theorem.
- `Gdbh/CounterexampleReduction.lean` now repackages the current tail target
  as a no-counterexample statement: the exact `goal.md` binary statement is
  equivalent to there being no even `n > 50000` with `GoldbachCount n = 0`.
  It also proves that this is pointwise equivalent to there being no
  `GoldbachRepresentation` failure above `50000`, and that any failure of the
  exact statement has a least such representation-shaped counterexample above
  the current finite certificate threshold.  The file now also exposes the
  literal `goal.md` counterexample predicate and proves that the `50000`
  finite certificate pushes every such counterexample into this same tail.
  It additionally packages any failure as an induction-ready minimal
  counterexample `m > 50000`, where every smaller even `n >= 4` already has a
  `GoldbachRepresentation`, and names the descent obligation whose proof
  would construct a smaller literal counterexample from any such package.
  The same file now also normalizes the representation target to a lower-half
  prime-complement witness: for each even `n > 50000`, it is equivalent to
  find `p <= n / 2` with `p` and `n - p` prime; a minimal counterexample
  therefore has no such lower-half prime complement. It now additionally
  exposes the sieve-shaped consequence of such a minimal counterexample: for
  every lower-half prime `p`, the composite complement `m - p` has a proper
  prime divisor.
- `Gdbh/KGoldbachShapeObstruction.lean` now formalizes the Path C shape
  obstruction: bounded-list coverage and `0`/`1` padded pair coverage do not
  logically recover unpadded binary pair coverage. It now includes the
  explicit `K = 6` Ramaré-shaped obstruction as well as the generic
  nonzero-`K` version, and also the exact two-pair-sumset obstruction matching
  the shape `sumset (A + A) (A + A)`. A stronger version shows this remains
  true even when the two-pair-sumset coverage holds for every positive integer
  and the allowed predicate contains `0` and `1`, matching the half-density
  handoff domain.
- `Gdbh/TernaryGoldbachObstruction.lean` now formalizes the ternary/weak
  Goldbach shape obstruction: modulo `8`, a residue set can cover every odd
  residue by three summands while still failing to cover an even residue by
  two summands.
- `Gdbh/ChenShapeObstruction.lean` now formalizes the Chen-type shape
  obstruction: a `Core + Broad` theorem, even when `Broad` strictly extends
  `Core`, does not logically recover a `Core + Core` binary endpoint.
- A targeted Lean probe on 2026-05-24 checked:
  - `Gdbh.strongGoldbach_iff_explicit_lower_bound100 :
    Gdbh.StrongGoldbach <-> Gdbh.ExplicitGoldbachLowerBound 100`.
  - `Gdbh.strongGoldbach_under_RH_phase5_reduced` concludes
    `Gdbh.StrongGoldbach` only from `RiemannHypothesis`, a
    `Gdbh.PathA_Phase5ReducedContent` bundle, finite verification, and
    threshold coverage.
  - `Gdbh.PathCKGoldbachUnconditional.pathC_kGoldbach_unconditional` still
    takes the four residual hypotheses listed below.
  - The two checked headline theorems depend only on
    `[propext, Classical.choice, Quot.sound]`.
- Added `Gdbh/Round1Status.lean` on 2026-05-24 and imported it from
  `Gdbh.lean`.  It formalizes this Round 1 status layer:
  - `Gdbh.Round1Status.BinaryGoldbachConjecture`
  - `Gdbh.Round1Status.binaryGoldbachConjecture_iff_strongGoldbach`
  - `Gdbh.Round1Status.goldbachUpTo_of_binaryGoldbachConjecture`
  - `Gdbh.Round1Status.explicitLowerBound_of_binaryGoldbachConjecture`
  - `Gdbh.Round1Status.binaryGoldbachConjecture_of_goldbachUpTo_and_explicitLowerBound`
  - `Gdbh.Round1Status.binaryGoldbachConjecture_iff_goldbachUpTo_and_explicitLowerBound`
  - `Gdbh.Round1Status.binaryGoldbachConjecture_iff_explicitLowerBound_of_goldbachUpTo_le`
  - `Gdbh.Round1Status.binaryGoldbachConjecture_iff_explicitLowerBound50000_of_chunkedCertificate2To50000`
  - `Gdbh.Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget`
  - `Gdbh.Round1Status.CurrentFormalTarget`
  - `Gdbh.Round1Status.CurrentFormalTarget20000`
  - `Gdbh.Round1Status.CurrentFormalTarget50000`
  - `Gdbh.Round1Status.strongGoldbach_iff_currentFormalTarget`
  - `Gdbh.Round1Status.strongGoldbach_iff_currentFormalTarget20000`
  - `Gdbh.Round1Status.strongGoldbach_iff_currentFormalTarget50000`
  - `Gdbh.Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget20000`
  - `Gdbh.Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000`
  - `Gdbh.Round1Status.currentFormalTarget_of_currentFormalTarget20000`
  - `Gdbh.Round1Status.currentFormalTarget20000_of_currentFormalTarget50000`
  - `Gdbh.Round1Status.currentFormalTarget_of_currentFormalTarget50000`
  - `Gdbh.Round1Status.binaryGoldbachConjecture_under_RH_phase5_reduced`
  - `Gdbh.Round1Status.PathCFourResiduals`
  - `Gdbh.Round1Status.pathC_kGoldbach_of_fourResiduals`
  - `Gdbh.Round1Status.pathCDocumentedKBound_eq_202`
  - `Gdbh.Round1Status.PathCPrimeOnlyTwoConclusion`
  - `Gdbh.Round1Status.pathCPrimeOnlyTwoConclusion_iff_binaryGoldbachConjecture`
- The same status layer now formalizes the Path C binary endgame distinction:
  the currently documented Path C result is K-Goldbach with documented
  `K <= 202` and `0`/`1` padding allowed, while binary Goldbach requires the
  stronger prime-only at-most-two-summand statement.
- The same status layer now also exposes the chunked finite certificate through
  `50000`: the exact goal is equivalent to proving
  `Gdbh.ExplicitGoldbachLowerBound 50000`, not merely the older `100`
  threshold target.  This improves threshold headroom but still leaves the
  infinite analytic estimate open.
- `Gdbh/GoalHandoff.lean` now exposes exact-goal bridges from the current
  `50000` certificate and selected analytic interfaces directly to
  `Gdbh.Round1Status.BinaryGoldbachConjecture`; these are handoff/accounting
  theorems and do not prove any missing analytic estimate. The selected bridges
  now include the current Path A inner-bilinear and inner-pointwise interfaces,
  the quarter Hardy-Littlewood normalized canonical route, the absolute-error
  canonical major/minor routes, and the current DFT uniform-minor-square
  frontiers with the same `50000` certificate handoff.
- The same handoff file now also exposes direct bridges to
  `Gdbh.Round1Status.CurrentFormalTarget50000`.  These let a later analytic
  estimate with threshold `T <= 50000` close the machine-status target
  `Gdbh.ExplicitGoldbachLowerBound 50000` directly, instead of first routing
  through `StrongGoldbach` or the exact binary statement.
- `Gdbh/CounterexampleReduction.lean` exposes the same remaining target as
  `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_iff_no_counterexample_above50000`
  and
  `Gdbh.CounterexampleReduction.exists_minimal_counterexample_above50000_of_not_binaryGoldbachConjecture`.
  It now also exposes the direct representation-shaped versions
  `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_iff_no_representation_counterexample_above50000`
  and
  `Gdbh.CounterexampleReduction.exists_minimal_representation_counterexample_above50000_of_not_binaryGoldbachConjecture`.
  It also exposes the lower-half prime-complement form
  `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_iff_halfWitnessLowerBound50000`,
  the no-half-witness counterexample form
  `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_iff_no_halfWitnessCounterexample_above50000`,
  and the pointwise bridge
  `Gdbh.CounterexampleReduction.goldbachRepresentation_iff_halfWitness`.
  Finally, it exposes the literal binary-counterexample form
  `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_iff_no_binary_counterexample`,
  the pointwise certificate reduction
  `Gdbh.CounterexampleReduction.binaryCounterexample_iff_representationCounterexampleAbove50000`,
  and
  `Gdbh.CounterexampleReduction.exists_minimal_binary_counterexample_of_not_binaryGoldbachConjecture`,
  which states that any failure of the exact goal has a least literal
  counterexample and that it lies above `50000`.
  The induction-ready package
  `Gdbh.CounterexampleReduction.exists_minimalBinaryCounterexample_of_not_binaryGoldbachConjecture`
  strengthens this by also recording that every smaller even number in the
  `goal.md` range is representable; equivalently,
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_iff_no_minimalBinaryCounterexample`
  identifies the current remaining Lean target with ruling out that package.
  It also defines
  `Gdbh.CounterexampleReduction.MinimalBinaryCounterexampleDescent` and proves
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalBinaryCounterexampleDescent`
  plus
  `Gdbh.CounterexampleReduction.minimalBinaryCounterexampleDescent_iff_explicitLowerBound50000`.
  It also proves
  `Gdbh.CounterexampleReduction.minimalBinaryCounterexampleDescent_iff_halfWitnessLowerBound50000`,
  `Gdbh.CounterexampleReduction.minimalBinaryCounterexampleDescent_iff_no_minimalBinaryCounterexample`,
  `Gdbh.CounterexampleReduction.minimalBinaryCounterexampleDescent_iff_currentFormalTarget50000`,
  and
  `Gdbh.CounterexampleReduction.minimalBinaryCounterexampleDescent_iff_no_halfWitnessCounterexampleAbove50000`,
  so the lower-half witness target is another exact statement of the remaining
  tail obligation, and the descent interface is not a separate weaker route:
  it is vacuous exactly when the induction-ready minimal-counterexample set is
  empty.
  The file also defines the forced sieve package
  `Gdbh.CounterexampleReduction.MinimalCounterexamplePrimeDivisorCover` and
  proves
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_iff_no_minimalCounterexamplePrimeDivisorCover`.
  Thus ruling out a minimal counterexample with its lower-half
  prime-complement divisor cover is another exact form of the remaining target.
  The same proper-divisor cover is also converted to residue language via
  `Gdbh.CounterexampleReduction.LowerHalfPrimeComplementResidueCover`, with
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_iff_no_minimalCounterexamplePrimeResidueCover`
  identifying the remaining target with ruling out the corresponding minimal
  prime-residue-cover package.  This is further finite-universe packaged by
  `Gdbh.CounterexampleReduction.PrimeModuliBelow` and
  `Gdbh.CounterexampleReduction.MinimalCounterexampleFinitePrimeResidueCover`,
  with
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_iff_no_minimalCounterexampleFinitePrimeResidueCover`
  identifying the same remaining target with ruling out a finite set of prime
  moduli below the alleged minimal counterexample.
  The same finite cover now has a dual escape handoff via
  `Gdbh.CounterexampleReduction.LowerHalfPrimeFiniteResidueEscape` and
  `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueEscape`; an
  escaping lower-half prime avoids all finite bad congruence classes, forces
  its complement to be prime, and closes the same
  `ExplicitGoldbachLowerBound 50000` target through
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_iff_minimalCounterexampleFiniteResidueEscape`.
  This has a concrete finite counting sufficient condition through
  `Gdbh.CounterexampleReduction.LowerHalfPrimes`,
  `Gdbh.CounterexampleReduction.BadLowerHalfPrimes`, and
  `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueSurplus`:
  if the lower-half prime set is strictly larger than the finite union of
  lower-half primes covered by bad residue classes, Lean constructs the escape
  witness and closes the same remaining target via
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSurplus`.
  The file also records the standard finite union-bound majorant
  `Gdbh.CounterexampleReduction.BadLowerHalfPrimeResidueClassCardSum` and the
  stronger obligation
  `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueUnionBoundSurplus`;
  proving that sum of individual bad-class sizes is below the lower-half-prime
  count also closes the same remaining target through
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueUnionBoundSurplus`.
  The file now also records a two-range split interface: choose a threshold
  `R`, use a union-bound sum only on small moduli, and leave the large-modulus
  covered set as an exact finite target; the resulting
  `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus`
  still closes the same remaining target through
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus`.
  The large-modulus side is further arithmeticized by
  `Gdbh.CounterexampleReduction.LargeBadLowerHalfPrimeCofactorPairs`: every
  large-modulus bad lower-half prime is recovered from a complement factorization
  `m - p = r * k` with `k >= 2`, and the resulting
  `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorSplitSurplus`
  also closes the same remaining target through
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueCofactorSplitSurplus`.
  This handoff is now exact at the image level: Lean also proves
  `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorImage_subset_largeModuli`,
  hence
  `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorImage_eq_largeModuli`
  and the corresponding cardinality identity
  `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorImage_card_eq_largeModuli_card`.
  The image is therefore exactly the large-modulus covered set, not merely a
  loose upper-bound universe.
  A separate square-root sharpening now lives in
  `Gdbh/CounterexampleSqrtCofactor.lean`: if `m < (R + 1)^2`, then the
  projection `(r,k) ↦ m - r*k` is injective on
  `LargeBadLowerHalfPrimeCofactorPairs m R`, giving
  `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorImage_card_eq_cofactorPairs_card_of_mul_lt`,
  `Gdbh.CounterexampleReduction.badLowerHalfPrimesLargeModuli_card_eq_cofactorPairs_card_of_mul_lt`,
  and
  `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundSplitSurplus_iff_cofactorSplitSurplus_of_mul_lt`.
  Lean also records the natural threshold wrappers from
  `Nat.sqrt m <= R` via `Gdbh.CounterexampleReduction.square_lt_of_sqrt_le`,
  including
  `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundSplitSurplus_iff_cofactorSplitSurplus_of_sqrt_le`.
  The same file now also specializes this to the canonical cutoff
  `R = Nat.sqrt m`, with
  `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundSplitSurplus_iff_cofactorSplitSurplus_at_sqrt`
  and the exact cofactor-cardinality handoff
  `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorSplitSurplus`.
  Its closure theorem
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus`
  shows that this fixed-sqrt exact cofactor inequality would close the
  remaining target, while
  `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSqrtCofactorSplitSurplus_iff_explicitLowerBound50000`
  records the exact-strength diagnostic.  This exact fixed-sqrt interface now
  also has an exact fiber-sum form:
  `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorPairs_card_eq_sum_fibers_at_sqrt`
  rewrites the large-modulus cofactor count as a sum over
  `2 <= k <= Nat.sqrt m` of the one-dimensional fibers
  `Gdbh.CounterexampleReduction.LargeBadLowerHalfPrimeSqrtCofactorFiber m k`.
  The local theorem
  `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorFiberSplitSurplus_iff_sqrtCofactorSplitSurplus`
  shows this is an exact rewrite of the fixed-sqrt cofactor surplus, and
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorFiberSplitSurplus`
  records that closing this fiber-sum inequality would close the tail target.
  There is also a cofactor-residue upper-bound interface:
  `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorPairs_card_le_sum_cofactorResidueClasses_at_sqrt`
  injects each fixed `k` fiber into
  `Gdbh.CounterexampleReduction.LowerHalfPrimeCofactorResidueClass m k`, the
  lower-half primes congruent to `m` modulo `k`.  Thus the new handoff
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorResidueSplitSurplus`
  would close the tail target from a summed cofactor-residue inequality.
  This residue interface is further split into coprime AP classes plus a
  divisor-error term:
  `Gdbh.CounterexampleReduction.lowerHalfPrimeCofactorResidueClass_card_le_coprime_add_divisors`
  proves that the non-coprime part is contained in
  `Gdbh.CounterexampleReduction.LowerHalfPrimeDivisors m`, since a prime
  `p` with `p ∣ k` and `p ≡ m [MOD k]` also divides `m`.  Therefore
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResidueSplitSurplus`
  closes the same tail target from coprime residue-class estimates plus a
  global divisor-error budget.
  The divisor-error budget has also been made explicit:
  `Gdbh.CounterexampleReduction.lowerHalfPrimeDivisors_card_le_primeCounting_sqrt_add_one_of_one_lt`
  proves `#LowerHalfPrimeDivisors m <= Nat.primeCounting (Nat.sqrt m) + 1`
  for `m > 1` by splitting prime divisors at `sqrt m`; above `sqrt m` there
  can be at most one prime divisor.  The handoff
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorCoprimeResiduePrimeCountingDivisorSplitSurplus`
  therefore closes the same tail target from coprime residue-class estimates
  plus the explicit error term `(Nat.sqrt m - 1) * (Nat.primeCounting (Nat.sqrt m) + 1)`.
  The coprime residue-class sum is now also supported only on coprime
  cofactor moduli: if
  `p ∈ Gdbh.CounterexampleReduction.LowerHalfPrimeCofactorResidueClassCoprime m k`,
  then `Nat.Coprime m k`, so non-coprime `k` contribute zero.  The theorem
  `Gdbh.CounterexampleReduction.cofactorCoprimeResidueClassSum_eq_sum_coprimeCofactorsAtSqrt`
  rewrites the fixed-sqrt sum over `2 <= k <= sqrt m` as a sum over
  `Gdbh.CounterexampleReduction.CoprimeCofactorsAtSqrt m`, and
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorCoprimeModulusPrimeCountingDivisorSplitSurplus`
  records the corresponding handoff with the same explicit divisor-error
  term.  This is still a structural reduction, not an analytic lower bound.
  On those coprime cofactor moduli, Lean now also removes the redundant
  `Nat.Coprime p k` filter: `p ≡ m [MOD k]` and `Nat.Coprime m k` imply
  `Nat.Coprime p k`, so
  `Gdbh.CounterexampleReduction.cofactorCoprimeResidueClassSum_coprimeCofactorsAtSqrt_eq_unfiltered`
  rewrites the summand as the ordinary primitive residue class
  `Gdbh.CounterexampleReduction.LowerHalfPrimeCofactorResidueClass m k`.
  The handoff
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorPrimitiveResiduePrimeCountingDivisorSplitSurplus`
  therefore leaves the future analytic input in standard primitive AP form,
  still with the same explicit divisor-error term.
  The summand has now been standardized further as an explicit AP
  prime-counting set: `Gdbh.CounterexampleReduction.PrimeResidueClassUpTo N a q`
  is `{p <= N | p.Prime ∧ p ≡ a [MOD q]}`, and
  `Gdbh.CounterexampleReduction.lowerHalfPrimeCofactorResidueClass_eq_primeResidueClassUpTo_half`
  proves `LowerHalfPrimeCofactorResidueClass m k =
  PrimeResidueClassUpTo (m / 2) m k`.  Thus
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus`
  exposes the remaining cofactor-sieve input directly as a sum of AP prime
  counts over primitive cofactor moduli.  The right side has also been
  normalized to `Nat.primeCounting (m / 2)` via
  `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorSplitSurplus_iff_apResiduePrimeCountingDivisorFullSplitSurplus`,
  so the latest diagnostic wrapper is
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorAPResiduePrimeCountingDivisorFullSplitSurplus`.
  This full-RHS target has been split into two budgeted sub-Props:
  `Gdbh.CounterexampleReduction.LowerHalfPrimeSmallResidueClassSqrtBudget`
  for the small residue-class contribution and
  `Gdbh.CounterexampleReduction.SqrtCofactorAPResiduePrimeCountingDivisorRemainderBudget`
  for the AP prime-counting plus divisor-error remainder.  Their conjunction
  `Gdbh.CounterexampleReduction.LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorBudgetSplitSurplus`
  supplies the full-RHS target for any chosen budget function.  The remainder
  budget is now split once more into
  `Gdbh.CounterexampleReduction.SqrtCofactorAPResidueClassSumBudget`,
  `Gdbh.CounterexampleReduction.SqrtCofactorPrimeCountingDivisorErrorBudget`,
  and
  `Gdbh.CounterexampleReduction.SqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetMargin`;
  the conjunction
  `Gdbh.CounterexampleReduction.LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorThreeBudgetSplitSurplus`
  supplies the one-budget split.  The AP-sum budget is also decomposed into
  pointwise cofactor-modulus estimates:
  `Gdbh.CounterexampleReduction.SqrtCofactorAPResidueClassPointwiseBudget`
  and
  `Gdbh.CounterexampleReduction.SqrtCofactorAPResidueClassPointwiseBudgetSum`
  imply `Gdbh.CounterexampleReduction.SqrtCofactorAPResidueClassSumBudget`
  via
  `Gdbh.CounterexampleReduction.sqrtCofactorAPResidueClassSumBudget_of_pointwiseBudget`,
  and the pointwise wrapper
  `Gdbh.CounterexampleReduction.LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorPointwiseAPBudgetSplitSurplus`
  supplies the three-budget split.
  The pointwise AP wrapper now has an elementary point-count specialization:
  `Gdbh.CounterexampleReduction.primeResidueClassUpTo_card_le_pointBound`
  proves `#PrimeResidueClassUpTo N a q <= N / q + 1`, so the cofactor AP
  point budget can be fixed to `(m / 2) / k + 1` and summed as
  `Gdbh.CounterexampleReduction.SqrtCofactorAPResidueClassElementaryPointBudgetSum`.
  The resulting
  `Gdbh.CounterexampleReduction.LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPSplitSurplus`
  still has an exact-strength wrapper to `ExplicitGoldbachLowerBound 50000`;
  it records the elementary loss explicitly rather than closing the tail
  target.
  The latest wrapper fixes the remaining small-residue and divisor-error
  budget functions to their exact terms:
  `BadLowerHalfPrimeSmallResidueClassCardSum m (Nat.sqrt m)` and
  `(Nat.sqrt m - 1) * (Nat.primeCounting (Nat.sqrt m) + 1)`.  The resulting
  `Gdbh.CounterexampleReduction.LowerHalfPrimeResidueSmallUnionBoundSqrtCofactorAPResiduePrimeCountingDivisorElementaryPointAPExplicitSplitSurplus`
  is a single explicit inequality and remains exact-strength over minimal
  counterexamples.
  Lean now also extracts two necessary component-feasibility conditions from
  this explicit inequality:
  `Gdbh.CounterexampleReduction.SqrtCofactorAPResidueClassElementaryPointBudgetSumFeasible`
  and
  `Gdbh.CounterexampleReduction.SqrtCofactorPrimeCountingDivisorExactBudgetFeasible`.
  In particular,
  `Gdbh.CounterexampleReduction.not_elementaryPointAPExplicitSplitSurplus_of_divisorExactBudget_not_feasible`
  records that divisor-budget failure alone refutes the fully explicit local
  split, giving a smaller obstruction target for this branch.
  The same exact fixed-sqrt interface now
  has a rectangular-box decomposition: `Gdbh.CounterexampleReduction.div_succ_sqrt_le_sqrt`
  proves `m / (Nat.sqrt m + 1) <= Nat.sqrt m`, so
  `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorPairs_card_le_sqrtCofactorBoxProduct`
  bounds the cofactor-pair count by
  `#PrimeModuliBelowAbove m (Nat.sqrt m) * #Icc 2 (Nat.sqrt m)`.  The handoff
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorBoxSplitSurplus`
  records that this box inequality would also close the tail target, with
  `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSqrtCofactorBoxSplitSurplus_iff_explicitLowerBound50000`
  as its exact-strength diagnostic.  A separate, cruder
  side-condition-free fixed-sqrt prime-counting/product handoff is also
  recorded as
  `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueSmallUnionBoundSqrtCofactorPrimeCountingFullSplitSurplus`.
  Its closure theorem
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullSplitSurplus`
  shows that this more arithmetic single-threshold inequality would close the
  target, while
  `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSqrtCofactorPrimeCountingFullSplitSurplus_iff_explicitLowerBound50000`
  records the exact-strength diagnostic.  This is a local structural
  improvement at the square-root barrier, not a proof of the remaining
  `ExplicitGoldbachLowerBound 50000`.
  The cofactor handoff is now sharpened by
  `Gdbh.CounterexampleReduction.LargeBadLowerHalfPrimeBoundedCofactorPairs`:
  since the large-modulus branch has `r > R`, every cofactor witness also
  satisfies `k <= m / (R + 1)`.  Conversely, Lean proves
  `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeBoundedCofactorPairs_subset_pairs`,
  so
  `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorPairs_eq_bounded`
  and
  `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorPairs_card_eq_bounded`.
  Lean now also records the local and minimal-obligation equivalences
  `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus_iff_boundedCofactorSplitSurplus`
  and
  `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueCofactorSplitSurplus_iff_boundedCofactorSplitSurplus`.
  The bounded-cofactor obligation
  `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueSmallUnionBoundBoundedCofactorSplitSurplus`
  therefore also closes the current target through
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueBoundedCofactorSplitSurplus`.
  The latest cofactor-box handoff
  `Gdbh.CounterexampleReduction.LargeBadLowerHalfPrimeCofactorBox` replaces the
  exact bounded-pair count by the explicit rectangle
  `#PrimeModuliBelowAbove m R * #Icc 2 (m / (R + 1))`; the resulting
  `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxSplitSurplus`
  also closes the same current target through
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueCofactorBoxSplitSurplus`.
  The cofactor-box product variant
  `Gdbh.CounterexampleReduction.LowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus`
  simplifies the interval cardinality to the pure factor
  `m / (R + 1) - 1`; the corresponding minimal-counterexample obligation
  closes the current target through
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplus`.
  Lean now also proves that this is exactly the same local and
  minimal-counterexample obligation as the cofactor-box form, via
  `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundCofactorBoxSplitSurplus_iff_cofactorBoxProductSplitSurplus`
  and
  `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueCofactorBoxSplitSurplus_iff_cofactorBoxProductSplitSurplus`.
  The prime-counting window variant
  `Gdbh.CounterexampleReduction.LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus`
  additionally rewrites the large-modulus count as
  `Nat.primeCounting (m - 1) - Nat.primeCounting R` under the side condition
  `R < m`; its corresponding obligation closes the current target through
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingSplitSurplus`.
  The side condition is now exposed as a named intermediate obligation:
  `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplusWithLt`.
  Lean proves the local identity
  `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus_iff_lt_and_cofactorBoxProductSplitSurplus`
  and the minimal-counterexample equivalence
  `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueCofactorPrimeCountingSplitSurplus_iff_cofactorBoxProductSplitSurplusWithLt`.
  The full prime-counting variant also rewrites the lower-half target count as
  `Nat.primeCounting (m / 2)`, closing through
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus`.
  That rewrite is exact too: Lean records
  `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus_iff_cofactorPrimeCountingFullSplitSurplus`
  and
  `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueCofactorPrimeCountingSplitSurplus_iff_cofactorPrimeCountingFullSplitSurplus`.
  The point-bound full prime-counting variant
  `Gdbh.CounterexampleReduction.LowerHalfPrimeResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus`
  additionally replaces the exact small-modulus residue-class sum by the
  elementary bound
  `Gdbh.CounterexampleReduction.BadLowerHalfPrimeSmallResidueClassPointBoundSum`,
  whose summands are `m / 2 / r + 1`, and closes through
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus`.
  A later catch now shows this point-bound variant is too crude:
  `Gdbh.CounterexampleReduction.not_lowerHalfPrimeResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus_of_eight_le`
  proves that for every `m >= 8` and every `R` the local point-bound
  inequality is false, and
  `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus_iff_no_minimalBinaryCounterexample`
  records that the corresponding minimal-counterexample obligation is
  equivalent to absence of minimal binary counterexamples, not a viable
  pointwise sieve inequality at a genuine large candidate.  Lean now also
  records this directly as
  `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus_iff_explicitLowerBound50000`,
  with matching status-layer and lower-half witness forms
  `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus_iff_currentFormalTarget50000`
  and
  `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus_iff_halfWitnessLowerBound50000`.
  Thus proving that obligation is exactly as hard as the current remaining
  tail target.
  A repaired parity-aware point-bound variant now keeps the modulus `2`
  separate:
  `Gdbh.CounterexampleReduction.BadLowerHalfPrimeSmallResidueClassParityPointBoundSum`
  contributes at most one point for the bad class modulo `2` when `m` is even
  and uses the generic `m / 2 / r + 1` bound only after erasing `2` from the
  small prime-modulus set. Its corresponding obligation
  `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus`
  closes the same current target through
  `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus`.
  The parity-aware repair is also now caught as a dead end:
  `Gdbh.CounterexampleReduction.not_lowerHalfPrimeResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus_of_eight_le`
  proves the local inequality is false for every `m >= 8` and every `R`;
  for `R < 5` the large-modulus cofactor window is too large, while for
  `R >= 5` the small-modulus `2`, `3`, and `5` contributions already dominate
  the crude prime-counting target.  The theorem
  `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus_iff_no_minimalBinaryCounterexample`
  records the same equivalence-to-no-minimal-counterexample verdict.  The
  direct theorem
  `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus_iff_explicitLowerBound50000`
  and its status-layer/lower-half witness forms
  `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus_iff_currentFormalTarget50000`
  and
  `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus_iff_halfWitnessLowerBound50000`
  make explicit that this repaired point-bound obligation is also exactly as
  strong as the current remaining tail target.
  Thus the named descent obligation is a precise handoff for the remaining
  target, not a shortcut around it.
  These are least-counterexample interfaces for the open tail, not proofs that
  the counterexample sets are empty.
- The same status layer also formalizes the exact-goal Path A bridge:
  `Gdbh.strongGoldbach_under_RH_phase5_reduced` yields the exact
  `goal.md` binary statement, but only under `RiemannHypothesis`, a
  `Gdbh.PathA_Phase5ReducedContent` value, finite verification, and the
  required threshold coverage.
- `lake build Gdbh.Round1Status` succeeded on 2026-05-24.
- `lake build Gdbh.CounterexampleReduction` succeeded on 2026-05-25 after
  adding the parity-aware point-bound dead-end catch on top of the original
  point-bound dead-end catch.
- `lake build Gdbh` succeeded again on 2026-05-25 after adding the
  point-bound counterexample-reduction layer and importing
  `Gdbh.Round1Status` from the root module.
- `proof_status.json` was regenerated on 2026-05-25 and now includes
  `formalized_objective`, whose Lean definition is
  `Gdbh.Round1Status.BinaryGoldbachConjecture`. It records the legacy
  `100`-threshold equivalence
  `Gdbh.Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget` and the
  current strongest `50000`-threshold equivalence
  `Gdbh.Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000`.
- The regenerated status also includes a top-level
  `strongest_finite_certificate` manifest for `Gdbh/Certificate50000.lean`,
  whose upgrade theorem is
  `Gdbh.goldbachUpTo50000_of_chunkedCertificate2To50000`.
- Targeted `#print axioms` for the new Round 1 status theorems showed:
  - `four_le_of_two_lt_even`: `[propext, Quot.sound]`
  - `binaryGoldbachConjecture_iff_strongGoldbach`:
    `[propext, Quot.sound]`
  - `goldbachUpTo_of_binaryGoldbachConjecture`: `[propext, Quot.sound]`
  - `explicitLowerBound_of_binaryGoldbachConjecture`:
    `[propext, Classical.choice, Quot.sound]`
  - `binaryGoldbachConjecture_of_goldbachUpTo_and_explicitLowerBound`:
    `[propext, Classical.choice, Quot.sound]`
  - `binaryGoldbachConjecture_iff_goldbachUpTo_and_explicitLowerBound`:
    `[propext, Classical.choice, Quot.sound]`
  - `binaryGoldbachConjecture_iff_explicitLowerBound_of_goldbachUpTo_le`:
    `[propext, Classical.choice, Quot.sound]`
  - `binaryGoldbachConjecture_iff_explicitLowerBound50000_of_chunkedCertificate2To50000`:
    `[propext, Classical.choice, Quot.sound]`
  - `binaryGoldbachConjecture_iff_currentFormalTarget`:
    `[propext, Classical.choice, Quot.sound]`
  - `strongGoldbach_iff_currentFormalTarget`:
    `[propext, Classical.choice, Quot.sound]`
  - `strongGoldbach_iff_currentFormalTarget20000`:
    `[propext, Classical.choice, Quot.sound]`
  - `binaryGoldbachConjecture_iff_currentFormalTarget20000`:
    `[propext, Classical.choice, Quot.sound]`
  - `strongGoldbach_iff_currentFormalTarget50000`:
    `[propext, Classical.choice, Quot.sound]`
  - `binaryGoldbachConjecture_iff_currentFormalTarget50000`:
    `[propext, Classical.choice, Quot.sound]`
  - `currentFormalTarget10000_of_currentFormalTarget20000`:
    `[propext, Classical.choice, Quot.sound]`
  - `currentFormalTarget_of_currentFormalTarget20000`:
    `[propext, Classical.choice, Quot.sound]`
  - `currentFormalTarget20000_of_currentFormalTarget50000`:
    `[propext, Classical.choice, Quot.sound]`
  - `currentFormalTarget10000_of_currentFormalTarget50000`:
    `[propext, Classical.choice, Quot.sound]`
  - `currentFormalTarget_of_currentFormalTarget50000`:
    `[propext, Classical.choice, Quot.sound]`
  - `binaryGoldbachConjecture_under_RH_phase5_reduced`:
    `[propext, Classical.choice, Quot.sound]`
  - `pathC_kGoldbach_of_fourResiduals`:
    `[propext, Classical.choice, Quot.sound]`
  - `pathCDocumentedKBound_eq_202`: no axioms.
  - `binaryGoldbachConjecture_of_pathCPrimeOnlyTwoConclusion`:
    `[propext, Classical.choice, Quot.sound]`
  - `pathCPrimeOnlyTwoConclusion_of_binaryGoldbachConjecture`: `[propext]`
  - `pathCPrimeOnlyTwoConclusion_iff_binaryGoldbachConjecture`:
    `[propext, Classical.choice, Quot.sound]`
- Targeted `#print axioms` for representative `Gdbh.GoalHandoff` exact-goal
  bridges, including the Path A inner-bilinear and inner-pointwise handoffs and
  the newer quarter-HL/absolute-error/DFT-frontier handoffs, showed only
  `[propext, Classical.choice, Quot.sound]`.
- Added `Gdbh/FiniteQuotientObstruction.lean` on 2026-05-25 and imported it
  from `Gdbh.lean`. It formalizes:
  - `Gdbh.FiniteQuotientObstruction.PairSums`
  - `Gdbh.FiniteQuotientObstruction.ResiduePairCovers`
  - `Gdbh.FiniteQuotientObstruction.ResiduePairCoversUpTo`
  - `Gdbh.FiniteQuotientObstruction.no_pairSums_range_above`
  - `Gdbh.FiniteQuotientObstruction.residuePairCovers_range_of_modulus_le`
  - `Gdbh.FiniteQuotientObstruction.residuePairCovers_range_of_pos`
  - `Gdbh.FiniteQuotientObstruction.residuePairCoversUpTo_range`
  - `Gdbh.FiniteQuotientObstruction.finiteQuotientCoverage_not_global`
  - `Gdbh.FiniteQuotientObstruction.finiteQuotientDataUpTo_not_global`
- Targeted `#print axioms` for the finite-quotient obstruction theorems showed
  only `[propext, Classical.choice, Quot.sound]`.
- Added `Gdbh/ExceptionalSetObstruction.lean` on 2026-05-25 and imported it
  from `Gdbh.lean`. It formalizes:
  - `Gdbh.ExceptionalSetObstruction.EvenDomainUniversal`
  - `Gdbh.ExceptionalSetObstruction.EvenDomainEventuallyAbove`
  - `Gdbh.ExceptionalSetObstruction.EvenDomainCheckedUpTo`
  - `Gdbh.ExceptionalSetObstruction.evenDomainUniversal_iff_checkedUpTo_and_eventuallyAbove`
  - `Gdbh.ExceptionalSetObstruction.eventuallyAbove_not_global`
  - `Gdbh.ExceptionalSetObstruction.evenDomainEventuallyAbove_not_global`
- Targeted `#print axioms` for the exceptional-set obstruction theorems showed
  only `[propext, Classical.choice, Quot.sound]`.
- Added `Gdbh/FinitePrefixObstruction.lean` on 2026-05-25 and imported it
  from `Gdbh.lean`. It formalizes:
  - `Gdbh.FinitePrefixObstruction.GoldbachEvenDomain`
  - `Gdbh.FinitePrefixObstruction.CheckedOnGoldbachPrefix`
  - `Gdbh.FinitePrefixObstruction.UniversalOnGoldbachDomain`
  - `Gdbh.FinitePrefixObstruction.finitePrefixCheck_not_global`
  - `Gdbh.FinitePrefixObstruction.finitePrefixCheck50000_not_global`
- Targeted `#print axioms` for the finite-prefix obstruction theorems showed
  only `[propext, Quot.sound]`.
- Added `Gdbh/CounterexampleReduction.lean` on 2026-05-25 and imported it
  from `Gdbh.lean`. It formalizes:
  - `Gdbh.CounterexampleReduction.GoldbachCounterexampleAbove`
  - `Gdbh.CounterexampleReduction.GoldbachRepresentationCounterexampleAbove`
  - `Gdbh.CounterexampleReduction.BinaryGoldbachCounterexample`
  - `Gdbh.CounterexampleReduction.GoldbachHalfWitness`
  - `Gdbh.CounterexampleReduction.GoldbachHalfWitnessLowerBound`
  - `Gdbh.CounterexampleReduction.GoldbachHalfWitnessCounterexampleAbove`
  - `Gdbh.CounterexampleReduction.MinimalBinaryGoldbachCounterexample`
  - `Gdbh.CounterexampleReduction.LowerHalfPrimeComplementDivisorCover`
  - `Gdbh.CounterexampleReduction.LowerHalfPrimeComplementResidueCover`
  - `Gdbh.CounterexampleReduction.PrimeModuliBelow`
  - `Gdbh.CounterexampleReduction.LowerHalfPrimes`
  - `Gdbh.CounterexampleReduction.LowerHalfPrimeComplementFiniteResidueCover`
  - `Gdbh.CounterexampleReduction.LowerHalfPrimeFiniteResidueEscape`
  - `Gdbh.CounterexampleReduction.BadLowerHalfPrimeResidueClass`
  - `Gdbh.CounterexampleReduction.BadLowerHalfPrimes`
  - `Gdbh.CounterexampleReduction.LowerHalfPrimeResidueSurplus`
  - `Gdbh.CounterexampleReduction.BadLowerHalfPrimeResidueClassCardSum`
  - `Gdbh.CounterexampleReduction.LowerHalfPrimeResidueUnionBoundSurplus`
  - `Gdbh.CounterexampleReduction.PrimeModuliBelowAtMost`
  - `Gdbh.CounterexampleReduction.PrimeModuliBelowAbove`
  - `Gdbh.CounterexampleReduction.BadLowerHalfPrimesSmallModuli`
  - `Gdbh.CounterexampleReduction.BadLowerHalfPrimesLargeModuli`
  - `Gdbh.CounterexampleReduction.BadLowerHalfPrimeSmallResidueClassCardSum`
  - `Gdbh.CounterexampleReduction.LowerHalfPrimeResidueSplitSurplus`
  - `Gdbh.CounterexampleReduction.LowerHalfPrimeResidueSmallUnionBoundSplitSurplus`
  - `Gdbh.CounterexampleReduction.LargeBadLowerHalfPrimeCofactorPairs`
  - `Gdbh.CounterexampleReduction.LargeBadLowerHalfPrimeBoundedCofactorPairs`
  - `Gdbh.CounterexampleReduction.LargeBadLowerHalfPrimeCofactorBox`
  - `Gdbh.CounterexampleReduction.LargeBadLowerHalfPrimeCofactorImage`
  - `Gdbh.CounterexampleReduction.LowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.LowerHalfPrimeResidueSmallUnionBoundBoundedCofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.LowerHalfPrimeResidueSmallUnionBoundCofactorBoxSplitSurplus`
  - `Gdbh.CounterexampleReduction.LowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus`
  - `Gdbh.CounterexampleReduction.LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus`
  - `Gdbh.CounterexampleReduction.LowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.BadLowerHalfPrimeSmallResidueClassPointBoundSum`
  - `Gdbh.CounterexampleReduction.LowerHalfPrimeResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.primeCounting_le_half_add_one`
  - `Gdbh.CounterexampleReduction.two_le_primeCounting_pred_of_eight_le`
  - `Gdbh.CounterexampleReduction.not_lowerHalfPrimeResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus_of_eight_le`
  - `Gdbh.CounterexampleReduction.MinimalCounterexamplePrimeDivisorCover`
  - `Gdbh.CounterexampleReduction.MinimalCounterexamplePrimeResidueCover`
  - `Gdbh.CounterexampleReduction.MinimalCounterexampleFinitePrimeResidueCover`
  - `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueEscape`
  - `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueSurplus`
  - `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueUnionBoundSurplus`
  - `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueSplitSurplus`
  - `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus`
  - `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueSmallUnionBoundBoundedCofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxSplitSurplus`
  - `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorBoxProductSplitSurplus`
  - `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus`
  - `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorPairs_image_injOn_of_mul_lt`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorImage_card_eq_cofactorPairs_card_of_mul_lt`
  - `Gdbh.CounterexampleReduction.badLowerHalfPrimesLargeModuli_card_eq_cofactorPairs_card_of_mul_lt`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus_of_splitSurplus_of_mul_lt`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundSplitSurplus_iff_cofactorSplitSurplus_of_mul_lt`
  - `Gdbh.CounterexampleReduction.square_lt_of_sqrt_le`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorPairs_image_injOn_of_sqrt_le`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorImage_card_eq_cofactorPairs_card_of_sqrt_le`
  - `Gdbh.CounterexampleReduction.badLowerHalfPrimesLargeModuli_card_eq_cofactorPairs_card_of_sqrt_le`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus_of_splitSurplus_of_sqrt_le`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundSplitSurplus_iff_cofactorSplitSurplus_of_sqrt_le`
  - `Gdbh.CounterexampleReduction.MinimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.no_minimalBinaryCounterexample_of_minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus_iff_no_minimalBinaryCounterexample`
  - `Gdbh.CounterexampleReduction.MinimalBinaryCounterexampleDescent`
  - `Gdbh.CounterexampleReduction.counterexampleAbove_iff_representationCounterexampleAbove`
  - `Gdbh.CounterexampleReduction.goldbachRepresentation_iff_halfWitness`
  - `Gdbh.CounterexampleReduction.explicitLowerBound_iff_halfWitnessLowerBound`
  - `Gdbh.CounterexampleReduction.representationCounterexampleAbove_iff_halfWitnessCounterexampleAbove`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_iff_no_binary_counterexample`
  - `Gdbh.CounterexampleReduction.not_binaryCounterexample_of_le50000`
  - `Gdbh.CounterexampleReduction.binaryCounterexample_iff_representationCounterexampleAbove50000`
  - `Gdbh.CounterexampleReduction.exists_binary_counterexample_iff_exists_representationCounterexampleAbove50000`
  - `Gdbh.CounterexampleReduction.minimalBinaryCounterexample_of_least_binaryCounterexample`
  - `Gdbh.CounterexampleReduction.exists_minimalBinaryCounterexample_of_not_binaryGoldbachConjecture`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_iff_no_minimalBinaryCounterexample`
  - `Gdbh.CounterexampleReduction.currentFormalTarget50000_iff_no_minimalBinaryCounterexample`
  - `Gdbh.CounterexampleReduction.explicitLowerBound50000_iff_no_minimalBinaryCounterexample`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_of_no_minimalBinaryCounterexample`
  - `Gdbh.CounterexampleReduction.no_minimalBinaryCounterexample_of_descent`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_of_minimalBinaryCounterexampleDescent`
  - `Gdbh.CounterexampleReduction.currentFormalTarget50000_of_minimalBinaryCounterexampleDescent`
  - `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalBinaryCounterexampleDescent`
  - `Gdbh.CounterexampleReduction.minimalBinaryCounterexampleDescent_iff_no_minimalBinaryCounterexample`
  - `Gdbh.CounterexampleReduction.minimalBinaryCounterexampleDescent_iff_binaryGoldbachConjecture`
  - `Gdbh.CounterexampleReduction.minimalBinaryCounterexampleDescent_iff_explicitLowerBound50000`
  - `Gdbh.CounterexampleReduction.minimalBinaryCounterexampleDescent_iff_currentFormalTarget50000`
  - `Gdbh.CounterexampleReduction.minimalBinaryCounterexampleDescent_iff_halfWitnessLowerBound50000`
  - `Gdbh.CounterexampleReduction.minimalBinaryCounterexampleDescent_iff_no_halfWitnessCounterexampleAbove50000`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleObligation_iff_no_minimalBinaryCounterexample`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleObligation_iff_explicitLowerBound50000`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueEscape_iff_no_minimalBinaryCounterexample`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSurplus_iff_explicitLowerBound50000`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus_iff_no_minimalBinaryCounterexample`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus_iff_explicitLowerBound50000`
  - `Gdbh.CounterexampleReduction.not_halfWitness_of_minimalBinaryCounterexample`
  - `Gdbh.CounterexampleReduction.not_prime_complement_of_minimalBinaryCounterexample`
  - `Gdbh.CounterexampleReduction.two_le_complement_of_half_prime`
  - `Gdbh.CounterexampleReduction.not_halfWitness_of_lowerHalfPrimeComplementDivisorCover`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeComplementDivisorCover_of_minimalBinaryCounterexample`
  - `Gdbh.CounterexampleReduction.minimalCounterexamplePrimeDivisorCover_of_minimalBinaryCounterexample`
  - `Gdbh.CounterexampleReduction.minimalBinaryCounterexample_iff_primeDivisorCoverPackage`
  - `Gdbh.CounterexampleReduction.explicitLowerBound50000_iff_no_minimalCounterexamplePrimeDivisorCover`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_iff_no_minimalCounterexamplePrimeDivisorCover`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeComplementResidueCover_of_divisorCover`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeComplementDivisorCover_of_residueCover`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeComplementDivisorCover_iff_residueCover`
  - `Gdbh.CounterexampleReduction.not_halfWitness_of_lowerHalfPrimeComplementResidueCover`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeComplementResidueCover_of_minimalBinaryCounterexample`
  - `Gdbh.CounterexampleReduction.minimalCounterexamplePrimeResidueCover_of_minimalBinaryCounterexample`
  - `Gdbh.CounterexampleReduction.minimalBinaryCounterexample_iff_primeResidueCoverPackage`
  - `Gdbh.CounterexampleReduction.minimalCounterexamplePrimeDivisorCover_iff_primeResidueCover`
  - `Gdbh.CounterexampleReduction.explicitLowerBound50000_iff_no_minimalCounterexamplePrimeResidueCover`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_iff_no_minimalCounterexamplePrimeResidueCover`
  - `Gdbh.CounterexampleReduction.mem_primeModuliBelow_iff`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeComplementFiniteResidueCover_of_residueCover`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeComplementResidueCover_of_finiteResidueCover`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeComplementResidueCover_iff_finiteResidueCover`
  - `Gdbh.CounterexampleReduction.not_halfWitness_of_lowerHalfPrimeComplementFiniteResidueCover`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeComplementFiniteResidueCover_of_minimalBinaryCounterexample`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFinitePrimeResidueCover_of_minimalBinaryCounterexample`
  - `Gdbh.CounterexampleReduction.minimalBinaryCounterexample_iff_finitePrimeResidueCoverPackage`
  - `Gdbh.CounterexampleReduction.minimalCounterexamplePrimeResidueCover_iff_finitePrimeResidueCover`
  - `Gdbh.CounterexampleReduction.explicitLowerBound50000_iff_no_minimalCounterexampleFinitePrimeResidueCover`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_iff_no_minimalCounterexampleFinitePrimeResidueCover`
  - `Gdbh.CounterexampleReduction.prime_complement_of_finiteResidueEscape_witness`
  - `Gdbh.CounterexampleReduction.halfWitness_of_finiteResidueEscape`
  - `Gdbh.CounterexampleReduction.not_finiteResidueCover_of_finiteResidueEscape`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeComplementFiniteResidueCover_iff_no_finiteResidueEscape`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueEscape`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueEscape_of_binaryGoldbachConjecture`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_iff_minimalCounterexampleFiniteResidueEscape`
  - `Gdbh.CounterexampleReduction.currentFormalTarget50000_iff_minimalCounterexampleFiniteResidueEscape`
  - `Gdbh.CounterexampleReduction.explicitLowerBound50000_iff_minimalCounterexampleFiniteResidueEscape`
  - `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueEscape`
  - `Gdbh.CounterexampleReduction.mem_lowerHalfPrimes_iff`
  - `Gdbh.CounterexampleReduction.mem_badLowerHalfPrimeResidueClass_iff`
  - `Gdbh.CounterexampleReduction.mem_badLowerHalfPrimes_iff`
  - `Gdbh.CounterexampleReduction.badLowerHalfPrimes_subset_lowerHalfPrimes`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeFiniteResidueEscape_of_not_mem_badLowerHalfPrimes`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeFiniteResidueEscape_of_residueSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueEscape_of_residueSurplus`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSurplus`
  - `Gdbh.CounterexampleReduction.currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSurplus`
  - `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSurplus`
  - `Gdbh.CounterexampleReduction.badLowerHalfPrimes_card_le_badResidueClassCardSum`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSurplus_of_unionBoundSurplus`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeFiniteResidueEscape_of_unionBoundSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSurplus_of_unionBoundSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueEscape_of_unionBoundSurplus`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueUnionBoundSurplus`
  - `Gdbh.CounterexampleReduction.currentFormalTarget50000_of_minimalCounterexampleFiniteResidueUnionBoundSurplus`
  - `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueUnionBoundSurplus`
  - `Gdbh.CounterexampleReduction.badLowerHalfPrimes_subset_small_union_large`
  - `Gdbh.CounterexampleReduction.badLowerHalfPrimes_card_le_small_add_large`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSurplus_of_splitSurplus`
  - `Gdbh.CounterexampleReduction.badLowerHalfPrimesSmallModuli_card_le_smallResidueClassCardSum`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSplitSurplus_of_smallUnionBoundSplitSurplus`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSurplus_of_smallUnionBoundSplitSurplus`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeFiniteResidueEscape_of_splitSurplus`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeFiniteResidueEscape_of_smallUnionBoundSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSurplus_of_splitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueEscape_of_splitSurplus`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSplitSurplus`
  - `Gdbh.CounterexampleReduction.currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSplitSurplus`
  - `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSplitSurplus_of_smallUnionBoundSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSurplus_of_smallUnionBoundSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueEscape_of_smallUnionBoundSplitSurplus`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus`
  - `Gdbh.CounterexampleReduction.currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus`
  - `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus`
  - `Gdbh.CounterexampleReduction.badLowerHalfPrimesLargeModuli_subset_cofactorImage`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorImage_subset_largeModuli`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorImage_eq_largeModuli`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorImage_card_eq_largeModuli_card`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorPairs_image_injOn_of_mul_lt`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorImage_card_eq_cofactorPairs_card_of_mul_lt`
  - `Gdbh.CounterexampleReduction.badLowerHalfPrimesLargeModuli_card_eq_cofactorPairs_card_of_mul_lt`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus_of_splitSurplus_of_mul_lt`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundSplitSurplus_iff_cofactorSplitSurplus_of_mul_lt`
  - `Gdbh.CounterexampleReduction.square_lt_of_sqrt_le`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorPairs_image_injOn_of_sqrt_le`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorImage_card_eq_cofactorPairs_card_of_sqrt_le`
  - `Gdbh.CounterexampleReduction.badLowerHalfPrimesLargeModuli_card_eq_cofactorPairs_card_of_sqrt_le`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus_of_splitSurplus_of_sqrt_le`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundSplitSurplus_iff_cofactorSplitSurplus_of_sqrt_le`
  - `Gdbh.CounterexampleReduction.badLowerHalfPrimesLargeModuli_card_le_cofactorPairs_card`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundSplitSurplus_of_cofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSurplus_of_cofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSmallUnionBoundSplitSurplus_of_cofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSurplus_of_cofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueEscape_of_cofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.currentFormalTarget50000_of_minimalCounterexampleFiniteResidueCofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueCofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorPairs_subset_bounded`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorPairs_card_le_bounded`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeBoundedCofactorPairs_subset_pairs`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorPairs_eq_bounded`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorPairs_card_eq_bounded`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus_of_boundedCofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundBoundedCofactorSplitSurplus_of_cofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundCofactorSplitSurplus_iff_boundedCofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSurplus_of_boundedCofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueCofactorSplitSurplus_of_boundedCofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueBoundedCofactorSplitSurplus_of_cofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueCofactorSplitSurplus_iff_boundedCofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSurplus_of_boundedCofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueEscape_of_boundedCofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueBoundedCofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.currentFormalTarget50000_of_minimalCounterexampleFiniteResidueBoundedCofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueBoundedCofactorSplitSurplus`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeBoundedCofactorPairs_subset_cofactorBox`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeBoundedCofactorPairs_card_le_cofactorBox`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeCofactorBox_card`
  - `Gdbh.CounterexampleReduction.largeBadLowerHalfPrimeBoundedCofactorPairs_card_le_cofactorBoxProduct`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundBoundedCofactorSplitSurplus_of_cofactorBoxSplitSurplus`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSurplus_of_cofactorBoxSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueBoundedCofactorSplitSurplus_of_cofactorBoxSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSurplus_of_cofactorBoxSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueEscape_of_cofactorBoxSplitSurplus`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorBoxSplitSurplus`
  - `Gdbh.CounterexampleReduction.currentFormalTarget50000_of_minimalCounterexampleFiniteResidueCofactorBoxSplitSurplus`
  - `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueCofactorBoxSplitSurplus`
  - `Gdbh.CounterexampleReduction.cofactorBoxProduct_card_eq`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundCofactorBoxSplitSurplus_of_cofactorBoxProductSplitSurplus`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSurplus_of_cofactorBoxProductSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueCofactorBoxSplitSurplus_of_cofactorBoxProductSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSurplus_of_cofactorBoxProductSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueEscape_of_cofactorBoxProductSplitSurplus`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplus`
  - `Gdbh.CounterexampleReduction.currentFormalTarget50000_of_minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplus`
  - `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplus`
  - `Gdbh.CounterexampleReduction.primeModuliBelow_card_eq_primeCounting_pred_of_pos`
  - `Gdbh.CounterexampleReduction.primeModuliBelowAtMost_card_eq_primeCounting_of_lt`
  - `Gdbh.CounterexampleReduction.primeModuliBelowAtMost_card_add_primeModuliBelowAbove_card`
  - `Gdbh.CounterexampleReduction.primeModuliBelowAbove_card_eq_primeCounting_sub_of_lt`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundCofactorBoxProductSplitSurplus_of_cofactorPrimeCountingSplitSurplus`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSurplus_of_cofactorPrimeCountingSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueCofactorBoxProductSplitSurplus_of_cofactorPrimeCountingSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSurplus_of_cofactorPrimeCountingSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueEscape_of_cofactorPrimeCountingSplitSurplus`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingSplitSurplus`
  - `Gdbh.CounterexampleReduction.currentFormalTarget50000_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingSplitSurplus`
  - `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingSplitSurplus`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimes_card_eq_primeCounting_half`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingSplitSurplus_of_cofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSurplus_of_cofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueCofactorPrimeCountingSplitSurplus_of_cofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSurplus_of_cofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueEscape_of_cofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.currentFormalTarget50000_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.card_filter_range_modEq_le_div_add_one`
  - `Gdbh.CounterexampleReduction.badLowerHalfPrimeResidueClass_card_le_pointBound`
  - `Gdbh.CounterexampleReduction.badLowerHalfPrimeSmallResidueClassCardSum_le_pointBoundSum`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus_of_smallPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSurplus_of_smallPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus_of_smallPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSurplus_of_smallPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueEscape_of_smallPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSmallPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.badLowerHalfPrimeResidueClass_two_card_le_one_of_even`
  - `Gdbh.CounterexampleReduction.badLowerHalfPrimeSmallResidueClassCardSum_le_parityPointBoundSum_of_even`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSmallUnionBoundCofactorPrimeCountingFullSplitSurplus_of_smallParityPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.lowerHalfPrimeResidueSurplus_of_smallParityPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueCofactorPrimeCountingFullSplitSurplus_of_smallParityPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSurplus_of_smallParityPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueEscape_of_smallParityPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_of_minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.currentFormalTarget50000_of_minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.explicitLowerBound50000_of_minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.four_le_primeCounting_pred_of_eight_le`
  - `Gdbh.CounterexampleReduction.parityPointBoundSum_ge_two_three_of_three_le`
  - `Gdbh.CounterexampleReduction.parityPointBoundSum_ge_two_three_five_of_five_le`
  - `Gdbh.CounterexampleReduction.not_lowerHalfPrimeResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus_of_eight_le`
  - `Gdbh.CounterexampleReduction.no_minimalBinaryCounterexample_of_minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus`
  - `Gdbh.CounterexampleReduction.minimalCounterexampleFiniteResidueSmallParityPointBoundCofactorPrimeCountingFullSplitSurplus_iff_no_minimalBinaryCounterexample`
  - `Gdbh.CounterexampleReduction.explicitLowerBound_iff_no_counterexample_above`
  - `Gdbh.CounterexampleReduction.explicitLowerBound_iff_no_representation_counterexample_above`
  - `Gdbh.CounterexampleReduction.explicitLowerBound_iff_no_halfWitnessCounterexample_above`
  - `Gdbh.CounterexampleReduction.not_explicitLowerBound_iff_exists_counterexample_above`
  - `Gdbh.CounterexampleReduction.currentFormalTarget50000_iff_no_counterexample_above`
  - `Gdbh.CounterexampleReduction.currentFormalTarget50000_iff_halfWitnessLowerBound`
  - `Gdbh.CounterexampleReduction.currentFormalTarget50000_iff_no_halfWitnessCounterexample_above`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_iff_no_counterexample_above50000`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_iff_no_representation_counterexample_above50000`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_iff_halfWitnessLowerBound50000`
  - `Gdbh.CounterexampleReduction.binaryGoldbachConjecture_iff_no_halfWitnessCounterexample_above50000`
  - `Gdbh.CounterexampleReduction.not_binaryGoldbachConjecture_iff_exists_representationCounterexampleAbove50000`
  - `Gdbh.CounterexampleReduction.not_binaryGoldbachConjecture_iff_exists_halfWitnessCounterexampleAbove50000`
  - `Gdbh.CounterexampleReduction.exists_minimal_counterexample_above50000_of_not_binaryGoldbachConjecture`
  - `Gdbh.CounterexampleReduction.exists_minimal_representation_counterexample_above50000_of_not_binaryGoldbachConjecture`
  - `Gdbh.CounterexampleReduction.exists_minimal_binary_counterexample_of_not_binaryGoldbachConjecture`
- Targeted `#print axioms` for the counterexample reduction theorems showed
  `[propext, Classical.choice, Quot.sound]`.
- Added `Gdbh/KGoldbachShapeObstruction.lean` on 2026-05-25 and imported it
  from `Gdbh.lean`. It formalizes:
  - `Gdbh.KGoldbachShapeObstruction.KSummandCoverageOn`
  - `Gdbh.KGoldbachShapeObstruction.BinaryPairCoverageOn`
  - `Gdbh.KGoldbachShapeObstruction.PaddedAllowed`
  - `Gdbh.KGoldbachShapeObstruction.kSummandCoverage_not_force_binaryPairCoverage`
  - `Gdbh.KGoldbachShapeObstruction.kSummandCoverage_not_force_binaryPairCoverage_of_one_le`
  - `Gdbh.KGoldbachShapeObstruction.sixSummandCoverage_not_force_binaryPairCoverage`
  - `Gdbh.KGoldbachShapeObstruction.paddedPairCoverage_not_force_coreBinaryPairCoverage`
- Targeted `#print axioms` for the K-Goldbach shape obstruction theorems
  showed only `[propext, Classical.choice, Quot.sound]`, with
  `largeCore_oneSummandCoverage` and `largeCore_kSummandCoverage_of_one_le`
  using only `[propext]`.
- Added `Gdbh/TernaryGoldbachObstruction.lean` on 2026-05-25 and imported it
  from `Gdbh.lean`. It formalizes:
  - `Gdbh.TernaryGoldbachObstruction.TernaryCoversResidues`
  - `Gdbh.TernaryGoldbachObstruction.BinaryCoversResidues`
  - `Gdbh.TernaryGoldbachObstruction.OddResiduesMod8`
  - `Gdbh.TernaryGoldbachObstruction.EvenResiduesMod8`
  - `Gdbh.TernaryGoldbachObstruction.ToyAllowedResidues`
  - `Gdbh.TernaryGoldbachObstruction.toyAllowedResidues_ternaryCoversOddResidues`
  - `Gdbh.TernaryGoldbachObstruction.toyAllowedResidues_not_binaryCoversEvenResidues`
  - `Gdbh.TernaryGoldbachObstruction.ternaryOddResidueCoverage_not_force_binaryEvenResidueCoverage`
- Targeted `#print axioms` for the ternary/weak Goldbach shape obstruction
  theorems showed only `[propext, Quot.sound]`.
- Added `Gdbh/ChenShapeObstruction.lean` on 2026-05-25 and imported it from
  `Gdbh.lean`. It formalizes:
  - `Gdbh.ChenShapeObstruction.CorePlusBroadCoverageOn`
  - `Gdbh.ChenShapeObstruction.CorePairCoverageOn`
  - `Gdbh.ChenShapeObstruction.StrictlyBroadens`
  - `Gdbh.ChenShapeObstruction.toyBroad_strictlyBroadens_toyCore`
  - `Gdbh.ChenShapeObstruction.toyCorePlusBroadCoverage`
  - `Gdbh.ChenShapeObstruction.toyCore_not_corePairCoverage`
  - `Gdbh.ChenShapeObstruction.corePlusBroadCoverage_not_force_corePairCoverage`
- Targeted `#print axioms` for the Chen-type shape obstruction theorem
  showed only `[propext, Classical.choice, Quot.sound]`.

## Live agent launch status

The requested 25-agent launch is constrained by the current session's live
agent limit. Three explorer agents were launched:

1. `path_a_audit`: Path A RH-conditional and no-RH handoff audit.
2. `path_c_audit`: Path C K-Goldbach residual and K-bound audit.
3. `status_docs_audit`: status artifact and discrepancy audit.

A fourth explorer launch was rejected by the runtime with `agent thread limit
reached`. The 25 attack slots below are therefore the Round 1 decomposition and
queue, not a claim that all 25 are currently running.

## Core reduction

Strongest current global target:

```lean
Gdbh.ExplicitGoldbachLowerBound 50000
```

Meaning:

```lean
forall n : Nat, 50000 < n -> Even n -> 0 < Gdbh.GoldbachCount n
```

Exact `goal.md` statement now formalized:

```lean
Gdbh.Round1Status.BinaryGoldbachConjecture
```

Lean theorem:

```lean
Gdbh.Round1Status.binaryGoldbachConjecture_iff_currentFormalTarget50000 :
  Gdbh.Round1Status.BinaryGoldbachConjecture ↔
    Gdbh.Round1Status.CurrentFormalTarget50000
```

Legacy certificate-100 target, implied by the `50000` target:

```lean
Gdbh.Round1Status.CurrentFormalTarget

Gdbh.Round1Status.currentFormalTarget_of_currentFormalTarget50000 :
  Gdbh.Round1Status.CurrentFormalTarget50000 →
    Gdbh.Round1Status.CurrentFormalTarget
```

Current Phase 5 Path A conditional route to the exact statement:

```lean
Gdbh.Round1Status.binaryGoldbachConjecture_under_RH_phase5_reduced
```

This theorem is an exact-goal bridge for the existing Path A headline. It is
not unconditional: it still assumes `RiemannHypothesis`,
`Gdbh.PathA_Phase5ReducedContent`, finite verification, and threshold coverage.

Path C's prime-only two-summand endgame is now separately named:

```lean
Gdbh.Round1Status.PathCPrimeOnlyTwoConclusion

Gdbh.Round1Status.pathCPrimeOnlyTwoConclusion_iff_binaryGoldbachConjecture :
  Gdbh.Round1Status.PathCPrimeOnlyTwoConclusion ↔
    Gdbh.Round1Status.BinaryGoldbachConjecture
```

Recommended analytic handoff from `proof_status.json`:

```lean
Gdbh.VonMangoldtQuarterHardyLittlewoodNormalizedCanonicalWeightSumEstimate
```

Its remaining hard inputs are:

1. A pointwise raw von Mangoldt Hardy-Littlewood normalized error bound.
2. Final threshold coverage for the canonical contamination threshold.

## Vector A: analytic no-RH path

Primary current handoff:

```lean
Gdbh.strongGoldbach_under_RH_unconditional_pntRealRemainder_quadraticZero_pageSiegelNonPrincipal_vinogradovInnerPointwiseT3DftSupComplementLittleOMinor
```

Round 1 slots:

| Slot | Target | Current status |
| --- | --- | --- |
| A1 | `Gdbh.ZetaZeroFreeRegionAndChebyshevPsiRealPNTRemainder` | Open analytic theorem package |
| A2 | `Gdbh.PrimitivePageSiegelExceptionalQuadraticZeroAndSiegelWalfiszNonPrincipal` | Open analytic theorem package |
| A3 | `Gdbh.PathA_VinogradovInnerPointwiseT3DftSupComplementLittleOMinorPackage` | Open Vinogradov/T3 package |

First attack:

- Audit whether the latest Path A wrapper has any remaining Lean bookkeeping
  that can be lowered further without changing the mathematical burden.
- Treat the actual analytic inputs as open unless a fully quantified theorem is
  already available in mathlib v4.29.1 or this project.

## Vector B: Path C K-Goldbach path

Current Path C residuals:

1. `BrunGoldbachLocalMainTermRefinedAtSqrtKernel`
2. `SingularSeriesMertens3Bound`
3. `AtSqrtFixAStrongToUniversal`
4. `WeightedSchnirelmannResidualBridge`

Round 1 slots:

| Slot | Target | Current status |
| --- | --- | --- |
| B1 | `BrunGoldbachLocalMainTermRefinedAtSqrtKernel` | Open Halberstam-Richert 3.11 kernel |
| B2 | `SingularSeriesMertens3Bound` | Open Mertens-3 style bound |
| B3 | `AtSqrtFixAStrongToUniversal` | Open uniform-in-`z` upgrade |
| B4 | `WeightedSchnirelmannResidualBridge` | Open weighted absorption bridge |
| B5 | Prime-only two-summand binary endgame | Open; documented `K <= 202`, Ramaré-shaped `K = 6`, and even the exact positive-domain two-pair-sumset shape `(A+A)+(A+A)` with `0`/`1` padding are not enough; shape obstructions formalized in `Gdbh.KGoldbachShapeObstruction`, `Gdbh.TernaryGoldbachObstruction`, and `Gdbh.ChenShapeObstruction` |

First attack:

- Verify the four-residual catalog against the current Lean declarations.
- Do not report Path C as closing binary Goldbach until the final theorem
  proves `PathCPrimeOnlyTwoConclusion`, not merely `PathCKGoldbachConclusion`.

## Vector C: Schnirelmann density path

Round 1 slots:

| Slot | Target | Current status |
| --- | --- | --- |
| C1 | Positive/half-density input for `primesSumset` | Open in K-estimate / weighted residual chain |
| C2 | `Gdbh.PathCKGoldbach.SchnirelmannBasisHalfDensity` | Closed by `Gdbh.PathCBasisHalfDensity.schnirelmannBasisHalfDensity_holds`; `Gdbh.PathCHalfDensityShape.primesAndOne_fourSummandCoverage_of_primesSumset_halfDensity` records that applying it to `primesSumset` gives four `primesAndOne` summands, not binary Goldbach; `Gdbh.KGoldbachShapeObstruction.positiveTwoPairSumsetCoverage_with_zero_one_not_force_binaryPairCoverage` formalizes that even positive-domain `(A+A)+(A+A)` coverage with `0,1 ∈ A` does not force binary pair coverage |
| C3 | Density-to-weighted residual comparison | Open, overlaps `WeightedSchnirelmannResidualBridge` |

First attack:

- Separate purely additive-combinatorial Mann/Schnirelmann bookkeeping from
  the missing prime-density lower bounds; the half-density bookkeeping is now
  closed, while the prime-density input and prime-only two-summand endpoint
  remain separate obligations.

## Vector D: Vinogradov/Heath-Brown style minor arcs

Round 1 slots:

| Slot | Target | Current status |
| --- | --- | --- |
| D1 | Vaughan divisor-antidiagonal expansions | Mostly formalized, audit exact statement coverage |
| D2 | Type I pointwise or energy estimate | Open analytic estimate |
| D3 | Type II/III inner pointwise estimates | Open analytic estimates |
| D4 | Minor DFT finite-supremum little-o | Open analytic estimate |

First attack:

- Prefer the actual finite-sum and inner-bilinear targets already named in
  `Gdbh/PathA_Final.lean` over creating another abstract minor-arc interface.

## Vector E: novel approaches

Round 1 slots:

| Slot | Target | Current status |
| --- | --- | --- |
| E1 | Polynomial/finite-quotient obstruction note | Lean finite-quotient obstruction formalized in `Gdbh.FiniteQuotientObstruction` |
| E2 | Green-Tao / weak-to-strong transfer applicability note | Ternary-to-binary residue-shape obstruction formalized in `Gdbh.TernaryGoldbachObstruction`; Chen-type core-plus-broad transfer obstruction formalized in `Gdbh.ChenShapeObstruction`; broader density-increment note not started |
| E3 | Model-theory transfer-principle obstruction note | Finite-quotient transfer obstruction formalized; broader model-theory note not started |
| E4 | Reverse-mathematics framing note | Not started |
| E5 | Computational/ML pattern note tied to finite certificates | Exceptional-range obstruction formalized in `Gdbh.ExceptionalSetObstruction`; finite-prefix obstruction formalized in `Gdbh.FinitePrefixObstruction` |

First attack:

- Produce obstruction notes unless a route yields a quantified theorem that can
  feed `Gdbh.ExplicitGoldbachLowerBound 50000`.

## Meta slots

| Slot | Target | Current status |
| --- | --- | --- |
| M1 | Source hygiene audit and root build | Passed `audit_lean_source.py` and `lake build Gdbh` on 2026-05-25 |
| M2 | Targeted `#print axioms` for headline/status theorems | Passed for RH Path A, Path C, and `Round1Status` |
| M3 | `proof_status.json` consistency with current Lean files | Regenerated with `formalized_objective`, finite-quotient obstruction, exceptional-set obstruction, K-Goldbach shape obstruction, ternary/weak Goldbach shape obstruction, and Chen-type shape obstruction |
| M4 | Certificate threshold strategy | Pending explicit analytic threshold |
| M5 | Final handoff wrapper strategy | Pending analytic estimates |

## Completion gate

Round 1 cannot claim the objective complete unless all of the following hold:

1. A no-argument theorem of `Gdbh.ExplicitGoldbachLowerBound 50000` exists.
2. A no-argument theorem of `Gdbh.StrongGoldbach` exists.
3. `lake build` succeeds.
4. `python3 audit_lean_source.py` succeeds.
5. Targeted `#print axioms` for the final theorem shows only the allowed
   foundation axioms: `Classical.choice`, `Quot.sound`, and `propext`.
6. Any analytic certificate used for the handoff passes
   `python3 analytic_handoff_certificate.py CERT.json --require-complete --check-lean`.
